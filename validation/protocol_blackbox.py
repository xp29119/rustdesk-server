#!/usr/bin/env python3
"""Black-box native protocol tests against actual hbbs/hbbr executables.

No production endpoint option. Linux private network namespace is mandatory.
PyNaCl implements only the independent test client; no server model is used.
"""
from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
from pathlib import Path
import secrets
import shutil
import signal
import socket
import subprocess
import sys
import tempfile
import time
import uuid

from nacl.exceptions import BadSignatureError, CryptoError
from nacl.public import Box, PrivateKey, PublicKey
from nacl.secret import SecretBox
from nacl.signing import SigningKey, VerifyKey

SERVER = "10.203.0.1"
CLIENT = "10.203.0.2"
TIMEOUT = 4.0
FRAME_LIMIT = 1024 * 1024
SOURCE_COMMIT = "fada664df7a294d1d1a9ca3e7cd3637069122f17"


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def varint(n):
    require(0 <= n < 2**64, "invalid unsigned varint")
    b = bytearray()
    while n > 127:
        b.append((n & 127) | 128)
        n >>= 7
    return bytes(b + bytes([n]))


def read_varint(data, pos):
    n = 0
    for shift in range(0, 70, 7):
        if pos >= len(data):
            raise ValueError("truncated protobuf varint")
        v = data[pos]
        pos += 1
        n |= (v & 127) << shift
        if v < 128:
            if n >= 2**64:
                raise ValueError("oversized protobuf varint")
            return n, pos
    raise ValueError("unterminated protobuf varint")


def blob(tag, value):
    if isinstance(value, str):
        value = value.encode()
    return varint(tag << 3 | 2) + varint(len(value)) + value


def number(tag, value):
    return varint(tag << 3) + varint(value)


def fields(data):
    result, pos = {}, 0
    while pos < len(data):
        key, pos = read_varint(data, pos)
        tag, wire = key >> 3, key & 7
        if not tag:
            raise ValueError("zero protobuf tag")
        if wire == 0:
            value, pos = read_varint(data, pos)
        elif wire in (1, 2, 5):
            if wire == 2:
                size, pos = read_varint(data, pos)
            else:
                size = 8 if wire == 1 else 4
            if size > len(data) - pos:
                raise ValueError("truncated protobuf field")
            value, pos = data[pos:pos + size], pos + size
        else:
            raise ValueError("unsupported protobuf wire type")
        result.setdefault(tag, []).append(value)
    return result


def field(data, tag, default=b""):
    return fields(data).get(tag, [default])[-1]


def envelope(data, expected=None):
    values = fields(data)
    candidates = [t for t in values if 6 <= t <= 26]
    require(len(candidates) == 1, "response has no unique known rendezvous union")
    tag = candidates[0]
    if expected is not None:
        require(tag == expected, f"expected rendezvous union {expected}, received {tag}")
    return tag, values[tag][-1]


def frame_header(n):
    for width in range(1, 5):
        if n < 1 << (width * 8 - 2):
            return ((n << 2) | (width - 1)).to_bytes(width, "little")
    raise ValueError("frame too large")


def recv_exact(sock, n):
    out = bytearray()
    while len(out) < n:
        part = sock.recv(n - len(out))
        if not part:
            raise EOFError("peer closed before complete frame")
        out.extend(part)
    return bytes(out)


def recv_frame(sock):
    first = recv_exact(sock, 1)
    header = first + recv_exact(sock, first[0] & 3)
    n = int.from_bytes(header, "little") >> 2
    require(n <= FRAME_LIMIT, "response frame exceeds client safety limit")
    return recv_exact(sock, n)


def send_frame(sock, payload):
    sock.sendall(frame_header(len(payload)) + payload)


def connect(port):
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    sock.settimeout(TIMEOUT)
    sock.bind((CLIENT, 0))
    try:
        sock.connect((SERVER, port))
    except BaseException:
        sock.close()
        raise
    return sock


def udp_socket():
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    sock.settimeout(TIMEOUT)
    sock.bind((CLIENT, 0))
    return sock


def expect_closed(sock):
    try:
        data = sock.recv(1)
    except (ConnectionResetError, ConnectionAbortedError):
        return
    except socket.timeout as exc:
        raise AssertionError("malformed connection was not closed within deadline") from exc
    require(not data, "malformed connection returned data instead of closing")


def nonce(counter):
    return counter.to_bytes(8, "little") + bytes(16)


def client_address(address):
    # AddrMangle's IPv4 format with an intentionally fixed timestamp of zero.
    # This is just an address encoding, not a security token or server response model.
    ip, port = address
    n = (int.from_bytes(socket.inet_aton(ip), "little") << 49) | port
    return n.to_bytes(16, "little").rstrip(b"\0")


def signed_offer(sock, public_key):
    _, body = envelope(recv_frame(sock), 25)
    offer = fields(body)
    require(len(offer.get(1, [])) == 1, "expected one signed ephemeral key")
    require(field(body, 2, 0) == 0, "expected legacy version zero")
    signed = offer[1][0]
    require(len(signed) == 96, "signed ephemeral key must be 96 bytes")
    public = VerifyKey(public_key).verify(signed)
    require(len(public) == 32, "server ephemeral key must be 32 bytes")
    require(public[31] & 0x80 == 0 and field(body, 3) == b"",
            "expected unmarked legacy key; official client requires signed parameters for marked keys")
    return public


def key_reply(server_public):
    client = PrivateKey.generate()
    key = secrets.token_bytes(32)
    sealed = Box(client, PublicKey(server_public)).encrypt(key, bytes(24)).ciphertext
    return bytes(client.public_key), sealed, key


class Secured:
    def __init__(self, sock, public_key):
        self.sock = sock
        self.ephemeral = signed_offer(sock, public_key)
        client, sealed, key = key_reply(self.ephemeral)
        self.box = SecretBox(key)
        self.sent = self.received = 0
        send_frame(sock, blob(25, blob(1, client) + blob(1, sealed)))

    def encrypt(self, payload):
        self.sent += 1
        return self.box.encrypt(payload, nonce(self.sent)).ciphertext

    def send(self, payload):
        send_frame(self.sock, self.encrypt(payload))

    def recv(self):
        self.received += 1
        return self.box.decrypt(recv_frame(self.sock), nonce(self.received))


def official_plain_receive(sock):
    """Official 1.5.0 common.rs:2046: at most two frames, not infinite skipping."""
    skipped = 0
    for _ in range(2):
        msg = recv_frame(sock)
        tag, _ = envelope(msg)
        if tag == 25:
            skipped += 1
            continue
        return msg, skipped
    raise AssertionError("official two-frame receive budget exhausted")


class Servers:
    def __init__(self, args, directory):
        self.args, self.directory = args, Path(directory)
        self.port = args.port
        self.processes, self.logs = [], []
        self.pubtext = ""
        self.public = b""

    def spawn(self, name, argv):
        log_path = self.directory / (name + ".log")
        stream = open(log_path, "xb")
        os.chmod(log_path, 0o600)
        self.logs.append(stream)
        # Deliberately do not inherit proxies, KEY, PORT, production HOME, or RUST_LOG.
        env = {"PATH": os.defpath, "HOME": str(self.directory), "RUST_LOG": "info",
               "LANG": "C", "TMPDIR": str(self.directory)}
        process = subprocess.Popen(argv, cwd=self.directory, env=env, stdin=subprocess.DEVNULL,
                                   stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
        self.processes.append((name, process))
        return process

    def alive(self):
        for name, process in self.processes:
            require(process.poll() is None, f"{name} process exited unexpectedly")

    def wait_port(self, port):
        deadline = time.monotonic() + 15
        while time.monotonic() < deadline:
            self.alive()
            try:
                with connect(port):
                    return
            except OSError:
                time.sleep(0.05)
        raise AssertionError("server listener did not start")

    def start(self):
        self.spawn("hbbs", [self.args.hbbs, "-p", str(self.port), "-k", "_", "-r",
                            f"{SERVER}:{self.port + 1}"])
        self.wait_port(self.port)
        public_file = self.directory / "id_ed25519.pub"
        self.pubtext = public_file.read_text().strip()  # Public key only; never read private file.
        self.public = base64.b64decode(self.pubtext, validate=True)
        require(len(self.public) == 32, "generated signing public key is invalid")
        self.spawn("hbbr", [self.args.hbbr, "-p", str(self.port + 1), "-k", self.pubtext])
        self.wait_port(self.port + 1)
        self.wait_port(self.port - 1)

    def stop(self):
        for _, process in reversed(self.processes):
            if process.poll() is None:
                try:
                    os.killpg(process.pid, signal.SIGTERM)
                except ProcessLookupError:
                    pass
        for _, process in reversed(self.processes):
            try:
                process.wait(timeout=4)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.wait(timeout=2)
        for stream in self.logs:
            stream.close()

    def healthy_exchange(self):
        self.alive()
        with connect(self.port) as sock:
            secure = Secured(sock, self.public)
            secure.send(blob(20, b""))
            _, response = envelope(secure.recv(), 21)
            require(field(response, 1, 0) == sock.getsockname()[1], "NAT reply has wrong port")
        self.alive()


class Cases:
    def __init__(self, servers, token):
        self.s = servers
        self.token = token
        self.peer = None
        self.peer_id = str(secrets.randbelow(899999999) + 100000000)
        self.peer_key = bytes(SigningKey.generate().verify_key)
        self.peer_uuid = secrets.token_bytes(16)

    def close(self):
        if self.peer:
            self.peer.close()

    def punch(self, peer_id="987654321999", key=None, token=None):
        return blob(8, blob(1, peer_id) + blob(3, self.s.pubtext if key is None else key)
                    + blob(5, self.token if token is None else token) + blob(6, "1.5.0"))

    def udp_roundtrip(self, payload, expected):
        self.peer.sendto(payload, (SERVER, self.s.port))
        data, addr = self.peer.recvfrom(65536)
        require(addr == (SERVER, self.s.port), "UDP reply source mismatch")
        return envelope(data, expected)[1]

    def heartbeat(self):
        response = self.udp_roundtrip(blob(6, blob(1, self.peer_id)), 7)
        require(field(response, 2, 0) == 0, "registered peer unexpectedly needs public key")

    def plaintext_registration_and_query(self):
        self.peer = udp_socket()
        response = self.udp_roundtrip(blob(6, blob(1, self.peer_id)), 7)
        require(field(response, 2, 0) == 1, "new native UDP peer was not asked for public key")
        response = self.udp_roundtrip(blob(15, blob(1, self.peer_id) + blob(2, self.peer_uuid)
                                                    + blob(3, self.peer_key)), 16)
        require(field(response, 1, 0) == 0, "native UDP RegisterPk did not return OK")
        self.heartbeat()
        with connect(self.s.port - 1) as sock:
            send_frame(sock, blob(23, blob(1, "native-query") + blob(2, self.peer_id)
                                 + blob(2, "987654321999")))
            _, response = envelope(recv_frame(sock), 24)
            states = field(response, 1)
            require(states == b"\x80", "online query did not distinguish registered/missing peer")
        return {"register_transport": "UDP", "online_query_port": "base-1", "account_token": False}

    def signed_account_request_deferred_response(self):
        require(self.peer is not None, "registration prerequisite failed")
        self.heartbeat()
        with connect(self.s.port) as controller:
            secure = Secured(controller, self.s.public)
            secure.send(self.punch(self.peer_id))
            notification, notification_source = self.peer.recvfrom(65536)
            require(notification_source == (SERVER, self.s.port), "punch notification source mismatch")
            tag, body = envelope(notification)
            require(tag in (9, 12), "registered target did not receive native punch notification")
            controller_address = field(body, 1)
            require(bool(controller_address), "missing controller address in notification")
            # Native controlled peer replies to hbbs over a separate TCP connection.
            # Reuse the opaque address supplied by hbbs; do not mirror AddrMangle.
            with connect(self.s.port) as controlled:
                if tag == 12:
                    # Official handle_intranet_ sends LocalAddr in response to FetchLocalAddr.
                    expected_target_address = client_address(controlled.getsockname())
                    reply = blob(13, blob(1, controller_address)
                                 + blob(2, expected_target_address)
                                 + blob(3, "relay.test.invalid") + blob(4, self.peer_id)
                                 + blob(5, "1.5.0"))
                else:
                    reply = blob(10, blob(1, controller_address)
                                 + blob(2, self.peer_id) + blob(3, "relay.test.invalid")
                                 + number(4, 2) + blob(5, "1.5.0"))
                send_frame(controlled, reply)
                envelope(recv_frame(controlled), 25)
            _, response = envelope(secure.recv(), 11)
            require(bool(field(response, 1)), "deferred response has no target address")
            if tag == 12:
                require(field(response, 1) == expected_target_address, "deferred local address changed")
                require(field(response, 6, 0) == 1, "deferred LocalAddr response lost is_local flag")
            require(field(response, 4) == b"relay.test.invalid", "deferred relay metadata changed")
            signed_peer = VerifyKey(self.s.public).verify(field(response, 2))
            require(field(signed_peer, 1) == self.peer_id.encode(), "signed peer ID mismatch")
            require(field(signed_peer, 2) == self.peer_key, "signed peer public key mismatch")
        return {"signed_offer_verified": True, "request_encrypted": True,
                "deferred_response_decrypted": True, "account_token_sent_inside_ciphertext": True}

    def plaintext_punch_uses_official_skip(self):
        with connect(self.s.port) as sock:
            # Official unlogged path sends first, then skips at most one offer while receiving.
            send_frame(sock, self.punch(token=""))
            msg, skipped = official_plain_receive(sock)
            _, response = envelope(msg, 11)
            require(skipped == 1, "expected exactly one unsolicited KeyExchange before plaintext reply")
            require(field(response, 3, 0) == 0, "missing native peer should return ID_NOT_EXIST")
        return {"official_max_frames": 2, "keyexchange_frames_skipped": skipped}

    def wrong_signing_public_key(self):
        with connect(self.s.port) as sock:
            try:
                signed_offer(sock, bytes(SigningKey.generate().verify_key))
            except BadSignatureError:
                pass
            else:
                raise AssertionError("wrong configured signing key accepted server signature")
            # No key reply or account request is sent after trust failure.
        self.s.healthy_exchange()
        return {"rejection_side": "client", "application_bytes_sent_after_bad_signature": 0}

    def wrong_licence_key(self):
        with connect(self.s.port) as sock:
            secure = Secured(sock, self.s.public)
            secure.send(self.punch(key=base64.b64encode(secrets.token_bytes(32)).decode()))
            _, response = envelope(secure.recv(), 11)
            require(field(response, 3, 0) == 3, "server did not reject wrong licence_key")
        return {"server_failure": "LICENSE_MISMATCH"}

    def malformed_handshake_lengths(self):
        variants = [[], [bytes(32)], [bytes(31), bytes(48)], [bytes(33), bytes(48)],
                    [bytes(32), bytes(47)], [bytes(32), bytes(49)], [bytes(32), bytes(48), b""]]
        for keys in variants:
            with connect(self.s.port) as sock:
                signed_offer(sock, self.s.public)
                send_frame(sock, blob(25, b"".join(blob(1, item) for item in keys)))
                expect_closed(sock)
            self.s.healthy_exchange()
        return {"malformed_variants": len(variants), "fresh_encrypted_check_after_each": True}

    def bad_box_ciphertext(self):
        with connect(self.s.port) as sock:
            server_public = signed_offer(sock, self.s.public)
            client, sealed, _ = key_reply(server_public)
            sealed = bytes([sealed[0] ^ 1]) + sealed[1:]
            send_frame(sock, blob(25, blob(1, client) + blob(1, sealed)))
            expect_closed(sock)
        self.s.healthy_exchange()

    def malformed_protobuf(self):
        with connect(self.s.port) as sock:
            signed_offer(sock, self.s.public)
            send_frame(sock, b"\x80")
            expect_closed(sock)
        self.s.healthy_exchange()

    def oversized_frame_header(self):
        # 1 MiB + 1 is bounded even if a baseline codec reserves it; never send huge/OOM lengths.
        for encrypted in (False, True):
            with connect(self.s.port) as sock:
                if encrypted:
                    Secured(sock, self.s.public)
                else:
                    signed_offer(sock, self.s.public)
                sock.sendall(frame_header(FRAME_LIMIT + 1))
                expect_closed(sock)
            self.s.healthy_exchange()
        return {"declared_bytes": FRAME_LIMIT + 1, "payload_bytes_sent": 0,
                "phases": ["before_exchange", "after_exchange"]}

    def bad_secretbox_no_plaintext_fallback(self):
        with connect(self.s.port) as sock:
            secure = Secured(sock, self.s.public)
            ciphertext = secure.encrypt(self.punch())
            ciphertext = bytes([ciphertext[0] ^ 1]) + ciphertext[1:]
            # Append a valid plaintext request in the same write: must not downgrade/recover.
            sock.sendall(frame_header(len(ciphertext)) + ciphertext
                         + frame_header(len(self.punch(token=""))) + self.punch(token=""))
            expect_closed(sock)
        self.s.healthy_exchange()

    def independent_connection_keys_and_counters(self):
        with connect(self.s.port) as a, connect(self.s.port) as b:
            first, second = Secured(a, self.s.public), Secured(b, self.s.public)
            require(first.ephemeral != second.ephemeral, "ephemeral server key reused across connections")
            first.send(self.punch())
            second.send(self.punch())
            # Each direction starts independently at one; request nonce must not advance response nonce.
            envelope(second.recv(), 11)
            envelope(first.recv(), 11)
        with connect(self.s.port) as a, connect(self.s.port) as b:
            first, second = Secured(a, self.s.public), Secured(b, self.s.public)
            captured = first.encrypt(self.punch())
            send_frame(b, captured)
            expect_closed(b)
            send_frame(a, captured)
            envelope(first.recv(), 11)
        self.s.healthy_exchange()
        return {"interleaved_connections": 2, "cross_connection_ciphertext_rejected": True,
                "scope": "one application response per native request connection"}

    def udp_punch_reflection_disabled_registration_survives(self):
        require(self.peer is not None, "registration prerequisite failed")
        self.heartbeat()
        with udp_socket() as caller:
            caller.settimeout(0.4)
            self.peer.settimeout(0.4)
            try:
                for target in ("987654321999", self.peer_id):
                    caller.sendto(self.punch(target, token=""), (SERVER, self.s.port))
                    for stream in (caller, self.peer):
                        try:
                            stream.recvfrom(65536)
                        except socket.timeout:
                            pass
                        else:
                            raise AssertionError("UDP PunchHoleRequest produced a reflected response")
            finally:
                self.peer.settimeout(TIMEOUT)
        # An unresponsive UDP socket alone is not a pass: normal register remains live.
        self.heartbeat()
        self.s.healthy_exchange()
        return {"unsupported_udp_punch_targets": ["missing", "registered"],
                "caller_and_registered_target_observed": True, "registration_after_probe": "OK"}

    def hbbr_pair_encrypted_opaque_roundtrip(self):
        pair_uuid = str(uuid.uuid4())
        request = blob(18, blob(1, self.peer_id) + blob(2, pair_uuid) + blob(6, self.s.pubtext))
        with connect(self.s.port + 1) as a, connect(self.s.port + 1) as b:
            send_frame(a, request)
            time.sleep(0.1)
            send_frame(b, request)
            time.sleep(0.1)
            box = SecretBox(secrets.token_bytes(32))
            for i in range(1, 4):
                for sender, receiver, direction in ((a, b, b"A"), (b, a, b"B")):
                    payload = direction + secrets.token_bytes(8192 + i)
                    encoded = box.encrypt(payload, direction + bytes(15) + i.to_bytes(8, "little"))
                    send_frame(sender, bytes(encoded))
                    received = recv_frame(receiver)
                    require(received == bytes(encoded), "hbbr changed opaque encrypted payload")
                    require(box.decrypt(received) == payload, "relayed payload failed independent decrypt")
        self.s.alive()
        return {"roundtrips_each_direction": 3, "payload_kind": "opaque test SecretBox data",
                "note": "hbbr forwards bytes; this is not a RustDesk desktop/media-session test"}

    def hbbr_wrong_licence_key(self):
        with connect(self.s.port + 1) as sock:
            send_frame(sock, blob(18, blob(1, self.peer_id) + blob(2, str(uuid.uuid4()))
                                 + blob(6, "wrong-test-key")))
            expect_closed(sock)
        self.hbbr_pair_encrypted_opaque_roundtrip()
        return {"fresh_relay_pair_after_rejection": True}


TESTS = [
    "plaintext_registration_and_query", "signed_account_request_deferred_response",
    "plaintext_punch_uses_official_skip", "wrong_signing_public_key", "wrong_licence_key",
    "malformed_handshake_lengths", "bad_box_ciphertext", "malformed_protobuf",
    "oversized_frame_header", "bad_secretbox_no_plaintext_fallback",
    "independent_connection_keys_and_counters", "udp_punch_reflection_disabled_registration_survives",
    "hbbr_pair_encrypted_opaque_roundtrip", "hbbr_wrong_licence_key",
]


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def assert_and_setup_namespace(parent_inode):
    require(sys.platform == "linux", "real integration requires Linux network namespaces")
    require(os.readlink("/proc/self/ns/net") != parent_inode, "refusing unchanged host network namespace")
    ip = shutil.which("ip")
    require(ip is not None, "iproute2 is required")
    # sysfs can retain the network-namespace view from when it was mounted.
    # A fresh rtnetlink query inspects this process's current network namespace.
    links = subprocess.run([ip, "-j", "link", "show"],
                           check=True, capture_output=True, text=True)
    interfaces = json.loads(links.stdout)
    require(isinstance(interfaces, list) and len(interfaces) == 1
            and interfaces[0].get("ifname") == "lo"
            and interfaces[0].get("link_type") == "loopback",
            "private namespace unexpectedly has non-loopback interfaces")
    for argv in ([ip, "link", "set", "lo", "up"],
                 [ip, "addr", "add", SERVER + "/32", "dev", "lo"],
                 [ip, "addr", "add", CLIENT + "/32", "dev", "lo"]):
        subprocess.run(argv, check=True, stdin=subprocess.DEVNULL, capture_output=True)
    routes = subprocess.run([ip, "-j", "route", "show", "table", "main"],
                            check=True, capture_output=True, text=True)
    require(all(r.get("dev") == "lo" and r.get("dst") != "default"
                for r in json.loads(routes.stdout)), "private namespace has an unexpected outbound route")


def self_check():
    # A tooling check only. Deliberately does not produce an integration success report.
    for size in (0, 1, 63, 64, 16383, 16384, FRAME_LIMIT + 1):
        header = frame_header(size)
        require(len(header) == (header[0] & 3) + 1, "frame width")
        require(int.from_bytes(header, "little") >> 2 == size, "frame length")
    payload = blob(8, blob(1, "test") + number(2, 2))
    require(field(envelope(payload, 8)[1], 1) == b"test", "protobuf helper")
    public = PrivateKey.generate()
    client, sealed, key = key_reply(bytes(public.public_key))
    require(Box(public, PublicKey(client)).decrypt(sealed, bytes(24)) == key, "client box helper")
    print("PASS tooling self-check; real_server_process=false; actualClient=false")


def run(args):
    assert_and_setup_namespace(args._parent_netns)
    report = {"schema": 1, "real_server_process": False, "actualClient": False,
              "started_at_unix": time.time(), "isolation": "new Linux netns; only lo; no outbound route",
              "test_client_source": "independent Python/PyNaCl client",
              "official_client_reference_commit": SOURCE_COMMIT,
              "account_token_origin": "synthetic", "hbbs_validates_account_token": False,
              "binaries": {"hbbs_sha256": sha256(args.hbbs), "hbbr_sha256": sha256(args.hbbr)},
              "limitations": ["Not an actual Mac/Windows/Android/iOS executable or remote desktop session",
                              "Synthetic opaque token exercises secure-client protocol selection, not API login",
                              "One application response per native request connection; no invented keepalive API",
                              "UDP regression checks native PunchHoleRequest, not all possible UDP abuse"],
              "tests": []}
    token = secrets.token_hex(32)
    if args.account_token_file:
        path = Path(args.account_token_file)
        require(path.is_file() and path.stat().st_mode & 0o077 == 0, "token file must be private (0600)")
        token = path.read_text().strip()
        require(bool(token) and len(token) <= 4096, "invalid token file length")
        report["account_token_origin"] = "supplied-private-file; issuance not verified by this harness"
    with tempfile.TemporaryDirectory(prefix="rustdesk-blackbox-") as directory:
        servers = Servers(args, directory)
        cases = Cases(servers, token)
        try:
            servers.start()
            report["real_server_process"] = True
            report["public_key_sha256"] = hashlib.sha256(servers.public).hexdigest()
            for name in TESTS:
                started = time.monotonic()
                item = {"name": name}
                try:
                    item["evidence"] = getattr(cases, name)() or {}
                    servers.alive()
                    item["status"] = "pass"
                except Exception as exc:
                    item["status"] = "fail"
                    item["error"] = (type(exc).__name__ + ": " + str(exc)).replace(token, "[REDACTED]")
                item["seconds"] = round(time.monotonic() - started, 3)
                report["tests"].append(item)
                print(item["status"].upper(), name, flush=True)
        except Exception as exc:
            report["startup_error"] = (type(exc).__name__ + ": " + str(exc)).replace(token, "[REDACTED]")
        finally:
            cases.close()
            servers.stop()
            # Logs contain only synthetic data and generated public metadata; redact optional supplied token.
            # Never copy keys, SQLite, or the temporary HOME into the retained result directory.
            if args.keep_logs:
                logdir = Path(args.report).parent / "protocol-blackbox-logs"
                logdir.mkdir(mode=0o700, parents=True, exist_ok=True)
                os.chmod(logdir, 0o700)
                for name in ("hbbs", "hbbr"):
                    source = Path(directory) / (name + ".log")
                    if source.exists():
                        target = logdir / (name + ".log")
                        target.write_text(source.read_text(errors="replace").replace(token, "[REDACTED]"))
                        os.chmod(target, 0o600)
                report["private_logs_retained"] = True
    report["passed"] = len(report["tests"]) == len(TESTS) and all(t["status"] == "pass" for t in report["tests"])
    report["finished_at_unix"] = time.time()
    destination = Path(args.report)
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(report, indent=2) + "\n")
    print("real_server_process=" + str(report["real_server_process"]).lower()
          + "; actualClient=false; passed=" + str(report["passed"]).lower())
    return 0 if report["passed"] else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--hbbs", help="absolute or relative path to reviewed, compiled hbbs")
    parser.add_argument("--hbbr", help="absolute or relative path to reviewed, compiled hbbr")
    parser.add_argument("--report", default="protocol-blackbox-result.json")
    parser.add_argument("--port", type=int, default=32116)
    parser.add_argument("--account-token-file", help="optional private 0600 token file; default is synthetic")
    parser.add_argument("--keep-logs", action="store_true", help="retain redacted process logs with 0600 mode")
    parser.add_argument("--self-check", action="store_true", help="tooling-only check, no integration claim")
    parser.add_argument("--_parent-netns", help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.self_check:
        self_check()
        return 0
    require(args.hbbs and args.hbbr, "--hbbs and --hbbr are required")
    require(1024 < args.port < 65532, "invalid test base port")
    for name in ("hbbs", "hbbr"):
        path = Path(getattr(args, name)).resolve(strict=True)
        require(path.is_file() and os.access(path, os.X_OK), "server binary must be executable")
        setattr(args, name, str(path))
    args.report = str(Path(args.report).resolve())
    if args.account_token_file:
        args.account_token_file = str(Path(args.account_token_file).resolve(strict=True))
    require(sys.platform == "linux", "real integration requires Linux; use CI, not the Mac host")
    if args._parent_netns:
        return run(args)
    unshare = shutil.which("unshare")
    require(unshare is not None, "util-linux unshare is required")
    command = [unshare]
    if os.geteuid() != 0:
        command += ["--user", "--map-root-user"]
    command += ["--net", sys.executable, str(Path(__file__).resolve()), "--hbbs", args.hbbs,
                "--hbbr", args.hbbr, "--report", args.report, "--port", str(args.port),
                "--_parent-netns", os.readlink("/proc/self/ns/net")]
    if args.account_token_file:
        command += ["--account-token-file", args.account_token_file]
    if args.keep_logs:
        command += ["--keep-logs"]
    # If namespace creation is forbidden, fail closed. Never retry on the host network.
    return subprocess.run(command, stdin=subprocess.DEVNULL).returncode


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (AssertionError, OSError, ValueError) as exc:
        print("ERROR:", str(exc), file=sys.stderr)
        raise SystemExit(2)
