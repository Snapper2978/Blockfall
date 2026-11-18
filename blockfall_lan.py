#!/usr/bin/env python3
"""
Blockfall same-wifi relay (browser players only).

One file, no packages, Python 3.8+.  It does two jobs on one machine:

  1. serves the browser build of Blockfall over plain HTTP, so Chromebooks,
     phones and PCs on the same wifi can just open a URL and play;
  2. runs the room relay on a WebSocket endpoint at /ws, so every browser
     that opened that URL lands in the same lobby.

No 3DS, no console settings, no port forwarding, no internet.

    python3 blockfall_lan.py                  # http://<your-ip>:8080
    python3 blockfall_lan.py --port 9000

Put blockfall.html next to this file (download it from the site's /play page).
The browser build reads its relay address from the page it was served from, so
players never type a server address.
"""
import argparse
import base64
import hashlib
import os
import socket
import struct
import sys
import threading
import time

GAME_FILE = "blockfall.html"
WS_PATH = "/ws"

MAX_PLAYERS = 8
HOST_NODE = 1
BROADCAST = 0xFF
ROOM_NAME_MAX = 16
PLAYER_NAME_MAX = 12
MAX_FRAME = 4096
MAX_ROOMS = 200

C_LIST, C_CREATE, C_JOIN, C_DATA, C_LEAVE = 0x01, 0x02, 0x03, 0x04, 0x05
S_ROOMS, S_CREATED, S_JOINED, S_ERROR, S_DATA = 0x81, 0x82, 0x83, 0x84, 0x85

E_BAD_REQUEST, E_VERSION, E_NAME_TAKEN, E_NO_ROOM, E_FULL, E_STARTED, \
    E_BAD_NAME, E_BUSY, E_LIMIT = range(1, 10)

PKT_WORLD = 2
PKT_BYE = 4
STATE_LOBBY = 0
PROTOCOL_VERSION = 1

WS_GUID = "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"

log_lock = threading.Lock()


def log(message):
    with log_lock:
        print(time.strftime("[%H:%M:%S] ") + message, flush=True)


def clean_text(raw, limit):
    text = "".join(chr(b) for b in raw if 32 <= b <= 126)
    return text.strip()[:limit]


def enc_str(text):
    data = text.encode("ascii", "replace")[:255]
    return bytes([len(data)]) + data


class Reader:
    def __init__(self, data):
        self.data, self.pos = data, 0

    def u8(self):
        if self.pos >= len(self.data):
            raise ValueError("short frame")
        value = self.data[self.pos]
        self.pos += 1
        return value

    def string(self):
        length = self.u8()
        if self.pos + length > len(self.data):
            raise ValueError("short string")
        value = self.data[self.pos:self.pos + length]
        self.pos += length
        return value

    def rest(self):
        value = self.data[self.pos:]
        self.pos = len(self.data)
        return value


class WsTransport:
    """Minimal RFC 6455 binary transport; each message carries relay bytes."""

    def __init__(self, sock, addr, rfile):
        self.sock = sock
        self.addr = addr
        self.rfile = rfile

    def read(self):
        while True:
            header = self.rfile.read(2)
            if len(header) < 2:
                return None
            first, second = header[0], header[1]
            opcode = first & 0x0F
            masked = bool(second & 0x80)
            length = second & 0x7F
            if length == 126:
                length = struct.unpack(">H", self.rfile.read(2))[0]
            elif length == 127:
                length = struct.unpack(">Q", self.rfile.read(8))[0]
            if length > 65536:
                return None
            mask = self.rfile.read(4) if masked else None
            payload = self.rfile.read(length) if length else b""
            if len(payload) < length:
                return None
            if mask:
                payload = bytes(byte ^ mask[i % 4] for i, byte in enumerate(payload))
            if opcode == 0x8:
                return None
            if opcode == 0x9:
                self._frame(payload, 0xA)
                continue
            if opcode == 0xA:
                continue
            return payload

    def _frame(self, data, opcode):
        header = bytes([0x80 | opcode])
        length = len(data)
        if length < 126:
            header += bytes([length])
        elif length < 65536:
            header += bytes([126]) + struct.pack(">H", length)
        else:
            header += bytes([127]) + struct.pack(">Q", length)
        self.sock.sendall(header + data)

    def send(self, data):
        self._frame(data, 0x2)

    def close(self):
        try:
            self._frame(b"", 0x8)
        except OSError:
            pass
        try:
            self.sock.close()
        except OSError:
            pass


class Room:
    def __init__(self, name, public, host_name):
        self.name = name
        self.public = public
        self.host_name = host_name
        self.state = STATE_LOBBY
        self.members = {}

    @property
    def key(self):
        return self.name.lower()

    def free_node(self):
        for node in range(HOST_NODE + 1, MAX_PLAYERS + 1):
            if node not in self.members:
                return node
        return None


class Peer:
    def __init__(self, transport):
        self.transport = transport
        self.room = None
        self.node = 0
        self.closed = False
        self.last_seen = time.time()

    def send(self, mtype, body=b""):
        if self.closed:
            return
        frame = bytes([mtype]) + body
        try:
            self.transport.send(struct.pack("<H", len(frame)) + frame)
        except OSError:
            self.closed = True

    def error(self, code, message):
        self.send(S_ERROR, bytes([code]) + enc_str(message))


class Relay:
    def __init__(self):
        self.lock = threading.RLock()
        self.rooms = {}

    def leave_room(self, peer):
        room, node = peer.room, peer.node
        if room is None:
            return
        peer.room, peer.node = None, 0
        room.members.pop(node, None)
        bye = bytes([PKT_BYE, 0])
        if node == HOST_NODE:
            if self.rooms.get(room.key) is room:
                del self.rooms[room.key]
            for other in list(room.members.values()):
                other.room, other.node = None, 0
                other.send(S_DATA, bytes([HOST_NODE]) + bye)
            room.members.clear()
            log("room %r closed" % room.name)
        else:
            host = room.members.get(HOST_NODE)
            if host:
                host.send(S_DATA, bytes([node]) + bye)
            log("player left room %r (%d left)" % (room.name, len(room.members)))

    def on_list(self, peer):
        rooms = [room for room in self.rooms.values() if room.public]
        rooms.sort(key=lambda room: (room.state != STATE_LOBBY,
                                     -len(room.members), room.name.lower()))
        rooms = rooms[:40]
        body = bytearray([len(rooms)])
        for room in rooms:
            body += enc_str(room.name) + enc_str(room.host_name)
            body += bytes([len(room.members), MAX_PLAYERS, room.state])
        peer.send(S_ROOMS, bytes(body))

    def on_create(self, peer, reader):
        version, public = reader.u8(), reader.u8()
        name = clean_text(reader.string(), ROOM_NAME_MAX)
        host_name = clean_text(reader.string(), PLAYER_NAME_MAX) or "HOST"
        if version != PROTOCOL_VERSION:
            return peer.error(E_VERSION, "Server and game versions differ.")
        if peer.room:
            return peer.error(E_BUSY, "Already in a room.")
        if not name:
            return peer.error(E_BAD_NAME, "Room name is empty.")
        if name.lower() in self.rooms:
            return peer.error(E_NAME_TAKEN, "That room name is taken.")
        if len(self.rooms) >= MAX_ROOMS:
            return peer.error(E_LIMIT, "Server is full, try later.")
        room = Room(name, bool(public), host_name)
        room.members[HOST_NODE] = peer
        peer.room, peer.node = room, HOST_NODE
        self.rooms[room.key] = room
        log("room %r created (%s)" % (name, "public" if public else "private"))
        peer.send(S_CREATED, bytes([HOST_NODE]))

    def on_join(self, peer, reader):
        version = reader.u8()
        name = clean_text(reader.string(), ROOM_NAME_MAX)
        if version != PROTOCOL_VERSION:
            return peer.error(E_VERSION, "Server and game versions differ.")
        if peer.room:
            return peer.error(E_BUSY, "Already in a room.")
        room = self.rooms.get(name.lower())
        if room is None:
            return peer.error(E_NO_ROOM, "No room with that name.")
        if room.state != STATE_LOBBY:
            return peer.error(E_STARTED, "That round already started.")
        node = room.free_node()
        if node is None:
            return peer.error(E_FULL, "That room is full.")
        room.members[node] = peer
        peer.room, peer.node = room, node
        log("player joined room %r as node %d" % (room.name, node))
        peer.send(S_JOINED, bytes([node]))

    def on_data(self, peer, reader):
        room = peer.room
        if room is None:
            return
        dst = reader.u8()
        payload = reader.rest()
        if not payload:
            return
        out = bytes([peer.node]) + payload
        if peer.node == HOST_NODE:
            if payload[0] == PKT_WORLD and len(payload) > 1:
                room.state = payload[1]
            if dst == BROADCAST:
                for node, other in list(room.members.items()):
                    if node != HOST_NODE:
                        other.send(S_DATA, out)
            else:
                other = room.members.get(dst)
                if other:
                    other.send(S_DATA, out)
        else:
            host = room.members.get(HOST_NODE)
            if host:
                host.send(S_DATA, out)

    def dispatch(self, peer, mtype, body):
        reader = Reader(body)
        with self.lock:
            if mtype == C_DATA:
                return self.on_data(peer, reader)
            if mtype == C_LIST:
                self.on_list(peer)
            elif mtype == C_CREATE:
                self.on_create(peer, reader)
            elif mtype == C_JOIN:
                self.on_join(peer, reader)
            elif mtype == C_LEAVE:
                self.leave_room(peer)
            else:
                raise ValueError("unknown message type %d" % mtype)

    def serve(self, transport):
        peer = Peer(transport)
        log("browser connected from %s" % (transport.addr[0],))
        buffer = b""
        try:
            while not peer.closed:
                chunk = transport.read()
                if not chunk:
                    break
                buffer += chunk
                while len(buffer) >= 2:
                    length = struct.unpack("<H", buffer[:2])[0]
                    if length < 1 or length > MAX_FRAME:
                        raise ValueError("bad frame length %d" % length)
                    if len(buffer) < 2 + length:
                        break
                    frame = buffer[2:2 + length]
                    buffer = buffer[2 + length:]
                    try:
                        self.dispatch(peer, frame[0], frame[1:])
                    except ValueError as exc:
                        log("bad request: %s" % exc)
                        peer.error(E_BAD_REQUEST, "Bad request.")
        except (OSError, ValueError):
            pass
        finally:
            with self.lock:
                self.leave_room(peer)
            peer.closed = True
            transport.close()


def make_handler(relay, game_path):
    from http.server import BaseHTTPRequestHandler

    class Handler(BaseHTTPRequestHandler):
        protocol_version = "HTTP/1.1"
        server_version = "BlockfallLAN/1"

        def log_message(self, fmt, *args):
            return

        def do_GET(self):
            path = self.path.split("?", 1)[0]
            if path == WS_PATH:
                return self.handle_websocket()
            if path in ("/", "/index.html", "/play", "/play/", "/blockfall.html",
                        "/play/blockfall.html"):
                return self.send_file(game_path, "text/html; charset=utf-8")
            if path.endswith(".wasm"):
                return self.send_file(game_path.replace(".html", ".wasm"),
                                      "application/wasm")
            if path == "/health":
                return self.send_bytes(b"ok", "text/plain")
            self.send_bytes(b"Not found", "text/plain", status=404)

        def send_file(self, file_path, content_type):
            try:
                with open(file_path, "rb") as handle:
                    body = handle.read()
            except OSError:
                self.send_bytes(
                    ("Could not read %s. Put it next to this script.\n"
                     % os.path.basename(file_path)).encode(),
                    "text/plain", status=500)
                return
            self.send_bytes(body, content_type)

        def send_bytes(self, body, content_type, status=200):
            self.send_response(status)
            self.send_header("Content-Type", content_type)
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            try:
                self.wfile.write(body)
            except OSError:
                pass

        def handle_websocket(self):
            key = self.headers.get("Sec-WebSocket-Key")
            if not key:
                self.send_bytes(b"Expected a WebSocket upgrade", "text/plain", 400)
                return
            accept = base64.b64encode(
                hashlib.sha1((key + WS_GUID).encode()).digest()).decode()
            self.send_response(101, "Switching Protocols")
            self.send_header("Upgrade", "websocket")
            self.send_header("Connection", "Upgrade")
            self.send_header("Sec-WebSocket-Accept", accept)
            self.end_headers()
            self.wfile.flush()
            self.close_connection = True
            transport = WsTransport(self.connection, self.client_address, self.rfile)
            relay.serve(transport)

    return Handler


def lan_addresses():
    found = []
    try:
        hostname = socket.gethostname()
        for info in socket.getaddrinfo(hostname, None, socket.AF_INET):
            ip = info[4][0]
            if not ip.startswith("127.") and ip not in found:
                found.append(ip)
    except OSError:
        pass
    if not found:
        try:
            probe = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            probe.connect(("8.8.8.8", 80))
            found.append(probe.getsockname()[0])
            probe.close()
        except OSError:
            pass
    return found


def main():
    from http.server import ThreadingHTTPServer

    parser = argparse.ArgumentParser(description="Blockfall same-wifi relay (browsers)")
    parser.add_argument("--host", default="0.0.0.0", help="bind address (default 0.0.0.0)")
    parser.add_argument("--port", type=int, default=8080,
                        help="HTTP + WebSocket port (default 8080)")
    parser.add_argument("--game", default=GAME_FILE,
                        help="path to blockfall.html (default next to this script)")
    args = parser.parse_args()

    game_path = args.game
    if not os.path.isabs(game_path):
        game_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), game_path)
    if not os.path.exists(game_path):
        print("Blockfall HTML not found at:\n  %s" % game_path, file=sys.stderr)
        print("Download it from the site's /play page and put it next to this "
              "script, or pass --game.", file=sys.stderr)
        return 1

    relay = Relay()
    httpd = ThreadingHTTPServer((args.host, args.port), make_handler(relay, game_path))
    httpd.daemon_threads = True

    print("")
    print("  BLOCKFALL  same-wifi relay  (browser players)")
    print("  ---------------------------------------------")
    print("  Everyone on this wifi opens:")
    for ip in lan_addresses() or ["<this machine's ip>"]:
        print("      http://%s:%d" % (ip, args.port))
    print("  ---------------------------------------------")
    print("  Rooms are shared by every browser that opens that address.")
    print("  Ctrl+C to stop.")
    print("")

    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        print("\nstopping")
    finally:
        httpd.server_close()
    return 0


if __name__ == "__main__":
    sys.exit(main())
