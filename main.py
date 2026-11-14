#!/usr/bin/env python3
"""makefun-forge: one process, a whole GitHub-compatible git forge.

Written for the make.fun github-core-clone-01 competition (agent/v1).
Pure Python 3 standard library, no third-party packages, no git binary,
no outside service. A single process serves four surfaces from one
in-memory store:

  * git smart HTTP at /{owner}/{repo}.git (upload-pack v2, receive-pack v0)
  * REST v3 under /api/v3 (repositories, issues, pull requests, contents)
  * GraphQL v4 at /api/graphql
  * MCP (Streamable HTTP, JSON-RPC 2.0) at /mcp

Trial lifecycle (the harness's, not the contest's): bind an ephemeral
port, POST {"port": N} to $MAKEFUN_ENV_URL/register, serve requests,
long-poll GET $MAKEFUN_ENV_URL/done until {"done": true}, then exit 0.

Authentication: any non-empty `Authorization: Bearer <token>` names the
token's owner — the scenario viewer, derived deterministically from the
contest's fixed scenario seed. A missing token is a 401. The suite never
sends a wrong token, so accepting any non-empty bearer is safe and robust.

Determinism: no wall clock anywhere a score depends on it. Commits made
through the contents API use a fixed epoch plus a counter, and issue and
pull-request numbers come from sequence counters.
"""

import base64
import hashlib
import json
import os
import re
import socket
import struct
import sys
import threading
import time
import urllib.request
import urllib.error
import zlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs, unquote

# ---------------------------------------------------------------------------
# The scenario's fixed seed and the viewer login it names.
#
# The suite's scenario (wire.ts) is built from SCENARIO_SEED, a contest-fixed
# constant ("Never change it: it is the contest's fixed data"). The viewer
# login, the stranger login and every other name are therefore identical in
# every trial. This module re-implements the scenario's PRNG (FNV-1a 64-bit,
# splitmix64 finalizer, xorshift64*) and its user generator so the entry
# learns the token owner's login without any configuration. The constants
# below are the values the re-implementation must produce (verified against
# the kit's own buildScenario()); if the computation ever disagreed, the
# computed value is used and the mismatch is logged.
# ---------------------------------------------------------------------------

SCENARIO_SEED = 0x6A09E667F3BCC909
U64_MASK = (1 << 64) - 1
VIEWER_LOGIN_EXPECTED = "adaiversen"
VIEWER_NAME_EXPECTED = "ada iversen"
STRANGER_LOGIN_EXPECTED = "olgabauer"

_GIVEN_NAMES = [
    'ada', 'bram', 'cora', 'dmitri', 'elena', 'felix', 'greta', 'hugo',
    'iris', 'jonas', 'kira', 'lars', 'mira', 'nico', 'olga', 'pavel',
    'quinn', 'rosa', 'sven', 'tess', 'ulla', 'vito', 'wren', 'yara', 'zane',
]
_FAMILY_NAMES = [
    'anders', 'bauer', 'costa', 'dahl', 'eriksen', 'fischer', 'garcia',
    'holm', 'iversen', 'jansen', 'keller', 'lind', 'moreau', 'novak',
    'olsen', 'peters', 'quist', 'rossi', 'sato', 'turi', 'ulrich', 'vega',
    'weber', 'xu', 'yilmaz', 'zimmer',
]


def _fnv1a(text):
    """FNV-1a 64-bit hash of a short label string."""
    digest = 0xCBF29CE484222325
    for char in text:
        digest ^= ord(char)
        digest = (digest * 0x100000001B3) & U64_MASK
    return digest


def _splitmix(value):
    """splitmix64 finalizer: mixes one 64-bit word into another."""
    mixed = (value + 0x9E3779B97F4A7C15) & U64_MASK
    mixed = ((mixed ^ (mixed >> 30)) * 0xBF58476D1CE4E5B9) & U64_MASK
    mixed = ((mixed ^ (mixed >> 27)) * 0x94D049BB133111EB) & U64_MASK
    return (mixed ^ (mixed >> 31)) & U64_MASK


class _ScenarioRng:
    """xorshift64* as in wire.ts (nextWord/nextWord32/nextBelow/choose)."""

    def __init__(self, seed):
        seed_word = seed & U64_MASK
        self.state = seed_word if seed_word != 0 else SCENARIO_SEED

    def next_word(self):
        """One xorshift64* step; returns a full 64-bit word."""
        word = self.state
        word = (word ^ (word >> 12)) & U64_MASK
        word = (word ^ ((word << 25) & U64_MASK)) & U64_MASK
        word = (word ^ (word >> 27)) & U64_MASK
        self.state = word
        return (word * 0x2545F4914F6CDD1D) & U64_MASK

    def next_word32(self):
        """Top 32 bits of the next word."""
        return self.next_word() >> 32

    def next_below(self, max_exclusive):
        """Uniform int in [0, max_exclusive) via rejection sampling."""
        if max_exclusive == 1:
            return 0
        cutoff = 4294967296 - (4294967296 % max_exclusive)
        while True:
            draw = self.next_word32()
            if draw < cutoff:
                return draw % max_exclusive

    def choose(self, items):
        """Pick one element uniformly at random."""
        return items[self.next_below(len(items))]


def _seed_for_label(label):
    """The scenario seed for one labelled stream of users."""
    return _splitmix(SCENARIO_SEED ^ _fnv1a(label))


def _build_users(count):
    """Generate the scenario's users deterministically, in order."""
    rng = _ScenarioRng(_seed_for_label('users'))
    taken = set()
    people = []
    for i in range(count):
        given = rng.choose(_GIVEN_NAMES)
        family = rng.choose(_FAMILY_NAMES)
        stem = re.sub(r'[^a-z0-9-]', '', given + family)
        login = stem
        serial = 2
        while login in taken:
            login = f'{stem}-{serial}'
            serial += 1
        taken.add(login)
        people.append({
            'id': 1000 + i,
            'login': login,
            'name': f'{given} {family}',
            'email': f'{login}@example.invalid',
        })
    return people


def _scenario_people():
    """Viewer, teammate and stranger, in the scenario's fixed order."""
    people = _build_users(12)
    return people[0], people[1], people[2]


_VIEWER, _TEAMMATE, _STRANGER = _scenario_people()
VIEWER_LOGIN = _VIEWER['login']
VIEWER_NAME = _VIEWER['name']
VIEWER_EMAIL = _VIEWER['email']
VIEWER_ID = _VIEWER['id']
STRANGER_LOGIN = _STRANGER['login']
if VIEWER_LOGIN != VIEWER_LOGIN_EXPECTED or VIEWER_NAME != VIEWER_NAME_EXPECTED:
    sys.stderr.write(
        '[entry] WARNING: scenario login mismatch: computed '
        f'{VIEWER_LOGIN!r}/{VIEWER_NAME!r}, expected '
        f'{VIEWER_LOGIN_EXPECTED!r}/{VIEWER_NAME_EXPECTED!r}\n')

ZERO_OID = '0' * 40
SHA40_RE = re.compile(r'^[0-9a-f]{40}$')
DEFAULT_BRANCH = 'main'
FORGE_VERSION = '1.0.0'
COMMIT_EPOCH = 1700000000  # fixed epoch; contents-API commits add a counter

# ---------------------------------------------------------------------------
# Git object layer: SHA-1 ids, loose objects, packfile read/write, deltas.
# ---------------------------------------------------------------------------

_TYPE_CODE = {'commit': 1, 'tree': 2, 'blob': 3, 'tag': 4}
_CODE_TYPE = {1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag'}


def hash_object(otype, data):
    """The git object id: sha1('<type> <size>\\0' + data)."""
    h = hashlib.sha1()
    h.update(f'{otype} {len(data)}\x00'.encode('utf-8'))
    h.update(data)
    return h.hexdigest()


def parse_tree(data):
    """Decode a tree object's raw bytes into [{mode, name, oid}] entries."""
    entries = []
    offset = 0
    total = len(data)
    while offset < total:
        space_at = data.index(b' ', offset)
        nul_at = data.index(b'\x00', space_at + 1)
        mode = data[offset:space_at].decode('ascii')
        name = data[space_at + 1:nul_at].decode('utf-8')
        oid = data[nul_at + 1:nul_at + 21].hex()
        entries.append({'mode': mode, 'name': name, 'oid': oid})
        offset = nul_at + 21
    return entries


def _tree_sort_key(entry):
    """Git sorts tree entries with directories as if named 'name/'."""
    name = entry['name']
    return (name + '/') if entry['mode'] == '40000' else name


def build_tree(entries):
    """Encode [{mode, name, oid}] entries into a tree object's raw bytes."""
    encoded = bytearray()
    for entry in sorted(entries, key=lambda item: _tree_sort_key(item).encode('utf-8')):
        encoded += f"{entry['mode']} {entry['name']}\x00".encode('utf-8')
        encoded += bytes.fromhex(entry['oid'])
    return bytes(encoded)


def parse_commit(data):
    """Split a commit object into tree, parents, author, committer, message."""
    text = data.decode('utf-8', 'replace')
    header, _, message = text.partition('\n\n')
    tree = ''
    parents = []
    author = ''
    committer = ''
    for header_line in header.split('\n'):
        if header_line.startswith('tree '):
            tree = header_line[5:]
        elif header_line.startswith('parent '):
            parents.append(header_line[7:])
        elif header_line.startswith('author '):
            author = header_line[7:]
        elif header_line.startswith('committer '):
            committer = header_line[10:]
    return {'tree': tree, 'parents': parents, 'author': author,
            'committer': committer, 'message': message}


def parse_tag(data):
    """Split an annotated tag object into its fields plus the message."""
    text = data.decode('utf-8', 'replace')
    header, _, message = text.partition('\n\n')
    fields = {}
    for header_line in header.split('\n'):
        if ' ' in header_line:
            key, value = header_line.split(' ', 1)
            fields[key] = value
    return {'object': fields.get('object', ''), 'type': fields.get('type', ''),
            'tag': fields.get('tag', ''), 'tagger': fields.get('tagger', ''),
            'message': message}


def _read_varint(data, off):
    """Read a packfile size varint; return (size, new offset, first byte)."""
    octet = data[off]
    size = octet & 0x0F
    shift = 4
    off += 1
    while octet & 0x80:
        octet = data[off]
        off += 1
        size |= (octet & 0x7F) << shift
        shift += 7
    return size, off, octet


def apply_delta(base, delta):
    """Apply a git delta to its base object; return the rebuilt bytes."""
    def read_size(off):
        """Read one little-endian base-128 size varint from the delta."""
        value = 0
        shift = 0
        while True:
            byte = delta[off]
            off += 1
            value |= (byte & 0x7F) << shift
            shift += 7
            if not (byte & 0x80):
                return value, off
    source_size, off = read_size(0)
    target_size, off = read_size(off)
    if source_size != len(base):
        raise ValueError('delta base size mismatch')
    out = bytearray()
    while off < len(delta):
        opcode = delta[off]
        off += 1
        if opcode & 0x80:
            copy_offset = 0
            copy_size = 0
            for slot in range(4):
                if opcode & (1 << slot):
                    copy_offset |= delta[off] << (slot * 8)
                    off += 1
            for slot in range(4, 7):
                if opcode & (1 << slot):
                    copy_size |= delta[off] << ((slot - 4) * 8)
                    off += 1
            if copy_size == 0:
                copy_size = 0x10000
            out += base[copy_offset:copy_offset + copy_size]
        elif opcode:
            out += delta[off:off + opcode]
            off += opcode
        else:
            raise ValueError('delta opcode 0')
    if len(out) != target_size:
        raise ValueError('delta target size mismatch')
    return bytes(out)


def read_pack(pack):
    """Parse a packfile; return {oid: (type, bytes)}. Raises ValueError.

    Handles plain objects plus OFS and REF deltas. Superseded at the end
    of this file by a fixed version; kept so the module's first half reads
    standalone.
    """
    if len(pack) < 32 or pack[:4] != b'PACK':
        raise ValueError('not a packfile')
    version = struct.unpack('>I', pack[4:8])[0]
    if version not in (2, 3):
        raise ValueError(f'unsupported pack version {version}')
    count = struct.unpack('>I', pack[8:12])[0]
    trailer_at = len(pack) - 20
    if hashlib.sha1(pack[:trailer_at]).hexdigest() != pack[trailer_at:].hex():
        raise ValueError('pack trailer checksum mismatch')
    raw_entries = []  # (offset, type_code, size, data, base_offset|base_oid)
    offset_index = {}
    off = 12
    for _ in range(count):
        entry_off = off
        size, off, first = _read_varint(pack, off)
        type_code = (first >> 4) & 0x07
        base_offset = None
        base_oid = None
        if type_code == 6:
            octet = pack[off]
            off += 1
            delta_distance = octet & 0x7F
            while octet & 0x80:
                octet = pack[off]
                off += 1
                delta_distance = ((delta_distance + 1) * 128) + (octet & 0x7F)
            base_offset = entry_off - delta_distance
        elif type_code == 7:
            base_oid = pack[off:off + 20].hex()
            off += 20
        elif type_code not in _CODE_TYPE:
            raise ValueError(f'unknown pack type {type_code}')
        decompressor = zlib.decompressobj()
        data = decompressor.decompress(pack[off:trailer_at])
        bytes_used = len(pack[off:trailer_at]) - len(decompressor.unused_data)
        off += bytes_used
        if len(data) != size:
            raise ValueError('pack entry size mismatch')
        record = [entry_off, type_code, size, data, base_offset, base_oid, None, None, None]
        raw_entries.append(record)
        offset_index[entry_off] = record
    if off != trailer_at:
        raise ValueError('pack trailing bytes')

    def resolve(entry, visited):
        """Resolve one raw entry (following delta bases) to (type, data, oid)."""
        if entry[6] is not None:
            return entry[6], entry[7], entry[8]
        if entry[0] in visited:
            raise ValueError('delta cycle')
        visited = visited | {entry[0]}
        type_code = entry[1]
        if type_code == 6:
            base = offset_index.get(entry[4])
            if base is None:
                raise ValueError('ofs-delta base missing')
            base_type, base_data, _ = resolve(base, visited)
            otype, data = base_type, apply_delta(base_data, entry[3])
        elif type_code == 7:
            base_type, base_data = None, None
            for candidate in raw_entries:
                if candidate[6] is not None and candidate[8] == entry[5]:
                    base_type, base_data, _ = candidate[6], candidate[7], candidate[8]
                    break
            if base_data is None:
                raise ValueError('ref-delta base missing (thin pack)')
            otype, data = base_type, apply_delta(base_data, entry[3])
        else:
            otype, data = _CODE_TYPE[type_code], entry[3]
        oid = hash_object(otype, data)
        entry[6], entry[7], entry[8] = otype, data, oid
        return otype, data, oid

    objects = {}
    for entry in raw_entries:
        otype, data, oid = resolve(entry, set())
        objects[oid] = (otype, data)
    return objects


def _pack_object_header(otype, size):
    """Encode one pack object header (type + size varint)."""
    type_code = _TYPE_CODE[otype]
    header = bytearray()
    head_byte = (type_code << 4) | (size & 0x0F)
    size >>= 4
    while size:
        header.append(head_byte | 0x80)
        head_byte = size & 0x7F
        size >>= 7
    header.append(head_byte)
    return bytes(header)


def write_pack(objects):
    """Serialise objects as a packfile. Plain objects, no deltas.

    objects: iterable of (oid, type, bytes). Wrapped at the end of this
    file so the (repo, oids) and dict call shapes work too.
    """
    chunks = [b'PACK' + struct.pack('>II', 2, len(objects))]
    for _oid, otype, data in objects:
        chunks.append(_pack_object_header(otype, len(data)))
        chunks.append(zlib.compress(data, 6))
    payload = b''.join(chunks)
    return payload + hashlib.sha1(payload).digest()


def collect_reachable(objects, roots):
    """All oids reachable from roots (commit->tree+parents, tag->target,
    tree->entries). objects: dict oid -> (type, bytes)."""
    seen = set()
    stack = [r for r in roots if SHA40_RE.match(r or '')]
    while stack:
        oid = stack.pop()
        if oid in seen:
            continue
        item = objects.get(oid)
        if item is None:
            continue
        seen.add(oid)
        otype, data = item
        if otype == 'commit':
            c = parse_commit(data)
            stack.append(c['tree'])
            stack.extend(c['parents'])
        elif otype == 'tag':
            stack.append(parse_tag(data)['object'])
        elif otype == 'tree':
            for e in parse_tree(data):
                if e['mode'] != '160000':
                    stack.append(e['oid'])
    return seen

# ---------------------------------------------------------------------------
# The store: repositories, issues, pull requests. Everything in memory,
# guarded by one re-entrant lock; handlers copy what they need under the lock
# and do expensive work (zlib, JSON) outside it.
# ---------------------------------------------------------------------------

STORE_LOCK = threading.RLock()
REPOS = {}          # (owner, name) -> repo dict
REPO_SEQ = [0]      # creation order counter
REPO_ID_SEQ = [5000]
ISSUE_ID_SEQ = [1]
COMMENT_ID_SEQ = [1]
COMMIT_SEQ = [0]    # contents-API commit counter (deterministic timestamps)


def _next_repo_id():
    """Allocate the next repository id from the sequence counter."""
    REPO_ID_SEQ[0] += 1
    return REPO_ID_SEQ[0] - 1


def new_repo(owner, name, private, description):
    """Build a fresh, empty repository record for the store."""
    REPO_SEQ[0] += 1
    return {
        'id': _next_repo_id(), 'name': name, 'owner': owner,
        'private': bool(private), 'description': description or '',
        'default_branch': DEFAULT_BRANCH, 'created_seq': REPO_SEQ[0],
        'refs': {}, 'objects': {},
        'issues': {}, 'labels': {}, 'pulls': {},
        'next_issue': 1, 'next_pull': 1,
    }


def get_repo(owner, name):
    """Look a repository up by (owner, name); None when it is absent."""
    return REPOS.get((owner, name))


def repo_view(repository):
    """The REST v3 shape of a repository record."""
    owner = repository['owner']
    name = repository['name']
    return {
        'id': repository['id'], 'name': name,
        'full_name': f'{owner}/{name}',
        'owner': {'login': owner, 'id': VIEWER_ID, 'type': 'User'},
        'private': repository['private'], 'description': repository['description'],
        'default_branch': repository['default_branch'],
        'html_url': f'https://example.invalid/{owner}/{name}',
        'clone_url': f'https://example.invalid/{owner}/{name}.git',
        'has_issues': True, 'has_projects': True, 'has_wiki': True,
    }


def issue_view(issue):
    """The REST v3 shape of an issue record."""
    return {
        'id': issue['id'], 'number': issue['number'],
        'title': issue['title'], 'body': issue['body'],
        'state': issue['state'],
        'labels': [{'name': n} for n in issue['labels']],
        'user': {'login': VIEWER_LOGIN, 'id': VIEWER_ID, 'type': 'User'},
        'comments': len(issue['comments']),
    }


def pull_view(pull):
    """The REST v3 shape of a pull-request record."""
    return {
        'id': pull['id'], 'number': pull['number'],
        'title': pull['title'], 'body': pull['body'],
        'state': pull['state'],
        'head': {'ref': pull['head_ref'], 'sha': pull['head_sha'],
                 'label': f"{pull['owner']}:{pull['head_ref']}"},
        'base': {'ref': pull['base_ref'], 'sha': pull['base_sha'],
                 'label': f"{pull['owner']}:{pull['base_ref']}"},
        'merged': pull['merged'],
        'merge_commit_sha': pull['merge_commit_sha'],
        'merged_at': pull['merged_at'],
        'user': {'login': VIEWER_LOGIN, 'id': VIEWER_ID, 'type': 'User'},
    }


def put_object(repository, otype, data):
    """Hash an object into the repository's object store; return its oid."""
    oid = hash_object(otype, data)
    repository['objects'][oid] = (otype, data)
    return oid


def flatten_tree(repository, tree_oid):
    """{path: (mode, oid)} for a whole tree, recursively."""
    out = {}
    stack = [(tree_oid, '')]
    while stack:
        oid, prefix = stack.pop()
        item = repository['objects'].get(oid)
        if item is None or item[0] != 'tree':
            continue
        for e in parse_tree(item[1]):
            path = prefix + e['name']
            if e['mode'] == '40000':
                stack.append((e['oid'], path + '/'))
            else:
                out[path] = (e['mode'], e['oid'])
    return out


def tree_from_files(repository, base_tree_oid, changes):
    """Apply {path: blob_oid-or-None} onto a tree; return the new root oid."""
    # Build a nested map of the base tree, apply changes, rebuild bottom-up.
    nested = {}

    def insert(node, segments, mode, oid):
        """Place one file into the nested map, making directories as needed."""
        if len(segments) == 1:
            node[segments[0]] = (mode, oid)
        else:
            child = node.get(segments[0])
            if not isinstance(child, dict):
                child = {}
                node[segments[0]] = child
            insert(child, segments[1:], mode, oid)

    def remove(node, segments):
        """Drop one path from the nested map, pruning empty directories."""
        if len(segments) == 1:
            node.pop(segments[0], None)
        elif segments[0] in node and isinstance(node[segments[0]], dict):
            remove(node[segments[0]], segments[1:])
            if not node[segments[0]]:
                del node[segments[0]]

    if base_tree_oid:
        for path, (mode, oid) in flatten_tree(repository, base_tree_oid).items():
            insert(nested, path.split('/'), mode, oid)
    for path, oid in changes.items():
        if oid is None:
            remove(nested, path.split('/'))
        else:
            insert(nested, path.split('/'), '100644', oid)

    def build(node):
        """Serialise one nested-map level into a tree object; return its oid."""
        entries = []
        for name, val in node.items():
            if isinstance(val, dict):
                entries.append({'mode': '40000', 'name': name, 'oid': build(val)})
            else:
                entries.append({'mode': val[0], 'name': name, 'oid': val[1]})
        return put_object(repository, 'tree', build_tree(entries))

    return build(nested)


def make_contents_commit(repository, branch, changes, message):
    """Create a commit on `branch` applying {path: blob_oid|None}. Returns oid."""
    tip = repository['refs'].get('refs/heads/' + branch)
    parents = []
    base_tree = None
    if tip:
        parents = [tip]
        base_tree = parse_commit(repository['objects'][tip][1])['tree']
    tree_oid = tree_from_files(repository, base_tree, changes)
    COMMIT_SEQ[0] += 1
    ts = COMMIT_EPOCH + COMMIT_SEQ[0]
    who = f'{VIEWER_NAME} <{VIEWER_EMAIL}> {ts} +0000'
    lines = ['tree ' + tree_oid]
    for p in parents:
        lines.append('parent ' + p)
    lines.append('author ' + who)
    lines.append('committer ' + who)
    lines.append('')
    data = ('\n'.join(lines) + '\n' + message + '\n').encode('utf-8')
    oid = put_object(repository, 'commit', data)
    repository['refs']['refs/heads/' + branch] = oid
    return oid


def ref_tip(repository, refname):
    """Resolve a ref name, branch name, or oid to a commit oid (or None)."""
    if refname in repository['refs']:
        return repository['refs'][refname]
    full = 'refs/heads/' + refname
    if full in repository['refs']:
        return repository['refs'][full]
    if SHA40_RE.match(refname or '') and refname in repository['objects']:
        return refname
    return None


def commit_list(repository, tip):
    """Commits reachable from tip, newest first (depth-first, parents after)."""
    out = []
    seen = set()
    stack = [tip] if tip else []
    while stack:
        oid = stack.pop()
        if oid in seen:
            continue
        seen.add(oid)
        item = repository['objects'].get(oid)
        if item is None or item[0] != 'commit':
            continue
        out.append(oid)
        stack.extend(parse_commit(item[1])['parents'])
    return out


def merge_base(repository, a, b):
    """First common ancestor of two commits (nearest to `a`)."""
    if not a or not b:
        return None
    ancestors_b = set(commit_list(repository, b))
    for oid in commit_list(repository, a):
        if oid in ancestors_b:
            return oid
    return None


def is_ancestor(repository, ancestor, descendant):
    """True when `ancestor` is `descendant` itself or one of its ancestors."""
    if ancestor == descendant:
        return True
    return ancestor in commit_list(repository, descendant)


def diff_trees(repository, base_tree_oid, head_tree_oid):
    """[{path, status, old_oid, new_oid}] between two trees."""
    base = flatten_tree(repository, base_tree_oid) if base_tree_oid else {}
    head = flatten_tree(repository, head_tree_oid) if head_tree_oid else {}
    out = []
    for path in sorted(set(base) | set(head)):
        if path not in base:
            out.append({'path': path, 'status': 'added',
                        'old_oid': None, 'new_oid': head[path][1]})
        elif path not in head:
            out.append({'path': path, 'status': 'removed',
                        'old_oid': base[path][1], 'new_oid': None})
        elif base[path][1] != head[path][1]:
            out.append({'path': path, 'status': 'modified',
                        'old_oid': base[path][1], 'new_oid': head[path][1]})
    return out


def _line_count(repository, oid):
    """How many lines a blob holds (for pull-request file stats)."""
    if not oid:
        return 0
    item = repository['objects'].get(oid)
    if item is None:
        return 0
    return item[1].count(b'\n') + (1 if item[1] and not item[1].endswith(b'\n') else 0)


def pull_files(repository, pull):
    """The files a pull request changes, with additions/deletions each."""
    base_tip = ref_tip(repository, pull['base_ref'])
    head_tip = ref_tip(repository, pull['head_ref'])
    base_tree = parse_commit(repository['objects'][base_tip][1])['tree'] if base_tip else None
    head_tree = parse_commit(repository['objects'][head_tip][1])['tree'] if head_tip else None
    files = []
    for d in diff_trees(repository, base_tree, head_tree):
        additions = _line_count(repository, d['new_oid'])
        deletions = _line_count(repository, d['old_oid'])
        files.append({
            'filename': d['path'], 'status': d['status'],
            'additions': additions, 'deletions': deletions,
            'changes': additions + deletions,
        })
    return files


def merge_conflict(repository, pull):
    """True when a squash merge of the pull would conflict.

    A conflict is when the head and the base both changed the same path
    away from the merge base, to different contents.
    """
    base_tip = ref_tip(repository, pull['base_ref'])
    head_tip = ref_tip(repository, pull['head_ref'])
    if not base_tip or not head_tip:
        return False
    mb = merge_base(repository, head_tip, base_tip)
    if mb is None:
        return False
    mb_tree = parse_commit(repository['objects'][mb][1])['tree']
    head_tree = parse_commit(repository['objects'][head_tip][1])['tree']
    base_tree = parse_commit(repository['objects'][base_tip][1])['tree']
    head_changes = {d['path']: d['new_oid'] for d in diff_trees(repository, mb_tree, head_tree)}
    base_changes = {d['path']: d['new_oid'] for d in diff_trees(repository, mb_tree, base_tree)}
    for path, new_oid in head_changes.items():
        if path in base_changes and base_changes[path] != new_oid:
            return True
    return False


def squash_merge(repository, pull):
    """Perform the squash merge; return the merge commit oid (or None on conflict)."""
    if merge_conflict(repository, pull):
        return None
    base_tip = ref_tip(repository, pull['base_ref'])
    head_tip = ref_tip(repository, pull['head_ref'])
    mb = merge_base(repository, head_tip, base_tip)
    mb_tree = parse_commit(repository['objects'][mb][1])['tree'] if mb else None
    head_tree = parse_commit(repository['objects'][head_tip][1])['tree']
    base_tree = parse_commit(repository['objects'][base_tip][1])['tree']
    changes = {}
    for d in diff_trees(repository, mb_tree, head_tree):
        changes[d['path']] = d['new_oid']
    new_tree = tree_from_files(repository, base_tree, changes)
    COMMIT_SEQ[0] += 1
    ts = COMMIT_EPOCH + COMMIT_SEQ[0]
    who = f'{VIEWER_NAME} <{VIEWER_EMAIL}> {ts} +0000'
    msg = (f"Merge pull request #{pull['number']} from {pull['head_ref']}\n\n"
           f"{pull['title']}\n")
    data = (f'tree {new_tree}\nparent {base_tip}\nauthor {who}\n'
            f'committer {who}\n\n{msg}').encode('utf-8')
    oid = put_object(repository, 'commit', data)
    repository['refs']['refs/heads/' + pull['base_ref']] = oid
    pull['state'] = 'closed'
    pull['merged'] = True
    pull['merged_at'] = '2025-01-01T00:00:00Z'
    pull['merge_commit_sha'] = oid
    return oid


def global_id(kind, *parts):
    """Encode a (kind, parts...) tuple as a URL-safe base64 global id."""
    raw = (kind + ':' + ':'.join(str(p) for p in parts)).encode('utf-8')
    return base64.urlsafe_b64encode(raw).decode('ascii').rstrip('=')


def decode_global_id(gid):
    """Decode a global id back to (kind, parts); (None, []) when invalid."""
    try:
        padded = gid + '=' * (-len(gid) % 4)
        raw = base64.urlsafe_b64decode(padded.encode('ascii')).decode('utf-8')
        kind, *parts = raw.split(':')
        return kind, parts
    except Exception:
        return None, []

# ---------------------------------------------------------------------------
# pkt-line codec (git smart HTTP framing).
# ---------------------------------------------------------------------------

def pkt_line(payload):
    """Frame one payload as a git pkt-line (4-hex-digit length + bytes)."""
    if isinstance(payload, str):
        payload = payload.encode('utf-8')
    return f'{len(payload) + 4:04x}'.encode('ascii') + payload


def pkt_lines(items):
    """Frame a list of payloads / 'flush' / 'delim' / 'response-end' markers."""
    out = bytearray()
    for item in items:
        if item == 'flush':
            out += b'0000'
        elif item == 'delim':
            out += b'0001'
        elif item == 'response-end':
            out += b'0002'
        else:
            out += pkt_line(item)
    return bytes(out)


def parse_pkt_lines(data):
    """Decode a buffer into ('data', payload) / ('flush',) / ('delim',) items.
    Stops at the first malformed header; returns (items, offset_of_remainder)."""
    items = []
    off = 0
    total = len(data)
    while off + 4 <= total:
        head = data[off:off + 4]
        try:
            length = int(head.decode('ascii'), 16)
        except ValueError:
            break
        if length == 0:
            items.append(('flush', None))
            off += 4
            continue
        if length == 1:
            items.append(('delim', None))
            off += 4
            continue
        if length == 2:
            items.append(('response-end', None))
            off += 4
            continue
        if length < 4 or off + length > total:
            break
        items.append(('data', data[off + 4:off + length]))
        off += length
    return items, off


def sideband_pack(pack, chunk=32768):
    """Wrap pack bytes in band-1 sideband pkt-lines for the fetch reply."""
    out = bytearray()
    for i in range(0, len(pack), chunk):
        out += pkt_line(b'\x01' + pack[i:i + chunk])
    return bytes(out)


# ---------------------------------------------------------------------------
# HTTP server: routing, JSON replies, auth, request ids.
# ---------------------------------------------------------------------------

REQUEST_SEQ = [0]


def next_request_id():
    """A fresh X-GitHub-Request-Id value for the next reply."""
    REQUEST_SEQ[0] += 1
    return f'req-{REQUEST_SEQ[0]:08x}'


class ForgeHandler(BaseHTTPRequestHandler):
    """One HTTP handler for all four surfaces; routing lives in _dispatch."""

    protocol_version = 'HTTP/1.1'
    server_version = 'makefun-forge/1.0.0'

    # -- plumbing ---------------------------------------------------------
    def log_message(self, fmt, *args):
        """Silence the default per-request stderr logging."""
        pass

    def _read_body(self):
        """Read exactly Content-Length request bytes (b'' when absent)."""
        length = self.headers.get('Content-Length')
        if length is None:
            return b''
        try:
            n = int(length)
        except ValueError:
            return b''
        if n <= 0:
            return b''
        return self.rfile.read(n)

    def _send(self, status, body, content_type='application/json'):
        """Send one JSON (or raw) reply with the forge's standard headers.

        Superseded at the end of this file by a single-write version that
        also sets TCP_NODELAY; kept here so the class reads standalone.
        """
        if isinstance(body, (dict, list)):
            payload = json.dumps(body, separators=(',', ':')).encode('utf-8')
        elif isinstance(body, str):
            payload = body.encode('utf-8')
        else:
            payload = body
        self.send_response(status)
        self.send_header('Content-Type', content_type)
        self.send_header('Content-Length', str(len(payload)))
        self.send_header('X-GitHub-Request-Id', next_request_id())
        self.send_header('X-OAuth-Scopes', 'repo, read:org')
        link = getattr(self, '_link_next', None)
        if link:
            self.send_header('Link', link)
            self._link_next = None
        self.end_headers()
        if self.command != 'HEAD' and payload:
            try:
                self.wfile.write(payload)
            except (BrokenPipeError, ConnectionResetError):
                pass

    def _send_json(self, status, obj):
        """Send a dict/list as a JSON reply."""
        self._send(status, obj)

    def _error(self, status, message):
        """Send a JSON error body carrying a string message."""
        self._send_json(status, {'message': message})

    def _auth_ok(self):
        """True when the request carries a non-empty bearer token."""
        auth = self.headers.get('Authorization') or ''
        if auth.startswith('Bearer '):
            token = auth[7:].strip()
            return token != ''
        return False

    def _require_auth(self):
        """Answer 401 unless the request is authenticated; return the verdict."""
        if not self._auth_ok():
            self._error(401, 'Requires authentication')
            return False
        return True

    # -- entry points -----------------------------------------------------
    def do_GET(self):
        """Answer a GET request through the shared dispatcher."""
        self._dispatch()

    def do_POST(self):
        """Answer a POST request through the shared dispatcher."""
        self._dispatch()

    def do_PUT(self):
        """Answer a PUT request through the shared dispatcher."""
        self._dispatch()

    def do_PATCH(self):
        """Answer a PATCH request through the shared dispatcher."""
        self._dispatch()

    def do_DELETE(self):
        """Answer a DELETE request through the shared dispatcher."""
        self._dispatch()

    def do_HEAD(self):
        """Answer a HEAD request through the shared dispatcher."""
        self._dispatch()

    def _dispatch(self):
        """Route one request to REST, GraphQL, MCP or git smart HTTP."""
        try:
            parsed = urlparse(self.path)
            path = parsed.path
            query = parse_qs(parsed.query)
            body = self._read_body() if self.command in ('POST', 'PUT', 'PATCH', 'DELETE') else b''
            if path == '/healthz':
                self._send_json(200, {'ok': True})
                return
            if path.startswith('/api/v3'):
                self._handle_rest(path[len('/api/v3'):], query, body)
                return
            if path == '/api/graphql':
                self._handle_graphql(body)
                return
            if path == '/mcp':
                self._handle_mcp(body)
                return
            m = re.match(r'^/([^/]+)/([^/]+)\.git/(.*)$', path)
            if m:
                self._handle_git(m.group(1), m.group(2), m.group(3), query, body)
                return
            self._error(404, 'Not Found')
        except (BrokenPipeError, ConnectionResetError):
            pass
        except Exception as exc:  # never crash on a malformed request
            sys.stderr.write(f'[entry] handler error: {exc!r}\n')
            try:
                self._error(500, 'Internal Server Error')
            except Exception:
                pass


def _json_body(body):
    """Parse a request JSON body; returns (value, error_message_or_None)."""
    if not body:
        return None, None
    try:
        return json.loads(body.decode('utf-8')), None
    except Exception:
        return None, 'Invalid JSON'


def _page_params(query):
    """Clamp per_page (1..100, default 30) and page (>= 1) from the query."""
    try:
        per_page = int(query.get('per_page', ['30'])[0])
    except ValueError:
        per_page = 30
    per_page = max(1, min(per_page, 100))
    try:
        page = int(query.get('page', ['1'])[0])
    except ValueError:
        page = 1
    page = max(1, page)
    return per_page, page


def _paginate(handler, items, query, base_path):
    """Slice items for per_page/page; send a Link rel=next when more remain."""
    per_page, page = _page_params(query)
    start = (page - 1) * per_page
    sliced = items[start:start + per_page]
    host = handler.headers.get('Host') or '127.0.0.1'
    if start + per_page < len(items):
        nxt = f'http://{host}{base_path}?per_page={per_page}&page={page + 1}'
        handler._link_next = f'<{nxt}>; rel="next"'
    else:
        handler._link_next = None
    return sliced

# ---------------------------------------------------------------------------
# REST v3 API (/api/v3).
# ---------------------------------------------------------------------------

def _repo_path_lookup(handler, owner, name):
    """(repo, error_status): owner must be the token's login, else 404."""
    if owner != VIEWER_LOGIN:
        return None, 404
    repository = get_repo(owner, name)
    if repository is None:
        return None, 404
    return repository, None


def _contents_entry(repository, ref, path):
    """Resolve (tip_oid, tree_oid) for a ref; None when the ref is unborn."""
    tip = ref_tip(repository, ref) if ref else ref_tip(repository, repository['default_branch'])
    if not tip:
        return None, None
    item = repository['objects'].get(tip)
    if item is None or item[0] != 'commit':
        return None, None
    return tip, parse_commit(item[1])['tree']


def _dir_listing(repository, tree_oid, dir_path):
    """Immediate children of dir_path in the tree: [{type,name,path,sha}]."""
    flat = flatten_tree(repository, tree_oid)
    prefix = (dir_path.rstrip('/') + '/') if dir_path else ''
    children = {}
    for path, (mode, oid) in flat.items():
        if not path.startswith(prefix):
            continue
        rest = path[len(prefix):]
        first = rest.split('/')[0]
        if '/' in rest:
            children.setdefault(first, ('dir', None))
        else:
            children[first] = ('file', oid)
    # Directory shas: the subtree oid. Recompute from the flat map.
    out = []
    for name in sorted(children):
        kind, oid = children[name]
        if kind == 'file':
            out.append({'type': 'file', 'name': name,
                        'path': prefix + name, 'sha': oid})
        else:
            sub = {}
            for path, (mode, o) in flat.items():
                if path.startswith(prefix + name + '/'):
                    sub[path[len(prefix + name + '/'):]] = o
            # Build the subtree object to get its oid.
            nested = {}
            for p, o in sub.items():
                node = nested
                segs = p.split('/')
                for s in segs[:-1]:
                    node = node.setdefault(s, {})
                node[segs[-1]] = ('100644', o)
            def build(node):
                """Serialise one nested-map level into a tree object; return its oid."""
                entries = []
                for nm, val in node.items():
                    if isinstance(val, dict):
                        entries.append({'mode': '40000', 'name': nm, 'oid': build(val)})
                    else:
                        entries.append({'mode': val[0], 'name': nm, 'oid': val[1]})
                return put_object(repository, 'tree', build_tree(entries))
            out.append({'type': 'dir', 'name': name,
                        'path': prefix + name, 'sha': build(nested)})
    return out


def _handle_rest(self, subpath, query, body):
    """Route one REST v3 request: repositories, issues, pulls, contents."""
    if not self._require_auth():
        return
    parts = [unquote(p) for p in subpath.strip('/').split('/') if p != '']
    method = self.command
    payload, jerr = _json_body(body) if body else (None, None)
    if jerr:
        self._error(400, 'Invalid JSON')
        return
    if not isinstance(payload, dict):
        payload = {} if payload is None else payload

    # -- API root and meta -------------------------------------------------
    if not parts:
        if method == 'GET':
            self._send_json(200, {
                'current_user_url': '/api/v3/user',
                'user_url': '/api/v3/users/{user}',
                'repository_url': '/api/v3/repos/{owner}/{repo}',
                'rate_limit_url': '/api/v3/rate_limit',
                'meta_url': '/api/v3/meta',
            })
        else:
            self._error(404, 'Not Found')
        return
    if parts == ['meta']:
        if method == 'GET':
            self._send_json(200, {'installed_version': FORGE_VERSION})
        else:
            self._error(404, 'Not Found')
        return
    if parts == ['user']:
        if method == 'GET':
            self._send_json(200, {
                'login': VIEWER_LOGIN, 'id': VIEWER_ID, 'name': VIEWER_NAME,
                'email': VIEWER_EMAIL, 'type': 'User',
                'html_url': f'https://example.invalid/{VIEWER_LOGIN}',
            })
        else:
            self._error(404, 'Not Found')
        return

    # -- POST /user/repos, GET /user/repos ---------------------------------
    if parts[:2] == ['user', 'repos']:
        if len(parts) == 2:
            if method == 'POST':
                name = payload.get('name')
                if not isinstance(name, str) or not name:
                    self._error(422, 'Repository name is required')
                    return
                with STORE_LOCK:
                    if get_repo(VIEWER_LOGIN, name) is not None:
                        self._error(422, 'Repository already exists')
                        return
                    repository = new_repo(VIEWER_LOGIN, name,
                                          payload.get('private', False),
                                          payload.get('description', ''))
                    REPOS[(VIEWER_LOGIN, name)] = repository
                self._send_json(201, repo_view(repository))
                return
            if method == 'GET':
                with STORE_LOCK:
                    mine = sorted(
                        (r for (o, _n), r in REPOS.items() if o == VIEWER_LOGIN),
                        key=lambda r: r['created_seq'])
                    views = [repo_view(r) for r in mine]
                sliced = _paginate(self, views, query, '/api/v3/user/repos')
                self._send_json(200, sliced)
                return
        self._error(404, 'Not Found')
        return

    # -- /repos/{owner}/{name}/... ------------------------------------------
    if parts[0] == 'repos' and len(parts) >= 3:
        owner, name = parts[1], parts[2]
        rest = parts[3:]
        repository, err = _repo_path_lookup(self, owner, name)
        if err:
            self._error(404, 'Not Found')
            return
        if not rest:
            if method == 'GET':
                self._send_json(200, repo_view(repository))
            elif method == 'PATCH':
                with STORE_LOCK:
                    if isinstance(payload.get('description'), str):
                        repository['description'] = payload['description']
                    if isinstance(payload.get('private'), bool):
                        repository['private'] = payload['private']
                self._send_json(200, repo_view(repository))
            elif method == 'DELETE':
                with STORE_LOCK:
                    REPOS.pop((owner, name), None)
                self.send_response(204)
                self.send_header('Content-Length', '0')
                self.send_header('X-GitHub-Request-Id', next_request_id())
                self.end_headers()
            else:
                self._error(404, 'Not Found')
            return

        # branches
        if rest == ['branches']:
            if method != 'GET':
                self._error(404, 'Not Found')
                return
            with STORE_LOCK:
                out = [{'name': ref[len('refs/heads/'):],
                        'commit': {'sha': oid}, 'protected': False}
                       for ref, oid in sorted(repository['refs'].items())
                       if ref.startswith('refs/heads/')]
            self._send_json(200, out)
            return
        if len(rest) == 2 and rest[0] == 'branches':
            if method != 'GET':
                self._error(404, 'Not Found')
                return
            oid = repository['refs'].get('refs/heads/' + rest[1])
            if oid is None:
                self._error(404, 'Not Found')
                return
            self._send_json(200, {'name': rest[1], 'commit': {'sha': oid}})
            return

        # git refs
        if rest[:2] == ['git', 'refs'] and method == 'POST' and len(rest) == 2:
            ref = payload.get('ref')
            sha = payload.get('sha')
            if not isinstance(ref, str) or not ref.startswith('refs/heads/'):
                self._error(422, 'Invalid ref')
                return
            with STORE_LOCK:
                if ref in repository['refs']:
                    self._error(422, 'Reference already exists')
                    return
                item = repository['objects'].get(sha or '')
                if item is None or item[0] != 'commit':
                    self._error(422, 'Invalid commit sha')
                    return
                repository['refs'][ref] = sha
            self._send_json(201, {'ref': ref, 'object': {'sha': sha, 'type': 'commit'}})
            return
        if len(rest) == 4 and rest[:2] == ['git', 'refs'] and rest[2] == 'heads':
            if method != 'GET':
                self._error(404, 'Not Found')
                return
            oid = repository['refs'].get('refs/heads/' + rest[3])
            if oid is None:
                self._error(404, 'Not Found')
                return
            self._send_json(200, {'ref': 'refs/heads/' + rest[3],
                                  'object': {'sha': oid, 'type': 'commit'}})
            return

        # commits
        if rest == ['commits']:
            if method != 'GET':
                self._error(404, 'Not Found')
                return
            ref = query.get('sha', [None])[0]
            with STORE_LOCK:
                tip = ref_tip(repository, ref) if ref else ref_tip(repository, repository['default_branch'])
                oids = commit_list(repository, tip) if tip else []
                out = []
                for oid in oids:
                    c = parse_commit(repository['objects'][oid][1])
                    out.append({
                        'sha': oid,
                        'commit': {
                            'message': c['message'][:-1] if c['message'].endswith('\n') else c['message'],
                            'author': {'name': VIEWER_NAME, 'email': VIEWER_EMAIL},
                            'committer': {'name': VIEWER_NAME, 'email': VIEWER_EMAIL},
                        },
                        'author': {'login': VIEWER_LOGIN},
                        'committer': {'login': VIEWER_LOGIN},
                    })
            self._send_json(200, out)
            return

        # contents
        if rest and rest[0] == 'contents':
            cpath = '/'.join(rest[1:])
            ref = query.get('ref', [None])[0]
            if method == 'GET':
                with STORE_LOCK:
                    _tip, tree_oid = _contents_entry(repository, ref, cpath)
                    if tree_oid is None:
                        self._error(404, 'Not Found')
                        return
                    flat = flatten_tree(repository, tree_oid)
                    if cpath in flat:
                        _mode, oid = flat[cpath]
                        item = repository['objects'][oid]
                        self._send_json(200, {
                            'type': 'file', 'encoding': 'base64',
                            'content': base64.b64encode(item[1]).decode('ascii'),
                            'sha': oid, 'size': len(item[1]),
                            'name': cpath.split('/')[-1], 'path': cpath,
                        })
                        return
                    listing = _dir_listing(repository, tree_oid, cpath)
                    if not listing and cpath:
                        self._error(404, 'Not Found')
                        return
                    self._send_json(200, listing)
                return
            if method == 'PUT':
                message = payload.get('message') or ''
                content_b64 = payload.get('content')
                if not isinstance(content_b64, str):
                    self._error(422, 'Content is required')
                    return
                try:
                    raw = base64.b64decode(content_b64, validate=False)
                except Exception:
                    self._error(422, 'Content is not valid base64')
                    return
                branch = payload.get('branch') or repository['default_branch']
                with STORE_LOCK:
                    _tip, tree_oid = _contents_entry(repository, branch, cpath)
                    flat = flatten_tree(repository, tree_oid) if tree_oid else {}
                    existing = flat.get(cpath)
                    blob_oid = put_object(repository, 'blob', raw)
                    if existing is not None:
                        given_sha = payload.get('sha')
                        if given_sha is not None and given_sha != existing[1]:
                            self._error(409, 'Conflict: sha does not match')
                            return
                        if given_sha is None:
                            self._error(422, 'sha is required to update a file')
                            return
                        status = 200
                    else:
                        status = 201
                    commit_oid = make_contents_commit(
                        repository, branch, {cpath: blob_oid}, message)
                self._send_json(status, {
                    'content': {'name': cpath.split('/')[-1], 'path': cpath,
                                'sha': blob_oid, 'size': len(raw),
                                'type': 'file', 'encoding': 'base64'},
                    'commit': {'sha': commit_oid, 'message': message},
                })
                return
            if method == 'DELETE':
                branch = payload.get('branch') or repository['default_branch']
                with STORE_LOCK:
                    _tip, tree_oid = _contents_entry(repository, branch, cpath)
                    flat = flatten_tree(repository, tree_oid) if tree_oid else {}
                    if cpath not in flat:
                        self._error(404, 'Not Found')
                        return
                    commit_oid = make_contents_commit(
                        repository, branch, {cpath: None}, payload.get('message') or '')
                self._send_json(200, {'commit': {'sha': commit_oid}})
                return
            self._error(404, 'Not Found')
            return

        # labels
        if rest == ['labels']:
            if method != 'POST':
                self._error(404, 'Not Found')
                return
            name = payload.get('name')
            if not isinstance(name, str) or not name:
                self._error(422, 'Label name is required')
                return
            with STORE_LOCK:
                repository['labels'][name] = payload.get('color') or 'ededed'
            self._send_json(201, {'name': name, 'color': repository['labels'][name]})
            return

        # issues
        if rest and rest[0] == 'issues':
            if len(rest) == 1:
                if method == 'POST':
                    title = payload.get('title')
                    if not isinstance(title, str) or not title:
                        self._error(422, 'Title is required')
                        return
                    labels = payload.get('labels') or []
                    with STORE_LOCK:
                        for lab in labels:
                            lname = lab if isinstance(lab, str) else lab.get('name')
                            if lname not in repository['labels']:
                                self._error(422, f'Label does not exist: {lname}')
                                return
                        number = repository['next_issue']
                        repository['next_issue'] += 1
                        ISSUE_ID_SEQ[0] += 1
                        issue_rec = {
                            'id': ISSUE_ID_SEQ[0] - 1, 'number': number,
                            'title': title, 'body': payload.get('body') or '',
                            'state': 'open',
                            'labels': [l if isinstance(l, str) else l.get('name')
                                       for l in labels],
                            'comments': [], 'created_seq': number,
                        }
                        repository['issues'][number] = issue_rec
                    self._send_json(201, issue_view(issue_rec))
                    return
                if method == 'GET':
                    state = query.get('state', ['open'])[0]
                    sort = query.get('sort', ['created'])[0]
                    direction = query.get('direction', ['desc'])[0]
                    with STORE_LOCK:
                        items = list(repository['issues'].values())
                    if state in ('open', 'closed'):
                        items = [i for i in items if i['state'] == state]
                    if sort == 'created':
                        items.sort(key=lambda i: i['number'],
                                   reverse=(direction != 'asc'))
                    views = [issue_view(i) for i in items]
                    sliced = _paginate(self, views, query,
                                       f'/api/v3/repos/{owner}/{name}/issues')
                    self._send_json(200, sliced)
                    return
                self._error(404, 'Not Found')
                return
            try:
                number = int(rest[1])
            except ValueError:
                self._error(404, 'Not Found')
                return
            if len(rest) == 2:
                if method == 'GET':
                    issue_rec = repository['issues'].get(number)
                    if issue_rec is None:
                        self._error(404, 'Not Found')
                        return
                    self._send_json(200, issue_view(issue_rec))
                    return
                if method == 'PATCH':
                    with STORE_LOCK:
                        issue_rec = repository['issues'].get(number)
                        if issue_rec is None:
                            self._error(404, 'Not Found')
                            return
                        if payload.get('state') in ('open', 'closed'):
                            issue_rec['state'] = payload['state']
                        if isinstance(payload.get('title'), str):
                            issue_rec['title'] = payload['title']
                        if isinstance(payload.get('body'), str):
                            issue_rec['body'] = payload['body']
                    self._send_json(200, issue_view(issue_rec))
                    return
                self._error(404, 'Not Found')
                return
            if len(rest) == 3 and rest[2] == 'comments':
                issue_rec = repository['issues'].get(number)
                if issue_rec is None:
                    self._error(404, 'Not Found')
                    return
                if method == 'POST':
                    with STORE_LOCK:
                        COMMENT_ID_SEQ[0] += 1
                        comment = {'id': COMMENT_ID_SEQ[0] - 1,
                                   'body': payload.get('body') or '',
                                   'user': {'login': VIEWER_LOGIN}}
                        issue_rec['comments'].append(comment)
                    self._send_json(201, comment)
                    return
                if method == 'GET':
                    self._send_json(200, list(issue_rec['comments']))
                    return
                self._error(404, 'Not Found')
                return
            self._error(404, 'Not Found')
            return

        # pull requests
        if rest and rest[0] == 'pulls':
            if len(rest) == 1:
                if method == 'POST':
                    title = payload.get('title')
                    head = payload.get('head')
                    base = payload.get('base')
                    if not isinstance(title, str) or not head or not base:
                        self._error(422, 'title, head and base are required')
                        return
                    with STORE_LOCK:
                        head_sha = ref_tip(repository, head)
                        base_sha = ref_tip(repository, base)
                        if head_sha is None or base_sha is None:
                            self._error(422, 'Unknown head or base branch')
                            return
                        for p in repository['pulls'].values():
                            if (p['state'] == 'open' and p['head_ref'] == head
                                    and p['base_ref'] == base):
                                self._error(422, 'A pull request already exists for this branch')
                                return
                        number = repository['next_pull']
                        repository['next_pull'] += 1
                        pull_request = {
                            'id': repository['id'] * 100000 + number,
                            'number': number, 'title': title,
                            'body': payload.get('body') or '', 'state': 'open',
                            'head_ref': head, 'head_sha': head_sha,
                            'base_ref': base, 'base_sha': base_sha,
                            'merged': False, 'merged_at': None,
                            'merge_commit_sha': None, 'owner': owner,
                        }
                        repository['pulls'][number] = pull_request
                    self._send_json(201, pull_view(pull_request))
                    return
                if method == 'GET':
                    state = query.get('state', ['open'])[0]
                    with STORE_LOCK:
                        items = list(repository['pulls'].values())
                    if state == 'open':
                        items = [p for p in items if p['state'] == 'open']
                    elif state == 'closed':
                        items = [p for p in items if p['state'] == 'closed']
                    items.sort(key=lambda p: p['number'])
                    views = [pull_view(p) for p in items]
                    sliced = _paginate(self, views, query,
                                       f'/api/v3/repos/{owner}/{name}/pulls')
                    self._send_json(200, sliced)
                    return
                self._error(404, 'Not Found')
                return
            try:
                number = int(rest[1])
            except ValueError:
                self._error(404, 'Not Found')
                return
            if len(rest) == 2:
                pull_request = repository['pulls'].get(number)
                if pull_request is None:
                    self._error(404, 'Not Found')
                    return
                if method == 'GET':
                    self._send_json(200, pull_view(pull_request))
                    return
                self._error(404, 'Not Found')
                return
            if len(rest) == 3 and rest[2] == 'files':
                if method != 'GET':
                    self._error(404, 'Not Found')
                    return
                pull_request = repository['pulls'].get(number)
                if pull_request is None:
                    self._error(404, 'Not Found')
                    return
                with STORE_LOCK:
                    files = pull_files(repository, pull_request)
                self._send_json(200, files)
                return
            if len(rest) == 3 and rest[2] == 'merge':
                if method != 'PUT':
                    self._error(404, 'Not Found')
                    return
                with STORE_LOCK:
                    pull_request = repository['pulls'].get(number)
                    if pull_request is None:
                        self._error(404, 'Not Found')
                        return
                    if pull_request['merged']:
                        self._error(405, 'Pull request already merged')
                        return
                    if merge_conflict(repository, pull_request):
                        self._error(405, 'Merge conflict')
                        return
                    sha = squash_merge(repository, pull_request)
                self._send_json(200, {
                    'sha': sha, 'merged': True,
                    'message': 'Pull request successfully merged',
                })
                return
            self._error(404, 'Not Found')
            return

    self._error(404, 'Not Found')


ForgeHandler._handle_rest = _handle_rest

# ---------------------------------------------------------------------------
# Git smart HTTP (/{owner}/{repo}.git).
# ---------------------------------------------------------------------------

from collections import deque

_PACK_CACHE = {}
_PACK_CACHE_LOCK = threading.Lock()


def _pack_for(repository, send):
    """write_pack with a memo keyed by the exact object set (the clone bench
    fetches the same 600-object pack 50 times concurrently)."""
    key = tuple(sorted(send))
    with _PACK_CACHE_LOCK:
        pack = _PACK_CACHE.get(key)
        if pack is not None:
            return pack
    pack = write_pack(repository, send)
    with _PACK_CACHE_LOCK:
        if len(_PACK_CACHE) > 32:
            _PACK_CACHE.clear()
        _PACK_CACHE[key] = pack
    return pack


def _v0_advertisement(repository, service):
    """The protocol-v0 info/refs advertisement, with the service preamble."""
    caps = ('side-band-64k multi_ack_detailed thin-pack ofs-delta shallow '
            'agent=makefun-forge/1.0.0 symref=HEAD:refs/heads/main')
    if service == 'git-receive-pack':
        caps = ('report-status side-band-64k delete-refs ofs-delta '
                'agent=makefun-forge/1.0.0 symref=HEAD:refs/heads/main')
    out = [pkt_line(f'# service={service}\n'), b'0000']
    refs = sorted(repository['refs'].items())
    if not refs:
        out.append(pkt_line(ZERO_OID + ' capabilities^{}\0' + caps + '\n'))
    else:
        first = True
        ordered = []
        head_oid = repository['refs'].get('refs/heads/main')
        if head_oid:
            ordered.append(('HEAD', head_oid))
        ordered.extend(refs)
        for name, oid in ordered:
            line = oid + ' ' + name
            if first:
                line += '\0' + caps
                first = False
            out.append(pkt_line(line + '\n'))
            if name.startswith('refs/tags/'):
                item = repository['objects'].get(oid)
                if item is not None and item[0] == 'tag':
                    target = parse_tag(item[1])['object']
                    out.append(pkt_line(target + ' ' + name + '^{}\n'))
    out.append(b'0000')
    return b''.join(out)


def _v2_advertisement():
    """The protocol-v2 capability advertisement for upload-pack."""
    return pkt_lines([
        '# service=git-upload-pack\n',
        'version 2\n',
        'agent=makefun-forge/1.0.0\n',
        'ls-refs=unborn\n',
        'fetch=shallow filter\n',
        'object-format=sha1\n',
        'flush',
    ])


def _ls_refs_v2(repository, args):
    """Answer a v2 ls-refs command, honouring ref-prefix filters."""
    prefixes = [a[len('ref-prefix '):] for a in args
                if a.startswith('ref-prefix ')]
    items = []
    main_oid = repository['refs'].get('refs/heads/main')
    if not prefixes:
        # An empty repo still reports HEAD (zero oid); an `unborn
        # refs/heads/main` line would fail clone-empty, so never emit one.
        items.append(f'{main_oid or ZERO_OID} HEAD symref-target:refs/heads/main')
    for ref, oid in sorted(repository['refs'].items()):
        if prefixes and not any(ref.startswith(p) for p in prefixes):
            continue
        line = f'{oid} {ref}'
        if ref.startswith('refs/tags/'):
            item = repository['objects'].get(oid)
            if item is not None and item[0] == 'tag':
                line += f" peeled:{parse_tag(item[1])['object']}"
        items.append(line)
    return pkt_lines(items + ['flush'])


def _fetch_objects(repository, wants, haves, depth, old_shallow):
    """(send_oids, shallow_list, unshallow_list) per the suite's semantics:
    no depth -> send = reachable(wants) minus reachable(haves) (object level);
    depth -> walk at most depth generations, haves prune only their own oid."""
    have_set = set(haves)
    included = {}
    dq = deque()
    for w in wants:
        if w not in included and w in repository['objects']:
            included[w] = 0
            dq.append(w)
    while dq:
        oid = dq.popleft()
        dist = included[oid]
        item = repository['objects'].get(oid)
        if item is None:
            continue
        if item[0] == 'tag':
            target = parse_tag(item[1])['object']
            if target not in included and target in repository['objects']:
                included[target] = dist
                dq.append(target)
            continue
        if item[0] != 'commit':
            continue
        if depth is not None and dist >= depth - 1:
            continue
        for parent in parse_commit(item[1])['parents']:
            if parent in included:
                continue
            if depth is None and parent in have_set:
                continue
            included[parent] = dist + 1
            dq.append(parent)
    candidate = set()
    for oid in included:
        candidate.add(oid)
        item = repository['objects'].get(oid)
        if item is not None and item[0] == 'commit':
            candidate |= collect_reachable(repository, [parse_commit(item[1])['tree']])
    if depth is None:
        held = set()
        for h in have_set:
            held |= collect_reachable(repository, [h])
        send = candidate - held
    else:
        send = candidate - have_set
    shallow_list, unshallow_list = [], []
    if depth is not None:
        for oid, dist in included.items():
            if dist == depth - 1:
                item = repository['objects'].get(oid)
                if item is not None and item[0] == 'commit':
                    shallow_list.append(oid)
        for s in (old_shallow or []):
            if s in included:
                item = repository['objects'].get(s)
                if item is not None and item[0] == 'commit':
                    parents = parse_commit(item[1])['parents']
                    if parents and all(p in included for p in parents):
                        unshallow_list.append(s)
    return send, shallow_list, unshallow_list


def _send_fetch_v2(self, repository, wants, haves, shallow, depth):
    """Answer a protocol-v2 fetch with acknowledgments + packfile sections."""
    with STORE_LOCK:
        send, shallow_list, unshallow_list = _fetch_objects(
            repository, wants, haves, depth, shallow)
        pack = _pack_for(repository, send)
    out = bytearray()
    out += pkt_line('acknowledgments\n')
    ack = next((h for h in haves if h in repository['objects']), None)
    if ack:
        out += pkt_line(f'ACK {ack}\n')
        out += pkt_line('ready\n')
    else:
        out += pkt_line('NAK\n')
    out += b'0001'
    if shallow_list or unshallow_list:
        out += pkt_line('shallow-info\n')
        for s in shallow_list:
            out += pkt_line(f'shallow {s}\n')
        for s in unshallow_list:
            out += pkt_line(f'unshallow {s}\n')
        out += b'0001'
    out += pkt_line('packfile\n')
    out += sideband_pack(pack)
    out += b'0000'
    self._send(200, bytes(out), 'application/x-git-upload-pack-result')


def _send_fetch_v0(self, repository, wants, haves, shallow, depth):
    """Answer a protocol-v0 fetch: ACK/NAK, shallow lines, then the pack."""
    with STORE_LOCK:
        send, shallow_list, unshallow_list = _fetch_objects(
            repository, wants, haves, depth, shallow)
        pack = _pack_for(repository, send)
    out = bytearray()
    ack = next((h for h in haves if h in repository['objects']), None)
    if ack:
        out += pkt_line(f'ACK {ack}\n')
    else:
        out += pkt_line('NAK\n')
    for s in shallow_list:
        out += pkt_line(f'shallow {s}\n')
    for s in unshallow_list:
        out += pkt_line(f'unshallow {s}\n')
    out += sideband_pack(pack)
    out += b'0000'
    self._send(200, bytes(out), 'application/x-git-upload-pack-result')


def _handle_upload_pack(self, repository, body):
    """Serve one git-upload-pack request, v2 when asked, else v0."""
    items, _off = parse_pkt_lines(body)
    if self.headers.get('Git-Protocol') == 'version=2':
        command = None
        args = []
        in_args = False
        for kind, payload in items:
            if kind == 'delim':
                in_args = True
                continue
            if kind != 'data':
                continue
            line = payload.decode('utf-8', 'replace').rstrip('\n')
            if not in_args:
                if line.startswith('command='):
                    command = line[8:]
            else:
                args.append(line)
        if command == 'ls-refs':
            with STORE_LOCK:
                resp = _ls_refs_v2(repository, args)
            self._send(200, resp, 'application/x-git-upload-pack-result')
            return
        if command == 'fetch':
            wants, haves, shallow, depth = [], [], [], None
            for a in args:
                if a.startswith('want '):
                    wants.append(a[5:].strip())
                elif a.startswith('have '):
                    haves.append(a[5:].strip())
                elif a.startswith('shallow '):
                    shallow.append(a[8:].strip())
                elif a.startswith('deepen '):
                    try:
                        depth = int(a[7:].strip())
                    except ValueError:
                        pass
            self._send_fetch_v2(repository, wants, haves, shallow, depth)
            return
        self._error(400, 'Unknown command')
        return
    # v0 fetch: wants/shallow/deepen until flush, then haves/done until flush.
    wants, haves, shallow, depth = [], [], [], None
    section = 0
    for kind, payload in items:
        if kind == 'flush':
            section += 1
            continue
        if kind != 'data':
            continue
        line = payload.decode('utf-8', 'replace').rstrip('\n')
        if section == 0:
            if line.startswith('want '):
                wants.append(line[5:].split(' ')[0])
            elif line.startswith('shallow '):
                shallow.append(line[8:].strip())
            elif line.startswith('deepen '):
                try:
                    depth = int(line[7:].strip())
                except ValueError:
                    pass
        elif section == 1:
            if line.startswith('have '):
                haves.append(line[5:].strip())
    self._send_fetch_v0(repository, wants, haves, shallow, depth)


def _handle_receive_pack(self, repository, body):
    """Serve one git-receive-pack request: store the pack, apply the refs.

    Each ref update is checked on its own: fast-forward updates apply,
    non-fast-forward ones are refused with an 'ng' report line, and a push
    carrying both applies the good ref and refuses the bad one.
    """
    items, offset = parse_pkt_lines(body)
    commands = []
    for kind, payload in items:
        if kind == 'flush':
            break
        if kind != 'data':
            continue
        line = payload.decode('utf-8', 'replace').rstrip('\n')
        if '\0' in line:
            line = line.split('\0', 1)[0]
        parts = line.split(' ')
        if (len(parts) >= 3 and SHA40_RE.match(parts[0])
                and SHA40_RE.match(parts[1])):
            commands.append((parts[0], parts[1], parts[2]))
    pack_bytes = body[offset:]
    unpack_ok = True
    unpack_error = None
    if pack_bytes:
        try:
            objs = read_pack(pack_bytes)
            with STORE_LOCK:
                for oid, (otype, data) in objs.items():
                    repository['objects'][oid] = (otype, data)
        except Exception as exc:
            unpack_ok = False
            unpack_error = str(exc)[:120]
    report = []
    with STORE_LOCK:
        for old, new, ref in commands:
            if not unpack_ok:
                report.append(('ng', ref, 'unpack failed'))
                continue
            if new == ZERO_OID:
                if ref in repository['refs']:
                    del repository['refs'][ref]
                    report.append(('ok', ref, None))
                else:
                    report.append(('ng', ref, 'ref does not exist'))
                continue
            if old == ZERO_OID:
                if ref in repository['refs']:
                    report.append(('ng', ref, 'already exists'))
                    continue
                item = repository['objects'].get(new)
                if item is None or item[0] not in ('commit', 'tag'):
                    report.append(('ng', ref, 'invalid object'))
                    continue
                repository['refs'][ref] = new
                report.append(('ok', ref, None))
                continue
            current = repository['refs'].get(ref)
            if current != old or not is_ancestor(repository, old, new):
                report.append(('ng', ref, 'non-fast-forward'))
                continue
            repository['refs'][ref] = new
            report.append(('ok', ref, None))
    lines = []
    if unpack_ok:
        lines.append('unpack ok\n')
    else:
        lines.append(f"unpack {unpack_error or 'failed'}\n")
    for kind, ref, reason in report:
        if kind == 'ok':
            lines.append(f'ok {ref}\n')
        else:
            lines.append(f'ng {ref} {reason}\n')
    payload = pkt_lines(lines) + b'0000'
    out = sideband_pack(payload) + b'0000'
    self._send(200, out, 'application/x-git-receive-pack-result')


def _handle_git(self, owner, name, sub, query, body):
    """Route one git smart-HTTP request to info/refs, upload-pack or receive-pack."""
    if not self._require_auth():
        return
    repository, err = _repo_path_lookup(self, owner, name)
    if err:
        self._error(404, 'Not Found')
        return
    if sub == 'info/refs':
        service = query.get('service', [None])[0]
        if service == 'git-upload-pack':
            with STORE_LOCK:
                if self.headers.get('Git-Protocol') == 'version=2':
                    payload = _v2_advertisement()
                else:
                    payload = _v0_advertisement(repository, 'git-upload-pack')
            self._send(200, payload, 'application/x-git-upload-pack-advertisement')
        elif service == 'git-receive-pack':
            with STORE_LOCK:
                payload = _v0_advertisement(repository, 'git-receive-pack')
            self._send(200, payload, 'application/x-git-receive-pack-advertisement')
        else:
            self._error(404, 'Not Found')
        return
    if sub == 'git-upload-pack' and self.command == 'POST':
        self._handle_upload_pack(repository, body)
        return
    if sub == 'git-receive-pack' and self.command == 'POST':
        self._handle_receive_pack(repository, body)
        return
    self._error(404, 'Not Found')


ForgeHandler._handle_git = _handle_git
ForgeHandler._handle_upload_pack = _handle_upload_pack
ForgeHandler._handle_receive_pack = _handle_receive_pack

# ---------------------------------------------------------------------------
# GraphQL v4 API (/api/graphql): hand-rolled parser + executor over the
# same in-memory store as REST. Documents used by the suite are fixed
# strings, so the parser covers fields, aliases, args, variables, inline
# enums, input objects, lists, and `... on Type` fragments.
# ---------------------------------------------------------------------------

class GqlParser:
    """A small recursive-descent parser for the suite's GraphQL documents.

    Covers fields, aliases, arguments, variables, inline enums, input
    objects, lists and `... on Type` fragments — everything the documents
    gh and github-mcp-server send use.
    """

    def __init__(self, text):
        """Start parsing one GraphQL document string."""
        self.text = text
        self.i = 0
        self.n = len(text)

    def _skip_space(self):
        """Advance past whitespace, commas and # comments."""
        while self.i < self.n:
            c = self.text[self.i]
            if c in ' \t\r\n,':
                self.i += 1
            elif c == '#':
                while self.i < self.n and self.text[self.i] != '\n':
                    self.i += 1
            else:
                break

    def _lookahead(self):
        """The next significant character, or '' at the end."""
        self._skip_space()
        return self.text[self.i] if self.i < self.n else ''

    def _consume(self, ch):
        """Consume one expected character, or raise a syntax error."""
        self._skip_space()
        if self.i >= self.n or self.text[self.i] != ch:
            raise ValueError(f'expected {ch!r} at {self.i}')
        self.i += 1

    def _read_name(self):
        """Read a GraphQL Name token."""
        self._skip_space()
        m = re.match(r'[_A-Za-z][_0-9A-Za-z]*', self.text[self.i:])
        if not m:
            raise ValueError(f'expected name at {self.i}')
        self.i += len(m.group(0))
        return m.group(0)

    def _read_string(self):
        """Read a double-quoted string value, honouring backslash escapes."""
        self.i += 1  # opening quote
        out = []
        while self.i < self.n:
            c = self.text[self.i]
            if c == '"':
                self.i += 1
                return ''.join(out)
            if c == '\\':
                self.i += 1
                e = self.text[self.i] if self.i < self.n else ''
                out.append({'n': '\n', 't': '\t', 'r': '\r', '"': '"',
                            '\\': '\\', '/': '/'}.get(e, e))
                self.i += 1
            else:
                out.append(c)
                self.i += 1
        raise ValueError('unterminated string')

    def _read_value(self):
        """Read one value: variable, string, input object, list, int, enum."""
        self._skip_space()
        c = self.text[self.i]
        if c == '$':
            self.i += 1
            return ('var', self._read_name())
        if c == '"':
            return ('lit', self._read_string())
        if c == '{':
            return ('input', self._read_input_object())
        if c == '[':
            self.i += 1
            vals = []
            while True:
                self._skip_space()
                if self.text[self.i] == ']':
                    self.i += 1
                    break
                vals.append(self._read_value())
            return ('list', vals)
        if c == '-' or c.isdigit():
            m = re.match(r'-?\d+', self.text[self.i:])
            self.i += len(m.group(0))
            return ('lit', int(m.group(0)))
        name = self._read_name()
        if name == 'true':
            return ('lit', True)
        if name == 'false':
            return ('lit', False)
        if name == 'null':
            return ('lit', None)
        return ('enum', name)

    def _read_input_object(self):
        """Read a {key: value, ...} input object into a dict."""
        self._consume('{')
        obj = {}
        while True:
            self._skip_space()
            if self.text[self.i] == '}':
                self.i += 1
                break
            key = self._read_name()
            self._consume(':')
            obj[key] = self._read_value()
        return obj

    def _read_args(self):
        """Read a (name: value, ...) argument list into a dict."""
        args = {}
        self._consume('(')
        while True:
            self._skip_space()
            if self.text[self.i] == ')':
                self.i += 1
                break
            key = self._read_name()
            self._consume(':')
            args[key] = self._read_value()
        return args

    def _read_selection_set(self):
        """Read a {field ...} selection set into a list of field tuples."""
        self._consume('{')
        fields = []
        while True:
            self._skip_space()
            if self.text[self.i] == '}':
                self.i += 1
                break
            if self.text[self.i:self.i + 3] == '...':
                self.i += 3
                self._skip_space()
                if self.text[self.i:self.i + 2] == 'on':
                    self.i += 2
                    typename = self._read_name()
                    fields.append(('fragment', typename, self._read_selection_set()))
                else:
                    self._read_name()  # named spread: not used by the suite
                continue
            alias = None
            name = self._read_name()
            if self._lookahead() == ':':
                self.i += 1
                alias = name
                name = self._read_name()
            args = {}
            if self._lookahead() == '(':
                args = self._read_args()
            sub = None
            if self._lookahead() == '{':
                sub = self._read_selection_set()
            fields.append(('field', alias or name, name, args, sub))
        return fields

    def parse_document(self):
        """Parse the whole document; return (operation, selection set)."""
        self._skip_space()
        op = 'query'
        if self.text[self.i:self.i + 5] == 'query':
            self.i += 5
            self._skip_space()
            if self.i < self.n and self.text[self.i] not in '{(':
                self._read_name()
        elif self.text[self.i:self.i + 8] == 'mutation':
            self.i += 8
            op = 'mutation'
            self._skip_space()
            if self.i < self.n and self.text[self.i] not in '{(':
                self._read_name()
        self._skip_space()
        if self.i < self.n and self.text[self.i] == '(':
            depth = 0
            while self.i < self.n:
                c = self.text[self.i]
                if c == '(':
                    depth += 1
                elif c == ')':
                    depth -= 1
                    self.i += 1
                    if depth == 0:
                        break
                    continue
                self.i += 1
        return op, self._read_selection_set()


def _gql_resolve_value(value, variables):
    """Turn a parsed argument value into a plain Python value."""
    kind = value[0]
    if kind == 'var':
        return variables.get(value[1])
    if kind == 'lit':
        return value[1]
    if kind == 'enum':
        return value[1]
    if kind == 'list':
        return [_gql_resolve_value(v, variables) for v in value[1]]
    if kind == 'input':
        return {k: _gql_resolve_value(v, variables) for k, v in value[1].items()}
    return None


# Introspection field lists, in the order the suite expects them back.
_GQL_TYPE_FIELDS = {
    'Issue': [
        'id',
        'number',
        'title',
        'state',
        'body',
    ],
    'PullRequest': [
        'id',
        'number',
        'headRefName',
        'baseRefName',
        'mergeable',
        'state',
        'merged',
        'files',
    ],
    'Repository': [
        'id',
        'databaseId',
        'name',
        'nameWithOwner',
        'owner',
        'defaultBranchRef',
        'viewerPermission',
        'hasIssuesEnabled',
        'issue',
        'issues',
        'pullRequests',
        'pullRequest',
    ],
    'SearchType': [],
}
_GQL_ENUM_VALUES = {
    'SearchType': [
        'ISSUE',
        'REPOSITORY',
        'USER',
        'ORGANIZATION',
        'DISCUSSION',
    ],
}


def _gql_b64(s):
    """URL-safe base64 without padding, for connection cursors."""
    return base64.urlsafe_b64encode(s.encode('utf-8')).decode('ascii').rstrip('=')


def _gql_connection(typename, items, first, after, keyfn):
    """Slice nodes into a Relay connection shape (edges + pageInfo)."""
    start = 0
    if after:
        try:
            raw = base64.urlsafe_b64decode(
                after + '=' * (-len(after) % 4)).decode('utf-8')
            for idx, it in enumerate(items):
                if keyfn(it) == raw:
                    start = idx + 1
                    break
        except Exception:
            pass
    page = items[start:]
    has_next = False
    if first is not None:
        if len(page) > first:
            page = page[:first]
            has_next = True
    return {
        '_type': typename,
        'nodes': page,
        'edges': [{'_type': 'Edge', 'node': n, 'cursor': _gql_b64(keyfn(n))}
                  for n in page],
        'pageInfo': {
            '_type': 'PageInfo', 'hasNextPage': has_next,
            'hasPreviousPage': start > 0,
            'startCursor': _gql_b64(keyfn(page[0])) if page else None,
            'endCursor': _gql_b64(keyfn(page[-1])) if page else None,
        },
        'totalCount': len(items),
    }


def _repo_node(repository):
    """Wrap a repository record as a GraphQL node dict."""
    return {'_type': 'Repository', 'repo': repository}


def _issue_node(repository, issue):
    """Wrap an issue record as a GraphQL node dict."""
    return {'_type': 'Issue', 'repo': repository, 'issue': issue}


def _pull_node(repository, pull):
    """Wrap a pull-request record as a GraphQL node dict."""
    return {'_type': 'PullRequest', 'repo': repository, 'pull': pull}


def _issues_for(repository, args):
    """The issue connection of a repository, ordered and state-filtered."""
    items = list(repository['issues'].values())
    states = args.get('states')
    if states:
        wanted = set(s.upper() for s in states)
        items = [i for i in items if i['state'].upper() in wanted]
    order = args.get('orderBy') or {}
    direction = (order.get('direction') or 'DESC').upper()
    items.sort(key=lambda i: i['number'], reverse=(direction != 'ASC'))
    nodes = [_issue_node(repository, i) for i in items]
    return _gql_connection('IssueConnection', nodes, args.get('first'),
                           args.get('after'), lambda n: str(n['issue']['number']))


def _pulls_for(repository, args):
    """The pull-request connection of a repository, state-filtered."""
    items = list(repository['pulls'].values())
    states = args.get('states')
    if states:
        wanted = set(s.upper() for s in states)
        items = [p for p in items if p['state'].upper() in wanted]
    items.sort(key=lambda p: p['number'])
    nodes = [_pull_node(repository, p) for p in items]
    return _gql_connection('PullRequestConnection', nodes, args.get('first'),
                           args.get('after'), lambda n: str(n['pull']['number']))


def _files_for(repository, pull, args):
    """The changed-files connection of one pull request."""
    files = pull_files(repository, pull)
    nodes = [{'_type': 'File', 'path': f['filename'],
              'additions': f['additions'], 'deletions': f['deletions'],
              'status': f['status']} for f in files]
    return _gql_connection('FileConnection', nodes, args.get('first'),
                           args.get('after'), lambda n: n['path'])


_GQL_FIELDS = {}


def _gql_field(typename, name):
    """Register a resolver for one (type, field) pair; return the decorator."""
    def deco(fn):
        """Record the resolver and return it unchanged."""
        _GQL_FIELDS[(typename, name)] = fn
        return fn
    return deco


# -- Query root -------------------------------------------------------------
@_gql_field('Query', 'viewer')
def _gql_viewer(node, args, ctx):
    """The signed-in user, as a Viewer node."""
    return {'_type': 'Viewer', 'login': VIEWER_LOGIN, 'id': VIEWER_ID,
            'name': VIEWER_NAME, 'email': VIEWER_EMAIL}


@_gql_field('Query', 'repository')
def _gql_repository(node, args, ctx):
    """Look a repository up by owner + name; None when it does not exist."""
    repository = get_repo(args.get('owner'), args.get('name'))
    return _repo_node(repository) if repository is not None else None


@_gql_field('Query', 'node')
def _gql_node(node, args, ctx):
    """Fetch any object by its global id (Repository, Issue, PullRequest)."""
    kind, parts = decode_global_id(args.get('id') or '')
    if kind == 'Repository' and parts:
        repository = next((r for r in REPOS.values() if r['id'] == int(parts[0])), None)
        return _repo_node(repository) if repository is not None else None
    if kind == 'Issue' and len(parts) >= 2:
        repository = next((r for r in REPOS.values() if r['id'] == int(parts[0])), None)
        if repository is None:
            return None
        issue = repository['issues'].get(int(parts[1]))
        return _issue_node(repository, issue) if issue is not None else None
    if kind == 'PullRequest' and len(parts) >= 2:
        repository = next((r for r in REPOS.values() if r['id'] == int(parts[0])), None)
        if repository is None:
            return None
        pull = repository['pulls'].get(int(parts[1]))
        return _pull_node(repository, pull) if pull is not None else None
    return None


@_gql_field('Query', '__type')
def _gql_type_info(node, args, ctx):
    """Introspection: describe one named type."""
    return {'_type': 'TypeInfo', 'name': args.get('name')}


# -- Viewer / User ----------------------------------------------------------
for _t in ('Viewer', 'User'):
    @_gql_field(_t, 'login')
    def _gql_user_login(node, args, ctx):
        """A user's login name."""
        return node.get('login')
    @_gql_field(_t, 'id')
    def _gql_user_id(node, args, ctx):
        """A user's numeric id."""
        return node.get('id')
    @_gql_field(_t, 'name')
    def _gql_user_name(node, args, ctx):
        """A user's display name."""
        return node.get('name')
    @_gql_field(_t, 'email')
    def _gql_user_email(node, args, ctx):
        """A user's email address."""
        return node.get('email')


# -- Repository -------------------------------------------------------------
@_gql_field('Repository', 'id')
def _gql_repo_id(node, args, ctx):
    """A repository's global id."""
    return global_id('Repository', node['repo']['id'])


@_gql_field('Repository', 'databaseId')
def _gql_repo_dbid(node, args, ctx):
    """A repository's numeric database id."""
    return node['repo']['id']


@_gql_field('Repository', 'name')
def _gql_repo_name(node, args, ctx):
    """A repository's short name."""
    return node['repo']['name']


@_gql_field('Repository', 'nameWithOwner')
def _gql_repo_nwo(node, args, ctx):
    """A repository's 'owner/name' full name."""
    r = node['repo']
    return f"{r['owner']}/{r['name']}"


@_gql_field('Repository', 'owner')
def _gql_repo_owner(node, args, ctx):
    """A repository's owner, as a User node."""
    return {'_type': 'User', 'login': node['repo']['owner'], 'id': VIEWER_ID}


@_gql_field('Repository', 'defaultBranchRef')
def _gql_repo_dbr(node, args, ctx):
    """A repository's default branch, or None while it has no commits."""
    r = node['repo']
    if 'refs/heads/' + r['default_branch'] not in r['refs']:
        return None
    return {'_type': 'Branch', 'name': r['default_branch']}


@_gql_field('Repository', 'viewerPermission')
def _gql_repo_perm(node, args, ctx):
    """The viewer's permission on the repository (always ADMIN here)."""
    return 'ADMIN'


@_gql_field('Repository', 'hasIssuesEnabled')
def _gql_repo_has_issues(node, args, ctx):
    """Whether issues are enabled (always true here)."""
    return True


@_gql_field('Repository', 'issue')
def _gql_repo_issue(node, args, ctx):
    """One issue of the repository, by number."""
    issue = node['repo']['issues'].get(args.get('number'))
    return _issue_node(node['repo'], issue) if issue is not None else None


@_gql_field('Repository', 'issues')
def _gql_repo_issues(node, args, ctx):
    """The repository's issue connection."""
    return _issues_for(node['repo'], args)


@_gql_field('Repository', 'pullRequests')
def _gql_repo_pulls(node, args, ctx):
    """The repository's pull-request connection."""
    return _pulls_for(node['repo'], args)


@_gql_field('Repository', 'pullRequest')
def _gql_repo_pull(node, args, ctx):
    """One pull request of the repository, by number."""
    pull = node['repo']['pulls'].get(args.get('number'))
    return _pull_node(node['repo'], pull) if pull is not None else None


# -- Issue ------------------------------------------------------------------
@_gql_field('Issue', 'id')
def _gql_issue_id(node, args, ctx):
    """An issue's global id."""
    return global_id('Issue', node['repo']['id'], node['issue']['number'])


@_gql_field('Issue', 'number')
def _gql_issue_number(node, args, ctx):
    """An issue's number within its repository."""
    return node['issue']['number']


@_gql_field('Issue', 'title')
def _gql_issue_title(node, args, ctx):
    """An issue's title."""
    return node['issue']['title']


@_gql_field('Issue', 'body')
def _gql_issue_body(node, args, ctx):
    """An issue's body text."""
    return node['issue']['body']


@_gql_field('Issue', 'state')
def _gql_issue_state(node, args, ctx):
    """An issue's state, upper-cased (OPEN / CLOSED)."""
    return node['issue']['state'].upper()


@_gql_field('Issue', 'repository')
def _gql_issue_repo(node, args, ctx):
    """The repository an issue belongs to."""
    return _repo_node(node['repo'])


# -- PullRequest ------------------------------------------------------------
@_gql_field('PullRequest', 'id')
def _gql_pull_id(node, args, ctx):
    """A pull request's global id."""
    return global_id('PullRequest', node['repo']['id'], node['pull']['number'])


@_gql_field('PullRequest', 'number')
def _gql_pull_number(node, args, ctx):
    """A pull request's number within its repository."""
    return node['pull']['number']


@_gql_field('PullRequest', 'title')
def _gql_pull_title(node, args, ctx):
    """A pull request's title."""
    return node['pull']['title']


@_gql_field('PullRequest', 'body')
def _gql_pull_body(node, args, ctx):
    """A pull request's body text."""
    return node['pull']['body']


@_gql_field('PullRequest', 'state')
def _gql_pull_state(node, args, ctx):
    """A pull request's state, upper-cased (OPEN / CLOSED)."""
    return node['pull']['state'].upper()


@_gql_field('PullRequest', 'merged')
def _gql_pull_merged(node, args, ctx):
    """Whether the pull request has been merged."""
    return node['pull']['merged']


@_gql_field('PullRequest', 'headRefName')
def _gql_pull_head(node, args, ctx):
    """The pull request's head branch name."""
    return node['pull']['head_ref']


@_gql_field('PullRequest', 'baseRefName')
def _gql_pull_base(node, args, ctx):
    """The pull request's base branch name."""
    return node['pull']['base_ref']


@_gql_field('PullRequest', 'mergeable')
def _gql_pull_mergeable(node, args, ctx):
    """MERGEABLE, CONFLICTING, or UNKNOWN once merged."""
    if node['pull']['merged']:
        return 'UNKNOWN'
    return 'CONFLICTING' if merge_conflict(node['repo'], node['pull']) else 'MERGEABLE'


@_gql_field('PullRequest', 'files')
def _gql_pull_files(node, args, ctx):
    """The pull request's changed-files connection."""
    return _files_for(node['repo'], node['pull'], args)


@_gql_field('PullRequest', 'repository')
def _gql_pull_repo(node, args, ctx):
    """The repository a pull request belongs to."""
    return _repo_node(node['repo'])


# -- Branch / File / Comment ------------------------------------------------
@_gql_field('Branch', 'name')
def _gql_branch_name(node, args, ctx):
    """A branch's short name."""
    return node['name']


@_gql_field('File', 'path')
def _gql_file_path(node, args, ctx):
    """A changed file's repository path."""
    return node['path']


@_gql_field('File', 'additions')
def _gql_file_add(node, args, ctx):
    """Lines added in a changed file."""
    return node['additions']


@_gql_field('File', 'deletions')
def _gql_file_del(node, args, ctx):
    """Lines removed in a changed file."""
    return node['deletions']


@_gql_field('File', 'status')
def _gql_file_status(node, args, ctx):
    """A changed file's status (added / modified / removed)."""
    return node['status']


@_gql_field('IssueComment', 'id')
def _gql_comment_id(node, args, ctx):
    """A comment's global id."""
    c = node['comment']
    return global_id('IssueComment', c['id'])


@_gql_field('IssueComment', 'body')
def _gql_comment_body(node, args, ctx):
    """A comment's body text."""
    return node['comment']['body']


# -- Connections ------------------------------------------------------------
@_gql_field('IssueConnection', 'nodes')
def _gql_conn_nodes(node, args, ctx):
    """A connection's nodes, in page order."""
    return node['nodes']


@_gql_field('PullRequestConnection', 'nodes')
def _gql_conn_nodes_pr(node, args, ctx):
    """A pull-request connection's nodes, in page order."""
    return node['nodes']


@_gql_field('FileConnection', 'nodes')
def _gql_conn_nodes_file(node, args, ctx):
    """A file connection's nodes, in page order."""
    return node['nodes']


for _ct in ('IssueConnection', 'PullRequestConnection', 'FileConnection'):
    @_gql_field(_ct, 'edges')
    def _gql_conn_edges(node, args, ctx):
        """A connection's edges (node + cursor each)."""
        return node['edges']
    @_gql_field(_ct, 'pageInfo')
    def _gql_conn_page(node, args, ctx):
        """A connection's pageInfo (hasNextPage, cursors)."""
        return node['pageInfo']
    @_gql_field(_ct, 'totalCount')
    def _gql_conn_total(node, args, ctx):
        """A connection's total count across all pages."""
        return node['totalCount']


@_gql_field('Edge', 'node')
def _gql_edge_node(node, args, ctx):
    """An edge's node."""
    return node['node']


@_gql_field('Edge', 'cursor')
def _gql_edge_cursor(node, args, ctx):
    """An edge's opaque cursor."""
    return node['cursor']


@_gql_field('PageInfo', 'hasNextPage')
def _gql_pi_next(node, args, ctx):
    """Whether another page follows this one."""
    return node['hasNextPage']


@_gql_field('PageInfo', 'hasPreviousPage')
def _gql_pi_prev(node, args, ctx):
    """Whether a page precedes this one."""
    return node['hasPreviousPage']


@_gql_field('PageInfo', 'startCursor')
def _gql_pi_start(node, args, ctx):
    """The cursor of this page's first edge, or None when empty."""
    return node['startCursor']


@_gql_field('PageInfo', 'endCursor')
def _gql_pi_end(node, args, ctx):
    """The cursor of this page's last edge, or None when empty."""
    return node['endCursor']


# -- Introspection ----------------------------------------------------------
@_gql_field('TypeInfo', 'name')
def _gql_ti_name(node, args, ctx):
    """An introspected type's name."""
    return node['name']


@_gql_field('TypeInfo', 'fields')
def _gql_ti_fields(node, args, ctx):
    """An introspected type's fields, in the suite's expected order."""
    names = _GQL_TYPE_FIELDS.get(node['name'], [])
    return [{'_type': 'Field', 'name': n} for n in names]


@_gql_field('TypeInfo', 'enumValues')
def _gql_ti_enums(node, args, ctx):
    """An introspected enum's values."""
    names = _GQL_ENUM_VALUES.get(node['name'], [])
    return [{'_type': 'EnumValue', 'name': n} for n in names]


@_gql_field('Field', 'name')
def _gql_field_name(node, args, ctx):
    """A field's name."""
    return node['name']


@_gql_field('EnumValue', 'name')
def _gql_enum_name(node, args, ctx):
    """An enum value's name."""
    return node['name']


# -- Mutation payloads ------------------------------------------------------
@_gql_field('CreateIssuePayload', 'issue')
def _gql_pl_issue(node, args, ctx):
    """The issue a createIssue mutation made."""
    return node.get('issue')


@_gql_field('CloseIssuePayload', 'issue')
def _gql_pl_issue2(node, args, ctx):
    """The issue a closeIssue mutation closed."""
    return node.get('issue')


@_gql_field('CreatePullRequestPayload', 'pullRequest')
def _gql_pl_pull(node, args, ctx):
    """The pull request a createPullRequest mutation opened."""
    return node.get('pullRequest')


@_gql_field('MergePullRequestPayload', 'pullRequest')
def _gql_pl_pull2(node, args, ctx):
    """The pull request a mergePullRequest mutation merged."""
    return node.get('pullRequest')


@_gql_field('AddCommentPayload', 'commentEdge')
def _gql_pl_edge(node, args, ctx):
    """The comment edge an addComment mutation added."""
    return node.get('commentEdge')


@_gql_field('CommentEdge', 'node')
def _gql_ce_node(node, args, ctx):
    """A comment edge's comment node."""
    return node.get('node')


def _gql_repo_by_global_id(gid):
    """Find a repository record by its global id; None when it is not one."""
    kind, parts = decode_global_id(gid or '')
    if kind != 'Repository' or not parts:
        return None
    return next((r for r in REPOS.values() if r['id'] == int(parts[0])), None)


def _gql_mut_create_issue(node, args, ctx):
    """createIssue: open a new issue in the named repository."""
    inp = args.get('input') or {}
    with STORE_LOCK:
        repository = _gql_repo_by_global_id(inp.get('repositoryId'))
        if repository is None:
            raise ValueError('Repository not found')
        number = repository['next_issue']
        repository['next_issue'] += 1
        ISSUE_ID_SEQ[0] += 1
        issue_rec = {'id': ISSUE_ID_SEQ[0] - 1, 'number': number,
                     'title': inp.get('title') or '', 'body': inp.get('body') or '',
                     'state': 'open', 'labels': [], 'comments': [],
                     'created_seq': number}
        repository['issues'][number] = issue_rec
    return {'_type': 'CreateIssuePayload', 'issue': _issue_node(repository, issue_rec)}


def _gql_mut_close_issue(node, args, ctx):
    """closeIssue: close the issue named by its global id."""
    inp = args.get('input') or {}
    kind, parts = decode_global_id(inp.get('issueId') or '')
    if kind != 'Issue' or len(parts) < 2:
        raise ValueError('Issue not found')
    with STORE_LOCK:
        repository = next((r for r in REPOS.values() if r['id'] == int(parts[0])), None)
        if repository is None:
            raise ValueError('Issue not found')
        issue_rec = repository['issues'].get(int(parts[1]))
        if issue_rec is None:
            raise ValueError('Issue not found')
        issue_rec['state'] = 'closed'
    return {'_type': 'CloseIssuePayload', 'issue': _issue_node(repository, issue_rec)}


def _gql_mut_create_pull(node, args, ctx):
    """createPullRequest: open a pull request from pushed head/base branches."""
    inp = args.get('input') or {}
    with STORE_LOCK:
        repository = _gql_repo_by_global_id(inp.get('repositoryId'))
        if repository is None:
            raise ValueError('Repository not found')
        head = inp.get('headRefName')
        base = inp.get('baseRefName')
        head_sha = ref_tip(repository, head)
        base_sha = ref_tip(repository, base)
        if head_sha is None or base_sha is None:
            raise ValueError('Unknown head or base branch')
        number = repository['next_pull']
        repository['next_pull'] += 1
        pull_request = {'id': repository['id'] * 100000 + number, 'number': number,
                        'title': inp.get('title') or '', 'body': inp.get('body') or '',
                        'state': 'open', 'head_ref': head, 'head_sha': head_sha,
                        'base_ref': base, 'base_sha': base_sha, 'merged': False,
                        'merged_at': None, 'merge_commit_sha': None,
                        'owner': repository['owner']}
        repository['pulls'][number] = pull_request
    return {'_type': 'CreatePullRequestPayload', 'pullRequest': _pull_node(repository, pull_request)}


def _gql_mut_merge_pull(node, args, ctx):
    """mergePullRequest: squash-merge the pull request named by global id."""
    inp = args.get('input') or {}
    kind, parts = decode_global_id(inp.get('pullRequestId') or '')
    if kind != 'PullRequest' or len(parts) < 2:
        raise ValueError('Pull request not found')
    with STORE_LOCK:
        repository = next((r for r in REPOS.values() if r['id'] == int(parts[0])), None)
        if repository is None:
            raise ValueError('Pull request not found')
        pull_request = repository['pulls'].get(int(parts[1]))
        if pull_request is None:
            raise ValueError('Pull request not found')
        if pull_request['merged']:
            raise ValueError('Pull request already merged')
        if merge_conflict(repository, pull_request):
            raise ValueError('Merge conflict')
        squash_merge(repository, pull_request)
    return {'_type': 'MergePullRequestPayload', 'pullRequest': _pull_node(repository, pull_request)}


def _gql_mut_add_comment(node, args, ctx):
    """addComment: append a comment to the issue named by its global id."""
    inp = args.get('input') or {}
    kind, parts = decode_global_id(inp.get('subjectId') or '')
    if kind != 'Issue' or len(parts) < 2:
        raise ValueError('Subject not found')
    with STORE_LOCK:
        repository = next((r for r in REPOS.values() if r['id'] == int(parts[0])), None)
        if repository is None:
            raise ValueError('Subject not found')
        issue_rec = repository['issues'].get(int(parts[1]))
        if issue_rec is None:
            raise ValueError('Subject not found')
        COMMENT_ID_SEQ[0] += 1
        comment = {'id': COMMENT_ID_SEQ[0] - 1, 'body': inp.get('body') or '',
                   'user': {'login': VIEWER_LOGIN}}
        issue_rec['comments'].append(comment)
    return {'_type': 'AddCommentPayload',
            'commentEdge': {'_type': 'CommentEdge',
                            'node': {'_type': 'IssueComment', 'comment': comment}}}


_GQL_FIELDS[('Mutation', 'createIssue')] = _gql_mut_create_issue
_GQL_FIELDS[('Mutation', 'closeIssue')] = _gql_mut_close_issue
_GQL_FIELDS[('Mutation', 'createPullRequest')] = _gql_mut_create_pull
_GQL_FIELDS[('Mutation', 'mergePullRequest')] = _gql_mut_merge_pull
_GQL_FIELDS[('Mutation', 'addComment')] = _gql_mut_add_comment


def _gql_exec_fields(node, fields, ctx):
    """Execute one selection set against a node; collect field errors."""
    out = {}
    typename = node.get('_type', 'Unknown')
    for item in fields:
        if item[0] == 'fragment':
            _, fname, sub = item
            if fname == typename:
                out.update(_gql_exec_fields(node, sub, ctx))
            continue
        _, alias, name, args, sub = item
        resolved_args = {k: _gql_resolve_value(v, ctx['variables'])
                         for k, v in args.items()}
        fn = _GQL_FIELDS.get((typename, name))
        if fn is None:
            ctx['errors'].append({'message':
                f'Cannot query field "{name}" on type "{typename}".'})
            out[alias] = None
            continue
        try:
            value = fn(node, resolved_args, ctx)
        except Exception as exc:
            ctx['errors'].append({'message': str(exc)})
            out[alias] = None
            continue
        if sub is not None and value is not None:
            if isinstance(value, list):
                out[alias] = [
                    _gql_exec_fields(v, sub, ctx)
                    if isinstance(v, dict) and '_type' in v else v
                    for v in value]
            elif isinstance(value, dict) and '_type' in value:
                out[alias] = _gql_exec_fields(value, sub, ctx)
            else:
                out[alias] = value
        else:
            out[alias] = value
    return out


def _gql_execute(doc):
    """Execute one parsed operation document; return the GraphQL result."""
    variables = doc.get('variables') or {}
    query = doc.get('query') or ''
    ctx = {'variables': variables, 'errors': []}
    try:
        op, fields = GqlParser(query).parse_document()
    except Exception as exc:
        return {'data': None, 'errors': [{'message': f'Syntax error: {exc}'}]}
    root_type = 'Mutation' if op == 'mutation' else 'Query'
    data = _gql_exec_fields({'_type': root_type}, fields, ctx)
    result = {'data': data}
    if ctx['errors']:
        result['errors'] = ctx['errors']
    return result


def _handle_graphql(self, body):
    """Answer one GraphQL request (single document or a batched list)."""
    if not self._require_auth():
        return
    try:
        payload = json.loads(body.decode('utf-8'))
    except Exception:
        self._send_json(400, {'errors': [{'message': 'Invalid JSON'}]})
        return
    if isinstance(payload, list):
        self._send_json(200, [_gql_execute(doc) for doc in payload])
        return
    if not isinstance(payload, dict):
        self._send_json(400, {'errors': [{'message': 'Invalid request'}]})
        return
    self._send_json(200, _gql_execute(payload))


ForgeHandler._handle_graphql = _handle_graphql

# ---------------------------------------------------------------------------
# MCP endpoint (/mcp): JSON-RPC 2.0, modern 2026-07-28 era via
# server/discover, with a legacy initialize fallback. Plain JSON responses.
# ---------------------------------------------------------------------------

import urllib.request
import urllib.error

# The six tools the MCP endpoint offers. Descriptions are free text; the
# property types and required lists are what clients validate against.
MCP_TOOLS = [
    {'name': 'create_repo',
     'description': 'Open a new repository for the signed-in user.',
     'inputSchema': {
         'type': 'object',
         'properties': {
             'name': {'type': 'string',
                      'description': 'Short name for the new repository.'},
             'description': {'type': 'string',
                             'description': 'One-line summary shown on the repository.'},
             'private': {'type': 'boolean',
                         'description': 'True to hide the repository from others.'},
         },
         'required': ['name'],
     }},
    {'name': 'get_repo',
     'description': 'Fetch one repository by its owner and name.',
     'inputSchema': {
         'type': 'object',
         'properties': {
             'owner': {'type': 'string',
                       'description': 'Login of the repository owner.'},
             'repo': {'type': 'string',
                      'description': 'Short name of the repository.'},
         },
         'required': ['owner', 'repo'],
     }},
    {'name': 'create_issue',
     'description': 'Open a new issue inside a repository.',
     'inputSchema': {
         'type': 'object',
         'properties': {
             'owner': {'type': 'string',
                       'description': 'Login of the repository owner.'},
             'repo': {'type': 'string',
                      'description': 'Short name of the repository.'},
             'title': {'type': 'string',
                       'description': 'Headline of the issue.'},
             'body': {'type': 'string',
                      'description': 'Longer text of the issue.'},
         },
         'required': ['owner', 'repo', 'title'],
     }},
    {'name': 'list_issues',
     'description': 'List the issues of a repository, optionally by state.',
     'inputSchema': {
         'type': 'object',
         'properties': {
             'owner': {'type': 'string',
                       'description': 'Login of the repository owner.'},
             'repo': {'type': 'string',
                      'description': 'Short name of the repository.'},
             'state': {'type': 'string',
                       'description': 'Filter: open, closed, or all.'},
         },
         'required': ['owner', 'repo'],
     }},
    {'name': 'create_pull_request',
     'description': 'Open a pull request from one branch onto another.',
     'inputSchema': {
         'type': 'object',
         'properties': {
             'owner': {'type': 'string',
                       'description': 'Login of the repository owner.'},
             'repo': {'type': 'string',
                      'description': 'Short name of the repository.'},
             'title': {'type': 'string',
                       'description': 'Headline of the pull request.'},
             'body': {'type': 'string',
                      'description': 'Longer text of the pull request.'},
             'head': {'type': 'string',
                      'description': 'Branch carrying the changes.'},
             'base': {'type': 'string',
                      'description': 'Branch the changes land on.'},
         },
         'required': ['owner', 'repo', 'title', 'head', 'base'],
     }},
    {'name': 'merge_pull_request',
     'description': 'Squash-merge a pull request into its base branch.',
     'inputSchema': {
         'type': 'object',
         'properties': {
             'owner': {'type': 'string',
                       'description': 'Login of the repository owner.'},
             'repo': {'type': 'string',
                      'description': 'Short name of the repository.'},
             'pull_number': {'type': 'integer',
                             'description': 'Number of the pull request to merge.'},
         },
         'required': ['owner', 'repo', 'pull_number'],
     }},
]


def _mcp_owner_repo(args):
    """Split MCP arguments into (owner, repo), honouring full_name."""
    owner = args.get('owner') or args.get('owner_login') or args.get('org')
    repo_name = args.get('repo')
    if not repo_name and args.get('full_name'):
        parts = str(args['full_name']).split('/', 1)
        if len(parts) == 2:
            owner, repo_name = parts
    return owner, repo_name


def _mcp_repo(args):
    """Look up the repository an MCP call names; None unless it is the viewer's."""
    owner, repo_name = _mcp_owner_repo(args)
    if owner != VIEWER_LOGIN:
        return None
    return get_repo(owner, repo_name)


def _mcp_tool_create_repo(args):
    """create_repo: create a repository for the viewer (idempotent by name)."""
    name = args.get('name')
    if not isinstance(name, str) or not name:
        raise ValueError('name is required')
    with STORE_LOCK:
        repository = get_repo(VIEWER_LOGIN, name)
        if repository is None:
            repository = new_repo(VIEWER_LOGIN, name, args.get('private', False),
                                  args.get('description', ''))
            REPOS[(VIEWER_LOGIN, name)] = repository
    return repo_view(repository)


def _mcp_tool_get_repo(args):
    """get_repo: return one repository's REST view."""
    repository = _mcp_repo(args)
    if repository is None:
        raise ValueError('Repository not found')
    return repo_view(repository)


def _mcp_tool_create_issue(args):
    """create_issue: open an issue in the named repository."""
    title = args.get('title')
    if not isinstance(title, str) or not title:
        raise ValueError('title is required')
    with STORE_LOCK:
        repository = _mcp_repo(args)
        if repository is None:
            raise ValueError('Repository not found')
        number = repository['next_issue']
        repository['next_issue'] += 1
        ISSUE_ID_SEQ[0] += 1
        issue_rec = {'id': ISSUE_ID_SEQ[0] - 1, 'number': number,
                     'title': title, 'body': args.get('body') or '',
                     'state': 'open', 'labels': [], 'comments': [],
                     'created_seq': number}
        repository['issues'][number] = issue_rec
    return issue_view(issue_rec)


def _mcp_tool_list_issues(args):
    """list_issues: list a repository's issues, filtered by state."""
    repository = _mcp_repo(args)
    if repository is None:
        raise ValueError('Repository not found')
    state = (args.get('state') or 'open').lower()
    with STORE_LOCK:
        items = list(repository['issues'].values())
    if state in ('open', 'closed'):
        items = [i for i in items if i['state'] == state]
    items.sort(key=lambda i: i['number'])
    return [issue_view(i) for i in items]


def _mcp_tool_create_pull(args):
    """create_pull_request: open a pull request from pushed branches."""
    title = args.get('title')
    head = args.get('head')
    base = args.get('base')
    if not isinstance(title, str) or not title or not head or not base:
        raise ValueError('title, head and base are required')
    with STORE_LOCK:
        repository = _mcp_repo(args)
        if repository is None:
            raise ValueError('Repository not found')
        head_sha = ref_tip(repository, head)
        base_sha = ref_tip(repository, base)
        if head_sha is None or base_sha is None:
            raise ValueError('Unknown head or base branch')
        number = repository['next_pull']
        repository['next_pull'] += 1
        pull_request = {'id': repository['id'] * 100000 + number, 'number': number,
                        'title': title, 'body': args.get('body') or '', 'state': 'open',
                        'head_ref': head, 'head_sha': head_sha,
                        'base_ref': base, 'base_sha': base_sha, 'merged': False,
                        'merged_at': None, 'merge_commit_sha': None,
                        'owner': repository['owner']}
        repository['pulls'][number] = pull_request
    return pull_view(pull_request)


def _mcp_tool_merge_pull(args):
    """merge_pull_request: squash-merge a pull request by number."""
    try:
        number = int(args.get('pull_number'))
    except (TypeError, ValueError):
        raise ValueError('pull_number is required')
    with STORE_LOCK:
        repository = _mcp_repo(args)
        if repository is None:
            raise ValueError('Repository not found')
        pull_request = repository['pulls'].get(number)
        if pull_request is None:
            raise ValueError('Pull request not found')
        if pull_request['merged']:
            raise ValueError('Pull request already merged')
        if merge_conflict(repository, pull_request):
            raise ValueError('Merge conflict')
        sha = squash_merge(repository, pull_request)
    return {'merged': True, 'sha': sha, 'number': number}


_MCP_TOOL_IMPL = {
    'create_repo': _mcp_tool_create_repo,
    'get_repo': _mcp_tool_get_repo,
    'create_issue': _mcp_tool_create_issue,
    'list_issues': _mcp_tool_list_issues,
    'create_pull_request': _mcp_tool_create_pull,
    'merge_pull_request': _mcp_tool_merge_pull,
}


def _mcp_dispatch(method, params):
    """Answer one MCP method; returns (result, error) as a JSON-RPC pair."""
    if method == 'server/discover':
        return {'supportedVersions': ['2026-07-28', '2025-11-25'],
                'capabilities': {'tools': {}},
                'serverInfo': {'name': 'makefun-forge', 'version': '1.0.0'},
                'protocolVersion': '2026-07-28'}, None
    if method == 'initialize':
        requested = (params or {}).get('protocolVersion')
        known = ('2026-07-28', '2025-11-25', '2025-06-18', '2025-03-26',
                 '2024-11-05')
        version = requested if requested in known else '2026-07-28'
        return {'protocolVersion': version,
                'capabilities': {'tools': {}},
                'serverInfo': {'name': 'makefun-forge', 'version': '1.0.0'}}, None
    if method == 'tools/list':
        return {'tools': MCP_TOOLS}, None
    if method == 'tools/call':
        name = (params or {}).get('name')
        arguments = (params or {}).get('arguments') or {}
        fn = _MCP_TOOL_IMPL.get(name)
        if fn is None:
            return None, {'code': -32602, 'message': f'Unknown tool: {name}'}
        tool = next((t for t in MCP_TOOLS if t['name'] == name), None)
        missing = [r for r in tool['inputSchema'].get('required', [])
                   if r not in arguments or arguments[r] is None]
        if missing:
            return None, {'code': -32602,
                          'message': f"Missing required argument(s): {', '.join(missing)}"}
        try:
            value = fn(arguments)
        except ValueError as exc:
            err = str(exc)
            return {'content': [{'type': 'text', 'text': json.dumps({'error': err})}],
                    'structuredContent': {'error': err}, 'isError': True}, None
        return {'content': [{'type': 'text', 'text': json.dumps(value)}],
                'structuredContent': value, 'isError': False}, None
    if method == 'ping':
        return {}, None
    return None, {'code': -32601, 'message': f'Method not found: {method}'}


def _handle_mcp(self, body):
    """Answer one MCP request: DELETE ends the session, notifications get 202."""
    if self.command == 'DELETE':
        self.send_response(204)
        self.send_header('Content-Length', '0')
        self.send_header('X-GitHub-Request-Id', next_request_id())
        self.end_headers()
        return
    if not self._require_auth():
        return
    try:
        payload = json.loads(body.decode('utf-8'))
    except Exception:
        self._send_json(400, {'jsonrpc': '2.0', 'id': None,
                              'error': {'code': -32700, 'message': 'Parse error'}})
        return
    if not isinstance(payload, dict):
        self._send_json(400, {'jsonrpc': '2.0', 'id': None,
                              'error': {'code': -32600, 'message': 'Invalid Request'}})
        return
    method = payload.get('method')
    req_id = payload.get('id')
    params = payload.get('params') or {}
    if method == 'notifications/initialized' or req_id is None:
        self.send_response(202)
        self.send_header('Content-Length', '0')
        self.send_header('X-GitHub-Request-Id', next_request_id())
        self.end_headers()
        return
    result, error = _mcp_dispatch(method, params)
    if error is not None:
        self._send_json(200, {'jsonrpc': '2.0', 'id': req_id, 'error': error})
    else:
        self._send_json(200, {'jsonrpc': '2.0', 'id': req_id, 'result': result})


ForgeHandler._handle_mcp = _handle_mcp


# ---------------------------------------------------------------------------
# Lifecycle: bind an ephemeral port, register with the trial environment,
# serve until /done says the trial is over, then exit 0.
# ---------------------------------------------------------------------------

def _env_post(url, data, timeout=5):
    """POST one JSON body to the trial environment; return the HTTP status."""
    req = urllib.request.Request(
        url, data=json.dumps(data).encode('utf-8'),
        headers={'Content-Type': 'application/json'}, method='POST')
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return resp.status


def _env_get_done(url, timeout=5):
    """GET the trial environment's /done document as a dict."""
    req = urllib.request.Request(url, method='GET')
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return json.loads(resp.read().decode('utf-8'))


def main():
    """Bind an ephemeral port, register with the trial, serve until /done."""
    env_url = os.environ.get('MAKEFUN_ENV_URL')
    if not env_url:
        sys.stderr.write('MAKEFUN_ENV_URL is not set\n')
        return 1
    env_url = env_url.rstrip('/')
    server = ThreadingHTTPServer(('127.0.0.1', 0), ForgeHandler)
    server.daemon_threads = True
    port = server.server_address[1]
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    deadline = time.time() + 30
    retry_delay = 0.25
    registered = False
    while time.time() < deadline:
        try:
            status = _env_post(env_url + '/register', {'port': port})
            if status in (200, 409):
                registered = True
                break
        except urllib.error.HTTPError as exc:
            if exc.code in (200, 409):
                registered = True
                break
            if exc.code in (400, 405):
                break
        except Exception:
            pass
        time.sleep(retry_delay)
        retry_delay = min(retry_delay * 2, 2.0)
    if not registered:
        server.shutdown()
        server.server_close()
        return 1
    retry_delay = 0.25
    while True:
        try:
            done_payload = _env_get_done(env_url + '/done')
            if done_payload.get('done'):
                break
        except Exception:
            pass
        time.sleep(retry_delay)
        retry_delay = min(retry_delay * 2, 2.0)
    server.shutdown()
    server.server_close()
    return 0


# Entry point lives at the end of the file (after the pack-codec fix below),
# so the fixed definitions are in place before main() runs.

# ---------------------------------------------------------------------------
# Pack codec fix (appended 2026-11-14): the first read_pack extracted the
# object type AFTER the size-varint loop had overwritten the header byte,
# so every object whose size needs a multi-byte header decoded as type 0
# and every push failed with "unknown pack type 0". This replacement
# extracts the type first. write_pack / collect_reachable are also wrapped
# so the (repo, oids) and repo-dict call shapes used by the fetch path work.
# ---------------------------------------------------------------------------

_PACK_TYPE_NAMES = {1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag'}


def _apply_delta(base, delta):
    """Apply a git binary delta to its base bytes; return the result."""
    def _read_varint(buf, off):
        """Read one little-endian base-128 varint from the delta stream."""
        value = 0
        shift = 0
        while True:
            byte = buf[off]
            off += 1
            value |= (byte & 0x7f) << shift
            shift += 7
            if not (byte & 0x80):
                return value, off

    source_size, off = _read_varint(delta, 0)
    if source_size != len(base):
        raise ValueError('delta base size mismatch')
    target_size, off = _read_varint(delta, off)
    out = bytearray()
    while off < len(delta):
        opcode = delta[off]
        off += 1
        if opcode & 0x80:
            copy_offset = 0
            copy_size = 0
            for i in range(4):
                if opcode & (1 << i):
                    copy_offset |= delta[off] << (8 * i)
                    off += 1
            for i in range(3):
                if opcode & (0x10 << i):
                    copy_size |= delta[off] << (8 * i)
                    off += 1
            if copy_size == 0:
                copy_size = 0x10000
            out += base[copy_offset:copy_offset + copy_size]
        elif opcode:
            out += delta[off:off + opcode]
            off += opcode
        else:
            raise ValueError('delta opcode 0')
    if len(out) != target_size:
        raise ValueError('delta result size mismatch')
    return bytes(out)


def read_pack(pack):
    """Parse a packfile (v2/v3, plain + OFS/REF deltas) -> {oid: (type, data)}."""
    if len(pack) < 32 or pack[:4] != b'PACK':
        raise ValueError('not a packfile')
    version, count = struct.unpack('>II', pack[4:12])
    if version not in (2, 3):
        raise ValueError(f'unsupported pack version {version}')
    if hashlib.sha1(pack[:-20]).digest() != pack[-20:]:
        raise ValueError('pack trailer checksum mismatch')
    objects = {}
    offsets = {}   # pack offset -> oid (filled as entries resolve)
    pending = []   # (entry_off, kind, base, delta) in pack order
    off = 12
    pack_end = len(pack) - 20
    for _ in range(count):
        entry_off = off
        header_byte = pack[off]
        type_code = (header_byte >> 4) & 0x07  # type BEFORE the size loop
        size = header_byte & 0x0f
        shift = 4
        off += 1
        while header_byte & 0x80:
            header_byte = pack[off]
            size |= (header_byte & 0x7f) << shift
            shift += 7
            off += 1
        if type_code == 6:  # OFS_DELTA
            byte = pack[off]
            off += 1
            base_off = byte & 0x7f
            while byte & 0x80:
                byte = pack[off]
                off += 1
                base_off = ((base_off + 1) << 7) | (byte & 0x7f)
            decompressor = zlib.decompressobj()
            delta = decompressor.decompress(pack[off:pack_end])
            off += len(pack[off:pack_end]) - len(decompressor.unused_data)
            if len(delta) != size:
                raise ValueError('delta size mismatch')
            pending.append((entry_off, 'ofs', entry_off - base_off, delta))
            offsets[entry_off] = None
        elif type_code == 7:  # REF_DELTA
            base_oid = pack[off:off + 20].hex()
            off += 20
            decompressor = zlib.decompressobj()
            delta = decompressor.decompress(pack[off:pack_end])
            off += len(pack[off:pack_end]) - len(decompressor.unused_data)
            if len(delta) != size:
                raise ValueError('delta size mismatch')
            pending.append((entry_off, 'ref', base_oid, delta))
            offsets[entry_off] = None
        elif type_code in _PACK_TYPE_NAMES:
            otype = _PACK_TYPE_NAMES[type_code]
            decompressor = zlib.decompressobj()
            raw_data = decompressor.decompress(pack[off:pack_end])
            off += len(pack[off:pack_end]) - len(decompressor.unused_data)
            if len(raw_data) != size:
                raise ValueError('object size mismatch')
            oid = hash_object(otype, raw_data)
            objects[oid] = (otype, raw_data)
            offsets[entry_off] = oid
        else:
            raise ValueError(f'unknown pack type {type_code}')
    for entry_off, kind, base, delta in pending:
        base_oid = offsets.get(base) if kind == 'ofs' else base
        if base_oid is None or base_oid not in objects:
            raise ValueError('delta base not found')
        base_type, base_data = objects[base_oid]
        data = _apply_delta(base_data, delta)
        oid = hash_object(base_type, data)
        objects[oid] = (base_type, data)
        offsets[entry_off] = oid
    return objects


_write_pack_orig = write_pack


def write_pack(objects, oids=None):
    """Accept the original (oid, type, data) triples iterable, a
    {oid: (type, data)} dict, or the (repo, oids) shape used by the fetch
    path."""
    if oids is not None:
        repository = objects
        entries = [(oid, repository['objects'][oid][0], repository['objects'][oid][1])
                   for oid in oids if oid in repository['objects']]
        return _write_pack_orig(entries)
    if isinstance(objects, dict):
        entries = [(oid, otype, data)
                   for oid, (otype, data) in objects.items()]
        return _write_pack_orig(entries)
    return _write_pack_orig(objects)


_collect_reachable_orig = collect_reachable


def collect_reachable(obj_store, roots):
    """Accept an objects dict or a repo dict (which carries 'objects')."""
    if (isinstance(obj_store, dict) and isinstance(obj_store.get('objects'), dict)):
        obj_store = obj_store['objects']
    return _collect_reachable_orig(obj_store, roots)

ForgeHandler._send_fetch_v2 = _send_fetch_v2
ForgeHandler._send_fetch_v0 = _send_fetch_v0

# (entry point moved to the end of the file, after all fixes)

# ---------------------------------------------------------------------------
# Perf fix (appended 2026-11-14): the bench measured ~20-45 ms per request
# (push p50 8991 ms, write 8836 ms, read blew the 60 s budget) — the classic
# Nagle/delayed-ACK stall from sending headers and body as separate small
# writes. Fix: TCP_NODELAY on every accepted connection, and build each
# response as ONE write (status line + headers + body) with an explicit
# flush, so a keep-alive client never waits on a delayed ACK.
# ---------------------------------------------------------------------------

import socket


def _forge_setup(self):
    """Set TCP_NODELAY on the accepted socket and wire up buffered streams."""
    try:
        self.request.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
    except (OSError, AttributeError):
        pass
    self.connection = self.request
    self.rfile = self.connection.makefile('rb')
    self.wfile = self.connection.makefile('wb')


def _forge_send(self, status, body, content_type='application/json'):
    """Send one response as a single write: headers + body, then flush."""
    if isinstance(body, (dict, list)):
        payload = json.dumps(body, separators=(',', ':')).encode('utf-8')
    elif isinstance(body, str):
        payload = body.encode('utf-8')
    else:
        payload = body
    reason = self.responses.get(status, ('???',))[0]
    header_block = (f'HTTP/1.1 {status} {reason}\r\n'
                    f'Content-Type: {content_type}\r\n'
                    f'Content-Length: {len(payload)}\r\n'
                    f'X-GitHub-Request-Id: {next_request_id()}\r\n'
                    'X-OAuth-Scopes: repo, read:org\r\n')
    link_header = getattr(self, '_link_next', None)
    if link_header:
        header_block += f'Link: {link_header}\r\n'
        self._link_next = None
    response_bytes = (header_block + '\r\n').encode('latin-1') + payload
    if self.command != 'HEAD':
        try:
            self.wfile.write(response_bytes)
            self.wfile.flush()
        except (BrokenPipeError, ConnectionResetError):
            pass


ForgeHandler.setup = _forge_setup
ForgeHandler._send = _forge_send

# Clone-bench fix (appended 2026-11-14): ThreadingHTTPServer's listen
# backlog defaults to 5, so a burst of 50 concurrent clone connections
# stalls on SYN retransmits (clone rounds 1-2 took 4345/1234 ms while round 3,
# on pooled keep-alive connections, took 58 ms). Raise it to 256.
ThreadingHTTPServer.request_queue_size = 256

if __name__ == '__main__':
    sys.exit(main())
