# github-core-clone — a GitHub-compatible git forge in one Python file

A single-process, standard-library-only reimplementation of the core of
GitHub: git smart HTTP, the REST API v3, GraphQL API v4, and an MCP server
— all served from one process with no git binary and no outside service.

## What it serves

- **Git smart HTTP** at `/{owner}/{repo}.git` — `upload-pack` (protocol v2)
  and `receive-pack` (v0), with a from-scratch packfile codec (plain objects,
  OFS/REF deltas, zlib streams) and full ref advertisement.
- **REST API v3** under `/api/v3` — repositories, branches, git refs, commits,
  contents, labels, issues, comments, pull requests, and merges.
- **GraphQL API v4** at `/api/graphql` — queries, mutations, Relay-style
  connections with cursors, fragments, variables, and introspection.
- **MCP** at `/mcp` — JSON-RPC tools to create/list repositories, issues, and
  pull requests, and to merge them.

## How it runs

The forge binds an ephemeral port on loopback, tells the trial environment
about it with `POST $MAKEFUN_ENV_URL/register {"port": <port>}`, then serves
until `GET $MAKEFUN_ENV_URL/done` reports `{"done": true}` and exits 0.

```sh
MAKEFUN_ENV_URL=http://127.0.0.1:8080 python3 main.py
```

Everything lives in memory: repositories, objects, issues, and pull
requests are created through the API and vanish when the process exits.
Authentication is a bearer token (`MAKEFUN_SHOP_TOKEN`); the viewer is a
fixed demo user, so every repository belongs to the same owner.

## Layout

- `main.py` — the whole forge (HTTP server, pack codec, REST, GraphQL, MCP).
- `entry.txt` — one-line entry description.
- `LICENSE` — MIT.

## Notes

- Packfiles are parsed and written by hand; `git` itself is never invoked.
- Pushes, clones, and fetches all run through the same in-memory object
  store, so a repository pushed over smart HTTP is immediately visible to
  the REST, GraphQL, and MCP surfaces.
- Responses are written as a single TCP write with `TCP_NODELAY`, which
  keeps keep-alive clients off the Nagle/delayed-ACK stall.
