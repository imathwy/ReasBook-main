# ADR-0017: Run the reviewer as a SiFlow general service

## Status

Accepted. The user has registered the service callback; OAuth activation uses
the same service UUID and an independently prepared runtime configuration.

## Date

2026-09-06

## Context

The existing reader runs behind a development-workbench port proxy. Its lifetime
depends on that workbench process. The user requested a managed SiFlow service
for the same reviewer, including book/declaration deep links. Its existing OAuth
callback points to localhost, which is not a usable remote-service callback.

## Decision

- Use the SiFlow 0.3.18 general-service API in cn-shanghai/changliu, with one
  replica, two sci.c22-2 units and HTTP port 8000. Keep `/ReasBook/` and item
  query parameters intact. Do not replace this with a batch compilation task.
- Deploy a separate application/SDK snapshot. Keep `.env`, credentials, tests,
  generated evidence and review-state files out of the application snapshot.
  Reuse the existing external evidence cache without launching Lean builds.
- Use a SQLite backup of existing review state in the new service's own state
  directory. Do not share a WAL database between workbench and service hosts.
  This is a point-in-time migration, not continuous database replication.
- Keep the old preview running during acceptance. Before enabling production
  review writes, choose the authoritative database and reconcile any reviews
  added to the old preview after the initial backup.
- Public reading is enabled; review mutations continue to require application
  authentication. Do not copy the localhost OAuth callback into production or
  put secrets in service commands. Enable sign-in only after the new HTTPS
  callback is registered with the identity provider, with secure cookies and a
  stable session secret injected by an appropriate runtime secret mechanism.
- Retain the service UUID and deployment plan in the external service cache.
  Inspect that UUID after a timeout; do not blindly create another service.
- Scope authentication cookies to the service's external `/ReasBook/` prefix,
  rather than the shared gateway hostname root. Preserve item queries across
  login. Normalize post-login return paths from human-readable gateway aliases
  to the registered callback's canonical prefix. Otherwise the session cookie
  is set successfully but is not sent to the page on the other alias. Do not
  widen cookie scope to the shared hostname to work around this mismatch.
  Stop the old replica before bringing up the updated one; do not use
  a rolling surge with the SQLite WAL database.

## Consequences

The service is independent of the workbench process, but still depends on its
shared Volume and pinned Python runtime. Two CPU units are an initial web-service
allocation, not a Lean compilation allocation. Scaling replicas requires a
database design that supports multiple hosts; it is not safe with the current
SQLite WAL store. Completed artifact builds and public artifact adoption remain
separate workflows. A running service does not establish complete book coverage.

The initial deployment served reading and existing review history. Enabling
OAuth does not establish a completed human login: verify authorization redirect,
secure cookie scope and invalid-callback rejection, then let the user complete
interactive sign-in. Do not write synthetic public comments as a smoke test.
