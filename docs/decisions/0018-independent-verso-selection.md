# 0018: Select approved project Verso independently

## Status

Accepted.

## Context

May and Forster have successful, content-verified project Verso producers while
the broader Docs assembly is not publishable. Replacing the whole evidence set
would lose existing compiled Graphs and could select incomplete Docs.

## Decision

Use an explicit reviewer-data selection per slug, pinning the original producer
result by SHA-256. Verify the entire producer tree using the existing finalizer
digest helper and content/browser canaries before activation. Runtime validates
the successful project result, ReleaseSpec membership, branch and matching source
commit. Only the Verso site root changes; Source, Docs and Graph remain bound to
the baseline. Report the separate Verso release ID in the resources API.

## Consequences

No original release, result or compilation cache is rewritten. Failed projects
are not adopted, and no whole-release or GitHub publication is implied. Deployment
must keep selected producer trees immutable. Runtime avoids hashing whole sites
on requests; invalid records fall back to baseline. Removal of a selection and a
reader restart rolls back without restoring or modifying review databases.
