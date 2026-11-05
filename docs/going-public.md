# Before going public

Do these in order; each is a checkable fact.

1. `runs-on` is a GitHub-hosted label in every workflow (no `self-hosted`), and the repository's self-hosted runner is removed
   (`gh api repos/OWNER/REPO/actions/runners` lists none).
2. `.github/visibility` says `public` (`scripts/lint-workflows.py` fails Tier 1 when a workflow names `self-hosted` and it does not say `private`).
3. `LAND_RED_MODE` in `scripts/land.conf` is unchanged (`push`).
4. The settings checklist `scripts/land/templates/PUBLIC-REPO-SETTINGS.md` is done.

## The runner switch, exactly

While private, `.github/workflows/ci.yml` runs both jobs on the owner's self-hosted runner (`runs-on: [self-hosted]`); a public repository must not (a pull request from a fork could run code on that machine). The single change that makes the repository publishable is one commit that:

1. replaces `runs-on: [self-hosted]` with `runs-on: ubuntu-latest` in both jobs, and the two trailing comments with nothing;
2. replaces the contents of `.github/visibility` with `public`;
3. leaves `scripts/land.conf` alone (the red check keeps reading the push run of `ci.yml`, now a hosted one).

`ci.yml` and `.github/visibility` are gate-defining: that commit lands by `scripts/land-direct` (the relabel-attack suite judges it) and is the owner's to approve. Then deregister the runner (the owner's runner host list; `gh api repos/OWNER/REPO/actions/runners` must list none), read one hosted push run to green, and only then change the visibility. The hosted job installs the pinned Lean by `mise install`; it has no cache of ours beyond `actions/cache` on `.lake`.

## What was checked before the flip

Recorded under the lane's data directory, not in this tree: gitleaks (full history and tree) and trufflehog (history) with zero findings; the public-readiness lint over the tree; the same hash and path checks over every commit and message of the history (the only hit is the author name in commit metadata, the same identity as the public `vbm-json`; the owner may still choose to publish from a squashed history); a clean `ubuntu:24.04` container clone running Tier 1 from nothing (image digest and log).
