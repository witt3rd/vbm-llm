# Going public: the record

This repository was made public by its owner on 2026-11-05. This page records what was checked, what the published history carries, and the order of the flip, so that a reader can see what "public-ready" meant here.

## History published as is

The history was **not** re-written or re-rooted: every commit hash is the one consumers pin (a pin records the 40-hex commit), so a rewrite would have broken every pinned consumer. What the history carries (scanned over every commit message, path, author line and changed line of every ref, 32 commits on `main`, no tags, no other branch):

- **The author identity.** The owner's name and e-mail appear as author and committer of every commit but the first (the same identity is already public in the owner's other repositories); the first commit carries a GitHub no-reply address.
- **Three public identifiers added as data:** the public half of the vbm-land release signing key (`scripts/land.signers`), the vendored update workflow's bot address, and a test-fixture address on an `.invalid` domain.
- Nothing else: no secret, no host name, no address, no local path, no other person's data, no private project name, none of the refused terms.

## What was checked (2026-11-05, on `main` at 64ce7ec)

| Check | Result |
|---|---|
| gitleaks 8.30.1, full history of every ref of a fresh mirror of the remote (31 commits scanned at that time), and the working tree | 0 findings |
| trufflehog 3.99.8, same scope | 0 verified, 0 unverified |
| the VBM public-readiness lint (hash list of private names, path patterns) over the tree | clean |
| a scan of every commit message, path, author line and changed line of all refs for the same hashes plus plain patterns (host names, home paths, e-mails, addresses) | only the accepted items above |
| `scripts/tier1.sh` in a fresh `ubuntu:24.04` container, network cut after the dependency fetch | passes |

## The flip, in order

Until the flip, CI ran on the owner's self-hosted runner. A public repository must not (a pull request from a fork could run code on that machine); `scripts/lint-workflows.py` fails Tier 1 on a `self-hosted` runner unless `.github/visibility` says `private`.

1. The owner changed the visibility and an anonymous `git clone` was checked.
2. The settings below that need a public repository were applied at once, and the self-hosted runner was removed. The workflows have no `pull_request` trigger, so no outside code reached it meanwhile.
3. One commit returned CI to hosted runners (`runs-on: ubuntu-latest`, `jdx/mise-action` pinned by sha to install the pinned Lean) and set `.github/visibility` to `public`; it landed with `scripts/land-direct` and its push CI was read green on a hosted runner.
4. The release-tag ruleset was applied once no release was in flight.

## Settings (each has a read-back)

1. Fork pull-request workflows need approval for **all outside collaborators**: `gh api -X PUT repos/witt3rd/vbm-llm/actions/permissions/fork-pr-contributor-approval -f approval_policy=all_external_contributors`; read back `gh api repos/witt3rd/vbm-llm/actions/permissions/fork-pr-contributor-approval`.
2. Read-only workflow token that cannot approve pull requests: `gh api -X PUT repos/witt3rd/vbm-llm/actions/permissions/workflow -f default_workflow_permissions=read -F can_approve_pull_request_reviews=false`; read back `gh api repos/witt3rd/vbm-llm/actions/permissions/workflow`.
3. Private vulnerability reporting: `gh api -X PUT repos/witt3rd/vbm-llm/private-vulnerability-reporting`; read back `gh api repos/witt3rd/vbm-llm/private-vulnerability-reporting`.
4. Secret scanning and push protection: `gh api -X PATCH repos/witt3rd/vbm-llm -F 'security_and_analysis[secret_scanning][status]=enabled' -F 'security_and_analysis[secret_scanning_push_protection][status]=enabled'`; read back `gh api repos/witt3rd/vbm-llm --jq .security_and_analysis`.
5. Delete head branches on merge: `gh api -X PATCH repos/witt3rd/vbm-llm -F delete_branch_on_merge=true`.
6. Protect `main` from deletion and non-fast-forward updates (no required pull request, no bypass list, so landing still works): `scripts/land/templates/ruleset-protect-main.json`; read back `gh api repos/witt3rd/vbm-llm/rules/branches/main --jq '.[].type'` prints `deletion` and `non_fast_forward`.
7. Protect release tags (`v*`) from deletion and update: `gh api repos/witt3rd/vbm-llm/rulesets --input scripts/land/templates/ruleset-protect-release-tags.json`; read back `gh api repos/witt3rd/vbm-llm/rulesets --jq '.[].name'`. No release exists yet.
8. No workflow uses `pull_request_target`, every workflow declares read-only `permissions:`, no secret is used, no deploy key exists, the runner list is empty (`gh api repos/witt3rd/vbm-llm/actions/runners`).
