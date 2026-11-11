# Source me (`. scripts/git-hermetic.sh`) from any script that creates a scratch git repository or remote (git init / git clone), and from the test of a gate
# that runs git. Hermetic git: the result must not depend on the box it runs on (a developer's ~/.gitconfig, a cold machine, an enclosing hook).
# What went red on main (a cold machine, not CI): the checkout there was SHALLOW and a push from a shallow repository is
# refused ("shallow update not allowed"); the developer's full clone never showed it. So a scratch base is built from a TREE (git_snapshot_repo), not by
# pushing history. Ambient config (default branch, identity, signing, hooksPath, GIT_DIR from an enclosing hook) is cut off and replaced by explicit values.
# The lint (scripts/lint-git-hermetic.sh, in Tier 1) fails a script that creates a repository without sourcing this file.
for _v in $(compgen -e | grep -E '^(GIT_CONFIG_.*|GIT_(DIR|WORK_TREE|INDEX_FILE|OBJECT_DIRECTORY|ALTERNATE_OBJECT_DIRECTORIES|COMMON_DIR|PREFIX|NAMESPACE|SHALLOW_FILE|CEILING_DIRECTORIES|AUTHOR_.*|COMMITTER_.*|SSH_COMMAND|EXEC_PATH|TEMPLATE_DIR))$'); do   # determinism-ok: unsets, order is irrelevant
  unset "$_v"
done
unset _v
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_SYSTEM=/dev/null GIT_CONFIG_NOSYSTEM=1          # no user, no system config
export GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=init.defaultBranch GIT_CONFIG_VALUE_0=main         # the branch name is ours, not the machine's
export GIT_AUTHOR_NAME=vbm-json-test GIT_AUTHOR_EMAIL=vbm-json-test@vbm-json.invalid GIT_COMMITTER_NAME=vbm-json-test GIT_COMMITTER_EMAIL=vbm-json-test@vbm-json.invalid   # identity: explicit, never ambient
export GIT_TERMINAL_PROMPT=0 GIT_EDITOR=true
# git_snapshot_repo REV DEST_BARE: a bare repository at DEST_BARE whose main is ONE root commit carrying REV's tree. Works from a shallow or a full clone alike
# (a root commit reaches no shallow boundary), and the content is exactly REV's.
git_snapshot_repo() {
  local rev=$1 dest=$2 c
  c=$(git commit-tree "$rev^{tree}" -m "snapshot of $(git rev-parse --short "$rev")") || return 1
  git init -q --bare -b main "$dest" && git push -q "$dest" "$c:refs/heads/main"
}
