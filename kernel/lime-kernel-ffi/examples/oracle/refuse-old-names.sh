# Sourced by build-oracle.sh and run-oracle.sh. An old developer variable (the fork's ref, the oracle's path, under the old prefix) is what the frozen
# record still spells; under one of these scripts it would be ignored and the sweep would answer about something else, so it
# is refused by name (AGENTS.md §4 D159). `TM_DIR` is a user's, and `lime-core/src/devenv.rs` is the same rule for test arms.
old=$(compgen -e | grep -E '^TM_' | grep -vx 'TM_DIR' || true)
if [ -n "$old" ]; then
  for v in $old; do
    echo "$(basename "$0"): $v is the old spelling of LIME_${v#TM_}: unset $v and set LIME_${v#TM_}" >&2
  done
  exit 2
fi
