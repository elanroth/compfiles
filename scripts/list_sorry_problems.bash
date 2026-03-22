#!/usr/bin/env bash

set -euo pipefail

usage() {
  cat <<'EOF'
Usage: scripts/list_sorry_problems.bash [options]

List problem files under Compfiles that still contain `sorry`.

Options:
  --match REGEX   Only include problem IDs matching the regex.
  --paths         Include the file path after the problem ID.
  --counts        Include the number of `sorry` occurrences in each file.
  --prompt        Emit a Claude-ready bullet list with pretty problem names.
  -h, --help      Show this help text.

Examples:
  scripts/list_sorry_problems.bash
  scripts/list_sorry_problems.bash --match '^(Imo|Usa)'
  scripts/list_sorry_problems.bash --match '^Imo' --counts --paths
  scripts/list_sorry_problems.bash --match '^(Imo|Usa)' --prompt
EOF
}

pretty_name() {
  local problem_id="$1"
  if [[ "$problem_id" =~ ^([A-Za-z]+)([0-9]{4})P([0-9]+)$ ]]; then
    local prefix
    prefix="$(printf '%s' "${BASH_REMATCH[1]}" | tr '[:lower:]' '[:upper:]')"
    printf '%s %s P%s' "$prefix" "${BASH_REMATCH[2]}" "${BASH_REMATCH[3]}"
  else
    printf '%s' "$problem_id"
  fi
}

list_sorry_files() {
  if command -v rg >/dev/null 2>&1; then
    rg -l '\bsorry\b' Compfiles --glob '*.lean' | sort
  else
    find Compfiles -type f -name '*.lean' | sort | while IFS= read -r path; do
      if grep -q -w 'sorry' "$path"; then
        printf '%s\n' "$path"
      fi
    done
  fi
}

count_sorries_in_file() {
  local path="$1"
  if command -v rg >/dev/null 2>&1; then
    rg -o '\bsorry\b' "$path" | wc -l | tr -d '[:space:]'
  else
    { grep -ow 'sorry' "$path" || true; } | wc -l | tr -d '[:space:]'
  fi
}

match_regex='.*'
include_paths=0
include_counts=0
prompt_mode=0

while (($#)); do
  case "$1" in
    --match)
      shift
      if (($# == 0)); then
        echo "missing value for --match" >&2
        exit 1
      fi
      match_regex="$1"
      ;;
    --paths)
      include_paths=1
      ;;
    --counts)
      include_counts=1
      ;;
    --prompt)
      prompt_mode=1
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "unknown option: $1" >&2
      usage >&2
      exit 1
      ;;
  esac
  shift
done

if ((prompt_mode)); then
  echo "Please fetch solution writeups for these problems:"
fi

while IFS= read -r path; do
  problem_id="$(basename "$path" .lean)"
  if [[ ! "$problem_id" =~ $match_regex ]]; then
    continue
  fi

  count=""
  if ((include_counts)); then
    count="$(count_sorries_in_file "$path")"
  fi

  if ((prompt_mode)); then
    line="$(pretty_name "$problem_id") ($problem_id)"
  else
    line="$problem_id"
  fi

  if ((include_counts)); then
    line="$line [$count sorries]"
  fi

  if ((include_paths)); then
    line="$line $path"
  fi

  if ((prompt_mode)); then
    printf -- '- %s\n' "$line"
  else
    printf '%s\n' "$line"
  fi
done < <(list_sorry_files)
