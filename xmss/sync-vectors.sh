#!/usr/bin/env bash
# Copy EthLib's leanXMSS test vectors at one commit, or check the copy.
#
#     xmss/sync-vectors.sh <ethlib-commit>
#     xmss/sync-vectors.sh --check
#
# Replaces contracts/test/vectors/ethlib/xmss with the `verify` and `signature_index` cases of
# EthLib's tests/cryptography/xmss at that commit, checks every case against EthLib's
# SHA256SUMS, and records the commit in contracts/test/vectors/ethlib/COMMIT.
#
# With --check, it copies nothing: it fails unless contracts/test/vectors/ethlib/xmss is exactly
# those cases at the commit in COMMIT, with no file changed, missing or added.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
dest="$here/../contracts/test/vectors/ethlib"
# The operations LeanXmss.sol implements.
operations=(verify signature_index)

check=false
if [[ "${1:-}" == "--check" ]]; then
  check=true
  commit=$(<"$dest/COMMIT")
else
  commit=${1:?usage: sync-vectors.sh <ethlib-commit> | --check}
fi

# One archive of EthLib at that commit, unpacked outside the tree. Retried, so that a transient
# network error does not fail CI.
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
curl -fsSL --retry 5 --retry-all-errors \
  "https://codeload.github.com/ethereum/EthLib/tar.gz/$commit" -o "$work/ethlib.tar.gz"
tar -xzf "$work/ethlib.tar.gz" -C "$work"

src=$(echo "$work"/*/tests/cryptography/xmss)
[[ -d "$src" ]] || {
  echo "error: no tests/cryptography/xmss in EthLib at $commit" >&2
  exit 1
}

# The digests EthLib pins must hold before anything is copied or compared.
for operation in "${operations[@]}"; do
  (cd "$src" && grep " $operation/" SHA256SUMS | sha256sum --quiet -c -)
done

if $check; then
  status=0
  for operation in "${operations[@]}"; do
    diff -r "$src/$operation" "$dest/xmss/$operation" || status=1
  done
  # Nothing else may sit next to the copied operations.
  diff <(printf '%s\n' "${operations[@]}" | sort) <(ls "$dest/xmss") || status=1
  if [[ "$status" -ne 0 ]]; then
    echo "error: contracts/test/vectors/ethlib/xmss is not EthLib's cases at $commit" >&2
    exit 1
  fi
  echo "contracts/test/vectors/ethlib/xmss matches EthLib at $commit"
  exit 0
fi

rm -rf "$dest/xmss"
mkdir -p "$dest/xmss"
for operation in "${operations[@]}"; do
  cp -R "$src/$operation" "$dest/xmss/$operation"
  echo "copied $(find "$dest/xmss/$operation" -name data.yaml | wc -l) $operation cases"
done
echo "$commit" >"$dest/COMMIT"
