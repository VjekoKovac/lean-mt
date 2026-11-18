#!/usr/bin/env bash
# Restore only the upstream proof cache corresponding to the project's exact pin.
set -euo pipefail
cd "$(dirname "$0")/.."
sha=2df65101324c0625904b6becbff317df88d8c3de
dep=.lake/packages/Nyll
if [[ ! -d "$dep" ]]; then
  # Lake materializes the revisions in the committed lockfile.
  lake env true
fi
if [[ "$(git -C "$dep" rev-parse HEAD)" != "$sha" ]]; then
  echo "Nyll checkout differs from the pinned release at $sha." >&2
  exit 1
fi
archive_dir=$(mktemp -d)
trap 'rm -rf "$archive_dir"' EXIT
release="https://github.com/n-yamaguchi-0729/SawinTotallyRealTowers/releases/download/cache-$sha-linux-x86_64"
for file in cache-manifest.json proof-cache-001.tar.gz proof-cache-002.tar.gz; do
  curl --fail --location --silent --show-error --retry 3 "$release/$file" -o "$archive_dir/$file"
done
(
  cd "$archive_dir"
  sha256sum --check <<'DIGESTS'
06b2df35938291c5e3009d4464bd6813408702ccf89e02f9b270f4fcb4fa12e1  cache-manifest.json
dfb0e25152b9cc27f26d5986af2f1879b583e5261ecdad0f290b7453c24707dc  proof-cache-001.tar.gz
de1a67f56962d737f9daa3915c5de4306dbe484ce36e6733b13cf5bc77d17472  proof-cache-002.tar.gz
DIGESTS
)
(
  cd "$dep"
  python3 -B .github/scripts/cache-export.py restore --directory "$archive_dir"
)
