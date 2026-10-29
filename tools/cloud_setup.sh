#!/bin/sh
# Install what leanzempic needs on a fresh Linux x86_64 machine (a cloud session, a container): the same
# toolchain CI uses. Idempotent. Afterwards:  . tools/cloud_env.sh   (puts elan and ghcup on PATH)
set -eu
if command -v apt-get >/dev/null 2>&1; then
  SUDO=""
  if [ "$(id -u)" -ne 0 ] && command -v sudo >/dev/null 2>&1; then SUDO="sudo"; fi
  $SUDO apt-get update -y >/dev/null
  $SUDO apt-get install -y build-essential curl git python3 openssl libgmp-dev libtinfo-dev libffi-dev zlib1g-dev xz-utils >/dev/null
fi
if [ ! -x "$HOME/.elan/bin/elan" ]; then
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
fi
if [ ! -x "$HOME/.ghcup/bin/ghcup" ]; then
  curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | \
    BOOTSTRAP_HASKELL_NONINTERACTIVE=1 BOOTSTRAP_HASKELL_MINIMAL=1 BOOTSTRAP_HASKELL_ADJUST_BASHRC=0 sh
fi
. "$(dirname "$0")/cloud_env.sh"
ghcup install ghc 9.14.1 --set
ghcup install cabal latest --set
cabal update
echo "--- versions"
(cd "$(dirname "$0")/.." && lake --version)
ghc --version
cabal --version
