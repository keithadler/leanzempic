#!/bin/sh
# usage: bench/aes/run.sh [N]   Build AES-256 (from lean-aes) with Lean's C backend and with leanzempic,
# check both give the same answer, and time them. Run with the system PATH for GHC (no elan clang).
set -e
cd "$(dirname "$0")/../.."
N=${1:-200000}
U=${UNROLL:-16}   # zempic.unroll: 0 off, else largest literal counter to unroll
lake build aesbench >/dev/null
rm -rf build/AesBench
sed "s/^#zempic/set_option zempic.unroll $U in\n#zempic/" bench/aes/AesEmit.lean > build/AesEmitU.lean
lake env lean -R bench/aes build/AesEmitU.lean >/dev/null 2>&1 || lake env lean build/AesEmitU.lean >/dev/null
SYS=$(echo "$PATH" | tr ':' '\n' | grep -v elan | paste -sd: -)
(cd bench && PATH=$SYS ghc -O2 -i../runtime -i../build/AesBench -outputdir ../build/ob -rtsopts "-with-rtsopts=-A128m" -o ../build/AesMain AesMain.hs >/dev/null)
c=$(.lake/build/bin/aesbench "$N"); h=$(build/AesMain "$N")
[ -n "$c" ] && [ "$c" = "$h" ] || { echo "MISMATCH c=$c hs=$h"; exit 1; }
best() { b=999; for i in 1 2 3; do t=$( { /usr/bin/time -p "$@" >/dev/null; } 2>&1 | awk '/real/{print $2}'); b=$(echo "$t $b" | awk '{print ($1<$2)?$1:$2}'); done; echo $b; }
echo "n=$N unroll=$U same answer; Lean C: $(best .lake/build/bin/aesbench $N) s, leanzempic: $(best build/AesMain $N) s"
