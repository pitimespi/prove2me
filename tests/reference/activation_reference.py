"""Independent reference for spot 19 (REVIEW_SPOT19.md): GetBlockScriptFlags with the two
mainnet script_flag_exceptions, DeploymentActiveAt / DeploymentActiveAfter for the buried
deployments, and the nLockTimeFlags selection of ConnectBlock, written from the C++
(validation.cpp:2249, deploymentstatus.h, kernel/chainparams.cpp:108, consensus/consensus.h)
without looking at the Lean. Emits tests/ActivationVectors.lean.

Interface adaptation: Core's flags are a bit set; the Lean's `ScriptFlags` is a record of the
seven flags GetBlockScriptFlags can set, so the reference computes the set with named bits and
prints it as the record `⟨p2sh, witness, taproot, dersig, cltv, csv, nulldummy⟩` in that order.
The exception table is keyed by block hash in Core; the Lean takes a three-valued label, which
`BitcoinBlockV2.scriptException` derives from the hash, so both are checked.

Usage: python3 -I activation_reference.py OUT_LEAN
"""
import sys

# script/interpreter.h: each flag is one bit; only the identity of the bits matters here.
P2SH, DERSIG, NULLDUMMY, CLTV, CSV, WITNESS, TAPROOT = (1 << i for i in range(7))
NONE = 0

# kernel/chainparams.cpp CMainParams
BIP34Height, BIP65Height, BIP66Height, CSVHeight, SegwitHeight = 227931, 388381, 363725, 419328, 481824
BIP16_EXCEPTION = "00000000000002dc756eebf4f49723ed8d30cc28a5f108eb94b1ba88ac4f9c22"
TAPROOT_EXCEPTION = "0000000000000000000f14c35b2d841e986ab5441de8c585d5ffe55ea1e395ad"
script_flag_exceptions = {BIP16_EXCEPTION: NONE, TAPROOT_EXCEPTION: P2SH | WITNESS}

# consensus/params.h DeploymentHeight
HEIGHT = {"heightInCB": BIP34Height, "cltv": BIP65Height, "derSig": BIP66Height,
          "csv": CSVHeight, "segwit": SegwitHeight}

def active_at(height, dep):            # deploymentstatus.h: index.nHeight >= DeploymentHeight(dep)
    return height >= HEIGHT[dep]

def active_after(prev_height, dep):    # (pindexPrev == nullptr ? 0 : pindexPrev->nHeight + 1) >= height
    return (0 if prev_height is None else prev_height + 1) >= HEIGHT[dep]

def block_script_flags(height, block_hash):   # validation.cpp:2249
    flags = P2SH | WITNESS | TAPROOT
    if block_hash in script_flag_exceptions:
        flags = script_flag_exceptions[block_hash]          # replaces, does not AND
    if active_at(height, "derSig"): flags |= DERSIG
    if active_at(height, "cltv"):   flags |= CLTV
    if active_at(height, "csv"):    flags |= CSV
    if active_at(height, "segwit"): flags |= NULLDUMMY
    return flags

LOCKTIME_VERIFY_SEQUENCE = 1 << 0     # consensus/consensus.h
def lock_time_flags(height):          # ConnectBlock, validation.cpp:2478
    return LOCKTIME_VERIFY_SEQUENCE if active_at(height, "csv") else 0

def record(flags):
    bits = [P2SH, WITNESS, TAPROOT, DERSIG, CLTV, CSV, NULLDUMMY]
    return "⟨" + ", ".join("true" if flags & b else "false" for b in bits) + "⟩"

def lb(b): return "true" if b else "false"

HEIGHTS = [0, 1, 170, 227930, 227931, 363724, 363725, 388380, 388381, 419327, 419328,
           481823, 481824, 709631, 709632, 170060, 692261]
# 170060 and 692261 are the mainnet heights of the two exception blocks; the source only keys
# them by hash, so the exception cases below are evaluated at those heights AND at other heights.

def le_bytes(display_hex):           # uint256 display hex is big-endian; serialized bytes are reversed
    return "".join(f"{b:02x}" for b in bytes.fromhex(display_hex)[::-1])

out = []
out.append("import Definitions.Def_BitcoinBlockV2")
out.append("open BitcoinActivation")
out.append("/-! Spot 19 vectors (`REVIEW_SPOT19.md`): `GetBlockScriptFlags` at the buried-deployment boundaries and")
out.append("on the two `script_flag_exceptions`, `DeploymentActiveAt`/`DeploymentActiveAfter`, and the `nLockTimeFlags` of")
out.append("`ConnectBlock`. Expectations computed by `tests/reference/activation_reference.py`. Every line prints `true`. -/")
out.append("def hexVal (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87")
out.append("def ofHexL : List Char → BitcoinSer.Bytes")
out.append("  | a :: b :: r => BitVec.ofNat 8 (hexVal a * 16 + hexVal b) :: ofHexL r")
out.append("  | _ => []")
out.append("def ofHex (s : String) : BitcoinSer.Bytes := ofHexL s.toList")
out.append("-- deployment heights (CMainParams)")
for dep, h in HEIGHT.items():
    out.append(f"#eval deploymentHeight .{dep} == {h}")
out.append("-- DeploymentActiveAt / DeploymentActiveAfter at every boundary")
for dep, h in HEIGHT.items():
    for x in (h - 1, h, h + 1):
        out.append(f"#eval activeAt {x} .{dep} == {lb(active_at(x, dep))}")
    for p in (h - 2, h - 1, h):
        out.append(f"#eval activeAfter {p} .{dep} == {lb(active_after(p, dep))}")
    out.append(f"#eval activeAt 0 .{dep} == {lb(active_at(0, dep))}")
    out.append(f"#eval activeAfter 0 .{dep} == {lb(active_after(0, dep))}")
out.append("-- GetBlockScriptFlags with no exception, at the listed heights")
for h in HEIGHTS:
    out.append(f"#eval blockScriptFlags {h} .none == {record(block_script_flags(h, 'other'))}")
out.append("-- the two exception blocks: the table entry replaces the base, the height flags are still OR'ed")
for h in HEIGHTS:
    out.append(f"#eval blockScriptFlags {h} .bip16Block == {record(block_script_flags(h, BIP16_EXCEPTION))}")
    out.append(f"#eval blockScriptFlags {h} .taprootBlock == {record(block_script_flags(h, TAPROOT_EXCEPTION))}")
out.append("-- the exception lookup by (serialized, little-endian) hash")
out.append(f"#eval BitcoinBlockV2.scriptException (ofHex \"{le_bytes(BIP16_EXCEPTION)}\") == .bip16Block")
out.append(f"#eval BitcoinBlockV2.scriptException (ofHex \"{le_bytes(TAPROOT_EXCEPTION)}\") == .taprootBlock")
out.append(f"#eval BitcoinBlockV2.scriptException (ofHex \"{BIP16_EXCEPTION}\") == .none  -- display order is not the key")
out.append(f"#eval BitcoinBlockV2.scriptException (ofHex \"{TAPROOT_EXCEPTION}\") == .none")
out.append(f"#eval BitcoinBlockV2.scriptException (ofHex \"{le_bytes('00000000000002dc756eebf4f49723ed8d30cc28a5f108eb94b1ba88ac4f9c23')}\") == .none")
out.append("#eval BitcoinBlockV2.scriptException [] == .none")
out.append("-- nLockTimeFlags")
for h in (0, 419326, 419327, 419328, 419329, 709632):
    out.append(f"#eval lockTimeFlags {h} == {lock_time_flags(h)}")
out.append("#eval LOCKTIME_VERIFY_SEQUENCE == 1")
out.append("-- noFlags / baseFlags / exceptionBase")
out.append(f"#eval noFlags == {record(NONE)}")
out.append(f"#eval baseFlags == {record(P2SH | WITNESS | TAPROOT)}")
out.append(f"#eval exceptionBase .none == {record(P2SH | WITNESS | TAPROOT)}")
out.append(f"#eval exceptionBase .bip16Block == {record(script_flag_exceptions[BIP16_EXCEPTION])}")
out.append(f"#eval exceptionBase .taprootBlock == {record(script_flag_exceptions[TAPROOT_EXCEPTION])}")

with open(sys.argv[1], "w") as f:
    f.write("\n".join(out) + "\n")
print(len([l for l in out if l.startswith("#eval")]), "vectors")
