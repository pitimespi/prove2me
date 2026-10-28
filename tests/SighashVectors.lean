import Definitions.Def_BitcoinSig
open BitcoinSer BitcoinSig
def hexVal (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87
def ofHexL : List Char → Bytes | a :: b :: r => BitVec.ofNat 8 (hexVal a * 16 + hexVal b) :: ofHexL r | _ => []
def ofHex (s : String) : Bytes := ofHexL s.toList
def rng (a b : Nat) : Bytes := (List.range (b - a)).map fun i => BitVec.ofNat 8 (a + i)
def tx : Tx := ⟨2, [⟨⟨rng 0 32, 1⟩, [], 0xfffffffe, []⟩, ⟨⟨rng 32 64, 0⟩, [], 0xffffffff, []⟩, ⟨⟨rng 64 96, 7⟩, [], 12345, []⟩],
  [⟨100000, ofHex "76a914" ++ List.replicate 20 0 ++ ofHex "88ac"⟩, ⟨0, ofHex "6a04deadbeef"⟩], 500123⟩
def sc : Bytes := ofHex "76a9140102030405060708090a0b0c0d0e0f101112131488abac"
/-! Independent Python reference (scratchpad/sig/gen.py): every line prints `true`. -/
#eval sigHashLegacy sc tx 0 1 == ofHex "29f4fc082ae8eb84f5d1aade2cc15d3d93715c5d704ff305e8546f4f2eed0923"
#eval sigHashWitnessV0 sc tx 0 1 5000 == ofHex "48b40d4bef38b0a4722d6ab92d11958e82fcbfd1544997c4399ea6dcbc5d7da0"
#eval sigHashLegacy sc tx 2 1 == ofHex "0a4b2ac6e2aa534f8a27a18ddae2fd69d89243c6f7a537168db5fa02dbaae31d"
#eval sigHashWitnessV0 sc tx 2 1 5000 == ofHex "666cf758973307b05b9763524b71f2de300c9aee79d3c448dc8368690fcd3b16"
#eval sigHashLegacy sc tx 0 2 == ofHex "13d1b992b9b3476d8549fd56961dea08c49b08899d6f5a739aa6dc4554421ee8"
#eval sigHashWitnessV0 sc tx 0 2 5000 == ofHex "8bd168f8ed1b821560093ff93ebf49c35246d6e8b8c561fe5c3bc897c0f82280"
#eval sigHashLegacy sc tx 2 2 == ofHex "c8a042bc5d9d73893edc7aa9fe0e4efd9fb1738b6459bf063a915916539fe235"
#eval sigHashWitnessV0 sc tx 2 2 5000 == ofHex "bb0c7b5f09d3c839e65fcd1abbb6c184bada3af3f60b8506d43b6e267a04c675"
#eval sigHashLegacy sc tx 0 3 == ofHex "a22729f38901abe66ec18cea5b0ea1c98779f9b9ea1db5ad6804800d0af9263f"
#eval sigHashWitnessV0 sc tx 0 3 5000 == ofHex "a83a01e5f22a9fd866a2a15c29092e56ed49083680ccbb8877ce6daba66796b1"
#eval sigHashLegacy sc tx 2 3 == ofHex "0100000000000000000000000000000000000000000000000000000000000000"
#eval sigHashWitnessV0 sc tx 2 3 5000 == ofHex "75a85db3278cbd83e99de9b9a9d874589038ef607be7b0b6fb38e39b32b1716a"
#eval sigHashLegacy sc tx 0 129 == ofHex "997a5d2f497f545ac07d2378685b402725d38bc7a92499fcbbef885d2a568170"
#eval sigHashWitnessV0 sc tx 0 129 5000 == ofHex "178f65478f52924d24a6bd6e3bea8bf5380e3b7af0f714cae365e385344158af"
#eval sigHashLegacy sc tx 2 129 == ofHex "8c55fb7f8c82e53e2e5500b7b24931f725ae904fc594b825739c6fbd2dae7fc4"
#eval sigHashWitnessV0 sc tx 2 129 5000 == ofHex "0cdae28e7599b334c17a4f3d4d7413ca9797763b984a23bc6909cde93d0fe589"
#eval sigHashLegacy sc tx 0 130 == ofHex "705d6bcabcc6dd9d53e75bf2d8fd86928f401e02bb40bfcee56cf14c6cd165e8"
#eval sigHashWitnessV0 sc tx 0 130 5000 == ofHex "58275cc5ad615578ccb767a4f8c24944b8828d0c59792da0830a2df1e4e6f71e"
#eval sigHashLegacy sc tx 2 130 == ofHex "3f129c4713c4e952465c7bc4dcc2e0655dc1c4ab0e87dcc8dcc98878f9ae8f70"
#eval sigHashWitnessV0 sc tx 2 130 5000 == ofHex "e180fca98f4641462e84cc9b0e9f6c47a7a266d6dd12814778ad396894602368"
#eval sigHashLegacy sc tx 0 131 == ofHex "7aad0146ade15e3c00a17d9c877243cdb93d94f4ab3a7302f979fb0f3ba1308c"
#eval sigHashWitnessV0 sc tx 0 131 5000 == ofHex "a4271fb4cf564fc01e83dce7ec86b573ebddb49fc4254d8373710f31ee24440d"
#eval sigHashLegacy sc tx 2 131 == ofHex "0100000000000000000000000000000000000000000000000000000000000000"
#eval sigHashWitnessV0 sc tx 2 131 5000 == ofHex "cf90898b93b911c8fc2889a8de449fd904ddbee560a2ef67adec3e39005b1766"
-- the SIGHASH_SINGLE bug: input 2 has no matching output
#eval sigHashLegacy sc tx 2 3 == uint256One
#eval sigHashLegacy sc tx 2 0x83 == uint256One
#eval sigHashLegacy sc tx 1 3 != uint256One
-- FindAndDelete: boundary matches only, repeated occurrences, and a match inside push data is not removed
#eval findAndDelete (ofHex "0101" ++ ofHex "0101" ++ ofHex "ac") (ofHex "0101") == (ofHex "ac", 2)
#eval findAndDelete (ofHex "020101" ++ ofHex "ac") (ofHex "0101") == (ofHex "020101ac", 0)
#eval findAndDelete (ofHex "ac0101") (ofHex "0101") == (ofHex "ac", 1)
#eval findAndDelete (ofHex "ac01") (ofHex "0101") == (ofHex "ac01", 0)
#eval findAndDelete (ofHex "0101ac") [] == (ofHex "0101ac", 0)
#eval findAndDelete (ofHex "00ac00") (ofHex "00") == (ofHex "ac", 2)   -- an empty signature deletes OP_0s
-- script code serialization drops OP_CODESEPARATOR instructions and keeps the ones inside pushes
#eval serScriptCode (ofHex "ab76ab01abac") == ofHex "0476" ++ ofHex "01abac"
