import Definitions.Def_BitcoinBlockV2
open BitcoinActivation
/-! Spot 19 vectors (`REVIEW_SPOT19.md`): `GetBlockScriptFlags` at the buried-deployment boundaries and
on the two `script_flag_exceptions`, `DeploymentActiveAt`/`DeploymentActiveAfter`, and the `nLockTimeFlags` of
`ConnectBlock`. Expectations computed by `tests/reference/activation_reference.py`. Every line prints `true`. -/
def hexVal (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87
def ofHexL : List Char → BitcoinSer.Bytes
  | a :: b :: r => BitVec.ofNat 8 (hexVal a * 16 + hexVal b) :: ofHexL r
  | _ => []
def ofHex (s : String) : BitcoinSer.Bytes := ofHexL s.toList
-- deployment heights (CMainParams)
#eval deploymentHeight .heightInCB == 227931
#eval deploymentHeight .cltv == 388381
#eval deploymentHeight .derSig == 363725
#eval deploymentHeight .csv == 419328
#eval deploymentHeight .segwit == 481824
-- DeploymentActiveAt / DeploymentActiveAfter at every boundary
#eval activeAt 227930 .heightInCB == false
#eval activeAt 227931 .heightInCB == true
#eval activeAt 227932 .heightInCB == true
#eval activeAfter 227929 .heightInCB == false
#eval activeAfter 227930 .heightInCB == true
#eval activeAfter 227931 .heightInCB == true
#eval activeAt 0 .heightInCB == false
#eval activeAfter 0 .heightInCB == false
#eval activeAt 388380 .cltv == false
#eval activeAt 388381 .cltv == true
#eval activeAt 388382 .cltv == true
#eval activeAfter 388379 .cltv == false
#eval activeAfter 388380 .cltv == true
#eval activeAfter 388381 .cltv == true
#eval activeAt 0 .cltv == false
#eval activeAfter 0 .cltv == false
#eval activeAt 363724 .derSig == false
#eval activeAt 363725 .derSig == true
#eval activeAt 363726 .derSig == true
#eval activeAfter 363723 .derSig == false
#eval activeAfter 363724 .derSig == true
#eval activeAfter 363725 .derSig == true
#eval activeAt 0 .derSig == false
#eval activeAfter 0 .derSig == false
#eval activeAt 419327 .csv == false
#eval activeAt 419328 .csv == true
#eval activeAt 419329 .csv == true
#eval activeAfter 419326 .csv == false
#eval activeAfter 419327 .csv == true
#eval activeAfter 419328 .csv == true
#eval activeAt 0 .csv == false
#eval activeAfter 0 .csv == false
#eval activeAt 481823 .segwit == false
#eval activeAt 481824 .segwit == true
#eval activeAt 481825 .segwit == true
#eval activeAfter 481822 .segwit == false
#eval activeAfter 481823 .segwit == true
#eval activeAfter 481824 .segwit == true
#eval activeAt 0 .segwit == false
#eval activeAfter 0 .segwit == false
-- GetBlockScriptFlags with no exception, at the listed heights
#eval blockScriptFlags 0 .none == ⟨true, true, true, false, false, false, false⟩
#eval blockScriptFlags 1 .none == ⟨true, true, true, false, false, false, false⟩
#eval blockScriptFlags 170 .none == ⟨true, true, true, false, false, false, false⟩
#eval blockScriptFlags 227930 .none == ⟨true, true, true, false, false, false, false⟩
#eval blockScriptFlags 227931 .none == ⟨true, true, true, false, false, false, false⟩
#eval blockScriptFlags 363724 .none == ⟨true, true, true, false, false, false, false⟩
#eval blockScriptFlags 363725 .none == ⟨true, true, true, true, false, false, false⟩
#eval blockScriptFlags 388380 .none == ⟨true, true, true, true, false, false, false⟩
#eval blockScriptFlags 388381 .none == ⟨true, true, true, true, true, false, false⟩
#eval blockScriptFlags 419327 .none == ⟨true, true, true, true, true, false, false⟩
#eval blockScriptFlags 419328 .none == ⟨true, true, true, true, true, true, false⟩
#eval blockScriptFlags 481823 .none == ⟨true, true, true, true, true, true, false⟩
#eval blockScriptFlags 481824 .none == ⟨true, true, true, true, true, true, true⟩
#eval blockScriptFlags 709631 .none == ⟨true, true, true, true, true, true, true⟩
#eval blockScriptFlags 709632 .none == ⟨true, true, true, true, true, true, true⟩
#eval blockScriptFlags 170060 .none == ⟨true, true, true, false, false, false, false⟩
#eval blockScriptFlags 692261 .none == ⟨true, true, true, true, true, true, true⟩
-- the two exception blocks: the table entry replaces the base, the height flags are still OR'ed
#eval blockScriptFlags 0 .bip16Block == ⟨false, false, false, false, false, false, false⟩
#eval blockScriptFlags 0 .taprootBlock == ⟨true, true, false, false, false, false, false⟩
#eval blockScriptFlags 1 .bip16Block == ⟨false, false, false, false, false, false, false⟩
#eval blockScriptFlags 1 .taprootBlock == ⟨true, true, false, false, false, false, false⟩
#eval blockScriptFlags 170 .bip16Block == ⟨false, false, false, false, false, false, false⟩
#eval blockScriptFlags 170 .taprootBlock == ⟨true, true, false, false, false, false, false⟩
#eval blockScriptFlags 227930 .bip16Block == ⟨false, false, false, false, false, false, false⟩
#eval blockScriptFlags 227930 .taprootBlock == ⟨true, true, false, false, false, false, false⟩
#eval blockScriptFlags 227931 .bip16Block == ⟨false, false, false, false, false, false, false⟩
#eval blockScriptFlags 227931 .taprootBlock == ⟨true, true, false, false, false, false, false⟩
#eval blockScriptFlags 363724 .bip16Block == ⟨false, false, false, false, false, false, false⟩
#eval blockScriptFlags 363724 .taprootBlock == ⟨true, true, false, false, false, false, false⟩
#eval blockScriptFlags 363725 .bip16Block == ⟨false, false, false, true, false, false, false⟩
#eval blockScriptFlags 363725 .taprootBlock == ⟨true, true, false, true, false, false, false⟩
#eval blockScriptFlags 388380 .bip16Block == ⟨false, false, false, true, false, false, false⟩
#eval blockScriptFlags 388380 .taprootBlock == ⟨true, true, false, true, false, false, false⟩
#eval blockScriptFlags 388381 .bip16Block == ⟨false, false, false, true, true, false, false⟩
#eval blockScriptFlags 388381 .taprootBlock == ⟨true, true, false, true, true, false, false⟩
#eval blockScriptFlags 419327 .bip16Block == ⟨false, false, false, true, true, false, false⟩
#eval blockScriptFlags 419327 .taprootBlock == ⟨true, true, false, true, true, false, false⟩
#eval blockScriptFlags 419328 .bip16Block == ⟨false, false, false, true, true, true, false⟩
#eval blockScriptFlags 419328 .taprootBlock == ⟨true, true, false, true, true, true, false⟩
#eval blockScriptFlags 481823 .bip16Block == ⟨false, false, false, true, true, true, false⟩
#eval blockScriptFlags 481823 .taprootBlock == ⟨true, true, false, true, true, true, false⟩
#eval blockScriptFlags 481824 .bip16Block == ⟨false, false, false, true, true, true, true⟩
#eval blockScriptFlags 481824 .taprootBlock == ⟨true, true, false, true, true, true, true⟩
#eval blockScriptFlags 709631 .bip16Block == ⟨false, false, false, true, true, true, true⟩
#eval blockScriptFlags 709631 .taprootBlock == ⟨true, true, false, true, true, true, true⟩
#eval blockScriptFlags 709632 .bip16Block == ⟨false, false, false, true, true, true, true⟩
#eval blockScriptFlags 709632 .taprootBlock == ⟨true, true, false, true, true, true, true⟩
#eval blockScriptFlags 170060 .bip16Block == ⟨false, false, false, false, false, false, false⟩
#eval blockScriptFlags 170060 .taprootBlock == ⟨true, true, false, false, false, false, false⟩
#eval blockScriptFlags 692261 .bip16Block == ⟨false, false, false, true, true, true, true⟩
#eval blockScriptFlags 692261 .taprootBlock == ⟨true, true, false, true, true, true, true⟩
-- the exception lookup by (serialized, little-endian) hash
#eval BitcoinBlockV2.scriptException (ofHex "229c4fac88bab194eb08f1a528cc308ded2397f4f4eb6e75dc02000000000000") == .bip16Block
#eval BitcoinBlockV2.scriptException (ofHex "ad95e3a15ee5ffd585c5e81d44b56a981e842d5bc3140f000000000000000000") == .taprootBlock
#eval BitcoinBlockV2.scriptException (ofHex "00000000000002dc756eebf4f49723ed8d30cc28a5f108eb94b1ba88ac4f9c22") == .none  -- display order is not the key
#eval BitcoinBlockV2.scriptException (ofHex "0000000000000000000f14c35b2d841e986ab5441de8c585d5ffe55ea1e395ad") == .none
#eval BitcoinBlockV2.scriptException (ofHex "239c4fac88bab194eb08f1a528cc308ded2397f4f4eb6e75dc02000000000000") == .none
#eval BitcoinBlockV2.scriptException [] == .none
-- nLockTimeFlags
#eval lockTimeFlags 0 == 0
#eval lockTimeFlags 419326 == 0
#eval lockTimeFlags 419327 == 0
#eval lockTimeFlags 419328 == 1
#eval lockTimeFlags 419329 == 1
#eval lockTimeFlags 709632 == 1
#eval LOCKTIME_VERIFY_SEQUENCE == 1
-- noFlags / baseFlags / exceptionBase
#eval noFlags == ⟨false, false, false, false, false, false, false⟩
#eval baseFlags == ⟨true, true, true, false, false, false, false⟩
#eval exceptionBase .none == ⟨true, true, true, false, false, false, false⟩
#eval exceptionBase .bip16Block == ⟨false, false, false, false, false, false, false⟩
#eval exceptionBase .taprootBlock == ⟨true, true, false, false, false, false, false⟩
