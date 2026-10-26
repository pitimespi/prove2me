import Definitions.Def_BitcoinScript

theorem BitcoinScript.p2pk_correct (f : Flags) (o : Oracle) (sig pubkey : Bytes)
    (hsig : sig.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hpk : pubkey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinScript.verifyScriptPlain f o [.push sig] (BitcoinScript.p2pkScript pubkey) = true ↔
      o.checkSig sig pubkey = some true := by sorry
