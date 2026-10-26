import Definitions.Def_BitcoinScript

theorem BitcoinScript.p2pkh_correct (f : Flags) (o : Oracle) (sig pubkey h : Bytes)
    (hsig : sig.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hpk : pubkey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hh : h.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinScript.verifyScriptPlain f o [.push sig, .push pubkey] (BitcoinScript.p2pkhScript h) = true ↔
      o.hash160 pubkey = h ∧ o.checkSig sig pubkey = some true := by sorry
