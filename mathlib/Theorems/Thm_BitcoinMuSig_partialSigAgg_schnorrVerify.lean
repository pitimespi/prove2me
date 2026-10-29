import Definitions.Def_BitcoinMuSig
import Definitions.Def_BitcoinSer
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.partialSigAgg_schnorrVerify (ctx : SessionCtx)
    (sigs : List (BitcoinSer.Bytes × BitcoinSer.Bytes × BitcoinSer.Bytes)) (hne : sigs ≠ [])
    (hpks : ctx.pks = sigs.map fun t => t.2.2) (hkeys : ∀ pk ∈ ctx.pks, n • tp (cpoint pk) = 0)
    (hagg : nonceAgg (sigs.map fun t => t.2.1) = some ctx.aggnonce)
    (hver : ∀ t ∈ sigs, partialSigVerifyInternal t.1 t.2.1 t.2.2 ctx = true)
    (hR : ∀ sv, getSessionValues ctx = some sv → sv.R' ≠ none) :
    ∃ sv sig, getSessionValues ctx = some sv ∧ partialSigAgg (sigs.map fun t => t.1) ctx = some sig ∧
      schnorrVerify (xbytes sv.Q) ctx.msg sig = true := by sorry
