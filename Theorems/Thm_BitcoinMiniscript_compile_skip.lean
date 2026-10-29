import Definitions.Def_BitcoinMiniscript
import Definitions.Def_BitcoinScript
open BitcoinMiniscript BitcoinToLocal BitcoinHtlc BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinMiniscript.compile_skip (f : BitcoinScript.Flags) (o : BitcoinScript.Oracle) (m : BitcoinMiniscript.Ms)
    (ty : BitcoinMiniscript.Ty) (ht : BitcoinMiniscript.HasType m ty) (st alt : List BitcoinScript.Bytes)
    (vf : List Bool) (k : Nat) (hvf : BitcoinScript.allTrue vf = false)
    (hk : k + BitcoinMiniscript.opsMax m ≤ BitcoinScript.MAX_OPS_PER_SCRIPT)
    (hsz : st.length + alt.length ≤ BitcoinScript.MAX_STACK_SIZE) :
    ∃ k', BitcoinMiniscript.runSeq f o ⟨st, alt, vf, k⟩ (BitcoinMiniscript.compile m) = some ⟨st, alt, vf, k'⟩ ∧
      k' ≤ k + BitcoinMiniscript.opsMax m := by sorry
