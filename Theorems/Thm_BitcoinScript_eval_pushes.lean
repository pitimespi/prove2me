import Definitions.Def_BitcoinScript

theorem BitcoinScript.eval_pushes (f : Flags) (o : Oracle) (ps : List Bytes)
    (hsz : ∀ p ∈ ps, p.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hlen : ps.length ≤ BitcoinScript.MAX_STACK_SIZE) :
    BitcoinScript.evalScript f o [] (ps.map Instr.push) = some ps.reverse := by sorry
