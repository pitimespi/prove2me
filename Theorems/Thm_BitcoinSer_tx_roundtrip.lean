import Definitions.Def_BitcoinSer

theorem BitcoinSer.tx_roundtrip (aw : Bool) (tx : Tx) (rest : Bytes) (hw : tx.wf)
    (hv : aw = true → tx.vin ≠ []) :
    BitcoinSer.readTx aw (BitcoinSer.serTx aw tx ++ rest) =
      some (if aw then tx else tx.stripWitness, rest) := by sorry
