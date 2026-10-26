import Definitions.Def_BitcoinSer

theorem BitcoinSer.weight_no_witness (tx : Tx) (h : tx.hasWitness = false) :
    BitcoinSer.serTx true tx = BitcoinSer.serTx false tx ∧
      BitcoinSer.txWeight tx = BitcoinSer.WITNESS_SCALE_FACTOR * (BitcoinSer.serTx false tx).length := by sorry
