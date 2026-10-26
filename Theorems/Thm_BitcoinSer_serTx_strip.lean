import Definitions.Def_BitcoinSer

theorem BitcoinSer.serTx_strip (tx : Tx) : BitcoinSer.serTx false tx = BitcoinSer.serTx false tx.stripWitness := by sorry
