import Definitions.Def_BitcoinSer

theorem BitcoinSer.txid_strip (tx : Tx) : BitcoinSer.txid tx = BitcoinSer.txid tx.stripWitness := by sorry
