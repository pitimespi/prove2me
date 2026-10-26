import Definitions.Def_BitcoinSer

theorem BitcoinSer.serHeader_length (h : Header) (hw : h.wf) : (BitcoinSer.serHeader h).length = 80 := by sorry
