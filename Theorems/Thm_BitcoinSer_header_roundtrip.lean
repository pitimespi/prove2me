import Definitions.Def_BitcoinSer

theorem BitcoinSer.header_roundtrip (h : Header) (rest : Bytes) (hw : h.wf) :
    BitcoinSer.readHeader (BitcoinSer.serHeader h ++ rest) = some (h, rest) := by sorry
