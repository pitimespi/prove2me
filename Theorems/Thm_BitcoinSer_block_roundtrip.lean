import Definitions.Def_BitcoinSer

theorem BitcoinSer.block_roundtrip (aw : Bool) (b : Block) (rest : Bytes) (hw : b.wf) :
    BitcoinSer.readBlock aw (BitcoinSer.serBlock aw b ++ rest) =
      some (⟨b.header, b.vtx.map (fun tx => if aw then tx else tx.stripWitness)⟩, rest) := by sorry
