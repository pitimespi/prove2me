import Definitions.Def_BitcoinUniqueness
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinHeader
open BitcoinUniqueness BitcoinSer BitcoinBlockV2

theorem BitcoinUniqueness.coinbases_distinct (S₁ S₂ : ChainState) (b₁ b₂ : BitcoinSer.Block) (now₁ now₂ : Int)
    (S₁' S₂' : ChainState) (undo₁ undo₂ : BlockUndo)
    (hR₁ : BitcoinBlockV2.Reachable S₁) (hR₂ : BitcoinBlockV2.Reachable S₂)
    (h₁ : BitcoinBlockV2.validate S₁ b₁ now₁ = .accept S₁' undo₁) (h₂ : BitcoinBlockV2.validate S₂ b₂ now₂ = .accept S₂' undo₂)
    (h34₁ : BitcoinHeader.BIP34Height ≤ S₁.nextHeight) (h34₂ : BitcoinHeader.BIP34Height ≤ S₂.nextHeight)
    (hlt₁ : S₁.nextHeight < 2 ^ 31) (hlt₂ : S₂.nextHeight < 2 ^ 31) (hne : S₁.nextHeight ≠ S₂.nextHeight) :
    BitcoinUniqueness.coinbaseScriptSig b₁ ≠ BitcoinUniqueness.coinbaseScriptSig b₂ := by sorry
