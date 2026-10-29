import Definitions.Def_BitcoinUniqueness
open BitcoinUniqueness BitcoinSer BitcoinBlockV2

theorem BitcoinUniqueness.heightScript_prefix (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31)
    (h : (BitcoinBlockV2.heightScript a).isPrefixOf (BitcoinBlockV2.heightScript b) = true) : a = b := by sorry
