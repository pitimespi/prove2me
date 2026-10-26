import Definitions.Def_BitcoinPow

open BitcoinPow

theorem BitcoinPow.overflow_iff (c : BitVec 32) :
    BitcoinPow.compactOverflow c = true ↔ BitcoinPow.width ≤ BitcoinPow.specTarget c := by sorry

theorem BitcoinPow.setCompact_eq_spec (c : BitVec 32) (h : BitcoinPow.compactOverflow c = false) :
    BitcoinPow.setCompact c = BitcoinPow.specTarget c := by sorry

theorem BitcoinPow.getCompact_le (v : Nat) (hv : v < BitcoinPow.width) :
    BitcoinPow.setCompact (BitcoinPow.getCompact v) ≤ v := by sorry

theorem BitcoinPow.getCompact_valid (v : Nat) (hv : v < BitcoinPow.width) :
    BitcoinPow.compactNegative (BitcoinPow.getCompact v) = false ∧
    BitcoinPow.compactOverflow (BitcoinPow.getCompact v) = false := by sorry

theorem BitcoinPow.round_mono (v w : Nat) (hvw : v ≤ w) (hw : w < BitcoinPow.width) :
    BitcoinPow.setCompact (BitcoinPow.getCompact v) ≤ BitcoinPow.setCompact (BitcoinPow.getCompact w) := by sorry

theorem BitcoinPow.checkProofOfWork_iff (hash : Nat) (nBits : BitVec 32) :
    BitcoinPow.checkProofOfWork hash nBits = true ↔
      BitcoinPow.compactNegative nBits = false ∧ BitcoinPow.compactOverflow nBits = false ∧
      0 < BitcoinPow.specTarget nBits ∧ BitcoinPow.specTarget nBits ≤ BitcoinPow.powLimit ∧
      hash ≤ BitcoinPow.specTarget nBits := by sorry

theorem BitcoinPow.clamp_bounds (actual : Int) :
    ((BitcoinPow.targetTimespan / 4 : Nat) : Int) ≤ BitcoinPow.clampTimespan actual ∧
    BitcoinPow.clampTimespan actual ≤ ((BitcoinPow.targetTimespan * 4 : Nat) : Int) := by sorry

theorem BitcoinPow.nextWork_le_powLimit (lastBits : BitVec 32) (lastTime firstTime : Int) :
    BitcoinPow.setCompact (BitcoinPow.calculateNextWork lastBits lastTime firstTime) ≤ BitcoinPow.powLimit := by sorry

theorem BitcoinPow.nextWork_off_boundary (lastHeight : Nat) (lastBits : BitVec 32) (lastTime firstTime : Int)
    (h : (lastHeight + 1) % BitcoinPow.difficultyAdjustmentInterval ≠ 0) :
    BitcoinPow.nextWorkRequired lastHeight lastBits lastTime firstTime = lastBits ∧
    BitcoinPow.permittedTransition (lastHeight + 1) lastBits lastBits = true := by sorry

theorem BitcoinPow.nextWork_permitted (height : Nat) (lastBits : BitVec 32) (lastTime firstTime : Int)
    (hh : height % BitcoinPow.difficultyAdjustmentInterval = 0)
    (hold : BitcoinPow.setCompact lastBits ≤ BitcoinPow.powLimit) :
    BitcoinPow.permittedTransition height lastBits
      (BitcoinPow.calculateNextWork lastBits lastTime firstTime) = true := by sorry
