import Definitions.Def_BitcoinPow

theorem BitcoinPow.nextWork_le_powLimit (lastBits : BitVec 32) (lastTime firstTime : Int) :
    BitcoinPow.setCompact (BitcoinPow.calculateNextWork lastBits lastTime firstTime) ≤ BitcoinPow.powLimit := by sorry
