import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.isDist_delta (t : BitcoinSelfishMining.State) :
    BitcoinSelfishErgodic.IsDist (BitcoinSelfishErgodic.delta t) := by sorry
