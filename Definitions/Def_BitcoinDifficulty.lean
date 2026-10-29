import Definitions.Def_BitcoinPow
import Definitions.Def_BitcoinBlockV2

/-!
# How fast the difficulty can move

`CalculateNextWorkRequired` multiplies the last target by the clamped actual timespan of the
period and divides by two weeks, caps at `powLimit`, and re-encodes. The clamp bounds the ratio
by a factor of four in either direction; this file names the raw (unencoded) next target so the
theorems can state that bound exactly, before the compact rounding, and then transfer it to the
encoded value and along a chain of periods. These are the limits on what an adversary who controls
timestamps can do to the difficulty: a "timewarp" moves the target by at most this much per period.
-/

namespace BitcoinDifficulty

open BitcoinPow

/-- The raw next target of a period: the last target times the clamped timespan, divided by the
target timespan, capped at `powLimit` — the value `CalculateNextWorkRequired` encodes. -/
def rawNextTarget (lastTarget : Nat) (lastTime firstTime : Int) : Nat :=
  let ts := (clampTimespan (lastTime - firstTime)).toNat
  let bn := (lastTarget * ts) % width / targetTimespan
  if powLimit < bn then powLimit else bn

/-- The encoded target after `m` retargets starting from `bits`, with the given sequence of
(last time, first time) pairs, one per period. -/
def targetAfter : BitVec 32 → List (Int × Int) → BitVec 32
  | bits, [] => bits
  | bits, (lastTime, firstTime) :: rest => targetAfter (calculateNextWork bits lastTime firstTime) rest

end BitcoinDifficulty
