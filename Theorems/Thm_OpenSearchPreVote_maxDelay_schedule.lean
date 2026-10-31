import Definitions.Def_OpenSearchPreVote
open OpenSearchCoordination OpenSearchPreVote

theorem OpenSearchPreVote.maxDelay_schedule (s : SchedulerSettings) (hs : s.Valid) :
    maxDelay s 0 = s.initialTimeout ∧ (∀ k k', k ≤ k' → maxDelay s k ≤ maxDelay s k') ∧
    (∀ k, maxDelay s k < s.maxTimeout → maxDelay s (k + 1) = maxDelay s k + s.backoffTime ∨
      maxDelay s (k + 1) = s.maxTimeout) ∧
    ∀ k, s.maxTimeout ≤ k → maxDelay s k = s.maxTimeout := by sorry
