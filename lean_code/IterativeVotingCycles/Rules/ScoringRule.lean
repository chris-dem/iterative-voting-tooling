import IterativeVotingCycles.Basic
import IterativeVotingCycles.Ballots
import IterativeVotingCycles.Rules.VotingRule
import Mathlib.Algebra.BigOperators.Fin

open Classical
open BigOperators



variable {n m: ℕ} [NeZero n] [NeZero m]

-- ────────────────────────────────────────────────
-- Shared helper: build winner set from a score fn
-- ────────────────────────────────────────────────

def scoreWinners {Ballot : Type}
    (score : Profile n m -> CandW m -> BallotProfile Ballot n → Cand m → WeightType)
    (P     : Profile n m)
    (CW    : CandW m)
    (BP    : BallotProfile Ballot n) : NonEmptyFinset (Cand m) :=
  let isWin c := ∀ d : Cand m, score P CW BP d ≤ score P CW BP c
  { val      := Finset.univ.filter isWin,
    nonempty := by
      obtain ⟨c, _, hc⟩ :=
        Finset.exists_max_image Finset.univ (score P CW BP) Finset.univ_nonempty
      exact ⟨c, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, fun d => hc d (Finset.mem_univ _)⟩⟩ }

-- ────────────────────────────────────────────────
-- Level 1 — ScoringRule
-- ────────────────────────────────────────────────

/-- Assigns a numeric score to each candidate from submitted ballots alone.
    No voter-weight information; suitable for unweighted rules. -/
class ScoringRule (Ballot : Type) (n m : ℕ) [NeZero n] [NeZero m] (L: LinearOrder (Fin m)) where
  candScore : Profile n m -> CandW m -> BallotProfile Ballot n → Cand m → WeightType

instance (priority := 100) instVotingRuleOfScoring
    [sr : ScoringRule Ballot n m L] : VotingRule Ballot n m L where
  winners P CW BP := scoreWinners sr.candScore P CW  BP

