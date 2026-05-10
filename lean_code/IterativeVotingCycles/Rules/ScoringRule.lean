import IterativeVotingCycles.Basic
import IterativeVotingCycles.Ballots
import IterativeVotingCycles.Rules.VotingRule
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Fin

open Classical
open BigOperators


variable {n m: ℕ} [NeZero n] [NeZero m]
abbrev WeightFunction (n m: ℕ) := (Voter n ⊕  Cand m) -> WeightType

-- lemma winners_nonempty (P : Profile n m) (C : CandW m) (V : VVote n m) : 
--   (winners P C V).Nonempty := by
--     rw [winners]
--     let s : Finset (Fin m) := Finset.univ
--     obtain ⟨c, h_mem, h_max⟩ := Finset.exists_max_image s (fun c => pluralityScore P C V c) Finset.univ_nonempty
--     use c
--     simp only [Finset.mem_filter, Finset.mem_univ, true_and, isWinner]
--     intro p
--     apply h_max
--     exact Finset.mem_univ p



class ScoringRule (Ballot : Type) (n m : ℕ) [NeZero n] [NeZero m]  where
  evalCandidate : VoterProfile m -> BallotProfile Ballot n -> Cand m -> WeightType
