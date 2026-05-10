import IterativeVotingCycles.Basic
import IterativeVotingCycles.Ballots
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Basic

structure NonEmptyFinset (α : Type*) where
  val : Finset α
  nonempty : val.Nonempty

/-- Tie-break by choosing the lex-smallest winner (F;in m has a natural linear order). -/
def NonEmptyFinset.lexMin {m : ℕ} (s : NonEmptyFinset (Cand m)) (L: LinearOrder (Fin m)) : Cand m :=
  s.val.min' s.nonempty


abbrev CandW  (m : ℕ) [NeZero m]:= Cand m -> WeightType

class VotingRule (Ballot : Type) (n m : ℕ) [NeZero n] [NeZero m] (L: LinearOrder (Fin m)) where
  winners : Profile n m -> CandW m -> BallotProfile Ballot n → NonEmptyFinset (Cand m)
  winner (P: Profile n m)  (CW : CandW m) (BP: BallotProfile Ballot n): Cand m:=  (winners P CW BP).lexMin L
