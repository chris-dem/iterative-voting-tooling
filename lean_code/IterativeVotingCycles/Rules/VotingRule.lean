import IterativeVotingCycles.Basic
import IterativeVotingCycles.Ballots
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Basic

structure NonEmptyFinset (α : Type*) where
  val : Finset α
  nonempty : val.Nonempty


class VotingRule (Ballot : Type) (n m : ℕ) [NeZero n] [NeZero m] (L: LinearOrder (Fin m)) where
  winners : VoterProfile m → BallotProfile Ballot n → NonEmptyFinset (Cand m)
  
  winner (VP: VoterProfile m) (BP: BallotProfile Ballot n): Cand m:= 
    let winset := winners VP BP
    let v := winset.val
    @Finset.min' _ L v winset.nonempty
