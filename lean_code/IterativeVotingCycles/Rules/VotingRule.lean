import IterativeVotingCycles.Basic
import IterativeVotingCycles.Ballots
import IterativeVotingCycles.Misc
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Basic

variable {n m : ℕ} [NeZero n] [NeZero m]

structure NonEmptyFinset (α : Type*) where
  val : Finset α
  nonempty : val.Nonempty

/-- Tie-break by choosing the lex-smallest winner (F;in m has a natural linear order). -/
def NonEmptyFinset.lexMin {m : ℕ} (s : NonEmptyFinset (Cand m)) (L: LinearOrder (Fin m)) : Cand m :=
  s.val.min' s.nonempty


abbrev CandW  (m : ℕ) [NeZero m]:= Cand m -> WeightType
abbrev VoterW (n : ℕ) [NeZero n]:= Voter n -> WeightType

class VotingRule (Ballot : Type) (n m : ℕ) [NeZero n] [NeZero m] (L: LinearOrder (Fin m)) where
  winners : VoterW n -> CandW m -> BallotProfile Ballot n → NonEmptyFinset (Cand m)
  winner (P: VoterW n)  (CW : CandW m) (BP: BallotProfile Ballot n): Cand m:=  (winners P CW BP).lexMin L

def candRelativePreference {n m : ℕ} [NeZero n] [NeZero m] (P : RankingVotes n m) (ba : Cand m) (bb: Cand m) : ℕ :=
  Finset.univ.filter (fun (p :Voter n) => prefers (P p) ba bb) |> Finset.card

def condorcetWinner (P : RankingVotes n m)  (b: Cand m): Prop :=
  ∀ p : Cand m, p ≠ b → (candRelativePreference P p b) > n/2

def weakCondorcetWinner (P : RankingVotes n m) (b : Cand m):= 
  ∀ p : Cand m, p ≠ b → (candRelativePreference P p b) ≥ n/2

instance (P: RankingVotes n m) (b : Cand m) :
    Decidable (condorcetWinner P b) := by
  unfold condorcetWinner
  infer_instance

def condorcetConsistentVR (f: BallotProfile (RankingBallot  m) n -> Cand m) (P : RankingVotes n m): Prop 
  :=
    ∃ c : Cand m, condorcetWinner P c ↔  f P = c

