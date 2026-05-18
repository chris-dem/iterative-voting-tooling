import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Algebra.BigOperators.Fin
import IterativeVotingCycles.Basic
import IterativeVotingCycles.Ballots
import IterativeVotingCycles.Rules.VotingRule
import IterativeVotingCycles.Rules.ScoringRule

open Classical
open BigOperators

variable {n m : ℕ} [NeZero n] [NeZero m]
variable {Ballot : Type} [DecidableEq Ballot]



/-- A voter performs a beneficial deviation if they change their ranking
    and strictly prefer the new winner to the old one -/
def beneficialStep (P: Profile n m) (VR: BallotProfile Ballot n -> Fin m) (V V' : BallotProfile Ballot n)
  : Prop :=
  ∃ v : Voter n,
    (∀ u ≠ v, V u = V' u) ∧
    prefers (P v).preference (VR V) (VR V')

instance (P: Profile n m) (VR: BallotProfile Ballot n -> Fin m) (V V' : BallotProfile Ballot n):
   Decidable (beneficialStep P VR V V') := by
  unfold beneficialStep prefers
  infer_instance


def deviators
  (V V' : BallotProfile Ballot n) : Finset (Fin n) :=
  Finset.univ.filter (fun u => V u ≠ V' u)


-- Theorem statement
def groupbeneficialStep (P: Profile n m) (VR: BallotProfile Ballot n -> Fin m) (V V' : BallotProfile Ballot n)
    : Prop :=
    let A := deviators V V'
    A.Nonempty ∧ (∀ u ∈ A , prefers (P u).preference (VR V) (VR V'))

instance (P : Profile n m) (VR: BallotProfile Ballot n -> Fin m) (V V' : BallotProfile Ballot n):
    Decidable (groupbeneficialStep P VR V V') := by
  unfold groupbeneficialStep deviators
  infer_instance
