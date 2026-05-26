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


structure StepDynamic where
  step : (P: Profile n m) -> (VR: BallotProfile Ballot n -> Fin m) -> (V V' : BallotProfile Ballot n) -> Prop
  beneficial_prop : ∀ P VR V V', step P VR V V' →  groupbeneficialStep P VR V V'


def BeneficialDynamic : StepDynamic (n := n)  (m := m) (Ballot := Ballot):= ⟨groupbeneficialStep, by simp⟩ 


def groupbeneficialDirectStep (P: Profile n m) (VR: CandidateVotes n m -> Fin m) (V V' : CandidateVotes n m)
    : Prop :=
    let A := deviators V V'
    A.Nonempty ∧ (∀ u ∈ A , (prefers (P u).preference (VR V) (VR V') ∧ V' u = VR V'))

instance (P : Profile n m) (VR: CandidateVotes n m -> Fin m) (V V' : CandidateVotes n m):
    Decidable (groupbeneficialDirectStep P VR V V') := by
  unfold groupbeneficialDirectStep deviators
  infer_instance

def GroupBeneficialAndDirectDynamic : StepDynamic (n := n)  (m := m) (Ballot := CandidateBallot m):= ⟨groupbeneficialDirectStep, by 
  simp [groupbeneficialDirectStep, groupbeneficialStep]; intro VR hq V V' hdq hud; 
    have hud' :=  fun q => fun hq => (hud q hq).left;
    exact And.intro hdq hud'⟩

def groupbeneficialDirectRBStep (P: Profile n m) (VR: RankingVotes n m -> Fin m) (V V' : RankingVotes n m)
    : Prop :=
    let A := deviators V V'
    A.Nonempty ∧ (∀ u ∈ A , (prefers (P u).preference (VR V) (VR V') 
      ∧ (V' u).pos (VR V') = m - 1 -- Current winner is at the top of the ballot
      ∧ (V' u).pos (VR V ) = 0 )) -- Previous winner is at the bottom of the deviator ballot


def GroupBeneficialAndDirectRDynamic : StepDynamic (n := n)  (m := m) (Ballot := RankingBallot m):= ⟨groupbeneficialDirectRBStep, by 
  simp [groupbeneficialDirectRBStep, groupbeneficialStep]; intro VR hq V V' hdq hud; 
    have hud' :=  fun q => fun hq => (hud q hq).left;
    exact And.intro hdq hud'⟩ 

def groupbeneficialTBStep (P: Profile n m) (VR: RankingVotes n m -> Fin m) (V V' : RankingVotes n m)
    : Prop :=
    let A := deviators V V'
    A.Nonempty ∧ (∀ u ∈ A , (prefers (P u).preference (VR V) (VR V')
      ∧ (V' u).pos (VR V') = m - 1 -- Current winner is at the top of the ballot
      ∧ (V' u).pos (VR V ) = 0 )) -- Previous winner is at the bottom of the deviator ballot


instance (P: Profile n m) (VR: RankingVotes n m -> Fin m) (V V' : RankingVotes n m):
    Decidable (groupbeneficialDirectRBStep P VR V V') := by
  unfold groupbeneficialDirectRBStep deviators
  infer_instance 


def GroupTopBottomRDynamic : StepDynamic (n := n)  (m := m) (Ballot := RankingBallot m):= ⟨groupbeneficialTBStep, by 
  simp [groupbeneficialTBStep, groupbeneficialStep]; intro VR hq V V' hdq hud; 
    have hud' :=  fun q => fun hq => (hud q hq).left;
    exact And.intro hdq hud'⟩ 
