import Mathlib.Tactic
import Mathlib.Tactic.Contrapose
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Algebra.BigOperators.Fin
import IterativeVotingCycles.Basic
import IterativeVotingCycles.Ballots
import IterativeVotingCycles.Rules.VotingRule
import IterativeVotingCycles.Rules.ScoringRule
import IterativeVotingCycles.Rules.Candidate.Plurality
import IterativeVotingCycles.Misc
import IterativeVotingCycles.Dynamics.Step

open Classical
open BigOperators
open Fin

variable {n m : ℕ} [NeZero n] [NeZero m]
variable {Ballot : Type} [DecidableEq Ballot] [Fintype Ballot]

def isStableState (P: Profile n m) (VR: BallotProfile Ballot n -> Fin m) (V: BallotProfile Ballot n) : Prop :=
  ∀ V', ¬ (groupbeneficialStep P VR V V')

instance (P : Profile n m) (VR: BallotProfile Ballot n -> Fin m)
  (V: BallotProfile Ballot n) :
    Decidable (isStableState P VR V) := by
  unfold isStableState groupbeneficialStep prefers
  infer_instance

def supFinKPlusOne {k : ℕ} : Fin (k+1) :=
  Fin.last k

def supFinK {k : ℕ} [NeZero k] : Fin k := by
  exact ⟨k-1,  (by exact Nat.pred_lt (NeZero.ne k))⟩ 


def isPathStableGroup {k : ℕ} 
    (P : Profile n m) (VR: BallotProfile Ballot n -> Fin m) 
    (f: Fin (k + 1) → BallotProfile Ballot n) : Prop :=
  (∀ i : Fin k, groupbeneficialStep P VR (f (i.castSucc)) (f (i.addNat 1) )) ∧
  isStableState P VR (f supFinK)

instance {k : ℕ} (P : Profile n m) (VR: BallotProfile Ballot n -> Fin m)
  (f: Fin (k + 1) ->  BallotProfile Ballot n) :
    Decidable (isPathStableGroup P VR f) := by
  unfold isPathStableGroup
  infer_instance

def isDirectStableState   (P: Profile n m) (VR: CandidateVotes n m -> Fin m) (V: CandidateVotes n m) : Prop := 
      ∀ V', ¬ (groupbeneficialDirectStep P VR V V')

instance (P: Profile n m) (VR: CandidateVotes n m -> Fin m) (V: CandidateVotes n m):
    Decidable (isDirectStableState P VR V) := by
  unfold isDirectStableState
  infer_instance

def isDirectPathStableGroup {k : ℕ} 
    (P : Profile n m) (VR: CandidateVotes n m -> Fin m) 
    (f: Fin (k + 1) → CandidateVotes n m) : Prop :=
  (∀ i : Fin k, groupbeneficialDirectStep P VR (f (i.castSucc)) (f (i.addNat 1) )) ∧ 
  isDirectStableState P VR (f supFinK)

instance {k  : ℕ} (P : Profile n m) (VR: CandidateVotes n m -> Fin m) 
    (f: Fin (k + 1) → CandidateVotes n m) :
    Decidable (isDirectPathStableGroup P VR f) := by
  unfold isDirectPathStableGroup
  infer_instance

def exists_path_stable_beneficial (k : ℕ) (V0 : CandidateVotes n m) : Prop := 
  ∃ (P : Profile n m) (VR : CandidateVotes n m → Fin m) 
    (f : Fin (k + 1) → CandidateVotes n m),
    (f 0 = V0) ∧  isDirectPathStableGroup P VR f

def exists_path_stable_beneficial_and_direct_from_f0 (k : ℕ) (V0 : BallotProfile Ballot n) : Prop := 
  ∃ (P : Profile n m) (VR : BallotProfile Ballot n → Fin m)
    (f : Fin (k + 1) → BallotProfile Ballot n),
    (f 0 = V0) ∧  isPathStableGroup P VR f

lemma direct_sub_beneficial (P: Profile n m) (VR: CandidateVotes n m -> Fin m): 
    Finset.univ.filter (fun (v : CandidateVotes n m) => isStableState P VR v) ⊆ Finset.univ.filter (fun (v : CandidateVotes n m) => isDirectStableState P VR v)    := by
      intro V hp
      simp [isDirectStableState, groupbeneficialDirectStep, deviators] 
      simp [isStableState, groupbeneficialStep, deviators]at hp
      intro Vnew h
      obtain ⟨x, hl, hr⟩ := hp Vnew h
      use x
      constructor
      exact hl
      contrapose! hr
      exact hr.left



def is_path_stable_general_vr  {k: ℕ} [NeZero n] [NeZero m]
    (P : Profile n m) (VR: BallotProfile Ballot n -> Fin m) 
    (f: Fin (k + 1) → BallotProfile Ballot n)
    (dyn : StepDynamic (n := n) (m := m) (Ballot := Ballot)): Prop :=
  (∀ i : Fin k, dyn.step P VR (f (i.castSucc)) (f (i.addNat 1) )) ∧ 
  ∀ V', ¬ dyn.step P VR (f supFinK) V'
  

def exists_path_vr_rule_condition_from_f0 (k : ℕ) (V0 : BallotProfile Ballot n) : Prop := 
  ∃ (P : Profile n m) (VR : BallotProfile Ballot n → Fin m)
    (f : Fin (k + 1) → BallotProfile Ballot n),
    (f 0 = V0) ∧  isPathStableGroup P VR f

