import Mathlib.Tactic
import Mathlib.Tactic.Contrapose
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Finite.Basic
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
import IterativeVotingCycles.Dynamics.PathStable.Basic

open Classical
open BigOperators
open Fin

variable {n m : ℕ} [NeZero n] [NeZero m]
variable {Ballot : Type} [DecidableEq Ballot] [Fintype Ballot]


section ReachabilityCounterExamplePV

private def dummyProfile : Profile 5 3 := toFunc (Vector.ofFn ![
  ⟨ rankingFromVector (Vector.ofFn ![2, 1, 0]) (by proveUnique)⟩,
  ⟨ rankingFromVector (Vector.ofFn ![2, 1, 0]) (by proveUnique)⟩,
  ⟨ rankingFromVector (Vector.ofFn ![1, 2, 0]) (by proveUnique)⟩,
  ⟨ rankingFromVector (Vector.ofFn ![1, 0, 2]) (by proveUnique)⟩,
  ⟨ rankingFromVector (Vector.ofFn ![0, 1, 2]) (by proveUnique)⟩
])



-- voter 0 and 1 vote for candidate 0; voter 2 votes for candidate 1
private def exBallots : BallotProfile (CandidateBallot 3) 5
  | ⟨0, _⟩ => ⟨0, by omega⟩
  | ⟨1, _⟩ => ⟨0, by omega⟩
  | ⟨2, _⟩ => ⟨1, by omega⟩
  | ⟨3, _⟩ => ⟨2, by omega⟩
  | ⟨4, _⟩ => ⟨2, by omega⟩

private abbrev linFin : LinearOrder (Fin 3)ᵒᵈ := inferInstance
private abbrev linFin' : LinearOrder (Fin 3) := linFin

#eval linFin'.lt  2 0

private lemma c_is_condorcet: condorcetWinner (VoterProfile.preference ∘ dummyProfile) 0 := by
  native_decide


private lemma is_stable_iff_1234_vote_0: 
    ∀ VP, isStableState dummyProfile (PV.unweightedPluralityVoting linFin') VP ↔ 
    ∀ i, i < 4 → VP i = 0 := by
  native_decide

private lemma unreachable_from_truth (k : ℕ) [NeZero k]: 
    ∀ f,  f 0 = exBallots → ¬ isPathStableGroup (k := k) dummyProfile (PV.unweightedPluralityVoting linFin') f := by
      intro f hfirst
      by_contra hExists
      rw [isPathStableGroup] at hExists
      obtain ⟨hMid, hLast⟩  := hExists
      set Vlast := f supFinK
      apply (is_stable_iff_1234_vote_0 Vlast).mp at hLast
      have hExists : ∃ t1, ∀ t',  (t1 < t') → (f t') 2 = 0 := by
        let A := Finset.univ.filter (fun n => (f n) 2 = 1) 
        have hAnE : A.Nonempty := by
          simp [Finset.Nonempty]
          use 0
          simp [A, hfirst, exBallots]
        set t:= A.max' hAnE with hTA
        use t
        intro t' htt'
        by_contra hContra
        set x' : Fin 3:= (f t') 2 with hx
        clear_value x'
        fin_cases x' 
        -- Case x' = 0: contradicts hContra
        . exact hContra rfl
        -- Cases x' = 1, x' = 2: need separate proofs
        simp at hx
        simp at hContra
        have hInA : t' ∈ A := by
          simp [A]
          symm at hx
          exact hx
        symm at hTA
        have hMax := ((Finset.max'_eq_iff A hAnE t).mp hTA).right t' hInA
        exact absurd htt' (by omega)
        simp at hx 

        rcases k with _ | _ | mq
        -- 0
        exact absurd rfl (NeZero.ne 0)
        -- 1
        have h : f (supFinK) = f 0 := by omega
        rw [hfirst] at h
        simp [Vlast] at hLast
        have hN := hLast 2 (by omega)
        simp [h,exBallots] at hN



        have hk1 : ∃ k, t'.val = t.val + k + 1 := Nat.exists_eq_add_of_lt (Fin.val_fin_lt.mpr htt')
        let ⟨k, hk2⟩  := hk1
        set tp : Fin (mq + 1 + 1) := ⟨t.val + k, by omega⟩ with htp
        have hMidTp :=  hMid tp (by simp [htp]; omega)
        simp [groupbeneficialStep] at hMidTp
 
        have hDiv : 2 ∈ deviators (f tp) (f (tp + 1)) := by
          simp [deviators]



      -- now have t ≤ tp and tp + 1 = t'




      sorry



end ReachabilityCounterExamplePV

