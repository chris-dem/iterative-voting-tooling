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
import IterativeVotingCycles.Dynamics.PathStable.PluralityVoting.Basic

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

private lemma unreachable_from_truth (k : ℕ): 
    ∀ f,  f 0 = exBallots → ¬ isDirectPathStableGroup (k := k) dummyProfile (PV.unweightedPluralityVoting linFin') f := by
      intro f hfirst
      by_contra hExists
      rw [isDirectPathStableGroup] at hExists
      obtain ⟨hMid, hLast⟩  := hExists
      set Vlast := f supFinK
      apply (is_stable_iff_1234_vote_0 Vlast).mp at hLast

      have hNstepV2 : ∀ i, i < 3 → ∀ ts, (f ts) i ≠ 2 := by
          intro i hi ts
          induction ts using Fin.induction with
          | zero  => 
            simp [hfirst,exBallots]
            intro hNeg
            fin_cases i <;> dsimp at hNeg <;> simp at hNeg <;> simp at hi
          | succ k hk => 
            intro hNext
            have hMidApplied :=  hMid k
            simp [groupbeneficialDirectStep] at hMidApplied
            obtain ⟨hDiv, hPref⟩ := hMidApplied
            by_cases h2InDiv : i ∈ (deviators (f k.castSucc) (f k.succ))
            obtain ⟨hPref, hWin⟩ := hPref i h2InDiv
            rw [← hWin] at hPref
            set cWin := (PV.unweightedPluralityVoting linFin' (f k.castSucc)) with hcWin
            clear_value cWin
            fin_cases i <;>(
            fin_cases cWin <;> simp at hNext <;>  simp [prefers, dummyProfile, toFunc,Vector.ofFn,Vector.get,rankingFromVector] at hPref
            <;> simp [hNext] at hPref
            <;> simp at hi
            <;> rw [deviators,hNext] at h2InDiv
            <;> exact absurd h2InDiv hk)
            simp [deviators, hNext, hk] at h2InDiv
          
      have hExistsV2 : ∃ t1, ((f t1) 2 = 1)  ∧  ∀ t',  (t1 < t') → (f t') 2 = 0 := by
        let A := Finset.univ.filter (fun n => (f n) 2 = 1) 
        have hAnE : A.Nonempty := by
          simp [Finset.Nonempty]
          use 0
          simp [A, hfirst, exBallots]
        set t:= A.max' hAnE with hTA
        use t
        constructor 
        have hTAe : t ∈ A := Finset.max'_mem A hAnE
        simp [A] at hTAe
        exact hTAe
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
        -- Deviated to c or 2
        simp at hx
        
        have hNstep0 := hNstepV2 0 (by simp) t'
        have hNstep1 := hNstepV2 1 (by simp) t'
        have hNstep2 := hNstepV2 2 (by simp) t'
        symm at hx
        exact absurd hx hNstep2


      have hNstepV4 : ∀ ts, (f ts) 4 ≠ 0 := by
          intro ts
          induction ts using Fin.induction with
          | zero   => 
            simp [hfirst,exBallots]
          | succ i hi => 
            intro hNext
            have hMidApplied :=  hMid i
            simp [groupbeneficialDirectStep] at hMidApplied
            obtain ⟨hDiv, hPref⟩ := hMidApplied
            by_cases h2InDiv : 4 ∈ (deviators (f i.castSucc) (f i.succ))
            obtain ⟨hPref, hWin⟩ := hPref 4 h2InDiv
            rw [← hWin] at hPref
            set cWin := (PV.unweightedPluralityVoting linFin' (f i.castSucc)) with hcWin
            clear_value cWin
            fin_cases cWin <;> simp [prefers, dummyProfile, toFunc,Vector.ofFn,Vector.get,rankingFromVector,hNext] at hPref
            simp [deviators,hNext] at h2InDiv
            exact absurd h2InDiv hi


      have hNstepV3 : ∀ ts, (f ts) 3 ≠ 1 := by
          intro ts
          induction ts using Fin.induction with
          | zero   => 
            simp [hfirst,exBallots]
          | succ i hi => 
            intro hNext
            have hMidApplied :=  hMid i
            simp [groupbeneficialDirectStep] at hMidApplied
            obtain ⟨hDiv, hPref⟩ := hMidApplied
            by_cases h2InDiv : 3 ∈ (deviators (f i.castSucc) (f i.succ))
            obtain ⟨hPref, hWin⟩ := hPref 3 h2InDiv
            rw [← hWin] at hPref
            set cWin := (PV.unweightedPluralityVoting linFin' (f i.castSucc)) with hcWin
            clear_value cWin
            fin_cases cWin <;> simp [prefers, dummyProfile, toFunc,Vector.ofFn,Vector.get,rankingFromVector,hNext] at hPref
            simp [deviators,hNext] at h2InDiv
            exact absurd h2InDiv hi

      have hExistsV3 : ∃ t1, (f t1) 3 = 2 ∧ ∀ t',  (t1 < t') → (f t') 3 = 0 := by
        let A := Finset.univ.filter (fun n => (f n) 3 = 2)
        have hAnE : A.Nonempty := by
          simp [Finset.Nonempty]
          use 0
          simp [A, hfirst, exBallots]
        set t:= A.max' hAnE with hTA
        use t
        constructor
        have hTAe : t ∈ A := Finset.max'_mem A hAnE
        simp [A] at hTAe
        exact hTAe
        intro t' htt'
        by_contra hContra
        set x' : Fin 3:= (f t') 3 with hx
        clear_value x'
        fin_cases x' 
        -- Case x' = 0: contradicts hContra
        . exact hContra rfl
        -- Deviated to b or 1
        simp at hx
        
        have hNstep2 := hNstepV3 t'
        symm at hx
        exact absurd hx hNstep2
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
      obtain ⟨t1V2, ht1V, ht1R⟩ := hExistsV2
      obtain ⟨t2V3, ht2V, ht2R⟩ := hExistsV3

      have ht1V2GT : t1V2.val < k := by
        by_contra h
        push Not at h
        apply Nat.le_iff_lt_or_eq.mp at h
        rcases h with hLt | hEq
        apply Nat.add_one_le_of_lt at hLt
        have h2 := t1V2.isLt
        exact absurd t1V2.isLt (by omega)
        simp [Vlast, supFinK] at hLast
        have htlast2 := hLast 2 (by simp)
        simp [hEq] at htlast2 
        rw [ht1V] at htlast2
        simp at htlast2

      let t1V2D := (Fin.castLT t1V2 ht1V2GT)
      have ht2Next := ht1R t1V2D.succ (by apply Fin.val_fin_lt.mp ; simp [t1V2D])
      have h2DeviatorP : 2 ∈ deviators (f t1V2D.castSucc) (f t1V2D.succ) := by 
          simp [deviators]
          intro hND
          simp [ht2Next,t1V2D] at hND
          rw [ht1V] at hND
          simp at hND

      have ht2V3GT : t2V3.val < k := by
        by_contra h
        push Not at h
        apply Nat.le_iff_lt_or_eq.mp at h
        rcases h with hLt | hEq
        apply Nat.add_one_le_of_lt at hLt
        have h2 := t2V3.isLt
        exact absurd t2V3.isLt (by omega)
        simp [Vlast, supFinK] at hLast
        have htlast2 := hLast 3 (by simp)
        simp [hEq] at htlast2 
        rw [ht2V] at htlast2
        simp at htlast2

      let t2V3D := (Fin.castLT t2V3 ht2V3GT)
      have ht3Next := ht2R t2V3D.succ (by apply Fin.val_fin_lt.mp ; simp [t2V3D])
      have h3DeviatorP : 3 ∈ deviators (f t2V3D.castSucc) (f t2V3D.succ) := by 
          simp [deviators]
          intro hND
          simp [ht3Next,t2V3D] at hND
          rw [ht2V] at hND
          simp at hND

      have hPVatT1 : PV.unweightedPluralityVoting linFin'  (f t1V2) = 2 := by
        by_contra hContra
        set c := PV.unweightedPluralityVoting linFin'  (f t1V2) with huPVc
        clear_value c
        fin_cases c
        simp at huPVc
        have hMidN := hMid t1V2D
        simp [groupbeneficialDirectStep] at hMidN
        obtain ⟨hDiv , hPref⟩  := hMidN
        obtain ⟨h2Pref, hWin⟩ := (hPref 2 h2DeviatorP)
        rw [ht2Next] at hWin
        simp [← hWin, t1V2D, ← huPVc, prefers ] at h2Pref
        -- Next case
        simp at huPVc
        have hMidN := hMid t1V2D
        simp [groupbeneficialDirectStep] at hMidN
        obtain ⟨hDiv , hPref⟩  := hMidN
        obtain ⟨h2Pref, hWin⟩ := (hPref 2 h2DeviatorP)
        rw [ht2Next] at hWin
        simp [← hWin, t1V2D, ← huPVc, prefers,dummyProfile,toFunc,Vector.ofFn,Vector.get, rankingFromVector] at h2Pref
        -- Assume that the winner is c
        simp at huPVc
        simp at hContra



      have hPVatT2 : PV.unweightedPluralityVoting linFin'  (f t2V3) = 1 := by
        by_contra hContra
        set c := PV.unweightedPluralityVoting linFin'  (f t2V3) with huPVc
        clear_value c
        fin_cases c
        -- Next case
        simp at huPVc
        have hMidN := hMid t2V3D
        simp [groupbeneficialDirectStep] at hMidN
        obtain ⟨hDiv , hPref⟩  := hMidN
        obtain ⟨h2Pref, hWin⟩ := (hPref 3 h3DeviatorP)
        rw [ht3Next] at hWin
        simp [← hWin, t2V3D, ← huPVc, prefers,dummyProfile,toFunc,Vector.ofFn,Vector.get, rankingFromVector] at h2Pref
        -- Assume that the winner is c

        simp at huPVc
        simp at hContra
        simp at huPVc
        have hMidN := hMid t2V3D
        simp [groupbeneficialDirectStep] at hMidN
        obtain ⟨hDiv , hPref⟩  := hMidN
        obtain ⟨h2Pref, hWin⟩ := (hPref 3 h3DeviatorP)
        rw [ht3Next] at hWin
        simp [← hWin, t2V3D, ← huPVc, prefers,dummyProfile,toFunc,Vector.ofFn,Vector.get, rankingFromVector] at h2Pref

      have h_t1_is_lt_t2 : t1V2 < t2V3 := by
        by_contra hp
        push Not at hp
        apply Nat.lt_or_eq_of_le at hp
        rw [Or.comm] at hp
        rcases  hp with hpEq | hpGt
        apply (Fin.val_eq_val t2V3 t1V2).mp at hpEq
        rw [← hpEq, hPVatT2] at hPVatT1
        simp at hPVatT1
        -- At Gt
        apply Fin.val_fin_lt.mp at hpGt
        -- Main idea of the proof is to argue that t1V2 must be a count of one
        -- Therefore cannot be winning
        
        have hSub : Finset.univ.filter (fun v => (f t1V2) v = 2) ⊆ {4} := by
          simp
          by_cases hLast :(f t1V2) 4 = 2
          right
          ext v
          constructor
          intro hv
          simp at hv
          simp
          cases v using Fin.lastCases  with 
            | last =>
              simp
            | cast i =>
              cases i using Fin.lastCases with
                | last =>
                  simp
                  simp [ht2R t1V2 hpGt] at hv
                | cast j =>
                  have hNstepApplied := hNstepV2 j.castSucc.castSucc j.isLt t1V2
                  exact absurd hv hNstepApplied
          -- Second dir
          simp 
          intro h1
          rw [h1]
          exact hLast
          left
          intro v
          cases v using Fin.lastCases  with 
            | last =>
              exact hLast
            | cast i =>
              cases i using Fin.lastCases with
                | last =>
                  simp
                  have hPreL := ht2R t1V2 hpGt
                  simp [hPreL]
                | cast j =>
                  have hNstepApplied := hNstepV2 j.castSucc.castSucc j.isLt t1V2
                  intro hv
                  exact absurd hv hNstepApplied

        have hSubCard := Finset.card_le_card hSub
        simp at hSubCard
        have ht1Winner : ∃ c , PV.unweightedPluralityScore linFin' (f t1V2) 2 < PV.unweightedPluralityScore linFin' (f t1V2) c := by
          by_contra h
          push Not at h
          simp [PV.unweightedPluralityScore, PV.pluralityScore, ScoringRule.candScore] at h
          have hp := fun c => (h c).trans hSubCard
          have hTot := unweighted_score_closure linFin' (f t1V2)
          -- Using our hypo we have that
          have huBsum : (∑ c, (Finset.univ.filter (fun v => (f t1V2) v = c)).card) ≤ 3 := by
            have hle := Finset.sum_le_card_nsmul Finset.univ
              (fun c => (Finset.univ.filter (fun v => (f t1V2) v = c)).card) 1
              (by intro c hf; simp; exact hp c)
            simp at hle  
            exact hle
          simp [PV.unweightedPluralityScore, PV.pluralityScore, ScoringRule.candScore] at hTot
          rw [hTot] at huBsum
          simp at huBsum
        simp [PV.unweightedPluralityScore, PV.pluralityScore, ScoringRule.candScore] at ht1Winner
        obtain ⟨winner, hvW⟩  := ht1Winner
        simp [PV.unweightedPluralityVoting, PV.pluralityVoting, VotingRule.winner,
        ScoringRule.candScore,scoreWinners,NonEmptyFinset.lexMin, Finset.min'_eq_iff] at hPVatT1
        have hl := hPVatT1.left winner
        exact absurd hl (Nat.not_le.mpr hvW)
      have hNEt20 : t2V3 ≠ 0 := by
        intro hContra
        rw [hContra] at h_t1_is_lt_t2
        simp at h_t1_is_lt_t2
      let tstar := (Fin.pred t2V3 hNEt20)
      let tstarC := tstar.castSucc
      have hsucc : tstar.succ = t2V3      := Fin.succ_pred t2V3 hNEt20
      have hle   : t1V2 ≤ tstar.castSucc           := by
        simp at tstar
        simp [Fin.le_iff_val_le_val]
        apply Nat.le_iff_lt_add_one.mpr
        have hval : tstar.val + 1 = t2V3.val := by
           have := congr_arg Fin.val hsucc
           simpa [Fin.val_succ] using this
        omega
      set c := PV.unweightedPluralityVoting linFin' (f tstarC) with hcPVu
      clear_value c
      fin_cases c
      symm at hcPVu
--      simp [PV.unweightedPluralityVoting, PV.pluralityVoting, VotingRule.winner,
--    scoreWinners, ScoringRule.candScore, NonEmptyFinset.lexMin,
--    Finset.min'_eq_iff]  at hcPVu
--    obtain ⟨hcPV, hcPVOrder⟩  := hcPVu
      have hNextStar := hMid tstar
      simp [groupbeneficialDirectStep,hsucc] at hNextStar
      obtain ⟨h_deviator_tstar, h_dev_win_tstar⟩ :=  hNextStar
      simp [tstarC, hcPVu, hPVatT2] at h_dev_win_tstar
      -- So we know that the only deviator must be (0-index) v2 or v4
      -- We know that v2 cannot be deviating therefore it must only be v4
      -- But if A is winnig, it must be the case that at least 3 voters win
      -- Since v4 will never vote for A we get a contradiction

      -- Proof that v4 can be the only deviator
      have h_deviators_is_singleton_4 : deviators (f tstar.castSucc) (f t2V3) = {4} := by
        ext v
        constructor
        intro h
        fin_cases v
        -- 0
        simp at h
        have h' := h_dev_win_tstar 0 h
        simp [dummyProfile,toFunc, rankingFromVector, Vector.get, prefers] at h'
        -- 1
        simp at h
        have h' := h_dev_win_tstar 1 h
        simp [dummyProfile,toFunc, rankingFromVector, Vector.get, prefers] at h'
        -- 2
        rcases Nat.le_iff_lt_or_eq.mp hle with h1 | h2
        simp [deviators, ht1R tstar.castSucc h1, ht1R t2V3 h_t1_is_lt_t2] at h
        have h1 := (Fin.val_eq_val t1V2 tstar.castSucc).mp h2
        simp [tstarC,← h1, hPVatT1] at hcPVu
        -- 3
        simp at h
        have h_dev_3 := (h_dev_win_tstar 3 h).left
        simp [prefers, dummyProfile, Vector.get, rankingFromVector, toFunc] at h_dev_3
        -- 4
        simp
        -- Other dir
        intro h
        simp at h
        simp at hcPVu
        obtain ⟨q, hq⟩ := h_deviator_tstar
        have hnext := h_dev_win_tstar q hq
        obtain ⟨h_pref, h_val⟩ := hnext
        fin_cases q
        simp [prefers, dummyProfile, Vector.get, rankingFromVector, toFunc] at h_pref
        simp [prefers, dummyProfile, Vector.get, rankingFromVector, toFunc] at h_pref
        simp [ht1R t2V3 h_t1_is_lt_t2] at h_val
        simp [ht2V] at h_val
        simp [← h]at hq
        exact hq

      -- Proof that A can only win if at least 3 voters vote
      have h_0_wins_iff_3 : ∀ VP : CandidateVotes 5 3,
          PV.unweightedPluralityVoting linFin' VP = 0
        ↔ PV.unweightedPluralityScore linFin' VP 0 ≥ 3  := by
          intro VP
          constructor
          simp [PV.unweightedPluralityScore, PV.pluralityScore, PV.unweightedPluralityVoting, PV.pluralityVoting, VotingRule.winner,
            ScoringRule.candScore,scoreWinners,NonEmptyFinset.lexMin, Finset.min'_eq_iff]
          intro hPV hR
          by_contra h'
          push Not at h'
          have h_larger: ∃ k ,k ≠ 0 ∧   (Finset.univ.filter (fun v => VP v = 0)).card
                ≤  (Finset.univ.filter (fun v => VP v = k)).card := by
                  by_contra h_cc
                  push Not at h_cc
                  apply Nat.le_iff_lt_add_one.mpr at h'
                  have h_cc_add := fun p hp => Nat.le_iff_lt_add_one.mpr ((h_cc p hp).trans_le h')
                  have hp' :=  Fin.sum_univ_three (fun k => (Finset.univ.filter (fun v => VP v = k)).card)
                  have hp'Tot := unweighted_score_closure linFin' VP
                  have h1cc := h_cc_add 1 (by simp)
                  have h2cc := h_cc_add 2 (by simp)
                  simp [PV.unweightedPluralityScore, PV.pluralityScore, ScoringRule.candScore, hp'] at hp'Tot
                  have h_add_all := Nat.add_le_add (Nat.add_le_add h1cc h2cc) h'
                  simp at h_add_all
                  rw [Nat.add_comm, ← Nat.add_assoc, hp'Tot] at h_add_all
                  omega
          obtain ⟨k, hkpNE0, hkp⟩ := h_larger
          have hPV' :=  fun c => (hPV c).trans hkp
          have hR' := hR k hPV'
          apply Nat.le_iff_lt_or_eq.mp at hR'
          rcases hR' with hLT | hEq
          simp at hLT
          simp at hEq
          exact hkpNE0 hEq

          simp [PV.unweightedPluralityScore, PV.pluralityScore, PV.unweightedPluralityVoting, PV.pluralityVoting, VotingRule.winner,
            ScoringRule.candScore,scoreWinners,NonEmptyFinset.lexMin, Finset.min'_eq_iff]
          intro hp
          constructor
          intro d
          by_cases hEqd0 : d = 0
          simp [hEqd0]
          by_contra  hp'
          push Not at hp'
          have hLeCP : ∑ k ∈  {d, 0}, (Finset.univ.filter (fun v => VP v = k)).card  ≤ ∑ k
              , (Finset.univ.filter (fun v => VP v = k)).card  := by
              apply Finset.sum_le_sum_of_subset
              simp
          have hTotSum := unweighted_score_closure linFin' VP
          simp [PV.unweightedPluralityScore, PV.pluralityScore, ScoringRule.candScore] at hTotSum
          simp [hTotSum, Finset.sum_pair (hEqd0)] at hLeCP
          have hp'1 := Nat.add_lt_add_left  hp' ((Finset.univ.filter (fun v => VP v = 0)).card)
          have hpp := Nat.add_le_add hp hp
          simp at hpp
          rw [Nat.add_comm] at hLeCP
          have htrans  := (hpp.trans_lt hp'1).trans_le hLeCP
          omega
          intro d hd
          apply Nat.le_iff_lt_or_eq.mpr
          by_cases heq0 : d = 0
          right
          simp [heq0]
          have hdD := hd 0
          have hLeCP : ∑ k ∈  {d, 0}, (Finset.univ.filter (fun v => VP v = k)).card  ≤ ∑ k
              , (Finset.univ.filter (fun v => VP v = k)).card  := by
              apply Finset.sum_le_sum_of_subset
              simp
          have hTotSum := unweighted_score_closure linFin' VP
          simp [PV.unweightedPluralityScore, PV.pluralityScore, ScoringRule.candScore] at hTotSum
          simp [hTotSum, Finset.sum_pair (heq0)] at hLeCP
          have hp'1 := Nat.add_le_add_left  hdD ((Finset.univ.filter (fun v => VP v = 0)).card)
          have hpp := Nat.add_le_add hp hp
          simp at hpp
          rw [Nat.add_comm] at hLeCP
          have htrans  := (hpp.trans hp'1).trans hLeCP
          omega
      simp at hcPVu
      have hrules := (h_0_wins_iff_3 (f tstarC)).mp hcPVu
      simp [PV.unweightedPluralityScore, PV.pluralityScore, ScoringRule.candScore] at hrules
      have ht2V3 : PV.unweightedPluralityScore linFin' (f t2V3) 0 ≥ 3 := by
        simp [PV.unweightedPluralityScore, PV.pluralityScore, ScoringRule.candScore]
        by_contra hp
        push Not at hp
        have hsub : Finset.univ.filter (fun b => (f tstarC)  b = 0) ⊆  Finset.univ.filter (fun b => (f t2V3) b = 0) := by
          intro v hv
          simp at hv
          simp 
          by_contra h
          rw [← hv] at h
          have hImp : v =4 := by
            simp [deviators] at h_deviators_is_singleton_4
            have hnk := h_deviators_is_singleton_4
            have hv : v ∈ deviators (f tstar.castSucc) (f t2V3) := by
              simp [deviators]
              intro hqv
              symm at hqv
              exact h hqv
            have hOo := h_deviators_is_singleton_4.subset hv
            exact Finset.eq_of_mem_singleton hOo
          have hn4 := hNstepV4 tstarC
          rw [hImp] at hv
          exact hn4 hv
        have hSub := hrules.trans (Finset.card_le_card hsub)
        exact absurd hSub (Nat.not_le.mpr hp)

      apply (h_0_wins_iff_3 (f t2V3)).mpr at ht2V3
      simp [hPVatT2] at ht2V3
      simp at hcPVu
      sorry











end ReachabilityCounterExamplePV

