import Mathlib.Tactic
import Mathlib.Tactic.Contrapose
import Mathlib.Order.Basic
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
import IterativeVotingCycles.Rules.Candidate.Borda
import IterativeVotingCycles.Misc
import IterativeVotingCycles.Dynamics.Step
import IterativeVotingCycles.Dynamics.PathStable.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas


open Asymptotics Filter
open Classical LinearOrder
open BigOperators
open Fin

variable {n m : ℕ} [NeZero n] [NeZero m]
variable {Ballot : Type} [DecidableEq Ballot] [Fintype Ballot]

def rankingExtender (r : Ranking m) (m' : ℕ)  (h1 : NeZero m') (h2 : m < m'): Ranking m' :=
  let f := fun k => if h: k.val < m then (r.pos (k.castLT h)).castLE h2.le else k
  let h : Function.Bijective f := by
    constructor
    simp [Function.Injective]
    intro k1 k2 hfk
    simp [f] at hfk
    by_cases hk1 : k1.val < m <;> by_cases hk2 : k2.val < m <;> simp [hk1,hk2] at hfk
    have hbij :=   r.bij.injective hfk
    simp [Fin.ext_iff, ] at hbij
    exact Fin.eq_of_val_eq hbij
    simp [← hfk] at hk2
    simp [hfk] at hk1
    exact hfk
    simp [Function.Surjective]
    intro b
    simp [f]
    by_cases hk1 : b.val < m 

    obtain ⟨a, hlt⟩ := r.bij.surjective (b.castLT hk1 )
    use (a.castLE h2.le)
    simp [hlt, a.isLt, Fin.castLE]
    use b
    simp [hk1]
  ⟨f, h⟩ 

def profilePadding (P : Profile n m) (m' : ℕ) (h1 : NeZero m')(h2 : m < m') : Profile n m' :=
    fun (v : Voter n) => VoterProfile.mk  (rankingExtender (P v).preference m' h1 h2)


@[reducible] def LinearOrder.extend {m m' : ℕ} [NeZero m']
    (L : LinearOrder (Fin m)) (h1 : m < m') : LinearOrder (Fin m') :=
  haveI : LinearOrder (Fin m) := L
  LinearOrder.lift'
    (fun a : Fin m' => toLex <|
      if ha : a.val < m
        then Sum.inl (⟨a.val, ha⟩ : Fin m)
        else Sum.inr (⟨a.val - m, by omega⟩ : Fin (m' - m)))
    (by
      intro a b heq
      simp only [toLex_inj] at heq
      split_ifs at heq with ha hb
      · exact Fin.eq_of_val_eq (Fin.mk.inj (Sum.inl.inj heq))
      · simp at heq
        omega)


lemma LinearOrder.extend_lt {m m' : ℕ} [NeZero m'] (h : m < m') (L : LinearOrder (Fin m)) :
    ∀ x y : Fin m, (L.extend h). (x.castLT (by omega)) (y.castLT (by omega)) = L.compare x y := by
  letI : LinearOrder (Fin m) := L
  letI : LinearOrder (Fin m') := L.extend h
  intro x y

theorem uw_plurality_path_imp_uw_borda_path :
  ∃ (c₁: ℕ), 
    ∀ (k n m : ℕ) [NeZero n] [NeZero m] (hn_is_odd : Odd n) (P : Profile n m) (L : LinearOrder (Fin m)) 
      (pluralityPath : Fin (k + 1) → CandidateVotes n m),
      is_path_stable_general_vr P (PV.unweightedPluralityVoting L) pluralityPath GroupBeneficialAndDirectDynamic →
      ∃ (m' : ℕ)
        (hm_nezero : NeZero m') -- Added as a standard explicit variable
        (hm : m' ≤ c₁ * n * m)
        (newProfile : Profile n m')
        (L' : LinearOrder (Fin m'))
        (bordaPath : Fin (k + 1) → RankingVotes n m'),
        is_path_stable_general_vr newProfile (BordaVoting.unweightedBordaVoting L') bordaPath GroupTopBottomRDynamic := by
  use 3
  intro k n m (h_is_ne_n) (h_is_ne_m) h_odd_n
  intro P Lm pPath
  intro hstable_upv
  let c :=  2 * n * m + 1
  use c
  have h_c_ne_zero : NeZero c :=  by simp [c, NeZero.mk]
  letI :=  h_c_ne_zero
  use h_c_ne_zero
  use (by 
        simp [c]
        simp only [Nat.mul_assoc, Nat.succ_mul  2, Nat.add_mul]
        simp
        constructor;
        exact Nat.lt_of_succ_le (h_is_ne_n.one_le)
        exact Nat.lt_of_succ_le (h_is_ne_m.one_le))
  have h_c_gt_m : m < c:= by
      simp [c]
      nth_rw 1 [← Nat.one_mul m]
      apply Nat.mul_le_mul_right m
      have hs := h_is_ne_n.ne
      omega

  use (profilePadding P c h_c_ne_zero h_c_gt_m)
  let L' : LinearOrder (Fin c) := Lm.extend h_c_gt_m


-- theorem uw_borda_path_imp_uw_plurality_path:
--   ∃ (c₁ d₁ c₂ d₂ : ℕ), 
--     ∀ (k n m : ℕ) [NeZero n] [NeZero m] (hn_is_odd : Odd n) (P : Profile n m) (L : LinearOrder (Fin m)) 
--       (bordaPath : Fin (k + 1) → RankingVotes n m),
--         (hm_nezero : NeZero m') -- Added as a standard explicit variable
--         (hm : m' ≤ c₁ * m ^ d₁)
--         (newProfile : Profile n m')
--         (L' : LinearOrder (Fin m'))
--         (pluralityPath : Fin (k + 1) → CandidateVotes n m'),
--         is_path_stable_general_vr newProfile (PV.unweightedPluralityVoting L') pluralityPath GroupBeneficialAndDirectDynamic := 
-- sorry
