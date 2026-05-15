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
variable {Ballot : Type} [DecidableEq Ballot]

def isStableState (P: Profile n m) (VR: BallotProfile Ballot n -> Fin m) (V: BallotProfile Ballot n) : Prop :=
  ∀ V', ¬ (groupbeneficialStep P VR V V')



section PluralityStableState

section PVStableExample
private def dummyProfile : Profile 5 3:= toFunc (Vector.ofFn ![
  ⟨ rankingFromVector (Vector.ofFn ![0, 1, 2]) (by proveUnique)⟩,
  ⟨ rankingFromVector (Vector.ofFn ![0, 1, 2]) (by proveUnique)⟩,
  ⟨ rankingFromVector (Vector.ofFn ![0, 1, 2]) (by proveUnique)⟩,
  ⟨ rankingFromVector (Vector.ofFn ![2, 1, 0]) (by proveUnique)⟩,
  ⟨ rankingFromVector (Vector.ofFn ![1, 2, 0]) (by proveUnique)⟩
])

-- voter 0 and 1 vote for candidate 0; voter 2 votes for candidate 1
private def exBallots : BallotProfile (CandidateBallot 3) 5
  | ⟨0, _⟩ => ⟨2, by omega⟩
  | ⟨1, _⟩ => ⟨2, by omega⟩
  | ⟨2, _⟩ => ⟨2, by omega⟩
  | ⟨3, _⟩ => ⟨0, by omega⟩
  | ⟨4, _⟩ => ⟨1, by omega⟩

private abbrev linFin := (inferInstance : LinearOrder (Fin 3))

#eval PV.unweightedPluralityVoting linFin exBallots
#eval PV.unweightedPluralityVoting linFin (toFunc (Vector.ofFn ![
    ⟨2, by omega⟩ 
  , ⟨2, by omega⟩
  , ⟨2, by omega⟩
  , ⟨1, by omega⟩
  , ⟨1, by omega⟩
]))

#eval condorcetWinner (fun (x : Voter 5) => (dummyProfile x).preference) ⟨2, by omega⟩

example: condorcetWinner  (n := 5) (m := 3) (fun (x : Voter 5) => (dummyProfile x).preference) ⟨2, by omega⟩  := by
  native_decide



example: isStableState (dummyProfile) (PV.unweightedPluralityVoting linFin) 
  (exBallots) := by
    rw [isStableState]
    native_decide


end PVStableExample

theorem condorcet_unique (P : RankingVotes n m) (c₁ c₂ : Cand m) 
    (h₁ : condorcetWinner P c₁) (h₂ : condorcetWinner P c₂) : c₁ = c₂ := by
  sorry

theorem unweighted_pv_condorcet_iff_stable (P : Profile n m) (L : LinearOrder (Cand m)) :
    ∀ c : Cand m, 
      condorcetWinner (fun v => (P v).preference) c ↔ 
      (∃ VP, isStableState P (PV.unweightedPluralityVoting L) VP) ∧ 
            (∀ VP : CandidateVotes n m, isStableState P (PV.unweightedPluralityVoting L) VP -> 
              PV.unweightedPluralityVoting L VP = c) := by
              intro c
              constructor
              intro hp
              simp [condorcetWinner,candRelativePreference, VoterProfile.preference,prefers ] at hp
              let vp : CandidateVotes n m := toFunc (Vector.replicate n c)
              have hvpF : ∀ v, vp v = c := by
                intro v
                simp [vp, toFunc]
                apply Vector.getElem_replicate (v.isLt)
              constructor
              use vp
              rw [isStableState]
              intro V'
              simp [groupbeneficialStep, groupbeneficialStepWith]
              intro A hAE hnnA
              obtain ⟨y, hAE⟩ := hAE
              use y
              have hLvp : PV.unweightedPluralityVoting L vp = c := by
                simp [PV.unweightedPluralityVoting, PV.pluralityVoting,
                VotingRule.winner, scoreWinners, ScoringRule.candScore, NonEmptyFinset.lexMin]
                simp [Finset.min'_eq_iff]
                constructor
                intro d
                simp [hvpF]
                by_cases hcd: c = d
                simp [hcd]
                simp [hcd]
                intro b hd
                simp [hvpF] at hd
                by_cases hcb: c = b
                simp [hcb]
                simp [hcb] at hd
                have hne := Finset.univ_nonempty (α := Voter n)
                simp [hd] at hne
              rw [hLvp]

              constructor
              exact hAE
              by_cases hVnew : PV.unweightedPluralityVoting L V' = c
              simp [hVnew, prefers]
              intro hpf
              rcases m with _ | _ | mq
              -- Zero
              exact absurd rfl (NeZero.ne 0)
              -- One
              have hO1 : ∀ VP:  (CandidateVotes n 1), PV.unweightedPluralityVoting L VP  = c := by
                intro V
                have hpQ1:= Fintype.domain_singleton_all_same (PV.unweightedPluralityVoting L) (by decide) vp V'
                rw [← hpQ1, hLvp] at hVnew
                exact absurd rfl hVnew
              have hpp := hO1 V'
              exact absurd hpp hVnew 
              -- 2 <=
              have hn1: ∃ p : Cand (mq + 2),  p ≠ c ∧ PV.unweightedPluralityVoting L V' = p := by
                have had2 : ∃ q, PV.unweightedPluralityVoting L V'  = q := by
                  refine ⟨ PV.unweightedPluralityVoting L V', rfl ⟩ 
                obtain ⟨q, hqE⟩ := had2
                use q
                constructor
                rw [hqE] at hVnew
                exact hVnew
                exact hqE
              obtain ⟨ q, hq, hnn⟩ := hn1
              have hqQ := hp q hq
              have hAllEqC : ∀ v,  ((¬ v = c) →  PV.unweightedPluralityScore L vp v = 0)
                  ∧ ((v = c) →  PV.unweightedPluralityScore L vp v = n) := by
                    intro v
                    constructor
                    intro h
                    simp [PV.unweightedPluralityScore,PV.pluralityScore, ScoringRule.candScore]
                    intro x
                    intro hmm2
                    simp [vp, toFunc, Vector.get] at hmm2
                    symm at hmm2
                    exact h hmm2
                    intro h
                    simp [PV.unweightedPluralityScore,PV.pluralityScore, ScoringRule.candScore
                    ,hvpF]
                    symm at h
                    simp [h]
              have hAllEqCq : PV.unweightedPluralityScore L vp q = 0 := by
                have h1 := hAllEqC q
                simp [h1.left hq]
              have hAllEqCc : PV.unweightedPluralityScore L vp c = n := by
                have h1 := hAllEqC c
                simp [h1.right]

              have hPVV'c : PV.unweightedPluralityScore L V' c ≤ PV.unweightedPluralityScore L V' q 
                := by
                  simp [PV.unweightedPluralityVoting, PV.pluralityVoting, VotingRule.winner,
                  scoreWinners,NonEmptyFinset.lexMin, ScoringRule.candScore, Finset.min'_eq_iff] 
                    at hnn
                  simp [PV.unweightedPluralityScore, PV.pluralityScore, ScoringRule.candScore]
                  exact hnn.left c
              have hV'cScore : PV.unweightedPluralityScore L V' c = n - A.card  := by
                simp [PV.unweightedPluralityScore, PV.pluralityScore, ScoringRule.candScore]
                rw [← Finset.filter_union_filter_neg_eq (fun v => v ∈ A) ({v | V' v = c})]
                rw [Finset.card_union_of_disjoint (s:= {v ∈ {v | V' v = c} | v ∈ A}) 
                          (t := {v ∈ {v | V' v = c} | v ∉ A})]
                rw [Finset.filter_filter, Finset.filter_filter]
                have  hinA : ¬ (Finset.univ.filter (fun a => V' a = c ∧ a ∈ A)).Nonempty  := by
                  simp
                  intro x hx
                  have hb := (hnnA x).mp
                  by_contra hneg
                  have h1b := hb hneg
                  rw [ ← hvpF x] at hx
                  symm at hx
                  exact absurd hx h1b
                rw [Finset.not_nonempty_iff_eq_empty] at hinA
                rw [hinA, Finset.card_empty,zero_add]
                have  hinA2 : (Finset.univ.filter (fun a => V' a = c ∧ a ∉ A)) = (Finset.univ.filter (fun a => a ∉ A))  := by
                  ext g
                  constructor
                  intro hgg
                  simp at  hgg
                  simp
                  exact hgg.right
                  intro hgg
                  simp at  hgg
                  simp
                  constructor
                  apply (hnnA g).not.mp at hgg
                  simp at hgg
                  rw [← hgg]
                  exact hvpF g
                  exact hgg
                have h := Finset.card_compl A
                simp at h
                rw [← h, hinA2]
                rw [show ({a | a ∉ A} : Finset (Fin n)) = Aᶜ by
                  ext a <;> simp] 
                





                -- apply congrArg Finset.card  at hinA
                -- rw [hinA]



                sorry


end PluralityStableState

section PluralityBordaTheorem
end PluralityBordaTheorem
