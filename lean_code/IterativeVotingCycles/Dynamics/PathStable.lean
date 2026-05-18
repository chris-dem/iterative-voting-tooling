import Mathlib.Tactic
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


-- set_option trace.Meta.synthInstance true

theorem unweighted_pv_condorcet_iff_stable (P : Profile n m) (L : LinearOrder (Cand m)) :
    ∀ c : Cand m, 
      condorcetWinner (fun v => (P v).preference) c ↔ 
      (∃ VP, isStableState P (PV.unweightedPluralityVoting L) VP) ∧ 
            (∀ VP : CandidateVotes n m, isStableState P (PV.unweightedPluralityVoting L) VP -> 
              PV.unweightedPluralityVoting L VP = c) := by
              intro c
              constructor
              intro hp
              simp [condorcetWinner,candRelativePreference, VoterProfile.preference ] at hp
              let vp : CandidateVotes n m := toFunc (Vector.replicate n c)
              have hvpF : ∀ v, vp v = c := by
                intro v
                simp [vp, toFunc]
                apply Vector.getElem_replicate (v.isLt)
              constructor
              use vp
              rw [isStableState]
              intro V'
              by_contra hCContra
              simp [groupbeneficialStep] at hCContra
              obtain ⟨hAE, hnnA⟩  := hCContra
              obtain ⟨y, hAE⟩ := hAE
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
              
              rcases m with _ | _ | mq
              -- Zero
              exact absurd rfl (NeZero.ne 0)
              -- One
              have hO1 : ∀ VP:  (CandidateVotes n 1), PV.unweightedPluralityVoting L VP  = c := by
                intro V
                have hpQ1:= Fintype.domain_singleton_all_same (PV.unweightedPluralityVoting L) (by decide) vp V
                rw [hpQ1] at hLvp
                exact hLvp
              have hpp := hO1 V'
              have hnnAA2 := hnnA y hAE
              rw [hpp, hO1] at hnnAA2
              simp [prefers] at hnnAA2
              -- 2 <=
              by_cases hVnew : PV.unweightedPluralityVoting L V' = c
              have hnbb := hnnA y hAE
              simp [hLvp,hVnew,prefers]  at hnbb
              have hn1: ∃ p : Cand (mq + 2),  p ≠ c ∧ PV.unweightedPluralityVoting L V' = p := by
                have had2 : ∃ q, PV.unweightedPluralityVoting L V'  = q := by
                  refine ⟨ PV.unweightedPluralityVoting L V', rfl ⟩ 
                obtain ⟨q, hqE⟩ := had2
                use q
                constructor
                intro hmw
                have hwA := hnnA y hAE
                rw [hqE, hLvp, hmw] at hwA
                simp [prefers] at hwA
                exact hqE
              obtain  ⟨q, hq, hnn⟩ := hn1
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
              set A :=  deviators vp V'
              have hV'cScore : PV.unweightedPluralityScore L V' c = n - A.card  := by
                simp [PV.unweightedPluralityScore, PV.pluralityScore, ScoringRule.candScore]
                rw [← Finset.filter_union_filter_not_eq (fun v => v ∈ A) ({v | V' v = c})]
                rw [Finset.card_union_of_disjoint (s:= {v ∈ {v | V' v = c} | v ∈ A}) 
                          (t := {v ∈ {v | V' v = c} | v ∉ A}) (by 
                          rw [Finset.disjoint_iff_inter_eq_empty]
                          ext v
                          simp
                          intro hvc hva hvcd
                          exact hva
                          )]
                rw [Finset.filter_filter, Finset.filter_filter]
                have  hinA : ¬ (Finset.univ.filter (fun a => V' a = c ∧ a ∈ A)).Nonempty  := by
                  simp
                  intro x hx
                  by_contra hneg
                  have hb := hnnA x hneg
                  simp [A, deviators] at  hneg
                  rw [← hvpF x] at hx
                  symm at hx
                  exact absurd hx hneg
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
                  simp [A, deviators] at hgg
                  rw [hvpF g] at hgg
                  symm at hgg
                  exact hgg
                  exact hgg
                have h := Finset.card_compl A
                simp at h
                rw [← h, hinA2]
                rw [show ({a | a ∉ A} : Finset (Fin n)) = Aᶜ by
                  ext a <;> simp] 
              have hV'qScore: PV.unweightedPluralityScore L V' q ≤ A.card := by
                simp [PV.unweightedPluralityScore, PV.pluralityScore, ScoringRule.candScore]
                have hSubVAll : Finset.univ.filter (fun v => V' v = q) ⊆  Finset.univ.filter (fun v => v ∈ A) := by
                  intro v hv
                  simp
                  simp at hv
                  by_contra hpbl
                  simp [A,deviators] at hpbl
                  rw [hvpF v, hv] at hpbl
                  symm at hpbl
                  exact absurd hpbl hq
                apply Finset.card_le_card at hSubVAll
                simpa using hSubVAll

              have hASt: A ⊆ Finset.univ.filter (fun v => prefers (P v).preference c q) := by
                intro a ha
                apply hnnA at ha
                simp
                rw [hLvp, hnn] at ha
                exact ha
              have hother (v :Voter n): (P v).preference.pos q ≤ (P v).preference.pos c →  (P v).preference.pos q < (P v).preference.pos c := by
                intro hqm
                apply Fin.lt_or_eq_of_le at hqm
                rcases hqm with  hqmL | hqmR
                exact hqmL
                have hmBij := (P v).preference.bij.injective hqmR
                exact absurd hmBij hq
              have FSAnti : (Finset.univ.filter (fun v => prefers (P v).preference c q))ᶜ = (Finset.univ.filter (fun v => prefers (P v).preference q c)) := by
                  ext v
                  constructor
                  intro hvl
                  simp [prefers]
                  simp [prefers] at hvl
                  apply hother v at hvl
                  exact hvl
                  intro hvr
                  simp [prefers]
                  simp [prefers] at hvr
                  apply Fin.le_of_lt at hvr
                  exact hvr
              have hSComp : (Finset.univ.filter (fun v => prefers (P v).preference c q)).card ≤ n / 2 := by
                rw [← FSAnti, Finset.card_compl, Fintype.card_fin] at hqQ
                omega

              have hPVV'c : PV.unweightedPluralityScore L V' c ≤ PV.unweightedPluralityScore L V' q 
                := by
                  simp [PV.unweightedPluralityVoting, PV.pluralityVoting, VotingRule.winner,
                  scoreWinners,NonEmptyFinset.lexMin, ScoringRule.candScore, Finset.min'_eq_iff] 
                    at hnn
                  simp [PV.unweightedPluralityScore, PV.pluralityScore, ScoringRule.candScore]
                  exact hnn.left c
              rw [Nat.le_iff_lt_or_eq] at hPVV'c
              rcases hPVV'c with hPvvL | hPvvR
              have  hnO2:  n / 2  <  A.card  := by
                rw [hV'cScore] at hPvvL
                have hJoinEqs := Nat.le_trans hPvvL hV'qScore
                simp at hJoinEqs
                have h := (Nat.div_le_iff_le_mul (k := 2) (x := n) (y := A.card) (by decide)).mpr
                simp at h
                omega
              have hLTA := (Nat.le_trans (Finset.card_le_card hASt) hSComp)
              exact absurd hLTA (Nat.not_le.mpr hnO2)
              by_cases hEvenN : Even n
              apply Even.exists_add_self at hEvenN
              obtain ⟨r , hr⟩ := hEvenN
              have hSCompEvenFix : (Finset.univ.filter (fun v => prefers (P v).preference c q)).card ≤ n / 2 -1 := by
                rw [← FSAnti, Finset.card_compl, Fintype.card_fin] at hqQ
                have twt: n /2  + 1 ≤ n - (Finset.univ.filter (fun v => prefers (P v).preference c q)).card  := by omega
                have twt2: (Finset.univ.filter (fun v => prefers (P v).preference c q)).card ≤ n - n/2 - 1  := by omega
                omega
              have hLTA := (Nat.le_trans (Finset.card_le_card hASt) hSCompEvenFix)
              rw [hV'cScore] at hPvvR
              rw [← hPvvR] at hV'qScore
              have hF := Nat.add_le_add_right  hV'qScore A.card
              have hM2F := Nat.mul_le_mul_left  2 hLTA
              simp at hF
              rw [← Nat.two_mul] at hF
              have hFF := Nat.le_trans hF hM2F
              simp [Nat.mul_sub, hr, ← mul_two, mul_comm] at hFF
              have h' : r - 1 < r := by
                have hNeZerio := NeZero.one_le (n := n)  
                omega
              exact absurd hFF (by omega)
              have hOddN  := (Nat.even_or_odd n).resolve_left hEvenN
              obtain ⟨r, hr⟩  :=  Odd.exists_bit1 hOddN
              simp [hr] at hSComp
              have hSComp : (Finset.univ.filter (fun v => prefers (P v).preference c q)).card ≤ r := by omega
              have hLTA := (Nat.le_trans (Finset.card_le_card hASt) hSComp)
              rw [← hPvvR, hV'cScore] at hV'qScore
              have hF := Nat.add_le_add_right  hV'qScore A.card
              simp at hF
              have hM2F := Nat.mul_le_mul_left  2 hLTA
              rw [← two_mul] at hF
              apply Nat.le_trans hF at hM2F
              rw [hr]  at hM2F
              exact absurd hM2F (by omega)










#reduce (∀ P, ∀ L, ∀ c : Cand m, 
      condorcetWinner (fun v => (P v).preference) c ↔ 
      (∃ VP, isStableState P (PV.unweightedPluralityVoting L) VP) ∧ 
            (∀ VP : CandidateVotes n m, isStableState P (PV.unweightedPluralityVoting L) VP -> 
              PV.unweightedPluralityVoting L VP = c))

end PluralityStableState

section PluralityBordaTheorem
end PluralityBordaTheorem
