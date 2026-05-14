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
              exact hVnew hpp
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
              rw [hnn] at hpf
              simp [PV.unweightedPluralityVoting, PV.pluralityVoting, VotingRule.winner,
              scoreWinners, NonEmptyFinset.lexMin, ScoringRule.candScore] at hnn
              have hVA: ∀ v, (v ∈ A → V' v = q)  ∧  (v ∉ A → V' v = c) := by
                intro v
                constructor
                intro hp






  
end PluralityStableState

section PluralityBordaTheorem
end PluralityBordaTheorem
