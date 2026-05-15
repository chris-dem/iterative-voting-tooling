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
namespace PV
instance instPluralityScoring : ScoringRule (CandidateBallot m) n m L where
  candScore P CW BP c := 
    let w := Finset.univ.filter (fun v => BP v = c)
    let wv := ∑ x ∈ w,  P x
    wv + CW c


def pluralityScore (L: LinearOrder (Fin m)) (P:  VoterW n)
  (C: CandW m) (ballot : BallotProfile (CandidateBallot m) n) (c : Cand m): WeightType :=  
    ScoringRule.candScore (self := instPluralityScoring) L P C ballot c

def pluralityVoting (L: LinearOrder (Fin m)) (P:  VoterW n)
  (C: CandW m) (ballot : BallotProfile (CandidateBallot m) n): Cand m :=  
    VotingRule.winner L 
      (self := instVotingRuleOfScoring (sr := instPluralityScoring))
        P C ballot


def unweightedPluralityScore (L: LinearOrder (Fin m)) 
  (ballot : BallotProfile (CandidateBallot m) n) (c : Cand m) : WeightType :=
    pluralityScore L (fun _ => 1) (fun _ => 0) ballot c

def unweightedPluralityVoting (L: LinearOrder (Fin m)) 
  (ballot : BallotProfile (CandidateBallot m) n)  : Cand m :=
    pluralityVoting L (fun _ => 1) (fun _ => 0) ballot

end PV


section PluralityExample
private def dummyRanking : Ranking 2 :=
  { pos := id, bij := Function.bijective_id }

private def exVoterW : VoterW 3 := fun v => v + 1

-- voter 0 and 1 vote for candidate 0; voter 2 votes for candidate 1
private def exBallots : BallotProfile (CandidateBallot 2) 3
  | ⟨0, _⟩ => ⟨0, by omega⟩
  | ⟨1, _⟩ => ⟨0, by omega⟩
  | ⟨2, _⟩ => ⟨1, by omega⟩

-- No candidate base scores
private def exCandW : Cand 2 → WeightType := fun _ => 0

private abbrev linFin := (inferInstance : LinearOrder (Fin 2))

-- Score for candidate 0: weight(v0) + weight(v1) = 1 + 2 = 3
-- Score for candidate 1: weight(v2)              = 3
#eval PV.pluralityScore linFin exVoterW exCandW exBallots ⟨0, by omega⟩ -- 3
#eval PV.pluralityScore linFin exVoterW exCandW exBallots ⟨1, by omega⟩ -- 3

-- Winners (both candidates tie)
private def my_winners : Finset (Fin 2) := (VotingRule.winners  linFin exVoterW exCandW exBallots).val 
#eval my_winners.sort  (· ≤ ·)
-- Tie-broken winner
#check VotingRule.winner linFin exVoterW exCandW exBallots         -- 0

end PluralityExample


