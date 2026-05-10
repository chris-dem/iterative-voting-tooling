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
    let wv := ∑ x ∈ w,  (P x).weight
    wv + CW c


def pluralityScore (L: LinearOrder (Fin m)) (P:  Profile n m)
  (C: CandW m) (ballot : BallotProfile (CandidateBallot m) n) (c : Cand m): WeightType :=  
    ScoringRule.candScore (self := instPluralityScoring) L P C ballot c

def pluralityVoting (L: LinearOrder (Fin m)) (P:  Profile n m)
  (C: CandW m) (ballot : BallotProfile (CandidateBallot m) n): Cand m :=  
    VotingRule.winner L 
      (self := instVotingRuleOfScoring (sr := instPluralityScoring))
        P C ballot


end PV

section PluralityExample


private def dummyRanking : Ranking 2 :=
  { pos := id, bij := Function.bijective_id }

-- 3 voters, 2 candidates
private def exProfile : Profile 3 2 := fun v => {
  preference := dummyRanking
  weight     := v.val + 1  -- voter 0 → weight 1, voter 1 → weight 2, voter 2 → weight 3
}

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
#eval PV.pluralityScore linFin exProfile exCandW exBallots ⟨0, by omega⟩ -- 3
#eval PV.pluralityScore linFin exProfile exCandW exBallots ⟨1, by omega⟩ -- 3

-- Winners (both candidates tie)
private def my_winners : Finset (Fin 2) := (VotingRule.winners  linFin exProfile exCandW exBallots).val 
#eval my_winners.sort  (· ≤ ·)
-- Tie-broken winner
#check VotingRule.winner linFin exProfile exCandW exBallots         -- 0

end PluralityExample


