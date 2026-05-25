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
namespace BordaVoting

instance instBordaScoring : ScoringRule (RankingBallot m) n m L where
  candScore P CW BP c := 
    let wv := ∑ x,  (P x) * ((BP x).pos c + 1) 
    wv + CW c


def bordaScore (L: LinearOrder (Fin m)) (P:  VoterW n)
  (C: CandW m) (ballot : BallotProfile (RankingBallot m) n) (c : Cand m): WeightType :=
    ScoringRule.candScore (self := instBordaScoring) L P C ballot c

def bordaVoting (L: LinearOrder (Fin m)) (P:  VoterW n)
  (C: CandW m) (ballot : BallotProfile (RankingBallot m) n): Cand m :=  
    VotingRule.winner L 
      (self := instVotingRuleOfScoring (sr := instBordaScoring))
        P C ballot

end BordaVoting
