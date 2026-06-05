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

instance instBordaScoring : ScoringRule (RankingBallot m) n m where
  candScore P CW BP c := 
    let wv := ∑ x,  (P x) * ((BP x).pos c + 1) 
    wv + CW c


def bordaScore  (P:  VoterW n)
  (C: CandW m) (ballot : BallotProfile (RankingBallot m) n) (c : Cand m): WeightType :=
    ScoringRule.candScore (self := instBordaScoring) P C ballot c

def bordaVoting (L: OrderMapping m) (P:  VoterW n)
  (C: CandW m) (ballot : BallotProfile (RankingBallot m) n): Cand m :=  
    VotingRule.winner L
      (self := instVotingRuleOfScoring (sr := instBordaScoring))
        P C ballot

def unweightedBordaVoting (L: OrderMapping m)
    (ballot : BallotProfile (RankingBallot m) n) : Cand m :=
    bordaVoting L (fun _ => 1) (fun _ => 1) ballot

def unweightedBordaScore (ballot : BallotProfile (RankingBallot m) n)
    (c : Cand m) : WeightType :=
      bordaScore (fun _ => 1) (fun _ => 1) ballot c

end BordaVoting
