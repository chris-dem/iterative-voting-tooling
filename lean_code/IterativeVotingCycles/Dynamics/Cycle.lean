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
import IterativeVotingCycles.Rules.Candidate.Plurality
import IterativeVotingCycles.Misc
import IterativeVotingCycles.Dynamics.Step

open Classical
open BigOperators

variable {n m : ℕ} [NeZero n] [NeZero m]
variable {Ballot : Type} [DecidableEq Ballot]


private def next {k : ℕ} (i : Fin k) (h: 1 < k): Fin k := 
    let op : Fin k := ⟨1, h⟩ 
    i.add op

def isSimpleCycle (k : ℕ) (h : 1 < k) 
    (P : Profile n m) (VR: BallotProfile Ballot n -> Fin m) 
    (f: Fin k → BallotProfile Ballot n) : Prop :=
  ∀ i : Fin k, beneficialStep P VR (f i) (f (next i h) )

instance (k  : ℕ) (h : 1< k) (P : Profile n m) (VR: BallotProfile Ballot n -> Fin m)
  (f: Fin k ->  BallotProfile Ballot n) :
    Decidable (isSimpleCycle k h P VR f) := by
  unfold isSimpleCycle beneficialStep prefers
  infer_instance



--d ef existsCycle : Prop :=
--  ∃ (k : ℕ) (_ : k ≥ 2) (P : Profile n m) (C: CandW m) (f : Fin k → VVote n m),
--    isCycle k (by omega) P C f

section PluralityCycles
abbrev VectorPref := Vector Int 4


def voters: Profile 3 4 := toFunc (Vector.ofFn ![
    ⟨rankingFromVector (Vector.ofFn ![0, 1, 3, 2]) (by proveUnique), 1⟩,
    ⟨rankingFromVector (Vector.ofFn ![1, 3, 2, 0]) (by proveUnique), 2⟩,
    ⟨rankingFromVector (Vector.ofFn ![3, 2, 1, 0]) (by proveUnique), 3⟩
  ])

def weights : CandW 4 := toFunc (Vector.ofFn ![0,1,2,3])

def voterCycle: Fin 6 -> CandidateVotes 3 4 := toFunc (Vector.ofFn ![
      toFunc (Vector.ofFn ![2 ,1, 0]),
      toFunc (Vector.ofFn ![3 ,1, 0]),
      toFunc (Vector.ofFn ![3 ,2, 0]),
      toFunc (Vector.ofFn ![3 ,2, 1]),
      toFunc (Vector.ofFn ![2 ,2, 1]),
      toFunc (Vector.ofFn ![2 ,1, 1])
  ])

abbrev linOrder :LinearOrder (Fin n) :=  inferInstance

def calcWinner := PV.pluralityVoting linOrder voters weights

example : isSimpleCycle 6 (by omega) voters calcWinner voterCycle := by
  native_decide

end  PluralityCycles


