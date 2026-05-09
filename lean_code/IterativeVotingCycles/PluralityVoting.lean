import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Algebra.BigOperators.Fin
import IterativeVotingCycles.MiscVotingLemmas

open Classical
open BigOperators


variable {n m : ℕ} [NeZero n] [NeZero m]

/-- Count how many voters rank c at the top (position = 0) -/
def pluralityScore (P : Profile n m) (C: CandW m) (V : VVote n m) (c : Cand m) : WeightType :=
  let voterSet := (Finset.univ.filter (fun v => (V v) = c))
  Finset.sum voterSet (fun v => (P v).weight) + C c

/-- c is a plurality winner if it maximizes the score -/
def isWinner (P : Profile n m) (C: CandW m) (V: VVote n m) (c : Cand m) : Prop :=
  ∀ d : Cand m, pluralityScore P C V d ≤ pluralityScore P C V c

instance (P : Profile n m) (C : CandW m) (V : VVote n m) (c : Cand m) :
    Decidable (isWinner P C V c) :=
  Fintype.decidableForallFintype

/-- Set of winners (to avoid tie-breaking issues) -/
def winners (P : Profile n m) (C : CandW m) (V : VVote n m) :
    Finset (Cand m) :=
  Finset.univ.filter (fun c => isWinner P C V c)
 


lemma winners_nonempty (P : Profile n m) (C : CandW m) (V : VVote n m) : 
  (winners P C V).Nonempty := by
    rw [winners]
    let s : Finset (Fin m) := Finset.univ
    obtain ⟨c, h_mem, h_max⟩ := Finset.exists_max_image s (fun c => pluralityScore P C V c) Finset.univ_nonempty
    use c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, isWinner]
    intro p
    apply h_max
    exact Finset.mem_univ p

def lexWinner (P : Profile n m) (C : CandW m) (V : VVote n m):
    Cand m := by
  let wins :=  winners P C V
  have p := winners_nonempty P C V
  exact wins.min' p



/-- A voter performs a beneficial deviation if they change their ranking
    and strictly prefer the new winner to the old one -/
def beneficialStep (P: Profile n m) (C: CandW m) (V V' : VVote n m) : Prop :=
  ∃ v : Voter n,
    (∀ u ≠ v, V u = V' u) ∧
    (∃ w w' : Cand m,
        w = lexWinner P C V ∧
        w' = lexWinner P C V' ∧
        prefers (P v).preference w w')

instance (P : Profile n m) (C : CandW m) (V V' : VVote n m) :
    Decidable (beneficialStep P C V V') := by
  unfold beneficialStep prefers
  infer_instance


def toFunc {α: Type} {k : ℕ} (vc: Vector α k) : Fin k -> α :=  Vector.get vc

def isUnique {α : Type}{n : ℕ} (vc: Vector α n): Prop := 
  ∀ i j : Fin n, Vector.get vc i =  Vector.get vc j → i = j

theorem is_unique_vec_n_n_bij_iff {n : ℕ} (vc: Vector (Fin n) n):
    isUnique (vc) ↔ Function.Bijective (toFunc vc) := by
      constructor
      intro hv
      rw [isUnique] at hv
      have hp : Function.Injective (toFunc vc) :=  by
        intro x y heq 
        simp [toFunc, Vector.get] at heq
        apply hv x y at heq
        exact heq

      apply Finite.injective_iff_bijective.mp at hp
      exact hp
      intro foo
      rw [isUnique, ← Function.Injective]
      exact foo.left

def rankingFromVector {m : ℕ} [NeZero m] 
    (vc : Vector (Cand m) m) 
    (h : isUnique vc) : Ranking m where
  pos := toFunc vc
  bij := is_unique_vec_n_n_bij_iff vc |>.mp h

syntax "proveUnique" : tactic

macro_rules
  | `(tactic| proveUnique) =>
    `(tactic| intro i j h; fin_cases i <;> fin_cases j <;> simp_all [Vector.get])



section SingleAction
def next {k : ℕ} (i : Fin k) (h: 1 < k): Fin k := 
    let op : Fin k := ⟨1, h⟩ 
    i.add op

def isCycle (k : ℕ) (h : 1 < k) (P : Profile n m)  (C: CandW m) (f: Fin k → VVote n m) : Prop :=
  ∀ i : Fin k, beneficialStep P C (f i) (f (next i h) )


instance  (k  : ℕ) (h : 1< k)(P : Profile n m) (C : CandW m) (f: Fin k ->  VVote n m) :
    Decidable (isCycle k h P C f) := by
  unfold isCycle beneficialStep prefers
  infer_instance



def existsCycle : Prop :=
  ∃ (k : ℕ) (_ : k ≥ 2) (P : Profile n m) (C: CandW m) (f : Fin k → VVote n m),
    isCycle k (by omega) P C f


--- Cycle construction

abbrev VectorPref := Vector Int 4


def voters: Profile 3 4 := toFunc (Vector.ofFn ![
    ⟨rankingFromVector (Vector.ofFn ![0, 1, 3, 2]) (by proveUnique), 1⟩,
    ⟨rankingFromVector (Vector.ofFn ![1, 3, 2, 0]) (by proveUnique), 2⟩,
    ⟨rankingFromVector (Vector.ofFn ![3, 2, 1, 0]) (by proveUnique), 3⟩
  ])

def weights : CandW 4 := toFunc (Vector.ofFn ![0,1,2,3])

def voterCycle: Fin 6 -> VVote 3 4 := toFunc (Vector.ofFn ![
      toFunc (Vector.ofFn ![2 ,1, 0]),
      toFunc (Vector.ofFn ![3 ,1, 0]),
      toFunc (Vector.ofFn ![3 ,2, 0]),
      toFunc (Vector.ofFn ![3 ,2, 1]),
      toFunc (Vector.ofFn ![2 ,2, 1]),
      toFunc (Vector.ofFn ![2 ,1, 1])
  ])

example : isCycle 6 (by omega) voters weights voterCycle := by
  native_decide

end SingleAction

section GroupAction

def groupbeneficialStepWith (P: Profile n m) (C: CandW m) (V V' : VVote n m) (A: Finset (Fin n))
    : Prop :=
    A.Nonempty ∧
    (∀ u ∉ A, V u = V' u) ∧
    (∀ u ∈ A, prefers (P u).preference (lexWinner P C V) (lexWinner P C V'))

instance (P : Profile n m) (C : CandW m) (V V' : VVote n m) (A: Finset (Fin n)):
    Decidable (groupbeneficialStepWith P C V V' A) := by
  unfold groupbeneficialStepWith prefers
  infer_instance

-- Theorem statement
def groupbeneficialStep (P: Profile n m) (C: CandW m) (V V' : VVote n m)
    : Prop :=
  ∃ A : Finset (Fin n),
    groupbeneficialStepWith P C V V' A

instance (P : Profile n m) (C : CandW m) (V V' : VVote n m) :
    Decidable (groupbeneficialStep P C V V') := by
  unfold groupbeneficialStep groupbeneficialStepWith
  infer_instance

def isStableState (P: Profile n m) (C: CandW m) (V: VVote n m) : Prop :=
  ∀ V': VVote n m, ¬ (groupbeneficialStep P C V V')

def isCondorcetWinner  (P: Profile n m) (C: CandW m) (V: VVote n m) (c : CandW m)
  : Prop := sorry

end GroupAction
