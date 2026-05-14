import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Algebra.BigOperators.Fin
import IterativeVotingCycles.Basic


open Classical
open BigOperators
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




theorem Fintype.domain_singleton_all_same {α β : Type*} [Fintype β] (f : α → β) (h : Fintype.card β = 1) :
    ∀ x y, f x = f y := by
  -- 1. Any Fintype with card 1 is a Subsingleton
  haveI : Subsingleton β := by
    apply Fintype.card_le_one_iff_subsingleton.mp
    simp [h]

  
  -- 2. In a Subsingleton, all elements are equal
  intro x y
  apply Subsingleton.allEq
