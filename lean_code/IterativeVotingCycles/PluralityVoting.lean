import Mathlib
import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Fin

open Classical
open BigOperators


variable {n m : ℕ} [NeZero n] [NeZero m]

abbrev Voter (n : ℕ) := Fin n
abbrev Cand (m : ℕ) := Fin m


/-- A ranking is a linear order encoded via a position function -/
structure Ranking (m: ℕ) [NeZero m]  where
  pos : Cand m → Cand m
  bij : Function.Bijective pos


abbrev Profile (n m : ℕ) [NeZero n] [NeZero m] := Voter n → Cand m

def prefers (r : Ranking m) (a b : Cand m) : Prop :=
  r.pos a < r.pos b


/-- Count how many voters rank c at the top (position = 0) -/
def pluralityScore (P : Profile n m) (c : Cand m) : ℕ :=
  (Finset.univ.filter (fun v => (P v) = c)).card

/-- c is a plurality winner if it maximizes the score -/
def isWinner (P : Profile n m) (c : Cand m) : Prop :=
  ∀ d : Cand m, pluralityScore P d ≤ pluralityScore P c

/-- Set of winners (to avoid tie-breaking issues) -/
noncomputable def winners  (P : Profile n m) : Finset (Cand m) :=
  Finset.univ.filter (fun c => isWinner P c)

/-- A voter performs a beneficial deviation if they change their ranking
    and strictly prefer the new winner to the old one -/
def beneficialStep (P P' : Profile n m) : Prop :=
  ∃ v : Voter n,
    (∀ u ≠ v, P u = P' u) ∧
    (∃ w w' : Cand m,
        w ∈ winners P ∧
        w' ∈ winners P' ∧
        prefers (P v) w' w)

def next {k : ℕ} (i : Fin k) : Fin k :=
  ⟨(i.val + 1) % k, Nat.mod_lt _ i.pos⟩

def isCycle (k : ℕ) (f : Fin k → Profile n m) : Prop :=
  ∀ i : Fin k, beneficialStep (f i) (f (next i))

def existsCycle : Prop :=
  ∃ (k : ℕ) (_ : k ≥ 2) (f : Fin k → Profile n m), isCycle k f
