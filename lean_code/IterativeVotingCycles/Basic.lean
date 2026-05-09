import Mathlib.Data.Fin.Basic

variable {n m : ℕ} [NeZero n] [NeZero m]

abbrev Voter (n : ℕ) := Fin n
abbrev Cand (m : ℕ) := Fin m


/-- A ranking is a linear order encoded via a position function -/
structure Ranking (m: ℕ) [NeZero m]  where
  pos : Cand m → Cand m
  bij : Function.Bijective pos


