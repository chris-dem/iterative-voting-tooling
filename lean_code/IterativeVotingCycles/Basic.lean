import Mathlib.Data.Fin.Basic

variable {n m : ℕ} [NeZero n] [NeZero m]

abbrev Voter (n : ℕ) := Fin n
abbrev Cand (m : ℕ) := Fin m


/-- A ranking is a linear order encoded via a position function -/
structure Ranking (m: ℕ) [NeZero m]  where
  pos : Cand m → Cand m
  bij : Function.Bijective pos

abbrev WeightType := ℕ

structure VoterProfile (m : ℕ) [NeZero m] where
  preference : Ranking m


abbrev Profile (n m : ℕ) [NeZero n]  [NeZero m] := Voter n -> VoterProfile m

def prefers (r : Ranking m) (a b : Cand m) : Prop :=
  r.pos a < r.pos b

instance (r : Ranking m) (a b : Cand m) :
    Decidable (prefers r a b) := by
  unfold prefers
  infer_instance

