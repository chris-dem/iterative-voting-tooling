import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Algebra.BigOperators.Fin

open Classical
open BigOperators

variable {n m : ℕ} [NeZero n] [NeZero m]


abbrev WeightType := ℕ
abbrev Profile (n m : ℕ) [NeZero n] [NeZero m] := Voter n → VoterProfile m
abbrev CandW (m : ℕ) [NeZero m] := Cand m → WeightType
abbrev VVote (n m : ℕ) [NeZero n] [NeZero m] := Voter n → Cand m

def prefers (r : Ranking m) (a b : Cand m) : Prop :=
  r.pos a < r.pos b

instance (r : Ranking m) (a b : Cand m) :
    Decidable (prefers r a b) := by
  unfold prefers
  infer_instance

