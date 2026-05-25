import Mathlib.Data.Fin.Basic

variable {n m : ℕ} [NeZero n] [NeZero m]

abbrev Voter (n : ℕ) := Fin n
abbrev Cand (m : ℕ) := Fin m


/-- A ranking is a linear order encoded via a position function -/
structure Ranking (m: ℕ) [NeZero m]  where
  pos : Cand m → Cand m
  bij : Function.Bijective pos

instance : DecidableEq (Ranking m) := fun r1 r2 =>
  if h : ∀ x : Cand m, r1.pos x = r2.pos x then
    isTrue (by cases r1; cases r2; congr; exact funext h)
  else
    isFalse (fun heq => h (fun x => congrFun (congrArg Ranking.pos heq) x))

abbrev WeightType := ℕ

structure VoterProfile (m : ℕ) [NeZero m] where
  preference : Ranking m


abbrev Profile (n m : ℕ) [NeZero n]  [NeZero m] := Voter n -> VoterProfile m
abbrev VProfile (n m : ℕ) [NeZero n]  [NeZero m] := Voter n -> Ranking m

def prefers (r : Ranking m) (a b : Cand m) : Prop :=
  r.pos a < r.pos b

instance (r : Ranking m) (a b : Cand m) :
    Decidable (prefers r a b) := by
  unfold prefers
  infer_instance

