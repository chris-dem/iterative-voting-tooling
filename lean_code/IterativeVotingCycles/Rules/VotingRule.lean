import Mathlib
import Mathlib.Tactic
import IterativeVotingCycles.Basic
import IterativeVotingCycles.Ballots
import IterativeVotingCycles.Misc
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Basic

variable {n m : ℕ} [NeZero n] [NeZero m]

open Fin

structure NonEmptyFinset (α : Type*) where
  val : Finset α
  nonempty : val.Nonempty


structure OrderMapping (m: ℕ) where
  pos : Equiv.Perm (Fin m)


@[simp, grind] def OrderMapping.extend {m : ℕ} (m' : ℕ)
  (hm: m ≤ m')
  (ord: OrderMapping m) :  OrderMapping m' := 
    let pos := fun (x : Fin m') => if h : x < m then (ord.pos.toFun (x.castLT h)).castLE (by omega) else x
    let inv_pos := fun (x : Fin m') => if h : x < m then (ord.pos.invFun (x.castLT h)).castLE (by omega) else x
    ⟨{ 
      toFun := pos,
      invFun := inv_pos,
      left_inv := by 
        simp [Function.LeftInverse]
        intro x
        have h1 := ord.pos.left_inv
        have h2 := ord.pos.right_inv
        by_cases h : x < m
        · simp [pos, inv_pos,h, castLE]
        · simp [pos, inv_pos,h, castLE]
      right_inv := by
        simp [Function.RightInverse]
        intro x
        have h1 := ord.pos.left_inv
        have h2 := ord.pos.right_inv
        by_cases h : x < m
        · simp [pos, inv_pos,h, castLE]
        · simp [pos, inv_pos,h, castLE]
    }⟩ 


@[simp] def OrderFromVector {m : ℕ} [NeZero m] 
    (vc : Vector (Cand m) m) 
    (h : isUnique vc) : OrderMapping m := 

  let vcL := vc.toList
  have hi :=  ((is_unique_vec_n_n_bij_iff  vc).mp h)


  let inv : Vector (Fin m) m := Vector.ofFn (fun x =>
    let indx := vcL.idxOf x
    have hp : indx < m := by
      simp [indx, vcL]
      have h1 := (List.idxOf_lt_length_iff (a := x) (l := vc.toList)).mpr
      simp at h1
      apply h1
      simp [Vector.mem_iff_getElem]
      have hsurj := hi.surjective
      simp [Function.Surjective] at hsurj
      obtain ⟨a, ha⟩ :=  hsurj x
      use a
      use (a.isLt)
      omega
    ⟨indx, hp⟩  
  )
  have inv_isuq : isUnique inv := by
    simp
    intro i j 
    simp [inv,vcL]
    intro hiL
    have hp : i ∈ vc.toList := by
      have hsurj := hi.surjective
      simp [Function.Surjective] at hsurj
      obtain ⟨a, ha⟩ :=  hsurj i 
      simp [Vector.mem_iff_getElem]
      use a
      use (a.isLt)
      omega
    exact (List.idxOf_inj hp).mp hiL

  ⟨{
    toFun := toFunc vc,
    invFun := toFunc <|  inv,
    left_inv := by
      simp [Function.LeftInverse]
      intro x
      simp [inv]
      apply Fin.eq_of_val_eq
      simp [List.idxOf]
      apply (List.findIdx_eq (xs := vcL) (i:=x.val) (by simp [vcL])).mpr
      constructor
      · simp [vcL, Vector.get]
      · intro j hj
        simp [vcL]
        intro hl
        have hinj := hi.injective
        simp [Function.Injective] at hinj
        have hmp := hinj hl
        grind
    right_inv := by
      simp [Function.RightInverse]
      intro x
      set i := inv.get x with hi
      simp [inv, List.idxOf, vcL] at hi
      symm at hi
      have hi_val :=  Fin.val_eq_of_eq hi
      simp at hi_val
      apply (List.findIdx_eq (xs := vcL) (i:= i.val) (by simp [vcL])).mp at hi_val
      have hi_v := hi_val.left
      simp at hi_v
      simp [← hi_v,vcL, Vector.get]
  }⟩ 

/-- Tie-break by choosing the lex-smallest winner (F;in m has a natural linear order). -/
@[simp] def NonEmptyFinset.lexMin {m : ℕ} (ord: OrderMapping m)
    (s : NonEmptyFinset (Cand m)) : Cand m :=
  let perm := s.val.image (fun x => ord.pos x)
  have perm_ne := s.nonempty.image (ord.pos)
  ord.pos.invFun (perm.min' perm_ne)

abbrev CandW  (m : ℕ) [NeZero m]:= Cand m -> WeightType
abbrev VoterW (n : ℕ) [NeZero n]:= Voter n -> WeightType

class VotingRule (Ballot : Type) (n m : ℕ) [NeZero n] [NeZero m] (ord: OrderMapping m) where
  winners : VoterW n -> CandW m -> BallotProfile Ballot n → NonEmptyFinset (Cand m)
  winner (P: VoterW n)  (CW : CandW m) (BP: BallotProfile Ballot n): Cand m :=  (winners P CW BP).lexMin ord

def candRelativePreference {n m : ℕ} [NeZero n] [NeZero m] (P : RankingVotes n m) (ba : Cand m) (bb: Cand m) : ℕ :=
  Finset.univ.filter (fun (p :Voter n) => prefers (P p) ba bb) |> Finset.card

def condorcetWinner (P : RankingVotes n m)  (b: Cand m): Prop :=
  ∀ p : Cand m, p ≠ b → (candRelativePreference P p b) > n/2

def weakCondorcetWinner (P : RankingVotes n m) (b : Cand m):= 
  ∀ p : Cand m, p ≠ b → (candRelativePreference P p b) ≥ n/2

instance (P: RankingVotes n m) (b : Cand m) :
    Decidable (condorcetWinner P b) := by
  unfold condorcetWinner
  infer_instance

def condorcetConsistentVR (f: BallotProfile (RankingBallot  m) n -> Cand m) (P : RankingVotes n m): Prop 
  :=
    ∃ c : Cand m, condorcetWinner P c ↔  f P = c

