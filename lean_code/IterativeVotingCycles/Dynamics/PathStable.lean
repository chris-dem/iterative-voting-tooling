
section GroupAction
def isStableState (P: Profile n m) (C: CandW m) (V: VVote n m) : Prop :=
  ∀ V': VVote n m, ¬ (groupbeneficialStep P C V V')

def isCondorcetWinner  (P: Profile n m) (C: CandW m) (V: VVote n m) (c : CandW m)
  : Prop := sorry

end GroupAction
