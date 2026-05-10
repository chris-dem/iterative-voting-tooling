import IterativeVotingCycles.Basic

abbrev BallotProfile (Ballot: Type) (n: ℕ) [NeZero n]:=
  Voter n -> Ballot

abbrev CandidateBallot (m: ℕ) [NeZero m] := Cand m
abbrev RankingBallot (m : ℕ) [NeZero m] := Ranking m


abbrev CandidateVotes (n m : ℕ) [NeZero n] [NeZero m]:=
  BallotProfile (CandidateBallot m) n

abbrev RankingVotes (n m : ℕ) [NeZero n] [NeZero m]:=
  BallotProfile (RankingBallot m) n
