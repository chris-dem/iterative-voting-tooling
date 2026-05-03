package iv

case class IVNode(
    voter_preferences: Vector[POrder],
    weightsV: Vector[Float],
    weightsC: Vector[Float]
) {
    def nVoters = weightsV.length
    def nCandidates = weightsC.length
}

object IVNode {
    def create(
        votingPrefs: Vector[POrder],
        weights: Option[(Vector[Float], Vector[Float])]
    ): IVNode =
        val nVoters = votingPrefs.length
        val nCandidates = votingPrefs(0).prefToVoter.length
        require(
          votingPrefs.forall(_.prefToVoter.length == nCandidates),
          "Number of candidates should be consisent"
        )
        weights.match {
            case Some((wV, wC)) =>
                require(wV.length == nVoters, "All voters should have a weight")
                require(
                  wC.length == nCandidates,
                  "All candidates should have a score"
                )
                IVNode(votingPrefs, wV, wC)
            case None =>
                IVNode(
                  votingPrefs,
                  Vector.fill(nVoters)(1),
                  Vector.fill(nCandidates)(1)
                )
        }
}
