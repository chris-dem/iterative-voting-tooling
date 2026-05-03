package iv.vr

import scala.collection.mutable.ArrayBuffer
import iv.IVNode
import iv.vr.VotingRule

final class PluralityVoting extends VotingRule {
    def calculateWinner(state: IVNode): Int = {
        val wSums = state.weightsV
            .zip(state.voter_preferences)
            .foldRight(state.weightsC)((vp, acc) => {
                val (w, pf) = vp
                acc.updated(pf.prefToVoter.last, acc(pf.prefToVoter.last) + w)
            })
        val highest = wSums.max
        wSums.zipWithIndex.findLast(_._1 == highest).get._2
    }

}
