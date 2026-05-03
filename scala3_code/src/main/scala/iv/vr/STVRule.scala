package iv.vr

import scala.collection.mutable.ArrayBuffer
import iv.IVNode
import iv.vr.VotingRule

final class STVoting extends VotingRule {
    def calculateWinner(state: IVNode): Int = {
        var vB = Vector.fill(state.nCandidates)(false)
        var vP = state._1.map(_.prefToVoter)
        for (i <- (1 until state.nCandidates)) {
            val arr = state.weightsC.to(ArrayBuffer)
            vP.zipWithIndex.foreach((p, i) => {
                arr(p.last) += state.weightsV(i)
            })
            val m = arr.min
            val lostCandidate = arr.zipWithIndex.filter(_._1 == m).head._2
            vB = vB.updated(lostCandidate, true)
            vP.map(e => e.reverse.dropWhile(c => vB(c)).reverse)
        }
        vB.zipWithIndex.find(!_._1).get._2
    }

}
