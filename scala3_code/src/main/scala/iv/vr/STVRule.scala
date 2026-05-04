package iv.vr

import scala.collection.mutable.ArrayBuffer
import iv.IVNode
import iv.vr.VotingRule
import cats.data.Writer
import cats.instances.vector._
import cats.implicits._
import cats.syntax.writer._
import cats.syntax.applicative._

case class LoggedItem(
    loserId: Int,
    candidateScores: Map[Int, Float],
    votes: Vector[(Int, Int)]
)

case class AccType(
    elimSet: Vector[Boolean],
    votPrefs: Vector[Vector[Int]]
)

type Logged[T] = Writer[Vector[LoggedItem], T]

final class STVoting extends VotingRule {
    type L = Vector[LoggedItem]
    def calculateWinnerWithLogger(
        state: IVNode
    ): Logged[Int] =
        (1 until state.nCandidates)
            .foldLeft(
              AccType(
                Vector.fill(state.nCandidates)(false),
                state._1
                    .map(_.prefToVoter)
              )
                  .pure[Logged]
            )((acc, i) =>
                acc.flatMap(currentState =>
                    val AccType(bools, prefs) = currentState
                    val w = prefs
                        .map(_.last)
                        .zip(state.weightsV)
                        .filter(x => !bools(x._1))
                        .groupMapReduce(x => x._1)(x => x._2)(_ + _)
                        .map((c, w) => (c, state.weightsC(c) + w))
                    val lostC = w.minBy(_.swap)._1
                    val newBool = bools.updated(lostC, true)
                    val newPrefs =
                        prefs.map(c =>
                            c.reverse.dropWhile(p => bools(p)).reverse
                        )
                    Writer(
                      Vector(
                        LoggedItem(
                          lostC,
                          w,
                          prefs.last.zip(newPrefs.map(_.last)).toVector
                        )
                      ),
                      AccType(newBool, newPrefs)
                    )
                )
            )
            .map(acc => {
                acc._1.zipWithIndex.find(!_._1).get._2
            })

    override def calculateWinner(state: IVNode): Int = {
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
