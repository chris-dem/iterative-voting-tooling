package iv.vr
import iv.IVNode
import cats.data.Writer

trait VotingRule {
    type L
    def calculateWinnerWithLogger(state: IVNode): Writer[L, Int]
    def calculateWinner(state: IVNode): Int = calculateWinnerWithLogger(
      state
    ).run._2
}
