package iv.vr
import iv.IVNode

trait VotingRule {
    def calculateWinner(state: IVNode): Int
}

