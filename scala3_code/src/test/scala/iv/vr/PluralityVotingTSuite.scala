package iv.vr

import iv.IVNode
import iv.POrder
import iv.vr.VotingRule
import munit.FunSuite
import munit.ScalaCheckSuite
import org.scalacheck.Gen
import org.scalacheck.Prop.forAll
import org.scalacheck.Prop.all
import scala.util.Random
import scala.util.Try

class PluralityVotingTSuite extends FunSuite with ScalaCheckSuite {
    test("Simple Plurality scenario") {
        val prefs = Vector(
          POrder.create(Vector(0, 1, 2)),
          POrder.create(Vector(0, 2, 1)),
          POrder.create(Vector(1, 2, 0)),
          POrder.create(Vector(2, 0, 1))
        )

        val state = IVNode.create(prefs, None)
        val winner = PluralityVoting().calculateWinner(state)
        assert(winner == 1, "Winner should be the one with the most votes")
    }

    test("Simple Plurality scenario, with lex") {
        val prefs = Vector(
          POrder.create(Vector(0, 1, 2)),
          POrder.create(Vector(1, 2, 0)),
          POrder.create(Vector(2, 0, 1))
        )

        val state = IVNode.create(prefs, None)
        val winner = PluralityVoting().calculateWinner(state)
        assert(winner == 2, "Winner should be the one with the most votes")
    }

    def generateVotingPrefs(nCand: Int, nVoters: Int): Gen[Vector[POrder]] = {
        Gen.listOfN(nCand, Gen.const((0 until nCand).toVector))
            .map(s =>
                s.map(_ => POrder.create(Random.shuffle(0 until nCand)))
                    .toVector
            )
    }

    property(
      "Voters with the most singular votes must win. Assume lex ordering"
    ) = forAll(generateVotingPrefs(3, 8)) { (p) =>
        {
            val winner = p
                .map(_.prefToVoter.last)
                .groupMapReduce(x => x)(_ => 1)(_ + _)
                .maxBy(a => (a._2, a._1))
                ._1
            val state = IVNode.create(p, None)
            val win = PluralityVoting().calculateWinner(state)
            assert(
              winner == win,
              s"Winner ${winner} should match the candidate with the most top votes: (${winner}, ${win})"
            )
        }
    }
}
