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
                .maxBy(a => a.swap)
                ._1
            val state = IVNode.create(p, None)
            val win = PluralityVoting().calculateWinner(state)
            assert(
              winner == win,
              s"Winner ${winner} should match the candidate with the most top votes: (${winner}, ${win})"
            )
        }
    }

    def generateWeights =
        for {
            w1 <- Gen.choose(50, 100)
            w2 <- Gen.choose(2, 10)
            w3 <- Gen.choose(2, 10)
            pref1 = POrder.create(Random.shuffle(Vector(1, 2)).appended(0))
            pref2 = POrder.create(Random.shuffle(Vector(0, 1, 2)))
            pref3 = POrder.create(Random.shuffle(Vector(0, 1, 2)))
        } yield (w1, w2, w3, pref1, pref2, pref3)

    property(
      "Candidate with highest score wins. Weights on voters. Assume lex ordering"
    ) = forAll(generateWeights) { (w1, w2, w3, p1, p2, p3) =>
        {
            val state =
                IVNode.create(
                  Vector(p1, p2, p3),
                  Some(Vector(w1, w2, w3), Vector.fill(3)(1))
                )
            val win = PluralityVoting().calculateWinner(state)
            assert(
              win == 0
            )
        }
    }

    property(
      "Candidate with highest score wins. Weights on candidates. Assume lex ordering"
    ) = forAll(generateWeights) { (w1, w2, w3, p1, p2, p3) =>
        {
            val state =
                IVNode.create(
                  Vector(p1, p2, p3),
                  Some(Vector.fill(3)(1), Vector(w1, w2, w3))
                )
            val win = PluralityVoting().calculateWinner(state)
            assert(
              win == 0
            )
        }
    }

    property(
      "For all outputs, weight max match the winner and the two methods match"
    ) = forAll(generateVotingPrefs(10, 5)) { (p) =>
        {
            val state =
                IVNode.create(p, None)
            val ptv = PluralityVoting()
            val win = ptv.calculateWinner(state)
            val win2 = ptv.calculateWinnerWithLogger(state).run
            assert(
              win == win2._2
            )
            assert(
              win2._1.zipWithIndex.max._2 == win,
              s"Current weight vector is ${win2}"
            )

        }
    }
}
