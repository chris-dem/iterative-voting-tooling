package iv

import munit.FunSuite
import munit.ScalaCheckSuite
import org.scalacheck.Gen
import org.scalacheck.Prop.forAll
import org.scalacheck.Prop.all
import scala.util.Random
import scala.util.Try

class POrderTSuite extends FunSuite with ScalaCheckSuite {
    def genPerm: Gen[(Int, Seq[Int])] = for {
        n <- Gen.choose(1, 100)
        perm = Random.shuffle((0 until n).toSeq)
    } yield (n, perm)

    test("Sequential order should pass") {
        val ord = POrder.create(0 until 10)
        assert(
          ord.prefToVoter == (0 until 10).toVector,
          "Should not affect the elements"
        )
    }

    property("Should always accept elements within the same list") =
        forAll(genPerm) { (n, pref) =>
            val ord = POrder.create(pref)
            all(
              ord.prefToVoter.length == pref.length,
              pref.zip(ord.prefToVoter).map(_ == _).reduce(_ && _)
            )
        }

    def genPermWithOrder: Gen[(Int, Seq[Int], Int, Int)] = for {
        n <- Gen.choose(10, 100)
        perm = Random.shuffle((0 until n).toSeq)
        i <- Gen.choose(0, n - 2)
        j <- Gen.choose(i + 1, n - 1)
    } yield (n, perm, i, j)

    property("Orders should match between the two vectors") =
        forAll(genPermWithOrder) { (n, pref, i, j) =>
            val ord = POrder.create(pref)
            val comp1 = ord.compare(i, j)
            val comp2 = (
              ord.prefToVoter.find(_ == i),
              ord.prefToVoter.find(_ == j),
              comp1
            ).match {
                case (Some(indI), Some(indJ), p) => {
                    if (p > 0) {
                        assert(
                          indI < indJ,
                          s"Candidate $i and candidate $j  are in positions $indI , $indJ"
                        )

                    } else {
                        assert(
                          indI < indJ,
                          s"Candidate $i and candidate $j  are in positions $indI , $indJ"
                        )
                    }
                    true
                }
                case (_, _, _) => false

            }
        }

    test("Out of range number elements should fail") {
        intercept[IllegalArgumentException](POrder.create(Seq(0, 10)))
    }

    def outOfBound: Gen[(Int, Seq[Int])] = for {
        n <- Gen.choose(5, 50)
        k <- Gen.choose(1, n - 1)
        g <- Gen.pick(k, (0 until n))
        rest <- Gen.pick(n - k, (60 to 250))
        perm = Random.shuffle(g.concat(rest)).toSeq
    } yield (n, perm)

    property("Property out of number elements should fail") =
        forAll(outOfBound) { (n, pref) =>
            Try(POrder.create(pref)).isFailure
        }
    def checkElems(g: List[Int]): Boolean =
        val n = g.length
        g.toSet.size != n
    def withDubs: Gen[Seq[Int]] = for {
        g <- Gen.listOfN(100, Gen.choose(1, 100))
        if checkElems(g)
    } yield g

    override def scalaCheckInitialSeed =
        "mfbgYSkEPjdOC3vWKGE_c4kUU_TjQXNxlnH3_YuyIjP="
    property("Duplicated elements should fail") = forAll(withDubs) { (pref) =>
        {
            Try(POrder.create(pref)).isFailure
        }
    }
}
