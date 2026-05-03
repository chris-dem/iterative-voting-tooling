package iv

import java.util.Comparator

final case class POrder(prefToVoter: Vector[Int]) extends Ordering[Int] {
    def compare(a: Int, b: Int): Int = {
        val n = prefToVoter.length
        require(a >= 0 && b >= 0, "Candidates have positive values")
        require(
          a < n && b < n,
          s"Candidates can have maximum value of ${n - 1}"
        )
        (prefToVoter.find(_ == a).get - prefToVoter.find(_ == b).get).sign
    }
}

object POrder {
    def create(vot_ord: Iterable[Int]): POrder = {
        val ord = vot_ord.toVector
        val n = ord.length
        require(
          n > 0 &&
              ord.forall(x => 0 <= x && x < n) && ord.zipWithIndex.foldLeft(0)(
                (acc, b) => acc ^ b(0) ^ b(1)
              ) == 0,
          "Invalid candidates"
        )

        POrder(ord)
    }
}
