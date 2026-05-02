package iv

/** [TODO:description]
  *
  * @param voters_order
  *   Order of voters
  */
final case class POrder(val voterPref: Vector[Int])

object POrder {

    def create(vot_ord: Iterable[Int]): POrder = {
        val ord = vot_ord.toVector
        val n = ord.length
        require(
          n > 0 &&
          ord.forall(x => 0 <= x && x < n) && ord.zipWithIndex.foldLeft(0)((acc, b) => acc ^ b(0) ^ b(1)) == 0,
          "Invalid candidates"
        )
        POrder(ord)
    }

}
