package iterative_voting
case class IVNode[C](voter_preferences: List[C])
case class IVWNode[C](voter_preferences: List[C], weights: List[Float] )

object IVNode {
  def create(v_p: List[Int]): Unit  = ???
}
