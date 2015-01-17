import scala.collection.mutable.ArrayBuffer

/** A mutable map from isomorphism classes of graphs to variable names. */
class VarMap private (private val _keys: ArrayBuffer[Digraph]) {

  /** The number of entries in this map. */
  def size: Int = _keys.size

  /** The keys of this map. */
  def keys: Seq[Digraph] = _keys

  /**
   * Lookup the variable name associated with the class '[g]' to
   * which 'g' belongs, or extend the map with a new variable name if
   * no such class exists.
   */
  def apply(g: Digraph): (Var, Boolean) =
    (0 until size).find(i => g ~ _keys(i)) match {
      case Some(i) => (mkName(i), false)
      case None    =>
        val i = size
        _keys += g
        (mkName(i), true)
    }

  private def mkName(i: Int): Var = Var("x", i)
}

object VarMap {
  def empty = new VarMap(new ArrayBuffer[Digraph])
}
