/** Abstract class of rules. */
abstract class Rule {

  /** The left-hand side (LHS) of the rule. */
  def lhs: Digraph

  /** The right-hand side (LHS) of the rule. */
  def rhs: Digraph

  /** The firing/transition rate of the rule. */
  def rate: Expr

  /** Given a graph 'g', produce the list of LHS and RHS gluings. */
  def apply(g: Digraph): Iterable[(Digraph, Int)]
}

/**
 * NOTE: Applying the rules below will *NOT* perform a rewrite
 * operation corresponding to the rules of the PA model, but will
 * compute the corresponding LHS and RHS gluings thereof!
 */

/**
 * Rule 0: A => A <- B
 *
 * In words: connect a new node to an arbitrary existing node).
 */
object Rule0 extends Rule {

  import Digraph._

  val lhs = node
  val rhs = Digraph(Array(NodeInfo(Set(), false), NodeInfo(Set(0), false)))
  val rate = Var("k", 0)

  def apply(g: Digraph): Iterable[(Digraph, Int)] = {

    // LHS gluings:
    //
    // Simply compute all the gluings of the LHS and 'g' and multiply
    // their multiplicity by -1.
    val lhsGs = for ((h, i) <- lhs glue g) yield (h, -i)

    // RHS gluings:
    //
    // First compute all the gluings of the RHS and 'g' then apply the
    // "reversed" rule (removing the image of the A <- B edge) to all
    // the gluings unless this would cause a side-effect (i.e. lead to
    // the deletion of "dangling" edges), in which case the gluing in
    // question is not derivable and must not be considered.
    val rhsGs = for {
      (h, i) <- rhs glue g
      if (h.succs(1).size == 1) && (h.preds(1).size == 0)
    } yield (h - 1, i)

    // Quotient the result to eliminate duplicates and irrelevant
    // gluings.
    quotientByIso(lhsGs ++ rhsGs)
  }

  override def toString = "r0"
}

/**
 * Rule 1: A -> B => A -> B <- C
 *
 * In words: connect a new node to an (arbitrary) existing node with
 * at least one predecessor.
 */
object Rule1 extends Rule {

  import Digraph._

  val lhs = Digraph(Array(NodeInfo(Set(), false), NodeInfo(Set(0), false)))
  val rhs = Digraph(Array(
    NodeInfo(Set(), false), NodeInfo(Set(0), false), NodeInfo(Set(0), false)))
  val rate = Var("k", 1)

  def apply(g: Digraph): Iterable[(Digraph, Int)] = {

    // LHS gluings:
    //
    // Simply compute all the gluings of the LHS and 'g' and multiply
    // their multiplicity by -1.
    val lhsGs = for ((h, i) <- lhs glue g) yield (h, -i)

    // RHS gluings:
    //
    // First compute all the gluings of the RHS and 'g' then apply the
    // "reversed" rule (removing the image of the B <- C edge) to all
    // the gluings unless this would cause a side-effect (i.e. lead to
    // the deletion of "dangling" edges), in which case the gluing is
    // not derivable and must not be considered.
    val rhsGs = for {
      (h, i) <- rhs glue g
      if (h.succs(2).size == 1) && (h.preds(2).size == 0)
    } yield (h - 2, i)

    // Quotient the result to eliminate duplicates and irrelevant
    // gluings.
    quotientByIso(lhsGs ++ rhsGs)
  }

  override def toString = "r1"
}

/**
 * Rule 2: A => {}
 *
 * In words: Remove an (arbitrary) existing node.
 */
object Rule2 extends Rule {

  import Digraph._

  val lhs = node
  val rhs = empty
  val rate = Var("k", 2)

  def apply(g: Digraph): Iterable[(Digraph, Int)] = {

    // LHS gluings:
    //
    // Simply compute all the gluings of the LHS and 'g' and multiply
    // their multiplicity by -1.
    val lhsGs = for ((h, i) <- lhs glue g) yield (h, -i)

    // RHS gluings:
    //
    // There is exactly one RHS gluing, which is 'g' itself.  Note
    // that, this is also the trivial gluing of the empty graph with
    // 'g', and hence it is always irrelevant.  Nevertheless, we need
    // to compute its preimage, in order to cancel out the
    // corresponding (trivial) irrelevant LHS gluing.
    assert(allIso(g glue rhs, (g, 1)))
    val rhsGs = List((g + lhs, 1))

    // Quotient the result to eliminate duplicates and irrelevant
    // gluings.
    quotientByIso(lhsGs ++ rhsGs)
  }

  override def toString = "r2"
}
