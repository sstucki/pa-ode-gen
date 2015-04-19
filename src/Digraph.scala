import scala.collection.mutable.ArrayBuffer

/** Marked digraphs. */
case class Digraph(val nodes: Array[Digraph.NodeInfo]) {

  import Digraph._

  /** Number of nodes in this graph. */
  val numNodes = nodes.size
  val numEdges = (for (n <- nodes) yield n.succs.size).sum

  /** The node set/range of this graph: { 0 .. n } */
  val nodeRange = 0 until numNodes

  /** Per-node successor lists. */
  def succs(i: NodeId) = nodes(i).succs

  /** Per-node predecessor lists. */
  val preds: Array[Set[NodeId]] = for (i <- nodeRange.toArray) yield {
    for (j <- nodeRange.toSet if succs(j) contains i) yield j
  }

  /** The edges of this graph (as pairs of node IDs). */
  val edges = for (i <- nodeRange; j <- nodes(i).succs) yield (i, j)

  /** Per-node in-degree. */
  def inDegree(i: NodeId): Int = preds(i).size

  /** Per-node out-degree. */
  def outDegree(i: NodeId): Int = succs(i).size

  /**
   * Compute the graph resulting from deleting the node 'i' and all
   * its edges.
   */
  def -(node: NodeId): Digraph = {
    def lift(n: NodeInfo) = NodeInfo(
      n.succs map { i => if (i < node) i else i - 1 }, n.inMark, n.outMark)
    val uNodes = new Array[NodeInfo](numNodes - 1)
    for (i <- 0 until node)              { uNodes(i)     = lift(nodes(i)) }
    for (i <- (node + 1) until numNodes) { uNodes(i - 1) = lift(nodes(i)) }
    Digraph(uNodes)
  }

  /** Compute the disjoint union of this graph and 'that'. */
  def +(that: Digraph): Digraph = {
    val k = this.numNodes
    def lift(n: NodeInfo) =
      NodeInfo(n.succs.map(_ + k), n.inMark, n.outMark)
    val uNodes = new Array[NodeInfo](k + that.numNodes)
    for (i <- this.nodeRange) { uNodes(i)     = this.nodes(i) }
    for (i <- that.nodeRange) { uNodes(i + k) = lift(that.nodes(i)) }
    Digraph(uNodes)
  }

  /** Add a single node to this graph. */
  def +(n: NodeInfo): Digraph = {
    val k = this.numNodes
    val uNodes = new Array[NodeInfo](k + 1)
    for (i <- this.nodeRange) { uNodes(i) = this.nodes(i) }
    uNodes(k) = n
    Digraph(uNodes)
  }

  /** Check whether this graph has cycles. */
  def hasCycles: Boolean = {

    val NotChecked = -1
    val Checking   =  0
    val Checked    =  1

    def checkFromRoot(i: NodeId, checked: Array[Int]): Boolean = {
      val n = nodes(i)
      checked(i) match {
        case Checked    => false
        case Checking   => true
        case NotChecked =>
          checked(i) = Checking
          val cycles = n.succs.exists { i => checkFromRoot(i, checked) }
          checked(i) = Checked
          cycles
      }
    }

    val checked = Array.fill[Int](numNodes)(NotChecked)
    var i = checked.indexOf(NotChecked)
    var cycleFound = false;
    while (i >= 0) {
      cycleFound = checkFromRoot(i, checked)
      if (cycleFound) i = -1 else i = checked.indexOf(NotChecked)
    }
    cycleFound
  }

  /** Check whether this graph is isomorphic to 'that'. */
  def ~(that: Digraph): Boolean = {

    // Find an as-of-yet unmapped source node.
    def findUnmapped(pinj: Array[NodeId]) = pinj.indexOf(-1)

    // Check whether two sets of adjacent nodes match
    def adjNodesMatch(
      is: Set[NodeId], js: Set[NodeId],
      pinj: Array[NodeId]): Option[Array[NodeId]] = {

      if (is.size != js.size) None        // Degrees must agree
      else if (is.isEmpty)    Some(pinj)  // Empty sets match
      else is.collectFirst(Function.unlift { i =>
        js.collectFirst(Function.unlift { j =>
          for (
            pinj2 <- extendsToSubIso(i, j, pinj);
            pinj3 <- adjNodesMatch(is - i, js - j, pinj2))
          yield pinj3
        })
      })
    }

    // Find an extension for a given node match and partial injection
    def extendsToSubIso(
      i: NodeId, j: NodeId, pinj: Array[NodeId]): Option[Array[NodeId]] = {

      // Look up the nodes infos.
      val n = this.nodes(i)
      val m = that.nodes(j)

      // Check the match.
      if (pinj(i) == j) Some(pinj)             // Node pair already matched
      else if (pinj(i) >= 0) None              // Source node already matched
      else if (pinj contains j) None           // Target node already matched
      else if (n.inMark  != m.inMark)  None    // In-marks must agree
      else if (n.outMark != m.outMark) None    // Out-marks must agree
      else {
        val pinj2 = pinj.updated(i, j)         // Record the match

        // Successors must match.
        for (
          pinj3 <- adjNodesMatch(n.succs, m.succs, pinj2);
          pinj4 <- adjNodesMatch(this.preds(i), that.preds(j), pinj3))
        yield pinj4
      }
    }

    // Quick check: two graphs can't be isomorphic unless they contain
    // the same number of nodes and edges.
    if (this.numNodes != that.numNodes || this.numEdges != that.numEdges) false
    else {
      // Allocate an "empty" partial injection on nodes.
      var pinj = Array.fill[NodeId](numNodes)(-1)
      var done: Boolean = false
      var foundPartialIso: Boolean = true

      // Match connected components until none is left.
      while (!done) {
        val i = findUnmapped(pinj)
        done = i < 0
        if (!done) {
          // Try pairing 'i' with some node in 'that'.
          foundPartialIso = nodeRange.exists { j =>
            // 'j' must not yet be mapped and the pair must extend to
            // a full sub-graph isomorphism.
            extendsToSubIso(i, j, pinj) match {
              case Some(pinj2) => pinj = pinj2; true
              case None        => false
            }
          }
          done = !foundPartialIso
        }
      }
      foundPartialIso
    }
  }

  /** Check whether this graph is NOT isomorphic to 'that'. */
  def !~(that: Digraph): Boolean = !(this ~ that)

  /** Glue this graph to 'that'. */
  def glue(that: Digraph): List[(Digraph, Int)] = {

    def weakMergeNodes(
      g: Digraph, i1: NodeId, i2: NodeId,
      inBounds:  Array[Int], outBounds:  Array[Int],
      inDegrees: Array[Int], outDegrees: Array[Int]) = {

      def lift(n: NodeInfo) = {
        val succs = n.succs map { j =>
          if (j < i2) j else if (j == i2) i1 else (j - 1)
        }
        NodeInfo(succs, n.inMark, n.outMark)
      }

      val n1   = g.nodes(i1);       val n2   = g.nodes(i2)
      val im1  = n1.inMark;         val im2  = n2.inMark
      val om1  = n1.outMark;        val om2  = n2.outMark
      val ib1  = inBounds(i1);      val ib2  = inBounds(i2)
      val ob1  = outBounds(i1);     val ob2  = outBounds(i2)
      val idg1 = inDegrees(i1);     val idg2 = inDegrees(i2)
      val odg1 = outDegrees(i1);    val odg2 = outDegrees(i2)

      // Quick check: are the constraints of these nodes compatible?
      if      (im1 && idg2 > ib1) Nil
      else if (om1 && odg2 > ob1) Nil
      else if (im2 && idg1 > ib2) Nil
      else if (om2 && odg1 > ob2) Nil
      else {
        // Merge the node arrays and lift all nodes but 'i1' and 'i2'.
        val uNodes = new Array[NodeInfo](g.numNodes - 1)
        for (i <- 0 until i1)                { uNodes(i) = lift(g.nodes(i)) }
        for (i <- (i1 + 1) until i2)         { uNodes(i) = lift(g.nodes(i)) }
        for (i <- (i2 + 1) until g.numNodes) {
          uNodes(i - 1) = lift(g.nodes(i))
        }

        // Merge 'i1' and 'i2' and lift the result.
        val succs = n1.succs ++ n2.succs
        val im = im1 || im2
        val om = om1 || om2
        uNodes(i1) = lift(NodeInfo(succs, im, om))

        val uInBounds   = new Array[Int](g.numNodes - 1)
        val uOutBounds  = new Array[Int](g.numNodes - 1)
        val uInDegrees  = new Array[Int](g.numNodes - 1)
        val uOutDegrees = new Array[Int](g.numNodes - 1)

        // Copy/merge the bound and degree arrays.
        Array.copy(inBounds,   0, uInBounds,   0, i1)
        Array.copy(outBounds,  0, uOutBounds,  0, i1)
        Array.copy(inDegrees,  0, uInDegrees,  0, i1)
        Array.copy(outDegrees, 0, uOutDegrees, 0, i1)
        Array.copy(inBounds,   i1 + 1, uInBounds,   i1 + 1, i2 - i1 - 1)
        Array.copy(outBounds,  i1 + 1, uOutBounds,  i1 + 1, i2 - i1 - 1)
        Array.copy(inDegrees,  i1 + 1, uInDegrees,  i1 + 1, i2 - i1 - 1)
        Array.copy(outDegrees, i1 + 1, uOutDegrees, i1 + 1, i2 - i1 - 1)
        Array.copy(inBounds,   i2 + 1, uInBounds,   i2, g.numNodes - i2 - 1)
        Array.copy(outBounds,  i2 + 1, uOutBounds,  i2, g.numNodes - i2 - 1)
        Array.copy(inDegrees,  i2 + 1, uInDegrees,  i2, g.numNodes - i2 - 1)
        Array.copy(outDegrees, i2 + 1, uOutDegrees, i2, g.numNodes - i2 - 1)

        // Compute the merged bound and degree of 'i1' and 'i2'.
        uInBounds(i1)   = if (!im2 || (im1 && (ib1 < ib2))) ib1 else ib2
        uOutBounds(i1)  = if (!om2 || (om1 && (ob1 < ob2))) ob1 else ob2
        uInDegrees(i1)  = if (idg1 > idg2) idg1 else idg2
        uOutDegrees(i1) = if (odg1 > odg2) odg1 else odg2

        List((Digraph(uNodes), uInBounds, uOutBounds, uInDegrees, uOutDegrees))
      }
    }

    def verifyBounds(
      g: Digraph, inBounds: Array[Int], outBounds: Array[Int]): Boolean =
      g.nodeRange.forall { i =>
        (!g.nodes(i).inMark  || (g.inDegree(i)  <= inBounds(i))) &&
        (!g.nodes(i).outMark || (g.outDegree(i) <= outBounds(i)))
      }

    def mergeNodes(
      g: Digraph, i: NodeId, pivot: NodeId,
      inBounds:  Array[Int], outBounds:  Array[Int],
      inDegrees: Array[Int], outDegrees: Array[Int]): List[(Digraph, Int)] = {

      if (i == pivot) {
        // Verify the initial graph and return it if is valid.
        if (verifyBounds(g, inBounds, outBounds)) List((g, 1)) else Nil
      } else {
        // Merge the remaining nodes recursively
        val merged = for {
          j <- pivot until g.numNodes
          gbd <- weakMergeNodes(
            g, i, j, inBounds, outBounds, inDegrees, outDegrees)
        } yield gbd
        val unmerged = (g, inBounds, outBounds, inDegrees, outDegrees)
        for {
          (g1, ib1, ob1, idg1, odg1) <- unmerged :: merged.toList
          g2 <- mergeNodes(g1, i + 1, pivot, ib1, ob1, idg1, odg1)
        } yield g2
      }
    }

    // Compute the trivial MG.
    val g = this + that

    // Record the in and out degree of every node.
    val inDegrees  = Array.tabulate(g.numNodes) { i => g.inDegree(i)  }
    val outDegrees = Array.tabulate(g.numNodes) { i => g.outDegree(i) }

    // Recursively merge nodes to produce gluings.
    mergeNodes(
      g, 0, this.numNodes,
      inDegrees, outDegrees, inDegrees, outDegrees).sortBy {
      case (g, _) => (-g.numNodes, -g.numEdges)
    }
  }

  override def toString: String = {
    def eStr(e: (NodeId, NodeId)) = e._1 + "->" + e._2
    def allInMarks  =
      (for (i <- nodeRange if nodes(i).inMark)  yield "-/->" + i)
    def allOutMarks =
      (for (i <- nodeRange if nodes(i).outMark) yield i + "-/->")
    def allEdges = edges.map(eStr) ++ allInMarks ++ allOutMarks

    "(" + {
      if (nodes.isEmpty) "{}" else "{ 0.." + (numNodes - 1) + " }"
    } + ", " + {
      if (allEdges.isEmpty) "{}" else allEdges.mkString("{ ", ", ", " }")
    } + ")"
  }

  /** Produce a DOT string for this graph. */
  def toDot: String = {
    def nStr(i: NodeId) = "v" + i + {
      if (nodes(i).inMark)
        "; i" + i + " [style=dashed]; i" + i + " -> " + "v" + i +
        " [style=dashed]"
      else ""
    } + {
      if (nodes(i).outMark)
        "; o" + i + " [style=dashed]; v" + i + " -> " + "o" + i +
        " [style=dashed]"
      else ""
    }
    def eStr(e: (NodeId, NodeId)) = "v" + e._1 + " -> " + "v" + e._2
    val allNodes = nodeRange.map(nStr)
    val allEdges = edges.map(eStr)
    "digraph { " +
      "node [label = \"\"; fixedsize = true; width = .15; shape = circle]; " +
      "edge [arrowsize=.75]; " +
      (allNodes ++ allEdges).mkString("; ") + " }"
  }
}

object Digraph {

  /** Nodes are just integers */
  type NodeId = Int

  /**
   * Node info:
   *  - list of successors,
   *  - is there a mark/constraint on the in-degree of this node?
   *  - is there a mark/constraint on the out-degree of this node?
   */
  case class NodeInfo(succs: Set[NodeId], inMark: Boolean, outMark: Boolean)

  /** The empty/initial graph. */
  val empty = Digraph(Array())

  /** The one-node graph (no edges). */
  val node = Digraph(Array(NodeInfo(Set(), false, false)))

  /** The fully marked one-node graph (no edges). */
  val mNode = Digraph(Array(NodeInfo(Set(), true, true)))

  /** The two-node, one-edge graph. */
  val edge = Digraph(Array(
    NodeInfo(Set(), false, false), NodeInfo(Set(0), false, false)))

  /** The terminal, one-node, one-edge graph. */
  val unit = Digraph(Array(NodeInfo(Set(0), false, false)))

  /** Create an n-star pattern with a in-mark on the center. */
  def star(n: Int): Digraph = {
    val nodes = new Array[NodeInfo](n + 1)
    nodes(0) = NodeInfo(Set(), true, false)
    for (i <- 1 to n) { nodes(i) = NodeInfo(Set(0), false, false) }
    Digraph(nodes)
  }

  /**
   * Quotient isomorphic graphs as a vector/sequence of integers
   * indexed by isomorphism classes of graphs.  If all the integers
   * in the sequence are positive, the result corresponds to a
   * multiset of non-isomorphic graphs.
   */
  def quotientByIso(gs: Seq[(Digraph, Int)]): Seq[(Digraph, Int)] = {
    val q = ArrayBuffer[(Digraph, Int)]()
    for ((g, i) <- gs if i != 0) {
      val pos = q indexWhere { case (h, _) => h ~ g }
      if (pos < 0) q += ((g, i))
      else {
        val (h, j) = q(pos)
        val m = i + j
        if (m == 0) q.remove(pos)
        else q(pos) = (h, m)
      }
    }
    q
  }

  /** Check whether two sequences of graphs are pair-wise isomorphic. */
  def allIso(as: Seq[(Digraph, Int)], bs: (Digraph, Int)*): Boolean =
    as.zipAll(bs, (empty, 0), (empty, 0)).forall {
      case ((a, i), (b, j)) => (a ~ b) && (i == j)
    }
}
