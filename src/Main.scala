import scala.collection.mutable.{ ArrayBuffer }
import java.io.{ BufferedReader, FileReader, PrintWriter }

case class TooManyOdes(numOdes: Int) extends Exception

object Main {

  import Digraph._

  def computeOdes(vs: VarMap, rules: Seq[Rule], thsld: Int)
      : Seq[(Var, Expr, Digraph)] = {

    def processRule(r: Rule, g: Digraph, vs: VarMap) = {
      var newGs = ArrayBuffer[Digraph]()
      var sum: Expr = Const(0)
      for ((g1, k) <- r(g)) {
        val (v, isNew) = vs(g1)  // Lookup the variable for 'g1'
        if (isNew) newGs += g1
        sum = Sum(Prod(Const(k), Prod(r.rate, v)), sum)
      }
      (newGs, sum)
    }

    var i = 0
    var toCheck = ArrayBuffer(vs.keys: _*)
    var odes = ArrayBuffer[(Var, Expr, Digraph)]()
    while (!toCheck.isEmpty) {
      print("  Iteration " + i + ": checking " + toCheck.size +
        " new graphs...")
      var newGs = ArrayBuffer[Digraph]()
      for (g <- toCheck) yield {
        val (v, _) = vs(g)  // Lookup the variable for 'g'
        var rhs: Expr = Const(0)
        for (r <- rules) {
          val (gs, sum) = processRule(r, g, vs)
          if (vs.size > thsld) throw TooManyOdes(vs.size)
          rhs = Sum(sum, rhs)
          newGs ++= gs
        }
        odes += ((v, rhs.normalize, g))
      }
      i += 1
      toCheck = newGs
      println(" done.")
    }
    assert(vs.size == odes.length)
    odes
  }

  // Command name
  val cmd = "ode-gen"

  // Symbolic constants for output type
  val TextOutput   = 0
  val DotOutput    = 1
  val OctaveOutput = 2
  val TexOutput    = 3

  /** Print usage instructions and exit with a given exit code. */
  def printUsage(exitCode: Int): Nothing = {
    Console.err.println("USAGE: " + cmd +
      " [OPTION]... [INDEGREE] [MOMENT]... [FILE]")
    Console.err.println("Options:")
    Console.err.println("  -d --dot     Produce DOT output (graphs only).")
    Console.err.println("  -o --octave  Produce GNU/Octave output." )
    Console.err.println("  -t --tex     Produce TeX output.")
    Console.err.println("  -h --help    Print these instructions.")
    sys.exit(exitCode)
  }

  /** Parse command line arguments. */
  def parseArgs(args: Array[String]) = {

    var i = 0;
    var outputType = -1
    while ((args.size > i) && (args(i)(0) == '-')) args(i) match {
      case "-d" | "--dot"    => outputType = DotOutput   ; i += 1
      case "-o" | "--octave" => outputType = OctaveOutput; i += 1
      case "-t" | "--tex"    => outputType = TexOutput   ; i += 1
      case "-h" | "--help"   => printUsage(0)
      case _                 =>
        Console.err.println(cmd + ": invalid option: " + args(i))
        printUsage(1)
    }

    // Degree of nodes.
    val n = if (args.size > i) args(i).toInt else 3; i += 1

    // Degree of moment.
    val ks = ArrayBuffer[Int]()
    var goodK = true
    while (args.size > i && goodK) try {
      val k = args(i).toInt
      if (k > 0) { ks += k; i+= 1 }
      else {
        Console.err.println(cmd + ": invalid moment degree: " + k)
        printUsage(1)
      }
    } catch {
      case _: java.lang.NumberFormatException => goodK = false
    }
    if (ks.isEmpty) ks += 1  // Need at least one moment

    // By default, use standard out for output.
    val (out, outFilename) = if (args.size > i) {
      try { (new PrintWriter(args(i)), "'" + args(i) + "'") }
      catch {
        case e: java.lang.Exception =>
          Console.err.println(cmd + ": error opening file '" + args(i) +
            "': " + e.getMessage)
          printUsage(1)
      }
    } else (new PrintWriter(Console.out), "standard out")

    // If no specific output type was specified, try to infer it from
    // the output file name.  Default to plain text output.
    if (outputType == -1) outputType =
      if (outFilename endsWith ".dot'") DotOutput
      else if (outFilename endsWith ".m'") OctaveOutput
      else if (outFilename endsWith ".tex'") TexOutput
      else TextOutput

    (n, ks, outputType, out, outFilename)
  }

  // *** Main method ***
  def main(args: Array[String]) {

    // Parse the command line arguments
    val (n, ks, outputType, out, outFilename) = parseArgs(args)

    // Build a star with n spokes. */
    val nStar = star(n)

    // Some unit tests to make sure isomorphism-checking works ;-)
    assert(empty ~ empty,  "empty !~ empty")
    assert(node  ~ node,   "node !~ node")
    assert(edge  ~ edge,   "edge !~ edge")
    assert(unit  ~ unit,   "unit !~ unit")
    assert(nStar ~ nStar,  "nStar !~ nStar")
    assert(empty !~ unit,  "empty ~ unit")
    assert(empty !~ node,  "empty ~ node")
    assert(empty !~ edge,  "empty ~ edge")
    assert(empty !~ nStar, "empty ~ nStar")
    assert(unit  !~ empty, "unit ~ empty")
    assert(unit  !~ nStar, "unit ~ nStar")
    assert(nStar !~ empty, "nStar ~ empty")
    assert(nStar !~ unit,  "nStar ~ unit")
    val a = Digraph(Array(NodeInfo(Set(), false), NodeInfo(Set(), false)))
    val b = Digraph(Array(NodeInfo(Set(), false), NodeInfo(Set(), true)))
    assert(a !~ b, a + " ~ " + b)
    assert(b !~ a, b + " ~ " + a)

    // Some unit tests to make sure gluing works ;-)
    assert(allIso(empty glue empty, (empty, 1)),
      "empty glue empty !~ { empty }")
    assert(allIso(node glue node, (node + node, 1), (node, 1)),
      "node glue node !~ { node, node + node }")
    assert(allIso(unit glue unit, (unit + unit, 1), (unit, 1)),
      "unit glue unit !~ { unit, unit + unit }")
    assert(allIso(empty glue unit, (unit, 1)),
      "empty glue unit !~ { unit }")
    assert(allIso(unit glue empty, (unit, 1)),
      "unit glue empty !~ { unit }")
    assert(allIso(node glue empty, (node, 1)),
      "node glue empty !~ { node }")
    assert(allIso(edge glue empty, (edge, 1)),
      "edge glue empty !~ { edge }")
    assert(allIso(empty glue nStar, (nStar, 1)),
      "empty glue nStar !~ { nStar }")
    assert(allIso(nStar glue empty, (nStar, 1)),
      "nStar glue empty !~ { nStar }")

    // Glue 'g' with itself 'k' times
    def kGlue(g: Digraph, k: Int): Seq[(Digraph, Int)] =
      if (k <= 1) Seq((g, 1)) else quotientByIso {
        for ((f, i) <- kGlue(g, k - 1); (h, j) <- g glue f) yield (h, i * j)
      }

    // Create the variable map and initialize it with the 'k'-ary
    // self-gluings corresponding to the various moments.
    val vs = VarMap.empty
    val momentRhsTerms = for (k <- ks) yield {

      // Compute the 'k'-ary self-gluings
      val gs = kGlue(nStar, k)

      // Extract the RHS terms of the 'k'-th moment definition.
      val rhs = for ((g, c) <- gs) yield {
        // Lookup/add the 'g' in the variable map and add the
        // resulting term.
        val (v, _) = vs(g)
        Prod(Const(c), v)
      }
      (k, rhs)
    }

    val rules = List(Rule0, Rule1, Rule2)

    // Redirect output to standard error.
    Console.withOut(Console.err) {

      // Generate the ODEs
      try {
        println("Generating ODEs for moments " + ks.mkString(", ") +
          " of the " + n + "-star observable...")
        val odes = computeOdes(vs, rules, 3000)
        println("done.")

        // Produce GNU/Octave output
        outputType match {
          case DotOutput =>
            for ((_, _, g) <- odes) out.println(g.toDot)

          case OctaveOutput =>
            print("Computing initial conditions...")
            val x0 = for ((_, _, g) <- odes) yield {
              if (g.nodes.size == 1 && g.edges.size == 0) 1.0 else 0.0
            }
            println("done.")

            out.println("# ODEs for moments " + ks.mkString(", ") +
              " of the " + n + "-star observable.")
            out.println("#")
            out.println("# Associated graph observables:")
            for ((v, _, g) <- odes)
              out.println("#   " + v.toOctave + " = #" + g)
            out.println("function xdot = f(x, t)")
            out.println("  global k")
            for ((v, rhs, _) <- odes)
              out.println("  xdot(" + (v.index + 1) + ") = " +
                rhs.toOctave + ";")
            out.println("endfunction")
            out.println
            out.println("# Initial conditions.")
            out.println("x_0 = " + x0.mkString("[ ", ", ", " ]") + ";")
            out.println
            out.println("# To solve the ODEs, load this file, then run " +
              "the following:")
            val rates = for (r <- rules) yield "<" + r.rate + ">"
            out.println("# global k = [ " + rates.mkString(", ") +
              " ];     # Rule rates.")
            out.println("# t = linspace(<t_0>, <t_end>, <#steps>);" +
              "   # Output times.")
            out.println("# x = lsode(\"f\", x_0, t);   # Solve ODEs.")
            for ((k, rhs) <- momentRhsTerms) {
              val terms =
                for (Prod(Const(c), Var(n, i)) <- rhs)
                yield c + " * " + n + "(:, " + (i + 1) + ")"
              out.println("# moment_" + k + " = " + terms.mkString(" + ") +
                ";  # Compute moment " + k + ".")
            }
            out.println("# plot(" + ks.map("t, moment_" + _).mkString(",") +
              ");  # Plot moments.");

          case TexOutput =>
            out.println("\\documentclass{article}")
            out.println("\\usepackage{amsmath}")
            out.println("\\begin{document}")
            out.println("\\allowdisplaybreaks")
            out.println("  \\begin{align*}")
            for ((k, rhs) <- momentRhsTerms) {
              val lhs = if (k == 1) "    x" else "    x^" + k
              out.println(
                lhs + " &= " + rhs.map(_.normalize.toTex).mkString(" + ") +
                  "\\\\")
            }
            for ((v, rhs, _) <- odes)
              out.println(
                "    \\tfrac{d}{dt}" + v.toTex + " &= " + rhs.toTex + "\\\\")
            out.println("  \\end{align*}")
            out.println("\\end{document}")

          case _ =>
            for ((k, rhs) <- momentRhsTerms) {
              out.println("x^" + k + " = " + rhs.mkString(" + "))
            }
            for ((v, rhs, _) <- odes) { out.println("d" + v + "/dt = " + rhs) }
            out.println("where")
            for ((v, _, g) <- odes) { out.println("  " + v + " = #" + g) }
        }
        out.flush
        if (args.size > 2) out.close
        println("Wrote " + odes.size + " ODEs to " + outFilename + ".")

      } catch {
        case TooManyOdes(odes) =>
          println("/nToo many ODEs: threshold exceeded at " + odes + " ODEs.")
          println("Aborting...")
      }
    }
  }
}
