
/** Symbolic expressions */
sealed abstract class Expr {

  /** Perform some simplifications. */
  def normalize: Expr = this match {
    case v: Var                  => v
    case Const(x)                => Const(x)
    case Sum(e1, e2)             => (e1.normalize, e2.normalize) match {
      case (Const(0), e)         => e
      case (e, Const(0))         => e
      case (Const(x), Const(y))  => Const(x + y)
      case (Const(x), Sum(Const(y), e)) => Sum(Const(x + y), e).normalize
/* FIXME: check these and comment them back in...
      case (Sum(e1, e2), e3)     => Sum(e1, Sum(e2, e3)).normalize
      case (e1, e2) if e1 == e2  => Prod(Const(2), e1).normalize
      case (e1, Sum(e2, e3)) if e1 == e2 =>
        Sum(Prod(Const(2), e1), e3).normalize
      case (Prod(e1, e2), e3) if e1 == e3 =>
        Prod(Sum(Const(1), e2), e1).normalize
      case (Prod(e1, e2), e3) if e2 == e3 =>
        Prod(Sum(Const(1), e1), e2).normalize
      case (e1, Prod(e2, e3)) if e1 == e2 =>
        Prod(Sum(Const(1), e3), e1).normalize
      case (e1, Prod(e2, e3)) if e1 == e3 =>
        Prod(Sum(Const(1), e2), e1).normalize
      case (Prod(e1, e2), Prod(e3, e4)) if e1 == e3 =>
        Prod(Sum(e2, e4), e1).normalize
      case (Prod(e1, e2), Prod(e3, e4)) if e1 == e4 =>
        Prod(Sum(e2, e3), e1).normalize
      case (Prod(e1, e2), Prod(e3, e4)) if e2 == e3 =>
        Prod(Sum(e1, e4), e2).normalize
      case (Prod(e1, e2), Prod(e3, e4)) if e2 == e4 =>
        Prod(Sum(e1, e3), e2).normalize
      case (Prod(e1, e2), Sum(Prod(e3, e4), e5)) if e1 == e3 =>
        Sum(Prod(Sum(e2, e4), e1), e5).normalize
      case (Prod(e1, e2), Sum(Prod(e3, e4), e5)) if e1 == e4 =>
        Sum(Prod(Sum(e2, e3), e1), e5).normalize
      case (Prod(e1, e2), Sum(Prod(e3, e4), e5)) if e2 == e3 =>
        Sum(Prod(Sum(e1, e4), e2), e5).normalize
      case (Prod(e1, e2), Sum(Prod(e3, e4), e5)) if e2 == e4 =>
        Sum(Prod(Sum(e1, e3), e2), e5).normalize
      case (e1, Sum(e2, e3)) if e1 < e2 => Sum(e2, Sum(e1, e3)).normalize
      case (e1, e2) if !e2.isInstanceOf[Sum] && (e1 < e2) =>
        Sum(e2, e1).normalize
 */
      case (e1, e2)              => Sum(e1, e2)
    }
    case Prod(e1, e2)            => (e1.normalize, e2.normalize) match {
      case (Const(0), e)         => Const(0)
      case (e, Const(0))         => Const(0)
      case (Const(1), e)         => e
      case (e, Const(1))         => e
      case (Const(x), Const(y))  => Const(x * y)
      case (Const(x), Prod(Const(y), e)) => Prod(Const(x * y), e).normalize
/* FIXME: check these and comment them back in...
      case (Prod(e1, e2), e3)    => Prod(e1, Prod(e2, e3)).normalize
      case (e1, e2) if e1 == e2  => Pow(e1, Const(2))
      case (e1, Prod(e2, e3)) if e1 == e2 =>
        Prod(Pow(e1, Const(2)), e3).normalize
      case (Pow(e1, e2), e3) if e1 == e3 =>
        Pow(Sum(Const(1), e1), e2).normalize
      case (e1, Pow(e2, e3)) if e1 == e2 =>
        Pow(Sum(Const(1), e1), e3).normalize
      case (Pow(e1, e2), Prod(e3, e4)) if e1 == e3 =>
        Prod(Pow(Sum(Const(1), e1), e2), e4).normalize
      case (e1, Prod(Pow(e2, e3), e4)) if e1 == e2 =>
        Prod(Pow(Sum(Const(1), e1), e3), e4).normalize
      case (Pow(e1, e2), Pow(e3, e4)) if e1 == e3 =>
        Pow(e1, Sum(e2, e4)).normalize
      case (Pow(e1, e2), Pow(e3, e4)) if e2 == e4 =>
        Pow(Prod(e1, e3), e2).normalize
      case (Pow(e1, e2), Prod(Pow(e3, e4), e5)) if e1 == e3 =>
        Prod(Pow(e1, Sum(e2, e4)), e5).normalize
      case (Pow(e1, e2), Prod(Pow(e3, e4), e5)) if e2 == e4 =>
        Prod(Pow(Prod(e1, e3), e2), e5).normalize
      case (Pow(e1, e2), Fact(e3)) => Prod(Fact(e3), Pow(e1, e2)).normalize
      case (Fact(e1), e2) if Sum(Const(1), e1).normalize == e2 => Fact(e2)
      case (Fact(e1), Prod(e2, e3))
          if Prod(Fact(e1), e3).normalize != Prod(Fact(e1), e3) =>
        Prod(Prod(Fact(e1), e3).normalize, e2).normalize
      case (e1, Prod(e2, e3)) if e1 < e2 => Prod(e2, Prod(e1, e3)).normalize
      case (e1, e2) if !e2.isInstanceOf[Prod] && (e1 < e2) =>
        Prod(e2, e1).normalize
*/
      case (e1, e2)              => Prod(e1, e2)
    }
/* FIXME: check these and comment them back in...
    case Pow(e1, e2)             => (e1.normalize, e2.normalize) match {
      case (Const(0), e)         => Const(0)
      case (e, Const(0))         => Const(1)
      case (Const(1), e)         => Const(1)
      case (e, Const(1))         => e
      case (Const(x), Const(y))  => Const(math.pow(x, y))
      case (Pow(e1, e2), e3)     => Pow(e1, Prod(e2, e3)).normalize
      case (e1, e2)              => Pow(e1, e2)
    }
    case Fact(e)                 => Fact(e.normalize)
*/
    case e => e
  }

  /** Precedence. */
  def precedence: Int = this match {
    case _: Var     => 3
    case _: Const   => 4
    case _: Sum     => 0
    case _: Prod    => 1
    case _: Pow     => 2
    case _: Fact    => 2
  }

  /** Lexicographic ordering. */
  def <(that: Expr): Boolean = (this, that) match {
    case (e1, e2) if e1.precedence < e2.precedence => true
    case (Var(m, i), Var(n, j))       => m > n || (m == n && i > j)
    case (Const(x), Const(y))         => x < y
    case (Sum(e1, e2), Sum(e3, e4))   => e1 < e3 || (!(e3 < e1) && e2 < e4)
    case (Prod(e1, e2), Prod(e3, e4)) => e1 < e3 || (!(e3 < e1) && e2 < e4)
    case (Pow(e1, e2), Pow(e3, e4))   => e1 < e3 || (!(e3 < e1) && e2 < e4)
    case (Fact(e1), Fact(e2))         => e1 < e2
    case (e1, e2)                     => false
  }

  /** Pretty print. */
  override def toString: String = {

    def inner(e: Expr) = e match {
      case _: Var | _: Const                   => e.toString
      case e if e.precedence < this.precedence => "(" + e.toString + ")"
      case e                                   => e.toString
    }

    this match {
      case Var(n, i)                => n + i
      case Const(n) if n.isWhole    => n.toLong.toString
      case Const(n)                 => n.toString
      case Sum(e1, Prod(Const(x), e2)) if x < 0 =>
        inner(e1) + " - " + inner(Prod(Const(-x), e2))
      case Sum(e1, Sum(Prod(Const(x), e2), e3)) if x < 0 =>
        inner(e1) + " - " + inner(Sum(Prod(Const(-x), e2), e3))
      case Sum(e1, e2)              => inner(e1) + " + " + inner(e2)
      case Prod(x: Const, y: Const) => x + " * " + y
      case Prod(Const(1),  e)       => inner(e)
      case Prod(e, Const(1))        => inner(e)
      case Prod(Const(-1), e)       => "-" + inner(e)
      case Prod(e, Const(-1))       => "-" + inner(e)
      case Prod(e, x: Const)        => x + " " + inner(e)
      case Prod(e1, e2)             => inner(e1) + " " + inner(e2)
      case Pow(e1, e2)              => inner(e1) + "^" + inner(e2)
      case Fact(e)                  => inner(e) + "!"
    }
  }

  /** Pretty print (for Octave code). */
  def toOctave: String = {

    def inner(e: Expr) = e match {
      case _: Var | _: Const => e.toOctave
      case _                 => "(" + e.toOctave + ")"
    }

    this match {
      case Var(n, i)                => n + "(" + (i + 1) + ")"
      case x: Const                 => x.toString
      case Sum(e1, e2)              => inner(e1) + " + " + inner(e2)
      case Prod(Const(-1), e)       => "-" + inner(e)
      case Prod(e, Const(-1))       => "-" + inner(e)
      case Prod(e, x: Const)        => x + " * " + inner(e)
      case Prod(e1, e2)             => inner(e1) + " * " + inner(e2)
      case Pow(e1, e2)              => inner(e1) + "^" + inner(e2)
      case Fact(e)                  => "factorial(" + inner(e) + ")"
    }
  }

  /** Pretty print (for Tex code). */
  def toTex: String = {

    def inner(e: Expr) = e match {
      case _: Var | _: Const                   => e.toTex
      case e if e.precedence < this.precedence => "(" + e.toTex + ")"
      case e                                   => e.toTex
    }

    this match {
      case Var(n, i)                => n + "_{" + i + "}"
      case x: Const                 => x.toString
      case Sum(e1, Prod(Const(x), e2)) if x < 0 =>
        inner(e1) + " - " + inner(Prod(Const(-x), e2))
      case Sum(e1, Sum(Prod(Const(x), e2), e3)) if x < 0 =>
        inner(e1) + " - " + inner(Sum(Prod(Const(-x), e2), e3))
      case Sum(e1, e2)              => inner(e1) + " + " + inner(e2)
      case Prod(x: Const, y: Const) => x + " \\cdot " + y
      case Prod(Const(-1), e)       => "-" + inner(e)
      case Prod(e, Const(-1))       => "-" + inner(e)
      case Prod(e, x: Const)        => x + " " + inner(e)
      case Prod(e1, e2)             => inner(e1) + " " + inner(e2)
      case Pow(e1, e2)              => "{" + inner(e1) + "}^{" + inner(e2) + "}"
      case Fact(e)                  => inner(e) + "!"
    }
  }
}

case class Var(name: String, index: Int) extends Expr
case class Const(value: Double) extends Expr
case class Sum(e1: Expr, e2: Expr) extends Expr
case class Prod(e1: Expr, e2: Expr) extends Expr
case class Pow(e1: Expr, e2: Expr) extends Expr
case class Fact(e: Expr) extends Expr
