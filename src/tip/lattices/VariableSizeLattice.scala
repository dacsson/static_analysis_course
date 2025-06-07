package tip.lattices

import tip.lattices.IntervalLattice.{IntNum, MInf, Num, PInf}

object VariableSizeLattice extends LatticeWithOps {

  sealed trait Type extends Ordered[Type] {
    val order: Int = -1
    override def compare(that: Type): Int = this.order - that.order
  }

  case object TAny extends Type {
    override val order: Int = Int.MaxValue
    override def toString = "any"
  }

  case object TNothing extends Type {
    override val order = 0
    override def toString = "nothing"
  }

  case object TBigInt extends Type {
    override val order = 4

    override def toString = "bigint"
  }

  case object TInt extends Type {
    override val order = 3
    override def toString = "int"
  }

  case object TChar extends Type {
    override val order = 3
    override def toString = "char"
  }

  case object TByte extends Type {
    override val order = 2
    override def toString = "byte"
  }

  case object TBool extends Type {
    override val order = 1
    override def toString = "bool"
  }

  type Element = (Num, Num, Type)

  val FullInterval: Element = (MInf, PInf, TAny)

  val EmptyInterval: Element = (PInf, MInf, TNothing)

  val bottom: Element = EmptyInterval

  override def top: Element = FullInterval

  private def inv(b: Element): Element =
    b match {
      case (_, _, TAny) => FullInterval
      case (_, _, TNothing) => EmptyInterval
      case (IntNum(j), PInf, _) => (MInf, IntNum(-j), TBigInt)
      case (MInf, IntNum(j), _) => (IntNum(-j), PInf, TBigInt)
      case (IntNum(l), IntNum(h), _) =>
        val low = IntNum(math.min(-h, -l))
        val high = IntNum(math.max(-h, -l))
        (low, high, resolveType(low, high))
      case (MInf, MInf, _) => (PInf, PInf, TBigInt)
      case (PInf, PInf, _) => (MInf, MInf, TBigInt)
      case _ => ???
    }

  private def signs(a: Element): Set[Int] =
    a match {
      case (MInf, PInf, _) => Set(-1, 0, +1)
      case (MInf, IntNum(x), _) => if (x > 0) Set(-1, 0, +1, x) else if (x == 0) Set(-1, 0) else Set(x, -1)
      case (IntNum(x), PInf, _) => if (x < 0) Set(x, -1, 0, +1) else if (x == 0) Set(0, +1, x) else Set(+1, x)
      case (IntNum(l), IntNum(h), _) =>
        Set(-1, +1, 0, l, h).filter { x =>
          x <= h && x >= l
        }
      case (MInf, MInf, _) => Set(-1)
      case (PInf, PInf, _) => Set(+1)
      case _ => ???
    }

  private def min(s: Set[Num]): Num =
    if (s.isEmpty) PInf
    else {
      s.reduce { (a, b) =>
        (a, b) match {
          case (PInf, x) => x
          case (x, PInf) => x
          case (MInf, _) | (_, MInf) => MInf
          case (IntNum(x), IntNum(y)) => IntNum(math.min(x, y))
        }
      }
    }

  private def max(s: Set[Num]): Num =
    if (s.isEmpty) MInf
    else {
      s.reduce { (a, b) =>
        (a, b) match {
          case (PInf, _) | (_, PInf) => PInf
          case (x, MInf) => x
          case (MInf, x) => x
          case (IntNum(x), IntNum(y)) => IntNum(math.max(x, y))
        }
      }
    }

  private def opNum(a: Element, b: Int, op: (Int, Int) => Int): Element =
    a match {
      case (_, _, TAny) => FullInterval
      case (_, _, TNothing) => EmptyInterval
      case (MInf, PInf, _) => (MInf, PInf, TBigInt)
      case (MInf, IntNum(x), _) => if (b == 0) (0, 0, TBool) else if (b < 0) (op(x, b), PInf, TBigInt) else (MInf, op(x, b), TBigInt)
      case (IntNum(x), PInf, _) => if (b == 0) (0, 0, TBool) else if (b < 0) (MInf, op(x, b), TBigInt) else (op(x, b), PInf, TBigInt)
      case (IntNum(x), IntNum(y), _) =>
        val low = min(Set(op(x, b), op(y, b)))
        val high = max(Set(op(x, b), op(y, b)))
        (low, high, resolveType(low, high))
    }

  implicit def int2num(i: Int): IntNum = IntNum(i)

  def resolveType(low: Num, high: Num): Type =
    if (low == MInf || low == PInf || high == MInf || high == PInf) TBigInt
    else if (0 <= low && high <= 1) TBool
    else if (-128 <= low && high <= 127) TByte
    else if (0 <= low && high <= 65535) TChar
    else TInt

  override def lub(x: Element, y: Element): Element =
    (x, y) match {
      case ((_, _, TAny), _) | (_, (_, _, TAny)) => FullInterval
      case ((_, _, TNothing), a) => a
      case (a, (_, _, TNothing)) => a
      case ((MInf, _, _), (_, PInf, _)) => (MInf, PInf, TBigInt)
      case ((MInf, IntNum(h1), _), (_, IntNum(h2), _)) => (MInf, IntNum(math.max(h1, h2)), TBigInt)
      case ((IntNum(l1), PInf, _), (IntNum(l2), _, _)) => (IntNum(math.min(l1, l2)), PInf, TBigInt)
      case ((IntNum(l1), IntNum(h1), _), (IntNum(l2), IntNum(h2), _)) =>
        val l = IntNum(math.min(l1, l2))
        val h = IntNum(math.max(h1, h2))
        (l, h, resolveType(l, h))
      case _ => lub(y, x)
    }

  override def num(i: Int): Element = {
    val num = IntNum(i)
    (num, num, resolveType(num, num))
  }

  override def plus(a: Element, b: Element): Element = {
    if (a._3 == TAny || b._3 == TAny) return FullInterval
    if (a._3 == TAny || b._3 == TAny) return FullInterval
    val low = (a._1, b._1) match {
      case (_, MInf) | (MInf, _) => MInf
      case (_, PInf) | (PInf, _) => PInf
      case (IntNum(i), IntNum(j)) => IntNum(i + j)
    }
    val high = (a._2, b._2) match {
      case (_, PInf) | (PInf, _) => PInf
      case (_, MInf) | (MInf, _) => MInf
      case (IntNum(i), IntNum(j)) => IntNum(i + j)
    }
    (low, high, resolveType(low, high))
  }

  override def minus(a: Element, b: Element): Element = plus(a, inv(b))

  override def div(a: Element, b: Element): Element =
    (a, b) match {
      case ((_, _, TNothing), _) => EmptyInterval
      case (_, (_, _, TNothing)) => EmptyInterval
      case ((_, _, TAny), _) => FullInterval
      case (_, (_, _, TAny)) => FullInterval
      case _ =>
        val sb = signs(b)
        val sbNoZero = sb - 0
        val d = { (x: Int, y: Int) =>
          x / y
        }
        val arange = sbNoZero.map(s => opNum(a, s, d))
        val low = min(arange.map { x =>
          x._1
        })
        val high = max(arange.map { x =>
          x._2
        })
        (low, high, resolveType(low, high))
    }

  override def times(a: Element, b: Element): Element =
    (a, b) match {
      case ((_, _, TNothing), _) => EmptyInterval
      case (_, (_, _, TNothing)) => EmptyInterval
      case ((_, _, TAny), _) => FullInterval
      case (_, (_, _, TAny)) => FullInterval
      case _ =>
        val sa = signs(a)
        val sb = signs(b)
        val mult = { (x: Int, y: Int) =>
          x * y
        }
        val arange = sb.map(s => opNum(a, s, mult))
        val brange = sa.map(s => opNum(b, s, mult))
        val low = min(arange.map { x =>
          x._1
        })
        val high = max(brange.map { x =>
          x._2
        })
        (low, high, resolveType(low, high))
    }

  def eqq(a: Element, b: Element): Element =
    (a, b) match {
      case (FullInterval, _) => FullInterval
      case (_, FullInterval) => FullInterval
      case ((IntNum(l1), IntNum(h1), _), (IntNum(l2), IntNum(h2), _)) =>
        if (l1 == h1 && h1 == l2 && l2 == h2) {
          val num = IntNum(1)
          (num, num, resolveType(num, num))
        } else {
          val l = IntNum(0)
          val h = IntNum(1)
          (l, h, resolveType(l, h))
        }
      case _ =>
        val l = IntNum(0)
        val h = IntNum(1)
        (l, h, resolveType(l, h))
    }

  def gt(a: Element, b: Element): Element =
    (a, b) match {
      case (FullInterval, _) => FullInterval
      case (_, FullInterval) => FullInterval
      case ((IntNum(l1), IntNum(h1), _), (IntNum(l2), IntNum(h2), _)) =>
        if (h1 < l2) {
          val num = IntNum(1)
          (num, num, resolveType(num, num))
        } else if (h2 < l1) {
          val num = IntNum(0)
          (num, num, resolveType(num, num))
        }else {
          val l = IntNum(0)
          val h = IntNum(1)
          (l, h, resolveType(l, h))
        }
      case _ =>
        val l = IntNum(0)
        val h = IntNum(1)
        (l, h, resolveType(l, h))
    }
}