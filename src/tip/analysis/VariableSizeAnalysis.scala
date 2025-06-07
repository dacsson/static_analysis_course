package tip.analysis

import tip.ast.AstNodeData.DeclarationData
import tip.ast.{AExpr, AInput}
import tip.cfg._
import tip.lattices.IntervalLattice.{MInf, Num, PInf}
import tip.lattices.VariableSizeLattice.{TBigInt, TNothing, resolveType}
import tip.lattices._
import tip.solvers._

import scala.collection.SortedSet

trait VariableSizeAnalysisWidening extends ValueAnalysisMisc with Dependencies[CfgNode] {
//  @note : originally i wanted to take all powers of 2 which is logical (for my dumb ahh)
//          then i realised we can take only a certain powers of 2, so char_min, char_max, int_max, int_min etc.
//          kaif
//
//  private val pos2pows =
//    (0 to 17).map(x => pow(2, x).intValue).toSet
//
//  private val pos2neg =
//    pos2pows.map(-_)
//
//  private val B = (pos2pows ++ pos2neg).map(x => IntNum(x): Num) + MInf + PInf

  // we need:
  //  Bool
  //  Byte
  //  Char
  //  Int

  val cfg: ProgramCfg

  val valuelattice: VariableSizeLattice.type

  val liftedstatelattice: LiftLattice[statelattice.type]

  def loophead(n: CfgNode): Boolean = indep(n).exists(cfg.rank(_) > cfg.rank(n))

  private val B : SortedSet[Num] = SortedSet(
      0, // Boolean
      1, // Boolean
      Byte.MinValue,
      Byte.MaxValue,
      Char.MinValue,
      Char.MaxValue,
      Int.MinValue,
      Int.MaxValue,
      MInf,
      PInf,
  );

  println(s"set is $B min is ${B.min}")
//    val maxs = List[Num](
//      1, // BOolean
//      Byte.MaxValue,
//      Char.MaxValue,
//      Int.MaxValue,
//    )
//
//    ( vals ::: List(MInf, PInf) ).toSet

  private def minB(b: IntervalLattice.Num) = B.filter(b <= _).min

  private def maxB(a: IntervalLattice.Num) = B.filter(_ <= a).max

  def widenInterval(x: valuelattice.Element, y: valuelattice.Element): valuelattice.Element = {
    println(s" - widenInterval: $x and $y")
    (x, y) match {
      case ((_, _, TNothing), _) => y
      case (_, (_, _, TNothing)) => x
      case ((l1, h1, _), (l2, h2, _)) =>
        val min = if (l1 <= l2) l1 else maxB(l2)
        val max = if (h2 <= h1) h1 else minB(h2)
        (min, max, resolveType(min, max))
    }
  }

  // MAX_INT -> +inf
  override def eval(exp: AExpr, env: statelattice.Element)(implicit declData: DeclarationData): valuelattice.Element = {
    exp match {
      case _: AInput => (MInf, PInf, TBigInt)
      case _ => super.eval(exp, env)
    }
  }

  def widen(x: liftedstatelattice.Element, y: liftedstatelattice.Element): liftedstatelattice.Element = {
    println(s"to widen : $x and $y")
    (x, y) match {
      case (liftedstatelattice.Bottom, _) => y
      case (_, liftedstatelattice.Bottom) => x
      case (liftedstatelattice.Lift(xm), liftedstatelattice.Lift(ym)) =>
        liftedstatelattice.Lift(declaredVars.map { v => {
          println(s"  - result: ${widenInterval(xm(v), ym(v))}")
          v -> widenInterval(xm(v), ym(v))
        }
        }.toMap)
    }
  }
}

object VariableSizeAnalysis {
  object Intraprocedural {
    class WorklistSolverWithWidening(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
      extends IntraprocValueAnalysisWorklistSolverWithReachability(cfg, VariableSizeLattice)
        with WorklistFixpointSolverWithReachabilityAndWidening[CfgNode]
        with VariableSizeAnalysisWidening

//    class WorklistSolverWithWideningAndNarrowing(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
//      extends IntraprocValueAnalysisWorklistSolverWithReachability(cfg, IntervalLattice)
//        with WorklistFixpointSolverWithReachabilityAndWideningAndNarrowing[CfgNode]
//        with VariableSizeAnalysisWidening {
//
//      val narrowingSteps = 5
//    }
  }
}