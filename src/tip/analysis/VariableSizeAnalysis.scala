package tip.analysis

import tip.ast.AstNodeData.DeclarationData
import tip.cfg._
import tip.lattices.IntervalLattice.{IntNum, MInf, Num, PInf}
import tip.lattices._
import tip.solvers._

import scala.math.Ordering.Implicits.infixOrderingOps
import scala.math.pow
import scala.util.Try

trait VariableSizeAnalysisWidening extends IntervalAnalysisWidening {
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

  private val B = {
    val vals = List[Num](
      0, // Boolean
      1, // Boolean
      Byte.MinValue,
      Byte.MaxValue,
      Char.MinValue,
      Char.MaxValue,
      Int.MinValue,
      Int.MaxValue
    )

//    val maxs = List[Num](
//      1, // BOolean
//      Byte.MaxValue,
//      Char.MaxValue,
//      Int.MaxValue,
//    )

    ( vals ::: List(MInf, PInf) ).toSet
  }

  private def minB(b: IntervalLattice.Num) = B.filter(b <= _).min

  private def maxB(a: IntervalLattice.Num) = B.filter(_ <= a).max

  override def widenInterval(x: valuelattice.Element, y: valuelattice.Element): valuelattice.Element =
    (x, y) match {
      case (IntervalLattice.EmptyInterval, _) => y
      case (_, IntervalLattice.EmptyInterval) => x
      case ((l1, h1), (l2, h2)) =>
        // [[l1, h1]] op [[l2, h2]] = [[min x1 op y1 , max x2 op y2]] ???
        (maxB(l1 min l2), minB(h1 max h2))
    }

  override def widen(x: liftedstatelattice.Element, y: liftedstatelattice.Element): liftedstatelattice.Element =
    (x, y) match {
      case (liftedstatelattice.Bottom, _) => y
      case (_, liftedstatelattice.Bottom) => x
      case (liftedstatelattice.Lift(xm), liftedstatelattice.Lift(ym)) =>
        liftedstatelattice.Lift(declaredVars.map { v =>
          v -> widenInterval(xm(v), ym(v))
        }.toMap)
    }
}

object VariableSizeAnalysis {
  object Intraprocedural {
    class WorklistSolverWithWidening(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
      extends IntraprocValueAnalysisWorklistSolverWithReachability(cfg, IntervalLattice)
        with WorklistFixpointSolverWithReachabilityAndWidening[CfgNode]
        with VariableSizeAnalysisWidening

    class WorklistSolverWithWideningAndNarrowing(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
      extends IntraprocValueAnalysisWorklistSolverWithReachability(cfg, IntervalLattice)
        with WorklistFixpointSolverWithReachabilityAndWideningAndNarrowing[CfgNode]
        with VariableSizeAnalysisWidening {

      val narrowingSteps = 5
    }
  }
}