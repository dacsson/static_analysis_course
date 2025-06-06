package tip.analysis

import tip.ast.AstNodeData.DeclarationData
import tip.ast._
import tip.cfg.{CfgFunEntryNode, CfgNode, CfgStmtNode, IntraproceduralProgramCfg}
import tip.lattices.{MapLattice, PowersetLattice}
import tip.solvers.{SimpleMapLatticeFixpointSolver, SimpleWorklistFixpointSolver}

abstract class ReachingDefinitionsAnalysis(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData) extends FlowSensitiveAnalysis(true) {

  val lattice: MapLattice[CfgNode, PowersetLattice[AStmt]] = new MapLattice(new PowersetLattice())

  val domain: Set[CfgNode] = cfg.nodes

  NoPointers.assertContainsProgram(cfg.prog)
  NoRecords.assertContainsProgram(cfg.prog)

  def transfer(n: CfgNode, s: lattice.sublattice.Element): lattice.sublattice.Element =
    n match {
      case _: CfgFunEntryNode => Set()
      case r: CfgStmtNode =>
        r.data match {
          case as: AAssignStmt =>
            // [[x = E]] = removedefs(JOIN(n), x) U {x = E}
            as.left match {
              case id: AIdentifier =>
                s.filter(
                  stmt =>
                    stmt match {
                      case assign: AAssignStmt =>
                        assign.left.asInstanceOf[AIdentifier].name != id.name
                      case varr: AVarStmt =>
                        !varr.declIds.map(_.name).contains(id.name)
                      case _ => false
                    }
                ) + as
              case _ => s
            }
          case varr: AVarStmt =>
            // [[var x]] = {var x}
            s ++ varr.declIds.map(v => AVarStmt(List(v), varr.loc)).toSet[AStmt]
          case _ => s
        }
      case _ => s
    }

}

class ReachingDefAnalysisSimpleSolver(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
  extends ReachingDefinitionsAnalysis(cfg)
    with SimpleMapLatticeFixpointSolver[CfgNode]
    with ForwardDependencies

class ReachingDefAnalysisWorklistSolver(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
  extends ReachingDefinitionsAnalysis(cfg)
    with SimpleWorklistFixpointSolver[CfgNode]
    with ForwardDependencies