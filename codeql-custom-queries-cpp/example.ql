/**
 * @kind problem
 * @problem.severity warning
 * @id cpp/example/empty-block
 */

import cpp
import semmle.code.cpp.commons.Dependency
import semmle.code.cpp.Function

import semmle.code.cpp.controlflow.StackVariableReachability

import semmle.code.cpp.dataflow.TaintTracking

 // from IfStmt ifstmt, BlockStmt block
 // where ifstmt.getThen() = block and
 //     block.getNumStmt() = 1
 // select ifstmt, "If statement with single statement in then branch"
 
 
 // from Function func, Variable var, Variable res, Location loc
 // where func.getName() = "swPipeBase_create" and
 //     var.getName() = "object" and
 //     // var.getScope() = func
 //     var.getAnAccess().getEnclosingFunction() = func and
 //     loc.getFile() = func.getFile() and
 //     loc.getStartLine() = 33 and
 //     var.getAnAccess().getLocation() = loc and
 //     // res.getAnAccess().getEnclosingFunction() = func
 //     dependsOnTransitive(res, loc)
 //     // and
 //     // dependsOnTransitive(var, res)
 // select res,  "selected var is"
 
 
//  predicate nodeInFunc(ControlFlowNode node) {
//      exists(Function func |
//          func.getName() = "swPipeBase_create" |
//          node.getEnclosingStmt().getEnclosingFunction() = func
//      )
//  }
 
//  predicate nodeOnTargetLine(ControlFlowNode node) {
//      exists(Function func, Location loc |
//          func.getName() = "swPipeBase_create" and
//          loc.getFile() = func.getFile() and
//          loc.getStartLine() = 33 and
//          node.getLocation() = loc
//      )
//  }
 
 
//  class VariableDependency extends StackVariableReachability {
//      VariableDependency() {
//          this = "VariableDependency"
//      }
 
//      override predicate isSource(ControlFlowNode node, StackVariable v) { nodeInFunc(node) }
 
//      override predicate isSink(ControlFlowNode node, StackVariable v) {
//          nodeOnTargetLine(node)
//      }
 
//      override predicate isBarrier(ControlFlowNode node, StackVariable v) {
//          none()
//      }
//  }
 
 
//  from VariableDependency dep, Expr src, Expr sink
//  where dep.reaches(src, _, sink)
//  select src, "src are"

predicate nodeInFunc(Expr node) {
    exists(Function func |
        func.getName() = "swPipeBase_create" |
        node.getEnclosingFunction() = func
    )
}

predicate nodeOnTargetLine(Expr node) {
    exists(Function func, Location loc |
        func.getName() = "swPipeBase_create" and
        loc.getFile() = func.getFile() and
        loc.getStartLine() = 33 and
        node.getLocation() = loc
    )
}


string target_function() {
    result = "swPipeBase_create"
}


predicate isFixLocation(Location loc) {
    exists(Function func |
        func.getName() = target_function() and
        loc.getFile() = func.getFile() and
        loc.getStartLine() = 41
    )
}

// predicate isCfgSuccessor(ControlFlowNode node1, ControlFlowNode node2) {
//     node1.getASuccessor() = node2
//     or
//     exists(ControlFlowNode node3 |
//         isCfgSuccessor(node1, node3) and
//         isCfgSuccessor(node3, node2)
//     )
// }

predicate isBbSuccessor(BasicBlock bb1, BasicBlock bb2) {
    bb1.getASuccessor() = bb2
    or
    exists(BasicBlock bb3 |
        isBbSuccessor(bb1, bb3) and
        isBbSuccessor(bb3, bb2)
    )
}

predicate isPredessesorOfFixLoc(BasicBlock node) {
    exists(Location loc, ControlFlowNode fixLocNode, BasicBlock bb |
        isFixLocation(loc) and
        fixLocNode.getLocation() = loc and
        bb = fixLocNode.getBasicBlock() and
        isBbSuccessor(node, bb)
    )
}

predicate isExprSource(Expr node) {
    exists(Function func, Declaration decl |
        func.getName() = "swPipeBase_create" and
        decl.getName() = "object" and
        node.getEnclosingFunction() = func and
        node instanceof VariableAccess and
        // node.getEnclosingVariable().getName() = "object"
        node.(VariableAccess).getTarget() = decl and
        decl.getADeclarationLocation().getStartLine() = 32
        and isPredessesorOfFixLoc(node.getBasicBlock())
    )
}

predicate isExprSink(Expr node) {
    exists(Function func |
        func.getName() = "swPipeBase_create" 
        and node.getEnclosingFunction() = func 
        and node instanceof VariableAccess 
        and isPredessesorOfFixLoc(node.getBasicBlock())
    )
}




class TaintTrackingConfiguration extends TaintTracking::Configuration {
    TaintTrackingConfiguration() { this = "TaintTrackingConfiguration" }

    override predicate isSource(DataFlow::Node node) {
        isExprSource(node.asExpr())
    }

    override predicate isSink(DataFlow::Node node) {
        isExprSink(node.asExpr())
    }

    override predicate isAdditionalTaintStep(DataFlow::Node node1, DataFlow::Node node2) {
        exists(VariableAccess va1, VariableAccess va2 |
            va1 = node1.asExpr() and
            va2 = node2.asExpr() and
            // va1.getTarget() = va2.getTarget()
            va1.getEnclosingStmt() = va2.getEnclosingStmt()
        )
    }
}

string expandPointerFieldAccess(PointerFieldAccess fa) {
    result = fa.getQualifier().toString() + "->" + fa.toString()
}

string expandDotFieldAccess(DotFieldAccess fa) {
    result = fa.getQualifier().toString() + "." + fa.toString()
}

string getStringFromAccess(VariableAccess va) {
    if va instanceof PointerFieldAccess then
        result = expandPointerFieldAccess(va.(PointerFieldAccess))
    else if va instanceof DotFieldAccess then
        result = expandDotFieldAccess(va.(DotFieldAccess))
    else
        result = va.toString()
}

string getFinalOutput(VariableAccess va) {
    if va.getUnderlyingType().getPointerIndirectionLevel() = 0 then
        result = getStringFromAccess(va)
    else
        result = getStringFromAccess(va) + "(pointer)"
}

from TaintTrackingConfiguration config, Expr src, Expr sink, string s
where 
    config.hasFlow(DataFlow::exprNode(src), DataFlow::exprNode(sink)) and
    // ( sink instanceof FieldAccess and fa = sink.(FieldAccess)) and
    // s = expandFieldAccess(fa)
    s = getFinalOutput(sink.(VariableAccess))
select sink, "sinks are " + s

// from Location location
// // where isPredessesorOfFixLoc(bb)
// where isFixLocation(location)
// select location, "bb"

// from BasicBlock bb
// where isPredessesorOfFixLoc(bb)
// select bb, "bb"





// from Expr src, Expr sink
// // where isSource(src) and
// // where    isSink(sink) and sink instanceof VariableAccess
// where isSource(src) and isSink(sink)
// and TaintTracking::localTaint(DataFlow::exprNode(src), DataFlow::exprNode(sink))

// // and sink.getLocation().getStartLine() < 45
// // and s = sink.(VariableAccess).getTarget().getName().toString()
//     // and TaintTracking::localTaint(DataFlow::exprNode(src), DataFlow::exprNode(sink))
// // select src, "src are"
// // select sink.(VariableAccess).getTarget().getName().toString(), "sink Are"
// // select sink.(VariableAccess).getTarget (),"Sink are"
// // select sink.get
// select sink, "sink are"
