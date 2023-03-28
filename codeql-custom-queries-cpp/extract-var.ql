/**
 * @kind problem
 * @problem.severity warning
 * @id cpp/patch-ingredients
 */

import cpp
import semmle.code.cpp.commons.Dependency
import semmle.code.cpp.Function
import semmle.code.cpp.controlflow.StackVariableReachability
import semmle.code.cpp.dataflow.TaintTracking

// predicate nodeInFunc(Expr node) {
//     exists(Function func |
//         func.getName() = "swPipeBase_create" |
//         node.getEnclosingFunction() = func
//     )
// }
// predicate nodeOnTargetLine(Expr node) {
//     exists(Function func, Location loc |
//         func.getName() = "swPipeBase_create" and
//         loc.getFile() = func.getFile() and
//         loc.getStartLine() = 33 and
//         node.getLocation() = loc
//     )
// }
string target_function() { result = "swPipeBase_create" }

/* line where the target variable is initialized. */
int taint_src_line() { result = 32 }

/* line where the fix location is. */
int taint_sink_line() { result = 41 }

predicate isFixLocation(Location loc) {
  exists(Function func |
    func.getName() = target_function() and
    loc.getFile() = func.getFile() and
    loc.getStartLine() = taint_sink_line()
  )
}

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

predicate isAccessInTargetFunction(VariableAccess node) {
    exists(Function func |
        func.getName() = target_function() and
        node.getEnclosingFunction() = func
    )
}

predicate isExprSource(Expr node) {
  exists(Declaration decl |
    isAccessInTargetFunction(node.(VariableAccess)) and
    decl.getADeclarationLocation().getStartLine() = taint_src_line() and
    // decl.getName() = target_object() and
    node.(VariableAccess).getTarget() = decl and
    isPredessesorOfFixLoc(node.getBasicBlock())
  )
}

predicate isExprSink(Expr node) {
    isAccessInTargetFunction(node.(VariableAccess)) and
    isPredessesorOfFixLoc(node.getBasicBlock())
}

class TaintTrackingConfiguration extends TaintTracking::Configuration {
  TaintTrackingConfiguration() { this = "TaintTrackingConfiguration" }

  override predicate isSource(DataFlow::Node node) { isExprSource(node.asExpr()) }

  override predicate isSink(DataFlow::Node node) { isExprSink(node.asExpr()) }

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
  if not (fa.getQualifier() instanceof PointerFieldAccess) then
    result = fa.getQualifier().toString() + "->" + fa.toString()
  else
    result = expandPointerFieldAccess(fa.getQualifier()) + "->" + fa.toString()
}

string expandDotFieldAccess(DotFieldAccess fa) {
  if not (fa.getQualifier() instanceof DotFieldAccess) then
    result = fa.getQualifier().toString() + "." + fa.toString()
  else
    result = expandDotFieldAccess(fa.getQualifier()) + "." + fa.toString()
}

string getStringFromAccess(VariableAccess va) {
  if va instanceof PointerFieldAccess
  then result = expandPointerFieldAccess(va.(PointerFieldAccess))
  else
    if va instanceof DotFieldAccess
    then result = expandDotFieldAccess(va.(DotFieldAccess))
    else result = va.toString()
}

predicate is_va_pointer_type(VariableAccess va) {
va.getUnspecifiedType() instanceof PointerType or
va.getUnspecifiedType() instanceof ArrayType
}

string getFinalOutput(VariableAccess va) {
if is_va_pointer_type(va)
then result = "pointer(" + getStringFromAccess(va) + ")"
else result = "non-pointer(" + getStringFromAccess(va) + ")"
}

from TaintTrackingConfiguration config, Expr src, Expr sink, string s
where
  config.hasFlow(DataFlow::exprNode(src), DataFlow::exprNode(sink)) and
  // ( sink instanceof FieldAccess and fa = sink.(FieldAccess)) and
  // s = expandFieldAccess(fa)
  s = getFinalOutput(sink.(VariableAccess))
select sink, s
