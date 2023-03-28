/**
 * @kind problem
 * @problem.severity warning
 * @id cpp/exit-stmts
 */


import cpp

string target_function() { result = "swPipeBase_create" }

predicate is_target_function(Function func) {
    func.getName() = target_function()
}

predicate func_in_src_files(Function func) {
    func.fromSource() and
    func.getFile().getExtension() = "c"
}

predicate func_has_return_type(Function func, Type target_type) {
    func_in_src_files(func) and
    func.getUnspecifiedType() = target_type
}

predicate is_return_stmt_for_func(ReturnStmt rs, Function func) {
    rs.getEnclosingFunction() = func
}

predicate is_returning_constant(ReturnStmt rs) {
    not rs.hasExpr() or 
    (
        rs.hasExpr() and
        rs.getExpr().isConstant()
    )
}

string print_rs(ReturnStmt rs) {
    if rs.hasExpr()
    // use this version to get evaled value printed
    // then result = "return " + rs.getExpr().getValue().toString() + ";"
    then result = "return " + rs.getExpr().getValueText().toString() + ";"
    else result = "return;"
}

from Function target_func, Function selected_func, Type target_type, ReturnStmt rs
where is_target_function(target_func) and
    target_type = target_func.getUnspecifiedType() and
    func_has_return_type(selected_func, target_type) and
    is_return_stmt_for_func(rs, selected_func) and
    is_returning_constant(rs)
select rs, print_rs(rs)
