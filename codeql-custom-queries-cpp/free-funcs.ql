/**
 * @kind problem
 * @problem.severity warning
 * @id cpp/free-funcs
 */


import cpp

predicate func_in_src_files(Function func) {
    func.fromSource() and
    func.getFile().getExtension() = "c"
}

predicate func_name_is_free(Function func) {
    func.getName().matches("%free")
}

predicate func_has_one_param(Function func) {
    func.getDefinition().getNumberOfParameters() = 1
}

predicate func_has_one_pointer_param(Function func) {
    func_has_one_param(func) and
    func.getAParameter().getUnspecifiedType() instanceof PointerType
}

from Function func
where func_in_src_files(func) and
    func_name_is_free(func) and
    func_has_one_pointer_param(func)
select func, func.getName()
