from __future__ import annotations
import sys
from mypy.nodes import (
    GDEF,
    MypyFile,
    FuncDef,
    ClassDef,
    AssignmentStmt,
    Decorator,
    OverloadedFuncDef,
    NameExpr,
    MemberExpr,
    Import,
    ImportFrom,
    ImportAll,
    Block,
    ExpressionStmt,
    ReturnStmt,
    IfStmt,
    WhileStmt,
    ForStmt,
    TryStmt,
    WithStmt,
    RaiseStmt,
    BreakStmt,
    ContinueStmt,
    DelStmt,
    AssertStmt,
    PassStmt,
    GlobalDecl,
    NonlocalDecl,
    OperatorAssignmentStmt,
    MatchStmt,
    IntExpr,
    StrExpr,
    FloatExpr,
    BytesExpr,
    ComplexExpr,
    EllipsisExpr,
    CallExpr,
    OpExpr,
    UnaryExpr,
    ComparisonExpr,
    IndexExpr,
    SliceExpr,
    ListExpr,
    TupleExpr,
    SetExpr,
    DictExpr,
    ConditionalExpr,
    StarExpr,
    YieldExpr,
    YieldFromExpr,
    AwaitExpr,
    AssignmentExpr,
    LambdaExpr,
    SuperExpr,
    ListComprehension,
    SetComprehension,
    DictionaryComprehension,
    GeneratorExpr,
    TempNode,
    Expression,
    ARG_POS,
    ARG_OPT,
    ARG_STAR,
    ARG_STAR2,
)
from mypy.patterns import (
    AsPattern,
    ClassPattern,
    OrPattern,
    SingletonPattern,
    ValuePattern,
)
from mypy.types import CallableType
from mypy.util import correct_relative_import
from pir_server.proto import pir_pb2
from pir_server.builder.type_mapper import TypeMapper


def _sanitize_surrogates(value: str) -> str:
    return value.encode("utf-8", errors="backslashreplace").decode("utf-8")


class AstSerializer:
    def __init__(self, tree: MypyFile, module_name: str):
        self.tree = tree
        self.module_name = module_name
        self.type_mapper = TypeMapper()
        self.dropped: list[str] = []
        self.unsupported_exprs: set[str] = set()

    def serialize(self, proto: pir_pb2.MypyModuleProto) -> None:
        proto.name = self.module_name
        proto.path = self.tree.path or ""
        for defn in self.tree.defs:
            start = len(proto.defs)
            try:
                self._serialize_definitions(defn, proto.defs)
            except Exception as e:
                del proto.defs[start:]
                self.dropped.append(self._dropped_message(e))
        proto.errors.extend(self.dropped)

    def _dropped_message(self, e: Exception) -> str:
        message = f"Dropped definition in {self.module_name}: {type(e).__name__}: {e}"
        print(f"WARNING: {message}", file=sys.stderr)
        return message

    def _unsupported_expr(self, expr: Expression) -> None:
        kind = type(expr).__name__
        if kind in self.unsupported_exprs:
            return
        self.unsupported_exprs.add(kind)
        message = f"Unsupported expression {kind} in {self.module_name}"
        print(f"WARNING: {message}", file=sys.stderr)
        self.dropped.append(message)

    def _serialize_definitions(
        self, defn, container, enclosing_class: str | None = None
    ) -> None:
        """Serialize a definition into `container` (usually 1 entry, but OverloadedFuncDef may produce multiple).

        `enclosing_class` carries the dotted class chain *without* the module
        prefix — e.g. `"Outer"` for a class nested in `Outer`, or
        `"Outer.Inner"` for a method on `Outer.Inner`. `_serialize_func_def`
        prepends the module name; `_serialize_class_def` does the same.
        """
        if isinstance(defn, ClassDef):
            self._serialize_class_def(defn, container.add().class_def, enclosing_class)
        elif isinstance(defn, Decorator):
            self._serialize_decorator_def(
                defn, container.add().decorator, enclosing_class
            )
        elif isinstance(defn, FuncDef):
            self._serialize_func_def(defn, container.add().func_def, enclosing_class)
        elif isinstance(defn, OverloadedFuncDef):
            if defn.impl is not None:
                self._serialize_definitions(defn.impl, container, enclosing_class)
                return
            for item in defn.items:
                self._serialize_definitions(item, container, enclosing_class)
        elif isinstance(defn, AssignmentStmt):
            if not self._serialize_stmt(defn, container.add().assignment):
                del container[-1]
        elif isinstance(defn, (Import, ImportFrom)):
            # Module-level Import / ImportFrom ride the `assignment` slot (typed MypyStmtProto,
            # so it accepts any statement variant).
            if not self._serialize_stmt(defn, container.add().assignment):
                del container[-1]

    def _serialize_class_def(
        self, class_def: ClassDef, out, enclosing_class: str | None = None
    ) -> None:
        own_qualifier = (
            f"{enclosing_class}.{class_def.name}" if enclosing_class else class_def.name
        )
        out.name = class_def.name
        out.fullname = class_def.fullname or f"{self.module_name}.{own_qualifier}"

        if class_def.info:
            for base in class_def.info.bases:
                if hasattr(base, "type") and hasattr(base.type, "fullname"):
                    out.base_classes.append(base.type.fullname)
            if hasattr(class_def.info, "mro") and class_def.info.mro:
                for mro_item in class_def.info.mro:
                    out.mro.append(mro_item.fullname)
            out.is_abstract = class_def.info.is_abstract
            out.is_enum = class_def.info.is_enum
            if (
                hasattr(class_def.info, "metadata")
                and "dataclass" in class_def.info.metadata
            ):
                out.is_dataclass = True

        # Unlike Decorator.decorators for methods, mypy's semantic analyzer does NOT strip
        # entries from ClassDef.decorators, so the raw expression list is safe to read.
        for dec_expr in class_def.decorators:
            self._serialize_decorator_info(dec_expr, out.decorators.add())

        for defn in class_def.defs.body:
            self._serialize_definitions(defn, out.body, enclosing_class=own_qualifier)

    def _decorator_names(self, expr: Expression) -> tuple[str, str]:
        if isinstance(expr, CallExpr):
            return self._decorator_names(expr.callee)
        if isinstance(expr, NameExpr):
            fullname = getattr(expr, "fullname", "") or ""
            return expr.name, fullname or expr.name
        if isinstance(expr, MemberExpr):
            fullname = getattr(expr, "fullname", "") or ""
            return expr.name, fullname or self._member_expr_dotted_path(expr)
        return "<unknown>", "<unknown>"

    def _serialize_decorator_info(self, expr: Expression, out) -> None:
        """Unwrap a decorator expression into a MypyDecoratorInfoProto summary.

        Mirrors the Kotlin `flatDecoratorFromExpr` unwrap (NameExpr / MemberExpr / CallExpr)
        so class-side and method-side decorators report identical {name, qualified_name}
        shapes. Argument stringification mirrors the Kotlin `exprRepr` behavior:
        literals → their text; names/members → dotted path; otherwise "<expr>".
        Keyword-arg names on CallExpr decorators are dropped (pre-existing Stage 1 nit).
        """
        out.name, out.qualified_name = self._decorator_names(expr)
        if isinstance(expr, CallExpr):
            for arg in expr.args:
                out.arguments.append(self._decorator_arg_repr(arg))

    def _member_expr_dotted_path(self, expr: MemberExpr) -> str:
        base = expr.expr
        if isinstance(base, NameExpr):
            prefix = getattr(base, "fullname", "") or base.name
        elif isinstance(base, MemberExpr):
            prefix = self._member_expr_dotted_path(base)
        else:
            prefix = "<expr>"
        return f"{prefix}.{expr.name}"

    def _decorator_arg_repr(self, expr: Expression) -> str:
        if isinstance(expr, IntExpr):
            return str(expr.value)
        if isinstance(expr, StrExpr):
            return f'"{self._escape_str_literal(expr.value)}"'
        if isinstance(expr, FloatExpr):
            return str(expr.value)
        if isinstance(expr, BytesExpr):
            return f'b"{self._escape_str_literal(expr.value)}"'
        if isinstance(expr, ComplexExpr):
            return f"{expr.value.real}+{expr.value.imag}j"
        if isinstance(expr, EllipsisExpr):
            return "..."
        if isinstance(expr, NameExpr):
            return expr.name
        if isinstance(expr, MemberExpr):
            return self._member_expr_dotted_path(expr)
        return "<expr>"

    @staticmethod
    def _escape_str_literal(s: str) -> str:
        return _sanitize_surrogates(s).replace("\\", "\\\\").replace('"', '\\"')

    def _serialize_func_def(
        self, func_def: FuncDef, out, enclosing_class: str | None = None
    ) -> None:
        native_fullname = getattr(func_def, "fullname", "") or ""
        if enclosing_class:
            fullname = f"{self.module_name}.{enclosing_class}.{func_def.name}"
        elif native_fullname and "." in native_fullname:
            fullname = native_fullname
        else:
            fullname = f"{self.module_name}.{func_def.name}"

        out.name = func_def.name
        out.fullname = fullname
        out.is_async = func_def.is_coroutine
        out.is_generator = func_def.is_generator
        out.line = getattr(func_def, "line", -1)

        if func_def.body:
            self._serialize_block(func_def.body, out.body)

        for arg in func_def.arguments:
            self._serialize_argument(arg, out.arguments.add())

        func_type = func_def.type
        if isinstance(func_type, CallableType):
            self.type_mapper.map(func_type.ret_type, out.return_type)

    def _serialize_decorator_def(
        self, dec: Decorator, out, enclosing_class: str | None = None
    ) -> None:
        out.name = dec.func.name
        self._serialize_func_def(dec.func, out.func, enclosing_class)
        # Serialize the pristine decorator list. mypy's semantic analyzer strips
        # @staticmethod / @classmethod / @property from `dec.decorators` (encoding
        # them onto `func.is_static` etc.) — so iterating that list would lose them.
        # `dec.original_decorators` is the untouched list.
        for d in dec.original_decorators:
            self._serialize_expr(d, out.original_decorators.add())
        if dec.func.fullname:
            out.qualified_name = dec.func.fullname

    def _serialize_argument(self, arg, out) -> None:
        out.name = arg.variable.name if arg.variable else ""
        out.kind = int(arg.kind.value)
        out.has_default = arg.initializer is not None
        if arg.variable and arg.variable.type:
            self.type_mapper.map(arg.variable.type, out.type)
        if arg.initializer:
            self._serialize_expr(arg.initializer, out.default_value)

    def _serialize_block(self, block: Block, out) -> None:
        out.SetInParent()
        for stmt in block.body:
            if not self._serialize_stmt(stmt, out.stmts.add()):
                del out.stmts[-1]

    def _serialize_stmt(self, stmt, out) -> bool:
        if isinstance(stmt, AssignmentStmt):
            self._serialize_assignment_stmt(stmt, out.assignment)
        elif isinstance(stmt, OperatorAssignmentStmt):
            op_assignment = out.op_assignment
            op_assignment.op = stmt.op
            self._serialize_expr(stmt.lvalue, op_assignment.lvalue)
            self._serialize_expr(stmt.rvalue, op_assignment.rvalue)
        elif isinstance(stmt, ExpressionStmt):
            self._serialize_expr(stmt.expr, out.expression_stmt.expr)
        elif isinstance(stmt, ReturnStmt):
            return_stmt = out.return_stmt
            return_stmt.SetInParent()
            if stmt.expr:
                self._serialize_expr(stmt.expr, return_stmt.expr)
        elif isinstance(stmt, IfStmt):
            if_stmt = out.if_stmt
            if_stmt.SetInParent()
            for cond in stmt.expr:
                self._serialize_expr(cond, if_stmt.conditions.add())
            for body in stmt.body:
                self._serialize_block(body, if_stmt.bodies.add())
            if stmt.else_body:
                self._serialize_block(stmt.else_body, if_stmt.else_body)
        elif isinstance(stmt, WhileStmt):
            while_stmt = out.while_stmt
            self._serialize_expr(stmt.expr, while_stmt.condition)
            self._serialize_block(stmt.body, while_stmt.body)
            if stmt.else_body:
                self._serialize_block(stmt.else_body, while_stmt.else_body)
        elif isinstance(stmt, ForStmt):
            for_stmt = out.for_stmt
            self._serialize_expr(stmt.index, for_stmt.index)
            self._serialize_expr(stmt.expr, for_stmt.iterable)
            self._serialize_block(stmt.body, for_stmt.body)
            if stmt.else_body:
                self._serialize_block(stmt.else_body, for_stmt.else_body)
        elif isinstance(stmt, MatchStmt):
            match_stmt = out.match_stmt
            self._serialize_expr(stmt.subject, match_stmt.subject)
            for pattern, guard, body in zip(stmt.patterns, stmt.guards, stmt.bodies):
                self._serialize_pattern(pattern, match_stmt.patterns.add())
                if guard is not None:
                    self._serialize_expr(guard, match_stmt.guards.add())
                else:
                    match_stmt.guards.add()
                self._serialize_block(body, match_stmt.bodies.add())
        elif isinstance(stmt, TryStmt):
            try_stmt = out.try_stmt
            self._serialize_block(stmt.body, try_stmt.body)
            for t in stmt.types:
                if t is not None:
                    self._serialize_expr(t, try_stmt.types.add())
                else:
                    try_stmt.types.add()
            for v in stmt.vars:
                if v is not None:
                    self._serialize_expr(v, try_stmt.vars.add())
                else:
                    try_stmt.vars.add()
            for h in stmt.handlers:
                self._serialize_block(h, try_stmt.handlers.add())
            if stmt.else_body:
                self._serialize_block(stmt.else_body, try_stmt.else_body)
            if stmt.finally_body:
                self._serialize_block(stmt.finally_body, try_stmt.finally_body)
        elif isinstance(stmt, WithStmt):
            with_stmt = out.with_stmt
            with_stmt.is_async = getattr(stmt, "is_async", False)
            self._serialize_block(stmt.body, with_stmt.body)
            for expr in stmt.expr:
                self._serialize_expr(expr, with_stmt.exprs.add())
            if stmt.target:
                for t in stmt.target:
                    if t is not None:
                        self._serialize_expr(t, with_stmt.targets.add())
                    else:
                        with_stmt.targets.add()
        elif isinstance(stmt, RaiseStmt):
            raise_stmt = out.raise_stmt
            raise_stmt.SetInParent()
            if stmt.expr:
                self._serialize_expr(stmt.expr, raise_stmt.expr)
            if stmt.from_expr:
                self._serialize_expr(stmt.from_expr, raise_stmt.from_expr)
        elif isinstance(stmt, BreakStmt):
            out.break_stmt.SetInParent()
        elif isinstance(stmt, ContinueStmt):
            out.continue_stmt.SetInParent()
        elif isinstance(stmt, DelStmt):
            self._serialize_expr(stmt.expr, out.del_stmt.expr)
        elif isinstance(stmt, AssertStmt):
            assert_stmt = out.assert_stmt
            self._serialize_expr(stmt.expr, assert_stmt.expr)
            if stmt.msg:
                self._serialize_expr(stmt.msg, assert_stmt.msg)
        elif isinstance(stmt, PassStmt):
            out.pass_stmt.SetInParent()
        elif isinstance(stmt, GlobalDecl):
            out.global_decl.names.extend(stmt.names)
        elif isinstance(stmt, Decorator):
            # Nested decorated-def: preserve the decorator expressions so the Kotlin
            # side can lift them into FlatFunctionIR.decorators. Routing this as a
            # FuncDef (via _unwrap_func) would drop the decorators silently.
            self._serialize_decorator_def(stmt, out.decorator)
        elif isinstance(stmt, (FuncDef, OverloadedFuncDef)):
            func_def = self._unwrap_func(stmt)
            if func_def:
                self._serialize_func_def(func_def, out.func_def)
        elif isinstance(stmt, ClassDef):
            self._serialize_class_def(stmt, out.class_def)
        elif isinstance(stmt, NonlocalDecl):
            out.nonlocal_decl.names.extend(stmt.names)
        elif isinstance(stmt, Import):
            import_stmt = out.import_stmt
            import_stmt.SetInParent()
            for module_id, as_id in stmt.ids:
                import_id = import_stmt.ids.add()
                import_id.module = module_id
                import_id.alias = as_id or ""
        elif isinstance(stmt, ImportFrom):
            resolved_module, ok = correct_relative_import(
                cur_mod_id=self.module_name,
                relative=stmt.relative,
                target=stmt.id,
                is_cur_package_init_file=self.tree.is_package_init_file(),
            )
            if not ok:
                # Over-relative import — mypy itself errors here. The
                # `correct_relative_import` helper still returns a string but
                # it's composed from negative-indexed slicing and may not be a
                # real module path. Fall back to the raw target so downstream
                # FlatGlobalRefs at least carry a recognizable prefix.
                resolved_module = stmt.id
            import_from_stmt = out.import_from_stmt
            import_from_stmt.module = resolved_module
            import_from_stmt.relative = stmt.relative
            for name, as_name in stmt.names:
                import_name = import_from_stmt.names.add()
                import_name.name = name
                import_name.alias = as_name or ""
        elif isinstance(stmt, ImportAll):
            return False
        elif isinstance(stmt, Block):
            return False
        else:
            return False

        out.line = getattr(stmt, "line", -1)
        out.col = getattr(stmt, "column", 0)
        # Mypy uses None / missing attribute for unknown end coords; -1 is the
        # wire-level sentinel. A literal 0 is a legitimate (if unusual) value
        # and must not be collapsed to -1.
        end_line = getattr(stmt, "end_line", None)
        if end_line is None:
            end_line = -1
        end_col = getattr(stmt, "end_column", None)
        if end_col is None:
            end_col = -1
        out.end_line = end_line
        out.end_col = end_col
        return True

    SINGLETON_VALUES = {
        None: pir_pb2.MypySingletonPatternProto.NONE,
        True: pir_pb2.MypySingletonPatternProto.TRUE,
        False: pir_pb2.MypySingletonPatternProto.FALSE,
    }

    def _serialize_pattern(self, pattern, out) -> None:
        if isinstance(pattern, AsPattern):
            as_pattern = out.as_pattern
            as_pattern.SetInParent()
            if pattern.pattern is not None:
                self._serialize_pattern(pattern.pattern, as_pattern.pattern)
            if pattern.name is not None:
                as_pattern.name = pattern.name.name
        elif isinstance(pattern, ValuePattern):
            self._serialize_expr(pattern.expr, out.value_pattern.expr)
        elif isinstance(pattern, OrPattern):
            or_pattern = out.or_pattern
            or_pattern.SetInParent()
            for alternative in pattern.patterns:
                self._serialize_pattern(alternative, or_pattern.patterns.add())
        elif isinstance(pattern, ClassPattern):
            self._serialize_expr(pattern.class_ref, out.class_pattern.class_ref)
        elif isinstance(pattern, SingletonPattern):
            singleton = self.SINGLETON_VALUES.get(pattern.value)
            if singleton is None:
                self._unknown_pattern(pattern, out)
                return
            out.singleton_pattern.value = singleton
        else:
            self._unknown_pattern(pattern, out)

    def _unknown_pattern(self, pattern, out) -> None:
        out.unknown_pattern.kind = type(pattern).__name__

    def _serialize_assignment_stmt(self, stmt: AssignmentStmt, out) -> None:
        if not isinstance(stmt.rvalue, TempNode):
            self._serialize_expr(stmt.rvalue, out.rvalue)
        for lvalue in stmt.lvalues:
            self._serialize_expr(lvalue, out.lvalues.add())
        if stmt.type is not None:
            self.type_mapper.map(stmt.type, out.type_annotation)

    def _serialize_expr(self, expr: Expression, out) -> None:
        if expr is None:
            out.SetInParent()
            return

        self._serialize_expr_inner(expr, out)

    def _serialize_expr_inner(self, expr: Expression, out) -> None:
        out.line = getattr(expr, "line", -1)
        out.col = getattr(expr, "column", 0)
        end_line = getattr(expr, "end_line", None)
        if end_line is None:
            end_line = -1
        end_col = getattr(expr, "end_column", None)
        if end_col is None:
            end_col = -1
        out.end_line = end_line
        out.end_col = end_col

        if isinstance(expr, IntExpr):
            int_expr = out.int_expr
            if -(2**63) <= expr.value <= 2**63 - 1:
                int_expr.value = expr.value
            else:
                int_expr.str_value = str(expr.value)
        elif isinstance(expr, StrExpr):
            try:
                out.str_expr.value = expr.value
            except UnicodeEncodeError:
                out.str_expr.value = _sanitize_surrogates(expr.value)
        elif isinstance(expr, FloatExpr):
            out.float_expr.value = expr.value
        elif isinstance(expr, BytesExpr):
            out.bytes_expr.value = expr.value.encode("latin-1", errors="replace")
        elif isinstance(expr, ComplexExpr):
            complex_expr = out.complex_expr
            complex_expr.real = expr.value.real
            complex_expr.imag = expr.value.imag
        elif isinstance(expr, EllipsisExpr):
            out.ellipsis_expr.SetInParent()
        elif isinstance(expr, NameExpr):
            name_expr = out.name_expr
            name_expr.name = expr.name
            fullname = ""
            if expr.node is not None:
                fullname = getattr(expr.node, "fullname", "") or ""
            name_expr.fullname = fullname
            # mypy's `kind` (LDEF/GDEF/MDEF) is what distinguishes a local from a
            # module-level/imported binding; without it the Kotlin side would have to guess from
            # `fullname` shape and would misclassify `import os` (fullname == "os") as a local.
            # A resolved MypyFile node means the name IS a module reference, emitted as
            # NAME_MODULE. Unresolved names leave `kind=None` and fall back to NAME_LOCAL.
            if isinstance(expr.node, MypyFile):
                name_expr.name_kind = pir_pb2.NAME_MODULE
            elif expr.kind == GDEF:
                name_expr.name_kind = pir_pb2.NAME_GLOBAL
            else:
                name_expr.name_kind = pir_pb2.NAME_LOCAL
        elif isinstance(expr, MemberExpr):
            member_expr = out.member_expr
            member_expr.name = expr.name
            self._serialize_expr(expr.expr, member_expr.expr)
            if expr.node is not None and hasattr(expr.node, "fullname"):
                member_expr.fullname = expr.node.fullname or ""
        elif isinstance(expr, CallExpr):
            call_expr = out.call_expr
            self._serialize_expr(expr.callee, call_expr.callee)
            resolved = ""
            if hasattr(expr.callee, "node"):
                node = expr.callee.node
                if node is not None and hasattr(node, "fullname"):
                    resolved = node.fullname or ""
            if resolved:
                call_expr.resolved_callee = resolved
            for i, arg_expr in enumerate(expr.args):
                kind = int(expr.arg_kinds[i].value)
                name = expr.arg_names[i] if expr.arg_names else None
                arg = call_expr.args.add()
                arg.kind = kind
                arg.name = name or ""
                self._serialize_expr(arg_expr, arg.expr)
        elif isinstance(expr, OpExpr):
            op_expr = out.op_expr
            op_expr.op = expr.op
            self._serialize_expr(expr.left, op_expr.left)
            self._serialize_expr(expr.right, op_expr.right)
        elif isinstance(expr, UnaryExpr):
            unary_expr = out.unary_expr
            unary_expr.op = expr.op
            self._serialize_expr(expr.expr, unary_expr.expr)
        elif isinstance(expr, ComparisonExpr):
            comparison_expr = out.comparison_expr
            comparison_expr.operators.extend(expr.operators)
            for operand in expr.operands:
                self._serialize_expr(operand, comparison_expr.operands.add())
        elif isinstance(expr, IndexExpr):
            index_expr = out.index_expr
            self._serialize_expr(expr.base, index_expr.base)
            self._serialize_expr(expr.index, index_expr.index)
        elif isinstance(expr, SliceExpr):
            slice_expr = out.slice_expr
            slice_expr.SetInParent()
            if expr.begin_index:
                self._serialize_expr(expr.begin_index, slice_expr.begin)
            if expr.end_index:
                self._serialize_expr(expr.end_index, slice_expr.end)
            if expr.stride:
                self._serialize_expr(expr.stride, slice_expr.stride)
        elif isinstance(expr, ListExpr):
            list_expr = out.list_expr
            list_expr.SetInParent()
            for item in expr.items:
                self._serialize_expr(item, list_expr.items.add())
        elif isinstance(expr, TupleExpr):
            tuple_expr = out.tuple_expr
            tuple_expr.SetInParent()
            for item in expr.items:
                self._serialize_expr(item, tuple_expr.items.add())
        elif isinstance(expr, SetExpr):
            set_expr = out.set_expr
            set_expr.SetInParent()
            for item in expr.items:
                self._serialize_expr(item, set_expr.items.add())
        elif isinstance(expr, DictExpr):
            dict_expr = out.dict_expr
            dict_expr.SetInParent()
            for k, v in expr.items:
                if k is not None:
                    self._serialize_expr(k, dict_expr.keys.add())
                else:
                    dict_expr.keys.add()
                self._serialize_expr(v, dict_expr.values.add())
        elif isinstance(expr, ConditionalExpr):
            conditional_expr = out.conditional_expr
            self._serialize_expr(expr.cond, conditional_expr.cond)
            self._serialize_expr(expr.if_expr, conditional_expr.if_expr)
            self._serialize_expr(expr.else_expr, conditional_expr.else_expr)
        elif isinstance(expr, StarExpr):
            self._serialize_expr(expr.expr, out.star_expr.expr)
        elif isinstance(expr, YieldExpr):
            yield_expr = out.yield_expr
            yield_expr.SetInParent()
            if expr.expr:
                self._serialize_expr(expr.expr, yield_expr.expr)
        elif isinstance(expr, YieldFromExpr):
            self._serialize_expr(expr.expr, out.yield_from_expr.expr)
        elif isinstance(expr, AwaitExpr):
            self._serialize_expr(expr.expr, out.await_expr.expr)
        elif isinstance(expr, AssignmentExpr):
            assignment_expr = out.assignment_expr
            self._serialize_expr(expr.target, assignment_expr.target)
            self._serialize_expr(expr.value, assignment_expr.value)
        elif isinstance(expr, LambdaExpr):
            lambda_expr = out.lambda_expr
            lambda_expr.SetInParent()
            for arg in expr.arguments:
                self._serialize_argument(arg, lambda_expr.arguments.add())
            if expr.body:
                self._serialize_block(expr.body, lambda_expr.body)
            func_type = expr.type
            if isinstance(func_type, CallableType):
                self.type_mapper.map(func_type.ret_type, lambda_expr.return_type)
        elif isinstance(expr, SuperExpr):
            out.super_expr.SetInParent()
        elif isinstance(expr, ListComprehension):
            self._serialize_generator_expr(
                expr.generator, out.list_comprehension.generator
            )
        elif isinstance(expr, SetComprehension):
            self._serialize_generator_expr(
                expr.generator, out.set_comprehension.generator
            )
        elif isinstance(expr, DictionaryComprehension):
            dict_comprehension = out.dict_comprehension
            self._serialize_expr(expr.key, dict_comprehension.key)
            self._serialize_expr(expr.value, dict_comprehension.value)
            for idx in expr.indices:
                self._serialize_expr(idx, dict_comprehension.indices.add())
            for seq in expr.sequences:
                self._serialize_expr(seq, dict_comprehension.sequences.add())
            for conds in expr.condlists:
                cl = dict_comprehension.condlists.add()
                for c in conds:
                    self._serialize_expr(c, cl.conditions.add())
        elif isinstance(expr, GeneratorExpr):
            self._serialize_generator_expr(expr, out.generator_expr)
        else:
            self._unsupported_expr(expr)

    def _serialize_generator_expr(self, gen: GeneratorExpr, out) -> None:
        self._serialize_expr(gen.left_expr, out.left_expr)
        for idx in gen.indices:
            self._serialize_expr(idx, out.indices.add())
        for seq in gen.sequences:
            self._serialize_expr(seq, out.sequences.add())
        for conds in gen.condlists:
            cl = out.condlists.add()
            for c in conds:
                self._serialize_expr(c, cl.conditions.add())

    def _unwrap_func(self, defn) -> FuncDef | None:
        if isinstance(defn, FuncDef):
            return defn
        elif isinstance(defn, Decorator):
            return defn.func
        elif isinstance(defn, OverloadedFuncDef):
            if defn.impl is not None:
                return self._unwrap_func(defn.impl)
            if defn.items:
                return self._unwrap_func(defn.items[0])
        return None
