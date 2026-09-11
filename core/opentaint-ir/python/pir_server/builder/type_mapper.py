from __future__ import annotations
from mypy.types import (
    Type,
    Instance,
    CallableType,
    UnionType,
    TupleType,
    NoneType,
    AnyType,
    UninhabitedType,
    TypeVarType,
    LiteralType,
    get_proper_type,
)
from pir_server.proto import pir_pb2


class TypeMapper:
    MAX_DEPTH = 10

    def __init__(self):
        self._depth = 0

    def map(self, typ: Type | None, out: pir_pb2.PIRTypeProto) -> None:
        out.SetInParent()
        if typ is None:
            out.any_type.SetInParent()
            return

        self._depth += 1
        if self._depth > self.MAX_DEPTH:
            self._depth -= 1
            out.any_type.SetInParent()
            return

        try:
            self._map_inner(typ, out)
        finally:
            self._depth -= 1

    def _map_inner(self, typ: Type, out: pir_pb2.PIRTypeProto) -> None:
        typ = get_proper_type(typ)

        if isinstance(typ, Instance):
            ct = out.class_type
            ct.qualified_name = typ.type.fullname
            for arg in typ.args:
                self.map(arg, ct.type_args.add())

        elif isinstance(typ, CallableType):
            ft = out.function_type
            self.map(typ.ret_type, ft.return_type)
            for arg_type in typ.arg_types:
                self.map(arg_type, ft.param_types.add())

        elif isinstance(typ, UnionType):
            ut = out.union_type
            ut.SetInParent()
            for item in typ.items:
                self.map(item, ut.members.add())

        elif isinstance(typ, TupleType):
            tt = out.tuple_type
            tt.SetInParent()
            for item in typ.items:
                self.map(item, tt.element_types.add())

        elif isinstance(typ, NoneType):
            out.none_type.SetInParent()

        elif isinstance(typ, AnyType):
            out.any_type.SetInParent()

        elif isinstance(typ, UninhabitedType):
            out.never_type.SetInParent()

        elif isinstance(typ, TypeVarType):
            tv = out.type_var_type
            tv.name = typ.name
            if typ.upper_bound:
                self.map(typ.upper_bound, tv.bounds.add())

        elif isinstance(typ, LiteralType):
            lt = out.literal_type
            lt.value = str(typ.value)
            self.map(typ.fallback, lt.base_type)

        else:
            out.any_type.SetInParent()
