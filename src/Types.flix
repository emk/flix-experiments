// A simplified type system for SQL, with BigQuery-style arrays. Note that
// unlike BigQuery, we allow nested arrays for simplicity.
pub enum Type with Eq, Order, ToString {
    // `Inconsistent` is a super-type of all other types. It's `Top` (⊤) in our
    // lattice.
    case Inconsistent,
    case Int64,
    case Float64,
    case String,
    case Null,
    // Arrays do not inherit subtyping from their element types. Int64 is a
    // subtype of Float64, but ARRAY(Int64) is not a subtype of ARRAY(Float64).
    case Array(Type),
    // `Unknown` is a subtype of all other types. It's `Bottom` (⊥) in our
    // lattice. `ARRAY[]` has the type `ARRAY(Unknown)`.
    case Unknown
}

instance LowerBound[Type] {
    pub def minValue(): Type = Type.Unknown
}

instance UpperBound[Type] {
    pub def maxValue(): Type = Type.Inconsistent
}

instance PartialOrder[Type] {
    pub def lessEqual(x: Type, y: Type): Bool = match (x, y) {
        case (t1, t2) if t1 == t2 => true
        case (_, Type.Inconsistent) => true
        case (Type.Unknown, _) => true
        case (Type.Null, _) => true
        case (Type.Int64, Type.Float64) => true
        case (_, _) => false
    }
}

instance JoinLattice[Type] {
    pub def leastUpperBound(x: Type, y: Type): Type = match (x, y) {
        case (t1, t2) if t1 == t2 => t1
        case (Type.Inconsistent, _) => Type.Inconsistent
        case (_, Type.Inconsistent) => Type.Inconsistent
        case (Type.Unknown, t) => t
        case (t, Type.Unknown) => t
        case (Type.Null, t) => t
        case (t, Type.Null) => t
        case (Type.Int64, Type.Float64) => Type.Float64
        case _ => Type.Inconsistent
    }
}

instance MeetLattice[Type] {
    pub def greatestLowerBound(x: Type, y: Type): Type = match (x, y) {
        case (t1, t2) if t1 == t2 => t1
        case (Type.Unknown, _) => Type.Unknown
        case (_, Type.Unknown) => Type.Unknown
        case (Type.Null, _) => Type.Null
        case (_, Type.Null) => Type.Null
        case (Type.Int64, Type.Float64) => Type.Int64
        case _ => Type.Unknown
    }
}

pub trait TypeOf[t] {
    pub def typeOf(x: t): Type
}

pub enum Lit {
    case Int64(Int64),
    case Float64(Float64),
    case String(String),
    case Null
}

instance TypeOf[Lit] {
    pub def typeOf(x: Lit): Type = match x {
        case Lit.Int64(_) => Type.Int64
        case Lit.Float64(_) => Type.Float64
        case Lit.String(_) => Type.String
        case Lit.Null => Type.Null
    }
}

pub enum Expr {
    case Lit(Lit),
    case Array(List[Expr])
}

instance TypeOf[Expr] {
    pub def typeOf(x: Expr): Type = match x {
        case Expr.Lit(l) => TypeOf.typeOf(l)
        case Expr.Array(es) =>
            let et = elementType(List.map(TypeOf.typeOf, es));
            match et {
                case Type.Inconsistent => Type.Inconsistent
                case _ => Type.Array(et)
            }
    }
}

@Test
def testTypeOfLitInt64(): Bool = Assert.eq(
    TypeOf.typeOf(Expr.Lit(Lit.Int64(42i64))),
    Type.Int64
)

@Test
def testTypeOfSimpleArray(): Bool = Assert.eq(
    TypeOf.typeOf(Expr.Array(Expr.Lit(Lit.Int64(42i64)) :: Nil)),
    Type.Array(Type.Int64)
)

@Test
def testTypeOfEmptyArray(): Bool = Assert.eq(
    TypeOf.typeOf(Expr.Array(Nil)),
    Type.Array(Type.Unknown)
)

@Test
def testTypeOfComplexArray(): Bool = Assert.eq(
    // ARRAY[42, 3.14, NULL] -> ARRAY[FLOAT64]
    TypeOf.typeOf(Expr.Array(
        Expr.Lit(Lit.Int64(42i64)) ::
        Expr.Lit(Lit.Float64(3.14f64)) ::
        Expr.Lit(Lit.Null) ::
        Nil
    )),
    Type.Array(Type.Float64)
)

@Test
def testTypeOfInconsistentArray(): Bool = Assert.eq(
    // ARRAY[42, 3.14, NULL] -> ARRAY[FLOAT64]
    TypeOf.typeOf(Expr.Array(
        Expr.Lit(Lit.Int64(42i64)) ::
        Expr.Lit(Lit.String("foo")) ::
        Nil
    )),
    Type.Inconsistent
)

def elementType(es: List[Type]): Type =
    let arg_types = inject es into ArgType;
    let elem_type = #{
        ElemType(; t: Type) :- ArgType(t).
    };
    let elem_types = query elem_type, arg_types select t from ElemType(; t);
    if (Vector.isEmpty(elem_types))
        Type.Unknown
    else
        Vector.get(0, elem_types)

