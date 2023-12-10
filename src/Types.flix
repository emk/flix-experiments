/// A simplified type system for SQL, with BigQuery-style arrays. Note that
/// unlike BigQuery, we allow nested arrays for simplicity.
pub enum Type with Eq, Order, ToString {
    /// Top is a supertype of all types. But since we can't represent that in /
    /// SQL, it means that we couldn't infer a consistent type for an expression.
    case Top,
    case Int64,
    case Float64,
    case String,
    case Null,
    /// Arrays do not inherit subtyping from their element types. Int64 is a
    /// subtype of Float64, but ARRAY(Int64) is not a subtype of ARRAY(Float64).
    case Array(Type),
    /// Bottom could be any type. In practice, it represents a "can't happen"
    /// situation. `ARRAY[]` has the type `ARRAY(Bottom)`.
    case Bottom
}

mod Type {
    pub def toResult(t: Type): Result[String, Type] =
        match t {
            case Type.Top => Err("inconsistent types")
            case _ => Ok(t)
        }
}

@Test
pub def testToResultReturnsErrorForTop(): Bool = Assert.eq(
    Type.toResult(Type.Top),
    Err("inconsistent types")
)

@Test
def testToResultReturnsOkForOtherTypes(): Bool = Assert.eq(
    Type.toResult(Type.Int64),
    Ok(Type.Int64)
)

instance LowerBound[Type] {
    pub def minValue(): Type = Type.Bottom
}

instance UpperBound[Type] {
    pub def maxValue(): Type = Type.Top
}

instance PartialOrder[Type] {
    pub def lessEqual(x: Type, y: Type): Bool = match (x, y) {
        case (t1, t2) if t1 == t2 => true
        case (_, Type.Top) => true
        case (Type.Bottom, _) => true
        case (Type.Null, _) => true
        case (Type.Int64, Type.Float64) => true
        case (_, _) => false
    }
}

instance JoinLattice[Type] {
    pub def leastUpperBound(x: Type, y: Type): Type = match (x, y) {
        case (t1, t2) if t1 == t2 => t1
        case (Type.Top, _) => Type.Top
        case (_, Type.Top) => Type.Top
        case (Type.Bottom, t) => t
        case (t, Type.Bottom) => t
        case (Type.Null, t) => t
        case (t, Type.Null) => t
        case (Type.Int64, Type.Float64) => Type.Float64
        case _ => Type.Top
    }
}

instance MeetLattice[Type] {
    pub def greatestLowerBound(x: Type, y: Type): Type = match (x, y) {
        case (t1, t2) if t1 == t2 => t1
        case (Type.Bottom, _) => Type.Bottom
        case (_, Type.Bottom) => Type.Bottom
        case (Type.Null, _) => Type.Null
        case (_, Type.Null) => Type.Null
        case (Type.Int64, Type.Float64) => Type.Int64
        case _ => Type.Bottom
    }
}

pub trait TypeOf[t] {
    pub def typeOf(x: t): Result[String, Type]
}

pub enum Lit {
    case Int64(Int64),
    case Float64(Float64),
    case String(String),
    case Null
}

instance TypeOf[Lit] {
    pub def typeOf(x: Lit): Result[String, Type] = match x {
        case Lit.Int64(_) => Ok(Type.Int64)
        case Lit.Float64(_) => Ok(Type.Float64)
        case Lit.String(_) => Ok(Type.String)
        case Lit.Null => Ok(Type.Null)
    }
}

pub enum Expr {
    case Lit(Lit),
    case Array(List[Expr])
}

instance TypeOf[Expr] {
    pub def typeOf(x: Expr): Result[String, Type] = match x {
        case Expr.Lit(l) => TypeOf.typeOf(l)
        case Expr.Array(es) => forM (
            ts <- typesOf(es);
            et <- elementType(ts)
        )
            yield Type.Array(et)
    }
}

@Test
def testTypeOfLitInt64(): Bool = Assert.eq(
    TypeOf.typeOf(Lit.Int64(42i64)),
    Ok(Type.Int64)
)

@Test
def testTypeOfSimpleArray(): Bool = Assert.eq(
    TypeOf.typeOf(Expr.Array(Expr.Lit(Lit.Int64(42i64)) :: Nil)),
    Ok(Type.Array(Type.Int64))
)

@Test
def testTypeOfEmptyArray(): Bool = Assert.eq(
    TypeOf.typeOf(Expr.Array(Nil)),
    Ok(Type.Array(Type.Bottom))
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
    Ok(Type.Array(Type.Float64))
)

@Test
def testTypeOfInconsistentArray(): Bool = Assert.eq(
    // ARRAY[42, 3.14, NULL] -> ARRAY[FLOAT64]
    TypeOf.typeOf(Expr.Array(
        Expr.Lit(Lit.Int64(42i64)) ::
        Expr.Lit(Lit.String("foo")) ::
        Nil
    )),
    Err("inconsistent types")
)

def elementType(es: List[Type]): Result[String, Type] =
    let arg_types = inject es into ArgType;
    let elem_type = #{
        ElemType(; t: Type) :- ArgType(t).
    };
    let elem_types = query elem_type, arg_types select t from ElemType(; t);
    if (Vector.isEmpty(elem_types))
        Ok(Type.Bottom)
        else Type.toResult(Vector.get(0, elem_types))

def typesOf(es: List[Expr]): Result[String, List[Type]] =
    mapM(TypeOf.typeOf, es)

def mapM(f: a -> Result[String, b], xs: List[a]): Result[String, List[b]] =
    match xs {
        case Nil => Ok(Nil)
        case Cons(x, xs2) =>
            forM (y <- f(x); ys <- mapM(f, xs2))
                yield Cons(y, ys)
    }
