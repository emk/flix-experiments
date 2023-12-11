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
        case (_, Type.Unknown) => false
        case (Type.Null, _) => true
        case (Type.Int64, Type.Float64) => true
        // Arrays have limited subtyping.
        case (Type.Array(_), Type.Array(Type.Inconsistent)) => true
        case (Type.Array(Type.Unknown), Type.Array(_)) => true
        case (_, _) => false
    }
}

instance JoinLattice[Type] {
    pub def leastUpperBound(x: Type, y: Type): Type =
        if (PartialOrder.lessEqual(x, y))
            y
        else if (PartialOrder.lessEqual(y, x))
            x
        else
            Type.Inconsistent
}

instance MeetLattice[Type] {
    pub def greatestLowerBound(x: Type, y: Type): Type =
        if (PartialOrder.lessEqual(x, y))
            x
        else if (PartialOrder.lessEqual(y, x))
            y
        else
            Type.Unknown
}

pub type alias ExprID = Int32

pub enum Lit {
    case Int64(Int64),
    case Float64(Float64),
    case String(String),
    case Null
}

mod Lit {
    pub def typeOf(x: Lit): Type = match x {
        case Lit.Int64(_) => Type.Int64
        case Lit.Float64(_) => Type.Float64
        case Lit.String(_) => Type.String
        case Lit.Null => Type.Null
    }
}

pub enum Expr {
    case Lit(ExprID, Lit),
    case Array(ExprID, List[Expr])
    case ArrayConcat(ExprID, List[Expr])
}

mod Expr {
    pub def id(e: Expr): ExprID = match e {
        case Expr.Lit(id, _) => id
        case Expr.Array(id, _) => id
        case Expr.ArrayConcat(id, _) => id
    }

    pub def facts(e: Expr): #{
        Lit(ExprID, Type),
        Array(ExprID),
        ArrayConcat(ExprID),
        Arg(ExprID, ExprID)
        | r
    } = match e {
        case Expr.Lit(id, lit) =>
            // Associate literal expression IDs with their types.
            inject (id, Lit.typeOf(lit)) :: Nil into Lit
        case Expr.Array(id, elem_exprs) =>
            // Declare arrays.
            let array = inject id :: Nil into Array;
            array <+> Expr.callFacts(id, elem_exprs)
        case Expr.ArrayConcat(id, array_exprs) =>
            // Declare array concatenations.
            let array_concat = inject id :: Nil into ArrayConcat;
            array_concat <+> Expr.callFacts(id, array_exprs)
    }

    def callFacts(id: ExprID, arg_exprs: List[Expr]): #{
        Lit(ExprID, Type),
        Array(ExprID),
        ArrayConcat(ExprID),
        Arg(ExprID, ExprID)
        | r
    } =
        // Associate the call with its arguments.
        let args = inject List.map(arg -> (id, Expr.id(arg)), arg_exprs) into Arg;
        // Get recursive type facts for the arguments.
        let arg_types = List.map(arg -> Expr.facts(arg), arg_exprs);
        // Combine our facts.
        List.foldLeft((f1, f2) -> f1 <+> f2, args, arg_types)

    pub def inferTypes(e: Expr): Map[ExprID, Type] =
        // Get all our raw facts.
        let facts = Expr.facts(e);
        //debug(facts);

        // Define our inference rules.
        //
        // "dummy" needed to avoid https://github.com/flix/flix/issues/4719.
        let rules = #{
            // Infer the type of a literal.
            Type("dummy", lit_id; t) :- Lit(lit_id, t).

            // Infer the type of an array. Several of these rules are likely to
            // match, and Flix will automatically combine the right-hand types
            // using `leastUpperBound`.
            Type("dummy", array_id; Type.Array(Type.Unknown)) :-
                Array(array_id).
            Type("dummy", array_id; Type.Array(t)) :-
                ArrayElemType("dummy", array_id; t).

            // This rule is responsible for combining the types of multiple
            // array elements. It will match once per element, and Flix will
            // automatically combine the types `t` of each element using
            // `leastUpperBound`.
            ArrayElemType("dummy", array_id; t) :-
                Array(array_id),
                Arg(array_id, elem_id),
                Type("dummy", elem_id; t).

            // Infer the type of an array concatenation.
            Type("dummy", array_concat_id; Type.Array(Type.Unknown)) :-
                ArrayConcat(array_concat_id).
            Type("dummy", array_concat_id; t) :-
                ArrayConcatArgType("dummy", array_concat_id; t).

            // Figure out the type of an array concatenation argument.
            ArrayConcatArgType("dummy", array_concat_id; t) :-
                ArrayConcat(array_concat_id),
                Arg(array_concat_id, arg_id),
                Type("dummy", arg_id; t).

            // Propagate inconsistent types up into any wrapping types. This
            // relies on combining the old and new types using
            // `leastUpperBound`.
            Type("dummy", array_id; Type.Inconsistent) :-
                Type("dummy", array_id; t),
                // This isn't actually monotonic in the sense that it should
                // be! But the rule as a whole should converge, which may or
                // may not be good enough. I need to read the docs.
                if (t == Type.Array(Type.Inconsistent)).
        };

        query rules, facts select (id, t) from Type("dummy", id; t) |> Vector.toMap
}
