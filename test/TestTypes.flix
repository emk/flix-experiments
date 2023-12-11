@Test
pub def testTypeOfLitInt64(): Bool = Assert.eq(
    Expr.inferTypes(InferenceDirection.Up, Expr.Lit(1, Lit.Int64(42i64))),
    Map#{ 1 => Type.Int64 }
)

@Test
pub def testTypeOfArray(): Bool = Assert.eq(
    Map#{ 1 => Type.Array(Type.Int64), 2 => Type.Int64 },
    Expr.inferTypes(
        InferenceDirection.Up,
        Expr.Array(1, Expr.Lit(2, Lit.Int64(42i64)) :: Nil)
    )
)

@Test
pub def testTypeOfArrayEmpty(): Bool = Assert.eq(
    Map#{ 1 => Type.Array(Type.Unknown) },
    Expr.inferTypes(InferenceDirection.Up, Expr.Array(1, Nil))
)

@Test
pub def testTypeOfArrayComplex(): Bool = Assert.eq(
    // ARRAY[42, 3.14, NULL] -> ARRAY[FLOAT64]
    Map#{
        1 => Type.Array(Type.Float64),
        2 => Type.Int64,
        3 => Type.Float64,
        4 => Type.Null
    },
    Expr.inferTypes(
        InferenceDirection.Up,
        Expr.Array(
            1,
            Expr.Lit(2, Lit.Int64(42i64)) ::
            Expr.Lit(3, Lit.Float64(3.14f64)) ::
            Expr.Lit(4, Lit.Null) ::
            Nil
        )
    )
)

@Test
pub def testTypeOfArrayComplexBidirectional(): Bool = Assert.eq(
    // ARRAY[42, 3.14, NULL] -> ARRAY[FLOAT64]
    Map#{
        1 => Type.Array(Type.Float64),
        2 => Type.Float64,
        3 => Type.Float64,
        4 => Type.Float64
    },
    Expr.inferTypes(
        InferenceDirection.Bidirectional,
        Expr.Array(
            1,
            Expr.Lit(2, Lit.Int64(42i64)) ::
            Expr.Lit(3, Lit.Float64(3.14f64)) ::
            Expr.Lit(4, Lit.Null) ::
            Nil
        )
    )
)

@Test
pub def testTypeOfArrayInconsistent(): Bool = Assert.eq(
    // ARRAY[42, "foo"] -> inconsistent type
    Map#{ 1 => Type.Inconsistent, 2 => Type.Int64, 3 => Type.String },
    Expr.inferTypes(
        InferenceDirection.Up,
        Expr.Array(
            1,
            Expr.Lit(2, Lit.Int64(42i64)) ::
            Expr.Lit(3, Lit.String("foo")) ::
            Nil
        )
    )
)

@Test
pub def testTypeOfArrayConcat(): Bool = Assert.eq(
    // ARRAY[42] || ARRAY[10] -> ARRAY[INT64]
    Map#{
        1 => Type.Array(Type.Int64),
        2 => Type.Array(Type.Int64), 3 => Type.Int64,
        4 => Type.Array(Type.Int64), 5 => Type.Int64
    },
    Expr.inferTypes(
        InferenceDirection.Up,
        Expr.ArrayConcat(
            1,
            Expr.Array(2, Expr.Lit(3, Lit.Int64(42i64)) :: Nil) ::
            Expr.Array(4, Expr.Lit(5, Lit.Int64(10i64)) :: Nil) ::
            Nil
        )
    )
)

@Test
pub def testTypeOfArrayConcatInconsistent(): Bool = Assert.eq(
    // ARRAY[42] || ARRAY[3.14] -> inconsistent type
    Map#{
        1 => Type.Inconsistent,
        2 => Type.Array(Type.Int64), 3 => Type.Int64,
        4 => Type.Array(Type.Float64), 5 => Type.Float64
    },
    Expr.inferTypes(
        InferenceDirection.Up,
        Expr.ArrayConcat(
             1,
            Expr.Array(2, Expr.Lit(3, Lit.Int64(42i64)) :: Nil) ::
            Expr.Array(4, Expr.Lit(5, Lit.Float64(3.14f64)) :: Nil) ::
            Nil
        )
    )
)

@Test
pub def testTypeOfArrayConcatEmpty(): Bool = Assert.eq(
    // ARRAY[42] || ARRAY[] -> ARRAY[INT64]
    Map#{
        1 => Type.Array(Type.Int64),
        2 => Type.Array(Type.Int64), 3 => Type.Int64,
        4 => Type.Array(Type.Unknown)
    },
    Expr.inferTypes(
        InferenceDirection.Up,
        Expr.ArrayConcat(
            1,
            Expr.Array(2, Expr.Lit(3, Lit.Int64(42i64)) :: Nil) ::
            Expr.Array(4, Nil) ::
            Nil
        )
    )
)

@Test
pub def testTypeOfArrayConcatEmptyBidirectional(): Bool = Assert.eq(
    // ARRAY[42] || ARRAY[] -> ARRAY[INT64]
    Map#{
        1 => Type.Array(Type.Int64),
        2 => Type.Array(Type.Int64), 3 => Type.Int64,
        4 => Type.Array(Type.Int64)
    },
    Expr.inferTypes(
        InferenceDirection.Bidirectional,
        Expr.ArrayConcat(
            1,
            Expr.Array(2, Expr.Lit(3, Lit.Int64(42i64)) :: Nil) ::
            Expr.Array(4, Nil) ::
            Nil
        )
    )
)
