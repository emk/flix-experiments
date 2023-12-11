@Test
pub def testTypeOfLitInt64(): Bool = Assert.eq(
    Expr.inferTypes(Expr.Lit(1, Lit.Int64(42i64))),
    Map#{ 1 => Type.Int64 }
)

@Test
pub def testTypeOfSimpleArray(): Bool = Assert.eq(
    Map#{ 1 => Type.Array(Type.Int64), 2 => Type.Int64 },
    Expr.inferTypes(Expr.Array(1, Expr.Lit(2, Lit.Int64(42i64)) :: Nil))
)

@Test
pub def testTypeOfEmptyArray(): Bool = Assert.eq(
    Map#{ 1 => Type.Array(Type.Unknown) },
    Expr.inferTypes(Expr.Array(1, Nil))
)

@Test
pub def testTypeOfComplexArray(): Bool = Assert.eq(
    // ARRAY[42, 3.14, NULL] -> ARRAY[FLOAT64]
    Map#{ 1 => Type.Array(Type.Float64), 2 => Type.Int64, 3 => Type.Float64, 4 => Type.Null },
    Expr.inferTypes(Expr.Array(
        1,
        Expr.Lit(2, Lit.Int64(42i64)) ::
        Expr.Lit(3, Lit.Float64(3.14f64)) ::
        Expr.Lit(4, Lit.Null) ::
        Nil
    ))
)

@Test
pub def testTypeOfInconsistentArray(): Bool = Assert.eq(
    // ARRAY[42, "foo"] -> inconsistent type
    Map#{ 1 => Type.Inconsistent, 2 => Type.Int64, 3 => Type.String },
    Expr.inferTypes(Expr.Array(
        1,
        Expr.Lit(2, Lit.Int64(42i64)) ::
        Expr.Lit(3, Lit.String("foo")) ::
        Nil
    ))
)