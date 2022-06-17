module Etog (
    Expr(Ident, Mul, Inv, Var), check,
    reflex, symm, trans, subst, leibniz,
    assocL, assocR,
    identIntroL, identIntroR, identElimL, identElimR,
    invIntroL, invIntroR, invElimL, invElimR
  ) where

--
-- Definitions
--

type VarName = String

data Expr = Ident
          | Mul Expr Expr
          | Inv Expr
          | Var VarName
    deriving (Ord, Eq)

instance Show Expr where
    show Ident = "e"
    show (Mul a b) = "(" ++ (show a) ++ "*" ++ (show b) ++ ")"
    show (Inv a) = "~" ++ (show a)
    show (Var n) = n

data Theorem = Thm Expr Expr
    deriving (Ord, Eq)

instance Show Theorem where
    show (Thm a b) = (show a) ++ "=" ++ (show b)

--
-- Primitive operations
--

substExpr :: Expr -> VarName -> Expr -> Expr
substExpr Ident _ _ = Ident
substExpr (Mul e1 e2) v ex = Mul (substExpr e1 v ex) (substExpr e2 v ex)
substExpr (Inv e1) v ex = Inv (substExpr e1 v ex)
substExpr e1@(Var s) v ex = if s == v then ex else e1

update :: (Expr -> Expr) -> [Int] -> Theorem -> Theorem
update f (1:index) (Thm lhs rhs) = Thm (updateExpr f index lhs) rhs
update f (2:index) (Thm lhs rhs) = Thm lhs (updateExpr f index rhs)

updateExpr f [] t = f t
updateExpr f (1:index) (Mul x y) = Mul (updateExpr f index x) y
updateExpr f (2:index) (Mul x y) = Mul x (updateExpr f index y)
updateExpr f (1:index) (Inv x) = Inv (updateExpr f index x)

--
-- Axioms and Rules of Inference of Equational Logic
--

reflex :: Expr -> Theorem
reflex e = Thm e e

symm :: Theorem -> Theorem
symm (Thm a b) = Thm b a

trans :: Theorem -> Theorem -> Theorem
trans (Thm p q1) (Thm q2 r) = if q1 == q2 then (Thm p r) else error "not transitive"

subst :: Expr -> VarName -> Theorem -> Theorem
subst e v (Thm p q) = Thm (substExpr p v e) (substExpr q v e)

leibniz :: Expr -> VarName -> Theorem -> Theorem
leibniz e v (Thm p q) = Thm (substExpr e v p) (substExpr e v q)

--
-- Axioms of Group Theory
--

assocL = update $ \(Mul (Mul x y) z) -> Mul x (Mul y z)
assocR = update $ \(Mul x (Mul y z)) -> Mul (Mul x y) z

identIntroL = update $ \x -> Mul Ident x
identIntroR = update $ \x -> Mul x Ident

identElimL = update $ \(Mul Ident x) -> x
identElimR = update $ \(Mul x Ident) -> x

invIntroL n = update $ \Ident -> Mul (Inv (Var n)) (Var n)
invIntroR n = update $ \Ident -> Mul (Var n) (Inv (Var n))

invElimL = update $ \(Mul (Inv x1) x2) -> if x1 == x2 then Ident else error "not inverse"
invElimR = update $ \(Mul x1 (Inv x2)) -> if x1 == x2 then Ident else error "not inverse"

--
-- Helpers
--

check thm expected =
    let
        errMsg = "expected '" ++ expected ++ "' but derived '" ++ (show thm) ++ "'"
    in
        if (show thm) == expected then thm else error errMsg
