module EtogDemo where

import Etog (
    Expr(Ident, Mul, Inv, Var), check,
    reflex, symm, trans, subst, leibniz,
    assocL, assocR,
    identIntroL, identIntroR, identElimL, identElimR,
    invIntroL, invIntroR, invElimL, invElimR
  )

--
-- "Socks and shoes"
--

proofSnSVerbose =
    let
        s1 = check (reflex Ident)             "e=e"
        s2 = check (invIntroR "c" [1] s1)     "(c*~c)=e"
        e1 = (Mul (Var "a") (Var "b"))
        s3 = check (subst e1 "c" s2)          "((a*b)*~(a*b))=e"
        s4 = check (invIntroR "a" [2] s3)     "((a*b)*~(a*b))=(a*~a)"
        s5 = check (identIntroR [2,1] s4)     "((a*b)*~(a*b))=((a*e)*~a)"
        s6 = check (invIntroR "b" [2,1,2] s5) "((a*b)*~(a*b))=((a*(b*~b))*~a)"
        s7 = check (assocR [2,1] s6)          "((a*b)*~(a*b))=(((a*b)*~b)*~a)"
        s8 = check (assocL [2] s7)            "((a*b)*~(a*b))=((a*b)*(~b*~a))"
        e2 = (Mul (Inv (Var "a")) (Var "c"))
        s9 = check (leibniz e2 "c" s8)        "(~a*((a*b)*~(a*b)))=(~a*((a*b)*(~b*~a)))"
        sa = check (assocR [1] s9)            "((~a*(a*b))*~(a*b))=(~a*((a*b)*(~b*~a)))"
        sb = check (assocR [1,1] sa)          "(((~a*a)*b)*~(a*b))=(~a*((a*b)*(~b*~a)))"
        sc = check (invElimL [1,1,1] sb)      "((e*b)*~(a*b))=(~a*((a*b)*(~b*~a)))"
        sd = check (identElimL [1,1] sc)      "(b*~(a*b))=(~a*((a*b)*(~b*~a)))"
        se = check (assocR [2] sd)            "(b*~(a*b))=((~a*(a*b))*(~b*~a))"
        sf = check (assocR [2,1] se)          "(b*~(a*b))=(((~a*a)*b)*(~b*~a))"
        sg = check (invElimL [2,1,1] sf)      "(b*~(a*b))=((e*b)*(~b*~a))"
        sh = check (identElimL [2,1] sg)      "(b*~(a*b))=(b*(~b*~a))"
        e3 = (Mul (Inv (Var "b")) (Var "c"))
        si = check (leibniz e3 "c" sh)        "(~b*(b*~(a*b)))=(~b*(b*(~b*~a)))"
        sj = check (assocR [1] si)            "((~b*b)*~(a*b))=(~b*(b*(~b*~a)))"
        sk = check (assocR [2] sj)            "((~b*b)*~(a*b))=((~b*b)*(~b*~a))"
        sl = check (invElimL [1,1] sk)        "(e*~(a*b))=((~b*b)*(~b*~a))"
        sm = check (invElimL [2,1] sl)        "(e*~(a*b))=(e*(~b*~a))"
        sn = check (identElimL [1] sm)        "~(a*b)=(e*(~b*~a))"
        so = check (identElimL [2] sn)        "~(a*b)=(~b*~a)"
    in
        so


proofSnSApply =
    identElimL [2] $ identElimL [1] $ invElimL [2,1] $ invElimL [1,1] $ assocR [2] $ assocR [1] $
      leibniz (Mul (Inv (Var "b")) (Var "c")) "c" $ identElimL [2,1] $ invElimL [2,1,1] $ assocR [2,1] $ assocR [2] $
        identElimL [1,1] $ invElimL [1,1,1] $ assocR [1,1] $ assocR [1] $ leibniz (Mul (Inv (Var "a")) (Var "c")) "c" $
          assocL [2] $ assocR [2,1] $ invIntroR "b" [2,1,2] $ identIntroR [2,1] $
            invIntroR "a" [2] $ subst (Mul (Var "a") (Var "b")) "c" $ invIntroR "c" [1] $ reflex Ident


proofSnSCompose =
    let
        f2 = invIntroR "c" [1]
        f3 = subst (Mul (Var "a") (Var "b")) "c"
        f4 = invIntroR "a" [2]
        -- etc, etc, etc.  You get the idea.
    in
        (f4 . f3 . f2) (reflex Ident)
