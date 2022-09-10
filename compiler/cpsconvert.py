from . import ast as A
from . import parse as P
from . import string2ast as S2A
from . import symbol as S


def cpsConvert(ast):
    def cps(ast, contAst):
        if A.isLit(ast):
            return A.makeApp([contAst, ast])

        if A.isRef(ast):
            return A.makeApp([contAst, ast])

        if A.isSetClj(ast):

            def fn(val):
                return A.makeApp(
                    [contAst, A.makeSet(val, A.setVar(ast))]
                )

            return cpsList(A.astSubx(ast), fn)

        if A.isCnd(ast):

            def xform(contAst):
                def fn(test):
                    testExp = test[0]
                    ifClause = A.astSubx(ast)[1]
                    elseClause = A.astSubx(ast)[2]
                    return A.makeCnd(
                        [
                            testExp,
                            cps(ifClause, contAst),
                            cps(elseClause, contAst),
                        ]
                    )

                return cpsList([A.astSubx(ast)[0]], fn)

            if A.isRef(contAst):
                return xform(contAst)

            k = S.newVar('k')
            return A.makeApp(
                [A.makeLam([xform(A.makeRef([], k))], [k]), contAst]
            )

        if A.isPrim(ast):

            def fn(args):
                return A.makeApp(
                    [contAst, A.makePrim(args, A.primOp(ast))]
                )

            return cpsList(A.astSubx(ast), fn)

        if A.isApp(ast):
            func = A.astSubx(ast)[0]

            def fn1(vals):
                lam = A.makeLam(
                    [cpsSeq(A.astSubx(func), contAst)], A.lamParams(func)
                )
                return A.makeApp([lam] + vals)

            def fn2(args):
                return A.makeApp([args[0], contAst] + args[1:])

            if A.isLam(func):
                ret = cpsList(A.astSubx(ast)[1:], fn1)
                return ret

            return cpsList(A.astSubx(ast), fn2)

        if A.isLam(ast):
            k = S.newVar("k")
            return A.makeApp(
                [
                    contAst,
                    A.makeLam(
                        [cpsSeq(A.astSubx(ast), A.makeRef([], k))],
                        [k] + A.lamParams(ast),
                    ),
                ]
            )

        if A.isSeqClj(ast):
            return cpsSeq(A.astSubx(ast), contAst)

        print('Unknown AST {}'.format(ast))
        exit()

    def cpsList(asts, inner):
        def body(x):
            def fn(newAsts):
                return inner([x] + newAsts)

            return cpsList(asts[1:], fn)

        if not asts:
            return inner([])

        if A.isLit(asts[0]) or A.isRef(asts[0]):
            return body(asts[0])

        r = S.newVar("r")
        return cps(asts[0], A.makeLam([body(A.makeRef([], r))], [r]))

    def cpsSeq(asts, contAst):
        if not asts:
            return A.makeApp([contAst, False])

        if not asts[1:]:
            return cps(asts[0], contAst)

        r = S.newVar('r')
        return cps(asts[0], A.makeLam([cpsSeq(asts[1:], contAst)], [r]))

    r = S.newVar('r')

    cpsAst = cps(
        ast, A.makeLam([A.makePrim([A.makeRef([], r)], '%halt')], [r])
    )

    if S.lookup('call/cc', S.fv(ast)):
        l = A.makeLam([cpsAst], [S.newVar('_')])
        x = S2A.parse(
            '(set! call/cc (lambda (k f) (f k (lambda (_ result) (k result)))))'
        )
        return A.makeApp([l, x])
    return cpsAst
