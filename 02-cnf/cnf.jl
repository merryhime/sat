using MLStyle

@data Expr begin
    Var(Char)
    And(Expr, Expr)
    Or(Expr, Expr)
    Not(Expr)
    Const(Bool)
end

function cnf(next::Expr)
    step(e::Expr) =
        let s = step
            @match e begin
                Not(Const(x)) => Const(!x)
                And(Const(true), x) => s(x)
                And(x, Const(true)) => s(x)
                Or(Const(false), x) => s(x)
                Or(x, Const(false)) => s(x)

                Not(Not(x)) => s(x)
                Not(And(a, b)) => s(Or(Not(a), Not(b)))
                Not(Or(a, b)) => s(And(Not(a), Not(b)))
                Or(a, And(b, c)) => s(And(Or(a, b), Or(a, c)))
                Or(And(b, c), a) => s(And(Or(a, b), Or(a, c)))

                Not(x) => Not(s(x))
                And(a, b) => And(s(a), s(b))
                Or(a, b) => Or(s(a), s(b))
                x => x
            end
        end

    while true
        prev = next
        next = step(prev)
        if prev == next
            return next
        end
    end
end

@assert cnf(Or(Or(And(Var('a'), Var('b')), And(Var('q'), Var('r'))), Var('z'))) == And(And(Or(Var('z'), Or(Var('q'), Var('a'))), Or(Var('z'), Or(Var('q'), Var('b')))), And(Or(Var('z'), Or(Var('r'), Var('a'))), Or(Var('z'), Or(Var('r'), Var('b')))))
