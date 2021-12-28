using MLStyle

@data Expr begin
    Var(Char)
    And(Expr, Expr)
    Or(Expr, Expr)
    Not(Expr)
    Const(Bool)
end

struct Literal
    name::Char
    positive::Bool
end

function cnf(next::Expr)
    step(e::Expr) =
        let s = step
            @match e begin
                Not(Const(x))       => Const(!x)
                And(Const(true), x) => s(x)
                And(x, Const(true)) => s(x)
                Or(Const(false), x) => s(x)
                Or(x, Const(false)) => s(x)

                Not(Not(x))         => s(x)
                Not(And(a, b))      => s(Or(Not(a), Not(b)))
                Not(Or(a, b))       => s(And(Not(a), Not(b)))
                Or(a, And(b, c))    => s(And(Or(a, b), Or(a, c)))
                Or(And(b, c), a)    => s(And(Or(a, b), Or(a, c)))

                Not(x)              => Not(s(x))
                And(a, b)           => And(s(a), s(b))
                Or(a, b)            => Or(s(a), s(b))
                _                   => e
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

freevar(e::Expr) =
    @match e begin
        Var(n)      => n
        And(a, b)   => coalesce(freevar(a), freevar(b))
        Or(a, b)    => coalesce(freevar(a), freevar(b))
        Not(a)      => freevar(a)
        Const(_)    => missing
    end

simplify(e::Expr) =
    @match e begin
        And(a, b)   =>  @match (simplify(a), simplify(b)) begin
                            (Const(false), _)   => Const(false)
                            (_, Const(false))   => Const(false)
                            (Const(true), x)    => x
                            (x, Const(true))    => x
                            (x, y)              => And(x, y)
                        end
        Or(a, b)    =>  @match (simplify(a), simplify(b)) begin
                            (Const(true), _)    => Const(true)
                            (_, Const(true))    => Const(true)
                            (Const(false), x)   => x
                            (x, Const(false))   => x
                            (x, y)              => Or(x, y)
                        end
        Not(a)      =>  @match simplify(a) begin
                            Const(v)            => Const(!v)
                            x                   => Not(x)
                        end
        _           =>  e
    end

guess(name::Char, value::Bool, e::Expr) =
    @match e begin
        Var(n)      => n == name ? Const(value) : e
        And(a, b)   => And(guess(name, value, a), guess(name, value, b))
        Or(a, b)    => Or(guess(name, value, a), guess(name, value, b))
        Not(a)      => Not(guess(name, value, a))
        Const(_)    => e
    end

literals(e::Expr) =
    @match e begin
        Not(Var(n)) => Set([Literal(n, false)])
        Var(n)      => Set([Literal(n, true)])
        And(a, b)   => literals(a) ∪ literals(b)
        Or(a, b)    => literals(a) ∪ literals(b)
        Not(a)      => literals(a)
        Const(_)    => Set()
    end

function polarized(e::Expr)
    ls = literals(e)
    ispolarized(l::Literal) = count(x->x.name==l.name, ls) == 1
    return filter(ispolarized, ls)
end

literalelimination(e::Expr) = reduce((e, l)->guess(l.name, l.positive, e), polarized(e); init=e)

@assert literalelimination(And(Or(Var('a'), Var('b')), Or(Var('a'), Not(Var('b'))))) ==
                           And(Or(Const(true), Var('b')), Or(Const(true), Not(Var('b'))))
@assert literalelimination(And(Or(Not(Var('a')), Var('b')), Or(Not(Var('a')), Not(Var('b'))))) ==
                           And(Or(Not(Const(false)), Var('b')), Or(Not(Const(false)), Not(Var('b'))))

clauses(e::Expr) =
    @match e begin
        And(a, b)   => clauses(a) ∪ clauses(b)
        e           => [e]
    end

function unitclauses(e::Expr)
    isunitclause(c::Expr) =
        @match c begin
            Var(n)      => Literal(n, true)
            Not(Var(n)) => Literal(n, false)
            _           => missing
        end
    return collect(skipmissing(map(isunitclause, clauses(e))))
end

unitpropagation(e::Expr) = reduce((e, l)->guess(l.name, l.positive, e), unitclauses(e); init=e)

@assert unitpropagation(And(Or(Var('a'), Var('b')), Not(Var('b')))) ==
                        And(Or(Var('a'), Const(false)), Not(Const(false)))
@assert unitpropagation(And(Or(Var('a'), Not(Var('b'))), Var('b'))) ==
                        And(Or(Var('a'), Not(Const(true))), Const(true))

function satisfiable(e::Expr)
    e = simplify(literalelimination(simplify(unitpropagation(cnf(e)))))
    n = freevar(e)
    if ismissing(n)
        return @match e begin Const(v) => v end
    end
    trytrue = simplify(guess(n, true, e))
    tryfalse = simplify(guess(n, false, e))
    return satisfiable(trytrue) || satisfiable(tryfalse)
end

@assert satisfiable(Const(true)) == true
@assert satisfiable(Const(false)) == false
@assert satisfiable(And(Var('x'), Var('x'))) == true
@assert satisfiable(And(Var('x'), Not(Var('x')))) == false
@assert satisfiable(And(Var('x'), Var('y'))) == true
@assert satisfiable(Or(Var('x'), Var('x'))) == true
@assert satisfiable(Or(Var('x'), Not(Var('x')))) == true
@assert satisfiable(Or(Var('x'), Var('y'))) == true
