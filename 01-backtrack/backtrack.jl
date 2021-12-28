# Simple boolean expressions:
abstract type Expr end
struct Var <: Expr; name::Char; end
struct And <: Expr; lhs::Expr; rhs::Expr; end
struct Or <: Expr; lhs::Expr; rhs::Expr; end
struct Not <: Expr; e::Expr; end
struct Const <: Expr; value::Bool; end

# Get the name of the next free variable:
freevar(v::Var) = v.name
freevar(e::And) = something(freevar(e.lhs), freevar(e.rhs))
freevar(e::Or) = something(freevar(e.lhs), freevar(e.rhs))
freevar(e::Not) = freevar(e.e)
freevar(_::Const) = nothing

# Guess that variable name has value value:
guess(name::Char, value::Bool, v::Var) = v.name == name ? Const(value) : v
guess(name::Char, value::Bool, e::And) = And(guess(name, value, e.lhs), guess(name, value, e.rhs))
guess(name::Char, value::Bool, e::Or) = Or(guess(name, value, e.lhs), guess(name, value, e.rhs))
guess(name::Char, value::Bool, e::Not) = Not(guess(name, value, e.e))
guess(name::Char, value::Bool, c::Const) = c

# Constant propagation:
simplify(v::Var) = v
simplify(e::And) =
    let f = filter(x->x!=Const(true), [simplify(e.lhs), simplify(e.rhs)])
        if f == []
            Const(true)
        elseif all(x->x==Const(false), f)
            Const(false)
        elseif length(f) == 1
            f[1]
        else
            Or(f[1], f[2])
        end
    end
simplify(e::Or) =
    let f = filter(x->x!=Const(false), [simplify(e.lhs), simplify(e.rhs)])
        if f == []
            Const(false)
        else if all(x->x==Const(true), f)
            Const(true)
        elseif length(f) == 1
            f[1]
        else
            Or(f[1], f[2])
        end
    end
simplify(e::Not) =
    let f = simplify(e.e)
        f isa Const ? Const(!f.value) : Not(f)
    end
simplify(c::Const) = c

# Backtracking search:
function satisfiable(e::Expr)
    v = freevar(e)
    if isnothing(v)
        return e.value
    end
    trytrue = satisfiable(simplify(guess(v, true, e)))
    tryfalse = satisfiable(simplify(guess(v, false, e)))
    return trytrue || tryfalse
end

# Tests:
@assert satisfiable(Const(true)) == true
@assert satisfiable(Const(false)) == false
@assert satisfiable(And(Var('x'), Var('x'))) == true
@assert satisfiable(And(Var('x'), Not(Var('x')))) == false
@assert satisfiable(And(Var('x'), Var('y'))) == true
@assert satisfiable(Or(Var('x'), Var('x'))) == true
@assert satisfiable(Or(Var('x'), Not(Var('x')))) == true
@assert satisfiable(Or(Var('x'), Var('y'))) == true
