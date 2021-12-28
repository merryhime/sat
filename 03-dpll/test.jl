struct Literal
    name::Char
    positive::Bool
end
const Clause = Vector{Literal}
const CNFExpr = Vector{Clause}

literals(e::CNFExpr) = Set(Iterators.flatten(e...))
literalnames(e::CNFExpr) = Set(map(l->l.name, Iterators.flatten(e...)))
ispolarized(e::CNFExpr, name::Char) = count(l->l.name==name, literals(e)) == 1
polarized(e::CNFExpr) = filter(l->ispolarized(e, l.name), literals(e))

guess(e::CNFExpr, name::Char, value::Bool)
