# A module for variable-capture
module ReviseCapture

function errors_on(vec, val)
    ret = first(vec)
    for v in vec
        err_on(v, val)
        ret = v
    end
    ret
end
@noinline err_on(x, val) = x == val ? error("oops") : x

Tval = Ref{Any}(nothing)
function param(z::S, a=""; kwarg::Bool=false) where S <: AbstractVector{T} where T
    Tval[] = T
    error("oops")
end

snoop0()             = snoop1("Spy")
snoop1(word)         = snoop2(word, "on")
snoop2(word1, word2) = snoop3(word1, word2, "arguments")
snoop3(word1, word2, word3::T; adv="simply") where T = join([word1, word2, word3, adv], ' ')

end
