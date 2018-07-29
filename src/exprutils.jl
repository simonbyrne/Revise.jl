# Much is taken from ExpressionUtils.jl but generalized to work with ExLike

using Core: MethodInstance
using Base: MethodList

const ExLike = Union{Expr,RelocatableExpr}

"""
    exf = funcdef_expr(ex)

Recurse, if necessary, into `ex` until the first function definition expression is found.

# Example

```jldoctest; setup=(using Revise), filter=r"#=.*=#"
julia> Revise.funcdef_expr(quote
       \"\"\"
       A docstring
       \"\"\"
       @inline foo(x) = 5
       end)
:(foo(x) = begin
          #= REPL[31]:5 =#
          5
      end)
```
"""
function funcdef_expr(ex)
    if ex.head == :macrocall
        if ex.args[1] isa GlobalRef && ex.args[1].name == Symbol("@doc")
            return funcdef_expr(ex.args[end])
        elseif ex.args[1] ∈ (Symbol("@inline"), Symbol("@noinline"))
            return funcdef_expr(first(LineSkippingIterator(ex.args[2:end])))
        else
            io = IOBuffer()
            dump(io, ex)
            throw(ArgumentError(string("unrecognized macro expression:\n", String(take!(io)))))
        end
    end
    if ex.head == :block
        return funcdef_expr(first(LineSkippingIterator(ex.args)))
    end
    if ex.head == :function || ex.head == :(=)
        return ex
    end
    dump(ex)
    throw(ArgumentError(string("expected function definition expression, got ", ex)))
end

function funcdef_body(ex)
    fex = funcdef_expr(ex)
    if ex.head == :function || ex.head == :(=)
        return ex.args[end]
    end
    throw(ArgumentError(string("expected function definition expression, got ", ex)))
end

"""
    sigex = get_signature(expr)

Extract the signature from an expression `expr` that defines a function.

If `expr` does not define a function, returns `nothing`.

# Examples

```jldoctest; setup = :(using Revise)
julia> Revise.get_signature(quote
       function count_different(x::AbstractVector{T}, y::AbstractVector{S}) where {S,T}
           sum(x .!= y)
       end
       end)
:(count_different(x::AbstractVector{T}, y::AbstractVector{S}) where {S, T})
```
"""
function get_signature(ex::E) where E <: ExLike
    while ex.head == :macrocall && isa(ex.args[end], E) || is_trivial_block_wrapper(ex)
        ex = ex.args[end]::E
    end
    if ex.head == :function
        return ex.args[1]
    elseif ex.head == :(=) && isa(ex.args[1], E)
        ex = ex.args[1]::E
        if ex.head == :where || ex.head == :call
            return ex
        end
    end
    nothing
end

"""
    callex = get_callexpr(sigex::ExLike)

Return the "call" expression for a signature-expression `sigex`.
(This strips out `:where` statements.)

# Example

```jldoctest; setup=:(using Revise)
julia> Revise.get_callexpr(:(nested(x::A) where A<:AbstractVector{T} where T))
:(nested(x::A))
```
"""
function get_callexpr(sigex::ExLike)
    while sigex.head == :where
        sigex = sigex.args[1]
    end
    sigex.head == :call || throw(ArgumentError(string("expected call expression, got ", sigex)))
    return sigex
end

"""
    typexs = sig_type_exprs(sigex::Expr)

From a function signature-expression `sigex` (see [`get_signature`](@ref)), generate a list
`typexs` of concrete signature type expressions.
This list will have length 1 unless `sigex` has default arguments,
in which case it will produce one type signature per valid number of supplied arguments.

These type-expressions can be evaluated in the appropriate module to obtain a Tuple-type.

# Examples

```jldoctest; setup=:(using Revise)
julia> Revise.sig_type_exprs(:(foo(x::Int, y::String)))
1-element Array{Expr,1}:
 :(Tuple{Core.Typeof(foo), Int, String})

julia> Revise.sig_type_exprs(:(foo(x::Int, y::String="hello")))
2-element Array{Expr,1}:
 :(Tuple{Core.Typeof(foo), Int})
 :(Tuple{Core.Typeof(foo), Int, String})

julia> Revise.sig_type_exprs(:(foo(x::AbstractVector{T}, y) where T))
1-element Array{Expr,1}:
 :(Tuple{Core.Typeof(foo), AbstractVector{T}, Any} where T)
```
"""
function sig_type_exprs(sigex::Expr, wheres...)
    if sigex.head == :where
        return sig_type_exprs(sigex.args[1], sigex.args[2:end], wheres...)
    end
    typexs = Expr[_sig_type_exprs(sigex, wheres)]
    # If the method has default arguments, generate one type signature
    # for each valid call. This replicates the syntactic sugar that defines
    # multiple methods from a single definition.
    while has_default_args(sigex)
        sigex = Expr(sigex.head, sigex.args[1:end-1]...)
        push!(typexs, _sig_type_exprs(sigex, wheres))
    end
    return reverse!(typexs)  # method table is organized in increasing # of args
end
sig_type_exprs(sigex::RelocatableExpr) = sig_type_exprs(convert(Expr, sigex))

function _sig_type_exprs(ex, @nospecialize(wheres))
    fex = ex.args[1]
    sigex = Expr(:curly, :Tuple, :(Core.Typeof($fex)), argtypeexpr(ex.args[2:end]...)...)
    for w in wheres
        sigex = Expr(:where, sigex, w...)
    end
    sigex
end

"""
    typeex1, typeex2, ... = argtypeexpr(ex...)

Return expressions that specify the types assigned to each argument in a method signature.
Returns `:Any` if no type is assigned to a specific argument. It also skips
keyword arguments.

`ex...` should be arguments `2:end` of a `:call` expression (i.e., skipping over the
function name).

# Examples

```jldoctest; setup=:(using Revise), filter=r"#=.*=#"
julia> sigex = :(varargs(x, rest::Int...))
:(varargs(x, rest::Int...))

julia> Revise.argtypeexpr(Revise.get_callexpr(sigex).args[2:end]...)
(:Any, :(Vararg{Int}))

julia> sigex = :(complexargs(w::Vector{T}, @nospecialize(x::Integer), y, z::String=""; kwarg::Bool=false) where T)
:(complexargs(w::Vector{T}, #= REPL[39]:1 =# @nospecialize(x::Integer), y, z::String=""; kwarg::Bool=false) where T)

julia> Revise.argtypeexpr(Revise.get_callexpr(sigex).args[2:end]...)
(:(Vector{T}), :Integer, :Any, :String)
```
"""
function argtypeexpr(ex::ExLike, rest...)
    # Handle @nospecialize(x)
    if ex.head == :macrocall
        return (argtypeexpr(ex.args[3])..., argtypeexpr(rest...)...)
    end
    if ex.head == :...
        # Handle varargs (those expressed with dots rather than Vararg{T,N})
        @assert isempty(rest)
        @assert length(ex.args) == 1
        T = argtypeexpr(ex.args[1])[1]
        return (:(Vararg{$T}),)
    end
    # Skip over keyword arguments
    ex.head == :parameters && return argtypeexpr(rest...)
    # Handle default arguments
    (ex.head == :(=) || ex.head == :kw) && return (argtypeexpr(ex.args[1])..., argtypeexpr(rest...)...)
    # Handle a destructured argument like foo(x, (count, name))
    ex.head == :tuple && return (:Any, argtypeexpr(rest...)...)
    # Should be a type specification, check and then return the type
    ex.head == :(::) || throw(ArgumentError("expected :(::) expression, got $ex"))
    1 <= length(ex.args) <= 2 || throw(ArgumentError("expected 1 or 2 args, got $(ex.args)"))
    return (ex.args[end], argtypeexpr(rest...)...)
end
argtypeexpr(s::Symbol, rest...) = (:Any, argtypeexpr(rest...)...)
argtypeexpr() = ()

"""
    fname, argnames, kwnames, parameternames = signature_names(sigex::Expr)

Return the function name `fname` and names given to its arguments, keyword arguments,
and parameters, as specified by the method signature-expression `sigex`.

# Examples

```jldoctest; setup=:(using Revise)
julia> Revise.signature_names(:(complexargs(w::Ref{A}, @nospecialize(x::Integer), y, z::String=""; kwarg::Bool=false, kw2::String="", kwargs...) where A <: AbstractArray{T,N} where {T,N}))
(:complexargs, (:w, :x, :y, :z), (:kwarg, :kw2, :kwargs), (:A, :T, :N))
```
"""
function signature_names(sigex::ExLike)
    # TODO: add parameter names
    argname(s::Symbol) = s
    function argname(ex::ExLike)
        if ex.head == :(...) && length(ex.args) == 1
            # varargs function
            ex = ex.args[1]
            ex isa Symbol && return ex
        end
        ex.head == :macrocall && return argname(ex.args[3])  # @nospecialize
        ex.head == :kw && return argname(ex.args[1])  # default arguments
        ex.head == :(::) || throw(ArgumentError(string("expected :(::) expression, got ", ex)))
        arg = ex.args[1]
        if isa(arg, Expr) && arg.head == :curly && arg.args[1] == :Type
            arg = arg.args[2]
        end
        return arg
    end
    paramname(s::Symbol) = s
    function paramname(ex::ExLike)
        ex.head == :(<:) && return paramname(ex.args[1])
        throw(ArgumentError(string("expected parameter expression, got ", ex)))
    end

    kwnames, parameternames = (), ()
    while sigex.head == :where
        parameternames = (paramname.(sigex.args[2:end])..., parameternames...)
        sigex = sigex.args[1]
    end
    name = sigex.args[1]
    offset = 1
    if isa(sigex.args[2], ExLike) && sigex.args[2].head == :parameters
        # keyword arguments
        kwnames = tuple(argname.(sigex.args[2].args)...)
        offset += 1
    end

    return sigex.args[1], tuple(argname.(sigex.args[offset+1:end])...), kwnames, parameternames
end

function rename_method!(ex, name::Symbol)
    sigex = get_callexpr(get_signature(ex))
    if isa(sigex.args[1], Symbol)
        sigex.args[1] = name
    else
        throw(ArgumentError(string("expected declaration, got ", ex)))
    end
    return ex
end

function has_default_args(sigex::Expr)
    a = sigex.args[end]
    return isa(a, Expr) && a.head == :kw
end

function is_trivial_block_wrapper(ex::ExLike)
    if ex.head == :block
        return length(ex.args) == 1 ||
            (length(ex.args) == 2 && (is_linenumber(ex.args[1]) || ex.args[1]===nothing))
    end
    false
end
is_trivial_block_wrapper(@nospecialize arg) = false

function is_linenumber(@nospecialize stmt)
    isa(stmt, LineNumberNode) || (isa(stmt, ExLike) && (stmt.head == :line))
end

function firstlineno(rex::ExLike)
    for a in rex.args
        if is_linenumber(a)
            isa(a, LineNumberNode) && return a.line
            return a.args[1]
        end
        if isa(a, ExLike)
            lineno = firstlineno(a)
            isa(lineno, Integer) && return lineno
        end
    end
    return nothing
end

