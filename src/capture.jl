import REPL
import REPL.LineEdit

const SF = Tuple{Base.StackFrame,Int}
const last_stacktrace   = SF[]
const saved_stacktrace  = SF[]
const saved_command     = Ref("")
const saved_args        = Ref{Any}(nothing)
const saved_let_command = Ref{Any}(nothing)

# Use to re-evaluate an expression without leaving "breadcrumbs" about where
# the eval is coming from. This is used below to prevent the re-evaluaton of an
# original method from being attributed to Revise itself in future backtraces.
eval_noinfo(mod::Module, ex::Expr) = ccall(:jl_toplevel_eval, Any, (Any, Any), mod, ex)

"""
    argnames = capture(method, command; on_err::Bool=false, params::Bool=false)

Runs `command` (a string or Expr) while capturing the input arguments to `Revise.saved_args[]`.
If `on_err` is `true`, capturing occurs only *after* the function throws an error.
This greatly reduces the performance hit of capturing but can be misleading for functions that
modify their arguments.

The argument values are stored as a tuple in `Revise.saved_args[]`. If capture fails
(e.g., the method never gets called, or never throws an error while `on_err==true`),
then `Revise.saved_args[] === nothing`.

`argnames` is a tuple of Symbols with the names of the method's arguments.
"""
function capture(method::Method, command::Expr; on_err::Bool=false, params::Bool=false)
    saved_args[] = nothing
    def = get_def(method)

    sigr = get_signature(def)
    if sigr == nothing
        @warn "skipping capture: could not extract signature from $def"
        return nothing
    end
    sig = convert(Expr, sigr)
    # Create a capturing method with the original name,
    # while "renaming" the old method
    methname, argnames, kwnames, paramnames = signature_names(sig)
    paramnames = params ? paramnames : ()
    kwrepro = [:($name=$name) for name in kwnames]
    allnames = (argnames..., kwnames..., paramnames...)
    tmpname = gensym(methname)
    capture_body = on_err ? quote
        local result
        try
            result = $tmpname($(argnames...); $(kwrepro...))
        catch err
            Main.Revise.saved_args[] = ($(allnames...),)
            rethrow(err)
        end
        return result
    end : quote
        Main.Revise.saved_args[] = Main.Revise.safe_deepcopy($(allnames...))
        return $tmpname($(argnames...))
    end
    capture_function = Expr(:function, sig, capture_body)
    tmp_function = rename_method!(convert(Expr, def), tmpname)
    mod = method.module
    Core.eval(mod, capture_function)
    try # Once we've `eval`ed capture_function, we can't exit until we've restored the original method
        Core.eval(mod, tmp_function)
        # Run the command
        try
            Core.eval(Main, command)
            if on_err && Revise.saved_args[] === nothing
                @warn "$command did not throw an error"
                allnames = nothing
            end
        catch err
        end
        # Variables should be stored in saved_args, so now we clean up.
        # tmpname must be unique, so we can bypass the complexity of get_method.
        anon = getfield(mod, tmpname)
        meths = methods(anon)
        for meth in meths   # will be multiples if method has default args
            Base.delete_method(meth)
        end
    finally
        eval_noinfo(mod, convert(Expr, def))   # restore the original method
    end
    return allnames
end
capture(method::Method, command::AbstractString; kwargs...) =
    capture(method, Meta.parse(command); kwargs...)

"""
    snoop_method(method, command)

Populate the `julia>` prompt with a `let` block that extracts the input arguments and
type-parameters to `method` when executing `command`.
The `let` block will also include the body-source of `method`, which you can edit
as desired before executing the block.
"""
function snoop_method(method, command)
    letcmd = _snoop_method(method, command)
    LineEdit.edit_insert(Base.active_repl.mistate, chomp(letcmd))
    nothing
end

function _snoop_method(method, command)
    ref = generate_let_command!(Ref{Any}(nothing), method, command, command; on_err=false)
    ref === nothing && return nothing
    ref[]
end

function generate_let_command!(refstring::Ref, method, command, annotation; on_err::Bool=false)
    method === nothing && return nothing
    methodvars = capture(method, command; on_err=on_err, params=true)
    methodvars === nothing && return nothing
    isempty(methodvars) && (@warn "no arguments"; return nothing)
    vars = argstring(methodvars)
    body = convert(Expr, striplines!(deepcopy(funcdef_body(get_def(method)))))
    refstring[] = """
        @eval $(method.module) let $vars = Main.Revise.saved_args[]  # $annotation
        $body
        end"""
    return refstring
end

function get_def(method)
    filename = String(method.file)
    fi = fileinfos[filename]
    maybe_parse_from_cache!(fi, filename)
    return fi.fm[method.module].sigtmap[method.sig]
end

function methtrace_selection(s)
    str = String(take!(LineEdit.buffer(s)))
    n = tryparse(Int, str)
    n === nothing && @goto writeback
    if n <= 0 || n > length(saved_stacktrace)
        @goto writeback
    end
    sf = saved_stacktrace[n][1]
    linfo = sf.linfo
    if linfo === nothing
        @warn "$(sf.func) in $(sf.file):$(sf.line) was inlined, capture is not possible"
        return n, nothing
    end
    m = linfo.def
    if isa(m, Module)
        @warn "This item was defined in a module: $(saved_stacktrace[n])"
        @goto writeback
    end
    if occursin("REPL", String(m.file))
        @warn "cannot capture variables for methods defined at the REPL"
        @goto writeback
    end
    LineEdit.refresh_line(s)
    return n, m

    @label writeback
    write(LineEdit.buffer(s), str)
    return n, nothing
end

function capturevars(s, o, when)
    n, method = methtrace_selection(s)
    method === nothing && return nothing
    argnames = capture(method, saved_command[]; on_err=when==:exit)
    argnames === nothing && return nothing
    isempty(argnames) && (@warn "no arguments"; return nothing)
    vars = argstring(argnames)
    LineEdit.edit_insert(s, "$vars = Revise.saved_args[]  # stackframe $n")
    return nothing
end

function capturevars(s, o, when, letsym)
    @assert letsym == :let
    if isempty(LineEdit.buffer(s).data) && saved_let_command[] !== nothing
        LineEdit.edit_insert(s, saved_let_command[])
        return nothing
    end
    n, method = methtrace_selection(s)
    method === nothing && return nothing
    ref = generate_let_command!(saved_let_command, method, saved_command[], "stackframe $n"; on_err=when==:exit)
    isa(ref, Ref) && LineEdit.edit_insert(s, ref[])
    return nothing
end

argstring(argnames) = length(argnames) == 1 ? argnames[1] : '(' * join(argnames, ", ") * ')'

const revisekeys = Dict{Any,Any}(
    "\es" => (s, o...) -> begin
        saved_command[] = Base.active_repl.interface.modes[1].hist.history[end]
        overwrite!(saved_stacktrace, last_stacktrace)
        println("stacktrace saved")
    end,
    # Capture calling vars
    "\ee" => (s, o...) -> capturevars(s, o, :enter),
    "\eE" => (s, o...) -> capturevars(s, o, :enter, :let),
    "\ex" => (s, o...) -> capturevars(s, o, :exit),
    "\eX" => (s, o...) -> capturevars(s, o, :exit, :let),
)

"""
    Revise.customize_keys(repl)

FIXME
Add key bindings for variable-capture from stacktraces:
- <stackframe #>Meta-c (e.g., 2Alt-c) will capture to variables in `Main`;
- <stackframe #>Meta-C (e.g., 2Alt-Shift-c) captures to variables in a module-evaluated
  `let` block and replicates the function body of the method, allowing you to insert
  debugging statements without modifying the corresponding file.

The `Meta-C` variant is preferred if you want to avoid contaminating `Main`'s namespace
with extra variables. If you've already run `Meta-C` on a particular stackframe in a
stacktrace, hitting `Meta-C` again (without the line number or preceding error and stacktrace)
will repeat the same `let` block, providing you with an opportunity to debug the same
block of code in a different way. (You can of course also use the REPL's history features.)

# Example

Given methods
```julia
foo(name, x) = bar(name)
bar(othername) = error("oops")
```
you can execute a call and obtain a stacktrace:
```julia
julia> foo("Revise", 0)
ERROR: oops
Stacktrace:
 [1] error(::String) at ./error.jl:33
 [2] bar(::String) at /tmp/capture_example.jl:2
 [3] foo(::String, ::Int64) at /tmp/capture_example.jl:1
 [4] top-level scope at none:0
```
Then typing
```julia
julia> 3Meta-c
```
will result in a line
```julia
julia> (name, x,) = Revise.saved_args[]  # stackframe 3
```
appearing at the REPL prompt. Hitting Enter will set `name="Revise"` and `x=0` in `Main`.

Had we picked line 2 of the stacktrace (`2Meta-c`), we would have instead obtained

```julia
julia> (othername,) = Revise.saved_args[]  # stackframe 2
```
"""
function customize_keys(repl)
    repl.interface = REPL.setup_interface(repl; extra_repl_keymap = revisekeys)
end

safe_deepcopy(a, args...) = (_deepcopy(a), safe_deepcopy(args...)...)
safe_deepcopy() = ()

_deepcopy(a) = deepcopy(a)
_deepcopy(a::Module) = a
