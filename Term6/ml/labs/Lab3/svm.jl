using DataFrames

include("valid.jl")

function mk_weight(dist, kernel, window)
    function f(xi, x)
        kernel(window(dist(xi, x)))
    end
end

# Distance

dist_euclidean(xi, x) = sqrt(sum((x -> x^2).(xi - x)))
dist_manhattan(xi, x) = sum(abs.(xi - x))
dist_chebyshev(xi, x) = maximum(abs.(xi - x))

function mk_dist_by_name(name)
    if name == :euclidean
        dist_euclidean
    elseif name == :manhattan
        dist_manhattan
    elseif name == :chebyshev
        dist_chebyshev
    end
end

# Kernels

kern_uniform(u) = 1 / 2
kern_triangular(u) = 1 - abs(u)
kern_epanechnikov(u) = 3 / 4 * (1 - u^2)
kern_quartic(u) = 15 / 16 * (1 - u^2)^2

function lim_kern(kern)
    u -> abs(u) >= 1 ? 0 : kern(u)
end

function mk_kern_by_name(name)
    lim_kern(
        if name == :uniform
            kern_uniform
        elseif name == :triangular
            kern_triangular
        elseif name == :epanechnikov
            kern_epanechnikov
        elseif name == :quartic
            kern_quartic
        end
    )
end

# Window

function mk_win_fixed(h)
    x -> x / h
end

function mk_win_variable(X, xi, dist, k)
    h = sort((x -> dist(x, xi)).(X))[k + 1]
    x -> x / h
end

function mk_win_by_name(name, X, xi, dist, param)
    if name == :fixed
        mk_win_fixed(param)
    elseif name == :variable
        mk_win_variable(X, xi, dist, param)
    end
end


function non_param_reg(x::Vector{Float64}, D::Vector{Vector{Float64}}, y::Vector{Vector{Float64}}, w)::Vector{Float64}
    sum(map(Base.splat((xi, yi) -> yi * w(xi, x)), zip(D, y))) / sum(map((xi) -> w(xi , x), D))
end

function leave_one_out(a, X::Vector{Vector{Float64}}, y_true::Vector{Vector{Float64}})
    pred::Vector{Vector{Float64}} = []
    for i ∈ 1:size(X)[1]
        x::Vector{Float64} = X[i]
        D::Vector{Vector{Float64}} = X[Not(i)]
        y::Vector{Vector{Float64}} = y_true[Not(i)]
        push!(pred, a(x, D, y))
    end
    f_score(pred, y_true)
end
