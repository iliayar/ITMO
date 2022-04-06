using DataFrames
using LinearAlgebra

function cross_validation(a, X::Vector{T}, y_true::Vector{E}; k=100) where {T, E}
    acc::Vector{Float64} = []
    for (X_train, y_train, X_test, y_test) ∈ cross_validation_split(X, y_true; k=k)
        push!(acc, accuracy(a(X_train, y_train, X_test), y_test))
        println("Iteration ", size(acc)[1], "\tAccuracy ", sum(acc) / size(acc)[1])
    end
    return sum(acc) / size(acc)[1]
end

kernel_linear() = (x1, x2) -> x1 ⋅ x2
kernel_polynomial(d) = (x1, x2) -> (x1 ⋅ x2)^d
kernel_gauss(β) = (x1, x2) -> exp(- β * norm(x1 - x2))

mutable struct SVC
    kernel
    C
    α
    b
    w
    N
    X
    y
    K
end

function mk_svc(kernel_name, kernel_param, N; C = 1.)::SVC
    kernel = (if kernel_name == :linear
        kernel_linear
    elseif kernel_name == :polynomial
        kernel_polynomial
    elseif kernel_name == :gauss
        kernel_gauss
    end)(kernel_param...)
    SVC(kernel, C, zeros(N), 0, zeros(N), N, nothing, nothing, nothing)
end


function fit_svc(cls::SVC, X, y; ITERS = 100)
    cls.X = X
    cls.y = y
    cls.K = calc_K(cls.kernel, X, X)
    for _ in 1:ITERS
        prev_α = copy(cls.α)
        for i in 1:cls.N
            j = rand_neq(1:cls.N, i)

            η = 2 * cls.K[i, j] - cls.K[i, i] - cls.K[j, j]
            if η >= 0
                continue
            end
            L, H = get_bounds(cls, i, j)
            if H - L < eps()
                continue
            end

            ei = calc_error(cls, i)
            ej = calc_error(cls, j)

            prev_prev_αi = cls.α[i]
            prev_prev_αj = cls.α[j]
            cls.α[j] = max(L, min(H, prev_prev_αj + (y[j] * (ej - ei)) / η))
            cls.α[i] = prev_prev_αi + y[i]*y[j] * (prev_prev_αj - cls.α[j])
        end
        if norm(cls.α - prev_α) < eps()
            break
        end
    end
    cls.b = calc_b_sv(cls)
end

function calc_K(kernel, X1, X2)
    N = size(X1)[1]
    M = size(X2)[1]
    reshape([kernel(x1, x2) for x1 in X1 for x2 in X2], (N, M))
end

function get_bounds(cls, i, j)
    if cls.y[i] != cls.y[j]
        (max(0, cls.α[j] - cls.α[i]),
         min(cls.C, cls.C - cls.α[i] + cls.α[j]))
    else
        (max(0, cls.α[j] + cls.α[i] - cls.C),
         min(cls.C, cls.α[j] + cls.α[i]))
    end
end

function calc_b(cls, i)
    1 / cls.y[i] - (cls.α .* cls.y) ⋅ cls.K[i, :]
end

function get_sv_ids(cls)
    f((_,α)) = α > eps() && α + eps() < cls.C
    d((i, _)) = i
    return collect(d.(filter(f, collect(enumerate(cls.α)))))
end

function calc_b_sv(cls)
    is = get_sv_ids(cls)
    if size(is)[1] == 0
        f1((_, α)) = α > eps()
        αs = filter(f1, collect(enumerate(cls.α)))
        g((i, _)) = calc_b(cls, i)
        if size(αs)[1] == 0
            return 0
        end
        return mapreduce(g, +, αs) / size(αs)[1]
    end
    return calc_b(cls, is[1])
end

function calc_error(cls, i)
    (cls.α .* cls.y) ⋅ cls.K[i, :] - cls.y[i]
end

function predict(cls, x)
    K = calc_K(cls.kernel, [x], cls.X)
    return sum((cls.α .* cls.y) .* K[1, :]) + cls.b
end

function rand_neq(r, i)
    n = rand(r)
    while n == i
        n = rand(r)
    end
    return n
end
