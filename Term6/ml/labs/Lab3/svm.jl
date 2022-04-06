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

            ei = calc_error(cls, i)
            ej = calc_error(cls, j)

            old_αi = cls.α[i]
            old_αj = cls.α[j]

            L, H = get_bounds(cls, i, j)
            if H == L
                continue
            end

            η = 2 * cls.kernel(X[i], X[j]) - cls.kernel(X[i], X[i]) - cls.kernel(X[j], X[j])
            if η >= 0
                continue
            end

            cls.α[j] = max(L, min(H, old_αj + (y[j] * (ej - ei)) / η))
            if abs(cls.α[j] - old_αj) < eps()
                continue
            end

            cls.α[i] = old_αi + y[i]*y[j] * (old_αj - cls.α[j])

            b1 = cls.b - ei - y[i] * (cls.α[i] - old_αi) * cls.kernel(X[i], X[i]) - y[j] * (cls.α[j] - old_αj) * cls.kernel(X[i], X[j])
            b2 = cls.b - ej - y[i] * (cls.α[i] - old_αi) * cls.kernel(X[i], X[j]) - y[j] * (cls.α[j] - old_αj) * cls.kernel(X[j], X[j])

            cls.b = if 0 < cls.α[i] < cls.C
                b1
            elseif 0 < cls.α[j] < cls.C
                b2
            else
                (b1 + b2) / 2
            end
        end
        if norm(cls.α - prev_α) < eps()
            break
        end
    end
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

function calc_error(cls, i)
    predict(cls, cls.X[i]) - cls.y[i]
end

function predict(cls, x)
    return mapreduce((αi, xi, yi) -> αi * yi * cls.kernel(xi, x), +, cls.α, cls.X, cls.y) + cls.b
end

function rand_neq(r, i)
    n = rand(r)
    while n == i
        n = rand(r)
    end
    return n
end
