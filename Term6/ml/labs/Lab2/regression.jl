
include("object.jl")
include("utils.jl")
include("loss.jl")

using LinearAlgebra

function least_squares(objs::Vector{Object})::Vector{Float64}
    X, y = split_objects(objs)
    U, S, V = svd(X)
    f(v, l, u) = u * v' / sqrt(l)
    FPlus = mapreduce(f, +, eachcol(U), S, eachrow(V))
    Θ = FPlus * y
    return Θ
end

b = 20
μ = 1

function gradient_descent(objs::Vector{Object}, init::Vector{Float64}, loss::Loss)::Vector{Float64}
    # X, y = split_objects(objs)

    w = init

    while true do
        batch = sample(objs, b)
        f(o::Object) = loss.calc(o.y, w * o.X) * o.X
        grad = mapreduce(f, +, batch)
        if norm(grad) < eps()
            break
        end
        w -= μ * grad
    end
end
    
