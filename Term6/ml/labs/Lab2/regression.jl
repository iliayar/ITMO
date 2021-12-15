
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

function gradient_descent(objs::Vector{Object}, init::Vector{Float64}, loss::Loss)::Vector{Float64}
    # X, y = split_objects(objs)

    w = init
    w_grad = loss.grad(w)

    while norm(w_grad) >= eps() do
        X, y = sample(objs, b) |> split_objects
	for i in 1:size(X)[1]
        end
    end
end
