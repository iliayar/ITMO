
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
    X, y = split_objects(objs)

    w = init
    w_grad = loss.grad(x)

    while norm(x_grad) >= eps() do
        
	
    end
end
