
include("object.jl")

unzip(a) = map(x->getfield.(a, x), fieldnames(eltype(a)))

function split_objects(objs::Vector{Object})::Tuple{Matrix{Float64}, Vector{Float64}}
    X, y = unzip(objs)
    (reduce(hcat, X)', y)
end

function sample{T}(X::Vector{T}, n::Int64)::Vector{T} where {T}
    ixs = []
    for _ in 1:n
        push!(ixs, rand(1:size(X)[1]))
    end
    return X[ixs]
end
