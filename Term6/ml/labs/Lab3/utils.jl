
unzip(a) = map(x->getfield.(a, x), fieldnames(eltype(a)))

# function split_objects(objs::Vector{T})::Tuple{, Vector{Float64}} where {T}
#     X, y = unzip(objs)
#     (reduce(hcat, X)', y)
# end

function sample(X::Vector{T}, n::Int64; do_delete::Bool=false)::Vector{T} where {T}
    ixs = []
    for _ in 1:min(n, size(X)[1])
        while true
            i = rand(1:size(X)[1])
            if i ∉ ixs
                push!(ixs, i)
                break
            end
        end
    end
    res = X[ixs]
    if do_delete
        for i in ixs
            deleteat!(X, i)
        end
    end
    return res
end

function split_samples(Xi::Vector{T}, n::Int64)::Vector{Vector{T}} where {T}
    X = copy(Xi)
    res = []
    while size(X)[1] > 0
        append!(res, sample(Xi, n; do_delete=true))
    end
end

function cross_validation_split(X::Vector{T}, y::Vector{E}; k::Int64 = 100)::Vector(Tuple{Vector{T}, Vector{E}, Vector{T}, Vector{E}}) where {T, E}
    ss = split_samples(zip(X, y), k)
    res = []
    for i ∈ 1:size(ss)[1]
        X_test, y_test = unzip(ss[i])
        X_train, y_train = unzip(vcat(ss[Not(i)]...))
        append!(res, (X_train, y_train, X_test, y_test))
    end
    return res
end

# function my_normalize!(objs::Vector{Object})
#     r = 1:size(objs[1].X)[1]
#     mi = map(i -> minimum(map(o -> o.X[i], objs)), r)
#     ma = map(i -> maximum(map(o -> o.X[i], objs)), r)
#     ymi = minimum(map(o -> o.y, objs))
#     yma = maximum(map(o -> o.y, objs))
#     for o in objs
#         for i in r
#             if mi[i] == ma[i]
#                 o.X[i] = 1
#             else
#                 o.X[i] = (o.X[i] - mi[i]) / (ma[i] - mi[i])
#             end
#         end
#         o.y = (o.y - ymi) / (yma - ymi)
#     end

# end

# function find_best(v)
#     ma = Inf
#     mi = -1
#     for i in 1:size(v)[1]
#         if v[i][1] < ma
#             ma = v[i][1]
#             mi = i
#         end
#     end
#     return v[mi]
# end
