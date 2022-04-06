
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
        deleteat!(X, sort(ixs))
    end
    return res
end

function split_samples(Xi::Vector{T}, n::Int64)::Vector{Vector{T}} where {T}
    X = copy(Xi)
    res = []
    while size(X)[1] > 0
        push!(res, sample(X, n; do_delete=true))
    end
    return res
end

function split_classes(X, y; k::Int64 = 100)::Vector{Vector{Tuple{Any, Any}}}
    cs = Dict()
    for (Xi, yi) in zip(X, y)
        if !(yi in keys(cs))
            cs[yi] = []
        end
        push!(cs[yi], Xi)
    end
    nb = Int64(ceil(size(X)[1] / k))
    res::Vector{Vector{Tuple{Any, Any}}} = repeat([[]], nb)
    i = 1
    for yi in keys(cs)
        for Xi in cs[yi]
            push!(res[i], (Xi, yi))
            i = i % nb + 1
        end
    end
    return res
end

function cross_validation_with(splitf, X, y; k::Int64 = 100)
    ss = splitf(X, y; k=k)
    res = []
    for i ∈ 1:size(ss)[1]
        X_test, y_test = unzip(ss[i])
        X_train, y_train = unzip(vcat(ss[Not(i)]...))
        push!(res, (X_train, y_train, X_test, y_test))
    end
    return res
end

function cross_validation_split(X, y; k::Int64 = 100)
    return cross_validation_with(split_classes, X, y; k=k)
end

function shuffle_split(X, y; k::Int64 = 100)
    return cross_validation_with((X, y; k::Int64 = 100) -> split_samples(collect(zip(X, y)), k), X, y; k=k)
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
