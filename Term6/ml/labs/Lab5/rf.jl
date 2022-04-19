using StatsBase: sample

mutable struct RandomForest <: Classifier
    dt_params
    ntrees::Int64
    nfeatures::Union{Int64, Nothing}
    nclasses::Union{Int64, Nothing}
    trees::Vector{Tuple{Vector{Int64}, DecisionTree}}
    positive_class::Union{Class, Nothing}
end

function mk_random_forest(;dt_params=(), ntrees=100, positive_class::Union{Class, Nothing}=nothing)::RandomForest
    return RandomForest(dt_params, ntrees, nothing, nothing, [], nothing)
end


function fit(clf::RandomForest, objects::Vector{Object}; weights::Union{Vector{Float64}, Nothing}=nothing)
    if isnothing(weights)
        weights = ones(size(objects)[1])
    end
    nfeatues, nclasses = get_stats(objects)
    if isnothing(clf.nfeatures)
        clf.nfeatures = nfeatues
    end
    if isnothing(clf.nclasses)
        clf.nclasses = nclasses
    end
    if isnothing(clf.positive_class)
        clf.positive_class = objects[1].y
    end
    while size(clf.trees)[1] < clf.ntrees
        push!(clf.trees, build_tree(clf, objects, weights))
        println("[", size(clf.trees)[1], "/", clf.ntrees, "] Building random forest")
    end
end

function select_features(objects::Vector{Object}, features::Vector{Int64})::Vector{Object}
    return map(o -> Object(o.x[features], o.y), objects)
end

function build_tree(clf::RandomForest, objects::Vector{Object}, weights::Vector{Float64})::Tuple{Vector{Int64}, DecisionTree}
    rand_features = sample(1:clf.nfeatures, round(sqrt(clf.nfeatures)) |> Int64; replace = false)
    rand_objects, rand_weights = unzip(rand(zip(objects, weights) |> collect, size(objects)[1]))
    nobjects = select_features(rand_objects, rand_features)
    tree = mk_decision_tree(; nclasses=clf.nclasses, nfeatures=size(rand_features)[1], clf.dt_params...)
    fit(tree, nobjects; weights=rand_weights)
    return (rand_features, tree)
end

function predict_impl(clf::RandomForest, x::Vector{Feature})::Dict{Class, Int64}
    res = Dict()
    for (features, tree) in clf.trees
        y = predict(tree, x[features])
        if y ∉ keys(res)
            res[y] = 0
        end
        res[y] += 1
    end
    return res
end

function predict(clf::RandomForest, x::Vector{Feature})::Class
    res = predict_impl(clf, x)
    return argmax(res)
end

function predictw(clf::RandomForest, x::Vector{Feature})::Float64
    res = predict_impl(clf, x)
    return mapreduce(((y, v),) -> y == clf.positive_class ? v : -v, +, collect(res)) / size(clf.trees)[1]
end
