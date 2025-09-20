

mutable struct AdaBoost{T <: Classifier}
    algorithms::Vector{T}
    weights::Union{Vector{Float64}, Nothing}
    algo_weights::Vector{Float64}
    positive_class::Union{Class, Nothing}
    bs::Union{Vector{Float64}, Nothing}
end

function convert_class(clf::AdaBoost, y::Class)::Int64
    return y == clf.positive_class ? 1 : -1
end

function mk_ada_boost(algorithms::Vector{T}; positive_class::Union{Class, Nothing}=nothing)::AdaBoost where {T <: Classifier}
    return AdaBoost(algorithms, nothing, zeros(size(algorithms)[1]), positive_class, nothing)
end

function fit(clf::AdaBoost{T}, objects::Vector{Object}; cb=(_, _) -> ()) where {T <: Classifier}
    if isnothing(clf.positive_class)
        clf.positive_class = objects[1].y
    end

    clf.weights = [1 / size(objects)[1] for _ in 1:size(objects)[1]]
    clf.bs = []
    i = 1
    for algo in clf.algorithms
        fit(algo, objects; weights=clf.weights)
        preds = map(o -> predict(algo, o.x), objects)
        N = mapreduce((o, yp, w) -> (o.y != yp ? 1 : 0) * w, +, objects, preds, clf.weights)
        b = 1 / 2 * log((1 - N) / N)
        for i in 1:size(clf.weights)[1]
            clf.weights[i] *= exp(-b * convert_class(clf, objects[i].y) * convert_class(clf, preds[i]))
        end
        clf.weights /= sum(clf.weights)
        push!(clf.bs, b)

        println(N, " | ", b)
        println("[", size(clf.bs)[1], "/", size(clf.algorithms)[1], "] Algos trained")
        cb(clf, i)
        i += 1
    end
    println(clf.weights)
end

function predictw(clf::AdaBoost{T}, x::Vector{Feature})::Float64 where {T <: Classifier}
    return mapreduce((algo, b) -> b * convert_class(clf, predict(algo, x)), +, clf.algorithms, clf.bs)
end

function predict(clf::AdaBoost{T}, x::Vector{Feature}; negative_class::Union{Class, Nothing}=nothing)::Union{Class, Nothing} where {T <: Classifier}
    return sign(predictw(clf, x)) == 1 ? clf.positive_class : negative_class
end
