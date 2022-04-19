
abstract type Node end

struct Leaf <: Node
    class::Class
end

struct Branch <: Node
    feature_id::Int64
    thresh::Float64

    left::Node
    right::Node
end

mutable struct DecisionTree <: Classifier
    max_depth::Union{Int64, Nothing}
    nclasses::Union{Int64, Nothing}
    nfeatures::Union{Int64, Nothing}
    root::Union{Node, Nothing}
    thresh_by_fun
end

function mk_find_thresh_fun(name::Symbol)
    if name == :entropy
        return thresh_by_entropy
    elseif name == :gini
        return thresh_by_gini
    end
end

function mk_decision_tree(;max_depth=nothing, nclasses=nothing, nfeatures=nothing, find_thresh_fun_name::Symbol=:entropy)::DecisionTree
    return DecisionTree(max_depth, nclasses, nfeatures, nothing, mk_find_thresh_fun(find_thresh_fun_name))
end

function has_same_classes(objects::Vector{Object})::Bool
    f(obj::Object) = obj.y
    return maximum(f, objects) == minimum(f, objects)
end

function entropy(a::Vector{T})::Float64 where {T}
    n::T = sum(a)
    return -sum(x -> (x / n) * log(x / n), filter(x -> x > 0, a))
end

function find_major_class(objects::Vector{Object})::Class
    nc::Dict{Class, Int64} = Dict()
    for obj ∈ objects
        if obj.y ∉ keys(nc)
            nc[obj.y] = 0
        end
        nc[obj.y] += 1
    end
    return argmax(nc)
end

thresh_by_entropy(lc, rc) = entropy(values(lc) |> collect) * sum(values(lc)) + entropy(values(rc) |> collect) * sum(values(rc))
function thresh_by_gini(lc, rc)
    sl = sum(values(lc))
    sr = sum(values(rc))
    return (1 - sum(x -> (x / sl)^2 , values(lc))) * sl + (1 - sum(x -> (x / sr)^2, values(rc))) * sr
end

function find_thresh_by(clf::DecisionTree, objects::Vector{Object}, weights::Vector{Float64})::Union{Tuple{Float64, Int64}, Nothing}
    bsc::Union{Float64, Nothing} = nothing
    br::Union{Tuple{Float64, Int64}, Nothing} = nothing
    for i ∈ 1:clf.nfeatures
        sort!(objects, by=x->x.x[i])
        if objects[1].x[i] == objects[end].x[i]
            continue
        end

        lc::Dict{Class, Float64} = Dict()
        rc::Dict{Class, Float64} = Dict()
    
        for (obj, w) ∈ zip(objects, weights)
            if obj.y ∉ keys(rc)
                rc[obj.y] = 0
                lc[obj.y] = 0
            end
            rc[obj.y] += w
        end
    
        pxi = nothing
        for j ∈ 1:size(objects)[1]
            obj = objects[j]
            w = weights[j]
            if j != 1 && obj.x[i] != pxi
                sc::Float64 = clf.thresh_by_fun(lc, rc)
                if isnothing(bsc) || bsc > sc
                    br = ((pxi + obj.x[i]) / 2, i)
                    bsc = sc
                end
            end
    

            rc[obj.y] -= w 
            lc[obj.y] += w
            pxi = obj.x[i]
        end
    end
    return br
end

function make_node(clf::DecisionTree, objects::Vector{Object}, weights::Vector{Float64}; depth=0)::Node
    if has_same_classes(objects) || (!isnothing(clf.max_depth) && clf.max_depth <= depth)
        return Leaf(find_major_class(objects))
    end

    br = find_thresh_by(clf, objects, weights)
    if !isnothing(br)
        fi = br[2]
        thresh = br[1]
        p = o -> o.x[fi] < thresh
        li = p.(objects)
        ri = (!).(p.(objects))
        l = make_node(clf, objects[li], weights[li]; depth=depth+1)
        r = make_node(clf, objects[ri], weights[ri]; depth=depth+1)
        return Branch(fi, thresh, l, r)
    else
        return Leaf(find_major_class(objects))
    end
end

function fit(clf::DecisionTree, objects::Vector{Object}; weights::Union{Vector{Float64}, Nothing}=nothing)
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
    clf.root = make_node(clf, objects, weights)
end

function predict(clf::DecisionTree, x::Vector{Feature})::Class
    return predict_impl(clf.root, x)
end

function predict_impl(node::Leaf, _::Vector{Feature})::Class
    return node.class
end

function predict_impl(node::Branch, x::Vector{Feature})::Class
    if x[node.feature_id] < node.thresh
        return predict_impl(node.left, x)
    else
        return predict_impl(node.right, x)
    end
end
