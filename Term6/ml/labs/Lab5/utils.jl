
unzip(a) = map(x->getfield.(a, x), fieldnames(eltype(a)))

function get_stats(objects::Vector{Object})::Tuple{Int64,Int64}
    nfeatures = size(objects[1].x)[1]
    nclasses = size(unique(map(x -> x.y, objects)))[1]
    return (nfeatures, nclasses)
end

function gen_fibs(n::Int64)::Vector{Int64}
    res = [1, 2]
    for i in 3:n
        push!(res, res[i - 1] + res[i - 2])
    end
    return res
end
