
unzip(a) = map(x->getfield.(a, x), fieldnames(eltype(a)))

function get_stats(objects::Vector{Object})::Tuple{Int64,Int64}
    nfeatures = size(objects[1].x)[1]
    nclasses = size(unique(map(x -> x.y, objects)))[1]
    return (nfeatures, nclasses)
end
