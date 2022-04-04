include("helpers.jl")

function accuracy(y::Vector{Float64}, y_true::Vector{Float64})
    mapreduce((p, t) -> p * t > 0 ? 1 : 0, y, y_true) / size(y)
end
