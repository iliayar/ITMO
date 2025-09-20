function accuracy(y::Vector{Float64}, y_true::Vector{Float64})::Float64
    mapreduce((p, t) -> p * t > 0 ? 1 : 0, +, y, y_true) / size(y)[1]
end
