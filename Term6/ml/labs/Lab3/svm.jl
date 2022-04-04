using DataFrames

function cross_validation(a, X::Vector{Vector{Float64}}, y_true::Vector{Vector{Float64}}; k=100)
    pred::Vector{Vector{Float64}} = []
    for (X_train, y_train, X_test, y_test) ∈ cross_validation_split(X, y_true; k=k)
        push!(pred, accuracy(a(X_train, y_train, X_test), y_test))
    end
    return sum(pred) / size(pred)[1]
end
