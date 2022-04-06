using CSV
using DataFrames

include("utils.jl")
include("helpers.jl")
include("valid.jl")
include("svm.jl")
include("find_best.jl")

function read_dataframe(filename)::Tuple{Vector{Vector{Float64}}, Vector{Float64}}
    df = CSV.read(filename, DataFrame);
    classes = map(c -> if c == "P" 1 else -1 end, df[!, "class"])
    return (dataframe_to_vector(df[!, ["x", "y"]]), classes)
end

# X, y = read_dataframe("./data/chips.csv")

# score = cross_validation(X, y; k = 20) do X_train, y_train, X_test
#     println("Algo run with:")
#     println("  - ", X_train)
#     println("  - ", y_train)
#     println("  - ", X_test)
#     println(size(X_train)[1], " ", size(X_test)[1])
#     return ones(size(X_test)[1])
# end

# println("Score: ", score)
