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
