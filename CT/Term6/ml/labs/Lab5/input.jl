using DataFrames
using CSV

function dataframe_to_vector(df)
    collect(map(collect, eachrow(df)))
end

Feature = Float64
Class = Symbol

struct Object
    x::Vector{Feature}
    y::Class
end

function read_dataframe_raw(filename)::Tuple{Vector{Vector{Float64}}, Vector{Class}}
    df = CSV.read(filename, DataFrame);
    classes = map(c -> c == "P" ? :P : :N, df[!, "class"])
    return (dataframe_to_vector(df[!, ["x", "y"]]), classes)
end

function read_dataframe(filename)::Vector{Object}
    (X, y) = read_dataframe_raw(filename)
    return map(Object, X, y)
end
