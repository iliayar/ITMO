using DataFrames
import LinearAlgebra: norm

function dataframe_to_vector(df)
    collect(map(collect, eachrow(df)))
end
