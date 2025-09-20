using DataFrames
import LinearAlgebra: norm

function one_hot!(df, column)
    Y = DataFrame()
    classes_col = df[!, column]
    classes = Set(classes_col)

    for c in classes
        ncol = zeros(length(classes_col))
        map!(cl -> cl == c ? 1 : 0, ncol, classes_col)
        Y[!, c] = ncol
    end

    select!(df, Not(column))
    return Y
end

function normalize_col!(col)
    mi, ma = minimum(col), maximum(col)
    map!(x -> (x - mi) / (ma - mi), col, col)
end

function normalize!(df)
    for c ∈ eachcol(df)
        normalize_col!(c)
    end
end
