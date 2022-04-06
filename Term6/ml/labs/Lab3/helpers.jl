using DataFrames
import LinearAlgebra: norm

# function one_hot!(df, column)
#     Y = DataFrame()
#     classes_col = df[!, column]
#     classes = Set(classes_col)

#     for c in classes
#         ncol = zeros(length(classes_col))
#         map!(cl -> cl == c ? 1 : 0, ncol, classes_col)
#         Y[!, c] = ncol
#     end

#     select!(df, Not(column))
#     return Y
# end

# function normalize_col!(col)
#     mi, ma = minimum(col), maximum(col)
#     map!(x -> (x - mi) / (ma - mi), col, col)
# end

# function normalize!(df)
#     for c ∈ eachcol(df)
#         normalize_col!(c)
#     end
# end

function dataframe_to_vector(df)
    collect(map(collect, eachrow(df)))
end

function get_pred_class(y)
    mi = 0
    m = 0
    i = 0
    for p ∈ y
        if p > m
            mi = i
            m = p
        end
        i += 1
    end

    return mi + 1
end

function dataframe_radius(df, dist)
    m = 0
    for x1 in eachrow(df)
        for x2 in eachrow(df)
            d = dist(collect(x1), collect(x2))
            m = max(m, d)
        end
    end
    m
end
