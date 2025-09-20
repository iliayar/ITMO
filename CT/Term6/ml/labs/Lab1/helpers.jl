using DataFrames

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
