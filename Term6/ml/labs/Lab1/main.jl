using DataFrames

function one_hot(df, column)
    classes_col = df[!, column]
    classes = Set(classes_col)

    for c in classes
        ncol = zeros(length(classes_col))
        map!(cl -> cl == c ? 1 : 0, ncol, classes_col)
        df[!, "class_$(c)"] = ncol
    end
end
