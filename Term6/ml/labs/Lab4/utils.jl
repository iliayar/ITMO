using DataFrames

unzip(a) = map(x->getfield.(a, x), fieldnames(eltype(a)))

function extract_classes(ds::Dataset{T})::Vector{Tuple{Event{T}, Symbol}} where {T}
    res = []
    for e in ds.events
        push!(res, (e, e.class))
    end
    return res
end

function cross_validation_with(splitf, X, y; k::Int64 = 100)
    ss = splitf(X, y; k=k)
    res = []
    for i ∈ 1:size(ss)[1]
        X_test, y_test = unzip(ss[i])
        X_train, y_train = unzip(vcat(ss[Not(i)]...))
        push!(res, (X_train, y_train, X_test, y_test))
    end
    return res
end


function cross_validation_const(dss::Vector{Dataset{T}}) where {T}
    return cross_validation_with((X, y; k) -> map(extract_classes, dss), nothing, nothing)
end

function cross_validation(a, dss::Vector{Dataset{T}}; scoref = accuracy) where {T}
    acc::Vector{Float64} = []
    for (X_train, y_train, X_test, y_test) ∈ cross_validation_const(dss)
        push!(acc, scoref(a(X_train, y_train, X_test), y_test))
        println("Iteration ", size(acc)[1], "\tAccuracy ", sum(acc) / size(acc)[1])
    end
    return sum(acc) / size(acc)[1]
end


function make_conj_matrix(y::Vector{Symbol}, y_true::Vector{Symbol})
    classes = Set(y) ∪ Set(y_true)
    res = Dict()
    for c1 ∈ classes
        res[c1] = Dict()
        for c2 ∈ classes
            res[c1][c2] = 0
        end
    end
    for (c, c_true) ∈ zip(y, y_true)
        res[c_true][c] += 1
    end
    res
end

function accuracy(y::Vector{Symbol}, y_true::Vector{Symbol})::Float64
    mapreduce((p, t) -> p == t ? 1 : 0, +, y, y_true) / size(y)[1]
end

function f_score(y::Vector{Symbol}, y_true::Vector{Symbol})::Float64
    cm = make_conj_matrix(y, y_true)
    classes = Set(y) ∪ Set(y_true)

    res = 0

    for c ∈ classes
        TP, TN, FP, FN = 0, 0, 0, 0
        for i ∈ classes
            for j in classes
                if i == c && j == c
                    TP += cm[i][j]
                end
                if i != c && j == c
                    FP += cm[i][j]
                end
                if i == c && j != c
                    FN += cm[i][j]
                end
                if i != c && j != c
                    TN += cm[i][j]
                end
            end
        end
        Prec = TP + FP == 0 ? 0 : TP / (TP + FP)
        Rec = TP + FN == 0 ? 0 : TP / (TP + FN)
        F = Prec + Rec == 0 ? 0 : 2 * (Prec * Rec) / (Prec + Rec)

        res += F * sum(values(cm[c]))
    end

    res / sum(map(x -> sum(values(x)), values(cm)))
end
