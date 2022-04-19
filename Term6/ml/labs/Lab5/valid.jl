using StatsBase: sample
using DataFrames

function split_train_test(objects::Vector{Object}; ratio=0.3)::Tuple{Vector{Object}, Vector{Object}}
    ids = sample(1:size(objects)[1], round(size(objects)[1] * ratio) |> Int64, replace=false)
    return (objects[Not(ids)], objects[ids])
end

function accuracy(y::Vector{Class}, y_true::Vector{Class})::Float64
    mapreduce((p, t) -> p == t ? 1 : 0, +, y, y_true) / size(y)[1]
end

function make_conj_matrix(y::Vector{Class}, y_true::Vector{Class})
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

function f_score(y::Vector{Class}, y_true::Vector{Class})::Float64
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

function estimate(clf::Classifier, test::Vector{Object}; score=f_score, predict_kwargs=())::Float64
    yp = [convert(Class, predict(clf, o.x; predict_kwargs...)) for o in test]
    y = [o.y for o in test]

    return f_score(yp, y)
end
