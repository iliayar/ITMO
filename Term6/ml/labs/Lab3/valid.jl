include("helpers.jl")

function make_conj_matrix(y::Vector{Vector{Float64}}, y_true::Vector{Vector{Float64}})
    nc = size(y_true[1])[1]
    res = zeros(nc, nc)
    for (p, p_true) ∈ zip(y, y_true)
        c = get_pred_class(p)
        c_true = get_pred_class(p_true)
        res[c_true, c] += 1
    end
    res
end


function f_score(y::Vector{Vector{Float64}}, y_true::Vector{Vector{Float64}})
    cm = make_conj_matrix(y, y_true)
    nclasses = size(y_true[1])[1]

    res = 0

    for c ∈ 1:nclasses
        TP, TN, FP, FN = 0, 0, 0, 0
        for i ∈ 1:nclasses
            for j in 1:nclasses
                if i == c && j == c
                    TP += cm[i, j]
                end
                if i != c && j == c
                    FP += cm[i, j]
                end
                if i == c && j != c
                    FN += cm[i, j]
                end
                if i != c && j != c
                    TN += cm[i, j]
                end
            end
        end
        Prec = TP + FP == 0 ? 0 : TP / (TP + FP)
        Rec = TP + FN == 0 ? 0 : TP / (TP + FN)
        F = Prec + Rec == 0 ? 0 : 2 * (Prec * Rec) / (Prec + Rec)

        res += F * sum(cm[c, :])
    end

    res / sum(cm)
end
