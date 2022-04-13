
function get_roc_data(a, dss, pc; L=nothing, H=nothing, TICKS=100, LOG=false)
    preds = []
    for (X_train, y_train, X_test, y_test) ∈ cross_validation_const(dss)
        append!(preds, zip(a(X_train, y_train, X_test), y_test))
    end

    if L === nothing
        L = minimum(x -> x[1][pc], preds)
    end
    if H === nothing
        H = maximum(x -> x[1][pc], preds)
    end

    function pred_to_res(x, thresh)
        p, y = x
        if p[pc] >= thresh
            if pc == y
                :TP
            else
                :FP
            end
        else
            if pc == y
                :FN
            else
                :TN
            end
        end 
    end

    function res_to_vec(r)
        if r == :TP
            [1, 0, 0, 0]
        elseif r == :FP
            [0, 1, 0, 0]
        elseif r == :TN
            [0, 0, 1, 0]
        elseif r == :FN
            [0, 0, 0, 1]
        end
    end

    res_fp = []
    res_tp = []

    ra = if LOG
        map(exp, range(log(L), log(H); length=TICKS))
    else
        range(L, H; length=TICKS)
    end

    for thresh ∈ ra
        tp, fp, tn, fn = sum(map(x -> res_to_vec(pred_to_res(x, thresh)), preds))
        push!(res_tp, tp / (tp + fn))
        push!(res_fp, fp / (fp + tn))
    end

    return (res_fp, res_tp)
end
