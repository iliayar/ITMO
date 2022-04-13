include("main.jl")

n, α = (1, 0.010000000000000004)
ratio = 0.6842105263157895

ds = build_ngramm_datasets(read_data("data"); N=n, N_SUBJ=n)
X, y = unzip(vcat(map(extract_classes, ds)...))

# λ_legit = map(exp, range(log(0.01), log(2); length=10))

λ_legit = 1.

res = []

# for λ_legit ∈ λ_legit
while true
    function score_strict(y, y_true)
        mapreduce(min, y, y_true) do p, t
            if t == :legal && p == :spam
                -Inf
            else
                accuracy(y, y_true)
            end
        end
    end

    score = cross_validation(ds; score=score_strict) do X_train, y_train, X_test
        X_train_subj, X_train_body = prep_train_dataset(X_train)
        X_test_subj, X_test_body = prep_test_dataset(X_test)
        clf_subj = mk_bayes_clf(NGrammWord, α, Dict(:legal => λ_legit, :spam => 1.))
        clf_body = mk_bayes_clf(NGrammWord, α, Dict(:legal => λ_legit, :spam => 1.))
        fit(clf_subj, X_train_subj)
        fit(clf_body, X_train_body)
        pred = (x_subj, x_body) -> argmax(sum_dicts(predictw(clf_body, x_body), predictw(clf_subj, x_subj); ratio = ratio))
        return collect(map(pred, X_test_subj, X_test_body))
    end
    
    # X_train_subj, X_train_body = prep_train_dataset(X)
    # X_test_subj, X_test_body = prep_test_dataset(X)
    # clf_subj = mk_bayes_clf(NGrammWord, α, Dict(:legal => λ_legit, :spam => 1.))
    # clf_body = mk_bayes_clf(NGrammWord, α, Dict(:legal => λ_legit, :spam => 1.))
    # fit(clf_subj, X_train_subj)
    # fit(clf_body, X_train_body)
    # pred = (x_subj, x_body) -> argmax(sum_dicts(predictw(clf_body, x_body), predictw(clf_subj, x_subj); w = w))

    # score = score_strict(map(pred, X_test_subj, X_test_body), y)

    println("score\tλ_legit")
    println(score, "\t", λ_legit)
    println("=========================")

    push!(res, (score, λ_legit))

    if score != -Inf
        break
    end

    global λ_legit *= 10
end

acc, params = maximum(res)

println("Best:\t", acc)
println("Params:\t", params)
