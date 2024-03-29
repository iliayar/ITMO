include("main.jl")

n, α = (1, 0.010000000000000004)

ds = build_ngramm_datasets(read_data("data"); N=n, N_SUBJ=n)

ratios = range(0, 1; length=20)

res = []

for ratio ∈ ratios
    score = cross_validation(ds; score=f_score) do X_train, y_train, X_test
        X_train_subj, X_train_body = prep_train_dataset(X_train)
        X_test_subj, X_test_body = prep_test_dataset(X_test)
        clf_subj = mk_bayes_clf(NGrammWord, α, Dict(:legal => 1.0, :spam => 1.0))
        clf_body = mk_bayes_clf(NGrammWord, α, Dict(:legal => 1.0, :spam => 1.0))
        fit(clf_subj, X_train_subj)
        fit(clf_body, X_train_body)
        pred = (x_subj, x_body) -> argmax(sum_dicts(predictw(clf_body, x_body), predictw(clf_subj, x_subj); ratio = ratio))
        return collect(map(pred, X_test_subj, X_test_body))
    end

    println("score\tw")
    println(score, "\t", ratio)
    println("=========================")

    push!(res, (score, ratio))
end

acc, params = maximum(res)

println("Best:\t", acc)
println("Params:\t", params)
