include("main.jl")

raw_ds = read_data("data")
n = [1, 2, 3]
α = map(exp, range(log(0.01), log(2), length=10)) |> collect

params = Iterators.product(n, α)

res = []

for (n, α) ∈ params
    ds = build_ngramm_datasets(raw_ds; N=n, N_SUBJ=n)
    score = cross_validation(ds) do X_train, y_train, X_test
        X_train_subj, X_train_body = prep_train_dataset(X_train)
        X_test_subj, X_test_body = prep_test_dataset(X_test)
        clf_subj = mk_bayes_clf(NGrammWord, α, Dict(:spam => 1.0, :legal => 1.0))
        clf_body = mk_bayes_clf(NGrammWord, α, Dict(:spam => 1.0, :legal => 1.0))
        fit(clf_subj, X_train_subj)
        fit(clf_body, X_train_body)
        pred = (x_subj, x_body) -> argmax(sum_dicts(predictw(clf_subj, x_subj), predictw(clf_body, x_body)))
        return collect(map(pred, X_test_subj, X_test_body))
    end

    println("score\tn\tα")
    println(score, "\t", n, "\t", α)
    println("===================================")

    push!(res, (score, (n, α)))
end

acc, params = maximum(res)

println("Best:\t", acc)
println("Params:\t", params)

