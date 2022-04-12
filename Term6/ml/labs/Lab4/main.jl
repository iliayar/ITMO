
include("input.jl")
include("utils.jl")
include("ngramm.jl")
include("bayes.jl")

# println(read_message("data/part1/11003spmsg97.txt"))
# println(read_dataset("data/part1"))
# show(read_data("data"))
# show(build_ngramm_datasets(read_data("data"))[1])
# show(cross_validation_const(read_data("data"))[1][2])

################3

# dss = read_data("data")
# ds1 = extract_classes(dss[1])
# eb, ee = prep_dataset(ds1)

# clf = mk_bayes_clf(1., Dict(:spam => 1., :legal => 1.))
# fit(clf, eb)
# println(predict(clf, dss[2].events[4].message.body))
# println(dss[2].events[4].class)


##############3

# println(f_score([:y, :n, :y, :y, :n], [:y, :n, :y, :y, :y]))

#############

dss = build_ngramm_datasets(read_data("data"); N=1, N_SUBJ=1)

cross_validation(dss) do X_train, y_train, X_test
    X_train_subj, X_train_body = prep_train_dataset(X_train)
    X_test_subj, X_test_body = prep_test_dataset(X_test)
    clf_subj = mk_bayes_clf(1.0, Dict(:spam => 1.0, :legal => 1.0))
    clf_body = mk_bayes_clf(1.0, Dict(:spam => 1.0, :legal => 1.0))
    fit(clf_subj, X_train_subj)
    fit(clf_body, X_train_body)
    pred = (x_subj, x_body) -> argmax(sum_dicts(predictw(clf_subj, x_subj), predictw(clf_body, x_body)))
    return collect(map(pred, X_test_subj, X_test_body))
end
