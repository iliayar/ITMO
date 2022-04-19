include("main.jl")

ds = read_dataframe("./data/chips.csv")

## Decision Tree

# dt = mk_decision_tree(max_depth=4)

# fit(dt, ds)
# println(dt.root)


## Random Forest

# rf = mk_random_forest()

# fit(rf, ds)

# for i in rand(1:size(ds)[1], 10)
#     o = ds[i]

#     yp = predict(rf, o.x)
#     println(yp, " ", o.y)
# end

## AdaBoost

# adaboost = mk_ada_boost([mk_decision_tree(max_depth=2) for _ in 1:100], 1.)
# fit(adaboost, ds)

# for i in rand(1:size(ds)[1], 10)
#     o = ds[i]

#     yp = predict(adaboost, o.x; negative_class=2.)
#     println(yp, " ", o.y)
# end

## AdaBoost Score

# train, test = split_train_test(ds; ratio=0.3)
# println(size(train), " ", size(test))
train = ds
test = ds

adaboost = mk_ada_boost([mk_decision_tree(max_depth=2, find_thresh_fun_name=:entropy) for _ in 1:100], :P)
fit(adaboost, train)

yp = [convert(Class, predict(adaboost, o.x; negative_class=:N)) for o in test]
y = [o.y for o in test]

# rf = mk_random_forest(;dt_params=(:find_thresh_fun_name => :gini,), ntrees=1000)
# fit(rf, train)

# yp = [convert(Class, predict(rf, o.x)) for o in test]
# y = [o.y for o in test]

println("FScore: ", f_score(yp, y))
println("Accuracy: ", accuracy(yp, y))
