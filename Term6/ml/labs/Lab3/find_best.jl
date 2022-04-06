
function find_best(X, y)
    res = []

    ds = collect(2:5)
    βs = collect(1:5)
    Cs = [0.05, 0.1, 0.5, 1.0, 5.0, 10.0, 50.0, 100.0]
    kerns = [:linear, :polynomial, :gauss]

    for kern in kerns
        kern_params = if kern == :linear
            [()]
        elseif kern == :polynomial
            ds
        elseif kern == :gauss
            βs
        end
        for kern_param in kern_params
            for C in Cs
                acc = cross_validation(X, y; k = 50) do X_train, y_train, X_test
                    cls = mk_svc(kern, kern_param, size(X_train)[1]; C = C)
                    fit_svc(cls, X_train, y_train)
                    r = collect((x -> predict(cls, x)).(X_test))
                    return r
                end
                # return []
                params = (kern, kern_param, C)
                println("Accuracy ", acc, "\tWith params ", params)
                push!(res, (acc, params))
            end
        end
    end
    return res
end

function best_by_kernels(res)
    d = Dict()
    d[:linear] = (0, nothing)
    d[:polynomial] = (0, nothing)
    d[:gauss] = (0, nothing)

    for (acc, params) in res
        kern = params[1]
        cur_acc, _ = d[kern]
        if cur_acc < acc
            d[params[1]] = (acc, params)
        end
    end
    return d
end
