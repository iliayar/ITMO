

Events = Vector{Tuple{Symbol, Vector{NGrammWord}}}

function prep_train_dataset(events::Vector{Event})::Tuple{Events, Events}
    res_body = []
    res_subj = []
    for e in events
        push!(res_body, (e.class, e.message.body))
        push!(res_subj, (e.class, e.message.subject))
    end
    return (res_body, res_subj)
end

function prep_test_dataset(events::Vector{Event})::Tuple{Vector{Vector{NGrammWord}}, Vector{Vector{NGrammWord}}}
    res_body = []
    res_subj = []
    for e in events
        push!(res_body, e.message.body)
        push!(res_subj, e.message.subject)
    end
    return (res_body, res_subj)
end

mutable struct Bayes
    α::Float64
    λs::Dict{Symbol, Float64}
    ne_c::Dict{Symbol, Int64}
    ne_wc::Dict{Symbol, Dict{NGrammWord, Int64}}
    ws::Set{NGrammWord}
    ne::Int64
    classes::Set{Symbol}
end

function mk_bayes_clf(α::Float64, λs::Dict{Symbol, Float64})::Bayes
    return Bayes(α, λs, Dict(), Dict(), Set(), 0, Set())
end

function fit(clf::Bayes, events::Events)
    for (c, ws) ∈ events
        push!(clf.classes, c)
        clf.ne += 1

        if c ∉ keys(clf.ne_c)
            clf.ne_c[c] = 0
        end
        if c ∉ keys(clf.ne_wc)
            clf.ne_wc[c] = Dict()
        end
        clf.ne_c[c] += 1

        ws_set::Set{NGrammWord} = Set()
        for w ∈ ws
            push!(ws_set, w)
        end

        for w ∈ ws_set
            push!(clf.ws, w)

            if w ∉ keys(clf.ne_wc[c])
                clf.ne_wc[c][w] = 0
            end
            clf.ne_wc[c][w] += 1
        end
    end

    for c ∈ clf.classes
        for w ∈ clf.ws
            if w ∉ keys(clf.ne_wc[c])
                clf.ne_wc[c][w] = 0
            end
        end
    end

    # println(clf.ws)
end

function predictw(clf::Bayes, msg::Vector{NGrammWord})::Dict{Symbol, Float64}
    ws::Set{NGrammWord} = Set()
    res::Dict{Symbol, Float64} = Dict()

    for w ∈ msg
        push!(ws, w)
    end

    for c ∈ clf.classes
        r::Float64 = log(clf.ne_c[c]) - log(clf.ne) + log(clf.λs[c])
        for w ∈ clf.ws
            nom::Float64 = clf.ne_wc[c][w] + clf.α
            denom::Float64 = clf.ne_c[c] + 2 * clf.α
            if w ∈ ws
                r += log(nom)
            else
                r += log(denom - nom)
            end
            r -= log(denom)
        end
        res[c] = r
    end

    # mp::Float64 = maximum(res)
    # st::Float64 = log(mapreduce(p -> exp(p - mp), +, res)) + mp
    # return collect(map(x -> exp(x - st), res))
    return res
end

function predict(clf::Bayes, msg::Vector{NGrammWord})::Symbol
    res = predictw(clf, msg)
    return argmax(res)
end

function sum_dicts(dl, dr)
    d = Dict()
    for k in keys(dl)
        d[k] = dl[k]
    end
    for k in keys(dl)
        if k ∉ keys(d)
            d[k] = dr[k]
        else
            d[k] += dr[k]
        end
    end
    return d
end
