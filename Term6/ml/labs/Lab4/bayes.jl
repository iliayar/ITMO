

Events{T} = Vector{Tuple{Symbol, Vector{T}}}

function prep_train_dataset(events::Vector{Event{T}})::Tuple{Events{T}, Events{T}} where {T}
    res_body = []
    res_subj = []
    for e in events
        push!(res_body, (e.class, e.message.body))
        push!(res_subj, (e.class, e.message.subject))
    end
    return (res_body, res_subj)
end

function prep_test_dataset(events::Vector{Event{T}})::Tuple{Vector{Vector{T}}, Vector{Vector{T}}} where {T}
    res_body = []
    res_subj = []
    for e in events
        push!(res_body, e.message.body)
        push!(res_subj, e.message.subject)
    end
    return (res_body, res_subj)
end

mutable struct Bayes{T}
    α::Float64
    λs::Dict{Symbol, Float64}
    ne_c::Dict{Symbol, Int64}
    ne_wc::Dict{Symbol, Dict{T, Int64}}
    ws::Set{T}
    ne::Int64
    classes::Set{Symbol}
end

function mk_bayes_clf(T::Type, α::Float64, λs::Dict{Symbol, Float64})::Bayes
    return Bayes{T}(α, λs, Dict(), Dict(), Set(), 0, Set())
end

function fit(clf::Bayes{T}, events::Events{T}) where {T}
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

        ws_set::Set{T} = Set()
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

function predictw(clf::Bayes{T}, msg::Vector{T})::Dict{Symbol, Float64} where {T}
    ws::Set{T} = Set()
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

function predict(clf::Bayes{T}, msg::Vector{T})::Symbol where {T}
    res = predictw(clf, msg)
    return argmax(res)
end

function sum_dicts(dl, dr; w = 1)
    d = Dict()
    for k in keys(dl)
        d[k] = dl[k]
    end
    for k in keys(dl)
        if k ∉ keys(d)
            d[k] = w * dr[k]
        else
            d[k] += w * dr[k]
        end
    end
    return d
end
