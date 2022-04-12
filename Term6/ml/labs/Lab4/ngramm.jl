
function build_ngramm(msg::Message{Word}; N::Int64=2, N_SUBJ::Int64=1)::Message{NGrammWord}
    function build_ngramm_impl(msg::Vector{Word}, N)::Vector{NGrammWord}
        res::Vector{NGrammWord} = []
        for i in 1:(size(msg)[1]-N+1)
            # push!(res, join(msg[i:(i+N-1)], "#"))
            push!(res, msg[i:(i+N-1)])
        end
        return res
    end
    nsubj = build_ngramm_impl(msg.subject, N_SUBJ)
    nbody = build_ngramm_impl(msg.body, N)
    return Message(nsubj, nbody)
end

function build_ngramm_dataset(ds::Dataset{Word}; N::Int64=2, N_SUBJ::Int64=1)::Dataset{NGrammWord}
    function convert_object(obj::Event{Word})::Event{NGrammWord}
        return Event(build_ngramm(obj.message; N=N, N_SUBJ=N_SUBJ), obj.class, obj.path)
    end
    return Dataset(collect(map(convert_object, ds.events)))
end

function build_ngramm_datasets(dss::Vector{Dataset{Word}}; N::Int64=2, N_SUBJ::Int64=1)::Vector{Dataset{NGrammWord}}
    function convert_dataset(ds::Dataset{Word})::Dataset{NGrammWord}
        return build_ngramm_dataset(ds; N=N, N_SUBJ=N_SUBJ)
    end
    return collect(map(convert_dataset, dss))
end
