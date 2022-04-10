
struct Message
    subject::Vector{Int64}
    body::Vector{Int64}
end

function read_message(path::String)::Message
    open(path) do f
        subj = split(readline(f))
        @assert subj[1] == "Subject:"
        readline(f)
        body = split(readline(f))

        s_to_i = c -> collect(map(s -> parse(Int64, s), c))

        return Message(s_to_i(subj[2:end]), s_to_i(body))
    end
end

struct Object
    message::Message
    class::Symbol
    path::String
end

struct Dataset
    objects::Vector{Object}
end

function read_dataset(path::String)::Dataset
    res = []
    for f in readdir(path)
        filename = "$(path)/$(f)"
        if contains(f, "legit")
            push!(res, Object(read_message(filename), :legal, filename))
        elseif contains(f, "spmsg")
            push!(res, Object(read_message(filename), :spam, filename))
        else
            error("Unexpected filename")
        end
    end
    return Dataset(res)
end

function read_data(path::String)::Vector{Dataset}
    res = []
    for dir in readdir(path)
        dirname = "$(path)/$(dir)"
        push!(res, read_dataset(dirname))
    end
    return res
end
