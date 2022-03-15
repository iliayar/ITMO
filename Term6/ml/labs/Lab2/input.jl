include("object.jl")

function read_data(filename::String)::Tuple{Vector{Object}, Vector{Object}}
    train::Vector{Object} = []
    test::Vector{Object} = []

    open("data/$filename") do f
        M = parse(Int64, readline(f))
        N = parse(Int64, readline(f))
        # println("N = $N, M = $M")

        function read_part!(n, d)
            for _ in 1:n
                X = (s -> parse(Float64, s)).(split(readline(f)))
                y = pop!(X)
                push!(d, Object(X, y))
            end
        end

        read_part!(N, train)

        K = parse(Int64, readline(f))
        read_part!(K, test)
    end

    return (train, test)
end

