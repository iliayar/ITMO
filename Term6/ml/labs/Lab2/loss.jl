
abstract type Loss end

struct SMAPE <: Loss end

function calc_loss(l::SMAPE, y::Vector{Float64}, yp::Vector{Float64})
    n = size(y)[1]
    mapreduce(+, y, yp) do y, yp
	abs(y - yp) / (abs(y) + abs(yp)) / n
    end
end

function calc_loss_grad(l::SMAPE, y::Vector{Float64}, yp::Vector{Float64}, X::Matrix{Float64})
    n = size(y)[1]
    mapreduce(+, y, yp, eachrow(X)) do y, yp, x
        (sign(yp - y) * (abs(y) + abs(yp)) - abs(yp - y) * sign(yp)) / (abs(y) + abs(yp))^2 * x / n
    end
end

struct MSE <: Loss end

function calc_loss(l::MSE, y::Vector{Float64}, yp::Vector{Float64})
    n = size(y)[1]
    mapreduce(+, y, yp) do y, yp
        (yp - y)^2 / 2n
    end
end

function calc_loss_grad(l::MSE, y::Vector{Float64}, yp::Vector{Float64}, X::Matrix{Float64})
    n = size(y)[1]
    mapreduce(+, y, yp, eachrow(X)) do y, yp, x
        (yp - y) * x / n
    end
end

struct NRMSE  <: Loss end

function calc_loss(l::NRMSE, y::Vector{Float64}, yp::Vector{Float64})
    sqrt(calc_loss(MSE(), y, yp)) / (maximum(y) - minimum(y))
end

function mk_loss(name)::Loss
    if name == :SMAPE
        return SMAPE()
    elseif name == :MSE
        return MSE()
    elseif name == :NRMSE
        return NRMSE()
    end
end

function calc_loss(l::Loss, w::Vector{Float64}, objs::Vector{Object})::Float64
    X, y = split_objects(objs)
    calc_loss(l, y, X * w)
end
