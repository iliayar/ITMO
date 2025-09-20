
abstract type Regularization end

abstract type LeastSquareRegularization <: Regularization end

struct LeastSquareNoRegularization <: LeastSquareRegularization end
struct LeastSquareRidgeRegularization <: LeastSquareRegularization
    τ::Float64
end

function calc_regularization(r::LeastSquareRidgeRegularization, v, λ, u)
    λ / (λ^2 + r.τ) * (u * v')
end

function calc_regularization(_::LeastSquareNoRegularization, v, λ, u)
    1 / λ * (u * v')
end

function mk_least_square_regularization(name, params...)::LeastSquareRegularization
    if name == :no
        LeastSquareNoRegularization(params...)
    elseif name == :ridge
        LeastSquareRidgeRegularization(params...)
    end
end

abstract type SGDRegularization <: Regularization end

struct SGDNoRegularization <: SGDRegularization end
struct SGDLassoRegularization <: SGDRegularization
    τ::Float64
end

function calc_regularization(r::SGDNoRegularization, Θ::Vector{Float64})::Float64
    0
end
function calc_regularization_grad(r::SGDNoRegularization, Θ::Vector{Float64})::Vector{Float64}
    zeros(size(Θ))
end

function calc_regularization(r::SGDLassoRegularization, Θ::Vector{Float64})::Float64
    r.τ * mapreduce(abs, +, Θ)
end
function calc_regularization_grad(r::SGDLassoRegularization, Θ::Vector{Float64})::Vector{Float64}
    r.τ * Θ
end
 


function mk_sgd_regularization(name, params...)::SGDRegularization
    if name == :no
        SGDNoRegularization(params...)
    elseif name == :lasso
        SGDLassoRegularization(params...)
    end
end
