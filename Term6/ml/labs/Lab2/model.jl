
abstract type SGDInit end

struct SGDInitCool <: SGDInit end

function sgd_init(i::SGDInitCool, n::Int64)
    f(_) = - 1 / 2n + rand() * 1 / n
    map(f, zeros(n))
end

function mk_sgd_init(name)::SGDInit
    if name == :cool
        return SGDInitCool()
    end
end

abstract type Model end

struct LeastSquares <: Model
    r::LeastSquareRegularization
end

struct SGDLossWithRegularization
    l::Loss
    r::SGDRegularization
end

abstract type SGDStepChange end

struct SGDStepChangeFactor <: SGDStepChange
    α::Float64
end

struct SGDStepChangeIter <: SGDStepChange
    α::Float64
end

struct SGDNoStepChange <: SGDStepChange end

function mk_sgd_step_change(name, params...)::SGDStepChange
    if name == :factor
        return SGDStepChangeFactor(params...)
    elseif name == :iter
        return SGDStepChangeIter(params...)
    elseif name == :no
        return SGDNoStepChange(params...)
   end
end

function change_step(c::SGDStepChangeFactor, i::Int64, μ::Float64)::Float64
    μ * c.α
end

function change_step(c::SGDStepChangeIter, i::Int64, μ::Float64)::Float64
    c.α / (i + 1)
end

function change_step(c::SGDNoStepChange, i::Int64, μ::Float64)::Float64
    μ
end

struct SGD <: Model
    loss_reg::SGDLossWithRegularization
    init::SGDInit
    steps::Int64
    b::Int64
    μ::Float64
    μ_change::SGDStepChange
    α::Float64
end

function mk_sgd_loss_with_regularization(l::Loss, r::SGDRegularization)::SGDLossWithRegularization
    SGDLossWithRegularization(l, r)
end

function mk_model(name, params...)::Model
    if name == :SGD
        return SGD(params...)
    elseif name == :LeastSquares
        return LeastSquares(params...)
    end
end
