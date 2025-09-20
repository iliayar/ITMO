
using LinearAlgebra

function compute(m::LeastSquares, objs::Vector{Object})::Vector{Float64}
    X, y = split_objects(objs)
    U, S, V = svd(X)
    f(v, l, u) = calc_regularization(m.r, v, l, u)
    FPlus = mapreduce(f, +, eachcol(U), S, eachcol(V))
    return FPlus * y
end

function compute(m::SGD, objs::Vector{Object}; log=[])::Vector{Float64}
    w = sgd_init(m.init, size(objs[1].X)[1])
    μ = m.μ
    L = 0
    pgrad = zeros(size(objs[1].X))
    pw = zeros(size(objs[1].X))

    for step in 1:m.steps
        X, y = sample(objs, m.b) |> split_objects
        yp = map(eachrow(X)) do x w ⋅ x end
        grad = calc_loss_grad(m.loss_reg.l, y, yp, X) + calc_regularization_grad(m.loss_reg.r, w)
        if isnan(norm(grad))
            println("grad norm is NaN")
            break
        end
        if norm(grad) < eps()
            println("Grad to small")
            break
        end
        w = w - μ * grad
        L = (1 - m.α) * L + m.α * (calc_loss(m.loss_reg.l, y, yp) + calc_regularization(m.loss_reg.r, w))
        push!(log, L)
        μ = change_step(m.μ_change, step, μ)
        pgrad = grad
        pw = w
    end

    return w
end
    
