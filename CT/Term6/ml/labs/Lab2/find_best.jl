include("./main.jl") 

train, test = read_data("6.txt")
my_normalize!(train)
my_normalize!(test)

res = []
loss = mk_loss(:SMAPE)
for _ in 1:20
    steps = rand(500:100:1000)
    b = rand(50:50:200)
    μ = rand(0:0.1:1)

    step_ch = [:iter, :factor][rand(1:2)]
    if step_ch == :iter
        μ_param = rand(1:10)
    elseif step_ch == :factor
        μ_param = rand(0:0.1:1)
    end
        
    τ = exp(rand(-10:10))

    params = (steps, b, step_ch, μ, μ_param, τ)
    println("Params: ", params)
    m = mk_model(
        :SGD,
        mk_sgd_loss_with_regularization(
            mk_loss(:MSE),
            mk_sgd_regularization(:lasso, τ),
        ),
        mk_sgd_init(:cool),
        steps,
        b,
        μ,
        mk_sgd_step_change(:iter, μ_param),
        0.2,
    )
    w = compute(m, train)
    L = calc_loss(loss, w, test)
    append!(res, [(L, params)])
    println("Loss: ", L)
    println("======================")
end
println(find_best(res))
