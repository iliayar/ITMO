#include <variant>
#include <iostream>
#include <functional>
#include <cassert>
#include <memory>
#include <type_traits>
#include <utility>

struct Unit { };

template <typename T>
struct Linear;

template <typename X>
using Value = Linear<X>;

template <typename A, typename B>
using Impl = std::function<auto (Linear<A>) -> Linear<B>>;

template <typename A, typename B>
using Times = std::pair<Linear<A>, Linear<B>>;

template <typename A, typename B>
using And = Linear<std::pair<Linear<A>, Linear<B>>>;

template <typename A, typename B>
using Or = std::variant<Linear<A>, Linear<B>>;

// template <typename A>
// using Bank = Linear<std::function<auto () -> Linear<A>>>;

template <typename A>
using Bank = std::function<auto () -> Linear<A>>;

template <typename T, typename... Gamma>
using Calc = std::function<auto (Gamma...) -> T>;


// template <typename A, typename B>
// auto CallImpl(Impl<A, B>&& _f, Linear<A>&& a) -> Linear<B> {
    // Impl<A, B> f = std::move(_f);
    // return f.value_(std::move(a));
// }

// template <typename CalcA, typename CalcB, typename A, typename B>
// auto IntTimes(CalcA a, CalcB b) -> Res {
    // return [=](auto... Gamma, auto... Delta) {
        // return Times{a(Gamma...), b(Delta...)};
    // };
// }

// !I
template <typename A>
auto MakeBank(A a) -> Bank<A> {
    return [a]() {
        return Linear<A>{a};
    };
}

// -oE
template <typename A, typename B>
auto Apply(std::function<auto (Linear<A>) -> Linear<B>> f, Linear<A> a) -> Linear<B> {
    return f(std::move(a));
}

// -oI ??
template <typename A, typename B>
auto Ident(std::function<auto (Linear<A>) -> Linear<B>> f)
    -> std::function<auto (Linear<A>) -> Linear<B>> {
    return f;
}

// (x)I
template <typename A, typename B>
auto MakePair(Linear<A> a, Linear<B> b) -> Times<A, B> {
    return {std::move(a), std::move(b)};
}

// (x)E
template <typename A, typename B, typename C>
auto UsePair(Times<A, B> times, 
        std::function<auto (Linear<A>, Linear<B>) -> Linear<C>> f) -> Linear<C> {
    return f(std::move(times.first), std::move(times.second));
}

// &E1
template <typename A, typename B>
auto AndLeft(And<A, B> a) -> Linear<A> {
    return std::move(a.value_.first);
}

// &E2
template <typename A, typename B>
auto AndRight(And<A, B> b) -> Linear<B> {
    return std::move(b.value_.second);
}

// &I
template <typename A, typename B>
auto MakeAnd(Linear<A> a, Linear<B> b) -> And<A, B> {
    return {{std::move(a), std::move(b)}};
}

// (+)I1
template <typename A, typename B>
auto OrLeft(Linear<A> a) -> Or<A, B> {
    return {std::move(a)};
}

// (+)I2
template <typename A, typename B>
auto OrRight(Linear<B> b) -> Or<A, B> {
    return {std::move(b)};
}

// (+)E
template <typename A, typename B, typename C>
auto MatchOr(Or<A, B> o, 
        std::function<auto (Linear<A>) -> Linear<C>> fA, 
        std::function<auto (Linear<B>) -> Linear<C>> fB) {
    if (std::holds_alternative<Linear<A>>(o)) {
        return fA(std::move(std::get<Linear<A>>(o)));
    } else {
        return fB(std::move(std::get<Linear<B>>(o)));
    }
}

// template <typename A>
// auto CallBank(Bank<A>&& _b) -> Linear<A> {
    // Bank<A> b = std::move(_b);
    // return b.value_();
// }

template <typename T>
struct Linear {
    Linear(Linear const&) = delete;
    Linear& operator=(Linear const&) = delete;

    Linear(Linear&& other) : value_(std::move(other.value_)), moved_(false) {
        assert(!other.moved_ && "Value already moved");
        other.moved_ = true; 
    }
    Linear& operator=(Linear&& other) {
        assert(!other.moved_ && "Value already moved");
        other.moved_ = true; 
        value_ = std::move(other.value_);
        moved_ = false;
        return *this;
    }

    Linear(T&& value) : value_(std::move(value)), moved_(false) {}

    template <typename A, typename B>
        friend auto AndLeft(And<A, B>) -> Linear<A>;
    template <typename A, typename B>
        friend auto AndRight(And<A, B>) -> Linear<B>;
    // template <typename A, typename B>
        // friend auto CallImpl(Impl<A, B>&& _f, Linear<A>&& a) -> Linear<B>;
    // template <typename A>
        // friend auto CallBank(Bank<A>&& _b) -> Linear<A>;

private:
    T value_;
    bool moved_;
};

struct AType {};
struct BType {};
struct CType {};


// template <typename A>
// struct Context {
    // A value;
    // EmptyContext next;
// };

template <typename A, typename... Gamma>
struct Context;

struct EmptyContext {};

template <typename... Gamma>
struct choose_context {
    using type = Context<Gamma...>;
};

template <>
struct choose_context<> {
    using type = EmptyContext;
};

template <typename A, typename... Gamma>
struct Context {
    A value;
    typename choose_context<Gamma...>::type next;
};

template <typename A, typename... Gamma>
auto MakeContext(A value, Gamma... vars) -> Context<A, Gamma...> {
    if constexpr (sizeof...(Gamma) > 0) {
        return Context<A, Gamma...>{std::move(value), MakeContext<Gamma...>(std::forward<Gamma>(vars)...)};
    } else {
        return Context<A>{std::move(value), EmptyContext{}};
    }
}

template <typename A, typename... Gamma>
auto PushContext(A value, Context<Gamma...> ctx) -> Context<A, Gamma...> {
    return Context<A, Gamma...>{std::move(value), std::move(ctx)};
}

template <typename A, typename... Gamma>
auto PopContext(Context<A, Gamma...> ctx) -> std::pair<A, Context<Gamma...>> {
    return std::make_pair(std::move(ctx.value), std::move(ctx.next));
}

template <typename Gamma...>
struct ContacContext {
    template <typename Delta...>
    static 
};

int main() {

    Context<AType, Linear<BType>, CType> ctx = MakeContext(AType{}, Linear<BType>{{}}, CType{});
    Context<int, AType, Linear<BType>, CType> ctx1 = PushContext(1, std::move(ctx));
    auto [a, ctx2] = PopContext(std::move(ctx1));
    // Context<AType, BType, CType> ctx;
    // Context<int, AType, BType, CType> ctx1 = AppendContext(5, ctx);


    // A & B
    // Linear<AType> A{{}};
    // Linear<BType> B{{}};
    // And<AType, BType> AndAB{{std::move(A), std::move(B)}};
    // And<AType, BType> AndAB = MakeAnd<AType, BType>(std::move(A), std::move(B));

    // Linear<AType> A1 = AndLeft(std::move(AndAB));


    // !A
    // Bank<Unit> bank{[]() {
        // return Linear<Unit>{{}};
    // }};

    // Linear<Unit> A = bank();
    // Linear<Unit> B = bank();

    // Linear<Unit> A1 = std::move(A);
    // Linear<Unit> B1 = std::move(B);


    // A -o B
    // Impl<AType, BType> AtoB{[](Linear<AType>&& a) {
        // return Linear<BType>{{}};
    // }};

    // Linear<AType> A{{}};
    // Linear<BType> B = AtoB(std::move(A));
    // Linear<AType> A1 = std::move(A);

    
    // A (+) B
    // Linear<AType> A{{}};
    // Or<AType, BType> _or = OrLeft<AType, BType>(std::move(A));
    // Linear<CType> C = MatchOr<AType, BType, CType>(std::move(_or), 
            // [](Linear<AType>) { std::cout << "A" << std::endl; return Linear<CType>{{}}; }, 
            // [](Linear<BType>) { std::cout << "B" << std::endl; return Linear<CType>{{}}; });

    // A (x) B
    // Linear<AType> A{{}};
    // Linear<BType> B{{}};
    // Times<AType, BType> t = MakePair(std::move(A), std::move(B));

    // UsePair<AType, BType, CType>(std::move(t), [](Linear<AType>, Linear<BType>) {
        // std::cout << "used" << std::endl;
        // return Linear<CType>{{}};
            // });

    // Test Linear
    // Linear<AType> A1{{}};
    // Linear<AType> A2{{}};

    // Linear<AType> A11 = std::move(A1);
    // A1 = std::move(A2);
    // Linear<AType> A12 = std::move(A1);
    // A2 = std::move(A12);
    // Linear<AType> A21 = std::move(A2);


    // Calc<int> one = []() { return 1; };
    // Calc<int> two = []() { return 2; };
    // Calc<Times<int, int>> pair = IntTimes<Calc<int>, Calc<int>, Calc<Times<int, int>>>(one, two);

    std::cout << "Test" << std::endl; 
}
