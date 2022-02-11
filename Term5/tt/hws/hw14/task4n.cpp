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
using Impl = std::function<auto (A) -> B>;

template <typename A, typename B>
using Times = std::pair<A, B>;

template <typename A, typename B>
using And = std::pair<std::function<auto () -> A>, std::function<auto () -> B>>;

template <typename A, typename B>
using Or = std::variant<A, B>;

template <typename A>
using Bank = std::function<auto () -> A>;

// Gamma |- T
template <typename T, typename... Gamma>
using Calc = std::function<auto (Gamma...) -> T>;

// Id
template <typename A>
auto MakeId() -> Calc<A, A> {
    return Calc<A, A>{[](A a) {
        return a;
    }};
}

// <Id>
template <typename A>
auto MakeLinId() -> Calc<Linear<A>, Linear<A>> {
    return Calc<Linear<A>, Linear<A>>{[](Linear<A> a) {
        return std::move(a);
    }};
}

// !I
template <typename A, typename... Gamma>
auto MakeBank(Calc<A, Gamma...> calc) -> Calc<Bank<A>, Gamma...> {
    return Calc<Bank<A>, Gamma...>{[calc](Gamma... ctx) {
        return Bank<A>{[calc, ctx...]() {
            return calc(ctx...);
        }};
    }};
}

// !E
template <typename A, typename B>
auto ApplyMany(Calc<Bank<A>> bank, Calc<B, A> fun) -> Calc<B> {
    return Calc<B>{[bank, fun]() {
        A a = bank()();
        return fun(a);
    }};
}

// -oE
template <typename A, typename B>
auto Apply(Calc<Impl<A, B>> impl, Calc<A> c) -> Calc<B> {
    return Calc<B>{[impl, c]() {
        return impl()(std::move(c()));
    }};
}

// -oI
template <typename A, typename B>
auto Deduce(Calc<B, A> c) -> Calc<Impl<A, B>> {
    return Calc<Impl<A, B>>{[c]() {
        return Impl<A, B>{[c](A a) {
            return c(std::move(a));
        }};
    }};
}

// (x)I
template <typename A, typename B>
auto MakePair(Calc<A> ca, Calc<B> cb) -> Calc<Times<A, B>> {
    return Calc<Times<A, B>>{[ca, cb]() {
        return std::make_pair(std::move(ca()), std::move(cb()));
    }};
}

// (x)E
template <typename A, typename B, typename C>
auto UsePair(Calc<Times<A, B>> ct, Calc<C, A, B> cc) -> Calc<C> {
    return Calc<C>{[ct, cc]() {
        Times<A, B> t = std::move(ct());
        A a = std::move(t.first);
        B b = std::move(t.second);
        return cc(std::move(a), std::move(b));
    }};
}

template <typename A, typename B>
auto AndLeft(And<A, B> a) -> A {
    return std::move(a.value_.first());
}

template <typename A, typename B>
auto AndRight(And<A, B> b) -> B {
    return std::move(b.value_.second());
}

// &E1
template <typename A, typename B>
auto GetLeft(Calc<And<A, B>> ca) -> Calc<A> {
    return Calc<A>{[ca]() {
        return AndLeft(ca());
    }};
}

// &E2
template <typename A, typename B>
auto GetRight(Calc<And<A, B>> ca) -> Calc<B> {
    return Calc<B>{[ca]() {
        return AndRight(ca());
    }};
}

// &I
template <typename A, typename B>
auto MakeAnd(Calc<A> ca, Calc<B> cb) -> Calc<And<A, B>> {
    return Calc<And<A, B>>{[ca, cb]() {
        return And<A, B>{[ca]() { return ca(); }, [cb]() { return cb(); }};
    }};
}

// (+)I1
template <typename A, typename B>
auto OrLeft(Calc<A> ca) -> Calc<Or<A, B>> {
    return Calc<Or<A, B>>{[ca]() {
        return Or<A, B>{std::move(ca())};
    }};
}

// (+)I2
template <typename A, typename B>
auto OrRight(Calc<B> cb) -> Calc<Or<A, B>> {
    return Calc<Or<A, B>>{[cb]() {
        return Or<A, B>{std::move(cb())};
    }};
}

// (+)E
template <typename A, typename B, typename C>
auto MatchOr(Calc<Or<A, B>> cor, Calc<C, A> ca, Calc<C, B> cb) -> Calc<C> {
    return Calc<C>{[cor, ca, cb]() {
        Or<A, B> o = cor();
        if (std::holds_alternative<Linear<A>>(o)) {
            return ca(std::move(std::get<Linear<A>>(o)));
        } else {
            return cb(std::move(std::get<Linear<B>>(o)));
        }
    }};
}

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
        friend auto AndLeft(And<A, B> a) -> A;

    template <typename A, typename B>
        friend auto AndRight(And<A, B> b) -> B;

private:
    T value_;
    bool moved_;
};

struct AType {};
struct BType {};
struct CType {};

int main() {
    Calc<AType, BType, CType> calc3{[](BType b, CType c) {
        return AType{};
    }};
    Calc<AType, BType> calc2{[](BType b) {
        return AType{};
    }};
    Calc<AType> calc1{[]() {
        return AType{};
    }};

    Calc<Linear<AType>, Linear<BType>, Linear<CType>> lcalc3{[](Linear<BType> b, Linear<CType> c) {
        return Linear<AType>{{}};
    }};
    Calc<Linear<AType>, Linear<BType>> lcalc2{[](Linear<BType> b) {
        return Linear<AType>{{}};
    }};
    Calc<Linear<AType>> lcalc1{[]() {
        return Linear<AType>{{}};
    }};

    // Calc<Bank<Linear<AType>>, Linear<BType>> bank = MakeBank(lcalc2);
    Calc<Bank<AType>, BType> bank = MakeBank(calc2);
    Linear<AType> a = bank(BType{})();
    Linear<AType> b = bank(BType{})();


    // Calc<And<Linear<AType>, Linear<BType>>> cand = Calc<And<Linear<AType>, Linear<BType>>>([]() { 
            // return And<Linear<AType>, Linear<BType>>{{Linear<AType>{{}}, Linear<BType>{{}}}};
            // });
    // Calc<Linear<AType>> cand_a = GetLeft(cand);



    Calc<Impl<Linear<AType>, Linear<BType>>> cimpl = Calc<Impl<Linear<AType>, Linear<BType>>>([]() {
        return Impl<Linear<AType>, Linear<BType>>{[](Linear<AType> a) {
            return Linear<BType>{{}};
        }};
    });

    Calc<Linear<BType>> cb = Apply(cimpl, lcalc1);
    Linear<BType> _b = cb();
    // Calc<Bank<AType>> cbank = Calc<Bank<AType>>{[](){ return Bank<AType>{[]() { return AType{}; }}; }};

    Calc<Impl<Linear<BType>, Linear<AType>>> _cimpl = Deduce(lcalc2);
}
