#import "common.typ": *


#show: doc => practice(
  subj: [Функциональное програмирование],
  title: [Практика 4],
  date: [1 октября],
  number: 4,
  doc
)

Неэффективный факториал, работает за $cal(O)(n)$ по памяти
```haskell
fact n
    | n == 0 = 1
    | otherwise = fact (n - 1)
```

Эффективный использует хвостовую рекурсию
```haskell
fact n = go n
  where
    go n r
      | n == 0 = r
      | otherwise = go (n - 1) (r * n)
```

Эффективный Фибоначи:
#raw(read("4_1.hs"), lang: "haskell")

Есть операторы `$`, `&`, `.`:
#raw(read("4_2.hs"), lang: "haskell")
