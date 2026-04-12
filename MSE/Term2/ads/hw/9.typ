#import "common.typ": *

#show: doc => hw(doc)

#line(length: 100%)
#task(numbering: (..) => numbering("1.a", 1, 1))[]
#solution[
  Понятно что если $n = i + p dot j$, $n mod p = i$, то $omega^(n mod p) = omega^i = omega^i dot (omega^p)^j  = omega^n$
  $ f'_r = f_(g^r mod p) = sum_(i = 0)^(p - 1) x_i omega_p^(g^r i) = x_0 + sum_(i = 1)^(p - 1) x_i omega_p^(g^r i) $
  Заметим что $g^(-s)$ пробегает по всем значениям ${1, dots, p - 1}$, т.к. $g$ --- генератор, при $s in {0, dots, p - 2}$. Тогда можем заменить индекс суммирования $i$ на $g^(-s)$:
  $ f'_r = x_0 + sum_(s = 0)^(p - 2) x_(g^(-s)) omega_p^(g^r g^(-s)) = x_0 + sum_(s = 0)^(p -2) x'_s omega_p^(g^(r - s mod (p - 1))) = x_0 + sum_(s = 0)^(p -2) x'_s Delta_(r - s mod (p - 1)) $
]

#task(numbering: (..) => numbering("1.a", 1, 2))[]
#solution[
  Возьмем многочлены $A$ с коэффициентами $x'_0, x'_1, dots, x'_(p - 2)$ и $B$ с коэффициентами $Delta_0, Delta_1, dots, Delta_(p - 2), Delta_0, dots, Delta_(p - 2)$. Перемножим их, получим многочлен $C$ с коэффициентами:
  $ C_i = sum_(s + t = k) x'_s dot Delta_(t mod p - 1) $
  Заметим что
  $ s <= r: quad & sum_(s = 0)^r x'_s Delta_(r - s) = sum_(s + i = r) x'_s Delta_i = C_r \
    s > r: quad & sum_(s = r + 1)^(p - 2) x'_s Delta_(r - s + p - 1) = sum_(s + i = r + p - 1) x'_s Delta_(i) = C_(r + p - 1)
  $
  $ sum_(s = 0)^(p - 2) x'_s Delta_(r - s mod (p - 1)) = sum_(s=0)^r x'_s Delta_(r - s) + sum_(s = r + 1)^(p - 2) x'_s Delta_(r - s + p - 1) = C_r + C_(r + p - 1)  $
  Тогда $f'_r = x_0 + C_r + C_(r + p - 1)$. Коэффициенты многочлена $C$ можем посчитать через FFT за $cal(O)(p log p)$. $f'_0$ считаем за $cal(O)(p)$, последующие получаются циклическим сдвигом, т.е. за $cal(O)(1)$. В конце заметим что $f_k$ это просто перестановка $f'_r$, можем найти за линию. Итого самое долгое это FFT за $cal(O)(p log p)$.
]

#line(length: 100%)
#task(numbering: (..) => numbering("1.a", 2, 1))[]
#solution[
  Пусть дана `DFT`
  $ A_k = sum_(i = 0)^(n - 1) a_i omega_n^(k i) $
  Разложим на две суммы, внутренняя с шагом $n_1$
  $ A_k = sum_(i = 0)^(n_1 - 1) sum_(j = 0)^(n_2 - 1) a_(i + n_1 j) omega_n^(k (i + n_1 j)) = sum_(i = 0)^(n_1 - 1) omega_n^(k i) sum_(j = 0)^(n_2 - 1) a_(i + n_1 j) omega_n^(n_1 j k) $
  Заметим что $omega_n^(n_1) = root(n_1 n_2, 1)^(n_1) = root(n_2, 1) = omega_(n_2)$ и аналогично $omega_n^(n_2) = omega_(n_1)$. Тогда
  $ A_k = sum_(i = 0)^(n_1 - 1) omega_n^(k i) sum_(j = 0)^(n_2 - 1) a_(i + n_1 j) omega_(n_2)^(j k) $
  Заметим что если $k = r + s n_2$, то $omega_(n_2)^(j r + j s n_2) = omega_(n_2)^(j r)$, тогда
  $ A_(r + s n_2) = sum_(i = 0)^(n_1 - 1) omega_n^(i r + i s n_2) sum_(j = 0)^(n_2 - 1) a_(i  + n_1 j) omega_(n_2)^(j r + j s n_2) = sum_(i = 0)^(n_1 - 1) omega_n^(i r) omega_(n_1)^(i s) sum_(j = 0)^(n_2 - 1) a_(i  + n_1 j) omega_(n_2)^(j r) $
  Пусть $B_(i, r) := sum_(j = 0)^(n_2 - 1) a_(i + n_1 j) omega_(n_2)^(j r)$. Заметим что для фиксированного $i$ это DFT от последовательности $a_(i), a_(i + n_1), dots, a_(i + (n_2 - 1) n_1)$. Т.к. $i in [0; n_1 - 1]$, то посчитав $n_1$ раз DFT размера $n_2$, получим все $B_(i, r)$. Тогда
  $ A_(r + s n_2) = sum_(i = 0)^(n_1 - 1) omega_n^(i r) omega_(n_1)^(i s) B_(i, r) $
  Эту сумму посчитаем за $cal(O)(n dot n_1) = cal(O)(n_1^2 n_2)$.
]

#task(numbering: (..) => numbering("1.a", 2, 2))[]
#solution[
  Перепишем получившуюся в прошлой задаче итоговую сумму:
  $ A_(r + s n_2) = sum_(i = 0)^(n_1 - 1) (B_(i, r) omega_n^(i r)) omega_(n_1)^(i s) $
  Пусть $C_(i, r) := B_(i, r) omega_n^(i r)$. Можем посчитать все такие $C$ за $cal(O)(n_1 n_2)$, т.к. $i in [0; n_1 - 1]$, а $r in [0; n_2 - 1]$. Тогда для фиксированного $r$: $A'_s := A_(r + s n_2) = sum_(i= 0)^(n_1 - 1) C_(i, r) omega_(n_1)^(i s)$, т.е. $A'_s$ это DFT от последовательности $C_(0, r), C_(1, r), dots, C_(n_1 - 1, r)$. Т.к. $r in [0; n_2 - 1]$, то посчитаем все $A'_s$ за $n_2$ DFT от последовательностей размера $n_1$. А это значит что получим все $A_(r + s n_2) = A_k$.
]
