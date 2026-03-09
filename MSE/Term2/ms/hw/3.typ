#import "common.typ": *

#show: doc => hw(doc)

#line(length: 100%)
#task(numbering: (..) => numbering("1", 1))[]
#solution[
  Решим уравнение для $theta$
  $ 1/n sum_(i = 1)^n X_i^(2k) = EE_theta X^(2k) $
  $ EE_theta X^(2k) = integral_(-theta)^theta x^(2k) f(x) d x = integral_(-theta)^theta x^(2k) 1 / (theta - (-theta)) d x = 1 / (2theta) dot integral_(-theta)^theta x^(2k) d x = 1 / (2theta) dot lr(x^(2k + 1) / (2k + 1)|)_(-theta)^theta = \
    = 1 / (2theta) dot 2 dot theta^(2k + 1) / (2k + 1) = theta^(2k) / (2 k + 1)
  $
  Тогда
  $ (hat(theta)_n^((k)))^(2k) / (2k + 1) = 1 / n sum_(i = 1)^n X_i^(2k) ==> hat(theta)_n^((k)) = root(2k, (2k + 1) / n sum_(i = 1)^n X_i^(2k)) $
]

#line(length: 100%)
#task(numbering: (..) => numbering("1", 2))[]
#solution[
  Посчитаем $EE_theta (hat(theta)_n^((k)) - theta)^2$. Пусть $f(x) = root(2k, (2k + 1) y)$, тогда $f'(x) = (2k + 1)^(1/ (2k))/(2k) x^(1 / (2k) - 1)$. Для равнмерного распределния знаем $EE X_i^(2k) = theta^(2k) / (2k + 1)$. По ЗБЧ:
  $ overline(X^(2k)) ->^PP EE X_i^(2k) = theta^(2k) / (2k + 1)  $
  Разложим в ряд Тейлора $f$ в точке $a := EE X_i^(2k)$:
  $ f(overline(X^(2k))) - f(a) approx f'(a) (overline(X_i^(2k)) - a) $
  $ hat(theta)_n^((k)) - theta approx f'(a) (overline(X_i^(2k)) - a) $
  $ EE (hat(theta)_n^((k)) - theta)^2 approx (f'(theta^(2k) / (2k + 1)))^2 dot undershell(EE (overline(X_i^(2k)) - EE X_i^(2k))^2, DD overline(X_i^(2k))) $
  Для равномерного распределения также значем что
  $ DD overline(X_i^(2k)) = 1 / n^2 dot n dot DD X_i^(2k) = 1/n (EE^2 X^(2k) - EE X^(4k)) = 1 / n (theta^(4k) / (2k+1)^2 - theta^(4k) / (4k + 1) ) = theta^(4k) / n dot (4 k^2) / ((2k + 1)^2 (4k + 1)) $
  Тогда
  $ EE (hat(theta)_n^((k)) - theta)^2 approx (2k+1)^(1 / k) / ((2k)^2) dot (theta^(2k) / (2k+1))^(1 / k - 2) dot theta^(4k) / n dot (4k^2) / ((2k + 1)^2 (4k + 1)) = \
    = 1 / (4k^2) dot (theta^(2k))^(1 / k - 2) dot theta^(4k) / n dot (4k^2) / (4k + 1) = theta^2 / (n(4k + 1))
  $
]

#line(length: 100%)
#task(numbering: (..) => numbering("1", 2))[]
#solution[
  Посчитаем санала $EE g_k (X)$. Известно что для биноминального распределения $PP(X = k) = binom(m, k) p^k (1 - p)^(m - k)$.
  $ EE g_k (X) = sum_(i = 0)^m g_k (i) PP(X = i) = sum_(i = 0)^m i dot (i - 1) dot dots dot (i - k + 1) binom(m, i) p^i (1 - p)^(m - i) $
  Заметим что салагаемые от $0$ до $k - 1$ всегда будут $0$, т.к. хотя один из множителей будет $0$. А также
  $ i dot (i - 1) dot dots dot (i - k + 1) dot m! / (i! (m - i)!) = i^(underline(k)) dot (m^(underline(k)) dot (m - k)!) / (i^(underline(k)) dot (i - k)! (m - i)!) = \
    = m dot (m - 1) dot dots dot (m - k + 1) binom(m - k, i - k)
  $
  Тогда
  $ EE g_k (X) = sum_(i = 0)^m m dot (m - 1) dot dots dot (m - k + 1) binom(m - k, i - k) p^k (1 - p)^(m - i) = m^underline(k) p^k sum_(i = k)^m binom(m - k, i - k) p^(i - k) (1 - p)^(m - i) = \
    = m^underline(k) p^k sum_(j = 0)^(m - k) binom(m - k, j) p^j (1 - p)^((m - k) - j) = m^underline(k) p^k (p + (1 - p))^(m - k) = m dot (m - 1) dot dots (m - k + 1) dot p^k
  $
  Теперь можно найти оценку параметра $p$ из уравнения
  $ 1/n sum_(i = 1)^n g_k (X) = EE g_k (X) = m^underline(k) (hat(p)^((k))_n)^k $
  $ hat(p)^((k))_n = root(k, (sum_(i = 1)^n X_i dot (X_i - 1) dot dots dot (X_i - k + 1)) / (n dot m dot (m - 1) dot dots dot (m - k + 1))) $
]
