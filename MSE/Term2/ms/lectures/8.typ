#import "../../../../other/typst/lecture_mse.typ": *

#show: doc => lecture(
  subj: [Математическая статистика],
  title: [Лекция 8],
  date: [23 апреля],
  number: 7,
  program: "ITMO MSE y2025",
  doc
)

= Общая схема построения критерия
1. Выбор статистики критерия $(t: (X_1, dots, X_n) -> R)$
2. ...
3. ...
4. Выбор критической области
  $ PP(t in S_alpha (H_0)) = alpha $
5. $ phi(X_1, dots, X_n) = cases(H_0"," t in.not S_alpha, H_1"," t in S_alpha) $
Итого $alpha_I = alpha$. $alpha_(II) = ?$.
