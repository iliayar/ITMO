fib nEnd = go 0 0 1
  where
    go i n n'
      | i == nEnd = n'
      | otherwise = go (i + 1) n' (n + n')
