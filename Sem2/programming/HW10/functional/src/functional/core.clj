;; (ns functional.core)

(defn constant [value]
  (fn [args] value))

(defn variable [name]
  (fn [args] (get args name)))

(defn operation [f]
  (fn [& operands]
    (fn [args] (apply f (mapv (fn [g] (g args)) operands)))))

(defn my-divide [& xs]
  (if (= (count xs) 1)
    (/ 1.0 (double (first xs)))
    (/ (double (first xs)) (double (apply * (rest xs))))))

(def add (operation +))
(def subtract (operation -))
(def multiply (operation *))
(def divide (operation my-divide))
;; (def divide (operation (fn [& xs] (apply / (map double xs)))))
(def avg (operation (fn [& xs] (/ (apply + xs) (count xs)))))
(def med (operation (fn [& xs] (nth (sort xs) (quot (count xs) 2)))))
(def negate subtract)

(def operations
  {'+ add
   '- subtract
   '* multiply
   '/ divide
   'negate negate
   'avg avg
   'med med })

(defn parseFunction' [expression]
  (cond
    (number? expression) (constant expression)
    (symbol? expression) (variable (str expression))
    (seq? expression) (apply (get operations (first expression)) (map parseFunction' (rest expression)))))

(defn parseFunction [expression] (parseFunction' (read-string expression)))
