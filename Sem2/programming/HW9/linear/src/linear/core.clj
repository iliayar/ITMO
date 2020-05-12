;; (ns linear.core)


(defn shape [a] (cond
                  (number? a) []
                  (every? number? a) [(count a)]
                  (some number? a) nil
                  :else (let [shape-a (mapv shape a)]
                          (if (and (not-any? nil? shape-a) (apply = shape-a))
                            (conj (first shape-a) (count a))
                            nil))))
(defn dim [a] (let [shape-a (shape a)] (if (nil? (shape a)) nil (count (shape a)))))

(defn same-shape? [& xs] (apply = (mapv shape xs)))
(defn tensor? [a] (not (nil? (shape a))))
(defn vec? [v] (= (dim v) 1))
(defn matrix? [m] (= (dim m) 2))
(defn vec3? [v] (= (shape v) [3]))

(defn elementwise' [check op]
  (letfn [
          (entry  [& xs]
            {:pre [(apply same-shape? xs) (every? check xs)]
             :post [(same-shape? (first xs) %) (check %)]}
            (apply impl xs))
          (impl [& xs]
            (cond
              (= (dim (first xs)) 0) (apply op xs)
              :else (apply mapv impl xs)))
          ]
    entry))
(def elementwise-vector' (partial elementwise' vec?))
(def elementwise-matrix' (partial elementwise' matrix?))
(def elementwise-tensor' (partial elementwise' tensor?))

(def v+ (elementwise-vector' +))
(def v- (elementwise-vector' -))
(def v* (elementwise-vector' *))

(defn scalar [& vs]
  {:pre [(apply same-shape? vs) (every? vec? vs)]
   :post [(number? %)]}
  (reduce + (apply v* vs)))

(defn vect-component [a b i j] (- (* (nth a i) (nth b j))
                             (* (nth a j) (nth b i))))
(defn vect' [a b] (vector
                       (vect-component a b 1 2)
                       (vect-component a b 2 0)
                       (vect-component a b 0 1)))
(defn vect [& vs]
  {:pre [(every? vec3? vs)]
   :post [(vec3? %)]}
  (reduce vect' vs))

(defn elementwise-scalar' [check f] (fn [v & ss]
  {:pre [(every? number? ss) (check v)]
   :post [(same-shape? v %) (check %)]}
  (let [s (apply * ss)] (mapv (fn [a] (f a s)) v))))
(def v*s (elementwise-scalar' vec? *))

(def m+ (elementwise-matrix' +))
(def m- (elementwise-matrix' -))
(def m* (elementwise-matrix' *))

(def m*s (elementwise-scalar' matrix? v*s))
(defn m*v [m & vs]
  {:pre [(apply same-shape? vs)
         (every? vec? vs)
         (= (first (shape m)) (first (shape (first vs))))
         (matrix? m)]
   :post [(= (first (shape %)) (second (shape m)))
          (vec? %)]}
  (mapv (apply partial scalar vs) m))

(defn transpose [m]
  {:pre [(matrix? m)]
   :post [(matrix? %)]}
  (apply mapv vector m))

(defn m*m' [a b]
  {:pre [(= (first (shape a)) (second (shape b)))
         (matrix? a) (matrix? b)]
   :post [(= (second (shape a)) (second (shape %)))
          (= (first (shape b)) (first (shape %)))
          (matrix? %)]}
  (mapv (fn [v] (m*v (transpose b) v)) a))
(defn m*m [& ms] (reduce m*m' ms))

(def t+ (elementwise-tensor' +))
(def t- (elementwise-tensor' -))
(def t* (elementwise-tensor' *))
