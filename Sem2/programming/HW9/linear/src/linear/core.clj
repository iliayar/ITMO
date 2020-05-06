(ns linear.core)


(defn shape [a] (cond
                (every? number? a) (vector (count a))
                (some number? a) nil
                (and (not-any? nil? (mapv shape a)) (apply = (mapv shape a))) (conj (first (mapv shape a)) (count a))
                :else nil))
(defn dim [a] (if (nil? (shape a)) 0 (count (shape a))))

(defn same-shape? [& xs] (apply = (mapv shape xs)))
(defn tensor? [a] (not (nil? (shape a))))
(defn vec? [v] (= (dim v) 1))
(defn matrix? [m] (= (dim m) 2))
(defn vec3? [v] (= (shape v) [3]))

(defn elementwise' [op] (fn [& xs]
  {:pre [(apply same-shape? xs) (every? tensor? xs)]
   :post [(same-shape? % (first xs))]}
  (apply mapv op xs)))

(def v+ (elementwise' +))
(def v- (elementwise' -))
(def v* (elementwise' *))

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

(defn elementwise-scalar' [f] (fn [v & ss]
  {:pre [(every? number? ss) (tensor? v)]
   :post [(same-shape? v %)]}
  (let [s (apply * ss)] (mapv (fn [a] (f a s)) v))))
(def v*s (elementwise-scalar' *))

(def m+ (elementwise' v+))
(def m- (elementwise' v-))
(def m* (elementwise' v*))

(def m*s (elementwise-scalar' v*s))
(defn m*v [m & vs]
  {:pre [(apply same-shape? vs)
         (= (first (shape m)) (first (shape (first vs))))
         (matrix? m)]
   :post [(= (first (shape %)) (second (shape m)))]}
  (mapv (apply partial scalar vs) m))

(defn transpose [m] (apply mapv vector m))

(defn m*m' [a b]
  {:pre [(= (first (shape a)) (second (shape b)))
         (matrix? a) (matrix? b)]
   :post [(= (second (shape a)) (second (shape %)))
          (= (first (shape b)) (first (shape %)))]}
  (mapv (fn [v] (m*v (transpose b) v)) a))
(defn m*m [& ms] (reduce m*m' ms))


(defn tensor-elementwise' [op] (letfn [(te [& xs]
  {:pre [(apply same-shape? xs) (every? tensor? xs)]
   :post [(same-shape? (first xs) %) (tensor? %)]}
  (cond
    (= (dim (first xs)) 1) (apply mapv op xs)
    :else (apply mapv te xs)))] te))

(def t+ (tensor-elementwise' +))
(def t- (tensor-elementwise' -))
(def t* (tensor-elementwise' *))
