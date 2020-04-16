(ns linear.core)

(defn v' [op & xs] (apply mapv op xs))
(def v+ (partial v' +))
(def v- (partial v' -))
(def v* (partial v' *))


(defn scalar [a b] (reduce + (v* a b)))

(defn v*s [c & xs] (map (fn [v] (mapv (fn [a] (* a c)) v)) xs))
