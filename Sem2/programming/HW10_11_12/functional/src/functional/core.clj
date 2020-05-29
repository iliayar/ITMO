;; (ns functional.core)

;; Functional

(defn avg-imp [& xs] (/ (apply + xs) (count xs)))

(defn constant [value]
  (fn [args] value))

(defn variable [name]
  (fn [args] (get args name)))

(defn operation [f]
  (fn [& operands]
    (fn [args] (apply f (mapv (fn [g] (g args)) operands)))))

(defn my-divide [& xs] (if (== 1 (count xs)) (/ 1 (double (first xs)))
                           (reduce (fn [x y] (/ x (double y))) xs)))

(def add (operation +))
(def subtract (operation -))
(def multiply (operation *))
(def divide (operation my-divide))
(def avg (operation avg-imp))
(def med (operation (fn [& xs] (nth (sort xs) (quot (count xs) 2)))))
(def negate subtract)

(def func-operations
  {:constant constant
   :variable variable
   '+ add
   '- subtract
   '* multiply
   '/ divide
   'negate negate
   'avg avg
   'med med })


;; Object

(defn proto-get [obj key]
  (cond
    (contains? obj key) (obj key)
    (contains? obj :prototype) (proto-get (obj :prototype) key)
    :else nil))

(defn proto-call [obj key & args]
  (apply (proto-get obj key) obj args))

(defn field [key]
  (fn [obj] (proto-get obj key)))

(defn method [key]
  (fn [obj & args] (apply proto-call obj key args)))


(def toString (method :to-string))
(def toStringSuffix (method :to-string-suffix))
(def toStringInfix (method :to-string-infix))
(def evaluate (method :evaluate))
(def diff (method :diff))

(def ZERO)
(def Constant' (let [_value (field :value)
                     to-string-imp (fn [this] (format "%.1f" (double (_value this))))]
                 {:to-string to-string-imp
                  :to-string-suffix to-string-imp
                  :to-string-infix to-string-imp
                  :diff (fn [_ _] ZERO)
                  :evaluate (fn [this _] (_value this))}))

(defn Constant [value]
  {:prototype Constant'
   :value value})
(def ZERO (Constant 0))
(def ONE (Constant 1))



(def Variable' (let [_symbol (field :symbol)
                     to-string-imp (fn [this] (_symbol this))]
                 {:to-string to-string-imp
                  :to-string-suffix to-string-imp
                  :to-string-infix to-string-imp
                  :diff (fn [this arg] (if (= arg (_symbol this)) ONE ZERO))
                  :evaluate (fn [this args] (args (_symbol this)))}))
(defn Variable [symbol]
  {:prototype Variable'
   :symbol symbol})

(def Operation
  (let [_operands (field :operands)
        _symbol (field :symbol)
        _evaluate (method :evaluate-imp)
        _diff (method :diff-imp)
        operands-str (fn [this str-fnc join-str]
                       (clojure.string/join join-str (map str-fnc (_operands this))))]
    {:evaluate (fn [this args]
                 (apply _evaluate this
                            (map (fn [operand] (evaluate operand args)) (_operands this))))
     :diff (fn [this arg]
             (_diff this arg
                    (_operands this)
                    (map (fn [operand] (diff operand arg)) (_operands this))))
     :to-string (fn [this] (str "(" (_symbol this) " " (operands-str this toString " ") ")"))
     :to-string-suffix (fn [this] (str "(" (operands-str this toStringSuffix " ") " " (_symbol this) ")"))
     :to-string-infix (fn [this] (if (= 1 (count (_operands this)))
                                   (str (_symbol this) "(" (toStringInfix (first (_operands this))) ")")
                                   (str "(" (operands-str this toStringInfix (str " " (_symbol this) " ")) ")")))}))

(defn create-operation
  [symbol evaluate-imp diff-imp]
  (let [abstract-operation {:prototype Operation
                            :evaluate-imp (fn [this & xs] (apply evaluate-imp xs))
                            :diff-imp (fn [this & xs] (apply diff-imp xs))
                            :symbol symbol}]
    (fn [& operands]
      {:prototype abstract-operation
       :operands operands})))


(defn create-bitwise [symbol evaluate-imp]
  (create-operation
   symbol
   (fn [a b] (Double/longBitsToDouble
              (evaluate-imp (Double/doubleToLongBits a)
                            (Double/doubleToLongBits b))))
   nil))

(def Add (create-operation
          '+
          +
          (fn [_ _ d-operands] (apply Add d-operands))))
(def And (create-bitwise
          '&
          bit-and))
(def Or (create-bitwise
         '|
         bit-or))
(def Xor (create-bitwise
          (symbol "^")
          bit-xor))
(def Subtract (create-operation
               '-
               -
               (fn [_ _ d-operands] (apply Subtract d-operands))))
(def Negate (create-operation
             'negate
             -
             (fn [_ _ [dx]] (Negate dx))))

(def Multiply (create-operation
               '*
               *
               (fn [arg operands d-operands]
                 (if (== 0 (count operands)) ZERO
                 (letfn [(diff-reduce [[x dx] [y dy]]
                           [(Multiply x y) (Add (Multiply x dy) (Multiply y dx))])]
                   (second (reduce diff-reduce [ONE ZERO] (map vector operands d-operands))))))))
(def Divide (create-operation
             '/
             my-divide
             (fn [arg operands d-operands]
               (if (== 1 (count operands)) (Divide (first d-operands)
                                              (Multiply (first operands) (first operands)))
               (letfn [(diff-reduce [[x dx] [y dy]]
                       [(Divide x y) (Divide (Subtract (Multiply dx y) (Multiply x dy))
                                             (Multiply y y))])]
               (second (reduce diff-reduce (map vector operands d-operands))))))))
(def Sum (create-operation
          'sum
          +
          (fn [_ _ d-operands] (apply Sum d-operands))))
(def Avg (create-operation
          'avg
          avg-imp
          (fn [_ _ d-operands] (Divide (apply Sum d-operands) (Constant (count d-operands))))))
(def obj-operations
  {:constant Constant
   :variable Variable
   '+ Add
   '& And
   '| Or
   (symbol "^") Xor
   '- Subtract
   '* Multiply
   '/ Divide
   'negate Negate
   'sum Sum
   'avg Avg})

;; Parser

(defn create-parser [symbols] (fn [expression]
  (letfn [(parser' [expression]
            (cond
              (number? expression) ((get symbols :constant) expression)
              (symbol? expression) ((get symbols :variable) (str expression))
              (seq? expression) (apply (get symbols (first expression)) (map parser' (rest expression)))))]
    (parser' (read-string expression)))))
(def parseFunction (create-parser func-operations))
(def parseObject (create-parser obj-operations))

;; Combinator Parser

(defn -return [value tail] {:value value :tail tail})
(def -valid? boolean)
(def -value :value)
(def -tail :tail)
(defn _show [result]
  (if (-valid? result) (str "-> " (pr-str (-value result)) " | " (pr-str (apply str (-tail result))))
      "!"))
(defn tabulate [parser inputs]
  (run! (fn [input] (printf "    %-10s %s\n" (pr-str input) (_show (parser input)))) inputs))

(defn _empty [value] (partial -return value))
(defn _char [p]
  (fn [[c & cs]]
    (if (and c (p c)) (-return c cs))))
(defn _map [f result]
  (if (-valid? result)
    (-return (f (-value result)) (-tail result))))

(defn _combine [f a b]
  (fn [str]
    (let [ar ((force a) str)]
      (if (-valid? ar)
        (_map (partial f (-value ar))
              ((force b) (-tail ar)))))))
(defn _either [a b]
  (fn [str]
    (let [ar ((force a) str)]
      (if (-valid? ar) ar ((force b) str)))))

(defn _parser [p]
  (fn [input]
    (-value ((_combine (fn [v _] v) p (_char #{\u0000})) (str input \u0000)))))
(defn +char [chars] (_char (set chars)))
(defn +char-not [chars] (_char (comp not (set chars))))
(defn +map [f parser] (comp (partial _map f) parser))
(def +parser _parser)

(def +ignore (partial +map (constantly 'ignore)))
(defn iconj [coll value]
  (if (= value 'ignore) coll (conj coll value)))
(defn +seq [& ps]
  (reduce (partial _combine iconj) (_empty []) ps))
(defn +seqf [f & ps] (+map (partial apply f) (apply +seq ps)))
(defn +seqn [n & ps] (apply +seqf (fn [& vs] (nth vs n)) ps))

(defn +or [p & ps]
  (reduce _either p ps))
(defn +opt [p]
  (+or p (_empty nil)))
(defn +star [p]
  (letfn [(rec [] (+or (+seqf cons p (delay (rec))) (_empty ())))] (rec)))
(defn +plus [p] (+seqf cons p (+star p)))
(defn +str [p] (+map (partial apply str) p))

;; Common

(def *digit (+char "0123456789"))
(def *number (+seqf str
                    (+opt (+char "-")) (+str (+plus *digit))
                    (+opt (+seqf str (+char ".") (+str (+star *digit))))))
(def *constant (+map (comp Constant read-string) *number))

(def *variable (+map (comp Variable str) (+char "xyz")))


(def *space (+char " \t\n\r"))
(def *ws (+ignore (+star *space)))

(defn +word [s] (apply +seqf str (map (comp +char str) s)))

(defn +operation-parser [ops-map] (+map
                 (comp ops-map symbol)
                 (+str (apply +or (map (comp +word str) (keys ops-map))))))
(def *all-operations (+operation-parser obj-operations))

;; Suffix
(def suffix
  (+or
    (+seqn 1
           *ws (+char "(") *ws
           (+map (fn [[args op]] (apply op args))
                 (+seq
                   (+plus (+seqn 0 (delay suffix) *ws))
                   *all-operations))
           *ws (+char ")") *ws)
    (+seqn 0 *ws (+or *constant *variable) *ws)))

(def parseObjectSuffix (+parser suffix))

;; Infix

(declare prior-0)
(def *unary-operations (+operation-parser {'negate Negate}))
(def unary
  (+seqn 0 *ws
         (+or (+seqn 1 (+char "(") (delay prior-0) (+char ")"))
              (+map (fn [[op arg]] (op arg))
                    (+seq *unary-operations  (delay unary)))
              *constant *variable)
         *ws))

(defn apply-op' [left-assoc]
  (letfn [(reduce' [args f]
            (reduce f (first args) (partition 2 (rest args))))
          (apply-op-imp [args]
            (if left-assoc
              (reduce' args (fn [a [op b]] (op a b)))
              (reduce' (reverse args) (fn [a [op b]] (op b a)))))]
    apply-op-imp))

(defn prior-n' [next ops-map left-assoc]
  (let [*operations (+operation-parser ops-map)]
  (+map (apply-op' left-assoc)
        (+seqf cons next (+map (partial apply concat)
                               (+star (+seq *operations next)))))))
;; (def prior-2 (prior-n' unary ["**" "//"] false))
(def prior-4 (prior-n' unary {'* Multiply
                              '/ Divide} true))
(def prior-3 (prior-n' prior-4 {'+ Add
                                '- Subtract} true))
(def prior-2 (prior-n' prior-3 {'& And} true))
(def prior-1 (prior-n' prior-2 {'| Or} true))
(def prior-0 (prior-n' prior-1 {(symbol "^") Xor} true))

(def parseObjectInfix (+parser prior-0))
