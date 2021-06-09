module Annotation where

import Data

data AnnotatedFile = AnnotatedFile Expr [AnnotatedExpr]

data AnnotatedExpr = AnnotatedExpr Expr Annotation

data AxiomNumber = Number Int | ArithmeticNumber Int

data Annotation = AxiomScheme Int AxiomNumber
                | ArithmeticAxiom Int AxiomNumber
                | ModusPonens Int Int Int
                | ForallRule Int Int
                | ExistsRule Int Int

instance Show AnnotatedFile where
  show (AnnotatedFile e es) = "|-" ++ show e ++ "\n" ++ unlines (map show es)

instance Show AnnotatedExpr where
  show (AnnotatedExpr e a) = show a ++ " " ++ show e

instance Show Annotation where
  show (AxiomScheme n k) = "[" ++ show n ++ ". Ax. sch. " ++ show k ++ "]"
  show (ArithmeticAxiom n k) = "[" ++ show n ++ ". Ax. " ++ show k ++ "]"
  show (ModusPonens n k l) = "[" ++ show n ++ ". M.P. " ++ show k ++ ", " ++ show l ++ "]"
  show (ForallRule n k) = "[" ++ show n ++ ". ?-intro " ++ show k ++ "]"
  show (ExistsRule n k) = "[" ++ show n ++ ". @-intro " ++ show k ++ "]"

instance Show AxiomNumber where
  show (Number n) = show n
  show (ArithmeticNumber n) = "A" ++ show n

data AnnotationErrorFile = AnnotationErrorFile AnnotatedFile AnnotationError

data AnnotationError = NonFreeForall Int Var
                     | NonFreeExists Int Var
                     | NonFreeForallAxiom Int Var Term
                     | NonFreeExistsAxiom Int Var Term
                     | NotProved Int
                     | WrongExpressionProved
instance Show AnnotationErrorFile where
  show (AnnotationErrorFile file err) = show file ++ show err

instance Show AnnotationError where
  show (NonFreeForall n v) = "Expression " ++ show n ++ ": variable " ++ show v ++ " occurs free in @-rule."
  show (NonFreeExists n v) = "Expression " ++ show n ++ ": variable " ++ show v ++ " occurs free in ?-rule."
  show (NonFreeForallAxiom n v t) = "Expression " ++ show n ++ ": variable " ++ show v ++ " is not free for term " ++ show t ++ " in @-axiom."
  show (NonFreeExistsAxiom n v t) = "Expression " ++ show n ++ ": variable " ++ show v ++ " is not free for term " ++ show t ++ " in ?-axiom."
  show (NotProved n) = "Expression " ++ show n ++ " is not proved."
  show WrongExpressionProved = "The proof proves different expression."
