{-# OPTIONS_GHC -w #-}
module Grammar where
import Tokens
import qualified Data.Array as Happy_Data_Array
import qualified Data.Bits as Bits
import Control.Applicative(Applicative(..))
import Control.Monad (ap)

-- parser produced by Happy Version 1.20.0

data HappyAbsSyn t4 t5 t6 t7 t8 t9 t10
	= HappyTerminal (Token)
	| HappyErrorToken Prelude.Int
	| HappyAbsSyn4 t4
	| HappyAbsSyn5 t5
	| HappyAbsSyn6 t6
	| HappyAbsSyn7 t7
	| HappyAbsSyn8 t8
	| HappyAbsSyn9 t9
	| HappyAbsSyn10 t10

happyExpList :: Happy_Data_Array.Array Prelude.Int Prelude.Int
happyExpList = Happy_Data_Array.listArray (0,114) ([8192,0,512,0,16,0,26312,0,0,1216,0,0,0,0,0,19,51200,102,0,4,16384,0,0,51200,102,0,0,0,32768,1644,0,0,92,49152,2052,0,147,0,16,0,0,4096,0,0,0,70,24576,4,17920,32768,1644,51200,102,27776,49158,4,0,0,128,0,768,0,17920,0,0,0,0,512,0,26312,32768,1644,0,0,0,0,26312,0,0,0,0,0,0,2096,0
	])

{-# NOINLINE happyExpListPerState #-}
happyExpListPerState st =
    token_strs_expected
  where token_strs = ["error","%dummy","%start_parseCalc","File","Header","Proof","Expr","Var","Pred","Term","and","or","newLine","turn","impl","not","plus","times","forall","exists","eq","zero","'('","')'","'.'","pred","var","%eof"]
        bit_start = st Prelude.* 28
        bit_end = (st Prelude.+ 1) Prelude.* 28
        read_bit = readArrayBit happyExpList
        bits = Prelude.map read_bit [bit_start..bit_end Prelude.- 1]
        bits_indexed = Prelude.zip bits [0..27]
        token_strs_expected = Prelude.concatMap f bits_indexed
        f (Prelude.False, _) = []
        f (Prelude.True, nr) = [token_strs Prelude.!! nr]

action_0 (14) = happyShift action_3
action_0 (4) = happyGoto action_4
action_0 (5) = happyGoto action_2
action_0 _ = happyFail (happyExpListPerState 0)

action_1 (14) = happyShift action_3
action_1 (5) = happyGoto action_2
action_1 _ = happyFail (happyExpListPerState 1)

action_2 (13) = happyShift action_16
action_2 _ = happyFail (happyExpListPerState 2)

action_3 (16) = happyShift action_9
action_3 (19) = happyShift action_10
action_3 (20) = happyShift action_11
action_3 (22) = happyShift action_12
action_3 (23) = happyShift action_13
action_3 (26) = happyShift action_14
action_3 (27) = happyShift action_15
action_3 (7) = happyGoto action_5
action_3 (8) = happyGoto action_6
action_3 (9) = happyGoto action_7
action_3 (10) = happyGoto action_8
action_3 _ = happyFail (happyExpListPerState 3)

action_4 (28) = happyAccept
action_4 _ = happyFail (happyExpListPerState 4)

action_5 (11) = happyShift action_28
action_5 (12) = happyShift action_29
action_5 (15) = happyShift action_30
action_5 _ = happyReduce_2

action_6 _ = happyReduce_13

action_7 _ = happyReduce_12

action_8 (17) = happyShift action_25
action_8 (18) = happyShift action_26
action_8 (21) = happyShift action_27
action_8 _ = happyFail (happyExpListPerState 8)

action_9 (16) = happyShift action_9
action_9 (19) = happyShift action_10
action_9 (20) = happyShift action_11
action_9 (22) = happyShift action_12
action_9 (23) = happyShift action_13
action_9 (26) = happyShift action_14
action_9 (27) = happyShift action_15
action_9 (7) = happyGoto action_24
action_9 (8) = happyGoto action_6
action_9 (9) = happyGoto action_7
action_9 (10) = happyGoto action_8
action_9 _ = happyFail (happyExpListPerState 9)

action_10 (27) = happyShift action_22
action_10 (8) = happyGoto action_23
action_10 _ = happyFail (happyExpListPerState 10)

action_11 (27) = happyShift action_22
action_11 (8) = happyGoto action_21
action_11 _ = happyFail (happyExpListPerState 11)

action_12 _ = happyReduce_20

action_13 (16) = happyShift action_9
action_13 (19) = happyShift action_10
action_13 (20) = happyShift action_11
action_13 (22) = happyShift action_12
action_13 (23) = happyShift action_13
action_13 (26) = happyShift action_14
action_13 (27) = happyShift action_15
action_13 (7) = happyGoto action_19
action_13 (8) = happyGoto action_6
action_13 (9) = happyGoto action_7
action_13 (10) = happyGoto action_20
action_13 _ = happyFail (happyExpListPerState 13)

action_14 _ = happyReduce_16

action_15 (17) = happyReduce_21
action_15 (18) = happyReduce_21
action_15 (21) = happyReduce_21
action_15 (24) = happyReduce_21
action_15 _ = happyReduce_14

action_16 (16) = happyShift action_9
action_16 (19) = happyShift action_10
action_16 (20) = happyShift action_11
action_16 (22) = happyShift action_12
action_16 (23) = happyShift action_13
action_16 (26) = happyShift action_14
action_16 (27) = happyShift action_15
action_16 (6) = happyGoto action_17
action_16 (7) = happyGoto action_18
action_16 (8) = happyGoto action_6
action_16 (9) = happyGoto action_7
action_16 (10) = happyGoto action_8
action_16 _ = happyReduce_4

action_17 _ = happyReduce_1

action_18 (11) = happyShift action_28
action_18 (12) = happyShift action_29
action_18 (13) = happyShift action_43
action_18 (15) = happyShift action_30
action_18 _ = happyFail (happyExpListPerState 18)

action_19 (11) = happyShift action_28
action_19 (12) = happyShift action_29
action_19 (15) = happyShift action_30
action_19 (24) = happyShift action_42
action_19 _ = happyFail (happyExpListPerState 19)

action_20 (17) = happyShift action_25
action_20 (18) = happyShift action_26
action_20 (21) = happyShift action_27
action_20 (24) = happyShift action_41
action_20 _ = happyFail (happyExpListPerState 20)

action_21 (25) = happyShift action_40
action_21 _ = happyFail (happyExpListPerState 21)

action_22 _ = happyReduce_14

action_23 (25) = happyShift action_39
action_23 _ = happyFail (happyExpListPerState 23)

action_24 _ = happyReduce_9

action_25 (22) = happyShift action_12
action_25 (23) = happyShift action_35
action_25 (27) = happyShift action_36
action_25 (10) = happyGoto action_38
action_25 _ = happyFail (happyExpListPerState 25)

action_26 (22) = happyShift action_12
action_26 (23) = happyShift action_35
action_26 (27) = happyShift action_36
action_26 (10) = happyGoto action_37
action_26 _ = happyFail (happyExpListPerState 26)

action_27 (22) = happyShift action_12
action_27 (23) = happyShift action_35
action_27 (27) = happyShift action_36
action_27 (10) = happyGoto action_34
action_27 _ = happyFail (happyExpListPerState 27)

action_28 (16) = happyShift action_9
action_28 (19) = happyShift action_10
action_28 (20) = happyShift action_11
action_28 (22) = happyShift action_12
action_28 (23) = happyShift action_13
action_28 (26) = happyShift action_14
action_28 (27) = happyShift action_15
action_28 (7) = happyGoto action_33
action_28 (8) = happyGoto action_6
action_28 (9) = happyGoto action_7
action_28 (10) = happyGoto action_8
action_28 _ = happyFail (happyExpListPerState 28)

action_29 (16) = happyShift action_9
action_29 (19) = happyShift action_10
action_29 (20) = happyShift action_11
action_29 (22) = happyShift action_12
action_29 (23) = happyShift action_13
action_29 (26) = happyShift action_14
action_29 (27) = happyShift action_15
action_29 (7) = happyGoto action_32
action_29 (8) = happyGoto action_6
action_29 (9) = happyGoto action_7
action_29 (10) = happyGoto action_8
action_29 _ = happyFail (happyExpListPerState 29)

action_30 (16) = happyShift action_9
action_30 (19) = happyShift action_10
action_30 (20) = happyShift action_11
action_30 (22) = happyShift action_12
action_30 (23) = happyShift action_13
action_30 (26) = happyShift action_14
action_30 (27) = happyShift action_15
action_30 (7) = happyGoto action_31
action_30 (8) = happyGoto action_6
action_30 (9) = happyGoto action_7
action_30 (10) = happyGoto action_8
action_30 _ = happyFail (happyExpListPerState 30)

action_31 (11) = happyShift action_28
action_31 (12) = happyShift action_29
action_31 (15) = happyShift action_30
action_31 _ = happyReduce_5

action_32 _ = happyReduce_6

action_33 (12) = happyShift action_29
action_33 _ = happyReduce_7

action_34 (17) = happyShift action_25
action_34 (18) = happyShift action_26
action_34 _ = happyReduce_15

action_35 (22) = happyShift action_12
action_35 (23) = happyShift action_35
action_35 (27) = happyShift action_36
action_35 (10) = happyGoto action_47
action_35 _ = happyFail (happyExpListPerState 35)

action_36 _ = happyReduce_21

action_37 _ = happyReduce_18

action_38 (18) = happyShift action_26
action_38 _ = happyReduce_17

action_39 (16) = happyShift action_9
action_39 (19) = happyShift action_10
action_39 (20) = happyShift action_11
action_39 (22) = happyShift action_12
action_39 (23) = happyShift action_13
action_39 (26) = happyShift action_14
action_39 (27) = happyShift action_15
action_39 (7) = happyGoto action_46
action_39 (8) = happyGoto action_6
action_39 (9) = happyGoto action_7
action_39 (10) = happyGoto action_8
action_39 _ = happyFail (happyExpListPerState 39)

action_40 (16) = happyShift action_9
action_40 (19) = happyShift action_10
action_40 (20) = happyShift action_11
action_40 (22) = happyShift action_12
action_40 (23) = happyShift action_13
action_40 (26) = happyShift action_14
action_40 (27) = happyShift action_15
action_40 (7) = happyGoto action_45
action_40 (8) = happyGoto action_6
action_40 (9) = happyGoto action_7
action_40 (10) = happyGoto action_8
action_40 _ = happyFail (happyExpListPerState 40)

action_41 _ = happyReduce_19

action_42 _ = happyReduce_8

action_43 (16) = happyShift action_9
action_43 (19) = happyShift action_10
action_43 (20) = happyShift action_11
action_43 (22) = happyShift action_12
action_43 (23) = happyShift action_13
action_43 (26) = happyShift action_14
action_43 (27) = happyShift action_15
action_43 (6) = happyGoto action_44
action_43 (7) = happyGoto action_18
action_43 (8) = happyGoto action_6
action_43 (9) = happyGoto action_7
action_43 (10) = happyGoto action_8
action_43 _ = happyReduce_4

action_44 _ = happyReduce_3

action_45 (11) = happyShift action_28
action_45 (12) = happyShift action_29
action_45 (15) = happyShift action_30
action_45 _ = happyReduce_11

action_46 (11) = happyShift action_28
action_46 (12) = happyShift action_29
action_46 (15) = happyShift action_30
action_46 _ = happyReduce_10

action_47 (17) = happyShift action_25
action_47 (18) = happyShift action_26
action_47 (24) = happyShift action_41
action_47 _ = happyFail (happyExpListPerState 47)

happyReduce_1 = happySpecReduce_3  4 happyReduction_1
happyReduction_1 (HappyAbsSyn6  happy_var_3)
	_
	(HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn4
		 (File happy_var_1 happy_var_3
	)
happyReduction_1 _ _ _  = notHappyAtAll 

happyReduce_2 = happySpecReduce_2  5 happyReduction_2
happyReduction_2 (HappyAbsSyn7  happy_var_2)
	_
	 =  HappyAbsSyn5
		 (happy_var_2
	)
happyReduction_2 _ _  = notHappyAtAll 

happyReduce_3 = happySpecReduce_3  6 happyReduction_3
happyReduction_3 (HappyAbsSyn6  happy_var_3)
	_
	(HappyAbsSyn7  happy_var_1)
	 =  HappyAbsSyn6
		 (happy_var_1 : happy_var_3
	)
happyReduction_3 _ _ _  = notHappyAtAll 

happyReduce_4 = happySpecReduce_0  6 happyReduction_4
happyReduction_4  =  HappyAbsSyn6
		 ([]
	)

happyReduce_5 = happySpecReduce_3  7 happyReduction_5
happyReduction_5 (HappyAbsSyn7  happy_var_3)
	_
	(HappyAbsSyn7  happy_var_1)
	 =  HappyAbsSyn7
		 (Impl happy_var_1 happy_var_3
	)
happyReduction_5 _ _ _  = notHappyAtAll 

happyReduce_6 = happySpecReduce_3  7 happyReduction_6
happyReduction_6 (HappyAbsSyn7  happy_var_3)
	_
	(HappyAbsSyn7  happy_var_1)
	 =  HappyAbsSyn7
		 (Or happy_var_1 happy_var_3
	)
happyReduction_6 _ _ _  = notHappyAtAll 

happyReduce_7 = happySpecReduce_3  7 happyReduction_7
happyReduction_7 (HappyAbsSyn7  happy_var_3)
	_
	(HappyAbsSyn7  happy_var_1)
	 =  HappyAbsSyn7
		 (And happy_var_1 happy_var_3
	)
happyReduction_7 _ _ _  = notHappyAtAll 

happyReduce_8 = happySpecReduce_3  7 happyReduction_8
happyReduction_8 _
	(HappyAbsSyn7  happy_var_2)
	_
	 =  HappyAbsSyn7
		 (happy_var_2
	)
happyReduction_8 _ _ _  = notHappyAtAll 

happyReduce_9 = happySpecReduce_2  7 happyReduction_9
happyReduction_9 (HappyAbsSyn7  happy_var_2)
	_
	 =  HappyAbsSyn7
		 (Not happy_var_2
	)
happyReduction_9 _ _  = notHappyAtAll 

happyReduce_10 = happyReduce 4 7 happyReduction_10
happyReduction_10 ((HappyAbsSyn7  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn8  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn7
		 (Forall happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_11 = happyReduce 4 7 happyReduction_11
happyReduction_11 ((HappyAbsSyn7  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn8  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn7
		 (Exists happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_12 = happySpecReduce_1  7 happyReduction_12
happyReduction_12 (HappyAbsSyn9  happy_var_1)
	 =  HappyAbsSyn7
		 (ExprPred happy_var_1
	)
happyReduction_12 _  = notHappyAtAll 

happyReduce_13 = happySpecReduce_1  7 happyReduction_13
happyReduction_13 (HappyAbsSyn8  happy_var_1)
	 =  HappyAbsSyn7
		 (ExprVar happy_var_1
	)
happyReduction_13 _  = notHappyAtAll 

happyReduce_14 = happySpecReduce_1  8 happyReduction_14
happyReduction_14 (HappyTerminal (TokenVar happy_var_1))
	 =  HappyAbsSyn8
		 (Var happy_var_1
	)
happyReduction_14 _  = notHappyAtAll 

happyReduce_15 = happySpecReduce_3  9 happyReduction_15
happyReduction_15 (HappyAbsSyn10  happy_var_3)
	_
	(HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn9
		 (PredEq happy_var_1 happy_var_3
	)
happyReduction_15 _ _ _  = notHappyAtAll 

happyReduce_16 = happySpecReduce_1  9 happyReduction_16
happyReduction_16 (HappyTerminal (TokenPred happy_var_1))
	 =  HappyAbsSyn9
		 (Pred happy_var_1
	)
happyReduction_16 _  = notHappyAtAll 

happyReduce_17 = happySpecReduce_3  10 happyReduction_17
happyReduction_17 (HappyAbsSyn10  happy_var_3)
	_
	(HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn10
		 (Plus happy_var_1 happy_var_3
	)
happyReduction_17 _ _ _  = notHappyAtAll 

happyReduce_18 = happySpecReduce_3  10 happyReduction_18
happyReduction_18 (HappyAbsSyn10  happy_var_3)
	_
	(HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn10
		 (Times happy_var_1 happy_var_3
	)
happyReduction_18 _ _ _  = notHappyAtAll 

happyReduce_19 = happySpecReduce_3  10 happyReduction_19
happyReduction_19 _
	(HappyAbsSyn10  happy_var_2)
	_
	 =  HappyAbsSyn10
		 (happy_var_2
	)
happyReduction_19 _ _ _  = notHappyAtAll 

happyReduce_20 = happySpecReduce_1  10 happyReduction_20
happyReduction_20 _
	 =  HappyAbsSyn10
		 (Zero
	)

happyReduce_21 = happySpecReduce_1  10 happyReduction_21
happyReduction_21 (HappyTerminal (TokenVar happy_var_1))
	 =  HappyAbsSyn10
		 (TermVar happy_var_1
	)
happyReduction_21 _  = notHappyAtAll 

happyNewToken action sts stk [] =
	action 28 28 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	TokenAnd -> cont 11;
	TokenOr -> cont 12;
	TokenNewLine -> cont 13;
	TokenTurn -> cont 14;
	TokenImpl -> cont 15;
	TokenNot -> cont 16;
	TokenPlus -> cont 17;
	TokenTimes -> cont 18;
	TokenForall -> cont 19;
	TokenExists -> cont 20;
	TokenEq -> cont 21;
	TokenZero -> cont 22;
	TokenLParen -> cont 23;
	TokenRParen -> cont 24;
	TokenDot -> cont 25;
	TokenPred happy_dollar_dollar -> cont 26;
	TokenVar happy_dollar_dollar -> cont 27;
	_ -> happyError' ((tk:tks), [])
	}

happyError_ explist 28 tk tks = happyError' (tks, explist)
happyError_ explist _ tk tks = happyError' ((tk:tks), explist)

newtype HappyIdentity a = HappyIdentity a
happyIdentity = HappyIdentity
happyRunIdentity (HappyIdentity a) = a

instance Prelude.Functor HappyIdentity where
    fmap f (HappyIdentity a) = HappyIdentity (f a)

instance Applicative HappyIdentity where
    pure  = HappyIdentity
    (<*>) = ap
instance Prelude.Monad HappyIdentity where
    return = pure
    (HappyIdentity p) >>= q = q p

happyThen :: () => HappyIdentity a -> (a -> HappyIdentity b) -> HappyIdentity b
happyThen = (Prelude.>>=)
happyReturn :: () => a -> HappyIdentity a
happyReturn = (Prelude.return)
happyThen1 m k tks = (Prelude.>>=) m (\a -> k a tks)
happyReturn1 :: () => a -> b -> HappyIdentity a
happyReturn1 = \a tks -> (Prelude.return) a
happyError' :: () => ([(Token)], [Prelude.String]) -> HappyIdentity a
happyError' = HappyIdentity Prelude.. (\(tokens, _) -> parseError tokens)
parseCalc tks = happyRunIdentity happySomeParser where
 happySomeParser = happyThen (happyParse action_0 tks) (\x -> case x of {HappyAbsSyn4 z -> happyReturn z; _other -> notHappyAtAll })

happySeq = happyDontSeq


parseError :: [Token] -> a
parseError _ = error "Parse error"

data File = File Epxr [Expr]

data Pred = Pred String | PredEq Term Term

data Term = Plus Term Term
          | Times Term Term
          | TermVar Var
          | Zero

data Var = Var String

data Expr = Impl Expr Expr
          | Or Expr Expr
          | Not Expr
          | Forall Var Expr
          | Exists Var Expr
          | ExprVar Var
          | ExprPred Pred
         deriving Show
{-# LINE 1 "templates/GenericTemplate.hs" #-}
-- $Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp $










































data Happy_IntList = HappyCons Prelude.Int Happy_IntList








































infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is ERROR_TOK, it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept (1) tk st sts (_ `HappyStk` ans `HappyStk` _) =
        happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
         (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action









































indexShortOffAddr arr off = arr Happy_Data_Array.! off


{-# INLINE happyLt #-}
happyLt x y = (x Prelude.< y)






readArrayBit arr bit =
    Bits.testBit (indexShortOffAddr arr (bit `Prelude.div` 16)) (bit `Prelude.mod` 16)






-----------------------------------------------------------------------------
-- HappyState data type (not arrays)



newtype HappyState b c = HappyState
        (Prelude.Int ->                    -- token number
         Prelude.Int ->                    -- token number (yes, again)
         b ->                           -- token semantic value
         HappyState b c ->              -- current state
         [HappyState b c] ->            -- state stack
         c)



-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state (1) tk st sts stk@(x `HappyStk` _) =
     let i = (case x of { HappyErrorToken (i) -> i }) in
--     trace "shifting the error token" $
     new_state i i tk (HappyState (new_state)) ((st):(sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state ((st):(sts)) ((HappyTerminal (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_0 nt fn j tk st@((HappyState (action))) sts stk
     = action nt j tk st ((st):(sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@(((st@(HappyState (action))):(_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_2 nt fn j tk _ ((_):(sts@(((st@(HappyState (action))):(_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_3 nt fn j tk _ ((_):(((_):(sts@(((st@(HappyState (action))):(_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k Prelude.- ((1) :: Prelude.Int)) sts of
         sts1@(((st1@(HappyState (action))):(_))) ->
                let r = fn stk in  -- it doesn't hurt to always seq here...
                happyDoSeq r (action nt j tk st1 sts1 r)

happyMonadReduce k nt fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
      case happyDrop k ((st):(sts)) of
        sts1@(((st1@(HappyState (action))):(_))) ->
          let drop_stk = happyDropStk k stk in
          happyThen1 (fn stk tk) (\r -> action nt j tk st1 sts1 (r `HappyStk` drop_stk))

happyMonad2Reduce k nt fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
      case happyDrop k ((st):(sts)) of
        sts1@(((st1@(HappyState (action))):(_))) ->
         let drop_stk = happyDropStk k stk





             _ = nt :: Prelude.Int
             new_state = action

          in
          happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))

happyDrop (0) l = l
happyDrop n ((_):(t)) = happyDrop (n Prelude.- ((1) :: Prelude.Int)) t

happyDropStk (0) l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n Prelude.- ((1)::Prelude.Int)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction









happyGoto action j tk st = action j j tk (HappyState action)


-----------------------------------------------------------------------------
-- Error recovery (ERROR_TOK is the error token)

-- parse error if we are in recovery and we fail again
happyFail explist (1) tk old_st _ stk@(x `HappyStk` _) =
     let i = (case x of { HappyErrorToken (i) -> i }) in
--      trace "failing" $ 
        happyError_ explist i tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  ERROR_TOK tk old_st CONS(HAPPYSTATE(action),sts) 
                                                (saved_tok `HappyStk` _ `HappyStk` stk) =
--      trace ("discarding state, depth " ++ show (length stk))  $
        DO_ACTION(action,ERROR_TOK,tk,sts,(saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail explist i tk (HappyState (action)) sts stk =
--      trace "entering error recovery" $
        action (1) (1) tk (HappyState (action)) sts ((HappyErrorToken (i)) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = Prelude.error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions







-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--      happySeq = happyDoSeq
-- otherwise it emits
--      happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `Prelude.seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.









{-# NOINLINE happyShift #-}
{-# NOINLINE happySpecReduce_0 #-}
{-# NOINLINE happySpecReduce_1 #-}
{-# NOINLINE happySpecReduce_2 #-}
{-# NOINLINE happySpecReduce_3 #-}
{-# NOINLINE happyReduce #-}
{-# NOINLINE happyMonadReduce #-}
{-# NOINLINE happyGoto #-}
{-# NOINLINE happyFail #-}

-- end of Happy Template.
