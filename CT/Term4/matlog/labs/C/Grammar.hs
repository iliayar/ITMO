{-# OPTIONS_GHC -w #-}
module Grammar where
import Tokens
import Data
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
happyExpList = Happy_Data_Array.listArray (0,114) ([4096,0,256,0,13888,6,25444,0,0,704,0,0,0,4248,16384,1590,0,64,0,4,0,16384,1590,0,0,0,0,0,27648,1590,0,0,13888,6,25444,16384,1590,704,4,18816,1,2048,0,0,0,8,0,0,17152,0,1072,0,67,0,0,4120,0,1072,0,16,256,1,25444,16384,1590,0,0,0,49152,2,1024,0,0,0,0,0,0,32768,321,0
	])

{-# NOINLINE happyExpListPerState #-}
happyExpListPerState st =
    token_strs_expected
  where token_strs = ["error","%dummy","%start_parseFile","File","Header","Proof","Expr","Var","Pred","Term","and","or","turn","impl","not","plus","times","forall","exists","eq","zero","'('","')'","'.'","succ","pred","var","%eof"]
        bit_start = st Prelude.* 28
        bit_end = (st Prelude.+ 1) Prelude.* 28
        read_bit = readArrayBit happyExpList
        bits = Prelude.map read_bit [bit_start..bit_end Prelude.- 1]
        bits_indexed = Prelude.zip bits [0..27]
        token_strs_expected = Prelude.concatMap f bits_indexed
        f (Prelude.False, _) = []
        f (Prelude.True, nr) = [token_strs Prelude.!! nr]

action_0 (13) = happyShift action_3
action_0 (4) = happyGoto action_4
action_0 (5) = happyGoto action_2
action_0 _ = happyFail (happyExpListPerState 0)

action_1 (13) = happyShift action_3
action_1 (5) = happyGoto action_2
action_1 _ = happyFail (happyExpListPerState 1)

action_2 (15) = happyShift action_8
action_2 (18) = happyShift action_9
action_2 (19) = happyShift action_10
action_2 (21) = happyShift action_11
action_2 (22) = happyShift action_12
action_2 (26) = happyShift action_13
action_2 (27) = happyShift action_14
action_2 (6) = happyGoto action_15
action_2 (7) = happyGoto action_16
action_2 (9) = happyGoto action_6
action_2 (10) = happyGoto action_7
action_2 _ = happyReduce_4

action_3 (15) = happyShift action_8
action_3 (18) = happyShift action_9
action_3 (19) = happyShift action_10
action_3 (21) = happyShift action_11
action_3 (22) = happyShift action_12
action_3 (26) = happyShift action_13
action_3 (27) = happyShift action_14
action_3 (7) = happyGoto action_5
action_3 (9) = happyGoto action_6
action_3 (10) = happyGoto action_7
action_3 _ = happyFail (happyExpListPerState 3)

action_4 (28) = happyAccept
action_4 _ = happyFail (happyExpListPerState 4)

action_5 (11) = happyShift action_18
action_5 (12) = happyShift action_19
action_5 (14) = happyShift action_20
action_5 _ = happyReduce_2

action_6 _ = happyReduce_12

action_7 (16) = happyShift action_27
action_7 (17) = happyShift action_28
action_7 (20) = happyShift action_29
action_7 (25) = happyShift action_30
action_7 _ = happyFail (happyExpListPerState 7)

action_8 (15) = happyShift action_8
action_8 (18) = happyShift action_9
action_8 (19) = happyShift action_10
action_8 (21) = happyShift action_11
action_8 (22) = happyShift action_12
action_8 (26) = happyShift action_13
action_8 (27) = happyShift action_14
action_8 (7) = happyGoto action_26
action_8 (9) = happyGoto action_6
action_8 (10) = happyGoto action_7
action_8 _ = happyFail (happyExpListPerState 8)

action_9 (27) = happyShift action_24
action_9 (8) = happyGoto action_25
action_9 _ = happyFail (happyExpListPerState 9)

action_10 (27) = happyShift action_24
action_10 (8) = happyGoto action_23
action_10 _ = happyFail (happyExpListPerState 10)

action_11 _ = happyReduce_20

action_12 (15) = happyShift action_8
action_12 (18) = happyShift action_9
action_12 (19) = happyShift action_10
action_12 (21) = happyShift action_11
action_12 (22) = happyShift action_12
action_12 (26) = happyShift action_13
action_12 (27) = happyShift action_14
action_12 (7) = happyGoto action_21
action_12 (9) = happyGoto action_6
action_12 (10) = happyGoto action_22
action_12 _ = happyFail (happyExpListPerState 12)

action_13 _ = happyReduce_15

action_14 _ = happyReduce_21

action_15 _ = happyReduce_1

action_16 (11) = happyShift action_18
action_16 (12) = happyShift action_19
action_16 (14) = happyShift action_20
action_16 (15) = happyShift action_8
action_16 (18) = happyShift action_9
action_16 (19) = happyShift action_10
action_16 (21) = happyShift action_11
action_16 (22) = happyShift action_12
action_16 (26) = happyShift action_13
action_16 (27) = happyShift action_14
action_16 (6) = happyGoto action_17
action_16 (7) = happyGoto action_16
action_16 (9) = happyGoto action_6
action_16 (10) = happyGoto action_7
action_16 _ = happyReduce_4

action_17 _ = happyReduce_3

action_18 (15) = happyShift action_8
action_18 (18) = happyShift action_9
action_18 (19) = happyShift action_10
action_18 (21) = happyShift action_11
action_18 (22) = happyShift action_12
action_18 (26) = happyShift action_13
action_18 (27) = happyShift action_14
action_18 (7) = happyGoto action_41
action_18 (9) = happyGoto action_6
action_18 (10) = happyGoto action_7
action_18 _ = happyFail (happyExpListPerState 18)

action_19 (15) = happyShift action_8
action_19 (18) = happyShift action_9
action_19 (19) = happyShift action_10
action_19 (21) = happyShift action_11
action_19 (22) = happyShift action_12
action_19 (26) = happyShift action_13
action_19 (27) = happyShift action_14
action_19 (7) = happyGoto action_40
action_19 (9) = happyGoto action_6
action_19 (10) = happyGoto action_7
action_19 _ = happyFail (happyExpListPerState 19)

action_20 (15) = happyShift action_8
action_20 (18) = happyShift action_9
action_20 (19) = happyShift action_10
action_20 (21) = happyShift action_11
action_20 (22) = happyShift action_12
action_20 (26) = happyShift action_13
action_20 (27) = happyShift action_14
action_20 (7) = happyGoto action_39
action_20 (9) = happyGoto action_6
action_20 (10) = happyGoto action_7
action_20 _ = happyFail (happyExpListPerState 20)

action_21 (11) = happyShift action_18
action_21 (12) = happyShift action_19
action_21 (14) = happyShift action_20
action_21 (23) = happyShift action_38
action_21 _ = happyFail (happyExpListPerState 21)

action_22 (16) = happyShift action_27
action_22 (17) = happyShift action_28
action_22 (20) = happyShift action_29
action_22 (23) = happyShift action_37
action_22 (25) = happyShift action_30
action_22 _ = happyFail (happyExpListPerState 22)

action_23 (24) = happyShift action_36
action_23 _ = happyFail (happyExpListPerState 23)

action_24 _ = happyReduce_13

action_25 (24) = happyShift action_35
action_25 _ = happyFail (happyExpListPerState 25)

action_26 _ = happyReduce_9

action_27 (21) = happyShift action_11
action_27 (22) = happyShift action_32
action_27 (27) = happyShift action_14
action_27 (10) = happyGoto action_34
action_27 _ = happyFail (happyExpListPerState 27)

action_28 (21) = happyShift action_11
action_28 (22) = happyShift action_32
action_28 (27) = happyShift action_14
action_28 (10) = happyGoto action_33
action_28 _ = happyFail (happyExpListPerState 28)

action_29 (21) = happyShift action_11
action_29 (22) = happyShift action_32
action_29 (27) = happyShift action_14
action_29 (10) = happyGoto action_31
action_29 _ = happyFail (happyExpListPerState 29)

action_30 _ = happyReduce_19

action_31 (16) = happyShift action_27
action_31 (17) = happyShift action_28
action_31 (25) = happyShift action_30
action_31 _ = happyReduce_14

action_32 (21) = happyShift action_11
action_32 (22) = happyShift action_32
action_32 (27) = happyShift action_14
action_32 (10) = happyGoto action_44
action_32 _ = happyFail (happyExpListPerState 32)

action_33 (25) = happyShift action_30
action_33 _ = happyReduce_17

action_34 (17) = happyShift action_28
action_34 (25) = happyShift action_30
action_34 _ = happyReduce_16

action_35 (15) = happyShift action_8
action_35 (18) = happyShift action_9
action_35 (19) = happyShift action_10
action_35 (21) = happyShift action_11
action_35 (22) = happyShift action_12
action_35 (26) = happyShift action_13
action_35 (27) = happyShift action_14
action_35 (7) = happyGoto action_43
action_35 (9) = happyGoto action_6
action_35 (10) = happyGoto action_7
action_35 _ = happyFail (happyExpListPerState 35)

action_36 (15) = happyShift action_8
action_36 (18) = happyShift action_9
action_36 (19) = happyShift action_10
action_36 (21) = happyShift action_11
action_36 (22) = happyShift action_12
action_36 (26) = happyShift action_13
action_36 (27) = happyShift action_14
action_36 (7) = happyGoto action_42
action_36 (9) = happyGoto action_6
action_36 (10) = happyGoto action_7
action_36 _ = happyFail (happyExpListPerState 36)

action_37 _ = happyReduce_18

action_38 _ = happyReduce_8

action_39 (11) = happyShift action_18
action_39 (12) = happyShift action_19
action_39 (14) = happyShift action_20
action_39 _ = happyReduce_5

action_40 (11) = happyShift action_18
action_40 _ = happyReduce_6

action_41 _ = happyReduce_7

action_42 (11) = happyShift action_18
action_42 (12) = happyShift action_19
action_42 (14) = happyShift action_20
action_42 _ = happyReduce_11

action_43 (11) = happyShift action_18
action_43 (12) = happyShift action_19
action_43 (14) = happyShift action_20
action_43 _ = happyReduce_10

action_44 (16) = happyShift action_27
action_44 (17) = happyShift action_28
action_44 (23) = happyShift action_37
action_44 (25) = happyShift action_30
action_44 _ = happyFail (happyExpListPerState 44)

happyReduce_1 = happySpecReduce_2  4 happyReduction_1
happyReduction_1 (HappyAbsSyn6  happy_var_2)
	(HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn4
		 (File happy_var_1 happy_var_2
	)
happyReduction_1 _ _  = notHappyAtAll 

happyReduce_2 = happySpecReduce_2  5 happyReduction_2
happyReduction_2 (HappyAbsSyn7  happy_var_2)
	_
	 =  HappyAbsSyn5
		 (happy_var_2
	)
happyReduction_2 _ _  = notHappyAtAll 

happyReduce_3 = happySpecReduce_2  6 happyReduction_3
happyReduction_3 (HappyAbsSyn6  happy_var_2)
	(HappyAbsSyn7  happy_var_1)
	 =  HappyAbsSyn6
		 (happy_var_1 : happy_var_2
	)
happyReduction_3 _ _  = notHappyAtAll 

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

happyReduce_13 = happySpecReduce_1  8 happyReduction_13
happyReduction_13 (HappyTerminal (TokenVar happy_var_1))
	 =  HappyAbsSyn8
		 (Var happy_var_1
	)
happyReduction_13 _  = notHappyAtAll 

happyReduce_14 = happySpecReduce_3  9 happyReduction_14
happyReduction_14 (HappyAbsSyn10  happy_var_3)
	_
	(HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn9
		 (PredEq happy_var_1 happy_var_3
	)
happyReduction_14 _ _ _  = notHappyAtAll 

happyReduce_15 = happySpecReduce_1  9 happyReduction_15
happyReduction_15 (HappyTerminal (TokenPred happy_var_1))
	 =  HappyAbsSyn9
		 (Pred happy_var_1
	)
happyReduction_15 _  = notHappyAtAll 

happyReduce_16 = happySpecReduce_3  10 happyReduction_16
happyReduction_16 (HappyAbsSyn10  happy_var_3)
	_
	(HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn10
		 (Plus happy_var_1 happy_var_3
	)
happyReduction_16 _ _ _  = notHappyAtAll 

happyReduce_17 = happySpecReduce_3  10 happyReduction_17
happyReduction_17 (HappyAbsSyn10  happy_var_3)
	_
	(HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn10
		 (Times happy_var_1 happy_var_3
	)
happyReduction_17 _ _ _  = notHappyAtAll 

happyReduce_18 = happySpecReduce_3  10 happyReduction_18
happyReduction_18 _
	(HappyAbsSyn10  happy_var_2)
	_
	 =  HappyAbsSyn10
		 (happy_var_2
	)
happyReduction_18 _ _ _  = notHappyAtAll 

happyReduce_19 = happySpecReduce_2  10 happyReduction_19
happyReduction_19 _
	(HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn10
		 (Succ happy_var_1
	)
happyReduction_19 _ _  = notHappyAtAll 

happyReduce_20 = happySpecReduce_1  10 happyReduction_20
happyReduction_20 _
	 =  HappyAbsSyn10
		 (Zero
	)

happyReduce_21 = happySpecReduce_1  10 happyReduction_21
happyReduction_21 (HappyTerminal (TokenVar happy_var_1))
	 =  HappyAbsSyn10
		 (TermVar $ Var happy_var_1
	)
happyReduction_21 _  = notHappyAtAll 

happyNewToken action sts stk [] =
	action 28 28 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	TokenAnd -> cont 11;
	TokenOr -> cont 12;
	TokenTurn -> cont 13;
	TokenImpl -> cont 14;
	TokenNot -> cont 15;
	TokenPlus -> cont 16;
	TokenTimes -> cont 17;
	TokenForall -> cont 18;
	TokenExists -> cont 19;
	TokenEq -> cont 20;
	TokenZero -> cont 21;
	TokenLParen -> cont 22;
	TokenRParen -> cont 23;
	TokenDot -> cont 24;
	TokenSucc -> cont 25;
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
parseFile tks = happyRunIdentity happySomeParser where
 happySomeParser = happyThen (happyParse action_0 tks) (\x -> case x of {HappyAbsSyn4 z -> happyReturn z; _other -> notHappyAtAll })

happySeq = happyDontSeq


parseError :: [Token] -> a
parseError ts = error $ "Parse error: " ++ show ts
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
