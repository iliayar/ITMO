{-# OPTIONS_GHC -w #-}
module Grammar where
import Tokens
import Proof
import qualified Data.Map as M
import qualified Data.Array as Happy_Data_Array
import qualified Data.Bits as Bits
import Control.Applicative(Applicative(..))
import Control.Monad (ap)

-- parser produced by Happy Version 1.20.0

data HappyAbsSyn t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
	= HappyTerminal (Token)
	| HappyErrorToken Prelude.Int
	| HappyAbsSyn4 t4
	| HappyAbsSyn5 t5
	| HappyAbsSyn6 t6
	| HappyAbsSyn7 t7
	| HappyAbsSyn8 t8
	| HappyAbsSyn9 t9
	| HappyAbsSyn10 t10
	| HappyAbsSyn11 t11
	| HappyAbsSyn12 t12
	| HappyAbsSyn13 t13
	| HappyAbsSyn14 t14
	| HappyAbsSyn15 t15

happyExpList :: Happy_Data_Array.Array Prelude.Int Prelude.Int
happyExpList = Happy_Data_Array.listArray (0,97) ([0,2,0,1,0,0,4096,0,8192,0,4096,0,0,0,0,0,0,0,32768,0,0,0,2048,0,72,1,49220,0,4,0,128,32768,6144,0,0,0,0,4096,0,2048,0,17408,192,0,8,0,1,0,0,64,0,288,4,0,4,2048,0,256,0,16386,0,1,0,8192,0,16,0,256,0,0,2048,0,9216,128,0,0,0,0,8192,0,1088,12,544,6,0,0,0,0,1024,0,16386,0,8201,0,0,0,0,0,0,0,1040,0,0,32768,0,8704,96,0,0,2176,24,0,0,0
	])

{-# NOINLINE happyExpListPerState #-}
happyExpListPerState st =
    token_strs_expected
  where token_strs = ["error","%dummy","%start_parseFile","File","Proof","Indent","Line","TypedExpression","Context","ContextPrime","Type","Monotype","Expression","Application","Atom","var","rule","indent","forall","let","in","'.'","':'","'->'","'|-'","','","'='","lambda","'('","')'","%eof"]
        bit_start = st Prelude.* 31
        bit_end = (st Prelude.+ 1) Prelude.* 31
        read_bit = readArrayBit happyExpList
        bits = Prelude.map read_bit [bit_start..bit_end Prelude.- 1]
        bits_indexed = Prelude.zip bits [0..30]
        token_strs_expected = Prelude.concatMap f bits_indexed
        f (Prelude.False, _) = []
        f (Prelude.True, nr) = [token_strs Prelude.!! nr]

action_0 (18) = happyShift action_5
action_0 (31) = happyReduce_2
action_0 (4) = happyGoto action_6
action_0 (5) = happyGoto action_2
action_0 (6) = happyGoto action_3
action_0 (7) = happyGoto action_4
action_0 _ = happyReduce_4

action_1 (18) = happyShift action_5
action_1 (5) = happyGoto action_2
action_1 (6) = happyGoto action_3
action_1 (7) = happyGoto action_4
action_1 _ = happyFail (happyExpListPerState 1)

action_2 _ = happyReduce_1

action_3 (16) = happyShift action_11
action_3 (9) = happyGoto action_9
action_3 (10) = happyGoto action_10
action_3 _ = happyReduce_9

action_4 (18) = happyShift action_5
action_4 (31) = happyReduce_2
action_4 (5) = happyGoto action_8
action_4 (6) = happyGoto action_3
action_4 (7) = happyGoto action_4
action_4 _ = happyReduce_4

action_5 (18) = happyShift action_5
action_5 (6) = happyGoto action_7
action_5 _ = happyReduce_4

action_6 (31) = happyAccept
action_6 _ = happyFail (happyExpListPerState 6)

action_7 _ = happyReduce_5

action_8 _ = happyReduce_3

action_9 (25) = happyShift action_13
action_9 _ = happyFail (happyExpListPerState 9)

action_10 _ = happyReduce_8

action_11 (23) = happyShift action_12
action_11 _ = happyFail (happyExpListPerState 11)

action_12 (16) = happyShift action_24
action_12 (19) = happyShift action_25
action_12 (29) = happyShift action_26
action_12 (11) = happyGoto action_22
action_12 (12) = happyGoto action_23
action_12 _ = happyFail (happyExpListPerState 12)

action_13 (16) = happyShift action_18
action_13 (20) = happyShift action_19
action_13 (28) = happyShift action_20
action_13 (29) = happyShift action_21
action_13 (8) = happyGoto action_14
action_13 (13) = happyGoto action_15
action_13 (14) = happyGoto action_16
action_13 (15) = happyGoto action_17
action_13 _ = happyFail (happyExpListPerState 13)

action_14 (17) = happyShift action_38
action_14 _ = happyFail (happyExpListPerState 14)

action_15 (23) = happyShift action_37
action_15 _ = happyFail (happyExpListPerState 15)

action_16 (16) = happyShift action_18
action_16 (28) = happyShift action_36
action_16 (29) = happyShift action_21
action_16 (15) = happyGoto action_35
action_16 _ = happyReduce_21

action_17 _ = happyReduce_22

action_18 _ = happyReduce_25

action_19 (16) = happyShift action_34
action_19 _ = happyFail (happyExpListPerState 19)

action_20 (16) = happyShift action_33
action_20 _ = happyFail (happyExpListPerState 20)

action_21 (16) = happyShift action_18
action_21 (20) = happyShift action_19
action_21 (28) = happyShift action_20
action_21 (29) = happyShift action_21
action_21 (13) = happyGoto action_32
action_21 (14) = happyGoto action_16
action_21 (15) = happyGoto action_17
action_21 _ = happyFail (happyExpListPerState 21)

action_22 (26) = happyShift action_31
action_22 _ = happyReduce_10

action_23 (24) = happyShift action_30
action_23 _ = happyReduce_13

action_24 _ = happyReduce_15

action_25 (16) = happyShift action_29
action_25 _ = happyFail (happyExpListPerState 25)

action_26 (16) = happyShift action_24
action_26 (19) = happyShift action_25
action_26 (29) = happyShift action_26
action_26 (11) = happyGoto action_27
action_26 (12) = happyGoto action_28
action_26 _ = happyFail (happyExpListPerState 26)

action_27 (30) = happyShift action_49
action_27 _ = happyFail (happyExpListPerState 27)

action_28 (24) = happyShift action_30
action_28 (30) = happyShift action_48
action_28 _ = happyFail (happyExpListPerState 28)

action_29 (22) = happyShift action_47
action_29 _ = happyFail (happyExpListPerState 29)

action_30 (16) = happyShift action_24
action_30 (29) = happyShift action_46
action_30 (12) = happyGoto action_45
action_30 _ = happyFail (happyExpListPerState 30)

action_31 (16) = happyShift action_11
action_31 (10) = happyGoto action_44
action_31 _ = happyReduce_9

action_32 (30) = happyShift action_43
action_32 _ = happyFail (happyExpListPerState 32)

action_33 (22) = happyShift action_42
action_33 _ = happyFail (happyExpListPerState 33)

action_34 (27) = happyShift action_41
action_34 _ = happyFail (happyExpListPerState 34)

action_35 _ = happyReduce_23

action_36 (16) = happyShift action_40
action_36 _ = happyFail (happyExpListPerState 36)

action_37 (16) = happyShift action_24
action_37 (19) = happyShift action_25
action_37 (29) = happyShift action_26
action_37 (11) = happyGoto action_39
action_37 (12) = happyGoto action_23
action_37 _ = happyFail (happyExpListPerState 37)

action_38 _ = happyReduce_6

action_39 _ = happyReduce_7

action_40 (22) = happyShift action_54
action_40 _ = happyFail (happyExpListPerState 40)

action_41 (16) = happyShift action_18
action_41 (20) = happyShift action_19
action_41 (28) = happyShift action_20
action_41 (29) = happyShift action_21
action_41 (13) = happyGoto action_53
action_41 (14) = happyGoto action_16
action_41 (15) = happyGoto action_17
action_41 _ = happyFail (happyExpListPerState 41)

action_42 (16) = happyShift action_18
action_42 (20) = happyShift action_19
action_42 (28) = happyShift action_20
action_42 (29) = happyShift action_21
action_42 (13) = happyGoto action_52
action_42 (14) = happyGoto action_16
action_42 (15) = happyGoto action_17
action_42 _ = happyFail (happyExpListPerState 42)

action_43 _ = happyReduce_24

action_44 _ = happyReduce_11

action_45 (24) = happyShift action_30
action_45 _ = happyReduce_17

action_46 (16) = happyShift action_24
action_46 (29) = happyShift action_46
action_46 (12) = happyGoto action_51
action_46 _ = happyFail (happyExpListPerState 46)

action_47 (16) = happyShift action_24
action_47 (19) = happyShift action_25
action_47 (29) = happyShift action_26
action_47 (11) = happyGoto action_50
action_47 (12) = happyGoto action_23
action_47 _ = happyFail (happyExpListPerState 47)

action_48 _ = happyReduce_16

action_49 _ = happyReduce_12

action_50 _ = happyReduce_14

action_51 (24) = happyShift action_30
action_51 (30) = happyShift action_48
action_51 _ = happyFail (happyExpListPerState 51)

action_52 _ = happyReduce_18

action_53 (21) = happyShift action_56
action_53 _ = happyFail (happyExpListPerState 53)

action_54 (16) = happyShift action_18
action_54 (20) = happyShift action_19
action_54 (28) = happyShift action_20
action_54 (29) = happyShift action_21
action_54 (13) = happyGoto action_55
action_54 (14) = happyGoto action_16
action_54 (15) = happyGoto action_17
action_54 _ = happyFail (happyExpListPerState 54)

action_55 _ = happyReduce_19

action_56 (16) = happyShift action_18
action_56 (20) = happyShift action_19
action_56 (28) = happyShift action_20
action_56 (29) = happyShift action_21
action_56 (13) = happyGoto action_57
action_56 (14) = happyGoto action_16
action_56 (15) = happyGoto action_17
action_56 _ = happyFail (happyExpListPerState 56)

action_57 _ = happyReduce_20

happyReduce_1 = happySpecReduce_1  4 happyReduction_1
happyReduction_1 (HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn4
		 (makeTree happy_var_1
	)
happyReduction_1 _  = notHappyAtAll 

happyReduce_2 = happySpecReduce_0  5 happyReduction_2
happyReduction_2  =  HappyAbsSyn5
		 ([]
	)

happyReduce_3 = happySpecReduce_2  5 happyReduction_3
happyReduction_3 (HappyAbsSyn5  happy_var_2)
	(HappyAbsSyn7  happy_var_1)
	 =  HappyAbsSyn5
		 (happy_var_1 : happy_var_2
	)
happyReduction_3 _ _  = notHappyAtAll 

happyReduce_4 = happySpecReduce_0  6 happyReduction_4
happyReduction_4  =  HappyAbsSyn6
		 (0
	)

happyReduce_5 = happySpecReduce_2  6 happyReduction_5
happyReduction_5 (HappyAbsSyn6  happy_var_2)
	_
	 =  HappyAbsSyn6
		 (1 + happy_var_2
	)
happyReduction_5 _ _  = notHappyAtAll 

happyReduce_6 = happyReduce 5 7 happyReduction_6
happyReduction_6 ((HappyTerminal (TokenRule happy_var_5)) `HappyStk`
	(HappyAbsSyn8  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn9  happy_var_2) `HappyStk`
	(HappyAbsSyn6  happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn7
		 ((happy_var_1, Statement happy_var_2 happy_var_4 (Rule happy_var_5))
	) `HappyStk` happyRest

happyReduce_7 = happySpecReduce_3  8 happyReduction_7
happyReduction_7 (HappyAbsSyn11  happy_var_3)
	_
	(HappyAbsSyn13  happy_var_1)
	 =  HappyAbsSyn8
		 (happy_var_1 ::: happy_var_3
	)
happyReduction_7 _ _ _  = notHappyAtAll 

happyReduce_8 = happySpecReduce_1  9 happyReduction_8
happyReduction_8 (HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn9
		 (Context happy_var_1
	)
happyReduction_8 _  = notHappyAtAll 

happyReduce_9 = happySpecReduce_0  10 happyReduction_9
happyReduction_9  =  HappyAbsSyn10
		 (M.empty
	)

happyReduce_10 = happySpecReduce_3  10 happyReduction_10
happyReduction_10 (HappyAbsSyn11  happy_var_3)
	_
	(HappyTerminal (TokenVar happy_var_1))
	 =  HappyAbsSyn10
		 (M.singleton (Var happy_var_1) happy_var_3
	)
happyReduction_10 _ _ _  = notHappyAtAll 

happyReduce_11 = happyReduce 5 10 happyReduction_11
happyReduction_11 ((HappyAbsSyn10  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn11  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenVar happy_var_1)) `HappyStk`
	happyRest)
	 = HappyAbsSyn10
		 (M.insert (Var happy_var_1) happy_var_3 happy_var_5
	) `HappyStk` happyRest

happyReduce_12 = happySpecReduce_3  11 happyReduction_12
happyReduction_12 _
	(HappyAbsSyn11  happy_var_2)
	_
	 =  HappyAbsSyn11
		 (happy_var_2
	)
happyReduction_12 _ _ _  = notHappyAtAll 

happyReduce_13 = happySpecReduce_1  11 happyReduction_13
happyReduction_13 (HappyAbsSyn12  happy_var_1)
	 =  HappyAbsSyn11
		 (TypeMonoType happy_var_1
	)
happyReduction_13 _  = notHappyAtAll 

happyReduce_14 = happyReduce 4 11 happyReduction_14
happyReduction_14 ((HappyAbsSyn11  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn11
		 (TypeForall (TypeVar happy_var_2) happy_var_4
	) `HappyStk` happyRest

happyReduce_15 = happySpecReduce_1  12 happyReduction_15
happyReduction_15 (HappyTerminal (TokenVar happy_var_1))
	 =  HappyAbsSyn12
		 (MonoTypeVar $ TypeVar happy_var_1
	)
happyReduction_15 _  = notHappyAtAll 

happyReduce_16 = happySpecReduce_3  12 happyReduction_16
happyReduction_16 _
	(HappyAbsSyn12  happy_var_2)
	_
	 =  HappyAbsSyn12
		 (happy_var_2
	)
happyReduction_16 _ _ _  = notHappyAtAll 

happyReduce_17 = happySpecReduce_3  12 happyReduction_17
happyReduction_17 (HappyAbsSyn12  happy_var_3)
	_
	(HappyAbsSyn12  happy_var_1)
	 =  HappyAbsSyn12
		 (happy_var_1 :->: happy_var_3
	)
happyReduction_17 _ _ _  = notHappyAtAll 

happyReduce_18 = happyReduce 4 13 happyReduction_18
happyReduction_18 ((HappyAbsSyn13  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn13
		 (Var happy_var_2 :\: happy_var_4
	) `HappyStk` happyRest

happyReduce_19 = happyReduce 5 13 happyReduction_19
happyReduction_19 ((HappyAbsSyn13  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenVar happy_var_3)) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn14  happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn13
		 (happy_var_1 :@: Var happy_var_3 :\: happy_var_5
	) `HappyStk` happyRest

happyReduce_20 = happyReduce 6 13 happyReduction_20
happyReduction_20 ((HappyAbsSyn13  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn13  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn13
		 (ExpressionLetIn (Var happy_var_2) happy_var_4 happy_var_6
	) `HappyStk` happyRest

happyReduce_21 = happySpecReduce_1  13 happyReduction_21
happyReduction_21 (HappyAbsSyn14  happy_var_1)
	 =  HappyAbsSyn13
		 (happy_var_1
	)
happyReduction_21 _  = notHappyAtAll 

happyReduce_22 = happySpecReduce_1  14 happyReduction_22
happyReduction_22 (HappyAbsSyn15  happy_var_1)
	 =  HappyAbsSyn14
		 (happy_var_1
	)
happyReduction_22 _  = notHappyAtAll 

happyReduce_23 = happySpecReduce_2  14 happyReduction_23
happyReduction_23 (HappyAbsSyn15  happy_var_2)
	(HappyAbsSyn14  happy_var_1)
	 =  HappyAbsSyn14
		 (happy_var_1 :@: happy_var_2
	)
happyReduction_23 _ _  = notHappyAtAll 

happyReduce_24 = happySpecReduce_3  15 happyReduction_24
happyReduction_24 _
	(HappyAbsSyn13  happy_var_2)
	_
	 =  HappyAbsSyn15
		 (happy_var_2
	)
happyReduction_24 _ _ _  = notHappyAtAll 

happyReduce_25 = happySpecReduce_1  15 happyReduction_25
happyReduction_25 (HappyTerminal (TokenVar happy_var_1))
	 =  HappyAbsSyn15
		 (ExpressionVar $ Var happy_var_1
	)
happyReduction_25 _  = notHappyAtAll 

happyNewToken action sts stk [] =
	action 31 31 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	TokenVar happy_dollar_dollar -> cont 16;
	TokenRule happy_dollar_dollar -> cont 17;
	TokenIndent -> cont 18;
	TokenForall -> cont 19;
	TokenLet -> cont 20;
	TokenIn -> cont 21;
	TokenDot -> cont 22;
	TokenColon -> cont 23;
	TokenArrow -> cont 24;
	TokenVdash -> cont 25;
	TokenComma -> cont 26;
	TokenAssign -> cont 27;
	TokenLambda -> cont 28;
	TokenLParen -> cont 29;
	TokenRParen -> cont 30;
	_ -> happyError' ((tk:tks), [])
	}

happyError_ explist 31 tk tks = happyError' (tks, explist)
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
