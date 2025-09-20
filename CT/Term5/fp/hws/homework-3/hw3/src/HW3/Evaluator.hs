{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns        #-}

module HW3.Evaluator
  ( eval ) where

import Control.Monad (foldM)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Except (runExceptT, throwE)
import Data.Bool (bool)
import qualified Data.ByteString as BS
import Data.List (foldl')
import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import Data.Semigroup (stimes)
import Data.Sequence (Seq (Empty, (:<|)))
import qualified Data.Sequence as S
import qualified Data.Text as T
import qualified Data.Text.Encoding as ENC
import qualified Data.Time as UTC
import Data.Tuple (swap)
import HW3.Base
import HW3.Evaluator.Base
import HW3.Evaluator.FunctionHelpers
import HW3.Evaluator.Helpers
import HW3.Helpers
import Text.Read (readMaybe)

-- | Evaluates `HiExpr` in `HiMonad` istance, returnes `Left err` if
-- invalid function or arguments met, any runtime error happened
eval :: HiMonad m => HiExpr -> m (Either HiError HiValue)
eval = runExceptT . eval'

-- | Evaluated `HiExpr` in `HiExcept` Monad for producing and handling
-- errors. Either just returns value, evaluate top function call or run
-- action in `HiMonad`
eval' :: HiMonad m => HiExpr -> HiExcept m HiValue
eval' (HiExprValue val)      = pure val
eval' (HiExprApply fun args) = evalApply fun args
eval' (HiExprRun expr)       = eval' expr >>=
  \case
    (HiValueAction act) -> lift $ runAction act
    _                   -> throwE HiErrorInvalidArgument
eval' (HiExprDict dictExpr)      = HiValueDict . M.fromList <$> mapM evalPair dictExpr
  where
    evalPair :: HiMonad m => (HiExpr, HiExpr) -> HiExcept m (HiValue, HiValue)
    evalPair (k, v) = do
      kV <- eval' k
      vV <- eval' v
      pure (kV, vV)

-- | Evaluates function call overloaded for strings, lists, bytes and
-- dictionaries.
evalApply :: HiMonad m => HiExpr -> [HiExpr] -> HiExcept m HiValue
evalApply funExpr argsExpr = eval' funExpr >>=
  \case
    HiValueFunction fun -> evalFunctionLazy fun argsExpr
    v ->
      do
      args <- mapM eval' argsExpr
      case v of
        HiValueString s  -> evalStringSlice s args
        HiValueList l    -> evalListSlice l args
        HiValueBytes bs  -> evalBytesSlice bs args
        HiValueDict dict -> evalDictLookup dict args
        _                -> throwE HiErrorInvalidFunction
  where
    evalStringSlice :: Monad m => T.Text -> [HiValue] -> HiExcept m HiValue
    evalStringSlice = evalSlice T.length (\ s n -> T.singleton $ T.index s n) HiValueString HiValueString T.take T.drop

    evalListSlice :: Monad m => Seq HiValue -> [HiValue] -> HiExcept m HiValue
    evalListSlice = evalSlice S.length S.index id HiValueList S.take S.drop

    evalBytesSlice :: Monad m => BS.ByteString -> [HiValue] -> HiExcept m HiValue
    evalBytesSlice = evalSlice BS.length BS.index (HiValueNumber . toRational) HiValueBytes BS.take BS.drop

    evalDictLookup :: Monad m => M.Map HiValue HiValue -> [HiValue] -> HiExcept m HiValue
    evalDictLookup m [k] =
      case M.lookup k m of
        Just v  -> pure v
        Nothing -> pure HiValueNull
    evalDictLookup _ _ = throwE HiErrorArityMismatch

-- | Evaluates `if`, `or`(`||`), `and`(`&&`) lazy. Other functions are
-- forces to evaluate its arguments first.
evalFunctionLazy :: HiMonad m => HiFun -> [HiExpr] -> HiExcept m HiValue
evalFunctionLazy HiFunIf =
  \case
    [bExpr, ifTrue, ifFalse] -> eval' bExpr >>=
        \case
          HiValueBool b -> eval' $ bool ifFalse ifTrue b
          _             -> throwE HiErrorInvalidArgument
    _ -> throwE HiErrorArityMismatch
evalFunctionLazy HiFunAnd = evalLazyBool $
  \x yExpr ->
    case x of
      HiValueNull       -> pure x
      HiValueBool False -> pure x
      _                 -> eval' yExpr
evalFunctionLazy HiFunOr = evalLazyBool $
  \x yExpr ->
    case x of
      HiValueNull       -> eval' yExpr
      HiValueBool False -> eval' yExpr
      _                 -> pure x
evalFunctionLazy f = withEval $ evalFunc $ mkFunction f
  where
    withEval :: HiMonad m => ([HiValue] -> HiExcept m HiValue) -> ([HiExpr] -> HiExcept m HiValue)
    withEval f' args = mapM eval' args >>= f'

-- | Helper for lazy evaluates `and` and `or`
evalLazyBool :: HiMonad m => (HiValue -> HiExpr -> HiExcept m HiValue) -> [HiExpr] -> HiExcept m HiValue
evalLazyBool f =
  \case
    [xExpr, yExpr] -> eval' xExpr >>= \x -> f x yExpr
    _              -> throwE HiErrorArityMismatch

-- | Converts `HiFun` enum to `Function` object, which than safely evaluates
mkFunction :: HiMonad m => HiFun -> Function m
mkFunction HiFunDiv = mkOverloadedFunction
  [ mkBinaryFunctionRat $
    \x y -> bool (throwE HiErrorDivideByZero) (pure $ x / y) $ y /= 0
  , mkBinaryFunctionStringNoExcept $
    \x y -> x <> "/" <> y
  ]
mkFunction HiFunMul =
  let replFuns =
        [ mkFuncReplicate exString HiValueString
        , mkFuncReplicate exList HiValueList
        , mkFuncReplicate exBytes HiValueBytes
        ]
  in
    mkOverloadedFunction $ [ mkBinaryFunctionRatNoExcept (*) ] ++
    replFuns ++
    map flipBinaryFunction replFuns
  where
    mkFuncReplicate :: (Semigroup a, Monad m) => (HiValue -> Maybe a) -> (a -> HiValue) -> Function m
    mkFuncReplicate ex1 ctr = binaryFunctionNoExcept ex1 exPosInteger ctr (flip stimes)
mkFunction HiFunAdd = mkOverloadedFunction
  [ mkBinaryFunctionRatNoExcept (+)
  , mkFuncConcat exString HiValueString
  , mkFuncConcat exList HiValueList
  , mkFuncConcat exBytes HiValueBytes
  , addTimeFunc
  , flipBinaryFunction addTimeFunc
  ]
  where
    mkFuncConcat :: (Monad m, Semigroup a) => (HiValue -> Maybe a) -> (a -> HiValue) -> Function m
    mkFuncConcat ex ctr = binaryFunctionNoExcept ex ex ctr (<>)

    addTimeFunc :: Monad m => Function m
    addTimeFunc = binaryFunctionNoExcept
      exTime exInteger HiValueTime $ \t diff -> UTC.addUTCTime (fromIntegral diff) t
mkFunction HiFunSub = mkOverloadedFunction
  [ mkBinaryFunctionRatNoExcept (-)
  , binaryFunctionNoExcept exTime exTime HiValueNumber $
    \begin end ->
      toRational $ UTC.nominalDiffTimeToSeconds $ UTC.diffUTCTime begin end
  ]
mkFunction HiFunNot = mkUnaryFunctionBool not
mkFunction HiFunAnd = unreachable -- handled in `evalFunctionLazy`
mkFunction HiFunOr  = unreachable -- handled in `evalFunctionLazy`
mkFunction HiFunLessThan = mkLessThanFunction id id
mkFunction HiFunGreaterThan = mkLessThanFunction swap id
mkFunction HiFunEquals = mkEqualsFunction id
mkFunction HiFunNotLessThan = mkLessThanFunction id not
mkFunction HiFunNotGreaterThan = mkLessThanFunction swap not
mkFunction HiFunNotEquals = mkEqualsFunction not
mkFunction HiFunIf = unreachable -- handled in `evalFunctionLazy`
mkFunction HiFunLength = mkOverloadedFunction
  [ mkLengthFunc exString T.length
  , mkLengthFunc exList S.length
  , mkLengthFunc exBytes BS.length ]
  where
    mkLengthFunc :: Monad m => (HiValue -> Maybe a) -> (a -> Int) -> Function m
    mkLengthFunc exc f = unaryFunctionNoExcept exc HiValueNumber (toRational . f)
mkFunction HiFunToUpper = mkUnaryFunctionStringNoExcept T.toUpper
mkFunction HiFunToLower = mkUnaryFunctionStringNoExcept T.toLower
mkFunction HiFunReverse = mkOverloadedFunction
  [ mkUnaryFunctionStringNoExcept T.reverse
  , mkUnaryFunctionListNoExcept S.reverse
  , mkUnaryFunctionBytesNoExcept BS.reverse ]
mkFunction HiFunTrim = mkUnaryFunctionStringNoExcept  T.strip
mkFunction HiFunList = rawFunction $ pure . HiValueList . S.fromList
mkFunction HiFunRange = binaryFunctionNoExcept exNumber exNumber HiValueList $
  \begin end -> HiValueNumber <$> S.fromList [begin..end]
mkFunction HiFunFold = binaryFunction exAny exList id $
  \f l ->
    case l of
      Empty -> pure HiValueNull
      x :<| Empty -> pure x
      x :<| xs ->
        foldM (\acc e -> eval' $ HiExprApply (HiExprValue f) $ map HiExprValue [acc, e]) x xs
mkFunction HiFunPackBytes = unaryFunction exList HiValueBytes $
  \l -> do
      bytes <- mapM
        (\case
            HiValueNumber (ratToByte -> Just n) -> pure $ BS.singleton $ fromIntegral n
            _                                   -> throwE HiErrorInvalidArgument) l
      pure $ foldl' (<>) BS.empty bytes
mkFunction HiFunUnpackBytes = mkUnaryFunctionBytesNoExcept' HiValueList $
  S.fromList . map (HiValueNumber . fromIntegral) . BS.unpack
mkFunction HiFunEncodeUtf8 = mkUnaryFunctionStringNoExcept' HiValueBytes ENC.encodeUtf8
mkFunction HiFunDecodeUtf8 = mkUnaryFunctionBytesNoExcept' id $
  \bs -> case ENC.decodeUtf8' bs of
           Left _  -> HiValueNull
           Right s -> HiValueString s
mkFunction HiFunZip = mkUnaryFunctionBytesNoExcept strictCompress
mkFunction HiFunUnzip = mkUnaryFunctionBytesNoExcept strictDecompress
mkFunction HiFunSerialise = unaryFunctionNoExcept exAny HiValueBytes strictSerialise
mkFunction HiFunDeserialise  = mkUnaryFunctionBytesNoExcept' id (fromMaybe HiValueNull . strictDeserialise)
mkFunction HiFunRead = mkValueAction HiActionRead
mkFunction HiFunWrite = mkOverloadedFunction
  [ binaryFunctionNoExcept exString exString HiValueAction $
    \f s -> HiActionWrite (T.unpack f) (ENC.encodeUtf8 s)
  , binaryFunctionNoExcept exString exBytes HiValueAction $
    \f bs -> HiActionWrite (T.unpack f) bs
  ]
mkFunction HiFunMkDir = mkValueAction HiActionMkDir
mkFunction HiFunChDir = mkValueAction HiActionChDir
mkFunction HiFunParseTime = mkUnaryFunctionStringNoExcept' id $
  maybe HiValueNull HiValueTime . readMaybe . T.unpack
mkFunction HiFunRand = binaryFunctionNoExcept exInt exInt HiValueAction HiActionRand
mkFunction HiFunEcho = mkUnaryFunctionStringNoExcept' HiValueAction HiActionEcho
mkFunction HiFunKeys = mkDictListFunction fst
mkFunction HiFunValues = mkDictListFunction snd
mkFunction HiFunCount = mkOverloadedFunction
  [ mkDictCountFunction T.foldl' (HiValueString . T.singleton) exString
  , mkDictCountFunction BS.foldl' (HiValueNumber . toRational) exBytes
  , mkDictCountFunction foldl' id exList
  ]
mkFunction HiFunInvert = unaryFunctionNoExcept exDict HiValueDict $
  M.map (HiValueList . S.fromList) . M.foldlWithKey' update' M.empty
  where
    update' :: M.Map HiValue [HiValue] -> HiValue -> HiValue -> M.Map HiValue [HiValue]
    update' dict v k  =
      case M.lookup k dict of
        Just l  -> M.insert k (v:l) dict
        Nothing -> M.insert k [v] dict

-- | Count elements in container and store results in dictionary
mkDictCountFunction :: forall a c m. Monad m
  => ((M.Map HiValue Integer -> a -> M.Map HiValue Integer)
       -> M.Map HiValue Integer -> c -> M.Map HiValue Integer) -- ^ Appopriate fold function
  -> (a -> HiValue) -- ^ Constructor of `HiValue` from native type
  -> (HiValue -> Maybe c) -- ^ Tries extract native type from `HiValue`
  -> Function m
mkDictCountFunction fold' elemToValue ex = unaryFunctionNoExcept ex HiValueDict $
  M.map (HiValueNumber . toRational) . count'
  where
    update' :: M.Map HiValue Integer -> a -> M.Map HiValue Integer
    update' d e =
      let v = elemToValue e
       in case M.lookup v d of
            Just n  -> M.insert v (n + 1) d
            Nothing -> M.insert v 1 d

    count' :: c -> M.Map HiValue Integer
    count' = fold' update' M.empty

-- | Helpers that makes function to extract keys or values from dictionary
mkDictListFunction :: Monad m => ((HiValue, HiValue) -> HiValue) -> Function m
mkDictListFunction f = unaryFunctionNoExcept exDict HiValueList $
  S.fromList . map f . M.toList

-- | Helpers that makes `HiValueAction` with single string argument
mkValueAction :: Monad m => (String -> HiAction) -> Function m
mkValueAction fun = mkUnaryFunctionStringNoExcept' HiValueAction $ fun . T.unpack

-- | Helpers that makes quality function modifing result of comparison
mkEqualsFunction :: Monad m => (Bool -> Bool) -> Function m
mkEqualsFunction modRes = binaryFunctionNoExcept exAny exAny (HiValueBool . modRes) (==)

-- | Helpers that makes comparison function, modifing result and
-- optionaly swaping arguments.
mkLessThanFunction :: Monad m
  => ((HiValue, HiValue) -> (HiValue, HiValue))
  -> (Bool -> Bool)
  -> Function m
mkLessThanFunction modArgs modRes =
  binaryFunctionNoExcept exAny exAny (HiValueBool . modRes) (curry $ uncurry (<) . modArgs)
