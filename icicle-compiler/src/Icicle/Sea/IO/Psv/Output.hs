{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
module Icicle.Sea.IO.Psv.Output where

import qualified Data.List as List
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Text as T

import           Icicle.Avalanche.Prim.Flat (Prim(..), PrimUnsafe(..))
import           Icicle.Avalanche.Prim.Flat (meltType)

import           Icicle.Common.Base (OutputName(..))
import           Icicle.Common.Type (ValType(..), StructType(..), StructField(..))

import           Icicle.Data (Attribute(..))

import           Icicle.Internal.Pretty

import           Icicle.Sea.Error (SeaError(..))
import           Icicle.Sea.FromAvalanche.Base (seaOfAttributeDesc)
import           Icicle.Sea.FromAvalanche.Base (seaOfNameIx, seaOfChar)
import           Icicle.Sea.FromAvalanche.Prim
import           Icicle.Sea.FromAvalanche.State

import           Icicle.Sea.IO.Psv.Base

import           P
import           Prelude (String)


data PsvOutputConfig = PsvOutputConfig {
    outputPsvMode      :: PsvMode
  , outputPsvFormat    :: PsvOutputFormat
  , outputPsvMissing   :: Text
  } deriving (Eq, Ord, Show)

data PsvOutputFormat
  = PsvOutputSparse
  | PsvOutputDense
  deriving (Eq, Ord, Show)

type PsvOutputWhiteList = Maybe [Text]

data PsvMissing
  = PsvMissing Text
  | PsvDrop

defaultOutputMissing :: Text
defaultOutputMissing = "NA"

------------------------------------------------------------------------

seaOfWriteFleetOutput :: PsvOutputConfig -> PsvOutputWhiteList -> [SeaProgramState] -> Either SeaError Doc
seaOfWriteFleetOutput config whitelist states = do
  let states' = case whitelist of
                  Nothing -> states
                  Just as -> filter (flip List.elem as . getAttribute . stateAttribute) states
  write_sea  <- traverse (seaOfWriteProgramOutput config) states'
  let (beforeChord, inChord, afterChord)
         = case outputPsvFormat config of
             PsvOutputDense
              -> (outputEntity, outputChord, outputChar '\n')
             PsvOutputSparse
              -> ("", "", "")

  pure $ vsep
    [ "#line 1 \"write all outputs\""
    , "static ierror_msg_t psv_write_outputs"
    , "    ( int fd"
    , "    , char  *buffer"
    , "    , char  *buffer_end"
    , "    , char **buffer_ptr_ptr"
    , "    , const char *entity"
    , "    , size_t entity_size"
    , "    , ifleet_t *fleet )"
    , "{"
    , "    iint_t         chord_count = fleet->chord_count;"
    , "    const itime_t *chord_times = fleet->chord_times;"
    , "    ierror_msg_t   error;"
    , ""
    , "    char *buffer_ptr = *buffer_ptr_ptr;"
    , ""
    , "    for (iint_t chord_ix = 0; chord_ix < chord_count; chord_ix++) {"
    , indent 8 beforeChord
    , indent 8 (seaOfChordTime $ outputPsvMode config)
    , indent 8 (vsep write_sea)
    , indent 8 inChord
    , indent 8 afterChord
    , "    }"
    , ""
    , "    *buffer_ptr_ptr = buffer_ptr;"
    , ""
    , "    return 0;"
    , "}"
    ]

seaOfChordTime :: PsvMode -> Doc
seaOfChordTime = \case
  PsvSnapshot _ -> vsep
    [ "const char  *chord_time = \"\";"
    , "const size_t chord_size = 0;"
    ]
  PsvChords     -> vsep
    [ "iint_t c_year, c_month, c_day, c_hour, c_minute, c_second;"
    , "itime_to_gregorian (chord_times[chord_ix], &c_year, &c_month, &c_day, &c_hour, &c_minute, &c_second);"
    , ""
    , "const size_t chord_size = sizeof (\"|yyyy-mm-ddThh:mm:ssZ\") - 1;"
    , "char chord_time[chord_size + 1];"
    , "snprintf (chord_time, chord_size + 1, \"|" <> timeFmt <> "Z\", "
             <> "c_year, c_month, c_day, c_hour, c_minute, c_second);"
    ]

outputChord :: Doc
outputChord
  = outputValue "string" ["chord_time", "chord_size"]


seaOfWriteProgramOutput :: PsvOutputConfig -> SeaProgramState -> Either SeaError Doc
seaOfWriteProgramOutput config state = do
  let ps    = "p" <> int (stateName state)
      stype = pretty (nameOfStateType state)
      pname = pretty (nameOfProgram state)
      tb    = outputPsvMissing config

  let outputState (name, (ty, tys))
        = case outputPsvFormat config of
            PsvOutputSparse
              -> seaOfWriteOutputSparse ps 0 name ty tys
            PsvOutputDense
              -> seaOfWriteOutputDense  ps 0 name ty tys tb

  let outputRes   name
        = ps <> "->" <> pretty (hasPrefix <> name) <+> "= ifalse;"

  let resumeables  = fmap (outputRes . fst) (stateResumables state)
  outputs         <- traverse outputState (stateOutputs state)

  pure $ vsep
    [ ""
    , "/* " <> seaOfAttributeDesc (stateAttribute state) <> " */"
    , stype <+> "*" <> ps <+> "=" <+> "&fleet->" <> pname <> "[chord_ix];"
    , pname <+> "(" <> ps <> ");"
    , ps <> "->input.new_count = 0;"
    , vsep resumeables
    , ""
    , vsep outputs
    ]

seaOfWriteOutputSparse :: Doc -> Int -> OutputName -> ValType -> [ValType] -> Either SeaError Doc
seaOfWriteOutputSparse struct structIndex outName@(OutputName name _) outType argTypes
  = let members = structMembers struct name argTypes structIndex
    in case outType of
         -- Top-level Sum is a special case, to avoid allocating and printing if
         -- the whole computation is an error (e.g. tombstone)
         SumT ErrorT outType'
          | (ErrorT : argTypes') <- argTypes
          , (ne     : _)         <- members
          -> do (m, f, body, _, _)
                   <- seaOfOutput NotInJSON struct (structIndex + 1) outName PsvDrop Map.empty outType' argTypes' id
                let body'        = seaOfOutputCond m f body
                let body''       = go body'
                pure $ conditionalNotError' ne body''
         _
          -> do (m, f, body, _, _)
                   <- seaOfOutput NotInJSON struct structIndex outName PsvDrop Map.empty outType argTypes id
                let body'        = seaOfOutputCond m f body
                return $ go body'

  where
    go str = vsep [ outputEntity
                  , outputChar '|'
                  , outputAttr name
                  , outputChar '|'
                  , str
                  , outputChord
                  , outputChar '\n'
                  ]

seaOfWriteOutputDense :: Doc -> Int -> OutputName -> ValType -> [ValType] -> Text -> Either SeaError Doc
seaOfWriteOutputDense struct structIndex outName outType argTypes missing
  = do (m, f, body, _, _)
          <- seaOfOutput NotInJSON struct structIndex outName (PsvMissing missing) Map.empty outType argTypes id
       let body' = seaOfOutputCond m f body
       pure $ vsep [ outputChar '|', body' ]

-- | Construct the struct member names for the output arguments.
--
structMembers :: Doc -> Text -> [ValType] -> Int -> [Doc]
structMembers struct name argTypes structIndex
  = List.take (length argTypes)
  $ fmap (\ix -> struct <> "->" <> seaOfNameIx name ix)
         [structIndex..]

-- | Output the entity, e.g "homer|"
--
outputEntity :: Doc
outputEntity
  = outputValue  "string" ["entity", "entity_size"]

-- | Output the attribute, e.g "salary|"
--
outputAttr :: Text -> Doc
outputAttr = outputString


--------------------------------------------------------------------------------

-- | A mapping of C name prefixes in use to the number of times they are used.
--   e.g. if @x_0@ and @x_1@ have been used, the environment must contain @(x, 2)@
--
type NameEnv = Map String Int

newName :: Doc -> NameEnv -> (Doc, NameEnv)
newName doc env
  = let n = show doc
    in  case Map.lookup n env of
          Nothing
            -> (pretty (0 :: Int), Map.insert n 1 env)
          Just i
            -> (pretty i, Map.insert n (i + 1) env)

seaOfOutput
  :: IsInJSON                      -- ^ Indicates whether to quote strings
  -> Doc                           -- ^ Struct of values to output
  -> Int                           -- ^ Current index into the struct of values
  -> OutputName                    -- ^ Use the output name as seed for generated C names
  -> PsvMissing                    -- ^ Drop missing values or output something
  -> NameEnv                       -- ^ C names in use
  -> ValType                       -- ^ Output type
  -> [ValType]                     -- ^ Types of arguments
  -> (Doc -> Doc)                  -- ^ Transformation to be applied to this struct member, e.g. index
  -> Either SeaError ( Maybe Doc   -- Output the value when this is true
                     , Maybe Doc   -- Otherwise output this
                     , Doc         -- The output statement, x
                     , Int         -- Where it's up to
                     , [ValType] ) -- Unconsumed arguments
seaOfOutput isJSON struct structIndex outName@(OutputName name _) missing env outType argTypes transform
 = let prefixi         = pretty name <> "_" <> pretty structIndex <> "_i"
       (suffixi, env'')= newName prefixi env
       counter         = prefixi <> suffixi

       prefixn         = pretty name <> "_" <> pretty structIndex <> "_n"
       (suffixn, env') = newName prefixn env''
       countLimit      = prefixn <> suffixn

       arrayIndex t x  = seaOfArrayIndex x counter t

   in case outType of
       ArrayT te
        | tes@(arg0:_) <- meltType te
        , (arr  : _)   <- members
        -> do (mcond, mfalse, body, ix, ts1)
                 <- seaOfOutput InJSON struct structIndex outName PsvDrop env' te tes (arrayIndex arg0 . transform)

              -- End the body with a comma, if applicable
              let body' = seaOfOutputCond mcond (withSep' counter mfalse) (withSep counter body)

              -- Array of arrays is allowed, so we apply the transform here
              let arr'  = transform arr

              -- Wrap the body in a for loop
              let numElems  = arrayCount arr'
              body''       <- seaOfOutputArray body' numElems counter countLimit

              return (Nothing, Nothing, body'', ix, ts1)


       MapT tk tv
        | tks@(argk0 : _) <- meltType tk
        , tvs@(argv0 : _) <- meltType tv
        , (arr : _)       <- members
        -> do (mcondk, mfalsek, bk, ixk, _)
                 <- seaOfOutput InJSON struct structIndex outName PsvDrop env' tk tks (arrayIndex argk0 . transform)
              (mcondv, mfalsev, bv, ixv, ts)
                 <- seaOfOutput InJSON struct ixk outName PsvDrop env' tv tvs (arrayIndex argv0 . transform)

              let p  = pair bk bv
              let p' = seaOfOutputCond mcondk (withSep' counter mfalsek)
                     $ seaOfOutputCond mcondv (withSep' counter mfalsev)
                     $ withSep counter p

              let numElems  = arrayCount arr
              body         <- seaOfOutputArray p' numElems counter countLimit
              return (Nothing, Nothing, body, ixv, ts)


       PairT ta tb
        | tas <- meltType ta
        , tbs <- meltType tb
        -> do (mcondk, mfalsek, ba, ixa, _)
                 <- seaOfOutput InJSON struct structIndex outName PsvDrop env' ta tas transform
              (mcondv, mfalsev, bb, ixb, ts)
                 <- seaOfOutput InJSON struct ixa outName PsvDrop env' tb tbs transform

              let p  = pair ba bb
              let p' = seaOfOutputCond mcondk mfalsek
                     $ seaOfOutputCond mcondv mfalsev
                     $ p

              return (Nothing, Nothing, p', ixb, ts)


       StructT fs
        | fields <- Map.toList (getStructType fs)
        -> do let go (ix, ts, docs) (n, t) = do
                    (cond, _, body, ix', ts') <- seaOfOutput InJSON struct ix outName PsvDrop env' t ts transform

                    let doc = vsep
                            [ outputChar '\"'
                            , outputString (nameOfStructField n)
                            , outputChar '\"'
                            , outputChar ':'
                            , body
                            ]
                    pure (ix', ts', (cond, doc) : docs)

              (ix, ts, docs) <- foldM go (structIndex, argTypes, mempty) fields
              let doc         = vsep $ [ outputChar '{' , seaOfOutputStructSep docs , outputChar '}' ]
              return (Nothing, Nothing, doc, ix, ts)


       -- Conditional's
       OptionT otype1
        | (BoolT : ts1) <- argTypes
        , (nb    : _)   <- members
        -> do (mcond, mfalse, body, ix, ts)
                 <- seaOfOutput isJSON struct (structIndex + 1) outName missing env' otype1 ts1 transform

              let body' = seaOfOutputCond mcond mfalse body
              let nb'   = transform nb
              pure ( Just nb', outputMissing, body', ix, ts )

       SumT ErrorT otype1
        | (ErrorT : ts1) <- argTypes
        , (ne     : _)   <- members
        -> do (mcond, mfalse, body, ix, ts)
                 <- seaOfOutput isJSON struct (structIndex + 1) outName missing env' otype1 ts1 transform

              let body' = seaOfOutputCond mcond mfalse body
              let ne'   = transform ne
              pure ( Just (ne' <> " == ierror_not_an_error"), outputMissing, body', ix, ts )

       -- Base
       _
        | (t  : ts) <- argTypes
        , (mx : _)  <- members
        , mx'       <- transform mx
        -> do d <- seaOfOutputBase' isJSON t mx'
              pure (Nothing, Nothing, d, structIndex + 1, ts)

       _ -> Left unsupported

  where
   mismatch    = SeaOutputTypeMismatch    outName outType argTypes
   unsupported = SeaUnsupportedOutputType outType

   members    = List.take (length argTypes)
              $ fmap (\ix -> struct <> "->" <> seaOfNameIx name ix) [structIndex..]

   arrayCount x
     = "(" <> x <> ")" <> "->count"

   withSep' counter mbody
     = fmap (vsep . ([seaOfOutputArraySep counter] <>) . pure) mbody

   withSep counter body
     = vsep [seaOfOutputArraySep counter, body ]

   outputMissing
     = case missing of
         PsvDrop
           -> Nothing
         PsvMissing s
           -> Just (outputString s)

   seaOfOutputBase' b
     = seaOfOutputBase b mismatch

   seaOfOutputArraySep c
     = conditional' (c <+> "> 0") (outputChar ',')

   withStructSep body assign
     = vsep
     [ conditional' "need_sep" (outputChar ',')
     , body
     , assign ]

   seaOfOutputStructSep fs
     = let go (Just cond, body)
             = conditional' cond
                (withStructSep body  ("need_sep = " <> cond <> ";"))
           go (Nothing, body)
             = withStructSep body "need_sep = itrue;"
       in  vsep ("ibool_t need_sep = ifalse;" : fmap go fs)

--------------------------------------------------------------------------------

seaOfArrayIndex :: Doc -> Doc -> ValType -> Doc
seaOfArrayIndex arr ix typ
 = seaOfPrimDocApps (seaOfXPrim (PrimUnsafe (PrimUnsafeArrayIndex typ)))
                    [ arr, ix ]

-- | Output an array with pre-defined bodies
seaOfOutputArray :: Applicative f => Doc -> Doc -> Doc -> Doc -> f Doc
seaOfOutputArray body numElems counter countLimit
 = pure (vsep [ outputChar '['
              , forStmt counter countLimit numElems
              , "{"
              , indent 4 body
              , "}"
              , outputChar ']'
              ]
        )

-- | Output an if statement
seaOfOutputCond :: Maybe Doc -> Maybe Doc -> Doc -> Doc
seaOfOutputCond mcond if_false if_true
  = case mcond of
      Nothing
        -> if_true
      Just cond
        -> case if_false of
             Nothing
               -> conditional' cond if_true
             Just x
               -> conditional cond if_true x

-- | Output single types
seaOfOutputBase :: IsInJSON -> SeaError -> ValType -> Doc -> Either SeaError Doc
seaOfOutputBase quoteStrings err t val
 = case t of
     BoolT
      -> pure
       $ vsep
           [ "if (" <> val <> ") {"
           , indent 4 $ outputString "true"
           , "} else {"
           , indent 4 $ outputString "false"
           , "}"
           ]
     IntT
      -> pure $ outputValue "int" [val]
     DoubleT
      -> pure $ outputValue "double" [val]
     StringT
      -> pure $ quotedOutput quoteStrings (outputValue "string" [val, "strlen(" <> val <> ")"])
     TimeT
      -> pure $ quotedOutput quoteStrings (outputValue "time" [val])
     FactIdentifierT
      -> pure $ outputValue "int" [val]

     _ -> Left err

------------------------------------------------------------------------

-- | A hack to tell whether or not strings should be quoted.
--   If in JSON, quote. If not, don't.
--   At any stage during output, if the elements should be JSON, pass @InJSON@,
--   e.g. when outputting arrays, we should specify that the elements be output
--        as JSON.
--
data IsInJSON = InJSON | NotInJSON

conditional' :: Doc -> Doc -> Doc
conditional' n body
 = vsep ["if (" <> n <> ")"
        , "{"
        , indent 4 body
        , "}"]

conditional :: Doc -> Doc -> Doc -> Doc
conditional n body1 body2
 = vsep ["if (" <> n <> ")"
        , "{"
        , indent 4 body1
        , "} else {"
        , indent 4 body2
        , "}"]

conditionalNotError' :: Doc -> Doc -> Doc
conditionalNotError' n body
 = conditional' (n <> " == ierror_not_an_error") body

conditionalNotError :: Doc -> Doc -> Doc -> Doc
conditionalNotError n body1 body2
 = conditional (n <> " == ierror_not_an_error") body1 body2

pair :: Doc -> Doc -> Doc
pair x y
 = vsep [ outputChar '['
        , x
        , outputChar ','
        , y
        , outputChar ']'
        ]

outputValue :: Doc -> [Doc] -> Doc
outputValue typ vals
 = vsep
 [ "error = psv_output_" <> typ <> " "
   <> "(fd, buffer, buffer_end, &buffer_ptr, " <> val <> ");"
 , outputDie
 ]
 where
  val = hcat (punctuate ", " vals)

forStmt :: Doc -> Doc -> Doc -> Doc
forStmt i n m
 = "for(iint_t" <+> i <+> "= 0," <+> n <+> "=" <+> m <> ";" <+> i <+> "<" <+> n <> "; ++" <> i <> ")"

outputChar :: Char -> Doc
outputChar x
 = outputValue "char" [seaOfChar x]

outputString :: Text -> Doc
outputString xs
 = vsep
 [ "if (buffer_end - buffer_ptr < " <> int rounded <> ") {"
 , "    error = psv_output_flush (fd, buffer, &buffer_ptr);"
 , indent 4 outputDie
 , "}"
 , vsep (fmap mkdoc swords)
 , "buffer_ptr += " <> int size <> ";"
 ]
 where
  swords = wordsOfString xs

  rounded  = length swords * 8
  size     = sum (fmap swSize swords)
  mkdoc sw = "*(uint64_t *)(buffer_ptr + " <> int (swOffset sw) <> ") = " <> swBits sw <> ";"

timeFmt :: Doc
timeFmt = "%04lld-%02lld-%02lldT%02lld:%02lld:%02lld"

outputDie :: Doc
outputDie = "if (error) return error;"

quotedOutput :: IsInJSON -> Doc -> Doc
quotedOutput NotInJSON out = out
quotedOutput InJSON    out = vsep [outputChar '"', out, outputChar '"']
