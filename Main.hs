-- https://arxiv.org/pdf/2406.14719

{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}

module Main where

import Data.List (intercalate, (\\), nub)
import Data.Maybe (listToMaybe, fromMaybe, catMaybes)
import Control.Monad (guard, msum)
import qualified Data.Map as M
import qualified Data.Set as S

data Formula = Atom String
             | Not Formula
             | And Formula Formula
             | Or Formula Formula
             | Implies Formula Formula
             | Bottom
             | Top
             deriving (Eq, Ord)

instance Show Formula where
  show (Atom s) = s
  show (Not f) = "~" ++ showParens f
  show (And f g) = showParens f ++ " & " ++ showParens g
  show (Or f g) = showParens f ++ " | " ++ showParens g
  show (Implies f g) = showParens f ++ " -> " ++ showParens g
  show Bottom = "False"
  show Top = "True"

showParens :: Formula -> String
showParens f@(Atom _) = show f
showParens f@Bottom = show f
showParens f@Top = show f
showParens f = "(" ++ show f ++ ")"

data Polarity = Positive | Negative deriving (Eq, Show)

polarity :: Formula -> Polarity
polarity (Atom _) = Positive 
polarity (Not f) = case polarity f of
  Positive -> Negative
  Negative -> Positive
polarity (And _ _) = Positive 
polarity (Or _ _) = Negative   --
polarity (Implies _ _) = Negative  --
polarity Top = Positive
polarity Bottom = Negative

isAsync :: Formula -> Bool
isAsync (And _ _) = True
isAsync (Not (Or _ _)) = True
isAsync _ = False

isSync :: Formula -> Bool
isSync f = not (isAsync f)

data Sequent = Sequent [Formula] [Formula]

instance Show Sequent where
  show (Sequent gamma delta) = 
    showFormulas gamma ++ " |- " ++ showFormulas delta
    where
      showFormulas [] = "·"
      showFormulas fs = intercalate ", " (map show fs)

data FocusedSequent = FocusedLeft [Formula] Formula [Formula]   --
                    | FocusedRight [Formula] Formula [Formula]  --
                    | Unfocused [Formula] [Formula]             --

instance Show FocusedSequent where
  show (FocusedLeft gamma f delta) =
    showFs gamma ++ " | [" ++ show f ++ "] |- " ++ showFs delta
    where
      showFs [] = "·"
      showFs fs = intercalate ", " (map show fs)
  show (FocusedRight gamma f delta) =
    showFs gamma ++ " |- [" ++ show f ++ "] | " ++ showFs delta
    where
      showFs [] = "·"
      showFs fs = intercalate ", " (map show fs)
  show (Unfocused gamma delta) =
    showFs gamma ++ " |- " ++ showFs delta
    where 
      showFs [] = "·"
      showFs fs = intercalate ", " (map show fs)

data ProofTree = Axiom Sequent
               | LeftNot Sequent Formula ProofTree
               | RightNot Sequent Formula ProofTree
               | LeftAnd Sequent Formula Formula ProofTree
               | RightAnd Sequent Formula Formula ProofTree ProofTree
               | LeftOr Sequent Formula Formula ProofTree ProofTree
               | RightOr Sequent Formula Formula ProofTree
               | LeftImplies Sequent Formula Formula ProofTree ProofTree
               | RightImplies Sequent Formula Formula ProofTree
               | LeftBottom Sequent
               | RightTop Sequent
               | Cut Sequent Formula ProofTree ProofTree
               | Weakening Sequent ProofTree
               | Contraction Sequent ProofTree
               | Exchange Sequent ProofTree

instance Show ProofTree where
  show = showProofTree

data FocusedProof = FAxiom FocusedSequent
                  | FocusLeft FocusedSequent Formula FocusedProof
                  | FocusRight FocusedSequent Formula FocusedProof
                  | Release FocusedSequent FocusedProof
                  | LeftSync FocusedSequent Formula FocusedProof
                  | RightSync FocusedSequent Formula FocusedProof
                  | LeftAsync FocusedSequent Formula FocusedProof
                  | RightAsync FocusedSequent Formula FocusedProof

normalToFocused :: Sequent -> [FocusedSequent]
normalToFocused (Sequent gamma delta) =
  [ FocusedRight gamma f (delta \\ [f]) | f <- delta, polarity f == Positive ] ++
  [ FocusedLeft (gamma \\ [f]) f delta | f <- gamma, polarity f == Negative ] ++
  [ Unfocused gamma delta ]

focusedToNormal :: FocusedSequent -> Sequent
focusedToNormal (FocusedLeft gamma f delta) = Sequent (f : gamma) delta
focusedToNormal (FocusedRight gamma f delta) = Sequent gamma (f : delta)
focusedToNormal (Unfocused gamma delta) = Sequent gamma delta

canRelease :: FocusedSequent -> Bool
canRelease (FocusedLeft _ f _) = case f of
  Atom _ -> True
  Bottom -> True
  _ -> False
canRelease (FocusedRight _ f _) = case f of
  Atom _ -> True
  Top -> True
  _ -> False
canRelease (Unfocused _ _) = True

isAxiom :: Sequent -> Bool
isAxiom (Sequent gamma delta) = 
  any (\f -> f `elem` delta) gamma ||
  Bottom `elem` gamma ||
  Top `elem` delta

proveSequent :: Int -> Sequent -> Maybe ProofTree
proveSequent depth seq@(Sequent gamma delta)
  | depth <= 0 = Nothing
  | isAxiom seq = Just (Axiom seq)
  | otherwise = tryRules
  where
    tryRules = case concat [tryRightRules, tryLeftRules] of
      (x:_) -> x
      [] -> Nothing
    
    tryRightRules = concat
      [ [ do guard (Not f `elem` delta)
             let newSeq = Sequent (f : gamma) (delta \\ [Not f])
             proof <- proveSequent (depth - 1) newSeq
             return $ RightNot seq f proof
        | Not f <- delta ]
        
      , [ do guard (And f g `elem` delta)
             let newSeq1 = Sequent gamma (f : (delta \\ [And f g]))
             let newSeq2 = Sequent gamma (g : (delta \\ [And f g]))
             proof1 <- proveSequent (depth - 1) newSeq1
             proof2 <- proveSequent (depth - 1) newSeq2
             return $ RightAnd seq f g proof1 proof2
        | And f g <- delta ]
        
      , [ do guard (Or f g `elem` delta)
             let newSeq = Sequent gamma (f : g : (delta \\ [Or f g]))
             proof <- proveSequent (depth - 1) newSeq
             return $ RightOr seq f g proof
        | Or f g <- delta ]
        
      , [ do guard (Implies f g `elem` delta)
             let newSeq = Sequent (f : gamma) (g : (delta \\ [Implies f g]))
             proof <- proveSequent (depth - 1) newSeq
             return $ RightImplies seq f g proof
        | Implies f g <- delta ]
        
      , if Top `elem` delta then [Just $ RightTop seq] else []
      ]
    
    tryLeftRules = concat
      [ [ do guard (Not f `elem` gamma)
             let newSeq = Sequent (gamma \\ [Not f]) (f : delta)
             proof <- proveSequent (depth - 1) newSeq
             return $ LeftNot seq f proof
        | Not f <- gamma ]
        
      , [ do guard (And f g `elem` gamma)
             let newSeq = Sequent (f : g : (gamma \\ [And f g])) delta
             proof <- proveSequent (depth - 1) newSeq
             return $ LeftAnd seq f g proof
        | And f g <- gamma ]
        
      , [ do guard (Or f g `elem` gamma)
             let newSeq1 = Sequent (f : (gamma \\ [Or f g])) delta
             let newSeq2 = Sequent (g : (gamma \\ [Or f g])) delta
             proof1 <- proveSequent (depth - 1) newSeq1
             proof2 <- proveSequent (depth - 1) newSeq2
             return $ LeftOr seq f g proof1 proof2
        | Or f g <- gamma ]
        
      , [ do guard (Implies f g `elem` gamma)
             let newSeq1 = Sequent (gamma \\ [Implies f g]) (f : delta)
             let newSeq2 = Sequent (g : (gamma \\ [Implies f g])) delta
             proof1 <- proveSequent (depth - 1) newSeq1
             proof2 <- proveSequent (depth - 1) newSeq2
             return $ LeftImplies seq f g proof1 proof2
        | Implies f g <- gamma ]
        
      , if Bottom `elem` gamma then [Just $ LeftBottom seq] else []
      ]

isFocusedAxiom :: FocusedSequent -> Bool
isFocusedAxiom (FocusedLeft gamma (Atom a) delta) = Atom a `elem` delta
isFocusedAxiom (FocusedRight gamma (Atom a) delta) = Atom a `elem` gamma
isFocusedAxiom (FocusedLeft _ Bottom _) = True
isFocusedAxiom (FocusedRight _ Top _) = True
isFocusedAxiom (Unfocused gamma delta) = 
  any (\f -> f `elem` delta) gamma || Bottom `elem` gamma || Top `elem` delta
isFocusedAxiom _ = False

proveFocused :: Int -> FocusedSequent -> Maybe FocusedProof
proveFocused depth fseq
  | depth <= 0 = Nothing
  | isFocusedAxiom fseq = Just (FAxiom fseq)
  | otherwise = case fseq of
      FocusedLeft gamma f delta -> case f of
        Not g -> do
          let newSeq = FocusedRight gamma g delta
          proof <- proveFocused (depth - 1) newSeq
          return $ LeftSync fseq f proof
          
        Or g h -> do
          let newSeq = Unfocused (g : h : gamma) delta
          proof <- proveFocused (depth - 1) newSeq
          return $ LeftAsync fseq f proof
          
        _ -> Nothing
      
      FocusedRight gamma f delta -> case f of
        Not g -> do
          let newSeq = FocusedLeft (g : gamma) g delta
          proof <- proveFocused (depth - 1) newSeq
          return $ RightSync fseq f proof
          
        And g h -> do
          let newSeq = Unfocused gamma (g : h : delta)
          proof <- proveFocused (depth - 1) newSeq
          return $ RightAsync fseq f proof
          
        _ -> Nothing
      
      Unfocused gamma delta -> do
        let candidates = normalToFocused (Sequent gamma delta)
        msum [ proveFocused (depth - 1) cand | cand <- candidates ]

applyCut :: Formula -> ProofTree -> ProofTree -> Maybe ProofTree
applyCut cutFormula left right = do
  let Sequent gammaL deltaL = getConclusion left
  let Sequent gammaR deltaR = getConclusion right
  guard (cutFormula `elem` deltaL)
  guard (cutFormula `elem` gammaR)
  let newSeq = Sequent (nub $ gammaL ++ (gammaR \\ [cutFormula])) 
                       (nub $ (deltaL \\ [cutFormula]) ++ deltaR)
  return $ Cut newSeq cutFormula left right
  where
    getConclusion (Axiom s) = s
    getConclusion (LeftNot s _ _) = s
    getConclusion (RightNot s _ _) = s
    getConclusion (LeftAnd s _ _ _) = s
    getConclusion (RightAnd s _ _ _ _) = s
    getConclusion (LeftOr s _ _ _ _) = s
    getConclusion (RightOr s _ _ _) = s
    getConclusion (LeftImplies s _ _ _ _) = s
    getConclusion (RightImplies s _ _ _) = s
    getConclusion (LeftBottom s) = s
    getConclusion (RightTop s) = s
    getConclusion (Cut s _ _ _) = s
    getConclusion (Weakening s _) = s
    getConclusion (Contraction s _) = s
    getConclusion (Exchange s _) = s

-- ASCII-friendly showProofTree for Windows
showProofTree :: ProofTree -> String
showProofTree = unlines . reverse . go 0
  where
    go :: Int -> ProofTree -> [String]
    go indent tree = case tree of
      Axiom s -> 
        [spaces indent ++ "------ (Axiom)", spaces indent ++ show s]
      
      LeftNot s f sub ->
        let subLines = go (indent + 2) sub
            rule = spaces indent ++ "------ (Not-L)"
            concl = spaces indent ++ show s
        in concl : rule : subLines
      
      RightNot s f sub ->
        let subLines = go (indent + 2) sub
            rule = spaces indent ++ "------ (Not-R)"
            concl = spaces indent ++ show s
        in concl : rule : subLines
      
      LeftAnd s f g sub ->
        let subLines = go (indent + 2) sub
            rule = spaces indent ++ "------ (And-L)"
            concl = spaces indent ++ show s
        in concl : rule : subLines
      
      RightAnd s f g sub1 sub2 ->
        let subLines1 = go (indent + 2) sub1
            subLines2 = go (indent + 2) sub2
            rule = spaces indent ++ "------ (And-R)"
            concl = spaces indent ++ show s
        in concl : rule : (subLines1 ++ [""] ++ subLines2)
      
      LeftOr s f g sub1 sub2 ->
        let subLines1 = go (indent + 2) sub1
            subLines2 = go (indent + 2) sub2
            rule = spaces indent ++ "------ (Or-L)"
            concl = spaces indent ++ show s
        in concl : rule : (subLines1 ++ [""] ++ subLines2)
      
      RightOr s f g sub ->
        let subLines = go (indent + 2) sub
            rule = spaces indent ++ "------ (Or-R)"
            concl = spaces indent ++ show s
        in concl : rule : subLines
      
      LeftImplies s f g sub1 sub2 ->
        let subLines1 = go (indent + 2) sub1
            subLines2 = go (indent + 2) sub2
            rule = spaces indent ++ "------ (Implies-L)"
            concl = spaces indent ++ show s
        in concl : rule : (subLines1 ++ [""] ++ subLines2)
      
      RightImplies s f g sub ->
        let subLines = go (indent + 2) sub
            rule = spaces indent ++ "------ (Implies-R)"
            concl = spaces indent ++ show s
        in concl : rule : subLines
      
      LeftBottom s ->
        [spaces indent ++ "------ (Bottom-L)", spaces indent ++ show s]
      
      RightTop s ->
        [spaces indent ++ "------ (Top-R)", spaces indent ++ show s]
      
      Cut s f sub1 sub2 ->
        let subLines1 = go (indent + 2) sub1
            subLines2 = go (indent + 2) sub2
            rule = spaces indent ++ "------ (Cut: " ++ show f ++ ")"
            concl = spaces indent ++ show s
        in concl : rule : (subLines1 ++ [""] ++ subLines2)
      
      Weakening s sub ->
        let subLines = go (indent + 2) sub
            rule = spaces indent ++ "------ (Weak)"
            concl = spaces indent ++ show s
        in concl : rule : subLines
      
      Contraction s sub ->
        let subLines = go (indent + 2) sub
            rule = spaces indent ++ "------ (Contr)"
            concl = spaces indent ++ show s
        in concl : rule : subLines
      
      Exchange s sub ->
        let subLines = go (indent + 2) sub
            rule = spaces indent ++ "------ (Exch)"
            concl = spaces indent ++ show s
        in concl : rule : subLines
    
    spaces n = replicate n ' '

(/\) :: Formula -> Formula -> Formula
(/\) = And

(\/) :: Formula -> Formula -> Formula
(\/) = Or

(==>) :: Formula -> Formula -> Formula
(==>) = Implies

neg :: Formula -> Formula
neg = Not

atom :: String -> Formula
atom = Atom

proveTheorem :: Int -> Formula -> Maybe ProofTree
proveTheorem depth f = proveSequent depth (Sequent [] [f])

prove :: Formula -> IO ()
prove f = case proveTheorem 20 f of
  Just proof -> putStrLn $ show proof
  Nothing -> putStrLn "X No proof found"

provable :: Formula -> Bool
provable f = case proveTheorem 20 f of
  Just _ -> True
  Nothing -> False

proveSeq :: [Formula] -> [Formula] -> IO ()
proveSeq gamma delta = case proveSequent 20 (Sequent gamma delta) of
  Just proof -> putStrLn $ show proof
  Nothing -> putStrLn "X No proof found"

examples :: [(String, Formula)]
examples =
  [ ("Identity", atom "A" ==> atom "A")
  , ("Law of Excluded Middle", atom "P" \/ neg (atom "P"))
  , ("Double Negation", neg (neg (atom "P")) ==> atom "P")
  , ("Modus Ponens", (atom "P" /\ (atom "P" ==> atom "Q")) ==> atom "Q")
  , ("Commutativity of And", (atom "A" /\ atom "B") ==> (atom "B" /\ atom "A"))
  , ("Distribution", (atom "A" /\ (atom "B" \/ atom "C")) ==> 
                     ((atom "A" /\ atom "B") \/ (atom "A" /\ atom "C")))
  ]

main :: IO ()
main = do
  putStrLn $ replicate 60 '='
  putStrLn ""
  putStrLn $ replicate 60 '='
  putStrLn "PROVING CLASSIC THEOREMS"
  putStrLn $ replicate 60 '=' ++ "\n"
  
  mapM_ testExample examples
  where
    testExample (name, formula) = do
      putStrLn $ "Theorem: " ++ name
      putStrLn $ "Formula: " ++ show formula
      case proveTheorem 15 formula of
        Nothing -> putStrLn "X Could not find proof\n"
        Just proof -> do
          putStrLn "V Proof found!\n"
          putStrLn $ showProofTree proof
          putStrLn ""
