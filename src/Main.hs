module Main where

import Grammar
import Lexer (alexScanTokens)
import Parser

import Data.List as List
import Data.Set as Set
import Data.Map as Map
import Data.Maybe
import Control.Monad (mapM_)

-- B
checkHyp :: [Expr] -> Expr -> Annotation
checkHyp context expr = let hyps = Map.fromList(zip context [1..])
                          in case Map.findWithDefault 0 expr hyps of
                            0 -> Incorrect
                            i -> Hypothesis i

checkAx :: Expr -> Annotation
checkAx (Binary Impl a (Binary Impl b a2))                                                                    | a == a2                                   = Axiom 1
checkAx (Binary Impl (Binary Impl a b) (Binary Impl (Binary Impl a2 (Binary Impl b2 c)) (Binary Impl a3 c2))) | a == a2 && a2 == a3 && b == b2 && c == c2 = Axiom 2
checkAx (Binary Impl a (Binary Impl b (Binary And a2 b2)))                                                    | a == a2 && b == b2                        = Axiom 3
checkAx (Binary Impl (Binary And a b) a2)                                                                     | a == a2                                   = Axiom 4
checkAx (Binary Impl (Binary And a b) b2)                                                                     | b == b2                                   = Axiom 5
checkAx (Binary Impl a (Binary Or a2 b))                                                                      | a == a2                                   = Axiom 6
checkAx (Binary Impl b (Binary Or a b2))                                                                      | b == b2                                   = Axiom 7
checkAx (Binary Impl (Binary Impl a c) (Binary Impl (Binary Impl b c2) (Binary Impl (Binary Or a2 b2) c3)))   | a == a2 && b == b2 && c == c2 && c2 == c3 = Axiom 8
checkAx (Binary Impl (Binary Impl a b) (Binary Impl (Binary Impl a2 (Not b2)) (Not a3)))                      | a == a2 && a2 == a3 && b == b2            = Axiom 9
checkAx (Binary Impl (Not (Not a)) a2)                                                                        | a == a2                                   = Axiom 10
checkAx _ = Incorrect

checkMP :: [Expr] -> Expr -> (Map [Expr] (Map Expr (Map Expr Int))) -> (Map [Expr] (Map Expr Int)) -> Annotation
checkMP context expr right left = let
      sameContext = Map.findWithDefault Map.empty context right
      sameRight   = Map.findWithDefault Map.empty expr sameContext
      sameLeft    = Map.findWithDefault Map.empty context left
            in case Map.intersection sameRight sameLeft of
            common | not (Map.null common) -> let key = head $ keys common
                        in ModusPonens (sameLeft ! key) (sameRight ! key)
            _ -> Incorrect

deductor :: [Expr] -> Expr -> Line
deductor context (Binary Impl a b) = deductor (a:context) b
deductor context expr = Line context expr

checkDed :: [Expr] -> Expr -> Map [Expr] (Map Expr Int) -> Annotation 
checkDed context expr deduction = let
      sameContext = Map.findWithDefault Map.empty context deduction
            in case Map.findWithDefault 0 expr sameContext of
                  0 -> Incorrect
                  i -> Deduction i

addImpl :: [Expr] -> Expr -> Expr -> Int
        -> Map [Expr] (Map Expr (Map Expr Int))
        -> Map [Expr] (Map Expr (Map Expr Int))
addImpl c a b n m = case Map.lookup c m of
    (Nothing) -> Map.insert c (Map.singleton b (Map.singleton a n)) m
    (Just m2) -> case Map.lookup b m2 of
        (Nothing) -> Map.insert c (Map.insert b (Map.singleton a n) m2) m
        (Just m3) -> case Map.lookup a m3 of
            (Nothing) -> Map.insert c (Map.insert b (Map.insert a n m3) m2) m
            _         -> m

addLine :: [Expr] -> Expr -> Int
        -> Map [Expr] (Map Expr Int)
        -> Map [Expr] (Map Expr Int)
addLine c e n m = case Map.lookup c m of
    (Nothing) -> Map.insert c (Map.singleton e n) m
    (Just m2) -> case Map.lookup e m2 of
        (Nothing) -> Map.insert c (Map.insert e n m2) m
        _         -> m

-- C
annotate :: [Line] -> Int -> (Map [Expr] (Map Expr (Map Expr Int)))
         -> (Map [Expr] (Map Expr Int)) -> (Map [Expr] (Map Expr Int))
         -> (Map Int Proof)
annotate [] _ _ _ _ = Map.empty
annotate (x:xs) ind right left deduction = do
  let
    (Line context expr) = x
    sorted = (sort . reverse) context
    (Line rawDed dedExpr) = deductor context expr
    dedCont = (sort . reverse) rawDed
    
    res = case checkHyp sorted expr of
        (Incorrect) -> case checkAx expr of
            (Incorrect) -> case checkMP sorted expr right left of
                (Incorrect) -> checkDed dedCont dedExpr deduction
                mp -> mp
            ax -> ax
        hyp -> hyp


        in case res of
            (Incorrect) -> annotate xs ind right left deduction
            _ -> let
                right2 = case expr of
                    (Binary Impl a b) -> addImpl sorted a b ind right
                    _ -> right
                left2 = addLine sorted expr ind left
                deduction2 = addLine dedCont dedExpr ind deduction
                    in Map.insert ind (Proof (Line sorted expr) res) (annotate xs (ind+1) right2 left2 deduction2)

goDedInside :: (Map Int Proof) -> Int -> Int
goDedInside proof ind = case proof ! ind of
    (Proof _ (Deduction next)) -> goDedInside proof next
    _ -> ind

simplify :: (Map Int Proof) -> Int -> (Map Int Proof)
simplify proof ind = case proof ! ind of
    (Proof line (Deduction ded)) -> let next = goDedInside proof ded
                                        in Map.insert ind (Proof line (Deduction next)) (simplify proof next)
    line@(Proof _ (ModusPonens first second)) -> Map.insert ind line (Map.union (simplify proof first) (simplify proof second))
    line@(Proof _ Incorrect) -> error "wrong proof"
    line -> Map.singleton ind line

smartDeductor :: Expr -> Expr -> Expr -> [Expr] -> [Expr] -> ([Expr], [Expr])
smartDeductor orig ded expr rem ins | ded == expr = (rem, ins)
smartDeductor orig ded (Binary Impl left right) rem ins = smartDeductor orig ded right rem (left:ins)
smartDeductor orig (Binary Impl left right) expr rem ins = smartDeductor orig right orig (left:rem) []

deductLeft :: [Expr] -> Expr -> [Proof] -> [Proof]
deductLeft [] _ res = res
deductLeft [x] (Binary Impl a b) res | x == a = deductLeft [] b ((Proof (Line [] b) (MP a)):(Proof (Line [] a) (Hypothesis 0)):res)
deductLeft (x:xs) (Binary Impl a b) res | x == a = deductLeft xs b ((Proof (Line [] b) (MP a)):(Proof (Line [] a) (Hypothesis 0)):res)
deductLeft s e r = error ((show s) ++ "\n" ++ (show e) ++ "\n" ++ (show r))

moveRight :: Expr -> [Proof] -> [Proof] -> [Proof]
moveRight e [] res = res
moveRight e ((Proof (Line _ x) _):xs) res | e == x = ((Proof (Line [] (Binary Impl x x)) (MP (Binary Impl x (Binary Impl (Binary Impl x x) x))))
                                                        :(Proof (Line [] (Binary Impl x (Binary Impl (Binary Impl x x) x))) (Axiom 1))
                                                        :(Proof (Line [] (Binary Impl (Binary Impl x (Binary Impl (Binary Impl x x) x)) (Binary Impl x x))) (MP (Binary Impl x (Binary Impl x x))))
                                                        :(Proof (Line [] (Binary Impl x (Binary Impl x x))) (Axiom 1))
                                                        :(Proof (Line [] (Binary Impl (Binary Impl x (Binary Impl x x)) (Binary Impl (Binary Impl x (Binary Impl (Binary Impl x x) x)) (Binary Impl x x)))) (Axiom 2))
                                                        :(moveRight e xs res))
moveRight e ((Proof (Line _ x) (Hypothesis _)):xs) res = ((Proof (Line [] (Binary Impl e x)) (MP x))
                                                            :(Proof (Line [] x) (Hypothesis 0))
                                                            :(Proof (Line [] (Binary Impl x (Binary Impl e x))) (Axiom 1))
                                                            :(moveRight e xs res))
moveRight e ((Proof (Line _ x) (Axiom _)):xs) res = ((Proof (Line [] (Binary Impl e x)) (MP x))
                                                        :(Proof (Line [] x) (Axiom 0))
                                                        :(Proof (Line [] (Binary Impl x (Binary Impl e x))) (Axiom 1))
                                                        :(moveRight e xs res))
moveRight e ((Proof (Line _ x) (MP a)):xs) res = ((Proof (Line [] (Binary Impl e x)) (MP (Binary Impl e (Binary Impl a x))))
                                                    :(Proof (Line [] (Binary Impl (Binary Impl e (Binary Impl a x)) (Binary Impl e x))) (MP (Binary Impl e a)))
                                                    :(Proof (Line [] (Binary Impl (Binary Impl e a) (Binary Impl (Binary Impl e (Binary Impl a x)) (Binary Impl e x)))) (Axiom 2))
                                                    :(moveRight e xs res))

deductRight :: [Expr] -> [Proof] -> [Proof]
deductRight [] res = res
deductRight (x:xs) proof = deductRight xs (moveRight x proof [])

convert :: (Map Int Proof) -> Int -> [Proof]
convert metaproof ind = case metaproof ! ind of
    line@(Proof _ (Hypothesis _)) -> [line]
    line@(Proof _ (Axiom _)) -> [line]
    (Proof line (ModusPonens first second)) -> let (Proof (Line _ a) _) = metaproof ! first
                                                in ((Proof line (MP a)):((convert metaproof first) ++ (convert metaproof second)))
    line@(Proof (Line _ expr) (Deduction next)) -> do
        let
            (Proof (Line _ ded) _) = (metaproof ! next)
            (rem, ins) = smartDeductor expr ded expr [] []
            left = deductLeft (reverse rem) ded (convert metaproof next)
                in deductRight ins left

toLine :: String -> Line
toLine str = let (Line context expr) = parseLine (alexScanTokens str)
                in (Line (List.sort context) expr)

toExpr :: Proof -> Expr
toExpr (Proof (Line _ e) _) = e

printProof :: [Expr] -> IO()
printProof proof = mapM_ (putStrLn . show) proof

main :: IO ()
main = do
    input <- getContents
    putStrLn (last (lines input))
    let raw = List.map toLine (lines input)
    let annotated = annotate raw 1 Map.empty Map.empty Map.empty
    let metaproof = simplify annotated (fst (Map.findMax annotated))
    let proof = convert metaproof (fst (Map.findMax metaproof))
    let small = (List.nub . reverse) (List.map toExpr proof)
    printProof small