-- Copyright 2015 Google Inc. All Rights Reserved.
--
-- Licensed under the Apache License, Version 2.0 (the "License")--
-- you may not use this file except in compliance with the License.
-- You may obtain a copy of the License at
--
--     http://www.apache.org/licenses/LICENSE-2.0
--
-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-- See the License for the specific language governing permissions and
-- limitations under the License.

{-# LANGUAGE OverloadedStrings #-}

module Algo (mergeTrs) where

import Debug.Trace
import Data.List ( intercalate, tails, inits )
import Data.Traversable
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Datatypes
import Signature
import Control.Monad.Writer.Strict (Writer, runWriter, tell)
import Terms
import Maranget
import Data.List

isBottom :: Term -> Bool
isBottom Bottom = True
isBottom _ = False

-- interleave abc ABC = Abc, aBc, abC
interleave :: [a] -> [a] -> [[a]]
interleave [] [] = []
interleave xs ys = zipWith3 glue (inits xs) ys (tails (tail xs))
  where glue xs x ys = xs ++ x : ys

complement :: Signature -> Term -> Term -> Term
complement sig p1 p2 = p1 \\ p2
  where
    appl f ps | any isBottom ps = Bottom
              | otherwise = Appl f ps

    plus Bottom u = u
    plus t Bottom = t
    plus t u = Plus t u

    sum = foldr plus Bottom

    alias x Bottom = Bottom
    alias x t = Alias x t

    a \\ b | trace (show a ++ "\\" ++ show b) False = undefined
    u \\ (Var _) = Bottom
    u \\ Bottom = u
    (Var x) \\ p@(Appl g ps) = alias x (sum [pattern f \\ p | f <- fs])
      where fs = ctorsOfSameRange sig g
            pattern f = Appl f (replicate (arity sig f) (Var "_"))
    
    Bottom \\ Appl _ _ = Bottom
    Appl f ps \\ Appl g qs
        | f /= g || someUnchanged = appl f ps
        | otherwise = sum [appl f ps' | ps' <- interleave ps pqs]
      where pqs = zipWith (\\) ps qs
            someUnchanged = or (zipWith (==) ps pqs)
    Plus q1 q2 \\ p@(Appl _ _) = plus (q1 \\ p) (q2 \\ p)
    Alias x p1 \\ p2 = alias x (p1 \\ p2)
    p1 \\ Alias x p2 = p1 \\ p2
    p \\ (Plus p1 p2) = (p \\ p1) \\ p2


preMinimize :: [Term] -> [Term]
preMinimize patterns = filter (not . isMatched) patterns
  where isMatched p = any (matches' p) patterns
        matches' p q = not (matches p q) && matches q p

minimize :: Signature -> [Term] -> [Term]
minimize sig ps = minimize' ps []
  where minimize' [] kernel = kernel
        minimize' (p:ps) kernel =
           if subsumes sig (ps++kernel) p
              then shortest (minimize' ps (p:kernel)) (minimize' ps kernel)
              else minimize' ps (p:kernel)

        shortest xs ys = if length xs <= length ys then xs else ys

removePlusses :: Term -> S.Set Term
removePlusses (Plus p1 p2) = removePlusses p1 `S.union` removePlusses p2
removePlusses (Appl f ps) = S.map (Appl f) (traverseSet removePlusses ps)
  where traverseSet f s = S.fromList (traverse (S.toList . f) s)
removePlusses (Alias x p) = S.map (Alias x) (removePlusses p)
removePlusses (Var x) = S.singleton (Var x)
removePlusses Bottom = S.empty



removeAliases :: Rule -> Rule
removeAliases (Rule lhs rhs) = Rule lhs' (substitute subst rhs)
  where (lhs', subst) = collectAliases (renameUnderscores lhs)

        collectAliases t = runWriter (collect t)

        collect :: Term -> Writer Substitution Term
        collect (Appl f ts) = Appl f <$> (mapM collect ts)
        collect (Var x) = return (Var x)
        collect (Alias x t) = do
          t' <- collect t
          tell (M.singleton x t')
          return t'

expandAnti :: Signature -> Term -> Term
expandAnti sig t = expandAnti' t
  where expandAnti' (Appl f ts) = Appl f (map expandAnti' ts)
        expandAnti' (Plus t1 t2) = Plus (expandAnti' t1) (expandAnti' t2)
        expandAnti' (Compl t1 t2) = complement sig (expandAnti' t1) (expandAnti' t2)
        expandAnti' (Anti t) = complement sig (Var "_") (expandAnti' t)
        expandAnti' (Var x) = Var x
        expandAnti' Bottom = Bottom

antiTrsToOtrs :: Signature -> [Rule] -> [Rule]
antiTrsToOtrs sig rules = [Rule (expandAnti sig lhs) rhs | Rule lhs rhs <- rules]

otrsToAdditiveTrs :: Signature -> [Rule] -> [Rule]
otrsToAdditiveTrs sig rules = zipWith diff rules (inits patterns)
  where patterns = [lhs | Rule lhs _ <- rules]
        diff (Rule lhs rhs) lhss = Rule (complement sig lhs (sum lhss)) rhs
        sum = foldr Plus Bottom

aliasedTrsToTrs :: [Rule] -> [Rule]
aliasedTrsToTrs = map removeAliases

additiveTrsToAliasedTrs :: Signature -> [Rule] -> [Rule]
additiveTrsToAliasedTrs sig rules = concatMap transform rules
  where transform (Rule lhs rhs) = map (flip Rule rhs) (expand lhs)
        expand = minimize sig . preMinimize . S.toList . removePlusses

fusionTrs :: Signature -> [Rule] -> [Rule]
fusionTrs sig rules = concat (map fusionTrs' rulesbyType)
  where
    rulesbyType = map sameReturn (rmdups (map rig rules))
      where
        sameReturn t =  map fst(filter snd(zip rules(map sameReturn' rules)))
          where 
            sameReturn' (Rule _ rh ) = t == rh
        rig (Rule lh rh) = rh
    fusionTrs' rules = map fst((filter snd (zip rules (map rulewithVar rules)))) ++ [last res] 
      where
        res = (scanl fusion' (head rules) (tail rules))
          where 
            fusion' (Rule lhs1 rhs1) (Rule lhs2 rhs2)  =  if (rhs1 == rhs2)
                                                          then Rule (fusionleft lhs1 lhs2) rhs2
                                                          else (Rule lhs1 rhs1)
              where 
                fusionleft (Appl f ts1) (Appl g ts2) = Appl f (map fusionleft' (zip ts1 ts2))
                  where
                    fusionleft' (Var x , Appl ff tts) = Appl ff tts
                    fusionleft' (Appl ff tts, Var x) = Appl ff tts
                    fusionleft' (Var y, Var x) = Var x
                    fusionleft' (Appl f1 ts11 , Appl g2 ts22) = if (and(ts11 == [],ts22 == []))
                                                                then 
                                                                  if (f1 /= g2)
                                                                  then Plus (Appl f1 ts11) (Appl g2 ts22)
                                                                  else (Appl f1 ts11)
                                                                else Appl f1 (map fusionleft' (zip ts11 ts22))
                    fusionleft' (Plus (Appl p1 ps1) p2 , Appl p3 ts22) = if (p1 /= p3 )
                                                              then 
                                                                if (p2 /= Appl p3 ts22 )
                                                                then Plus (Plus (Appl p1 ps1) p2) (Appl p3 ts22)
                                                                else Plus (Appl p1 ps1) p2
                                                              else Plus (Appl p1 ps1) p2 
                    fusionleft' (Plus (Plus p3 p4) p5 , Appl p6 ts66) = if (p5 == Appl p6 ts66)
                                                                        then fusionleft' ((Plus p3 p4),Appl p6 ts66)
                                                                        else Plus (fusionleft' ((Plus p3 p4),Appl p6 ts66))  p5

mergePlusses :: Signature -> [Rule] -> [Rule]
mergePlusses a b | trace ("fusionleft' : " ++  "  " ++ show b) False = undefined
mergePlusses sig rules = rmdups(map merge rules)
  where 
    merge (Rule lhs rhs) = Rule (merge' lhs) rhs
      where
        merge' (Appl f ts) = Appl f (map mergePlus ts)
          where 
            mergePlus (Appl ff tts) = Appl ff (map mergePlus tts)
            mergePlus (Plus (Appl p1 t1) (Appl p2 t2)) =  if (t1 == [])
                                                          then
                                                            if (t2 == [])
                                                            then 
                                                              if (listsEqual ( [p1] ++ [p2])  (ctorsOfSameRange sig p2))
                                                              then Var "y"
                                                              else Plus (Appl p1 t1) (Appl p2 t2)
                                                            else Plus (Appl p1 t1) (Appl p2 (map mergePlus t2))
                                                          else Plus (Appl p1 (map mergePlus t1)) (Appl p2 t2)
            mergePlus (Plus (Plus p1 p2) (Appl p3 t3)) =  if (listsEqual ((funNames (Plus p1 p2)) ++ [p3])  (ctorsOfSameRange sig p3))
                                                          then Var "y"
                                                          else Plus (Plus p1 p2) (Appl p3 t3)
                                                            where
                                                                  funNames (Plus pp1 (Appl pp2 _)) = (funNames pp1) ++ [pp2]
                                                                  funNames (Appl f ts) = [f]
            mergePlus (Var x) = Var x
            

listsEqual :: [FunName] -> [FunName] -> Bool
listsEqual x y = null (x \\ y) && null (y \\ x)

rmdups :: (Ord a) => [a] -> [a]
rmdups = map head . group . sort

otrsToTrs sig = aliasedTrsToTrs
              . additiveTrsToAliasedTrs sig
              . otrsToAdditiveTrs sig
              . antiTrsToOtrs sig
            
mergeTrs sig = aliasedTrsToTrs
              .additiveTrsToAliasedTrs sig
              .mergePlusses sig
              . fusionTrs sig

