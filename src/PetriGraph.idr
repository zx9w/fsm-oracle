module PetriGraph

import Data.Vect
import Basic.Category
import Cartographer.HypergraphStrictMonoidalCategory
import MonoidalCategory.StrictMonoidalCategory
import Cartographer.Hypergraph


%default total
{-
StringDiag := {
  tensor := {
    tensor := {
      f
      g
    }
    sequence := {
      h
      identity A
      }
    }
  }
}

data Tree o m = Tensor Tree Tree | Sequence Tree Tree | Id o | Mor m
-}
-- PetriSpec
-- Vertex: Nat, Edges : List ((List Nat), (List Nat))
{-
PetriVertex : TDefR 0
PetriVertex = TProd [TList Nat, TList (TList Nat, TList Nat)]

PetriState : TDefR 0
PetriState = TList `ap` TNat

PetriPath : TDefR 2
PetriPath = TMu [ ("Tensor", TProd [TVar 0, TVar 0])
                , ("Sequence", TProd [TVar 0, TVar 0])
                , ("Id", TVar 1)
                , ("Mor", TVar 2)
                ]

-}

record PetriSpec (k : Nat) where 
  constructor MkPetriSpec
  Places : Nat
  Edges : Vect k (List (Fin Places), List (Fin Places))

PetriState : Type
PetriState = List Nat

data Tree o m = Tensor (Tree o m) (Tree o m) 
              | Sequence (Tree o m) (Tree o m) 
              | Sym o o
              | Id o 
              | Mor m

--l --------\ / -------- r
--           X
--r --------/ \--------- l

-- o ------------------------- o

Domain : (morphisms : Vect k (List a, List a)) -> Tree a (Fin k) -> List a
Domain m (Tensor l r) = (Domain m l) ++ (Domain m r)
Domain m (Sequence l r) = Domain m l
Domain m (Id o) = pure o
Domain m (Sym l r) = [l, r]
Domain m (Mor i) = fst $ index i m


Codomain : (morphisms : Vect k (List a, List a)) -> Tree a (Fin k) -> List a
Codomain m (Tensor l r) = Codomain m l ++ Codomain m r
Codomain m (Sequence l r) = Codomain m r
Codomain m (Id o) = pure o
Codomain m (Sym l r) = [r, l]
Codomain m (Mor i) = snd $ index i m


PetriPath : Nat -> Nat -> Type
PetriPath places k = Tree (Fin places) (Fin k)

-- PetriExec : Nat -> Type
-- PetriExec n = (PetriSpec n, PetriState, PetriPath)

-- checkSpec : (spec : PetriSpec) -> Maybe (Nat -> (List (Fin (Places spec))), Nat -> (List (Fin (Places spec)))

-- leftCheck : (spec : PetriSpec) -> Maybe (Nat -> List (Fin (Places spec)))

-- rightCheck : (spec : PetriSpec) -> Maybe (Nat -> List (Fin (Places spec)))


-- checkSpec : PetriSpec -> (Nat -> Maybe (List Nat), Nat -> Maybe (List Nat))
-- checkSpec (MkPetriSpec pl eg)  = (\idx => do (ai, ao) <- index' idx eg
--                                              if all ( < pl) ai then pure ai else Nothing
--                                  ,\idx => do (ai, ao) <- index' idx eg
--                                              if all ( < pl) ao then pure ao else Nothing)


everything : (spec : PetriSpec k) -> (ai, ao : Fin k -> List (Fin (Places spec))) -> (path : PetriPath (Places spec) k)
          -> Maybe (mor (cat (hypergraphSMC (Fin k) ai ao)) (Domain (Edges spec) path) (Codomain (Edges spec) path) )
everything _ ai ao (Tensor lt rt) = ?te
everything _ ai ao (Sequence lt rt) = ?seq
everything _ ai ao (Sym a b) = ?sym
everything _ ai ao (Id o) = Just (Hypergraph.identity [o])
everything _ ai ao (Mor m) = Just ?wat--(Hypergraph.singleton m)

-- hypergraphSMC : (s : Type) -> (ai, ao : s -> List o) -> StrictMonoidalCategory
--  {s : Type} -> {ai, ao : s -> List o} -> (n : List o) -> Hypergraph s ai ao n n
-- 

-- PetriOracle : (description : (PEtriSpec, PetriState, PetriPath)) -> Maybe (tree : Tree Nat (List Nat, List Nat))
--            -> Maybe (left : domain tree ** right : codomain tree ** Hypergraph left right)

-- (s: Type, ai, ao: s -> List o)
-- 
-- {s : Type} -> {ai, ao : Nat -> List (Fin (length Edges))}