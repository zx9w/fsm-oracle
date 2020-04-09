{-

SPDX-License-Identifier: AGPL-3.0-only

This file is part of `statebox/fsm-oracle`.

Copyright (C) 2020 Stichting Statebox <https://statebox.nl>

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Affero General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.

-}

module TGraph

-- base
import Data.Vect

-- idris-ct
import Graph.Graph
--import Graph.Path

-- typedefs
import Typedefs.Names
import Typedefs.Typedefs

%access public export
%default total

-- Base definitions

-- Defines naturals
TNat : TDefR 3
TNat = RRef 0

-- Graph definitions

||| The type definition for vertices in the graph is jsut
||| A natural enumerating the vertexes. e.g. 5 means
||| That there are 5 vertexes, denoted 0,1,2,3,4
FSMVertex : TDefR 3
FSMVertex = TNat

||| The type definition for edges in the graph is just a couple
||| of vertexes defining the edge source and target
FSMEdges : TDefR 3
FSMEdges = RRef 1

||| A Finite State Machine is defined by its vertices and a list of edges
||| The definition might not be valid if edges endpoints are out of range
FSMSpec : TDefR 3
FSMSpec = TProd [FSMVertex, FSMEdges]

||| A state is a vertex in the graph (might be out of range)
FSMState : TDefR 3
FSMState = FSMVertex

||| A path is a list of edges (might not be valid)
FSMPath : TDefR 3
FSMPath =  RRef 2-- TList `ap` [FSMEdge]

||| An execution is a FSM, a state representing an inital edge and a path from that edge.
||| The execution might not be valid.
FSMExec : TDefR 3
FSMExec = TProd [FSMSpec, FSMState, FSMPath]

||| Errors related to checking if a FSM description is valid
data FSMError =
  ||| Error in the FSM description
  InvalidFSM |
  ||| Error in the state transitions
  InvalidState |
  ||| Error in the execution path
  InvalidPath |
  ||| Error when parsing the JSON file
  JSONError |
  ||| Error when reading the file
  FSError

TFSMErr : TDefR 0
TFSMErr = TMu [("InvalidFSM", T1),
               ("InvalidState", T1),
               ("InvalidPath", T1),
               ("JSONError", T1),
               ("FSError", T1)
               ]

toTDefErr : FSMError -> Ty [] TFSMErr
toTDefErr InvalidFSM   = Inn (Left ())
toTDefErr InvalidState = Inn (Right (Left ()))
toTDefErr InvalidPath  = Inn (Right (Right (Left ())))
toTDefErr JSONError    = Inn (Right (Right (Right (Left ()))))
toTDefErr FSError      = Inn (Right (Right (Right (Right ()))))

Show FSMError where
  show InvalidFSM   = "Invalid FSM"
  show InvalidState = "Invalid state"
  show InvalidPath  = "Invalid path"
  show JSONError    = "JSON parsing error"
  show FSError      = "Filesystem error"

IdrisType : TDefR 3 -> Type
IdrisType = Ty [Nat, List (Nat, Nat), List Nat]

||| Monad to check errors when compiling FSMs
FSMCheck : Type -> Type
FSMCheck = Either FSMError

convertList : (n : Nat) -> List (Nat, Nat) -> Maybe (List (Fin n, Fin n))
convertList n edges = traverse (\(x,y) => [| MkPair (natToFin x n) (natToFin y n) |]) edges

||| Convert a list of nat into the index into the vector of edges
convertList' : (n : Nat) -> List Nat -> Maybe (List (Fin n))
convertList' n edges = traverse (\x => natToFin x n) edges

-- > record Graph vertices where
-- >   constructor MkGraph
-- >   edges : Vect n (vertices, vertices)

mkTGraph : (Nat, List (Nat, Nat)) -> Maybe (DPair Nat (\size => Graph (Fin size)))
mkTGraph (size, edges) = do convertedEdges <- convertList size edges
                            pure (size ** MkGraph $ fromList convertedEdges)

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
PetriVertex : TDefR 0
PetriVertex = TProd [List Nat, List (List Nat, List Nat)]

PetriState : TDefR 0
PetriState = TList `ap` TNat

PetriPath : TDefR 2
PetriPath = TMu [ ("Tensor", TProd [TVar 0, TVar 0])
                , ("Sequence", TProd [TVar 0, TVar 0])
                , ("Id", TVar 1)
                , ("Mor", TVar 2)
                ]
{-
FSMSpec, FSMState, FSMPath

Tensor f g : a c -> b d
       |
      xa
   /      \
 /          \
 |         ;
 |        /    \
 x       |   id
/  \     |     |
f  g     h   x
              /   \
             a    b
(f * g) * (h;id_a)



DecEq a => Maybe HYpergraph a b -> Maybe HYpergraph b c -> Maybe (Hypergraph a c)
a b = [| compose a b |] <=> pure compose <*> a <$> b

{a,b,c,d : TDef 0} -> Mor a b -> Mor' c d  -> Maybe (Mor a d)
if b = c then Compose
otherwise fuck off

PetriOracle : (description : (PEtriSpec, PetriState, PetriPath)) -> Maybe (tree : Tree Nat (List Nat, List Nat))
           -> Maybe (left : Domain tree ** right : Codomain tree ** Hypergraph left right)


HasObject tree -> (p : Object tree ** Position tree)
-}

Domain : (morphisms : Vect k (List a, List a)) -> Tree a (Fin k) -> List a
Domain _ (Tensor l r) = Domain l ++ Domain r
Domain _ (Sequence l r) = Domain l
Domain _ (Id o) = o
Domain m (Mor i) = fst $ index i m

CoDomain : (morphisms : Vect k (List a, List a)) -> Tree a (Fin k) -> List a
CoDomain _ (Tensor l r) = CoDomain l ++ CoDomain r
CoDomain _ (Sequence l r) = CoDomain r
CoDomain _ (Id o) = o
CoDomain m (Mor i) = snd $ index i m
