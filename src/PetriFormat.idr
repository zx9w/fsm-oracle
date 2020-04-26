
module PetriFormat

import Typedefs.Typedefs
import Typedefs.Names
import Data.Vect
import PetriGraph

TNat : TDefR 2
TNat = RRef 0

TEdges : TDefR 2
TEdges = RRef 1

TState : TDefR 3
TState = RRef 2

TPetriSpec : TDefR 2
TPetriSpec = TProd [TNat, TEdges]

convertSpec : Ty [Nat, List (List Nat, List Nat)] TPetriSpec -> Maybe (n ** PetriSpec n)
convertSpec (places, edges) =
  MkDPair (length edges) . MkPetriSpec places <$> convertList places (fromList edges)
  where
    convertList : (p : Nat) ->  (Vect n (List Nat, List Nat))
               -> Maybe (Vect n (List (Fin p), List (Fin p)))
    convertList p = traverse (\(a, b) => [| MkPair (traverse (\v => natToFin v p) a)
                                                   (traverse (\v => natToFin v p) b) |])

TTree : TDefR 1
TTree = TMu
  [ ("Tensor", TProd [TVar 0, TVar 0])
  , ("Sequence", TProd [TVar 0, TVar 0])
  , ("Sym", TProd [TVar 1, TVar 1])
  , ("Id", TVar 1)
  , ("Mor", TVar 1)
  ]

convertTree : Ty [Nat] TTree -> (Tree Nat Nat)
convertTree (Inn (Left (a, b))) = Tensor (convertTree a) (convertTree b)
convertTree (Inn (Right (Left (a, b)))) = Sequence (convertTree a) (convertTree b)
convertTree (Inn (Right (Right (Left (a, b))))) = Sym a b
convertTree (Inn (Right (Right (Right (Left i))))) = Id i
convertTree (Inn (Right (Right (Right (Right m))))) = Mor m

convertState : (spec : PetriSpec k) -> List Nat -> Maybe (PetriState spec)
convertState spec = traverse (\s => natToFin s (Places spec))

public export
TPetriExec : TDefR 3
TPetriExec = TProd [TProd [RRef 0 , RRef 1], RRef 2, weakenTDef TTree 3 (LTESucc LTEZero)]

dropContext : Ty [Nat, a, b] (weakenTDef TTree 3 (LTESucc LTEZero)) -> Ty [Nat] TTree

export
convertExec : Ty [Nat, List (List Nat, List Nat), List Nat] TPetriExec -> Maybe PetriExec
convertExec ((a, b), c, d) = do (k ** spec) <- convertSpec (a , b)
                                path <- checkTree spec (convertTree $ dropContext d)
                                state <- convertState spec c
                                pure $ MkPetriExec spec path state

