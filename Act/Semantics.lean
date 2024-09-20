-- give act expressions a concrete semantics in terms of the EVM

import Mathlib.Control.Traversable.Basic
import Mathlib.Data.List.AList
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Finmap
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic

import Act.AST

namespace Act

-- Get the representation type for an Act AST type --

class Rep (α : Type) where
  rep : α → Type

open Rep

-- Basic Rep instances --

@[simp]
instance : Rep ActType where
  rep a := match a with
  | .Int => Int
  | .ByteStr => ByteArray
  | .Bool => Bool
  | .Contract => sorry

instance : Rep TypedExp where
  rep a := match a with
    | @TypedExp.TExp t _ => Rep.rep t

-- Type erased wrapper for values --

def Val := Σ t : ActType, rep t

def cast : (a : ActType) → Val → Option (rep a)
| .Int, ⟨.Int, v⟩ => some v
| .ByteStr, ⟨.ByteStr, v⟩ => some v
| .Bool, ⟨.Bool, v⟩ => some v
| _, _ => none

-- Storage Definition --

inductive LocType where
| Mapping : List ActType -> ActType → LocType
| Value   : ActType -> LocType
deriving Repr, DecidableEq, BEq

instance : Rep LocType where
  -- TODO: this restricts the types in a nice way but is very dependent, we might regret this later
  rep a := match a with
  | .Value ty => rep ty
  | .Mapping args ret => (Π (idx : Fin args.length), Rep.rep (args.get idx)) → (rep ret)

def StorageVal := Σ t : LocType, rep t

abbrev Storage := String → String → Option StorageVal

-- Evaluation State --

structure State where
  env : AList (λ (_ : EthEnv t) => rep t)
  vars : String → Option Val
  store : Storage

-- Evaluation Relations --

inductive Eval : State → Exp a → rep a → Type where
| And
  : Eval s x rx
  → Eval s y ry
  → Eval s (.And x y) (Bool.and rx ry)

| LitInt : ∀ i, Eval s (.LitInt i) i

| Add
  : Eval s x rx
  → Eval s y ry
  → Eval s (.Add x y) (Int.add rx ry)

| Var
  : s.vars nm = some val
  → cast ty val = some ret
  → Eval s (.Var ty abi  nm) ret

inductive EvalTExp : State → (e : TypedExp) → rep e → Type where
| TExp : ∀ ty e (rty : rep ty), Eval s e rty → EvalTExp s (@TypedExp.TExp ty e) rty

inductive EvalArgs : State → (args : List TypedExp) → (Π (idx : Fin args.length), Rep.rep (args.get idx)) → Type where
| Nil : EvalArgs state [] (λ idx => Fin.elim0 idx)
| Cons : EvalTExp state hd val
       → EvalArgs state tl rest
       → EvalArgs state (hd :: tl) (λ idx =>
           match idx with
           | ⟨0, _⟩ => val
           | ⟨.succ n, h⟩ => rest ⟨n, Nat.lt_of_succ_lt_succ h⟩
         )

inductive Updates : State → State → List StorageUpdate → State → Type where
| Base : ∀ pre, Updates pre acc [] acc
| Var
  : ∀ pre acc (e : Exp ta)
  , Eval pre e v
  → Updates pre acc tl post
  → Updates pre post ((.Update (.Item ta tv (.Var c nm)) e) :: tl)
    ⟨ pre.env
    , pre.vars
    , λ c' nm' => sorry
    ⟩
-- TODO: handle n-d maps
| Mapping1
  : ∀ pre acc (e : Exp ta)
  , Eval pre e v
  → EvalArgs pre args eargs
  → Updates pre acc tl post
  → Updates pre post ((.Update (.Item ta tv (.Mapping (.Var c nm) args)) e) :: tl)
    ⟨ pre.env
    , pre.vars
    , λ c' nm' => sorry
    ⟩

inductive Update : State → List StorageUpdate → State → Type where
| Update : Updates pre pre updates post → Update pre updates post

inductive EvalRet : State → Option TypedExp → Option (Σ a : ActType, rep a) → Type where
| None : EvalRet s .none .none
| Some
  : ∀ (exp : Exp t)
  , EvalTExp s (.TExp exp) v
  → EvalRet s (.some (@TypedExp.TExp t exp)) (some ⟨t, v⟩)

inductive Step : Behaviour → State → State → Option (Σ a : ActType, rep a) → Type where
| Step
   : ∀ (behv : Behaviour) pre
   , ∀ (e : Exp .Bool), e ∈ behv.preconditions → Eval pre e true
   → ∀ (e : Exp .Bool), e ∈ behv.caseconditions → Eval pre e true
   → Update pre behv.storageUpdates post
   → EvalRet pre behv.returns ret
   → Step behv pre post ret

end Act
