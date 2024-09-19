-- give act expressions a concrete semantics in terms of the EVM

import Mathlib.Control.Traversable.Basic
import Mathlib.Data.List.AList
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Finmap
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic

import Act.AST

namespace Act

inductive Val where
| Int : Int → Val
| ByteStr : ByteArray → Val
| Bool : Bool → Val
deriving BEq

class Rep (α : Type) where
  rep : α → Type

open Rep

@[simp]
instance : Rep ActType where
  rep a := match a with
  | .Int => Int
  | .ByteStr => ByteArray
  | .Bool => Bool
  | .Contract => sorry

def cast : (a : ActType) → Val → Option (rep a)
| .Int, .Int v => some v
| .ByteStr, .ByteStr v => some v
| .Bool, .Bool v => some v
| _, _ => none

inductive LocType where
| Mapping : List ActType -> ActType → LocType
| Value   : ActType -> LocType
deriving Repr, DecidableEq, BEq

instance : Rep LocType where
  -- TODO: this restricts the types in a nice way but is very dependent, we might regret this later
  rep a := match a with
  | .Value ty => rep ty
  | .Mapping args ret => (Π (idx : Fin args.length), Rep.rep (args.get idx)) → (rep ret)

def extractTy : TypedExp → ActType
| @TypedExp.TExp t _ => t

def locTy (rt : ActType) : StorageRef → LocType
| .Var _ _ => .Value rt
| .Mapping r args => .Mapping (args.map extractTy) rt
| .Field _ _ _ => sorry

inductive StorageVal : Type where
| Val : (ty : LocType) → rep ty → StorageVal

abbrev Storage := String → String → Option StorageVal

structure State where
  env : ∀ t, EthEnv t → Val
  vars : String → Option Val
  store : Storage

namespace ind

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

instance : Rep TypedExp where
  rep a := match a with
    | @TypedExp.TExp t _ => Rep.rep t

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
    , λ c' nm' =>
      if c = c' && nm = nm'
      then some (.Val (locTy ta (.Var c nm)) v)
      else post.store c' nm'
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
    , λ c' nm' =>
      if c = c' && nm = nm'
      -- TODO: gotta build a function with the same number of
      then some (.Val (locTy ta (.Mapping (.Var c nm) args)) (λ as =>
        have len_thm : args.length  = (List.map extractTy args).length := by sorry
        have arg_thm : ∀ i, rep ((List.map extractTy args).get (len_thm ▸ i)) = rep (args.get i) := by sorry
        Fin.foldl args.length (λ (a : Bool) i =>
          a && (eargs i == (arg_thm i ▸ as (len_thm ▸ i)))
        ) True
      ))
      else post.store c' nm'
    ⟩

inductive Update : State → List StorageUpdate → State → Type where
| Update : Updates pre pre updates post → Update pre updates post

inductive EvalRet : State → Option TypedExp → Option (Σ a : ActType, rep a) → Type where
| None : EvalRet s .none .none
| Some
  : ∀ (exp : Exp t)
  , EvalTExp s (.TExp exp) ⟨t, v⟩
  → EvalRet s (.some (@TypedExp.TExp t exp)) (some ⟨t, v⟩)

inductive Step : Behaviour → State → State → Option (Σ a : ActType, rep a) → Type where
| Step
   : ∀ (behv : Behaviour) pre
   , ∀ (e : Exp .Bool), e ∈ behv.preconditions → Eval pre e true
   → ∀ (e : Exp .Bool), e ∈ behv.caseconditions → Eval pre e true
   → Update pre behv.storageUpdates post
   → EvalRet pre behv.returns ret
   → Step behv pre post ret

end ind

namespace int

def eval (s : State) : Exp a → Option Val
| .And l r => match eval s l, eval s r with
  | .some (.Bool l'), .some (.Bool r') => .some (.Bool (l' && r'))
  | _, _ => .none

| .Add l r => match eval s l, eval s r with
  | .some (.Int l'), .some (.Int r') => .some (.Int (l' + r'))
  | _, _ => .none

| .Cat l r => match eval s l, eval s r with
  | .some (.ByteStr l'), .some (.ByteStr r') => .some (.ByteStr (l' ++ r'))
  | _, _ => .none

| .Eq l r => match eval s l, eval s r with
  | .some (.Int l'), .some (.Int r') => .some (.Bool (l' == r'))
  | .some (.ByteStr l'), .some (.ByteStr r') => .some (.Bool (l' == r'))
  | .some (.Bool l'), .some (.Bool r') => .some (.Bool (l' == r'))
  | _, _ => .some (.Bool false)

| _ => .none


def step (behv : Behaviour) (state : State) : Option (State × Option Val) := do
  let cond ← do
    let vs ← sequence $ List.map (eval state) (behv.preconditions ++ behv.caseconditions)
    let bs ← sequence $ vs.map (λ v => match v with
      | .Bool b => some b
      | _ => none)
    pure $ bs.all id

  let ret := match behv.returns with
    | .some (.TExp e) => eval state e
    | .none => .none

  let store' :=
      if not cond
      then state.store
      else behv.storageUpdates.foldl (λ store upd => match upd with
        | .Update (.Item t _ ref) exp => match eval state exp with
          | .none => store
          | .some v => λ r => if r == ref then v else store r
      ) state.store

  pure ⟨⟨ state.env, state.vars, store' ⟩, ret⟩

end int


end Act
