-- give act expressions a concrete semantics in terms of the EVM

import Mathlib.Control.Traversable.Basic
import Mathlib.Data.List.AList

import Act.AST

namespace Act

inductive Val where
| Int : Int → Val
| ByteStr : ByteArray → Val
| Bool : Bool → Val
deriving BEq

@[simp]
def rep : (a : ActType) → Type
| .Int => Int
| .ByteStr => ByteArray
| .Bool => Bool
| .Contract => sorry

def cast : (a : ActType) → Val → Option (rep a)
| .Int, .Int v => some v
| .ByteStr, .ByteStr v => some v
| .Bool, .Bool v => some v
| _, _ => none

-- TODO: this name sucks. it should be SlotType, but that's taken...
inductive LocType where
| Mapping : ActType -> LocType -> LocType
| Value   : ActType -> LocType
deriving Repr, DecidableEq, BEq

-- TODO: this name is bad too
-- TODO: this restricts the types in a nice way but is very dependent, we might regret this later
def rep' : LocType → Type
| .Mapping arg ret => rep arg → rep' ret
| .Value ty => rep ty

def extractTy : TypedExp → ActType
| @TypedExp.TExp t _ => t

def locTy (rt : ActType) : StorageRef → LocType
| .Var _ _ => .Value rt
| .Mapping r args => args.foldl (λ acc arg => .Mapping (extractTy arg) acc) (.Value rt)
| _ => sorry

inductive StorageVal : Type where
| Val : (ty : LocType) → rep' ty → StorageVal

abbrev Storage := String → Option StorageVal

def applyUpdate (store : Storage) (ref : StorageRef) (t : ActType) (val : rep t) : Storage :=
   -- TODO: brain hurts...
   λ k => if k == k then some (.Val (locTy t ref) sorry) else store k

structure State where
  env : ∀ t, EthEnv t → Val
  vars : String → Option Val
  store : Storage

namespace ind

inductive eval : State → Exp a → rep a → Type where
| And
  : eval s x rx
  → eval s y ry
  → eval s (.And x y) (Bool.and rx ry)

| LitInt : ∀ s i, eval s (.LitInt i) i

| Add
  : eval pre x rx
  → eval pre y ry
  → eval pre (.Add x y) (Int.add rx ry)

| Var :
  ∀ nm val ty ret abi
  , pre.vars nm = some val
  → cast ty val = some ret
  → eval pre (.Var ty abi  nm) ret

inductive evalTExp : State → TypedExp → (Σ a, rep a) → Type where
| TExp : ∀ ty e (rty : rep ty), eval s e rty → evalTExp s (@TypedExp.TExp ty e) ⟨ty, rty⟩

inductive Updates : State → State → List StorageUpdate → State → Type where
| Base : ∀ pre, Updates pre acc [] acc
| App
  : ∀ pre acc (e : Exp ta)
  , eval pre e v
  → Updates pre acc tl post
  → Updates pre post ((.Update (.Item ta tv ref) e) :: tl) ⟨pre.env, pre.vars, applyUpdate pre.store ref ta v⟩

inductive step : Behaviour → State → State → (Σ a, rep a) → Type where
| Step
   : ∀ name iface pres cases posts updates retexp
   , ∀ (e : Exp .Bool), e ∈ pres → eval s e true
   → ∀ (e : Exp .Bool), e ∈ cases → eval s e true
   -- TODO: state updates
   -- for each update,
   → evalTExp pre retexp rval
   → step ⟨name, iface, pres, cases, posts, updates, retexp⟩ pre post rval

def hi (s : State) := eval.Add (.LitInt s 10) (.LitInt s 2)

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
