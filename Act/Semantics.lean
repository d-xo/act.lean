-- give act expressions a concrete semantics in terms of the EVM

import Mathlib.Data.List.AList

import Act.AST

namespace Act

@[simp]
def rep : ActType -> Type
| .Bool => Bool
| .ByteStr => ByteArray
| .Int => Int
-- TODO: what to do here?
| .Contract => sorry

inductive Val where
| Val : {t : ActType} → rep t → Val

structure State where
  env : EthEnv t → rep t
  store : StorageRef → Val

def Vars := AList (λ (_ : String) => Val)

def eval (s : State) (v : Vars) : Exp a → rep a
| .And l r => (eval s v l) && (eval s v r)
| .Or l r => (eval s v l) || (eval s v r)

| .Add l r => Int.add (eval s v l) (eval s v r)
| .Sub l r => Int.sub (eval s v l) (eval s v r)

-- TODO: how to do this?
--| .Eq l r => eval s v l == eval s v r

| .Var ty _ nm => match v.lookup nm with
  | .some (@Val.Val t v) => match decEq t ty with
    | isTrue h => h ▸ v
    -- TODO: what to do about these unreachable cases...
    | isFalse _ => sorry
  | .none => sorry

| _ => sorry

-- TODO: handle returns
def step (behv : Behaviour) (state : State) : State := ⟨ state.env, store' ⟩
  where
    -- TODO: construct from sig
    vars := sorry
    cond := List.map (eval state vars) (behv.preconditions ++ behv.caseconditions)
         |> (List.all · id)
    store' :=
      if not cond
      then state.store
      else behv.storageUpdates.foldl (λ store upd => match upd with
        | .Update (.Item t _ ref) exp =>
          -- TODO: fails because we don't have DecidableEq for StorageRef...
          (λ r => if r = ref then @Val.Val t (eval state vars exp) else store r)
      ) state.store

end Act
