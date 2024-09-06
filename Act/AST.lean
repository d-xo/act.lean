import Lean.Elab.Deriving.DecEq
import Mathlib.Tactic
import Mathlib.Data.List.AList
import Init.Data.ByteArray

-- AST definitions for Act

inductive AbiType where
| UInt : Nat -> AbiType
| Int  : Nat -> AbiType
deriving Repr, DecidableEq
-- TODO other types

inductive ValueType where
| Contract  : String -> ValueType
| Primitive : AbiType -> ValueType
deriving Repr, DecidableEq


inductive SlotType where
| Mapping : List ValueType -> ValueType -> SlotType
| Value   : ValueType -> SlotType
deriving Repr, DecidableEq

inductive StorageVar where
| StorageVar : String -> SlotType -> StorageVar
deriving Repr, DecidableEq


def Store := AList (λ (_ : String) => AList (λ (_ : String) => SlotType × Nat))
deriving DecidableEq

instance : Repr Store where
  reprPrec s n :=
    let ks := s.keys
    sorry

instance : Repr ByteArray where
  reprPrec b n := sorry

inductive ActType where
| Bool
| Int
| ByteStr
| Contract
deriving Repr, DecidableEq

inductive When where
| Pre
| Post
deriving Repr, DecidableEq

inductive EthEnv : ActType → Type where
| Caller : EthEnv .Int
| Callvalue : EthEnv .Int
| Calldepth : EthEnv .Int
| Origin : EthEnv .Int
| Blockhash : EthEnv .Int
| Blocknumber : EthEnv .Int
| Difficulty : EthEnv .Int
| Chainid : EthEnv .Int
| Gaslimit : EthEnv .Int
| Coinbase : EthEnv .Int
| Timestamp : EthEnv .Int
| This : EthEnv .Int
| Nonce : EthEnv .Int
deriving Repr, DecidableEq

mutual

inductive Exp : ActType → Type where
-- booleans
| And : Exp .Bool → Exp .Bool → Exp .Bool
| Or : Exp .Bool → Exp .Bool → Exp .Bool
| Impl : Exp .Bool → Exp .Bool → Exp .Bool
| Neg : Exp .Bool → Exp .Bool
| LT : Exp .Bool → Exp .Bool → Exp .Bool
| LEQ : Exp .Bool → Exp .Bool → Exp .Bool
| GEQ : Exp .Bool → Exp .Bool → Exp .Bool
| GT : Exp .Bool → Exp .Bool → Exp .Bool
| LitBool : Exp .Bool → Exp .Bool → Exp .Bool

-- integers
| Add : Exp .Int → Exp .Int → Exp .Int
| Sub : Exp .Int → Exp .Int → Exp .Int
| Mul : Exp .Int → Exp .Int → Exp .Int
| Div : Exp .Int → Exp .Int → Exp .Int
| Mod : Exp .Int → Exp .Int → Exp .Int
| Exp : Exp .Int → Exp .Int → Exp .Int
| LitInt : Int → Exp .Int

-- bounds
| IntMin : Int → Exp .Int
| IntMax : Int → Exp .Int
| UIntMin : Int → Exp .Int
| UIntMax : Int → Exp .Int
| InRange : AbiType → Exp .Int → Exp .Bool

-- bytestrings
| Cat : Exp .ByteStr → Exp .ByteStr → Exp .ByteStr
| Slice : Exp .ByteStr → Exp .Int → Exp .Int → Exp .ByteStr
| ByLit : ByteArray → Exp .ByteStr

-- contracts
| Create : (nm : String) → List TypedExp → Exp .Contract

-- polymorphic
| Eq : Exp t → Exp t → Exp .Bool
| Env : EthEnv t → Exp t
| NEq : Exp t → Exp t → Exp .Bool
| ITE : Exp .Bool → Exp t → Exp t → Exp t
| Var : (t : ActType) → AbiType → String → Exp t

-- storage
| Entry : When → StorageItem t → Exp t
deriving Repr

inductive TypedExp where
| TExp : ∀ {ty}, Exp ty → TypedExp
deriving Repr

inductive StorageRef where
| Var : String → String → StorageRef
| Mapping : StorageRef → List (TypedExp) → StorageRef
| Field : StorageRef → String → String → StorageRef
deriving Repr

inductive StorageItem : ActType → Type where
| Item : (ty : ActType) → ValueType → StorageRef → StorageItem ty
deriving Repr

end

mutual

instance (α : ActType) : DecidableEq (Exp α) := decExp
instance : DecidableEq StorageRef := sorry
instance : DecidableEq TypedExp := decTExp
instance (α : ActType) : DecidableEq (StorageItem α) := sorry

def decExp (a b : Exp t) : Decidable (a = b) :=
  match a, b with
  | .And la ra, .And lb rb => match decExp la lb, decExp ra rb with
    | isTrue hl, isTrue hr => isTrue (by rw [hl, hr])
    | isFalse _, _ => isFalse (by intro h; injection h; contradiction)
    | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  | .Or la ra, .Or lb rb => match decExp la lb, decExp ra rb with
    | isTrue hl, isTrue hr => isTrue (by rw [hl, hr])
    | isFalse _, _ => isFalse (by intro h; injection h; contradiction)
    | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  | _, _ => isFalse (by sorry)

def decTExp (a b : TypedExp) : Decidable (a = b) :=
  match a, b with
  | @TypedExp.TExp tl l, @TypedExp.TExp tr r => match tl, tr with
    | .Int, .Int => match decExp l r with
      | isTrue h => isTrue (by rw [h])
      | isFalse h => isFalse (by intro h; injection h; contradiction)
    | .Bool, .Bool => match decExp l r with
      | isTrue h => isTrue (by rw [h])
      | isFalse h => isFalse (by intro h; injection h; contradiction)
    | .ByteStr, .ByteStr => match decExp l r with
      | isTrue h => isTrue (by rw [h])
      | isFalse h => isFalse (by intro h; injection h; contradiction)
    | .Contract, .Contract => match decExp l r with
      | isTrue h => isTrue (by rw [h])
      | isFalse h => isFalse (by intro h; injection h; contradiction)
    | .Int, .ByteStr => isFalse (by intro h; injection h; contradiction)
    | .Int, .Bool => isFalse (by intro h; injection h; contradiction)
    | .Int, .Contract => isFalse (by intro h; injection h; contradiction)
    | .Bool, .Int => isFalse (by intro h; injection h; contradiction)
    | .Bool, .ByteStr => isFalse (by intro h; injection h; contradiction)
    | .Bool, .Contract => isFalse (by intro h; injection h; contradiction)
    | .ByteStr, .Int => isFalse (by intro h; injection h; contradiction)
    | .ByteStr, .Bool => isFalse (by intro h; injection h; contradiction)
    | .ByteStr, .Contract => isFalse (by intro h; injection h; contradiction)
    | .Contract, .Int => isFalse (by intro h; injection h; contradiction)
    | .Contract, .Bool => isFalse (by intro h; injection h; contradiction)
    | .Contract, .ByteStr => isFalse (by intro h; injection h; contradiction)

def decStorageRef (a b : StorageRef) : Decidable (a = b) :=
  match a, b with
  | .Var la lb, .Var ra rb => match instDecidableEqString la ra, instDecidableEqString lb rb with
    | isTrue hl, isTrue hr => isTrue (by rw [hl, hr])
    | isFalse _, _ => isFalse (by intro h; injection h; contradiction)
    | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  | .Mapping la lb, .Mapping ra rb => match decStorageRef la ra, instDecidableEqList lb rb with
    | isTrue hl, isTrue hr => isTrue (by rw [hl, hr])
    | isFalse _, _ => isFalse (by intro h; injection h; contradiction)
    | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  | _, _ => isFalse (by sorry)

end

inductive StorageUpdate where
| Update : StorageItem ty → Exp ty → StorageUpdate
deriving Repr, DecidableEq

structure Decl where
  type : AbiType
  name : String
deriving Repr, DecidableEq

structure Interface where
  name : String
  decls : List Decl
deriving Repr, DecidableEq

structure Constructor where
  name           : String
  interface      : Interface
  preconditions  : List (Exp .Bool)
  postconditions : List (Exp .Bool)
  initStorage    : List StorageUpdate
deriving Repr, DecidableEq

structure Behaviour where
  name           : String
  interface     : Interface
  preconditions  : List (Exp .Bool)
  caseconditions : List (Exp .Bool)
  postconditions : List (Exp .Bool)
  storageUpdates : List StorageUpdate
  initStorage    : List StorageUpdate
deriving Repr, DecidableEq

structure Invariant where
  contract : String
  preconditions : List (Exp .Bool)
  storageBounds : List (Exp .Bool)
  predicate : Exp .Bool × Exp .Bool
deriving Repr, DecidableEq

structure Contract where
  constructor : Constructor
  behaviours : List Behaviour
  invariants : List Invariant
deriving Repr, DecidableEq

structure Act where
  store : Store
  contracts : List Contract
deriving Repr, DecidableEq
