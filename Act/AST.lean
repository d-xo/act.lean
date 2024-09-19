import Lean.Elab.Deriving.DecEq
import Mathlib.Tactic
import Mathlib.Data.List.AList
import Init.Data.ByteArray

namespace Act

-- AST definitions for Act

inductive AbiType where
| UInt : Nat -> AbiType
| Int  : Nat -> AbiType
deriving Repr, DecidableEq, BEq
-- TODO other types

inductive ValueType where
| Contract  : String -> ValueType
| Primitive : AbiType -> ValueType
deriving Repr, DecidableEq, BEq

inductive SlotType where
| Mapping : List ValueType -> ValueType -> SlotType
| Value   : ValueType -> SlotType
deriving Repr, DecidableEq, BEq

inductive StorageVar where
| StorageVar : String -> SlotType -> StorageVar
deriving Repr, DecidableEq, BEq

def Store := AList (λ (_ : String) => AList (λ (_ : String) => SlotType × Nat))
deriving DecidableEq, BEq

instance : Repr Store where
  reprPrec s n := reprPrec (s.entries.map (λ v => (v.fst, v.snd.entries))) n

instance : Repr ByteArray where
  reprPrec b n := reprPrec b.data n

instance : BEq ByteArray where
  beq l r := BEq.beq l.data r.data

inductive ActType where
| Bool
| Int
| ByteStr
| Contract
deriving Repr, DecidableEq, BEq

-- TODO: why can't I just use the LawfulBEq instance here:
-- https://github.com/leanprover/lean4/blob/8f9843a4a5fe1b0c2f24c74097f296e2818771ee/src/Init/Core.lean#L635C1-L637C37
@[simp]
protected def ActTy.beq : ActType → ActType → Bool
| .Bool, .Bool => true
| .Int, .Int => true
| .ByteStr, .ByteStr => true
| .Contract, .Contract => true
| _, _ => false

@[simp]
instance : BEq ActType := ⟨ActTy.beq⟩

instance : LawfulBEq ActType where
  rfl {a} := by induction a <;> simp_all
  eq_of_beq {a b} := by
    induction a generalizing b <;> (cases b <;> aesop)

inductive When where
| Pre
| Post
deriving Repr, DecidableEq, BEq

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
deriving Repr, DecidableEq, BEq

-- Lean can't automatically derive DecidableEq for nested inductive types yes:
--  - https://github.com/leanprover/lean4/issues/2329
--  - https://github.com/leanprover/lean4/pull/3160
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
| LitBool : Bool → Exp .Bool

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
| Env : ∀ {t}, EthEnv t → Exp t
| NEq : Exp t → Exp t → Exp .Bool
| ITE : Exp .Bool → Exp t → Exp t → Exp t
| Var : (t : ActType) → AbiType → String → Exp t
| Entry : When → StorageItem t → Exp t
deriving Repr, BEq

inductive TypedExp where
| TExp : ∀ {ty}, Exp ty → TypedExp
deriving Repr, BEq

inductive StorageRef where
| Var : String → String → StorageRef
| Mapping : StorageRef → List TypedExp → StorageRef
| Field : StorageRef → String → String → StorageRef
deriving Repr, BEq

inductive StorageItem : ActType → Type where
| Item : (ty : ActType) → ValueType → StorageRef → StorageItem ty
deriving Repr, BEq

end

inductive StorageUpdate where
| Update : StorageItem ty → Exp ty → StorageUpdate
deriving Repr, BEq

structure Decl where
  type : AbiType
  name : String
deriving Repr, BEq

structure Interface where
  name : String
  decls : List Decl
deriving Repr, BEq

structure Constructor where
  name           : String
  interface      : Interface
  preconditions  : List (Exp .Bool)
  postconditions : List (Exp .Bool)
  initStorage    : List StorageUpdate
deriving Repr, BEq

structure Behaviour where
  name           : String
  interface      : Interface
  preconditions  : List (Exp .Bool)
  caseconditions : List (Exp .Bool)
  postconditions : List (Exp .Bool)
  storageUpdates : List StorageUpdate
  returns        : Option TypedExp
deriving Repr, BEq

structure Invariant where
  contract : String
  preconditions : List (Exp .Bool)
  storageBounds : List (Exp .Bool)
  predicate : Exp .Bool × Exp .Bool
deriving Repr, BEq

structure Contract where
  constructor : Constructor
  behaviours : List Behaviour
  invariants : List Invariant
deriving Repr, BEq

structure Spec where
  store : Store
  contracts : List Contract
deriving Repr, BEq

end Act
