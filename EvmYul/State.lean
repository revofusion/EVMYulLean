module

public import Std.Data.TreeSet.Basic
public meta import Std.Data.TreeSet.Basic
public import Std.Data.TreeSet.Lemmas
public meta import Std.Data.TreeSet.Lemmas
public import Mathlib.Data.Finset.Basic
public meta import Mathlib.Data.Finset.Basic

public import EvmYul.State.ExecutionEnv
public meta import EvmYul.State.ExecutionEnv
public import EvmYul.State.Substate
public meta import EvmYul.State.Substate
public import EvmYul.State.Account
public meta import EvmYul.State.Account
public import EvmYul.State.Block
public meta import EvmYul.State.Block
public import EvmYul.State.Substate
public meta import EvmYul.State.Substate
public import EvmYul.State.Transaction
public meta import EvmYul.State.Transaction

public import EvmYul.Maps.AccountMap
public meta import EvmYul.Maps.AccountMap

public import EvmYul.UInt256
public meta import EvmYul.UInt256
public import EvmYul.Wheels
public meta import EvmYul.Wheels

@[expose] public section

namespace EvmYul

/--
The `State`. Section 9.3.

- `accountMap`   `σ`
- `substate`     `A`
- `executionEnv` `I`
- `totalGasUsedInBlock` `Υᵍ`
-/
structure State (τ : OperationType) where
  accountMap          : AccountMap τ
  σ₀                  : AccountMap .EVM
  totalGasUsedInBlock : ℕ
  transactionReceipts  : Array TransactionReceipt
  substate            : Substate
  executionEnv        : ExecutionEnv τ
  blocks              : ProcessedBlocks
  genesisBlockHeader  : BlockHeader
  createdAccounts     : Std.TreeSet AccountAddress compare
deriving Inhabited

def State.blockHashes {τ} (self : State τ) : Array UInt256 :=
  self.blocks.map ProcessedBlock.hash

end EvmYul
