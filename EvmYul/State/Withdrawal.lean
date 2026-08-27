-- Requires the following python packages: pycryptodome

module

public import EvmYul.Wheels
public meta import EvmYul.Wheels
public import EvmYul.PerformIO
public meta import EvmYul.PerformIO
public import EvmYul.Maps.AccountMap
public meta import EvmYul.Maps.AccountMap
public import Conform.Wheels
public meta import Conform.Wheels
public import EvmYul.EVM.Exception
public meta import EvmYul.EVM.Exception

public import EvmYul.State.TrieRoot
public meta import EvmYul.State.TrieRoot

@[expose] public section

open EvmYul ByteArray

/--
EIP-4895: Beacon chain push withdrawals as operations.
- `index` - starting from `0`
- `validator_index`
- `address` - a recipient for the withdrawn ether
- `amount` - a nonzero amount of ether given in Gwei
-/
structure Withdrawal where
  index : UInt64
  validatorIndex : UInt64
  address : AccountAddress
  amount : UInt64
deriving Repr, BEq

namespace Withdrawal

def to𝕋 : Withdrawal → 𝕋
  | {index, validatorIndex, address, amount} =>
    .𝕃
      [ .𝔹 (BE index.toFin.val)
      , .𝔹 (BE validatorIndex.toFin.val)
      , .𝔹 (address.toByteArray)
      , .𝔹 (BE amount.toFin.val)
      ]

end Withdrawal

def Withdrawal.toBlobs (w : ℕ × ByteArray) : Option (String × String) := do
  let rlpᵢ ← RLP (.𝔹 (BE w.1))
  let rlp ← w.2
  pure (EvmYul.toHex rlpᵢ, EvmYul.toHex rlp)

-- EIP-4895
def Withdrawal.computeTrieRoot (ws : Array ByteArray) : Option ByteArray := do
  match Array.mapM Withdrawal.toBlobs ((Array.range ws.size).zip ws) with
    | none => .none
    | some ws => (ByteArray.ofBlob (blobComputeTrieRoot ws)).toOption

def applyWithdrawals
  (σ : AccountMap .EVM)
  (ws : Array Withdrawal)
    :
  AccountMap .EVM
:=
  ws.foldl applyWithdrawal σ
 where
  applyWithdrawal (σ : AccountMap .EVM) (w : Withdrawal) : AccountMap .EVM :=
    if w.amount <= 0 then σ else
      match σ.get? w.address with
        | none =>
          σ.insert w.address {(default : Account .EVM) with balance := .ofNat <| w.amount.toFin.val * 10^9}
        | some ac =>
          σ.insert w.address {ac with balance := .ofNat <| ac.balance.toNat + w.amount.toFin.val * 10^9}
