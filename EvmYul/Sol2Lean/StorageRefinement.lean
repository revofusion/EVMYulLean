module

public import Std.Data.TreeMap.Lemmas
public meta import Std.Data.TreeMap.Lemmas

public import EvmYul.FFI.ffi
public meta import EvmYul.FFI.ffi
public import EvmYul.State.AccountOps
public meta import EvmYul.State.AccountOps
public import EvmYul.StateOps
public meta import EvmYul.StateOps

@[expose] public section

namespace EvmYul
namespace Sol2Lean

/--
Scalar Solidity storage fields use their assigned slot directly.
-/
abbrev scalarSlot (slot : UInt256) : UInt256 := slot

/--
Mappings use the standard Solidity slot derivation `keccak256(key ++ baseSlot)`.
-/
def mappingSlot (key baseSlot : UInt256) : UInt256 :=
  .ofNat <| fromByteArrayBigEndian <| ffi.KEC (UInt256.toByteArray key ++ UInt256.toByteArray baseSlot)

/--
Read a raw storage slot with Solidity's default-zero convention.
-/
def storageRead (storage : Storage) (slot : UInt256) : UInt256 :=
  storage.getD slot default

/--
Read a logical mapping entry from raw storage.
-/
def mappingRead (storage : Storage) (baseSlot key : UInt256) : UInt256 :=
  storageRead storage (mappingSlot key baseSlot)

def StorageRefinesScalar (storage : Storage) (slot value : UInt256) : Prop :=
  storageRead storage slot = value

def StorageRefinesMappingKey (storage : Storage) (baseSlot key value : UInt256) : Prop :=
  mappingRead storage baseSlot key = value

/--
Refine a typed mapping as a total function with default zero.
-/
def StorageRefinesMapping (storage : Storage) (baseSlot : UInt256) (f : UInt256 → UInt256) : Prop :=
  ∀ key, mappingRead storage baseSlot key = f key

def StateRefinesScalar {τ} (self : State τ) (slot value : UInt256) : Prop :=
  StorageRefinesScalar self.selfStorage! slot value

def StateRefinesMappingKey {τ} (self : State τ) (baseSlot key value : UInt256) : Prop :=
  StorageRefinesMappingKey self.selfStorage! baseSlot key value

def StateRefinesMapping {τ} (self : State τ) (baseSlot : UInt256) (f : UInt256 → UInt256) : Prop :=
  StorageRefinesMapping self.selfStorage! baseSlot f

theorem storageRead_of_refinesScalar {storage : Storage} {slot value : UInt256}
    (h : StorageRefinesScalar storage slot value) :
    storageRead storage slot = value :=
  h

theorem mappingRead_of_refinesKey {storage : Storage} {baseSlot key value : UInt256}
    (h : StorageRefinesMappingKey storage baseSlot key value) :
    mappingRead storage baseSlot key = value :=
  h

theorem mappingRead_of_refines {storage : Storage} {baseSlot : UInt256} {f : UInt256 → UInt256}
    (h : StorageRefinesMapping storage baseSlot f) (key : UInt256) :
    mappingRead storage baseSlot key = f key :=
  h key

theorem sload_of_refinesScalar {τ} {self : State τ} {slot value : UInt256}
    (h : StateRefinesScalar self slot value) :
    (State.sload self slot).2 = value := by
  unfold StateRefinesScalar StorageRefinesScalar storageRead State.selfStorage! at h
  unfold State.sload
  cases hacc : self.lookupAccount self.executionEnv.codeOwner with
  | none =>
      simp [hacc] at h ⊢
      exact h
  | some acc =>
      simp [hacc, Account.lookupStorage] at h ⊢
      exact h

theorem sload_of_refinesMappingKey {τ} {self : State τ} {baseSlot key value : UInt256}
    (h : StateRefinesMappingKey self baseSlot key value) :
    (State.sload self (mappingSlot key baseSlot)).2 = value := by
  simpa [StateRefinesMappingKey, StorageRefinesMappingKey, mappingRead]
    using sload_of_refinesScalar (self := self) (slot := mappingSlot key baseSlot) (value := value) h

theorem sload_of_refinesMapping {τ} {self : State τ} {baseSlot : UInt256} {f : UInt256 → UInt256}
    (h : StateRefinesMapping self baseSlot f) (key : UInt256) :
    (State.sload self (mappingSlot key baseSlot)).2 = f key := by
  simpa [StateRefinesMapping, StorageRefinesMapping, StorageRefinesMappingKey, mappingRead]
    using sload_of_refinesScalar (self := self) (slot := mappingSlot key baseSlot) (value := f key) (h key)

theorem storageRead_insert_self (storage : Storage) (slot value : UInt256) :
    storageRead (storage.insert slot value) slot = value := by
  unfold storageRead
  rw [Std.TreeMap.getD_insert_self]

theorem storageRead_insert_of_ne (storage : Storage) (slot slot' value : UInt256) (hslot : slot' ≠ slot) :
    storageRead (storage.insert slot value) slot' = storageRead storage slot' := by
  have hcmp : compare slot slot' ≠ .eq := by
    simpa [compare_eq_iff_eq] using (Ne.symm hslot)
  unfold storageRead
  rw [Std.TreeMap.getD_insert, if_neg hcmp]

/--
`Account.updateStorage` branches on `value == 0`, so the nonzero case is expressed with the same boolean
guard that EVMYulLean uses internally.
-/
theorem lookupStorage_updateStorage_same_of_nonzero {τ} (acc : Account τ) (slot value : UInt256)
    (hvalue : (value == default) = false) :
    (acc.updateStorage slot value).lookupStorage slot = value := by
  simp [Account.updateStorage, Account.lookupStorage, hvalue]

theorem lookupStorage_updateStorage_of_ne_of_nonzero {τ} (acc : Account τ)
    (slot slot' value : UInt256) (hvalue : (value == default) = false) (hslot : slot' ≠ slot) :
    (acc.updateStorage slot value).lookupStorage slot' = acc.lookupStorage slot' := by
  simp [Account.updateStorage, Account.lookupStorage, hvalue, Std.TreeMap.getD_insert, Ne.symm hslot]

theorem refinesScalar_updateStorage_same_of_nonzero {τ} {acc : Account τ} {slot value : UInt256}
    (hvalue : (value == default) = false) :
    StorageRefinesScalar (acc.updateStorage slot value).storage slot value := by
  simp [StorageRefinesScalar, Account.updateStorage, hvalue]
  exact storageRead_insert_self acc.storage slot value

theorem refinesScalar_updateStorage_of_ne_of_nonzero {τ} {acc : Account τ}
    {slot slot' value preserved : UInt256}
    (href : StorageRefinesScalar acc.storage slot' preserved)
    (hvalue : (value == default) = false)
    (hslot : slot' ≠ slot) :
    StorageRefinesScalar (acc.updateStorage slot value).storage slot' preserved := by
  simp [StorageRefinesScalar, Account.updateStorage, hvalue]
  exact (storageRead_insert_of_ne acc.storage slot slot' value hslot).trans href

theorem refinesMappingKey_updateStorage_same_of_nonzero {τ} {acc : Account τ}
    {baseSlot key value : UInt256}
    (hvalue : (value == default) = false) :
    StorageRefinesMappingKey (acc.updateStorage (mappingSlot key baseSlot) value).storage baseSlot key value := by
  simpa [StorageRefinesMappingKey, mappingRead, StorageRefinesScalar] using
    refinesScalar_updateStorage_same_of_nonzero (acc := acc) (slot := mappingSlot key baseSlot) (value := value) hvalue

/--
Updating a mapping entry preserves the whole functional refinement if the caller supplies the expected
non-collision fact for the hashed slots. This keeps the bridge honest: we do not prove Keccak injective.
-/
theorem refinesMapping_updateStorage_of_nonzero
    {τ} {acc : Account τ} {baseSlot key value : UInt256} {f : UInt256 → UInt256}
    (href : StorageRefinesMapping acc.storage baseSlot f)
    (hvalue : (value == default) = false)
    (hsep : ∀ {other : UInt256}, other ≠ key → mappingSlot other baseSlot ≠ mappingSlot key baseSlot) :
    StorageRefinesMapping
      (acc.updateStorage (mappingSlot key baseSlot) value).storage
      baseSlot
      (Function.update f key value) := by
  intro other
  by_cases hother : other = key
  · subst other
    simpa [StorageRefinesMappingKey, mappingRead, Function.update] using
      refinesMappingKey_updateStorage_same_of_nonzero (acc := acc) (baseSlot := baseSlot) (key := key) (value := value) hvalue
  · have hslot : mappingSlot other baseSlot ≠ mappingSlot key baseSlot :=
      hsep hother
    have hpreserved :=
      refinesScalar_updateStorage_of_ne_of_nonzero
        (acc := acc)
        (slot := mappingSlot key baseSlot)
        (slot' := mappingSlot other baseSlot)
        (value := value)
        (preserved := f other)
        (href := href other)
        hvalue
        hslot
    simpa [StorageRefinesMapping, StorageRefinesMappingKey, mappingRead, StorageRefinesScalar, Function.update, hother] using hpreserved

section Examples

example :
    StorageRefinesScalar ((default : Storage).insert (scalarSlot ⟨7⟩) ⟨11⟩) (scalarSlot ⟨7⟩) ⟨11⟩ := by
  simpa [StorageRefinesScalar] using
    storageRead_insert_self (storage := (default : Storage)) (slot := scalarSlot ⟨7⟩) (value := ⟨11⟩)

example :
    StorageRefinesMappingKey ((default : Storage).insert (mappingSlot ⟨1⟩ ⟨0⟩) ⟨9⟩) ⟨0⟩ ⟨1⟩ ⟨9⟩ := by
  simpa [StorageRefinesMappingKey, mappingRead] using
    storageRead_insert_self (storage := (default : Storage)) (slot := mappingSlot ⟨1⟩ ⟨0⟩) (value := ⟨9⟩)

example {τ} (acc : Account τ) :
    StorageRefinesScalar (acc.updateStorage ⟨5⟩ ⟨7⟩).storage ⟨5⟩ ⟨7⟩ := by
  simpa using refinesScalar_updateStorage_same_of_nonzero (acc := acc) (slot := ⟨5⟩) (value := ⟨7⟩) (by decide)

end Examples

/-!
## Storage Refinement Bridge Architecture

The **StorageRefines*** family relates raw EVM storage (a flat `UInt256 → UInt256` map) to typed
Lean state fields that generated proof sidecars work with.

### Key types

- `StorageRefinesScalar storage slot value`: the scalar at `slot` reads back as `value`.
- `StorageRefinesMappingKey storage baseSlot key value`: the mapping entry at
  `keccak256(key ++ baseSlot)` reads back as `value`.
- `StorageRefinesMapping storage baseSlot f`: every key in the mapping refines through function `f`.

### Separation assumptions

Solidity's storage layout relies on Keccak-256 to separate mapping-derived slots from scalar slots
and from each other. We do **not** prove Keccak injective — instead, callers supply lightweight
*separation hypotheses* (`MappingSlotsSeparate`, `ScalarMappingSeparate`, or ad-hoc `≠` facts).
This keeps the bridge honest while letting generated sidecars discharge these assumptions via
trusted axioms or assumed non-collision facts.

### How generated sidecars use these theorems

A typical sidecar for a Solidity contract:
1. Asserts `StorageRefinesScalar` / `StorageRefinesMapping` for every field in the Lean model.
2. Uses the *read* theorems (`storageRead_of_refinesScalar`, `mappingRead_of_refines`, …) to
   connect `sload` results to model values.
3. Uses the *preservation* theorems (`refinesScalar_preserved_of_ne_slot`, …) to show that
   writing one field does not break refinement of other fields.
4. Uses the *separation* definitions to bundle the non-collision facts cleanly.
-/

-- ============================================================================
-- A4.1: Scalar Read/Write Preservation Theorems
-- ============================================================================

/--
Writing to a different slot (via raw insert) preserves scalar refinement.
This is the pure-storage version for direct `Storage.insert` patterns.
-/
theorem refinesScalar_preserved_of_ne_slot {storage : Storage}
    {slotA valueA slotB valueB : UInt256}
    (href : StorageRefinesScalar storage slotA valueA)
    (hne : slotA ≠ slotB) :
    StorageRefinesScalar (storage.insert slotB valueB) slotA valueA := by
  unfold StorageRefinesScalar at href ⊢
  rw [storageRead_insert_of_ne storage slotB slotA valueB hne]
  exact href

/--
Writing to a different slot (via `Account.updateStorage` with nonzero value) preserves scalar
refinement. This is a synonym of `refinesScalar_updateStorage_of_ne_of_nonzero` presented with
the hypothesis order that matches the "preservation" naming convention.
-/
theorem refinesScalar_preserved_updateStorage_of_ne {τ} {acc : Account τ}
    {slotA valueA slotB valueB : UInt256}
    (href : StorageRefinesScalar acc.storage slotA valueA)
    (hvalue : (valueB == default) = false)
    (hne : slotA ≠ slotB) :
    StorageRefinesScalar (acc.updateStorage slotB valueB).storage slotA valueA :=
  refinesScalar_updateStorage_of_ne_of_nonzero href hvalue hne

-- ============================================================================
-- A4.2: Mapping Read/Write Preservation Theorems
-- ============================================================================

/--
Writing to a slot that is provably different from the derived mapping slot preserves a single
mapping-key refinement. Useful when updating a scalar that cannot collide with a mapping entry.
-/
theorem refinesMappingKey_preserved_of_ne_slot {τ} {acc : Account τ}
    {baseSlot key valueK slotW valueW : UInt256}
    (href : StorageRefinesMappingKey acc.storage baseSlot key valueK)
    (hvalue : (valueW == default) = false)
    (hne : mappingSlot key baseSlot ≠ slotW) :
    StorageRefinesMappingKey (acc.updateStorage slotW valueW).storage baseSlot key valueK := by
  unfold StorageRefinesMappingKey mappingRead at href ⊢
  exact refinesScalar_updateStorage_of_ne_of_nonzero href hvalue hne

/--
Writing to a slot that is not any derived mapping slot of `baseSlot` preserves the full mapping
refinement. The caller must supply a separation hypothesis proving the write target cannot be
`mappingSlot k baseSlot` for any `k`.
-/
theorem refinesMapping_preserved_of_ne_baseSlot {τ} {acc : Account τ}
    {baseSlot : UInt256} {f : UInt256 → UInt256} {slotW valueW : UInt256}
    (href : StorageRefinesMapping acc.storage baseSlot f)
    (hvalue : (valueW == default) = false)
    (hsep : ∀ k, mappingSlot k baseSlot ≠ slotW) :
    StorageRefinesMapping (acc.updateStorage slotW valueW).storage baseSlot f := by
  intro key
  have hne : mappingSlot key baseSlot ≠ slotW := hsep key
  simp only [StorageRefinesMapping, mappingRead] at href ⊢
  exact refinesScalar_updateStorage_of_ne_of_nonzero (href key) hvalue hne

/--
Updating the mapping slot for key `K` at `baseSlot` reflects the new value in the mapping-key
refinement. This is the "write-then-read-same-key" direction.
-/
theorem refinesMappingKey_updateStorage_same_key {τ} {acc : Account τ}
    {baseSlot key value : UInt256}
    (hvalue : (value == default) = false) :
    StorageRefinesMappingKey (acc.updateStorage (mappingSlot key baseSlot) value).storage baseSlot key value :=
  refinesMappingKey_updateStorage_same_of_nonzero hvalue

-- ============================================================================
-- A4.3: Multi-Field Update Composition
-- ============================================================================

/--
Reading after two successive inserts where neither insert slot matches the read slot.
-/
theorem storageRead_insert_insert_of_ne (storage : Storage)
    (s1 v1 s2 v2 target : UInt256)
    (hne1 : target ≠ s1) (hne2 : target ≠ s2) :
    storageRead ((storage.insert s1 v1).insert s2 v2) target = storageRead storage target := by
  rw [storageRead_insert_of_ne (storage.insert s1 v1) s2 target v2 hne2]
  rw [storageRead_insert_of_ne storage s1 target v1 hne1]

/--
Scalar refinement is preserved through a chain of two inserts at different slots.
-/
theorem refinesScalar_insert_chain {storage : Storage}
    {slot value s1 v1 s2 v2 : UInt256}
    (href : StorageRefinesScalar storage slot value)
    (hne1 : slot ≠ s1) (hne2 : slot ≠ s2) :
    StorageRefinesScalar ((storage.insert s1 v1).insert s2 v2) slot value := by
  unfold StorageRefinesScalar at href ⊢
  rw [storageRead_insert_insert_of_ne storage s1 v1 s2 v2 slot hne1 hne2]
  exact href

/--
If scalar refinement holds after an insert at a different slot, then it held before the insert too.
This is the reverse direction — useful for backward reasoning.
-/
theorem refinesScalar_of_refinesScalar_insert {storage : Storage}
    {slot value insertSlot insertValue : UInt256}
    (h : StorageRefinesScalar (storage.insert insertSlot insertValue) slot value)
    (hne : slot ≠ insertSlot) :
    StorageRefinesScalar storage slot value := by
  unfold StorageRefinesScalar at h ⊢
  rwa [storageRead_insert_of_ne storage insertSlot slot insertValue hne] at h

/--
Scalar refinement is preserved through a chain of two `updateStorage` calls at different slots.
-/
theorem refinesScalar_updateStorage_chain {τ} {acc : Account τ}
    {slot value s1 v1 s2 v2 : UInt256}
    (href : StorageRefinesScalar acc.storage slot value)
    (hv1 : (v1 == default) = false)
    (hv2 : (v2 == default) = false)
    (hne1 : slot ≠ s1) (hne2 : slot ≠ s2) :
    StorageRefinesScalar ((acc.updateStorage s1 v1).updateStorage s2 v2).storage slot value := by
  have h1 := refinesScalar_updateStorage_of_ne_of_nonzero href hv1 hne1
  exact refinesScalar_updateStorage_of_ne_of_nonzero
    (acc := acc.updateStorage s1 v1)
    (href := h1) hv2 hne2

-- ============================================================================
-- A4.4: No-Collision Assumption Helpers
-- ============================================================================

/--
Two mapping base slots produce non-overlapping derived slots.
This is an unprovable separation assumption that callers assert based on
the Keccak non-collision property.
-/
def MappingSlotsSeparate (baseSlot1 baseSlot2 : UInt256) : Prop :=
  ∀ k1 k2, mappingSlot k1 baseSlot1 ≠ mappingSlot k2 baseSlot2

/--
A scalar slot is separate from all derived mapping slots of a given base slot.
-/
def ScalarMappingSeparate (scSlot baseSlot : UInt256) : Prop :=
  ∀ k, scSlot ≠ mappingSlot k baseSlot

/--
Symmetry: `MappingSlotsSeparate` is symmetric.
-/
theorem MappingSlotsSeparate.symm {b1 b2 : UInt256}
    (h : MappingSlotsSeparate b1 b2) :
    MappingSlotsSeparate b2 b1 :=
  fun k1 k2 => Ne.symm (h k2 k1)

/--
`ScalarMappingSeparate` reversed: if `scSlot` is separate from all mapping slots of `baseSlot`,
then no mapping slot of `baseSlot` equals `scSlot`.
-/
theorem ScalarMappingSeparate.ne_mappingSlot {scSlot baseSlot : UInt256}
    (h : ScalarMappingSeparate scSlot baseSlot) (k : UInt256) :
    mappingSlot k baseSlot ≠ scSlot :=
  Ne.symm (h k)

/--
If a scalar slot is separate from a mapping's derived slots, writing the scalar preserves
the full mapping refinement.
-/
theorem refinesMapping_preserved_of_scalarSeparate {τ} {acc : Account τ}
    {baseSlot : UInt256} {f : UInt256 → UInt256} {scSlot scValue : UInt256}
    (href : StorageRefinesMapping acc.storage baseSlot f)
    (hvalue : (scValue == default) = false)
    (hsep : ScalarMappingSeparate scSlot baseSlot) :
    StorageRefinesMapping (acc.updateStorage scSlot scValue).storage baseSlot f :=
  refinesMapping_preserved_of_ne_baseSlot href hvalue (fun k => hsep.ne_mappingSlot k)

/--
If two mappings have separate base slots, updating an entry in the second mapping preserves
the full refinement of the first mapping.
-/
theorem refinesMapping_preserved_of_mappingSeparate {τ} {acc : Account τ}
    {baseSlot1 baseSlot2 : UInt256} {f : UInt256 → UInt256} {key2 value2 : UInt256}
    (href : StorageRefinesMapping acc.storage baseSlot1 f)
    (hvalue : (value2 == default) = false)
    (hsep : MappingSlotsSeparate baseSlot1 baseSlot2) :
    StorageRefinesMapping (acc.updateStorage (mappingSlot key2 baseSlot2) value2).storage baseSlot1 f :=
  refinesMapping_preserved_of_ne_baseSlot href hvalue (fun k => hsep k key2)

/--
If a scalar slot is separate from a mapping, writing a mapping entry preserves the scalar refinement.
This is the dual of `refinesMapping_preserved_of_scalarSeparate`.
-/
theorem refinesScalar_preserved_of_scalarSeparate {τ} {acc : Account τ}
    {scSlot scValue baseSlot key valueM : UInt256}
    (href : StorageRefinesScalar acc.storage scSlot scValue)
    (hvalue : (valueM == default) = false)
    (hsep : ScalarMappingSeparate scSlot baseSlot) :
    StorageRefinesScalar (acc.updateStorage (mappingSlot key baseSlot) valueM).storage scSlot scValue :=
  refinesScalar_updateStorage_of_ne_of_nonzero href hvalue (hsep key)

/--
Two distinct scalar slots are trivially separate.
-/
theorem scalarSlots_ne_of_ne {s1 s2 : UInt256} (h : s1 ≠ s2) :
    scalarSlot s1 ≠ scalarSlot s2 :=
  h

/--
Mapping-key refinement is preserved when writing to a mapping slot derived from a
different base slot, given that the two base slots produce separate derived slots.
-/
theorem refinesMappingKey_preserved_of_mappingSeparate {τ} {acc : Account τ}
    {baseSlot1 key1 valueK baseSlot2 key2 valueW : UInt256}
    (href : StorageRefinesMappingKey acc.storage baseSlot1 key1 valueK)
    (hvalue : (valueW == default) = false)
    (hsep : MappingSlotsSeparate baseSlot1 baseSlot2) :
    StorageRefinesMappingKey (acc.updateStorage (mappingSlot key2 baseSlot2) valueW).storage baseSlot1 key1 valueK := by
  unfold StorageRefinesMappingKey mappingRead at href ⊢
  exact refinesScalar_updateStorage_of_ne_of_nonzero href hvalue (hsep key1 key2)

-- ============================================================================
-- A4.1 (new): Generic StorageRefines Invariant
-- ============================================================================

/-!
## Generic Storage Layout and Refinement

A `StorageLayout` describes which EVM storage slots correspond to which typed fields
in a Lean model. `StorageLayoutWellFormed` ensures all slots are pairwise separate.
`GenericStorageRefines` bundles refinement of every field in the layout into a single
proposition.
-/

/--
A scalar field: one storage slot holding a single `UInt256` value.
-/
structure ScalarFieldSpec where
  slot : UInt256
  name : String
deriving Repr

/--
A mapping field: a base slot whose derived slots `keccak256(key ++ baseSlot)` hold values.
-/
structure MappingFieldSpec where
  baseSlot : UInt256
  name : String
deriving Repr

/--
Describes the storage layout of a Solidity contract: which slots are scalars and which
are mapping base slots.
-/
structure StorageLayout where
  scalarFields  : List ScalarFieldSpec
  mappingFields : List MappingFieldSpec
deriving Repr

/--
A storage layout is well-formed when:
1. All scalar slots are pairwise distinct.
2. All mapping base slots are pairwise distinct.
3. Every scalar slot is separate from every mapping's derived slots.
-/
def StorageLayoutWellFormed (layout : StorageLayout) : Prop :=
  -- All scalar slots are pairwise distinct
  (layout.scalarFields.map (·.slot)).Nodup ∧
  -- All mapping base slots are pairwise distinct
  (layout.mappingFields.map (·.baseSlot)).Nodup ∧
  -- Scalar slots don't collide with any mapping-derived slots
  ∀ sf ∈ layout.scalarFields, ∀ mf ∈ layout.mappingFields,
    ScalarMappingSeparate sf.slot mf.baseSlot

/--
A storage layout is well-formed with mapping separation when, in addition to
`StorageLayoutWellFormed`, all pairs of distinct mapping base slots produce
non-overlapping derived slots.
-/
def StorageLayoutFullySeparated (layout : StorageLayout) : Prop :=
  StorageLayoutWellFormed layout ∧
  -- Distinct mapping base slots produce separate derived slots
  ∀ mf1 ∈ layout.mappingFields, ∀ mf2 ∈ layout.mappingFields,
    mf1.baseSlot ≠ mf2.baseSlot → MappingSlotsSeparate mf1.baseSlot mf2.baseSlot

/--
`GenericStorageRefines` asserts that raw EVM storage refines a typed model according
to a layout. The caller provides:
- `scalarVal`: a function mapping each scalar slot to its expected value.
- `mappingFn`: a function mapping each mapping base slot to its expected key→value function.

The proposition asserts that every scalar field reads back its expected value and every
mapping field refines through its expected function.
-/
def GenericStorageRefines
    (storage : Storage)
    (layout : StorageLayout)
    (scalarVal : UInt256 → UInt256)
    (mappingFn : UInt256 → UInt256 → UInt256) : Prop :=
  (∀ sf ∈ layout.scalarFields,
    StorageRefinesScalar storage sf.slot (scalarVal sf.slot)) ∧
  (∀ mf ∈ layout.mappingFields,
    StorageRefinesMapping storage mf.baseSlot (mappingFn mf.baseSlot))

/--
Extract the scalar refinement for a specific field from a `GenericStorageRefines` bundle.
-/
theorem GenericStorageRefines.scalar
    {storage : Storage} {layout : StorageLayout}
    {scalarVal : UInt256 → UInt256} {mappingFn : UInt256 → UInt256 → UInt256}
    (h : GenericStorageRefines storage layout scalarVal mappingFn)
    {sf : ScalarFieldSpec} (hmem : sf ∈ layout.scalarFields) :
    StorageRefinesScalar storage sf.slot (scalarVal sf.slot) :=
  h.1 sf hmem

/--
Extract the mapping refinement for a specific field from a `GenericStorageRefines` bundle.
-/
theorem GenericStorageRefines.mapping
    {storage : Storage} {layout : StorageLayout}
    {scalarVal : UInt256 → UInt256} {mappingFn : UInt256 → UInt256 → UInt256}
    (h : GenericStorageRefines storage layout scalarVal mappingFn)
    {mf : MappingFieldSpec} (hmem : mf ∈ layout.mappingFields) :
    StorageRefinesMapping storage mf.baseSlot (mappingFn mf.baseSlot) :=
  h.2 mf hmem

-- ============================================================================
-- A4.2: World-State Refinement
-- ============================================================================

/-!
## World-State Refinement

`WorldRefines` relates the EVM execution state to a typed world-state model.
Currently a placeholder — expand when the Aeneas `WorldState` type gains richer fields
(e.g., contract balance, block info, etc.).
-/

/--
World-state refinement: the EVM state is consistent with a typed world-state model.
Currently a `True` placeholder; extend when `WorldState` gains concrete fields.
-/
def WorldRefines {τ} (_self : State τ) : Prop :=
  True

/--
The initial (default) state trivially satisfies world refinement.
-/
theorem worldRefines_initial {τ} (self : State τ) : WorldRefines self :=
  trivial

/--
An `sstore` operation does not affect world refinement (which currently tracks no
storage-dependent world properties).
-/
theorem worldRefines_preserved_by_sstore {τ} (self : State τ)
    (slot value : UInt256)
    (_h : WorldRefines self) :
    WorldRefines (State.sstore self slot value) :=
  trivial

-- ============================================================================
-- A4.3: Layout-Aware Preservation Theorem Infrastructure
-- ============================================================================

/-!
## Layout-Aware Preservation Theorems

These theorems show that an `sstore` at a slot unrelated to the layout's fields
preserves the entire `GenericStorageRefines` invariant. They use
`StorageLayoutWellFormed` to derive the necessary separation facts.
-/

/--
If we write (via raw `Storage.insert`) to a slot that is not any scalar field's slot,
every scalar refinement in the layout is preserved.
-/
theorem allScalars_preserved_by_insert
    {storage : Storage}
    {layout : StorageLayout}
    {scalarVal : UInt256 → UInt256}
    {slotW valueW : UInt256}
    (hscalars : ∀ sf ∈ layout.scalarFields,
      StorageRefinesScalar storage sf.slot (scalarVal sf.slot))
    (hne : ∀ sf ∈ layout.scalarFields, sf.slot ≠ slotW) :
    ∀ sf ∈ layout.scalarFields,
      StorageRefinesScalar (storage.insert slotW valueW) sf.slot (scalarVal sf.slot) := by
  intro sf hmem
  exact refinesScalar_preserved_of_ne_slot (hscalars sf hmem) (hne sf hmem)

/--
If we write (via `Account.updateStorage` with nonzero value) to a slot that is not
any scalar field's slot, every scalar refinement in the layout is preserved.
-/
theorem allScalars_preserved_by_updateStorage {τ} {acc : Account τ}
    {layout : StorageLayout}
    {scalarVal : UInt256 → UInt256}
    {slotW valueW : UInt256}
    (hscalars : ∀ sf ∈ layout.scalarFields,
      StorageRefinesScalar acc.storage sf.slot (scalarVal sf.slot))
    (hvalue : (valueW == default) = false)
    (hne : ∀ sf ∈ layout.scalarFields, sf.slot ≠ slotW) :
    ∀ sf ∈ layout.scalarFields,
      StorageRefinesScalar (acc.updateStorage slotW valueW).storage sf.slot (scalarVal sf.slot) := by
  intro sf hmem
  exact refinesScalar_updateStorage_of_ne_of_nonzero (hscalars sf hmem) hvalue (hne sf hmem)

/--
If we write (via `Account.updateStorage` with nonzero value) to a slot that is not
any mapping-derived slot for any mapping in the layout, every mapping refinement is preserved.
The caller must supply the stronger hypothesis: for every mapping field, no derived slot
of that mapping equals the write target.
-/
theorem allMappings_preserved_by_updateStorage {τ} {acc : Account τ}
    {layout : StorageLayout}
    {mappingFn : UInt256 → UInt256 → UInt256}
    {slotW valueW : UInt256}
    (hmappings : ∀ mf ∈ layout.mappingFields,
      StorageRefinesMapping acc.storage mf.baseSlot (mappingFn mf.baseSlot))
    (hvalue : (valueW == default) = false)
    (hsep : ∀ mf ∈ layout.mappingFields, ∀ k, mappingSlot k mf.baseSlot ≠ slotW) :
    ∀ mf ∈ layout.mappingFields,
      StorageRefinesMapping (acc.updateStorage slotW valueW).storage mf.baseSlot (mappingFn mf.baseSlot) := by
  intro mf hmem
  exact refinesMapping_preserved_of_ne_baseSlot (hmappings mf hmem) hvalue (hsep mf hmem)

/--
Writing a scalar value at `slotW` preserves the full `GenericStorageRefines` when:
1. `slotW` is not any other scalar field's slot.
2. `slotW` does not collide with any mapping-derived slot.

This is the main preservation theorem for scalar writes in a well-formed layout.
-/
theorem genericRefines_preserved_by_scalar_updateStorage {τ} {acc : Account τ}
    {layout : StorageLayout}
    {scalarVal : UInt256 → UInt256}
    {mappingFn : UInt256 → UInt256 → UInt256}
    {slotW valueW : UInt256}
    (href : GenericStorageRefines acc.storage layout scalarVal mappingFn)
    (hvalue : (valueW == default) = false)
    (hne_scalars : ∀ sf ∈ layout.scalarFields, sf.slot ≠ slotW)
    (hne_mappings : ∀ mf ∈ layout.mappingFields, ∀ k, mappingSlot k mf.baseSlot ≠ slotW) :
    GenericStorageRefines (acc.updateStorage slotW valueW).storage layout scalarVal mappingFn :=
  ⟨allScalars_preserved_by_updateStorage href.1 hvalue hne_scalars,
   allMappings_preserved_by_updateStorage href.2 hvalue hne_mappings⟩

/--
Specialised preservation: writing a scalar field that belongs to the layout preserves
the refinement of all *other* scalar fields and all mapping fields, assuming
`StorageLayoutWellFormed`. The written field itself gets a new value.
-/
theorem genericRefines_update_scalar {τ} {acc : Account τ}
    {layout : StorageLayout}
    {scalarVal : UInt256 → UInt256}
    {mappingFn : UInt256 → UInt256 → UInt256}
    {sf₀ : ScalarFieldSpec} {newVal : UInt256}
    (href : GenericStorageRefines acc.storage layout scalarVal mappingFn)
    (hwf : StorageLayoutWellFormed layout)
    (hmem : sf₀ ∈ layout.scalarFields)
    (hvalue : (newVal == default) = false) :
    GenericStorageRefines
      (acc.updateStorage sf₀.slot newVal).storage
      layout
      (Function.update scalarVal sf₀.slot newVal)
      mappingFn := by
  constructor
  · -- Scalar fields
    intro sf hsfmem
    by_cases heq : sf.slot = sf₀.slot
    · simp [Function.update, heq]
      exact refinesScalar_updateStorage_same_of_nonzero hvalue
    · simp [Function.update, heq]
      exact refinesScalar_updateStorage_of_ne_of_nonzero (href.1 sf hsfmem) hvalue heq
  · -- Mapping fields
    intro mf hmfmem
    have hsep : ScalarMappingSeparate sf₀.slot mf.baseSlot :=
      hwf.2.2 sf₀ hmem mf hmfmem
    exact refinesMapping_preserved_of_scalarSeparate (href.2 mf hmfmem) hvalue hsep

/--
If we `sstore` at a slot that is not any scalar field's slot in the layout, all
scalar refinements are preserved. This is a convenience wrapper that extracts the
separation from a direct slot-inequality hypothesis.

This is the "unrelated sstore" version for scalars: the written slot does not belong
to any scalar field in the layout.
-/
theorem refinesScalar_preserved_by_unrelated_sstore {τ} {acc : Account τ}
    {layout : StorageLayout}
    {scalarVal : UInt256 → UInt256}
    {slotW valueW : UInt256}
    (hscalars : ∀ sf ∈ layout.scalarFields,
      StorageRefinesScalar acc.storage sf.slot (scalarVal sf.slot))
    (hvalue : (valueW == default) = false)
    (hne : ∀ sf ∈ layout.scalarFields, sf.slot ≠ slotW) :
    ∀ sf ∈ layout.scalarFields,
      StorageRefinesScalar (acc.updateStorage slotW valueW).storage sf.slot (scalarVal sf.slot) :=
  allScalars_preserved_by_updateStorage hscalars hvalue hne

/--
If we `sstore` at a slot that is not any mapping-derived slot for any mapping in
the layout, all mapping refinements are preserved.

This is the "unrelated sstore" version for mappings: the written slot is not
`mappingSlot k mf.baseSlot` for any key `k` and any mapping field `mf` in the layout.
-/
theorem refinesMapping_preserved_by_unrelated_sstore {τ} {acc : Account τ}
    {layout : StorageLayout}
    {mappingFn : UInt256 → UInt256 → UInt256}
    {slotW valueW : UInt256}
    (hmappings : ∀ mf ∈ layout.mappingFields,
      StorageRefinesMapping acc.storage mf.baseSlot (mappingFn mf.baseSlot))
    (hvalue : (valueW == default) = false)
    (hsep : ∀ mf ∈ layout.mappingFields, ∀ k, mappingSlot k mf.baseSlot ≠ slotW) :
    ∀ mf ∈ layout.mappingFields,
      StorageRefinesMapping (acc.updateStorage slotW valueW).storage mf.baseSlot (mappingFn mf.baseSlot) :=
  allMappings_preserved_by_updateStorage hmappings hvalue hsep

/--
Combining both preservation results: if we `sstore` at a slot unrelated to all fields
in a well-formed layout, the full `GenericStorageRefines` invariant is preserved.
-/
theorem genericRefines_preserved_by_unrelated_sstore {τ} {acc : Account τ}
    {layout : StorageLayout}
    {scalarVal : UInt256 → UInt256}
    {mappingFn : UInt256 → UInt256 → UInt256}
    {slotW valueW : UInt256}
    (href : GenericStorageRefines acc.storage layout scalarVal mappingFn)
    (hvalue : (valueW == default) = false)
    (hne_scalars : ∀ sf ∈ layout.scalarFields, sf.slot ≠ slotW)
    (hne_mappings : ∀ mf ∈ layout.mappingFields, ∀ k, mappingSlot k mf.baseSlot ≠ slotW) :
    GenericStorageRefines (acc.updateStorage slotW valueW).storage layout scalarVal mappingFn :=
  genericRefines_preserved_by_scalar_updateStorage href hvalue hne_scalars hne_mappings

/--
When the layout is well-formed and we write to a scalar slot that belongs to the layout,
the separation facts for mappings follow from `StorageLayoutWellFormed`.
This extracts the mapping separation from the well-formedness hypothesis.
-/
theorem StorageLayoutWellFormed.scalar_mapping_sep
    {layout : StorageLayout}
    (hwf : StorageLayoutWellFormed layout)
    {sf : ScalarFieldSpec}
    (hsfmem : sf ∈ layout.scalarFields) :
    ∀ mf ∈ layout.mappingFields, ∀ k, mappingSlot k mf.baseSlot ≠ sf.slot :=
  fun mf hmfmem k => (hwf.2.2 sf hsfmem mf hmfmem).ne_mappingSlot k

-- ============================================================================
-- Mapping Update Refinement Through Layout
-- ============================================================================

/-!
## Mapping Update Refinement Through Layout

These theorems show that updating a mapping entry while the layout is fully separated
preserves the entire `GenericStorageRefines` invariant, with the affected mapping's
function updated via `Function.update`.
-/

/--
When writing to a mapping entry at `mf₀.baseSlot` for key `k` with value `v`, the
`GenericStorageRefines` is preserved with `mappingFn` updated so that
`mappingFn mf₀.baseSlot` becomes `Function.update (mappingFn mf₀.baseSlot) k v`.
All other scalar and mapping refinements are preserved.

Requires `StorageLayoutFullySeparated` to derive mapping-mapping separation for
distinct base slots.
-/
theorem genericRefines_update_mapping_entry {τ} {acc : Account τ}
    {layout : StorageLayout}
    {scalarVal : UInt256 → UInt256}
    {mappingFn : UInt256 → UInt256 → UInt256}
    {mf₀ : MappingFieldSpec} {k v : UInt256}
    (href : GenericStorageRefines acc.storage layout scalarVal mappingFn)
    (hfs : StorageLayoutFullySeparated layout)
    (hmem : mf₀ ∈ layout.mappingFields)
    (hvalue : (v == default) = false)
    (hkec_inj : ∀ {other : UInt256}, other ≠ k → mappingSlot other mf₀.baseSlot ≠ mappingSlot k mf₀.baseSlot) :
    GenericStorageRefines
      (acc.updateStorage (mappingSlot k mf₀.baseSlot) v).storage
      layout
      scalarVal
      (Function.update mappingFn mf₀.baseSlot (Function.update (mappingFn mf₀.baseSlot) k v)) := by
  have hwf := hfs.1
  constructor
  · -- Scalar fields: writing to a mapping slot preserves all scalar refinements
    intro sf hsfmem
    have hsep : ScalarMappingSeparate sf.slot mf₀.baseSlot := hwf.2.2 sf hsfmem mf₀ hmem
    exact refinesScalar_preserved_of_scalarSeparate (href.1 sf hsfmem) hvalue hsep
  · -- Mapping fields
    intro mf hmfmem
    by_cases hbs : mf.baseSlot = mf₀.baseSlot
    · -- Same base slot: update the function
      simp [Function.update, hbs]
      rw [← hbs]
      exact refinesMapping_updateStorage_of_nonzero
        (hbs ▸ href.2 mf hmfmem) hvalue (fun hother => hbs ▸ hkec_inj hother)
    · -- Different base slot: mapping is preserved
      simp [Function.update, hbs]
      have hsep : MappingSlotsSeparate mf.baseSlot mf₀.baseSlot :=
        hfs.2 mf hmfmem mf₀ hmem hbs
      exact refinesMapping_preserved_of_mappingSeparate (href.2 mf hmfmem) hvalue hsep

/--
If we `sstore` at a mapping-derived slot `mappingSlot k mf₀.baseSlot` and the layout
is fully separated, the `GenericStorageRefines` updates accordingly: the mapping function
for `mf₀.baseSlot` is updated at key `k`, and everything else is preserved.
-/
theorem genericRefines_preserved_by_mapping_sstore {τ} {acc : Account τ}
    {layout : StorageLayout}
    {scalarVal : UInt256 → UInt256}
    {mappingFn : UInt256 → UInt256 → UInt256}
    {mf₀ : MappingFieldSpec} {k v : UInt256}
    (href : GenericStorageRefines acc.storage layout scalarVal mappingFn)
    (hfs : StorageLayoutFullySeparated layout)
    (hmem : mf₀ ∈ layout.mappingFields)
    (hvalue : (v == default) = false)
    (hkec_inj : ∀ {other : UInt256}, other ≠ k → mappingSlot other mf₀.baseSlot ≠ mappingSlot k mf₀.baseSlot) :
    GenericStorageRefines
      (acc.updateStorage (mappingSlot k mf₀.baseSlot) v).storage
      layout
      scalarVal
      (Function.update mappingFn mf₀.baseSlot (Function.update (mappingFn mf₀.baseSlot) k v)) :=
  genericRefines_update_mapping_entry href hfs hmem hvalue hkec_inj

-- ============================================================================
-- Composable Multi-Step Refinement
-- ============================================================================

/-!
## Composable Multi-Step Refinement

Infrastructure for composing multiple storage updates. These theorems allow generated
preservation proofs to chain multiple storage writes within a single function.
-/

/--
If we have two sequential scalar updates at different layout slots, the composition
preserves `GenericStorageRefines` with both `scalarVal` updates applied.

The second update is applied on top of the first, so the resulting `scalarVal` is:
`Function.update (Function.update scalarVal sf₁.slot v₁) sf₂.slot v₂`.
-/
theorem genericRefines_compose_scalar_updates {τ} {acc : Account τ}
    {layout : StorageLayout}
    {scalarVal : UInt256 → UInt256}
    {mappingFn : UInt256 → UInt256 → UInt256}
    {sf₁ sf₂ : ScalarFieldSpec} {v₁ v₂ : UInt256}
    (href : GenericStorageRefines acc.storage layout scalarVal mappingFn)
    (hwf : StorageLayoutWellFormed layout)
    (hmem₁ : sf₁ ∈ layout.scalarFields)
    (hmem₂ : sf₂ ∈ layout.scalarFields)
    (hv₁ : (v₁ == default) = false)
    (hv₂ : (v₂ == default) = false)
    (_hne : sf₁.slot ≠ sf₂.slot) :
    GenericStorageRefines
      ((acc.updateStorage sf₁.slot v₁).updateStorage sf₂.slot v₂).storage
      layout
      (Function.update (Function.update scalarVal sf₁.slot v₁) sf₂.slot v₂)
      mappingFn := by
  have h₁ := genericRefines_update_scalar href hwf hmem₁ hv₁
  exact genericRefines_update_scalar (acc := acc.updateStorage sf₁.slot v₁) h₁ hwf hmem₂ hv₂

/--
If we have a scalar update followed by a mapping update, the composition preserves
`GenericStorageRefines`. The scalar value is updated via `Function.update` on `scalarVal`,
and the mapping function is updated via nested `Function.update` on `mappingFn`.
-/
theorem genericRefines_compose_mixed_updates {τ} {acc : Account τ}
    {layout : StorageLayout}
    {scalarVal : UInt256 → UInt256}
    {mappingFn : UInt256 → UInt256 → UInt256}
    {sf₀ : ScalarFieldSpec} {vS : UInt256}
    {mf₀ : MappingFieldSpec} {k vM : UInt256}
    (href : GenericStorageRefines acc.storage layout scalarVal mappingFn)
    (hfs : StorageLayoutFullySeparated layout)
    (hsfmem : sf₀ ∈ layout.scalarFields)
    (hmfmem : mf₀ ∈ layout.mappingFields)
    (hvS : (vS == default) = false)
    (hvM : (vM == default) = false)
    (hkec_inj : ∀ {other : UInt256}, other ≠ k → mappingSlot other mf₀.baseSlot ≠ mappingSlot k mf₀.baseSlot) :
    GenericStorageRefines
      ((acc.updateStorage sf₀.slot vS).updateStorage (mappingSlot k mf₀.baseSlot) vM).storage
      layout
      (Function.update scalarVal sf₀.slot vS)
      (Function.update mappingFn mf₀.baseSlot (Function.update (mappingFn mf₀.baseSlot) k vM)) := by
  have h₁ := genericRefines_update_scalar href hfs.1 hsfmem hvS
  exact genericRefines_update_mapping_entry (acc := acc.updateStorage sf₀.slot vS) h₁ hfs hmfmem hvM hkec_inj

/--
If we have a mapping update followed by a scalar update, the composition preserves
`GenericStorageRefines`. The mapping function is updated first, then the scalar value.
-/
theorem genericRefines_compose_mapping_then_scalar {τ} {acc : Account τ}
    {layout : StorageLayout}
    {scalarVal : UInt256 → UInt256}
    {mappingFn : UInt256 → UInt256 → UInt256}
    {mf₀ : MappingFieldSpec} {k vM : UInt256}
    {sf₀ : ScalarFieldSpec} {vS : UInt256}
    (href : GenericStorageRefines acc.storage layout scalarVal mappingFn)
    (hfs : StorageLayoutFullySeparated layout)
    (hmfmem : mf₀ ∈ layout.mappingFields)
    (hsfmem : sf₀ ∈ layout.scalarFields)
    (hvM : (vM == default) = false)
    (hvS : (vS == default) = false)
    (hkec_inj : ∀ {other : UInt256}, other ≠ k → mappingSlot other mf₀.baseSlot ≠ mappingSlot k mf₀.baseSlot) :
    GenericStorageRefines
      ((acc.updateStorage (mappingSlot k mf₀.baseSlot) vM).updateStorage sf₀.slot vS).storage
      layout
      (Function.update scalarVal sf₀.slot vS)
      (Function.update mappingFn mf₀.baseSlot (Function.update (mappingFn mf₀.baseSlot) k vM)) := by
  have h₁ := genericRefines_update_mapping_entry href hfs hmfmem hvM hkec_inj
  exact genericRefines_update_scalar
    (acc := acc.updateStorage (mappingSlot k mf₀.baseSlot) vM) h₁ hfs.1 hsfmem hvS

-- ============================================================================
-- Convenience Extraction Theorems
-- ============================================================================

/-!
## Convenience Extraction Theorems

Extractors from `GenericStorageRefines` for common proof patterns. These allow
generated sidecars to extract specific equalities without manually destructuring
the `GenericStorageRefines` bundle.
-/

/--
Extract the specific scalar refinement equality for a given slot from
`GenericStorageRefines`: `storageRead storage sf.slot = scalarVal sf.slot`.
-/
theorem genericRefines_scalar_eq
    {storage : Storage} {layout : StorageLayout}
    {scalarVal : UInt256 → UInt256} {mappingFn : UInt256 → UInt256 → UInt256}
    (h : GenericStorageRefines storage layout scalarVal mappingFn)
    {sf : ScalarFieldSpec} (hmem : sf ∈ layout.scalarFields) :
    storageRead storage sf.slot = scalarVal sf.slot :=
  h.scalar hmem

/--
Extract the specific mapping refinement equality for a given base slot and key from
`GenericStorageRefines`: `mappingRead storage mf.baseSlot key = mappingFn mf.baseSlot key`.
-/
theorem genericRefines_mapping_eq
    {storage : Storage} {layout : StorageLayout}
    {scalarVal : UInt256 → UInt256} {mappingFn : UInt256 → UInt256 → UInt256}
    (h : GenericStorageRefines storage layout scalarVal mappingFn)
    {mf : MappingFieldSpec} (hmem : mf ∈ layout.mappingFields)
    (key : UInt256) :
    mappingRead storage mf.baseSlot key = mappingFn mf.baseSlot key :=
  h.mapping hmem key

/--
Extract the scalar value at a specific slot directly from `GenericStorageRefines`,
given a slot value rather than a `ScalarFieldSpec`. Useful when the caller knows the
slot number but not the spec structure.
-/
theorem genericRefines_scalar_val_eq
    {storage : Storage} {layout : StorageLayout}
    {scalarVal : UInt256 → UInt256} {mappingFn : UInt256 → UInt256 → UInt256}
    (h : GenericStorageRefines storage layout scalarVal mappingFn)
    {slot : UInt256}
    (hmem : ∃ sf ∈ layout.scalarFields, sf.slot = slot) :
    storageRead storage slot = scalarVal slot := by
  obtain ⟨sf, hsfmem, hslot⟩ := hmem
  rw [← hslot]
  exact h.scalar hsfmem

/--
Extract the mapping value at a specific base slot and key directly from
`GenericStorageRefines`, given slot values rather than a `MappingFieldSpec`.
-/
theorem genericRefines_mapping_val_eq
    {storage : Storage} {layout : StorageLayout}
    {scalarVal : UInt256 → UInt256} {mappingFn : UInt256 → UInt256 → UInt256}
    (h : GenericStorageRefines storage layout scalarVal mappingFn)
    {baseSlot : UInt256}
    (hmem : ∃ mf ∈ layout.mappingFields, mf.baseSlot = baseSlot)
    (key : UInt256) :
    mappingRead storage baseSlot key = mappingFn baseSlot key := by
  obtain ⟨mf, hmfmem, hbs⟩ := hmem
  rw [← hbs]
  exact h.mapping hmfmem key

-- ============================================================================
-- Execution-Step Refinement Preservation
-- ============================================================================

/-!
## Execution-Step Refinement Preservation

These theorems bridge the gap between "this function performs these storage writes"
and "the refinement invariant is preserved". They connect individual SSTORE
execution steps (scalar writes, mapping writes) and chains of writes to the
`GenericStorageRefines` invariant.
-/

/--
After a single scalar write at a known layout slot, `GenericStorageRefines` holds
with the `scalarVal` function updated at the written slot. This is the canonical
"execution-step" theorem for scalar SSTOREs.
-/
theorem genericRefines_after_scalar_write
    (layout : StorageLayout)
    (hwf : StorageLayoutWellFormed layout)
    {τ} {acc : Account τ}
    {scalarVal : UInt256 → UInt256}
    {mappingFn : UInt256 → UInt256 → UInt256}
    (href : GenericStorageRefines acc.storage layout scalarVal mappingFn)
    (sf : ScalarFieldSpec) (hmem : sf ∈ layout.scalarFields)
    (newVal : UInt256) (hnonzero : (newVal == default) = false) :
    GenericStorageRefines
      (acc.updateStorage sf.slot newVal).storage
      layout
      (Function.update scalarVal sf.slot newVal)
      mappingFn :=
  genericRefines_update_scalar href hwf hmem hnonzero

/--
After a single mapping write at a known layout base slot for a given key,
`GenericStorageRefines` holds with the `mappingFn` updated at the written
base slot and key. This is the canonical "execution-step" theorem for mapping
SSTOREs.

Requires `StorageLayoutFullySeparated` for cross-mapping separation and a
local Keccak injectivity hypothesis for the written mapping.
-/
theorem genericRefines_after_mapping_write
    (layout : StorageLayout)
    (hsep : StorageLayoutFullySeparated layout)
    {τ} {acc : Account τ}
    {scalarVal : UInt256 → UInt256}
    {mappingFn : UInt256 → UInt256 → UInt256}
    (href : GenericStorageRefines acc.storage layout scalarVal mappingFn)
    (mf : MappingFieldSpec) (hmem : mf ∈ layout.mappingFields)
    (key newVal : UInt256) (hnonzero : (newVal == default) = false)
    (hinj : ∀ k, k ≠ key → mappingSlot k mf.baseSlot ≠ mappingSlot key mf.baseSlot) :
    GenericStorageRefines
      (acc.updateStorage (mappingSlot key mf.baseSlot) newVal).storage
      layout
      scalarVal
      (Function.update mappingFn mf.baseSlot
        (Function.update (mappingFn mf.baseSlot) key newVal)) :=
  genericRefines_update_mapping_entry href hsep hmem hnonzero (fun {other} h => hinj other h)

-- ============================================================================
-- Chain of Writes (applyWrites)
-- ============================================================================

/-!
## Chain of Writes

`applyWrites` applies a list of `(slot, value)` pairs to an account via successive
`updateStorage` calls. The preservation theorems show that `GenericStorageRefines`
is maintained through such chains under appropriate separation hypotheses.
-/

/--
Apply a sequence of `(slot, value)` storage writes to an account.
The writes are applied left-to-right: the first pair in the list is written first.
-/
def applyWrites {τ} (acc : Account τ) : List (UInt256 × UInt256) → Account τ
  | [] => acc
  | (slot, val) :: rest => applyWrites (acc.updateStorage slot val) rest

/--
`applyWrites` on an empty list is the identity.
-/
@[simp]
theorem applyWrites_nil {τ} (acc : Account τ) : applyWrites acc [] = acc := rfl

/--
`applyWrites` on a cons unfolds to a recursive call on the tail after one `updateStorage`.
-/
@[simp]
theorem applyWrites_cons {τ} (acc : Account τ) (slot val : UInt256)
    (rest : List (UInt256 × UInt256)) :
    applyWrites acc ((slot, val) :: rest) = applyWrites (acc.updateStorage slot val) rest := rfl

/--
A predicate asserting that every write in the list targets a slot that is completely
unrelated to the layout: not any scalar slot and not any mapping-derived slot. This
is the simplest separation condition for chain preservation.
-/
def WritesUnrelatedToLayout (layout : StorageLayout) (writes : List (UInt256 × UInt256)) : Prop :=
  ∀ p ∈ writes,
    (∀ sf ∈ layout.scalarFields, sf.slot ≠ p.1) ∧
    (∀ mf ∈ layout.mappingFields, ∀ k, mappingSlot k mf.baseSlot ≠ p.1)

/--
A predicate asserting that every value written in the list is nonzero.
Required because `Account.updateStorage` branches on the zero check.
-/
def WritesAllNonzero (writes : List (UInt256 × UInt256)) : Prop :=
  ∀ p ∈ writes, (p.2 == default) = false

/--
`WritesUnrelatedToLayout` on an empty list is trivially true.
-/
theorem writesUnrelated_nil (layout : StorageLayout) :
    WritesUnrelatedToLayout layout [] := by
  intro p hp; simp at hp

/--
`WritesAllNonzero` on an empty list is trivially true.
-/
theorem writesNonzero_nil : WritesAllNonzero [] := by
  intro p hp; simp at hp

/--
`WritesUnrelatedToLayout` on a cons: the head is unrelated and the tail satisfies
the predicate.
-/
theorem writesUnrelated_cons {layout : StorageLayout}
    {slot val : UInt256} {rest : List (UInt256 × UInt256)}
    (hhead_sc : ∀ sf ∈ layout.scalarFields, sf.slot ≠ slot)
    (hhead_mp : ∀ mf ∈ layout.mappingFields, ∀ k, mappingSlot k mf.baseSlot ≠ slot)
    (htail : WritesUnrelatedToLayout layout rest) :
    WritesUnrelatedToLayout layout ((slot, val) :: rest) := by
  intro p hp
  simp only [List.mem_cons] at hp
  rcases hp with rfl | htl
  · exact ⟨hhead_sc, hhead_mp⟩
  · exact htail p htl

/--
`WritesAllNonzero` on a cons: the head value is nonzero and the tail satisfies the
predicate.
-/
theorem writesNonzero_cons {slot val : UInt256} {rest : List (UInt256 × UInt256)}
    (hhead : (val == default) = false)
    (htail : WritesAllNonzero rest) :
    WritesAllNonzero ((slot, val) :: rest) := by
  intro p hp
  simp only [List.mem_cons] at hp
  rcases hp with rfl | htl
  · exact hhead
  · exact htail p htl

/--
`GenericStorageRefines` is preserved through a chain of writes when every write
targets a slot unrelated to the layout (not any scalar slot and not any
mapping-derived slot) and every written value is nonzero.

This is the main inductive chain-preservation theorem. It says: if the refinement
holds before the writes, and the writes don't touch any layout-relevant slots,
then the refinement still holds after all writes.
-/
theorem genericRefines_chain_writes {τ} {acc : Account τ}
    {layout : StorageLayout}
    {scalarVal : UInt256 → UInt256}
    {mappingFn : UInt256 → UInt256 → UInt256}
    (href : GenericStorageRefines acc.storage layout scalarVal mappingFn)
    (writes : List (UInt256 × UInt256))
    (hunrel : WritesUnrelatedToLayout layout writes)
    (hnz : WritesAllNonzero writes) :
    GenericStorageRefines (applyWrites acc writes).storage layout scalarVal mappingFn := by
  induction writes generalizing acc with
  | nil => exact href
  | cons w rest ih =>
    have hmem_head : w ∈ w :: rest := List.mem_cons_self ..
    have hw := hunrel w hmem_head
    have hvw := hnz w hmem_head
    have hunrel' : WritesUnrelatedToLayout layout rest :=
      fun p hp => hunrel p (List.mem_cons.mpr (Or.inr hp))
    have hnz' : WritesAllNonzero rest :=
      fun p hp => hnz p (List.mem_cons.mpr (Or.inr hp))
    have href' := genericRefines_preserved_by_unrelated_sstore href hvw hw.1 hw.2
    exact ih href' hunrel' hnz'

/--
Specialized chain theorem: applying a single-element write list is the same as
a single `updateStorage`.
-/
theorem genericRefines_chain_singleton {τ} {acc : Account τ}
    {layout : StorageLayout}
    {scalarVal : UInt256 → UInt256}
    {mappingFn : UInt256 → UInt256 → UInt256}
    (href : GenericStorageRefines acc.storage layout scalarVal mappingFn)
    {slot val : UInt256}
    (hne_sc : ∀ sf ∈ layout.scalarFields, sf.slot ≠ slot)
    (hne_mp : ∀ mf ∈ layout.mappingFields, ∀ k, mappingSlot k mf.baseSlot ≠ slot)
    (hnz : (val == default) = false) :
    GenericStorageRefines (applyWrites acc [(slot, val)]).storage layout scalarVal mappingFn := by
  exact genericRefines_chain_writes href [(slot, val)]
    (writesUnrelated_cons hne_sc hne_mp (writesUnrelated_nil layout))
    (writesNonzero_cons hnz writesNonzero_nil)

/--
Concatenating two write lists: `applyWrites acc (ws₁ ++ ws₂)` is the same as
applying `ws₁` first and then `ws₂`.
-/
theorem applyWrites_append {τ} (acc : Account τ) (ws₁ ws₂ : List (UInt256 × UInt256)) :
    applyWrites acc (ws₁ ++ ws₂) = applyWrites (applyWrites acc ws₁) ws₂ := by
  induction ws₁ generalizing acc with
  | nil => rfl
  | cons w rest ih =>
    simp only [List.cons_append]
    exact ih (acc.updateStorage w.1 w.2)

/--
Chain composition: if refinement is preserved through `ws₁` and then through `ws₂`,
it is preserved through `ws₁ ++ ws₂`.
-/
theorem genericRefines_chain_append {τ} {acc : Account τ}
    {layout : StorageLayout}
    {scalarVal : UInt256 → UInt256}
    {mappingFn : UInt256 → UInt256 → UInt256}
    (href : GenericStorageRefines acc.storage layout scalarVal mappingFn)
    (ws₁ ws₂ : List (UInt256 × UInt256))
    (hunrel : WritesUnrelatedToLayout layout (ws₁ ++ ws₂))
    (hnz : WritesAllNonzero (ws₁ ++ ws₂)) :
    GenericStorageRefines (applyWrites acc (ws₁ ++ ws₂)).storage layout scalarVal mappingFn := by
  exact genericRefines_chain_writes href (ws₁ ++ ws₂) hunrel hnz

-- ============================================================================
-- Scalar Write Chain with Tracked Updates
-- ============================================================================

/-!
## Scalar Write Chain with Tracked Updates

When a chain of writes targets known scalar slots in the layout, we can track
the accumulated `Function.update`s to `scalarVal` through the chain. This is
useful for functions that perform multiple scalar SSTOREs.
-/

/--
A single scalar write in the layout: the slot, value, and membership proof.
-/
structure ScalarWrite (layout : StorageLayout) where
  sf : ScalarFieldSpec
  val : UInt256
  hmem : sf ∈ layout.scalarFields
  hnonzero : (val == default) = false

/--
Apply the `Function.update` corresponding to a scalar write to a `scalarVal` function.
-/
def ScalarWrite.applyToScalarVal {layout : StorageLayout}
    (sw : ScalarWrite layout) (scalarVal : UInt256 → UInt256) : UInt256 → UInt256 :=
  Function.update scalarVal sw.sf.slot sw.val

/--
Fold a list of scalar writes into accumulated `Function.update`s.
-/
def foldScalarUpdates {layout : StorageLayout}
    (sws : List (ScalarWrite layout)) (scalarVal : UInt256 → UInt256) : UInt256 → UInt256 :=
  sws.foldl (fun sv sw => Function.update sv sw.sf.slot sw.val) scalarVal

/--
`foldScalarUpdates` on an empty list is the identity.
-/
@[simp]
theorem foldScalarUpdates_nil {layout : StorageLayout} (scalarVal : UInt256 → UInt256) :
    foldScalarUpdates (layout := layout) [] scalarVal = scalarVal := rfl

/--
`foldScalarUpdates` on a cons applies the head's update before folding the tail.
-/
@[simp]
theorem foldScalarUpdates_cons {layout : StorageLayout}
    (sw : ScalarWrite layout) (rest : List (ScalarWrite layout))
    (scalarVal : UInt256 → UInt256) :
    foldScalarUpdates (sw :: rest) scalarVal =
    foldScalarUpdates rest (Function.update scalarVal sw.sf.slot sw.val) := rfl

/--
Apply a list of scalar writes to an account, extracting the `(slot, val)` pairs.
-/
def applyScalarWrites {τ} {layout : StorageLayout}
    (acc : Account τ) (sws : List (ScalarWrite layout)) : Account τ :=
  applyWrites acc (sws.map fun sw => (sw.sf.slot, sw.val))

/--
`GenericStorageRefines` is preserved through a chain of scalar writes at known
layout slots in a well-formed layout. The `scalarVal` function accumulates the
corresponding `Function.update`s, and `mappingFn` is unchanged.
-/
theorem genericRefines_chain_scalar_writes {τ} {acc : Account τ}
    {layout : StorageLayout}
    {scalarVal : UInt256 → UInt256}
    {mappingFn : UInt256 → UInt256 → UInt256}
    (href : GenericStorageRefines acc.storage layout scalarVal mappingFn)
    (hwf : StorageLayoutWellFormed layout)
    (sws : List (ScalarWrite layout)) :
    GenericStorageRefines
      (applyScalarWrites acc sws).storage
      layout
      (foldScalarUpdates sws scalarVal)
      mappingFn := by
  induction sws generalizing acc scalarVal with
  | nil => exact href
  | cons sw rest ih =>
    simp only [applyScalarWrites, List.map, applyWrites_cons, foldScalarUpdates_cons]
    have href' := genericRefines_after_scalar_write layout hwf href sw.sf sw.hmem sw.val sw.hnonzero
    exact ih href'

-- ============================================================================
-- Event / Log Refinement Infrastructure
-- ============================================================================

/-!
## Event / Log Refinement

The EVM represents events as log entries with topics and data. The typed Lean
model uses `List (String × List UInt256)` where each pair is `(eventName, args)`.

`EventSpec` describes the structure of a known event type.
`EventLogRefines` relates a single typed event to its spec.
`LogTraceRefines` lifts this to lists.

Since event emission only appends to the log and never touches storage, we also
state the (trivial but useful) theorem that emitting an event preserves
`GenericStorageRefines`.
-/

/--
Describe the structure of an event type.
- `name`: the event name (e.g., `"Transfer"`).
- `topicCount`: the number of indexed parameters plus one (for the event
  signature hash), unless the event is anonymous.
- `anonymous`: whether the event is anonymous (no signature topic).
-/
structure EventSpec where
  name : String
  topicCount : Nat
  anonymous : Bool := false
deriving Repr

/--
A typed event refines an EVM log if the event name matches the spec name.
(Full topic/data matching is left to per-contract sidecars; this infrastructure
provides the structural backbone.)
-/
def EventLogRefines (spec : EventSpec) (typedEvent : String × List UInt256) : Prop :=
  typedEvent.1 = spec.name

/--
A list of typed events refines against a set of known event specs when every
event in the list is described by some spec.
-/
def LogTraceRefines (specs : List EventSpec) (typedLogs : List (String × List UInt256)) : Prop :=
  ∀ event ∈ typedLogs, ∃ spec ∈ specs, EventLogRefines spec event

-- ---------- LogTraceRefines theorems ----------

/--
An empty log trace trivially refines against any set of event specs.
-/
theorem logTraceRefines_nil (specs : List EventSpec) :
    LogTraceRefines specs [] := by
  intro _ h; simp at h

/--
If the head event refines some spec and the tail refines, then the cons refines.
-/
theorem logTraceRefines_cons {specs : List EventSpec}
    {e : String × List UInt256} {rest : List (String × List UInt256)}
    (hhead : ∃ spec ∈ specs, EventLogRefines spec e)
    (htail : LogTraceRefines specs rest) :
    LogTraceRefines specs (e :: rest) := by
  intro ev hmem
  simp only [List.mem_cons] at hmem
  rcases hmem with rfl | htl
  · exact hhead
  · exact htail ev htl

/--
Appending two log traces preserves refinement: if both halves refine then so
does their concatenation.
-/
theorem logTraceRefines_append {specs : List EventSpec}
    {logs₁ logs₂ : List (String × List UInt256)}
    (h₁ : LogTraceRefines specs logs₁)
    (h₂ : LogTraceRefines specs logs₂) :
    LogTraceRefines specs (logs₁ ++ logs₂) := by
  intro ev hmem
  rw [List.mem_append] at hmem
  rcases hmem with h | h
  · exact h₁ ev h
  · exact h₂ ev h

-- ---------- Event emission preserves storage refinement ----------

/--
Event emission (appending to the log) does not affect storage, so
`GenericStorageRefines` is trivially preserved. Stating this explicitly lets
generated proofs reference it at event-emission steps.
-/
theorem eventEmission_preserves_genericRefines
    (layout : StorageLayout)
    {storage : Storage}
    {scalarVal : UInt256 → UInt256}
    {mappingFn : UInt256 → UInt256 → UInt256}
    (href : GenericStorageRefines storage layout scalarVal mappingFn) :
    GenericStorageRefines storage layout scalarVal mappingFn := href

/--
Variant that makes the event list explicit in the statement, for documentation
and readability of generated proofs.
-/
theorem eventEmission_preserves_genericRefines'
    (layout : StorageLayout)
    {storage : Storage}
    {scalarVal : UInt256 → UInt256}
    {mappingFn : UInt256 → UInt256 → UInt256}
    (href : GenericStorageRefines storage layout scalarVal mappingFn)
    (_events : List (String × List UInt256)) :
    GenericStorageRefines storage layout scalarVal mappingFn := href

-- ============================================================================
-- ABI Encoding / Decoding Foundation
-- ============================================================================

/-!
## ABI Encoding / Decoding Foundation

Minimal type model for Solidity ABI encoding. These definitions describe ABI
types, typed ABI values, calldata, and return data at a structural level,
without committing to full encoding/decoding proofs. Generated proof sidecars
can use these types to describe function signatures and assert properties of
ABI-encoded data.
-/

/--
Describe Solidity ABI types.
-/
inductive ABIType where
  | uint256 : ABIType
  | address : ABIType
  | bool : ABIType
  | bytes32 : ABIType
  | dynamicBytes : ABIType
  | dynamicArray : ABIType → ABIType
  | fixedArray : ABIType → Nat → ABIType
  | tuple : List ABIType → ABIType
deriving Repr

/--
Typed ABI values corresponding to `ABIType`.
-/
inductive ABIValue where
  | uint256 : UInt256 → ABIValue
  | address : UInt256 → ABIValue
  | bool : Bool → ABIValue
  | bytes32 : UInt256 → ABIValue
  | dynamicBytes : List UInt8 → ABIValue
  | array : List ABIValue → ABIValue
  | tuple : List ABIValue → ABIValue
deriving Repr

/--
Compute the ABI-encoded size (in bytes) of a static type. Returns `none` for
dynamic types (`dynamicBytes`, `dynamicArray`) since they do not have a
fixed encoded size.
-/
def abiEncodedSize : ABIType → Option Nat
  | .uint256 | .address | .bool | .bytes32 => some 32
  | .fixedArray t n => do let s ← abiEncodedSize t; some (s * n)
  | .tuple ts => ts.foldlM (fun acc t => do let s ← abiEncodedSize t; some (acc + s)) 0
  | _ => none  -- dynamic types don't have fixed size

/--
Describe a function call's ABI encoding: a 4-byte selector followed by
the encoded parameters.
-/
structure ABICalldata where
  selector : UInt256  -- first 4 bytes
  params : List ABIValue

/--
Describe the ABI encoding of return values.
-/
structure ABIReturndata where
  values : List ABIValue

/--
ABI encoding is a pure computation over values and does not touch EVM
storage. Therefore, any `GenericStorageRefines` invariant that holds before
an ABI encode/decode step trivially holds after it.
-/
theorem abiEncoding_preserves_genericRefines
    (layout : StorageLayout)
    {storage : Storage}
    {scalarVal : UInt256 → UInt256}
    {mappingFn : UInt256 → UInt256 → UInt256}
    (href : GenericStorageRefines storage layout scalarVal mappingFn) :
    GenericStorageRefines storage layout scalarVal mappingFn := href

end Sol2Lean
end EvmYul
