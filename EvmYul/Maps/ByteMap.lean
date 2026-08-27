/-
We need a more unified approach to maps.

This file shouldn't exist; but it does for now.
`Finmap`s have terrible computational behaviour, one needs some ordering lemmas to make them compute.

In `Conform`, we use `Lean.RBMap`, although we would ideally use `Batteries.RBMap`, but the `Lean.Json`
uses `Lean.RBMap`, which means that we would need an additional cast to `Batteries.RBMap`.

Furthermore, replacing everything with either of the `RBMaps` would then reintroduce this mess,
but with ordering lemmas needed for some `Decidable` instances.

When time allows, I suggest we replace everything with `Batteries.RBMap` and prove the reasoning lemmas we need.
This way, we get decent performance AND the ability to conveniently reason about the structure
a'la `Finmap`.

TODO - All of this is very ugly.
-/

module

public import Std.Data.TreeMap.Basic
public meta import Std.Data.TreeMap.Basic
public import Std.Data.TreeMap.Lemmas
public meta import Std.Data.TreeMap.Lemmas

public import EvmYul.Wheels
public meta import EvmYul.Wheels

@[expose] public section

namespace EvmYul

section RemoveLater

abbrev ByteMap := Std.TreeMap UInt256 UInt8 compare

end RemoveLater

end EvmYul
