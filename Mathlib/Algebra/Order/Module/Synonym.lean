/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Order.GroupWithZero.Action.Synonym
import Mathlib.Algebra.Order.Ring.Synonym

/-!
# Action instances for `OrderDual`

This file provides instances of algebraic actions for `OrderDual`. Note that the `SMul` instances
are already defined in `Mathlib.Algebra.Order.Group.Synonym`.

## See also

* `Mathlib.Algebra.Order.Group.Synonym`
* `Mathlib.Algebra.Order.Ring.Synonym`
-/

namespace OrderDual
variable {α β : Type*}

instance instModule [Semiring α] [AddCommMonoid β] [Module α β] : Module αᵒᵈ β where
  add_smul := add_smul (R := α)
  zero_smul := zero_smul _

instance instModule' [Semiring α] [AddCommMonoid β] [Module α β] : Module α βᵒᵈ where
  add_smul := add_smul (M := β)
  zero_smul := zero_smul _

end OrderDual
