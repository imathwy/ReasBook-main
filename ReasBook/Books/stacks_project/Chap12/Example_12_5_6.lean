import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

/- Domain-style sampling for Example 12.5.6:
- primary domain: pullbacks and pushouts in an abelian category, expressed as kernels and cokernels
  of the canonical biproduct comparison maps;
- inspected owner declarations:
  `Abelian.PullbackToBiproductIsKernel.pullbackToBiproduct`,
  `Abelian.PullbackToBiproductIsKernel.pullbackToBiproductFork`,
  `Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct`,
  `Abelian.BiproductToPushoutIsCokernel.isColimitBiproductToPushout`;
- best owner abstraction: the universal-property owners `KernelFork` / `CokernelCofork` together
  with `IsLimit` / `IsColimit`, specialized to the canonical pullback-to-biproduct and
  biproduct-to-pushout maps already provided by mathlib;
- primitive data: the canonical comparison maps `pullback a b ⟶ x ⊞ z` and
  `x' ⊞ z' ⟶ pushout f g`;
- derived API: the induced kernel fork and cokernel cofork, and the statements that they are
  limiting/colimiting.

Source/core/bridge triage:
- `source-facing`: the two textbook example statements identifying the fibre product with the
  kernel of `(a, -b)` and the pushout with the cokernel of `(f, -g)`;
- `core/canonical`: `KernelFork`, `CokernelCofork`, `IsLimit`, and `IsColimit`;
- `bridge/view`: the specialized owner declarations
  `Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct` and
  `Abelian.BiproductToPushoutIsCokernel.isColimitBiproductToPushout`, which package the
  source-facing constructions into the canonical kernel/cokernel interface.
-/

section

variable {C : Type u} [Category.{v} C] [Abelian C]

/- Example 12.5.6 (1): in an abelian category, for morphisms `a : x ⟶ y` and `b : z ⟶ y`,
the canonical map `pullback a b ⟶ x ⊞ z` exhibits the fibre product as the kernel of
`(a, -b) : x ⊞ z ⟶ y`. The owner declaration is the kernel-fork statement
`Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct`. -/
recall Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct

/- Example 12.5.6 (2): dually, for morphisms `f : y' ⟶ x'` and `g : y' ⟶ z'`, the canonical map
`x' ⊞ z' ⟶ pushout f g` exhibits the pushout as the cokernel of
`(f, -g) : y' ⟶ x' ⊞ z'`. The owner declaration is the cokernel-cofork statement
`Abelian.BiproductToPushoutIsCokernel.isColimitBiproductToPushout`. -/
recall Abelian.BiproductToPushoutIsCokernel.isColimitBiproductToPushout

end

end CategoryTheory
