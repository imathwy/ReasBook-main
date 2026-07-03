import Mathlib
import stacks_project.Chap10.Definition_10_110_7

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open scoped TensorProduct

universe u v

section

variable {R : Type u} {A : Type v} [CommRing R] [IsDomain R] [ValuationRing R]
variable [CommRing A] [Algebra R A] [IsLocalRing A] [IsLocalHom (algebraMap R A)]
variable [Module.Flat R A] [Algebra.EssFiniteType R A]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) A
local notation "GenericFiber" => Ideal.Fiber (⊥ : Ideal R) A

/- Domain-style sampling:
- primary domain: Picard groups of fibers of local flat algebras over valuation rings, with the
  closed and generic fibers carried by the canonical owner `Ideal.Fiber`;
- sampled owner declarations:
  `Ideal.Fiber`,
  `CommRing.Pic`,
  `subsingleton_picardGroup_of_uniqueFactorizationMonoid`,
  `IsRegularRing`,
  `flat_iff_isTorsionFree_of_valuationRing`;
- best owner abstraction: the closed fiber should be written as
  `ClosedFiber = Ideal.Fiber (maximalIdeal R) A` and the generic fiber as
  `GenericFiber = Ideal.Fiber (⊥ : Ideal R) A`; the tensor-product models
  `A ⊗[R] ResidueField R` and `A ⊗[R] FractionRing R` are bridge presentations of those owners;
- primitive vs. derived:
  the primitive data are the valuation-ring map `R → A`, locality of `A`, flatness, essential
  finite type, and regularity of the canonical closed fiber `ClosedFiber`;
  the Picard-triviality conclusion belongs on the owner `CommRing.Pic GenericFiber`, while any
  tensor-model reformulation is derived bridge/view API rather than the core owner statement.

Source/core/bridge triage:
- `source-facing`: the theorem below asserting Picard triviality of the generic fiber;
- `core/canonical`: the fiber-ring owner `Ideal.Fiber` together with `CommRing.Pic`;
- `bridge/view`: the textbook tensor-product presentations of the closed and generic fibers.
-/

-- Proof sketch: let `L` represent a class in `CommRing.Pic GenericFiber`, using the tensor-model
-- presentation `GenericFiber = A ⊗[R] FractionRing R`. Use the extension result for finite modules
-- over the generic fiber to choose a finite `A`-module whose base change to `GenericFiber`
-- is `L`. Over a valuation ring, torsion-free implies flat, so the cited finite-presentation and
-- perfectness lemmas give a finite free resolution of this model over `A`. After base change to
-- `GenericFiber`, Lemma `15.120.1` makes the class of `L` an integral multiple of the
-- free rank-one class in `K₀`, and Lemma `15.119.7` then forces `L` to be free of rank one.
-- Hence every element of the Picard group is trivial.
/-- Lemma 15.122.3: if `R` is a valuation ring and `R → A` is a local, flat, essentially finite
type map with `A` local and regular closed fiber
`ClosedFiber = Ideal.Fiber (maximalIdeal R) A`, equivalently `A ⊗[R] ResidueField R`, then the
generic fiber `GenericFiber = Ideal.Fiber (⊥ : Ideal R) A`, canonically presented by
`A ⊗[R] FractionRing R`, has trivial Picard group. -/
theorem subsingleton_picardGroup_genericFiber_of_regular_closedFiber
    [IsRegularRing ClosedFiber] :
    Subsingleton (CommRing.Pic GenericFiber) := sorry

end
