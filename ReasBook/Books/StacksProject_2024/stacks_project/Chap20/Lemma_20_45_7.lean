import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import StacksProject_2024.Chap13.Definition_13_27_1
import StacksProject_2024.Chap20.Global_sections_module_owners_core
import StacksProject_2024.Chap20.Open_subspace_module_core

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open scoped DerivedExt

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.45.7:
- primary domain: restriction of derived `𝒪_X`-modules to nested open subspaces of a
  ringed space and the transfinite gluing statement built from those restrictions;
- sampled owner declarations:
  `ModuleDerived`,
  `moduleRestrictionToOpenDerived`,
  `moduleDerivedOnOpen`,
  `derivedRestrictionBetweenOpens`,
  `derivedRestrictionBetweenOpensCompIso`,
  `moduleRestrictionToOpenDerivedCompIso`,
  `Ext^i(-, -)`;
- best owner abstraction:
  `source-facing`: the well-ordered gluing theorem for an indexed increasing cover;
  `core/canonical`: the chapter owner `ModuleDerived X`, together with `moduleDerivedOnOpen`,
    `moduleRestrictionToOpenDerived`, and the nested-open restriction functors from
    `Open_subspace_module_core`;
  `bridge/view`: the canonical comparison isomorphisms
    `derivedRestrictionBetweenOpensCompIso` and `moduleRestrictionToOpenDerivedCompIso`;
  the indexed conclusion remains source-facing rather than being repackaged through
  `OpenFamilyDerivedGluing`, because repeated values of `W` would force a noncanonical choice of
  representative in `Set.range W`.

Primitive vs derived:
- primitive data: the local derived objects `Kα` and their transition isomorphisms;
- derived API: negative self-Ext vanishing in the canonical `Ext^i` notation and the direct
  indexed realization conclusion for a global derived object.
-/

variable {X : RingedSpace.{u}}

section

variable {E : Type v} [LinearOrder E] [SuccOrder E] [WellFoundedLT E]
variable (W : E → Opens X.carrier) (hmono : Monotone W)

local notation "DModX" => ModuleDerived X
local notation "DMod[" U "]" => moduleDerivedOnOpen X U
local notation "DRes[" U "]" => moduleRestrictionToOpenDerived X U
local notation "DRes≤[" h "]" => derivedRestrictionBetweenOpens X (hmono h)
local notation "DResComp[" h₁ "," h₂ "]" =>
  derivedRestrictionBetweenOpensCompIso X (hmono h₁) (hmono h₂)
local notation "DResFromXComp[" h "]" => moduleRestrictionToOpenDerivedCompIso X (hmono h)

-- Proof sketch: choose K-injective representatives of the local objects and construct compatible
-- extension-by-zero transition morphisms by transfinite recursion. At successor stages, extend
-- across the new open using the given restriction isomorphism. At non-successor stages, take the
-- filtered colimit over the earlier glued complexes and use vanishing of negative self-Ext to
-- identify this colimit with the prescribed local object. A final filtered colimit over the whole
-- well-ordered cover produces the global derived object, and the restriction compatibilities are
-- recorded directly in the indexed conclusion below.
/-- Lemma 20.45.7: for a ringed space `X`, a well-ordered increasing open cover `W` that is
continuous at every non-successor stage, and a compatible family of objects
`Kα α ∈ D(𝒪_{W α})` with `Ext^i(Kα α, Kα α) = 0` for `i < 0`, there exists an object
`K ∈ D(𝒪_X)` whose restriction to each `W α` is identified with `Kα α` and is compatible with the
given restriction isomorphisms. Because the same open may occur at multiple indices, the
conclusion is stated directly in indexed form rather than by collapsing the data to
`OpenFamilyDerivedGluing` on `Set.range W`. -/
@[stacks 0D6B]
theorem exists_glued_derived_object_of_wellOrdered_open_cover
    (hcover : iSup W = ⊤)
    (hlimit : ∀ ⦃α : E⦄, Order.IsSuccPrelimit α → W α = ⨆ β : Set.Iio α, W β.1)
    (Kα : ∀ α : E, DMod[W α])
    (hExt : ∀ α (i : ℤ), i < 0 → IsZero (AddCommGrpCat.of (Ext^i(Kα α, Kα α))))
    (rho : ∀ {β α : E} (hβα : β < α),
      (DRes≤[hβα.le]).obj (Kα α) ≅ Kα β)
    (hrho : ∀ {γ β α : E} (hγβ : γ < β) (hβα : β < α),
      ((DResComp[hγβ.le, hβα.le]).app (Kα α)) ≪≫
          rho (lt_trans hγβ hβα) =
        (DRes≤[hγβ.le]).mapIso (rho hβα) ≪≫
          rho hγβ) :
    ∃ K : DModX,
      ∃ iso : ∀ α : E, ((DRes[W α]).obj K) ≅ Kα α,
        ∀ {β α : E} (hβα : β < α),
          CommSq (((DResFromXComp[hβα.le]).app K).inv)
            (iso β).hom ((DRes≤[hβα.le]).map (iso α).hom) (rho hβα).inv := sorry

end

end AlgebraicGeometry.RingedSpace
