import StacksProject_2024.stacks_project.Chap20.Lemma_20_33_2
import StacksProject_2024.stacks_project.Chap20.Open_subspace_module_pushforward_along_derived

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open TopologicalSpace
open AlgebraicGeometry
open scoped RingedSpace.Hom RingedSpaceDerivedPushforward

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X Y : RingedSpace.{u}}
variable (f : X ⟶ Y)
variable [(f _*).Additive]

local notation "DModX" => ModuleDerived X
local notation "DModY" => ModuleDerived Y
local notation "RPushRel[" U "]" =>
  modulePushforwardFromOpenAlongDerived f U

/-- The canonical relative Mayer-Vietoris restriction map
`R(f)_* E ⟶ Ra_*(E|_U) ⊞ Rb_*(E|_V)`. -/
abbrev modulePushforwardDerivedMayerVietorisToBiprod
    (U V : Opens X) :
    R(f)_* ⟶ RPushRel[U] ⊞ RPushRel[V] :=
  biprod.lift
    (modulePushforwardFromOpenAlongDerivedUnitNatTrans f U)
    (modulePushforwardFromOpenAlongDerivedUnitNatTrans f V)

/-- The canonical relative Mayer-Vietoris overlap-difference map
`Ra_*(E|_U) ⊞ Rb_*(E|_V) ⟶ Rc_*(E|_{U ∩ V})`. -/
abbrev modulePushforwardDerivedMayerVietorisDifference
    (U V : Opens X) :
    RPushRel[U] ⊞ RPushRel[V] ⟶ RPushRel[U ⊓ V] :=
  biprod.desc
    (modulePushforwardFromOpenAlongDerivedRestrictionNatTrans f
      (inf_le_left : U ⊓ V ≤ U))
    (-(modulePushforwardFromOpenAlongDerivedRestrictionNatTrans f
      (inf_le_right : U ⊓ V ≤ V)))

/- Domain-style sampling for Lemma 20.33.5:
- primary domain: relative Mayer-Vietoris distinguished triangles for derived direct image on
  ringed spaces;
- sampled owner declarations:
  `ringedSpaceModule_derivedMayerVietoris_triangle`,
  `modulePushforwardFromOpenAlongDerived`,
  `modulePushforwardDerivedMayerVietorisToBiprod`,
  `modulePushforwardDerivedMayerVietorisDifference`,
  `modulePushforwardFromOpenAlongDerivedUnitNatTrans`,
  `modulePushforwardFromOpenAlongDerivedRestrictionNatTrans`,
  `moduleDerivedPushforward`,
  `Triangle.mk`;
- best owner abstraction:
  `source-facing`: the functorial relative Mayer-Vietoris restriction and overlap-difference
    natural transformations for `Rf_*`, together with the resulting distinguished triangle;
  `core/canonical`: the Chapter 20 owner
    `ringedSpaceModule_derivedMayerVietoris_triangle`,
    `modulePushforwardFromOpenAlongDerived`,
    `modulePushforwardDerivedMayerVietorisToBiprod`,
    `modulePushforwardDerivedMayerVietorisDifference`,
    `modulePushforwardFromOpenAlongDerivedUnitNatTrans`,
    `modulePushforwardFromOpenAlongDerivedRestrictionNatTrans`, and the chapter-owned
    derived-pushforward owner `moduleDerivedPushforward f` written as `R(f)_*`;
  `bridge/view`: none beyond the theorem-local notation for the canonical owner
    `modulePushforwardFromOpenAlongDerived`.

Primitive-vs-derived split:
- primitive data: the morphism `f : X ⟶ Y` and the opens `U, V ⊆ X`;
- derived API: the source-facing relative Mayer-Vietoris distinguished triangle theorem below,
  whose first two displayed morphisms are built from the canonical derived restriction maps.

Source/core/bridge triage:
- `source-facing`: the functorial relative Mayer-Vietoris triangle for `R(f)_*`, whose first two
  displayed morphisms are the biproduct of the canonical derived restriction maps to `U` and `V`
  and their overlap-difference map to `U ∩ V`;
- `core/canonical`: `ringedSpaceModule_derivedMayerVietoris_triangle`,
  `modulePushforwardFromOpenAlongDerived`,
  `modulePushforwardDerivedMayerVietorisToBiprod`,
  `modulePushforwardDerivedMayerVietorisDifference`,
  `modulePushforwardFromOpenAlongDerivedUnitNatTrans`,
  `modulePushforwardFromOpenAlongDerivedRestrictionNatTrans`,
  `moduleDerivedPushforward`, and `R(f)_*`;
- `bridge/view`: none beyond the theorem-local notation for the canonical owner.
-/

-- Proof sketch: start from the chapter-owned Mayer-Vietoris distinguished triangle on
-- `ModuleDerived X` from Lemma `20.33.2` and apply the exact functor `R(f)_*`. This yields the
-- three relative terms in the canonical owner form `modulePushforwardFromOpenAlongDerived f W`.
-- The first two displayed morphisms are the canonical biproduct of the derived restriction maps
-- to `U` and `V` and their overlap-difference map, so only the connecting morphism remains
-- existential.
/-- Lemma 20.33.5: if `f : X ⟶ Y` is a morphism of ringed spaces and `X = U ∪ V`, then there
exist natural morphisms
`Rf_* E ⟶ Ra_*(E|_U) ⊕ Rb_*(E|_V) ⟶ Rc_*(E|_{U ∩ V}) ⟶ Rf_* E[1]`
whose evaluation at every `E ∈ D(𝒪_X)` is a distinguished triangle; hence the relative
Mayer-Vietoris triangle is functorial in `E`. Here `RPushRel[W]` denotes the canonical Chapter 20
owner `modulePushforwardFromOpenAlongDerived f W`. -/
@[stacks 08HZ]
theorem ringedSpaceModulePushforward_derivedMayerVietoris_triangle
    (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    ∃ δ : RPushRel[U ⊓ V] ⟶ R(f)_* ⋙ shiftFunctor DModY (1 : ℤ),
      ∀ E : DModX,
        Triangle.mk
            ((modulePushforwardDerivedMayerVietorisToBiprod f U V).app E)
            ((modulePushforwardDerivedMayerVietorisDifference f U V).app E)
            (δ.app E) ∈ distTriang DModY := by
  sorry

/-- Objectwise companion to Lemma 20.33.5: for each `E ∈ D(𝒪_X)`, the canonical relative
Mayer-Vietoris restriction biproduct map and overlap-difference map extend to a distinguished
triangle in `D(𝒪_Y)`. -/
theorem ringedSpaceModulePushforwardDerivedMayerVietorisTriangle
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (E : DModX) :
    ∃ δ : (RPushRel[U ⊓ V]).obj E ⟶ ((R(f)_*).obj E)⟦(1 : ℤ)⟧,
      Triangle.mk
          ((modulePushforwardDerivedMayerVietorisToBiprod f U V).app E)
          ((modulePushforwardDerivedMayerVietorisDifference f U V).app E)
          δ ∈ distTriang DModY := by
  obtain ⟨δ, hδ⟩ := ringedSpaceModulePushforward_derivedMayerVietoris_triangle f U V hUV
  exact ⟨δ.app E, hδ E⟩

end

end AlgebraicGeometry.RingedSpace
