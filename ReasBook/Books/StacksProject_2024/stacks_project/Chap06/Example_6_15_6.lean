import Mathlib
import StacksProject_2024.Chap06.Definition_6_15_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.Limits

noncomputable section

universe w v u uC

variable {C : Type v} [Category.{uC} C] {X : TopCat.{u}}

/-
Domain-style sampling for Example 6.15.6:
- primary domain: presheaves on `X` built from categorical products in `C`, together with the
  canonical comparison between sheaf conditions before and after composing with a forgetful functor
  to types;
- inspected owner declarations:
  `TopCat.presheafToTypes`,
  `TopCat.Presheaf.toTypes_isSheaf`,
  `TopCat.Presheaf.isSheaf_iff_isSheaf_comp`,
  `CategoryTheory.Limits.Pi.map'`;
- owner abstraction:
  the source-facing owner in this file is the `C`-valued presheaf itself, while its underlying
  `Type`-valued comparison should be expressed through the canonical dependent-function presheaf
  `TopCat.presheafToTypes`;
- primitive-vs-derived split:
  primitive data are the product objects `∏ᶜ fun x : U.unop ↦ Aₓ x.1`;
  the restriction maps are derived from the canonical product reindexing morphism `Pi.map'`,
  and the sheaf statement is derived by comparing with the underlying `Type`-valued presheaf;
  the owner itself only needs `[HasProducts.{u} C]`, while the bridge theorem only needs
  `[HasLimitsOfSize.{u, u} C]`, `[PreservesLimitsOfSize.{u, u} F]`, and
  `[F.ReflectsIsomorphisms]`, so the larger chapter package `IsAlgebraicStructure C F` is
  derived context here rather than primitive data.

Source/core/bridge triage:
- `source-facing`: the `C`-valued presheaf `U ↦ ∏ x : U, Aₓ x`;
- `core/canonical`: `Pi.map'` for product reindexing and `TopCat.presheafToTypes` for the
  underlying dependent-function presheaf;
- `bridge/view`: the sheaf comparison after composing with `F ⋙ uliftFunctor`.
-/

section HasProducts

variable [HasProducts.{u} C]

local instance sectionHasProduct (Aₓ : X → C) (U : (Opens X)ᵒᵖ) :
    HasProduct (fun x : U.unop ↦ Aₓ x.1) := by
  change HasLimit (Discrete.functor (fun x : U.unop ↦ Aₓ x.1))
  let h : HasProductsOfShape U.unop C := hasProductsOfShape_of_hasProducts U.unop
  exact h.has_limit (Discrete.functor (fun x : U.unop ↦ Aₓ x.1))

/-- The `C`-valued presheaf whose sections over `U` are the products of the fibres `Aₓ x` for
`x ∈ U`. -/
def pointwiseProductPresheaf (Aₓ : X → C) : TopCat.Presheaf C X where
  obj U := ∏ᶜ fun x : U.unop ↦ Aₓ x.1
  map {_ _} i := Pi.map' i.unop (fun _ ↦ 𝟙 _)
  map_id U := by
    simp
  map_comp {U V W} i j := by
    simpa using
      (Pi.map'_comp_map' i.unop j.unop (fun _ ↦ 𝟙 _) (fun _ ↦ 𝟙 _)).symm

end HasProducts

section SheafComparison

variable (F : C ⥤ Type w) (Aₓ : X → C)
variable [HasLimitsOfSize.{u, u} C] [PreservesLimitsOfSize.{u, u} F]

private abbrev hasProductsOfBaseSize : HasProducts.{u} C := fun J ↦ by
  let _ : HasLimitsOfShape (Discrete J) C :=
    HasLimitsOfSize.has_limits_of_shape (Discrete J)
  infer_instance

local instance : HasProducts.{u} C := hasProductsOfBaseSize

/-- After composing with the forgetful functor and a universe lift, the pointwise product presheaf
is a sheaf of types. -/
-- Proof sketch: the composite
-- `pointwiseProductPresheaf X Aₓ ⋙ F ⋙ uliftFunctor` is canonically identified objectwise with
-- the dependent-function presheaf
-- `U ↦ ∀ x : U, ULift (F.obj (Aₓ x.1))`; this is a sheaf by Example 6.7.5.
private theorem pointwiseProductPresheaf_comp_uliftFunctor_isSheaf
    : TopCat.Presheaf.IsSheaf
        (pointwiseProductPresheaf Aₓ ⋙ F ⋙ uliftFunctor.{u, w}) := sorry

-- Proof sketch: apply `TopCat.Presheaf.isSheaf_iff_isSheaf_comp` to the composite forgetful
-- functor `F ⋙ uliftFunctor`; the companion theorem above supplies the sheaf condition for the
-- resulting `Type`-valued presheaf.
/-- Example 6.15.6: let `(C, F)` be a type of algebraic structures, let `X` be a topological
space, and let `Aₓ : X → C`. Then the presheaf `U ↦ ∏ x : U, Aₓ x` with the evident restriction
maps is a sheaf. For the source application to algebraic structures, this conclusion is obtained
from the canonical comparison theorem using only limit preservation and reflection of
isomorphisms. -/
theorem pointwiseProductPresheaf_isSheaf
    [F.ReflectsIsomorphisms] : (pointwiseProductPresheaf Aₓ).IsSheaf := sorry

end SheafComparison
