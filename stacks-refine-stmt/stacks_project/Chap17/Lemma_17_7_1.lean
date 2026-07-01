import Mathlib
import Mathlib.Topology.Sheaves.Abelian
import stacks_project.Chap06.Lemma_6_31_6
import stacks_project.Chap06.Lemma_6_32_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace
open TopCat.Sheaf
open OpenSubsetExtensionByInitial

noncomputable section

universe u

section

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

local instance : Preadditive (X.Sheaf AddCommGrpCat.{u}) :=
  inferInstanceAs
    (Preadditive
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))

local notation "i[" U "]" => X.closedSubsetInclusion ((U : Set X)ᶜ)
local notation "i⁻¹[" U "]" => Sheaf.pullback AddCommGrpCat i[U]
local notation "i_*[" U "]" => Sheaf.pushforward AddCommGrpCat i[U]
local notation "iAdj[" U "]" => Sheaf.pullbackPushforwardAdjunction AddCommGrpCat i[U]
local notation "jAdj[" U "]" => sheafExtensionByInitialAdjunction U

/-
Domain-style sampling for Lemma 17.7.1:
- primary domain: sheaves of abelian groups on an open/closed decomposition of a topological
  space;
- sampled owner declarations:
  `sheafExtensionByInitialAdjunction`,
  `OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalkDescription`,
  `closedSubsetAbelianSheaf_pushforward_stalk_isZero_of_not_mem`,
  `exact_iff_stalkFunctor_map_exact`;
- owner abstraction: the canonical adjunction maps
  `j_! j^{-1} ℱ ⟶ ℱ` and `ℱ ⟶ i_* i^{-1} ℱ`, organized by
  `ShortComplex` / `ShortComplex.ShortExact` in `X.Sheaf AddCommGrpCat`;
- primitive data: the open subset `U`, the sheaf `ℱ`, and those two owner maps;
- derived API: the zero-composite relation and the resulting short-exactness statement.

Source/core/bridge triage:
- `source-facing`: the short exact sequence
  `j_! j^{-1} ℱ ⟶ ℱ ⟶ i_* i^{-1} ℱ`;
- `core/canonical`: the owner adjunction maps and `ShortComplex.ShortExact`;
- `bridge/view`: the stalkwise identifications on points of `U` and of `X \ U`.

The packaged short complex is therefore only one-off derived data in this file, so the public API
should keep the source-facing short-exact theorem rather than a parallel named wrapper object.
-/

-- Proof sketch: these are the built-in naturality squares of the counit for `j! U ⊣ j^{-1}` and
-- of the unit for `i^{-1} ⊣ i_*`.
/-- The counit map `j_! j^{-1} ℱ ⟶ ℱ` is natural in the sheaf. -/
theorem openClosedComplementAbelianSheaf_left_naturality
    (U : Opens X) {ℱ 𝒢 : X.Sheaf AddCommGrpCat.{u}} (φ : ℱ ⟶ 𝒢) :
    CommSq
      ((j! U).map
        ((Sheaf.pullback AddCommGrpCat (extensionByZeroOpenSubsetInclusion U)).map φ))
      ((jAdj[U]).counit.app ℱ)
      ((jAdj[U]).counit.app 𝒢)
      φ := by
  exact CommSq.mk ((jAdj[U]).counit.naturality φ)

omit [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}] in
/-- The unit map `ℱ ⟶ i_* i^{-1} ℱ` for the closed complement of `U` is natural in the sheaf. -/
theorem openClosedComplementAbelianSheaf_right_naturality
    (U : Opens X) {ℱ 𝒢 : X.Sheaf AddCommGrpCat.{u}} (φ : ℱ ⟶ 𝒢) :
    CommSq
      φ
      ((iAdj[U]).unit.app ℱ)
      ((iAdj[U]).unit.app 𝒢)
      ((i_*[U]).map ((i⁻¹[U]).map φ)) := by
  exact CommSq.mk ((iAdj[U]).unit.naturality φ)

-- Proof sketch: check the composite on stalks. At points of `U`, the first map is the identity on
-- stalks and the second map vanishes because the closed-complement pushforward has zero stalk
-- there; at points of `X \ U`, the first map vanishes because extension by zero has zero stalk.
/-- The two adjunction maps for an open subset and its closed complement compose to zero. -/
theorem openClosedComplementAbelianSheaf_comp_zero
    (U : Opens X) (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    ((jAdj[U]).counit.app ℱ) ≫ ((iAdj[U]).unit.app ℱ) =
      0 := sorry

-- Proof sketch: use the stalkwise exactness criterion for sheaves of abelian groups. For `x ∈ U`,
-- identify the stalk of `j_! j^{-1} ℱ` with the stalk of `ℱ` and the stalk of `i_* i^{-1} ℱ`
-- with zero; for `x ∉ U`, identify the stalk of `j_! j^{-1} ℱ` with zero and the stalk of
-- `i_* i^{-1} ℱ` with the stalk over the closed complement. The resulting stalk complex is the
-- evident short exact sequence `0 → F_x → F_x → 0` or `0 → 0 → F_x → F_x`.
/-- Lemma 17.7.1: for an open subset `U ⊆ X` with closed complement `X \ U`, the adjunction maps
`j_! j^{-1} ℱ ⟶ ℱ` and `ℱ ⟶ i_* i^{-1} ℱ` form a short exact sequence of sheaves of abelian
groups on `X`. -/
theorem openClosedComplementAbelianSheaf_shortExact
    (U : Opens X) (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    (ShortComplex.mk
      ((jAdj[U]).counit.app ℱ)
      ((iAdj[U]).unit.app ℱ)
      (openClosedComplementAbelianSheaf_comp_zero U ℱ)).ShortExact := by
  sorry

end
