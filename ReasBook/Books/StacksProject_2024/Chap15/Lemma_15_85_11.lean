import StacksProject_2024.Chap13.Definition_13_11_3
import StacksProject_2024.Chap13.Lemma_13_12_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.ComposableArrows
open DerivedCategory.TStructure

universe w v u

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/- Domain-style sampling for Lemma 15.85.11:
- primary domain: the canonical `t`-structure on `D(𝒜)` for an abelian category `𝒜`, and
  objects concentrated in degrees `≤ 0` and `≥ -1`;
- sampled owner declarations:
  `exists_factor_through_truncLE_of_stepwise_homologyMap_eq_zero`,
  `Triangulated.TStructure.isZero_truncLE_obj_of_isGE`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.IsLE`,
  `DerivedCategory.isGE_iff`,
  `DerivedCategory.isLE_iff`;
- best owner abstraction: the endpoint cohomology bounds belong to the canonical owner predicates
  `K1.IsLE 0` and `K3.IsGE (-1)`, the intervening factorization belongs to
  `exists_factor_through_truncLE_of_stepwise_homologyMap_eq_zero`, and the final vanishing should
  be expressed by the canonical `t`-structure fact that `τ_{\le -2} K3 = 0` under the owner
  hypothesis `K3.IsGE (-1)`, rather than through a parallel degree-gap wrapper;
- primitive data: the objects `K1`, `K2`, `K3`, the morphisms `φ`, `ψ`, and the vanishing
  conditions on `H^0(φ)` and `H^{-1}(ψ)`;
- derived API: the composite-vanishing conclusion.

Source/core/bridge triage:
- `source-facing`: the textbook composite-vanishing statement below;
- `core/canonical`: the `t`-structure predicates `IsGE` / `IsLE`;
- `bridge/view`: the equivalent cohomology-vanishing formulations `isGE_iff` / `isLE_iff`.

Accordingly, this file keeps the source-facing theorem and replaces the repeated interval-vanishing
binders by the canonical `t`-structure owner predicates. Since the proof is purely formal in the
derived-category `t`-structure, the owner ambient category is the general `DerivedCategory 𝒜`,
not the special case `D(R)`. -/

-- Proof sketch: apply Lemma `13.12.5` to the length-two chain `K1 ⟶ K2 ⟶ K3`. The hypotheses
-- `H^0(φ) = 0` and `H^{-1}(ψ) = 0` force the composite to factor through the truncation
-- `τ_{\le -2} K3`, and `K3.IsGE (-1)` implies that truncation object is zero, so the factorized
-- morphism vanishes.
/-- Lemma 15.85.11: in the derived category of an abelian category, if `K1` has no cohomology in
degrees `> 0`, if `K3` has no cohomology in degrees `< -1`, if `φ : K1 ⟶ K2` induces the zero
map on `H^0`, and if `ψ : K2 ⟶ K3` induces the zero map on `H^{-1}`, then the composite
`K1 ⟶ K3` is zero. -/
theorem comp_zero_of_h0_map_eq_zero_of_hneg1_map_eq_zero
    {K1 K2 K3 : D(𝒜)} (φ : K1 ⟶ K2) (ψ : K2 ⟶ K3)
    (hK1 : K1.IsLE 0) (hK3 : K3.IsGE (-1))
    (hφ : (H^0).map φ = 0)
    (hψ : (H^(-1)).map ψ = 0) :
    φ ≫ ψ = 0 := by
  obtain ⟨τφ, hfactor⟩ :=
    exists_factor_through_truncLE_of_stepwise_homologyMap_eq_zero (mk₂ φ ψ) hK1
      (fun j hj ↦ by
        cases j with
        | zero =>
            simpa [ComposableArrows.mk₂, ComposableArrows.Precomp.map_zero_one] using hφ
        | succ j =>
            cases j with
            | zero =>
                simpa [ComposableArrows.mk₂, ComposableArrows.Precomp.map_one_succ] using hψ
            | succ j =>
                exact False.elim (by simpa using hj))
  letI := hK3
  have hτK3 : Limits.IsZero ((t.truncLE (-2)).obj K3) := by
    simpa using t.isZero_truncLE_obj_of_isGE (-2) (-1) rfl K3
  have hτφ : τφ = 0 := hτK3.eq_of_tgt τφ 0
  calc
    φ ≫ ψ = τφ ≫ (t.truncLEι (-2)).app K3 := by
      simpa [ComposableArrows.mk₂, ComposableArrows.Precomp.map_zero_one,
        ComposableArrows.Precomp.map_one_succ] using hfactor.symm
    _ = 0 := by rw [hτφ, Limits.zero_comp]

end

end CategoryTheory
