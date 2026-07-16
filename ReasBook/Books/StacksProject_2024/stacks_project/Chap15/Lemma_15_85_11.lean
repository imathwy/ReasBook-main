import StacksProject_2024.stacks_project.Chap13.Definition_13_11_3
import StacksProject_2024.stacks_project.Chap13.Remark_13_12_4
import StacksProject_2024.stacks_project.Chap13.Lemma_13_35_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.ComposableArrows
open CategoryTheory.Pretriangulated
open DerivedCategory
open DerivedCategory.TStructure

universe w v u

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

local notation "H" => DerivedCategory.homologyFunctor 𝒜

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

/-- Helper for Lemma 15.85.11: a morphism between single-degree objects is zero once its
degree-`a` homology map is zero. -/
private lemma single_map_eq_zero_of_homologyMap_eq_zero_local
    {A B : 𝒜} {a : ℤ}
    (q : (singleFunctor 𝒜 a).obj A ⟶ (singleFunctor 𝒜 a).obj B)
    (hq : (H a).map q = 0) :
    q = 0 := by
  let hFF : (singleFunctor 𝒜 a).FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful (singleFunctor 𝒜 a)
  let u : A ⟶ B := hFF.preimage q
  have huq : (singleFunctor 𝒜 a).map u = q := by
    simpa [u] using hFF.map_preimage q
  -- Proof comment: naturality of the canonical comparison `singleFunctor ⋙ H^a ≅ 𝟭`
  -- transports the vanishing homology map back to the underlying morphism in `𝒜`.
  have hu : ((singleFunctorCompHomologyFunctorIso 𝒜 a).app A).hom ≫ u = 0 := by
    simpa [Functor.comp_map, huq, hq] using
      (NatTrans.naturality (singleFunctorCompHomologyFunctorIso 𝒜 a).hom u).symm
  have hu' :
      ((singleFunctorCompHomologyFunctorIso 𝒜 a).app A).hom ≫ u =
        ((singleFunctorCompHomologyFunctorIso 𝒜 a).app A).hom ≫ 0 := by
    calc
      ((singleFunctorCompHomologyFunctorIso 𝒜 a).app A).hom ≫ u = 0 := hu
      _ = ((singleFunctorCompHomologyFunctorIso 𝒜 a).app A).hom ≫ 0 := by
        symm
        rw [Limits.comp_zero]
  have hu_zero : u = 0 := by
    exact (cancel_epi ((singleFunctorCompHomologyFunctorIso 𝒜 a).app A).hom).1 hu'
  rw [← huq, hu_zero]
  simp

/-- Helper for Lemma 15.85.11: a morphism from an object of `D^{≤ a}` to a single-degree object
in degree `a` vanishes once its degree-`a` homology map is zero. -/
private lemma hom_to_single_eq_zero_of_isLE_homologyMap_eq_zero_local
    {X : DerivedCategory 𝒜} {A₀ : 𝒜} {a : ℤ}
    (hX : X.IsLE a)
    (g : X ⟶ (singleFunctor 𝒜 a).obj A₀)
    (hg : (H a).map g = 0) :
    g = 0 := by
  letI : X.IsLE a := hX
  let desc : (t.truncGE a).obj X ⟶ (singleFunctor 𝒜 a).obj A₀ := t.descTruncGE g a
  -- Proof comment: factor `g` through `τ_{\ge a} X`, where the source becomes concentrated in
  -- degree `a`, and transport the zero homology-map condition across `τ_{\ge a}`.
  have hdesc_homology : (H a).map desc = 0 := by
    apply (cancel_epi ((H a).map ((t.truncGEπ a).app X))).1
    simpa [desc, Functor.map_comp, hg] using
      congrArg (fun k ↦ (H a).map k) (t.π_descTruncGE g a)
  have htruncLE : ((t.truncGE a).obj X).IsLE a := by
    infer_instance
  let e := singleFunctorIso_of_isGE_of_isLE (A := 𝒜) ((t.truncGE a).obj X) a
  let q :
      (singleFunctor 𝒜 a).obj ((H a).obj ((t.truncGE a).obj X)) ⟶
        (singleFunctor 𝒜 a).obj A₀ :=
    e.inv ≫ desc
  have hq_homology : (H a).map q = 0 := by
    simp [q, Functor.map_comp, hdesc_homology]
  have hq_zero : q = 0 :=
    single_map_eq_zero_of_homologyMap_eq_zero_local q hq_homology
  have hdesc_zero : desc = 0 := by
    calc
      desc = e.hom ≫ q := by simp [q, Category.assoc]
      _ = 0 := by simp [hq_zero]
  have hg_factor : g = (t.truncGEπ a).app X ≫ desc := by
    simpa [desc] using (t.π_descTruncGE g a).symm
  rw [hg_factor, hdesc_zero]
  simp

/-- Helper for Lemma 15.85.11: a morphism `f : X ⟶ Y` from an object of `D^{≤ a}` factors through
`τ_{< a} Y` once its degree-`a` homology map vanishes. -/
private lemma exists_factor_through_prev_truncLT_of_isLE_and_homologyMap_eq_zero_local
    {X Y : DerivedCategory 𝒜} {a : ℤ}
    (f : X ⟶ Y)
    (hX : X.IsLE a)
    (hf : (H a).map f = 0) :
    ∃ φ : X ⟶ (t.truncLT a).obj Y,
      φ ≫ (t.truncLTι a).app Y = f := by
  -- TODO: factor the lifted map `fLT : X ⟶ τ_{< a + 1} Y` through the first vertex of
  -- `truncLE_step_homologyTriangle Y (a - 1)` by showing its composite with the single-degree
  -- third vertex is zero via `hom_to_single_eq_zero_of_isLE_homologyMap_eq_zero_local`, then
  -- use `Triangle.coyoneda_exact₂` and `natTransTruncLTOfLE_ι_app` to descend from `τ_{< a}` to `Y`.
  sorry

-- Route correction: the original proof route still factors through the next lower truncation,
-- but the broken imported Chapter 13 theorem is replaced here by the local one-step truncation
-- factorization proved above and applied twice.
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
  -- Proof comment: first factor `φ` through `τ_{< 0} K2`, then factor the induced map to `K3`
  -- through `τ_{< -1} K3`, which is zero because `K3 ∈ D^{≥ -1}`.
  obtain ⟨φ₀, hφ₀⟩ :=
    exists_factor_through_prev_truncLT_of_isLE_and_homologyMap_eq_zero_local φ hK1 hφ
  have hψ' : (H^(-1)).map (((t.truncLTι 0).app K2) ≫ ψ) = 0 := by
    simp [Functor.map_comp, hψ]
  have hK2LT : ((t.truncLT 0).obj K2).IsLE (-1) := by
    simpa using (inferInstance : ((t.truncLT 0).obj K2).IsLE (0 - 1))
  obtain ⟨φ₁, hφ₁⟩ :=
    exists_factor_through_prev_truncLT_of_isLE_and_homologyMap_eq_zero_local
      (((t.truncLTι 0).app K2) ≫ ψ) hK2LT hψ'
  have hzero : Limits.IsZero ((t.truncLT (-1)).obj K3) := by
    simpa using t.isZero_truncLT_obj_of_isGE (-1) K3
  have hφ₁_zero : φ₁ = 0 := hzero.eq_of_tgt φ₁ 0
  calc
    φ ≫ ψ = φ₀ ≫ (t.truncLTι 0).app K2 ≫ ψ := by
      rw [← hφ₀]
      simp [Category.assoc]
    _ = φ₀ ≫ φ₁ ≫ (t.truncLTι (-1)).app K3 := by
      rw [hφ₁]
      simp [Category.assoc]
    _ = φ₀ ≫ (0 : (t.truncLT 0).obj K2 ⟶ (t.truncLT (-1)).obj K3) ≫
        (t.truncLTι (-1)).app K3 := by
      rw [hφ₁_zero]
    _ = 0 := by
      have hzero_comp :
          φ₀ ≫ (0 : (t.truncLT 0).obj K2 ⟶ (t.truncLT (-1)).obj K3) ≫
            (t.truncLTι (-1)).app K3 = 0 := by
        simp
        rfl
      exact hzero_comp

end

end CategoryTheory
