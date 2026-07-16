import Mathlib
import StacksProject_2024.stacks_project.Chap13.Definition_13_19_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits ComplexShape DerivedCategory DerivedCategory.TStructure
  HomotopyCategory
  HomologicalComplex

noncomputable section

universe v u

attribute [local instance] HasDerivedCategory.standard

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable {K L : CochainComplex 𝒜 ℤ}

/- Domain-style sampling:
- primary domain: hom-vanishing from bounded-above projective cochain complexes, detected by
  strict source support, target homology truncation, and the K-projective comparison from the
  homotopy category to the derived category;
- sampled owner declarations:
  `CochainComplex.ProjectiveMinus`,
  `CochainComplex.IsKProjective.Qh_map_bijective`,
  `CochainComplex.isZero_of_isStrictlyGE`,
  `CochainComplex.isZero_of_isStrictlyLE`,
  `CochainComplex.quasiIso_ιTruncLE_iff`,
  `DerivedCategory.isIso_Q_map_iff_quasiIso`;
- best owner abstraction: `ProjectiveMinus 𝒜` is the source-facing owner for the bounded-above
  projective source complex, and `IsKProjective.Qh_map_bijective` is the canonical comparison
  owner; the target homology-vanishing hypothesis should first be turned into the canonical
  truncation quasi-isomorphism `K.truncLE (n - 1) ⟶ K`, and only then transported across the
  comparison map;
- source/core/bridge triage:
  `source-facing`: the homotopy-category vanishing statement of Lemma `13.19.10`;
  `core/canonical`: `ProjectiveMinus 𝒜`, `IsKProjective.Qh_map_bijective`, and the truncation map
    `K.ιTruncLE (n - 1)`;
  `bridge/view`: the target homology-vanishing condition `∀ i ≥ n, IsZero (K.homology i)` as the
    proof that `K.ιTruncLE (n - 1)` is a quasi-isomorphism, and the resulting derived-category
    vanishing statement for maps out of `Q.obj P`.

Primitive data are the bounded-above projective source `P : ProjectiveMinus 𝒜`, the strict lower
support bound on `P`, the target complex `K`, and the homology-vanishing range on `K`. The
derived-category equality-to-zero statement is only a `bridge/view` corollary of the homotopy
statement through `IsKProjective.Qh_map_bijective`; it is not the owner theorem. -/

local notation "KQ" => quotient 𝒜 (up ℤ)

/-- A cochain complex whose homology vanishes in degrees `≥ n` lies in `D^{≤ n - 1}` after
passing to the derived category. -/
theorem isLE_of_homology_vanishing_ge
    (n : ℤ) (hK : ∀ i : ℤ, n ≤ i → IsZero (K.homology i)) :
    K.IsLE (n - 1) := by
  rw [CochainComplex.isLE_iff]
  intro i hi
  rw [exactAt_iff_isZero_homology]
  exact hK i (by omega)

/-- Under the hypotheses of the main lemma, every morphism `P^• ⟶ K^•` in the homotopy category
`K(\mathcal A)` is zero. -/
theorem homotopyCategory_hom_eq_zero_of_bounded_projective_strictlyGE_and_homology_vanishing_ge
    {P : ProjectiveMinus 𝒜} (n : ℤ)
    (hP_ge : (P : CochainComplex 𝒜 ℤ).IsStrictlyGE n)
    (hK : ∀ i : ℤ, n ≤ i → IsZero (K.homology i))
    (f : (KQ).obj P ⟶ (KQ).obj K) :
    f = 0 := by
  letI : (P : CochainComplex 𝒜 ℤ).IsStrictlyGE n := hP_ge
  letI : K.IsLE (n - 1) := isLE_of_homology_vanishing_ge n hK
  let K' := K.truncLE (n - 1)
  let e := Iso.homCongr ((quotientCompQhIso 𝒜).app P) ((quotientCompQhIso 𝒜).app K)
  let e' := Iso.homCongr ((quotientCompQhIso 𝒜).app P) ((quotientCompQhIso 𝒜).app K')
  have hι : IsIso (Q.map (K.ιTruncLE (n - 1))) := by
    rw [isIso_Q_map_iff_quasiIso]
    infer_instance
  let f' : Q.obj P ⟶ Q.obj K' := e (Qh.map f) ≫ inv (Q.map (K.ιTruncLE (n - 1)))
  obtain ⟨g, hg⟩ :=
      (IsKProjective.Qh_map_bijective (P : CochainComplex 𝒜 ℤ) ((KQ).obj K')).surjective
      (e'.symm f')
  have hg_zero : g = 0 := by
    obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient 𝒜 (up ℤ)).map_surjective g
    have hφ_zero : φ = 0 := by
      ext i
      by_cases hi : i < n
      · exact ((P : CochainComplex 𝒜 ℤ).isZero_of_isStrictlyGE n i hi).eq_of_src _ _
      · exact (K'.isZero_of_isStrictlyLE (n - 1) i (by omega)).eq_of_tgt _ _
    simp [hφ_zero]
  have hf'_zero : f' = 0 := by
    have hgf' : e' (Qh.map g) = f' := by
      rw [hg]
      exact e'.apply_symm_apply f'
    have he'_zero : e' 0 = 0 := by
      change (quotientCompQhIso 𝒜).inv.app P ≫ 0 ≫ (quotientCompQhIso 𝒜).hom.app K' = 0
      simp only [zero_comp, comp_zero]
    rw [← hgf']
    rw [hg_zero]
    simpa using he'_zero
  have hQh_zero : Qh.map f = 0 := by
    have he_zero : e 0 = 0 := by
      change (quotientCompQhIso 𝒜).inv.app P ≫ 0 ≫ (quotientCompQhIso 𝒜).hom.app K = 0
      simp only [zero_comp, comp_zero]
    apply e.injective
    calc
      e (Qh.map f) = f' ≫ Q.map (K.ιTruncLE (n - 1)) := by simp [f']
      _ = 0 := by simp [hf'_zero]
      _ = e 0 := he_zero.symm
  have hQh_zero' : Qh.map f = Qh.map 0 := by
    simpa using hQh_zero
  exact (IsKProjective.Qh_map_bijective P ((KQ).obj K)).injective hQh_zero'

/-- Bridge form of Lemma `13.19.10`: if `P^•` is bounded above with projective terms, if
`P^i = 0` for `i < n`, and if `H^i(K^•) = 0` for all `i ≥ n`, then every morphism
`P^• ⟶ K^•` in `D(\mathcal A)` is zero. -/
theorem derivedCategory_hom_eq_zero_of_bounded_projective_strictlyGE_and_homology_vanishing_ge
    {P : ProjectiveMinus 𝒜} (n : ℤ)
    (hP_ge : (P : CochainComplex 𝒜 ℤ).IsStrictlyGE n)
    (hK : ∀ i : ℤ, n ≤ i → IsZero (K.homology i))
    (f : Q.obj P ⟶ Q.obj K) :
    f = 0 := by
  let e := Iso.homCongr ((quotientCompQhIso 𝒜).app P) ((quotientCompQhIso 𝒜).app K)
  obtain ⟨g, hg⟩ :=
    (IsKProjective.Qh_map_bijective (P : CochainComplex 𝒜 ℤ) ((KQ).obj K)).surjective
      (e.symm f)
  have hg_zero :
      g = 0 :=
    homotopyCategory_hom_eq_zero_of_bounded_projective_strictlyGE_and_homology_vanishing_ge
      n hP_ge hK g
  have hgf : e (Qh.map g) = f := by
    rw [hg]
    exact e.apply_symm_apply f
  have he_zero : e 0 = 0 := by
    change (quotientCompQhIso 𝒜).inv.app P ≫ 0 ≫ (quotientCompQhIso 𝒜).hom.app K = 0
    simp only [zero_comp, comp_zero]
  rw [← hgf]
  rw [hg_zero]
  simpa using he_zero

-- The source-facing statement is the pair of vanishing assertions in the homotopy and derived
-- categories, proved above in their canonical owner forms.
/-- Lemma 13.19.10: let `𝒜` be an abelian category, let `P^•` be a bounded-above cochain complex
of projective objects with `P^i = 0` for `i < n`, and let `K^•` be a cochain complex with
`H^i(K^•) = 0` for all `i ≥ n`. Then every morphism `P^• ⟶ K^•` in both `K(\mathcal A)` and
`D(\mathcal A)` is zero. -/
theorem hom_eq_zero_in_homotopy_and_derivedCategory_of_bounded_projective_strictlyGE_and_homology_vanishing_ge
    {P : ProjectiveMinus 𝒜} (n : ℤ)
    (hP_ge : (P : CochainComplex 𝒜 ℤ).IsStrictlyGE n)
    (hK : ∀ i : ℤ, n ≤ i → IsZero (K.homology i)) :
    (∀ f : (KQ).obj P ⟶ (KQ).obj K, f = 0) ∧ ∀ f : Q.obj P ⟶ Q.obj K, f = 0 := by
  constructor
  · intro f
    exact
      homotopyCategory_hom_eq_zero_of_bounded_projective_strictlyGE_and_homology_vanishing_ge
        n hP_ge hK f
  · intro f
    exact
      derivedCategory_hom_eq_zero_of_bounded_projective_strictlyGE_and_homology_vanishing_ge
        n hP_ge hK f

end CochainComplex
