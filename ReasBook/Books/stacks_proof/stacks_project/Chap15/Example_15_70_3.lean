import stacks_proof.stacks_project.Chap13.Lemma_13_27_3
import stacks_proof.stacks_project.Chap13.Lemma_13_27_10
import stacks_proof.stacks_project.Chap10.Lemma_10_109_9
import stacks_proof.stacks_project.Chap15.Lemma_15_22_11
import stacks_proof.stacks_project.Chap15.Lemma_15_70_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Limits
open DerivedCategory
open Abelian.Ext
open scoped CategoryTheory
open scoped DerivedExt

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R] [IsDedekindDomain R]

local notation "Mod" => ModuleCat R
local notation "DbMod" => Dᵇ(Mod)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/- Domain-style sampling for Example 15.70.3:
- primary domain: injective-dimension bounds in `ModuleCat R` and bounded-derived splitting in
  `Dᵇ(ModuleCat R)`;
- sampled owner declarations:
  `injectiveDimension`,
  `injectiveDimension_le_iff`,
  `HasInjectiveDimensionLT.subsingleton`,
  `isomorphic_to_biproduct_shiftedCohomology_of_ext2_vanishing`;
- best owner abstraction: the source-facing statement is the Dedekind-domain specialization of the
  Chapter 13 bounded-derived splitting theorem. The primitive new input is the owner-level module
  bound `injectiveDimension _ ≤ 1`, while the needed `HasInjectiveDimensionLT _ 2` instance and
  resulting degree-two `Ext`-vanishing are derived through `injectiveDimension_le_iff` and
  `HasInjectiveDimensionLT.subsingleton`;
- primitive vs. derived API: primitive data are the Dedekind-domain injective-dimension bound in
  the canonical owner `injectiveDimension` and the bounded derived object `K : Dᵇ(Mod)`; the
  `HasInjectiveDimensionLT` witness and `Ext`-vanishing input for the splitting theorem are derived
  pointwise from that owner-level bound.
- source/core/bridge triage:
  `source-facing`: the Dedekind-domain specialization of the bounded-derived splitting statement;
  `core/canonical`: `injectiveDimension`, `injectiveDimension_le_iff`,
    `HasInjectiveDimensionLT.subsingleton`, and
    `isomorphic_to_biproduct_shiftedCohomology_of_ext2_vanishing`;
  `bridge/view`: the pointwise passage from the Dedekind-domain injective-dimension bound to the
  degree-two `Ext`-vanishing hypothesis required by the Chapter 13 owner theorem.
-/

omit [IsDedekindDomain R] in
/-- Helper for Example 15.70.3: the ideal inclusion followed by the quotient map is zero in
`ModuleCat R`. -/
private theorem ideal_subtype_comp_mkQ_eq_zero
    (J : Ideal R) :
    ModuleCat.ofHom J.subtype ≫ ModuleCat.ofHom J.mkQ = 0 := by
  -- Check the quotient map on elements: every element of the ideal already maps to zero.
  apply ModuleCat.hom_ext
  ext x
  change Submodule.Quotient.mk ((J.subtype x : R)) = Submodule.Quotient.mk (0 : R)
  rw [Submodule.Quotient.eq]
  simpa using x.2

omit [IsDedekindDomain R] in
/-- Helper for Example 15.70.3: the ideal inclusion and quotient map form the canonical quotient
short complex in `ModuleCat R`. -/
private abbrev ideal_quotient_shortComplex
    (J : Ideal R) :
    CategoryTheory.ShortComplex Mod :=
  CategoryTheory.ShortComplex.mk
    (ModuleCat.ofHom J.subtype)
    (ModuleCat.ofHom J.mkQ)
    (ideal_subtype_comp_mkQ_eq_zero (R := R) J)

omit [IsDedekindDomain R] in
/-- Helper for Example 15.70.3: the canonical quotient sequence
`0 → J → R → R / J → 0` is short exact in `ModuleCat R`. -/
private theorem ideal_quotient_shortExact
    (J : Ideal R) :
    (ideal_quotient_shortComplex (R := R) J).ShortExact := by
  -- Package the standard exact quotient sequence with the canonical mono/epi owners.
  have hMono : Mono (ideal_quotient_shortComplex (R := R) J).f := by
    rw [ModuleCat.mono_iff_injective]
    exact J.subtype_injective
  have hEpi : Epi (ideal_quotient_shortComplex (R := R) J).g := by
    rw [ModuleCat.epi_iff_surjective]
    exact Submodule.mkQ_surjective J
  have hExact : (ideal_quotient_shortComplex (R := R) J).Exact := by
    rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (ideal_quotient_shortComplex (R := R) J)]
    exact LinearMap.exact_subtype_mkQ J
  exact CategoryTheory.ShortComplex.ShortExact.mk' hExact hMono hEpi

/-- Helper for Example 15.70.3: the carrier of an ideal in a Dedekind domain is projective as an
`R`-module. -/
private theorem ideal_subtype_projective_of_isDedekindDomain
    (J : Ideal R) :
    Projective (ModuleCat.of R ↥J) := by
  -- Over a Dedekind domain, ideal carriers are torsion free, hence flat, and they are finitely
  -- presented because the ring is Noetherian.
  letI : Module.FinitePresentation R ↥J := Module.finitePresentation_of_finite R ↥J
  letI : Module.Flat R ↥J :=
    (flat_iff_isTorsionFree_of_isDedekindDomain (A := R) (M := ↥J)).2 inferInstance
  letI : Module.Projective R ↥J :=
    Module.Flat.projective_of_finitePresentation (R := R) (M := ↥J)
  infer_instance

/-- Helper for Example 15.70.3: every quotient `R / J` has projective dimension at most `1`. -/
private theorem ideal_quotient_hasProjectiveDimensionLE_one_of_isDedekindDomain
    (J : Ideal R) :
    HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ J)) 1 := by
  -- Route correction: use the canonical short exact sequence `0 → J → R → R / J → 0`, so the
  -- Dedekind-domain projectivity of `J` and freeness of `R` feed directly into Lemma `10.109.9`.
  have h₁ : HasProjectiveDimensionLE (ModuleCat.of R ↥J) 0 := by
    -- The ideal carrier is projective, hence has projective dimension at most `0`.
    exact
      (projective_iff_hasProjectiveDimensionLE_zero (ModuleCat.of R ↥J)).mp
        (ideal_subtype_projective_of_isDedekindDomain (R := R) J)
  have h₂ : HasProjectiveDimensionLE (ModuleCat.of R R) 1 := by
    -- The free rank-one module is projective, so its projective dimension is at most `1`.
    letI : Projective (ModuleCat.of R R) := inferInstance
    infer_instance
  exact
    CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLE_X₃
      (ideal_quotient_shortExact (R := R) J) 0 h₁ h₂

/-- Helper for Example 15.70.3: the derived extensions from an ideal quotient into `M[0]` vanish
outside degrees `0` and `1`. -/
private theorem ideal_quotient_shiftedExt_eq_zero_outside_zero_one_of_isDedekindDomain
    (M : ModuleCat.{u} R) (J : Ideal R) (i : ℤ)
    (hi : i ∉ Set.Icc (0 : ℤ) 1)
    (e : Ext^i((single₀).obj (ModuleCat.of R (R ⧸ J)), (single₀).obj M)) :
    e = 0 := by
  -- Route correction: negative degrees vanish formally, while nonnegative degrees are transported
  -- to module `Ext` using the typed `Abelian.Ext.homEquiv` pattern from Chapter `15`.
  by_cases hi_neg : i < 0
  · -- Negative shifted-Hom groups from degree-zero module objects vanish.
    exact
      (single_shiftedHom_subsingleton_of_lt_zero
        (𝒜 := ModuleCat.{u} R) (B := ModuleCat.of R (R ⧸ J)) (A := M) i hi_neg).elim e 0
  · have hi_nonneg : 0 ≤ i := le_of_not_gt hi_neg
    have h_one_lt : (1 : ℤ) < i := by
      by_contra hi_le
      apply hi
      exact ⟨hi_nonneg, le_of_not_gt hi_le⟩
    have hi_nat : 2 ≤ Int.toNat i := by
      omega
    have hi_cast : ((Int.toNat i : ℕ) : ℤ) = i := by
      exact Int.toNat_of_nonneg hi_nonneg
    letI : HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ J)) 1 :=
      ideal_quotient_hasProjectiveDimensionLE_one_of_isDedekindDomain (R := R) J
    let e' : CategoryTheory.Abelian.Ext (ModuleCat.of R (R ⧸ J)) M (Int.toNat i) :=
      (CategoryTheory.Abelian.Ext.homEquiv
        (C := ModuleCat.{u} R) (X := ModuleCat.of R (R ⧸ J)) (Y := M)
        (n := Int.toNat i)).symm
          (by simpa [hi_cast] using e)
    have he' : e' = 0 :=
      CategoryTheory.Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT e' 2 hi_nat
    have hext :
        (CategoryTheory.Abelian.Ext.homEquiv
          (C := ModuleCat.{u} R) (X := ModuleCat.of R (R ⧸ J)) (Y := M)
          (n := Int.toNat i)) e' = 0 := by
      -- Apply the bridge equivalence to transport the module-side vanishing back to the derived
      -- shifted-Hom class.
      simpa using
        congrArg
          (CategoryTheory.Abelian.Ext.homEquiv
            (C := ModuleCat.{u} R) (X := ModuleCat.of R (R ⧸ J)) (Y := M)
            (n := Int.toNat i))
          he'
    simpa [e', hi_cast] using hext

/-- Every `R`-module over a Dedekind domain has injective dimension at most `1`. -/
-- Proof sketch: apply Lemma `15.70.2` to the degree-zero derived object of `M`; the hypothesis
-- needed there is that every quotient `R/I` has projective dimension at most `1`, which follows
-- from the fact that every nonzero ideal of a Dedekind domain is finite projective.
theorem injectiveDimension_le_one_of_isDedekindDomain
    (M : ModuleCat.{u} R) :
    injectiveDimension M ≤ 1 := by
  -- Apply Lemma `15.70.2` to the degree-zero derived object `M[0]`.
  have hAmp : HasInjectiveAmplitudeIn ((single₀).obj M) 0 1 := by
    refine
      ((injectiveAmplitudeIn_ext_vanishing_tfae ((single₀).obj M) 0 1).out 2 0).mp ?_
    intro J i hi e
    -- The quotient-module test objects satisfy the required vanishing outside `[0, 1]`.
    exact
      ideal_quotient_shiftedExt_eq_zero_outside_zero_one_of_isDedekindDomain
        (R := R) M J i hi e
  have hExt :
      ∀ (N : ModuleCat.{u} R) (i : ℤ), i ∉ Set.Icc (0 : ℤ) 1 →
        ∀ e : Ext^i((single₀).obj N, (single₀).obj M), e = 0 :=
    ((injectiveAmplitudeIn_ext_vanishing_tfae ((single₀).obj M) 0 1).out 0 1).mp hAmp
  have hzero :
      ∀ (N : ModuleCat.{u} R) (e : CategoryTheory.Abelian.Ext N M 2), e = 0 := by
    intro N e
    have he :
        (CategoryTheory.Abelian.Ext.homEquiv
          (C := ModuleCat.{u} R) (X := N) (Y := M) (n := 2)) e = 0 :=
      hExt N 2 (by simp)
        ((CategoryTheory.Abelian.Ext.homEquiv
          (C := ModuleCat.{u} R) (X := N) (Y := M) (n := 2)) e)
    -- The derived vanishing in degree `2` translates back to the module `Ext²` group.
    have hback :
        (CategoryTheory.Abelian.Ext.homEquiv
          (C := ModuleCat.{u} R) (X := N) (Y := M) (n := 2)).symm
            ((CategoryTheory.Abelian.Ext.homEquiv
              (C := ModuleCat.{u} R) (X := N) (Y := M) (n := 2)) e) = 0 := by
      simpa using
        congrArg
          (CategoryTheory.Abelian.Ext.homEquiv
            (C := ModuleCat.{u} R) (X := N) (Y := M) (n := 2)).symm
          he
    simpa using hback
  have hExt₂ : ∀ N : ModuleCat.{u} R, Subsingleton (CategoryTheory.Abelian.Ext N M 2) := by
    intro N
    refine ⟨?_⟩
    intro e₁ e₂
    rw [hzero N e₁, hzero N e₂]
  have hInj : HasInjectiveDimensionLT M 2 :=
    HasInjectiveDimensionLT.of_ext_vanishing M 2 hExt₂
  exact (injectiveDimension_le_iff M 1).2 hInj

/-- Bridge/view: over a Dedekind domain, every degree-two `Ext` group of modules is trivial. -/
theorem subsingleton_ext_two_of_isDedekindDomain
    (M N : ModuleCat.{u} R) :
    Subsingleton (Ext N M 2) := by
  -- Convert the owner inequality `injectiveDimension M ≤ 1` into the canonical
  -- `HasInjectiveDimensionLT M 2` witness used by the Ext-vanishing API.
  letI : HasInjectiveDimensionLT M 2 :=
    (injectiveDimension_le_iff M 1).mp (injectiveDimension_le_one_of_isDedekindDomain M)
  simpa using HasInjectiveDimensionLT.subsingleton M 2 2 le_rfl N

/-- Example 15.70.3: over a Dedekind domain, every bounded derived object of `R`-modules is
isomorphic to the finite biproduct of its shifted cohomology modules over some interval
containing its cohomological support. -/
-- Proof sketch: apply the Chapter 13 splitting theorem
-- `isomorphic_to_biproduct_shiftedCohomology_of_ext2_vanishing`; its degree-two `Ext`-vanishing
-- hypothesis is supplied by the module-level owner bound above through
-- `injectiveDimension_le_iff` and the canonical owner lemma
-- `HasInjectiveDimensionLT.subsingleton`.
theorem isomorphic_to_biproduct_shiftedCohomology_of_isDedekindDomain
    (K : CategoryTheory.boundedDerivedCategory (ModuleCat.{u} R)) :
    ∃ a b : ℤ,
      Nonempty (K.obj ≅ ⨁ shiftedCohomologyOn (ModuleCat.{u} R) K.obj a b) := by
  -- Apply the Chapter `13` splitting theorem with the uniform degree-two Ext-vanishing obtained
  -- from the module-level injective-dimension bound proved above.
  letI : HasExt (ModuleCat.{u} R) := hasExt_of_hasDerivedCategory (ModuleCat.{u} R)
  have hExt₂ : ∀ A B : ModuleCat.{u} R, Subsingleton (Ext B A 2) := by
    intro A B
    -- Rebuild the degree-two vanishing under the exact `HasExt` instance used by the splitting
    -- theorem, avoiding a universe mismatch from the standalone helper.
    letI : HasInjectiveDimensionLT A 2 :=
      (injectiveDimension_le_iff A 1).mp
        (injectiveDimension_le_one_of_isDedekindDomain (R := R) A)
    simpa using HasInjectiveDimensionLT.subsingleton A 2 2 le_rfl B
  exact isomorphic_to_biproduct_shiftedCohomology_of_ext2_vanishing
    (𝒜 := ModuleCat.{u} R) K
    hExt₂

end

end CategoryTheory
