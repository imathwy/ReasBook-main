import Mathlib
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.TFAE
import stacks_proof.stacks_project.Chap15.Lemma_15_65_17
import stacks_proof.stacks_project.Chap15.Lemma_15_69_2
import stacks_proof.stacks_project.Chap15.Lemma_15_78_4

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedExt

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single₀" => (ModuleCat.single0Functor : ModuleCat R ⥤ DMod)
local notation "singleCpx₀" => (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ))

/-- Helper for Lemma 15.85.1: projective-amplitude in a fixed interval is invariant under
isomorphism in the derived category. -/
lemma hasProjectiveAmplitudeIn_iff_of_iso
    {K L : DMod} {a b : ℤ} (e : K ≅ L) :
    HasProjectiveAmplitudeIn K a b ↔ HasProjectiveAmplitudeIn L a b := by
  constructor
  · rintro ⟨P, eP, hPge, hPle, hPproj⟩
    exact ⟨P, e.symm ≪≫ eP, hPge, hPle, hPproj⟩
  · rintro ⟨P, eP, hPge, hPle, hPproj⟩
    exact ⟨P, e ≪≫ eP, hPge, hPle, hPproj⟩

/-- Helper for Lemma 15.85.1: a projective module concentrated in degree `0` has
projective-amplitude in `[0, 0]`. -/
lemma single_zero_hasProjectiveAmplitude_of_projective
    (M : ModuleCat R) (hM : Projective M) :
    HasProjectiveAmplitudeIn ((single₀).obj M) 0 0 := by
  refine ⟨(singleCpx₀).obj M, ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app M).symm,
    ?_, ?_, ?_⟩
  · -- Proof comment: the literal single complex is supported in degree `0`.
    simpa using
      (inferInstance : ((singleCpx₀).obj M).IsStrictlyGE (0 : ℤ))
  · -- Proof comment: the same single complex is also supported in degrees `≤ 0`.
    simpa using
      (inferInstance : ((singleCpx₀).obj M).IsStrictlyLE (0 : ℤ))
  · intro i
    by_cases hi : i = 0
    · subst hi
      -- Proof comment: in degree `0`, the single complex is canonically the original module.
      simpa using
        (Module.Projective.of_equiv
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M).toLinearEquiv.symm
          hM)
    · let hzero :
        IsZero (((singleCpx₀).obj M).X i) := by
        simpa [singleCpx₀] using
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (0 : ℤ) M i hi)
      -- Proof comment: every other degree is zero, so its term is automatically projective.
      exact Projective.of_iso hzero.isoZero (by infer_instance)

/-- Helper for Lemma 15.85.1: under the canonical two-term bounds, the homology outside
degrees `-1` and `0` vanishes. -/
lemma two_term_homology_isZero_of_not_mem
    (K : DMod) (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0)
    {n : ℤ} (hn : n ∉ Set.Icc (-1) 0) :
    IsZero ((H n).obj K) := by
  by_cases hlt : n < -1
  · -- Proof comment: below degree `-1`, the lower `t`-structure bound kills homology.
    let _ : K.IsGE (-1) := hKGE
    exact DerivedCategory.isZero_of_isGE K (-1) n hlt
  · have hgt : 0 < n := by
      by_contra hgt
      have hge : -1 ≤ n := by omega
      have hle : n ≤ 0 := by omega
      exact hn ⟨hge, hle⟩
    -- Proof comment: above degree `0`, the upper `t`-structure bound kills homology.
    let _ : K.IsLE 0 := hKLE
    exact DerivedCategory.isZero_of_isLE K 0 n hgt

/-- Helper for Lemma 15.85.1: under the canonical two-term bounds, the textbook condition
`H^{-1}(K)=0` and `H^0(K)` projective is equivalent to projective-amplitude in `[0, 0]`. -/
lemma two_term_source_condition_iff_projective_amplitude_zero_zero
    (K : DMod) (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0) :
    (IsZero ((H (-1)).obj K) ∧ Projective ((H 0).obj K)) ↔
      HasProjectiveAmplitudeIn K 0 0 := by
  constructor
  · rintro ⟨hneg, hproj₀⟩
    have hKGE₀ : K.IsGE 0 := by
      -- Proof comment: the only potentially nonzero homology below `0` is `H^{-1}`, and that
      -- term vanishes by hypothesis.
      rw [DerivedCategory.isGE_iff]
      intro i hi
      by_cases hEq : i = -1
      · subst hEq
        simpa using hneg
      · let _ : K.IsGE (-1) := hKGE
        exact DerivedCategory.isZero_of_isGE K (-1) i (by omega)
    classical
    let hsingle := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K 0
    let N : ModuleCat R := Classical.choose hsingle
    let e : K ≅ (single₀).obj N := Classical.choice (Classical.choose_spec hsingle)
    let eH :
        ((H 0).obj K) ≅ N :=
      (H 0).mapIso e ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) (0 : ℤ)).app N
    have hNproj : Projective N := by
      -- Proof comment: transport projectivity from `H^0(K)` across the concentrated-model
      -- identification.
      exact Projective.of_iso eH hproj₀
    have hAmpSingle : HasProjectiveAmplitudeIn ((single₀).obj N) 0 0 :=
      single_zero_hasProjectiveAmplitude_of_projective N hNproj
    -- Proof comment: replace `K` by its degree-zero single-object model.
    exact (hasProjectiveAmplitudeIn_iff_of_iso e).2 hAmpSingle
  · rintro ⟨P, eP, hPge, hPle, hPproj⟩
    let eSingle :
        DerivedCategory.Q.obj P ≅ (single₀).obj (P.X 0) :=
      representative_single_iso_of_strict_bounds (A := ModuleCat R) P 0
    let e : K ≅ (single₀).obj (P.X 0) := eP ≪≫ eSingle
    have hzeroSingle : IsZero ((H (-1)).obj ((single₀).obj (P.X 0))) := by
      -- Proof comment: a degree-zero single object has no cohomology in degree `-1`.
      exact DerivedCategory.isZero_of_isGE _ 0 (-1) (by omega)
    have hneg : IsZero ((H (-1)).obj K) := by
      -- Proof comment: transport the vanishing across the chosen concentrated-model
      -- comparison.
      exact hzeroSingle.of_iso ((H (-1)).mapIso e)
    let eH :
        ((H 0).obj K) ≅ P.X 0 :=
      (H 0).mapIso e ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) (0 : ℤ)).app (P.X 0)
    have hproj₀ : Projective ((H 0).obj K) := by
      -- Proof comment: the surviving degree-zero term of the projective representative is
      -- projective, and `H^0(K)` is identified with it.
      exact Projective.of_iso eH (hPproj 0)
    exact ⟨hneg, hproj₀⟩

/-- Helper for Lemma 15.85.1: vanishing of all degree-`1` extensions is exactly the vanishing of
the degree-`1` derived-Ext functor. -/
lemma ext_one_vanishing_iff_derivedExtToModuleFunctor_isZero
    (K : DMod) :
    (∀ (N : ModuleCat R), ∀ e : Ext^(1 : ℤ)(K, (single₀).obj N), e = 0) ↔
      IsZero (derivedExtToModuleFunctor K (1 : ℤ)) := by
  constructor
  · intro hExt
    rw [Functor.isZero_iff]
    intro N
    rw [AddCommGrpCat.isZero_iff_subsingleton]
    intro x y
    have hx : x = 0 := hExt N x
    have hy : y = 0 := hExt N y
    simpa [hx, hy]
  · intro hExt
    rw [Functor.isZero_iff] at hExt
    intro N e
    let _ :
        Subsingleton (((derivedExtToModuleFunctor K (1 : ℤ)).obj N) : Type _) :=
      AddCommGrpCat.isZero_iff_subsingleton.1 (hExt N)
    exact Subsingleton.elim _ _

/-- Helper for Lemma 15.85.1: after specializing Lemma `15.69.2` to `a = b = 0`, the boundary
clause is exactly the vanishing of the degree-`1` derived-Ext functor. -/
lemma two_term_boundary_clause_iff_derived_ext_one_functor_is_zero
    (K : DMod) (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0) :
    ((∀ n : ℤ, n ∉ Set.Icc (-1) 0 → IsZero ((H n).obj K)) ∧
        (∀ (N : ModuleCat R), ∀ e : Ext^(1 : ℤ)(K, (single₀).obj N), e = 0)) ↔
      IsZero (derivedExtToModuleFunctor K (1 : ℤ)) := by
  constructor
  · intro h
    -- Proof comment: the homology-vanishing half is automatic from the two-term bounds, so only
    -- the degree-`1` Ext clause remains.
    exact (ext_one_vanishing_iff_derivedExtToModuleFunctor_isZero K).1 h.2
  · intro hExt
    constructor
    · intro n hn
      -- Proof comment: outside `[-1, 0]`, the two-term support bounds already force vanishing.
      exact two_term_homology_isZero_of_not_mem K hKGE hKLE hn
    · -- Proof comment: the zero-functor formulation is exactly the owner-level version of the
      -- source-facing `Ext¹` vanishing clause.
      exact (ext_one_vanishing_iff_derivedExtToModuleFunctor_isZero K).2 hExt

/- Domain-style sampling:
- primary domain: projective-amplitude criteria in the derived category of modules, specialized to
  two-term cohomology and degree-`1` derived `Ext`;
- sampled owner declarations:
  `DerivedCategory.IsGE`,
  `DerivedCategory.IsLE`,
  `HasProjectiveAmplitudeIn` from `Definition_15_69_1`,
  `derivedExtToModuleFunctor` and `projectiveAmplitudeIn_ext_vanishing_tfae` from
    `Lemma_15_69_2`,
  `projectiveAmplitudeIn_perfect_finitelyPresented_ext_tfae_of_isPseudoCoherent` from
    `Lemma_15_78_4`;
- best owner abstraction: the unrestricted degree-`1` vanishing condition is already the canonical
  zero-object statement `IsZero (derivedExtToModuleFunctor K 1)`, while the Noetherian
  specialization should keep the source-facing finite-module `Ext¹` clause explicit and use the
  finitely presented degree-`1` clause from `Lemma_15_78_4` only as the bridge justified by
  Noetherianness. The two-term cohomology-support hypothesis itself should live on the canonical
  t-structure owners `K.IsGE (-1)` and `K.IsLE 0`, with the entrywise vanishing formulation
  demoted to the bridge `DerivedCategory.isGE_iff` / `DerivedCategory.isLE_iff`.

Source/core/bridge triage:
- `source-facing`: the two-term cohomology projectivity criterion of Lemma `15.85.1`;
- `core/canonical`: `K.IsGE (-1)`, `K.IsLE 0`, `HasProjectiveAmplitudeIn`,
  `derivedExtToModuleFunctor`, and
  `projectiveAmplitudeIn_perfect_finitelyPresented_ext_tfae_of_isPseudoCoherent` from
  `Lemma_15_78_4`;
- `bridge/view`: the equivalence between the two-term cohomology condition
  `IsZero (H⁻¹ K) ∧ Projective (H⁰ K)` and the projective-amplitude owner specialized to
  `[0, 0]` under the canonical two-term bounds `K.IsGE (-1)` and `K.IsLE 0`.

Primitive data here are only the canonical two-term support bounds and the two-term cohomology
condition. The unrestricted `Ext¹` test is already canonical upstream as
`IsZero (derivedExtToModuleFunctor K 1)`; the finite-module test in the Noetherian specialization
is source-facing data and should stay visible in the public `TFAE`, with the finitely presented
degree-`1` clause demoted to a companion bridge.
-/

-- Proof sketch: apply Lemma `15.69.2` with `a = b = 0`. Under the hypothesis that the
-- canonical two-term bounds `K.IsGE (-1)` and `K.IsLE 0`, projective-amplitude in `[0, 0]`
-- means exactly that `H⁻¹(K) = 0` and `H⁰(K)` is projective, while
-- `IsZero (derivedExtToModuleFunctor K 1)` is the same as vanishing of `Ext¹_R(K, M)` for every
-- `R`-module `M`.
/-- Lemma 15.85.1: for a derived `R`-complex whose cohomology is concentrated in degrees `-1`
and `0`, encoded by `K.IsGE (-1)` and `K.IsLE 0`, the condition `H⁻¹(K) = 0` together with
projectivity of `H⁰(K)` is equivalent to the vanishing of `Ext¹_R(K, M)` for every
`R`-module `M`. -/
@[stacks 0G9C]
theorem two_term_cohomology_projective_iff_ext1_vanishes
    (K : DMod)
    (hKGE : K.IsGE (-1))
    (hKLE : K.IsLE 0) :
    (IsZero ((H (-1)).obj K) ∧ Projective ((H 0).obj K)) ↔
      IsZero (derivedExtToModuleFunctor K (1 : ℤ)) := by
  -- Proof comment: first replace the source-facing two-term condition by projective-amplitude in
  -- `[0, 0]`, then specialize the Chapter 15 amplitude/Ext criterion at `a = b = 0`, and
  -- finally rewrite the boundary clause back to the canonical degree-`1` derived-Ext functor.
  calc
    (IsZero ((H (-1)).obj K) ∧ Projective ((H 0).obj K)) ↔
        HasProjectiveAmplitudeIn K 0 0 :=
      two_term_source_condition_iff_projective_amplitude_zero_zero K hKGE hKLE
    _ ↔
        ((∀ n : ℤ, n ∉ Set.Icc (-1) 0 → IsZero ((H n).obj K)) ∧
          (∀ (N : ModuleCat R), ∀ e : Ext^(1 : ℤ)(K, (single₀).obj N), e = 0)) := by
        simpa using
          ((projectiveAmplitudeIn_ext_vanishing_tfae (R := R) K 0 0).out 0 3)
    _ ↔ IsZero (derivedExtToModuleFunctor K (1 : ℤ)) :=
      two_term_boundary_clause_iff_derived_ext_one_functor_is_zero K hKGE hKLE

end

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single₀" => (ModuleCat.single0Functor : ModuleCat R ⥤ DMod)

/-- Helper for Lemma 15.85.1: a zero module is finite over any ring. -/
lemma module_finite_of_isZero {M : ModuleCat R} (hM : IsZero M) :
    Module.Finite R M := by
  -- Proof comment: transport the obvious finite-generation witness from the zero module.
  simpa using
    (Module.Finite.equiv hM.isoZero.toLinearEquiv.symm
      (by infer_instance : Module.Finite R (0 : ModuleCat R)))

/-- Helper for Lemma 15.85.1: over a Noetherian ring, finite cohomology in degrees `-1` and `0`
plus the canonical two-term support bounds imply pseudo-coherence. -/
lemma two_term_is_pseudo_coherent_of_noetherian_finite_cohomology
    (K : DMod) (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0)
    (hfin_neg_one : Module.Finite R ((H (-1)).obj K))
    (hfin_zero : Module.Finite R ((H 0).obj K)) :
    K.IsPseudoCoherent := by
  apply (isPseudoCoherent_iff_boundedAbove_and_homology_finite (R := R) K).2
  constructor
  · -- Proof comment: the upper two-term bound is exactly a bounded-above witness.
    rw [derivedCategory_t_minus_iff]
    refine ⟨0, ?_⟩
    intro i hi
    let _ : K.IsLE 0 := hKLE
    exact DerivedCategory.isZero_of_isLE K 0 i hi
  · intro i
    by_cases hneg : i = -1
    · subst hneg
      simpa using hfin_neg_one
    by_cases hzero : i = 0
    · subst hzero
      simpa using hfin_zero
    have hizero : IsZero ((H i).obj K) := by
      have hi_mem : i ∉ Set.Icc (-1) 0 := by
        simp [hneg, hzero]
      exact two_term_homology_isZero_of_not_mem K hKGE hKLE hi_mem
    -- Proof comment: every remaining homology module is zero, hence finite.
    exact module_finite_of_isZero hizero

/-- Helper for Lemma 15.85.1: after specializing Lemma `15.78.4` to `a = b = 0`, the finitely
presented boundary clause is equivalent to vanishing of `Ext¹` against all finite modules. -/
lemma two_term_finitely_presented_boundary_clause_iff_finite_module_ext_one_vanishing
    (K : DMod) (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0) :
    ((∀ n : ℤ, n ∉ Set.Icc (-1) 0 → IsZero ((H n).obj K)) ∧
        (∀ (N : ModuleCat R) [Module.FinitePresentation R N],
          ∀ e : Ext^(1 : ℤ)(K, (single₀).obj N), e = 0)) ↔
      ∀ (N : ModuleCat R), Module.Finite R N →
        ∀ e : Ext^(1 : ℤ)(K, (single₀).obj N), e = 0 := by
  constructor
  · intro h N hN e
    let _ : Module.FinitePresentation R N := Module.finitePresentation_of_finite R N
    -- Proof comment: over a Noetherian ring, finite modules are finitely presented.
    exact h.2 N e
  · intro h
    constructor
    · intro n hn
      -- Proof comment: the homology-vanishing half is automatic from the fixed two-term support
      -- bounds.
      exact two_term_homology_isZero_of_not_mem K hKGE hKLE hn
    · intro N _ e
      have hN : Module.Finite R N := by infer_instance
      -- Proof comment: finitely presented modules are in particular finite, so the explicit
      -- finite-module vanishing hypothesis applies.
      exact h N hN e

-- Proof sketch: the finiteness of `H⁻¹(K)` and `H⁰(K)` together with the canonical two-term
-- bounds `K.IsGE (-1)` and `K.IsLE 0` implies that `K` is pseudo-coherent by Lemma `15.65.17`.
-- Apply Lemma `15.78.4` with `a = b = 0`, and use the canonical bridge
-- `Module.finitePresentation_of_finite` to replace the finitely presented `Ext¹` test by the
-- source-facing finite-module version with finiteness exposed as an explicit hypothesis.
/-- Over a Noetherian ring, a two-term derived complex with finite cohomology in degrees `-1`
and `0` satisfies the same projectivity criterion when `Ext¹_R(K, M)` is tested only on finite
`R`-modules. -/
theorem two_term_cohomology_projective_ext1_tfae_of_noetherian
    (K : DMod)
    (hKGE : K.IsGE (-1))
    (hKLE : K.IsLE 0)
    (hfin_neg_one : Module.Finite R ((H (-1)).obj K))
    (hfin_zero : Module.Finite R ((H 0).obj K)) :
    List.TFAE [
      IsZero ((H (-1)).obj K) ∧ Projective ((H 0).obj K),
      IsZero (derivedExtToModuleFunctor K (1 : ℤ)),
      ∀ (M : ModuleCat R), Module.Finite R M →
        ∀ e : Ext^(1 : ℤ)(K, (single₀).obj M), e = 0
    ] := by
  let hPc : K.IsPseudoCoherent :=
    two_term_is_pseudo_coherent_of_noetherian_finite_cohomology
      K hKGE hKLE hfin_neg_one hfin_zero
  tfae_have 1 ↔ 2 := by
    -- Proof comment: the first equivalence is exactly the unrestricted `Ext¹` criterion proved
    -- above.
    exact two_term_cohomology_projective_iff_ext1_vanishes K hKGE hKLE
  tfae_have 1 ↔ 3 := by
    -- Proof comment: replace the source-facing two-term condition by projective-amplitude in
    -- `[0, 0]`, then specialize the pseudo-coherent finitely presented `Ext` criterion and
    -- convert it to the explicit finite-module clause.
    calc
      (IsZero ((H (-1)).obj K) ∧ Projective ((H 0).obj K)) ↔
          HasProjectiveAmplitudeIn K 0 0 :=
        two_term_source_condition_iff_projective_amplitude_zero_zero K hKGE hKLE
      _ ↔
          ((∀ n : ℤ, n ∉ Set.Icc (-1) 0 → IsZero ((H n).obj K)) ∧
            (∀ (N : ModuleCat R) [Module.FinitePresentation R N],
              ∀ e : Ext^(1 : ℤ)(K, (single₀).obj N), e = 0)) := by
          simpa using
            ((projectiveAmplitudeIn_perfect_finitelyPresented_ext_tfae_of_isPseudoCoherent
              (R := R) K 0 0 hPc).out 0 4)
      _ ↔
          ∀ (M : ModuleCat R), Module.Finite R M →
            ∀ e : Ext^(1 : ℤ)(K, (single₀).obj M), e = 0 :=
        two_term_finitely_presented_boundary_clause_iff_finite_module_ext_one_vanishing
          K hKGE hKLE
  tfae_finish

end

end CategoryTheory
