import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_42_1
import stacks_proof.stacks_project.Chap10.Lemma_10_140_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Algebra

/-- Helper for Chap10 Lemma 10 158 10: the essential-finite-type witness subalgebra has the
ambient field as its fraction field. -/
private lemma essFiniteTypeSubalgebra_isFractionRing
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] :
    IsFractionRing (Algebra.EssFiniteType.subalgebra k K) K := by
  let B : Subalgebra k K := Algebra.EssFiniteType.subalgebra k K
  let S : Submonoid B := Algebra.EssFiniteType.submonoid k K
  have hinj : Function.Injective (algebraMap B K) := by
    intro x y hxy
    exact Subtype.ext hxy
  have hfaith : FaithfulSMul B K :=
    (faithfulSMul_iff_algebraMap_injective B K).mpr hinj
  letI : FaithfulSMul B K := hfaith
  refine IsFractionRing.of_field B K ?_
  intro z
  obtain ⟨⟨x, s⟩, hz⟩ := IsLocalization.surj S z
  refine ⟨x, s, ?_⟩
  have hsunit : IsUnit (algebraMap B K s) := s.2
  have hsne : algebraMap B K s ≠ 0 := by
    intro hzero
    rw [hzero] at hsunit
    exact not_isUnit_zero hsunit
  -- Proof comment: the essential-finite-type localization writes every element of `K` as a
  -- quotient of two elements of the witness subalgebra.
  exact (eq_div_iff_mul_eq hsne).2 hz

/-- Helper for Chap10 Lemma 10 158 10: smooth subalgebras with ambient fraction field give
Stacks-project separability of the field extension. -/
private lemma isSeparableOver_of_smoothSubalgebra_fractionRing
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (A : Subalgebra k K) [Smooth k A] [IsFractionRing A K] :
    IsSeparableOver k K := by
  have hloc : Algebra.FormallySmooth A K :=
    Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors A)
  letI : Algebra.FormallySmooth A K := hloc
  have hformal : Algebra.FormallySmooth k K :=
    Algebra.FormallySmooth.comp k A K
  -- Proof comment: formal smoothness passes from the smooth model through its fraction field.
  exact isSeparableOver_of_formallySmooth_fieldExtension hformal

/-- Helper for Chap10 Lemma 10 158 10: separability makes the generic point of the canonical
essential-finite-type model smooth. -/
private lemma isSmoothAt_bot_essFiniteTypeSubalgebra_of_isSeparableOver
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] (hsep : IsSeparableOver k K) :
    IsSmoothAt k (⊥ : Ideal (Algebra.EssFiniteType.subalgebra k K)) := by
  let B : Subalgebra k K := Algebra.EssFiniteType.subalgebra k K
  have hfrac : IsFractionRing B K :=
    essFiniteTypeSubalgebra_isFractionRing (k := k) (K := K)
  letI : IsFractionRing B K := hfrac
  letI : IsSeparableOver k K := hsep
  letI : Algebra.FormallySmooth k K := Algebra.formallySmooth_of_isSeparableOver
  have hsmoothFrac : Algebra.FormallySmooth k (FractionRing B) := by
    let e : FractionRing B ≃ₐ[k] K :=
      (FractionRing.algEquiv B K).restrictScalars k
    exact (Algebra.FormallySmooth.iff_of_equiv e).2 inferInstance
  have hsmoothAt : IsSmoothAt k (⊥ : Ideal B) := by
    -- Proof comment: Lemma 10.140.9 identifies generic-point smoothness with formal smoothness
    -- of the fraction field.
    exact (isSmoothAt_bot_iff_formallySmooth_fractionRing (R := k) (S := B)).2 hsmoothFrac
  simpa [B] using hsmoothAt

/-- Helper for Chap10 Lemma 10 158 10: smoothness transports from an abstract localization to
the corresponding localization subalgebra of the ambient fraction field. -/
private lemma smooth_restrictScalars_localizationSubalgebra
    {k : Type u} {B : Type v} {K : Type w}
    [CommRing k] [CommRing B] [Field K]
    [Algebra k B] [Algebra B K] [Algebra k K] [IsScalarTower k B K]
    [IsFractionRing B K] (S : Submonoid B) (hS : S ≤ nonZeroDivisors B)
    [Smooth k (Localization S)] :
    Smooth k ((Localization.subalgebra.ofField K S hS).restrictScalars k) := by
  let C : Subalgebra B K := Localization.subalgebra.ofField K S hS
  let e : Localization S ≃ₐ[B] C :=
    IsLocalization.algEquiv S (Localization S) C
  -- Proof comment: the range subalgebra is canonically the same localization, so smoothness
  -- transfers across the localization equivalence after restricting scalars to `k`.
  exact Smooth.of_equiv (A := Localization S) (B := C) (R := k) (e.restrictScalars k)

/-- Helper for Chap10 Lemma 10 158 10: restricting scalars on an intermediate localization
subalgebra does not change its fraction-field structure. -/
private lemma isFractionRing_restrictScalars
    {k : Type u} {B : Type v} {K : Type w}
    [CommSemiring k] [CommSemiring B] [Semifield K]
    [Algebra k B] [Algebra B K] [Algebra k K] [IsScalarTower k B K]
    (C : Subalgebra B K) [IsFractionRing C K] :
    IsFractionRing (C.restrictScalars k) K := by
  -- Proof comment: only the scalar ring of the subalgebra changes; the carrier and inclusion into
  -- the ambient field are unchanged.
  convert (inferInstance : IsFractionRing C K)

/-- Helper for Chap10 Lemma 10 158 10: a smooth generic point gives a smooth subalgebra whose
fraction field is the ambient field. -/
private lemma exists_smoothSubalgebra_fractionRing_of_isSmoothAt_bot
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (B : Subalgebra k K) [Algebra.FiniteType k B] [IsFractionRing B K]
    (h : IsSmoothAt k (⊥ : Ideal B)) :
    ∃ A : Subalgebra k K, Smooth k A ∧ IsFractionRing A K := by
  have hfinitePresentation : Algebra.FinitePresentation k B :=
    (Algebra.FinitePresentation.of_finiteType (R := k) (A := B)).1 inferInstance
  letI : Algebra.FinitePresentation k B := hfinitePresentation
  obtain ⟨g, hg, hsm⟩ :=
    IsSmoothAt.exists_notMem_smooth k (A := B) (⊥ : Ideal B)
  let S : Submonoid B := Submonoid.powers g
  have hS : S ≤ nonZeroDivisors B := by
    intro s hs
    rw [mem_nonZeroDivisors_iff_ne_zero]
    obtain ⟨n, rfl⟩ := hs
    have hg0 : g ≠ 0 := by
      intro hgzero
      have hgmem : g ∈ (⊥ : Ideal B) := by
        simp [hgzero]
      exact hg hgmem
    exact pow_ne_zero n hg0
  let C : Subalgebra B K := Localization.subalgebra.ofField K S hS
  let A : Subalgebra k K := C.restrictScalars k
  refine ⟨A, ?_, ?_⟩
  · letI : Smooth k (Localization S) := hsm
    -- Proof comment: replace the smooth basic open by its image inside the fraction field.
    exact smooth_restrictScalars_localizationSubalgebra
      (k := k) (B := B) (K := K) S hS
  · dsimp [A, C]
    exact isFractionRing_restrictScalars (k := k) (B := B) (K := K)
      (Localization.subalgebra.ofField K S hS)

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
variable [Algebra.EssFiniteType k K]

-- Domain-style sampling:
-- * primary domain: finitely generated field extensions, smooth algebras, and fraction fields;
-- * sampled owners: `Algebra.IsSeparableOver`, `Algebra.Smooth.exists_subalgebra_fg`,
--   `Algebra.EssFiniteType.subalgebra`, and `IsFractionRing` for subalgebras obtained from
--   localizations inside a field;
-- * best owner abstraction here: the source-facing pair consisting of a `k`-subalgebra
--   `A : Subalgebra k K` together with the canonical fraction-field condition `IsFractionRing A K`;
--   smoothness of `A` is the extra geometric property, while the inclusion `A →ₐ[k] K` is derived
--   from the owner `A` itself.
--
-- Proof sketch: choose a domain `A` of finite type over `k` whose fraction field is `K`, using
-- that `K / k` is essentially of finite type, and replace it by its image in `K`, viewed as a
-- `k`-subalgebra. By Lemma `10.140.9`, the extension `K / k` is separable exactly when `A` is
-- smooth at the generic point `(0)`. Since smoothness is local on the source, smoothness at `(0)`
-- is equivalent to replacing `A` by a localization `A_g` that is smooth over `k`, and inside the
-- ambient field `K` that localization is again represented by a smooth `k`-subalgebra whose
-- fraction field is `K`.
/-- Chap10 Lemma 10 158 10: a finitely generated field extension `K / k` is separable in the Stacks
Project sense if and only if `K` is the fraction field of some smooth domain over `k`. In the
canonical owner formulation below, that domain is represented by a smooth `k`-subalgebra of the
ambient field `K` together with the canonical condition that `K` is its fraction field. -/
@[stacks 037X]
theorem isSeparableOver_iff_exists_smooth_domain_with_fractionRing :
    IsSeparableOver k K ↔
      ∃ A : Subalgebra k K, Smooth k A ∧ IsFractionRing A K := by
  constructor
  · intro hsep
    let B : Subalgebra k K := Algebra.EssFiniteType.subalgebra k K
    have hfrac : IsFractionRing B K :=
      essFiniteTypeSubalgebra_isFractionRing (k := k) (K := K)
    letI : IsFractionRing B K := hfrac
    have hsmoothAt :
        IsSmoothAt k (⊥ : Ideal B) := by
      simpa [B] using
        isSmoothAt_bot_essFiniteTypeSubalgebra_of_isSeparableOver
          (k := k) (K := K) hsep
    -- Proof comment: generic smoothness on the finite-type model supplies a smooth basic open
    -- inside `K`, and that open still has fraction field `K`.
    exact exists_smoothSubalgebra_fractionRing_of_isSmoothAt_bot
      (k := k) (K := K) B hsmoothAt
  · rintro ⟨A, hSmooth, hFraction⟩
    letI : Smooth k A := hSmooth
    letI : IsFractionRing A K := hFraction
    -- Proof comment: the converse composes formal smoothness through the fraction-field map.
    exact isSeparableOver_of_smoothSubalgebra_fractionRing (k := k) (K := K) A

end

end Algebra
