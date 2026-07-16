import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_39_18

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

variable (A : Type u) [CommRing A]

/-- Definition 15.105.1 (1): a commutative ring is absolutely flat if every `A`-module is flat
over `A`. We package the standard equivalent elementwise criterion so the owner is independent of
the module universe; the flatness of arbitrary `A`-modules is exposed as derived API below. -/
@[stacks 092B]
class IsAbsolutelyFlatRing : Prop where
  /-- Every element of `A` admits a von Neumann regular factorization. -/
  exists_factor (a : A) : ∃ b : A, a = a ^ 2 * b

section

variable (K : Type u) [Field K]

/-- Helper for Definition 15.105.1: every element of a field admits the required factorization. -/
lemma field_exists_factor (a : K) : ∃ b : K, a = a ^ 2 * b := by
  by_cases ha : a = 0
  · -- The zero element is handled by the trivial factor.
    refine ⟨0, ?_⟩
    simp [ha]
  · -- For a nonzero element, its inverse gives the von Neumann regular factorization.
    refine ⟨a⁻¹, ?_⟩
    calc
      a = a * 1 := by simp
      _ = a * (a * a⁻¹) := by simp [ha]
      _ = a ^ 2 * a⁻¹ := by ring

/-- Every field is an absolutely flat ring. -/
instance : IsAbsolutelyFlatRing K where
  exists_factor := field_exists_factor K

end

/-- Helper for Definition 15.105.1: the elementwise factorization criterion localizes. -/
lemma localization_exists_factor {R : Type u} [CommRing R] [IsAbsolutelyFlatRing R]
    (M : Submonoid R) (S : Type v) [CommRing S] [Algebra R S] [IsLocalization M S] (z : S) :
    ∃ w : S, z = z ^ 2 * w := by
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M z
  obtain ⟨b, hb⟩ := IsAbsolutelyFlatRing.exists_factor (A := R) a
  refine ⟨algebraMap R S (b * s), ?_⟩
  change IsLocalization.mk' S a s = (IsLocalization.mk' S a s) ^ 2 * algebraMap R S (b * ↑s)
  calc
    IsLocalization.mk' S a s = IsLocalization.mk' S (a * a * (b * ↑s)) (s * s) := by
      -- Cross-multiplication reduces the localization identity to the original factorization.
      apply (IsLocalization.mk'_eq_iff_eq'.2)
      have hbase : a * (↑s * ↑s) = (a * a * (b * ↑s)) * ↑s := by
        nth_rewrite 1 [hb]
        ring
      exact congrArg (algebraMap R S) hbase
    _ = IsLocalization.mk' S (a * a) (s * s) * IsLocalization.mk' S (b * ↑s) 1 := by
      rw [← IsLocalization.mk'_mul]
      simp
    _ = IsLocalization.mk' S (a * a) (s * s) * algebraMap R S (b * ↑s) := by
      rw [IsLocalization.mk'_one]
    _ = (IsLocalization.mk' S a s) ^ 2 * algebraMap R S (b * ↑s) := by
      rw [pow_two, IsLocalization.mk'_mul]

/-- Helper for Definition 15.105.1: a local ring satisfying the factorization criterion is a
field. -/
lemma isField_of_localRing_exists_factor {R : Type u} [CommRing R] [IsLocalRing R]
    (hexists : ∀ r : R, ∃ s : R, r = r ^ 2 * s) : IsField R := by
  refine IsField.mk ?_ (fun x y ↦ mul_comm x y) ?_
  · exact ⟨0, 1, zero_ne_one⟩
  · intro a ha0
    obtain ⟨b, hb⟩ := hexists a
    have hzero : a * (1 - a * b) = 0 := by
      calc
        a * (1 - a * b) = a - a * (a * b) := by ring
        _ = a - a ^ 2 * b := by simp [pow_two, mul_assoc]
        _ = 0 := by
          -- Rewrite exactly the leading copy of `a` using the factorization and normalize.
          nth_rewrite 1 [hb]
          ring
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (a * b) with hab | h1ab
    · -- If `a * b` is a unit, then `a` already has a right inverse.
      rcases hab with ⟨u, hu⟩
      refine ⟨b * ↑u⁻¹, ?_⟩
      calc
        a * (b * ↑u⁻¹) = (a * b) * ↑u⁻¹ := by ring
        _ = (↑u : R) * ↑u⁻¹ := by rw [hu]
        _ = 1 := by simp
    · -- If `1 - a * b` is a unit, the displayed zero-product forces `a = 0`.
      exfalso
      rcases h1ab with ⟨u, hu⟩
      have hau : a * (↑u : R) = 0 := by
        simpa [hu] using hzero
      have ha : a = 0 := by
        calc
          a = a * 1 := by simp
          _ = a * ((↑u : R) * ↑u⁻¹) := by simp
          _ = (a * ↑u) * ↑u⁻¹ := by ring
          _ = 0 := by simp [hau]
      exact ha0 ha

/-- Helper for Definition 15.105.1: every prime localization of an absolutely flat ring is a
field. -/
lemma isField_atPrime_of_isAbsolutelyFlatRing {R : Type u} [CommRing R] [IsAbsolutelyFlatRing R]
    (p : PrimeSpectrum R) : IsField (Localization.AtPrime p.asIdeal) := by
  letI : p.asIdeal.IsPrime := p.isPrime
  letI : IsLocalRing (Localization.AtPrime p.asIdeal) :=
    IsLocalization.AtPrime.isLocalRing (Localization.AtPrime p.asIdeal) p.asIdeal
  -- Apply the local-ring criterion after transporting the factorization axiom to the localization.
  apply isField_of_localRing_exists_factor
  intro z
  simpa using
    localization_exists_factor (R := R) (M := p.asIdeal.primeCompl)
      (S := Localization.AtPrime p.asIdeal) z

/-- Every additive `A`-module is flat over an absolutely flat ring. -/
instance {M : Type w} [AddCommGroup M] [Module A M] [IsAbsolutelyFlatRing A] : Module.Flat A M := by
  -- Flatness is checked on all prime localizations.
  refine (flat_iff_flat_localizedModule_atPrime (R := A) (M := M)).2 ?_
  intro p
  -- Each prime localization is a field by the elementwise factorization criterion.
  let hfield : IsField (Localization.AtPrime p.asIdeal) :=
    isField_atPrime_of_isAbsolutelyFlatRing (R := A) p
  letI : Field (Localization.AtPrime p.asIdeal) := hfield.toField
  infer_instance

section

variable {ι : Type u} (A : ι → Type v) [∀ i, CommRing (A i)] [∀ i, IsAbsolutelyFlatRing (A i)]

/-- Coordinatewise products of absolutely flat rings are absolutely flat. -/
instance : IsAbsolutelyFlatRing ((i : ι) → A i) where
  exists_factor a := by
    classical
    choose b hb using fun i ↦ (inferInstance : IsAbsolutelyFlatRing (A i)).exists_factor (a i)
    refine ⟨b, ?_⟩
    ext i
    simpa [pow_two] using hb i

end

namespace Algebra

variable (B : Type v) [CommRing B] [Algebra A B]

/-- Definition 15.105.1 (2): a ring map `A → B` is weakly étale, or absolutely flat, if `B` is
flat over `A` and the multiplication map `B ⊗[A] B → B` is flat. -/
@[stacks 092B]
class IsWeaklyEtale : Prop where
  /-- The structure map `A → B` is flat, expressed on the underlying `A`-module `B`. -/
  moduleFlat : Module.Flat A B
  /-- The multiplication map `B ⊗[A] B → B` is flat. -/
  flat_tensorSquareMultiplication :
    (Algebra.TensorProduct.lmul' A : B ⊗[A] B →ₐ[A] B).Flat

/-- A weakly étale `A`-algebra is flat over `A`. -/
instance [h : IsWeaklyEtale A B] : Module.Flat A B :=
  h.moduleFlat

namespace IsWeaklyEtale

/-- The structure map of a weakly étale algebra is flat. -/
theorem flat (h : IsWeaklyEtale A B) : (algebraMap A B).Flat :=
  RingHom.flat_algebraMap_iff.mpr h.moduleFlat

end IsWeaklyEtale

section

variable {A}

/-- Helper for Definition 15.105.1: the tensor-square multiplication map for the identity algebra
is bijective, hence flat. -/
lemma tensorSquareMul_self_flat (A : Type u) [CommRing A] :
    (Algebra.TensorProduct.lmul' A : A ⊗[A] A →ₐ[A] A).Flat := by
  have hmul_eq_lid :
      (Algebra.TensorProduct.lmul' A : A ⊗[A] A →ₐ[A] A) =
        (Algebra.TensorProduct.lid A A).toAlgHom := rfl
  refine RingHom.Flat.of_bijective ?_
  constructor
  · -- Injectivity follows because `lmul'` agrees definitionally with the tensor-product unitor.
    intro x y hxy
    rw [hmul_eq_lid] at hxy
    exact (Algebra.TensorProduct.lid A A).injective hxy
  · -- Surjectivity is witnessed by the pure tensor `1 ⊗ a`.
    intro a
    refine ⟨1 ⊗ₜ[A] a, ?_⟩
    simp [Algebra.TensorProduct.lmul'_apply_tmul]

/-- The identity map of a commutative ring is weakly étale. -/
instance : IsWeaklyEtale A A where
  moduleFlat := inferInstance
  flat_tensorSquareMultiplication := tensorSquareMul_self_flat A

end

end Algebra
