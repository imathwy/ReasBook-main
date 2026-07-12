import Mathlib
import StacksProject_2024.Chap10.Lemma_10_131_10
import StacksProject_2024.Chap10.Lemma_10_20_1_Nakayama_s_lemma

open Algebra
open scoped TensorProduct
open KaehlerDifferential

universe u v

section

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

section SmoothSection

variable [Algebra.Smooth R S] (σ : S →ₐ[R] R)
  (hσ : Function.LeftInverse σ (algebraMap R S))

include hσ

/-- Helper for Lemma 10.139.4: a section of `algebraMap R S` makes `σ` surjective. -/
theorem smooth_section_sigma_surjective :
    Function.Surjective σ := by
  -- Evaluate `σ` on the image of any `r : R`.
  intro r
  exact ⟨algebraMap R S r, hσ r⟩

/-- Helper for Lemma 10.139.4: the reduced quotient `S / ker σ` is canonically `R` via the chosen
section. -/
noncomputable def smooth_section_quotientKerAlgEquiv :
    (S ⧸ RingHom.ker σ) ≃ₐ[R] R :=
  Ideal.quotientKerAlgEquivOfRightInverse (f := σ) (g := algebraMap R S) hσ

section

omit [CommRing S] [Algebra R S] [Algebra.Smooth R S] σ hσ

/-- Helper for Lemma 10.139.4: evaluating a polynomial ring at the zero tuple kills exactly the
variable ideal. This is the source-side identification `P/J ≃ R` for `P = R[x_1, ..., x_d]` and
`J = (x_1, ..., x_d)`. -/
theorem aeval_zero_ker_eq_idealOfVars {d : ℕ} :
    RingHom.ker (MvPolynomial.aeval (R := R) (0 : Fin d → R)).toRingHom =
      MvPolynomial.idealOfVars (Fin d) R := by
  ext p
  constructor
  · intro hp
    -- On the source side, vanishing at the zero tuple means the constant coefficient is zero.
    rw [MvPolynomial.idealOfVars, ← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    have hconst : MvPolynomial.constantCoeff p = 0 := by
      simpa [RingHom.mem_ker, MvPolynomial.aeval_zero] using hp
    -- Every monomial in the support is therefore nonconstant, so some variable occurs in it.
    have hm_ne_zero : m ≠ 0 := by
      intro hm0
      have hmem : 0 ∈ p.support := by
        simpa [hm0] using hm
      exact (MvPolynomial.mem_support_iff.mp hmem) <|
        by simpa [MvPolynomial.constantCoeff_eq] using hconst
    obtain ⟨i, hi⟩ : ∃ i : Fin d, m i ≠ 0 := by
      by_contra h
      apply hm_ne_zero
      ext i
      by_contra hmi
      exact h ⟨i, hmi⟩
    exact ⟨i, Set.mem_univ _, hi⟩
  · intro hp
    -- Conversely, membership in the variable ideal forbids a constant monomial in the support.
    rw [MvPolynomial.idealOfVars, ← Set.image_univ, MvPolynomial.mem_ideal_span_X_image] at hp
    have hnot : (0 : Fin d →₀ ℕ) ∉ p.support := by
      intro h0
      rcases hp 0 h0 with ⟨i, -, hi⟩
      exact hi (by simp)
    have hcoeff : p.coeff 0 = 0 := Finsupp.notMem_support_iff.mp hnot
    simpa [RingHom.mem_ker, MvPolynomial.aeval_zero, MvPolynomial.constantCoeff_eq] using hcoeff

/-- Helper for Lemma 10.139.4: the polynomial quotient by the variable ideal is canonically `R`
via evaluation at the zero tuple. -/
noncomputable def idealOfVars_quotientAlgEquiv {d : ℕ} :
    (MvPolynomial (Fin d) R ⧸ MvPolynomial.idealOfVars (Fin d) R) ≃ₐ[R] R :=
  (Ideal.quotientEquivAlgOfEq (R₁ := R) (A := MvPolynomial (Fin d) R)
      (aeval_zero_ker_eq_idealOfVars (R := R) (d := d)).symm).trans <|
    Ideal.quotientKerAlgEquivOfRightInverse
      (f := MvPolynomial.aeval (R := R) (0 : Fin d → R))
      (g := algebraMap R (MvPolynomial (Fin d) R))
      (by
        -- The polynomial inclusion is a right inverse to evaluation at the zero tuple.
        intro r
        simp)

end

section

omit hσ

/-- Helper for Lemma 10.139.4: the chosen kernel lifts define the polynomial map used in the
source proof. -/
noncomputable def cotangent_lift_polynomial_map {d : ℕ}
    (f : Fin d → RingHom.ker σ) :
    MvPolynomial (Fin d) R →ₐ[R] S :=
  MvPolynomial.aeval fun i ↦ ((f i : RingHom.ker σ) : S)

/-- Helper for Lemma 10.139.4: the polynomial map sends the variable ideal into `ker σ`. -/
theorem cotangent_lift_polynomial_map_idealOfVars_le_ker {d : ℕ}
    (f : Fin d → RingHom.ker σ) :
    Ideal.map (cotangent_lift_polynomial_map (R := R) (S := S) (σ := σ) f).toRingHom
      (MvPolynomial.idealOfVars (Fin d) R) ≤ RingHom.ker σ := by
  -- It suffices to check the generators `X i`, because their images are exactly the chosen lifts.
  rw [Ideal.map_le_iff_le_comap]
  change Ideal.span (Set.range MvPolynomial.X) ≤
    Ideal.comap (cotangent_lift_polynomial_map (R := R) (S := S) (σ := σ) f).toRingHom
      (RingHom.ker σ)
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  change (cotangent_lift_polynomial_map (R := R) (S := S) (σ := σ) f) (MvPolynomial.X i) ∈
    RingHom.ker σ
  simpa [cotangent_lift_polynomial_map] using (f i).property

/-- Helper for Lemma 10.139.4: the variable ideal lies in the comap of `ker σ`, so the cotangent
map for the polynomial lift is defined on `J/J²`. -/
theorem cotangent_lift_idealOfVars_le_comap_ker {d : ℕ}
    (f : Fin d → RingHom.ker σ) :
    MvPolynomial.idealOfVars (Fin d) R ≤
      Ideal.comap (cotangent_lift_polynomial_map (R := R) (S := S) (σ := σ) f).toRingHom
        (RingHom.ker σ) := by
  -- This is the comap form of the previous containment, matching the cotangent-map API.
  simpa [Ideal.map_le_iff_le_comap] using
    cotangent_lift_polynomial_map_idealOfVars_le_ker (R := R) (S := S) (σ := σ) f

/-- Helper for Lemma 10.139.4: on the cotangent class of each variable, the induced cotangent map
is the cotangent class of the chosen kernel lift. -/
theorem cotangent_lift_mapCotangent_variable {d : ℕ}
    (f : Fin d → RingHom.ker σ) (i : Fin d) :
    Ideal.mapCotangent (MvPolynomial.idealOfVars (Fin d) R) (RingHom.ker σ)
        (cotangent_lift_polynomial_map (R := R) (S := S) (σ := σ) f)
        (cotangent_lift_idealOfVars_le_comap_ker (R := R) (S := S) (σ := σ) f)
        ((MvPolynomial.idealOfVars (Fin d) R).toCotangent
          ⟨MvPolynomial.X i, by
            simpa [MvPolynomial.idealOfVars] using
              (Ideal.subset_span (Set.mem_range_self i) :
                MvPolynomial.X i ∈ MvPolynomial.idealOfVars (Fin d) R)⟩) =
      (RingHom.ker σ).toCotangent (f i) := by
  -- `mapCotangent_toCotangent` reduces the claim to the defining formula `Ψ(X i) = f i`.
  simp [Ideal.mapCotangent_toCotangent, cotangent_lift_polynomial_map]

/-- Helper for Lemma 10.139.4: if the lifted kernel classes realize the chosen basis `b`, then the
induced cotangent map sends the variable class at `i` to the basis vector `b i`. -/
theorem cotangent_lift_mapCotangent_variable_basis {d : ℕ}
    (b : Module.Basis (Fin d) R (RingHom.ker σ).Cotangent)
    (f : Fin d → RingHom.ker σ)
    (hf : ∀ i, (RingHom.ker σ).toCotangent (f i) = b i)
    (i : Fin d) :
    Ideal.mapCotangent (MvPolynomial.idealOfVars (Fin d) R) (RingHom.ker σ)
        (cotangent_lift_polynomial_map (R := R) (S := S) (σ := σ) f)
        (cotangent_lift_idealOfVars_le_comap_ker (R := R) (S := S) (σ := σ) f)
        ((MvPolynomial.idealOfVars (Fin d) R).toCotangent
          ⟨MvPolynomial.X i, by
            simpa [MvPolynomial.idealOfVars] using
              (Ideal.subset_span (Set.mem_range_self i) :
                MvPolynomial.X i ∈ MvPolynomial.idealOfVars (Fin d) R)⟩) =
      b i := by
  -- This packages the source data `hf` into the cotangent-map computation for later use.
  rw [cotangent_lift_mapCotangent_variable (R := R) (S := S) (σ := σ) f i, hf i]

/-- Helper for Lemma 10.139.4: the polynomial map respects all powers of the adic ideals. -/
theorem cotangent_lift_polynomial_map_pow_idealOfVars_le_ker_pow {d : ℕ}
    (f : Fin d → RingHom.ker σ) (n : ℕ) :
    Ideal.map (cotangent_lift_polynomial_map (R := R) (S := S) (σ := σ) f).toRingHom
      ((MvPolynomial.idealOfVars (Fin d) R) ^ n) ≤ (RingHom.ker σ) ^ n := by
  -- Once the variable ideal maps into `ker σ`, the same is true for all powers.
  simpa [Ideal.map_pow] using
    Ideal.pow_right_mono
      (cotangent_lift_polynomial_map_idealOfVars_le_ker (R := R) (S := S) (σ := σ) f) n

/-- Helper for Lemma 10.139.4: the polynomial map descends to every truncation by powers of the
variable ideal and `ker σ`. -/
noncomputable def cotangent_lift_truncated_map {d : ℕ}
    (f : Fin d → RingHom.ker σ) (n : ℕ) :
    MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n →ₐ[R]
      S ⧸ (RingHom.ker σ) ^ n :=
  Ideal.Quotient.liftₐ ((MvPolynomial.idealOfVars (Fin d) R) ^ n)
    (((Ideal.Quotient.mkₐ R ((RingHom.ker σ) ^ n)).comp
      (cotangent_lift_polynomial_map (R := R) (S := S) (σ := σ) f))) <|
    by
      intro x hx
      -- Elements in `J ^ n` map into `I ^ n`, hence vanish in the quotient.
      change Ideal.Quotient.mk ((RingHom.ker σ) ^ n)
          ((cotangent_lift_polynomial_map (R := R) (S := S) (σ := σ) f) x) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr <|
        (cotangent_lift_polynomial_map_pow_idealOfVars_le_ker_pow
          (R := R) (S := S) (σ := σ) f n) <|
          Ideal.mem_map_of_mem _ hx

/-- Helper for Lemma 10.139.4: the descended truncation maps commute with the quotient transition
maps. -/
theorem cotangent_lift_truncated_map_compatible {d : ℕ}
    (f : Fin d → RingHom.ker σ) {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp
        (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n) =
      (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f m).comp
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)) := by
  -- Both sides descend the same polynomial map and then reduce modulo the smaller power.
  refine Ideal.Quotient.algHom_ext _ ?_
  ext x
  simp [cotangent_lift_truncated_map, cotangent_lift_polynomial_map]

end

end SmoothSection

end
