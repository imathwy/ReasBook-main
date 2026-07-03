import Mathlib
import StacksProject_2024.Chap10.Lemma_10_131_10
import StacksProject_2024.Chap10.Lemma_10_20_1_Nakayama_s_lemma

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra
open scoped TensorProduct
open KaehlerDifferential

universe u v

section

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/- Domain-style sampling for Lemma 10.139.4:
- primary domain: smooth commutative algebra retractions, their conormal module, and the induced
  formal local structure on adic completions;
- sampled owner declarations:
  `Algebra.Smooth`,
  `KaehlerDifferential.finite`,
  `FormallySmooth.projective_kaehlerDifferential`,
  `retractionKerCotangentToTensorEquivSection`;
- best owner abstraction: the smooth owner `Algebra.Smooth R S` together with the canonical
  conormal owner `(RingHom.ker σ).Cotangent` attached to a section `σ : S →ₐ[R] R`;
- primitive data: the smooth `R`-algebra `S`, the section `σ`, and the left-inverse equation `hσ`;
- derived API: finiteness/projectivity of the conormal module and, after a freeness hypothesis, the
  existence of a formal-power-series description of the `ker σ`-adic completion.

Source/core/bridge triage:
- `source-facing`: the two theorems below about the conormal module and the completed algebra of a
  smooth retraction;
- `core/canonical`: `Algebra.Smooth`, the Kähler/formal-smooth owner theorems, and the canonical
  conormal owner `RingHom.ker σ`;
- `bridge/view`: the textbook identification `I/I²` with `(RingHom.ker σ).Cotangent` and the
  resulting power-series presentation of the completion. -/

section SmoothSection

variable [Algebra.Smooth R S] (σ : S →ₐ[R] R)
  (hσ : Function.LeftInverse σ (algebraMap R S))

include hσ

-- Proof sketch: apply the split conormal sequence for the section `σ : S →ₐ[R] R` to identify
-- `(RingHom.ker σ).Cotangent` with a base change of `Ω[S⁄R]`; smoothness makes
-- `Ω[S⁄R]` finite and projective over `S`, and restriction along the section preserves those
-- finiteness and projectivity properties over `R`.
/-- Lemma 10.139.4: if `R → S` is smooth and `σ : S →ₐ[R] R` is a left inverse to the structure
map, then the conormal module `I/I²`, with `I = ker σ`, is a finite projective `R`-module. This
is the canonical mathlib-facing formulation of the source statement that `I/I²` is finite locally
free over `R`. -/
theorem smooth_section_cotangent_finite_projective :
    Module.Finite R (RingHom.ker σ).Cotangent ∧
      Module.Projective R (RingHom.ker σ).Cotangent := by
  letI : Algebra S R := σ.toRingHom.toAlgebra
  have hsection :
      (IsScalarTower.toAlgHom R S R).comp (IsScalarTower.toAlgHom R R S) = AlgHom.id R R := by
    exact AlgHom.ext hσ
  have hker : RingHom.ker (algebraMap S R) = RingHom.ker σ := by
    ext x
    rfl
  -- The split conormal sequence identifies `I/I²` with the base change of `Ω[S⁄R]`.
  obtain ⟨hexact, -, ⟨l, hl⟩⟩ :=
    kaehlerDifferential_conormal_sequence_split_of_section (R := R) (S := S) (S' := R)
      (β := IsScalarTower.toAlgHom R R S) hsection
  have hsurjective : Function.Surjective (KaehlerDifferential.kerCotangentToTensor R S R) := by
    intro x
    have hx0 : KaehlerDifferential.mapBaseChange R S R x = 0 := Subsingleton.elim _ _
    exact (hexact x).mp hx0
  let eKer : (RingHom.ker σ).Cotangent ≃ₗ[R] (RingHom.ker (algebraMap S R)).Cotangent :=
    (Ideal.Cotangent.equivOfEq _ _ hker.symm).restrictScalars R
  let eBase : (RingHom.ker (algebraMap S R)).Cotangent ≃ₗ[R] R ⊗[S] Ω[S⁄R] :=
    LinearEquiv.ofBijective (KaehlerDifferential.kerCotangentToTensor R S R)
      ⟨LinearMap.injective_of_comp_eq_id _ _ hl, hsurjective⟩ |>.restrictScalars R
  let e : (RingHom.ker σ).Cotangent ≃ₗ[R] R ⊗[S] Ω[S⁄R] := eKer.trans eBase
  -- Smoothness makes `Ω[S⁄R]` finite projective, and base change preserves both properties.
  refine ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm⟩

/-- Helper for Lemma 10.139.4: freeness together with the finite/projective result gives a basis of
the conormal module indexed by `Fin d`, and each basis vector can be lifted back to `ker σ`. -/
private theorem exists_cotangent_fin_basis_and_lifts
    (hfree : Module.Free R (RingHom.ker σ).Cotangent) :
    ∃ d : ℕ, ∃ b : Module.Basis (Fin d) R (RingHom.ker σ).Cotangent,
      ∃ f : Fin d → RingHom.ker σ, ∀ i, (RingHom.ker σ).toCotangent (f i) = b i := by
  obtain ⟨hfinite, -⟩ :=
    smooth_section_cotangent_finite_projective (R := R) (S := S) (σ := σ) hσ
  letI : Module.Free R (RingHom.ker σ).Cotangent := hfree
  letI : Module.Finite R (RingHom.ker σ).Cotangent := hfinite
  let b0 : Module.Basis (Module.Free.ChooseBasisIndex R (RingHom.ker σ).Cotangent) R
      (RingHom.ker σ).Cotangent := Module.Free.chooseBasis R (RingHom.ker σ).Cotangent
  let b : Module.Basis (Fin (Fintype.card (Module.Free.ChooseBasisIndex R
        (RingHom.ker σ).Cotangent))) R (RingHom.ker σ).Cotangent :=
    b0.reindex (Fintype.equivFin _)
  -- Each cotangent basis vector comes from some element of the kernel ideal.
  choose f hf using fun i : Fin (Fintype.card (Module.Free.ChooseBasisIndex R
      (RingHom.ker σ).Cotangent)) ↦
    (RingHom.ker σ).toCotangent_surjective (b i)
  exact ⟨_, b, f, hf⟩

/-- Helper for Lemma 10.139.4: a section of `algebraMap R S` makes `σ` surjective. -/
private theorem smooth_section_sigma_surjective :
    Function.Surjective σ := by
  -- Evaluate `σ` on the image of any `r : R`.
  intro r
  exact ⟨algebraMap R S r, hσ r⟩

/-- Helper for Lemma 10.139.4: the reduced quotient `S / ker σ` is canonically `R` via the chosen
section. -/
private noncomputable def smooth_section_quotientKerAlgEquiv :
    (S ⧸ RingHom.ker σ) ≃ₐ[R] R :=
  Ideal.quotientKerAlgEquivOfRightInverse (f := σ) (g := algebraMap R S) hσ

section

omit [CommRing S] [Algebra R S] [Algebra.Smooth R S] σ hσ

/-- Helper for Lemma 10.139.4: evaluating a polynomial ring at the zero tuple kills exactly the
variable ideal. This is the source-side identification `P/J ≃ R` for `P = R[x_1, ..., x_d]` and
`J = (x_1, ..., x_d)`. -/
private theorem aeval_zero_ker_eq_idealOfVars {d : ℕ} :
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
private noncomputable def idealOfVars_quotientAlgEquiv {d : ℕ} :
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
private noncomputable def cotangent_lift_polynomial_map {d : ℕ}
    (f : Fin d → RingHom.ker σ) :
    MvPolynomial (Fin d) R →ₐ[R] S :=
  MvPolynomial.aeval fun i ↦ ((f i : RingHom.ker σ) : S)

/-- Helper for Lemma 10.139.4: the polynomial map sends the variable ideal into `ker σ`. -/
private theorem cotangent_lift_polynomial_map_idealOfVars_le_ker {d : ℕ}
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
private theorem cotangent_lift_idealOfVars_le_comap_ker {d : ℕ}
    (f : Fin d → RingHom.ker σ) :
    MvPolynomial.idealOfVars (Fin d) R ≤
      Ideal.comap (cotangent_lift_polynomial_map (R := R) (S := S) (σ := σ) f).toRingHom
        (RingHom.ker σ) := by
  -- This is the comap form of the previous containment, matching the cotangent-map API.
  simpa [Ideal.map_le_iff_le_comap] using
    cotangent_lift_polynomial_map_idealOfVars_le_ker (R := R) (S := S) (σ := σ) f

/-- Helper for Lemma 10.139.4: on the cotangent class of each variable, the induced cotangent map
is the cotangent class of the chosen kernel lift. -/
private theorem cotangent_lift_mapCotangent_variable {d : ℕ}
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
private theorem cotangent_lift_mapCotangent_variable_basis {d : ℕ}
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
private theorem cotangent_lift_polynomial_map_pow_idealOfVars_le_ker_pow {d : ℕ}
    (f : Fin d → RingHom.ker σ) (n : ℕ) :
    Ideal.map (cotangent_lift_polynomial_map (R := R) (S := S) (σ := σ) f).toRingHom
      ((MvPolynomial.idealOfVars (Fin d) R) ^ n) ≤ (RingHom.ker σ) ^ n := by
  -- Once the variable ideal maps into `ker σ`, the same is true for all powers.
  simpa [Ideal.map_pow] using
    Ideal.pow_right_mono
      (cotangent_lift_polynomial_map_idealOfVars_le_ker (R := R) (S := S) (σ := σ) f) n

/-- Helper for Lemma 10.139.4: the polynomial map descends to every truncation by powers of the
variable ideal and `ker σ`. -/
private noncomputable def cotangent_lift_truncated_map {d : ℕ}
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
private theorem cotangent_lift_truncated_map_compatible {d : ℕ}
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

/-- Helper for Lemma 10.139.4: formal smoothness gives a section of the completion projection
`AdicCompletion (ker σ) S → R`. -/
private theorem smooth_section_completion_has_section :
    ∃ s : R →ₐ[R] AdicCompletion (RingHom.ker σ) S,
      (AdicCompletion.kerProj
          (smooth_section_sigma_surjective (R := R) (S := S) (σ := σ) hσ)).comp s =
        AlgHom.id R R := by
  -- The target `R` is formally smooth over itself, so the completion projection splits.
  exact Algebra.FormallySmooth.exists_kerProj_comp_eq_id
    (R := R) (A := R) (S := S) (f := σ)
    (smooth_section_sigma_surjective (R := R) (S := S) (σ := σ) hσ)

/-- Helper for Lemma 10.139.4: `I / I²` carries the opposite `R`-action induced by commutativity,
so it can serve as the square-zero summand in `TrivSqZeroExt`. -/
private instance smooth_section_cotangent_opModule :
    Module Rᵐᵒᵖ (RingHom.ker σ).Cotangent :=
  Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)

/-- Helper for Lemma 10.139.4: the left and right `R`-actions on `I / I²` coincide. -/
private instance smooth_section_cotangent_isCentralScalar :
    IsCentralScalar R (RingHom.ker σ).Cotangent where
  op_smul_eq_smul _ _ := rfl

/-- Helper for Lemma 10.139.4: the natural reduction map `S / I² → S / I` for `I = ker σ`. -/
private noncomputable def smooth_section_secondQuotToQuot :
    (S ⧸ (RingHom.ker σ) ^ 2) →ₐ[R] (S ⧸ RingHom.ker σ) :=
  Ideal.Quotient.factorₐ R <| by
    simpa [pow_two] using
      (show (RingHom.ker σ) * (RingHom.ker σ) ≤ RingHom.ker σ from Ideal.mul_le_right)

/-- Helper for Lemma 10.139.4: the kernel of `S / I² → S / I` is exactly the cotangent ideal
inside `S / I²`. This is the quotient-level form of the source statement that the kernel is
`I / I²`. -/
private theorem smooth_section_secondQuot_ker_eq_cotangentIdeal :
    RingHom.ker (smooth_section_secondQuotToQuot (R := R) (S := S) (σ := σ)).toRingHom =
      (RingHom.ker σ).cotangentIdeal := by
  -- Unwinding the quotient map shows that vanishing in `S / I` is exactly membership in `I`.
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simpa [smooth_section_secondQuotToQuot, Ideal.mk_mem_cotangentIdeal] using
    (show Ideal.Quotient.mk (RingHom.ker σ) x = 0 ↔ σ x = 0 by
      rw [Ideal.Quotient.eq_zero_iff_mem, RingHom.mem_ker])

/-- Helper for Lemma 10.139.4: the cotangent summand in `S / I²` has square zero. -/
private theorem smooth_section_cotangentToQuotientSquare_mul_eq_zero
    (x y : (RingHom.ker σ).Cotangent) :
    (RingHom.ker σ).cotangentToQuotientSquare x *
        (RingHom.ker σ).cotangentToQuotientSquare y = 0 := by
  -- Both cotangent classes lift to kernel elements, and products of such lifts land in `I²`.
  obtain ⟨x, rfl⟩ := (RingHom.ker σ).toCotangent_surjective x
  obtain ⟨y, rfl⟩ := (RingHom.ker σ).toCotangent_surjective y
  rw [Ideal.toCotangent_to_quotient_square, Ideal.toCotangent_to_quotient_square]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr <| by
    simpa [pow_two] using Ideal.mul_mem_mul x.2 y.2

/-- Helper for Lemma 10.139.4: reducing `S / I²` modulo `I` kills the cotangent summand. -/
private theorem smooth_section_secondQuotToQuot_cotangentToQuotientSquare_eq_zero
    (x : (RingHom.ker σ).Cotangent) :
    smooth_section_secondQuotToQuot (R := R) (S := S) (σ := σ)
      ((RingHom.ker σ).cotangentToQuotientSquare x) = 0 := by
  -- The cotangent summand is represented by an element of `I`, which vanishes in `S / I`.
  obtain ⟨x, rfl⟩ := (RingHom.ker σ).toCotangent_surjective x
  change Ideal.Quotient.mk (RingHom.ker σ) x = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr x.2

/-- Helper for Lemma 10.139.4: every class in `S / I²` splits as its scalar part from `R` plus a
unique cotangent contribution. This is the source decomposition `S / I² = φ(R) ⊕ I / I²`. -/
private theorem smooth_section_secondQuot_eq_scalar_add_cotangent
    (x : S ⧸ (RingHom.ker σ) ^ 2) :
    ∃ y : (RingHom.ker σ).Cotangent,
      algebraMap R (S ⧸ (RingHom.ker σ) ^ 2)
          (((smooth_section_quotientKerAlgEquiv (R := R) (S := S) (σ := σ) hσ).toAlgHom.comp
              (smooth_section_secondQuotToQuot (R := R) (S := S) (σ := σ))) x) +
        (RingHom.ker σ).cotangentToQuotientSquare y = x := by
  let ρ : (S ⧸ (RingHom.ker σ) ^ 2) →ₐ[R] R :=
    (smooth_section_quotientKerAlgEquiv (R := R) (S := S) (σ := σ) hσ).toAlgHom.comp
      (smooth_section_secondQuotToQuot (R := R) (S := S) (σ := σ))
  let z : S ⧸ (RingHom.ker σ) ^ 2 := x - algebraMap R _ (ρ x)
  have hz_quot :
      smooth_section_secondQuotToQuot (R := R) (S := S) (σ := σ) x =
        algebraMap R (S ⧸ RingHom.ker σ) (ρ x) := by
    -- Compare both classes after identifying `S / I` with `R` via the section.
    apply (smooth_section_quotientKerAlgEquiv (R := R) (S := S) (σ := σ) hσ).injective
    simp [ρ]
  have hz_mem :
      z ∈ (RingHom.ker σ).cotangentIdeal := by
    -- The residual term dies in `S / I`, so it lies in the cotangent ideal.
    have hzker : z ∈
        RingHom.ker (smooth_section_secondQuotToQuot (R := R) (S := S) (σ := σ)).toRingHom := by
      rw [RingHom.mem_ker]
      simp [z, hz_quot]
    rw [smooth_section_secondQuot_ker_eq_cotangentIdeal (R := R) (S := S) (σ := σ) hσ] at hzker
    exact hzker
  let y : (RingHom.ker σ).Cotangent :=
    (RingHom.ker σ).cotangentEquivIdeal.symm ⟨z, hz_mem⟩
  have hy :
      (RingHom.ker σ).cotangentToQuotientSquare y = z := by
    -- Translate the chosen element of the cotangent ideal back through the canonical equivalence.
    change ↑((RingHom.ker σ).cotangentEquivIdeal y) = z
    simpa [y] using congrArg Subtype.val
      ((RingHom.ker σ).cotangentEquivIdeal.apply_symm_apply ⟨z, hz_mem⟩)
  refine ⟨y, ?_⟩
  -- Substitute the residual cotangent term back into the scalar-plus-residual decomposition.
  calc
    algebraMap R (S ⧸ (RingHom.ker σ) ^ 2) (ρ x) +
        (RingHom.ker σ).cotangentToQuotientSquare y =
      algebraMap R (S ⧸ (RingHom.ker σ) ^ 2) (ρ x) + z := by rw [hy]
    _ = x := by
      simp [z, sub_eq_add_neg, add_left_comm]

/-- Helper for Lemma 10.139.4: the second-order quotient `S / I²` is the split square-zero
extension of `R` by `I / I²`, where `I = ker σ`. This is the target-side source decomposition
`S / I² = φ(R) ⊕ I / I²`. -/
private noncomputable def smooth_section_trivSqZero_algEquiv_kerSquareQuot :
    TrivSqZeroExt R (RingHom.ker σ).Cotangent ≃ₐ[R] (S ⧸ (RingHom.ker σ) ^ 2) := by
  let F : TrivSqZeroExt R (RingHom.ker σ).Cotangent →ₐ[R] S ⧸ (RingHom.ker σ) ^ 2 :=
    TrivSqZeroExt.liftEquivOfComm
      ⟨(RingHom.ker σ).cotangentToQuotientSquare,
        smooth_section_cotangentToQuotientSquare_mul_eq_zero (R := R) (S := S) (σ := σ) hσ⟩
  -- Route correction: package the split square-zero model through the source decomposition
  -- `S / I² = φ(R) ⊕ I / I²`, so the remaining work is a flat bijectivity proof on the scalar and
  -- cotangent coordinates rather than repeated transport normalization.
  refine AlgEquiv.ofBijective F ⟨?_, ?_⟩
  · intro x y hxy
    suffices hker_zero : ∀ z : TrivSqZeroExt R (RingHom.ker σ).Cotangent, F z = 0 → z = 0 by
      have hzero : F (x - y) = 0 := by
        simpa [map_sub, hxy]
      exact sub_eq_zero.mp (hker_zero (x - y) hzero)
    intro z hz
    have hsum :
        algebraMap R (S ⧸ (RingHom.ker σ) ^ 2) z.fst +
            (RingHom.ker σ).cotangentToQuotientSquare z.snd = 0 := by
      -- Expand `z` into its scalar and cotangent coordinates, then use `F z = 0`.
      calc
        algebraMap R (S ⧸ (RingHom.ker σ) ^ 2) z.fst +
            (RingHom.ker σ).cotangentToQuotientSquare z.snd =
          F (TrivSqZeroExt.inl z.fst + TrivSqZeroExt.inr z.snd) := by
            simp [F, map_add, TrivSqZeroExt.liftEquivOfComm_apply, TrivSqZeroExt.lift_apply_inl,
              TrivSqZeroExt.lift_apply_inr, Algebra.ofId_apply]
        _ = F z := by rw [TrivSqZeroExt.inl_fst_add_inr_snd_eq]
        _ = 0 := hz
    have hfst_quot : algebraMap R (S ⧸ RingHom.ker σ) z.fst = 0 := by
      -- Reducing modulo `I` kills the cotangent part and leaves only the scalar coordinate.
      have := congrArg (smooth_section_secondQuotToQuot (R := R) (S := S) (σ := σ)) hsum
      simpa [map_add,
        smooth_section_secondQuotToQuot_cotangentToQuotientSquare_eq_zero
          (R := R) (S := S) (σ := σ) hσ] using this
    have hfst : z.fst = 0 := by
      -- The section identifies `S / I` with `R`, so the scalar coordinate already vanishes in `R`.
      have := congrArg (smooth_section_quotientKerAlgEquiv (R := R) (S := S) (σ := σ) hσ)
        hfst_quot
      simpa using this
    have hsnd_zero :
        (RingHom.ker σ).cotangentToQuotientSquare z.snd = 0 := by
      -- Once the scalar coordinate is zero, the residual cotangent term must vanish too.
      simpa [hfst] using hsum
    have hsnd : z.snd = 0 :=
      (RingHom.ker σ).cotangentToQuotientSquare_injective hsnd_zero
    ext <;> simp [hfst, hsnd]
  · intro x
    obtain ⟨y, hy⟩ :=
      smooth_section_secondQuot_eq_scalar_add_cotangent (R := R) (S := S) (σ := σ) hσ x
    refine ⟨TrivSqZeroExt.inl (((smooth_section_quotientKerAlgEquiv
        (R := R) (S := S) (σ := σ) hσ).toAlgHom.comp
          (smooth_section_secondQuotToQuot (R := R) (S := S) (σ := σ))) x) +
        TrivSqZeroExt.inr y, ?_⟩
    -- The decomposition lemma directly gives a preimage under the forward map `F`.
    simpa [F, map_add, TrivSqZeroExt.liftEquivOfComm_apply, TrivSqZeroExt.lift_apply_inl,
      TrivSqZeroExt.lift_apply_inr, Algebra.ofId_apply] using hy

section

omit [CommRing S] [Algebra R S] [Algebra.Smooth R S] σ hσ

/-- Helper for Lemma 10.139.4: each polynomial variable lies in the variable ideal. -/
private theorem idealOfVars_variable_mem {d : ℕ} (i : Fin d) :
    MvPolynomial.X i ∈ MvPolynomial.idealOfVars (Fin d) R := by
  -- The variable ideal is generated by the variables themselves.
  simpa [MvPolynomial.idealOfVars] using
    (Ideal.subset_span (Set.mem_range_self i) :
      MvPolynomial.X i ∈ MvPolynomial.idealOfVars (Fin d) R)

/-- Helper for Lemma 10.139.4: the product of two variable classes vanishes modulo `J²`. -/
private theorem idealOfVars_truncTwo_variable_mul_eq_zero {d : ℕ} (i j : Fin d) :
    (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ 2) (MvPolynomial.X i)) *
        Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ 2) (MvPolynomial.X j) = 0 := by
  -- The product `X i * X j` already lies in `J²`, so its class is zero in the quotient.
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [pow_two]
  exact Ideal.mul_mem_mul
    (idealOfVars_variable_mem (R := R) i)
    (idealOfVars_variable_mem (R := R) j)

/-- Helper for Lemma 10.139.4: evaluation at the square-zero variable classes sends `J²` to zero,
so it descends from `P` to `P / J²`. -/
private theorem idealOfVars_trivSqZero_descends_aeval {d : ℕ}
    (p : MvPolynomial (Fin d) R)
    (hp : p ∈ (MvPolynomial.idealOfVars (Fin d) R) ^ 2) :
    MvPolynomial.aeval
        (fun i : Fin d ↦ TrivSqZeroExt.inr (Pi.single i (1 : R))) p =
      (0 : TrivSqZeroExt R (Fin d → R)) := by
  let Fraw : MvPolynomial (Fin d) R →ₐ[R] TrivSqZeroExt R (Fin d → R) :=
    MvPolynomial.aeval fun i : Fin d ↦ TrivSqZeroExt.inr (Pi.single i (1 : R))
  have hJker_comap :
      MvPolynomial.idealOfVars (Fin d) R ≤
        Ideal.comap Fraw.toRingHom (TrivSqZeroExt.kerIdeal R (Fin d → R)) := by
    -- Each generator `X i` lands in the kernel ideal of the projection to the scalar part.
    rw [MvPolynomial.idealOfVars]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    change Fraw (MvPolynomial.X i) ∈
      RingHom.ker (TrivSqZeroExt.fstHom R R (Fin d → R)).toRingHom
    rw [RingHom.mem_ker]
    simp [Fraw]
  have hJker :
      Ideal.map Fraw.toRingHom (MvPolynomial.idealOfVars (Fin d) R) ≤
        TrivSqZeroExt.kerIdeal R (Fin d → R) := by
    exact (Ideal.map_le_iff_le_comap).2 hJker_comap
  have hJsq :
      Ideal.map Fraw.toRingHom ((MvPolynomial.idealOfVars (Fin d) R) ^ 2) ≤
        (TrivSqZeroExt.kerIdeal R (Fin d → R)) ^ 2 := by
    -- Squaring preserves the containment into the square-zero ideal.
    simpa [Ideal.map_pow] using Ideal.pow_right_mono hJker 2
  have hp_image :
      Fraw p ∈ (TrivSqZeroExt.kerIdeal R (Fin d → R)) ^ 2 := by
    exact hJsq <| Ideal.mem_map_of_mem _ hp
  -- The kernel ideal of the scalar projection is square-zero.
  simpa [Fraw, TrivSqZeroExt.kerIdeal_sq] using hp_image

/-- Helper for Lemma 10.139.4: the classes of the variables define the canonical linear map from
the free module `Fin d → R` into `P / J²`. -/
private noncomputable abbrev idealOfVars_truncTwo_variable_linearMap {d : ℕ} :
    (Fin d → R) →ₗ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 2 :=
  (Pi.basisFun R (Fin d)).constr R fun i ↦
    Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ 2) (MvPolynomial.X i)

/-- Helper for Lemma 10.139.4: the canonical linear map into `P / J²` expands in the quotient
classes of the variables. -/
private theorem idealOfVars_truncTwo_variable_linearMap_apply {d : ℕ} (x : Fin d → R) :
    idealOfVars_truncTwo_variable_linearMap (R := R) x =
      ∑ i, x i •
        Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ 2) (MvPolynomial.X i) := by
  -- The standard basis on `Fin d → R` records the coefficients of the quotient variable classes.
  rw [idealOfVars_truncTwo_variable_linearMap]
  rw [(Pi.basisFun R (Fin d)).constr_apply R
    (fun i ↦ Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ 2) (MvPolynomial.X i)) x]
  simp [Pi.basisFun_repr, Finsupp.sum_fintype]

/-- Helper for Lemma 10.139.4: the canonical linear map sends the `i`th basis vector to the class
of `X i` in `P / J²`. -/
private theorem idealOfVars_truncTwo_variable_linearMap_basis {d : ℕ} (i : Fin d) :
    idealOfVars_truncTwo_variable_linearMap (R := R) (Pi.single i (1 : R)) =
      Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ 2) (MvPolynomial.X i) := by
  -- This is exactly how `Basis.constr` is defined on the standard basis vectors.
  rw [← Pi.basisFun_apply]
  simp [idealOfVars_truncTwo_variable_linearMap]

/-- Helper for Lemma 10.139.4: the image of the canonical linear map into `P / J²` has square
zero, because all pairwise products of variable classes vanish modulo `J²`. -/
private theorem idealOfVars_trivSqZero_variable_linear_square_zero {d : ℕ}
    (x y : Fin d → R) :
    idealOfVars_truncTwo_variable_linearMap (R := R) x *
        idealOfVars_truncTwo_variable_linearMap (R := R) y = 0 := by
  -- Expand in the quotient variable basis and kill each pairwise product separately.
  rw [idealOfVars_truncTwo_variable_linearMap_apply, idealOfVars_truncTwo_variable_linearMap_apply,
    Finset.sum_mul]
  refine Finset.sum_eq_zero ?_
  intro i _
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero ?_
  intro j _
  rw [smul_mul_assoc, mul_smul_comm, idealOfVars_truncTwo_variable_mul_eq_zero, smul_zero,
    smul_zero]

/-- Helper for Lemma 10.139.4: the descended evaluation map from `P / J²` to the split
square-zero model sends each variable class to the corresponding basis vector. -/
private noncomputable def idealOfVars_trivSqZero_toAlgHom {d : ℕ} :
    MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 2 →ₐ[R]
      TrivSqZeroExt R (Fin d → R) :=
  Ideal.Quotient.liftₐ ((MvPolynomial.idealOfVars (Fin d) R) ^ 2)
    (MvPolynomial.aeval fun i : Fin d ↦ TrivSqZeroExt.inr (Pi.single i (1 : R)))
    (idealOfVars_trivSqZero_descends_aeval (R := R))

/-- Helper for Lemma 10.139.4: the descended forward map on `P / J²` sends the `i`th variable
class to the `i`th square-zero basis vector. -/
private theorem idealOfVars_trivSqZero_toAlgHom_variable {d : ℕ} (i : Fin d) :
    idealOfVars_trivSqZero_toAlgHom (R := R) (d := d)
        (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ 2) (MvPolynomial.X i)) =
      TrivSqZeroExt.inr (Pi.single i (1 : R)) := by
  -- The quotient map still evaluates each variable to the chosen square-zero basis vector.
  have hcomp :=
    AlgHom.congr_fun
      (Ideal.Quotient.liftₐ_comp ((MvPolynomial.idealOfVars (Fin d) R) ^ 2)
        (MvPolynomial.aeval fun j : Fin d ↦ TrivSqZeroExt.inr (Pi.single j (1 : R)))
        (idealOfVars_trivSqZero_descends_aeval (R := R)))
      (MvPolynomial.X i)
  simpa [idealOfVars_trivSqZero_toAlgHom] using hcomp

/-- Helper for Lemma 10.139.4: the split square-zero extension maps back to `P / J²` through the
linear map spanned by the variable classes. -/
private noncomputable def idealOfVars_trivSqZero_fromAlgHom {d : ℕ} :
    TrivSqZeroExt R (Fin d → R) →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 2 :=
  TrivSqZeroExt.liftEquivOfComm
    (R' := R)
    (A := MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 2)
    ⟨idealOfVars_truncTwo_variable_linearMap (R := R),
      idealOfVars_trivSqZero_variable_linear_square_zero (R := R)⟩

/-- Helper for Lemma 10.139.4: the inverse square-zero map sends `inr x` to the linear combination
of variable classes with coefficients `x`. -/
private theorem idealOfVars_trivSqZero_fromAlgHom_inr {d : ℕ} (x : Fin d → R) :
    idealOfVars_trivSqZero_fromAlgHom (R := R) (d := d) (TrivSqZeroExt.inr x) =
      idealOfVars_truncTwo_variable_linearMap (R := R) x := by
  -- The universal square-zero map restricts to the chosen linear map on the nilpotent summand.
  simp [idealOfVars_trivSqZero_fromAlgHom]

/-- Helper for Lemma 10.139.4: the square-zero coordinates `Pi.single i 1` reconstruct the
corresponding basis vector under the standard basis of `Fin d → R`. -/
private theorem idealOfVars_trivSqZero_toAlgHom_linear {d : ℕ} (x : Fin d → R) :
    idealOfVars_trivSqZero_toAlgHom (R := R) (d := d)
        (idealOfVars_truncTwo_variable_linearMap (R := R) x) =
      TrivSqZeroExt.inr x := by
  -- Expand in the quotient variable basis and reassemble the vector in the square-zero summand.
  have hsum : ∑ i, x i • (Pi.single i (1 : R) : Fin d → R) = x := by
    ext i
    simpa [Pi.single_apply, mul_comm]
  rw [idealOfVars_truncTwo_variable_linearMap_apply]
  calc
    idealOfVars_trivSqZero_toAlgHom (R := R) (d := d)
        (∑ i, x i •
          Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ 2) (MvPolynomial.X i)) =
      ∑ i, x i •
        idealOfVars_trivSqZero_toAlgHom (R := R) (d := d)
          (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ 2) (MvPolynomial.X i)) := by
        simp [map_sum]
    _ = ∑ i, x i • TrivSqZeroExt.inr (Pi.single i (1 : R)) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [idealOfVars_trivSqZero_toAlgHom_variable]
    _ = TrivSqZeroExt.inr (∑ i, x i • (Pi.single i (1 : R) : Fin d → R)) := by
      simp_rw [← TrivSqZeroExt.inr_smul]
      simpa using
        (TrivSqZeroExt.inr_sum (R := R) (M := Fin d → R) Finset.univ
          (fun i ↦ x i • (Pi.single i (1 : R) : Fin d → R))).symm
    _ = TrivSqZeroExt.inr x := by rw [hsum]

/-- Helper for Lemma 10.139.4: the two square-zero model maps on `P / J²` are inverse. -/
private theorem idealOfVars_trivSqZero_fromAlgHom_comp_toAlgHom {d : ℕ} :
    (idealOfVars_trivSqZero_fromAlgHom (R := R) (d := d)).comp
        (idealOfVars_trivSqZero_toAlgHom (R := R) (d := d)) =
      AlgHom.id R
        (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 2) := by
  -- Two maps out of the quotient agree once they agree on the polynomial variables.
  refine Ideal.Quotient.algHom_ext _ ?_
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  simp [AlgHom.comp_apply, idealOfVars_trivSqZero_toAlgHom_variable,
    idealOfVars_trivSqZero_fromAlgHom_inr]

/-- Helper for Lemma 10.139.4: the two square-zero model maps on `P / J²` are inverse. -/
private theorem idealOfVars_trivSqZero_toAlgHom_comp_fromAlgHom {d : ℕ} :
    (idealOfVars_trivSqZero_toAlgHom (R := R) (d := d)).comp
        (idealOfVars_trivSqZero_fromAlgHom (R := R) (d := d)) =
      AlgHom.id R (TrivSqZeroExt R (Fin d → R)) := by
  -- Two algebra maps out of the trivial square-zero extension agree once they agree on every
  -- square-zero generator `inr x`.
  apply TrivSqZeroExt.algHom_ext
  intro x
  rw [AlgHom.comp_apply, idealOfVars_trivSqZero_fromAlgHom_inr,
    idealOfVars_trivSqZero_toAlgHom_linear]
  simp

/-- Helper for Lemma 10.139.4: the source second-order quotient `P / J²` is the split square-zero
extension of `R` by the free module on the variables. -/
private noncomputable abbrev idealOfVars_trivSqZero_algEquiv_truncTwo {d : ℕ} :
    (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 2) ≃ₐ[R]
      TrivSqZeroExt R (Fin d → R) :=
  AlgEquiv.ofAlgHom
    (idealOfVars_trivSqZero_toAlgHom (R := R) (d := d))
    (idealOfVars_trivSqZero_fromAlgHom (R := R) (d := d))
    (idealOfVars_trivSqZero_toAlgHom_comp_fromAlgHom (R := R) (d := d))
    (idealOfVars_trivSqZero_fromAlgHom_comp_toAlgHom (R := R) (d := d))

/-- Helper for Lemma 10.139.4: the explicit source-side square-zero equivalence sends the `i`th
variable class to the `i`th split square-zero basis vector. -/
private theorem idealOfVars_trivSqZero_algEquiv_truncTwo_variable {d : ℕ} (i : Fin d) :
    idealOfVars_trivSqZero_algEquiv_truncTwo (R := R) (d := d)
        (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ 2) (MvPolynomial.X i)) =
      TrivSqZeroExt.inr (Pi.single i (1 : R)) := by
  -- This is the computation rule inherited from the descended evaluation map.
  exact idealOfVars_trivSqZero_toAlgHom_variable (R := R) (d := d) i

end

/-- Helper for Lemma 10.139.4: the chosen basis identifies the standard coordinate vector
`Pi.single i 1` with the `i`th basis element in the cotangent module. -/
private theorem basis_equivFun_symm_single {d : ℕ}
    (b : Module.Basis (Fin d) R (RingHom.ker σ).Cotangent) (i : Fin d) :
    b.equivFun.symm (Pi.single i (1 : R)) = b i := by
  -- The inverse coordinate map sends the standard basis vector back to the corresponding basis
  -- element.
  rw [b.equivFun_symm_apply]
  simp [Pi.single_apply]

/-- Helper for Lemma 10.139.4: the target-side square-zero equivalence sends `inr x` to the
cotangent class in `S / (ker σ)^2`. -/
private theorem smooth_section_trivSqZero_algEquiv_kerSquareQuot_inr
    (x : (RingHom.ker σ).Cotangent) :
    smooth_section_trivSqZero_algEquiv_kerSquareQuot (R := R) (S := S) (σ := σ) hσ
        (TrivSqZeroExt.inr x) =
      (RingHom.ker σ).cotangentToQuotientSquare x := by
  -- Unfold the forward square-zero model only on the nilpotent summand.
  simp [smooth_section_trivSqZero_algEquiv_kerSquareQuot, TrivSqZeroExt.liftEquivOfComm_apply,
    TrivSqZeroExt.lift_apply_inr]

/-- Helper for Lemma 10.139.4: at truncation level `2`, the actual polynomial map agrees with the
composite through the explicit source and target split square-zero models. -/
private theorem trunc_two_model_comparison_variable {d : ℕ}
    (b : Module.Basis (Fin d) R (RingHom.ker σ).Cotangent)
    (f : Fin d → RingHom.ker σ)
    (hf : ∀ i, (RingHom.ker σ).toCotangent (f i) = b i)
    (i : Fin d) :
    (((smooth_section_trivSqZero_algEquiv_kerSquareQuot
        (R := R) (S := S) (σ := σ) hσ).toAlgHom).comp
      ((TrivSqZeroExt.map b.equivFun.symm.toLinearMap).comp
        (idealOfVars_trivSqZero_algEquiv_truncTwo (R := R) (d := d)).toAlgHom))
      (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ 2) (MvPolynomial.X i)) =
        Ideal.Quotient.mk ((RingHom.ker σ) ^ 2) ((f i : RingHom.ker σ) : S) := by
  -- Track the single variable class through the source model, the basis transport, and the
  -- target model until it becomes the quotient class of the chosen kernel lift.
  calc
    (((smooth_section_trivSqZero_algEquiv_kerSquareQuot
        (R := R) (S := S) (σ := σ) hσ).toAlgHom).comp
      ((TrivSqZeroExt.map b.equivFun.symm.toLinearMap).comp
        (idealOfVars_trivSqZero_algEquiv_truncTwo (R := R) (d := d)).toAlgHom))
      (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ 2) (MvPolynomial.X i)) =
        (RingHom.ker σ).cotangentToQuotientSquare
          (b.equivFun.symm (Pi.single i (1 : R))) := by
          rw [AlgHom.comp_apply, AlgHom.comp_apply]
          calc
            (smooth_section_trivSqZero_algEquiv_kerSquareQuot
                (R := R) (S := S) (σ := σ) hσ)
                ((TrivSqZeroExt.map b.equivFun.symm.toLinearMap)
                  ((idealOfVars_trivSqZero_algEquiv_truncTwo (R := R) (d := d))
                    (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ 2)
                      (MvPolynomial.X i)))) =
                (smooth_section_trivSqZero_algEquiv_kerSquareQuot
                  (R := R) (S := S) (σ := σ) hσ)
                    ((TrivSqZeroExt.map b.equivFun.symm.toLinearMap)
                      (TrivSqZeroExt.inr (Pi.single i (1 : R)))) := by
                      congr 2
                      exact idealOfVars_trivSqZero_algEquiv_truncTwo_variable (R := R) (d := d) i
            _ = (smooth_section_trivSqZero_algEquiv_kerSquareQuot
                  (R := R) (S := S) (σ := σ) hσ)
                    (TrivSqZeroExt.inr (b.equivFun.symm (Pi.single i (1 : R)))) := by
                      rw [TrivSqZeroExt.map_inr]
                      rfl
            _ = (RingHom.ker σ).cotangentToQuotientSquare
                  (b.equivFun.symm (Pi.single i (1 : R))) := by
                    rw [smooth_section_trivSqZero_algEquiv_kerSquareQuot_inr]
    _ = (RingHom.ker σ).cotangentToQuotientSquare (b i) := by
      rw [basis_equivFun_symm_single (R := R) (S := S) (σ := σ) (hσ := hσ) b i]
    _ = Ideal.Quotient.mk ((RingHom.ker σ) ^ 2) ((f i : RingHom.ker σ) : S) := by
      rw [← hf i, Ideal.toCotangent_to_quotient_square]
      rfl

/-- Helper for Lemma 10.139.4: at level `2`, quotient extensionality upgrades the variable
comparison to equality of the full truncation map with the square-zero-model composite. -/
private theorem trunc_two_algHom_via_trivSqZero_models {d : ℕ}
    (b : Module.Basis (Fin d) R (RingHom.ker σ).Cotangent)
    (f : Fin d → RingHom.ker σ)
    (hf : ∀ i, (RingHom.ker σ).toCotangent (f i) = b i) :
    cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f 2 =
      ((smooth_section_trivSqZero_algEquiv_kerSquareQuot
          (R := R) (S := S) (σ := σ) hσ).toAlgHom).comp
        ((TrivSqZeroExt.map b.equivFun.symm.toLinearMap).comp
          (idealOfVars_trivSqZero_algEquiv_truncTwo (R := R) (d := d)).toAlgHom) := by
  -- Compare the two quotient maps on polynomial variables; the `R`-algebra structure handles
  -- constants automatically, so `MvPolynomial.algHom_ext` reduces everything to the generator case.
  refine Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext fun i ↦ ?_)
  -- On `X i`, both maps land in the quotient class of the chosen kernel lift `f i`.
  simpa [cotangent_lift_truncated_map, cotangent_lift_polynomial_map] using
    (trunc_two_model_comparison_variable (R := R) (S := S) (σ := σ) hσ b f hf i).symm

/-- Helper for Lemma 10.139.4: transporting across the chosen basis and back is the identity on
the two split square-zero models. -/
private theorem trivSqZero_map_basis_transport_cancel {d : ℕ}
    (b : Module.Basis (Fin d) R (RingHom.ker σ).Cotangent) :
    ((TrivSqZeroExt.map b.equivFun.toLinearMap).comp
      (TrivSqZeroExt.map b.equivFun.symm.toLinearMap) =
        AlgHom.id R (TrivSqZeroExt R (Fin d → R))) ∧
      ((TrivSqZeroExt.map b.equivFun.symm.toLinearMap).comp
        (TrivSqZeroExt.map b.equivFun.toLinearMap) =
          AlgHom.id R (TrivSqZeroExt R (RingHom.ker σ).Cotangent)) := by
  have hsource :
      b.equivFun.toLinearMap.comp b.equivFun.symm.toLinearMap =
        (LinearMap.id : (Fin d → R) →ₗ[R] Fin d → R) := by
    ext x j
    simp
  have htarget :
      b.equivFun.symm.toLinearMap.comp b.equivFun.toLinearMap =
        (LinearMap.id :
          (RingHom.ker σ).Cotangent →ₗ[R] (RingHom.ker σ).Cotangent) := by
    ext x
    simp
  constructor
  · -- Compose the forward and backward basis transports on the source square-zero model.
    calc
      (TrivSqZeroExt.map b.equivFun.toLinearMap).comp
          (TrivSqZeroExt.map b.equivFun.symm.toLinearMap) =
        TrivSqZeroExt.map (b.equivFun.toLinearMap.comp b.equivFun.symm.toLinearMap) := by
          rw [← TrivSqZeroExt.map_comp_map]
      _ = TrivSqZeroExt.map (LinearMap.id : (Fin d → R) →ₗ[R] Fin d → R) := by
        rw [hsource]
      _ = AlgHom.id R (TrivSqZeroExt R (Fin d → R)) := by
        rw [TrivSqZeroExt.map_id]
  · -- Compose the backward and forward basis transports on the target square-zero model.
    calc
      (TrivSqZeroExt.map b.equivFun.symm.toLinearMap).comp
          (TrivSqZeroExt.map b.equivFun.toLinearMap) =
        TrivSqZeroExt.map (b.equivFun.symm.toLinearMap.comp b.equivFun.toLinearMap) := by
          rw [← TrivSqZeroExt.map_comp_map]
      _ = TrivSqZeroExt.map
          (LinearMap.id :
            (RingHom.ker σ).Cotangent →ₗ[R] (RingHom.ker σ).Cotangent) := by
        rw [htarget]
      _ = AlgHom.id R (TrivSqZeroExt R (RingHom.ker σ).Cotangent) := by
        rw [TrivSqZeroExt.map_id]

/-- Helper for Lemma 10.139.4: the explicit split square-zero models give the actual inverse to
the truncation map `Ψtrunc 2`. -/
private noncomputable def trunc_two_inverse_via_trivSqZero_models {d : ℕ}
    (b : Module.Basis (Fin d) R (RingHom.ker σ).Cotangent) :
    S ⧸ (RingHom.ker σ) ^ 2 →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 2 :=
  ((idealOfVars_trivSqZero_algEquiv_truncTwo (R := R) (d := d)).symm.toAlgHom).comp
    ((TrivSqZeroExt.map b.equivFun.toLinearMap).comp
      ((smooth_section_trivSqZero_algEquiv_kerSquareQuot
        (R := R) (S := S) (σ := σ) hσ).symm.toAlgHom))

/-- Helper for Lemma 10.139.4: in the level-`2` model comparison, the target-side transport
`eS2.symm ≫ eS2` cancels after one controlled reassociation. -/
private theorem trunc_two_target_transport_cancel {d : ℕ}
    (φ : MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 2 →ₐ[R]
      TrivSqZeroExt R (RingHom.ker σ).Cotangent) :
    ((smooth_section_trivSqZero_algEquiv_kerSquareQuot
        (R := R) (S := S) (σ := σ) hσ).symm.toAlgHom).comp
      (((smooth_section_trivSqZero_algEquiv_kerSquareQuot
          (R := R) (S := S) (σ := σ) hσ).toAlgHom).comp φ) =
        φ := by
  let e :=
    smooth_section_trivSqZero_algEquiv_kerSquareQuot (R := R) (S := S) (σ := σ) hσ
  have he :
      (e.symm.toAlgHom.comp e.toAlgHom) =
        AlgHom.id R (TrivSqZeroExt R (RingHom.ker σ).Cotangent) := by
    simpa [e] using (AlgEquiv.symm_comp (R := R) e)
  -- Reassociate only the exact middle factor so the square-zero equivalence cancels on the nose.
  calc
    e.symm.toAlgHom.comp (e.toAlgHom.comp φ) =
      (e.symm.toAlgHom.comp e.toAlgHom).comp φ := by
            rw [← AlgHom.comp_assoc]
    _ = (AlgHom.id R (TrivSqZeroExt R (RingHom.ker σ).Cotangent)).comp φ := by
          rw [he]
    _ = φ := by
          rw [AlgHom.id_comp]

/-- Helper for Lemma 10.139.4: in the level-`2` model comparison, the source-side transport
`eP2 ≫ eP2.symm` cancels after one controlled reassociation. -/
private theorem trunc_two_source_transport_cancel {d : ℕ}
    (ψ : S ⧸ (RingHom.ker σ) ^ 2 →ₐ[R] TrivSqZeroExt R (Fin d → R)) :
    ((idealOfVars_trivSqZero_algEquiv_truncTwo (R := R) (d := d)).toAlgHom).comp
      (((idealOfVars_trivSqZero_algEquiv_truncTwo
          (R := R) (d := d)).symm.toAlgHom).comp ψ) =
        ψ := by
  let e := idealOfVars_trivSqZero_algEquiv_truncTwo (R := R) (d := d)
  have he :
      (e.toAlgHom.comp e.symm.toAlgHom) =
        AlgHom.id R (TrivSqZeroExt R (Fin d → R)) := by
    simpa [e] using (AlgEquiv.comp_symm (R := R) e)
  -- Reassociate only the exact middle factor so the source square-zero equivalence cancels.
  calc
    e.toAlgHom.comp (e.symm.toAlgHom.comp ψ) =
      (e.toAlgHom.comp e.symm.toAlgHom).comp ψ := by
            rw [← AlgHom.comp_assoc]
    _ =
        (AlgHom.id R (TrivSqZeroExt R (Fin d → R))).comp ψ := by
            rw [he]
    _ = ψ := by
          rw [AlgHom.id_comp]

/-- Helper for Lemma 10.139.4: the explicit square-zero-model inverse is inverse to the actual
truncation map at level `2`. -/
private theorem trunc_two_inverse_via_trivSqZero_models_spec {d : ℕ}
    (b : Module.Basis (Fin d) R (RingHom.ker σ).Cotangent)
    (f : Fin d → RingHom.ker σ)
    (hf : ∀ i, (RingHom.ker σ).toCotangent (f i) = b i) :
    ((trunc_two_inverse_via_trivSqZero_models (R := R) (S := S) (σ := σ) hσ b).comp
        (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f 2) =
      AlgHom.id R
        (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 2)) ∧
      ((cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f 2).comp
        (trunc_two_inverse_via_trivSqZero_models (R := R) (S := S) (σ := σ) hσ b) =
      AlgHom.id R (S ⧸ (RingHom.ker σ) ^ 2)) := by
  obtain ⟨hsourceBasis, htargetBasis⟩ :=
    trivSqZero_map_basis_transport_cancel (R := R) (S := S) (σ := σ) (hσ := hσ) b
  constructor
  · -- Rewrite the actual truncation map through the explicit source and target square-zero models.
    rw [trunc_two_algHom_via_trivSqZero_models (R := R) (S := S) (σ := σ) hσ b f hf]
    rw [trunc_two_inverse_via_trivSqZero_models]
    -- Reassociate to expose the exact `eS2.symm ≫ eS2` middle factor, then the basis transport.
    rw [AlgHom.comp_assoc, AlgHom.comp_assoc]
    rw [trunc_two_target_transport_cancel (R := R) (S := S) (σ := σ) (hσ := hσ)]
    calc
      ((idealOfVars_trivSqZero_algEquiv_truncTwo
          (R := R) (d := d)).symm.toAlgHom).comp
          ((TrivSqZeroExt.map b.equivFun.toLinearMap).comp
            ((TrivSqZeroExt.map b.equivFun.symm.toLinearMap).comp
              (idealOfVars_trivSqZero_algEquiv_truncTwo
                (R := R) (d := d)).toAlgHom)) =
        ((idealOfVars_trivSqZero_algEquiv_truncTwo
            (R := R) (d := d)).symm.toAlgHom).comp
          (((TrivSqZeroExt.map b.equivFun.toLinearMap).comp
              (TrivSqZeroExt.map b.equivFun.symm.toLinearMap)).comp
            (idealOfVars_trivSqZero_algEquiv_truncTwo
              (R := R) (d := d)).toAlgHom) := by
              rw [AlgHom.comp_assoc, ← AlgHom.comp_assoc]
      _ = ((idealOfVars_trivSqZero_algEquiv_truncTwo
              (R := R) (d := d)).symm.toAlgHom).comp
            ((AlgHom.id R (TrivSqZeroExt R (Fin d → R))).comp
              (idealOfVars_trivSqZero_algEquiv_truncTwo
                (R := R) (d := d)).toAlgHom) := by
              rw [hsourceBasis]
      _ = ((idealOfVars_trivSqZero_algEquiv_truncTwo
              (R := R) (d := d)).symm.toAlgHom).comp
            (idealOfVars_trivSqZero_algEquiv_truncTwo
              (R := R) (d := d)).toAlgHom := by
              rw [AlgHom.id_comp]
      _ = AlgHom.id R
            (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 2) := by
              simpa using
                (AlgEquiv.symm_comp
                  (R := R)
                  (idealOfVars_trivSqZero_algEquiv_truncTwo (R := R) (d := d)))
  · -- Repeat the same comparison in the opposite direction, cancelling the source model first.
    rw [trunc_two_algHom_via_trivSqZero_models (R := R) (S := S) (σ := σ) hσ b f hf]
    rw [trunc_two_inverse_via_trivSqZero_models]
    -- Reassociate to expose the exact `eP2 ≫ eP2.symm` middle factor, then the basis transport.
    rw [AlgHom.comp_assoc, AlgHom.comp_assoc]
    rw [trunc_two_source_transport_cancel (R := R) (S := S) (σ := σ) (hσ := hσ)]
    calc
      ((smooth_section_trivSqZero_algEquiv_kerSquareQuot
          (R := R) (S := S) (σ := σ) hσ).toAlgHom).comp
          ((TrivSqZeroExt.map b.equivFun.symm.toLinearMap).comp
            ((TrivSqZeroExt.map b.equivFun.toLinearMap).comp
              (smooth_section_trivSqZero_algEquiv_kerSquareQuot
                (R := R) (S := S) (σ := σ) hσ).symm.toAlgHom)) =
        ((smooth_section_trivSqZero_algEquiv_kerSquareQuot
            (R := R) (S := S) (σ := σ) hσ).toAlgHom).comp
          (((TrivSqZeroExt.map b.equivFun.symm.toLinearMap).comp
              (TrivSqZeroExt.map b.equivFun.toLinearMap)).comp
            (smooth_section_trivSqZero_algEquiv_kerSquareQuot
              (R := R) (S := S) (σ := σ) hσ).symm.toAlgHom) := by
              rw [AlgHom.comp_assoc, ← AlgHom.comp_assoc]
      _ = ((smooth_section_trivSqZero_algEquiv_kerSquareQuot
              (R := R) (S := S) (σ := σ) hσ).toAlgHom).comp
            ((AlgHom.id R (TrivSqZeroExt R (RingHom.ker σ).Cotangent)).comp
              (smooth_section_trivSqZero_algEquiv_kerSquareQuot
                (R := R) (S := S) (σ := σ) hσ).symm.toAlgHom) := by
              rw [htargetBasis]
      _ = ((smooth_section_trivSqZero_algEquiv_kerSquareQuot
              (R := R) (S := S) (σ := σ) hσ).toAlgHom).comp
            (smooth_section_trivSqZero_algEquiv_kerSquareQuot
              (R := R) (S := S) (σ := σ) hσ).symm.toAlgHom := by
              rw [AlgHom.id_comp]
      _ = AlgHom.id R (S ⧸ (RingHom.ker σ) ^ 2) := by
              simpa using
                (AlgEquiv.comp_symm
                  (R := R)
                  (smooth_section_trivSqZero_algEquiv_kerSquareQuot
                    (R := R) (S := S) (σ := σ) hσ))

/-- Helper for Lemma 10.139.4: for any ideal `K`, the transition ideal `K^n / K^(n + 1)` in
`A / K^(n + 1)` has square zero once `n > 0`. -/
private theorem quotient_pow_transition_square_zero
    {A : Type*} [CommRing A] (K : Ideal A) {n : ℕ} (hn : 0 < n) :
    (Ideal.map (Ideal.Quotient.mk (K ^ (n + 1))) (K ^ n)) ^ 2 = ⊥ := by
  -- The square is the image of `K^(2n)`, and `2n ≥ n + 1` for positive `n`.
  rw [pow_two, ← Ideal.map_mul, ← pow_add]
  have hle : n + 1 ≤ n + n := by
    omega
  exact eq_bot_mono
    (Ideal.map_mono (Ideal.pow_le_pow_right hle))
    (Ideal.map_quotient_self _)

/-- Helper for Lemma 10.139.4: the kernel of the quotient transition `A / K^(n + 1) → A / K^n`
is the image of `K^n` in `A / K^(n + 1)`. -/
private theorem factorPow_kernel_eq_map_pow
    {A : Type*} [CommRing A] (K : Ideal A) (n : ℕ) :
    RingHom.ker (Ideal.Quotient.factorPow K (Nat.le_succ n)) =
      Ideal.map (Ideal.Quotient.mk (K ^ (n + 1))) (K ^ n) := by
  -- This is the quotient-power kernel description specialized to successive powers.
  simpa [Ideal.Quotient.factorPow] using
    (Ideal.Quotient.factor_ker (I := K ^ (n + 1)) (J := K ^ n)
      (Ideal.pow_le_pow_right (Nat.le_succ n)))

/-- Helper for Lemma 10.139.4: for any ideal `K`, the kernel of the quotient transition
`A / K^(n + 1) → A / K^n` is nilpotent. -/
private theorem factorPow_transition_kernel_isNilpotent
    {A : Type*} [CommRing A] (K : Ideal A) {n : ℕ} (hn : 0 < n) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.factorPow K (Nat.le_succ n))) := by
  -- The transition kernel is the image of `K^n`, and its square vanishes in `A / K^(n + 1)`.
  refine ⟨2, ?_⟩
  rw [factorPow_kernel_eq_map_pow (R := R) (S := S) (σ := σ) (hσ := hσ)
    (A := A) (K := K) (n := n)]
  simpa using
    quotient_pow_transition_square_zero (R := R) (S := S) (σ := σ) (hσ := hσ)
      (A := A) (K := K) (n := n) hn

/-- Helper for Lemma 10.139.4: the kernel of the transition
`P / J^(n + 1) → P / J^n` is square-zero, so it is nilpotent. -/
private theorem truncation_transition_kernel_mul_eq_zero {d : ℕ} {n : ℕ}
    (hn : 0 < n)
    {x y : MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)}
    (hx :
      x ∈ RingHom.ker
        (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)))
    (hy :
      y ∈ RingHom.ker
        (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n))) :
    x * y = 0 := by
  have hx' :
      x ∈ Ideal.map
        (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)))
    ((MvPolynomial.idealOfVars (Fin d) R) ^ n) := by
    -- The transition kernel is exactly the image of the previous power `J^n`.
    rw [factorPow_kernel_eq_map_pow (R := R) (S := S) (σ := σ) (hσ := hσ)
      (A := MvPolynomial (Fin d) R)
      (K := MvPolynomial.idealOfVars (Fin d) R) (n := n)] at hx
    exact hx
  have hy' :
      y ∈ Ideal.map
        (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)))
    ((MvPolynomial.idealOfVars (Fin d) R) ^ n) := by
    -- The same kernel description applies to the second factor.
    rw [factorPow_kernel_eq_map_pow (R := R) (S := S) (σ := σ) (hσ := hσ)
      (A := MvPolynomial (Fin d) R)
      (K := MvPolynomial.idealOfVars (Fin d) R) (n := n)] at hy
    exact hy
  have hxy :
      x * y ∈
        (Ideal.map
          (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)))
          ((MvPolynomial.idealOfVars (Fin d) R) ^ n)) ^ 2 := by
    -- Products of kernel elements lie in the square of the transition ideal.
    rw [pow_two]
    exact Ideal.mul_mem_mul hx' hy'
  have hsq :
      (Ideal.map
        (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)))
        ((MvPolynomial.idealOfVars (Fin d) R) ^ n)) ^ 2 = ⊥ := by
    -- The image ideal is square-zero because `2n ≥ n + 1` for positive `n`.
    simpa using
      quotient_pow_transition_square_zero (R := R) (S := S) (σ := σ) (hσ := hσ)
        (A := MvPolynomial (Fin d) R)
        (K := MvPolynomial.idealOfVars (Fin d) R) (n := n) hn
  have hzero_mem :
      x * y ∈
        (⊥ :
          Ideal
            (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))) := by
    simpa [hsq] using hxy
  -- Passing to the quotient by `J^(n + 1)` kills every element of the square of the transition
  -- ideal, so the product vanishes.
  simpa using hzero_mem

/-- Helper for Lemma 10.139.4: reducing `A / K^(m + 1)` directly to `A / K` has kernel equal to
the image of `K` in `A / K^(m + 1)`. -/
private theorem factorPow_to_one_kernel_eq_map
    {A : Type*} [CommRing A] (K : Ideal A) (m : ℕ) :
    RingHom.ker
      (Ideal.Quotient.factorPow K (Nat.succ_le_of_lt (Nat.succ_pos m))) =
        Ideal.map (Ideal.Quotient.mk (K ^ (m + 1))) K := by
  -- This is the power-transition kernel formula specialized to reduction all the way to level `1`.
  rw [RingHom.ker_eq_comap_bot]
  have hmap : Ideal.map (Ideal.Quotient.mk (K ^ 1)) K = ⊥ := by
    rw [pow_one]
    exact Ideal.map_quotient_self K
  rw [← hmap]
  simpa [pow_one] using
    (Ideal.map_mk_comap_factorPow (I := K) (a := 1) (b := m + 1)
      (Nat.succ_pos 0) (Nat.succ_le_of_lt (Nat.succ_pos m)))

/-- Helper for Lemma 10.139.4: if an endomorphism of `P / J^(n + 1)` becomes the identity after
reducing modulo `J^n`, then the error on each variable class lies in the transition kernel. -/
private theorem truncation_selfmap_variable_error_mem_kernel {d : ℕ} {n : ℕ}
    (α : MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
    (hα :
      (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)).comp α =
        Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n))
    (i : Fin d) :
    α (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)) (MvPolynomial.X i)) -
        Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
          (MvPolynomial.X i) ∈
      RingHom.ker
        (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)) := by
  -- Apply the quotient transition to the variable error and use that `α` fixes the lower
  -- truncation to see that the error reduces to zero.
  rw [RingHom.mem_ker]
  calc
    Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)
        (α (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
          (MvPolynomial.X i)) -
          Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
            (MvPolynomial.X i)) =
      Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)
          (α (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
            (MvPolynomial.X i))) -
        Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)
          (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
            (MvPolynomial.X i)) := by
          simp
    _ =
      Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)
          (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
            (MvPolynomial.X i)) -
        Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)
          (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
            (MvPolynomial.X i)) := by
          -- Evaluate the identity `q ∘ α = q` on the variable class.
          have hαi :=
            congrArg
              (fun β =>
                β
                  (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
                    (MvPolynomial.X i)))
              hα
          simpa [AlgHom.comp_apply] using congrArg
            (fun z =>
              z - Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)
                (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
                  (MvPolynomial.X i))) hαi
    _ = 0 := sub_self _

/-- Helper for Lemma 10.139.4: each variable class in `P / J^(n + 1)` comes from the image of the
variable ideal `J`. -/
private theorem truncation_variable_class_mem_idealOfVars_image {d n : ℕ} (i : Fin d) :
    Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)) (MvPolynomial.X i) ∈
      Ideal.map
        (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)))
        (MvPolynomial.idealOfVars (Fin d) R) := by
  -- The quotient class of `X i` is the image of the corresponding generator of `J`.
  simpa [MvPolynomial.idealOfVars] using
    (Ideal.mem_map_of_mem
      (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)))
      (Ideal.subset_span (Set.mem_range_self i) :
        MvPolynomial.X i ∈ MvPolynomial.idealOfVars (Fin d) R))

/-- Helper for Lemma 10.139.4: the variable error already lands in the image of the variable ideal
`J`, which is the descent condition needed for the correction map. -/
private theorem truncation_selfmap_variable_error_mem_idealOfVars_image {d : ℕ} {n : ℕ}
    (hn : 0 < n)
    (α : MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
    (hα :
      (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)).comp α =
        Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n))
    (i : Fin d) :
    α (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)) (MvPolynomial.X i)) -
        Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
          (MvPolynomial.X i) ∈
      Ideal.map
        (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)))
        (MvPolynomial.idealOfVars (Fin d) R) := by
  let J : Ideal (MvPolynomial (Fin d) R) := MvPolynomial.idealOfVars (Fin d) R
  have hmem :
      α (Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X i)) -
          Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X i) ∈
        Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) (J ^ n) := by
    -- First identify the transition kernel with the image of `J ^ n`.
    rw [← factorPow_kernel_eq_map_pow (R := R) (S := S) (σ := σ) (hσ := hσ)
      (A := MvPolynomial (Fin d) R) (K := J) (n := n)]
    exact truncation_selfmap_variable_error_mem_kernel
      (R := R) (S := S) (σ := σ) (hσ := hσ) α hα i
  -- Since `n > 0`, the previous power `J ^ n` lies inside `J`.
  exact
    (Ideal.map_mono
      (show J ^ n ≤ J from by
        simpa [pow_one] using (Ideal.pow_le_pow_right (I := J) hn)))
      hmem

/-- Helper for Lemma 10.139.4: the corrected image of each variable still lies in the image of the
variable ideal `J`. -/
private theorem truncation_selfmap_correction_variable_mem_idealOfVars_image
    {d : ℕ} {n : ℕ} (hn : 0 < n)
    (α : MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
    (hα :
      (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)).comp α =
        Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n))
    (i : Fin d) :
    Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)) (MvPolynomial.X i) -
        (α (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
            (MvPolynomial.X i)) -
          Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
            (MvPolynomial.X i)) ∈
      Ideal.map
        (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)))
        (MvPolynomial.idealOfVars (Fin d) R) := by
  -- Both the variable class and its correction error lie in the image of `J`.
  exact sub_mem
    (truncation_variable_class_mem_idealOfVars_image
      (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) i)
    (truncation_selfmap_variable_error_mem_idealOfVars_image
      (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) hn α hα i)

/-- Helper for Lemma 10.139.4: the variable-wise correction evaluation sends the variable ideal
into the visible image of `J` in `P / J^(n + 1)`. -/
private theorem truncation_selfmap_correction_map_idealOfVars_le_visible {d : ℕ} {n : ℕ}
    (hn : 0 < n)
    (α : MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
    (hα :
      (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)).comp α =
        Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)) :
    Ideal.map
        (MvPolynomial.aeval
          (fun i : Fin d ↦
            Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
                (MvPolynomial.X i) -
              (α (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
                  (MvPolynomial.X i)) -
                Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
                  (MvPolynomial.X i)))).toRingHom
        (MvPolynomial.idealOfVars (Fin d) R) ≤
      Ideal.map
        (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)))
        (MvPolynomial.idealOfVars (Fin d) R) := by
  let J : Ideal (MvPolynomial (Fin d) R) := MvPolynomial.idealOfVars (Fin d) R
  let F :
      MvPolynomial (Fin d) R →ₐ[R] MvPolynomial (Fin d) R ⧸ J ^ (n + 1) :=
    MvPolynomial.aeval fun i : Fin d ↦
      Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X i) -
        (α (Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X i)) -
          Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X i))
  -- Route correction: the descent proof should pass through ideal containment `map F J ≤ map mk J`
  -- rather than a large direct `aeval` computation on `J^(n + 1)`.
  rw [Ideal.map_le_iff_le_comap]
  change Ideal.span (Set.range MvPolynomial.X) ≤
    Ideal.comap F.toRingHom (Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J)
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  change F (MvPolynomial.X i) ∈ Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J
  simpa [F, J] using
    truncation_selfmap_correction_variable_mem_idealOfVars_image
      (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) hn α hα i

/-- Helper for Lemma 10.139.4: the variable-wise correction evaluation sends `J^(n + 1)` to zero,
so it descends to an endomorphism of `P / J^(n + 1)`. -/
private theorem truncation_selfmap_correction_descends {d : ℕ} {n : ℕ}
    (hn : 0 < n)
    (α : MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
    (hα :
      (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)).comp α =
        Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)) :
    ∀ x : MvPolynomial (Fin d) R, x ∈ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) →
      MvPolynomial.aeval
          (fun i : Fin d ↦
            Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
                (MvPolynomial.X i) -
              (α (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
                  (MvPolynomial.X i)) -
                Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
                  (MvPolynomial.X i))) x = 0 := by
  let J : Ideal (MvPolynomial (Fin d) R) := MvPolynomial.idealOfVars (Fin d) R
  let F :
      MvPolynomial (Fin d) R →ₐ[R] MvPolynomial (Fin d) R ⧸ J ^ (n + 1) :=
    MvPolynomial.aeval fun i : Fin d ↦
      Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X i) -
        (α (Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X i)) -
          Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X i))
  have hJ :
      Ideal.map F.toRingHom J ≤
        Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J := by
    -- First place every corrected variable image back inside the visible image of `J`.
    simpa [F, J] using
      truncation_selfmap_correction_map_idealOfVars_le_visible
        (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) hn α hα
  have hpow :
      Ideal.map F.toRingHom (J ^ (n + 1)) ≤
        (Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J) ^ (n + 1) := by
    -- Raising the containment to the `(n + 1)`st power follows from `map_pow`.
    simpa [Ideal.map_pow] using Ideal.pow_right_mono hJ (n + 1)
  have hvisible_zero :
      (Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J) ^ (n + 1) = ⊥ := by
    -- The visible ideal to the `(n + 1)`st power is the image of `J^(n + 1)`, hence zero.
    calc
      (Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J) ^ (n + 1) =
          Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) (J ^ (n + 1)) := by
            rw [Ideal.map_pow]
      _ = ⊥ := Ideal.map_quotient_self _
  intro x hx
  have hx_map : F x ∈ (Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J) ^ (n + 1) := by
    exact hpow (Ideal.mem_map_of_mem F.toRingHom hx)
  have hx_zero :
      F x ∈
        (⊥ :
          Ideal (MvPolynomial (Fin d) R ⧸ J ^ (n + 1))) := by
    simpa [hvisible_zero] using hx_map
  simpa [F, J] using hx_zero

/-- Helper for Lemma 10.139.4: correcting each variable by its error defines the quotient
endomorphism suggested by the source proof. -/
private noncomputable def truncation_selfmap_correction {d : ℕ} {n : ℕ}
    (hn : 0 < n)
    (α : MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
    (hα :
      (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)).comp α =
        Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)) :
    MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) :=
  Ideal.Quotient.liftₐ ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
    (MvPolynomial.aeval fun i : Fin d ↦
      Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)) (MvPolynomial.X i) -
        (α (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
            (MvPolynomial.X i)) -
          Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
            (MvPolynomial.X i)))
    (truncation_selfmap_correction_descends
      (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) hn α hα)

/-- Helper for Lemma 10.139.4: the correction endomorphism still reduces to the identity modulo
`J^n`. -/
private theorem truncation_selfmap_correction_factorPow_comp {d : ℕ} {n : ℕ}
    (hn : 0 < n)
    (α : MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
    (hα :
      (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)).comp α =
        Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)) :
    (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)).comp
        (truncation_selfmap_correction
          (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) hn α hα) =
      Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n) := by
  let J : Ideal (MvPolynomial (Fin d) R) := MvPolynomial.idealOfVars (Fin d) R
  let q :
      MvPolynomial (Fin d) R ⧸ J ^ (n + 1) →ₐ[R]
        MvPolynomial (Fin d) R ⧸ J ^ n :=
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ n))
  -- Route correction: the correction map is determined by its variable values, and modulo `J^n`
  -- the source error term on each variable already lies in the transition kernel.
  have hq :
      q.comp
          (truncation_selfmap_correction
            (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) hn α hα) =
        q := by
    apply Ideal.Quotient.algHom_ext (R₁ := R)
      (A := MvPolynomial (Fin d) R) (I := J ^ (n + 1))
      (S := MvPolynomial (Fin d) R ⧸ J ^ n)
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    let err :
        MvPolynomial (Fin d) R ⧸ J ^ (n + 1) :=
      α (Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X i)) -
        Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X i)
    have hcorr :
        truncation_selfmap_correction
            (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) hn α hα
            (Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X i)) =
          Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X i) - err := by
      -- Evaluate the quotient lift on the generator `X i`.
      have hcomp :
          (truncation_selfmap_correction
              (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) hn α hα).comp
              (Ideal.Quotient.mkₐ R (J ^ (n + 1))) =
            MvPolynomial.aeval fun j : Fin d ↦
              Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X j) -
                (α (Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X j)) -
                  Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X j)) := by
        simpa [truncation_selfmap_correction] using
          (Ideal.Quotient.liftₐ_comp (J ^ (n + 1))
            (MvPolynomial.aeval fun j : Fin d ↦
              Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X j) -
                (α (Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X j)) -
                  Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X j)))
            (truncation_selfmap_correction_descends
              (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) hn α hα))
      simpa [err] using AlgHom.congr_fun hcomp (MvPolynomial.X i)
    have herr_zero : q err = 0 := by
      -- The source hypothesis `q ∘ α = q` says exactly that the variable error dies modulo `J^n`.
      exact RingHom.mem_ker.mp <|
        truncation_selfmap_variable_error_mem_kernel
          (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) α hα
          i
    -- After reducing modulo `J^n`, only the original variable class remains.
    calc
      q
          (truncation_selfmap_correction
            (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) hn α hα
            (Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X i))) =
        q (Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X i) - err) := by
          rw [hcorr]
      _ = q (Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X i)) - q err := by
          simp [q]
      _ = q (Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X i)) := by
          simp [herr_zero]
  exact congrArg AlgHom.toRingHom hq

/-- Helper for Lemma 10.139.4: once the variable errors lie in the transition kernel, their
pairwise products vanish because that kernel is square-zero. -/
private theorem truncation_selfmap_variable_error_mul_eq_zero {d : ℕ} {n : ℕ}
    (hn : 0 < n)
    (α : MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
    (hα :
      (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)).comp α =
        Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n))
    (i j : Fin d) :
    (α (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)) (MvPolynomial.X i)) -
        Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
          (MvPolynomial.X i)) *
      (α (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)) (MvPolynomial.X j)) -
        Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
          (MvPolynomial.X j)) = 0 := by
  -- Each variable error lies in the square-zero transition kernel, so their product vanishes.
  apply truncation_transition_kernel_mul_eq_zero (R := R) (S := S) (σ := σ) (hσ := hσ)
    (d := d) (n := n) hn
  · exact truncation_selfmap_variable_error_mem_kernel
      (R := R) (S := S) (σ := σ) (hσ := hσ) α hα i
  · exact truncation_selfmap_variable_error_mem_kernel
      (R := R) (S := S) (σ := σ) (hσ := hσ) α hα j

/-- Helper for Lemma 10.139.4: any endomorphism reducing to the identity modulo `J^n` differs
from the identity by an element of the transition piece `J^n / J^(n + 1)` on every input. -/
private theorem truncation_selfmap_sub_mem_transition_image {d : ℕ} {n : ℕ}
    (γ : MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
    (hγ :
      (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)).comp γ =
        Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n))
    (y : MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)) :
    γ y - y ∈
      Ideal.map
        (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)))
        ((MvPolynomial.idealOfVars (Fin d) R) ^ n) := by
  let J : Ideal (MvPolynomial (Fin d) R) := MvPolynomial.idealOfVars (Fin d) R
  let q :
      MvPolynomial (Fin d) R ⧸ J ^ (n + 1) →+*
        MvPolynomial (Fin d) R ⧸ J ^ n :=
    Ideal.Quotient.factorPow J (Nat.le_succ n)
  -- The hypothesis `q ∘ γ = q` says exactly that `γ y - y` lands in the transition kernel.
  rw [← factorPow_kernel_eq_map_pow (R := R) (S := S) (σ := σ) (hσ := hσ)
    (A := MvPolynomial (Fin d) R) (K := J) (n := n)]
  rw [RingHom.mem_ker]
  have hy := congrArg (fun β ↦ β y) hγ
  calc
    q (γ y - y) = q (γ y) - q y := by simp [q]
    _ = q y - q y := by simpa [q, AlgHom.comp_apply] using congrArg (fun z ↦ z - q y) hy
    _ = 0 := sub_self _

/-- Helper for Lemma 10.139.4: the stage-`1` inverse `σ₁` is the canonical transport
`S / I ≃ R ≃ P / J`, where `I = ker σ` and `J` is the variable ideal. -/
private noncomputable def smooth_section_stageOne_inverse {d : ℕ} :
    S ⧸ RingHom.ker σ →ₐ[R]
      MvPolynomial (Fin d) R ⧸ MvPolynomial.idealOfVars (Fin d) R :=
  ((idealOfVars_quotientAlgEquiv (R := R) (d := d)).symm.toAlgHom).comp
    ((smooth_section_quotientKerAlgEquiv (R := R) (S := S) (σ := σ) hσ).toAlgHom)

/-- Helper for Lemma 10.139.4: the first power of the variable ideal is the variable ideal itself. -/
private theorem idealOfVars_pow_one_eq {d : ℕ} :
    (MvPolynomial.idealOfVars (Fin d) R) ^ 1 = MvPolynomial.idealOfVars (Fin d) R := by
  simp

/-- Helper for Lemma 10.139.4: the first power of `ker σ` is `ker σ` itself. -/
private theorem smooth_section_ker_pow_one_eq :
    (RingHom.ker σ) ^ 1 = RingHom.ker σ := by
  simp

/-- Helper for Lemma 10.139.4: the source level-`1` quotient `P / J^1` is canonically identified
with `P / J`. -/
private noncomputable def idealOfVars_powOneQuotientAlgEquiv {d : ℕ} :
    (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 1) ≃ₐ[R]
      (MvPolynomial (Fin d) R ⧸ MvPolynomial.idealOfVars (Fin d) R) :=
  Ideal.quotientEquivAlgOfEq (R₁ := R) (A := MvPolynomial (Fin d) R)
    (idealOfVars_pow_one_eq (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d))

/-- Helper for Lemma 10.139.4: the target level-`1` quotient `S / I^1` is canonically identified
with `S / I`. -/
private noncomputable def smooth_section_kerPowOneQuotientAlgEquiv :
    (S ⧸ (RingHom.ker σ) ^ 1) ≃ₐ[R] (S ⧸ RingHom.ker σ) :=
  Ideal.quotientEquivAlgOfEq (R₁ := R) (A := S)
    (smooth_section_ker_pow_one_eq (R := R) (S := S) (σ := σ) (hσ := hσ))

/-- Helper for Lemma 10.139.4: after transporting both source and target level-`1` quotients along
`pow_one`, the first truncation map is exactly the canonical quotient transport `P / J ≃ R ≃ S / I`.
-/
private theorem truncation_one_eq_canonical_transport {d : ℕ}
    (f : Fin d → RingHom.ker σ) :
    (smooth_section_kerPowOneQuotientAlgEquiv (R := R) (S := S) (σ := σ) (hσ := hσ)).toAlgHom.comp
        (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f 1) =
      (((smooth_section_quotientKerAlgEquiv
            (R := R) (S := S) (σ := σ) hσ).symm.toAlgHom).comp
          (idealOfVars_quotientAlgEquiv (R := R) (d := d)).toAlgHom).comp
        (idealOfVars_powOneQuotientAlgEquiv
          (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d)).toAlgHom := by
  -- Compare the transported level-`1` maps after precomposing with the quotient map from the
  -- polynomial ring; then quotient extensionality reduces the proof to the variable classes.
  refine Ideal.Quotient.algHom_ext _ ?_
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  -- On each variable, the left side is the quotient class of `f i`, hence zero in `S / ker σ`,
  -- while the right side is zero because `idealOfVars_quotientAlgEquiv` comes from zero evaluation.
  calc
    ((((smooth_section_kerPowOneQuotientAlgEquiv
        (R := R) (S := S) (σ := σ) (hσ := hσ)).toAlgHom).comp
          (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f 1)).comp
          (Ideal.Quotient.mkₐ R ((MvPolynomial.idealOfVars (Fin d) R) ^ 1)))
        (MvPolynomial.X i) =
      Ideal.Quotient.mk (RingHom.ker σ) ((f i : RingHom.ker σ) : S) := by
        simp [cotangent_lift_truncated_map, cotangent_lift_polynomial_map,
          smooth_section_kerPowOneQuotientAlgEquiv]
    _ = 0 := by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (f i).property
    _ = ((smooth_section_quotientKerAlgEquiv
        (R := R) (S := S) (σ := σ) hσ).symm) (0 : R) := by
      simpa using
        (map_zero ((smooth_section_quotientKerAlgEquiv
          (R := R) (S := S) (σ := σ) hσ).symm.toAlgHom)).symm
    _ =
      ((((smooth_section_quotientKerAlgEquiv
          (R := R) (S := S) (σ := σ) hσ).symm.toAlgHom).comp
            (idealOfVars_quotientAlgEquiv (R := R) (d := d)).toAlgHom).comp
            (idealOfVars_powOneQuotientAlgEquiv
              (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d)).toAlgHom).comp
            (Ideal.Quotient.mkₐ R ((MvPolynomial.idealOfVars (Fin d) R) ^ 1))
            (MvPolynomial.X i) := by
        symm
        change
          ((smooth_section_quotientKerAlgEquiv
              (R := R) (S := S) (σ := σ) hσ).symm.toAlgHom)
              (((((idealOfVars_quotientAlgEquiv (R := R) (d := d)).toAlgHom).comp
                  (idealOfVars_powOneQuotientAlgEquiv
                    (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d)).toAlgHom).comp
                    (Ideal.Quotient.mkₐ R ((MvPolynomial.idealOfVars (Fin d) R) ^ 1)))
                (MvPolynomial.X i)) =
            ((smooth_section_quotientKerAlgEquiv
              (R := R) (S := S) (σ := σ) hσ).symm.toAlgHom) 0
        congr 1
        calc
          ((((idealOfVars_quotientAlgEquiv (R := R) (d := d)).toAlgHom).comp
              (idealOfVars_powOneQuotientAlgEquiv
                (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d)).toAlgHom).comp
                (Ideal.Quotient.mkₐ R ((MvPolynomial.idealOfVars (Fin d) R) ^ 1)))
              (MvPolynomial.X i) =
            (idealOfVars_quotientAlgEquiv (R := R) (d := d))
              (Ideal.Quotient.mk (MvPolynomial.idealOfVars (Fin d) R) (MvPolynomial.X i)) := by
                simp [idealOfVars_powOneQuotientAlgEquiv]
          _ = (idealOfVars_quotientAlgEquiv (R := R) (d := d)) 0 := by
            congr 1
            exact Ideal.Quotient.eq_zero_iff_mem.mpr (idealOfVars_variable_mem (R := R) i)
          _ = 0 := by
            simpa using map_zero ((idealOfVars_quotientAlgEquiv (R := R) (d := d)).toAlgHom)

/-- Helper for Lemma 10.139.4: the canonical stage-`1` inverse transported back to the
`pow_one` quotients. This is the level-`1` inverse used to normalize the successor lift. -/
private noncomputable def smooth_section_stageOne_inverse_powOne {d : ℕ} :
    S ⧸ (RingHom.ker σ) ^ 1 →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 1 :=
  (((idealOfVars_powOneQuotientAlgEquiv
      (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d)).symm).toAlgHom).comp
    ((smooth_section_stageOne_inverse (R := R) (S := S) (σ := σ) hσ).comp
      (smooth_section_kerPowOneQuotientAlgEquiv
        (R := R) (S := S) (σ := σ) (hσ := hσ)).toAlgHom)

/-- Helper for Lemma 10.139.4: the transported stage-`1` inverse is indeed inverse to the first
truncation map. This is the exact level-`1` normalization used in the textbook induction. -/
private theorem smooth_section_stageOne_inverse_powOne_spec {d : ℕ}
    (f : Fin d → RingHom.ker σ) :
    (smooth_section_stageOne_inverse_powOne (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d)).comp
        (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f 1) =
      AlgHom.id R
        (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 1) := by
  -- Route correction: normalize the level-`1` inverse on the `pow_one` quotients first, so later
  -- successor lifts can be compared to the canonical stage-`1` inverse without ad hoc transports.
  let eJ1 :=
    idealOfVars_powOneQuotientAlgEquiv (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d)
  let eP1 := idealOfVars_quotientAlgEquiv (R := R) (d := d)
  let eS1 := smooth_section_quotientKerAlgEquiv (R := R) (S := S) (σ := σ) hσ
  have htransport :=
    truncation_one_eq_canonical_transport (R := R) (S := S) (σ := σ) hσ f
  have hcomp :=
    congrArg
      (fun β =>
        (((eJ1.symm.toAlgHom).comp (eP1.symm.toAlgHom)).comp eS1.toAlgHom).comp β)
      htransport
  have hcancel :
      ((((eJ1.symm.toAlgHom).comp (eP1.symm.toAlgHom)).comp eS1.toAlgHom).comp
          (((eS1.symm.toAlgHom).comp eP1.toAlgHom).comp eJ1.toAlgHom)) =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 1) := by
    ext x
    simp
  simpa [smooth_section_stageOne_inverse_powOne, smooth_section_stageOne_inverse,
    AlgHom.comp_assoc] using hcomp.trans hcancel

/-- Helper for Lemma 10.139.4: the transported stage-`1` inverse is inverse to the first
truncation map in the opposite direction as well. This closes the entire level-`1` base case for
the source-faithful induction. -/
private theorem smooth_section_stageOne_inverse_powOne_spec_symm {d : ℕ}
    (f : Fin d → RingHom.ker σ) :
    (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f 1).comp
        (smooth_section_stageOne_inverse_powOne
          (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d)) =
      AlgHom.id R (S ⧸ (RingHom.ker σ) ^ 1) := by
  -- Apply the canonical quotient transport to the composite and cancel the stage-`1` source and
  -- target identifications explicitly.
  let eJ1 :=
    idealOfVars_powOneQuotientAlgEquiv (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d)
  let eP1 := idealOfVars_quotientAlgEquiv (R := R) (d := d)
  let eS1 := smooth_section_quotientKerAlgEquiv (R := R) (S := S) (σ := σ) hσ
  let eI1 :=
    smooth_section_kerPowOneQuotientAlgEquiv (R := R) (S := S) (σ := σ) (hσ := hσ)
  have htransport :=
    truncation_one_eq_canonical_transport (R := R) (S := S) (σ := σ) hσ f
  ext x
  apply eI1.injective
  -- Evaluate the transported first truncation at the canonical stage-`1` inverse and simplify
  -- through the quotient equivalences.
  calc
    eI1
        (((cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f 1).comp
          (smooth_section_stageOne_inverse_powOne
            (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d))) x) =
      ((((eS1.symm.toAlgHom).comp eP1.toAlgHom).comp eJ1.toAlgHom)
        ((smooth_section_stageOne_inverse_powOne
          (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d)) x)) := by
            exact AlgHom.congr_fun htransport
              ((smooth_section_stageOne_inverse_powOne
                (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d)) x)
    _ = eI1 x := by
      simp [smooth_section_stageOne_inverse_powOne, smooth_section_stageOne_inverse,
        AlgHom.comp_assoc, eJ1, eP1, eS1, eI1]


/-- Helper for Lemma 10.139.4: any actual inverse `σₙ` to `Ψtrunc n` reduces to the transported
stage-`1` inverse after passing from `n`th-order quotients to first-order quotients. -/
private theorem truncation_inverse_reduces_to_stage_one {d n : ℕ}
    (hn : 0 < n)
    (f : Fin d → RingHom.ker σ)
    (σn : S ⧸ (RingHom.ker σ) ^ n →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n)
    (hσΨ :
      σn.comp (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n) =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n))
    (hΨσ :
      (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n).comp σn =
        AlgHom.id R (S ⧸ (RingHom.ker σ) ^ n)) :
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.succ_le_of_lt hn))).comp σn =
      (smooth_section_stageOne_inverse_powOne
          (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d)).comp
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.succ_le_of_lt hn))) := by
  -- Evaluate both maps at a stage-`n` class, reduce via compatibility of `Ψtrunc`, and then use
  -- the verified stage-`1` inverse to close the comparison.
  ext x
  calc
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.succ_le_of_lt hn)) (σn x) =
      (smooth_section_stageOne_inverse_powOne
          (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d))
        ((cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f 1)
          (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.succ_le_of_lt hn)) (σn x))) := by
          symm
          exact AlgHom.congr_fun
            (smooth_section_stageOne_inverse_powOne_spec
              (R := R) (S := S) (σ := σ) hσ (d := d) f)
            (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.succ_le_of_lt hn)) (σn x))
    _ =
      (smooth_section_stageOne_inverse_powOne
          (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d))
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.succ_le_of_lt hn))
          ((cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n) (σn x))) := by
          congr 1
          exact (AlgHom.congr_fun
            (cotangent_lift_truncated_map_compatible
              (R := R) (S := S) (σ := σ) f (m := 1) (n := n)
              (Nat.succ_le_of_lt hn))
            (σn x)).symm
    _ =
      (smooth_section_stageOne_inverse_powOne
          (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d))
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.succ_le_of_lt hn)) x) := by
          congr 1
          exact congrArg
            (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.succ_le_of_lt hn)))
            (AlgHom.congr_fun hΨσ x)

/-- Helper for Lemma 10.139.4: once an inverse `σₙ` to `Ψtrunc n` has been constructed, formal
smoothness lifts it one stage further and the lift descends to
`S / (ker σ)^(n + 1) → P / J^(n + 1)`. This restores the textbook successor-lift step before the
variable-shift correction. -/
private theorem formally_smooth_lift_of_truncation_inverse_descends {d n : ℕ}
    (hn : 2 ≤ n)
    (f : Fin d → RingHom.ker σ)
    (σn : S ⧸ (RingHom.ker σ) ^ n →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n)
    (hσΨ :
      σn.comp (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n) =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n))
    (hΨσ :
      (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n).comp σn =
        AlgHom.id R (S ⧸ (RingHom.ker σ) ^ n)) :
    ∃ τbar : S ⧸ (RingHom.ker σ) ^ (n + 1) →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ n))).comp τbar =
        σn.comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ n))) := by
  let I : Ideal S := RingHom.ker σ
  let J : Ideal (MvPolynomial (Fin d) R) := MvPolynomial.idealOfVars (Fin d) R
  let qJ :
      MvPolynomial (Fin d) R ⧸ J ^ (n + 1) →ₐ[R]
        MvPolynomial (Fin d) R ⧸ J ^ n :=
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ n))
  let qI :
      S ⧸ I ^ (n + 1) →ₐ[R] S ⧸ I ^ n :=
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ n))
  let σlift : S →ₐ[R] MvPolynomial (Fin d) R ⧸ J ^ n :=
    σn.comp (Ideal.Quotient.mkₐ R (I ^ n))
  have hqJ_surj : Function.Surjective qJ := by
    intro x
    rcases Ideal.Quotient.factor_surjective
        (by simpa using (Ideal.pow_le_pow_right (I := J) (Nat.le_succ n))) x with ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  have hn0 : 0 < n := lt_of_lt_of_le (by simp) hn
  have hqJ_nilpotent : IsNilpotent (RingHom.ker qJ.toRingHom) := by
    change IsNilpotent (RingHom.ker (Ideal.Quotient.factorPow J (Nat.le_succ n)))
    exact factorPow_transition_kernel_isNilpotent
      (R := R) (S := S) (σ := σ) (hσ := hσ)
      (A := MvPolynomial (Fin d) R) (K := J) (n := n) hn0
  let τ : S →ₐ[R] MvPolynomial (Fin d) R ⧸ J ^ (n + 1) :=
    Algebra.FormallySmooth.liftOfSurjective σlift qJ hqJ_surj hqJ_nilpotent
  have hqJτ : qJ.comp τ = σlift := by
    simpa [τ, σlift] using
      (Algebra.FormallySmooth.comp_liftOfSurjective σlift qJ hqJ_surj hqJ_nilpotent)
  let qJ1 :
      MvPolynomial (Fin d) R ⧸ J ^ (n + 1) →ₐ[R]
        MvPolynomial (Fin d) R ⧸ J ^ 1 :=
    Ideal.Quotient.factorₐ R <| by
      simpa using (Ideal.pow_le_pow_right (I := J) (show 1 ≤ n + 1 by simp))
  let qJn1 :
      MvPolynomial (Fin d) R ⧸ J ^ n →ₐ[R]
        MvPolynomial (Fin d) R ⧸ J ^ 1 :=
    Ideal.Quotient.factorₐ R <| by
      simpa using (Ideal.pow_le_pow_right (I := J) (show 1 ≤ n by omega))
  let qIn1 :
      S ⧸ I ^ n →ₐ[R] S ⧸ I ^ 1 :=
    Ideal.Quotient.factorₐ R <| by
      simpa using (Ideal.pow_le_pow_right (I := I) (show 1 ≤ n by omega))
  let σ1lift : S →ₐ[R] MvPolynomial (Fin d) R ⧸ J ^ 1 :=
    (smooth_section_stageOne_inverse_powOne
      (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d)).comp
      (Ideal.Quotient.mkₐ R (I ^ 1))
  have hqJ1 :
      qJ1 = qJn1.comp qJ := by
    symm
    simpa [qJ1, qJn1, qJ] using
      (Ideal.Quotient.factorₐ_comp (R₁ := R)
        (I := J ^ (n + 1)) (J := J ^ n) (K := J ^ 1)
        (hIJ := Ideal.pow_le_pow_right (Nat.le_succ n))
        (hJK := by simpa using (Ideal.pow_le_pow_right (I := J) (show 1 ≤ n by omega))))
  have hqIn1_mk :
      qIn1.comp (Ideal.Quotient.mkₐ R (I ^ n)) = Ideal.Quotient.mkₐ R (I ^ 1) := by
    simpa [qIn1] using
      (Ideal.Quotient.factorₐ_comp_mk (R₁ := R)
        (I := I ^ n) (J := I ^ 1)
        (hIJ := by simpa using (Ideal.pow_le_pow_right (I := I) (show 1 ≤ n by omega))))
  have hqJ1τ : qJ1.comp τ = σ1lift := by
    -- Reduce the formal smooth lift all the way to level `1` and compare with the canonical
    -- stage-`1` inverse provided by the previously constructed inverse `σₙ`.
    calc
      qJ1.comp τ = (qJn1.comp qJ).comp τ := by rw [hqJ1]
      _ = qJn1.comp (qJ.comp τ) := by rw [AlgHom.comp_assoc]
      _ = qJn1.comp σlift := by rw [hqJτ]
      _ = (qJn1.comp σn).comp (Ideal.Quotient.mkₐ R (I ^ n)) := by
            change qJn1.comp (σn.comp (Ideal.Quotient.mkₐ R (I ^ n))) =
              (qJn1.comp σn).comp (Ideal.Quotient.mkₐ R (I ^ n))
            rw [AlgHom.comp_assoc]
      _ =
          ((smooth_section_stageOne_inverse_powOne
              (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d)).comp qIn1).comp
            (Ideal.Quotient.mkₐ R (I ^ n)) := by
              rw [truncation_inverse_reduces_to_stage_one
                (R := R) (S := S) (σ := σ) (hσ := hσ)
                (d := d) (n := n) hn0 f σn hσΨ hΨσ]
      _ =
          (smooth_section_stageOne_inverse_powOne
              (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d)).comp
            (qIn1.comp (Ideal.Quotient.mkₐ R (I ^ n))) := by
              rw [AlgHom.comp_assoc]
      _ = σ1lift := by
            rw [hqIn1_mk]
  have hmapI :
      Ideal.map τ.toRingHom I ≤ Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    have hx0 : qJ1 (τ x) = 0 := by
      calc
        qJ1 (τ x) = σ1lift x := by
          exact AlgHom.congr_fun hqJ1τ x
        _ = 0 := by
          have hxquot : Ideal.Quotient.mk (I ^ 1) x = 0 := by
            exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa [pow_one, I] using hx)
          simpa [σ1lift, hxquot]
    have hxker : τ x ∈ RingHom.ker qJ1.toRingHom := RingHom.mem_ker.mpr hx0
    rwa [show RingHom.ker qJ1.toRingHom =
        Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J by
          simpa [qJ1, pow_one, J] using
            (factorPow_to_one_kernel_eq_map
              (R := R) (S := S) (σ := σ) (hσ := hσ)
              (A := MvPolynomial (Fin d) R) (K := J) n)] at hxker
  have hpowI :
      Ideal.map τ.toRingHom (I ^ (n + 1)) ≤
        (Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J) ^ (n + 1) := by
    -- Once the lift carries `I` into the visible image of `J`, the same holds for all powers.
    simpa [Ideal.map_pow] using Ideal.pow_right_mono hmapI (n + 1)
  have hτ_zero :
      ∀ x : S, x ∈ I ^ (n + 1) → τ x = 0 := by
    intro x hx
    have hJpow_bot :
        (Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J) ^ (n + 1) = ⊥ := by
      calc
        (Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J) ^ (n + 1) =
          Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) (J ^ (n + 1)) := by
            rw [Ideal.map_pow]
        _ = ⊥ := Ideal.map_quotient_self _
    have hxpow :
        τ x ∈ (Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J) ^ (n + 1) := by
      exact hpowI <| Ideal.mem_map_of_mem _ hx
    have hxbot :
        τ x ∈
          (⊥ :
            Ideal (MvPolynomial (Fin d) R ⧸ J ^ (n + 1))) := by
      simpa [hJpow_bot] using hxpow
    simpa using hxbot
  let τbar :
      S ⧸ I ^ (n + 1) →ₐ[R] MvPolynomial (Fin d) R ⧸ J ^ (n + 1) :=
    Ideal.Quotient.liftₐ (I ^ (n + 1)) τ hτ_zero
  refine ⟨τbar, ?_⟩
  refine Ideal.Quotient.algHom_ext _ ?_
  ext x
  -- After precomposing with the quotient map from `S`, the descended lift is the original
  -- formally smooth lift `τ`, and `qI` reduces the quotient class of `x` modulo `I^n`.
  calc
    (((Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ n))).comp τbar).comp
        (Ideal.Quotient.mkₐ R (I ^ (n + 1)))) x =
      qJ (τ x) := by
        simp [τbar, qJ, AlgHom.comp_assoc]
    _ = σn (Ideal.Quotient.mk (I ^ n) x) := by
        exact AlgHom.congr_fun hqJτ x
    _ =
      ((σn.comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ n)))).comp
        (Ideal.Quotient.mkₐ R (I ^ (n + 1)))) x := by
          have hmk :
              ((Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ n))).comp
                (Ideal.Quotient.mkₐ R (I ^ (n + 1)))) x =
                Ideal.Quotient.mk (I ^ n) x := by
            simpa using
              AlgHom.congr_fun
                (Ideal.Quotient.factorₐ_comp_mk (R₁ := R)
                  (I := I ^ (n + 1)) (J := I ^ n)
                  (hIJ := Ideal.pow_le_pow_right (Nat.le_succ n)))
                x
          rw [← hmk]
          rfl

/-- Helper for Lemma 10.139.4: the formally-smooth lift of the canonical stage-`1` inverse to
`P / J^(n + 1)` sends `(ker σ)^(n + 1)` to zero, so it descends to a map
`S / (ker σ)^(n + 1) → P / J^(n + 1)`. -/
private theorem stage_one_formally_smooth_lift_descends_to_quotient_pow {d : ℕ} (n : ℕ) :
    Nonempty
      (S ⧸ (RingHom.ker σ) ^ (n + 1) →ₐ[R]
        MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)) := by
  let I : Ideal S := RingHom.ker σ
  let J : Ideal (MvPolynomial (Fin d) R) := MvPolynomial.idealOfVars (Fin d) R
  let σ1lift : S →ₐ[R] MvPolynomial (Fin d) R ⧸ J :=
    (smooth_section_stageOne_inverse (R := R) (S := S) (σ := σ) hσ).comp
      (Ideal.Quotient.mkₐ R I)
  let q1 :
      MvPolynomial (Fin d) R ⧸ J ^ (n + 1) →ₐ[R]
        MvPolynomial (Fin d) R ⧸ J :=
    Ideal.Quotient.factorₐ R <| by
      simpa using (Ideal.pow_le_pow_right (I := J) (show 1 ≤ n + 1 by simp))
  have hq1_surj : Function.Surjective q1 := by
    intro x
    rcases Ideal.Quotient.factor_surjective
        (by
          simpa using
            (Ideal.pow_le_pow_right (I := J) (show 1 ≤ n + 1 by simp))) x with ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  have hq1_ker :
      RingHom.ker q1.toRingHom =
        Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J := by
    simpa [q1] using
      (Ideal.Quotient.factor_ker (I := J ^ (n + 1)) (J := J) <| by
        simpa using (Ideal.pow_le_pow_right (I := J) (show 1 ≤ n + 1 by simp)))
  have hq1_nilpotent : IsNilpotent (RingHom.ker q1.toRingHom) := by
    refine ⟨n + 1, ?_⟩
    -- The image of `J` in `P / J^(n + 1)` has `(n + 1)`st power zero.
    rw [hq1_ker]
    calc
      (Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J) ^ (n + 1) =
        Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) (J ^ (n + 1)) := by
          rw [Ideal.map_pow]
      _ = ⊥ := Ideal.map_quotient_self _
  let τ :
      S →ₐ[R] MvPolynomial (Fin d) R ⧸ J ^ (n + 1) :=
    Algebra.FormallySmooth.liftOfSurjective σ1lift q1 hq1_surj hq1_nilpotent
  have hq1τ : q1.comp τ = σ1lift := by
    simpa [τ] using
      (Algebra.FormallySmooth.comp_liftOfSurjective σ1lift q1 hq1_surj hq1_nilpotent)
  have hmapI :
      Ideal.map τ.toRingHom I ≤ Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    -- Reducing the lift modulo `J` matches the stage-`1` inverse, so every element of `ker σ`
    -- lands in the kernel of `q1`, i.e. in the image of `J`.
    have hx0 :
        q1 (τ x) = 0 := by
      calc
        q1 (τ x) = σ1lift x := by
          exact AlgHom.congr_fun hq1τ x
        _ = 0 := by
          have hxquot : Ideal.Quotient.mk I x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
          simpa [σ1lift, hxquot]
    have hxker : τ x ∈ RingHom.ker q1.toRingHom := RingHom.mem_ker.mpr hx0
    rwa [hq1_ker] at hxker
  have hpowI :
      Ideal.map τ.toRingHom (I ^ (n + 1)) ≤
        (Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J) ^ (n + 1) := by
    -- Once `τ(I)` lies in the image of `J`, the same holds for `(n + 1)`st powers.
    simpa [Ideal.map_pow] using Ideal.pow_right_mono hmapI (n + 1)
  have hτ_zero :
      ∀ x : S, x ∈ I ^ (n + 1) → τ x = 0 := by
    intro x hx
    have hJpow_bot :
        (Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J) ^ (n + 1) = ⊥ := by
      calc
        (Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J) ^ (n + 1) =
          Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) (J ^ (n + 1)) := by
            rw [Ideal.map_pow]
        _ = ⊥ := Ideal.map_quotient_self _
    have hxpow :
        τ x ∈ (Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J) ^ (n + 1) := by
      exact hpowI <| Ideal.mem_map_of_mem _ hx
    have hxbot :
        τ x ∈
          (⊥ :
            Ideal (MvPolynomial (Fin d) R ⧸ J ^ (n + 1))) := by
      simpa [hJpow_bot] using hxpow
    simpa using hxbot
  let τbar :
      S ⧸ I ^ (n + 1) →ₐ[R] MvPolynomial (Fin d) R ⧸ J ^ (n + 1) :=
    Ideal.Quotient.liftₐ (I ^ (n + 1)) τ hτ_zero
  exact ⟨τbar⟩

/-- Helper for Lemma 10.139.4: a compatible family of quotient inverses packages into an
`R`-algebra equivalence between the corresponding adic completions. -/
private noncomputable def completion_algEquiv_of_truncation_inverses {d : ℕ}
    (Ψtrunc : (n : ℕ) →
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n →ₐ[R]
        S ⧸ (RingHom.ker σ) ^ n)
    (hΨtrunc :
      ∀ {m n : ℕ} (hmn : m ≤ n),
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp (Ψtrunc n) =
          (Ψtrunc m).comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)))
    (σtrunc : (n : ℕ) →
      S ⧸ (RingHom.ker σ) ^ n →ₐ[R]
        MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n)
    (hσtrunc :
      ∀ {m n : ℕ} (hmn : m ≤ n),
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp (σtrunc n) =
          (σtrunc m).comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)))
    (hσΨ : ∀ n,
      (σtrunc n).comp (Ψtrunc n) =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n))
    (hΨσ : ∀ n, (Ψtrunc n).comp (σtrunc n) = AlgHom.id R (S ⧸ (RingHom.ker σ) ^ n)) :
    AdicCompletion (RingHom.ker σ) S ≃ₐ[R]
      AdicCompletion (MvPolynomial.idealOfVars (Fin d) R) (MvPolynomial (Fin d) R) := by
  let toCompletionFamily : (n : ℕ) →
      AdicCompletion (RingHom.ker σ) S →ₐ[R]
        MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n :=
    fun n ↦ (σtrunc n).comp ((AdicCompletion.evalₐ (RingHom.ker σ) n).restrictScalars R)
  have htoCompletionFamily :
      ∀ {m n : ℕ} (hmn : m ≤ n),
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp
            (toCompletionFamily n) =
          toCompletionFamily m := by
    intro m n hmn
    ext x
    let p : AdicCompletion (RingHom.ker σ) S → Prop := fun y ↦
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp
          (toCompletionFamily n) y =
        toCompletionFamily m y
    change p x
    -- Reduce the compatibility check to a representative of the source completion.
    refine AdicCompletion.induction_on (I := RingHom.ker σ) (M := S) x ?_
    intro s
    dsimp [p, toCompletionFamily]
    have hs :
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn))
            (AdicCompletion.evalₐ (RingHom.ker σ) n ((AdicCompletion.mk (RingHom.ker σ) S) s)) =
          AdicCompletion.evalₐ (RingHom.ker σ) m ((AdicCompletion.mk (RingHom.ker σ) S) s) := by
      simpa [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorₐ_comp_mk] using
        (AdicCompletion.Ideal.mk_eq_mk (I := RingHom.ker σ) (m := m) (n := n) hmn s)
    -- On a concrete representative, the target equality is exactly the stagewise compatibility
    -- of `σtrunc`, together with the canonical quotient transition on `evalₐ`.
    calc
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn))
          ((σtrunc n)
            (AdicCompletion.evalₐ (RingHom.ker σ) n
              ((AdicCompletion.mk (RingHom.ker σ) S) s))) =
        (σtrunc m)
          ((Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn))
            (AdicCompletion.evalₐ (RingHom.ker σ) n
              ((AdicCompletion.mk (RingHom.ker σ) S) s))) := by
            exact AlgHom.congr_fun (hσtrunc hmn)
              (AdicCompletion.evalₐ (RingHom.ker σ) n
                ((AdicCompletion.mk (RingHom.ker σ) S) s))
      _ = (σtrunc m)
          (AdicCompletion.evalₐ (RingHom.ker σ) m
            ((AdicCompletion.mk (RingHom.ker σ) S) s)) := by
            exact congrArg (σtrunc m) hs
  let toCompletion :
      AdicCompletion (RingHom.ker σ) S →ₐ[R]
        AdicCompletion (MvPolynomial.idealOfVars (Fin d) R) (MvPolynomial (Fin d) R) :=
    AdicCompletion.liftAlgHom (MvPolynomial.idealOfVars (Fin d) R)
      toCompletionFamily htoCompletionFamily
  let fromCompletionFamily : (n : ℕ) →
      AdicCompletion (MvPolynomial.idealOfVars (Fin d) R) (MvPolynomial (Fin d) R) →ₐ[R]
        S ⧸ (RingHom.ker σ) ^ n :=
    fun n ↦ (Ψtrunc n).comp
      ((AdicCompletion.evalₐ (MvPolynomial.idealOfVars (Fin d) R) n).restrictScalars R)
  have hfromCompletionFamily :
      ∀ {m n : ℕ} (hmn : m ≤ n),
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp
            (fromCompletionFamily n) =
          fromCompletionFamily m := by
    intro m n hmn
    ext x
    let q :
        AdicCompletion (MvPolynomial.idealOfVars (Fin d) R) (MvPolynomial (Fin d) R) → Prop :=
      fun y ↦
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp
            (fromCompletionFamily n) y =
          fromCompletionFamily m y
    change q x
    -- The same quotientwise reduction works on the polynomial completion side.
    refine AdicCompletion.induction_on (I := MvPolynomial.idealOfVars (Fin d) R)
      (M := MvPolynomial (Fin d) R) x ?_
    intro p
    dsimp [q, fromCompletionFamily]
    have hp :
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn))
            (AdicCompletion.evalₐ (MvPolynomial.idealOfVars (Fin d) R) n
              ((AdicCompletion.mk (MvPolynomial.idealOfVars (Fin d) R)
                (MvPolynomial (Fin d) R)) p)) =
          AdicCompletion.evalₐ (MvPolynomial.idealOfVars (Fin d) R) m
            ((AdicCompletion.mk (MvPolynomial.idealOfVars (Fin d) R)
              (MvPolynomial (Fin d) R)) p) := by
      simpa [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorₐ_comp_mk] using
        (AdicCompletion.Ideal.mk_eq_mk (I := MvPolynomial.idealOfVars (Fin d) R)
          (m := m) (n := n) hmn p)
    -- The polynomial-side compatibility reduces to `hΨtrunc` on the quotient class of `p`.
    calc
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn))
          ((Ψtrunc n)
            (AdicCompletion.evalₐ (MvPolynomial.idealOfVars (Fin d) R) n
              ((AdicCompletion.mk (MvPolynomial.idealOfVars (Fin d) R)
                (MvPolynomial (Fin d) R)) p))) =
        (Ψtrunc m)
          ((Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn))
            (AdicCompletion.evalₐ (MvPolynomial.idealOfVars (Fin d) R) n
              ((AdicCompletion.mk (MvPolynomial.idealOfVars (Fin d) R)
                (MvPolynomial (Fin d) R)) p))) := by
            exact AlgHom.congr_fun (hΨtrunc hmn)
              (AdicCompletion.evalₐ (MvPolynomial.idealOfVars (Fin d) R) n
                ((AdicCompletion.mk (MvPolynomial.idealOfVars (Fin d) R)
                  (MvPolynomial (Fin d) R)) p))
      _ = (Ψtrunc m)
          (AdicCompletion.evalₐ (MvPolynomial.idealOfVars (Fin d) R) m
            ((AdicCompletion.mk (MvPolynomial.idealOfVars (Fin d) R)
              (MvPolynomial (Fin d) R)) p)) := by
            exact congrArg (Ψtrunc m) hp
  let fromCompletion :
      AdicCompletion (MvPolynomial.idealOfVars (Fin d) R) (MvPolynomial (Fin d) R) →ₐ[R]
        AdicCompletion (RingHom.ker σ) S :=
    AdicCompletion.liftAlgHom (RingHom.ker σ) fromCompletionFamily hfromCompletionFamily
  -- Compare the two lifted completion maps quotientwise at every stage.
  refine AlgEquiv.ofAlgHom toCompletion fromCompletion ?_ ?_
  · apply AlgHom.ext
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    -- After evaluating at stage `n`, the composite reduces to `σtrunc n ≫ Ψtrunc n`.
    calc
      AdicCompletion.evalₐ (MvPolynomial.idealOfVars (Fin d) R) n
          (toCompletion (fromCompletion x)) =
            toCompletionFamily n (fromCompletion x) := by
              simpa [toCompletion] using
                (AdicCompletion.evalₐ_liftAlgHom (MvPolynomial.idealOfVars (Fin d) R)
                  toCompletionFamily htoCompletionFamily n (fromCompletion x))
      _ = σtrunc n (fromCompletionFamily n x) := by
            exact congrArg (σtrunc n) <| by
              simpa [fromCompletion] using
                (AdicCompletion.evalₐ_liftAlgHom (RingHom.ker σ)
                  fromCompletionFamily hfromCompletionFamily n x)
      _ = σtrunc n
          (Ψtrunc n (AdicCompletion.evalₐ (MvPolynomial.idealOfVars (Fin d) R) n x)) := by rfl
      _ = AdicCompletion.evalₐ (MvPolynomial.idealOfVars (Fin d) R) n x := by
            simpa using
              AlgHom.congr_fun (hσΨ n)
                (AdicCompletion.evalₐ (MvPolynomial.idealOfVars (Fin d) R) n x)
  · apply AlgHom.ext
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    -- The opposite composite reduces to `Ψtrunc n ≫ σtrunc n` on the `n`th quotient.
    calc
      AdicCompletion.evalₐ (RingHom.ker σ) n (fromCompletion (toCompletion x)) =
          fromCompletionFamily n (toCompletion x) := by
            simpa [fromCompletion] using
              (AdicCompletion.evalₐ_liftAlgHom (RingHom.ker σ)
                fromCompletionFamily hfromCompletionFamily n (toCompletion x))
      _ = Ψtrunc n (toCompletionFamily n x) := by
            exact congrArg (Ψtrunc n) <| by
              simpa [toCompletion] using
                (AdicCompletion.evalₐ_liftAlgHom (MvPolynomial.idealOfVars (Fin d) R)
                  toCompletionFamily htoCompletionFamily n x)
      _ = Ψtrunc n (σtrunc n (AdicCompletion.evalₐ (RingHom.ker σ) n x)) := by rfl
      _ = AdicCompletion.evalₐ (RingHom.ker σ) n x := by
            simpa using
              AlgHom.congr_fun (hΨσ n) (AdicCompletion.evalₐ (RingHom.ker σ) n x)

/-- Helper for Lemma 10.139.4: once the source-faithful induction supplies compatible quotient
inverses, the final power-series presentation follows by passing to adic completions. -/
private theorem completion_equiv_of_truncation_inverses {d : ℕ}
    (Ψtrunc : (n : ℕ) →
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n →ₐ[R]
        S ⧸ (RingHom.ker σ) ^ n)
    (hΨtrunc :
      ∀ {m n : ℕ} (hmn : m ≤ n),
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp (Ψtrunc n) =
          (Ψtrunc m).comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)))
    (σtrunc : (n : ℕ) →
      S ⧸ (RingHom.ker σ) ^ n →ₐ[R]
        MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n)
    (hσtrunc :
      ∀ {m n : ℕ} (hmn : m ≤ n),
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp (σtrunc n) =
          (σtrunc m).comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)))
    (hσΨ : ∀ n,
      (σtrunc n).comp (Ψtrunc n) =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n))
    (hΨσ : ∀ n, (Ψtrunc n).comp (σtrunc n) = AlgHom.id R (S ⧸ (RingHom.ker σ) ^ n)) :
    Nonempty ((AdicCompletion (RingHom.ker σ) S) ≃ₐ[R] MvPowerSeries (Fin d) R) := by
  let eCompletion :=
    completion_algEquiv_of_truncation_inverses (R := R) (S := S) (σ := σ)
      Ψtrunc hΨtrunc σtrunc hσtrunc hσΨ hΨσ
  -- Compose the completion comparison with the canonical power-series/completion equivalence.
  exact ⟨eCompletion.trans
    ((MvPowerSeries.toAdicCompletionAlgEquiv (Fin d) R).symm.restrictScalars R)⟩

/-- Helper for Lemma 10.139.4: if `Ψ_n` already has a two-sided inverse, then `Ψ_(n + 1)` is
surjective. The source proof lifts a preimage modulo `I^n` and absorbs the remaining transition
error with nilpotent Nakayama. -/
private theorem cotangent_lift_truncated_map_surjective_of_prev_inverse {d n : ℕ}
    (hn : 2 ≤ n)
    (f : Fin d → RingHom.ker σ)
    (σn : S ⧸ (RingHom.ker σ) ^ n →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n)
    (hσΨ :
      σn.comp (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n) =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n))
    (hΨσ :
      (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n).comp σn =
        AlgHom.id R (S ⧸ (RingHom.ker σ) ^ n)) :
    Function.Surjective (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f (n + 1)) := by
  -- TODO: lift a preimage modulo `I^n`, show the residual error lies in the nilpotent transition
  -- ideal, and finish by Nakayama on the quotient module.
  sorry

/-- Helper for Lemma 10.139.4: once the verified stage-`1` and stage-`2` inverse data are fixed,
the remaining source-faithful local task is to correct the formally-smooth lift at stage
`n + 1` by a quotient automorphism of `P / J^(n + 1)`. -/
private theorem exists_successor_truncation_inverse {d n : ℕ}
    (hn : 2 ≤ n)
    (f : Fin d → RingHom.ker σ)
    (σn : S ⧸ (RingHom.ker σ) ^ n →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n)
    (hσΨ :
      σn.comp (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n) =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n))
    (hΨσ :
      (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n).comp σn =
        AlgHom.id R (S ⧸ (RingHom.ker σ) ^ n)) :
    ∃ σsucc : S ⧸ (RingHom.ker σ) ^ (n + 1) →ₐ[R]
        MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1),
      σsucc.comp (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f (n + 1)) =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)) ∧
      (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f (n + 1)).comp σsucc =
        AlgHom.id R (S ⧸ (RingHom.ker σ) ^ (n + 1)) := by
  let Ψsucc :=
    cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f (n + 1)
  let qJ :
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) →ₐ[R]
        MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n :=
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ n))
  let qI :
      S ⧸ (RingHom.ker σ) ^ (n + 1) →ₐ[R] S ⧸ (RingHom.ker σ) ^ n :=
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ n))
  obtain ⟨τbar, hτbar⟩ :=
    formally_smooth_lift_of_truncation_inverse_descends
      (R := R) (S := S) (σ := σ) (hσ := hσ)
      (d := d) (n := n) hn f σn hσΨ hΨσ
  let α :
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) →ₐ[R]
        MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) :=
    τbar.comp Ψsucc
  have hα : qJ.comp α = qJ := by
    ext x
    -- Reduce the correction problem to the stage-`n` inverse through the descended lift `τbar`.
    calc
      qJ (α x) = (σn.comp qI) (Ψsucc x) := by
        exact congrArg (fun β ↦ β (Ψsucc x)) hτbar
      _ =
        σn ((cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n) (qJ x)) := by
          exact congrArg σn <|
            AlgHom.congr_fun
              (cotangent_lift_truncated_map_compatible
                (R := R) (S := S) (σ := σ) f (m := n) (n := n + 1) (Nat.le_succ n))
              x
      _ = qJ x := by
        exact AlgHom.congr_fun hσΨ (qJ x)
  have hα_factorPow :
      (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)).comp α =
        Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n) := by
    -- The correction API is stated with `factorPow`; this is the same reduction map as `qJ`.
    change qJ.toRingHom.comp α.toRingHom = qJ.toRingHom
    exact congrArg AlgHom.toRingHom hα
  have hn0 : 0 < n := lt_of_lt_of_le (by simp) hn
  let β :
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) →ₐ[R]
        MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) :=
    truncation_selfmap_correction
      (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) hn0 α hα_factorPow
  have hβ :
      (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)).comp β =
        Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n) :=
    truncation_selfmap_correction_factorPow_comp
      (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) hn0 α hα_factorPow
  have hδ :
      ∀ i : Fin d,
        α (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
            (MvPolynomial.X i)) -
            Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
              (MvPolynomial.X i) ∈
          Ideal.map
            (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)))
            (MvPolynomial.idealOfVars (Fin d) R) := by
    intro i
    exact truncation_selfmap_variable_error_mem_idealOfVars_image
      (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) hn0 α hα_factorPow i
  have hΨsucc_surj : Function.Surjective Ψsucc :=
    cotangent_lift_truncated_map_surjective_of_prev_inverse
      (R := R) (S := S) (σ := σ) (hσ := hσ)
      (d := d) (n := n) hn f σn hσΨ hΨσ
  -- Route correction: the stalled variable-by-variable cancellation was too weak. The source proof
  -- needs the stronger invariant that `β` and `α` fix the whole transition piece `J^n / J^(n+1)`.
  -- TODO: prove `β.comp α = id` by showing both maps fix every class from `J^n / J^(n + 1)`,
  -- then define `σsucc := β.comp τbar` and use `hΨsucc_surj` to upgrade the left inverse.
  sorry

/-- Helper for Lemma 10.139.4: once the stagewise two-sided inverses are available, compatibility
of the inverse family follows formally from the already-known compatibility of `Ψtrunc`. -/
private theorem truncation_inverses_compatible_of_two_sided {d : ℕ}
    (f : Fin d → RingHom.ker σ)
    (σtrunc : (n : ℕ) →
      S ⧸ (RingHom.ker σ) ^ n →ₐ[R]
        MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n)
    (hσΨ : ∀ n,
      (σtrunc n).comp (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n) =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n))
    (hΨσ : ∀ n,
      (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n).comp (σtrunc n) =
        AlgHom.id R (S ⧸ (RingHom.ker σ) ^ n)) :
    ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp (σtrunc n) =
        (σtrunc m).comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)) := by
  intro m n hmn
  ext x
  -- Rewrite both sides through `Ψtrunc m`; its left inverse `σtrunc m` then reduces the
  -- compatibility check to the already-known compatibility of the forward truncation maps.
  calc
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)) ((σtrunc n) x) =
      (σtrunc m)
        ((cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f m)
          ((Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)) ((σtrunc n) x))) := by
            symm
            exact AlgHom.congr_fun (hσΨ m)
              ((Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)) ((σtrunc n) x))
    _ = (σtrunc m)
        ((Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn))
          ((cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n) ((σtrunc n) x))) := by
            congr 1
            exact (AlgHom.congr_fun
              (cotangent_lift_truncated_map_compatible
                (R := R) (S := S) (σ := σ) f (m := m) (n := n) hmn)
              ((σtrunc n) x)).symm
    _ = (σtrunc m)
        ((Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)) x) := by
            congr 1
            exact congrArg
              (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn))
              (AlgHom.congr_fun (hΨσ n) x)

/-- Helper for Lemma 10.139.4: once the verified stage-`1` and stage-`2` inverse data are fixed,
the remaining source-faithful task is to extend them to a compatible inverse family on all
truncations. -/
private theorem exists_truncation_inverse_family {d : ℕ}
    (f : Fin d → RingHom.ker σ)
    (σ1 :
      S ⧸ (RingHom.ker σ) ^ 1 →ₐ[R]
        MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 1)
    (hσ1Ψ :
      σ1.comp (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f 1) =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 1))
    (hΨ1σ :
      (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f 1).comp σ1 =
        AlgHom.id R (S ⧸ (RingHom.ker σ) ^ 1))
    (σ2 :
      S ⧸ (RingHom.ker σ) ^ 2 →ₐ[R]
        MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 2)
    (hσ2 :
      σ2.comp (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f 2) =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 2) ∧
      (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f 2).comp σ2 =
        AlgHom.id R (S ⧸ (RingHom.ker σ) ^ 2)) :
    ∃ σtrunc : (n : ℕ) →
        S ⧸ (RingHom.ker σ) ^ n →ₐ[R]
          MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n,
      (∀ {m n : ℕ} (hmn : m ≤ n),
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp (σtrunc n) =
          (σtrunc m).comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn))) ∧
      (∀ n,
        (σtrunc n).comp (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n) =
          AlgHom.id R
            (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n)) ∧
      (∀ n,
        (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n).comp (σtrunc n) =
          AlgHom.id R (S ⧸ (RingHom.ker σ) ^ n)) := by
  classical
  have hstage :
      ∀ k : ℕ,
        ∃ σk : S ⧸ (RingHom.ker σ) ^ (k + 2) →ₐ[R]
            MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (k + 2),
          (σk.comp (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f (k + 2)) =
              AlgHom.id R
                (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (k + 2))) ∧
            ((cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f (k + 2)).comp σk =
              AlgHom.id R (S ⧸ (RingHom.ker σ) ^ (k + 2))) := by
    intro k
    induction k with
    | zero =>
        exact ⟨σ2, hσ2⟩
    | succ k ih =>
        rcases ih with ⟨σk, hσk⟩
        exact exists_successor_truncation_inverse
          (R := R) (S := S) (σ := σ) (hσ := hσ)
          (d := d) (n := k + 2) (by omega) f σk hσk.1 hσk.2
  let σtrunc : (n : ℕ) →
      S ⧸ (RingHom.ker σ) ^ n →ₐ[R]
        MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n
    | 0 => by
        letI :
            Subsingleton
              (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 0) := by
          simp
        exact default
    | 1 => σ1
    | k + 2 => Classical.choose (hstage k)
  have hσΨtrunc : ∀ n,
      (σtrunc n).comp (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n) =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n) := by
    intro n
    cases n with
    | zero =>
        letI :
            Subsingleton
              (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 0) := by
          simpa using
            (inferInstance :
              Subsingleton (MvPolynomial (Fin d) R ⧸ (⊤ : Ideal (MvPolynomial (Fin d) R))))
        ext x
        exact Subsingleton.elim _ _
    | succ n =>
        cases n with
        | zero =>
            simpa [σtrunc] using hσ1Ψ
        | succ k =>
            simpa [σtrunc] using (Classical.choose_spec (hstage k)).1
  have hΨσtrunc : ∀ n,
      (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n).comp (σtrunc n) =
        AlgHom.id R (S ⧸ (RingHom.ker σ) ^ n) := by
    intro n
    cases n with
    | zero =>
        letI : Subsingleton (S ⧸ (RingHom.ker σ) ^ 0) := by
          simpa using (inferInstance : Subsingleton (S ⧸ (⊤ : Ideal S)))
        ext x
        exact Subsingleton.elim _ _
    | succ n =>
        cases n with
        | zero =>
            simpa [σtrunc] using hΨ1σ
        | succ k =>
            simpa [σtrunc] using (Classical.choose_spec (hstage k)).2
  have hσtrunc :
      ∀ {m n : ℕ} (hmn : m ≤ n),
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp (σtrunc n) =
          (σtrunc m).comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)) :=
    truncation_inverses_compatible_of_two_sided
      (R := R) (S := S) (σ := σ) (hσ := hσ) f σtrunc hσΨtrunc hΨσtrunc
  -- Route correction: keep the stagewise construction and the compatibility proof separate.
  -- The only remaining substantive source-faithful blocker is the successor-step correction
  -- isolated in `exists_successor_truncation_inverse`.
  exact ⟨σtrunc, hσtrunc, hσΨtrunc, hΨσtrunc⟩

-- Proof sketch: choose a finite basis of `(RingHom.ker σ).Cotangent`, lift basis
-- vectors to elements of `ker σ`, and use formal smoothness of `S` over `R` to build compatible
-- inverses modulo successive powers of `ker σ`; the induced map from a multivariable formal power
-- series ring is then an `R`-algebra isomorphism onto the `ker σ`-adic completion.
/-- If the conormal module attached to a smooth retraction is free over `R`, then the
`ker σ`-adic completion of `S` is isomorphic, as an `R`-algebra, to a formal power series ring in
finitely many variables over `R`. -/
theorem smooth_section_adicCompletion_exists_algEquiv_mvPowerSeries
    (hfree : Module.Free R (RingHom.ker σ).Cotangent) :
    ∃ d : ℕ,
      Nonempty ((AdicCompletion (RingHom.ker σ) S) ≃ₐ[R] MvPowerSeries (Fin d) R) := by
  -- Route correction: the source proof first fixes a finite basis of `I/I²` and lifts it to
  -- elements of `I`; we record exactly that data before attempting any quotient-by-powers step.
  obtain ⟨d, b, f, hf⟩ :=
    exists_cotangent_fin_basis_and_lifts (R := R) (S := S) (σ := σ) hσ hfree
  let Ψ : MvPolynomial (Fin d) R →ₐ[R] S :=
    cotangent_lift_polynomial_map (R := R) (S := S) (σ := σ) f
  let Ψtrunc : (n : ℕ) →
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n →ₐ[R]
        S ⧸ (RingHom.ker σ) ^ n :=
    cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f
  have hΨtrunc :
      ∀ {m n : ℕ} (hmn : m ≤ n),
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp (Ψtrunc n) =
          (Ψtrunc m).comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)) := by
    intro m n hmn
    exact cotangent_lift_truncated_map_compatible
      (R := R) (S := S) (σ := σ) f hmn
  let σ2 :
      S ⧸ (RingHom.ker σ) ^ 2 →ₐ[R]
        MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 2 :=
    trunc_two_inverse_via_trivSqZero_models (R := R) (S := S) (σ := σ) hσ b
  have hσ2 :
      σ2.comp (Ψtrunc 2) =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 2) ∧
      (Ψtrunc 2).comp σ2 = AlgHom.id R (S ⧸ (RingHom.ker σ) ^ 2) := by
    -- The explicit level-`2` inverse is the formal base case for the textbook induction.
    simpa [σ2] using
      trunc_two_inverse_via_trivSqZero_models_spec
        (R := R) (S := S) (σ := σ) hσ b f hf
  let σ1 :
      S ⧸ (RingHom.ker σ) ^ 1 →ₐ[R]
        MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 1 :=
    smooth_section_stageOne_inverse_powOne (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d)
  have hσ1Ψ :
      σ1.comp (Ψtrunc 1) =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 1) := by
    -- The transported stage-`1` inverse gives the forward base case of the induction.
    simpa [σ1, Ψtrunc] using
      smooth_section_stageOne_inverse_powOne_spec
        (R := R) (S := S) (σ := σ) hσ (d := d) f
  have hΨ1σ :
      (Ψtrunc 1).comp σ1 = AlgHom.id R (S ⧸ (RingHom.ker σ) ^ 1) := by
    -- The same transported stage-`1` inverse also closes the reverse base case.
    simpa [σ1, Ψtrunc] using
      smooth_section_stageOne_inverse_powOne_spec_symm
        (R := R) (S := S) (σ := σ) hσ (d := d) f
  obtain ⟨σtrunc, hσtrunc, hσΨ, hΨσ⟩ :=
    exists_truncation_inverse_family (R := R) (S := S) (σ := σ) (hσ := hσ)
      f σ1 hσ1Ψ hΨ1σ σ2 hσ2
  -- Once the quotient-level inverse family is available, the completion comparison theorem closes
  -- the source proof immediately.
  exact ⟨d,
    completion_equiv_of_truncation_inverses (R := R) (S := S) (σ := σ) (hσ := hσ)
      Ψtrunc hΨtrunc σtrunc hσtrunc hσΨ hΨσ⟩

end SmoothSection

end
