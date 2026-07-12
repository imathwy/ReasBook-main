import Mathlib
import StacksProject_2024.Chap10.Definition_10_17_1
import StacksProject_2024.Chap10.Lemma_10_137_2
import StacksProject_2024.Chap10.Lemma_10_143_9
import StacksProject_2024.Chap15.PrincipalIdeal
import StacksProject_2024.Chap15.Lemma_15_32_3

-- Declarations for this item will be appended below by the statement pipeline.

open MvPolynomial PrimeSpectrum

universe u

noncomputable section

namespace Algebra

/-
Domain-style sampling for Example 16.2.6:
- primary domain: commutative algebra and affine smooth loci for finitely presented quotient maps;
- sampled owner declarations:
  `Algebra.smoothLocus`,
  `Algebra.basicOpen_subset_smoothLocus_iff_smooth`,
  `Algebra.isOpen_smoothLocus`,
  `FinitePresentation.quotient`,
  `Algebra.singularIdeal`;
- best owner abstraction: `Algebra.smoothLocus` for the quotient map `R → A`;
- primitive data: the public source-facing ring and element names
  `smoothCounterexampleR k`,
  `smoothCounterexampleA k`,
  `smoothCounterexampleX k`,
  `smoothCounterexampleY k i`;
- derived API: the identification of `smoothLocus R A` with `⋃ i, D(yᵢ)` and the resulting
  non-compactness.
- minimal coefficient assumptions from the sampled owners: `CommRing k` for the quotient
  presentation and smooth-locus description, with `Nontrivial k` needed only for the
  non-compactness statement.

Source/core/bridge triage:
- source-facing: the two public theorems describing the smooth locus and its non-compactness;
- core/canonical: `Algebra.smoothLocus`, `PrimeSpectrum.basicOpen`, and
  `FinitePresentation.quotient`;
- bridge/view: the internal `Option ℕ+` presentation, with `none` representing `x` and `some i`
  representing `yᵢ`, together with the private ambient polynomial ring, relation ideal, and
  source-ring lift of `yᵢ`. This keeps the source indexing `y₁, y₂, …` explicit rather than
  silently reindexing by all of `ℕ`, while the public theorem surface is expressed through the
  source-facing owners listed above.
-/

private abbrev smoothCounterexamplePolynomialRing (k : Type u) [CommRing k] :=
  MvPolynomial (Option ℕ+) k

/-- The polynomial variable `x` in the ambient ring of Example 16.2.6. -/
private abbrev smoothCounterexampleXPolynomial (k : Type u) [CommRing k] :
    smoothCounterexamplePolynomialRing k :=
  X (none : Option ℕ+)

/-- The polynomial variable `yᵢ` in the ambient ring of Example 16.2.6. -/
private abbrev smoothCounterexampleYPolynomial (k : Type u) [CommRing k] (i : ℕ+) :
    smoothCounterexamplePolynomialRing k :=
  X (some i)

private abbrev smoothCounterexampleRelationIdeal (k : Type u) [CommRing k] :
    Ideal (smoothCounterexamplePolynomialRing k) :=
  Ideal.span (Set.range fun i : ℕ+ ↦
    smoothCounterexampleXPolynomial k * smoothCounterexampleYPolynomial k i)

/-- The source ring
`R = k[x, y₁, y₂, y₃, ...] / (x yᵢ \mid i \ge 1)` from Example 16.2.6. -/
abbrev smoothCounterexampleR (k : Type u) [CommRing k] : Type u :=
  smoothCounterexamplePolynomialRing k ⧸ smoothCounterexampleRelationIdeal k

/-- The class of `x` in the source ring `R` of Example 16.2.6. -/
def smoothCounterexampleX (k : Type u) [CommRing k] : smoothCounterexampleR k :=
  Ideal.Quotient.mk (smoothCounterexampleRelationIdeal k) (smoothCounterexampleXPolynomial k)

/-- The class of `yᵢ` in the source ring `R` of Example 16.2.6. -/
private def smoothCounterexampleYInR (k : Type u) [CommRing k] (i : ℕ+) :
    smoothCounterexampleR k :=
  Ideal.Quotient.mk (smoothCounterexampleRelationIdeal k) (smoothCounterexampleYPolynomial k i)

/-- The target ring `A = R / (x)` from Example 16.2.6. -/
abbrev smoothCounterexampleA (k : Type u) [CommRing k] : Type u :=
  smoothCounterexampleR k ⧸ principalIdeal (smoothCounterexampleX k)

/-- The class of `yᵢ` in the target ring `A` of Example 16.2.6. -/
def smoothCounterexampleY (k : Type u) [CommRing k] (i : ℕ+) :
    smoothCounterexampleA k :=
  Ideal.Quotient.mk
    (principalIdeal (smoothCounterexampleX k))
    (smoothCounterexampleYInR k i)

/-- Helper for Example 16.2.6: evaluate the ambient polynomial ring at `x = 0`, keeping the
variables `yᵢ` unchanged. -/
private def smoothCounterexampleAmbientToYPolynomial (k : Type u) [CommRing k] :
    smoothCounterexamplePolynomialRing k →+* MvPolynomial ℕ+ k :=
  (Polynomial.eval₂RingHom (RingHom.id _) 0).comp
    (MvPolynomial.optionEquivLeft k ℕ+).toRingHom

/-- Helper for Example 16.2.6: the polynomial ring on the `yᵢ` maps to `A` by sending `X i` to
the class of `yᵢ`. -/
private def smoothCounterexampleYPolynomialToA (k : Type u) [CommRing k] :
    MvPolynomial ℕ+ k →ₐ[k] smoothCounterexampleA k :=
  MvPolynomial.eval₂AlgHom k fun i ↦ smoothCounterexampleY k i

/-- Helper for Example 16.2.6: the quotient map to `A` agrees with first setting `x = 0` and then
mapping the remaining `yᵢ`-polynomial to `A`. -/
private lemma smoothCounterexample_quotient_toA_eq_yPolynomial_map
    (k : Type u) [CommRing k] :
    ((Ideal.Quotient.mk (principalIdeal (smoothCounterexampleX k))).comp
        (Ideal.Quotient.mk (smoothCounterexampleRelationIdeal k))) =
      (smoothCounterexampleYPolynomialToA k).toRingHom.comp
        (smoothCounterexampleAmbientToYPolynomial k) := by
  -- Compare the two ambient maps by their values on coefficients.
  apply MvPolynomial.ringHom_ext
  · intro r
    calc
      ((Ideal.Quotient.mk (principalIdeal (smoothCounterexampleX k))).comp
            (Ideal.Quotient.mk (smoothCounterexampleRelationIdeal k))) (C r) =
          Ideal.Quotient.mk (principalIdeal (smoothCounterexampleX k))
            (Ideal.Quotient.mk (smoothCounterexampleRelationIdeal k) (C r)) := rfl
      _ = (algebraMap k (smoothCounterexampleA k)) r := by
            rfl
      _ =
          ((smoothCounterexampleYPolynomialToA k).toRingHom.comp
              (smoothCounterexampleAmbientToYPolynomial k)) (C r) := by
            simp [smoothCounterexampleAmbientToYPolynomial, smoothCounterexampleYPolynomialToA]
  · intro i
    cases i with
    | none =>
        -- Both maps kill the `x`-variable: the left map quotients by `(x)`, the right map sets
        -- `x = 0` before evaluating the remaining variables.
        calc
          ((Ideal.Quotient.mk (principalIdeal (smoothCounterexampleX k))).comp
                (Ideal.Quotient.mk (smoothCounterexampleRelationIdeal k))) (X none) =
              Ideal.Quotient.mk (principalIdeal (smoothCounterexampleX k))
                (smoothCounterexampleX k) := rfl
          _ = 0 := by
                exact Ideal.Quotient.eq_zero_iff_mem.mpr <|
                  Ideal.mem_span_singleton_self (smoothCounterexampleX k)
          _ =
              ((smoothCounterexampleYPolynomialToA k).toRingHom.comp
                  (smoothCounterexampleAmbientToYPolynomial k)) (X none) := by
                simp [smoothCounterexampleAmbientToYPolynomial, smoothCounterexampleYPolynomialToA]
    | some i =>
        -- Each `yᵢ` survives both quotient presentations unchanged.
        simp [smoothCounterexampleAmbientToYPolynomial, smoothCounterexampleYPolynomialToA,
          smoothCounterexampleY, smoothCounterexampleYInR]

/-- Helper for Example 16.2.6: the defining relations force `x yᵢ = 0` in `R`. -/
private lemma smoothCounterexample_x_mul_y_eq_zero
    (k : Type u) [CommRing k] (i : ℕ+) :
    smoothCounterexampleX k * smoothCounterexampleYInR k i = 0 := by
  -- This is exactly one of the ambient generators of the relation ideal.
  change Ideal.Quotient.mk (smoothCounterexampleRelationIdeal k)
      (smoothCounterexampleXPolynomial k * smoothCounterexampleYPolynomial k i) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr <|
    Ideal.subset_span <| by
      refine ⟨i, rfl⟩

/-- Helper for Example 16.2.6: multiplication by the polynomial variable `X` is injective. -/
private lemma polynomial_eq_zero_of_mul_X_eq_zero
    {S : Type*} [Semiring S] (F : Polynomial S)
    (hF : F * Polynomial.X = 0) :
    F = 0 := by
  -- Compare coefficients after shifting degrees by one.
  ext n
  simpa [hF] using (Polynomial.coeff_mul_X F n).symm

/-- Helper for Example 16.2.6: if `F * X` lies in the transported relation ideal, then the
constant coefficient of `F` already lies in the ideal generated by the variables `yᵢ`. -/
private lemma smoothCounterexample_constantCoeff_mem_span_y_of_mul_X_mem_relation
    (k : Type u) [CommRing k] (F : Polynomial (MvPolynomial ℕ+ k))
    (hF : F * Polynomial.X ∈
      Ideal.span (Set.range fun i : ℕ+ ↦
        Polynomial.X * Polynomial.C (MvPolynomial.X i))) :
    F.coeff 0 ∈ Ideal.span (Set.range (MvPolynomial.X : ℕ+ → MvPolynomial ℕ+ k)) := by
  let Iy : Ideal (MvPolynomial ℕ+ k) :=
    Ideal.span (Set.range (MvPolynomial.X : ℕ+ → MvPolynomial ℕ+ k))
  let φ : MvPolynomial ℕ+ k →+* (MvPolynomial ℕ+ k ⧸ Iy) := Ideal.Quotient.mk Iy
  have hvar_zero (i : ℕ+) : φ (MvPolynomial.X i) = 0 := by
    -- Each generator `X i` vanishes in the quotient by the `y`-span.
    exact Ideal.Quotient.eq_zero_iff_mem.mpr <|
      Ideal.subset_span <| by
        refine ⟨i, rfl⟩
  have hrelation_zero :
      Ideal.span (Set.range fun i : ℕ+ ↦
        Polynomial.X * Polynomial.C (MvPolynomial.X i)) ≤
        RingHom.ker (Polynomial.mapRingHom φ) := by
    -- After quotienting by the `y`-span, every relation generator `X * C (X i)` becomes zero.
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    show (Polynomial.mapRingHom φ) (Polynomial.X * Polynomial.C (MvPolynomial.X i)) = 0
    simp [φ, hvar_zero i]
  have hmap_mul_zero : (F.map φ) * Polynomial.X = 0 := by
    -- Map the ambient relation membership to the polynomial ring over the quotient.
    have hmap_mul_zero' : (Polynomial.mapRingHom φ) (F * Polynomial.X) = 0 :=
      hrelation_zero hF
    simpa only [Polynomial.coe_mapRingHom, Polynomial.map_mul, Polynomial.map_X] using
      hmap_mul_zero'
  have hmap_zero : F.map φ = 0 :=
    polynomial_eq_zero_of_mul_X_eq_zero (F.map φ) hmap_mul_zero
  have hcoeff_zero : φ (F.coeff 0) = 0 := by
    -- Read off the constant coefficient after the injectivity step.
    simpa [Polynomial.coeff_map, φ] using
      congrArg (fun p : Polynomial (MvPolynomial ℕ+ k ⧸ Iy) => p.coeff 0) hmap_zero
  -- Route correction: isolate the coefficient bridge before descending back to the quotient `A`.
  exact Ideal.Quotient.eq_zero_iff_mem.mp hcoeff_zero

/-- Helper for Example 16.2.6: transporting the relation ideal through
`MvPolynomial.optionEquivLeft` turns the generators `x * yᵢ` into the polynomial generators
`X * C(X i)`. -/
private lemma smoothCounterexample_optionEquivLeft_map_relationIdeal
    (k : Type u) [CommRing k] :
    Ideal.map ((MvPolynomial.optionEquivLeft k ℕ+).toRingHom)
        (smoothCounterexampleRelationIdeal k) =
      Ideal.span (Set.range fun i : ℕ+ ↦
        Polynomial.X * Polynomial.C (MvPolynomial.X i)) := by
  -- Transport the whole span at once so the main proof can rewrite relation membership canonically.
  rw [smoothCounterexampleRelationIdeal, Ideal.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨f, ⟨i, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    change Polynomial.X * Polynomial.C (MvPolynomial.X i) =
      ((MvPolynomial.optionEquivLeft k ℕ+).toRingHom)
        (smoothCounterexampleXPolynomial k * smoothCounterexampleYPolynomial k i)
    rw [RingHom.map_mul]
    simp [smoothCounterexampleXPolynomial, smoothCounterexampleYPolynomial]
  · rintro ⟨i, rfl⟩
    refine ⟨smoothCounterexampleXPolynomial k * smoothCounterexampleYPolynomial k i, ?_, ?_⟩
    · exact ⟨i, rfl⟩
    · change
        ((MvPolynomial.optionEquivLeft k ℕ+).toRingHom)
          (smoothCounterexampleXPolynomial k * smoothCounterexampleYPolynomial k i) =
            Polynomial.X * Polynomial.C (MvPolynomial.X i)
      rw [RingHom.map_mul]
      simp [smoothCounterexampleXPolynomial, smoothCounterexampleYPolynomial]

/-- Helper for Example 16.2.6: setting `x = 0` in the ambient presentation reads off the constant
coefficient after `MvPolynomial.optionEquivLeft`. -/
private lemma smoothCounterexample_ambientToYPolynomial_eq_coeff_zero
    (k : Type u) [CommRing k] (f : smoothCounterexamplePolynomialRing k) :
    smoothCounterexampleAmbientToYPolynomial k f =
      (MvPolynomial.optionEquivLeft k ℕ+ f).coeff 0 := by
  -- Evaluate the transported polynomial at `0`; for a polynomial in `X`, this is the constant
  -- coefficient.
  rw [smoothCounterexampleAmbientToYPolynomial]
  simpa [RingHom.comp_apply] using
    (Polynomial.eval₂_at_zero (f := RingHom.id (MvPolynomial ℕ+ k))
      (p := MvPolynomial.optionEquivLeft k ℕ+ f))

/-- Helper for Example 16.2.6: if an element of `R` kills `x`, then its image in `A` lies in the
ideal generated by the `yᵢ`. -/
private lemma smoothCounterexample_image_mem_span_y_of_mul_x_eq_zero
    (k : Type u) [CommRing k] (r : smoothCounterexampleR k)
    (hr : r * smoothCounterexampleX k = 0) :
    Ideal.Quotient.mk (principalIdeal (smoothCounterexampleX k)) r ∈
      Ideal.span (Set.range fun i : ℕ+ ↦ smoothCounterexampleY k i) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective r
  let Iy : Ideal (MvPolynomial ℕ+ k) :=
    Ideal.span (Set.range (MvPolynomial.X : ℕ+ → MvPolynomial ℕ+ k))
  -- Route correction: first transport the annihilator relation to the ambient polynomial ring in
  -- `X`, then read off the constant coefficient and descend back to `A`.
  change
    Ideal.Quotient.mk (principalIdeal (smoothCounterexampleX k))
        (Ideal.Quotient.mk (smoothCounterexampleRelationIdeal k) f) ∈
      Ideal.span (Set.range fun i : ℕ+ ↦ smoothCounterexampleY k i)
  change
    Ideal.Quotient.mk (smoothCounterexampleRelationIdeal k)
        (f * smoothCounterexampleXPolynomial k) = 0 at hr
  have hrelation :
      (MvPolynomial.optionEquivLeft k ℕ+) (f * smoothCounterexampleXPolynomial k) ∈
        Ideal.span (Set.range fun i : ℕ+ ↦
          Polynomial.X * Polynomial.C (MvPolynomial.X i)) := by
    have hmem :
        (MvPolynomial.optionEquivLeft k ℕ+) (f * smoothCounterexampleXPolynomial k) ∈
          Ideal.map ((MvPolynomial.optionEquivLeft k ℕ+).toRingHom)
            (smoothCounterexampleRelationIdeal k) := by
      exact Ideal.mem_map_of_mem ((MvPolynomial.optionEquivLeft k ℕ+).toRingHom)
        (Ideal.Quotient.eq_zero_iff_mem.mp hr)
    rw [smoothCounterexample_optionEquivLeft_map_relationIdeal k] at hmem
    simpa only [smoothCounterexampleXPolynomial, RingHom.map_mul,
      MvPolynomial.optionEquivLeft_X_none] using hmem
  have hrelation_mul :
      (MvPolynomial.optionEquivLeft k ℕ+ f) * Polynomial.X ∈
        Ideal.span (Set.range fun i : ℕ+ ↦
          Polynomial.X * Polynomial.C (MvPolynomial.X i)) := by
    simpa [smoothCounterexampleXPolynomial, RingHom.map_mul, MvPolynomial.optionEquivLeft_X_none]
      using hrelation
  have hcoeff :
      smoothCounterexampleAmbientToYPolynomial k f ∈ Iy := by
    rw [smoothCounterexample_ambientToYPolynomial_eq_coeff_zero]
    exact smoothCounterexample_constantCoeff_mem_span_y_of_mul_X_mem_relation k
      (MvPolynomial.optionEquivLeft k ℕ+ f) hrelation_mul
  have hmapIy :
      Ideal.map (smoothCounterexampleYPolynomialToA k).toRingHom Iy =
        Ideal.span (Set.range fun i : ℕ+ ↦ smoothCounterexampleY k i) := by
    -- Push the `y`-span through the evaluation map to `A`; the generators stay the classes `yᵢ`.
    change
      Ideal.map (smoothCounterexampleYPolynomialToA k).toRingHom
          (Ideal.span (Set.range (MvPolynomial.X : ℕ+ → MvPolynomial ℕ+ k))) =
        Ideal.span (Set.range fun i : ℕ+ ↦ smoothCounterexampleY k i)
    rw [Ideal.map_span]
    congr 1
    ext z
    constructor
    · rintro ⟨g, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, by simp [smoothCounterexampleYPolynomialToA]⟩
    · rintro ⟨i, rfl⟩
      refine ⟨MvPolynomial.X i, ?_, by simp [smoothCounterexampleYPolynomialToA]⟩
      exact ⟨i, rfl⟩
  have htoA :
      Ideal.Quotient.mk (principalIdeal (smoothCounterexampleX k))
          (Ideal.Quotient.mk (smoothCounterexampleRelationIdeal k) f) =
        (smoothCounterexampleYPolynomialToA k)
          (smoothCounterexampleAmbientToYPolynomial k f) := by
    -- Compare the two quotient presentations using the previously established ring-hom equality.
    simpa [RingHom.comp_apply] using
      congrArg
        (fun φ : smoothCounterexamplePolynomialRing k →+* smoothCounterexampleA k ↦ φ f)
        (smoothCounterexample_quotient_toA_eq_yPolynomial_map k)
  have himage :
      (smoothCounterexampleYPolynomialToA k) (smoothCounterexampleAmbientToYPolynomial k f) ∈
        Ideal.map (smoothCounterexampleYPolynomialToA k).toRingHom Iy := by
    exact Ideal.mem_map_of_mem (smoothCounterexampleYPolynomialToA k).toRingHom hcoeff
  rw [htoA, ← hmapIy]
  exact himage

/-- Helper for Example 16.2.6: if a prime of `A` contains every `yᵢ`, then the class of `x`
remains nonzero in the corresponding localization of `R`. -/
private lemma smoothCounterexample_x_nonzero_in_localization_of_forall_y_mem
    (k : Type u) [CommRing k] (q : PrimeSpectrum (smoothCounterexampleA k))
    (hqy : ∀ i : ℕ+, smoothCounterexampleY k i ∈ q.asIdeal) :
    algebraMap (smoothCounterexampleR k)
      (Localization.AtPrime (q.asIdeal.under (smoothCounterexampleR k)))
      (smoothCounterexampleX k) ≠ 0 := by
  intro hxzero
  obtain ⟨s, hs⟩ :=
    (IsLocalization.map_eq_zero_iff
      (q.asIdeal.under (smoothCounterexampleR k)).primeCompl
      (Localization.AtPrime (q.asIdeal.under (smoothCounterexampleR k)))
      (smoothCounterexampleX k)).mp hxzero
  have hs_image :
      Ideal.Quotient.mk (principalIdeal (smoothCounterexampleX k))
          (s : smoothCounterexampleR k) ∈
        Ideal.span (Set.range fun i : ℕ+ ↦ smoothCounterexampleY k i) := by
    -- The denominator kills `x`, so its image in `A` lands in the ideal generated by the `yᵢ`.
    exact smoothCounterexample_image_mem_span_y_of_mul_x_eq_zero k (s : smoothCounterexampleR k) hs
  have hspan_le :
      Ideal.span (Set.range fun i : ℕ+ ↦ smoothCounterexampleY k i) ≤ q.asIdeal := by
    -- Every generator `yᵢ` already lies in `q`, so the whole span does as well.
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hqy i
  have hsq_image :
      Ideal.Quotient.mk (principalIdeal (smoothCounterexampleX k))
          (s : smoothCounterexampleR k) ∈ q.asIdeal :=
    hspan_le hs_image
  have hsq :
      (s : smoothCounterexampleR k) ∈ q.asIdeal.under (smoothCounterexampleR k) := by
    -- Membership in the contracted prime is exactly membership of the quotient image in `q`.
    simpa [Ideal.under_def] using hsq_image
  exact s.2 hsq

open scoped PrimeSpectrum

/-- The quotient map `R → A = R / (x)` in Example 16.2.6 is finitely presented. -/
instance smoothCounterexampleFinitePresentation (k : Type u) [CommRing k] :
    FinitePresentation (smoothCounterexampleR k) (smoothCounterexampleA k) := by
  have hfp :
      FinitePresentation (smoothCounterexampleR k)
        ((smoothCounterexampleR k) ⧸ principalIdeal (smoothCounterexampleX k)) :=
    FinitePresentation.quotient (principalIdeal_fg (smoothCounterexampleX k))
  simpa [smoothCounterexampleA] using hfp

/-- Helper for Example 16.2.6: after inverting `yᵢ`, the class of `x` vanishes in the localized
source ring. -/
private lemma smoothCounterexample_x_zero_in_away_y
    (k : Type u) [CommRing k] (i : ℕ+) :
    algebraMap (smoothCounterexampleR k)
      (Localization.Away (smoothCounterexampleYInR k i))
      (smoothCounterexampleX k) = 0 := by
  let φ :
      smoothCounterexampleR k →+* Localization.Away (smoothCounterexampleYInR k i) :=
    algebraMap (smoothCounterexampleR k) (Localization.Away (smoothCounterexampleYInR k i))
  have hxy :
      φ (smoothCounterexampleX k) * φ (smoothCounterexampleYInR k i) = 0 := by
    -- First transport the defining relation `x * yᵢ = 0` into the away localization.
    rw [← map_mul, smoothCounterexample_x_mul_y_eq_zero]
    simp [φ]
  rcases
      (IsLocalization.Away.algebraMap_isUnit
        (S := Localization.Away (smoothCounterexampleYInR k i))
        (smoothCounterexampleYInR k i)) with
    ⟨u, hu⟩
  have hu_one :
      (↑u : Localization.Away (smoothCounterexampleYInR k i)) *
          (((u⁻¹ : Units (Localization.Away (smoothCounterexampleYInR k i))) :
            Localization.Away (smoothCounterexampleYInR k i))) = 1 := by
    simpa using u.mul_inv
  have hxu : φ (smoothCounterexampleX k) * ↑u = 0 := by
    -- Rewrite the localized `yᵢ` as the chosen unit before cancelling it.
    rw [← hu] at hxy
    exact hxy
  -- Route correction: cancel `yᵢ` only after passing to the away localization where it is a unit.
  calc
    φ (smoothCounterexampleX k) = φ (smoothCounterexampleX k) * 1 := by simp
    _ = φ (smoothCounterexampleX k) *
          ((↑u : Localization.Away (smoothCounterexampleYInR k i)) *
            (((u⁻¹ : Units (Localization.Away (smoothCounterexampleYInR k i))) :
              Localization.Away (smoothCounterexampleYInR k i)))) := by
          rw [hu_one.symm]
    _ = (φ (smoothCounterexampleX k) * ↑u) *
          (((u⁻¹ : Units (Localization.Away (smoothCounterexampleYInR k i))) :
            Localization.Away (smoothCounterexampleYInR k i))) := by
          rw [mul_assoc]
    _ = 0 := by simp [hxu]

/-- Helper for Example 16.2.6: the principal ideal `(x)` becomes zero after inverting `yᵢ`. -/
private lemma smoothCounterexample_principalIdeal_x_map_eq_bot_away_y
    (k : Type u) [CommRing k] (i : ℕ+) :
    Ideal.map
        (algebraMap (smoothCounterexampleR k)
          (Localization.Away (smoothCounterexampleYInR k i)))
        (principalIdeal (smoothCounterexampleX k)) = ⊥ := by
  -- Once `x` itself maps to zero, every multiple of `x` maps to zero as well.
  apply (Ideal.map_eq_bot_iff_le_ker _).2
  intro r hr
  rw [RingHom.mem_ker]
  rcases Ideal.mem_span_singleton.mp hr with ⟨a, rfl⟩
  rw [map_mul, smoothCounterexample_x_zero_in_away_y]
  simp

/-- Helper for Example 16.2.6: the source localized away from `yᵢ` is smooth over `R`. -/
private lemma smoothCounterexample_source_smooth_away_y
    (k : Type u) [CommRing k] (i : ℕ+) :
    Smooth (smoothCounterexampleR k)
      (Localization.Away (smoothCounterexampleYInR k i)) := by
  -- This is the canonical smoothness of an away localization of the source ring itself.
  simpa using
    (Smooth.of_isLocalization_Away (smoothCounterexampleYInR k i) :
      Smooth (smoothCounterexampleR k)
        (Localization.Away (smoothCounterexampleYInR k i)))

/-- Helper for Example 16.2.6: every element of the principal ideal `(x)` maps to zero in the
source localization away from `yᵢ`. -/
private lemma smoothCounterexample_principalIdeal_x_mapsToZero_away_y
    (k : Type u) [CommRing k] (i : ℕ+) :
    ∀ a ∈ principalIdeal (smoothCounterexampleX k),
      (Algebra.ofId (smoothCounterexampleR k)
        (Localization.Away (smoothCounterexampleYInR k i))) a = 0 := by
  intro a ha
  rcases Ideal.mem_span_singleton.mp ha with ⟨r, rfl⟩
  -- The quotient generator `x` is already zero after inverting `yᵢ`.
  change
    algebraMap (smoothCounterexampleR k)
        (Localization.Away (smoothCounterexampleYInR k i))
        (smoothCounterexampleX k * r) = 0
  rw [map_mul, smoothCounterexample_x_zero_in_away_y]
  simp

/-- Helper for Example 16.2.6: the quotient map `A → R[1 / yᵢ]` obtained by killing `x` before
localizing away from `yᵢ`. -/
private noncomputable abbrev smoothCounterexample_target_to_source_away_y
    (k : Type u) [CommRing k] (i : ℕ+) :
    smoothCounterexampleA k →ₐ[smoothCounterexampleR k]
      Localization.Away (smoothCounterexampleYInR k i) :=
  Ideal.Quotient.liftₐ (principalIdeal (smoothCounterexampleX k))
    (Algebra.ofId (smoothCounterexampleR k)
      (Localization.Away (smoothCounterexampleYInR k i)))
    (smoothCounterexample_principalIdeal_x_mapsToZero_away_y k i)

/-- Helper for Example 16.2.6: after inverting `yᵢ`, the quotient `A[1 / yᵢ]` identifies with the
source localization `R[1 / yᵢ]`. -/
private noncomputable def smoothCounterexample_targetAwayYAlgEquivSourceAwayY
    (k : Type u) [CommRing k] (i : ℕ+) :
    Localization.Away (smoothCounterexampleYInR k i) ≃ₐ[smoothCounterexampleR k]
      Localization.Away (smoothCounterexampleY k i) :=
  let eQuot := Classical.choice <|
    Ideal.quotient_localizationAway_algEquiv
      (R := smoothCounterexampleR k)
      (I := principalIdeal (smoothCounterexampleX k))
      (g := smoothCounterexampleYInR k i)
  let eBot :
      Localization.Away (smoothCounterexampleYInR k i) ≃ₐ[smoothCounterexampleR k]
        ((Localization.Away (smoothCounterexampleYInR k i)) ⧸
          Ideal.map
            (algebraMap (smoothCounterexampleR k)
              (Localization.Away (smoothCounterexampleYInR k i)))
            (principalIdeal (smoothCounterexampleX k))) :=
    -- Proof comment: once the extended ideal `(x)` becomes zero, the quotient-by-`(x)` chart is
    -- just the identity quotient-by-`⊥`.
    (AlgEquiv.quotientBot
      (smoothCounterexampleR k)
      (Localization.Away (smoothCounterexampleYInR k i))).symm.trans
      (Ideal.quotientEquivAlgOfEq
        (smoothCounterexampleR k)
        (smoothCounterexample_principalIdeal_x_map_eq_bot_away_y k i).symm)
  let eQuotR :
      ((Localization.Away (smoothCounterexampleYInR k i)) ⧸
          Ideal.map
            (algebraMap (smoothCounterexampleR k)
              (Localization.Away (smoothCounterexampleYInR k i)))
            (principalIdeal (smoothCounterexampleX k))) ≃ₐ[smoothCounterexampleR k]
        Localization.Away (smoothCounterexampleY k i) :=
    { toRingEquiv := eQuot.toRingEquiv
      commutes' := fun r ↦ by
        -- Proof comment: the quotient-localization equivalence is already `A`-linear, so it also
        -- respects the original `R`-algebra structure after precomposing with `R → A`.
        simpa [smoothCounterexampleA, RingHom.algebraMap_toAlgebra] using
          eQuot.commutes
            (Ideal.Quotient.mk (principalIdeal (smoothCounterexampleX k)) r) }
  -- Proof comment: compose the quotient-by-`⊥` collapse with the canonical quotient/localization
  -- comparison.
  eBot.trans eQuotR

/-- Helper for Example 16.2.6: the contracted source stalk attached to a prime of `A`. -/
private abbrev smoothCounterexampleSourceStalk
    (k : Type u) [CommRing k] (q : PrimeSpectrum (smoothCounterexampleA k)) :=
  Localization.AtPrime (q.asIdeal.under (smoothCounterexampleR k))

/-- Helper for Example 16.2.6: the target stalk attached to a prime of `A`. -/
private abbrev smoothCounterexampleTargetStalk
    (k : Type u) [CommRing k] (q : PrimeSpectrum (smoothCounterexampleA k)) :=
  Localization.AtPrime q.asIdeal

/-- Helper for Example 16.2.6: the quotient map `R → A` sends the prime complement of the
contracted source stalk exactly to the prime complement of the target stalk prime. -/
private lemma smoothCounterexample_stalkPrimeCompl_map_eq
    (k : Type u) [CommRing k] (q : PrimeSpectrum (smoothCounterexampleA k)) :
    Submonoid.map
        (Ideal.Quotient.mk (principalIdeal (smoothCounterexampleX k)))
        (q.asIdeal.under (smoothCounterexampleR k)).primeCompl =
      q.asIdeal.primeCompl := by
  ext a
  constructor
  · rintro ⟨r, hr, rfl⟩
    change Ideal.Quotient.mk (principalIdeal (smoothCounterexampleX k)) r ∉ q.asIdeal
    simpa [Ideal.under_def] using hr
  · intro ha
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨r, ?_, rfl⟩
    change Ideal.Quotient.mk (principalIdeal (smoothCounterexampleX k)) r ∉ q.asIdeal at ha
    simpa [Ideal.under_def] using ha

/-- Helper for Example 16.2.6: if the idempotent from the smooth-surjective local criterion is a
unit, then the localized source class of `x` must vanish, contradicting the earlier nonvanishing
lemma. -/
private lemma smoothCounterexample_false_of_unit_idempotent
    (k : Type u) [CommRing k] (q : PrimeSpectrum (smoothCounterexampleA k))
    {e : smoothCounterexampleSourceStalk k q}
    (he : IsIdempotentElem e) (heUnit : IsUnit e)
    (hAway : IsLocalization.Away e (smoothCounterexampleTargetStalk k q))
    (hx_nonzero :
      algebraMap (smoothCounterexampleR k)
        (smoothCounterexampleSourceStalk k q)
        (smoothCounterexampleX k) ≠ 0) :
    False := by
  let L := smoothCounterexampleSourceStalk k q
  let B := smoothCounterexampleTargetStalk k q
  letI : Algebra L B := by
    exact
      (Localization.localRingHom
        (q.asIdeal.under (smoothCounterexampleR k))
        q.asIdeal
        (Ideal.Quotient.mk (principalIdeal (smoothCounterexampleX k)))
        rfl).toAlgebra
  have heEqOne : e = 1 := (IsIdempotentElem.iff_eq_one_of_isUnit heUnit).mp he
  subst heEqOne
  let _ : IsLocalization.Away (1 : L) B := hAway
  let eUnits : L ≃ₐ[L] B := IsLocalization.atOne L B
  have hx_zero_target :
      algebraMap (smoothCounterexampleR k)
        B (smoothCounterexampleX k) = 0 := by
    -- Proof comment: `x` is zero already in the quotient ring `A`, so it stays zero after
    -- localizing at `q`.
    have hx_zero_in_A :
        (Ideal.Quotient.mk (principalIdeal (smoothCounterexampleX k))
          (smoothCounterexampleX k) : smoothCounterexampleA k) = 0 := by
      have hx_in_ideal :
        smoothCounterexampleX k ∈ principalIdeal (smoothCounterexampleX k) :=
        Ideal.mem_span_singleton_self (smoothCounterexampleX k)
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hx_in_ideal
    have hx_zero_target' :
        algebraMap (smoothCounterexampleA k) B
          (Ideal.Quotient.mk (principalIdeal (smoothCounterexampleX k))
            (smoothCounterexampleX k)) = 0 := by
      simpa using congrArg (algebraMap (smoothCounterexampleA k) B) hx_zero_in_A
    change algebraMap (smoothCounterexampleA k) B
      (Ideal.Quotient.mk (principalIdeal (smoothCounterexampleX k))
        (smoothCounterexampleX k)) = 0
    exact hx_zero_target'
  have hx_zero_local :
      algebraMap L B
        (algebraMap (smoothCounterexampleR k) L (smoothCounterexampleX k)) = 0 := by
    -- Proof comment: compare the two local expressions for `x` through the source-to-target
    -- algebra tower.
    simpa [L, B, RingHom.algebraMap_toAlgebra, Localization.localRingHom_to_map] using
      hx_zero_target
  have hx_zero :
      algebraMap (smoothCounterexampleR k) L (smoothCounterexampleX k) = 0 := by
    -- Proof comment: the target localization becomes the source localization after inverting the
    -- unit idempotent `e = 1`.
    apply eUnits.injective
    calc
      eUnits (algebraMap (smoothCounterexampleR k) L (smoothCounterexampleX k))
          = algebraMap L B
              (algebraMap (smoothCounterexampleR k) L (smoothCounterexampleX k)) := by
                simpa using
                  eUnits.commutes
                    (algebraMap (smoothCounterexampleR k) L (smoothCounterexampleX k))
      _ = 0 := hx_zero_local
      _ = eUnits 0 := by
        simpa using (eUnits.commutes (0 : L)).symm
  exact hx_nonzero hx_zero

/-- Helper for Example 16.2.6: smoothness at `q` gives formal smoothness of the induced stalk map
from the contracted source localization. -/
private lemma smoothCounterexample_stalkFormallySmooth_of_mem_smoothLocus
    (k : Type u) [CommRing k] (q : PrimeSpectrum (smoothCounterexampleA k))
    (hqSmooth : q ∈ smoothLocus (smoothCounterexampleR k) (smoothCounterexampleA k)) :
    Algebra.FormallySmooth (smoothCounterexampleSourceStalk k q)
      (smoothCounterexampleTargetStalk k q) := by
  -- Route correction: the intended bridge is `q ∈ smoothLocus -> IsSmoothAt R q.asIdeal ->
  -- FormallySmooth R_q∩R A_q`, but the current blocker is the stalk algebra normalization needed
  -- to supply the exact `IsScalarTower`/`Algebra` spelling for `localization_base`.
  -- TODO: normalize the source-stalk algebra to the canonical `Localization.AtPrime` owner
  -- spelling, then apply `Algebra.FormallySmooth.localization_base`.
  sorry

/-- Helper for Example 16.2.6: finite presentation survives after localizing the quotient map at
the prime `q`. -/
private lemma smoothCounterexample_stalkFinitePresentation
    (k : Type u) [CommRing k] (q : PrimeSpectrum (smoothCounterexampleA k)) :
    Algebra.FinitePresentation (smoothCounterexampleSourceStalk k q)
      (smoothCounterexampleTargetStalk k q) := by
  -- TODO: use `smoothCounterexample_stalkPrimeCompl_map_eq` and `IsLocalization.ker_map` to
  -- identify the stalk-map kernel with the localized principal ideal `(x)`, then apply
  -- `RingHom.FinitePresentation.of_surjective` to the localized quotient map.
  sorry

/-- Helper for Example 16.2.6: the quotient map remains surjective after localizing at a prime of
`A`. -/
private lemma smoothCounterexample_stalkSurjective
    (k : Type u) [CommRing k] (q : PrimeSpectrum (smoothCounterexampleA k)) :
    Function.Surjective
      (algebraMap
        (smoothCounterexampleSourceStalk k q)
        (smoothCounterexampleTargetStalk k q)) := by
  let L := smoothCounterexampleSourceStalk k q
  letI : Algebra L (smoothCounterexampleTargetStalk k q) := by
    exact
      (Localization.localRingHom
        (q.asIdeal.under (smoothCounterexampleR k))
        q.asIdeal
        (Ideal.Quotient.mk (principalIdeal (smoothCounterexampleX k)))
        rfl).toAlgebra
  -- Proof comment: surjectivity of the quotient map survives after passing to the stalk at `q`.
  simpa [L, RingHom.algebraMap_toAlgebra] using
    (RingHom.surjective_localRingHom_of_surjective
      (Ideal.Quotient.mk (principalIdeal (smoothCounterexampleX k)))
      Ideal.Quotient.mk_surjective q.asIdeal)

/-- Helper for Example 16.2.6: a smooth stalk yields the idempotent localization witness from the
flat-surjective criterion. -/
private lemma smoothCounterexample_existsIdempotentStalk_of_mem_smoothLocus
    (k : Type u) [CommRing k] (q : PrimeSpectrum (smoothCounterexampleA k))
    (hqSmooth : q ∈ smoothLocus (smoothCounterexampleR k) (smoothCounterexampleA k)) :
    ∃ e : smoothCounterexampleSourceStalk k q,
      IsIdempotentElem e ∧
        IsLocalization.Away e (smoothCounterexampleTargetStalk k q) := by
  -- TODO: once the localized `FormallySmooth` and `FinitePresentation` bridges are normalized,
  -- package them into `Smooth L B`, obtain `Module.Flat L B`, and apply
  -- `exists_idempotent_localizationAway_of_surjective_of_flat_of_finitePresentation`.
  sorry

/-- Helper for Example 16.2.6: if the complementary idempotent `1 - e` is a unit, then the away
localization witness forces the target stalk to collapse, which is impossible. -/
private lemma smoothCounterexample_false_of_one_sub_unit_idempotent
    (k : Type u) [CommRing k] (q : PrimeSpectrum (smoothCounterexampleA k))
    {e : Localization.AtPrime (q.asIdeal.under (smoothCounterexampleR k))}
    (he : IsIdempotentElem e)
    (heUnit :
      IsUnit ((1 : Localization.AtPrime (q.asIdeal.under (smoothCounterexampleR k))) - e))
    (hAway : IsLocalization.Away e (Localization.AtPrime q.asIdeal)) :
    False := by
  -- TODO: rewrite idempotence as `e * (1 - e) = 0`, cancel the unit `1 - e` to prove `e = 0`,
  -- then rewrite the away-localization witness to `Away 0` and contradict nontriviality via
  -- `IsLocalization.subsingleton`.
  sorry

/-- Helper for Example 16.2.6: a prime containing every `yᵢ` cannot lie in the smooth locus. -/
private lemma smoothCounterexample_not_mem_smoothLocus_of_forall_y_mem
    (k : Type u) [CommRing k] (q : PrimeSpectrum (smoothCounterexampleA k))
      (hqy : ∀ i : ℕ+, smoothCounterexampleY k i ∈ q.asIdeal) :
      q ∉ smoothLocus (smoothCounterexampleR k) (smoothCounterexampleA k) := by
  -- TODO: combine the already-proved nonvanishing of `x` in the source stalk with the localized
  -- idempotent witness from `smoothCounterexample_existsIdempotentStalk_of_mem_smoothLocus`, then
  -- split on `IsLocalRing.isUnit_or_isUnit_one_sub_self e`.
  sorry

-- Proof sketch: away from `y_i`, the relation `x y_i = 0` forces `x = 0`, so on `D(y_i)` the
-- quotient `A` agrees with the corresponding localization of `R` and is smooth there. Conversely,
-- if all `y_i` vanish at a prime of `A`, the fiber still carries infinitely many singular
-- directions coming from the countable family of relations `x y_i`, so the map is not smooth at
-- that prime.
/-- Helper for Example 16.2.6: any smooth prime must avoid at least one `yᵢ`. -/
private lemma smoothCounterexample_smoothLocus_subset_iUnion_basicOpen
    (k : Type u) [CommRing k] :
    smoothLocus (smoothCounterexampleR k) (smoothCounterexampleA k) ⊆
      ⋃ i : ℕ+, (PrimeSpectrum.basicOpen (smoothCounterexampleY k i) :
        Set (PrimeSpectrum (smoothCounterexampleA k))) := by
  intro q hq
  by_contra hqUnion
  have hqy : ∀ i : ℕ+, smoothCounterexampleY k i ∈ q.asIdeal := by
    intro i
    by_contra hyi
    apply hqUnion
    refine Set.mem_iUnion.2 ⟨i, ?_⟩
    simpa using (PrimeSpectrum.mem_basicOpen (smoothCounterexampleY k i) q).2 hyi
  -- Proof comment: outside every basic open `D(yᵢ)`, the localized class of `x` stays nonzero, so
  -- the local quotient cannot be smooth.
  exact smoothCounterexample_not_mem_smoothLocus_of_forall_y_mem k q hqy hq

/-- Helper for Example 16.2.6: each basic open `D(yᵢ)` lies inside the smooth locus. -/
private lemma smoothCounterexample_iUnion_basicOpen_subset_smoothLocus
    (k : Type u) [CommRing k] :
    (⋃ i : ℕ+, (PrimeSpectrum.basicOpen (smoothCounterexampleY k i) :
      Set (PrimeSpectrum (smoothCounterexampleA k)))) ⊆
      smoothLocus (smoothCounterexampleR k) (smoothCounterexampleA k) := by
  intro q hq
  rcases Set.mem_iUnion.mp hq with ⟨i, hi⟩
  have hbasic :
      (PrimeSpectrum.basicOpen (smoothCounterexampleY k i) :
        Set (PrimeSpectrum (smoothCounterexampleA k))) ⊆
        smoothLocus (smoothCounterexampleR k) (smoothCounterexampleA k) := by
    rw [Algebra.basicOpen_subset_smoothLocus_iff_smooth]
    let e := smoothCounterexample_targetAwayYAlgEquivSourceAwayY k i
    let _ :
        Smooth (smoothCounterexampleR k)
          (Localization.Away (smoothCounterexampleYInR k i)) :=
      smoothCounterexample_source_smooth_away_y k i
    -- Proof comment: the localized target chart is equivalent to the source localization, so
    -- smoothness transports directly across that equivalence.
    exact Smooth.of_equiv e
  exact hbasic hi

/-- Example 16.2.6: for
`R = k[x, y₁, y₂, y₃, ...] / (x y_i \mid i \ge 1)` and `A = R / (x)`, the smooth locus of the
ring map `R → A` is exactly `⋃_i D(y_i)`. -/
theorem smoothCounterexample_smoothLocus_eq_iUnion_basicOpen
    (k : Type u) [CommRing k] :
    smoothLocus (smoothCounterexampleR k) (smoothCounterexampleA k) =
      ⋃ i : ℕ+, (PrimeSpectrum.basicOpen (smoothCounterexampleY k i) :
        Set (PrimeSpectrum (smoothCounterexampleA k))) :=
by
  -- Proof comment: the equality is now assembled from the two separately packaged inclusions.
  exact Set.Subset.antisymm
    (smoothCounterexample_smoothLocus_subset_iUnion_basicOpen k)
    (smoothCounterexample_iUnion_basicOpen_subset_smoothLocus k)

/-- Helper for Example 16.2.6: every finite union of the basic opens `D(y_i)` misses a prime of
`A` that still lies in some other `D(y_j)`. -/
lemma smoothCounterexample_finite_subunion_missed
    (k : Type u) [CommRing k] [Nontrivial k] (s : Finset ℕ+) :
    ∃ q : PrimeSpectrum (smoothCounterexampleA k),
      q ∈ ⋃ i : ℕ+, (PrimeSpectrum.basicOpen (smoothCounterexampleY k i) :
        Set (PrimeSpectrum (smoothCounterexampleA k))) ∧
      q ∉ ⋃ i ∈ s, (PrimeSpectrum.basicOpen (smoothCounterexampleY k i) :
        Set (PrimeSpectrum (smoothCounterexampleA k))) := by
  classical
  have hbot : (⊥ : Ideal k) ≠ ⊤ := by
    intro htop
    have hone : (1 : k) ∈ (⊥ : Ideal k) := by simpa [htop]
    simpa using hone
  obtain ⟨m, hmmax, _⟩ := Ideal.exists_le_maximal (⊥ : Ideal k) hbot
  letI : m.IsMaximal := hmmax
  let jNat : ℕ := s.sup fun i : ℕ+ ↦ (i : ℕ)
  let j : ℕ+ := ⟨jNat + 1, Nat.succ_pos _⟩
  have hj_not_mem : j ∉ s := by
    intro hj
    have hle : (j : ℕ) ≤ jNat := by
      simpa [jNat] using (Finset.le_sup (f := fun i : ℕ+ ↦ (i : ℕ)) hj)
    exact Nat.not_succ_le_self jNat (by simpa [j, jNat] using hle)
  let ambientEval : smoothCounterexamplePolynomialRing k →ₐ[k] (k ⧸ m) :=
    MvPolynomial.eval₂AlgHom k fun t =>
      match t with
      | none => 0
      | some i => if i = j then 1 else 0
  have hrel_mem :
      smoothCounterexampleRelationIdeal k ≤ RingHom.ker ambientEval.toRingHom := by
    rw [smoothCounterexampleRelationIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    -- Each relation `x * y_i` vanishes because the chosen evaluation sends `x` to `0`.
    simp [ambientEval, smoothCounterexampleXPolynomial, smoothCounterexampleYPolynomial]
  have hrel_zero :
      ∀ a ∈ smoothCounterexampleRelationIdeal k, ambientEval a = 0 := by
    intro a ha
    exact hrel_mem ha
  let toR : smoothCounterexampleR k →+* (k ⧸ m) :=
    Ideal.Quotient.lift _ ambientEval.toRingHom hrel_zero
  have hx_zero : toR (smoothCounterexampleX k) = 0 := by
    -- The outer quotient by `(x)` is available because `x` itself evaluates to zero.
    calc
      toR (smoothCounterexampleX k)
          = ambientEval (smoothCounterexampleXPolynomial k) := by
              simp [toR, smoothCounterexampleX]
      _ = 0 := by
        simp [ambientEval, smoothCounterexampleXPolynomial]
  let toA : smoothCounterexampleA k →+* (k ⧸ m) :=
    Ideal.Quotient.lift _ toR fun a ha => by
      rcases (Ideal.mem_span_singleton.mp ha) with ⟨r, rfl⟩
      simp [hx_zero]
  have hy_image (i : ℕ+) :
      toA (smoothCounterexampleY k i) = if i = j then 1 else 0 := by
    -- Unwind the two quotient lifts and then evaluate the chosen variable assignment.
    calc
      toA (smoothCounterexampleY k i)
          = toR (smoothCounterexampleYInR k i) := by
              simp [toA, smoothCounterexampleY]
      _ = ambientEval (smoothCounterexampleYPolynomial k i) := by
        simp [toR, smoothCounterexampleYInR]
      _ = if i = j then 1 else 0 := by
        simp [ambientEval, smoothCounterexampleYPolynomial]
  let q : PrimeSpectrum (smoothCounterexampleA k) :=
    PrimeSpectrum.mk (RingHom.ker toA) (RingHom.ker_isPrime toA)
  refine ⟨q, ?_, ?_⟩
  · -- The chosen point lies in `D(y_j)` because `y_j` evaluates to `1`.
    refine Set.mem_iUnion.2 ⟨j, ?_⟩
    have hbasic :
        q ∈ (PrimeSpectrum.basicOpen (smoothCounterexampleY k j) :
          Set (PrimeSpectrum (smoothCounterexampleA k))) ↔
          smoothCounterexampleY k j ∉ q.asIdeal := by
      simpa using (PrimeSpectrum.mem_basicOpen (smoothCounterexampleY k j) q)
    rw [hbasic]
    change toA (smoothCounterexampleY k j) ≠ 0
    simpa [hy_image]
  · -- Every `y_i` with `i ∈ s` evaluates to `0`, so the point misses the finite subunion.
    intro hq
    rcases Set.mem_iUnion₂.mp hq with ⟨i, his, hiq⟩
    have hiq' :
        smoothCounterexampleY k i ∉ q.asIdeal := by
      simpa using (PrimeSpectrum.mem_basicOpen (smoothCounterexampleY k i) q).mp hiq
    apply hiq'
    change toA (smoothCounterexampleY k i) = 0
    have hij_ne : i ≠ j := by
      intro hij
      subst hij
      exact hj_not_mem his
    rw [hy_image, if_neg hij_ne]

-- Proof sketch: if the displayed union were compact, then in the spectral space `Spec(A)` it
-- would be a finite union of basic opens. But any finite subunion `⋃_{i ∈ s} D(y_i)` misses a
-- prime containing all `y_i` with `i ∉ s`, so no finite subcover exists.
/-- The smooth locus in the counterexample is not quasi-compact, equivalently not compact as a
subset of `Spec(A)`. -/
theorem smoothCounterexample_smoothLocus_not_isCompact
    (k : Type u) [CommRing k] [Nontrivial k] :
    ¬ IsCompact (smoothLocus (smoothCounterexampleR k) (smoothCounterexampleA k)) := by
  classical
  intro hcompact
  let U : ℕ+ → Set (PrimeSpectrum (smoothCounterexampleA k)) :=
    fun i ↦ PrimeSpectrum.basicOpen (smoothCounterexampleY k i)
  have hcover :
      smoothLocus (smoothCounterexampleR k) (smoothCounterexampleA k) ⊆ ⋃ i, U i := by
    simpa [U, smoothCounterexample_smoothLocus_eq_iUnion_basicOpen k] using
      (Set.Subset.refl (smoothLocus (smoothCounterexampleR k) (smoothCounterexampleA k)))
  obtain ⟨t, ht⟩ :=
    IsCompact.elim_finite_subcover hcompact U
      (fun i ↦ PrimeSpectrum.isOpen_basicOpen) hcover
  obtain ⟨q, hqUnion, hqNotFinite⟩ :=
    smoothCounterexample_finite_subunion_missed (k := k) t
  have hqSmooth : q ∈ smoothLocus (smoothCounterexampleR k) (smoothCounterexampleA k) := by
    simpa [U, smoothCounterexample_smoothLocus_eq_iUnion_basicOpen k] using hqUnion
  exact hqNotFinite (ht hqSmooth)

end Algebra
