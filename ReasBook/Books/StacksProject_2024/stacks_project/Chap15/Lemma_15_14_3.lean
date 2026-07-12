import Mathlib.RingTheory.Ideal.Quotient.Basic
import StacksProject_2024.Chap15.Definition_15_14_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {A : Type u} [CommRing A]
variable [IsAbsolutelyIntegrallyClosed A]

/-
Domain-style sampling for Lemma 15.14.3:
- primary domain: commutative algebra of absolute integral closedness, polynomial splitting, and
  permanence under quotient and localization maps;
- sampled owner-level declarations:
  `IsAbsolutelyIntegrallyClosed`,
  `IsAbsolutelyIntegrallyClosed.exists_root`,
  `Polynomial.lifts_and_natDegree_eq_and_monic`,
  `IsLocalization.scaleRoots_commonDenom_mem_lifts`;
- best owner abstraction: the chapter owner `IsAbsolutelyIntegrallyClosed`;
- primitive data: the owner field `splits` for monic polynomials, together with the canonical
  quotient and localization ring maps used to transport that splitting data;
- derived API: root-existence results such as `IsAbsolutelyIntegrallyClosed.exists_root`, which are
  downstream consequences rather than primitive inputs here.

Source/core/bridge triage:
- `source-facing`: permanence of absolute integral closedness under quotients and localizations;
- `core/canonical`: `IsAbsolutelyIntegrallyClosed`;
- `bridge/view`: the quotient map `A →+* A ⧸ I` and the localization map `A →+* S`, through which
  the canonical splitting data is transported.
-/

-- Proof sketch: for a monic polynomial over `A ⧸ I`, lift its coefficients to `A`, keep the
-- leading coefficient equal to `1`, and use absolute integral closedness of `A` to split the
-- lifted monic polynomial. Mapping the resulting linear-factor decomposition through the quotient
-- map gives a splitting in `A ⧸ I`.
/-- Lemma 15.14.3 (1): any quotient ring `A ⧸ I` of an absolutely integrally closed ring `A` is
absolutely integrally closed. -/
instance (I : Ideal A) : IsAbsolutelyIntegrallyClosed (A ⧸ I) where
  splits f hf := by
    let φ : A →+* A ⧸ I := Ideal.Quotient.mk I
    have hf_lifts : f ∈ Polynomial.lifts (Ideal.Quotient.mk I) := by
      rw [Polynomial.mem_lifts]
      exact Polynomial.map_surjective φ Ideal.Quotient.mk_surjective f
    obtain ⟨g, hg, -, hg_monic⟩ :=
      Polynomial.lifts_and_natDegree_eq_and_monic hf_lifts hf
    simpa [← hg] using (IsAbsolutelyIntegrallyClosed.splits g hg_monic).map φ

-- Proof sketch: given a monic polynomial over a localization `S` of `A` at `M`, clear denominators from its
-- non-leading coefficients to obtain a monic polynomial over `A` after rescaling. Split that
-- monic polynomial in `A` using absolute integral closedness, then map the factorization to `S`
-- and undo the rescaling to obtain a splitting there.
/-- Lemma 15.14.3 (2): any localization of an absolutely integrally closed ring `A` is
absolutely integrally closed. -/
theorem isAbsolutelyIntegrallyClosed_of_isLocalization
    {S : Type v} [CommRing S] [Algebra A S] (M : Submonoid A) [IsLocalization M S] :
    IsAbsolutelyIntegrallyClosed S := by
  refine ⟨?_⟩
  intro f hf
  let d : M := IsLocalization.commonDenom M f.support f.coeff
  let φ : A →+* S := algebraMap A S
  have hf_lifts :
      f.scaleRoots (φ d) ∈ Polynomial.lifts φ := by
    exact IsLocalization.scaleRoots_commonDenom_mem_lifts M f ⟨1, by simp [hf.leadingCoeff]⟩
  obtain ⟨g, hg, -, hg_monic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hf_lifts
      ((Polynomial.monic_scaleRoots_iff (φ d)).2 hf)
  have hsplits_scaled : (f.scaleRoots (φ d)).Splits := by
    simpa [← hg] using (IsAbsolutelyIntegrallyClosed.splits g hg_monic).map φ
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp (IsLocalization.map_units S d)
  have hscale : (f.scaleRoots (φ d)).scaleRoots v = f := by
    rw [← Polynomial.scaleRoots_mul, hv, Polynomial.scaleRoots_one]
  simpa [hscale] using hsplits_scaled.scaleRoots v

instance (M : Submonoid A) : IsAbsolutelyIntegrallyClosed (Localization M) :=
  isAbsolutelyIntegrallyClosed_of_isLocalization M

end
