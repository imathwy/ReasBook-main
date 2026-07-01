import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Localization

section

variable {R : Type u} {K : Type v} [CommRing R] [Field K] [Algebra R K]

-- Layering for this item:
-- * source-facing: the existence of a nonzero localization `R_f` that is a field and makes the
--   induced map to `K` finite.
-- * core/canonical owners: `Localization.Away`, the canonical lift `awayLift`, and the owner
--   finiteness predicates `RingHom.FiniteType` and `RingHom.Finite`.
-- * bridge/view: `RingHom.FiniteType.of_comp_finiteType` and
--   `RingHom.finite_iff_finiteType_of_isJacobsonRing`.

/-- Lemma 10.34.2: if `R ⊆ K` and `K` is a finite type `R`-algebra, then some nonzero
localization `R_f` is a field and the induced map `R_f → K` is finite, i.e. `K / R_f` is a finite
field extension. -/
-- Proof sketch: apply Lemma `10.30.2` to the image of `Spec(K) → Spec(R)` to obtain a nonzero
-- `f : R` with `D(f) = {(0)}`. This makes `Spec(R_f)` a singleton, hence `R_f` a field. The
-- induced map `R_f → K` is still of finite type, and then Hilbert Nullstellensatz
-- (`finite_of_finite_type_of_isJacobsonRing`) yields finiteness over the field `R_f`.
theorem exists_nonzero_localizationAway_isField_and_finite
    (hinj : Function.Injective (algebraMap R K)) [Algebra.FiniteType R K] :
    ∃ (f : R) (hf : f ≠ 0),
      IsField (Localization.Away f) ∧
        RingHom.Finite
          (awayLift (algebraMap R K) f
            (IsUnit.mk0 _ ((map_ne_zero_iff (algebraMap R K) hinj).2 hf))) := by
  -- Source-facing primitive step: after shrinking to some basic open `D(f)`, the localization
  -- `R_f` becomes a field.
  have hfield :
      ∃ (f : R) (hf : f ≠ 0), IsField (Localization.Away f) := by
    sorry
  rcases hfield with ⟨f, hf, hfield⟩
  let φ : Localization.Away f →+* K :=
    awayLift (algebraMap R K) f
      (IsUnit.mk0 _ ((map_ne_zero_iff (algebraMap R K) hinj).2 hf))
  have hfiniteType : φ.FiniteType := by
    have hcomp : (φ.comp (algebraMap R (Localization.Away f))).FiniteType := by
      simpa [φ] using
        (RingHom.finiteType_algebraMap).2 (inferInstance : Algebra.FiniteType R K)
    exact RingHom.FiniteType.of_comp_finiteType hcomp
  letI : Field (Localization.Away f) := hfield.toField
  have hfinite : φ.Finite := by
    exact (RingHom.finite_iff_finiteType_of_isJacobsonRing).2 hfiniteType
  exact ⟨f, hf, hfield,
    hfinite⟩

end
