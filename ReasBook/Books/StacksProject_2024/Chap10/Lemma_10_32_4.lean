import Mathlib
import StacksProject_2024.Chap10.Definition_10_32_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R]

/-- Lemma 10.32.4: if `I` is locally nilpotent, then an element of `R` is a unit exactly when
its image in the quotient ring `R ⧸ I` is a unit.

This is a `bridge/view` theorem: the source-facing hypothesis `I.IsLocallyNilpotent` supplies the
owner abstraction `IsLocalHom (Ideal.Quotient.mk I)` via the Jacobson-radical criterion, and the
statement then follows from `isUnit_map_iff`. -/
theorem isUnit_iff_isUnit_quotient_mk_of_isLocallyNilpotent (I : Ideal R)
    (hI : I.IsLocallyNilpotent) {x : R} :
    IsUnit x ↔ IsUnit (Ideal.Quotient.mk I x) := by
  have hIjac : I ≤ Ideal.jacobson ⊥ := by
    simpa [Ideal.jacobson_bot] using le_trans hI (nilradical_le_jacobson R)
  let _ : IsLocalHom (Ideal.Quotient.mk I) :=
    isLocalHom_of_le_jacobson_bot I hIjac
  exact (isUnit_map_iff (Ideal.Quotient.mk I) x).symm

end
