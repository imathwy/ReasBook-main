import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum Set Topology

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsJacobsonRing R] [Algebra.FiniteType R S]

/- Layering for this item:
* source-facing: finite type maps from Jacobson rings send closed points to closed points, and the
  induced residue-field extensions at closed points are finite;
* core/canonical owner: `closedPoints` together with the canonical map `PrimeSpectrum.comap`;
* bridge/view: the restricted map `PrimeSpectrum.comapClosedPoints` on the closed-point loci.
-/

/- Proposition 10.35.19 (1): if `R` is a Jacobson ring and `S` is a finite type `R`-algebra, then
`S` is again a Jacobson ring. This is exactly the canonical mathlib theorem
`isJacobsonRing_of_finiteType`. -/
recall isJacobsonRing_of_finiteType

-- Proof sketch: a closed point of `Spec S` is the same as a maximal ideal of `S`. Apply
-- `PrimeSpectrum.isClosed_singleton_iff_isMaximal` to the given closed point, use the Jacobson
-- finite-type theorem on the quotient map to see that its contraction is maximal, and translate
-- back to a closed point of `Spec R`.
/-- Proposition 10.35.19 (2): for a finite type map from a Jacobson ring, the induced map
`Spec S → Spec R` sends closed points to closed points. -/
theorem comap_mapsTo_closedPoints :
    Set.MapsTo (comap (algebraMap R S))
      (closedPoints (PrimeSpectrum S)) (closedPoints (PrimeSpectrum R)) := by
  sorry

-- Proof sketch: if `x.asIdeal` is maximal, pass to the induced finite type map on quotients
-- `R / (x.asIdeal ∩ R) → S / x.asIdeal`; the target is a field, so
-- `finite_of_finite_type_of_isJacobsonRing` makes it a finite module over the source.
-- Identifying the source and target fraction fields with the corresponding residue fields gives
-- finiteness of `κ(x) / κ(f(x))`.
private theorem moduleFinite_residueField_of_isMaximal (x : PrimeSpectrum S)
    (hx : x.asIdeal.IsMaximal) :
    Module.Finite (comap (algebraMap R S) x).asIdeal.ResidueField
      x.asIdeal.ResidueField := sorry

/-- Proposition 10.35.19 (3): if `x : Spec(S)` is a closed point, equivalently if `x.asIdeal` is
maximal, then the residue field extension `κ(x) / κ(f(x))` is finite, where
`f : Spec S → Spec R` is induced by `R → S`. -/
theorem moduleFinite_residueField_of_mem_closedPoints (x : PrimeSpectrum S)
    (hx : x ∈ closedPoints (PrimeSpectrum S)) :
    Module.Finite (comap (algebraMap R S) x).asIdeal.ResidueField
      x.asIdeal.ResidueField := by
  exact moduleFinite_residueField_of_isMaximal x
    ((isClosed_singleton_iff_isMaximal x).1 <| by simpa [closedPoints] using hx)

end

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable [IsJacobsonRing R]

namespace PrimeSpectrum

private theorem comap_mapsTo_closedPoints_of_finiteType (f : R →+* S) (hf : f.FiniteType) :
    Set.MapsTo (comap f) (closedPoints (PrimeSpectrum S)) (closedPoints (PrimeSpectrum R)) := by
  letI : Algebra R S := f.toAlgebra
  have hf' : (algebraMap R S).FiniteType := by
    simpa [RingHom.algebraMap_toAlgebra] using hf
  letI : Algebra.FiniteType R S := (RingHom.finiteType_algebraMap).mp hf'
  have hclosed :
      Set.MapsTo (comap (algebraMap R S))
        (closedPoints (PrimeSpectrum S)) (closedPoints (PrimeSpectrum R)) :=
    comap_mapsTo_closedPoints
  simpa [RingHom.algebraMap_toAlgebra] using hclosed

/-- The map on spectra induced by a finite type ring homomorphism restricts to the canonical
closed-point loci when the source ring is Jacobson. -/
def comapClosedPoints (f : R →+* S) (hf : f.FiniteType) :
    closedPoints (PrimeSpectrum S) → closedPoints (PrimeSpectrum R) :=
  (comap_mapsTo_closedPoints_of_finiteType f hf).restrict (comap f)
    (closedPoints (PrimeSpectrum S)) (closedPoints (PrimeSpectrum R))

@[simp] theorem val_comapClosedPoints (f : R →+* S) (hf : f.FiniteType)
    (x : closedPoints (PrimeSpectrum S)) :
    ((comapClosedPoints f hf x : closedPoints (PrimeSpectrum R)) : PrimeSpectrum R) = comap f x :=
  Set.MapsTo.val_restrict_apply (comap_mapsTo_closedPoints_of_finiteType f hf) x

end PrimeSpectrum

end
