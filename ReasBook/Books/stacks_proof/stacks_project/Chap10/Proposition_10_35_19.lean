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
/-- Helper for Proposition 10.35.19: the contraction of a maximal ideal along a finite type map
from a Jacobson ring is maximal. -/
private theorem comap_asIdeal_isMaximal_of_isMaximal (x : PrimeSpectrum S)
    (hx : x.asIdeal.IsMaximal) :
    (comap (algebraMap R S) x).asIdeal.IsMaximal := by
  let q : Ideal S := x.asIdeal
  let p : Ideal R := q.under R
  letI : q.IsMaximal := hx
  letI : q.LiesOver p := ⟨rfl⟩
  have hp_eq : p = (comap (algebraMap R S) x).asIdeal := by
    simp [p, q, Ideal.under_def, PrimeSpectrum.comap_asIdeal]
  letI : Field (S ⧸ q) := Ideal.Quotient.field q
  -- The quotient map `(R / p) → (S / q)` is finite type with field target, so it is finite.
  have hfinite : Module.Finite (R ⧸ p) (S ⧸ q) := by
    letI : Algebra.FiniteType (R ⧸ p) (S ⧸ q) := inferInstance
    simpa using (finite_of_finite_type_of_isJacobsonRing (R ⧸ p) (S ⧸ q))
  letI : Algebra.IsIntegral (R ⧸ p) (S ⧸ q) :=
    Algebra.IsIntegral.of_finite (R := R ⧸ p) (B := S ⧸ q)
  -- An integral subring of a field is a field, so `R / p` is a field and `p` is maximal.
  have hfield : IsField (R ⧸ p) := by
    exact isField_of_isIntegral_of_isField Ideal.algebraMap_quotient_injective
      (Ideal.Quotient.field q).toIsField
  have hpmax : p.IsMaximal := Ideal.Quotient.maximal_of_isField p hfield
  simpa [hp_eq] using hpmax

/-- Helper for Proposition 10.35.19: the residue-field map at a closed point is of finite type. -/
private theorem finiteType_residueField_of_isMaximal (x : PrimeSpectrum S)
    (hx : x.asIdeal.IsMaximal) :
    Algebra.FiniteType (comap (algebraMap R S) x).asIdeal.ResidueField x.asIdeal.ResidueField := by
  let q : Ideal S := x.asIdeal
  let p : Ideal R := q.under R
  letI : q.IsMaximal := hx
  letI : q.LiesOver p := ⟨rfl⟩
  have hp_eq : p = (comap (algebraMap R S) x).asIdeal := by
    simp [p, q, Ideal.under_def, PrimeSpectrum.comap_asIdeal]
  letI : p.IsMaximal := comap_asIdeal_isMaximal_of_isMaximal x hx
  have hcomap : p = Ideal.comap (algebraMap R S) q := by
    simp [p, q, Ideal.under_def]
  let pToQ : p.ResidueField →ₐ[R] q.ResidueField :=
    Ideal.ResidueField.mapₐ p q (Algebra.ofId R S) hcomap
  letI : Algebra p.ResidueField q.ResidueField := pToQ.toAlgebra
  let quotientToResidue : (R ⧸ p) →+* q.ResidueField :=
    (algebraMap p.ResidueField q.ResidueField).comp (algebraMap (R ⧸ p) p.ResidueField)
  letI : Algebra (R ⧸ p) q.ResidueField := quotientToResidue.toAlgebra
  letI : IsScalarTower (R ⧸ p) p.ResidueField q.ResidueField :=
    IsScalarTower.of_algebraMap_eq' rfl
  -- Make the quotient-to-residue-field map available as an `(R / p)`-algebra morphism.
  letI : IsScalarTower (R ⧸ p) (S ⧸ q) q.ResidueField := by
    refine .of_algebraMap_eq fun y => ?_
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [show algebraMap (R ⧸ p) q.ResidueField (Ideal.Quotient.mk p y) =
        algebraMap p.ResidueField q.ResidueField
          (algebraMap (R ⧸ p) p.ResidueField (Ideal.Quotient.mk p y)) by
      rfl]
    simp only [Ideal.Quotient.algebraMap_mk_of_liesOver, Ideal.algebraMap_quotient_residueField_mk]
    change Ideal.ResidueField.map p q (algebraMap R S) hcomap (algebraMap R p.ResidueField y) =
      algebraMap S q.ResidueField ((algebraMap R S) y)
    exact Ideal.ResidueField.map_algebraMap p q (algebraMap R S) hcomap y
  -- First show `q.ResidueField` is finite type over `R / p` using the surjection `S / q → κ(q)`.
  have hquot : Algebra.FiniteType (R ⧸ p) q.ResidueField := by
    let f : (S ⧸ q) →ₐ[R ⧸ p] q.ResidueField := IsScalarTower.toAlgHom _ _ _
    apply Algebra.FiniteType.of_surjective f
    simpa using q.bijective_algebraMap_quotient_residueField.surjective
  -- Then descend finite type across the surjective map `(R / p) → κ(p)`.
  have hcomp : (Algebra.ofId (R ⧸ p) q.ResidueField).FiniteType := by
    simpa [AlgHom.FiniteType] using hquot
  have hres : (IsScalarTower.toAlgHom (R ⧸ p) p.ResidueField q.ResidueField).FiniteType := by
    exact AlgHom.FiniteType.of_comp_finiteType
      (f := Algebra.ofId (R ⧸ p) p.ResidueField)
      (g := IsScalarTower.toAlgHom (R ⧸ p) p.ResidueField q.ResidueField)
      (by simpa using hcomp)
  rw [← RingHom.finiteType_algebraMap]
  simpa [AlgHom.FiniteType, hp_eq] using hres

/-- Proposition 10.35.19 (2): for a finite type map from a Jacobson ring, the induced map
`Spec S → Spec R` sends closed points to closed points. -/
@[stacks 00GB]
theorem comap_mapsTo_closedPoints :
    Set.MapsTo (comap (algebraMap R S))
      (closedPoints (PrimeSpectrum S)) (closedPoints (PrimeSpectrum R)) := by
  intro x hx
  -- Closed points are exactly maximal ideals, so the previous helper proves the claim.
  rw [closedPoints, Set.mem_setOf_eq, PrimeSpectrum.isClosed_singleton_iff_isMaximal] at hx ⊢
  exact comap_asIdeal_isMaximal_of_isMaximal x hx

-- Proof sketch: if `x.asIdeal` is maximal, pass to the induced finite type map on quotients
-- `R / (x.asIdeal ∩ R) → S / x.asIdeal`; the target is a field, so
-- `finite_of_finite_type_of_isJacobsonRing` makes it a finite module over the source.
-- Identifying the source and target fraction fields with the corresponding residue fields gives
-- finiteness of `κ(x) / κ(f(x))`.
private theorem moduleFinite_residueField_of_isMaximal (x : PrimeSpectrum S)
    (hx : x.asIdeal.IsMaximal) :
    Module.Finite (comap (algebraMap R S) x).asIdeal.ResidueField
      x.asIdeal.ResidueField := by
  let q : Ideal S := x.asIdeal
  let p : Ideal R := q.under R
  letI : q.IsMaximal := hx
  letI : p.IsMaximal := comap_asIdeal_isMaximal_of_isMaximal x hx
  have hp_eq : p = (comap (algebraMap R S) x).asIdeal := by
    simp [p, q, Ideal.under_def, PrimeSpectrum.comap_asIdeal]
  have hfiniteType : Algebra.FiniteType p.ResidueField q.ResidueField :=
    finiteType_residueField_of_isMaximal x hx
  letI : Algebra.FiniteType p.ResidueField q.ResidueField := hfiniteType
  -- Over the field `κ(p)`, a finite type algebra field is automatically finite.
  have hfinite : Module.Finite p.ResidueField q.ResidueField := by
    simpa using (finite_of_finite_type_of_isJacobsonRing p.ResidueField q.ResidueField)
  simpa [hp_eq, p, q] using hfinite

/-- Proposition 10.35.19 (3): if `x : Spec(S)` is a closed point, equivalently if `x.asIdeal` is
maximal, then the residue field extension `κ(x) / κ(f(x))` is finite, where
`f : Spec S → Spec R` is induced by `R → S`. -/
@[stacks 00GB]
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
