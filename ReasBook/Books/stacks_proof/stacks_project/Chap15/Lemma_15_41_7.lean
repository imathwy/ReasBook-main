import StacksProject_2024.Chap10.Lemma_10_39_10
import StacksProject_2024.Chap10.Lemma_10_166_3
import StacksProject_2024.Chap15.Definition_15_41_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open scoped TensorProduct

namespace RingHom.IsRegularRingMap

universe u v w

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]
variable {f : A →+* B} {g : B →+* C}

/-- Helper for Lemma 15.41.7: the algebra structures induced by `f`, `g`, and `g.comp f` form the
expected scalar tower `A → B → C`. -/
lemma comp_isScalarTower :
    let _ : Algebra A B := f.toAlgebra
    let _ : Algebra B C := g.toAlgebra
    let _ : Algebra A C := (g.comp f).toAlgebra
    IsScalarTower A B C := by
  let _ : Algebra A B := f.toAlgebra
  let _ : Algebra B C := g.toAlgebra
  let _ : Algebra A C := (g.comp f).toAlgebra
  -- The composite algebra structure on `C` is definitionally `g.comp f`.
  exact IsScalarTower.of_algebraMap_eq' <| RingHom.ext fun _ ↦ rfl

/-- Helper for Lemma 15.41.7: faithful flatness of `g` descends flatness from `g.comp f` to
`f`. -/
lemma flat_of_comp_of_faithfullyFlat (hgf : (g.comp f).Flat) (hg : g.FaithfullyFlat) : f.Flat := by
  let _ : Algebra A B := f.toAlgebra
  let _ : Algebra B C := g.toAlgebra
  let _ : Algebra A C := (g.comp f).toAlgebra
  -- Rewrite the owner hypotheses into the canonical algebra-map forms used by Chapter 10.
  have hBC : (algebraMap B C).FaithfullyFlat := by
    simpa [RingHom.algebraMap_toAlgebra] using hg
  have hAC : (algebraMap A C).Flat := by
    simpa [RingHom.algebraMap_toAlgebra] using hgf
  have hBCff : Module.FaithfullyFlat B C := RingHom.faithfullyFlat_algebraMap_iff.mp hBC
  have hACflat : Module.Flat A C := RingHom.flat_algebraMap_iff.mp hAC
  have hRestrict : Module.Flat A (RestrictScalars A B C) := by
    -- The `A`-module underlying `RestrictScalars A B C` is exactly `C`.
    change Module.Flat A C
    exact hACflat
  let _ : Module.FaithfullyFlat B C := hBCff
  let _ : Module.Flat A (RestrictScalars A B C) := hRestrict
  -- Apply the canonical faithfully flat descent lemma for flatness.
  simpa [RingHom.algebraMap_toAlgebra] using
    (algebraMap_flat_of_flat_of_faithfullyFlat C : (algebraMap A B).Flat)

section FiberBaseChange

variable [Algebra A B] [Algebra B C]

/-- Helper for Lemma 15.41.7: the fiber of `B → C` over a prime `p : Spec A`, base changed from
`B` to `C`. -/
abbrev fiberBaseChange (p : PrimeSpectrum A) : Type (max u v w) :=
  (p.asIdeal.Fiber B) ⊗[B] C

/-- Helper for Lemma 15.41.7: the fiber base change carries the obvious scalar tower from the
residue field through the fiber of `B`. -/
lemma fiber_baseChange_isScalarTower (p : PrimeSpectrum A) :
    IsScalarTower p.asIdeal.ResidueField (p.asIdeal.Fiber B) (fiberBaseChange (B := B) (C := C) p) := by
  -- Both routes from the residue field to the tensor product are the canonical left-factor map.
  exact IsScalarTower.of_algebraMap_eq' <| RingHom.ext fun _ ↦ rfl

/-- Helper for Lemma 15.41.7: faithful flatness of `B → C` survives after passing to the fiber
over `p`. -/
lemma fiber_baseChange_faithfullyFlat
    (hBC : (algebraMap B C).FaithfullyFlat) (p : PrimeSpectrum A) :
    (algebraMap (p.asIdeal.Fiber B) (fiberBaseChange (B := B) (C := C) p)).FaithfullyFlat := by
  have hBCff : Module.FaithfullyFlat B C := RingHom.faithfullyFlat_algebraMap_iff.mp hBC
  let _ : Module.FaithfullyFlat B C := hBCff
  have hfiber :
      Module.FaithfullyFlat (p.asIdeal.Fiber B) (fiberBaseChange (B := B) (C := C) p) := by
    infer_instance
  -- This is the standard faithfully flat base change instance for tensor products.
  exact RingHom.faithfullyFlat_algebraMap_iff.mpr hfiber

section FiberComparison

variable [Algebra A C] [IsScalarTower A B C]

/-- Helper for Lemma 15.41.7: canceling the base change along `A → κ(p)` identifies the base
changed fiber of `B → C` with the fiber of `A → C` over `p`. -/
noncomputable def fiber_baseChange_algEquiv (p : PrimeSpectrum A) :
    fiberBaseChange (B := B) (C := C) p ≃ₐ[p.asIdeal.ResidueField] p.asIdeal.Fiber C :=
  Algebra.IsPushout.cancelBaseChangeAlg A p.asIdeal.ResidueField
    B (p.asIdeal.Fiber B) C

/-- Helper for Lemma 15.41.7: geometric regularity of the composite fiber transfers across the
canonical cancellation equivalence to the fiber base change. -/
lemma fiber_baseChange_comparison_isScalarTower (p : PrimeSpectrum A) :
    let _ : Algebra (fiberBaseChange (B := B) (C := C) p) (p.asIdeal.Fiber C) :=
      (fiber_baseChange_algEquiv (p := p)).toRingHom.toAlgebra
    IsScalarTower p.asIdeal.ResidueField (fiberBaseChange (B := B) (C := C) p) (p.asIdeal.Fiber C) := by
  let e : fiberBaseChange (B := B) (C := C) p ≃ₐ[p.asIdeal.ResidueField] p.asIdeal.Fiber C :=
    fiber_baseChange_algEquiv (p := p)
  let _ : Algebra (fiberBaseChange (B := B) (C := C) p) (p.asIdeal.Fiber C) := e.toRingHom.toAlgebra
  -- The comparison equivalence is an algebra equivalence over the residue field.
  exact IsScalarTower.of_algebraMap_eq' <|
    RingHom.ext fun x ↦ by
      change algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber C) x =
        e.toRingHom
          (algebraMap p.asIdeal.ResidueField (fiberBaseChange (B := B) (C := C) p) x)
      exact (e.commutes x).symm

/-- Helper for Lemma 15.41.7: geometric regularity of the composite fiber transfers across the
canonical cancellation equivalence to the fiber base change. -/
lemma fiber_baseChange_isGeometricallyRegular
    (p : PrimeSpectrum A)
    [Algebra.IsGeometricallyRegular p.asIdeal.ResidueField (p.asIdeal.Fiber C)] :
    Algebra.IsGeometricallyRegular p.asIdeal.ResidueField (fiberBaseChange (B := B) (C := C) p) := by
  let e : fiberBaseChange (B := B) (C := C) p ≃ₐ[p.asIdeal.ResidueField] p.asIdeal.Fiber C :=
    fiber_baseChange_algEquiv (p := p)
  let g' : fiberBaseChange (B := B) (C := C) p →+* p.asIdeal.Fiber C := e.toRingHom
  have hg' : g'.FaithfullyFlat := RingHom.FaithfullyFlat.of_bijective e.bijective
  let _ : Algebra (fiberBaseChange (B := B) (C := C) p) (p.asIdeal.Fiber C) := g'.toAlgebra
  have htower :
      IsScalarTower p.asIdeal.ResidueField (fiberBaseChange (B := B) (C := C) p) (p.asIdeal.Fiber C) := by
    simpa [g', e] using (fiber_baseChange_comparison_isScalarTower (p := p))
  let _ :
      IsScalarTower p.asIdeal.ResidueField (fiberBaseChange (B := B) (C := C) p) (p.asIdeal.Fiber C) :=
    htower
  -- Descend geometric regularity along the bijective comparison map.
  exact
    Algebra.isGeometricallyRegular_of_faithfullyFlat
      (k := p.asIdeal.ResidueField)
      (A := fiberBaseChange (B := B) (C := C) p)
      (B := p.asIdeal.Fiber C)
      hg'

end FiberComparison

end FiberBaseChange

/-- Helper for Lemma 15.41.7: for each prime `p`, geometric regularity of the composite fiber
descends to the fiber of `f` through the faithfully flat base-changed fiber map. -/
lemma fiber_isGeometricallyRegular_of_comp
    (hgf : (g.comp f).IsRegularRingMap) (hg : g.FaithfullyFlat) (p : PrimeSpectrum A) :
    let _ : Algebra A B := f.toAlgebra
    Algebra.IsGeometricallyRegular p.asIdeal.ResidueField (p.asIdeal.Fiber B) := by
  let _ : Algebra A B := f.toAlgebra
  let _ : Algebra B C := g.toAlgebra
  let _ : Algebra A C := (g.comp f).toAlgebra
  have htower : IsScalarTower A B C := by
    simpa using (comp_isScalarTower (f := f) (g := g))
  let _ : IsScalarTower A B C := htower
  let D := fiberBaseChange (A := A) (B := B) (C := C) p
  have hBC : (algebraMap B C).FaithfullyFlat := by
    -- Rewrite the owner hypothesis on `g` as a faithful-flatness statement for `algebraMap B C`.
    simpa [RingHom.algebraMap_toAlgebra] using hg
  have hDff : (algebraMap (p.asIdeal.Fiber B) D).FaithfullyFlat :=
    fiber_baseChange_faithfullyFlat (A := A) (B := B) (C := C) hBC p
  have hDGeom : Algebra.IsGeometricallyRegular p.asIdeal.ResidueField D := by
    let _ : Algebra.IsGeometricallyRegular p.asIdeal.ResidueField (p.asIdeal.Fiber C) :=
      hgf.isGeometricallyRegular_fiber p
    -- Move geometric regularity from the composite fiber to the base-changed fiber model.
    exact fiber_baseChange_isGeometricallyRegular (A := A) (B := B) (C := C) p
  let _ : Algebra.IsGeometricallyRegular p.asIdeal.ResidueField D := hDGeom
  let _ : IsScalarTower p.asIdeal.ResidueField (p.asIdeal.Fiber B) D :=
    fiber_baseChange_isScalarTower (A := A) (B := B) (C := C) p
  -- Descend geometric regularity along the faithfully flat map on fibers.
  exact
    (Algebra.isGeometricallyRegular_of_faithfullyFlat
      (k := p.asIdeal.ResidueField)
      (A := p.asIdeal.Fiber B)
      (B := D)
      hDff)

-- Proof sketch: first use Lemma `10.39.10` together with faithful flatness of `g` to descend
-- flatness from `g.comp f` to `f`. For each `p : Spec A`, base change `g` to `κ(p)`; the induced
-- map on the fibers of `f` and `g.comp f` stays faithfully flat. Since the fiber of `g.comp f`
-- over `p` is geometrically regular, Lemma `10.166.3` descends geometric regularity to the fiber
-- of `f` over `p`.
/-- Lemma 15.41.7: if `g.comp f : A →+* C` is a regular ring map and `g : B →+* C` is faithfully
flat, then `f : A →+* B` is a regular ring map. -/
@[stacks 07NT]
theorem of_comp_of_faithfullyFlat (hgf : (g.comp f).IsRegularRingMap) (hg : g.FaithfullyFlat) :
    f.IsRegularRingMap := by
  let _ : Algebra A B := f.toAlgebra
  let _ : Algebra B C := g.toAlgebra
  let _ : Algebra A C := (g.comp f).toAlgebra
  -- Build the regularity structure from the descended flatness and fiberwise geometric regularity.
  refine
    { toFlat := flat_of_comp_of_faithfullyFlat (f := f) (g := g) hgf.toFlat hg
      isGeometricallyRegular_fiber := ?_ }
  intro p
  -- Apply the fiberwise faithfully flat descent argument prime by prime.
  simpa using fiber_isGeometricallyRegular_of_comp (f := f) (g := g) hgf hg p

end

end RingHom.IsRegularRingMap
