import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open PrimeSpectrum

universe u v w

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S]

/-- A ring homomorphism induces purely inseparable extensions on all residue fields. -/
def RingHom.HasPurelyInseparableResidueFieldExtensions (f : R →+* S) : Prop :=
  ∀ q : PrimeSpectrum S,
    let p : PrimeSpectrum R := comap f q
    let fκ := Ideal.ResidueField.map p.asIdeal q.asIdeal f rfl
    let _ : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField := fκ.toAlgebra
    IsPurelyInseparable p.asIdeal.ResidueField q.asIdeal.ResidueField

variable [Algebra R S]

local notation "f" => algebraMap R S

/-
Layering for this item:
* source-facing: the base-change stability of injectivity on `Spec` together with purely
  inseparable residue-field extensions;
* core/canonical owner: the spectral map `PrimeSpectrum.comap f` and the predicate
  `RingHom.HasPurelyInseparableResidueFieldExtensions f`;
* bridge/view: the induced residue-field maps
  `Ideal.ResidueField.map p.asIdeal q.asIdeal f rfl`.
-/

-- Proof sketch: inspect each fiber of `Spec (R' ⊗[R] S) → Spec R'` via
-- `PrimeSpectrum.preimageHomeomorphFiber`. For a prime `p'` over `p`, the fiber ring of the
-- base-changed map is `κ(p') ⊗[κ(p)] (κ(p) ⊗[R] S)`. The original injectivity and purely
-- inseparable residue-field hypotheses imply that `κ(p) → κ(r)` has singleton spectrum and is
-- purely inseparable for the unique prime `r` of the original fiber. Purely inseparable base
-- change preserves these two properties, so the new fiber is again a singleton and its residue
-- extensions remain purely inseparable.
/-- Lemma 10.46.8: if `R → S` induces an injective map on prime spectra and purely inseparable
extensions on residue fields, then after any base change `R → R'` the canonical map
`R' → R' ⊗[R] S` has the same two properties. -/
theorem baseChange_injective_comap_and_hasPurelyInseparableResidueFieldExtensions
    (R' : Type w) [CommRing R'] [Algebra R R']
    (hinj : Function.Injective (comap f))
    (hres : RingHom.HasPurelyInseparableResidueFieldExtensions f) :
    let f' : R' →+* R' ⊗[R] S := algebraMap R' (R' ⊗[R] S)
    Function.Injective (comap f') ∧ f'.HasPurelyInseparableResidueFieldExtensions := sorry

end
