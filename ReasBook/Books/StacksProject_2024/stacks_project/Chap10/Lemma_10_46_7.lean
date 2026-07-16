import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap10.Definition_10_32_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_46_4
import StacksProject_2024.stacks_project.Chap10.Lemma_10_46_8

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum
open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {p : ℕ} [Fact p.Prime] (f : R →+* S)

namespace RingHom

/-- Source-facing generator predicate for Lemma 10.46.7: `S` is generated as an `R`-algebra by
elements `x` such that some positive `p^n`-th power of `x` and the corresponding scalar multiple
`p^n • x` both lie in the image of `f`. -/
def IsGeneratedByPrimePowerAndScalarImage (f : R →+* S) (p : ℕ) [Fact p.Prime] : Prop :=
  let _ : Algebra R S := f.toAlgebra
  Algebra.adjoin R
      {x : S |
        ∃ n : ℕ, 0 < n ∧ x ^ (p ^ n) ∈ f.range ∧ p ^ n • x ∈ f.range} = ⊤

end RingHom

/- The homeomorphism owner theorem used below is the canonical theorem
`PrimeSpectrum.isHomeomorph_comap`. -/
recall PrimeSpectrum.isHomeomorph_comap

-- Proof sketch: pass the displayed generation condition to each residue-field map
-- `κ(q ∩ R) → κ(q)`. Lemma `10.46.6` then gives exactly the source-facing alternative:
-- either the residue-field map is surjective, or the source has characteristic `p` and the target
-- extension is purely inseparable.
/-- Lemma 10.46.7, source-facing residue-field clause: the generator predicate above implies the
residue-field criterion from Lemma `10.46.6` at every prime of `S`. -/
theorem residueFieldMapsSurjectiveOrCharPPurelyInseparable_of_isGeneratedByPrimePowerAndScalarImage
    (hgen : f.IsGeneratedByPrimePowerAndScalarImage p)
    (q : PrimeSpectrum S) :
    let p' : PrimeSpectrum R := comap f q
    let fκ := Ideal.ResidueField.map p'.asIdeal q.asIdeal f rfl
    let _ : Algebra p'.asIdeal.ResidueField q.asIdeal.ResidueField := fκ.toAlgebra
    Function.Surjective fκ ∨
      ringChar p'.asIdeal.ResidueField = p ∧
        IsPurelyInseparable p'.asIdeal.ResidueField q.asIdeal.ResidueField := by
  sorry

-- Proof sketch: apply the source-facing residue-field clause above at each prime `q : Spec(S)`
-- and then package the purely inseparable branch into the owner predicate
-- `RingHom.HasPurelyInseparableResidueFieldExtensions`.
private theorem hasPurelyInseparableResidueFieldExtensions_of_residueFieldCriterion
    (hres : ∀ q : PrimeSpectrum S,
      let p' : PrimeSpectrum R := comap f q
      let fκ := Ideal.ResidueField.map p'.asIdeal q.asIdeal f rfl
      let _ : Algebra p'.asIdeal.ResidueField q.asIdeal.ResidueField := fκ.toAlgebra
      Function.Surjective fκ ∨
        ringChar p'.asIdeal.ResidueField = p ∧
          IsPurelyInseparable p'.asIdeal.ResidueField q.asIdeal.ResidueField) :
    f.HasPurelyInseparableResidueFieldExtensions := by
  sorry

/-- Lemma 10.46.7, bridge/view form: the generator predicate implies the owner predicate
`RingHom.HasPurelyInseparableResidueFieldExtensions`. -/
theorem hasPurelyInseparableResidueFieldExtensions_of_isGeneratedByPrimePowerAndScalarImage
    (hgen : f.IsGeneratedByPrimePowerAndScalarImage p) :
    f.HasPurelyInseparableResidueFieldExtensions := by
  exact
    hasPurelyInseparableResidueFieldExtensions_of_residueFieldCriterion
      f
      (residueFieldMapsSurjectiveOrCharPPurelyInseparable_of_isGeneratedByPrimePowerAndScalarImage
        f hgen)

-- Proof sketch: the same generators show that every element of `S` has some positive power in the
-- image of `f`, which is the source-facing bridge needed for `PrimeSpectrum.isHomeomorph_comap`.
/-- Under the generation hypothesis of Lemma 10.46.7, every element of `S` has a positive power in
the image of `f`. -/
theorem exists_pow_mem_range_of_isGeneratedByPrimePowerAndScalarImage
    (hgen : f.IsGeneratedByPrimePowerAndScalarImage p) :
    ∀ x : S, ∃ n > 0, x ^ n ∈ f.range := by
  sorry

-- Proof sketch: combine the positive-power-in-range bridge above with the locally nilpotent kernel
-- hypothesis and apply the canonical theorem `PrimeSpectrum.isHomeomorph_comap`.
/-- Lemma 10.46.7, homeomorphism clause: if in addition `ker f` is locally nilpotent, then
`Spec(S) → Spec(R)` is a homeomorphism. -/
theorem isHomeomorph_comap_of_isGeneratedByPrimePowerAndScalarImage
    (hgen : f.IsGeneratedByPrimePowerAndScalarImage p)
    (hker : (RingHom.ker f).IsLocallyNilpotent) :
    IsHomeomorph (comap f) := by
  exact PrimeSpectrum.isHomeomorph_comap f
    (exists_pow_mem_range_of_isGeneratedByPrimePowerAndScalarImage f hgen)
    (by simpa [Ideal.IsLocallyNilpotent] using hker)

variable {R' : Type w} [CommRing R'] [Algebra R R']

/-- Lemma 10.46.7, base-change generation clause: for every ring map `R → R'`, the canonical
base-changed map `R' → R' ⊗[R] S` satisfies the same generation hypothesis. -/
theorem isGeneratedByPrimePowerAndScalarImage_baseChange_of_isGeneratedByPrimePowerAndScalarImage
    (hgen : f.IsGeneratedByPrimePowerAndScalarImage p) :
    let _ : Algebra R S := f.toAlgebra
    let f' : R' →+* R' ⊗[R] S := algebraMap R' (R' ⊗[R] S)
    f'.IsGeneratedByPrimePowerAndScalarImage p := by
  sorry

-- Proof sketch: combine the base-change generation clause above with stability of locally
-- nilpotent kernels under arbitrary base change.
/-- Lemma 10.46.7, source-facing full base-change clause: for every ring map `R → R'`, if `ker f`
is locally nilpotent, then the canonical base-changed map `R' → R' ⊗[R] S` satisfies the same
generation hypothesis and has locally nilpotent kernel. -/
theorem isGeneratedByPrimePowerAndScalarImage_and_ker_baseChange_isLocallyNilpotent_of_isGeneratedByPrimePowerAndScalarImage
    (hgen : f.IsGeneratedByPrimePowerAndScalarImage p)
    (hker : (RingHom.ker f).IsLocallyNilpotent) :
    let _ : Algebra R S := f.toAlgebra
    let f' : R' →+* R' ⊗[R] S := algebraMap R' (R' ⊗[R] S)
    f'.IsGeneratedByPrimePowerAndScalarImage p ∧
      (RingHom.ker f').IsLocallyNilpotent := by
  sorry

end
