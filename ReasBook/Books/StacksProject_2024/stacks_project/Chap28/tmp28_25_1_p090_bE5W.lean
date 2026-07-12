import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite
open AlgebraicGeometry
open PrimeSpectrum
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {A : Type u} [CommRing A]

-- Semantic recall: `lean_leansearch` surfaced `ModuleCat.tilde` and the affine `Spec`/`Γ` API; the
-- concrete owner here is therefore the actual sheaf of `A`-modules
-- `AlgebraicGeometry.modulesSpecToSheaf.obj (AlgebraicGeometry.tilde M)` over `Spec A`, together
-- with a chosen finite basic-open cover coming from `I.FG`.

/-- The canonical sheaf of `A`-modules attached to `\widetilde M` on `Spec(A)`. -/
private noncomputable def tildeSheaf (M : ModuleCat A) :
    TopCat.Sheaf (ModuleCat (CommRingCat.of A)) (Spec (.of A)) :=
  AlgebraicGeometry.modulesSpecToSheaf.obj (AlgebraicGeometry.tilde M)

private noncomputable def tildePresheaf (M : ModuleCat A) :
    TopCat.Presheaf (ModuleCat (CommRingCat.of A)) (Spec (.of A)) :=
  (tildeSheaf M).1

/-- The open complement `Spec(A) \ V(I)` as an open subset of `Spec(A)`. -/
def idealComplementOpens (I : Ideal A) : (Spec (.of A)).Opens :=
  ⟨(PrimeSpectrum.zeroLocus (I : Set A))ᶜ, (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩

/-- A chosen finite generating set for a finitely generated ideal, repackaged as a `Fin`-indexed
family. This is internal scaffolding for the finite basic-open cover used in the comparison map. -/
private noncomputable def idealGeneratorsData (I : Ideal A) (hI : I.FG) :
    Σ r : ℕ, Fin r → A := by
  classical
  let s : Finset A := Classical.choose hI
  refine ⟨s.card, fun i ↦ (s.equivFin.symm i : A)⟩

/-- The number of chosen generators in `idealGeneratorsData`. -/
private noncomputable abbrev idealGeneratorCount (I : Ideal A) (hI : I.FG) : ℕ :=
  (idealGeneratorsData I hI).1

/-- The chosen `Fin`-indexed generator family attached to `idealGeneratorsData`. -/
private noncomputable abbrev idealGenerators (I : Ideal A) (hI : I.FG) :
    Fin (idealGeneratorCount I hI) → A :=
  (idealGeneratorsData I hI).2

/-- Each chosen generator belongs to the ideal it generates. -/
private theorem idealGenerators_mem (I : Ideal A) (hI : I.FG) (i : Fin (idealGeneratorCount I hI)) :
    idealGenerators I hI i ∈ I := sorry

/-- The chosen generator family spans the given finitely generated ideal. -/
private theorem span_idealGenerators (I : Ideal A) (hI : I.FG) :
    Ideal.span (Set.range (idealGenerators I hI)) = I := sorry

/-- The chosen basic-open cover attached to a finitely generated ideal. -/
private noncomputable def idealGeneratorBasicOpen (I : Ideal A) (hI : I.FG)
    (i : Fin (idealGeneratorCount I hI)) :
    (Spec (.of A)).Opens :=
  PrimeSpectrum.basicOpen (idealGenerators I hI i)

/-- Each chosen basic open lies in `Spec(A) \ V(I)`. -/
private theorem idealGeneratorBasicOpen_le_complement
    (I : Ideal A) (hI : I.FG) (i : Fin (idealGeneratorCount I hI)) :
    idealGeneratorBasicOpen I hI i ≤ idealComplementOpens I := sorry

/-- The chosen basic opens cover `Spec(A) \ V(I)`. -/
private theorem idealComplementOpens_le_iSup_idealGeneratorBasicOpen
    (I : Ideal A) (hI : I.FG) :
    idealComplementOpens I ≤ iSup (idealGeneratorBasicOpen I hI) := sorry

private def idealComplementSectionType (I : Ideal A) (M : ModuleCat A) : Type u :=
  ((tildePresheaf M).obj (Opposite.op (idealComplementOpens I)) : Type u)

/-- The additive group of sections of `\widetilde M` on `Spec(A) \ V(I)`. -/
noncomputable abbrev idealComplementTildeSections (I : Ideal A) (M : ModuleCat A) :
    AddCommGrpCat :=
  AddCommGrpCat.of (idealComplementSectionType I M)

/-- The `n`-th stage `Hom_A(I^n, M)` of the direct system, viewed as an additive group. -/
private abbrev idealPowerHomType (I : Ideal A) (M : ModuleCat A) (n : ℕ) :=
  ((I ^ n : Ideal A) →ₗ[A] M)

noncomputable abbrev idealPowerHomStage (I : Ideal A) (M : ModuleCat A) (n : ℕ) :
    AddCommGrpCat :=

end AlgebraicGeometry.Scheme.Modules
