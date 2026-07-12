import Mathlib
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import StacksProject_2024.Chap15.Definition_15_28_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open MonoidalCategory
open ModuleCat
open scoped KoszulComplex

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]

private abbrev koszulComplexOnTensorLeft (R : Type u) [CommRing R] (M : Type u)
    [AddCommGroup M] [Module R M] {r : ℕ} (f : Fin r → R) :
    ChainComplex (ModuleCat R) ℕ :=
  ((tensorLeft (of R M)).mapHomologicalComplex (ComplexShape.down ℕ)).obj (K^•(f))

/- Domain triage:
* primary domain: Koszul complexes and regular sequences for finite families in commutative
  algebra;
* sampled owner API: `K^•(-)`, `tensorLeft`, `Functor.mapHomologicalComplex`,
  `HomologicalComplex.homologyMapIso`;
* layer split: the notation `K^•(-)` is the `Fin`-family owner surface for the complex itself,
  and this file is the source-facing owner layer for the regularity predicates on finite
  families;
* primitive data vs derived API: the only new source-facing primitive here is the degree-one
  vanishing predicate `IsH1RegularOn`; `IsKoszulRegularSequence` and `IsH1RegularSequence` are the
  regular-module specializations derived from the module-valued owners.
-/

section ModuleRegularity

/-- Definition 15.30.1 (1): a finite family `f` is `M`-Koszul-regular if every positive homology
object of the Koszul complex on `f`, after tensoring with `M`, vanishes. -/
noncomputable abbrev IsKoszulRegularOn (M : Type u) [AddCommGroup M] [Module R M]
    {r : ℕ} (f : Fin r → R) : Prop :=
  ∀ i : ℕ, 1 ≤ i → CategoryTheory.Limits.IsZero ((koszulComplexOnTensorLeft R M f).homology i)

/-- Definition 15.30.1 (2): a finite family `f` is `M`-`H_1`-regular if the first homology object
of the Koszul complex on `f`, after tensoring with `M`, vanishes. -/
noncomputable def IsH1RegularOn (M : Type u) [AddCommGroup M] [Module R M]
    {r : ℕ} (f : Fin r → R) : Prop :=
  CategoryTheory.Limits.IsZero ((koszulComplexOnTensorLeft R M f).homology 1)

end ModuleRegularity

private theorem isZero_koszulComplexOnTensorLeft_homology_iff (R : Type u) [CommRing R]
    {r : ℕ} (f : Fin r → R) (i : ℕ) :
    CategoryTheory.Limits.IsZero ((koszulComplexOnTensorLeft R R f).homology i) ↔
      CategoryTheory.Limits.IsZero ((K^•(f)).homology i) := by
  have e : koszulComplexOnTensorLeft R R f ≅ K^•(f) := by
    exact ((NatIso.mapHomologicalComplex
      (MonoidalCategory.leftUnitorNatIso (ModuleCat R))
      (ComplexShape.down ℕ)).app (K^•(f)))
  exact Iso.isZero_iff (HomologicalComplex.homologyMapIso e i)

/-- Definition 15.30.1 (3): a finite family `f` is Koszul-regular if it is Koszul-regular on the
regular module `R`. -/
noncomputable abbrev IsKoszulRegularSequence {r : ℕ} (f : Fin r → R) : Prop :=
  IsKoszulRegularOn R f

/-- The ring-theoretic predicate `IsKoszulRegularSequence f` is equivalently the vanishing of all
positive homology objects of `K^•(f)`. -/
theorem isKoszulRegularSequence_iff {r : ℕ} (f : Fin r → R) :
    IsKoszulRegularSequence f ↔
      ∀ i : ℕ, 1 ≤ i → CategoryTheory.Limits.IsZero ((K^•(f)).homology i) := by
  constructor
  · intro h i hi
    exact (isZero_koszulComplexOnTensorLeft_homology_iff R f i).mp (h i hi)
  · intro h i hi
    exact (isZero_koszulComplexOnTensorLeft_homology_iff R f i).mpr (h i hi)

/-- Definition 15.30.1 (4): a finite family `f` is `H_1`-regular if it is `H_1`-regular on the
regular module `R`. -/
noncomputable abbrev IsH1RegularSequence {r : ℕ} (f : Fin r → R) : Prop :=
  IsH1RegularOn R f

/-- The ring-theoretic predicate `IsH1RegularSequence f` is equivalently the vanishing of the first
homology object of `K^•(f)`. -/
theorem isH1RegularSequence_iff {r : ℕ} (f : Fin r → R) :
    IsH1RegularSequence f ↔ CategoryTheory.Limits.IsZero ((K^•(f)).homology 1) := by
  simpa [IsH1RegularSequence, IsH1RegularOn] using
    isZero_koszulComplexOnTensorLeft_homology_iff R f 1

end RingTheory.Sequence
