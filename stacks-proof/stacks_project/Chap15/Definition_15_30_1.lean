import Mathlib
import stacks_project.Chap15.Definition_15_28_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open MonoidalCategory

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]

/- Domain triage:
* primary domain: Koszul complexes and regular sequences for finite families in commutative
  algebra;
* sampled owner API: `koszulComplexOn`, `HomologicalComplex.tensorObj`, `ρ_`,
  `HomologicalComplex.homologyMapIso`;
* layer split: `koszulComplexOn` is the `Fin`-family owner for the complex itself, and this file
  is the source-facing owner layer for the regularity predicates on finite families;
* primitive data vs derived API: the only new source-facing primitive here is the degree-one
  vanishing predicate `IsH1RegularOn`; `IsKoszulRegularSequence` and `IsH1RegularSequence` are the
  regular-module specializations derived from the module-valued owners.
-/

section ModuleRegularity

variable (M : Type u) [AddCommGroup M] [Module R M]

/-- Definition 15.30.1 (1): a finite family `f` is `M`-Koszul-regular if every positive homology
object of the Koszul complex on `f`, after tensoring with `M`, vanishes. -/
noncomputable abbrev IsKoszulRegularOn {r : ℕ} (f : Fin r → R) : Prop :=
  ∀ i : ℕ, 1 ≤ i →
    IsZero ((HomologicalComplex.tensorObj (koszulComplexOn f) ((ChainComplex.single₀ (ModuleCat R)).obj
      (ModuleCat.of R M))).homology i)

/-- Definition 15.30.1 (2): a finite family `f` is `M`-`H_1`-regular if the first homology object
of the Koszul complex on `f`, after tensoring with `M`, vanishes. -/
noncomputable def IsH1RegularOn {r : ℕ} (f : Fin r → R) : Prop :=
  IsZero ((HomologicalComplex.tensorObj (koszulComplexOn f) ((ChainComplex.single₀ (ModuleCat R)).obj
    (ModuleCat.of R M))).homology 1)

end ModuleRegularity

/-- Definition 15.30.1 (3): a finite family `f` is Koszul-regular if it is Koszul-regular on the
regular module `R`. -/
noncomputable abbrev IsKoszulRegularSequence {r : ℕ} (f : Fin r → R) : Prop :=
  IsKoszulRegularOn R f

/-- The ring-theoretic predicate `IsKoszulRegularSequence f` is equivalently the vanishing of all
positive homology objects of `koszulComplexOn f`. -/
theorem isKoszulRegularSequence_iff {r : ℕ} (f : Fin r → R) :
    IsKoszulRegularSequence f ↔
      ∀ i : ℕ, 1 ≤ i → IsZero ((koszulComplexOn f).homology i) := by
  let e :
      HomologicalComplex.tensorObj (koszulComplexOn f)
          ((ChainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R R)) ≅
        koszulComplexOn f :=
    ρ_ (koszulComplexOn f)
  constructor
  · intro h i hi
    exact (Iso.isZero_iff (HomologicalComplex.homologyMapIso e i)).mp (h i hi)
  · intro h i hi
    exact (Iso.isZero_iff (HomologicalComplex.homologyMapIso e i)).mpr (h i hi)

/-- Definition 15.30.1 (4): a finite family `f` is `H_1`-regular if it is `H_1`-regular on the
regular module `R`. -/
noncomputable abbrev IsH1RegularSequence {r : ℕ} (f : Fin r → R) : Prop :=
  IsH1RegularOn R f

/-- The ring-theoretic predicate `IsH1RegularSequence f` is equivalently the vanishing of the first
homology object of `koszulComplexOn f`. -/
theorem isH1RegularSequence_iff {r : ℕ} (f : Fin r → R) :
    IsH1RegularSequence f ↔ IsZero ((koszulComplexOn f).homology 1) := by
  let e :
      HomologicalComplex.tensorObj (koszulComplexOn f)
          ((ChainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R R)) ≅
        koszulComplexOn f :=
    ρ_ (koszulComplexOn f)
  simpa [IsH1RegularSequence, IsH1RegularOn] using
    (Iso.isZero_iff (HomologicalComplex.homologyMapIso e 1))

end RingTheory.Sequence
