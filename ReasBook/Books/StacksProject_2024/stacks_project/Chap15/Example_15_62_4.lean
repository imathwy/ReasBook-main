import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.CochainComplexOpposite
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import StacksProject_2024.Chap12.Definition_12_24_9
import StacksProject_2024.Chap12.Definition_12_24_5
import StacksProject_2024.Chap12.Lemma_12_24_11
import StacksProject_2024.Chap12.Lemma_12_25_1
import StacksProject_2024.Chap13.Definition_13_11_3
import StacksProject_2024.Chap13.Lemma_13_19_3
import StacksProject_2024.Chap13.Situation_13_15_1
import StacksProject_2024.Chap15.Definition_15_59_13
import StacksProject_2024.Chap15.Lemma_15_59_14

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ModuleCat.MonoidalCategory
open scoped DerivedTensorProduct

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace StacksProject

section

variable {R : Type u} [CommRing R]
variable [LocallySmall.{0} (ModuleCat.{u} R)]
variable [WellPowered.{0} (ModuleCat.{u} R)]

/-
Domain-style sampling for Example `15.62.4`.
- primary domain: cohomological spectral sequences in the bounded-above derived category of
  `R`-modules and their convergence to derived tensor-product cohomology;
- sampled owner/canonical declarations in the same domain:
  `CategoryTheory.CohomologicalSpectralSequence`,
  `CategoryTheory.FilteredComplex.convergesToCohomology`,
  `CategoryTheory.firstDoubleComplexFilteredComplex`,
  `CategoryTheory.secondDoubleComplexFilteredComplex`,
  `CategoryTheory.derivedTensorProduct`,
  `CategoryTheory.DerivedCategory.homologyFunctor`;
- best owner abstraction: a cohomological spectral sequence `E` with source-facing Prop-valued
  predicates recording the right or left `E₂`-page formula together with the Chapter `12`
  convergence owner `F.convergesToCohomology E` for some associated filtered complex `F`;
- primitive data: `E : CohomologicalSpectralSequence ModR 0` and the existential filtered-complex
  witness `F : FilteredComplex ModR` occurring in the convergence clause;
- derived API: the right and left `E₂`-page identifications and the common abutment
  identification with `H^*(K ⊗[R]^L L)`;
- source/core/bridge triage:
  `source-facing`: `IsRightCohomologyDerivedTensorSpectralSequence` and
    `IsLeftCohomologyDerivedTensorSpectralSequence`;
  `core/canonical`: `CohomologicalSpectralSequence`, `FilteredComplex.convergesToCohomology`,
    `firstDoubleComplexFilteredComplex`, `secondDoubleComplexFilteredComplex`,
    `DerivedCategory.homologyFunctor`, and `derivedTensorProduct`;
  `bridge/view`: the local page-two and abutment abbreviations together with the shared internal
    convergence clause used to state the source-facing predicates concisely.
-/
local notation "ModR" => ModuleCat R
local notation "DModMinus" => boundedAboveDerivedCategory ModR
local notation "H" => DerivedCategory.homologyFunctor ModR
local notation "single₀" => DerivedCategory.singleFunctor ModR (0 : ℤ)
local notation "singleCpx₀" => CochainComplex.singleFunctor ModR (0 : ℤ)

/-- The abutment object `H^n(K^• \otimes_R^{\mathbf L} L^•)`. -/
private abbrev derivedTensorCohomologyAbutment
    (K L : DModMinus) (n : ℤ) : ModR :=
  (H n).obj (K.obj ⊗[R]^L L.obj)

/-- The right-hand `E₂`-term `H^p(K^• \otimes_R^{\mathbf L} H^q(L^•))`. -/
private abbrev rightDerivedTensorPageTwo
    (K L : DModMinus) (p q : ℤ) : ModR :=
  (H p).obj (K.obj ⊗[R]^L ((single₀).obj ((H q).obj L.obj)))

/-- The left-hand `E₂`-term `H^p(H^q(K^•) \otimes_R^{\mathbf L} L^•)`. -/
private abbrev leftDerivedTensorPageTwo
    (K L : DModMinus) (p q : ℤ) : ModR :=
  (H p).obj (((single₀).obj ((H q).obj K.obj)) ⊗[R]^L L.obj)

/-- Internal bridge: a cohomological spectral sequence converges to
`H^*(K^• \otimes_R^{\mathbf L} L^•)` if it is associated to a filtered complex whose cohomology
identifies with that of the derived tensor product and which satisfies the Chapter `12`
convergence owner. -/
private def convergesToDerivedTensorCohomology
    (E : CohomologicalSpectralSequence ModR 0) (K L : DModMinus) : Prop :=
  ∃ (F : FilteredComplex ModR) (_ : IsAssociatedToFilteredComplex F E),
    F.convergesToCohomology E ∧
      ∀ n : ℤ,
        Nonempty (F.underlying.homology n ≅ derivedTensorCohomologyAbutment K L n)

/-- Helper for Example 15.62.4: only finitely many entries on each antidiagonal of a cohomological
double complex are allowed to be nonzero. -/
private def doubleComplexHasFiniteAntidiagonalSupport
    (K : HomologicalComplex₂ ModR (ComplexShape.up ℤ) (ComplexShape.up ℤ)) : Prop :=
  ∀ n : ℤ, { p : ℤ | ¬ Limits.IsZero ((K.X p).X (n - p)) }.Finite

/-- Helper for Example 15.62.4: the horizontal indices retained by a tail filtration stage. -/
private abbrev double_complex_tail_indices (p : ℤ) := { i : ℤ // p ≤ i }

/-- Helper for Example 15.62.4: the degree-`n`, stage-`p` map for the first filtration on the
total complex of a cohomological double complex. -/
private noncomputable def firstDoubleComplexFiltrationMap
    (K : HomologicalComplex₂ ModR (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (n p : ℤ) :
    ∐ (fun i : double_complex_tail_indices p ↦ (K.X i.1).X (n - i.1)) ⟶ (Tot(K)).X n :=
  Limits.Sigma.desc fun i : double_complex_tail_indices p ↦
    K.ιTotal (ComplexShape.up ℤ) i.1 (n - i.1) n (by simp)

/-- Helper for Example 15.62.4: the degree-`n`, stage-`p` map for the second filtration on the
total complex of a cohomological double complex. -/
private noncomputable def secondDoubleComplexFiltrationMap
    (K : HomologicalComplex₂ ModR (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (n p : ℤ) :
    ∐ (fun i : double_complex_tail_indices p ↦ (K.X (n - i.1)).X i.1) ⟶ (Tot(K)).X n :=
  Limits.Sigma.desc fun i : double_complex_tail_indices p ↦
    K.ιTotal (ComplexShape.up ℤ) (n - i.1) i.1 n (by simp)

/-- Helper for Example 15.62.4: the `p`-th stage of the first filtration on `Tot(K)^n` is the
image of the tail-summand map keeping horizontal degrees at least `p`. -/
private noncomputable abbrev firstDoubleComplexFiltrationStage
    (K : HomologicalComplex₂ ModR (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (n p : ℤ) :
    Subobject ((Tot(K)).X n) :=
  imageSubobject (firstDoubleComplexFiltrationMap K n p)

/-- Helper for Example 15.62.4: the `p`-th stage of the second filtration on `Tot(K)^n` is the
image of the tail-summand map keeping vertical degrees at least `p`. -/
private noncomputable abbrev secondDoubleComplexFiltrationStage
    (K : HomologicalComplex₂ ModR (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (n p : ℤ) :
    Subobject ((Tot(K)).X n) :=
  imageSubobject (secondDoubleComplexFiltrationMap K n p)

/-- Helper for Example 15.62.4: enlarging the cutoff index for the first filtration removes
summands, so the corresponding image subobject can only decrease. -/
private theorem first_filtration_stage_mono
    (K : HomologicalComplex₂ ModR (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (n p q : ℤ) (hpq : p ≤ q) :
    firstDoubleComplexFiltrationStage K n q ≤ firstDoubleComplexFiltrationStage K n p := by
  let ι :
      ∐ (fun i : double_complex_tail_indices q ↦ (K.X i.1).X (n - i.1)) ⟶
        ∐ (fun i : double_complex_tail_indices p ↦ (K.X i.1).X (n - i.1)) :=
    Limits.Sigma.map' (fun i : double_complex_tail_indices q ↦
        (⟨i.1, hpq.trans i.2⟩ : double_complex_tail_indices p))
      (fun _ ↦ 𝟙 _)
  have hcomp :
      ι ≫ firstDoubleComplexFiltrationMap K n p = firstDoubleComplexFiltrationMap K n q := by
    apply Limits.Sigma.hom_ext
    intro i
    cases i with
    | mk i hi =>
      change K.ιTotal (ComplexShape.up ℤ) i (n - i) n (by simp) =
        K.ιTotal (ComplexShape.up ℤ) i (n - i) n (by simp)
      simp
  simpa [firstDoubleComplexFiltrationStage, hcomp] using
    (Limits.imageSubobject_comp_le ι (firstDoubleComplexFiltrationMap K n p))

/-- Helper for Example 15.62.4: enlarging the cutoff index for the second filtration likewise
removes summands, so the corresponding image subobject can only decrease. -/
private theorem second_filtration_stage_mono
    (K : HomologicalComplex₂ ModR (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (n p q : ℤ) (hpq : p ≤ q) :
    secondDoubleComplexFiltrationStage K n q ≤ secondDoubleComplexFiltrationStage K n p := by
  let ι :
      ∐ (fun i : double_complex_tail_indices q ↦ (K.X (n - i.1)).X i.1) ⟶
        ∐ (fun i : double_complex_tail_indices p ↦ (K.X (n - i.1)).X i.1) :=
    Limits.Sigma.map' (fun i : double_complex_tail_indices q ↦
        (⟨i.1, hpq.trans i.2⟩ : double_complex_tail_indices p))
      (fun _ ↦ 𝟙 _)
  have hcomp :
      ι ≫ secondDoubleComplexFiltrationMap K n p = secondDoubleComplexFiltrationMap K n q := by
    apply Limits.Sigma.hom_ext
    intro i
    cases i with
    | mk i hi =>
      change K.ιTotal (ComplexShape.up ℤ) (n - i) i n (by simp) =
        K.ιTotal (ComplexShape.up ℤ) (n - i) i n (by simp)
      simp
  simpa [secondDoubleComplexFiltrationStage, hcomp] using
    (Limits.imageSubobject_comp_le ι (secondDoubleComplexFiltrationMap K n p))

/-- Helper for Example 15.62.4: the filtered object in total degree `n` for the first filtration
on a cohomological double complex. -/
private noncomputable def firstDoubleComplexFilteredObject
    (K : HomologicalComplex₂ ModR (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (n : ℤ) :
    FilteredObject ModR where
  obj := (Tot(K)).X n
  filtration :=
    { toFun := firstDoubleComplexFiltrationStage K n
      monotone' := by
        intro p q hpq
        exact first_filtration_stage_mono K n q p hpq }

/-- Helper for Example 15.62.4: the filtered object in total degree `n` for the second
filtration on a cohomological double complex. -/
private noncomputable def secondDoubleComplexFilteredObject
    (K : HomologicalComplex₂ ModR (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (n : ℤ) :
    FilteredObject ModR where
  obj := (Tot(K)).X n
  filtration :=
    { toFun := secondDoubleComplexFiltrationStage K n
      monotone' := by
        intro p q hpq
        exact second_filtration_stage_mono K n q p hpq }

/-- Helper for Example 15.62.4: the domain-level tail map for the first filtration intertwines
with the total differential in consecutive degrees. -/
private noncomputable def firstDoubleComplexFiltrationTransition
    (K : HomologicalComplex₂ ModR (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (n p : ℤ) :
    ∐ (fun i : double_complex_tail_indices p ↦ (K.X i.1).X (n - i.1)) ⟶
      ∐ (fun i : double_complex_tail_indices p ↦ (K.X i.1).X (n + 1 - i.1)) :=
  Limits.Sigma.desc fun i : double_complex_tail_indices p ↦
    let i' : double_complex_tail_indices p := ⟨i.1, i.2⟩
    let i1' : double_complex_tail_indices p := ⟨i.1 + 1, by omega⟩
    ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (i.1, n - i.1) •
        ((K.d i.1 (i.1 + 1)).f (n - i.1) ≫ Sigma.ι _ i1') +
      ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (i.1, n - i.1) •
        ((K.X i.1).d (n - i.1) (n - i.1 + 1) ≫ Sigma.ι _ i')

/-- Helper for Example 15.62.4: the first tail-transition map composes with the next-stage tail
inclusion to the total differential on the current tail inclusion. -/
private theorem firstDoubleComplexFiltrationTransition_comp
    (K : HomologicalComplex₂ ModR (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (n p : ℤ) :
    firstDoubleComplexFiltrationTransition K n p ≫ firstDoubleComplexFiltrationMap K (n + 1) p =
      firstDoubleComplexFiltrationMap K n p ≫ (Tot(K)).d n (n + 1) := by
  apply Limits.Sigma.hom_ext
  intro i
  cases i with
  | mk i hi =>
    simp [firstDoubleComplexFiltrationTransition, firstDoubleComplexFiltrationMap,
      HomologicalComplex₂.total, Category.assoc, Preadditive.add_comp,
      HomologicalComplex₂.d₁_eq, HomologicalComplex₂.d₂_eq]

/-- Helper for Example 15.62.4: the total differential of a cohomological double complex preserves
the first tail filtration. -/
private theorem firstDoubleComplexFilteredComplex_preserves
    (K : HomologicalComplex₂ ModR (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (i j : ℤ) :
    ∀ p : ℤ,
      ((firstDoubleComplexFilteredObject K j).filtration p).Factors
        (((firstDoubleComplexFilteredObject K i).filtration p).arrow ≫ (Tot(K)).d i j) := by
  intro p
  by_cases hij : (ComplexShape.up ℤ).Rel i j
  · have hj : j = i + 1 := by simpa [ComplexShape.up, eq_comm] using hij
    subst hj
    let T : Subobject ((Tot(K)).X (i + 1)) := firstDoubleComplexFiltrationStage K (i + 1) p
    have hT :
        T.Factors (firstDoubleComplexFiltrationMap K i p ≫ (Tot(K)).d i (i + 1)) := by
      refine ⟨firstDoubleComplexFiltrationTransition K i p ≫
          factorThruImageSubobject (firstDoubleComplexFiltrationMap K (i + 1) p), ?_⟩
      simpa [T, Category.assoc] using firstDoubleComplexFiltrationTransition_comp K i p
    let P : Subobject ((Tot(K)).X i) := (Subobject.pullback ((Tot(K)).d i (i + 1))).obj T
    have hP : P.Factors (firstDoubleComplexFiltrationMap K i p) := by
      rw [show P = (Subobject.pullback ((Tot(K)).d i (i + 1))).obj T by rfl]
      rw [pullback_factors_iff]
      exact hT
    have hle :
        firstDoubleComplexFiltrationStage K i p ≤ P := by
      exact Subobject.le_of_factors hP
    rw [show P = (Subobject.pullback ((Tot(K)).d i (i + 1))).obj T by rfl] at hle
    rw [pullback_factors_iff]
    exact
      Subobject.factors_of_le
        (((firstDoubleComplexFilteredObject K i).filtration p).arrow) hle
        (Subobject.factors_self _)
  · have hd : (Tot(K)).d i j = 0 := (Tot(K)).shape i j hij
    rw [hd, Category.comp_zero]
    exact Subobject.factors_zero _

/-- Helper for Example 15.62.4: the domain-level tail map for the second filtration intertwines
with the total differential in consecutive degrees. -/
private noncomputable def secondDoubleComplexFiltrationTransition
    (K : HomologicalComplex₂ ModR (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (n p : ℤ) :
    ∐ (fun i : double_complex_tail_indices p ↦ (K.X (n - i.1)).X i.1) ⟶
      ∐ (fun i : double_complex_tail_indices p ↦ (K.X (n + 1 - i.1)).X i.1) :=
  Limits.Sigma.desc fun i : double_complex_tail_indices p ↦
    let i' : double_complex_tail_indices p := ⟨i.1, i.2⟩
    let i1' : double_complex_tail_indices p := ⟨i.1 + 1, by omega⟩
    ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (n - i.1, i.1) •
        ((K.d (n - i.1) (n - i.1 + 1)).f i.1 ≫ Sigma.ι _ i') +
      ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (n - i.1, i.1) •
        ((K.X (n - i.1)).d i.1 (i.1 + 1) ≫ Sigma.ι _ i1')

/-- Helper for Example 15.62.4: the second tail-transition map composes with the next-stage tail
inclusion to the total differential on the current tail inclusion. -/
private theorem secondDoubleComplexFiltrationTransition_comp
    (K : HomologicalComplex₂ ModR (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (n p : ℤ) :
    secondDoubleComplexFiltrationTransition K n p ≫ secondDoubleComplexFiltrationMap K (n + 1) p =
      secondDoubleComplexFiltrationMap K n p ≫ (Tot(K)).d n (n + 1) := by
  apply Limits.Sigma.hom_ext
  intro i
  cases i with
  | mk i hi =>
    simp [secondDoubleComplexFiltrationTransition, secondDoubleComplexFiltrationMap,
      HomologicalComplex₂.total, Category.assoc, Preadditive.add_comp,
      HomologicalComplex₂.d₁_eq, HomologicalComplex₂.d₂_eq]

/-- Helper for Example 15.62.4: the total differential of a cohomological double complex preserves
the second tail filtration. -/
private theorem secondDoubleComplexFilteredComplex_preserves
    (K : HomologicalComplex₂ ModR (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (i j : ℤ) :
    ∀ p : ℤ,
      ((secondDoubleComplexFilteredObject K j).filtration p).Factors
        (((secondDoubleComplexFilteredObject K i).filtration p).arrow ≫ (Tot(K)).d i j) := by
  intro p
  by_cases hij : (ComplexShape.up ℤ).Rel i j
  · have hj : j = i + 1 := by simpa [ComplexShape.up, eq_comm] using hij
    subst hj
    let T : Subobject ((Tot(K)).X (i + 1)) := secondDoubleComplexFiltrationStage K (i + 1) p
    have hT :
        T.Factors (secondDoubleComplexFiltrationMap K i p ≫ (Tot(K)).d i (i + 1)) := by
      refine ⟨secondDoubleComplexFiltrationTransition K i p ≫
          factorThruImageSubobject (secondDoubleComplexFiltrationMap K (i + 1) p), ?_⟩
      simpa [T, Category.assoc] using secondDoubleComplexFiltrationTransition_comp K i p
    let P : Subobject ((Tot(K)).X i) := (Subobject.pullback ((Tot(K)).d i (i + 1))).obj T
    have hP : P.Factors (secondDoubleComplexFiltrationMap K i p) := by
      rw [show P = (Subobject.pullback ((Tot(K)).d i (i + 1))).obj T by rfl]
      rw [pullback_factors_iff]
      exact hT
    have hle :
        secondDoubleComplexFiltrationStage K i p ≤ P := by
      exact Subobject.le_of_factors hP
    rw [show P = (Subobject.pullback ((Tot(K)).d i (i + 1))).obj T by rfl] at hle
    rw [pullback_factors_iff]
    exact
      Subobject.factors_of_le
        (((secondDoubleComplexFilteredObject K i).filtration p).arrow) hle
        (Subobject.factors_self _)
  · have hd : (Tot(K)).d i j = 0 := (Tot(K)).shape i j hij
    rw [hd, Category.comp_zero]
    exact Subobject.factors_zero _

/-- Helper for Example 15.62.4: the filtered complex on the total complex of a bicomplex coming
from the first horizontal-tail filtration. -/
private noncomputable def firstDoubleComplexFilteredComplex
    (K : HomologicalComplex₂ ModR (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] :
    FilteredComplex ModR :=
  { X := firstDoubleComplexFilteredObject K
    d i j :=
      { hom := (Tot(K)).d i j
        preserves := firstDoubleComplexFilteredComplex_preserves K i j }
    shape i j hij := by
      exact FilteredObject.forget.map_injective ((Tot(K)).shape i j hij)
    d_comp_d' i j k hij hjk := by
      exact FilteredObject.forget.map_injective ((Tot(K)).d_comp_d' i j k hij hjk) }

/-- Helper for Example 15.62.4: the filtered complex on the total complex of a bicomplex coming
from the second vertical-tail filtration. -/
private noncomputable def secondDoubleComplexFilteredComplex
    (K : HomologicalComplex₂ ModR (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] :
    FilteredComplex ModR :=
  { X := secondDoubleComplexFilteredObject K
    d i j :=
      { hom := (Tot(K)).d i j
        preserves := secondDoubleComplexFilteredComplex_preserves K i j }
    shape i j hij := by
      exact FilteredObject.forget.map_injective ((Tot(K)).shape i j hij)
    d_comp_d' i j k hij hjk := by
      exact FilteredObject.forget.map_injective ((Tot(K)).d_comp_d' i j k hij hjk) }

/-- The first spectral sequence of Example `15.62.4`: its `E₂`-page is
`H^p(K^• \otimes_R^{\mathbf L} H^q(L^•))`, and it converges to
`H^{p+q}(K^• \otimes_R^{\mathbf L} L^•)`. -/
def IsRightCohomologyDerivedTensorSpectralSequence
    (E : CohomologicalSpectralSequence ModR 0) (K L : DModMinus) : Prop :=
  (∀ p q : ℤ,
      Nonempty ((E.page 2).X (p, q) ≅ rightDerivedTensorPageTwo K L p q)) ∧
    convergesToDerivedTensorCohomology E K L

/-- The second spectral sequence of Example `15.62.4`: its `E₂`-page is
`H^p(H^q(K^•) \otimes_R^{\mathbf L} L^•)`, and it converges to
`H^{p+q}(K^• \otimes_R^{\mathbf L} L^•)`. -/
def IsLeftCohomologyDerivedTensorSpectralSequence
    (E : CohomologicalSpectralSequence ModR 0) (K L : DModMinus) : Prop :=
  (∀ p q : ℤ,
      Nonempty ((E.page 2).X (p, q) ≅ leftDerivedTensorPageTwo K L p q)) ∧
    convergesToDerivedTensorCohomology E K L

/-- Helper for Example 15.62.4: a bounded-above derived `R`-complex has a representative complex
whose ordinary cohomology vanishes in all sufficiently large degrees. -/
private theorem preimage_eventually_isZero_homology_of_boundedAbove
    (X : DModMinus) :
    ∃ a : ℤ, ∀ n : ℤ, a < n → Limits.IsZero ((DerivedCategory.Q.objPreimage X.obj).homology n) := by
  -- Unpack the bounded-above hypothesis into eventual vanishing in the derived category.
  obtain ⟨a, ha⟩ := (derivedCategory_t_minus_iff (K := X.obj)).1 X.property
  refine ⟨a, ?_⟩
  intro n hn
  -- Compare derived-category cohomology with the homology of the chosen preimage complex.
  let e : (H n).obj X.obj ≅ (DerivedCategory.Q.objPreimage X.obj).homology n :=
    ((H n).mapIso (DerivedCategory.Q.objObjPreimageIso X.obj)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors ModR n).app
        (DerivedCategory.Q.objPreimage X.obj)
  exact (e.isZero_iff).1 (ha n hn)

/-- Helper for Example 15.62.4: fixing the ambient category to `ModuleCat R` removes the universe
packaging issue and gives a projective resolution of the chosen preimage complex. -/
private theorem nonempty_projective_resolution_preimage_of_boundedAbove
    (X : DModMinus) :
    Nonempty (CochainComplex.ProjectiveResolution (DerivedCategory.Q.objPreimage X.obj)) := by
  -- Proof comment: apply the Chapter `13.19.3` existence theorem to the chosen preimage
  -- complex, using the bounded-above vanishing statement proved just above.
  exact
    nonempty_projectiveResolution_of_eventually_isZero_homology
      (preimage_eventually_isZero_homology_of_boundedAbove X)

/-- Helper for Example 15.62.4: the quasi-isomorphism from a projective resolution becomes an
isomorphism after localizing to the derived category. -/
private theorem derived_qobj_iso_of_projective_resolution_preimage
    (X : DModMinus)
    (P : CochainComplex.ProjectiveResolution (DerivedCategory.Q.objPreimage X.obj)) :
    Nonempty (DerivedCategory.Q.obj (P : CochainComplex ModR ℤ) ≅ X.obj) := by
  -- Route correction: keep the localization transport separate from the existence step so Lean
  -- does not reopen the ambient category while elaborating the final existential package.
  have hπ : IsIso (DerivedCategory.Q.map P.π) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  exact ⟨(asIso (DerivedCategory.Q.map P.π)) ≪≫ DerivedCategory.Q.objObjPreimageIso X.obj⟩

/-- Helper for Example 15.62.4: every bounded-above derived `R`-complex admits a bounded-above
projective representative whose image in the derived category is the original object. -/
private theorem exists_projective_resolution_model_of_boundedAbove
    (X : DModMinus) :
    ∃ P : CochainComplex.ProjectiveResolution (DerivedCategory.Q.objPreimage X.obj),
      ∃ a : ℤ,
        (P : CochainComplex ModR ℤ).IsStrictlyLE a ∧
          Nonempty (DerivedCategory.Q.obj (P : CochainComplex ModR ℤ) ≅ X.obj) := by
  -- First choose the projective model in the fixed ambient category.
  obtain ⟨P⟩ := nonempty_projective_resolution_preimage_of_boundedAbove X
  -- Then record the bounded-above cut-off and transport the resolution map through `Q`.
  obtain ⟨a, hPa⟩ := P.exists_isStrictlyLE
  exact ⟨P, a, hPa, derived_qobj_iso_of_projective_resolution_preimage X P⟩

/-- Helper for Example 15.62.4: the tensor bicomplex attached to two cochain complexes of
`R`-modules. -/
private abbrev tensor_bicomplex
    (P Q : CochainComplex ModR ℤ) :
    HomologicalComplex₂ ModR (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (((curriedTensor ModR).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj P).obj Q

/-- Helper for Example 15.62.4: if the left index of the tensor bicomplex lies above the strict
upper bound for `P`, then the corresponding bicomplex term is zero. -/
private theorem tensor_bicomplex_isZero_of_left_strictlyLE
    {P Q : CochainComplex ModR ℤ} {a p q : ℤ}
    (hP : P.IsStrictlyLE a) (hp : a < p) :
    Limits.IsZero ((tensor_bicomplex P Q).X p |>.X q) := by
  -- The left tensor factor vanishes in degree `p`, so the entire tensor term vanishes.
  have hPzero : Limits.IsZero (P.X p) := P.isZero_of_isStrictlyLE a p hp
  let F : ModR ⥤ ModR := (curriedTensor ModR).flip.obj (Q.X q)
  change Limits.IsZero (F.obj (P.X p))
  exact F.map_isZero hPzero

/-- Helper for Example 15.62.4: if the right index of the tensor bicomplex lies above the strict
upper bound for `Q`, then the corresponding bicomplex term is zero. -/
private theorem tensor_bicomplex_isZero_of_right_strictlyLE
    {P Q : CochainComplex ModR ℤ} {b p q : ℤ}
    (hQ : Q.IsStrictlyLE b) (hq : b < q) :
    Limits.IsZero ((tensor_bicomplex P Q).X p |>.X q) := by
  -- The right tensor factor vanishes in degree `q`, so tensoring with it gives zero.
  have hQzero : Limits.IsZero (Q.X q) := Q.isZero_of_isStrictlyLE b q hq
  let F : ModR ⥤ ModR := (curriedTensor ModR).obj (P.X p)
  change Limits.IsZero (F.obj (Q.X q))
  exact F.map_isZero hQzero

/-- Helper for Example 15.62.4: strict upper bounds on the two projective models force the tensor
bicomplex to have only finitely many nonzero terms on each antidiagonal. -/
private theorem tensor_bicomplex_has_finite_antidiagonal_support_of_strictlyLE
    {P Q : CochainComplex ModR ℤ} {a b : ℤ}
    (hP : P.IsStrictlyLE a) (hQ : Q.IsStrictlyLE b) :
    doubleComplexHasFiniteAntidiagonalSupport (tensor_bicomplex P Q) := by
  intro n
  -- Any nonzero antidiagonal term must lie in the interval `n - b ≤ p ≤ a`.
  refine (Set.finite_Icc (n - b) a).subset ?_
  intro p hp
  constructor
  · by_contra hp'
    have hq : b < n - p := by omega
    have hzero :
        Limits.IsZero ((tensor_bicomplex P Q).X p |>.X (n - p)) :=
      tensor_bicomplex_isZero_of_right_strictlyLE hQ hq
    exact hp hzero
  · by_contra hp'
    have hpgt : a < p := lt_of_not_ge hp'
    have hzero :
        Limits.IsZero ((tensor_bicomplex P Q).X p |>.X (n - p)) :=
      tensor_bicomplex_isZero_of_left_strictlyLE hP hpgt
    exact hp hzero

/-- Helper for Example 15.62.4: the `q`-th homology of the `p`-th column of the tensor bicomplex
is the tensor of the fixed projective term `P^p` with `H^q(Q^•)`. -/
private theorem tensor_bicomplex_column_homology_iso_of_projective
    (P Q : CochainComplex ModR ℤ) (p q : ℤ)
    (hPproj : Projective (P.X p)) :
    Nonempty
      (((tensor_bicomplex P Q).X p).homology q ≅
        ((curriedTensor ModR).obj (P.X p)).obj (Q.homology q)) := by
  -- Route correction: isolate the literal column object before reopening the page-two transport.
  let F : ModR ⥤ ModR := CategoryTheory.MonoidalCategory.tensorLeft (P.X p)
  letI : Projective (P.X p) := hPproj
  letI : Module.Projective R (P.X p) := by
    infer_instance
  letI : Module.Flat R (P.X p) := Module.Flat.of_projective
  letI : PreservesFiniteLimits F := inferInstance
  letI : PreservesFiniteColimits F := inferInstance
  let hExact : exactFunctor ModR ModR F := (exactFunctor_iff F).2 ⟨inferInstance, inferInstance⟩
  letI : F.Additive := (exactFunctor_le_additiveFunctor ModR ModR) F hExact
  letI : F.PreservesHomology := inferInstance
  let eColumn :
      ((tensor_bicomplex P Q).X p) ≅ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) :=
    Iso.refl _
  refine ⟨?_⟩
  -- Compare the literal column with the fixed-left tensor image of `Q`, then commute homology
  -- through that exact functor.
  exact (HomologicalComplex.homologyMapIso eColumn q) ≪≫ (Q.sc q).mapHomologyIso F

/-- Helper for Example 15.62.4: the `q`-th homology of the `p`-th row of the flipped tensor
bicomplex is the tensor of `H^q(P^•)` with the fixed projective term `Q^p`. -/
private theorem tensor_bicomplex_row_homology_iso_of_projective
    (P Q : CochainComplex ModR ℤ) (p q : ℤ)
    (hQproj : Projective (Q.X p)) :
    Nonempty
      (((tensor_bicomplex P Q).flip.X p).homology q ≅
        (((curriedTensor ModR).flip.obj (Q.X p)).obj (P.homology q))) := by
  -- Route correction: prove the row owner directly on the flipped bicomplex instead of adding a
  -- second layer of `flip` transport on top of the column calculation.
  let F : ModR ⥤ ModR := CategoryTheory.MonoidalCategory.tensorRight (Q.X p)
  letI : Projective (Q.X p) := hQproj
  letI : Module.Projective R (Q.X p) := by
    infer_instance
  letI : Module.Flat R (Q.X p) := Module.Flat.of_projective
  letI : PreservesFiniteLimits F :=
    preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight (Q.X p))
  letI : PreservesFiniteColimits F :=
    preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight (Q.X p))
  let hExact : exactFunctor ModR ModR F := (exactFunctor_iff F).2 ⟨inferInstance, inferInstance⟩
  letI : F.Additive := (exactFunctor_le_additiveFunctor ModR ModR) F hExact
  letI : F.PreservesHomology := inferInstance
  let eRow :
      ((tensor_bicomplex P Q).flip.X p) ≅ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
    Iso.refl _
  refine ⟨?_⟩
  -- The flipped row is the fixed-right tensor image of `P`, so the same exact-functor transport
  -- identifies its homology with tensoring `P.homology q` by `Q.X p`.
  exact (HomologicalComplex.homologyMapIso eRow q) ≪≫ (P.sc q).mapHomologyIso F

/-- Helper for Example 15.62.4: the total complex of the tensor bicomplex is the ordinary tensor
product complex of `P` and `Q`. -/
private theorem tensor_bicomplex_total_iso_tensorObj
    (P Q : CochainComplex ModR ℤ) :
    Nonempty
      (HomologicalComplex₂.total (tensor_bicomplex P Q) (ComplexShape.up ℤ) ≅
        HomologicalComplex.tensorObj P Q) := by
  -- Route correction: compare the chain-level owners once here, so the abutment proof does not
  -- repeatedly unfold both `HomologicalComplex₂.total` and `HomologicalComplex.tensorObj`.
  -- Both owners are definitionally the same total tensor construction on cochain complexes.
  exact ⟨Iso.refl _⟩

/-- Helper for Example 15.62.4: the localization functor `Q` on cochain complexes carries the
monoidal structure induced from the homotopy-category localization. -/
private noncomputable instance derivedCategoryQMonoidal :
    (DerivedCategory.Q : CochainComplex ModR ℤ ⥤ DerivedCategory ModR).Monoidal := by
  change (((HomotopyCategory.quotient ModR (ComplexShape.up ℤ)) ⋙
      (DerivedCategory.Qh :
        HomotopyCategory ModR (ComplexShape.up ℤ) ⥤ DerivedCategory ModR))).Monoidal
  infer_instance

/-- Helper for Example 15.62.4: tensoring the chosen projective models and then localizing gives
the same derived tensor-product object as tensoring the original derived complexes. -/
private noncomputable def tensorObj_projective_model_iso_derivedTensorProduct
    (K L : DModMinus)
    (P' Q' : CochainComplex ModR ℤ)
    (eP : DerivedCategory.Q.obj P' ≅ K.obj)
    (eQ : DerivedCategory.Q.obj Q' ≅ L.obj) :
    DerivedCategory.Q.obj (HomologicalComplex.tensorObj P' Q') ≅ K.obj ⊗[R]^L L.obj :=
  -- Compare the localized tensor complex with the monoidal tensor in `D(R)`, then replace the
  -- two localized projective models by `K` and `L`.
  (Functor.Monoidal.μIso (DerivedCategory.Q : CochainComplex ModR ℤ ⥤ DerivedCategory ModR)
      P' Q').symm ≪≫
    (eP ⊗ᵢ eQ) ≪≫
      derivedCategory_tensorObj_iso_derivedTensorProduct K.obj L.obj

/-- Helper for Example 15.62.4: the ordinary homology of the tensor complex of the chosen
projective models computes the derived tensor-product cohomology abutment. -/
private theorem tensorObj_projective_model_homology_iso_derivedTensor_abutment
    (K L : DModMinus)
    (P' Q' : CochainComplex ModR ℤ)
    (eP : DerivedCategory.Q.obj P' ≅ K.obj)
    (eQ : DerivedCategory.Q.obj Q' ≅ L.obj) :
    ∀ n : ℤ,
      Nonempty
        ((HomologicalComplex.tensorObj P' Q').homology n ≅
          derivedTensorCohomologyAbutment K L n) := by
  intro n
  refine ⟨?_⟩
  -- First pass from ordinary homology to derived-category cohomology of `Q.obj (P' ⊗ Q')`, then
  -- transport that object along the monoidal localization comparison.
  exact
    ((DerivedCategory.homologyFunctorFactors ModR n).app
      (HomologicalComplex.tensorObj P' Q')).symm ≪≫
      (H n).mapIso
    (tensorObj_projective_model_iso_derivedTensorProduct
      (K := K) (L := L) (P' := P') (Q' := Q') eP eQ)

/-- Helper for Example 15.62.4: the fixed-`q` slice of the `E₁`-page, viewed as an ordinary
cochain complex in the `p`-direction. -/
private def associatedPageOneComplex
    (E : CohomologicalSpectralSequence ModR 0) (q : ℤ) : CochainComplex ModR ℤ where
  X p := (E.page 1).X (p, q)
  d p p' := (E.page 1).d (p, q) (p', q)
  shape p p' hpp' := by
    have hpq :
        ¬ (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ)).Rel (p, q) (p', q) := by
      simpa [ComplexShape.up'] using hpp'
    exact (E.page 1).shape (p, q) (p', q) hpq
  d_comp_d' p p' p'' hpp' hp'p'' := by
    exact (E.page 1).d_comp_d (p, q) (p', q) (p'', q)

/-- Helper for Example 15.62.4: the short-complex view of the fixed-`q` `E₁`-slice agrees with
the ambient short complex at bidegree `(p, q)`. -/
private noncomputable def associatedPageOneComplexScIso
    (E : CohomologicalSpectralSequence ModR 0) (p q : ℤ) :
    (associatedPageOneComplex E q).sc' (p - 1) p (p + 1) ≅
      (E.page 1).sc' (p - 1, q) (p, q) (p + 1, q) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [associatedPageOneComplex])
    (by simp [associatedPageOneComplex])

/-- Helper for Example 15.62.4: the `p`-th homology of the fixed-`q` `E₁`-slice is the ambient
page-one homology object at bidegree `(p, q)`. -/
private noncomputable def associatedPageOneComplex_homologyIso
    (E : CohomologicalSpectralSequence ModR 0) (p q : ℤ) :
    (associatedPageOneComplex E q).homology p ≅ (E.page 1).homology (p, q) :=
  let hprevSlice : (ComplexShape.up ℤ).prev p = p - 1 :=
    ComplexShape.prev_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up'])
  let hnextSlice : (ComplexShape.up ℤ).next p = p + 1 :=
    ComplexShape.next_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up'])
  let hprevPage :
      (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ)).prev (p, q) = (p - 1, q) :=
    ComplexShape.prev_eq' (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ))
      (by simp [ComplexShape.up'])
  let hnextPage :
      (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ)).next (p, q) = (p + 1, q) :=
    ComplexShape.next_eq' (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ))
      (by simp [ComplexShape.up'])
  -- The fixed-`q` slice uses the same differential data as the ambient `E₁` page at `(p, q)`.
  (associatedPageOneComplex E q).homologyIsoSc' (p - 1) p (p + 1) hprevSlice hnextSlice ≪≫
    ShortComplex.homologyMapIso (associatedPageOneComplexScIso E p q) ≪≫
    ((E.page 1).homologyIsoSc' (p - 1, q) (p, q) (p + 1, q) hprevPage hnextPage).symm

/-- Helper for Example 15.62.4: any fixed-`q` comparison of the `E₁`-slice with an ordinary
cochain complex yields the corresponding `E₂`-page identification by taking `p`-th homology. -/
private theorem associated_pageTwo_iso_of_pageOne_complex_iso
    (E : CohomologicalSpectralSequence ModR 0) (p q : ℤ)
    (C : CochainComplex ModR ℤ)
    (e : associatedPageOneComplex E q ≅ C) :
    Nonempty ((E.page 2).X (p, q) ≅ C.homology p) := by
  refine ⟨?_⟩
  -- First rewrite the ambient `E₂` term as the homology of the page-one object at `(p,q)`.
  -- Then transport that homology to the fixed-`q` slice and along the chosen complex isomorphism.
  exact
    (E.iso 1 2 (p, q)).symm ≪≫
    (associatedPageOneComplex_homologyIso E p q).symm ≪≫
        HomologicalComplex.homologyMapIso e p

/-- Helper for Example 15.62.4: the fixed-`q` `E₁`-slice of an associated spectral sequence for
the first filtered double-complex owner is the textbook first page-one complex. -/
private noncomputable def associated_pageOneComplex_first_component_iso
    (K : HomologicalComplex₂ ModR (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (E : CohomologicalSpectralSequence ModR 0)
    [IsAssociatedToFilteredComplex (firstDoubleComplexFilteredComplex K) E]
    (p q : ℤ) :
    (associatedPageOneComplex E q).X p ≅ ((K.X p).homology q) :=
  -- Proof comment: for the first filtration, the owner `FilteredComplex.pageOneIso` already
  -- identifies the `E₁` term at `(p,q)` with the vertical homology of the `p`-th column.
  by
    simpa [associatedPageOneComplex, firstDoubleComplexPageOne_def] using
      (FilteredComplex.pageOneIso (firstDoubleComplexFilteredComplex K) E p q)

/-- Helper for Example 15.62.4: the fixed-`q` `E₁`-slice of an associated spectral sequence for
the second filtered double-complex owner has the expected objectwise horizontal homology terms. -/
private noncomputable def associated_pageOneComplex_second_component_iso
    (K : HomologicalComplex₂ ModR (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (E : CohomologicalSpectralSequence ModR 0)
    [IsAssociatedToFilteredComplex (secondDoubleComplexFilteredComplex K) E]
    (p q : ℤ) :
    (associatedPageOneComplex E q).X p ≅ ((K.flip.X p).homology q) :=
  -- Proof comment: the second filtration gives the rowwise analogue of the previous page-one
  -- identification via the same owner comparison.
  by
    simpa [associatedPageOneComplex, secondDoubleComplexPageOne_def] using
      (FilteredComplex.pageOneIso (secondDoubleComplexFilteredComplex K) E p q)

/-- Helper for Example 15.62.4: the first-filtration `d₁` differential on the fixed-`q` page-one
slice matches the textbook horizontal homology differential. -/
private theorem first_doubleComplex_pageOne_d_commSq
    (K : HomologicalComplex₂ ModR (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (E : CohomologicalSpectralSequence ModR 0)
    [IsAssociatedToFilteredComplex (firstDoubleComplexFilteredComplex K) E]
    (p q : ℤ) :
    CommSq
      ((associatedPageOneComplex E q).d p (p + 1))
      (associated_pageOneComplex_first_component_iso (K := K) (E := E) p q).hom
      (associated_pageOneComplex_first_component_iso (K := K) (E := E) (p + 1) q).hom
      ((firstDoubleComplexPageOneComplex K q).d p (p + 1)) := by
  -- Proof comment: after expanding both sides, this is exactly the compatibility of the
  -- first-filtration page-one identification with the horizontal `d₁` differential.
  refine ⟨?_⟩
  simp [associatedPageOneComplex, associated_pageOneComplex_first_component_iso,
    firstDoubleComplexPageOneComplex_d]

/-- Helper for Example 15.62.4: the second-filtration `d₁` differential on the fixed-`q` page-one
slice matches the textbook signed horizontal-homology differential. -/
private theorem second_doubleComplex_pageOne_d_commSq
    (K : HomologicalComplex₂ ModR (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (E : CohomologicalSpectralSequence ModR 0)
    [IsAssociatedToFilteredComplex (secondDoubleComplexFilteredComplex K) E]
    (p q : ℤ) :
    CommSq
      ((associatedPageOneComplex E q).d p (p + 1))
      (associated_pageOneComplex_second_component_iso (K := K) (E := E) p q).hom
      (associated_pageOneComplex_second_component_iso (K := K) (E := E) (p + 1) q).hom
      ((secondDoubleComplexPageOneComplex K q).d p (p + 1)) := by
  -- Proof comment: the second-filtration differential is the signed row-homology map, and the
  -- owner page-one identification transports it directly to the textbook `d₁`.
  refine ⟨?_⟩
  simp [associatedPageOneComplex, associated_pageOneComplex_second_component_iso,
    secondDoubleComplexPageOneComplex_d]

/-- Helper for Example 15.62.4: the fixed-`q` `E₁`-slice of an associated spectral sequence for
the first filtered double-complex owner is the textbook first page-one complex. -/
private noncomputable def associated_pageOneComplex_iso_of_firstDoubleComplex_spec
    (K : HomologicalComplex₂ ModR (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (E : CohomologicalSpectralSequence ModR 0)
    [IsAssociatedToFilteredComplex (firstDoubleComplexFilteredComplex K) E]
    (q : ℤ) :
    associatedPageOneComplex E q ≅ firstDoubleComplexPageOneComplex K q :=
  -- Proof comment: assemble the objectwise page-one identifications into a cochain-complex
  -- isomorphism by checking the `d₁` square on consecutive degrees.
  HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ associated_pageOneComplex_first_component_iso (K := K) (E := E) p q)
    (fun p p' hpp' ↦ by
      have hp : p + 1 = p' := by
        simpa [ComplexShape.up, ComplexShape.up'] using hpp'
      subst hp
      exact first_doubleComplex_pageOne_d_commSq (K := K) (E := E) p q)

/-- Helper for Example 15.62.4: the fixed-`q` `E₁`-slice of an associated spectral sequence for
the first filtered double-complex owner is the textbook first page-one complex. -/
private noncomputable def associated_pageOneComplex_iso_of_firstDoubleComplex
    (K : HomologicalComplex₂ ModR (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (E : CohomologicalSpectralSequence ModR 0)
    [IsAssociatedToFilteredComplex (firstDoubleComplexFilteredComplex K) E]
    (q : ℤ) :
    associatedPageOneComplex E q ≅ firstDoubleComplexPageOneComplex K q :=
  associated_pageOneComplex_iso_of_firstDoubleComplex_spec (K := K) (E := E) q

/-- Helper for Example 15.62.4: the fixed-`q` `E₁`-slice of an associated spectral sequence for
the second filtered double-complex owner is the textbook second page-one complex. -/
private noncomputable def associated_pageOneComplex_iso_of_secondDoubleComplex
    (K : HomologicalComplex₂ ModR (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (E : CohomologicalSpectralSequence ModR 0)
    [IsAssociatedToFilteredComplex (secondDoubleComplexFilteredComplex K) E]
    (q : ℤ) :
    associatedPageOneComplex E q ≅ secondDoubleComplexPageOneComplex K q :=
  -- Proof comment: the rowwise page-one comparison also assembles degreewise into a cochain
  -- isomorphism once the signed `d₁` compatibility is recorded.
  HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ associated_pageOneComplex_second_component_iso (K := K) (E := E) p q)
    (fun p p' hpp' ↦ by
      have hp : p + 1 = p' := by
        simpa [ComplexShape.up, ComplexShape.up'] using hpp'
      subst hp
      exact second_doubleComplex_pageOne_d_commSq (K := K) (E := E) p q)

/-- Helper for Example 15.62.4: normalize the associated `E₂`-page of the first filtration to the
textbook owner `firstDoubleComplexPageTwo`. -/
private theorem first_associated_pageTwo_iso_of_firstDoubleComplex
    (K : HomologicalComplex₂ ModR (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (E : CohomologicalSpectralSequence ModR 0)
    [IsAssociatedToFilteredComplex (firstDoubleComplexFilteredComplex K) E]
    (p q : ℤ) :
    Nonempty ((E.page 2).X (p, q) ≅ firstDoubleComplexPageTwo K p q) := by
  -- Proof comment: the generic page-two transport becomes the textbook first page-two term once
  -- the fixed-`q` `E₁` slice is identified with the first page-one complex.
  simpa [firstDoubleComplexPageTwo_def] using
    associated_pageTwo_iso_of_pageOne_complex_iso
      E p q (firstDoubleComplexPageOneComplex K q)
      (associated_pageOneComplex_iso_of_firstDoubleComplex (K := K) (E := E) q)

/-- Helper for Example 15.62.4: normalize the associated `E₂`-page of the second filtration to
the textbook owner `secondDoubleComplexPageTwo`. -/
private theorem second_associated_pageTwo_iso_of_secondDoubleComplex
    (K : HomologicalComplex₂ ModR (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (E : CohomologicalSpectralSequence ModR 0)
    [IsAssociatedToFilteredComplex (secondDoubleComplexFilteredComplex K) E]
    (p q : ℤ) :
    Nonempty ((E.page 2).X (p, q) ≅ secondDoubleComplexPageTwo K p q) := by
  -- Proof comment: this is the same generic page-two transport applied to the second
  -- filtration and then rewritten with the textbook second page-two owner.
  simpa [secondDoubleComplexPageTwo_def] using
    associated_pageTwo_iso_of_pageOne_complex_iso
      E p q (secondDoubleComplexPageOneComplex K q)
      (associated_pageOneComplex_iso_of_secondDoubleComplex (K := K) (E := E) q)

/-- Helper for Example 15.62.4: away from degree `0`, the right single complex contributes a zero
summand to the tensor totalization. -/
private theorem tensorObj_right_single_zero_summand_isZero
    (P' : CochainComplex ModR ℤ) (M : ModR) {i j : ℤ} (hj : j ≠ 0) :
    Limits.IsZero (((curriedTensor ModR).obj (P'.X i)).obj (((singleCpx₀).obj M).X j)) := by
  -- Proof comment: only the degree-zero term of the single complex survives.
  exact
    CategoryTheory.Functor.map_isZero ((curriedTensor ModR).obj (P'.X i))
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (0 : ℤ) M j hj)

/-- Helper for Example 15.62.4: on the surviving degree-zero summand, tensoring with a right
single complex is exactly right tensoring by the underlying module. -/
private noncomputable def tensorObj_right_single_zero_diagonal_iso
    (P' : CochainComplex ModR ℤ) (M : ModR) (n : ℤ) :
    ((curriedTensor ModR).obj (P'.X n)).obj (((singleCpx₀).obj M).X 0) ≅
      (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P').X n := by
  -- Proof comment: after fixing degree `0`, only the canonical `singleObjXSelf` identification
  -- remains.
  simpa using
    CategoryTheory.Functor.mapIso ((curriedTensor ModR).obj (P'.X n))
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M)

/-- Helper for Example 15.62.4: the forward comparison keeps only the diagonal summand of the
tensor totalization with a right single complex. -/
private noncomputable def tensorObj_right_single_zero_component_hom
    (P' : CochainComplex ModR ℤ) (M : ModR) (n : ℤ) :
    (HomologicalComplex.tensorObj P' ((singleCpx₀).obj M)).X n ⟶
      (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P').X n :=
  HomologicalComplex.mapBifunctorDesc
    (K₁ := P')
    (K₂ := (singleCpx₀).obj M)
    (F := curriedTensor ModR)
    (c := ComplexShape.up ℤ)
    (A := (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P').X n))
    (j := n)
    (fun p q h ↦ by
      by_cases hq : q = 0
      · subst hq
        have hp : p = n := by simpa using h
        subst p
        exact (tensorObj_right_single_zero_diagonal_iso P' M n).hom
      · exact 0)

/-- Helper for Example 15.62.4: on the diagonal summand, the forward comparison is the canonical
degreewise tensor identification. -/
@[reassoc]
private theorem tensorObj_right_single_zero_component_hom_diag
    (P' : CochainComplex ModR ℤ) (M : ModR) (n : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (n, 0) = n) :
    HomologicalComplex.ιTensorObj P' ((singleCpx₀).obj M) n 0 n h ≫
      tensorObj_right_single_zero_component_hom P' M n =
        (tensorObj_right_single_zero_diagonal_iso P' M n).hom := by
  let B :
      ModR :=
    (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P').X n
  let f : ∀ p q
      (h' : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n),
      ((curriedTensor ModR).obj (P'.X p)).obj (((singleCpx₀).obj M).X q) ⟶ B :=
    fun p q h' ↦ by
      by_cases hq : q = 0
      · subst hq
        have hp : p = n := by simpa using h'
        subst p
        exact (tensorObj_right_single_zero_diagonal_iso P' M n).hom
      · exact 0
  -- Proof comment: evaluate the descended map on the unique surviving `(n,0)` summand.
  simpa [tensorObj_right_single_zero_component_hom, B, f] using
    (iTensorObj_mapBifunctorDesc_assoc
      (K := P')
      (L := (singleCpx₀).obj M)
      (n := n) (B := B) (C := B) f (𝟙 B) n 0 h)

/-- Helper for Example 15.62.4: away from the diagonal summand, the forward comparison vanishes.
-/
@[reassoc]
private theorem tensorObj_right_single_zero_component_hom_off_diagonal
    (P' : CochainComplex ModR ℤ) (M : ModR) (n p q : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n)
    (hq : q ≠ 0) :
    HomologicalComplex.ιTensorObj P' ((singleCpx₀).obj M) p q n h ≫
      tensorObj_right_single_zero_component_hom P' M n =
        0 := by
  let B :
      ModR :=
    (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P').X n
  let f : ∀ p' q'
      (h' : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p', q') = n),
      ((curriedTensor ModR).obj (P'.X p')).obj (((singleCpx₀).obj M).X q') ⟶ B :=
    fun p' q' h' ↦ by
      by_cases hq' : q' = 0
      · subst hq'
        have hp' : p' = n := by simpa using h'
        subst p'
        exact (tensorObj_right_single_zero_diagonal_iso P' M n).hom
      · exact 0
  -- Proof comment: off the diagonal, the defining branch of the descended map is literally zero.
  simpa [tensorObj_right_single_zero_component_hom, B, f, hq] using
    (iTensorObj_mapBifunctorDesc_assoc
      (K := P')
      (L := (singleCpx₀).obj M)
      (n := n) (B := B) (C := B) f (𝟙 B) p q h)

/-- Helper for Example 15.62.4: the inverse degreewise comparison reinserts the surviving
diagonal summand into the tensor totalization with a right single complex. -/
private noncomputable def tensorObj_right_single_zero_component_inv
    (P' : CochainComplex ModR ℤ) (M : ModR) (n : ℤ) :
    (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P').X n ⟶
      (HomologicalComplex.tensorObj P' ((singleCpx₀).obj M)).X n :=
  (tensorObj_right_single_zero_diagonal_iso P' M n).inv ≫
    HomologicalComplex.ιTensorObj P' ((singleCpx₀).obj M) n 0 n
      (by simp)

/-- Helper for Example 15.62.4: in each total degree, tensoring with a right degree-zero single
complex collapses to the unique surviving diagonal summand. -/
private noncomputable def tensorObj_right_single_zero_component_iso
    (P' : CochainComplex ModR ℤ) (M : ModR) (n : ℤ) :
    (HomologicalComplex.tensorObj P' ((singleCpx₀).obj M)).X n ≅
      (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P').X n :=
  { hom := tensorObj_right_single_zero_component_hom P' M n
    inv := tensorObj_right_single_zero_component_inv P' M n
    hom_inv_id := by
      -- Proof comment: check the identity on the tensor totalization summandwise.
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro p q h
      by_cases hq : q = 0
      · subst hq
        have hp : p = n := by simpa using h
        subst p
        change
          ((HomologicalComplex.ιTensorObj P' ((singleCpx₀).obj M) n 0 n h ≫
              tensorObj_right_single_zero_component_hom P' M n) ≫
            tensorObj_right_single_zero_component_inv P' M n) =
            HomologicalComplex.ιTensorObj P' ((singleCpx₀).obj M) n 0 n h ≫
              𝟙 ((HomologicalComplex.tensorObj P' ((singleCpx₀).obj M)).X n)
        simpa [tensorObj_right_single_zero_component_inv, Category.assoc] using
          congrArg (fun k ↦ k ≫ tensorObj_right_single_zero_component_inv P' M n)
            (tensorObj_right_single_zero_component_hom_diag P' M n h)
      · change
          ((HomologicalComplex.ιTensorObj P' ((singleCpx₀).obj M) p q n h ≫
              tensorObj_right_single_zero_component_hom P' M n) ≫
            tensorObj_right_single_zero_component_inv P' M n) =
            HomologicalComplex.ιTensorObj P' ((singleCpx₀).obj M) p q n h ≫
              𝟙 ((HomologicalComplex.tensorObj P' ((singleCpx₀).obj M)).X n)
        rw [tensorObj_right_single_zero_component_hom_off_diagonal P' M n p q h hq]
        simp only [CategoryTheory.Limits.zero_comp, Category.comp_id]
        symm
        exact
          (tensorObj_right_single_zero_summand_isZero
            (P' := P') (M := M) (i := p) (j := q) hq).eq_of_src _ _
    inv_hom_id := by
      let h0 : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (n, 0) = n := by
        simp
      -- Proof comment: the inverse immediately lands in the diagonal summand and cancels there.
      change
        ((tensorObj_right_single_zero_diagonal_iso P' M n).inv ≫
            HomologicalComplex.ιTensorObj P' ((singleCpx₀).obj M) n 0 n h0) ≫
          tensorObj_right_single_zero_component_hom P' M n =
            𝟙 ((((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P').X n)
      calc
        ((tensorObj_right_single_zero_diagonal_iso P' M n).inv ≫
            HomologicalComplex.ιTensorObj P' ((singleCpx₀).obj M) n 0 n h0) ≫
          tensorObj_right_single_zero_component_hom P' M n
            = (tensorObj_right_single_zero_diagonal_iso P' M n).inv ≫
                (HomologicalComplex.ιTensorObj P' ((singleCpx₀).obj M) n 0 n h0 ≫
                  tensorObj_right_single_zero_component_hom P' M n) := by
                    simp [Category.assoc]
        _ = (tensorObj_right_single_zero_diagonal_iso P' M n).inv ≫
              (tensorObj_right_single_zero_diagonal_iso P' M n).hom := by
                simpa using
                  congrArg (fun k ↦ (tensorObj_right_single_zero_diagonal_iso P' M n).inv ≫ k)
                    (tensorObj_right_single_zero_component_hom_diag P' M n h0)
        _ = 𝟙 _ := by simp }

/-- Helper for Example 15.62.4: the diagonal tensor comparison is natural in the differential of
the left cochain complex. -/
private theorem tensorObj_right_single_zero_diagonal_iso_hom_naturality
    (P' : CochainComplex ModR ℤ) (M : ModR) (i j : ℤ)
    (_hij : (ComplexShape.up ℤ).Rel i j) :
    (tensorObj_right_single_zero_diagonal_iso P' M i).hom ≫
        (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P').d i j =
      (((curriedTensor ModR).map (P'.d i j)).app (((singleCpx₀).obj M).X 0)) ≫
        (tensorObj_right_single_zero_diagonal_iso P' M j).hom := by
  -- Proof comment: this is the `singleObjXSelf` naturality square transported through
  -- `tensorRight`.
  simpa [tensorObj_right_single_zero_diagonal_iso,
    CategoryTheory.Functor.mapHomologicalComplex_obj_d, singleCpx₀] using
    (((curriedTensor ModR).map (P'.d i j)).naturality
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M).hom)

/-- Helper for Example 15.62.4: the inverse diagonal tensor comparison satisfies the same
naturality square rewritten for the inverse map. -/
private theorem tensorObj_right_single_zero_diagonal_iso_inv_naturality
    (P' : CochainComplex ModR ℤ) (M : ModR) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    (tensorObj_right_single_zero_diagonal_iso P' M i).inv ≫
        (((curriedTensor ModR).map (P'.d i j)).app (((singleCpx₀).obj M).X 0)) =
      (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P').d i j ≫
        (tensorObj_right_single_zero_diagonal_iso P' M j).inv := by
  -- Proof comment: cancel the target diagonal isomorphism and reuse the forward naturality
  -- square.
  apply (cancel_mono (tensorObj_right_single_zero_diagonal_iso P' M j).hom).1
  simpa [Category.assoc] using
    calc
      (tensorObj_right_single_zero_diagonal_iso P' M i).inv ≫
          (((curriedTensor ModR).map (P'.d i j)).app (((singleCpx₀).obj M).X 0)) ≫
          (tensorObj_right_single_zero_diagonal_iso P' M j).hom
        = (tensorObj_right_single_zero_diagonal_iso P' M i).inv ≫
            ((tensorObj_right_single_zero_diagonal_iso P' M i).hom ≫
              (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P').d i j) := by
            rw [tensorObj_right_single_zero_diagonal_iso_hom_naturality P' M i j hij]
      _ =
          (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P').d i j := by
            simp

/-- Helper for Example 15.62.4: the inverse degreewise tensor comparison already respects the
cochain differential. -/
private theorem tensorObj_right_single_zero_component_inv_comm
    (P' : CochainComplex ModR ℤ) (M : ModR) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    tensorObj_right_single_zero_component_inv P' M i ≫
        (HomologicalComplex.tensorObj P' ((singleCpx₀).obj M)).d i j =
      (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P').d i j ≫
        tensorObj_right_single_zero_component_inv P' M j := by
  have hj : j = i + 1 := by
    simpa [ComplexShape.up, eq_comm] using hij
  subst hj
  -- Proof comment: expand the total differential; the vertical part vanishes because the single
  -- complex has zero outgoing differential from degree `0`.
  simp only [tensorObj_right_single_zero_component_inv, Category.assoc,
    HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂]
  rw [HomologicalComplex.mapBifunctor.d₁_eq
      (K₁ := P')
      (K₂ := (singleCpx₀).obj M)
      (F := curriedTensor ModR)
      (c := ComplexShape.up ℤ)
      (h := (show (ComplexShape.up ℤ).Rel i (i + 1) by simp))
      (i₂ := 0)
      (j := i + 1)
      (h' := by simp)]
  rw [HomologicalComplex.mapBifunctor.d₂_eq
      (K₁ := P')
      (K₂ := (singleCpx₀).obj M)
      (F := curriedTensor ModR)
      (c := ComplexShape.up ℤ)
      (i₁ := i)
      (h := (show (ComplexShape.up ℤ).Rel 0 (0 + 1) by simp))
      (j := i + 1)
      (h' := by simp)]
  have hsingle : (((singleCpx₀).obj M).d 0 (0 + 1)) = 0 := rfl
  rw [hsingle, Functor.map_zero, CategoryTheory.Limits.zero_comp, smul_zero,
    CategoryTheory.Limits.comp_zero, add_zero]
  rw [show ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (i, 0) = 1 by rfl, one_smul]
  rw [← Category.assoc]
  rw [tensorObj_right_single_zero_diagonal_iso_inv_naturality
      P' M i (i + 1) (show (ComplexShape.up ℤ).Rel i (i + 1) by simp)]
  simp [HomologicalComplex.ιTensorObj, Category.assoc]

/-- Helper for Example 15.62.4: tensoring a cochain complex with a right degree-zero single
complex is canonically the same as right tensoring by the underlying module. -/
private noncomputable def tensorObj_right_single_zero_complex_iso
    (P' : CochainComplex ModR ℤ) (M : ModR) :
    HomologicalComplex.tensorObj P' ((singleCpx₀).obj M) ≅
      (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P') :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ tensorObj_right_single_zero_component_iso P' M n)
    (fun i j hij ↦ by
      -- Proof comment: rewrite the inverse chain-map square into the forward orientation
      -- expected by `isoOfComponents`.
      apply (cancel_mono (tensorObj_right_single_zero_component_iso P' M j).inv).1
      apply (cancel_epi (tensorObj_right_single_zero_component_iso P' M i).inv).1
      simpa [Category.assoc] using
        (tensorObj_right_single_zero_component_inv_comm P' M i j hij).symm)

/-- Helper for Example 15.62.4: degreewise, the first page-one complex of the tensor bicomplex is
the tensor of `P'^p` with `H^q(Q')`, before collapsing the right degree-zero single complex. -/
private noncomputable def tensor_bicomplex_first_pageOne_tensorRight_component_iso
    (P' Q' : CochainComplex ModR ℤ) (q p : ℤ)
    (hPproj : ∀ p : ℤ, Projective (P'.X p)) :
    (firstDoubleComplexPageOneComplex (tensor_bicomplex (P := P') (Q := Q')) q).X p ≅
      ((((CategoryTheory.MonoidalCategory.tensorRight (Q'.homology q)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P').X p) :=
  let F : ModR ⥤ ModR := CategoryTheory.MonoidalCategory.tensorLeft (P'.X p)
  letI : Projective (P'.X p) := hPproj p
  letI : Module.Projective R (P'.X p) := inferInstance
  letI : Module.Flat R (P'.X p) := Module.Flat.of_projective
  letI : PreservesFiniteLimits F := inferInstance
  letI : PreservesFiniteColimits F := inferInstance
  let hExact : exactFunctor ModR ModR F := (exactFunctor_iff F).2 ⟨inferInstance, inferInstance⟩
  letI : F.Additive := (exactFunctor_le_additiveFunctor ModR ModR) F hExact
  letI : F.PreservesHomology := inferInstance
  (Q'.sc q).mapHomologyIso F

/-- Helper for Example 15.62.4: the first page-one comparison is natural with respect to the
horizontal differential before the right degree-zero single complex is collapsed. -/
private theorem tensor_bicomplex_first_pageOne_tensorRight_homology_naturality
    (P' Q' : CochainComplex ModR ℤ) (q p : ℤ)
    (hPproj : ∀ p : ℤ, Projective (P'.X p)) :
    ((firstDoubleComplexPageOneComplex (tensor_bicomplex (P := P') (Q := Q')) q).d p (p + 1)) ≫
        (tensor_bicomplex_first_pageOne_tensorRight_component_iso
          (P' := P') (Q' := Q') q (p + 1) hPproj).hom =
      (tensor_bicomplex_first_pageOne_tensorRight_component_iso
        (P' := P') (Q' := Q') q p hPproj).hom ≫
        ((((CategoryTheory.MonoidalCategory.tensorRight (Q'.homology q)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P').d p (p + 1)) := by
  let Fp : ModR ⥤ ModR := CategoryTheory.MonoidalCategory.tensorLeft (P'.X p)
  let Fp1 : ModR ⥤ ModR := CategoryTheory.MonoidalCategory.tensorLeft (P'.X (p + 1))
  letI : Projective (P'.X p) := hPproj p
  letI : Module.Projective R (P'.X p) := inferInstance
  letI : Module.Flat R (P'.X p) := Module.Flat.of_projective
  letI : PreservesFiniteLimits Fp := inferInstance
  letI : PreservesFiniteColimits Fp := inferInstance
  let hExactp : exactFunctor ModR ModR Fp := (exactFunctor_iff Fp).2 ⟨inferInstance, inferInstance⟩
  letI : Fp.Additive := (exactFunctor_le_additiveFunctor ModR ModR) Fp hExactp
  letI : Fp.PreservesHomology := inferInstance
  letI : Projective (P'.X (p + 1)) := hPproj (p + 1)
  letI : Module.Projective R (P'.X (p + 1)) := inferInstance
  letI : Module.Flat R (P'.X (p + 1)) := Module.Flat.of_projective
  letI : PreservesFiniteLimits Fp1 := inferInstance
  letI : PreservesFiniteColimits Fp1 := inferInstance
  let hExactp1 : exactFunctor ModR ModR Fp1 :=
    (exactFunctor_iff Fp1).2 ⟨inferInstance, inferInstance⟩
  letI : Fp1.Additive := (exactFunctor_le_additiveFunctor ModR ModR) Fp1 hExactp1
  letI : Fp1.PreservesHomology := inferInstance
  let τ : Fp ⟶ Fp1 := (curriedTensor ModR).map (P'.d p (p + 1))
  have hτ :
      τ.app (Q'.sc q).homology =
        ((Q'.sc q).mapHomologyIso Fp).inv ≫
          ShortComplex.homologyMap ((Q'.sc q).mapNatTrans τ) ≫
            ((Q'.sc q).mapHomologyIso Fp1).hom :=
    NatTrans.app_homology (τ := τ) (S := Q'.sc q)
  have hτ' :
      ((Q'.sc q).mapHomologyIso Fp).hom ≫ τ.app (Q'.sc q).homology =
        ShortComplex.homologyMap ((Q'.sc q).mapNatTrans τ) ≫
          ((Q'.sc q).mapHomologyIso Fp1).hom := by
    -- Proof comment: precompose with the inverse transport to cancel the left `mapHomologyIso`.
    simpa [Category.assoc] using
      congrArg (fun f ↦ ((Q'.sc q).mapHomologyIso Fp).hom ≫ f) hτ
  -- Proof comment: rewrite the raw naturality equality onto the owner complexes appearing in the
  -- first `E₁` normalization statement.
  simpa [tensor_bicomplex_first_pageOne_tensorRight_component_iso,
    firstDoubleComplexPageOneComplex_d,
    CategoryTheory.Functor.mapHomologicalComplex_obj_d, Category.assoc] using hτ'

/-- Helper for Example 15.62.4: the first page-one comparison is natural with respect to the
horizontal differential before the right degree-zero single complex is collapsed. -/
private theorem tensor_bicomplex_first_pageOne_tensorRight_d_commSq
    (P' Q' : CochainComplex ModR ℤ) (q p : ℤ)
    (hPproj : ∀ p : ℤ, Projective (P'.X p)) :
    CommSq
      ((firstDoubleComplexPageOneComplex (tensor_bicomplex (P := P') (Q := Q')) q).d p (p + 1))
      (tensor_bicomplex_first_pageOne_tensorRight_component_iso
        (P' := P') (Q' := Q') q p hPproj).hom
      (tensor_bicomplex_first_pageOne_tensorRight_component_iso
        (P' := P') (Q' := Q') q (p + 1) hPproj).hom
      ((((CategoryTheory.MonoidalCategory.tensorRight (Q'.homology q)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P').d p (p + 1)) := by
  -- Proof comment: the raw owner-level naturality equality is already the desired commutative
  -- square once packaged as `CommSq`.
  exact ⟨tensor_bicomplex_first_pageOne_tensorRight_homology_naturality
    (P' := P') (Q' := Q') q p hPproj⟩

/-- Helper for Example 15.62.4: after the intermediate tensor-right normalization, collapsing the
right degree-zero single complex yields the final degreewise first page-one comparison. -/
private noncomputable def tensor_bicomplex_first_pageOne_component_iso
    (P' Q' : CochainComplex ModR ℤ) (q p : ℤ)
    (hPproj : ∀ p : ℤ, Projective (P'.X p)) :
    (firstDoubleComplexPageOneComplex (tensor_bicomplex (P := P') (Q := Q')) q).X p ≅
      (HomologicalComplex.tensorObj P' ((singleCpx₀).obj (Q'.homology q))).X p :=
  tensor_bicomplex_first_pageOne_tensorRight_component_iso
      (P' := P') (Q' := Q') q p hPproj ≪≫
    (tensorObj_right_single_zero_component_iso P' (Q'.homology q) p).symm

/-- Helper for Example 15.62.4: after the degreewise first-page comparison is fixed, the
remaining compatibility condition is the `d₁` square against the tensor differential. -/
private theorem tensor_bicomplex_first_pageOne_d_commSq
    (P' Q' : CochainComplex ModR ℤ) (q p : ℤ)
    (hPproj : ∀ p : ℤ, Projective (P'.X p)) :
    CommSq
      ((firstDoubleComplexPageOneComplex (tensor_bicomplex (P := P') (Q := Q')) q).d p (p + 1))
      (tensor_bicomplex_first_pageOne_component_iso
        (P' := P') (Q' := Q') q p hPproj).hom
      (tensor_bicomplex_first_pageOne_component_iso
        (P' := P') (Q' := Q') q (p + 1) hPproj).hom
      ((HomologicalComplex.tensorObj P' ((singleCpx₀).obj (Q'.homology q))).d
        p (p + 1)) := by
  have hTensorRight :
      CommSq
        ((firstDoubleComplexPageOneComplex (tensor_bicomplex (P := P') (Q := Q')) q).d p (p + 1))
        (tensor_bicomplex_first_pageOne_tensorRight_component_iso
          (P' := P') (Q' := Q') q p hPproj).hom
        (tensor_bicomplex_first_pageOne_tensorRight_component_iso
          (P' := P') (Q' := Q') q (p + 1) hPproj).hom
        ((((CategoryTheory.MonoidalCategory.tensorRight (Q'.homology q)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P').d p (p + 1)) :=
    tensor_bicomplex_first_pageOne_tensorRight_d_commSq
      (P' := P') (Q' := Q') q p hPproj
  have hCollapse :=
    tensorObj_right_single_zero_component_inv_comm
      P' (Q'.homology q) p (p + 1) (show (ComplexShape.up ℤ).Rel p (p + 1) by simp)
  refine ⟨?_⟩
  -- Proof comment: first use the intermediate tensor-right square, then replace the tensor-right
  -- differential by the tensor-with-single differential via the previously established collapse.
  calc
    ((firstDoubleComplexPageOneComplex (tensor_bicomplex (P := P') (Q := Q')) q).d p (p + 1)) ≫
        (tensor_bicomplex_first_pageOne_component_iso
          (P' := P') (Q' := Q') q (p + 1) hPproj).hom
      =
        ((firstDoubleComplexPageOneComplex (tensor_bicomplex (P := P') (Q := Q')) q).d p (p + 1)) ≫
          (tensor_bicomplex_first_pageOne_tensorRight_component_iso
            (P' := P') (Q' := Q') q (p + 1) hPproj).hom ≫
            (tensorObj_right_single_zero_component_iso P' (Q'.homology q) (p + 1)).inv := by
              simp [tensor_bicomplex_first_pageOne_component_iso, Category.assoc]
    _ =
        (tensor_bicomplex_first_pageOne_tensorRight_component_iso
          (P' := P') (Q' := Q') q p hPproj).hom ≫
          ((((CategoryTheory.MonoidalCategory.tensorRight (Q'.homology q)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P').d p (p + 1)) ≫
            (tensorObj_right_single_zero_component_iso P' (Q'.homology q) (p + 1)).inv := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ k ≫
                    (tensorObj_right_single_zero_component_iso P' (Q'.homology q) (p + 1)).inv)
                  hTensorRight.w
    _ =
        (tensor_bicomplex_first_pageOne_tensorRight_component_iso
          (P' := P') (Q' := Q') q p hPproj).hom ≫
          (tensorObj_right_single_zero_component_iso P' (Q'.homology q) p).inv ≫
            (HomologicalComplex.tensorObj P' ((singleCpx₀).obj (Q'.homology q))).d p (p + 1) := by
              rw [← Category.assoc, ← hCollapse]
    _ =
        (tensor_bicomplex_first_pageOne_component_iso
          (P' := P') (Q' := Q') q p hPproj).hom ≫
          (HomologicalComplex.tensorObj P' ((singleCpx₀).obj (Q'.homology q))).d p (p + 1) := by
              simp [tensor_bicomplex_first_pageOne_component_iso, Category.assoc]

/-- Helper for Example 15.62.4: the first page-one differential compatibility above extends to
the general `isoOfComponents` shape required for a complex isomorphism. -/
private theorem tensor_bicomplex_first_pageOne_d_commSq_of_rel
    (P' Q' : CochainComplex ModR ℤ) (q i j : ℤ)
    (hPproj : ∀ p : ℤ, Projective (P'.X p))
    (hij : (ComplexShape.up ℤ).Rel i j) :
    CommSq
      ((firstDoubleComplexPageOneComplex (tensor_bicomplex (P := P') (Q := Q')) q).d i j)
      (tensor_bicomplex_first_pageOne_component_iso
        (P' := P') (Q' := Q') q i hPproj).hom
      (tensor_bicomplex_first_pageOne_component_iso
        (P' := P') (Q' := Q') q j hPproj).hom
      ((HomologicalComplex.tensorObj P' ((singleCpx₀).obj (Q'.homology q))).d i j) := by
  have hj : j = i + 1 := by
    simpa [ComplexShape.up, eq_comm] using hij
  subst hj
  exact tensor_bicomplex_first_pageOne_d_commSq
    (P' := P') (Q' := Q') q i hPproj

private noncomputable def tensor_bicomplex_first_pageOne_complex_iso
    (P' Q' : CochainComplex ModR ℤ) (q : ℤ)
    (hPproj : ∀ p : ℤ, Projective (P'.X p)) :
    firstDoubleComplexPageOneComplex (tensor_bicomplex (P := P') (Q := Q')) q ≅
      HomologicalComplex.tensorObj P' ((singleCpx₀).obj (Q'.homology q)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ tensor_bicomplex_first_pageOne_component_iso (P' := P') (Q' := Q') q p hPproj)
    (fun i j hij ↦
      tensor_bicomplex_first_pageOne_d_commSq_of_rel
        (P' := P') (Q' := Q') q i j hPproj hij)

/-- Helper for Example 15.62.4: multiplying every differential of a cochain complex by a fixed
unit still yields a square-zero differential. -/
private theorem cochain_complex_units_smul_sq
    (L : CochainComplex ModR ℤ) (ε : ℤˣ) (p : ℤ) :
    (ε • L.d p (p + 1)) ≫ (ε • L.d (p + 1) ((p + 1) + 1)) = 0 := by
  -- Pull the common unit scalar outside the composition and use `d ∘ d = 0`.
  calc
    (ε • L.d p (p + 1)) ≫ (ε • L.d (p + 1) ((p + 1) + 1)) =
        ε • (ε • (L.d p (p + 1) ≫ L.d (p + 1) ((p + 1) + 1))) := by
      simp [Linear.units_smul_comp, Linear.comp_units_smul]
    _ = 0 := by
      simp [L.d_comp_d p (p + 1) ((p + 1) + 1)]

/-- Helper for Example 15.62.4: the fixed-`q` row-homology normalization of the second page-one
complex, before identifying it with the canonical tensor-with-single complex. -/
private def second_pageOne_row_tensorRight_complex
    (P' Q' : CochainComplex ModR ℤ) (q : ℤ) : CochainComplex ModR ℤ :=
  let tensorRightComplex :
      CochainComplex ModR ℤ :=
    (((curriedTensor ModR).obj (P'.homology q)).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q'
  CochainComplex.of
    tensorRightComplex.X
    (fun p ↦ q.negOnePow • tensorRightComplex.d p (p + 1))
    (cochain_complex_units_smul_sq tensorRightComplex q.negOnePow)

/-- Helper for Example 15.62.4: degreewise, the second page-one complex of the tensor bicomplex is
the row-homology tensor of `H^q(P')` with `Q'^p`. -/
private noncomputable def tensor_bicomplex_second_pageOne_row_tensor_component_iso
    (P' Q' : CochainComplex ModR ℤ) (q p : ℤ)
    (hQproj : ∀ p : ℤ, Projective (Q'.X p)) :
    (secondDoubleComplexPageOneComplex (tensor_bicomplex (P := P') (Q := Q')) q).X p ≅
      (second_pageOne_row_tensorRight_complex (P' := P') (Q' := Q') q).X p :=
  let F : ModR ⥤ ModR := CategoryTheory.MonoidalCategory.tensorRight (Q'.X p)
  letI : Projective (Q'.X p) := hQproj p
  letI : Module.Projective R (Q'.X p) := inferInstance
  letI : Module.Flat R (Q'.X p) := Module.Flat.of_projective
  letI : PreservesFiniteLimits F :=
    preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight (Q'.X p))
  letI : PreservesFiniteColimits F :=
    preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight (Q'.X p))
  let hExact : exactFunctor ModR ModR F := (exactFunctor_iff F).2 ⟨inferInstance, inferInstance⟩
  letI : F.Additive := (exactFunctor_le_additiveFunctor ModR ModR) F hExact
  letI : F.PreservesHomology := inferInstance
  (P'.sc q).mapHomologyIso F

/-- Helper for Example 15.62.4: after the degreewise second-page-one comparison is fixed, the
remaining compatibility is exactly the signed `d₁` square against the row-tensor differential. -/
private theorem tensor_bicomplex_second_pageOne_row_tensor_homology_naturality
    (P' Q' : CochainComplex ModR ℤ) (q p : ℤ)
    (hQproj : ∀ p : ℤ, Projective (Q'.X p)) :
    ((firstDoubleComplexPageOneComplex (tensor_bicomplex (P := P') (Q := Q')).flip q).d
        p (p + 1)) ≫
        (tensor_bicomplex_second_pageOne_row_tensor_component_iso
          (P' := P') (Q' := Q') q (p + 1) hQproj).hom =
      (tensor_bicomplex_second_pageOne_row_tensor_component_iso
        (P' := P') (Q' := Q') q p hQproj).hom ≫
        ((((curriedTensor ModR).obj (P'.homology q)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q').d p (p + 1) := by
  let Fp : ModR ⥤ ModR := CategoryTheory.MonoidalCategory.tensorRight (Q'.X p)
  let Fp1 : ModR ⥤ ModR := CategoryTheory.MonoidalCategory.tensorRight (Q'.X (p + 1))
  letI : Projective (Q'.X p) := hQproj p
  letI : Module.Projective R (Q'.X p) := inferInstance
  letI : Module.Flat R (Q'.X p) := Module.Flat.of_projective
  letI : PreservesFiniteLimits Fp :=
    preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight (Q'.X p))
  letI : PreservesFiniteColimits Fp :=
    preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight (Q'.X p))
  let hExactp : exactFunctor ModR ModR Fp := (exactFunctor_iff Fp).2 ⟨inferInstance, inferInstance⟩
  letI : Fp.Additive := (exactFunctor_le_additiveFunctor ModR ModR) Fp hExactp
  letI : Fp.PreservesHomology := inferInstance
  letI : Projective (Q'.X (p + 1)) := hQproj (p + 1)
  letI : Module.Projective R (Q'.X (p + 1)) := inferInstance
  letI : Module.Flat R (Q'.X (p + 1)) := Module.Flat.of_projective
  letI : PreservesFiniteLimits Fp1 :=
    preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight (Q'.X (p + 1)))
  letI : PreservesFiniteColimits Fp1 :=
    preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight (Q'.X (p + 1)))
  let hExactp1 : exactFunctor ModR ModR Fp1 :=
    (exactFunctor_iff Fp1).2 ⟨inferInstance, inferInstance⟩
  letI : Fp1.Additive := (exactFunctor_le_additiveFunctor ModR ModR) Fp1 hExactp1
  letI : Fp1.PreservesHomology := inferInstance
  let τ : Fp ⟶ Fp1 := (curriedTensor ModR).flip.map (Q'.d p (p + 1))
  have hτ :
      τ.app (P'.sc q).homology =
        ((P'.sc q).mapHomologyIso Fp).inv ≫
          ShortComplex.homologyMap ((P'.sc q).mapNatTrans τ) ≫
            ((P'.sc q).mapHomologyIso Fp1).hom :=
    NatTrans.app_homology (τ := τ) (S := P'.sc q)
  have hτ' :
      ((P'.sc q).mapHomologyIso Fp).hom ≫ τ.app (P'.sc q).homology =
        ShortComplex.homologyMap ((P'.sc q).mapNatTrans τ) ≫
          ((P'.sc q).mapHomologyIso Fp1).hom := by
    -- Proof comment: precompose with the inverse transport to cancel the left `mapHomologyIso`.
    simpa [Category.assoc] using
      congrArg (fun f ↦ ((P'.sc q).mapHomologyIso Fp).hom ≫ f) hτ
  -- Proof comment: rewrite the raw row-homology naturality equality onto the unsigned owner
  -- complex before inserting the uniform `(-1)^q` sign twist.
  simpa [tensor_bicomplex_second_pageOne_row_tensor_component_iso,
    firstDoubleComplexPageOneComplex_d,
    CategoryTheory.Functor.mapHomologicalComplex_obj_d, Category.assoc] using hτ'

/-- Helper for Example 15.62.4: after the degreewise second-page-one comparison is fixed, the
remaining compatibility is exactly the signed `d₁` square against the row-tensor differential. -/
private theorem tensor_bicomplex_second_pageOne_row_tensor_d_commSq
    (P' Q' : CochainComplex ModR ℤ) (q p : ℤ)
    (hQproj : ∀ p : ℤ, Projective (Q'.X p)) :
    CommSq
      ((secondDoubleComplexPageOneComplex (tensor_bicomplex (P := P') (Q := Q')) q).d p (p + 1))
      (tensor_bicomplex_second_pageOne_row_tensor_component_iso
        (P' := P') (Q' := Q') q p hQproj).hom
      (tensor_bicomplex_second_pageOne_row_tensor_component_iso
        (P' := P') (Q' := Q') q (p + 1) hQproj).hom
      ((second_pageOne_row_tensorRight_complex (P' := P') (Q' := Q') q).d p (p + 1)) := by
  refine ⟨?_⟩
  -- Proof comment: first use the unsigned row-homology naturality square, then multiply both
  -- sides by the common scalar `(-1)^q` and rewrite to the signed owners.
  simpa [secondDoubleComplexPageOneComplex_d, CochainComplex.of_d, Category.assoc,
    Linear.units_smul_comp, Linear.comp_units_smul] using
    congrArg (fun f ↦ q.negOnePow • f)
      (tensor_bicomplex_second_pageOne_row_tensor_homology_naturality
        (P' := P') (Q' := Q') q p hQproj)

/-- Helper for Example 15.62.4: the signed row-tensor differential compatibility extends to the
generic `isoOfComponents` relation needed for the complex isomorphism. -/
private theorem tensor_bicomplex_second_pageOne_row_tensor_d_commSq_of_rel
    (P' Q' : CochainComplex ModR ℤ) (q i j : ℤ)
    (hQproj : ∀ p : ℤ, Projective (Q'.X p))
    (hij : (ComplexShape.up ℤ).Rel i j) :
    CommSq
      ((secondDoubleComplexPageOneComplex (tensor_bicomplex (P := P') (Q := Q')) q).d i j)
      (tensor_bicomplex_second_pageOne_row_tensor_component_iso
        (P' := P') (Q' := Q') q i hQproj).hom
      (tensor_bicomplex_second_pageOne_row_tensor_component_iso
        (P' := P') (Q' := Q') q j hQproj).hom
      ((second_pageOne_row_tensorRight_complex (P' := P') (Q' := Q') q).d i j) := by
  have hj : j = i + 1 := by
    simpa [ComplexShape.up, eq_comm] using hij
  subst hj
  exact tensor_bicomplex_second_pageOne_row_tensor_d_commSq
    (P' := P') (Q' := Q') q i hQproj

/-- Helper for Example 15.62.4: the second page-one complex of the tensor bicomplex first
normalizes to the fixed-`q` row-tensor owner before the final tensor-with-single comparison. -/
private noncomputable def tensor_bicomplex_second_pageOne_row_tensor_iso
    (P' Q' : CochainComplex ModR ℤ) (q : ℤ)
    (hQproj : ∀ p : ℤ, Projective (Q'.X p)) :
    secondDoubleComplexPageOneComplex (tensor_bicomplex (P := P') (Q := Q')) q ≅
      second_pageOne_row_tensorRight_complex (P' := P') (Q' := Q') q :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p ↦
      tensor_bicomplex_second_pageOne_row_tensor_component_iso
        (P' := P') (Q' := Q') q p hQproj)
    (fun i j hij ↦
      tensor_bicomplex_second_pageOne_row_tensor_d_commSq_of_rel
        (P' := P') (Q' := Q') q i j hQproj hij)

/-- Helper for Example 15.62.4: if the left index of the tensor totalization comes from a
degree of the single complex other than `0`, the corresponding summand is zero. -/
private theorem tensorObj_single_zero_right_summand_isZero
    (M : ModR) (Q' : CochainComplex ModR ℤ) {i j : ℤ} (hi : i ≠ 0) :
    Limits.IsZero (((curriedTensor ModR).obj (((singleCpx₀).obj M).X i)).obj (Q'.X j)) := by
  let F : ModR ⥤ ModR := (curriedTensor ModR).flip.obj (Q'.X j)
  -- The only nonzero degree of the single complex is degree `0`, so any other tensor summand
  -- vanishes after applying the fixed-right tensor functor.
  have hzero : Limits.IsZero (((singleCpx₀).obj M).X i) :=
    HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M i hi
  change Limits.IsZero (F.obj (((singleCpx₀).obj M).X i))
  exact F.map_isZero hzero

/-- Helper for Example 15.62.4: after removing the extra sign twist, the row tensor complex is the
canonical tensor of the degree-zero single complex with `Q'`. -/
private noncomputable def tensorObj_single_zero_right_complex_iso
    (M : ModR) (Q' : CochainComplex ModR ℤ) :
    (((curriedTensor ModR).obj M).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q' ≅
      HomologicalComplex.tensorObj ((singleCpx₀).obj M) Q' :=
  ((NatIso.mapHomologicalComplex
      (BraidedCategory.tensorLeftIsoTensorRight M) (ComplexShape.up ℤ)).app Q') ≪≫
    (tensorObj_right_single_zero_complex_iso Q' M).symm ≪≫
      β_ Q' ((singleCpx₀).obj M)

/-- Helper for Example 15.62.4: the degreewise sign-conjugation on the `q`-twisted complex squares
to the identity in each degree. -/
private theorem cochain_complex_negOnePow_twist_component_hom_inv_id
    (C : CochainComplex ModR ℤ) (q p : ℤ) :
    (((p * q).negOnePow : ℤˣ) • (𝟙 (C.X p))) ≫
        (((p * q).negOnePow : ℤˣ) • (𝟙 (C.X p))) =
      𝟙 (C.X p) := by
  -- Proof comment: the degreewise sign is an involution because `((-1)^n)^2 = 1`.
  simpa [Linear.units_smul_comp, Int.negOnePow_mul_self]

/-- Helper for Example 15.62.4: in each degree, the `q`-twisted complex is canonically identified
with the original complex by multiplying by `(-1)^{pq}`. -/
private noncomputable def cochain_complex_negOnePow_twist_component_iso
    (C : CochainComplex ModR ℤ) (q p : ℤ) :
    (CochainComplex.of C.X (fun p ↦ q.negOnePow • C.d p (p + 1))
      (cochain_complex_units_smul_sq C q.negOnePow)).X p ≅ C.X p :=
  { hom := ((p * q).negOnePow : ℤˣ) • (𝟙 (C.X p))
    inv := ((p * q).negOnePow : ℤˣ) • (𝟙 (C.X p))
    hom_inv_id := cochain_complex_negOnePow_twist_component_hom_inv_id C q p
    inv_hom_id := cochain_complex_negOnePow_twist_component_hom_inv_id C q p }

/-- Helper for Example 15.62.4: the degreewise sign conjugation transports the twisted
differential back to the original differential. -/
private theorem cochain_complex_negOnePow_twist_d_commSq
    (C : CochainComplex ModR ℤ) (q p : ℤ) :
    CommSq
      ((CochainComplex.of C.X (fun p ↦ q.negOnePow • C.d p (p + 1))
          (cochain_complex_units_smul_sq C q.negOnePow)).d p (p + 1))
      (cochain_complex_negOnePow_twist_component_iso C q p).hom
      (cochain_complex_negOnePow_twist_component_iso C q (p + 1)).hom
      (C.d p (p + 1)) := by
  refine ⟨?_⟩
  have hpq : (p + 1) * q = p * q + q := by ring
  have hsign :
      q.negOnePow * ((((p + 1) * q).negOnePow : ℤˣ)) = ((p * q).negOnePow : ℤˣ) := by
    -- Proof comment: rewrite the exponent as `p * q + q`, split `(-1)^(a+b)`, and cancel the
    -- duplicated `(-1)^q` using its involutivity.
    rw [hpq, Int.negOnePow_add]
    calc
      q.negOnePow * (((p * q).negOnePow : ℤˣ) * q.negOnePow)
          = ((p * q).negOnePow : ℤˣ) * (q.negOnePow * q.negOnePow) := by
              simp [mul_assoc, mul_left_comm, mul_comm]
      _ = ((p * q).negOnePow : ℤˣ) := by
            simp [Int.negOnePow_mul_self]
  -- Proof comment: both component isomorphisms are scalar multiples of the identity, so the
  -- differential square reduces to the scalar identity `hsign`.
  simpa [CochainComplex.of_d, cochain_complex_negOnePow_twist_component_iso, Category.assoc,
    Linear.units_smul_comp, Linear.comp_units_smul, hsign, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Example 15.62.4: the sign-conjugation differential square also extends to the
general relation needed by `isoOfComponents`. -/
private theorem cochain_complex_negOnePow_twist_d_commSq_of_rel
    (C : CochainComplex ModR ℤ) (q i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    CommSq
      ((CochainComplex.of C.X (fun p ↦ q.negOnePow • C.d p (p + 1))
          (cochain_complex_units_smul_sq C q.negOnePow)).d i j)
      (cochain_complex_negOnePow_twist_component_iso C q i).hom
      (cochain_complex_negOnePow_twist_component_iso C q j).hom
      (C.d i j) := by
  have hj : j = i + 1 := by
    simpa [ComplexShape.up, eq_comm] using hij
  subst hj
  exact cochain_complex_negOnePow_twist_d_commSq C q i

/-- Helper for Example 15.62.4: twisting every differential of a cochain complex by the constant
sign `(-1)^q` yields an isomorphic complex via the standard degreewise sign conjugation. -/
private noncomputable def cochain_complex_negOnePow_twist_iso
    (C : CochainComplex ModR ℤ) (q : ℤ) :
    CochainComplex.of C.X (fun p ↦ q.negOnePow • C.d p (p + 1))
      (cochain_complex_units_smul_sq C q.negOnePow) ≅ C :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ cochain_complex_negOnePow_twist_component_iso C q p)
    (fun i j hij ↦ cochain_complex_negOnePow_twist_d_commSq_of_rel C q i j hij)

/-- Helper for Example 15.62.4: the fixed-`q` signed row-tensor complex should next be identified
with the canonical tensor-with-single complex. -/
private noncomputable def second_pageOne_row_tensorRight_to_tensorObj_single_iso
    (P' Q' : CochainComplex ModR ℤ) (q : ℤ) :
    second_pageOne_row_tensorRight_complex (P' := P') (Q' := Q') q ≅
      HomologicalComplex.tensorObj ((singleCpx₀).obj (P'.homology q)) Q' :=
  cochain_complex_negOnePow_twist_iso
      ((((curriedTensor ModR).obj (P'.homology q)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Q') q ≪≫
    tensorObj_single_zero_right_complex_iso (P'.homology q) Q'

private noncomputable def tensor_bicomplex_second_pageOne_complex_iso
    (P' Q' : CochainComplex ModR ℤ) (q : ℤ)
    (hQproj : ∀ p : ℤ, Projective (Q'.X p)) :
    secondDoubleComplexPageOneComplex (tensor_bicomplex (P := P') (Q := Q')) q ≅
      HomologicalComplex.tensorObj ((singleCpx₀).obj (P'.homology q)) Q' :=
  tensor_bicomplex_second_pageOne_row_tensor_iso (P' := P') (Q' := Q') q hQproj ≪≫
    second_pageOne_row_tensorRight_to_tensorObj_single_iso (P' := P') (Q' := Q') q

/-- Helper for Example 15.62.4: the chain-level homology of a projective model matches the
derived-category cohomology object placed in degree `0`. -/
private noncomputable def singleFunctor_iso_of_projective_resolution_homology
    (X : DModMinus) (P : CochainComplex ModR ℤ)
    (eP : DerivedCategory.Q.obj P ≅ X.obj) (q : ℤ) :
    DerivedCategory.Q.obj ((singleCpx₀).obj (P.homology q)) ≅
      (single₀).obj ((H q).obj X.obj) :=
  -- First move the degree-zero single complex through `Q`, then rewrite the module in degree
  -- zero by the standard comparison from ordinary homology of `P` to derived cohomology of `X`.
  ((DerivedCategory.singleFunctorIsoCompQ ModR (0 : ℤ)).app (P.homology q)).symm ≪≫
    (single₀).mapIso
      (((DerivedCategory.homologyFunctorFactors ModR q).app P).symm ≪≫
        (H q).mapIso eP)

/-- Helper for Example 15.62.4: the `p`-th homology of tensoring the projective model `P'` with
the degree-zero complex on `H^q(L^•)` is the displayed right-hand `E₂`-term. -/
private theorem tensorObj_projective_model_single_homology_iso_rightDerivedTensorPageTwo
    (K L : DModMinus)
    (P' Q' : CochainComplex ModR ℤ)
    (eP : DerivedCategory.Q.obj P' ≅ K.obj)
    (eQ : DerivedCategory.Q.obj Q' ≅ L.obj)
    (p q : ℤ) :
    Nonempty
      ((HomologicalComplex.tensorObj P' ((singleCpx₀).obj (Q'.homology q))).homology
          p ≅
        rightDerivedTensorPageTwo K L p q) := by
  let eSingleQ :
      DerivedCategory.Q.obj ((singleCpx₀).obj (Q'.homology q)) ≅
        (single₀).obj ((H q).obj L.obj) :=
    singleFunctor_iso_of_projective_resolution_homology (X := L) (P := Q') eQ q
  let eTensor :
      DerivedCategory.Q.obj
          (HomologicalComplex.tensorObj P' ((singleCpx₀).obj (Q'.homology q))) ≅
        K.obj ⊗[R]^L ((single₀).obj ((H q).obj L.obj)) :=
    (Functor.Monoidal.μIso (DerivedCategory.Q : CochainComplex ModR ℤ ⥤ DerivedCategory ModR)
        P' ((singleCpx₀).obj (Q'.homology q))).symm ≪≫
      (eP ⊗ᵢ eSingleQ) ≪≫
        derivedCategory_tensorObj_iso_derivedTensorProduct
          K.obj ((single₀).obj ((H q).obj L.obj))
  refine ⟨?_⟩
  -- First pass from chain-level homology to the derived-category cohomology of the localized
  -- tensor-with-single complex, then transport the derived object to the displayed page-two term.
  exact
    ((DerivedCategory.homologyFunctorFactors ModR p).app
      (HomologicalComplex.tensorObj P' ((singleCpx₀).obj (Q'.homology q)))).symm ≪≫
      (H p).mapIso eTensor

/-- Helper for Example 15.62.4: once the first associated `E₂`-page is normalized to the Chapter
12 owner, the resulting textbook page-two term computes the displayed right derived-tensor page. -/
private theorem first_doubleComplex_pageTwo_iso_rightDerivedTensorPageTwo
    (K L : DModMinus)
    (P : CochainComplex.ProjectiveResolution (DerivedCategory.Q.objPreimage K.obj))
    (Q : CochainComplex.ProjectiveResolution (DerivedCategory.Q.objPreimage L.obj))
    (eP : DerivedCategory.Q.obj (P : CochainComplex ModR ℤ) ≅ K.obj)
    (eQ : DerivedCategory.Q.obj (Q : CochainComplex ModR ℤ) ≅ L.obj)
    (p q : ℤ) :
    Nonempty
      (firstDoubleComplexPageTwo
          (tensor_bicomplex (P := (P : CochainComplex ModR ℤ))
            (Q := (Q : CochainComplex ModR ℤ)))
          p q ≅
        rightDerivedTensorPageTwo K L p q) := by
  let P' : CochainComplex ModR ℤ := (P : CochainComplex ModR ℤ)
  let Q' : CochainComplex ModR ℤ := (Q : CochainComplex ModR ℤ)
  let hPproj : ∀ i : ℤ, Projective (P'.X i) := fun i ↦ by infer_instance
  let ePageOne :
      firstDoubleComplexPageOneComplex (tensor_bicomplex (P := P') (Q := Q')) q ≅
        HomologicalComplex.tensorObj P' ((singleCpx₀).obj (Q'.homology q)) :=
    tensor_bicomplex_first_pageOne_complex_iso (P' := P') (Q' := Q') q hPproj
  obtain ⟨eTensorPageTwo⟩ :=
    tensorObj_projective_model_single_homology_iso_rightDerivedTensorPageTwo
      (K := K) (L := L) (P' := P') (Q' := Q') eP eQ p q
  refine ⟨?_⟩
  -- First normalize the textbook `E₂` owner to the `p`-th homology of the tensor-with-single
  -- complex. Then pass through `Q` and transport the localized tensor complex to the displayed
  -- derived tensor product with `H^q(L)`.
  simpa [firstDoubleComplexPageTwo_def, rightDerivedTensorPageTwo, P', Q'] using
    ((HomologicalComplex.homologyMapIso ePageOne p) ≪≫ eTensorPageTwo)

/-- Helper for Example 15.62.4: the `p`-th homology of tensoring the degree-zero complex on
`H^q(K^•)` with the projective model `Q'` is the displayed left-hand `E₂`-term. -/
private theorem single_projective_model_tensor_homology_iso_leftDerivedTensorPageTwo
    (K L : DModMinus)
    (P' Q' : CochainComplex ModR ℤ)
    (eP : DerivedCategory.Q.obj P' ≅ K.obj)
    (eQ : DerivedCategory.Q.obj Q' ≅ L.obj)
    (p q : ℤ) :
    Nonempty
      ((HomologicalComplex.tensorObj ((singleCpx₀).obj (P'.homology q)) Q').homology
          p ≅
        leftDerivedTensorPageTwo K L p q) := by
  let eSingleP :
      DerivedCategory.Q.obj ((singleCpx₀).obj (P'.homology q)) ≅
        (single₀).obj ((H q).obj K.obj) :=
    singleFunctor_iso_of_projective_resolution_homology (X := K) (P := P') eP q
  let eTensor :
      DerivedCategory.Q.obj
          (HomologicalComplex.tensorObj ((singleCpx₀).obj (P'.homology q)) Q') ≅
        ((single₀).obj ((H q).obj K.obj)) ⊗[R]^L L.obj :=
    (Functor.Monoidal.μIso (DerivedCategory.Q : CochainComplex ModR ℤ ⥤ DerivedCategory ModR)
        ((singleCpx₀).obj (P'.homology q)) Q').symm ≪≫
      (eSingleP ⊗ᵢ eQ) ≪≫
        derivedCategory_tensorObj_iso_derivedTensorProduct
          ((single₀).obj ((H q).obj K.obj)) L.obj
  refine ⟨?_⟩
  -- This is the left-handed analogue of the previous transport: rewrite chain homology as
  -- derived cohomology after localizing, then replace the localized tensor by the derived tensor.
  exact
    ((DerivedCategory.homologyFunctorFactors ModR p).app
      (HomologicalComplex.tensorObj ((singleCpx₀).obj (P'.homology q)) Q')).symm ≪≫
      (H p).mapIso eTensor

/-- Helper for Example 15.62.4: the second textbook `E₂`-page term computes the displayed left
derived-tensor page. -/
private theorem second_doubleComplex_pageTwo_iso_leftDerivedTensorPageTwo
    (K L : DModMinus)
    (P : CochainComplex.ProjectiveResolution (DerivedCategory.Q.objPreimage K.obj))
    (Q : CochainComplex.ProjectiveResolution (DerivedCategory.Q.objPreimage L.obj))
    (eP : DerivedCategory.Q.obj (P : CochainComplex ModR ℤ) ≅ K.obj)
    (eQ : DerivedCategory.Q.obj (Q : CochainComplex ModR ℤ) ≅ L.obj)
    (p q : ℤ) :
    Nonempty
      (secondDoubleComplexPageTwo
          (tensor_bicomplex (P := (P : CochainComplex ModR ℤ))
            (Q := (Q : CochainComplex ModR ℤ)))
          p q ≅
        leftDerivedTensorPageTwo K L p q) := by
  let P' : CochainComplex ModR ℤ := (P : CochainComplex ModR ℤ)
  let Q' : CochainComplex ModR ℤ := (Q : CochainComplex ModR ℤ)
  let hQproj : ∀ i : ℤ, Projective (Q'.X i) := fun i ↦ by infer_instance
  let ePageOne :
      secondDoubleComplexPageOneComplex (tensor_bicomplex (P := P') (Q := Q')) q ≅
        HomologicalComplex.tensorObj ((singleCpx₀).obj (P'.homology q)) Q' :=
    tensor_bicomplex_second_pageOne_complex_iso (P' := P') (Q' := Q') q hQproj
  obtain ⟨eTensorPageTwo⟩ :=
    single_projective_model_tensor_homology_iso_leftDerivedTensorPageTwo
      (K := K) (L := L) (P' := P') (Q' := Q') eP eQ p q
  refine ⟨?_⟩
  -- Once the second page-one complex is normalized, the left `E₂`-page is the `p`-th homology
  -- of the tensor-with-single complex, transported through `Q` to the derived tensor product.
  simpa [secondDoubleComplexPageTwo_def, leftDerivedTensorPageTwo, P', Q'] using
    ((HomologicalComplex.homologyMapIso ePageOne p) ≪≫ eTensorPageTwo)

/-- Helper for Example 15.62.4: the first associated spectral sequence of the tensor bicomplex
has `E₂`-page `H^p(K^• \otimes_R^{\mathbf L} H^q(L^•))`. -/
private theorem first_tensor_bicomplex_pageTwo_iso
    (K L : DModMinus)
    (P : CochainComplex.ProjectiveResolution (DerivedCategory.Q.objPreimage K.obj))
    (Q : CochainComplex.ProjectiveResolution (DerivedCategory.Q.objPreimage L.obj))
    (eP : DerivedCategory.Q.obj (P : CochainComplex ModR ℤ) ≅ K.obj)
    (eQ : DerivedCategory.Q.obj (Q : CochainComplex ModR ℤ) ≅ L.obj)
    (E : CohomologicalSpectralSequence ModR 0)
    [IsAssociatedToFilteredComplex
      (firstDoubleComplexFilteredComplex
        (tensor_bicomplex (P := (P : CochainComplex ModR ℤ))
          (Q := (Q : CochainComplex ModR ℤ)))) E] :
    ∀ p q : ℤ,
      Nonempty ((E.page 2).X (p, q) ≅ rightDerivedTensorPageTwo K L p q) := by
  intro p q
  obtain ⟨eAssoc⟩ :=
    first_associated_pageTwo_iso_of_firstDoubleComplex
      (K := tensor_bicomplex (P := (P : CochainComplex ModR ℤ))
        (Q := (Q : CochainComplex ModR ℤ))) (E := E) p q
  obtain ⟨ePageTwo⟩ :=
    first_doubleComplex_pageTwo_iso_rightDerivedTensorPageTwo K L P Q eP eQ p q
  -- Proof comment: compose the generic associated `E₂` comparison for the first filtration with
  -- the tensor-bicomplex computation of the resulting textbook page-two term.
  exact ⟨eAssoc ≪≫ ePageTwo⟩

/-- Helper for Example 15.62.4: the second associated spectral sequence of the tensor bicomplex
has `E₂`-page `H^p(H^q(K^•) \otimes_R^{\mathbf L} L^•)`. -/
private theorem second_tensor_bicomplex_pageTwo_iso
    (K L : DModMinus)
    (P : CochainComplex.ProjectiveResolution (DerivedCategory.Q.objPreimage K.obj))
    (Q : CochainComplex.ProjectiveResolution (DerivedCategory.Q.objPreimage L.obj))
    (eP : DerivedCategory.Q.obj (P : CochainComplex ModR ℤ) ≅ K.obj)
    (eQ : DerivedCategory.Q.obj (Q : CochainComplex ModR ℤ) ≅ L.obj)
    (E : CohomologicalSpectralSequence ModR 0)
    [IsAssociatedToFilteredComplex
      (secondDoubleComplexFilteredComplex
        (tensor_bicomplex (P := (P : CochainComplex ModR ℤ))
          (Q := (Q : CochainComplex ModR ℤ)))) E] :
    ∀ p q : ℤ,
      Nonempty ((E.page 2).X (p, q) ≅ leftDerivedTensorPageTwo K L p q) := by
  intro p q
  obtain ⟨eAssoc⟩ :=
    second_associated_pageTwo_iso_of_secondDoubleComplex
      (K := tensor_bicomplex (P := (P : CochainComplex ModR ℤ))
        (Q := (Q : CochainComplex ModR ℤ))) (E := E) p q
  obtain ⟨ePageTwo⟩ :=
    second_doubleComplex_pageTwo_iso_leftDerivedTensorPageTwo K L P Q eP eQ p q
  -- Proof comment: the second associated spectral sequence is handled by the same two-step
  -- transport: first to the textbook second page-two owner, then to the displayed derived tensor
  -- term.
  exact ⟨eAssoc ≪≫ ePageTwo⟩

/-- Helper for Example 15.62.4: the total complex of the tensor bicomplex computes the cohomology
of `K^• \otimes_R^{\mathbf L} L^•`. -/
private theorem tensor_bicomplex_total_abutment_iso
    (K L : DModMinus)
    (P : CochainComplex.ProjectiveResolution (DerivedCategory.Q.objPreimage K.obj))
    (Q : CochainComplex.ProjectiveResolution (DerivedCategory.Q.objPreimage L.obj))
    (eP : DerivedCategory.Q.obj (P : CochainComplex ModR ℤ) ≅ K.obj)
    (eQ : DerivedCategory.Q.obj (Q : CochainComplex ModR ℤ) ≅ L.obj) :
    ∀ n : ℤ,
      Nonempty
        ((HomologicalComplex₂.total
            (tensor_bicomplex (P := (P : CochainComplex ModR ℤ))
              (Q := (Q : CochainComplex ModR ℤ)))
            (ComplexShape.up ℤ)).homology n ≅
          derivedTensorCohomologyAbutment K L n) := by
  intro n
  let P' : CochainComplex ModR ℤ := (P : CochainComplex ModR ℤ)
  let Q' : CochainComplex ModR ℤ := (Q : CochainComplex ModR ℤ)
  obtain ⟨eTot⟩ := tensor_bicomplex_total_iso_tensorObj (P := P') (Q := Q')
  obtain ⟨eAbutment⟩ := tensorObj_projective_model_homology_iso_derivedTensor_abutment
    (K := K) (L := L) (P' := P') (Q' := Q') eP eQ n
  refine ⟨?_⟩
  -- Route correction: the remaining abutment transport is now flat. First identify the total
  -- tensor bicomplex with the ordinary tensor complex, then apply the packaged monoidal `Q`
  -- comparison from the tensor complex of the projective models to `K ⊗[R]^L L`.
  exact (HomologicalComplex.homologyMapIso eTot n) ≪≫ eAbutment

-- Proof sketch: replace `K^•` and `L^•` by bounded-above complexes of projective `R`-modules and
-- apply the two spectral sequences of Homology, Section `12.25` to the double complex
-- `Tot(K^• ⊗_R L^•)`. The projective replacements compute the same derived tensor product, so the
-- two `E₂`-pages identify with `H^p(K^• \otimes_R^{\mathbf L} H^q(L^•))` and
-- `H^p(H^q(K^•) \otimes_R^{\mathbf L} L^•)` respectively, and both abut to
-- `H^{p+q}(K^• \otimes_R^{\mathbf L} L^•)`.
/-- Example 15.62.4: for objects `K^•` and `L^•` of `D^{-}(R)`, there are two cohomological
spectral sequences converging to `H^{p+q}(K^• \otimes_R^{\mathbf L} L^•)`, one with
`E_2^{p,q} = H^p(K^• \otimes_R^{\mathbf L} H^q(L^•))` and the other with
`E_2^{p,q} = H^p(H^q(K^•) \otimes_R^{\mathbf L} L^•)`. Because both are cohomological spectral
sequences, their page-two differentials have bidegree `(2, -1)`, i.e.
`d_2^{p,q} : E_2^{p,q} → E_2^{p+2,q-1}`. -/
theorem exists_derivedTensor_cohomology_spectralSequences
    (K L : DModMinus) :
    ∃ E_right E_left : CohomologicalSpectralSequence ModR 0,
      IsRightCohomologyDerivedTensorSpectralSequence E_right K L ∧
        IsLeftCohomologyDerivedTensorSpectralSequence E_left K L := by
  -- Replace both derived objects by bounded-above projective models, as in the source proof.
  obtain ⟨P, a, hPstrict, ⟨eP⟩⟩ :=
    exists_projective_resolution_model_of_boundedAbove K
  obtain ⟨Q, b, hQstrict, ⟨eQ⟩⟩ :=
    exists_projective_resolution_model_of_boundedAbove L
  let I : HomologicalComplex₂ ModR (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
    tensor_bicomplex (P := (P : CochainComplex ModR ℤ)) (Q := (Q : CochainComplex ModR ℤ))
  let FI₁ : FilteredComplex ModR := firstDoubleComplexFilteredComplex I
  let FI₂ : FilteredComplex ModR := secondDoubleComplexFilteredComplex I
  let hI :
      doubleComplexHasFiniteAntidiagonalSupport I :=
    by
      simpa [I] using
        tensor_bicomplex_has_finite_antidiagonal_support_of_strictlyLE
          hPstrict hQstrict
  -- Next choose the two canonical associated spectral sequences of the tensor bicomplex.
  obtain ⟨E_right, hE_right_assoc⟩ := exists_filteredComplexAssociatedSpectralSequence FI₁
  obtain ⟨E_left, hE_left_assoc⟩ := exists_filteredComplexAssociatedSpectralSequence FI₂
  refine ⟨E_right, E_left, ?_, ?_⟩
  · letI : IsAssociatedToFilteredComplex FI₁ E_right := hE_right_assoc
    refine ⟨?_, ?_⟩
    · -- Route correction: the projective-model packaging is now complete, so the remaining gap is
      -- the explicit `E₂`-page comparison for the first filtration.
      intro p q
      simpa [FI₁, I] using
        first_tensor_bicomplex_pageTwo_iso K L P Q eP eQ E_right p q
    · -- Convergence already comes from Chapter 12 once finite antidiagonal support is established.
      refine ⟨FI₁, hE_right_assoc, ?_, ?_⟩
      · simpa [FI₁, I] using
          firstDoubleComplex_convergesToTotalCohomology_of_finiteAntidiagonalSupport I E_right hI
      · intro n
        simpa [FI₁, I] using tensor_bicomplex_total_abutment_iso K L P Q eP eQ n
  · letI : IsAssociatedToFilteredComplex FI₂ E_left := hE_left_assoc
    refine ⟨?_, ?_⟩
    · -- The second filtration is in the same state: convergence is settled, and only the `E₂`
      -- comparison remains to be transported to the derived tensor notation.
      intro p q
      simpa [FI₂, I] using
        second_tensor_bicomplex_pageTwo_iso K L P Q eP eQ E_left p q
    · refine ⟨FI₂, hE_left_assoc, ?_, ?_⟩
      · simpa [FI₂, I] using
          secondDoubleComplex_convergesToTotalCohomology_of_finiteAntidiagonalSupport I E_left hI
      · intro n
        simpa [FI₂, I] using tensor_bicomplex_total_abutment_iso K L P Q eP eQ n

end

end StacksProject
