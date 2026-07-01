import Mathlib
import stacks_project.Chap12.Lemma_12_25_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape HomologicalComplex HomologicalComplex₂
open scoped HomologicalComplex₂

universe v u

noncomputable section

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜] [CategoryTheory.Limits.HasZeroObject 𝒜]

local notation "single₀" => CochainComplex.singleFunctor (CochainComplex 𝒜 ℤ) (0 : ℤ)

/- Domain-style sampling for Lemma 12.25.5:
- primary domain: cohomological bicomplexes, total complexes, and homotopy equivalences;
- sampled owner declarations:
  `doubleComplexZeroColumnToTotal`,
  `HomologicalComplex₂.total`,
  `HomologicalComplex₂.totalFunctor`,
  `Functor.mapHomotopyEquiv`,
  `HomotopyEquiv`;
- source/core/bridge triage:
  `source-facing`: the comparison map induced by `a : M^•[0] ⟶ A^{•,•}`;
  `core/canonical`: `Tot(A)` / `totalFunctor 𝒜 (up ℤ) (up ℤ) (up ℤ)` together with
    `doubleComplexZeroColumnToTotal` and `Functor.mapHomotopyEquiv`;
  `bridge/view`: the degree-zero column map extracted from `a`.

Primitive data:
- a bicomplex morphism `a : (single₀).obj M ⟶ A`;
- its degree-zero column map `M^• ⟶ A.X 0`.

Derived API:
- the source-facing comparison map `M^• ⟶ Tot(A)`,
- its compatibility with the owner morphism `total.map`.
-/

/-- The degree-zero column map extracted from `a : M^•[0] ⟶ A^{•,•}`. -/
noncomputable def singleZeroToZeroColumn
    {M : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)}
    (a : (single₀).obj M ⟶ A) :
    M ⟶ A.X 0 :=
  (singleObjXSelf (up ℤ) 0 M).inv ≫ a.f 0

/-- The cycle condition on the degree-zero column induced by `a`. -/
private theorem singleZeroToZeroColumn_comp_d
    {M : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)}
    (a : (single₀).obj M ⟶ A) :
    ∀ p : ℤ, (singleZeroToZeroColumn a).f p ≫ (A.d 0 1).f p = 0 := by
  sorry

/-- The comparison map `α : M^• ⟶ \mathrm{Tot}(A^{•,•})` attached to a bicomplex morphism
`a : M^•[0] ⟶ A^{•,•}`. -/
noncomputable def singleZeroToTotal
    {M : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    (a : (single₀).obj M ⟶ A) :
    M ⟶ Tot(A) :=
  doubleComplexZeroColumnToTotal (singleZeroToZeroColumn a) (singleZeroToZeroColumn_comp_d a)

/-- The source-facing comparison map is functorial in the target bicomplex map, and the
comparison with the owner totalization functor is the canonical map `total.map`. -/
theorem singleZeroToTotal_comp_map
    {M : CochainComplex 𝒜 ℤ}
    {A B : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)] [B.HasTotal (up ℤ)]
    (a : (single₀).obj M ⟶ A) (b : A ⟶ B) :
    singleZeroToTotal (a ≫ b) =
      singleZeroToTotal a ≫ total.map b (up ℤ) := by
  sorry

-- Proof sketch: transport `a` through the owner totalization functor, use
-- `Functor.mapHomotopyEquiv` on a homotopy inverse of `a`, and compare the resulting map
-- `Tot(M^•[0]) ⟶ Tot(A)` with the canonical zero-column comparison `singleZeroToTotal a`.
/-- Lemma 12.25.5: if `a : M^•[0] ⟶ A^{•,•}` is a homotopy equivalence of cohomological
complexes of cochain complexes, then the induced comparison map
`α : M^• ⟶ \mathrm{Tot}(A^{•,•})` coming from the degree-zero column `M^• ⟶ A^{0,•}` is a
homotopy equivalence. -/
theorem singleZeroToTotal_homotopyEquivalence_of_homotopyEquivalence
    {M : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    {a : (single₀).obj M ⟶ A}
    (ha : homotopyEquivalences (CochainComplex 𝒜 ℤ) (up ℤ) a) :
    homotopyEquivalences 𝒜 (up ℤ) (singleZeroToTotal a) := sorry

end
