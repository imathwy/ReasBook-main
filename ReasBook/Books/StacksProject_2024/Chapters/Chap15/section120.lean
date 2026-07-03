import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.Shift
import Mathlib.CategoryTheory.Triangulated.Subcategory

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_120_1 (from Chap15) -/
noncomputable section

open scoped BigOperators

open CategoryTheory
open CategoryTheory.Pretriangulated

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {R : Type u} [Ring R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "K₀" => projectiveGrothendieckGroup R

/- Domain-style sampling for Lemma 15.120.1:
- primary domain: Euler characteristics of perfect objects in the derived category, valued in the
  Grothendieck group of finite projective modules;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `CategoryTheory.DPerf`,
  `projectiveGrothendieckGroup`,
  `CategoryTheory.TriangulatedK0`;
- best owner abstraction:
  the source-facing notion here is an Euler-characteristic value attached to an object of the
  perfect derived category `DPerf R`, while the canonical later owner for the comparison theorem is
  the additive `K₀`-equivalence in Lemma `15.120.2`;
- primitive vs. derived:
  primitive data are a bounded finite-projective representative together with its canonical
  complex-level alternating sum in `K₀(R)`;
  interval formulas, the perfect-complex value predicate, and the canonical Euler characteristic
  with its shift/additivity lemmas are derived API built from that owner and the uniqueness
  statement;
- source/core/bridge triage:
  `source-facing`: the value predicate and its uniqueness statement for a perfect complex;
  `core/canonical`: `DPerf`, `projectiveGrothendieckGroup`, and later `TriangulatedK0`;
  `bridge/view`: the bounded finite-projective representative witnessing a source-facing value,
    together with its complex-level Euler characteristic.

The public source-facing predicate should therefore live on the chapter owner `DPerf` rather than
as a parallel global "perfect complex" wrapper name. -/

namespace CochainComplex

/-- The alternating-sum Euler-characteristic class of a bounded finite-projective cochain complex,
written canonically as a `finsum` in `K₀(R)`. -/
noncomputable def eulerCharacteristic
    (L : Cpx) [hL : IsBoundedFiniteProjective L] : projectiveGrothendieckGroup R :=
  ∑ᶠ i : ℤ,
    i.negOnePow •
      projectiveGrothendieckGroupOf R
        ⟨L.X i, ⟨hL.finite i, hL.projective i⟩⟩

/-- If an interval `[a, b]` contains all nonzero terms of a bounded finite-projective complex,
its canonical Euler-characteristic class is the corresponding finite alternating sum. -/
theorem eulerCharacteristic_eq_sum_Icc
    (L : Cpx) [hL : IsBoundedFiniteProjective L] {a b : ℤ}
    (hge : L.IsStrictlyGE a) (hle : L.IsStrictlyLE b) :
    L.eulerCharacteristic =
      Finset.sum (Finset.Icc a b) fun i ↦
        i.negOnePow •
          projectiveGrothendieckGroupOf R
            ⟨L.X i, ⟨hL.finite i, hL.projective i⟩⟩ := sorry

end CochainComplex

namespace CategoryTheory.DPerf

open CochainComplex DerivedCategory

/-- A class `c ∈ K₀(R)` is an Euler-characteristic value of a perfect derived `R`-complex `K`
if `K` is represented by a bounded finite-projective complex and `c` is the canonical
Euler-characteristic class of that representative. Equivalently, by
`CochainComplex.eulerCharacteristic_eq_sum_Icc`, `c` is the finite alternating sum over any
interval containing all nonzero terms of the representative. -/
def IsEulerCharacteristicValue
    (K : DPerf R) (c : K₀) : Prop :=
  ∃ (L : Cpx) (_ : K.obj ≅ DerivedCategory.Q.obj L) (_ : IsBoundedFiniteProjective L),
    c = L.eulerCharacteristic

-- Proof sketch: existence comes from choosing any bounded finite-projective representative of the
-- perfect complex and taking the alternating sum of its terms in `K₀(R)`. Uniqueness is the
-- well-definedness argument from the textbook: quasi-isomorphic bounded finite-projective
-- representatives have acyclic cone, and acyclic bounded finite-projective complexes contribute
-- zero in `K₀(R)`.
/-- Lemma 15.120.1: every perfect complex over `R` has a unique Euler-characteristic class in
`K₀(R)`, namely the alternating sum of the terms of any bounded finite-projective representative. -/
theorem existsUnique_isEulerCharacteristicValue
    (K : DPerf R) :
    ∃! c : K₀, K.IsEulerCharacteristicValue c := sorry

/-- The canonical Euler-characteristic class in `K₀(R)` attached to a perfect derived
`R`-complex. -/
noncomputable def eulerCharacteristic
    (K : DPerf R) : K₀ :=
  (K.existsUnique_isEulerCharacteristicValue).choose

/-- The canonical Euler-characteristic class satisfies the defining alternating-sum formula. -/
theorem eulerCharacteristic_spec
    (K : DPerf R) :
    K.IsEulerCharacteristicValue K.eulerCharacteristic := by
  exact (K.existsUnique_isEulerCharacteristicValue).choose_spec.1

/-- Any Euler-characteristic value of a perfect complex agrees with its canonical
Euler-characteristic class. -/
theorem eq_eulerCharacteristic
    {K : DPerf R} {c : K₀}
    (hc : K.IsEulerCharacteristicValue c) :
    c = K.eulerCharacteristic := by
  exact (K.existsUnique_isEulerCharacteristicValue).choose_spec.2 c hc

-- Proof sketch: shift a bounded finite-projective representative by `n`; its terms are the same
-- modules with all degrees translated by `n`, so the alternating sum is multiplied by the
-- canonical sign `(-1)^n`.
/-- Shifting a perfect complex multiplies its Euler-characteristic class by the canonical sign
`(-1)^n`. -/
theorem isEulerCharacteristicValue_shift
    {K : DPerf R} {c : K₀}
    (hc : K.IsEulerCharacteristicValue c) (n : ℤ) :
    (K⟦n⟧).IsEulerCharacteristicValue (n.negOnePow • c) := sorry

-- Proof sketch: the source-facing shift statement applied to the canonical value of `K` produces
-- a value for `K⟦n⟧`; uniqueness for `K⟦n⟧` then identifies that value with the canonical Euler
-- characteristic of the shift.
/-- Shifting a perfect complex multiplies its canonical Euler-characteristic class by the canonical
sign `(-1)^n`. -/
theorem eulerCharacteristic_shift
    (K : DPerf R) (n : ℤ) :
    (K⟦n⟧).eulerCharacteristic = n.negOnePow • K.eulerCharacteristic := sorry

-- Proof sketch: represent a distinguished triangle of perfect complexes by a short exact sequence
-- of bounded finite-projective complexes up to quasi-isomorphism. The termwise short exact
-- sequences split because the terms are projective, so the alternating sums satisfy the desired
-- additivity in `K₀(R)`.
/-- In a distinguished triangle of perfect complexes, the middle Euler-characteristic class is the
sum of the outer two classes. -/
theorem isEulerCharacteristicValue_add_of_distinguishedTriangle
    {T : Triangle (DPerf R)} (hT : T ∈ distTriang (DPerf R))
    {c₁ c₂ c₃ : K₀}
    (hc₁ : T.obj₁.IsEulerCharacteristicValue c₁)
    (hc₂ : T.obj₂.IsEulerCharacteristicValue c₂)
    (hc₃ : T.obj₃.IsEulerCharacteristicValue c₃) :
    c₂ = c₁ + c₃ := sorry

-- Proof sketch: apply the source-facing additivity statement to the canonical values of the
-- three vertices and use uniqueness on each object to identify those values with the owner-level
-- Euler characteristics.
/-- In a distinguished triangle of perfect complexes, the canonical Euler-characteristic classes
are additive. -/
theorem eulerCharacteristic_add_of_distinguishedTriangle
    {T : Triangle (DPerf R)} (hT : T ∈ distTriang (DPerf R)) :
    T.obj₂.eulerCharacteristic = T.obj₁.eulerCharacteristic + T.obj₃.eulerCharacteristic := sorry

end CategoryTheory.DPerf

end

/-! ### Lemma_15_120_2 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated

universe u v

set_option checkBinderAnnotations false

attribute [local instance] HasDerivedCategory.standard

section

variable (R : Type u) [Ring R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "K₀" => projectiveGrothendieckGroup R
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/- Domain-style sampling for Lemma 15.120.2:
- primary domain: the zeroth `K`-group of the perfect derived category and its comparison with the
  Grothendieck group of finite projective modules;
- sampled owner declarations:
  `CategoryTheory.TriangulatedK0`,
  `CategoryTheory.TriangulatedK0.lift`,
  `CategoryTheory.boundedDerivedCategoryK0Equiv`,
  `projectiveGrothendieckGroup`;
- best owner abstraction:
  the source-facing map is the Euler-characteristic homomorphism
  `K₀(D_{perf}(R)) → K₀(R)`, while the canonical owner for the identification itself is the
  additive equivalence between these two `K₀`-groups;
- primitive vs. derived:
  primitive data in this file are the two additive maps and the relation-killing lemmas needed to
  construct them;
  derived API is bijectivity and the resulting equivalence, so those should be built from the
  inverse laws rather than through a parallel proof path;
- source/core/bridge triage:
  `source-facing`: the bijectivity of the comparison map from `K₀(D_{perf}(R))` to `K₀(R)`;
  `core/canonical`: the additive equivalence between `TriangulatedK0 (DPerf R)` and
    `projectiveGrothendieckGroup R`;
  `bridge/view`: the degree-zero embedding of finite projective modules into `D_{perf}(R)` and
    the Euler-characteristic map in the opposite direction.

This file should therefore keep the source-facing bijectivity theorem, but organize the API around
the additive equivalence owner exactly as in the chapter's earlier `K₀` comparison files.
-/

-- Proof sketch: a distinguished triangle in `D_{perf}(R)` is distinguished after forgetting to
-- `D(R)`, and `DPerf.eulerCharacteristic_add_of_distinguishedTriangle` shows that the associated
-- triangulated relation maps to zero in `K₀(R)`.
/-- Distinguished-triangle relations in `K₀(D_{perf}(R))` are killed by the Euler-characteristic
generator map. -/
private theorem triangulatedK0Relations_le_ker_perfectDerivedCategoryK0 :
    TriangulatedK0.relations (DPerf R) ≤
      (FreeAbelianGroup.lift fun K : DPerf R ↦ K.eulerCharacteristic).ker := sorry

/-- The comparison homomorphism `c : K₀(D_{perf}(R)) → K₀(R)` sending a perfect complex to the
Euler characteristic of any bounded finite-projective representative. -/
noncomputable def perfectDerivedCategoryK0ToProjectiveGrothendieckGroup :
    TriangulatedK0 (DPerf R) →+ K₀ :=
  TriangulatedK0.lift
    DPerf.eulerCharacteristic
    (triangulatedK0Relations_le_ker_perfectDerivedCategoryK0 R)

/-- The Euler-characteristic map sends the class of a perfect complex to its canonical
Euler-characteristic class in `K₀(R)`. -/
@[simp] theorem perfectDerivedCategoryK0ToProjectiveGrothendieckGroup_apply_of
    (K : DPerf R) :
    perfectDerivedCategoryK0ToProjectiveGrothendieckGroup R (TriangulatedK0.of K) =
      K.eulerCharacteristic := by
  simpa [perfectDerivedCategoryK0ToProjectiveGrothendieckGroup] using
    TriangulatedK0.lift_of
      (fun K : DPerf R ↦ K.eulerCharacteristic)
      (triangulatedK0Relations_le_ker_perfectDerivedCategoryK0 R)
      K

/-- The degree-zero perfect complex attached to a finite projective `R`-module, viewed as an
object of `D_{perf}(R)`. -/
abbrev finiteProjectiveModule_singleInPerfectDerived (M : FiniteProjectiveModuleCat R) :
    DPerf R :=
  ⟨(single₀).obj M.obj, finiteProjectiveModule_single_isPerfect R M⟩

-- Proof sketch: a short exact sequence of finite projective modules yields a distinguished
-- triangle of the associated degree-zero complexes in `D(R)`, so the defining Grothendieck
-- relation maps to zero in `K₀(D_{perf}(R))`.
/-- The Grothendieck relations of finite projective modules are killed after passing to degree-zero
perfect complexes. -/
private theorem projectiveGrothendieckGroup_relations_le_ker_toPerfectDerivedCategoryK0 :
    modulePropertyK0Relations R (finiteProjectiveModuleProperty R) ≤
      (FreeAbelianGroup.lift fun M : FiniteProjectiveModuleCat R ↦
        TriangulatedK0.of (finiteProjectiveModule_singleInPerfectDerived R M)).ker := sorry

/-- The map `K₀(R) → K₀(D_{perf}(R))` sending `[M]` to the class of the degree-zero perfect
complex `M[0]`. -/
noncomputable def projectiveGrothendieckGroupToPerfectDerivedCategoryK0 :
    K₀ →+ TriangulatedK0 (DPerf R) :=
  ModulePropertyK0.lift R
    (fun M : FiniteProjectiveModuleCat R ↦
      TriangulatedK0.of (finiteProjectiveModule_singleInPerfectDerived R M))
    (projectiveGrothendieckGroup_relations_le_ker_toPerfectDerivedCategoryK0 R)

/-- The degree-zero map sends the class of a finite projective module to the class of its
degree-zero perfect complex. -/
@[simp] theorem projectiveGrothendieckGroupToPerfectDerivedCategoryK0_apply_of
    (M : FiniteProjectiveModuleCat R) :
    projectiveGrothendieckGroupToPerfectDerivedCategoryK0 R
        (projectiveGrothendieckGroupOf R M) =
      TriangulatedK0.of (finiteProjectiveModule_singleInPerfectDerived R M) := by
  simpa [projectiveGrothendieckGroupToPerfectDerivedCategoryK0] using
    ModulePropertyK0.lift_of R
      (fun M : FiniteProjectiveModuleCat R ↦
        TriangulatedK0.of (finiteProjectiveModule_singleInPerfectDerived R M))
      (projectiveGrothendieckGroup_relations_le_ker_toPerfectDerivedCategoryK0 R)
      M

-- Proof sketch: on a generator `[M]` of `K₀(R)`, the composite sends `M` to `M[0]` and then
-- applies the Euler-characteristic map, which returns `[M]` because the complex has exactly one
-- nonzero term in degree `0`. The quotient presentation then gives the identity everywhere.
/-- The degree-zero map on `K₀` is a right inverse to the Euler-characteristic map. -/
theorem projectiveGrothendieckGroupToPerfectDerivedCategoryK0_rightInverse :
    Function.RightInverse
      (projectiveGrothendieckGroupToPerfectDerivedCategoryK0 R)
      (perfectDerivedCategoryK0ToProjectiveGrothendieckGroup R) := sorry

-- Proof sketch: represent a perfect object by a bounded finite-projective complex. The stupid
-- truncation triangles express its `K₀(D_{perf}(R))`-class as the alternating sum of the degree-
-- zero classes of its terms, exactly matching the chosen Euler-characteristic class in `K₀(R)`.
/-- The degree-zero map `K₀(R) → K₀(D_{perf}(R))` is a left inverse to the Euler-characteristic
comparison map. -/
theorem projectiveGrothendieckGroupToPerfectDerivedCategoryK0_leftInverse :
    Function.LeftInverse
      (projectiveGrothendieckGroupToPerfectDerivedCategoryK0 R)
      (perfectDerivedCategoryK0ToProjectiveGrothendieckGroup R) := sorry

-- Proof sketch: the previous two theorems exhibit explicit two-sided inverses between the
-- comparison map `K₀(D_{perf}(R)) → K₀(R)` and the degree-zero map `K₀(R) → K₀(D_{perf}(R))`,
-- so the comparison map is bijective.
/-- Lemma 15.120.2: the comparison map `c : K₀(D_{perf}(R)) → K₀(R)` from the perfect derived
category is bijective, hence identifies `K₀(D_{perf}(R))` with `K₀(R)`. -/
theorem perfectDerivedCategoryK0ToProjectiveGrothendieckGroup_bijective :
    Function.Bijective (perfectDerivedCategoryK0ToProjectiveGrothendieckGroup R) := by
  refine ⟨?_, ?_⟩
  · exact Function.LeftInverse.injective
      (projectiveGrothendieckGroupToPerfectDerivedCategoryK0_leftInverse R)
  · exact Function.RightInverse.surjective
      (projectiveGrothendieckGroupToPerfectDerivedCategoryK0_rightInverse R)

/-- The canonical additive equivalence between `K₀(D_{perf}(R))` and `K₀(R)` induced by the
comparison map. -/
noncomputable def perfectDerivedCategoryK0Equiv :
    TriangulatedK0 (DPerf R) ≃+ K₀ :=
  { toFun := perfectDerivedCategoryK0ToProjectiveGrothendieckGroup R
    invFun := projectiveGrothendieckGroupToPerfectDerivedCategoryK0 R
    left_inv := projectiveGrothendieckGroupToPerfectDerivedCategoryK0_leftInverse R
    right_inv := projectiveGrothendieckGroupToPerfectDerivedCategoryK0_rightInverse R
    map_add' := (perfectDerivedCategoryK0ToProjectiveGrothendieckGroup R).map_add }

end
