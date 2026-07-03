import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.Shift
import Mathlib.CategoryTheory.Triangulated.Subcategory
import StacksProject_2024.Chap13.Lemma_13_28_2
import StacksProject_2024.Chap10.Lemma_10_55_6
import StacksProject_2024.Chap15.Definition_15_75_1
import StacksProject_2024.Chap15.Lemma_15_120_1
import StacksProject_2024.Chap15.Lemma_15_79_1

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
