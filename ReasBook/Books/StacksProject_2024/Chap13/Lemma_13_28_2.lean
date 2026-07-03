import Mathlib
import StacksProject_2024.Chap12.Definition_12_11_1
import StacksProject_2024.Chap13.Definition_13_11_3
import StacksProject_2024.Chap13.Definition_13_28_1
import StacksProject_2024.Chap13.Lemma_13_28_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open DerivedCategory
open DerivedCategory.TStructure
open scoped CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory

section BoundedDerivedK0

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]
local notation "single₀" => singleFunctor 𝒜 (0 : ℤ)

/- Domain-style sampling for Lemma 13.28.2:
- primary domain: Grothendieck groups of abelian and triangulated categories, applied to the
  bounded derived category `Dᵇ(𝒜)`;
- sampled owner declarations:
  `CategoryTheory.boundedDerivedCategory`,
  `CategoryTheory.boundedDerivedHomologyFunctor`,
  `CategoryTheory.TriangulatedK0`,
  `CategoryTheory.Functor.eulerK0Map`,
  `CategoryTheory.Functor.eulerClass`,
  `CategoryTheory.Functor.shiftVanishingBounded`,
  `CategoryTheory.DerivedCategory.shift_homologyFunctor`,
  `CategoryTheory.ObjectProperty.lift`,
  `DerivedCategory.singleFunctor`,
  the mathlib instance `t.bounded.IsTriangulated`;
- best owner abstraction:
  the core owners are `Dᵇ(𝒜)` for the bounded derived category and `TriangulatedK0` for its
  Grothendieck group, while the inverse comparison map to `AbelianK0 𝒜` should be routed through
  the owner-functor map `boundedDerivedZeroHomologyFunctor.eulerK0Map` applied to the degree-zero
  homology functor on
  `Dᵇ(𝒜)`; the degree-zero embedding `𝒜 ⥤ Dᵇ(𝒜)` is only the bridge used for the map in the
  opposite direction;
- primitive vs. derived:
  primitive data in this file are the degree-zero embedding `𝒜 ⥤ Dᵇ(𝒜)` and the degree-zero
  homology family `boundedDerivedHomologyFunctor 𝒜 i : Dᵇ(𝒜) ⥤ 𝒜`;
  the raw quotient-kernel arguments and the finite-support witness for the homological functor are
  derived API and should stay internal to the resulting `K₀` maps;
- source/core/bridge triage:
  `source-facing`: the comparison maps on `K₀` and the resulting equivalence
    `TriangulatedK0 (Dᵇ(𝒜)) ≃+ AbelianK0 𝒜`;
  `core/canonical`: `Dᵇ(𝒜)`, `TriangulatedK0`,
    `boundedDerivedZeroHomologyFunctor.eulerK0Map`, and the instance `t.bounded.IsTriangulated`;
  `bridge/view`: the degree-zero functor `𝒜 ⥤ Dᵇ(𝒜)` induced by `ObjectProperty.lift`, and the
    restricted degree-zero homology functor `Dᵇ(𝒜) ⥤ 𝒜`.
-/

-- Proof sketch: the object `X[0]` has cohomology `X` in degree `0` and zero in every other
-- degree, so it is bounded both below and above.
/-- The degree-zero complex attached to an object of `\mathcal A` is a bounded derived object. -/
theorem singleFunctor_obj_mem_boundedDerivedCategory (X : 𝒜) :
    t.bounded ((single₀).obj X) := sorry

/-- The degree-zero embedding `\mathcal A ⥤ Dᵇ(\mathcal A)`. -/
abbrev singleFunctorToBoundedDerived :
    𝒜 ⥤ Dᵇ(𝒜) :=
  ObjectProperty.lift
    t.bounded
    single₀
    (singleFunctor_obj_mem_boundedDerivedCategory 𝒜)

/-- The bounded-derived triangle attached to a short exact sequence in `\mathcal A`. -/
private def singleFunctorToBoundedDerivedTriangle {S : ShortComplex 𝒜} (hS : S.ShortExact) :
    Triangle (Dᵇ(𝒜)) :=
  Triangle.mk
    ((singleFunctorToBoundedDerived 𝒜).map S.f)
    ((singleFunctorToBoundedDerived 𝒜).map S.g)
    ((ObjectProperty.ι t.bounded).preimage
      (hS.singleδ ≫
        ((ObjectProperty.ι t.bounded).commShiftIso (1 : ℤ)).inv.app
          ((singleFunctorToBoundedDerived 𝒜).obj S.X₁)))

/-- The bounded-derived triangle attached to a short exact sequence is distinguished. -/
private theorem singleFunctorToBoundedDerivedTriangle_distinguished {S : ShortComplex 𝒜}
    (hS : S.ShortExact) :
    singleFunctorToBoundedDerivedTriangle 𝒜 hS ∈ distTriang (Dᵇ(𝒜)) := by
  rw [← (ObjectProperty.ι t.bounded).map_distinguished_iff]
  change
    Triangle.mk
        ((ObjectProperty.ι t.bounded).map ((singleFunctorToBoundedDerived 𝒜).map S.f))
        ((ObjectProperty.ι t.bounded).map ((singleFunctorToBoundedDerived 𝒜).map S.g))
        ((ObjectProperty.ι t.bounded).map
            ((ObjectProperty.ι t.bounded).preimage
              (hS.singleδ ≫
                ((ObjectProperty.ι t.bounded).commShiftIso (1 : ℤ)).inv.app
                  ((singleFunctorToBoundedDerived 𝒜).obj S.X₁))) ≫
          ((ObjectProperty.ι t.bounded).commShiftIso (1 : ℤ)).hom.app
            ((singleFunctorToBoundedDerived 𝒜).obj S.X₁)) ∈
      distTriang (D(𝒜))
  rw [(ObjectProperty.ι t.bounded).map_preimage]
  refine isomorphic_distinguished _ hS.singleTriangle_distinguished _ ?_
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · simp [singleFunctorToBoundedDerived]
  · simp [singleFunctorToBoundedDerived]
  · simpa [Category.assoc] using
      congrArg (fun k ↦ hS.singleδ ≫ k)
        (((ObjectProperty.ι t.bounded).commShiftIso (1 : ℤ)).inv_hom_id_app
          ((singleFunctorToBoundedDerived 𝒜).obj S.X₁))

/-- The short-exact Grothendieck relations in `K₀(\mathcal A)` are killed by the degree-zero
embedding into the bounded derived category. -/
private theorem relations_le_ker_abelianToBoundedDerivedK0 :
    AbelianK0.relations 𝒜 ≤
      (FreeAbelianGroup.lift
        fun X ↦ TriangulatedK0.of ((singleFunctorToBoundedDerived 𝒜).obj X)).ker := by
  rw [AbelianK0.relations, AddSubgroup.closure_le]
  rintro _ ⟨S, rfl⟩
  rcases S with ⟨S, hS⟩
  change
    (FreeAbelianGroup.lift
        fun X ↦ TriangulatedK0.of ((singleFunctorToBoundedDerived 𝒜).obj X))
      (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  simp only [FreeAbelianGroup.lift_apply_of, map_sub]
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    sub_eq_zero.mpr
      (TriangulatedK0.of_distinguished
        (singleFunctorToBoundedDerivedTriangle 𝒜 hS)
        (singleFunctorToBoundedDerivedTriangle_distinguished 𝒜 hS))

/-- The canonical map `K₀(\mathcal A) → K₀(D^b(\mathcal A))` induced by `X ↦ X[0]`. -/
def abelianToBoundedDerivedK0 :
    AbelianK0 𝒜 →+ TriangulatedK0 (Dᵇ(𝒜)) :=
  AbelianK0.lift
    (fun X ↦ TriangulatedK0.of ((singleFunctorToBoundedDerived 𝒜).obj X))
    (relations_le_ker_abelianToBoundedDerivedK0 𝒜)

-- Proof sketch: `abelianToBoundedDerivedK0` is `AbelianK0.lift` applied to the object-level
-- class map `X ↦ [X[0]]`, so evaluation on `AbelianK0.of X` is the owner lemma
-- `AbelianK0.lift_of`.
/-- The canonical map on `K₀` sends `[X]` to the class of the degree-zero object `X[0]`. -/
@[simp] theorem abelianToBoundedDerivedK0_apply_of (X : 𝒜) :
    abelianToBoundedDerivedK0 𝒜 K₀[X] =
      TriangulatedK0.of ((singleFunctorToBoundedDerived 𝒜).obj X) := by
  simpa [abelianToBoundedDerivedK0] using
    AbelianK0.lift_of
      (fun Y : 𝒜 ↦ TriangulatedK0.of ((singleFunctorToBoundedDerived 𝒜).obj Y))
      (relations_le_ker_abelianToBoundedDerivedK0 𝒜)
      X

local instance boundedDerivedZeroHomologyFunctor_isHomological :
    (boundedDerivedZeroHomologyFunctor 𝒜).IsHomological := inferInstance

noncomputable local instance boundedDerivedZeroHomologyFunctor_shiftSequence :
    (boundedDerivedZeroHomologyFunctor 𝒜).ShiftSequence ℤ :=
  Functor.ShiftSequence.tautological _ _

-- Proof sketch: boundedness of `X` means `X.obj` lies in both `t.plus` and `t.minus`, so the
-- standard `t`-structure vanishing bounds show that only finitely many shifted values
-- `H⁰(X[i]) ≅ H^i(X.obj)` can be nonzero.
/-- The degree-zero homology functor on `D^b(\mathcal A)` has finite shift support. -/
theorem boundedDerivedZeroHomologyFunctor_hasFiniteShiftSupport
    (X : Dᵇ(𝒜)) :
    (boundedDerivedZeroHomologyFunctor 𝒜).shiftVanishingBounded X := by
  sorry

/-- On generators, the Euler-characteristic map sends a bounded derived object to the alternating
sum of the classes of its cohomology objects in `K₀(\mathcal A)`. -/
noncomputable abbrev boundedDerivedEulerClass
    (X : Dᵇ(𝒜)) :
    AbelianK0 𝒜 :=
  ∑ᶠ i : ℤ, i.negOnePow • K₀[((boundedDerivedHomologyFunctor 𝒜 i).obj X)]

-- Proof sketch: with the tautological shift sequence on the restricted degree-zero cohomology
-- functor, the `i`-th shifted value is `H⁰(X[i])`. The canonical shift sequence on derived
-- cohomology identifies this with `H^i(X)`, so the general Euler class is exactly the textbook
-- alternating sum of cohomology classes.
/-- The Euler class coming from the general homological-functor owner for the restricted degree-zero
cohomology functor agrees with the textbook alternating sum of cohomology objects. -/
theorem boundedDerivedZeroHomologyFunctor_eulerClass_eq
    (X : Dᵇ(𝒜)) :
    (boundedDerivedZeroHomologyFunctor 𝒜).eulerClass X =
      boundedDerivedEulerClass 𝒜 X := sorry

/-- The canonical map `K₀(D^b(\mathcal A)) → K₀(\mathcal A)` given by Euler characteristic. -/
def boundedDerivedToAbelianK0 :
    TriangulatedK0 (Dᵇ(𝒜)) →+ AbelianK0 𝒜 :=
  (boundedDerivedZeroHomologyFunctor 𝒜).eulerK0Map
    (boundedDerivedZeroHomologyFunctor_hasFiniteShiftSupport 𝒜)

/-- The Euler-characteristic map sends the class of `X` to the alternating sum of the cohomology
classes of `X`. -/
@[simp] theorem boundedDerivedToAbelianK0_apply_of
    (X : Dᵇ(𝒜)) :
    boundedDerivedToAbelianK0 𝒜 (TriangulatedK0.of X) =
      boundedDerivedEulerClass 𝒜 X := by
  simpa [boundedDerivedToAbelianK0] using
    (Functor.eulerK0Map_apply_of (boundedDerivedZeroHomologyFunctor 𝒜)
      (boundedDerivedZeroHomologyFunctor_hasFiniteShiftSupport 𝒜)
      X).trans (boundedDerivedZeroHomologyFunctor_eulerClass_eq 𝒜 X)

-- Proof sketch: evaluate the Euler characteristic of the degree-zero complex `X[0]`. Its only
-- nonzero cohomology object is `X` in degree `0`, so the composition sends `[X]` to `[X]`.
/-- The Euler characteristic map is a right inverse to the degree-zero embedding on `K₀`. -/
theorem abelianToBoundedDerivedK0_rightInverse :
    Function.RightInverse (abelianToBoundedDerivedK0 𝒜) (boundedDerivedToAbelianK0 𝒜) := sorry

-- Proof sketch: represent a bounded derived object by a bounded complex, then use the stupid
-- truncation triangles to express its class in `K₀(D^b(\mathcal A))` as the alternating sum of
-- the classes of its cohomology objects embedded in degree `0`.
/-- The degree-zero embedding on `K₀` is a left inverse to the Euler characteristic map. -/
theorem abelianToBoundedDerivedK0_leftInverse :
    Function.LeftInverse (abelianToBoundedDerivedK0 𝒜) (boundedDerivedToAbelianK0 𝒜) := sorry

/-- Lemma 13.28.2: for an abelian category `\mathcal A`, the zeroth `K`-group of the bounded
derived category `D^b(\mathcal A)` is canonically identified with the zeroth `K`-group of
`\mathcal A`. -/
noncomputable def boundedDerivedCategoryK0Equiv :
    TriangulatedK0 (Dᵇ(𝒜)) ≃+ AbelianK0 𝒜 where
  toFun := boundedDerivedToAbelianK0 𝒜
  invFun := abelianToBoundedDerivedK0 𝒜
  left_inv := abelianToBoundedDerivedK0_leftInverse 𝒜
  right_inv := abelianToBoundedDerivedK0_rightInverse 𝒜
  map_add' := (boundedDerivedToAbelianK0 𝒜).map_add

-- Proof sketch: this is the `right_inv` field of `boundedDerivedCategoryK0Equiv`, evaluated on
-- the generator coming from the degree-zero complex `X[0]`.
/-- The canonical identification sends the class of `X[0]` in `K₀(D^b(\mathcal A))` to the class
of `X` in `K₀(\mathcal A)`. -/
theorem boundedDerivedCategoryK0Equiv_apply_single (X : 𝒜) :
    boundedDerivedCategoryK0Equiv 𝒜
      (abelianToBoundedDerivedK0 𝒜 K₀[X]) = K₀[X] := by
  exact (boundedDerivedCategoryK0Equiv 𝒜).right_inv K₀[X]

end BoundedDerivedK0

end CategoryTheory
