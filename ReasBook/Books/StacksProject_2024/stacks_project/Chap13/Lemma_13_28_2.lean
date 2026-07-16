import Mathlib
import StacksProject_2024.stacks_project.Chap12.Definition_12_11_1
import StacksProject_2024.stacks_project.Chap13.Definition_13_11_3
import StacksProject_2024.stacks_project.Chap13.Lemma_13_6_4
import StacksProject_2024.stacks_project.Chap13.Definition_13_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open scoped ZeroObject
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

/-- Helper for Lemma 13.28.2: the zero object has trivial class in the abelian Grothendieck
group. -/
private theorem abelian_k0_zero_eq :
    K₀[(0 : 𝒜)] = 0 := by
  -- Proof comment: apply the short-exact-sequence relation to the zero sequence and cancel one
  -- copy of the zero class.
  let S : ShortComplex 𝒜 :=
    ShortComplex.mk (0 : (0 : 𝒜) ⟶ 0) (0 : (0 : 𝒜) ⟶ 0) (by simp)
  have hExact : S.Exact := by
    exact (S.exact_iff_epi (by simp [S])).2 inferInstance
  have hShort : S.ShortExact := ShortComplex.ShortExact.mk' hExact inferInstance inferInstance
  have hK0 : K₀[(0 : 𝒜)] = K₀[(0 : 𝒜)] + K₀[(0 : 𝒜)] := by
    simpa [S] using (AbelianK0.of_shortExact S hShort)
  have hSub := congrArg (fun z : AbelianK0 𝒜 ↦ z - K₀[(0 : 𝒜)]) hK0
  have hZero : (0 : AbelianK0 𝒜) = K₀[(0 : 𝒜)] := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hSub
  simpa using hZero.symm

/-- Helper for Lemma 13.28.2: isomorphic objects define the same class in the abelian
Grothendieck group. -/
private theorem abelian_k0_eq_of_iso {X Y : 𝒜} (e : X ≅ Y) :
    K₀[X] = K₀[Y] := by
  -- Proof comment: use the short exact sequence `0 → X → Y → 0` attached to the isomorphism.
  let S : ShortComplex 𝒜 := ShortComplex.mk e.hom (0 : Y ⟶ 0) (by simp)
  have hExact : S.Exact := by
    exact (S.exact_iff_epi (by simp [S])).2 inferInstance
  have hShort : S.ShortExact := ShortComplex.ShortExact.mk' hExact inferInstance inferInstance
  simpa [S, abelian_k0_zero_eq (𝒜 := 𝒜), add_comm] using (AbelianK0.of_shortExact S hShort).symm

-- Proof sketch: the object `X[0]` has cohomology `X` in degree `0` and zero in every other
-- degree, so it is bounded both below and above.
/-- The degree-zero complex attached to an object of `\mathcal A` is a bounded derived object. -/
theorem singleFunctor_obj_mem_boundedDerivedCategory (X : 𝒜) :
    t.bounded ((single₀).obj X) := by
  -- Proof comment: the degree-zero complex has no cohomology below or above degree `0`.
  rw [derivedCategory_t_bounded_iff]
  refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩⟩
  · intro i hi
    let _ : ((single₀).obj X).IsGE 0 := inferInstance
    exact DerivedCategory.isZero_of_isGE _ 0 i hi
  · intro i hi
    let _ : ((single₀).obj X).IsLE 0 := inferInstance
    exact DerivedCategory.isZero_of_isLE _ 0 i hi

/-- The degree-zero embedding `\mathcal A ⥤ Dᵇ(\mathcal A)`. -/
abbrev singleFunctorToBoundedDerived :
    𝒜 ⥤ Dᵇ(𝒜) :=
  ObjectProperty.lift
    t.bounded
    single₀
    (singleFunctor_obj_mem_boundedDerivedCategory 𝒜)

/-- Helper for Lemma 13.28.2: the cohomology of a degree-zero complex vanishes away from degree
`0`. -/
theorem single_zero_complex_homology_isZero_of_ne
    (X : 𝒜) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor 𝒜 i).obj ((single₀).obj X)) := by
  -- Proof comment: a degree-zero complex is bounded below and above by `0`, so any nonzero
  -- degree cohomology vanishes by the canonical `t`-structure bounds.
  by_cases hlt : i < 0
  · let _ : ((single₀).obj X).IsGE 0 := inferInstance
    exact DerivedCategory.isZero_of_isGE _ 0 i hlt
  · have hgt : 0 < i := by
      omega
    let _ : ((single₀).obj X).IsLE 0 := inferInstance
    exact DerivedCategory.isZero_of_isLE _ 0 i hgt

/-- Helper for Lemma 13.28.2: on a shifted bounded derived object, degree-zero cohomology agrees
with the corresponding ambient cohomology object. -/
noncomputable def boundedDerived_zero_homology_shift_obj_iso
    (X : Dᵇ(𝒜)) (i : ℤ) :
    ((boundedDerivedZeroHomologyFunctor 𝒜).obj ((shiftFunctor (Dᵇ(𝒜)) i).obj X)) ≅
      ((boundedDerivedHomologyFunctor 𝒜 i).obj X) := by
  -- Proof comment: commute the bounded-derived inclusion past the shift and then apply the
  -- standard derived-category comparison `H⁰(X[i]) ≅ Hⁱ(X)`.
  dsimp [boundedDerivedZeroHomologyFunctor, boundedDerivedHomologyFunctor]
  exact
    ((DerivedCategory.homologyFunctor 𝒜 0).mapIso
      (((ObjectProperty.ι t.bounded).commShiftIso i).app X)) ≪≫
      ((DerivedCategory.homologyFunctor 𝒜 0).shiftIso i 0 i (by omega)).app X.obj

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

-- Proof sketch: boundedness of `X` means `X.obj` lies in both `t.plus` and `t.minus`, so the
-- standard `t`-structure vanishing bounds show that only finitely many shifted values
-- `H⁰(X[i]) ≅ H^i(X.obj)` can be nonzero.
/-- The degree-zero homology functor on `D^b(\mathcal A)` has finite shift support. -/
theorem boundedDerivedZeroHomologyFunctor_hasFiniteShiftSupport
    (X : Dᵇ(𝒜)) :
    (boundedDerivedZeroHomologyFunctor 𝒜).shiftVanishingBounded X := by
  -- Proof comment: boundedness of `X.obj` gives lower and upper vanishing bounds for `Hⁱ(X)`,
  -- and the previous comparison identifies these groups with `H⁰(X[i])`.
  rcases (derivedCategory_t_bounded_iff X.obj).1 X.property with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  refine ⟨⟨a - 1, ?_⟩, ⟨b + 1, ?_⟩⟩
  · intro n hn
    have hzero :
        IsZero ((boundedDerivedHomologyFunctor 𝒜 n).obj X) := by
      simpa [boundedDerivedHomologyFunctor] using ha n (by omega)
    exact IsZero.of_iso
      hzero
      (boundedDerived_zero_homology_shift_obj_iso 𝒜 X n)
  · intro n hn
    have hzero :
        IsZero ((boundedDerivedHomologyFunctor 𝒜 n).obj X) := by
      simpa [boundedDerivedHomologyFunctor] using hb n (by omega)
    exact IsZero.of_iso
      hzero
      (boundedDerived_zero_homology_shift_obj_iso 𝒜 X n)

/-- On generators, the Euler-characteristic map sends a bounded derived object to the alternating
sum of the classes of its cohomology objects in `K₀(\mathcal A)`. -/
noncomputable abbrev boundedDerivedEulerClass
    (X : Dᵇ(𝒜)) :
    AbelianK0 𝒜 :=
  ∑ᶠ i : ℤ, i.negOnePow • K₀[((boundedDerivedHomologyFunctor 𝒜 i).obj X)]

/-- Helper for Lemma 13.28.2: the Euler class of a degree-zero object recovers its original
`K₀(\mathcal A)`-class. -/
theorem boundedDerivedEulerClass_single_zero (X : 𝒜) :
    boundedDerivedEulerClass 𝒜 ((singleFunctorToBoundedDerived 𝒜).obj X) = K₀[X] := by
  -- Proof comment: only the degree-zero cohomology term survives for `X[0]`.
  let Y := (singleFunctorToBoundedDerived 𝒜).obj X
  let f : ℤ → AbelianK0 𝒜 :=
    fun i ↦ i.negOnePow • K₀[((boundedDerivedHomologyFunctor 𝒜 i).obj Y)]
  have hsupport :
      ∀ i : ℤ, i ∉ Set.Icc (0 : ℤ) 0 → f i = 0 := by
    intro i hi
    have hi0 : i ≠ 0 := by
      simpa using hi
    have hzeroHomology :
        IsZero ((boundedDerivedHomologyFunctor 𝒜 i).obj Y) :=
      single_zero_complex_homology_isZero_of_ne (𝒜 := 𝒜) X i hi0
    have hk0 :
        K₀[((boundedDerivedHomologyFunctor 𝒜 i).obj Y)] = 0 := by
      calc
        K₀[((boundedDerivedHomologyFunctor 𝒜 i).obj Y)] = K₀[(0 : 𝒜)] := by
          exact abelian_k0_eq_of_iso (𝒜 := 𝒜) hzeroHomology.isoZero
        _ = 0 := abelian_k0_zero_eq (𝒜 := 𝒜)
    change i.negOnePow • K₀[((boundedDerivedHomologyFunctor 𝒜 i).obj Y)] = 0
    rw [hk0]
    simp
  have hsum :
      boundedDerivedEulerClass 𝒜 Y =
        Finset.sum (Finset.Icc (0 : ℤ) 0) f := by
    have hsupp :
        Function.support f ⊆ ↑(Finset.Icc (0 : ℤ) 0) := by
      intro i hi
      by_contra hnot
      exact hi (hsupport i (by simpa using hnot))
    simpa [boundedDerivedEulerClass, f] using
      (finsum_eq_sum_of_support_subset (s := Finset.Icc (0 : ℤ) 0) f hsupp)
  have hzero :
      K₀[((boundedDerivedHomologyFunctor 𝒜 (0 : ℤ)).obj Y)] = K₀[X] := by
    -- Proof comment: the degree-zero cohomology of `X[0]` is canonically `X`.
    refine abelian_k0_eq_of_iso (𝒜 := 𝒜) ?_
    dsimp [Y, boundedDerivedHomologyFunctor, singleFunctorToBoundedDerived]
    exact (DerivedCategory.singleFunctorCompHomologyFunctorIso 𝒜 (0 : ℤ)).app X
  calc
    boundedDerivedEulerClass 𝒜 Y = Finset.sum (Finset.Icc (0 : ℤ) 0) f := hsum
    _ = f 0 := by simp
    _ = K₀[X] := by simpa [f, hzero]

/-- The canonical map `K₀(D^b(\mathcal A)) → K₀(\mathcal A)` given by Euler characteristic. -/
def boundedDerivedToAbelianK0 :
    TriangulatedK0 (Dᵇ(𝒜)) →+ AbelianK0 𝒜 := sorry

/-- The Euler-characteristic map sends the class of `X` to the alternating sum of the cohomology
classes of `X`. -/
@[simp] theorem boundedDerivedToAbelianK0_apply_of
    (X : Dᵇ(𝒜)) :
    boundedDerivedToAbelianK0 𝒜 (TriangulatedK0.of X) =
      boundedDerivedEulerClass 𝒜 X := sorry

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
    Function.LeftInverse (abelianToBoundedDerivedK0 𝒜) (boundedDerivedToAbelianK0 𝒜) := by
  -- TODO: use a bounded complex representative and the stupid truncation triangles to express
  -- `[X]` as the alternating sum of the embedded cohomology objects `[H^i(X)[0]]`.
  sorry

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
