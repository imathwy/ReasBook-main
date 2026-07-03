import Mathlib
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import stacks_project.Chap13.Definition_13_15_3
import stacks_project.Chap13.Lemma_13_14_6
import stacks_project.Chap13.Lemma_13_14_11
import stacks_project.Chap13.Lemma_13_14_12
import stacks_project.Chap13.Lemma_13_15_2
import stacks_project.Chap13.Lemma_13_16_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.ObjectProperty
open CochainComplex
open scoped CategoryTheory
open ComplexShape

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

local notation "QisPlus" => boundedBelowHomotopyQuasiIso 𝒜
local notation "KplusToDplus" => mapBoundedBelowHomotopyCategoryToDerivedBelow F
local notation "Qis" => HomotopyCategory.quasiIso 𝒜 (up ℤ)
local notation "KtoD" => mapHomotopyCategoryToDerived F
local notation "H" => DerivedCategory.homologyFunctor ℬ

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): a cochain complex supported in the
single degree `a` becomes the corresponding single object in the homotopy category. -/
noncomputable abbrev representative_single_iso_of_strict_bounds
    (K : CochainComplex 𝒜 ℤ) (a : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE a] :
    (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ≅
      (HomotopyCategory.singleFunctor 𝒜 a).obj (K.X a) :=
  let M : 𝒜 := Classical.choose (CochainComplex.exists_iso_single (K := K) a)
  let e : K ≅ (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) a).obj M :=
    Classical.choice (Classical.choose_spec (CochainComplex.exists_iso_single (K := K) a))
  let eX : K.X a ≅ M :=
    (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) a).mapIso e ≪≫
      HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a M
  (HomotopyCategory.quotient 𝒜 (up ℤ)).mapIso e ≪≫
    (HomotopyCategory.singleFunctor 𝒜 a).mapIso eX.symm

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): quasi-isomorphisms in the unbounded
homotopy category are stable under shifts. This is the bridge needed to apply the generic
shift-stability API for `ComputesRightDerivedAt` to `K(\mathcal A) ⟶ D(\mathcal B)`. -/
local instance homotopyCategory_quasiIso_isCompatibleWithShift :
    (HomotopyCategory.quasiIso 𝒜 (up ℤ)).IsCompatibleWithShift ℤ where
  condition n := by
    ext X Y f
    change Qis (f⟦n⟧') ↔ Qis f
    rw [HomotopyCategory.mem_quasiIso_iff]
    rw [HomotopyCategory.mem_quasiIso_iff]
    constructor
    · intro hf j
      -- Shift the homology index back by `n` so the shifted quasi-isomorphism hypothesis matches
      -- the source of the canonical homology shift isomorphism.
      simpa [Functor.comp_map] using
        (NatIso.isIso_map_iff
          ((HomotopyCategory.homologyFunctor 𝒜 (up ℤ) 0).shiftIso
            n (j - n) j (by omega)) f).1
          (hf (j - n))
    · intro hf i
      -- The forward direction uses the same homology shift isomorphism with target degree
      -- `n + i`.
      simpa [Functor.comp_map] using
        (NatIso.isIso_map_iff
          ((HomotopyCategory.homologyFunctor 𝒜 (up ℤ) 0).shiftIso
            n i (n + i) rfl) f).2
          (hf (n + i))

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): a cochain complex concentrated in a
single degree whose unique term is right `F`-acyclic computes the unbounded right derived
functor. -/
lemma computesRightDerivedAt_single_degree_of_right_acyclic
    (K : CochainComplex 𝒜 ℤ) (a : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE a]
    (hK : IsRightAcyclicForAdditiveFunctor F (K.X a)) :
    ComputesRightDerivedAt KtoD Qis ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K) := by
  -- Identify the representative with the single complex concentrated in degree `a`.
  let e := representative_single_iso_of_strict_bounds (𝒜 := 𝒜) K a
  have hsingle_shift :
      ComputesRightDerivedAt KtoD Qis
        (((HomotopyCategory.singleFunctor 𝒜 a).obj (K.X a))⟦a⟧) := by
    -- The shift of the single complex in degree `a` is the degree-zero single complex.
    exact ((mapHomotopyCategoryToDerived F).computesRightDerivedObjectProperty Qis).prop_of_iso
      (((HomotopyCategory.singleFunctors 𝒜).shiftIso a 0 a (by simp)).symm.app (K.X a))
      hK
  have hsingle :
      ComputesRightDerivedAt KtoD Qis
        ((HomotopyCategory.singleFunctor 𝒜 a).obj (K.X a)) := by
    -- Shift invariance transports the computation statement back to degree `a`.
    exact (computesRightDerivedAt_iff_shift (F := KtoD) (S := Qis)
      (X := (HomotopyCategory.singleFunctor 𝒜 a).obj (K.X a)) (n := a)).2 hsingle_shift
  -- Finally transport the computation statement across the chosen representative isomorphism.
  exact ((mapHomotopyCategoryToDerived F).computesRightDerivedObjectProperty Qis).prop_of_iso
    e.symm hsingle

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): termwise bounded-below right acyclicity
of a bounded-below homotopy object implies termwise right acyclicity of the underlying unbounded
homotopy object. -/
lemma isTermwiseRightAcyclic_of_termwise_boundedBelowRightAcyclic
    (A : K⁺(𝒜))
    (hA : IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor F A) :
    IsTermwiseRightAcyclicForAdditiveFunctor F A := by
  intro n
  -- Convert each degree-zero bounded-below computation statement to the unbounded one via the
  -- canonical comparison of Lemma `13.15.2`.
  simpa [IsRightAcyclicForAdditiveFunctor, HomotopyCategory.quotient_obj_as] using
    (computes_right_derived_functor_at_iff_bounded_below
      (F := F) ((single0Plus 𝒜).obj (A.obj.as.X n))).2 (hA n)

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): turn an `IsIso` witness into an explicit
isomorphism. -/
private noncomputable def isoOfIsIso
    {C : Type*} [Category C] {X Y : C} {f : X ⟶ Y} (hf : IsIso f) :
    X ≅ Y := by
  let invf := hf.out.choose
  have h₁ : f ≫ invf = 𝟙 X := hf.out.choose_spec.1
  have h₂ : invf ≫ f = 𝟙 Y := hf.out.choose_spec.2
  exact ⟨f, invf, h₁, h₂⟩

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): a morphism in `D(\mathcal B)` is an
isomorphism exactly when all of its cohomology maps are isomorphisms. -/
lemma derivedCategory_isIso_iff_homology_map_isIso
    {X Y : DerivedCategory ℬ} (f : X ⟶ Y) :
    IsIso f ↔ ∀ i : ℤ, IsIso ((H i).map f) := by
  constructor
  · intro hf
    intro i
    -- Any isomorphism stays an isomorphism after applying the cohomology functor.
    let _ : IsIso f := hf
    exact Functor.map_isIso (H i) f
  · intro hf
    -- Lift `f` to the homotopy category and detect isomorphisms there via quasi-isomorphisms.
    obtain ⟨g, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := DerivedCategory.Qh.mapArrow) (Arrow.mk f)
    have hq : HomotopyCategory.quasiIso ℬ (ComplexShape.up ℤ) g.hom := by
      rw [HomotopyCategory.mem_quasiIso_iff]
      intro i
      haveI : IsIso e.hom := e.isIso_hom
      let eleft :
          (H i).obj (DerivedCategory.Qh.obj g.left) ≅ (H i).obj X :=
        Functor.mapIso (H i) (isoOfIsIso (Functor.map_isIso Arrow.leftFunc e.hom))
      let eright :
          (H i).obj (DerivedCategory.Qh.obj g.right) ≅ (H i).obj Y :=
        Functor.mapIso (H i) (isoOfIsIso (Functor.map_isIso Arrow.rightFunc e.hom))
      let ef : (H i).obj X ≅ (H i).obj Y := isoOfIsIso (hf i)
      have hw :
          (H i).map (Arrow.Hom.left e.hom) ≫ (H i).map f =
            (H i).map (DerivedCategory.Qh.map g.hom) ≫ (H i).map (Arrow.Hom.right e.hom) := by
        simpa [Functor.map_comp] using congrArg ((H i).map) (Arrow.w e.hom)
      have hcomp :
          IsIso ((H i).map (DerivedCategory.Qh.map g.hom) ≫
            (H i).map (Arrow.Hom.right e.hom)) := by
        haveI : IsIso (eleft.hom ≫ ef.hom) := by infer_instance
        rw [← hw]
        change IsIso (eleft.hom ≫ ef.hom)
        infer_instance
      have heright : eright.hom = (H i).map (Arrow.Hom.right e.hom) := by
        rfl
      haveI :
          IsIso ((H i).map (DerivedCategory.Qh.map g.hom) ≫ eright.hom) := by
        rw [heright]
        exact hcomp
      have hmap : IsIso ((H i).map (DerivedCategory.Qh.map g.hom)) := by
        exact IsIso.of_isIso_comp_right ((H i).map (DerivedCategory.Qh.map g.hom)) eright.hom
      rw [← NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactorsh ℬ i) g.hom]
      exact hmap
    have hQg : IsIso (DerivedCategory.Qh.map g.hom) :=
      (DerivedCategory.isIso_Qh_map_iff g.hom).2 hq
    haveI : IsIso e.hom := e.isIso_hom
    exact (Arrow.isIso_iff_isIso_of_isIso e.hom).1 hQg

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): the canonical identity-denominator legs
for pointwise right-derived values are natural in the source morphism. -/
lemma rightDerivedValueLeg_id_naturality
    {X Y : HomotopyCategory 𝒜 (up ℤ)} (f : X ⟶ Y)
    [HasPointwiseRightDerivedFunctorAt KtoD Qis X]
    [HasPointwiseRightDerivedFunctorAt KtoD Qis Y] :
    (mapHomotopyCategoryToDerived F).map f ≫
        rightDerivedValueLeg Qis KtoD (𝟙 Y)
          (MorphismProperty.id_mem (HomotopyCategory.quasiIso 𝒜 (up ℤ)) Y) =
      rightDerivedValueLeg Qis KtoD (𝟙 X)
          (MorphismProperty.id_mem (HomotopyCategory.quasiIso 𝒜 (up ℤ)) X) ≫
        rightDerivedValueMap Qis KtoD f := by
  -- The generic denominator-square compatibility specializes to the square with identity
  -- denominators on both sides.
  simpa using
    (show CommSq
        (rightDerivedValueLeg Qis KtoD (𝟙 X)
          (MorphismProperty.id_mem (HomotopyCategory.quasiIso 𝒜 (up ℤ)) X))
        ((mapHomotopyCategoryToDerived F).map f)
        (rightDerivedValueMap Qis KtoD f)
        (rightDerivedValueLeg Qis KtoD (𝟙 Y)
          (MorphismProperty.id_mem (HomotopyCategory.quasiIso 𝒜 (up ℤ)) Y)) from
      rightDerivedValueMap_comp_of_square Qis KtoD f
        (𝟙 X) (𝟙 Y)
        (MorphismProperty.id_mem (HomotopyCategory.quasiIso 𝒜 (up ℤ)) X)
        (MorphismProperty.id_mem (HomotopyCategory.quasiIso 𝒜 (up ℤ)) Y)
        f ⟨by simp⟩).w.symm

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): the brutal bounded-support case should
be proved by induction on the width of the support interval, peeling off one term with stupid
truncation triangles. -/
lemma computesRightDerivedAt_of_strict_bounds_termwise_rightAcyclic
    (K : CochainComplex 𝒜 ℤ) (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b]
    (hK : ∀ n : ℤ, IsRightAcyclicForAdditiveFunctor F (K.X n)) :
    ComputesRightDerivedAt KtoD Qis ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K) := by
  -- TODO: follow the source proof with brutal truncations `σ_{≤ a}` and `σ_{≥ a + 1}`.
  -- The remaining blocker is a reusable homotopy-category triangle API for those stupid
  -- truncations, so that Lemmas `13.14.6` and `13.14.12` can run the bounded-support induction.
  sorry

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): once the bounded-support case is known,
each bounded-below termwise right-acyclic complex computes `RF` by comparing it degreewise with
its upper truncations. -/
lemma computesRightDerivedAt_obj_of_termwise_rightAcyclic
    (A : K⁺(𝒜))
    (hder : HasPointwiseRightDerivedFunctorAt KtoD Qis A.obj)
    (hA : IsTermwiseRightAcyclicForAdditiveFunctor F A) :
    ComputesRightDerivedAt KtoD Qis A.obj := by
  -- The fixed-degree comparison is now reduced to the bounded-support computation step.
  -- The naturality square for the identity legs is packaged by
  -- `rightDerivedValueLeg_id_naturality`.
  -- TODO: compute the bounded-support truncation by the first helper above, then combine those
  -- comparisons with the missing source-side truncation/homology adapter and
  -- `rightDerivedValue_homologyMap_isIso_of_truncLE` to conclude.
  sorry

/- Domain-style sampling for Lemma 13.16.7:
- primary domain: bounded-below right derived functors of additive functors between abelian
  categories, and the Leray criterion that termwise right-acyclic bounded-below complexes already
  compute the derived value;
- sampled owner declarations:
  `HasPointwiseRightDerivedFunctorAt KplusToDplus QisPlus`,
  `ComputesRightDerivedAt KplusToDplus QisPlus`,
  `IsBoundedBelowRightAcyclicForAdditiveFunctor`,
  `mapBoundedBelowHomotopyCategoryToDerivedBelow`;
- best owner abstraction: the source-facing owner here is the pointwise computation predicate
  `ComputesRightDerivedAt KplusToDplus QisPlus A`; the termwise acyclicity hypothesis should be
  expressed directly using the chapter owner
  `IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor F A`;
- primitive data: a bounded-below homotopy object `A`, pointwise right-derived-definedness at `A`,
  and the termwise bounded-below right-acyclicity predicate
  `IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor F A`;
- derived API: the Leray comparison theorem below, asserting that `A` computes the bounded-below
  right derived functor.

Source/core/bridge triage:
- `source-facing`: the Leray acyclicity criterion for bounded-below complexes;
- `core/canonical`: `HasPointwiseRightDerivedFunctorAt KplusToDplus QisPlus`,
  `ComputesRightDerivedAt KplusToDplus QisPlus`, and
  `IsBoundedBelowRightAcyclicForAdditiveFunctor`;
- `bridge/view`: the bounded/unbounded comparison results from Lemma `13.15.2` and Proposition
  `13.16.8`, which should reuse this owner-level criterion rather than replace it.
-/

-- Proof sketch: argue first for bounded complexes by induction on the amplitude, using stupid
-- truncation triangles and Lemma `13.14.12` together with the fact that a single right
-- `F`-acyclic object computes the bounded-below right derived functor by Definition `13.15.3`.
-- Then truncate a bounded-below complex above degree `i + 1`, compare the long exact cohomology
-- sequences for `F(A^•)` and `RF(A^•)`, and use Lemma `13.16.1` to see that the higher
-- truncation contributes no cohomology in degrees `i` and `i + 1`.
/-- Lemma 13.16.7 (Leray's acyclicity lemma): if `A^•` is a bounded-below complex whose every term
is right acyclic for the bounded-below right derived functor of `F`, and if that right derived
functor is defined at `A^•`, then `A^•` computes the bounded-below right derived functor of `F`,
formalized by `ComputesRightDerivedAt KplusToDplus QisPlus A`. Equivalently, the canonical map
`F(A^•) ⟶ RF(A^•)` is an isomorphism in `D^+(\mathcal B)`. -/
theorem computesRightDerivedAt_of_termwise_boundedBelowRightAcyclic
    (A : K⁺(𝒜))
    (hder : HasPointwiseRightDerivedFunctorAt KplusToDplus QisPlus A)
    (hA : IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor F A) :
    ComputesRightDerivedAt KplusToDplus QisPlus A := by
  -- Route correction: the viable proof route is to pass to the unbounded homotopy category,
  -- prove the bounded-support part there using truncation triangles, and then transport the
  -- resulting computation back to `K^+`.
  have hA' : IsTermwiseRightAcyclicForAdditiveFunctor F A :=
    isTermwiseRightAcyclic_of_termwise_boundedBelowRightAcyclic (F := F) A hA
  have hder' : HasPointwiseRightDerivedFunctorAt KtoD Qis A.obj := by
    exact (right_derived_defined_at_iff_bounded_below (F := F) A).2 hder
  have hcompute' : ComputesRightDerivedAt KtoD Qis A.obj :=
    computesRightDerivedAt_obj_of_termwise_rightAcyclic (F := F) A hder' hA'
  -- The final step is the bounded/unbounded comparison from Lemma `13.15.2`.
  exact (computes_right_derived_functor_at_iff_bounded_below (F := F) A).1 hcompute'

end

end CategoryTheory
