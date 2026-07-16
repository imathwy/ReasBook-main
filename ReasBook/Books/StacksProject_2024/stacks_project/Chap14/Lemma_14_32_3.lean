import Mathlib
import StacksProject_2024.stacks_project.Chap14.Lemma_14_20_2
import StacksProject_2024.stacks_project.Chap14.Remark_14_20_4
import StacksProject_2024.stacks_project.Chap14.Definition_14_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open Opposite
open scoped Simplicial
open SSet.modelCategoryQuillen

universe u

/- Domain-style sampling for Lemma 14.32.3:
- primary domain: simplicial-set trivial Kan fibrations for augmented Čech nerve maps.
- sampled owner declarations:
  `CategoryTheory.Arrow.augmentedCechNerve`,
  `CategoryTheory.CechNerveTerminalFrom.iso`,
  `SSet.modelCategoryQuillen.I.rlp`,
  `CategoryTheory.MorphismProperty.pullback_snd`,
  `trivialKanFibration_of_bijective_below_of_surjective_of_coskeletal`.
- best owner abstraction:
  the source-facing map is the canonical augmentation
  `(Arrow.mk f).augmentedCechNerve.hom`, and the target property “trivial Kan fibration” is the
  owner predicate `I.rlp`.
- primitive-vs-derived split:
  primitive data: only the function `f : A → B` and the surjectivity hypothesis `hf`;
  derived API: the augmented Čech nerve map, its comparison with the pullback of the coordinatewise
  map on `0`-coskeleta, and the base-change closure of `I.rlp`.

Source/core/bridge triage:
- `source-facing`: the Stacks statement that the augmentation from the simplicial set of iterated
  fibre products of a surjective map is a trivial Kan fibration;
- `core/canonical`: `Arrow.augmentedCechNerve` for the augmentation object and `I.rlp` for the
  lifting property;
- `bridge/view`: identify the augmentation as the pullback of the coordinatewise map
  `cechNerveTerminalFrom A ⟶ cechNerveTerminalFrom B` along the diagonal map
  `const B ⟶ cechNerveTerminalFrom B`, then apply
  `trivialKanFibration_of_bijective_below_of_surjective_of_coskeletal` at `n = 0` and
  `I.rlp.pullback_snd`.

There is no exact upstream theorem with this source-facing interface, so the correct refinement is
to keep the theorem and express its proof route entirely through these canonical owners, rather than
introducing any local wrapper around the pullback comparison or the lifting-property owner. -/

-- Proof sketch: build the filler from the degree-`0` lift using the owner-level Čech adjunction
-- `SimplicialObject.equivalenceLeftToRight`, then compare augmented morphisms through
-- `SimplicialObject.cechNerveEquiv` after projecting to `0`-simplices.
/-- Helper for Lemma 14.32.3: the boundary of a positive-dimensional simplex contains all
vertices, so the inclusion on `0`-simplices is bijective. -/
private theorem boundary_zero_bijective (n : ℕ) :
    Function.Bijective ((∂Δ[n + 1].ι).app (op ⦋0⦌)) := by
  constructor
  · intro x y h
    exact Subtype.ext h
  · intro x
    refine ⟨⟨x, ?_⟩, rfl⟩
    intro hs
    have hcard := Fintype.card_le_of_surjective _ hs
    simp at hcard

/-- Lemma 14.32.3: if `f : A → B` is surjective, then the augmentation from the simplicial set
whose `n`-simplices are the `(n + 1)`-fold fibre products `A ×[B] ⋯ ×[B] A`, canonically
formalized as the augmented Čech nerve map `(Arrow.mk f).augmentedCechNerve.hom`, to the constant
simplicial set on `B` is a trivial Kan fibration. -/
theorem trivialKanFibration_cechNerveAugmentation_of_surjective
    {A B : Type u} (f : A → B) (hf : Function.Surjective f) :
    I.rlp ((Arrow.mk f).augmentedCechNerve.hom) := by
  classical
  let fhom : A ⟶ B := f
  have hObj0 :
      (CategoryTheory.Arrow.cechNerve (Arrow.mk fhom)).obj (op ⦋0⦌) =
        widePullback B (fun _ : Fin 1 ↦ A) (fun _ ↦ fhom) := by
    rfl
  apply boundaryInclusions_rlp_of_zero_surjective_and_boundary_lifting
  · intro b
    let s : A ⟶ (CategoryTheory.Arrow.cechNerve (Arrow.mk fhom)).obj (op ⦋0⦌) :=
      WidePullback.lift fhom (fun _ ↦ 𝟙 A) (fun _ ↦ by simp)
    have hs :
        s ≫
            eqToHom hObj0 ≫
              (WidePullback.π (B := B) (objs := fun _ : Fin 1 ↦ A) (arrows := fun _ ↦ fhom) 0 :
                widePullback B (fun _ : Fin 1 ↦ A) (fun _ ↦ fhom) ⟶ A) =
          𝟙 A := by
      cases hObj0
      simpa using
        (WidePullback.lift_π (arrows := fun _ : Fin 1 ↦ fhom) (f := fhom)
          (fs := fun _ : Fin 1 ↦ 𝟙 A) (w := fun _ ↦ by simp) 0)
    rcases hf b with ⟨a, rfl⟩
    have hcomp :
        s ≫ eqToHom hObj0 ≫
            WidePullback.base (B := B) (objs := fun _ : Fin 1 ↦ A) (arrows := fun _ ↦ fhom) = fhom := by
      rw [← Category.assoc]
      rw [show WidePullback.base (B := B) (objs := fun _ : Fin 1 ↦ A) (arrows := fun _ ↦ fhom) =
          (WidePullback.π (B := B) (objs := fun _ : Fin 1 ↦ A) (arrows := fun _ ↦ fhom) 0 :
            widePullback B (fun _ : Fin 1 ↦ A) (fun _ ↦ fhom) ⟶ A) ≫ fhom by
            simpa using
              (WidePullback.π_arrow (B := B) (objs := fun _ : Fin 1 ↦ A)
                (arrows := fun _ ↦ fhom) 0)]
      simpa [Category.assoc] using congrArg (· ≫ fhom) hs
    let aug0 : (Arrow.mk fhom).cechNerve _⦋0⦌ ⟶ B :=
      (CategoryTheory.Arrow.augmentedCechNerve (Arrow.mk fhom)).hom.app (op ⦋0⦌)
    have haug_comp :
        aug0 (s a) =
          ((s ≫ eqToHom hObj0 ≫
              WidePullback.base (B := B) (objs := fun _ : Fin 1 ↦ A) (arrows := fun _ ↦ fhom)) a) := by
      cases hObj0
      rfl
    exact ⟨s a, by simpa [aug0] using haug_comp.trans (congrFun hcomp a)⟩
  · intro n
    refine ⟨?_⟩
    intro u v sq
    let boundaryZeroLift :
        (∂Δ[n + 1] : SSet.{u}).obj (op ⦋0⦌) ⟶ A :=
      u.app (op ⦋0⦌) ≫
        eqToHom hObj0 ≫
          (WidePullback.π (B := B) (objs := fun _ : Fin 1 ↦ A) (arrows := fun _ ↦ fhom) 0 :
            widePullback B (fun _ : Fin 1 ↦ A) (fun _ ↦ fhom) ⟶ A)
    have hboundaryZeroLift :
        boundaryZeroLift ≫ fhom =
          (∂Δ[n + 1].ι).app (op ⦋0⦌) ≫ v.app (op ⦋0⦌) := by
      -- Read the commutative square on `0`-simplices and rewrite the augmentation as the common
      -- base map of the one-fold wide pullback.
      simpa [boundaryZeroLift, fhom, Category.assoc, CategoryTheory.Arrow.augmentedCechNerve,
        WidePullback.π_arrow] using congrArg (fun η ↦ η.app (op ⦋0⦌)) sq.w
    let e0 :=
      Equiv.ofBijective ((∂Δ[n + 1].ι).app (op ⦋0⦌)) (boundary_zero_bijective n)
    let simplexZeroLift :
        (Δ[n + 1] : SSet.{u}).obj (op ⦋0⦌) ⟶ A :=
      fun x ↦ boundaryZeroLift (e0.symm x)
    have hsimplexZeroLift_restricts :
        (∂Δ[n + 1].ι).app (op ⦋0⦌) ≫ simplexZeroLift = boundaryZeroLift := by
      -- The extension was defined by precomposing with the inverse bijection on vertices.
      ext x
      exact congrArg boundaryZeroLift (e0.left_inv x)
    have hsimplexZeroLift_lies_over_v :
        simplexZeroLift ≫ fhom = v.app (op ⦋0⦌) := by
      -- Evaluate the boundary equality at the inverse image of a vertex.
      ext x
      have hx := congrFun hboundaryZeroLift (e0.symm x)
      calc
        f (simplexZeroLift x)
            = f (boundaryZeroLift (e0.symm x)) := rfl
        _ = v.app (op ⦋0⦌) ((∂Δ[n + 1].ι).app (op ⦋0⦌) (e0.symm x)) := by
              simpa [boundaryZeroLift, Category.assoc] using hx
        _ = v.app (op ⦋0⦌) x := by
              simpa [e0] using congrArg (v.app (op ⦋0⦌)) (e0.apply_symm_apply x)
    let simplexArrow : Arrow.mk (v.app (op ⦋0⦌)) ⟶ Arrow.mk fhom :=
      Arrow.homMk simplexZeroLift (𝟙 B) hsimplexZeroLift_lies_over_v
    let l : Δ[n + 1] ⟶ (Arrow.mk fhom).cechNerve :=
      augmentationToCechNerve v ≫ Arrow.mapCechNerve simplexArrow
    have hObj0v :
        (CategoryTheory.Arrow.cechNerve (Arrow.mk (v.app (op ⦋0⦌)))).obj (op ⦋0⦌) =
          widePullback B (fun _ : Fin 1 ↦ (Δ[n + 1] : SSet.{u}).obj (op ⦋0⦌))
            (fun _ ↦ v.app (op ⦋0⦌)) := by
      rfl
    have hmap_zero :
        (Arrow.mapCechNerve simplexArrow).app (op ⦋0⦌) ≫
            eqToHom hObj0 ≫
                (WidePullback.π (B := B) (objs := fun _ : Fin 1 ↦ A) (arrows := fun _ ↦ fhom) 0 :
                widePullback B (fun _ : Fin 1 ↦ A) (fun _ ↦ fhom) ⟶ A) =
          eqToHom hObj0v ≫
              (WidePullback.π (B := B)
                (objs := fun _ : Fin 1 ↦ (Δ[n + 1] : SSet.{u}).obj (op ⦋0⦌))
                (arrows := fun _ ↦ v.app (op ⦋0⦌)) 0 :
                widePullback B
                  (fun _ : Fin 1 ↦ (Δ[n + 1] : SSet.{u}).obj (op ⦋0⦌))
                  (fun _ ↦ v.app (op ⦋0⦌)) ⟶
                    (Δ[n + 1] : SSet.{u}).obj (op ⦋0⦌)) ≫
            simplexZeroLift := by
      cases hObj0
      cases hObj0v
      simpa [simplexArrow, Category.assoc, CategoryTheory.Arrow.mapCechNerve,
        CategoryTheory.Arrow.cechNerve] using
        (WidePullback.lift_π (arrows := fun _ : Fin 1 ↦ fhom)
          (f := WidePullback.base (fun _ : Fin 1 ↦ v.app (op ⦋0⦌)) ≫ 𝟙 B)
          (fs := fun i : Fin 1 ↦
            WidePullback.π (fun _ : Fin 1 ↦ v.app (op ⦋0⦌)) i ≫ simplexZeroLift)
          (w := fun _ ↦ by simp [Category.assoc, hsimplexZeroLift_lies_over_v]) 0)
    have haug_zero_v :
        (augmentationToCechNerve v).app (op ⦋0⦌) ≫
            eqToHom hObj0v ≫
              (WidePullback.π (B := B)
                (objs := fun _ : Fin 1 ↦ (Δ[n + 1] : SSet.{u}).obj (op ⦋0⦌))
                (arrows := fun _ ↦ v.app (op ⦋0⦌)) 0 :
                  widePullback B
                    (fun _ : Fin 1 ↦ (Δ[n + 1] : SSet.{u}).obj (op ⦋0⦌))
                    (fun _ ↦ v.app (op ⦋0⦌)) ⟶
                      (Δ[n + 1] : SSet.{u}).obj (op ⦋0⦌)) =
          𝟙 ((Δ[n + 1] : SSet.{u}).obj (op ⦋0⦌)) := by
      cases hObj0v
      simpa using augmentationToCechNerve_app_zero_pi (ε := v)
    have hl_zero :
        l.app (op ⦋0⦌) ≫
            eqToHom hObj0 ≫
              (WidePullback.π (B := B) (objs := fun _ : Fin 1 ↦ A) (arrows := fun _ ↦ fhom) 0 :
                widePullback B (fun _ : Fin 1 ↦ A) (fun _ ↦ fhom) ⟶ A) =
          simplexZeroLift := by
      calc
        l.app (op ⦋0⦌) ≫
            eqToHom hObj0 ≫
              (WidePullback.π (B := B) (objs := fun _ : Fin 1 ↦ A) (arrows := fun _ ↦ fhom) 0 :
                widePullback B (fun _ : Fin 1 ↦ A) (fun _ ↦ fhom) ⟶ A)
            = (augmentationToCechNerve v).app (op ⦋0⦌) ≫
                (Arrow.mapCechNerve simplexArrow).app (op ⦋0⦌) ≫
                  eqToHom hObj0 ≫
                    (WidePullback.π (B := B) (objs := fun _ : Fin 1 ↦ A) (arrows := fun _ ↦ fhom) 0 :
                      widePullback B (fun _ : Fin 1 ↦ A) (fun _ ↦ fhom) ⟶ A) := by
                simp [l, Category.assoc]
        _ = (augmentationToCechNerve v).app (op ⦋0⦌) ≫
              eqToHom hObj0v ≫
                (WidePullback.π (B := B)
                  (objs := fun _ : Fin 1 ↦ (Δ[n + 1] : SSet.{u}).obj (op ⦋0⦌))
                  (arrows := fun _ ↦ v.app (op ⦋0⦌)) 0 :
                  widePullback B
                    (fun _ : Fin 1 ↦ (Δ[n + 1] : SSet.{u}).obj (op ⦋0⦌))
                    (fun _ ↦ v.app (op ⦋0⦌)) ⟶
                      (Δ[n + 1] : SSet.{u}).obj (op ⦋0⦌)) ≫
                simplexZeroLift := by
              simpa [Category.assoc] using
                congrArg ((augmentationToCechNerve v).app (op ⦋0⦌) ≫ ·) hmap_zero
        _ = simplexZeroLift := by
              simpa [Category.assoc] using
                congrArg (· ≫ simplexZeroLift) haug_zero_v
    let augf : (Arrow.mk fhom).cechNerve ⟶ (const (Type u)).obj B :=
      (CategoryTheory.Arrow.augmentedCechNerve (Arrow.mk fhom)).hom
    let augv : (Arrow.mk (v.app (op ⦋0⦌))).cechNerve ⟶ (const (Type u)).obj B :=
      (CategoryTheory.Arrow.augmentedCechNerve (Arrow.mk (v.app (op ⦋0⦌)))).hom
    have hl_right :
        l ≫ augf = v := by
      calc
        l ≫ augf
            = augmentationToCechNerve v ≫
                (Arrow.mapCechNerve simplexArrow ≫ augf) := by
                  simp [l, augf, Category.assoc]
        _ = augmentationToCechNerve v ≫ augv := by
              ext m x
              dsimp [simplexArrow, augf, augv, CategoryTheory.Arrow.mapCechNerve,
                CategoryTheory.Arrow.augmentedCechNerve, CategoryTheory.Arrow.cechNerve]
              simpa using congrFun
                (WidePullback.lift_base
                  (B := B)
                  (objs := fun _ : Fin ((unop m).len + 1) ↦ (Δ[n + 1] : SSet.{u}).obj (op ⦋0⦌))
                  (arrows := fun _ ↦ v.app (op ⦋0⦌))
                  (f := WidePullback.base (fun _ : Fin ((unop m).len + 1) ↦ v.app (op ⦋0⦌)) ≫ 𝟙 B)
                  (fs := fun i : Fin ((unop m).len + 1) ↦
                    WidePullback.π (fun _ : Fin ((unop m).len + 1) ↦ v.app (op ⦋0⦌)) i ≫
                      simplexZeroLift)
                  (w := fun _ ↦ hsimplexZeroLift_lies_over_v))
                ((augmentationToCechNerve v).app m x)
        _ = v := by
              simpa [augv, Category.assoc] using
                (augmentationToCechNerve_comp_augmentedCechNerve_hom (ε := v))
    have hl_left : (∂Δ[n + 1].ι) ≫ l = u := by
      -- Compare the two boundary augmentations through the owner-level Čech adjunction.
      let boundaryAugmented : SimplicialObject.Augmented (Type u) :=
        { left := (∂Δ[n + 1] : SSet.{u})
          right := B
          hom := (∂Δ[n + 1].ι) ≫ v }
      have huAugmented_w :
          u ≫ (Arrow.mk fhom).augmentedCechNerve.hom =
            boundaryAugmented.hom ≫ 𝟙 ((const (Type u)).obj B) := by
        simpa [boundaryAugmented, fhom, Category.assoc] using sq.w
      let uAugmented :
          boundaryAugmented ⟶ (Arrow.mk fhom).augmentedCechNerve :=
        { left := u
          right := 𝟙 B
          w := huAugmented_w }
      have hlAugmented_w :
          (∂Δ[n + 1].ι) ≫ l ≫ (Arrow.mk fhom).augmentedCechNerve.hom =
            boundaryAugmented.hom ≫ 𝟙 ((const (Type u)).obj B) := by
        simpa [boundaryAugmented, augf, Category.assoc] using
          congrArg ((∂Δ[n + 1].ι) ≫ ·) hl_right
      let lBoundaryAugmented :
          boundaryAugmented ⟶ (Arrow.mk fhom).augmentedCechNerve :=
        { left := (∂Δ[n + 1].ι) ≫ l
          right := 𝟙 B
          w := hlAugmented_w }
      have hArrow :
          CategoryTheory.SimplicialObject.equivalenceRightToLeft boundaryAugmented
              (Arrow.mk fhom) lBoundaryAugmented =
            CategoryTheory.SimplicialObject.equivalenceRightToLeft boundaryAugmented
              (Arrow.mk fhom) uAugmented := by
        ext
        · rename_i x
          change
            ((l.app (op ⦋0⦌) ≫
                eqToHom hObj0 ≫
                  (WidePullback.π (B := B) (objs := fun _ : Fin 1 ↦ A)
                    (arrows := fun _ ↦ fhom) 0 :
                      widePullback B (fun _ : Fin 1 ↦ A) (fun _ ↦ fhom) ⟶ A))
              ((((∂Δ[n + 1].ι).app (op ⦋0⦌)) x)) =
              (u.app (op ⦋0⦌) ≫
                eqToHom hObj0 ≫
                  (WidePullback.π (B := B) (objs := fun _ : Fin 1 ↦ A)
                    (arrows := fun _ ↦ fhom) 0 :
                      widePullback B (fun _ : Fin 1 ↦ A) (fun _ ↦ fhom) ⟶ A)) x)
          calc
            ((l.app (op ⦋0⦌) ≫
                eqToHom hObj0 ≫
                  (WidePullback.π (B := B) (objs := fun _ : Fin 1 ↦ A)
                    (arrows := fun _ ↦ fhom) 0 :
                      widePullback B (fun _ : Fin 1 ↦ A) (fun _ ↦ fhom) ⟶ A))
              (((∂Δ[n + 1].ι).app (op ⦋0⦌)) x))
                = simplexZeroLift (((∂Δ[n + 1].ι).app (op ⦋0⦌)) x) := by
                    exact congrFun hl_zero (((∂Δ[n + 1].ι).app (op ⦋0⦌)) x)
            _ = boundaryZeroLift x := by
                  exact congrFun hsimplexZeroLift_restricts x
            _ = (u.app (op ⦋0⦌) ≫
                eqToHom hObj0 ≫
                  (WidePullback.π (B := B) (objs := fun _ : Fin 1 ↦ A)
                    (arrows := fun _ ↦ fhom) 0 :
                      widePullback B (fun _ : Fin 1 ↦ A) (fun _ ↦ fhom) ⟶ A)) x := by
                    rfl
        · rename_i y
          simp [lBoundaryAugmented, uAugmented]
      have hBoundaryAugmented :
          lBoundaryAugmented = uAugmented := by
        exact
          (CategoryTheory.SimplicialObject.cechNerveEquiv boundaryAugmented
            (Arrow.mk fhom)).symm.injective (by simpa using hArrow)
      simpa [lBoundaryAugmented, uAugmented] using
        congrArg (fun η ↦ η.left) hBoundaryAugmented
    refine CommSq.HasLift.mk' ?_
    refine { l := l, fac_left := ?_, fac_right := ?_ }
    · simpa using hl_left
    · simpa [augf] using hl_right
