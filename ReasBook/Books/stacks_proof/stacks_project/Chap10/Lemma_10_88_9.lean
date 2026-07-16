import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_8_2
import stacks_proof.stacks_project.Chap10.Definition_10_88_7
import stacks_proof.stacks_project.Chap10.Lemma_10_12_14

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct

universe u v w

namespace Module

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/- The proof follows the source presentation argument: tensor the two chosen directed
presentations over the product preorder, use tail factorizations componentwise, and identify the
resulting colimit with the tensor product of the two colimits. -/

/-- Helper for Chap10 Lemma 10 88 9: the product of two directed preorders is directed. -/
private instance instIsDirectedOrderProd {I J : Type*} [Preorder I] [Preorder J]
    [IsDirectedOrder I] [IsDirectedOrder J] : IsDirectedOrder (I × J) where
  directed a b := by
    -- Choose simultaneous upper bounds in the two factors and combine them componentwise.
    rcases exists_ge_ge a.1 b.1 with ⟨i, hai, hbi⟩
    rcases exists_ge_ge a.2 b.2 with ⟨j, haj, hbj⟩
    exact ⟨(i, j), ⟨hai, haj⟩, ⟨hbi, hbj⟩⟩

/-- Helper for Chap10 Lemma 10 88 9: a Mittag-Leffler presentation has eventual transition-map
factorizations. -/
private lemma presentation_exists_tail_factorization
    (P : MittagLefflerPresentation R M) :
    letI : Preorder P.index := P.indexPreorder
    ∀ i : P.index, ∃ j : P.index, ∃ hij : i ≤ j,
      ∀ k : P.index, ∀ hik : i ≤ k, ∃ h : P.diagram.obj k ⟶ P.diagram.obj j,
        P.diagram.map (homOfLE hij) = P.diagram.map (homOfLE hik) ≫ h := by
  classical
  letI : Preorder P.index := P.indexPreorder
  letI : Nonempty P.index := P.indexNonempty
  letI : IsDirectedOrder P.index := P.indexDirected
  rcases P.presentation_isMittagLeffler with ⟨hfp, hall⟩
  rcases P.colimitIso with ⟨c⟩
  -- Clause `(4) -> (3)` of Proposition `10.88.6` extracts the source tail factorization.
  exact ((directed_colimit_presentation_mittag_leffler_tfae P.diagram hfp c).out 3 2).mp hall

/- Route correction: the failed route tried to tensor `ModuleCat` presentations using a mixed-
universe monoidal instance. The replacement route keeps the source proof's presentation invariant
but builds the tensor presentation as an explicit unbundled directed system on the product index. -/

/-- Helper for Chap10 Lemma 10 88 9: the linear transition map underlying a Mittag-Leffler
presentation. -/
private abbrev presentationStageMap (P : MittagLefflerPresentation R M) :
    letI : Preorder P.index := P.indexPreorder
    (i j : P.index) → i ≤ j → P.diagram.obj i →ₗ[R] P.diagram.obj j :=
  letI : Preorder P.index := P.indexPreorder
  fun _ _ h ↦ (P.diagram.map (homOfLE h)).hom

/-- Helper for Chap10 Lemma 10 88 9: the transition maps of a presentation form a directed
system. -/
private instance presentationStageMap_directedSystem
    (P : MittagLefflerPresentation R M) :
    letI : Preorder P.index := P.indexPreorder
    DirectedSystem (fun i : P.index ↦ P.diagram.obj i)
      (fun i j h ↦ presentationStageMap P i j h) := by
  letI : Preorder P.index := P.indexPreorder
  refine ⟨?_, ?_⟩
  · intro i x
    -- The transition along `i ≤ i` is the functorial identity map.
    simpa [presentationStageMap] using congr(($((P.diagram.map_id i)) x))
  · intro i j k hij hjk x
    -- Functoriality identifies the composite of two transitions with the direct transition.
    simpa [presentationStageMap] using
      congr(($((P.diagram.map_comp (homOfLE hij) (homOfLE hjk)).symm) x))

/-- Helper for Chap10 Lemma 10 88 9: the quotient-model direct limit of a presentation is
linearly equivalent to its presented module. -/
private noncomputable abbrev presentationDirectLimitLinearEquiv
    (P : MittagLefflerPresentation R M) :
    letI : Preorder P.index := P.indexPreorder
    letI : DecidableEq P.index := Classical.decEq P.index
    Module.DirectLimit (fun i : P.index ↦ P.diagram.obj i)
      (fun i j h ↦ presentationStageMap P i j h) ≃ₗ[R] M :=
  letI : Preorder P.index := P.indexPreorder
  letI : DecidableEq P.index := Classical.decEq P.index
  CategoryTheory.Iso.toLinearEquiv
    ((module_system_colimit_iso_moduleDirectLimit P.diagram).symm ≪≫ Classical.choice P.colimitIso)

/-- Helper for Chap10 Lemma 10 88 9: the product-index tensor stages
`(i, j) ↦ P_M i ⊗[R] P_N j`. -/
private abbrev tensorProductPresentationStage
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Preorder PN.index := PN.indexPreorder
    PM.index × PN.index → Type (max v w) :=
  letI : Preorder PM.index := PM.indexPreorder
  letI : Preorder PN.index := PN.indexPreorder
  fun p ↦ PM.diagram.obj p.1 ⊗[R] PN.diagram.obj p.2

/-- Helper for Chap10 Lemma 10 88 9: the transition map of the product-index tensor
presentation. -/
private abbrev tensorProductPresentationStageMap
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Preorder PN.index := PN.indexPreorder
    (p q : PM.index × PN.index) → p ≤ q →
      tensorProductPresentationStage PM PN p →ₗ[R] tensorProductPresentationStage PM PN q :=
  letI : Preorder PM.index := PM.indexPreorder
  letI : Preorder PN.index := PN.indexPreorder
  fun p q h ↦ TensorProduct.map (presentationStageMap PM p.1 q.1 h.1)
    (presentationStageMap PN p.2 q.2 h.2)

/-- Helper for Chap10 Lemma 10 88 9: for a fixed left stage, the right-index tensor stages. -/
private abbrev tensorProductInnerStage
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Preorder PN.index := PN.indexPreorder
    PM.index → PN.index → Type (max v w) :=
  letI : Preorder PM.index := PM.indexPreorder
  letI : Preorder PN.index := PN.indexPreorder
  fun i j ↦ PM.diagram.obj i ⊗[R] PN.diagram.obj j

/-- Helper for Chap10 Lemma 10 88 9: for a fixed left stage, the right-index tensor transition
maps. -/
private abbrev tensorProductInnerStageMap
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Preorder PN.index := PN.indexPreorder
    (i : PM.index) → (j k : PN.index) → j ≤ k →
      tensorProductInnerStage PM PN i j →ₗ[R] tensorProductInnerStage PM PN i k :=
  letI : Preorder PM.index := PM.indexPreorder
  letI : Preorder PN.index := PN.indexPreorder
  fun i j k h ↦ (presentationStageMap PN j k h).lTensor (PM.diagram.obj i)

/-- Helper for Chap10 Lemma 10 88 9: tensoring fixed left stages with the right presentation
again gives a directed system. -/
private instance tensorProductInnerStageMap_directedSystem
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Preorder PN.index := PN.indexPreorder
    (i : PM.index) → DirectedSystem (tensorProductInnerStage PM PN i)
      (fun j k h ↦ tensorProductInnerStageMap PM PN i j k h) := by
  letI : Preorder PM.index := PM.indexPreorder
  letI : Preorder PN.index := PN.indexPreorder
  intro i
  infer_instance

/-- Helper for Chap10 Lemma 10 88 9: changing the left tensor factor commutes with right-index
transition maps. -/
private lemma tensorProductLeftMap_comm_innerStageMap
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Preorder PN.index := PN.indexPreorder
    ∀ {i i' : PM.index}, (hi : i ≤ i') → ∀ {j j' : PN.index}, (hj : j ≤ j') →
    ((presentationStageMap PM i i' hi).rTensor (PN.diagram.obj j')).comp
      (tensorProductInnerStageMap PM PN i j j' hj) =
    (tensorProductInnerStageMap PM PN i' j j' hj).comp
      ((presentationStageMap PM i i' hi).rTensor (PN.diagram.obj j)) := by
  letI : Preorder PM.index := PM.indexPreorder
  letI : Preorder PN.index := PN.indexPreorder
  intro i i' hi j j' hj
  -- On pure tensors this is the naturality square for `TensorProduct.map`.
  ext x y
  simp [tensorProductInnerStageMap]

/-- Helper for Chap10 Lemma 10 88 9: the iterated direct-limit stage obtained after first taking
the right-index direct limit. -/
private noncomputable abbrev tensorProductIteratedStage
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Preorder PN.index := PN.indexPreorder
    letI : DecidableEq PN.index := Classical.decEq PN.index
    PM.index → Type (max v w) :=
  letI : Preorder PM.index := PM.indexPreorder
  letI : Preorder PN.index := PN.indexPreorder
  letI : DecidableEq PN.index := Classical.decEq PN.index
  fun i ↦ Module.DirectLimit (tensorProductInnerStage PM PN i)
    (tensorProductInnerStageMap PM PN i)

/-- Helper for Chap10 Lemma 10 88 9: left-index transition maps between the inner direct limits. -/
private noncomputable abbrev tensorProductIteratedStageMap
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Preorder PN.index := PN.indexPreorder
    letI : DecidableEq PN.index := Classical.decEq PN.index
    (i i' : PM.index) → i ≤ i' →
      tensorProductIteratedStage PM PN i →ₗ[R] tensorProductIteratedStage PM PN i' :=
  letI : Preorder PM.index := PM.indexPreorder
  letI : Preorder PN.index := PN.indexPreorder
  letI : DecidableEq PN.index := Classical.decEq PN.index
  fun i i' h ↦ Module.DirectLimit.map
    (fun j ↦ (presentationStageMap PM i i' h).rTensor (PN.diagram.obj j))
    (fun _ _ hj ↦ tensorProductLeftMap_comm_innerStageMap PM PN h hj)

/-- Helper for Chap10 Lemma 10 88 9: the iterated transition maps form a directed system. -/
private instance tensorProductIteratedStageMap_directedSystem
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Preorder PN.index := PN.indexPreorder
    letI : Nonempty PN.index := PN.indexNonempty
    letI : IsDirectedOrder PN.index := PN.indexDirected
    letI : DecidableEq PN.index := Classical.decEq PN.index
    DirectedSystem (tensorProductIteratedStage PM PN)
      (fun i j h ↦ tensorProductIteratedStageMap PM PN i j h) := by
  letI : Preorder PM.index := PM.indexPreorder
  letI : Preorder PN.index := PN.indexPreorder
  letI : Nonempty PN.index := PN.indexNonempty
  letI : IsDirectedOrder PN.index := PN.indexDirected
  letI : DecidableEq PN.index := Classical.decEq PN.index
  refine ⟨?_, ?_⟩
  · intro i z
    -- Reduce the identity law to the canonical generators of the inner direct limit.
    induction z using Module.DirectLimit.induction_on with
    | ih l x =>
        have hmap :
            presentationStageMap PM i i (le_refl i) =
              LinearMap.id := by
          ext a
          simpa [presentationStageMap] using congr(($((PM.diagram.map_id i)) a))
        simp only [tensorProductIteratedStageMap, Module.DirectLimit.map_apply_of]
        simpa [hmap]
  · intro i j k hij hjk z
    -- Reduce composition to generators, where it is functoriality of the left presentation.
    induction z using Module.DirectLimit.induction_on with
    | ih l x =>
        have hmap :
            (presentationStageMap PM j i hjk).comp (presentationStageMap PM k j hij) =
              presentationStageMap PM k i (hij.trans hjk) := by
          ext a
          simpa [presentationStageMap] using
            congr(($((PM.diagram.map_comp (homOfLE hij) (homOfLE hjk)).symm) a))
        simp only [tensorProductIteratedStageMap, Module.DirectLimit.map_apply_of]
        have htensor :
            ((presentationStageMap PM j i hjk).rTensor (PN.diagram.obj l)).comp
                ((presentationStageMap PM k j hij).rTensor (PN.diagram.obj l)) =
              (presentationStageMap PM k i (hij.trans hjk)).rTensor (PN.diagram.obj l) := by
          simpa [LinearMap.rTensor_comp] using
            congrArg (fun f : PM.diagram.obj k →ₗ[R] PM.diagram.obj i ↦
              f.rTensor (PN.diagram.obj l)) hmap
        exact congrArg
          (fun y ↦ (Module.DirectLimit.of R PN.index (tensorProductInnerStage PM PN i)
            (tensorProductInnerStageMap PM PN i) l) y)
          (LinearMap.congr_fun htensor x)

/-- Helper for Chap10 Lemma 10 88 9: the product-index tensor transition maps form a directed
system. -/
private instance tensorProductPresentationStageMap_directedSystem
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Preorder PN.index := PN.indexPreorder
    DirectedSystem (tensorProductPresentationStage PM PN)
      (fun p q h ↦ tensorProductPresentationStageMap PM PN p q h) := by
  letI : Preorder PM.index := PM.indexPreorder
  letI : Preorder PN.index := PN.indexPreorder
  refine ⟨?_, ?_⟩
  · intro p x
    -- The identity transition is the tensor product of the two component identity transitions.
    induction x using TensorProduct.induction_on with
    | zero =>
        simp [tensorProductPresentationStageMap, presentationStageMap]
    | tmul a b =>
        simp [tensorProductPresentationStageMap, presentationStageMap]
    | add x y hx hy =>
        simp [hx, hy]
  · intro p q r hpq hqr x
    -- Composition of tensor transitions follows from functoriality in each component.
    induction x using TensorProduct.induction_on with
    | zero =>
        simp [tensorProductPresentationStageMap, presentationStageMap]
    | tmul a b =>
        have ha :
            (PM.diagram.map (homOfLE hqr.1)).hom
                ((PM.diagram.map (homOfLE hpq.1)).hom a) =
              (PM.diagram.map (homOfLE (hpq.1.trans hqr.1))).hom a := by
          simpa using
            congr(($((PM.diagram.map_comp (homOfLE hpq.1) (homOfLE hqr.1)).symm) a))
        have hb :
            (PN.diagram.map (homOfLE hqr.2)).hom
                ((PN.diagram.map (homOfLE hpq.2)).hom b) =
              (PN.diagram.map (homOfLE (hpq.2.trans hqr.2))).hom b := by
          simpa using
            congr(($((PN.diagram.map_comp (homOfLE hpq.2) (homOfLE hqr.2)).symm) b))
        simp [tensorProductPresentationStageMap, presentationStageMap, ha, hb]
    | add x y hx hy =>
        simp [hx, hy]

/-- Helper for Chap10 Lemma 10 88 9: the product-index direct limit of the tensor presentation. -/
private noncomputable abbrev tensorProductPresentationDirectLimit
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Preorder PN.index := PN.indexPreorder
    letI : DecidableEq (PM.index × PN.index) := Classical.decEq (PM.index × PN.index)
    Type (max v w) :=
  letI : Preorder PM.index := PM.indexPreorder
  letI : Preorder PN.index := PN.indexPreorder
  letI : DecidableEq (PM.index × PN.index) := Classical.decEq (PM.index × PN.index)
  Module.DirectLimit (tensorProductPresentationStage PM PN)
    (fun p q h ↦ tensorProductPresentationStageMap PM PN p q h)

/-- Helper for Chap10 Lemma 10 88 9: the iterated direct limit of the tensor presentation. -/
private noncomputable abbrev tensorProductIteratedDirectLimit
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Preorder PN.index := PN.indexPreorder
    letI : Nonempty PN.index := PN.indexNonempty
    letI : IsDirectedOrder PN.index := PN.indexDirected
    letI : DecidableEq PM.index := Classical.decEq PM.index
    letI : DecidableEq PN.index := Classical.decEq PN.index
    Type (max v w) :=
  letI : Preorder PM.index := PM.indexPreorder
  letI : Preorder PN.index := PN.indexPreorder
  letI : Nonempty PN.index := PN.indexNonempty
  letI : IsDirectedOrder PN.index := PN.indexDirected
  letI : DecidableEq PM.index := Classical.decEq PM.index
  letI : DecidableEq PN.index := Classical.decEq PN.index
  Module.DirectLimit (tensorProductIteratedStage PM PN)
    (fun i j h ↦ tensorProductIteratedStageMap PM PN i j h)

/-- Helper for Chap10 Lemma 10 88 9: the self transition in a presentation is the identity
linear map. -/
private lemma presentationStageMap_self (P : MittagLefflerPresentation R M) :
    letI : Preorder P.index := P.indexPreorder
    ∀ i : P.index, presentationStageMap P i i (le_refl i) = LinearMap.id := by
  letI : Preorder P.index := P.indexPreorder
  intro i
  -- Evaluate functoriality of the identity morphism on each element.
  ext x
  simpa [presentationStageMap] using congr(($((P.diagram.map_id i)) x))

/-- Helper for Chap10 Lemma 10 88 9: if only the right coordinate changes, the product-index
transition is the inner-stage transition. -/
private lemma tensorProductPresentationStageMap_left_refl
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Preorder PN.index := PN.indexPreorder
    ∀ (i : PM.index) {j k : PN.index} (hjk : j ≤ k),
      tensorProductPresentationStageMap PM PN (i, j) (i, k) ⟨le_refl i, hjk⟩ =
        tensorProductInnerStageMap PM PN i j k hjk := by
  letI : Preorder PM.index := PM.indexPreorder
  letI : Preorder PN.index := PN.indexPreorder
  intro i j k hjk
  -- The left transition is the identity, so only the right tensor factor moves.
  ext a b
  simp [tensorProductPresentationStageMap, tensorProductInnerStageMap,
    presentationStageMap_self PM i]

/-- Helper for Chap10 Lemma 10 88 9: if only the left coordinate changes, the product-index
transition is right tensoring by the left presentation transition. -/
private lemma tensorProductPresentationStageMap_right_refl
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Preorder PN.index := PN.indexPreorder
    ∀ {i k : PM.index} (hik : i ≤ k) (j : PN.index),
      tensorProductPresentationStageMap PM PN (i, j) (k, j) ⟨hik, le_refl j⟩ =
        (presentationStageMap PM i k hik).rTensor (PN.diagram.obj j) := by
  letI : Preorder PM.index := PM.indexPreorder
  letI : Preorder PN.index := PN.indexPreorder
  intro i k hik j
  -- The right transition is the identity, so only the left tensor factor moves.
  ext a b
  simp [tensorProductPresentationStageMap, presentationStageMap_self PN j]

/-- Helper for Chap10 Lemma 10 88 9: the product-to-iterated generator maps are compatible with
the product-index transition relation. -/
private lemma tensorProductProductToIteratedMap_compat
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Nonempty PM.index := PM.indexNonempty
    letI : IsDirectedOrder PM.index := PM.indexDirected
    letI : Preorder PN.index := PN.indexPreorder
    letI : Nonempty PN.index := PN.indexNonempty
    letI : IsDirectedOrder PN.index := PN.indexDirected
    letI : DecidableEq PM.index := Classical.decEq PM.index
    letI : DecidableEq PN.index := Classical.decEq PN.index
    ∀ (p q : PM.index × PN.index) (hpq : p ≤ q)
      (x : tensorProductPresentationStage PM PN p),
      ((Module.DirectLimit.of R PM.index (tensorProductIteratedStage PM PN)
          (fun i j h ↦ tensorProductIteratedStageMap PM PN i j h) q.1).comp
        (Module.DirectLimit.of R PN.index (tensorProductInnerStage PM PN q.1)
          (tensorProductInnerStageMap PM PN q.1) q.2))
          ((tensorProductPresentationStageMap PM PN p q hpq) x) =
      ((Module.DirectLimit.of R PM.index (tensorProductIteratedStage PM PN)
          (fun i j h ↦ tensorProductIteratedStageMap PM PN i j h) p.1).comp
        (Module.DirectLimit.of R PN.index (tensorProductInnerStage PM PN p.1)
          (tensorProductInnerStageMap PM PN p.1) p.2)) x := by
  letI : Preorder PM.index := PM.indexPreorder
  letI : Nonempty PM.index := PM.indexNonempty
  letI : IsDirectedOrder PM.index := PM.indexDirected
  letI : Preorder PN.index := PN.indexPreorder
  letI : Nonempty PN.index := PN.indexNonempty
  letI : IsDirectedOrder PN.index := PN.indexDirected
  letI : DecidableEq PM.index := Classical.decEq PM.index
  letI : DecidableEq PN.index := Classical.decEq PN.index
  intro p q hpq x
  -- It is enough to check the relation on pure tensors; the two direct-limit relations then
  -- move first in the right coordinate and then in the left coordinate.
  induction x using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul a b =>
      simp only [LinearMap.comp_apply, tensorProductPresentationStageMap,
        TensorProduct.map_tmul, tensorProductIteratedStageMap]
      have hright :
          (Module.DirectLimit.of R PN.index (tensorProductInnerStage PM PN q.1)
              (tensorProductInnerStageMap PM PN q.1) q.2)
              ((presentationStageMap PM p.1 q.1 hpq.1) a ⊗ₜ[R]
                (presentationStageMap PN p.2 q.2 hpq.2) b) =
            (Module.DirectLimit.of R PN.index (tensorProductInnerStage PM PN q.1)
              (tensorProductInnerStageMap PM PN q.1) p.2)
              ((presentationStageMap PM p.1 q.1 hpq.1) a ⊗ₜ[R] b) := by
        -- First use the right-coordinate direct-limit relation.
        simpa [tensorProductInnerStageMap] using
          (Module.DirectLimit.of_f (R := R) (ι := PN.index)
            (G := tensorProductInnerStage PM PN q.1)
            (f := tensorProductInnerStageMap PM PN q.1)
            (i := p.2) (j := q.2) (hij := hpq.2)
            (x := (presentationStageMap PM p.1 q.1 hpq.1) a ⊗ₜ[R] b))
      rw [hright]
      have hleftMap :
          (tensorProductIteratedStageMap PM PN p.1 q.1 hpq.1)
              ((Module.DirectLimit.of R PN.index (tensorProductInnerStage PM PN p.1)
                (tensorProductInnerStageMap PM PN p.1) p.2) (a ⊗ₜ[R] b)) =
            (Module.DirectLimit.of R PN.index (tensorProductInnerStage PM PN q.1)
              (tensorProductInnerStageMap PM PN q.1) p.2)
              ((presentationStageMap PM p.1 q.1 hpq.1) a ⊗ₜ[R] b) := by
        -- The left-coordinate transition is the map of the inner direct limit on generators.
        simpa [tensorProductIteratedStageMap] using
          (Module.DirectLimit.map_apply_of
            (g := fun j ↦ (presentationStageMap PM p.1 q.1 hpq.1).rTensor
              (PN.diagram.obj j))
            (hg := fun j j' hj ↦ tensorProductLeftMap_comm_innerStageMap PM PN hpq.1 hj)
            (x := a ⊗ₜ[R] b))
      rw [← hleftMap]
      exact Module.DirectLimit.of_f
  | add x y hx hy =>
      simp [map_add, hx, hy]

/-- Helper for Chap10 Lemma 10 88 9: the forward map from the product-index direct limit to the
iterated direct limit. -/
private noncomputable def tensorProductProductToIteratedMap
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Nonempty PM.index := PM.indexNonempty
    letI : IsDirectedOrder PM.index := PM.indexDirected
    letI : Preorder PN.index := PN.indexPreorder
    letI : Nonempty PN.index := PN.indexNonempty
    letI : IsDirectedOrder PN.index := PN.indexDirected
    letI : DecidableEq PM.index := Classical.decEq PM.index
    letI : DecidableEq PN.index := Classical.decEq PN.index
    letI : DecidableEq (PM.index × PN.index) := Classical.decEq (PM.index × PN.index)
    tensorProductPresentationDirectLimit PM PN →ₗ[R]
      tensorProductIteratedDirectLimit PM PN :=
  letI : Preorder PM.index := PM.indexPreorder
  letI : Nonempty PM.index := PM.indexNonempty
  letI : IsDirectedOrder PM.index := PM.indexDirected
  letI : Preorder PN.index := PN.indexPreorder
  letI : Nonempty PN.index := PN.indexNonempty
  letI : IsDirectedOrder PN.index := PN.indexDirected
  letI : DecidableEq PM.index := Classical.decEq PM.index
  letI : DecidableEq PN.index := Classical.decEq PN.index
  letI : DecidableEq (PM.index × PN.index) := Classical.decEq (PM.index × PN.index)
  Module.DirectLimit.lift R (PM.index × PN.index) (tensorProductPresentationStage PM PN)
    (fun p q h ↦ tensorProductPresentationStageMap PM PN p q h)
    (fun p ↦
      (Module.DirectLimit.of R PM.index (tensorProductIteratedStage PM PN)
        (fun i j h ↦ tensorProductIteratedStageMap PM PN i j h) p.1).comp
      (Module.DirectLimit.of R PN.index (tensorProductInnerStage PM PN p.1)
        (tensorProductInnerStageMap PM PN p.1) p.2))
    (tensorProductProductToIteratedMap_compat PM PN)

/-- Helper for Chap10 Lemma 10 88 9: the forward map sends product-index generators to iterated
generators. -/
private lemma tensorProductProductToIteratedMap_of
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Nonempty PM.index := PM.indexNonempty
    letI : IsDirectedOrder PM.index := PM.indexDirected
    letI : Preorder PN.index := PN.indexPreorder
    letI : Nonempty PN.index := PN.indexNonempty
    letI : IsDirectedOrder PN.index := PN.indexDirected
    letI : DecidableEq PM.index := Classical.decEq PM.index
    letI : DecidableEq PN.index := Classical.decEq PN.index
    letI : DecidableEq (PM.index × PN.index) := Classical.decEq (PM.index × PN.index)
    ∀ (p : PM.index × PN.index) (x : tensorProductPresentationStage PM PN p),
      tensorProductProductToIteratedMap PM PN
        ((Module.DirectLimit.of R (PM.index × PN.index) (tensorProductPresentationStage PM PN)
          (fun p q h ↦ tensorProductPresentationStageMap PM PN p q h) p) x) =
      ((Module.DirectLimit.of R PM.index (tensorProductIteratedStage PM PN)
          (fun i j h ↦ tensorProductIteratedStageMap PM PN i j h) p.1).comp
        (Module.DirectLimit.of R PN.index (tensorProductInnerStage PM PN p.1)
          (tensorProductInnerStageMap PM PN p.1) p.2)) x := by
  letI : Preorder PM.index := PM.indexPreorder
  letI : Nonempty PM.index := PM.indexNonempty
  letI : IsDirectedOrder PM.index := PM.indexDirected
  letI : Preorder PN.index := PN.indexPreorder
  letI : Nonempty PN.index := PN.indexNonempty
  letI : IsDirectedOrder PN.index := PN.indexDirected
  letI : DecidableEq PM.index := Classical.decEq PM.index
  letI : DecidableEq PN.index := Classical.decEq PN.index
  letI : DecidableEq (PM.index × PN.index) := Classical.decEq (PM.index × PN.index)
  intro p x
  -- This is the defining computation rule for the direct-limit lift.
  simpa [tensorProductProductToIteratedMap] using
    (Module.DirectLimit.lift_of (R := R) (ι := PM.index × PN.index)
      (G := tensorProductPresentationStage PM PN)
      (f := fun p q h ↦ tensorProductPresentationStageMap PM PN p q h)
      (P := tensorProductIteratedDirectLimit PM PN)
      (g := fun p ↦
        (Module.DirectLimit.of R PM.index (tensorProductIteratedStage PM PN)
          (fun i j h ↦ tensorProductIteratedStageMap PM PN i j h) p.1).comp
        (Module.DirectLimit.of R PN.index (tensorProductInnerStage PM PN p.1)
          (tensorProductInnerStageMap PM PN p.1) p.2))
      (Hg := tensorProductProductToIteratedMap_compat PM PN) (i := p) x)

/-- Helper for Chap10 Lemma 10 88 9: for a fixed left index, inner direct-limit generators map
to product-index generators compatibly with right transitions. -/
private lemma tensorProductInnerToProductMap_compat
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Preorder PN.index := PN.indexPreorder
    letI : DecidableEq (PM.index × PN.index) := Classical.decEq (PM.index × PN.index)
    ∀ (i : PM.index) (j k : PN.index) (hjk : j ≤ k)
      (x : tensorProductInnerStage PM PN i j),
      (Module.DirectLimit.of R (PM.index × PN.index) (tensorProductPresentationStage PM PN)
          (fun p q h ↦ tensorProductPresentationStageMap PM PN p q h) (i, k))
          ((tensorProductInnerStageMap PM PN i j k hjk) x) =
        (Module.DirectLimit.of R (PM.index × PN.index) (tensorProductPresentationStage PM PN)
          (fun p q h ↦ tensorProductPresentationStageMap PM PN p q h) (i, j)) x := by
  letI : Preorder PM.index := PM.indexPreorder
  letI : Preorder PN.index := PN.indexPreorder
  letI : DecidableEq (PM.index × PN.index) := Classical.decEq (PM.index × PN.index)
  intro i j k hjk x
  -- Rewrite the inner transition as the corresponding one-coordinate product transition, then
  -- use the product direct-limit relation.
  rw [← LinearMap.congr_fun (tensorProductPresentationStageMap_left_refl PM PN i hjk) x]
  exact Module.DirectLimit.of_f

/-- Helper for Chap10 Lemma 10 88 9: for a fixed left index, map the right direct limit into the
product-index direct limit. -/
private noncomputable def tensorProductInnerToProductMap
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Preorder PN.index := PN.indexPreorder
    letI : DecidableEq PN.index := Classical.decEq PN.index
    letI : DecidableEq (PM.index × PN.index) := Classical.decEq (PM.index × PN.index)
    (i : PM.index) →
      tensorProductIteratedStage PM PN i →ₗ[R] tensorProductPresentationDirectLimit PM PN :=
  letI : Preorder PM.index := PM.indexPreorder
  letI : Preorder PN.index := PN.indexPreorder
  letI : DecidableEq PN.index := Classical.decEq PN.index
  letI : DecidableEq (PM.index × PN.index) := Classical.decEq (PM.index × PN.index)
  fun i ↦
    Module.DirectLimit.lift R PN.index (tensorProductInnerStage PM PN i)
      (tensorProductInnerStageMap PM PN i)
      (fun j ↦
        Module.DirectLimit.of R (PM.index × PN.index) (tensorProductPresentationStage PM PN)
          (fun p q h ↦ tensorProductPresentationStageMap PM PN p q h) (i, j))
      (tensorProductInnerToProductMap_compat PM PN i)

/-- Helper for Chap10 Lemma 10 88 9: the fixed-left reverse map sends inner generators to
product-index generators. -/
private lemma tensorProductInnerToProductMap_of
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Preorder PN.index := PN.indexPreorder
    letI : DecidableEq PN.index := Classical.decEq PN.index
    letI : DecidableEq (PM.index × PN.index) := Classical.decEq (PM.index × PN.index)
    ∀ (i : PM.index) (j : PN.index) (x : tensorProductInnerStage PM PN i j),
      tensorProductInnerToProductMap PM PN i
        ((Module.DirectLimit.of R PN.index (tensorProductInnerStage PM PN i)
          (tensorProductInnerStageMap PM PN i) j) x) =
        (Module.DirectLimit.of R (PM.index × PN.index) (tensorProductPresentationStage PM PN)
          (fun p q h ↦ tensorProductPresentationStageMap PM PN p q h) (i, j)) x := by
  letI : Preorder PM.index := PM.indexPreorder
  letI : Preorder PN.index := PN.indexPreorder
  letI : DecidableEq PN.index := Classical.decEq PN.index
  letI : DecidableEq (PM.index × PN.index) := Classical.decEq (PM.index × PN.index)
  intro i j x
  -- This is the defining computation rule for the inner direct-limit lift.
  simpa [tensorProductInnerToProductMap] using
    (Module.DirectLimit.lift_of (R := R) (ι := PN.index)
      (G := tensorProductInnerStage PM PN i)
      (f := tensorProductInnerStageMap PM PN i)
      (P := tensorProductPresentationDirectLimit PM PN)
      (g := fun j ↦
        Module.DirectLimit.of R (PM.index × PN.index) (tensorProductPresentationStage PM PN)
          (fun p q h ↦ tensorProductPresentationStageMap PM PN p q h) (i, j))
      (Hg := tensorProductInnerToProductMap_compat PM PN i) (i := j) x)

/-- Helper for Chap10 Lemma 10 88 9: the fixed-left reverse maps are compatible with left
transitions in the outer direct limit. -/
private lemma tensorProductIteratedToProductMap_compat
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Preorder PN.index := PN.indexPreorder
    letI : Nonempty PN.index := PN.indexNonempty
    letI : IsDirectedOrder PN.index := PN.indexDirected
    letI : DecidableEq PN.index := Classical.decEq PN.index
    letI : DecidableEq (PM.index × PN.index) := Classical.decEq (PM.index × PN.index)
    ∀ (i k : PM.index) (hik : i ≤ k) (z : tensorProductIteratedStage PM PN i),
      tensorProductInnerToProductMap PM PN k
          ((tensorProductIteratedStageMap PM PN i k hik) z) =
        tensorProductInnerToProductMap PM PN i z := by
  letI : Preorder PM.index := PM.indexPreorder
  letI : Preorder PN.index := PN.indexPreorder
  letI : Nonempty PN.index := PN.indexNonempty
  letI : IsDirectedOrder PN.index := PN.indexDirected
  letI : DecidableEq PN.index := Classical.decEq PN.index
  letI : DecidableEq (PM.index × PN.index) := Classical.decEq (PM.index × PN.index)
  intro i k hik z
  -- Reduce the outer compatibility to the inner generators, where the product direct-limit
  -- relation changes only the left coordinate.
  induction z using Module.DirectLimit.induction_on with
  | ih j x =>
      simp only [tensorProductIteratedStageMap, Module.DirectLimit.map_apply_of]
      rw [tensorProductInnerToProductMap_of, tensorProductInnerToProductMap_of]
      rw [← LinearMap.congr_fun
        (tensorProductPresentationStageMap_right_refl PM PN hik j) x]
      exact Module.DirectLimit.of_f

/-- Helper for Chap10 Lemma 10 88 9: the reverse map from the iterated direct limit to the
product-index direct limit. -/
private noncomputable def tensorProductIteratedToProductMap
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Nonempty PM.index := PM.indexNonempty
    letI : IsDirectedOrder PM.index := PM.indexDirected
    letI : Preorder PN.index := PN.indexPreorder
    letI : Nonempty PN.index := PN.indexNonempty
    letI : IsDirectedOrder PN.index := PN.indexDirected
    letI : DecidableEq PM.index := Classical.decEq PM.index
    letI : DecidableEq PN.index := Classical.decEq PN.index
    letI : DecidableEq (PM.index × PN.index) := Classical.decEq (PM.index × PN.index)
    tensorProductIteratedDirectLimit PM PN →ₗ[R]
      tensorProductPresentationDirectLimit PM PN :=
  letI : Preorder PM.index := PM.indexPreorder
  letI : Nonempty PM.index := PM.indexNonempty
  letI : IsDirectedOrder PM.index := PM.indexDirected
  letI : Preorder PN.index := PN.indexPreorder
  letI : Nonempty PN.index := PN.indexNonempty
  letI : IsDirectedOrder PN.index := PN.indexDirected
  letI : DecidableEq PM.index := Classical.decEq PM.index
  letI : DecidableEq PN.index := Classical.decEq PN.index
  letI : DecidableEq (PM.index × PN.index) := Classical.decEq (PM.index × PN.index)
  Module.DirectLimit.lift R PM.index (tensorProductIteratedStage PM PN)
    (fun i j h ↦ tensorProductIteratedStageMap PM PN i j h)
    (fun i ↦ tensorProductInnerToProductMap PM PN i)
    (tensorProductIteratedToProductMap_compat PM PN)

/-- Helper for Chap10 Lemma 10 88 9: the reverse map sends outer generators to the fixed-left
reverse maps. -/
private lemma tensorProductIteratedToProductMap_of
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Nonempty PM.index := PM.indexNonempty
    letI : IsDirectedOrder PM.index := PM.indexDirected
    letI : Preorder PN.index := PN.indexPreorder
    letI : Nonempty PN.index := PN.indexNonempty
    letI : IsDirectedOrder PN.index := PN.indexDirected
    letI : DecidableEq PM.index := Classical.decEq PM.index
    letI : DecidableEq PN.index := Classical.decEq PN.index
    letI : DecidableEq (PM.index × PN.index) := Classical.decEq (PM.index × PN.index)
    ∀ (i : PM.index) (z : tensorProductIteratedStage PM PN i),
      tensorProductIteratedToProductMap PM PN
        ((Module.DirectLimit.of R PM.index (tensorProductIteratedStage PM PN)
          (fun i j h ↦ tensorProductIteratedStageMap PM PN i j h) i) z) =
        tensorProductInnerToProductMap PM PN i z := by
  letI : Preorder PM.index := PM.indexPreorder
  letI : Nonempty PM.index := PM.indexNonempty
  letI : IsDirectedOrder PM.index := PM.indexDirected
  letI : Preorder PN.index := PN.indexPreorder
  letI : Nonempty PN.index := PN.indexNonempty
  letI : IsDirectedOrder PN.index := PN.indexDirected
  letI : DecidableEq PM.index := Classical.decEq PM.index
  letI : DecidableEq PN.index := Classical.decEq PN.index
  letI : DecidableEq (PM.index × PN.index) := Classical.decEq (PM.index × PN.index)
  intro i z
  -- This is the defining computation rule for the outer direct-limit lift.
  simpa [tensorProductIteratedToProductMap] using
    (Module.DirectLimit.lift_of (R := R) (ι := PM.index)
      (G := tensorProductIteratedStage PM PN)
      (f := fun i j h ↦ tensorProductIteratedStageMap PM PN i j h)
      (P := tensorProductPresentationDirectLimit PM PN)
      (g := fun i ↦ tensorProductInnerToProductMap PM PN i)
      (Hg := tensorProductIteratedToProductMap_compat PM PN) (i := i) z)

/-- Helper for Chap10 Lemma 10 88 9: the reverse map sends iterated generators back to
product-index generators. -/
private lemma tensorProductIteratedToProductMap_of_of
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Nonempty PM.index := PM.indexNonempty
    letI : IsDirectedOrder PM.index := PM.indexDirected
    letI : Preorder PN.index := PN.indexPreorder
    letI : Nonempty PN.index := PN.indexNonempty
    letI : IsDirectedOrder PN.index := PN.indexDirected
    letI : DecidableEq PM.index := Classical.decEq PM.index
    letI : DecidableEq PN.index := Classical.decEq PN.index
    letI : DecidableEq (PM.index × PN.index) := Classical.decEq (PM.index × PN.index)
    ∀ (i : PM.index) (j : PN.index) (x : tensorProductInnerStage PM PN i j),
      tensorProductIteratedToProductMap PM PN
        ((Module.DirectLimit.of R PM.index (tensorProductIteratedStage PM PN)
          (fun i j h ↦ tensorProductIteratedStageMap PM PN i j h) i)
          ((Module.DirectLimit.of R PN.index (tensorProductInnerStage PM PN i)
            (tensorProductInnerStageMap PM PN i) j) x)) =
        (Module.DirectLimit.of R (PM.index × PN.index) (tensorProductPresentationStage PM PN)
          (fun p q h ↦ tensorProductPresentationStageMap PM PN p q h) (i, j)) x := by
  letI : Preorder PM.index := PM.indexPreorder
  letI : Nonempty PM.index := PM.indexNonempty
  letI : IsDirectedOrder PM.index := PM.indexDirected
  letI : Preorder PN.index := PN.indexPreorder
  letI : Nonempty PN.index := PN.indexNonempty
  letI : IsDirectedOrder PN.index := PN.indexDirected
  letI : DecidableEq PM.index := Classical.decEq PM.index
  letI : DecidableEq PN.index := Classical.decEq PN.index
  letI : DecidableEq (PM.index × PN.index) := Classical.decEq (PM.index × PN.index)
  intro i j x
  -- Combine the outer and inner generator formulas.
  rw [tensorProductIteratedToProductMap_of, tensorProductInnerToProductMap_of]

/-- Helper for Chap10 Lemma 10 88 9: the forward map followed by the reverse map is the identity
on the iterated direct limit. -/
private lemma tensorProductProductToIteratedMap_comp_iteratedToProductMap
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Nonempty PM.index := PM.indexNonempty
    letI : IsDirectedOrder PM.index := PM.indexDirected
    letI : Preorder PN.index := PN.indexPreorder
    letI : Nonempty PN.index := PN.indexNonempty
    letI : IsDirectedOrder PN.index := PN.indexDirected
    letI : DecidableEq PM.index := Classical.decEq PM.index
    letI : DecidableEq PN.index := Classical.decEq PN.index
    letI : DecidableEq (PM.index × PN.index) := Classical.decEq (PM.index × PN.index)
    (tensorProductProductToIteratedMap PM PN).comp
        (tensorProductIteratedToProductMap PM PN) =
      LinearMap.id := by
  letI : Preorder PM.index := PM.indexPreorder
  letI : Nonempty PM.index := PM.indexNonempty
  letI : IsDirectedOrder PM.index := PM.indexDirected
  letI : Preorder PN.index := PN.indexPreorder
  letI : Nonempty PN.index := PN.indexNonempty
  letI : IsDirectedOrder PN.index := PN.indexDirected
  letI : DecidableEq PM.index := Classical.decEq PM.index
  letI : DecidableEq PN.index := Classical.decEq PN.index
  letI : DecidableEq (PM.index × PN.index) := Classical.decEq (PM.index × PN.index)
  -- Extensionality reduces the outer direct limit, then the inner direct limit, to their
  -- canonical generators.
  apply Module.DirectLimit.hom_ext
  intro i
  apply Module.DirectLimit.hom_ext
  intro j
  ext x
  simp [LinearMap.comp_apply, tensorProductIteratedToProductMap_of_of,
    tensorProductProductToIteratedMap_of]

/-- Helper for Chap10 Lemma 10 88 9: the reverse map followed by the forward map is the identity
on the product-index direct limit. -/
private lemma tensorProductIteratedToProductMap_comp_productToIteratedMap
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Nonempty PM.index := PM.indexNonempty
    letI : IsDirectedOrder PM.index := PM.indexDirected
    letI : Preorder PN.index := PN.indexPreorder
    letI : Nonempty PN.index := PN.indexNonempty
    letI : IsDirectedOrder PN.index := PN.indexDirected
    letI : DecidableEq PM.index := Classical.decEq PM.index
    letI : DecidableEq PN.index := Classical.decEq PN.index
    letI : DecidableEq (PM.index × PN.index) := Classical.decEq (PM.index × PN.index)
    (tensorProductIteratedToProductMap PM PN).comp
        (tensorProductProductToIteratedMap PM PN) =
      LinearMap.id := by
  letI : Preorder PM.index := PM.indexPreorder
  letI : Nonempty PM.index := PM.indexNonempty
  letI : IsDirectedOrder PM.index := PM.indexDirected
  letI : Preorder PN.index := PN.indexPreorder
  letI : Nonempty PN.index := PN.indexNonempty
  letI : IsDirectedOrder PN.index := PN.indexDirected
  letI : DecidableEq PM.index := Classical.decEq PM.index
  letI : DecidableEq PN.index := Classical.decEq PN.index
  letI : DecidableEq (PM.index × PN.index) := Classical.decEq (PM.index × PN.index)
  -- Extensionality on product-index generators makes the two generator formulas cancel.
  apply Module.DirectLimit.hom_ext
  intro p
  ext x
  simp [LinearMap.comp_apply, tensorProductProductToIteratedMap_of,
    tensorProductIteratedToProductMap_of_of]

/-- Helper for Chap10 Lemma 10 88 9: the product-index direct limit is the same as the iterated
direct limit. -/
private noncomputable def tensorProductProductIteratedLinearEquiv
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Nonempty PM.index := PM.indexNonempty
    letI : IsDirectedOrder PM.index := PM.indexDirected
    letI : Preorder PN.index := PN.indexPreorder
    letI : Nonempty PN.index := PN.indexNonempty
    letI : IsDirectedOrder PN.index := PN.indexDirected
    letI : DecidableEq PM.index := Classical.decEq PM.index
    letI : DecidableEq PN.index := Classical.decEq PN.index
    letI : DecidableEq (PM.index × PN.index) := Classical.decEq (PM.index × PN.index)
    tensorProductPresentationDirectLimit PM PN ≃ₗ[R]
      tensorProductIteratedDirectLimit PM PN :=
  letI : Preorder PM.index := PM.indexPreorder
  letI : Nonempty PM.index := PM.indexNonempty
  letI : IsDirectedOrder PM.index := PM.indexDirected
  letI : Preorder PN.index := PN.indexPreorder
  letI : Nonempty PN.index := PN.indexNonempty
  letI : IsDirectedOrder PN.index := PN.indexDirected
  letI : DecidableEq PM.index := Classical.decEq PM.index
  letI : DecidableEq PN.index := Classical.decEq PN.index
  letI : DecidableEq (PM.index × PN.index) := Classical.decEq (PM.index × PN.index)
  LinearEquiv.ofLinear (tensorProductProductToIteratedMap PM PN)
    (tensorProductIteratedToProductMap PM PN)
    (tensorProductProductToIteratedMap_comp_iteratedToProductMap PM PN)
    (tensorProductIteratedToProductMap_comp_productToIteratedMap PM PN)

/-- Helper for Chap10 Lemma 10 88 9: after commuting the inner direct limit past tensor product,
left transitions match right tensoring by the left presentation maps. -/
private lemma tensorProductIteratedStageTensorLinearEquiv_compat
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Preorder PN.index := PN.indexPreorder
    letI : DecidableEq PN.index := Classical.decEq PN.index
    ∀ (i k : PM.index) (hik : i ≤ k),
      ((TensorProduct.directLimitRight
          (fun j l h ↦ presentationStageMap PN j l h) (PM.diagram.obj k)).symm :
          tensorProductIteratedStage PM PN k →ₗ[R]
            PM.diagram.obj k ⊗[R]
              Module.DirectLimit (fun j : PN.index ↦ PN.diagram.obj j)
                (fun j l h ↦ presentationStageMap PN j l h)).comp
          (tensorProductIteratedStageMap PM PN i k hik) =
        ((presentationStageMap PM i k hik).rTensor
          (Module.DirectLimit (fun j : PN.index ↦ PN.diagram.obj j)
            (fun j l h ↦ presentationStageMap PN j l h))).comp
          ((TensorProduct.directLimitRight
            (fun j l h ↦ presentationStageMap PN j l h) (PM.diagram.obj i)).symm :
            tensorProductIteratedStage PM PN i →ₗ[R]
              PM.diagram.obj i ⊗[R]
                Module.DirectLimit (fun j : PN.index ↦ PN.diagram.obj j)
                  (fun j l h ↦ presentationStageMap PN j l h)) := by
  letI : Preorder PM.index := PM.indexPreorder
  letI : Preorder PN.index := PN.indexPreorder
  letI : DecidableEq PN.index := Classical.decEq PN.index
  intro i k hik
  -- Check compatibility on inner direct-limit generators, then on pure tensors.
  apply Module.DirectLimit.hom_ext
  intro j
  ext a b
  simp [LinearMap.comp_apply, tensorProductIteratedStageMap, Module.DirectLimit.map_apply_of]

/-- Helper for Chap10 Lemma 10 88 9: the iterated direct limit is the tensor product of the two
presentation direct limits. -/
private noncomputable def tensorProductIteratedTensorLinearEquiv
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Nonempty PM.index := PM.indexNonempty
    letI : IsDirectedOrder PM.index := PM.indexDirected
    letI : Preorder PN.index := PN.indexPreorder
    letI : Nonempty PN.index := PN.indexNonempty
    letI : IsDirectedOrder PN.index := PN.indexDirected
    letI : DecidableEq PM.index := Classical.decEq PM.index
    letI : DecidableEq PN.index := Classical.decEq PN.index
    tensorProductIteratedDirectLimit PM PN ≃ₗ[R] M ⊗[R] N :=
  letI : Preorder PM.index := PM.indexPreorder
  letI : Nonempty PM.index := PM.indexNonempty
  letI : IsDirectedOrder PM.index := PM.indexDirected
  letI : Preorder PN.index := PN.indexPreorder
  letI : Nonempty PN.index := PN.indexNonempty
  letI : IsDirectedOrder PN.index := PN.indexDirected
  letI : DecidableEq PM.index := Classical.decEq PM.index
  letI : DecidableEq PN.index := Classical.decEq PN.index
  (Module.DirectLimit.congr
    (fun i ↦
      (TensorProduct.directLimitRight
        (fun j k h ↦ presentationStageMap PN j k h) (PM.diagram.obj i)).symm)
    (tensorProductIteratedStageTensorLinearEquiv_compat PM PN)).trans
    (((TensorProduct.directLimitLeft
      (fun i k h ↦ presentationStageMap PM i k h)
      (Module.DirectLimit (fun j : PN.index ↦ PN.diagram.obj j)
        (fun j k h ↦ presentationStageMap PN j k h))).symm).trans
      (TensorProduct.congr (presentationDirectLimitLinearEquiv PM)
        (presentationDirectLimitLinearEquiv PN)))

/-- Helper for Chap10 Lemma 10 88 9: the explicit tensor presentation diagram attached to two
Mittag-Leffler presentations. -/
private abbrev tensorProductPresentationDiagram
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Preorder PN.index := PN.indexPreorder
    letI : Category (PM.index × PN.index) := Preorder.smallCategory (PM.index × PN.index)
    PM.index × PN.index ⥤ ModuleCat R :=
  letI : Preorder PM.index := PM.indexPreorder
  letI : Preorder PN.index := PN.indexPreorder
  letI : Category (PM.index × PN.index) := Preorder.smallCategory (PM.index × PN.index)
  ModuleCat.directLimitDiagram (tensorProductPresentationStage PM PN)
    (fun p q hpq ↦ tensorProductPresentationStageMap PM PN p q hpq)

/-- Helper for Chap10 Lemma 10 88 9: stages of the tensor presentation are finitely presented. -/
private lemma tensorProductPresentationStage_finitePresentation
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Nonempty PM.index := PM.indexNonempty
    letI : IsDirectedOrder PM.index := PM.indexDirected
    letI : Preorder PN.index := PN.indexPreorder
    letI : Nonempty PN.index := PN.indexNonempty
    letI : IsDirectedOrder PN.index := PN.indexDirected
    ∀ p, Module.FinitePresentation R (tensorProductPresentationStage PM PN p) := by
  letI : Preorder PM.index := PM.indexPreorder
  letI : Nonempty PM.index := PM.indexNonempty
  letI : IsDirectedOrder PM.index := PM.indexDirected
  letI : Preorder PN.index := PN.indexPreorder
  letI : Nonempty PN.index := PN.indexNonempty
  letI : IsDirectedOrder PN.index := PN.indexDirected
  intro p
  -- Each component stage is finitely presented, and Lemma `10.12.14` preserves finite
  -- presentation under tensor products.
  have hPM : Module.FinitePresentation R (PM.diagram.obj p.1) :=
    PM.presentation_isMittagLeffler.1 p.1
  have hPN : Module.FinitePresentation R (PN.diagram.obj p.2) :=
    PN.presentation_isMittagLeffler.1 p.2
  letI : Module.FinitePresentation R (PM.diagram.obj p.1) := hPM
  letI : Module.FinitePresentation R (PN.diagram.obj p.2) := hPN
  exact inferInstance

/-- Helper for Chap10 Lemma 10 88 9: tensor maps respect componentwise factorizations. -/
private lemma tensorProduct_map_eq_comp_of_eq_comp
    {A : Type v} {B : Type v} {C : Type v}
    {D : Type w} {E : Type w} {F : Type w}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    [AddCommGroup D] [Module R D] [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F]
    {fAC : A →ₗ[R] C} {fAB : A →ₗ[R] B} {fBC : B →ₗ[R] C}
    {gDF : D →ₗ[R] F} {gDE : D →ₗ[R] E} {gEF : E →ₗ[R] F}
    (hf : fAC = fBC.comp fAB) (hg : gDF = gEF.comp gDE) :
    TensorProduct.map fAC gDF =
      (TensorProduct.map fBC gEF).comp (TensorProduct.map fAB gDE) := by
  -- Check the equality on pure tensors, where it is just the two component factorizations.
  ext a d
  simp [hf, hg]

/-- Helper for Chap10 Lemma 10 88 9: component eventual factorizations combine to an eventual
factorization of the product-index tensor presentation. -/
private lemma tensorProductPresentation_tailFactorization
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Nonempty PM.index := PM.indexNonempty
    letI : IsDirectedOrder PM.index := PM.indexDirected
    letI : Preorder PN.index := PN.indexPreorder
    letI : Nonempty PN.index := PN.indexNonempty
    letI : IsDirectedOrder PN.index := PN.indexDirected
    letI : Category (PM.index × PN.index) := Preorder.smallCategory (PM.index × PN.index)
    ∀ p : PM.index × PN.index, ∃ q : PM.index × PN.index, ∃ hpq : p ≤ q,
      ∀ r : PM.index × PN.index, ∀ hpr : p ≤ r,
        ∃ h : (tensorProductPresentationDiagram PM PN).obj r ⟶
            (tensorProductPresentationDiagram PM PN).obj q,
          (tensorProductPresentationDiagram PM PN).map (homOfLE hpq) =
            (tensorProductPresentationDiagram PM PN).map (homOfLE hpr) ≫ h := by
  letI : Preorder PM.index := PM.indexPreorder
  letI : Nonempty PM.index := PM.indexNonempty
  letI : IsDirectedOrder PM.index := PM.indexDirected
  letI : Preorder PN.index := PN.indexPreorder
  letI : Nonempty PN.index := PN.indexNonempty
  letI : IsDirectedOrder PN.index := PN.indexDirected
  letI : Category (PM.index × PN.index) := Preorder.smallCategory (PM.index × PN.index)
  intro p
  -- Choose the eventual factorization stage in each component presentation.
  obtain ⟨jM, hpjM, hMtail⟩ := presentation_exists_tail_factorization (R := R) PM p.1
  obtain ⟨jN, hpjN, hNtail⟩ := presentation_exists_tail_factorization (R := R) PN p.2
  refine ⟨(jM, jN), ⟨hpjM, hpjN⟩, ?_⟩
  intro r hpr
  obtain ⟨a, ha⟩ := hMtail r.1 hpr.1
  obtain ⟨b, hb⟩ := hNtail r.2 hpr.2
  refine ⟨ModuleCat.ofHom (TensorProduct.map a.hom b.hom), ?_⟩
  -- Convert the two categorical component factorizations into linear-map factorizations.
  have haLin :
      presentationStageMap PM p.1 jM hpjM =
        a.hom.comp (presentationStageMap PM p.1 r.1 hpr.1) := by
    simpa [presentationStageMap] using congrArg ModuleCat.Hom.hom ha
  have hbLin :
      presentationStageMap PN p.2 jN hpjN =
        b.hom.comp (presentationStageMap PN p.2 r.2 hpr.2) := by
    simpa [presentationStageMap] using congrArg ModuleCat.Hom.hom hb
  have hlin := tensorProduct_map_eq_comp_of_eq_comp (R := R) haLin hbLin
  -- Repackage the linear tensor factorization as a morphism equality in `ModuleCat`.
  simpa [tensorProductPresentationDiagram, ModuleCat.directLimitDiagram_map,
      ModuleCat.ofHom_comp, tensorProductPresentationStageMap]
    using congrArg ModuleCat.ofHom hlin

/-- Helper for Chap10 Lemma 10 88 9: the product-index tensor presentation has colimit
`M ⊗[R] N`. -/
private lemma tensorProductPresentation_colimitIso
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Preorder PN.index := PN.indexPreorder
    letI : Category (PM.index × PN.index) := Preorder.smallCategory (PM.index × PN.index)
    Nonempty (colimit (tensorProductPresentationDiagram PM PN) ≅
      ModuleCat.of R (M ⊗[R] N)) := by
  letI : Preorder PM.index := PM.indexPreorder
  letI : Nonempty PM.index := PM.indexNonempty
  letI : IsDirectedOrder PM.index := PM.indexDirected
  letI : Preorder PN.index := PN.indexPreorder
  letI : Nonempty PN.index := PN.indexNonempty
  letI : IsDirectedOrder PN.index := PN.indexDirected
  letI : Category (PM.index × PN.index) := Preorder.smallCategory (PM.index × PN.index)
  letI : DecidableEq PM.index := Classical.decEq PM.index
  letI : DecidableEq PN.index := Classical.decEq PN.index
  letI : DecidableEq (PM.index × PN.index) := Classical.decEq (PM.index × PN.index)
  -- First identify the categorical colimit with the quotient-model direct limit, then use the
  -- product-to-iterated comparison and the tensor/direct-limit equivalence.
  exact ⟨module_system_colimit_iso_moduleDirectLimit (tensorProductPresentationDiagram PM PN) ≪≫
    LinearEquiv.toModuleIso
      ((tensorProductProductIteratedLinearEquiv PM PN).trans
        (tensorProductIteratedTensorLinearEquiv PM PN))⟩

/-- Helper for Chap10 Lemma 10 88 9: the explicit tensor presentation is a
Mittag-Leffler directed system. -/
private lemma tensorProductPresentation_isMittagLefflerDirectedSystem
    (PM : MittagLefflerPresentation R M) (PN : MittagLefflerPresentation R N) :
    letI : Preorder PM.index := PM.indexPreorder
    letI : Nonempty PM.index := PM.indexNonempty
    letI : IsDirectedOrder PM.index := PM.indexDirected
    letI : Preorder PN.index := PN.indexPreorder
    letI : Nonempty PN.index := PN.indexNonempty
    letI : IsDirectedOrder PN.index := PN.indexDirected
    letI : Category (PM.index × PN.index) := Preorder.smallCategory (PM.index × PN.index)
    letI : IsDirectedOrder (PM.index × PN.index) := instIsDirectedOrderProd
    IsMittagLefflerDirectedSystem (tensorProductPresentationDiagram PM PN) := by
  letI : Preorder PM.index := PM.indexPreorder
  letI : Nonempty PM.index := PM.indexNonempty
  letI : IsDirectedOrder PM.index := PM.indexDirected
  letI : Preorder PN.index := PN.indexPreorder
  letI : Nonempty PN.index := PN.indexNonempty
  letI : IsDirectedOrder PN.index := PN.indexDirected
  letI : Category (PM.index × PN.index) := Preorder.smallCategory (PM.index × PN.index)
  letI : IsDirectedOrder (PM.index × PN.index) := instIsDirectedOrderProd
  refine ⟨tensorProductPresentationStage_finitePresentation PM PN, ?_⟩
  rcases tensorProductPresentation_colimitIso PM PN with ⟨c⟩
  -- Proposition `10.88.6` turns the tail-factorization clause into the Hom Mittag-Leffler field.
  exact ((directed_colimit_presentation_mittag_leffler_tfae
    (tensorProductPresentationDiagram PM PN)
    (tensorProductPresentationStage_finitePresentation PM PN) c).out 2 3).mp
      (tensorProductPresentation_tailFactorization PM PN)

/- Source/core/bridge triage:
* source-facing: the tensor-product stability statement from Lemma `10.88.9`.
* core/canonical: the chapter owner `Module.MittagLeffler` from `Definition_10_88_7`.
* bridge/view: none; the theorem is a derived closure property of the owner abstraction.
-/
-- Proof sketch: choose directed colimit presentations of `M` and `N` by finitely presented
-- modules with eventual factorization of transition maps, as in Proposition `10.88.6`. The
-- tensor-product presentation indexed by pairs `(i, j)` has finitely presented stages by Lemma
-- `10.12.14`, and the tensor products of the eventual factorization maps give the same eventual
-- factorization property for the tensor-product system. Therefore `M ⊗[R] N` is Mittag-Leffler.
/-- Chap10 Lemma 10 88 9: if `M` and `N` are Mittag-Leffler modules over `R`, then
`M ⊗[R] N` is a Mittag-Leffler `R`-module. -/
@[stacks 05CN]
theorem mittagLeffler_tensorProduct_of_mittagLeffler
    (hM : MittagLeffler R M) (hN : MittagLeffler R N) :
    MittagLeffler R (M ⊗[R] N) := by
  classical
  rcases hM.exists_presentation with ⟨PM⟩
  rcases hN.exists_presentation with ⟨PN⟩
  letI : Preorder PM.index := PM.indexPreorder
  letI : Nonempty PM.index := PM.indexNonempty
  letI : IsDirectedOrder PM.index := PM.indexDirected
  letI : Preorder PN.index := PN.indexPreorder
  letI : Nonempty PN.index := PN.indexNonempty
  letI : IsDirectedOrder PN.index := PN.indexDirected
  letI : Category (PM.index × PN.index) := Preorder.smallCategory (PM.index × PN.index)
  letI : IsDirectedOrder (PM.index × PN.index) := instIsDirectedOrderProd
  -- Package the product-index tensor presentation; the helper lemmas supply the stagewise
  -- finite-presentation, Hom Mittag-Leffler, and colimit fields.
  refine ⟨⟨{
    index := PM.index × PN.index
    indexPreorder := inferInstance
    indexNonempty := inferInstance
    indexDirected := inferInstance
    diagram := tensorProductPresentationDiagram PM PN
    presentation_isMittagLeffler := tensorProductPresentation_isMittagLefflerDirectedSystem PM PN
    colimitIso := tensorProductPresentation_colimitIso PM PN
  }⟩⟩

end

end Module
