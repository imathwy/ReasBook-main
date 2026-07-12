import Mathlib
import StacksProject_2024.Chap14.Lemma_14_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Simplicial
open CategoryTheory.SimplicialObject
open Opposite

/- Domain-style sampling for Lemma 14.19.15:
- primary domain: simplicial-set skeleton/coskeleton adjunctions and coskeletal simplicial sets;
- sampled owner-style declarations:
  `SimplexCategory.Truncated.matchingIndex`,
  `SimplicialObject.IsCoskeletal`,
  `SimplicialObject.isCoskeletal_iff_isIso`,
  `SimplicialObject.isoCoskOfIsCoskeletal`,
  `stdSimplex.isoNerve`;
- best owner abstraction: `SimplicialObject.IsCoskeletal 1`, with the canonical comparison map
  owned by the adjunction unit `(coskAdj 1).unit.app (Δ[n] : SSet)`;
- source/core/bridge triage:
  `source-facing`: the statement that the canonical map `Δ[n] ⟶ cosk₁ sk₁ Δ[n]` is an
  isomorphism;
  `core/canonical`: the owner predicate `(Δ[n] : SSet).IsCoskeletal 1`;
  `bridge/view`: `SimplicialObject.isCoskeletal_iff_isIso`, which converts the owner predicate to
  the source-facing unit-isomorphism statement.

Primitive data are only the standard simplex `Δ[n]`; the comparison morphism is derived from the
adjunction owner. The file should therefore expose the owner-level coskeletality statement and keep
the unit-isomorphism theorem as a thin companion. -/

namespace CategoryTheory.Nerve

open CategoryTheory.Category Limits
open Functor StructuredArrow
open SSet SSet.Truncated
open SimplexCategory.Truncated.Hom
open SimplexCategory SimplexCategory.Truncated
open SimplicialObject.Truncated

universe v u

variable (C : Type u) [Category.{v} C] [Quiver.IsThin C]

namespace Pointwise

private abbrev strArrowMk {i n : ℕ} (φ : ⦋i⦌ ⟶ ⦋n⦌) (hi : i ≤ 1 := by omega) :
    matchingIndex 1 n :=
  ⟨⟨⟨⟩⟩, op (⟨⦋i⦌, hi⟩ : SimplexCategory.Truncated 1), φ.op⟩

private def conePath {n : ℕ}
    (s : Cone (proj (op ⦋n⦌) (SimplexCategory.Truncated.inclusion 1).op ⋙
      (SimplexCategory.Truncated.inclusion 1).op ⋙ nerve C))
    (x : s.pt) : (nerve C).Path n where
  vertex i := s.π.app (strArrowMk (SimplexCategory.const _ _ i)) x
  arrow i := s.π.app (strArrowMk (SimplexCategory.mkOfSucc i)) x
  arrow_src i := by
    let α : strArrowMk (SimplexCategory.mkOfSucc i) ⟶
        strArrowMk (⦋0⦌.const ⦋n⦌ i.castSucc) :=
      StructuredArrow.homMk (tr (SimplexCategory.δ 1)).op
        (Quiver.Hom.unop_inj (by ext j; fin_cases j; rfl))
    simpa using congr_fun (s.w α) x
  arrow_tgt i := by
    let α : strArrowMk (SimplexCategory.mkOfSucc i) ⟶
        strArrowMk (⦋0⦌.const ⦋n⦌ i.succ) :=
      StructuredArrow.homMk (tr (SimplexCategory.δ 0)).op
        (Quiver.Hom.unop_inj (by ext j; fin_cases j; rfl))
    simpa using congr_fun (s.w α) x

private noncomputable def lift {n : ℕ}
    (s : Cone (proj (op ⦋n⦌) (SimplexCategory.Truncated.inclusion 1).op ⋙
      (SimplexCategory.Truncated.inclusion 1).op ⋙ nerve C))
    (x : s.pt) : (nerve C) _⦋n⦌ :=
  (strictSegal C).spineToSimplex (conePath C s x)

omit [Quiver.IsThin C] in
private lemma fac_zero {n : ℕ}
    (s : Cone (proj (op ⦋n⦌) (SimplexCategory.Truncated.inclusion 1).op ⋙
      (SimplexCategory.Truncated.inclusion 1).op ⋙ nerve C))
    (x : s.pt) (i : Fin (n + 1)) :
    (nerve C).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op (lift C s x) =
      s.π.app (strArrowMk (SimplexCategory.const ⦋0⦌ ⦋n⦌ i)) x := by
  simpa [lift, conePath] using (strictSegal C).spineToSimplex_vertex i (conePath C s x)

private lemma fac_one {n : ℕ}
    (s : Cone (proj (op ⦋n⦌) (SimplexCategory.Truncated.inclusion 1).op ⋙
      (SimplexCategory.Truncated.inclusion 1).op ⋙ nerve C))
    (x : s.pt) (φ : ⦋1⦌ ⟶ ⦋n⦌) :
    (nerve C).map φ.op (lift C s x) = s.π.app (strArrowMk φ) x := by
  apply nerve.ext_of_isThin
  ext j
  fin_cases j
  · have hφ : SimplexCategory.δ 1 ≫ φ = SimplexCategory.const ⦋0⦌ ⦋n⦌ (φ.toOrderHom 0) := by
      ext k
      fin_cases k
      rfl
    let α : strArrowMk φ ⟶
        strArrowMk (SimplexCategory.const ⦋0⦌ ⦋n⦌ (φ.toOrderHom 0)) :=
      StructuredArrow.homMk (tr (SimplexCategory.δ 1)).op
        (Quiver.Hom.unop_inj (by ext k; fin_cases k; rfl))
    have hα :
        s.π.app (strArrowMk (SimplexCategory.const ⦋0⦌ ⦋n⦌ (φ.toOrderHom 0))) x =
          (nerve C).map (SimplexCategory.δ 1).op (s.π.app (strArrowMk φ) x) := by
      simpa using (congr_fun (s.w α) x).symm
    have hsrc :
        (nerve C).δ 1 ((nerve C).map φ.op (lift C s x)) =
          (nerve C).δ 1 (s.π.app (strArrowMk φ) x) := by
      rw [SimplicialObject.δ_def, ← FunctorToTypes.map_comp_apply, ← op_comp, hφ]
      rw [fac_zero C s x (φ.toOrderHom 0), hα]
    simpa [nerveEquiv] using congrArg nerveEquiv hsrc
  · have hφ : SimplexCategory.δ 0 ≫ φ = SimplexCategory.const ⦋0⦌ ⦋n⦌ (φ.toOrderHom 1) := by
      ext k
      fin_cases k
      rfl
    let α : strArrowMk φ ⟶
        strArrowMk (SimplexCategory.const ⦋0⦌ ⦋n⦌ (φ.toOrderHom 1)) :=
      StructuredArrow.homMk (tr (SimplexCategory.δ 0)).op
        (Quiver.Hom.unop_inj (by ext k; fin_cases k; rfl))
    have hα :
        s.π.app (strArrowMk (SimplexCategory.const ⦋0⦌ ⦋n⦌ (φ.toOrderHom 1))) x =
          (nerve C).map (SimplexCategory.δ 0).op (s.π.app (strArrowMk φ) x) := by
      simpa using (congr_fun (s.w α) x).symm
    have htgt :
        (nerve C).δ 0 ((nerve C).map φ.op (lift C s x)) =
          (nerve C).δ 0 (s.π.app (strArrowMk φ) x) := by
      rw [SimplicialObject.δ_def, ← FunctorToTypes.map_comp_apply, ← op_comp, hφ]
      rw [fac_zero C s x (φ.toOrderHom 1), hα]
    simpa [nerveEquiv] using congrArg nerveEquiv htgt

end Pointwise

open Pointwise in
private noncomputable def isPointwiseRightKanExtensionAt (n : ℕ) :
    (SSet.Truncated.rightExtensionInclusion (nerve C) 1).IsPointwiseRightKanExtensionAt ⟨⦋n⦌⟩ where
  lift s x := lift C s x
  fac s j := by
    ext x
    obtain ⟨⟨i, hi⟩, ⟨f : _ ⟶ _⟩, rfl⟩ := j.mk_surjective
    obtain ⟨i, rfl⟩ : ∃ m, ⦋m⦌ = i := ⟨_, i.mk_len⟩
    dsimp at hi ⊢
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl
    · have hf : f = SimplexCategory.const ⦋0⦌ ⦋n⦌ (f.toOrderHom 0) := by
        ext k
        fin_cases k
        rfl
      rw [hf]
      simpa using fac_zero C s x (f.toOrderHom 0)
    · simpa using fac_one C s x f
  uniq s m hm := by
    ext x
    apply (strictSegal C).spineInjective
    change (nerve C).spine n (m x) = (nerve C).spine n (lift C s x)
    dsimp [lift, conePath]
    rw [(strictSegal C).spine_spineToSimplex_apply]
    refine SSet.Path.ext ?_ ?_
    · funext i
      exact congr_fun (hm (strArrowMk (SimplexCategory.const ⦋0⦌ ⦋n⦌ i))) x
    · funext i
      exact congr_fun (hm (strArrowMk (SimplexCategory.mkOfSucc i))) x

private noncomputable def isPointwiseRightKanExtension :
    (SSet.Truncated.rightExtensionInclusion (nerve C) 1).IsPointwiseRightKanExtension :=
  fun Δ ↦ isPointwiseRightKanExtensionAt C Δ.unop.len

private theorem isRightKanExtension :
    (nerve C).IsRightKanExtension (𝟙 ((SimplexCategory.Truncated.inclusion 1).op ⋙ nerve C)) :=
  RightExtension.IsPointwiseRightKanExtension.isRightKanExtension
    (isPointwiseRightKanExtension C)

/-- The nerve of a thin category is `1`-coskeletal. -/
instance : SimplicialObject.IsCoskeletal (nerve C) 1 where
  isRightKanExtension := isRightKanExtension C

end CategoryTheory.Nerve

-- Proof sketch: identify maps into `Δ[n]` with monotone maps into `Fin (n + 1)` via Yoneda, show
-- that such maps are determined by their values on vertices and that monotonicity is already forced
-- by the `1`-simplices, and conclude that `Δ[n]` is the right Kan extension of its `1`-truncation.
/-- The standard simplex `Δ[n]` is `1`-coskeletal. -/
theorem stdSimplex_isCoskeletal_one (n : ℕ) :
    (Δ[n] : SSet).IsCoskeletal 1 := by
  rw [SimplicialObject.isCoskeletal_iff]
  let e := SSet.stdSimplex.isoNerve n
  let e₁ := Functor.isoWhiskerLeft (SimplexCategory.Truncated.inclusion 1).op e
  let _ : (nerve (ULift (Fin (n + 1))) : SSet).IsCoskeletal 1 :=
    inferInstance
  exact
    (Functor.isRightKanExtension_iff_of_iso₂
      (𝟙 ((SimplexCategory.Truncated.inclusion 1).op ⋙ (Δ[n] : SSet)))
      (𝟙 ((SimplexCategory.Truncated.inclusion 1).op ⋙ (nerve (ULift (Fin (n + 1))) : SSet)))
      e₁
      e
      (by simp [e₁])).2 inferInstance

/-- Lemma 14.19.15: the canonical map `Δ[n] ⟶ cosk₁ sk₁ Δ[n]` is an isomorphism. Once
`stdSimplex_isCoskeletal_one n` is established, this is the canonical `IsIso` instance for the
unit of `coskAdj 1`. -/
theorem stdSimplex_cosk_unit_isIso (n : ℕ) :
    IsIso ((coskAdj 1).unit.app (Δ[n] : SSet)) := by
  exact (SimplicialObject.isCoskeletal_iff_isIso (Δ[n] : SSet) 1).1
    (stdSimplex_isCoskeletal_one n)
