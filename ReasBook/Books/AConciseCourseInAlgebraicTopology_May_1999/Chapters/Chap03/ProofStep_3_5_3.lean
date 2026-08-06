import Mathlib.CategoryTheory.Types.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_3_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Lemma_3_4_11
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Remark_3_3_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory

namespace CategoryTheory.Functor.IsCovering

variable {X : Type u₁} {E : Type u₂} {B : Type u₃}
variable [Groupoid.{v₁} X] [Groupoid.{v₂} E] [Groupoid.{v₃} B]

/-- Helper for ProofStep 3.5.3: a fiber translation from a general fiber point can be normalized
to the literal basepoint `⟨e, rfl⟩` by precomposing with the equality witness. -/
private theorem fiberTranslationMap_normalize_basepoint {p : E ⥤ B} (hp : Functor.IsCovering p)
    {e : E} {b b' : B} (h : p.obj e = b) (γ : b ⟶ b') :
    fiberTranslationMap hp γ ⟨e, h⟩ =
      fiberTranslationMap hp (eqToHom h ≫ γ) ⟨e, rfl⟩ := by
  calc
    fiberTranslationMap hp γ ⟨e, h⟩ =
        fiberTranslationMap hp γ (fiberTranslationMap hp (eqToHom h) ⟨e, rfl⟩) := by
      rw [fiberTranslationMap_eqToHom_basepoint hp h]
    _ = fiberTranslationMap hp (eqToHom h ≫ γ) ⟨e, rfl⟩ := by
      exact congrArg (fun m ↦ m (⟨e, rfl⟩ : p.Fiber (p.obj e)))
        (fiberTranslationMap_comp hp (eqToHom h) γ).symm

/-- Helper for ProofStep 3.5.3: any loop whose class lies in the transported image subgroup fixes
the chosen fiber point under fiber translation. -/
private theorem fiberTranslationMap_eq_self_of_mem_transport_range {p : E ⥤ B}
    (hp : Functor.IsCovering p)
    {e : E} {b : B} (h : p.obj e = b) (δ : b ⟶ b)
    (hδ : δ ∈ h ▸ (Functor.mapVertexGroup p e).range) :
    fiberTranslationMap hp δ ⟨e, h⟩ = ⟨e, h⟩ := by
  -- First move the subgroup-membership statement to the literal basepoint `⟨e, rfl⟩`.
  have hδ' : eqToHom h ≫ δ ≫ eqToHom h.symm ∈ (Functor.mapVertexGroup p e).range := by
    exact (mapVertexGroup_range_transport_iff h δ).1 hδ
  have hbase :
      fiberTranslationMap hp (eqToHom h ≫ δ ≫ eqToHom h.symm) ⟨e, rfl⟩ = ⟨e, rfl⟩ := by
    exact (mem_mapVertexGroup_range_iff_fiberTranslationMap_basepoint_eq hp e
      (eqToHom h ≫ δ ≫ eqToHom h.symm)).mp hδ'
  -- Then transport that fixed-point statement back along the equality witness.
  calc
    fiberTranslationMap hp δ ⟨e, h⟩ =
        fiberTranslationMap hp (eqToHom h ≫ δ) ⟨e, rfl⟩ := by
      simpa using fiberTranslationMap_normalize_basepoint hp h δ
    _ = fiberTranslationMap hp
          ((eqToHom h ≫ δ ≫ eqToHom h.symm) ≫ eqToHom h) ⟨e, rfl⟩ := by
      simp [Category.assoc]
    _ = fiberTranslationMap hp (eqToHom h)
          (fiberTranslationMap hp (eqToHom h ≫ δ ≫ eqToHom h.symm) ⟨e, rfl⟩) := by
      rw [fiberTranslationMap_comp]
      rfl
    _ = fiberTranslationMap hp (eqToHom h) ⟨e, rfl⟩ := by
      rw [hbase]
    _ = ⟨e, h⟩ := by
      simpa using fiberTranslationMap_eqToHom_basepoint hp h

/-- ProofStep 3.5.3: under the subgroup condition from Theorem 3.5.1, the candidate value
`fiberTranslationMap hp (f.map α) e₀` used to define the lifted functor at an object `x` is
independent of the chosen morphism `α : x₀ ⟶ x`. -/
-- Proof sketch: the loop `α₂ * α₁⁻¹` at `x₀` maps under `f` to
-- `f.map α₂ * (f.map α₁)⁻¹`. The subgroup inclusion hypothesis puts this loop in the image of
-- `π(E, e₀.1)` under `p`, so the fixed-point lemma
-- `fiberTranslationMap_eq_self_of_mem_transport_range` shows that this loop fixes `e₀`.
-- Composing with the lift of `f.map α₁` then identifies the endpoints of the lifts of
-- `f.map α₁` and `f.map α₂`.
theorem fiberTranslationMap_eq_of_mapVertexGroup_range_le {p : E ⥤ B}
    (hp : Functor.IsCovering p) {f : X ⥤ B} (x₀ : X) (e₀ : p.Fiber (f.obj x₀))
    (hsub : (Functor.mapVertexGroup f x₀).range ≤
      e₀.2 ▸ (Functor.mapVertexGroup p e₀.1).range)
    {x : X} (α₁ α₂ : x₀ ⟶ x) :
    fiberTranslationMap hp (f.map α₁) e₀ = fiberTranslationMap hp (f.map α₂) e₀ := by
  symm
  -- Compare the two candidate lifts by the loop based at `x₀` obtained from `α₂` and `α₁`.
  have hloop :
      f.map (α₂ ≫ CategoryTheory.Groupoid.inv α₁) ∈
        e₀.2 ▸ (Functor.mapVertexGroup p e₀.1).range := by
    apply hsub
    refine ⟨α₂ ≫ CategoryTheory.Groupoid.inv α₁, ?_⟩
    simp [Functor.map_comp]
  -- The subgroup condition forces that comparison loop to fix the chosen basepoint in the fiber.
  have hfix :
      fiberTranslationMap hp (f.map (α₂ ≫ CategoryTheory.Groupoid.inv α₁)) e₀ = e₀ := by
    exact fiberTranslationMap_eq_self_of_mem_transport_range hp e₀.2
      (f.map (α₂ ≫ CategoryTheory.Groupoid.inv α₁)) hloop
  -- Rewrite the lift along `α₂` as the comparison loop followed by the lift along `α₁`.
  calc
    fiberTranslationMap hp (f.map α₂) e₀ =
        fiberTranslationMap hp (f.map ((α₂ ≫ CategoryTheory.Groupoid.inv α₁) ≫ α₁)) e₀ := by
      simp
    _ = fiberTranslationMap hp (f.map α₁)
          (fiberTranslationMap hp (f.map (α₂ ≫ CategoryTheory.Groupoid.inv α₁)) e₀) := by
      simpa [Functor.map_comp] using
        congrArg (fun m ↦ m e₀)
          (fiberTranslationMap_comp hp
            (f.map (α₂ ≫ CategoryTheory.Groupoid.inv α₁)) (f.map α₁))
    _ = fiberTranslationMap hp (f.map α₁) e₀ := by
      rw [hfix]

end CategoryTheory.Functor.IsCovering
