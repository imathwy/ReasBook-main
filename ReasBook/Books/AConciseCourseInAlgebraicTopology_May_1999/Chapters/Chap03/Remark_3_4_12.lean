import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Lemma_3_3_12
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Lemma_3_4_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory

namespace CategoryTheory.Functor.IsCovering

variable {E : Type u₁} {B : Type u₂} [Groupoid.{v₁} E] [Groupoid.{v₂} B]
variable {p : E ⥤ B}

/-- The distinguished point of the fiber over `p.obj e` coming from `e`. -/
abbrev fiberTranslationBasepoint (e : E) : p.Fiber (p.obj e) := ⟨e, rfl⟩

/-- The stabilizer of the distinguished fiber point under the canonical fiber-translation action
of `π(B, p.obj e)`. -/
noncomputable abbrev fiberTranslationBasepointStabilizer (hp : Functor.IsCovering p) (e : E) :
    Subgroup (p.obj e ⟶ p.obj e) :=
  @MulAction.stabilizer (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) inferInstance
    (fiberTranslationMulAction hp (p.obj e)) (⟨e, rfl⟩ : p.Fiber (p.obj e))

/-- The distinguished-point stabilizer for fiber translation is exactly the image of the upstairs
vertex group. -/
@[simp] theorem fiberTranslationBasepointStabilizer_eq_mapVertexGroup_range
    (hp : Functor.IsCovering p) (e : E) :
    fiberTranslationBasepointStabilizer hp e = (Functor.mapVertexGroup p e).range := by
  simpa [fiberTranslationBasepointStabilizer, fiberTranslationBasepoint] using
    fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range hp e

/-- The regularity condition is equivalent to normality of the stabilizer of the distinguished
point in the fiber action. -/
-- Proof sketch: rewrite the stabilizer at `⟨e, rfl⟩` as the image of
-- `Functor.mapVertexGroup p e` using
-- `fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range`, then unfold
-- `Functor.IsRegularCovering`.
theorem isRegularCovering_iff_fiberTranslation_basepoint_stabilizer_normal
    (hp : Functor.IsCovering p) (e : E) :
    Functor.IsRegularCovering p e ↔
      (fiberTranslationBasepointStabilizer hp e).Normal := by
  constructor
  · intro hreg
    rw [fiberTranslationBasepointStabilizer_eq_mapVertexGroup_range]
    exact hreg.2
  · intro hnormal
    exact ⟨hp, by
      rw [← fiberTranslationBasepointStabilizer_eq_mapVertexGroup_range]
      exact hnormal⟩

section Connected

variable [IsConnected E]

/-- On a connected total groupoid, universality at `e` is equivalent to freeness of the
fiber-translation action over `p.obj e`. -/
theorem isUniversalCovering_iff_fiberTranslation_isFree
    (hp : Functor.IsCovering p) (e : E) :
    Functor.IsUniversalCovering p e ↔ fiberTranslationMulAction.IsFree hp (p.obj e) := by
  -- Connectedness supplies the pretransitivity required by Lemma 3.3.12.
  exact isUniversalCovering_iff_fiberTranslation_isFree_of_isPretransitive hp e
    (fiberTranslationMulAction_isPretransitive hp (p.obj e))

/-- For a connected total groupoid, universality is equivalent to the fiber translation action
being free and transitive. -/
-- Proof sketch:
-- connectedness supplies transitivity of the whole fiber action, and Lemma 3.3.12 upgrades
-- universality to freeness of the canonical fiber-translation action; pairing these gives the
-- free-transitive description.
theorem isUniversalCovering_iff_fiberTranslation_free_transitive
    (hp : Functor.IsCovering p) (e : E) :
    Functor.IsUniversalCovering p e ↔
      fiberTranslationMulAction.IsFree hp (p.obj e) ∧
        fiberTranslationMulAction.IsTransitive hp (p.obj e) := by
  have htrans : fiberTranslationMulAction.IsTransitive hp (p.obj e) :=
    fiberTranslationMulAction_isTransitive hp (p.obj e)
  -- First collapse universality to the freeness criterion specialized to the connected case.
  rw [isUniversalCovering_iff_fiberTranslation_isFree hp e]
  constructor
  · intro hfree
    -- The transitivity witness is global, so freeness is the only remaining datum.
    exact ⟨hfree, htrans⟩
  · rintro ⟨hfree, htrans⟩
    -- The backward direction only needs the freeness component; transitivity is automatic here.
    exact hfree

/-- Remark 3.4.12, bundled form: regular coverings correspond to normal isotropy subgroups,
while on a connected total groupoid universal coverings correspond to free transitive fiber
actions. -/
theorem regular_and_universal_covering_characterizations
    (hp : Functor.IsCovering p) (e : E) :
    (Functor.IsRegularCovering p e ↔
        (fiberTranslationBasepointStabilizer hp e).Normal) ∧
      (Functor.IsUniversalCovering p e ↔
        fiberTranslationMulAction.IsFree hp (p.obj e) ∧
          fiberTranslationMulAction.IsTransitive hp (p.obj e)) := by
  constructor
  · -- Regularity is exactly normality of the basepoint stabilizer.
    exact isRegularCovering_iff_fiberTranslation_basepoint_stabilizer_normal hp e
  · -- In the connected case, universality is freeness together with transitivity.
    exact isUniversalCovering_iff_fiberTranslation_free_transitive hp e

end Connected

end CategoryTheory.Functor.IsCovering
