import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Definition_1_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_2_1

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

noncomputable section

universe u

variable {A X : Type u} [TopologicalSpace A] [TopologicalSpace X]

-- Semantic recall note: `lean_leansearch` was temporarily unavailable (HTTP 429), so this item
-- follows the verified local `IsCofibration`/`mappingCylinder` API from Definitions 6.1.4 and
-- 6.2.1.

namespace ContinuousMap

/-- The canonical map `A × I ⟶ X × I` induced by a map `i : A ⟶ X`. -/
def mappingCylinderCylinderMap (i : C(A, X)) : C(A × I, X × I) :=
  (i.comp ContinuousMap.fst).prodMk ContinuousMap.snd

@[simp] theorem mappingCylinderCylinderMap_apply (i : C(A, X)) (a : A) (t : I) :
    mappingCylinderCylinderMap i (a, t) = (i a, t) :=
  rfl

/-- Helper for Construction 6.2.2: the HEP test data satisfies the compatibility relation needed
to descend a map from the mapping cylinder pushout. -/
private theorem mappingCylinderDesc_condition {i : C(A, X)} {Y : Type u} [TopologicalSpace Y]
    (f₀ : C(X, Y)) {g : C(A, Y)} (H : (f₀.comp i).Homotopy g) :
    TopCat.ofHom i ≫ TopCat.ofHom f₀ =
      TopCat.ofHom (mappingCylinderTimeZeroInclusion A) ≫
        TopCat.ofHom H.prodSwap := by
  -- Reduce the pushout compatibility to pointwise equality of the two continuous maps out of `A`.
  have hComp : f₀.comp i = H.prodSwap.comp (mappingCylinderTimeZeroInclusion A) := by
    ext a
    simp [mappingCylinderTimeZeroInclusion, ContinuousMap.comp_apply]
  simpa using congrArg TopCat.ofHom hComp

/-- The universal map `M_i ⟶ Y` induced by an HEP test diagram
`f₀ : X ⟶ Y`, `H : (f₀ ∘ i) ≃ g`. -/
def mappingCylinderDesc {i : C(A, X)} {Y : Type u} [TopologicalSpace Y]
    (f₀ : C(X, Y)) {g : C(A, Y)} (H : (f₀.comp i).Homotopy g) : C(i.mappingCylinder, Y) :=
  (pushout.desc (TopCat.ofHom f₀)
    (TopCat.ofHom H.prodSwap)
    (mappingCylinderDesc_condition f₀ H)).hom

/-- The universal map induced by an HEP test diagram restricts on `X` to the chosen map
`f₀ : X ⟶ Y`. -/
theorem mappingCylinderDesc_comp_targetInclusion {i : C(A, X)} {Y : Type u}
    [TopologicalSpace Y] (f₀ : C(X, Y)) {g : C(A, Y)} (H : (f₀.comp i).Homotopy g) :
    (mappingCylinderDesc f₀ H).comp (mappingCylinderTargetInclusion i) = f₀ := by
  -- Read the descended map on the target side via the pushout computation rule.
  simpa [mappingCylinderDesc, mappingCylinderTargetInclusion] using
    congrArg TopCat.Hom.hom
      (pushout.inl_desc
        (TopCat.ofHom f₀)
        (TopCat.ofHom H.prodSwap)
        (mappingCylinderDesc_condition f₀ H))

/-- The universal map induced by an HEP test diagram restricts on `A × I` to the given homotopy,
viewed as the textbook-order map `H.prodSwap : A × I ⟶ Y`. -/
theorem mappingCylinderDesc_comp_cylinderInclusion {i : C(A, X)} {Y : Type u}
    [TopologicalSpace Y] (f₀ : C(X, Y)) {g : C(A, Y)} (H : (f₀.comp i).Homotopy g) :
    (mappingCylinderDesc f₀ H).comp (mappingCylinderCylinderInclusion i) =
      H.prodSwap := by
  -- Read the descended map on the cylinder side via the complementary pushout computation rule.
  simpa [mappingCylinderDesc, mappingCylinderCylinderInclusion] using
    congrArg TopCat.Hom.hom
      (pushout.inr_desc
        (TopCat.ofHom f₀)
        (TopCat.ofHom H.prodSwap)
        (mappingCylinderDesc_condition f₀ H))

/-- Construction 6.2.2. If there is a retraction-like map `r : X × I → M_i` whose restriction to
`X × {0}` is the target inclusion `X ⟶ M_i` and whose restriction along the canonical cylinder map
`mappingCylinderCylinderMap i = i × id_I` is the cylinder inclusion `A × I ⟶ M_i`, then `i`
passes every HEP test diagram, i.e. `i` is a cofibration. -/
theorem isCofibration_of_mappingCylinderRetract {i : C(A, X)} (r : C(X × I, i.mappingCylinder))
    (hX :
      r.comp (mappingCylinderTimeZeroInclusion X) = mappingCylinderTargetInclusion i)
    (hA :
      r.comp (mappingCylinderCylinderMap i) = mappingCylinderCylinderInclusion i) :
    IsCofibration.{u, u, u} i := by
  intro Y _ f₀ g H
  let E : C(i.mappingCylinder, Y) := mappingCylinderDesc f₀ H
  have hEtarget : E.comp (mappingCylinderTargetInclusion i) = f₀ := by
    simpa [E] using mappingCylinderDesc_comp_targetInclusion (f₀ := f₀) (H := H)
  have hEcylinder : E.comp (mappingCylinderCylinderInclusion i) = H.prodSwap := by
    simpa [E] using mappingCylinderDesc_comp_cylinderInclusion (f₀ := f₀) (H := H)
  let G : C(X, Y) :=
    (E.comp r).comp ((ContinuousMap.id X).prodMk (ContinuousMap.const X (1 : I)))
  -- Route correction: construct the extension through the descended map `E : M_i ⟶ Y`, then
  -- package `E.comp r : X × I ⟶ Y` as a homotopy by checking only its two endpoint slices.
  have hZero : ∀ x : X, (E.comp r) (x, 0) = f₀ x := by
    intro x
    -- Evaluate the retract hypothesis on `X × {0}` before rewriting through the target
    -- restriction of `E`.
    have hx0 := congrArg (fun f : C(X, i.mappingCylinder) => f x) hX
    have hx : r (x, 0) = (mappingCylinderTargetInclusion i) x := by
      simpa [mappingCylinderTimeZeroInclusion, ContinuousMap.comp_apply] using hx0
    calc
      (E.comp r) (x, 0) = E (r (x, 0)) := rfl
      _ = E ((mappingCylinderTargetInclusion i) x) := by rw [hx]
      _ = (E.comp (mappingCylinderTargetInclusion i)) x := rfl
      _ = f₀ x := by rw [hEtarget]
  have hOne : ∀ x : X, (E.comp r) (x, 1) = G x := by
    intro x
    -- The endpoint map `G` is defined as the time-`1` slice of `E.comp r`.
    simp [G, ContinuousMap.comp_apply]
  let F : f₀.Homotopy G := ContinuousMap.Homotopy.ofProdSwap (E.comp r) hZero hOne
  refine ⟨G, F, ?_⟩
  rintro ⟨t, a⟩
  -- Evaluate the retract hypothesis on `A × I` and rewrite through the cylinder restriction of `E`.
  have ha0 := congrArg (fun f : C(A × I, i.mappingCylinder) => f (a, t)) hA
  have ha : r (i a, t) = (mappingCylinderCylinderInclusion i) (a, t) := by
    simpa [ContinuousMap.comp_apply] using ha0
  calc
    F (t, i a) = (E.comp r) (i a, t) := by
      simp [F]
    _ = E (r (i a, t)) := rfl
    _ = E ((mappingCylinderCylinderInclusion i) (a, t)) := by rw [ha]
    _ = (E.comp (mappingCylinderCylinderInclusion i)) (a, t) := rfl
    _ = H.prodSwap (a, t) := by rw [hEcylinder]
    _ = H (t, a) := by simp

end ContinuousMap
