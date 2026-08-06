import Mathlib.Topology.Category.TopCat.Limits.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Construction_6_2_2

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

noncomputable section

universe u

variable {A X : Type u} [TopologicalSpace A] [TopologicalSpace X]

-- Semantic recall: `lean_leansearch` only surfaced model-categorical homotopy-extension results;
-- the source-faithful Chapter 6 owners here are `IsCofibration` and the pushout model
-- `ContinuousMap.mappingCylinder` from Definition 6.2.1.

namespace ContinuousMap

private theorem mappingCylinderCanonicalMap_comp_eq (i : C(A, X)) :
    (mappingCylinderTimeZeroInclusion X).comp i =
      (mappingCylinderCylinderMap i).comp (mappingCylinderTimeZeroInclusion A) := by
  ext a : 1
  simp [mappingCylinderTimeZeroInclusion, mappingCylinderCylinderMap_apply]

private theorem mappingCylinderCanonicalMap_condition (i : C(A, X)) :
    TopCat.ofHom i ≫ TopCat.ofHom (mappingCylinderTimeZeroInclusion X) =
      TopCat.ofHom (mappingCylinderTimeZeroInclusion A) ≫
        TopCat.ofHom (mappingCylinderCylinderMap i) := by
  simpa using congrArg TopCat.ofHom (mappingCylinderCanonicalMap_comp_eq i)

/-- The canonical map `j : M_i ⟶ X × I` from the mapping cylinder of `i` to the ordinary cylinder
`X × I`. -/
def mappingCylinderCanonicalMap (i : C(A, X)) : C(i.mappingCylinder, X × I) :=
  pushout.desc (TopCat.ofHom (mappingCylinderTimeZeroInclusion X))
    (TopCat.ofHom (mappingCylinderCylinderMap i))
    (mappingCylinderCanonicalMap_condition i) |>.hom

/-- The canonical map `M_i ⟶ X × I` restricts on `X` to the time-`0` inclusion `X ⟶ X × I`. -/
theorem mappingCylinderCanonicalMap_comp_targetInclusion (i : C(A, X)) :
    (mappingCylinderCanonicalMap i).comp (mappingCylinderTargetInclusion i) =
      mappingCylinderTimeZeroInclusion X := by
  simpa [mappingCylinderCanonicalMap, mappingCylinderTargetInclusion] using
    congrArg TopCat.Hom.hom
      (pushout.inl_desc
        (TopCat.ofHom (mappingCylinderTimeZeroInclusion X))
        (TopCat.ofHom (mappingCylinderCylinderMap i))
        (mappingCylinderCanonicalMap_condition i))

/-- The canonical map `M_i ⟶ X × I` restricts on `A × I` to the product map `i × id_I`. -/
theorem mappingCylinderCanonicalMap_comp_cylinderInclusion (i : C(A, X)) :
    (mappingCylinderCanonicalMap i).comp (mappingCylinderCylinderInclusion i) =
      mappingCylinderCylinderMap i := by
  simpa [mappingCylinderCanonicalMap, mappingCylinderCylinderInclusion] using
    congrArg TopCat.Hom.hom
      (pushout.inr_desc
        (TopCat.ofHom (mappingCylinderTimeZeroInclusion X))
        (TopCat.ofHom (mappingCylinderCylinderMap i))
        (mappingCylinderCanonicalMap_condition i))

end ContinuousMap

open scoped ContinuousMap

/-- A retract `r : X × I ⟶ M_i` of the canonical map `j : M_i ⟶ X × I` that agrees with the
standard inclusions of `X × {0}` and `A × I` into the mapping cylinder. -/
class IsMappingCylinderRetract {i : C(A, X)} (r : C(X × I, i.mappingCylinder)) : Prop where
  /-- `r` is a left inverse to the canonical map `j : M_i ⟶ X × I`. -/
  left_inv :
    r.comp (ContinuousMap.mappingCylinderCanonicalMap i) =
      ContinuousMap.id i.mappingCylinder
  /-- `r` restricts on `X × {0}` to the canonical map `X ⟶ M_i`. -/
  endpoint :
    r.comp (ContinuousMap.mappingCylinderTimeZeroInclusion X) =
      ContinuousMap.mappingCylinderTargetInclusion i
  /-- `r` restricts on `A × I` to the canonical map `A × I ⟶ M_i`. -/
  cylinder :
    r.comp (ContinuousMap.mappingCylinderCylinderMap i) =
      ContinuousMap.mappingCylinderCylinderInclusion i

namespace IsMappingCylinderRetract

/-- A mapping-cylinder retract witness gives the HEP criterion of Construction 6.2.2. -/
theorem isCofibration {i : C(A, X)} {r : C(X × I, i.mappingCylinder)}
    (hr : IsMappingCylinderRetract r) :
    IsCofibration.{u, u, u} i :=
  ContinuousMap.isCofibration_of_mappingCylinderRetract r hr.endpoint hr.cylinder

end IsMappingCylinderRetract

/-- Helper for Criterion 6.2.3: the time-`1` slice of the canonical cylinder inclusion
`A × I ⟶ M_i`. -/
private def mappingCylinderCylinderEndpoint (i : C(A, X)) : C(A, i.mappingCylinder) :=
  (ContinuousMap.mappingCylinderCylinderInclusion i).comp
    ((ContinuousMap.id A).prodMk (ContinuousMap.const A (1 : I)))

/-- Helper for Criterion 6.2.3: the time-`0` slice of the cylinder inclusion recovers
`(mappingCylinderTargetInclusion i).comp i`. -/
private theorem mappingCylinderCylinderInclusion_apply_zero (i : C(A, X)) :
    ∀ a : A,
      (ContinuousMap.mappingCylinderCylinderInclusion i) (a, 0) =
        ((ContinuousMap.mappingCylinderTargetInclusion i).comp i) a := by
  intro a
  -- Evaluate the pushout compatibility relation at `a`.
  have ha :=
    congrArg (fun f : C(A, i.mappingCylinder) => f a)
      (ContinuousMap.mappingCylinderTargetInclusion_comp i)
  simpa [ContinuousMap.mappingCylinderTimeZeroInclusion, ContinuousMap.comp_apply] using ha.symm

/-- Helper for Criterion 6.2.3: the time-`1` slice of the cylinder inclusion is the chosen
endpoint map on `A`. -/
private theorem mappingCylinderCylinderInclusion_apply_one (i : C(A, X)) :
    ∀ a : A,
      (ContinuousMap.mappingCylinderCylinderInclusion i) (a, 1) =
        mappingCylinderCylinderEndpoint i a := by
  intro a
  -- This is exactly how the endpoint map was defined.
  simp [mappingCylinderCylinderEndpoint, ContinuousMap.comp_apply]

/-- Helper for Criterion 6.2.3: the canonical cylinder inclusion packages into the universal
homotopy on `A` from `X ⟶ M_i` to its time-`1` slice. -/
private def mappingCylinderCylinderInclusionHomotopy (i : C(A, X)) :
    ((ContinuousMap.mappingCylinderTargetInclusion i).comp i).Homotopy
      (mappingCylinderCylinderEndpoint i) :=
  ContinuousMap.Homotopy.ofProdSwap
    (ContinuousMap.mappingCylinderCylinderInclusion i)
    (mappingCylinderCylinderInclusion_apply_zero i)
    (mappingCylinderCylinderInclusion_apply_one i)

/-- Helper for Criterion 6.2.3: boundary compatibility with `X × {0}` and `A × I` determines a
left inverse to the canonical map `M_i ⟶ X × I` by the pushout universal property. -/
private theorem mappingCylinderCanonicalMap_leftInverse_of_boundary {i : C(A, X)}
    (r : C(X × I, i.mappingCylinder))
    (hX :
      r.comp (ContinuousMap.mappingCylinderTimeZeroInclusion X) =
        ContinuousMap.mappingCylinderTargetInclusion i)
    (hA :
      r.comp (ContinuousMap.mappingCylinderCylinderMap i) =
        ContinuousMap.mappingCylinderCylinderInclusion i) :
    r.comp (ContinuousMap.mappingCylinderCanonicalMap i) =
      ContinuousMap.id i.mappingCylinder := by
  have hcat :
      TopCat.ofHom (r.comp (ContinuousMap.mappingCylinderCanonicalMap i)) =
        TopCat.ofHom (ContinuousMap.id i.mappingCylinder) := by
    -- Compare both maps out of the pushout on the target and cylinder coprojections.
    apply pushout.hom_ext
    · simpa [TopCat.ofHom_comp] using
        congrArg TopCat.ofHom
          (by
            rw [ContinuousMap.comp_assoc,
              ContinuousMap.mappingCylinderCanonicalMap_comp_targetInclusion, hX]
            simp :
              ((r.comp (ContinuousMap.mappingCylinderCanonicalMap i)).comp
                  (ContinuousMap.mappingCylinderTargetInclusion i)) =
                (ContinuousMap.id i.mappingCylinder).comp
                  (ContinuousMap.mappingCylinderTargetInclusion i))
    · simpa [TopCat.ofHom_comp] using
        congrArg TopCat.ofHom
          (by
            rw [ContinuousMap.comp_assoc,
              ContinuousMap.mappingCylinderCanonicalMap_comp_cylinderInclusion, hA]
            simp :
              ((r.comp (ContinuousMap.mappingCylinderCanonicalMap i)).comp
                  (ContinuousMap.mappingCylinderCylinderInclusion i)) =
                (ContinuousMap.id i.mappingCylinder).comp
                  (ContinuousMap.mappingCylinderCylinderInclusion i))
  -- Return from the categorical equality to the underlying continuous maps.
  simpa using congrArg TopCat.Hom.hom hcat

/-- Criterion 6.2.3. A map `i` satisfies the HEP exactly when the canonical map
`j : M_i → X × I` has a left inverse `r : X × I → M_i` whose restrictions to `X × {0}` and
`A × I` are the canonical maps into the mapping cylinder. -/
theorem isCofibration_iff_exists_mappingCylinderRetract {i : C(A, X)} :
    IsCofibration.{u, u, u} i ↔
      ∃ r : C(X × I, i.mappingCylinder), IsMappingCylinderRetract r := by
  constructor
  · intro hi
    obtain ⟨G, F, hF⟩ :=
      hi.exists_homotopy_extension
        (f₀ := ContinuousMap.mappingCylinderTargetInclusion i)
        (g := mappingCylinderCylinderEndpoint i)
        (mappingCylinderCylinderInclusionHomotopy i)
    let r : C(X × I, i.mappingCylinder) := F.prodSwap
    have hEndpoint :
        r.comp (ContinuousMap.mappingCylinderTimeZeroInclusion X) =
          ContinuousMap.mappingCylinderTargetInclusion i := by
      -- Read the time-`0` endpoint of the extended homotopy on `X`.
      ext x
      simp [r, ContinuousMap.mappingCylinderTimeZeroInclusion, ContinuousMap.comp_apply]
    have hCylinder :
        r.comp (ContinuousMap.mappingCylinderCylinderMap i) =
          ContinuousMap.mappingCylinderCylinderInclusion i := by
      -- The extension agrees with the universal cylinder homotopy on `A × I`.
      ext z
      rcases z with ⟨a, t⟩
      calc
        (r.comp (ContinuousMap.mappingCylinderCylinderMap i)) (a, t) = F (t, i a) := by
          simp [r, ContinuousMap.comp_apply, ContinuousMap.mappingCylinderCylinderMap_apply]
        _ = (mappingCylinderCylinderInclusionHomotopy i) (t, a) := by
          exact hF (t, a)
        _ = (ContinuousMap.mappingCylinderCylinderInclusion i) (a, t) := by
          rfl
    have hLeftInv :
        r.comp (ContinuousMap.mappingCylinderCanonicalMap i) =
          ContinuousMap.id i.mappingCylinder := by
      -- Once the two boundary restrictions match, pushout uniqueness gives the retract equation.
      exact mappingCylinderCanonicalMap_leftInverse_of_boundary r hEndpoint hCylinder
    -- Assemble the retract data extracted from the extended homotopy.
    refine ⟨r, ?_⟩
    exact ⟨hLeftInv, hEndpoint, hCylinder⟩
  · rintro ⟨r, hr⟩
    exact hr.isCofibration
