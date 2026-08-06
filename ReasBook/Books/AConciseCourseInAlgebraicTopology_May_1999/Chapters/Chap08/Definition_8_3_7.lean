import Mathlib.CategoryTheory.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.WithTerminal.Cone
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_3_6

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

noncomputable section

local notation "BasedSpace" => Under (⊤_ TopCat)
local notation "I₊" => adjoinBasepoint (TopCat.of I)

-- Semantic recall via `lean_leansearch`: `pushout`, `pushout.inl`, `pushout.inr`, and
-- `pushout.condition` are the canonical gluing API. Definition 8.3.6 already fixes
-- `reducedCylinder X = X ∧ I₊`, so the source definition is best expressed as the pushout of
-- `f : X ⟶ Y` with the time-zero inclusion `X ⟶ reducedCylinder X`.

/-- The category of based spaces inherits pushouts from `TopCat`. -/
private instance basedSpaceHasPushouts : HasPushouts BasedSpace := inferInstance

/-- The endpoint inclusion `X ⟶ X ∧ I₊` sending `x` to the class of `(x, 0)`. -/
def reducedCylinderBaseInclusionContinuousMap (X : BasedSpace) :
    C(X.right, (reducedCylinder X).right) :=
  ⟨
    fun x ↦
      smashProductMk X I₊ (x, ((Sum.inr (0 : I)) : I₊.right)),
    by
      simpa [reducedCylinder, smashProductMk] using
        (continuous_quotient_mk'.comp
          ((ContinuousMap.id X.right).continuous.prodMk
            (ContinuousMap.const X.right
              (((Sum.inr (0 : I)) : I₊.right))).continuous))
  ⟩

/-- Helper for Definition 8.3.7: the point `(underTopBasepoint X, 0)` represents the basepoint of
`reducedCylinder X = X ∧ I₊`. -/
private theorem reducedCylinderZeroEndpoint_eq_basepoint (X : BasedSpace) :
    smashProductMk X I₊ (underTopBasepoint X, ((Sum.inr (0 : I)) : I₊.right)) =
      underTopBasepoint (reducedCylinder X) := by
  -- Collapse the time-zero representative because its first coordinate is the basepoint of `X`.
  simpa [reducedCylinder] using
    (smashProduct_mk_eq_basepoint_of_mem_smashWedge X I₊
      ((smashWedge_iff X I₊ (underTopBasepoint X, Sum.inr (0 : I))).2 (Or.inl rfl)))

/-- The endpoint inclusion `X ⟶ X ∧ I₊` preserves the chosen basepoint. -/
theorem reducedCylinderBaseInclusion_w (X : BasedSpace) :
    X.hom ≫ TopCat.ofHom (reducedCylinderBaseInclusionContinuousMap X) =
      (reducedCylinder X).hom := by
  -- Maps out of the terminal object are determined by their value at the unique point.
  ext u
  have hu :
      u =
        (ConcreteCategory.hom TopCat.terminalIsoPUnit.inv)
          ((ConcreteCategory.hom TopCat.terminalIsoPUnit.hom) u) := by
    simp
  have hX :
      (ConcreteCategory.hom X.hom) u = underTopBasepoint X := by
    -- Re-express `u` through `PUnit` so the terminal map becomes definitionally constant.
    rw [hu]
    cases (TopCat.terminalIsoPUnit.hom u)
    rfl
  -- Rewrite the composite through the explicit time-zero representative and then collapse it.
  change
    smashProductMk X I₊ ((ConcreteCategory.hom X.hom) u, ((Sum.inr (0 : I)) : I₊.right)) =
      (ConcreteCategory.hom (reducedCylinder X).hom) u
  rw [hX, reducedCylinderZeroEndpoint_eq_basepoint X, hu]
  cases (TopCat.terminalIsoPUnit.hom u)
  rfl

/-- The based map `X ⟶ X ∧ I₊` used to attach the reduced cylinder to the target of a based map. -/
def reducedCylinderBaseInclusion (X : BasedSpace) : X ⟶ reducedCylinder X :=
  Under.homMk
    (TopCat.ofHom (reducedCylinderBaseInclusionContinuousMap X))
    (reducedCylinderBaseInclusion_w X)

/-- Evaluating `reducedCylinderBaseInclusion X` at `x` gives the class of `(x, 0)` in `X ∧ I₊`. -/
@[simp] theorem reducedCylinderBaseInclusion_apply (X : BasedSpace) (x : X.right) :
    (reducedCylinderBaseInclusion X).right.hom x =
      smashProductMk X I₊ (x, ((Sum.inr (0 : I)) : I₊.right)) := by
  -- `Under.homMk` packages the continuous map without changing its pointwise formula.
  rfl

/-- Definition 8.3.7. For a based map `f : X ⟶ Y`, the based mapping cylinder `M_f` is the
pushout `Y ∪_f (X ∧ I₊)`, realized in `BasedSpace` as the pushout of `f` and
`reducedCylinderBaseInclusion X`. -/
abbrev basedMappingCylinder {X Y : BasedSpace} (f : X ⟶ Y) : BasedSpace :=
  pushout f (reducedCylinderBaseInclusion X)

/-- The canonical inclusion of `Y` into the based mapping cylinder `M_f`. -/
abbrev basedMappingCylinderTargetInclusion {X Y : BasedSpace} (f : X ⟶ Y) :
    Y ⟶ basedMappingCylinder f :=
  pushout.inl f (reducedCylinderBaseInclusion X)

/-- The canonical inclusion of the reduced cylinder `X ∧ I₊` into the based mapping cylinder
`M_f`. -/
abbrev basedMappingCylinderCylinderInclusion {X Y : BasedSpace} (f : X ⟶ Y) :
    reducedCylinder X ⟶ basedMappingCylinder f :=
  pushout.inr f (reducedCylinderBaseInclusion X)

/-- The defining pushout square for `M_f` commutes: the two inclusions identify
`f : X ⟶ Y` with the time-`0` inclusion `X ⟶ X ∧ I₊`. -/
theorem basedMappingCylinderInclusion_commSq {X Y : BasedSpace} (f : X ⟶ Y) :
    CommSq f (reducedCylinderBaseInclusion X)
      (basedMappingCylinderTargetInclusion f) (basedMappingCylinderCylinderInclusion f) := by
  refine ⟨?_⟩
  simpa [basedMappingCylinderTargetInclusion, basedMappingCylinderCylinderInclusion] using
    (pushout.condition :
      f ≫ pushout.inl f (reducedCylinderBaseInclusion X) =
        reducedCylinderBaseInclusion X ≫ pushout.inr f (reducedCylinderBaseInclusion X))

/-- In the based mapping cylinder pushout square, the two ways of attaching `X` agree. -/
theorem basedMappingCylinder_condition {X Y : BasedSpace} (f : X ⟶ Y) :
    f ≫ basedMappingCylinderTargetInclusion f =
      reducedCylinderBaseInclusion X ≫ basedMappingCylinderCylinderInclusion f := by
  simpa using (basedMappingCylinderInclusion_commSq f).w
