import Mathlib.CategoryTheory.CommSq
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_3_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.OnePointBasedSpace

open CategoryTheory Limits
open scoped unitInterval

noncomputable section

local notation "BasedSpace" => Under (⊤_ TopCat)
local notation "I₊" => adjoinBasepoint (TopCat.of I)

/-- The Chapter 8 based-space view of `basedInterval`, with distinguished point `1 : I`. -/
abbrev basedUnitInterval : BasedSpace :=
  basedInterval.toBasedSpace

/-- The chosen basepoint of `basedUnitInterval` is the endpoint `1 : I`. -/
@[simp] theorem underTopBasepoint_basedUnitInterval :
    underTopBasepoint basedUnitInterval = (1 : I) := rfl

/-- The based-space cone view `X ∧ I`, with `I` based at `1`. For pointed compactly generated
spaces, `basedCone X.toBasedSpace` is canonically identified with the earlier reduced-cone owner
`(reducedCone X).toBasedSpace`. -/
abbrev basedCone (X : BasedSpace) : BasedSpace :=
  smashProduct X basedUnitInterval

/-- For pointed compactly generated spaces, the Chapter 8 cone view agrees with the reduced cone
from Definition 8.2.1. -/
noncomputable abbrev basedConeIsoReducedCone (X : PointedCompactlyGenerated) :
    basedCone X.toBasedSpace ≅ (reducedCone X).toBasedSpace :=
  (reducedConeIsoSmashProduct X).symm

/-- The raw map `x ↦ [(x, 0)]` is continuous as a map from `X.right` to `(basedCone X).right`. -/
private theorem basedConeBaseInclusionContinuous (X : BasedSpace) :
    Continuous (fun x : X.right ↦ smashProductMk X basedUnitInterval (x, (0 : I))) := sorry

/-- The continuous map `X.right → (basedCone X).right` sending `x` to the class of `(x, 0)`. -/
private def basedConeBaseInclusionContinuousMap (X : BasedSpace) :
    C(X.right, (basedCone X).right) :=
  ⟨fun x ↦ smashProductMk X basedUnitInterval (x, (0 : I)), basedConeBaseInclusionContinuous X⟩

/-- The time-`0` inclusion into the cone preserves basepoints. -/
private theorem basedConeBaseInclusion_w (X : BasedSpace) :
    X.hom ≫ TopCat.ofHom (basedConeBaseInclusionContinuousMap X) =
      (basedCone X).hom := sorry

/-- The inclusion `X ⟶ CX` sending `x` to the class of `(x, 0)` in `X ∧ I`. -/
def basedConeBaseInclusion (X : BasedSpace) : X ⟶ basedCone X :=
  Under.homMk
    (TopCat.ofHom (basedConeBaseInclusionContinuousMap X))
    (basedConeBaseInclusion_w X)

/-- Evaluating `basedConeBaseInclusion X` at `x` gives the class of `(x, 0)` in `X ∧ I`. -/
@[simp] theorem basedConeBaseInclusion_apply (X : BasedSpace) (x : X.right) :
    (basedConeBaseInclusion X).right.hom x =
      smashProductMk X basedUnitInterval (x, (0 : I)) := sorry

/-- The raw map `x ↦ [(x, 1)]` is continuous as a map from `X.right` to `(reducedCylinder X).right`.
-/
private theorem reducedCylinderTopInclusionContinuous (X : BasedSpace) :
    Continuous
      (fun x : X.right ↦
        smashProductMk X I₊ (x, ((Sum.inr (1 : I)) : I₊.right))) := sorry

/-- The endpoint inclusion `X ⟶ X ∧ I₊` sending `x` to the class of `(x, 1)`. -/
private def reducedCylinderTopInclusionContinuousMap (X : BasedSpace) :
    C(X.right, (reducedCylinder X).right) :=
  ⟨
    fun x ↦ smashProductMk X I₊ (x, ((Sum.inr (1 : I)) : I₊.right)),
    reducedCylinderTopInclusionContinuous X
  ⟩

/-- The endpoint inclusion at time `1` preserves the chosen basepoint. -/
private theorem reducedCylinderTopInclusion_w (X : BasedSpace) :
    X.hom ≫ TopCat.ofHom (reducedCylinderTopInclusionContinuousMap X) =
      (reducedCylinder X).hom := sorry

/-- The endpoint inclusion `X ⟶ X ∧ I₊` sending `x` to the class of `(x, 1)`. -/
def reducedCylinderTopInclusion (X : BasedSpace) : X ⟶ reducedCylinder X :=
  Under.homMk
    (TopCat.ofHom (reducedCylinderTopInclusionContinuousMap X))
    (reducedCylinderTopInclusion_w X)

/-- Evaluating `reducedCylinderTopInclusion X` at `x` gives the class of `(x, 1)` in `X ∧ I₊`. -/
@[simp] theorem reducedCylinderTopInclusion_apply (X : BasedSpace) (x : X.right) :
    (reducedCylinderTopInclusion X).right.hom x =
      smashProductMk X I₊ (x, ((Sum.inr (1 : I)) : I₊.right)) := rfl

/-- The continuous map underlying the time-`1` copy of `X` inside the based mapping cylinder
`M_f`. -/
private def basedMappingCylinderTopInclusionContinuousMap {X Y : BasedSpace} (f : X ⟶ Y) :
    C(X.right, (basedMappingCylinder f).right) :=
  (basedMappingCylinderCylinderInclusion f).right.hom.comp
    (reducedCylinderTopInclusionContinuousMap X)

/-- The time-`1` inclusion into `M_f` preserves the chosen basepoints. -/
private theorem basedMappingCylinderTopInclusion_w {X Y : BasedSpace} (f : X ⟶ Y) :
    X.hom ≫ TopCat.ofHom (basedMappingCylinderTopInclusionContinuousMap f) =
      (basedMappingCylinder f).hom := sorry

/-- The copy of `X` sitting at time `1` inside the based mapping cylinder `M_f`. -/
def basedMappingCylinderTopInclusion {X Y : BasedSpace} (f : X ⟶ Y) :
    X ⟶ basedMappingCylinder f :=
  Under.homMk
    (TopCat.ofHom (basedMappingCylinderTopInclusionContinuousMap f))
    (basedMappingCylinderTopInclusion_w f)

/-- Evaluating `basedMappingCylinderTopInclusion f` at `x` first includes `x` into `X ∧ I₊` at
time `1` and then into the pushout `M_f`. -/
@[simp] theorem basedMappingCylinderTopInclusion_apply {X Y : BasedSpace} (f : X ⟶ Y)
    (x : X.right) :
    (basedMappingCylinderTopInclusion f).right.hom x =
      (basedMappingCylinderCylinderInclusion f).right.hom
        ((reducedCylinderTopInclusion X).right.hom x) := rfl

/-- Definition 8.4.1 (1). For a based map `f : X ⟶ Y`, the homotopy cofiber `C_f` is the based
pushout `Y ∪_f CX`, realized here as the pushout of `f` with the cone-base inclusion
`basedConeBaseInclusion X : X ⟶ basedCone X`. -/
abbrev homotopyCofiber {X Y : BasedSpace} (f : X ⟶ Y) : BasedSpace :=
  pushout f (basedConeBaseInclusion X)

/-- The canonical inclusion of `Y` into the homotopy cofiber `C_f = Y ∪_f CX`. -/
abbrev homotopyCofiberTargetInclusion {X Y : BasedSpace} (f : X ⟶ Y) :
    Y ⟶ homotopyCofiber f :=
  pushout.inl f (basedConeBaseInclusion X)

/-- The canonical inclusion of the cone summand `CX` into the homotopy cofiber `C_f = Y ∪_f CX`.
-/
abbrev homotopyCofiberConeInclusion {X Y : BasedSpace} (f : X ⟶ Y) :
    basedCone X ⟶ homotopyCofiber f :=
  pushout.inr f (basedConeBaseInclusion X)

/-- The defining pushout square for `C_f` commutes. -/
theorem homotopyCofiberInclusion_commSq {X Y : BasedSpace} (f : X ⟶ Y) :
    CommSq f (basedConeBaseInclusion X)
      (homotopyCofiberTargetInclusion f) (homotopyCofiberConeInclusion f) := by
  refine ⟨?_⟩
  simpa [homotopyCofiberTargetInclusion, homotopyCofiberConeInclusion] using
    (pushout.condition :
      f ≫ pushout.inl f (basedConeBaseInclusion X) =
        basedConeBaseInclusion X ≫ pushout.inr f (basedConeBaseInclusion X))

/-- In the pushout presentation `C_f = Y ∪_f CX`, the target and cone inclusions agree on `X`. -/
theorem homotopyCofiber_condition {X Y : BasedSpace} (f : X ⟶ Y) :
    f ≫ homotopyCofiberTargetInclusion f =
      basedConeBaseInclusion X ≫ homotopyCofiberConeInclusion f := by
  simpa using (homotopyCofiberInclusion_commSq f).w

/-- Definition 8.4.1 (2). Equivalently, the homotopy cofiber `C_f` is the based mapping cylinder
`M_f` with the copy of `X` at time `1` collapsed to the basepoint. -/
abbrev homotopyCofiberMappingCylinderCollapse {X Y : BasedSpace} (f : X ⟶ Y) : BasedSpace :=
  pushout (basedMappingCylinderTopInclusion f) (collapseToOnePoint X)

/-- The canonical inclusion of `M_f` into the mapping-cylinder-collapse pushout model of
`C_f`. -/
abbrev homotopyCofiberMappingCylinderCollapseTargetInclusion {X Y : BasedSpace} (f : X ⟶ Y) :
    basedMappingCylinder f ⟶ homotopyCofiberMappingCylinderCollapse f :=
  pushout.inl (basedMappingCylinderTopInclusion f) (collapseToOnePoint X)

/-- The canonical inclusion of the collapsed one-point space into the mapping-cylinder-collapse
pushout model of `C_f`. -/
abbrev homotopyCofiberMappingCylinderCollapseBasepointInclusion {X Y : BasedSpace}
    (f : X ⟶ Y) :
    onePointBasedSpace ⟶ homotopyCofiberMappingCylinderCollapse f :=
  pushout.inr (basedMappingCylinderTopInclusion f) (collapseToOnePoint X)

/-- The defining pushout square for the mapping-cylinder-collapse model of `C_f` commutes. -/
theorem homotopyCofiberMappingCylinderCollapse_commSq {X Y : BasedSpace} (f : X ⟶ Y) :
    CommSq (basedMappingCylinderTopInclusion f) (collapseToOnePoint X)
      (homotopyCofiberMappingCylinderCollapseTargetInclusion f)
      (homotopyCofiberMappingCylinderCollapseBasepointInclusion f) := by
  refine ⟨?_⟩
  simpa
      [ homotopyCofiberMappingCylinderCollapseTargetInclusion
      , homotopyCofiberMappingCylinderCollapseBasepointInclusion
      ] using
    (pushout.condition :
      basedMappingCylinderTopInclusion f ≫
          pushout.inl (basedMappingCylinderTopInclusion f) (collapseToOnePoint X) =
        collapseToOnePoint X ≫
          pushout.inr (basedMappingCylinderTopInclusion f) (collapseToOnePoint X))

/-- In the mapping-cylinder-collapse model, the time-`1` copy of `X` inside `M_f` is identified
with the collapsed copy of `X`. -/
theorem homotopyCofiberMappingCylinderCollapse_condition {X Y : BasedSpace} (f : X ⟶ Y) :
    basedMappingCylinderTopInclusion f ≫
        homotopyCofiberMappingCylinderCollapseTargetInclusion f =
      collapseToOnePoint X ≫
        homotopyCofiberMappingCylinderCollapseBasepointInclusion f := by
  simpa using (homotopyCofiberMappingCylinderCollapse_commSq f).w

/-- The cone summand `CX` maps to the mapping-cylinder-collapse model by sending the class of
`(x, t)` to the class of `(x, t)` in `M_f` and then collapsing the time-`1` copy of `X`. -/
private def basedConeToMappingCylinderCollapseRaw {X Y : BasedSpace} (f : X ⟶ Y) :
    X.right × I → (homotopyCofiberMappingCylinderCollapse f).right
  | (x, t) =>
      (homotopyCofiberMappingCylinderCollapseTargetInclusion f).right.hom
        ((basedMappingCylinderCylinderInclusion f).right.hom
          (smashProductMk X I₊ (x, Sum.inr t)))

private theorem basedConeToMappingCylinderCollapseRaw_eq_basepoint_of_mem_smashWedge
    {X Y : BasedSpace} (f : X ⟶ Y) {p : X.right × I}
    (hp : smashWedge X basedUnitInterval p) :
    basedConeToMappingCylinderCollapseRaw f p =
      underTopBasepoint (homotopyCofiberMappingCylinderCollapse f) := by
  rcases p with ⟨x, t⟩
  rcases (smashWedge_iff X basedUnitInterval (x, t)).1 hp with hx | ht
  · have hmk :
        smashProductMk X I₊ (x, Sum.inr t) = underTopBasepoint (reducedCylinder X) := by
      apply smashProduct_mk_eq_basepoint_of_mem_smashWedge
      exact (smashWedge_iff X I₊ (x, Sum.inr t)).2 (Or.inl hx)
    calc
      basedConeToMappingCylinderCollapseRaw f (x, t)
          =
        (homotopyCofiberMappingCylinderCollapseTargetInclusion f).right.hom
          ((basedMappingCylinderCylinderInclusion f).right.hom
            (underTopBasepoint (reducedCylinder X))) := by
              rw [basedConeToMappingCylinderCollapseRaw, hmk]
      _ =
        (homotopyCofiberMappingCylinderCollapseTargetInclusion f).right.hom
          (underTopBasepoint (basedMappingCylinder f)) := by
            rw [fundamentalGroupFunctorMap_basepoint (basedMappingCylinderCylinderInclusion f)]
      _ = underTopBasepoint (homotopyCofiberMappingCylinderCollapse f) := by
        rw [fundamentalGroupFunctorMap_basepoint
          (homotopyCofiberMappingCylinderCollapseTargetInclusion f)]
  · have htop :
        basedConeToMappingCylinderCollapseRaw f (x, t) =
          (homotopyCofiberMappingCylinderCollapseBasepointInclusion f).right.hom PUnit.unit := by
      have ht' : t = (1 : I) := by
        simpa using ht
      calc
        basedConeToMappingCylinderCollapseRaw f (x, t)
            =
          (homotopyCofiberMappingCylinderCollapseTargetInclusion f).right.hom
            ((basedMappingCylinderCylinderInclusion f).right.hom
              ((reducedCylinderTopInclusion X).right.hom x)) := by
                rw [basedConeToMappingCylinderCollapseRaw, ht', reducedCylinderTopInclusion_apply]
        _ =
          ((collapseToOnePoint X) ≫
              homotopyCofiberMappingCylinderCollapseBasepointInclusion f).right.hom x := by
                simpa [Category.assoc] using
                  congrArg
                    (fun k ↦ k.right.hom x)
                    (homotopyCofiberMappingCylinderCollapse_condition f)
        _ = (homotopyCofiberMappingCylinderCollapseBasepointInclusion f).right.hom PUnit.unit := by
          exact congrArg
            (homotopyCofiberMappingCylinderCollapseBasepointInclusion f).right.hom
            (collapseToOnePoint_apply X x)
    exact htop.trans <| by
      simpa [underTopBasepoint_onePointBasedSpace] using
        (fundamentalGroupFunctorMap_basepoint
          (homotopyCofiberMappingCylinderCollapseBasepointInclusion f))

private theorem basedConeToMappingCylinderCollapseRaw_respects {X Y : BasedSpace}
    (f : X ⟶ Y) :
    ∀ ⦃p q : X.right × I⦄,
      smashProductRel X basedUnitInterval p q →
        basedConeToMappingCylinderCollapseRaw f p =
          basedConeToMappingCylinderCollapseRaw f q := by
  intro p q hpq
  rcases hpq with rfl | ⟨hp, hq⟩
  · rfl
  · exact
      (basedConeToMappingCylinderCollapseRaw_eq_basepoint_of_mem_smashWedge f hp).trans
        (basedConeToMappingCylinderCollapseRaw_eq_basepoint_of_mem_smashWedge f hq).symm

private theorem basedConeToMappingCylinderCollapseContinuous {X Y : BasedSpace} (f : X ⟶ Y) :
    Continuous
      (Quotient.lift
        (basedConeToMappingCylinderCollapseRaw f)
        (basedConeToMappingCylinderCollapseRaw_respects f) :
          (basedCone X).right → (homotopyCofiberMappingCylinderCollapse f).right) := sorry

private def basedConeToMappingCylinderCollapseContinuousMap {X Y : BasedSpace} (f : X ⟶ Y) :
    C((basedCone X).right, (homotopyCofiberMappingCylinderCollapse f).right) :=
  ⟨Quotient.lift
      (basedConeToMappingCylinderCollapseRaw f)
      (basedConeToMappingCylinderCollapseRaw_respects f),
    basedConeToMappingCylinderCollapseContinuous f⟩

private theorem basedConeToMappingCylinderCollapse_w {X Y : BasedSpace} (f : X ⟶ Y) :
    (basedCone X).hom ≫ TopCat.ofHom (basedConeToMappingCylinderCollapseContinuousMap f) =
      (homotopyCofiberMappingCylinderCollapse f).hom := sorry

def basedConeToMappingCylinderCollapse {X Y : BasedSpace} (f : X ⟶ Y) :
    basedCone X ⟶ homotopyCofiberMappingCylinderCollapse f :=
  Under.homMk
    (TopCat.ofHom (basedConeToMappingCylinderCollapseContinuousMap f))
    (basedConeToMappingCylinderCollapse_w f)

/-- On the cone class of `(x, t)`, the comparison map first includes `(x, t)` into `M_f` and then
into the mapping-cylinder-collapse pushout. -/
@[simp] theorem basedConeToMappingCylinderCollapse_apply {X Y : BasedSpace} (f : X ⟶ Y)
    (x : X.right) (t : I) :
    (basedConeToMappingCylinderCollapse f).right.hom (smashProductMk X basedUnitInterval (x, t)) =
      (homotopyCofiberMappingCylinderCollapseTargetInclusion f).right.hom
        ((basedMappingCylinderCylinderInclusion f).right.hom
          (smashProductMk X I₊ (x, Sum.inr t))) := sorry

/-- The canonical comparison map from the pushout model `Y ∪_f CX` to the mapping-cylinder
collapse model. -/
private theorem homotopyCofiberToMappingCylinderCollapse_w {X Y : BasedSpace} (f : X ⟶ Y) :
    f ≫
        (basedMappingCylinderTargetInclusion f ≫
          homotopyCofiberMappingCylinderCollapseTargetInclusion f) =
      basedConeBaseInclusion X ≫ basedConeToMappingCylinderCollapse f := by
  ext x
  simpa [Category.assoc] using
    congrArg
      (fun k ↦
        (homotopyCofiberMappingCylinderCollapseTargetInclusion f).right.hom (k.right.hom x))
      (basedMappingCylinder_condition f)

def homotopyCofiberToMappingCylinderCollapse {X Y : BasedSpace} (f : X ⟶ Y) :
    homotopyCofiber f ⟶ homotopyCofiberMappingCylinderCollapse f :=
  pushout.desc
    (basedMappingCylinderTargetInclusion f ≫
      homotopyCofiberMappingCylinderCollapseTargetInclusion f)
    (basedConeToMappingCylinderCollapse f)
    (homotopyCofiberToMappingCylinderCollapse_w f)

/-- The reduced cylinder `X ∧ I₊` maps to the pushout model `Y ∪_f CX` by sending the adjoined
basepoint to the basepoint of `C_f` and sending `(x, t)` to the cone class of `(x, t)`. -/
private def reducedCylinderToHomotopyCofiberRaw {X Y : BasedSpace} (f : X ⟶ Y) :
    X.right × I₊.right → (homotopyCofiber f).right
  | (_, Sum.inl _) => underTopBasepoint (homotopyCofiber f)
  | (x, Sum.inr t) =>
      (homotopyCofiberConeInclusion f).right.hom
        (smashProductMk X basedUnitInterval (x, t))

private theorem reducedCylinderToHomotopyCofiberRaw_eq_basepoint_of_mem_smashWedge
    {X Y : BasedSpace} (f : X ⟶ Y) {p : X.right × I₊.right}
    (hp : smashWedge X I₊ p) :
    reducedCylinderToHomotopyCofiberRaw f p =
      underTopBasepoint (homotopyCofiber f) := by
  rcases p with ⟨x, t⟩
  rcases t with _ | t
  · rfl
  · rcases (smashWedge_iff X I₊ (x, Sum.inr t)).1 hp with hx | ht
    · have hmk :
          smashProductMk X basedUnitInterval (x, t) = underTopBasepoint (basedCone X) := by
        apply smashProduct_mk_eq_basepoint_of_mem_smashWedge
        exact (smashWedge_iff X basedUnitInterval (x, t)).2 (Or.inl hx)
      calc
        reducedCylinderToHomotopyCofiberRaw f (x, Sum.inr t)
            =
          (homotopyCofiberConeInclusion f).right.hom
            (underTopBasepoint (basedCone X)) := by
              rw [reducedCylinderToHomotopyCofiberRaw, hmk]
        _ = underTopBasepoint (homotopyCofiber f) := by
          rw [fundamentalGroupFunctorMap_basepoint (homotopyCofiberConeInclusion f)]
    · simp [underTopBasepoint_adjoinBasepoint] at ht

private theorem reducedCylinderToHomotopyCofiberRaw_respects {X Y : BasedSpace} (f : X ⟶ Y) :
    ∀ ⦃p q : X.right × I₊.right⦄,
      smashProductRel X I₊ p q →
        reducedCylinderToHomotopyCofiberRaw f p =
          reducedCylinderToHomotopyCofiberRaw f q := by
  intro p q hpq
  rcases hpq with rfl | ⟨hp, hq⟩
  · rfl
  · exact
      (reducedCylinderToHomotopyCofiberRaw_eq_basepoint_of_mem_smashWedge f hp).trans
        (reducedCylinderToHomotopyCofiberRaw_eq_basepoint_of_mem_smashWedge f hq).symm

private theorem reducedCylinderToHomotopyCofiberContinuous {X Y : BasedSpace} (f : X ⟶ Y) :
    Continuous
      (Quotient.lift
        (reducedCylinderToHomotopyCofiberRaw f)
        (reducedCylinderToHomotopyCofiberRaw_respects f) :
          (reducedCylinder X).right → (homotopyCofiber f).right) := sorry

private def reducedCylinderToHomotopyCofiberContinuousMap {X Y : BasedSpace} (f : X ⟶ Y) :
    C((reducedCylinder X).right, (homotopyCofiber f).right) :=
  ⟨Quotient.lift
      (reducedCylinderToHomotopyCofiberRaw f)
      (reducedCylinderToHomotopyCofiberRaw_respects f),
    reducedCylinderToHomotopyCofiberContinuous f⟩

private theorem reducedCylinderToHomotopyCofiber_w {X Y : BasedSpace} (f : X ⟶ Y) :
    (reducedCylinder X).hom ≫ TopCat.ofHom (reducedCylinderToHomotopyCofiberContinuousMap f) =
      (homotopyCofiber f).hom := sorry

def reducedCylinderToHomotopyCofiber {X Y : BasedSpace} (f : X ⟶ Y) :
    reducedCylinder X ⟶ homotopyCofiber f :=
  Under.homMk
    (TopCat.ofHom (reducedCylinderToHomotopyCofiberContinuousMap f))
    (reducedCylinderToHomotopyCofiber_w f)

/-- On the adjoined basepoint of `I₊`, the cylinder-to-cofiber map lands at the basepoint of
`C_f`. -/
@[simp] theorem reducedCylinderToHomotopyCofiber_apply_basepoint {X Y : BasedSpace}
    (f : X ⟶ Y) (x : X.right) :
    (reducedCylinderToHomotopyCofiber f).right.hom
        (smashProductMk X I₊ (x, Sum.inl PUnit.unit)) =
      underTopBasepoint (homotopyCofiber f) := sorry

/-- On the cylinder class of `(x, t)`, the cylinder-to-cofiber map lands in the cone summand of
`Y ∪_f CX`. -/
@[simp] theorem reducedCylinderToHomotopyCofiber_apply {X Y : BasedSpace} (f : X ⟶ Y)
    (x : X.right) (t : I) :
    (reducedCylinderToHomotopyCofiber f).right.hom (smashProductMk X I₊ (x, Sum.inr t)) =
      (homotopyCofiberConeInclusion f).right.hom
        (smashProductMk X basedUnitInterval (x, t)) := sorry

/-- The mapping cylinder `M_f` maps to the pushout model `Y ∪_f CX` by the identity on the
target summand `Y` and by the cylinder-to-cone collapse on the reduced-cylinder summand. -/
private theorem basedMappingCylinderToHomotopyCofiber_w {X Y : BasedSpace} (f : X ⟶ Y) :
    f ≫ homotopyCofiberTargetInclusion f =
      reducedCylinderBaseInclusion X ≫ reducedCylinderToHomotopyCofiber f := by
  ext x
  simpa [Category.assoc] using
    congrArg (fun k ↦ k.right.hom x) (homotopyCofiber_condition f)

def basedMappingCylinderToHomotopyCofiber {X Y : BasedSpace} (f : X ⟶ Y) :
    basedMappingCylinder f ⟶ homotopyCofiber f :=
  pushout.desc
    (homotopyCofiberTargetInclusion f)
    (reducedCylinderToHomotopyCofiber f)
    (basedMappingCylinderToHomotopyCofiber_w f)

/-- The mapping-cylinder-collapse pushout maps back to `Y ∪_f CX` by sending the collapsed top
copy of `X` to the basepoint of the homotopy cofiber. -/
private theorem mappingCylinderCollapseToHomotopyCofiber_w {X Y : BasedSpace} (f : X ⟶ Y) :
    basedMappingCylinderTopInclusion f ≫ basedMappingCylinderToHomotopyCofiber f =
      collapseToOnePoint X ≫ constantBasedMap onePointBasedSpace (homotopyCofiber f) := by
  ext x
  have htop :
      smashProductMk X basedUnitInterval (x, (1 : I)) =
        underTopBasepoint (basedCone X) := by
    simpa [basedCone] using
      smashProduct_mk_eq_basepoint_of_mem_smashWedge X basedUnitInterval
        ((smashWedge_iff X basedUnitInterval (x, (1 : I))).2
          (Or.inr underTopBasepoint_basedUnitInterval.symm))
  have hcone :
      (homotopyCofiberConeInclusion f).right.hom
          (smashProductMk X basedUnitInterval (x, (1 : I))) =
        underTopBasepoint (homotopyCofiber f) := by
    calc
      (homotopyCofiberConeInclusion f).right.hom
          (smashProductMk X basedUnitInterval (x, (1 : I)))
          =
        (homotopyCofiberConeInclusion f).right.hom
          (underTopBasepoint (basedCone X)) := by rw [htop]
      _ = underTopBasepoint (homotopyCofiber f) := by
        simpa [underTopBasepoint] using
          congrArg
            (fun k ↦ k (TopCat.terminalIsoPUnit.inv PUnit.unit))
            (CategoryTheory.Under.w (homotopyCofiberConeInclusion f))
  calc
    ((basedMappingCylinderTopInclusion f ≫ basedMappingCylinderToHomotopyCofiber f).right.hom x)
        =
      (basedMappingCylinderToHomotopyCofiber f).right.hom
        ((basedMappingCylinderCylinderInclusion f).right.hom
          ((reducedCylinderTopInclusion X).right.hom x)) := by
      rfl
    _ =
      (reducedCylinderToHomotopyCofiber f).right.hom
        ((reducedCylinderTopInclusion X).right.hom x) := by
      simpa using
        congrArg
          (fun k ↦ k.right.hom ((reducedCylinderTopInclusion X).right.hom x))
          (pushout.inr_desc
            (homotopyCofiberTargetInclusion f)
            (reducedCylinderToHomotopyCofiber f)
            (basedMappingCylinderToHomotopyCofiber_w f))
    _ = (homotopyCofiberConeInclusion f).right.hom
          (smashProductMk X basedUnitInterval (x, (1 : I))) := by
      rw [reducedCylinderTopInclusion_apply]
      simpa using reducedCylinderToHomotopyCofiber_apply f x (1 : I)
    _ = underTopBasepoint (homotopyCofiber f) := hcone
    _ =
      (collapseToOnePoint X ≫
          constantBasedMap onePointBasedSpace (homotopyCofiber f)).right.hom x := by
      rfl

def mappingCylinderCollapseToHomotopyCofiber {X Y : BasedSpace} (f : X ⟶ Y) :
    homotopyCofiberMappingCylinderCollapse f ⟶ homotopyCofiber f :=
  pushout.desc
    (basedMappingCylinderToHomotopyCofiber f)
    (constantBasedMap onePointBasedSpace (homotopyCofiber f))
    (mappingCylinderCollapseToHomotopyCofiber_w f)

/-- The two pushout presentations of `C_f` are canonically isomorphic: the cone pushout
`Y ∪_f CX` and the mapping-cylinder-collapse pushout. -/
def homotopyCofiberIsoMappingCylinderCollapse {X Y : BasedSpace} (f : X ⟶ Y) :
    homotopyCofiber f ≅ homotopyCofiberMappingCylinderCollapse f where
  hom := homotopyCofiberToMappingCylinderCollapse f
  inv := mappingCylinderCollapseToHomotopyCofiber f
  hom_inv_id := sorry
  inv_hom_id := sorry
