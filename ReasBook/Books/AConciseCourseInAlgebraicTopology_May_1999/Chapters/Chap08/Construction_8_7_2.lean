import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_5_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_4_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_6_5

open CategoryTheory Limits
open scoped Topology.Homotopy unitInterval

noncomputable section

local notation "BasedSpace" => Under (⊤_ TopCat)

/-- The `Y`-summand inclusion in `C_f` sends the basepoint of `Y` to the basepoint of `C_f`. -/
theorem homotopyCofiberTargetInclusion_basepoint {X Y : BasedSpace} (f : X ⟶ Y) :
    underTopBasepoint (homotopyCofiber f) =
      (homotopyCofiberTargetInclusion f).right.hom (underTopBasepoint Y) := sorry

/-- Mapping the path coordinate of `z : F_f` into `C_f` ends at the image of `f(z.point)`. -/
theorem homotopyFiberToLoopHomotopyCofiberPrefix_target {X Y : BasedSpace}
    (f : X ⟶ Y) (z : HomotopyFiber f) :
    (homotopyCofiberTargetInclusion f).right.hom z.path.endpoint =
      (homotopyCofiberTargetInclusion f).right.hom (f.right.hom z.point) := sorry

/-- The cone coordinate in `C_f` starts at the image of `f(z.point)` under the pushout
identification. -/
theorem homotopyFiberToLoopHomotopyCofiberConeSource {X Y : BasedSpace}
    (f : X ⟶ Y) (z : HomotopyFiber f) :
    (homotopyCofiberTargetInclusion f).right.hom (f.right.hom z.point) =
      (homotopyCofiberConeInclusion f).right.hom
        (smashProductMk X basedUnitInterval (z.point, (0 : I))) := sorry

/-- The cone coordinate in `C_f` ends at the basepoint of the homotopy cofiber. -/
theorem homotopyFiberToLoopHomotopyCofiberConeTarget {X Y : BasedSpace}
    (f : X ⟶ Y) (z : HomotopyFiber f) :
    underTopBasepoint (homotopyCofiber f) =
      (homotopyCofiberConeInclusion f).right.hom
        (smashProductMk X basedUnitInterval (z.point, (1 : I))) := sorry

/-- The loop in `C_f` obtained from `z : F_f` by first traversing its path coordinate in the
`Y`-summand and then traversing the cone coordinate of its `X`-coordinate. -/
def homotopyFiberToLoopHomotopyCofiberPath {X Y : BasedSpace} (f : X ⟶ Y)
    (z : HomotopyFiber f) :
    Ω (homotopyCofiber f).right (underTopBasepoint (homotopyCofiber f)) :=
  let pathPrefix :
      Path (underTopBasepoint (homotopyCofiber f))
        ((homotopyCofiberTargetInclusion f).right.hom (f.right.hom z.point)) :=
    ((PathSpace.toPath z.path).map
        ((homotopyCofiberTargetInclusion f).right.hom.continuous)).cast
      (homotopyCofiberTargetInclusion_basepoint f)
      (homotopyFiberToLoopHomotopyCofiberPrefix_target f z).symm
  let cone :
      Path ((homotopyCofiberTargetInclusion f).right.hom (f.right.hom z.point))
        (underTopBasepoint (homotopyCofiber f)) :=
    { toContinuousMap :=
        { toFun := fun t ↦
            (homotopyCofiberConeInclusion f).right.hom
              (smashProductMk X basedUnitInterval (z.point, t))
          continuous_toFun := sorry }
      source' := (homotopyFiberToLoopHomotopyCofiberConeSource f z).symm
      target' := (homotopyFiberToLoopHomotopyCofiberConeTarget f z).symm }
  pathPrefix.trans cone

/-- The loop family `z ↦ homotopyFiberToLoopHomotopyCofiberPath f z` is continuous. -/
theorem homotopyFiberToLoopHomotopyCofiberContinuous {X Y : BasedSpace} (f : X ⟶ Y) :
    Continuous fun z : HomotopyFiber f ↦ homotopyFiberToLoopHomotopyCofiberPath f z := sorry

/-- The continuous map underlying `η : F_f ⟶ ΩC_f`. -/
def homotopyFiberToLoopHomotopyCofiberContinuousMap {X Y : BasedSpace} (f : X ⟶ Y) :
    C(HomotopyFiber f,
      Ω (homotopyCofiber f).right (underTopBasepoint (homotopyCofiber f))) :=
  { toFun := fun z ↦ homotopyFiberToLoopHomotopyCofiberPath f z
    continuous_toFun := homotopyFiberToLoopHomotopyCofiberContinuous f }

/-- Construction 8.7.2 (1). For `f : X ⟶ Y`, the map `η : F_f ⟶ Ω C_f` sends
`(x, χ)` to the loop in `C_f` obtained by first traversing the path `χ` in the `Y`-summand and
then traversing the cone coordinate of `x` in the `CX`-summand. -/
def homotopyFiberToLoopHomotopyCofiber {X Y : BasedSpace} (f : X ⟶ Y) :
    homotopyFiber f ⟶ Ωᵇ (homotopyCofiber f) :=
  Under.homMk
    (TopCat.ofHom (homotopyFiberToLoopHomotopyCofiberContinuousMap f))
    sorry

/-- Evaluating `homotopyFiberToLoopHomotopyCofiber f` at `z : F_f` recovers the loop obtained by
following the `Y`-path of `z` and then the cone coordinate of `z.point`. -/
@[simp] theorem homotopyFiberToLoopHomotopyCofiber_hom_apply {X Y : BasedSpace}
    (f : X ⟶ Y) (z : HomotopyFiber f) :
    (homotopyFiberToLoopHomotopyCofiber f).right.hom z =
      homotopyFiberToLoopHomotopyCofiberPath f z := rfl

namespace homotopyFiberToLoopHomotopyCofiber

/-- Remark 8.7.5. The comparison map `η : F_f ⟶ Ω C_f` from Construction 8.7.2 makes the
incoming square from the fiber sequence to the looped cofiber sequence homotopy commute:
composing `ι(f) : Ωᵇ Y ⟶ F_f` with `η` is homotopic under the basepoint to the signed loop map on
the target inclusion `Y ⟶ C_f`. -/
theorem comp_homotopyFiberLoopInclusion_homotopic {X Y : BasedSpace} (f : X ⟶ Y) :
    HomotopicUnder
      (homotopyFiberLoopInclusion f ≫ homotopyFiberToLoopHomotopyCofiber f)
      (signedLoopBasedMap (homotopyCofiberTargetInclusion f)) :=
  sorry

end homotopyFiberToLoopHomotopyCofiber

/-- The representative-level cone evaluation sends `(z, t)` to the value at `t` of the loop from
Construction 8.7.2 (1). -/
private def homotopyFiberSuspensionConeToHomotopyCofiberRaw {X Y : BasedSpace} (f : X ⟶ Y) :
    HomotopyFiber f × I → (homotopyCofiber f).right
  | (z, t) => homotopyFiberToLoopHomotopyCofiberPath f z t

/-- The representative-level cone evaluation respects the quotient relation defining
`basedCone (homotopyFiber f)`. -/
private theorem homotopyFiberSuspensionConeToHomotopyCofiber_respects {X Y : BasedSpace}
    (f : X ⟶ Y) :
    ∀ p q : HomotopyFiber f × I,
      smashProductRel (homotopyFiber f) basedUnitInterval p q →
        homotopyFiberSuspensionConeToHomotopyCofiberRaw f p =
          homotopyFiberSuspensionConeToHomotopyCofiberRaw f q := by
  intro p q hpq
  sorry

/-- The quotient-lifted cone evaluation is continuous. -/
private theorem homotopyFiberSuspensionConeToHomotopyCofiberConeContinuous
    {X Y : BasedSpace} (f : X ⟶ Y) :
    Continuous
      (Quotient.lift
        (homotopyFiberSuspensionConeToHomotopyCofiberRaw f)
        (homotopyFiberSuspensionConeToHomotopyCofiber_respects f) :
          (basedCone (homotopyFiber f)).right → (homotopyCofiber f).right) := sorry

/-- The continuous map underlying the cone coordinate map used in Construction 8.7.2 (2). -/
private def homotopyFiberSuspensionConeToHomotopyCofiberContinuousMap {X Y : BasedSpace}
    (f : X ⟶ Y) :
    C((basedCone (homotopyFiber f)).right, (homotopyCofiber f).right) :=
  ⟨Quotient.lift
      (homotopyFiberSuspensionConeToHomotopyCofiberRaw f)
      (homotopyFiberSuspensionConeToHomotopyCofiber_respects f),
    homotopyFiberSuspensionConeToHomotopyCofiberConeContinuous f⟩

/-- The continuous cone evaluation sends the cone basepoint to the basepoint of `C_f`. -/
private theorem homotopyFiberSuspensionConeToHomotopyCofiber_w {X Y : BasedSpace} (f : X ⟶ Y) :
    (basedCone (homotopyFiber f)).hom ≫
        TopCat.ofHom (homotopyFiberSuspensionConeToHomotopyCofiberContinuousMap f) =
      (homotopyCofiber f).hom := sorry

/-- The cone-coordinate map used to descend `ε : ΣF_f ⟶ C_f`. -/
def homotopyFiberSuspensionConeToHomotopyCofiber {X Y : BasedSpace} (f : X ⟶ Y) :
    basedCone (homotopyFiber f) ⟶ homotopyCofiber f :=
  Under.homMk
    (TopCat.ofHom (homotopyFiberSuspensionConeToHomotopyCofiberContinuousMap f))
    (homotopyFiberSuspensionConeToHomotopyCofiber_w f)

/-- Evaluating the cone-coordinate map on the cone generator `(z, t)` evaluates the loop from
Construction 8.7.2 (1) at the suspension coordinate `t`. -/
@[simp] theorem homotopyFiberSuspensionConeToHomotopyCofiber_apply_mk {X Y : BasedSpace}
    (f : X ⟶ Y) (z : HomotopyFiber f) (t : I) :
    (homotopyFiberSuspensionConeToHomotopyCofiber f).right.hom
        (smashProductMk (homotopyFiber f) basedUnitInterval (z, t)) =
      homotopyFiberToLoopHomotopyCofiberPath f z t := rfl

/-- The maps defining `ε : ΣF_f ⟶ C_f` agree on the collapsed copy of `F_f`. -/
private theorem homotopyFiberSuspensionToHomotopyCofiber_w {X Y : BasedSpace} (f : X ⟶ Y) :
    collapseToOnePoint (homotopyFiber f) ≫ constantBasedMap onePointBasedSpace (homotopyCofiber f) =
      basedConeBaseInclusion (homotopyFiber f) ≫
        homotopyFiberSuspensionConeToHomotopyCofiber f := sorry

/-- Construction 8.7.2 (2). For `f : X ⟶ Y`, the map `ε : ΣF_f ⟶ C_f` is obtained by evaluating
the loop from Construction 8.7.2 (1), equivalently by first traversing the path coordinate in `Y`
and then the cone coordinate in `X`. -/
def homotopyFiberSuspensionToHomotopyCofiber {X Y : BasedSpace} (f : X ⟶ Y) :
    Σᵇ (homotopyFiber f) ⟶ homotopyCofiber f :=
  pushout.desc
    (constantBasedMap onePointBasedSpace (homotopyCofiber f))
    (homotopyFiberSuspensionConeToHomotopyCofiber f)
    (homotopyFiberSuspensionToHomotopyCofiber_w f)

/-- The map `ε : ΣF_f ⟶ C_f` is the pushout descent of the constant map on the collapsed
`F_f`-summand and the cone-evaluation map on the cone summand. -/
theorem homotopyFiberSuspensionToHomotopyCofiber_def {X Y : BasedSpace} (f : X ⟶ Y) :
    homotopyFiberSuspensionToHomotopyCofiber f =
      pushout.desc
        (constantBasedMap onePointBasedSpace (homotopyCofiber f))
        (homotopyFiberSuspensionConeToHomotopyCofiber f)
        (homotopyFiberSuspensionToHomotopyCofiber_w f) := rfl

/-- Restricting `homotopyFiberSuspensionToHomotopyCofiber f` along the collapsed basepoint
summand recovers the constant map to the basepoint of `C_f`. -/
@[simp] theorem homotopyFiberSuspensionToHomotopyCofiber_inl {X Y : BasedSpace} (f : X ⟶ Y) :
    (pushout.inl (collapseToOnePoint (homotopyFiber f))
        (basedConeBaseInclusion (homotopyFiber f))) ≫
      homotopyFiberSuspensionToHomotopyCofiber f =
    constantBasedMap onePointBasedSpace (homotopyCofiber f) := by
  simpa [homotopyFiberSuspensionToHomotopyCofiber_def] using
    (pushout.inl_desc
      (constantBasedMap onePointBasedSpace (homotopyCofiber f))
      (homotopyFiberSuspensionConeToHomotopyCofiber f)
      (homotopyFiberSuspensionToHomotopyCofiber_w f))

/-- Restricting `homotopyFiberSuspensionToHomotopyCofiber f` along the canonical suspension cone
inclusion recovers the cone-evaluation map used in its pushout construction. -/
@[simp] theorem homotopyFiberSuspensionToHomotopyCofiber_inr {X Y : BasedSpace} (f : X ⟶ Y) :
    basedSuspensionConeInclusion (homotopyFiber f) ≫
        homotopyFiberSuspensionToHomotopyCofiber f =
    homotopyFiberSuspensionConeToHomotopyCofiber f := by
  simpa
      [ basedSuspensionConeInclusion
      , homotopyFiberSuspensionToHomotopyCofiber_def
      ] using
    (pushout.inr_desc
      (constantBasedMap onePointBasedSpace (homotopyCofiber f))
      (homotopyFiberSuspensionConeToHomotopyCofiber f)
      (homotopyFiberSuspensionToHomotopyCofiber_w f))

/-- On a suspension generator represented by `(z, t) ∈ F_f × I`, the map
`homotopyFiberSuspensionToHomotopyCofiber f` evaluates the loop from
`homotopyFiberToLoopHomotopyCofiberPath f z` at the suspension coordinate `t`. -/
@[simp] theorem homotopyFiberSuspensionToHomotopyCofiber_inr_apply_mk {X Y : BasedSpace}
    (f : X ⟶ Y) (z : HomotopyFiber f) (t : I) :
    (homotopyFiberSuspensionToHomotopyCofiber f).right.hom
        ((basedSuspensionConeInclusion (homotopyFiber f)).right.hom
          (smashProductMk (homotopyFiber f) basedUnitInterval (z, t))) =
      homotopyFiberToLoopHomotopyCofiberPath f z t := by
  change
    (((basedSuspensionConeInclusion (homotopyFiber f)) ≫
        homotopyFiberSuspensionToHomotopyCofiber f).right.hom
      (smashProductMk (homotopyFiber f) basedUnitInterval (z, t)) =
        homotopyFiberToLoopHomotopyCofiberPath f z t)
  rw [homotopyFiberSuspensionToHomotopyCofiber_inr]
  exact homotopyFiberSuspensionConeToHomotopyCofiber_apply_mk f z t
