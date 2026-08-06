import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_4_1

open CategoryTheory Limits

noncomputable section

local notation "BasedSpace" => Under (⊤_ TopCat)

-- Semantic recall via `lean_leansearch`: the visible quotient-map hits were `Quotient.map` and
-- `Topology.IsQuotientMap.mk`, while the local Chapter 8 cofiber API already packages these
-- quotients by pushouts in `Under (⊤_ TopCat)`. The source-faithful owner here is therefore the
-- based suspension `CX/X`, with the quotient stage `C_f ⟶ C_f / Y` expressed by pushout maps.

/-- The suspension of a based space `X`, realized in `Under (⊤_ TopCat)` as the quotient `CX/X`.
-/
abbrev basedSuspension (X : BasedSpace) : BasedSpace :=
  pushout (collapseToOnePoint X) (basedConeBaseInclusion X)

prefix:max "Σᵇ " => basedSuspension

/-- The cone summand `CX` includes into the based suspension `ΣX = CX/X`. -/
abbrev basedSuspensionConeInclusion (X : BasedSpace) :
    basedCone X ⟶ Σᵇ X :=
  pushout.inr (collapseToOnePoint X) (basedConeBaseInclusion X)

/-- The quotient of `C_f` obtained by collapsing the target summand `Y` to the basepoint. -/
abbrev homotopyCofiberTargetCollapse {X Y : BasedSpace} (f : X ⟶ Y) : BasedSpace :=
  pushout (collapseToOnePoint Y) (homotopyCofiberTargetInclusion f)

/-- The quotient map `C_f ⟶ C_f / Y` is the right pushout map collapsing the copy of `Y`. -/
abbrev homotopyCofiberTargetCollapseQuotientMap {X Y : BasedSpace} (f : X ⟶ Y) :
    homotopyCofiber f ⟶ homotopyCofiberTargetCollapse f :=
  pushout.inr (collapseToOnePoint Y) (homotopyCofiberTargetInclusion f)

private theorem constantBasedMap_eq_collapseToOnePoint_comp (X Y : BasedSpace) :
    constantBasedMap X Y =
      collapseToOnePoint X ≫ constantBasedMap onePointBasedSpace Y := by
  ext x
  rfl

private theorem comp_collapseToOnePoint {X Y : BasedSpace} (f : X ⟶ Y) :
    f ≫ collapseToOnePoint Y = collapseToOnePoint X := by
  ext x
  rfl

private theorem pushoutInl_eq_constantBasedMap {X Y : BasedSpace} (f : X ⟶ Y) :
    pushout.inl (collapseToOnePoint X) f =
      constantBasedMap onePointBasedSpace (pushout (collapseToOnePoint X) f) := by
  ext x
  cases x
  simpa [underTopBasepoint_onePointBasedSpace] using
    congrArg
      (fun k ↦ k (TopCat.terminalIsoPUnit.inv PUnit.unit))
      (CategoryTheory.Under.w (pushout.inl (collapseToOnePoint X) f))

/-- Collapsing the target summand of `C_f = Y ∪_f CX` sends the cone summand to `ΣX = CX/X`. -/
private theorem cofiberStructureMap_w {X Y : BasedSpace} (f : X ⟶ Y) :
    f ≫ constantBasedMap Y (Σᵇ X) =
      basedConeBaseInclusion X ≫ basedSuspensionConeInclusion X := by
  calc
    f ≫ constantBasedMap Y (Σᵇ X)
        = f ≫ collapseToOnePoint Y ≫ constantBasedMap onePointBasedSpace (Σᵇ X) := by
            rw [constantBasedMap_eq_collapseToOnePoint_comp]
    _ = collapseToOnePoint X ≫ constantBasedMap onePointBasedSpace (Σᵇ X) := by
      simpa [Category.assoc] using
        congrArg
          (fun k ↦ k ≫ constantBasedMap onePointBasedSpace (Σᵇ X))
          (comp_collapseToOnePoint f)
    _ = collapseToOnePoint X ≫ pushout.inl (collapseToOnePoint X) (basedConeBaseInclusion X) := by
      rw [pushoutInl_eq_constantBasedMap]
    _ = basedConeBaseInclusion X ≫ basedSuspensionConeInclusion X := by
      simpa [basedSuspension, basedSuspensionConeInclusion] using
        (pushout.condition :
          collapseToOnePoint X ≫
              pushout.inl (collapseToOnePoint X) (basedConeBaseInclusion X) =
            basedConeBaseInclusion X ≫
              pushout.inr (collapseToOnePoint X) (basedConeBaseInclusion X))

/-- Definition 8.4.4. The next structure map in the cofiber construction is the quotient map
`π : C_f ⟶ C_f / Y`, with codomain canonically identified with the suspension `ΣX`; in the
based-space model this is the induced map `C_f ⟶ Σᵇ X`. -/
def cofiberStructureMap {X Y : BasedSpace} (f : X ⟶ Y) :
    homotopyCofiber f ⟶ Σᵇ X :=
  pushout.desc
    (constantBasedMap Y (Σᵇ X))
    (basedSuspensionConeInclusion X)
    (cofiberStructureMap_w f)

/-- The structure map `C_f ⟶ ΣX` is the pushout descent of the constant map on `Y` and the cone
inclusion `CX ⟶ ΣX`. -/
theorem cofiberStructureMap_def {X Y : BasedSpace} (f : X ⟶ Y) :
    cofiberStructureMap f =
      pushout.desc
        (constantBasedMap Y (Σᵇ X))
        (basedSuspensionConeInclusion X)
        (cofiberStructureMap_w f) := rfl

/-- The map `C_f ⟶ ΣX` factors through the quotient collapsing the `Y`-summand of `C_f`. -/
private theorem homotopyCofiberTargetCollapseToBasedSuspension_w {X Y : BasedSpace}
    (f : X ⟶ Y) :
    collapseToOnePoint Y ≫ constantBasedMap onePointBasedSpace (Σᵇ X) =
      homotopyCofiberTargetInclusion f ≫ cofiberStructureMap f := by
  calc
    collapseToOnePoint Y ≫ constantBasedMap onePointBasedSpace (Σᵇ X)
        = constantBasedMap Y (Σᵇ X) := by
            rw [← constantBasedMap_eq_collapseToOnePoint_comp]
    _ = homotopyCofiberTargetInclusion f ≫ cofiberStructureMap f := by
      symm
      simpa [cofiberStructureMap_def] using
        (pushout.inl_desc
          (constantBasedMap Y (Σᵇ X))
          (basedSuspensionConeInclusion X)
          (cofiberStructureMap_w f))

/-- The quotient `C_f / Y` maps canonically to `ΣX`. -/
private def homotopyCofiberTargetCollapseToBasedSuspension {X Y : BasedSpace} (f : X ⟶ Y) :
    homotopyCofiberTargetCollapse f ⟶ Σᵇ X :=
  pushout.desc
    (constantBasedMap onePointBasedSpace (Σᵇ X))
    (cofiberStructureMap f)
    (homotopyCofiberTargetCollapseToBasedSuspension_w f)

/-- The cone inclusion into `C_f`, followed by the quotient `C_f ⟶ C_f / Y`, identifies the
base of the cone with the collapsed target copy of `Y`. -/
private theorem basedSuspensionToHomotopyCofiberTargetCollapse_w {X Y : BasedSpace}
    (f : X ⟶ Y) :
    collapseToOnePoint X ≫ constantBasedMap onePointBasedSpace (homotopyCofiberTargetCollapse f) =
      basedConeBaseInclusion X ≫
        (homotopyCofiberConeInclusion f ≫ homotopyCofiberTargetCollapseQuotientMap f) := by
  calc
    collapseToOnePoint X ≫ constantBasedMap onePointBasedSpace (homotopyCofiberTargetCollapse f)
        =
      collapseToOnePoint X ≫
        pushout.inl (collapseToOnePoint Y) (homotopyCofiberTargetInclusion f) := by
          rw [pushoutInl_eq_constantBasedMap (homotopyCofiberTargetInclusion f)]
    _ = (f ≫ collapseToOnePoint Y) ≫
          pushout.inl (collapseToOnePoint Y) (homotopyCofiberTargetInclusion f) := by
      rw [comp_collapseToOnePoint f]
    _ = f ≫
          (collapseToOnePoint Y ≫
            pushout.inl (collapseToOnePoint Y) (homotopyCofiberTargetInclusion f)) := by
      simp [Category.assoc]
    _ = f ≫
          (homotopyCofiberTargetInclusion f ≫ homotopyCofiberTargetCollapseQuotientMap f) := by
      rw [show collapseToOnePoint Y ≫
            pushout.inl (collapseToOnePoint Y) (homotopyCofiberTargetInclusion f) =
          homotopyCofiberTargetInclusion f ≫ homotopyCofiberTargetCollapseQuotientMap f from by
            simpa [homotopyCofiberTargetCollapseQuotientMap] using
              (pushout.condition :
                collapseToOnePoint Y ≫
                    pushout.inl (collapseToOnePoint Y)
                      (homotopyCofiberTargetInclusion f) =
                  homotopyCofiberTargetInclusion f ≫
                    pushout.inr (collapseToOnePoint Y)
                      (homotopyCofiberTargetInclusion f))]
    _ = (f ≫ homotopyCofiberTargetInclusion f) ≫ homotopyCofiberTargetCollapseQuotientMap f := by
      simp [Category.assoc]
    _ = (basedConeBaseInclusion X ≫ homotopyCofiberConeInclusion f) ≫
          homotopyCofiberTargetCollapseQuotientMap f := by
            rw [homotopyCofiber_condition]
    _ = basedConeBaseInclusion X ≫
          (homotopyCofiberConeInclusion f ≫ homotopyCofiberTargetCollapseQuotientMap f) := by
            simp [Category.assoc]

/-- The suspension `ΣX = CX/X` maps back to the quotient `C_f / Y` through the cone summand of
`C_f`. -/
private def basedSuspensionToHomotopyCofiberTargetCollapse {X Y : BasedSpace} (f : X ⟶ Y) :
    Σᵇ X ⟶ homotopyCofiberTargetCollapse f :=
  pushout.desc
    (constantBasedMap onePointBasedSpace (homotopyCofiberTargetCollapse f))
    (homotopyCofiberConeInclusion f ≫ homotopyCofiberTargetCollapseQuotientMap f)
    (basedSuspensionToHomotopyCofiberTargetCollapse_w f)

/-- The quotient `C_f / Y` is canonically identified with the suspension `ΣX = CX/X`. -/
def homotopyCofiberTargetCollapseIsoBasedSuspension {X Y : BasedSpace} (f : X ⟶ Y) :
    homotopyCofiberTargetCollapse f ≅ Σᵇ X where
  hom := homotopyCofiberTargetCollapseToBasedSuspension f
  inv := basedSuspensionToHomotopyCofiberTargetCollapse f
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The structure map `C_f ⟶ ΣX` is also the composite of the quotient map `C_f ⟶ C_f / Y` with
the canonical identification `C_f / Y ≅ ΣX`. -/
theorem cofiberStructureMap_eq_homotopyCofiberTargetCollapseQuotientMap_comp
    {X Y : BasedSpace} (f : X ⟶ Y) :
    cofiberStructureMap f =
      homotopyCofiberTargetCollapseQuotientMap f ≫
        (homotopyCofiberTargetCollapseIsoBasedSuspension f).hom := by
  symm
  simpa
      [ homotopyCofiberTargetCollapseIsoBasedSuspension
      , homotopyCofiberTargetCollapseToBasedSuspension
      ] using
    (pushout.inr_desc
      (constantBasedMap onePointBasedSpace (Σᵇ X))
      (cofiberStructureMap f)
      (homotopyCofiberTargetCollapseToBasedSuspension_w f))

/-- On the target summand `Y ⟶ C_f`, `cofiberStructureMap f` is the constant map to the
suspension basepoint. -/
@[simp] theorem cofiberStructureMap_targetInclusion {X Y : BasedSpace} (f : X ⟶ Y) :
    homotopyCofiberTargetInclusion f ≫ cofiberStructureMap f =
      constantBasedMap Y (Σᵇ X) := by
  simpa [homotopyCofiberTargetInclusion, cofiberStructureMap_def] using
    (pushout.inl_desc
      (constantBasedMap Y (Σᵇ X))
      (basedSuspensionConeInclusion X)
      (cofiberStructureMap_w f))

/-- On the cone summand `CX ⟶ C_f`, `cofiberStructureMap f` is the canonical inclusion
`CX ⟶ ΣX = CX/X`. -/
@[simp] theorem cofiberStructureMap_coneInclusion {X Y : BasedSpace} (f : X ⟶ Y) :
    homotopyCofiberConeInclusion f ≫ cofiberStructureMap f =
      basedSuspensionConeInclusion X := by
  simpa [homotopyCofiberConeInclusion, cofiberStructureMap_def] using
    (pushout.inr_desc
      (constantBasedMap Y (Σᵇ X))
      (basedSuspensionConeInclusion X)
      (cofiberStructureMap_w f))
