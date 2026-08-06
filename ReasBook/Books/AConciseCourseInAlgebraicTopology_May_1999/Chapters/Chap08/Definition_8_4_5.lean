import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Adjunction_8_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_4_4

open CategoryTheory Limits
open scoped unitInterval

noncomputable section

local notation "BasedSpace" => Under (⊤_ TopCat)

-- Semantic recall via `lean_leansearch`: the visible `cofiber` and `cofiber sequence` hits were
-- model-categorical or homological, while the verified local Chapter 8 owners for based spaces
-- are `homotopyCofiber`, `basedSuspension`, and `cofiberStructureMap`. The source-faithful owner
-- here is therefore an explicit forward `ℕ`-indexed sequence of based spaces and maps.

/-- A forward sequence of based spaces indexed by `ℕ`, with maps from stage `n` to stage `n + 1`.
-/
structure ForwardBasedSequence where
  /-- The `n`th object in the sequence. -/
  obj : ℕ → BasedSpace
  /-- The map from stage `n` to stage `n + 1`. -/
  map : (n : ℕ) → obj n ⟶ obj (n + 1)

namespace ForwardBasedSequence

/-- A `ForwardBasedSequence` may be viewed as its object function. -/
instance : CoeFun ForwardBasedSequence (fun _ ↦ ℕ → BasedSpace) where
  coe S := S.obj

end ForwardBasedSequence

/-- The quotient map into a smash product is continuous. -/
private theorem continuous_smashProductMk (X Y : BasedSpace) :
    Continuous (fun p : X.right × Y.right ↦ smashProductMk X Y p) := by
  simpa [smashProductMk, smashProductType] using
    (continuous_quotient_mk' :
      Continuous (@Quotient.mk' (smashProductPair X Y) (smashProductSetoid X Y)))

/-- In the suspension `Σᵇ Y = CY/Y`, the cone class of `(y, 0)` is the basepoint. -/
private theorem basedSuspensionConeInclusion_apply_timeZero (Y : BasedSpace) (y : Y.right) :
    (basedSuspensionConeInclusion Y).right.hom
      (smashProductMk Y basedUnitInterval (y, (0 : I))) =
        underTopBasepoint (basedSuspension Y) := by
  calc
    (basedSuspensionConeInclusion Y).right.hom
        (smashProductMk Y basedUnitInterval (y, (0 : I)))
      = (basedSuspensionConeInclusion Y).right.hom ((basedConeBaseInclusion Y).right.hom y) := by
          rw [basedConeBaseInclusion_apply]
    _ = ((basedConeBaseInclusion Y ≫ basedSuspensionConeInclusion Y).right.hom y) := rfl
    _ =
        ((collapseToOnePoint Y ≫
            pushout.inl (collapseToOnePoint Y) (basedConeBaseInclusion Y)).right.hom y) := by
          simpa [basedSuspension, basedSuspensionConeInclusion, Category.assoc] using
            congrArg
              (fun k ↦ k.right.hom y)
              ((pushout.condition :
                  collapseToOnePoint Y ≫
                      pushout.inl (collapseToOnePoint Y) (basedConeBaseInclusion Y) =
                    basedConeBaseInclusion Y ≫
                      pushout.inr (collapseToOnePoint Y) (basedConeBaseInclusion Y)).symm)
    _ =
        (pushout.inl (collapseToOnePoint Y) (basedConeBaseInclusion Y)).right.hom PUnit.unit := by
          rfl
    _ = underTopBasepoint (basedSuspension Y) := by
      simpa [basedSuspension, underTopBasepoint_onePointBasedSpace] using
        (fundamentalGroupFunctorMap_basepoint
          (pushout.inl (collapseToOnePoint Y) (basedConeBaseInclusion Y)))

/-- The sign-convention cone map on representatives sends `(x, t)` to the suspension class of
`(f x, 1 - t)`. -/
private def basedConeToSignedBasedSuspensionRaw {X Y : BasedSpace} (f : X ⟶ Y) :
    X.right × I → (basedSuspension Y).right
  | (x, t) =>
      (basedSuspensionConeInclusion Y).right.hom
        (smashProductMk Y basedUnitInterval (f.right.hom x, unitInterval.symm t))

/-- On any point in the wedge collapsed in `CX`, the representative-level signed cone map lands at
the basepoint of `ΣY`. -/
private theorem basedConeToSignedBasedSuspensionRaw_eq_basepoint_of_mem_smashWedge
    {X Y : BasedSpace} (f : X ⟶ Y) {p : X.right × I}
    (hp : smashWedge X basedUnitInterval p) :
    basedConeToSignedBasedSuspensionRaw f p = underTopBasepoint (basedSuspension Y) := by
  rcases p with ⟨x, t⟩
  rcases (smashWedge_iff X basedUnitInterval (x, t)).1 hp with hx | ht
  · have hmk :
        smashProductMk Y basedUnitInterval (underTopBasepoint Y, unitInterval.symm t) =
          underTopBasepoint (basedCone Y) := by
        simpa [basedCone] using
          smashProduct_mk_eq_basepoint_of_mem_smashWedge Y basedUnitInterval
            ((smashWedge_iff Y basedUnitInterval
                (underTopBasepoint Y, unitInterval.symm t)).2 (Or.inl rfl))
    calc
      basedConeToSignedBasedSuspensionRaw f (x, t)
          =
        (basedSuspensionConeInclusion Y).right.hom
          (smashProductMk Y basedUnitInterval (underTopBasepoint Y, unitInterval.symm t)) := by
            rw [basedConeToSignedBasedSuspensionRaw]
            have hbase : f.right.hom x = underTopBasepoint Y := by
              have hx' : x = underTopBasepoint X := by
                simpa using hx
              rw [hx']
              exact fundamentalGroupFunctorMap_basepoint f
            rw [hbase]
      _ = (basedSuspensionConeInclusion Y).right.hom (underTopBasepoint (basedCone Y)) := by
        rw [hmk]
      _ = underTopBasepoint (basedSuspension Y) := by
        exact fundamentalGroupFunctorMap_basepoint (basedSuspensionConeInclusion Y)
  · have ht' : t = (1 : I) := by
      simpa [underTopBasepoint_basedUnitInterval] using ht
    rw [basedConeToSignedBasedSuspensionRaw, ht', unitInterval.symm_one]
    exact basedSuspensionConeInclusion_apply_timeZero Y (f.right.hom x)

/-- The sign-convention representative map respects the cone quotient relation. -/
private theorem basedConeToSignedBasedSuspension_respects {X Y : BasedSpace} (f : X ⟶ Y) :
    ∀ p q : X.right × I,
      smashProductRel X basedUnitInterval p q →
        basedConeToSignedBasedSuspensionRaw f p = basedConeToSignedBasedSuspensionRaw f q := by
  intro p q hpq
  rcases hpq with rfl | ⟨hp, hq⟩
  · rfl
  · exact
      (basedConeToSignedBasedSuspensionRaw_eq_basepoint_of_mem_smashWedge f hp).trans
        (basedConeToSignedBasedSuspensionRaw_eq_basepoint_of_mem_smashWedge f hq).symm

/-- The sign-convention representative map `X × I → Σᵇ Y` is continuous. -/
private theorem basedConeToSignedBasedSuspensionRawContinuous {X Y : BasedSpace} (f : X ⟶ Y) :
    Continuous (basedConeToSignedBasedSuspensionRaw f) := by
  let g : C(X.right, Y.right) := f.right.hom
  let hf : Continuous g := g.continuous
  let coneInclusion : C((basedCone Y).right, (basedSuspension Y).right) :=
    (basedSuspensionConeInclusion Y).right.hom
  let hConeInclusion : Continuous coneInclusion := coneInclusion.continuous
  have hfst : Continuous fun p : X.right × I ↦ f.right.hom p.1 :=
    hf.comp continuous_fst
  have hsnd : Continuous fun p : X.right × I ↦ unitInterval.symm p.2 :=
    unitInterval.continuous_symm.comp continuous_snd
  exact hConeInclusion.comp <|
    (continuous_smashProductMk Y basedUnitInterval).comp (hfst.prodMk hsnd)

/-- The sign-convention cone map is continuous. -/
private theorem basedConeToSignedBasedSuspensionContinuous {X Y : BasedSpace} (f : X ⟶ Y) :
    Continuous
      (show (basedCone X).right → (basedSuspension Y).right from
        Quotient.lift
          (basedConeToSignedBasedSuspensionRaw f)
          (basedConeToSignedBasedSuspension_respects f)) :=
  (basedConeToSignedBasedSuspensionRawContinuous f).quotient_lift
    (basedConeToSignedBasedSuspension_respects f)

/-- The sign-convention cone map preserves the distinguished basepoints. -/
private theorem basedConeToSignedBasedSuspension_w {X Y : BasedSpace} (f : X ⟶ Y) :
    (basedCone X).hom ≫
        TopCat.ofHom
      (show C((basedCone X).right, (basedSuspension Y).right) from
            { toFun :=
                show (basedCone X).right → (basedSuspension Y).right from
                  Quotient.lift
                    (basedConeToSignedBasedSuspensionRaw f)
                    (basedConeToSignedBasedSuspension_respects f)
              continuous_toFun := basedConeToSignedBasedSuspensionContinuous f }) =
      (basedSuspension Y).hom := by
  ext x
  have hbase :
      basedConeToSignedBasedSuspensionRaw f (smashProductBasepointPair X basedUnitInterval) =
        underTopBasepoint (basedSuspension Y) :=
    basedConeToSignedBasedSuspensionRaw_eq_basepoint_of_mem_smashWedge f
      (smashWedge_basepointPair X basedUnitInterval)
  calc
    ((basedCone X).hom ≫
        TopCat.ofHom
          (show C((basedCone X).right, (basedSuspension Y).right) from
            { toFun :=
                show (basedCone X).right → (basedSuspension Y).right from
                  Quotient.lift
                    (basedConeToSignedBasedSuspensionRaw f)
                    (basedConeToSignedBasedSuspension_respects f)
              continuous_toFun := basedConeToSignedBasedSuspensionContinuous f })).hom x
        =
          basedConeToSignedBasedSuspensionRaw f
            (smashProductBasepointPair X basedUnitInterval) := by
            rfl
    _ = underTopBasepoint (basedSuspension Y) := hbase
    _ = (basedSuspension Y).hom x := by
      have hx : TopCat.terminalIsoPUnit.hom x = PUnit.unit := by
        cases h : TopCat.terminalIsoPUnit.hom x
        rfl
      calc
        underTopBasepoint (basedSuspension Y)
            = (basedSuspension Y).hom (TopCat.terminalIsoPUnit.inv PUnit.unit) := rfl
        _ = (basedSuspension Y).hom
              (TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom x)) := by
                rw [hx]
        _ = (basedSuspension Y).hom x := by simp

/-- The cone map used to impose the alternating-sign suspension convention on cofiber sequences. -/
private def basedConeToSignedBasedSuspension {X Y : BasedSpace} (f : X ⟶ Y) :
    basedCone X ⟶ basedSuspension Y :=
  Under.homMk
    (TopCat.ofHom
      (show C((basedCone X).right, (basedSuspension Y).right) from
        { toFun :=
            show (basedCone X).right → (basedSuspension Y).right from
              Quotient.lift
                (basedConeToSignedBasedSuspensionRaw f)
                (basedConeToSignedBasedSuspension_respects f)
          continuous_toFun := basedConeToSignedBasedSuspensionContinuous f }))
    (basedConeToSignedBasedSuspension_w f)

@[simp] private theorem basedConeToSignedBasedSuspension_apply {X Y : BasedSpace} (f : X ⟶ Y)
    (x : X.right) (t : I) :
    (basedConeToSignedBasedSuspension f).right.hom
        (smashProductMk X basedUnitInterval (x, t)) =
      (basedSuspensionConeInclusion Y).right.hom
        (smashProductMk Y basedUnitInterval (f.right.hom x, unitInterval.symm t)) := rfl

/-- The sign-convention suspension map collapses the `*`-summand of `Σᵇ X = CX/X` and sends the
cone class of `(x, t)` to the suspension class of `(f x, 1 - t)` in `Σᵇ Y`. -/
private theorem signedBasedSuspensionMap_w {X Y : BasedSpace} (f : X ⟶ Y) :
    collapseToOnePoint X ≫ constantBasedMap onePointBasedSpace (basedSuspension Y) =
      basedConeBaseInclusion X ≫ basedConeToSignedBasedSuspension f := by
  ext x
  have htop :
      smashProductMk Y basedUnitInterval (f.right.hom x, unitInterval.symm (0 : I)) =
        underTopBasepoint (basedCone Y) := by
    rw [unitInterval.symm_zero]
    simpa [basedCone] using
      smashProduct_mk_eq_basepoint_of_mem_smashWedge Y basedUnitInterval
        ((smashWedge_iff Y basedUnitInterval (f.right.hom x, (1 : I))).2
          (Or.inr underTopBasepoint_basedUnitInterval.symm))
  calc
    ((collapseToOnePoint X ≫
        constantBasedMap onePointBasedSpace (basedSuspension Y)).right.hom x)
        = underTopBasepoint (basedSuspension Y) := rfl
    _ = (basedSuspensionConeInclusion Y).right.hom (underTopBasepoint (basedCone Y)) := by
      symm
      exact fundamentalGroupFunctorMap_basepoint (basedSuspensionConeInclusion Y)
    _ = (basedSuspensionConeInclusion Y).right.hom
          (smashProductMk Y basedUnitInterval (f.right.hom x, unitInterval.symm (0 : I))) := by
      rw [htop]
    _ = (basedConeToSignedBasedSuspension f).right.hom
          (smashProductMk X basedUnitInterval (x, (0 : I))) := by
      symm
      exact basedConeToSignedBasedSuspension_apply f x (0 : I)
    _ = ((basedConeBaseInclusion X ≫ basedConeToSignedBasedSuspension f).right.hom x) := by
      rfl

/-- The sign-convention suspension map induced by `f : X ⟶ Y`, implementing the alternating-sign
rule by reversing the suspension coordinate. -/
def signedBasedSuspensionMap {X Y : BasedSpace} (f : X ⟶ Y) :
    Σᵇ X ⟶ Σᵇ Y :=
  pushout.desc
    (constantBasedMap onePointBasedSpace (Σᵇ Y))
    (basedConeToSignedBasedSuspension f)
    (signedBasedSuspensionMap_w f)

/-- The sign-convention suspension map is the pushout descent of the constant map on the collapsed
`X`-summand and the cone map `(x, t) ↦ (f x, 1 - t)`. -/
theorem signedBasedSuspensionMap_def {X Y : BasedSpace} (f : X ⟶ Y) :
    signedBasedSuspensionMap f =
      pushout.desc
        (constantBasedMap onePointBasedSpace (Σᵇ Y))
        (basedConeToSignedBasedSuspension f)
        (signedBasedSuspensionMap_w f) := rfl

/-- The objects of the cofiber sequence generated by `f`, indexed so that stage `0` is `X`. -/
def cofiberSequenceGeneratedByObj {X Y : BasedSpace} (f : X ⟶ Y) : ℕ → BasedSpace
  | 0 => X
  | 1 => Y
  | 2 => homotopyCofiber f
  | n + 3 => Σᵇ (cofiberSequenceGeneratedByObj f n)

/-- The maps of the cofiber sequence generated by `f`, with iterated suspension maps twisted by
`signedBasedSuspensionMap` to record the alternating-sign convention. -/
def cofiberSequenceGeneratedByMap {X Y : BasedSpace} (f : X ⟶ Y) :
    (n : ℕ) → cofiberSequenceGeneratedByObj f n ⟶ cofiberSequenceGeneratedByObj f (n + 1)
  | 0 => f
  | 1 => homotopyCofiberTargetInclusion f
  | 2 => cofiberStructureMap f
  | n + 3 => signedBasedSuspensionMap (cofiberSequenceGeneratedByMap f n)

/-- Definition 8.4.5. The cofiber sequence generated by `f` is the forward `ℕ`-indexed based
sequence
`X ⟶ Y ⟶ C_f ⟶ Σᵇ X ⟶ Σᵇ Y ⟶ Σᵇ C_f ⟶ Σ²X ⟶ ⋯`,
formalized using `homotopyCofiber f` for `C_f`, `cofiberStructureMap f : C_f ⟶ Σᵇ X` for the third
map, and `signedBasedSuspensionMap` for the iterated suspension maps carrying the alternating-sign
convention. -/
def cofiberSequenceGeneratedBy {X Y : BasedSpace} (f : X ⟶ Y) : ForwardBasedSequence where
  obj := cofiberSequenceGeneratedByObj f
  map := cofiberSequenceGeneratedByMap f

/-- The object function of `cofiberSequenceGeneratedBy f` is `cofiberSequenceGeneratedByObj f`. -/
theorem cofiberSequenceGeneratedBy_obj {X Y : BasedSpace} (f : X ⟶ Y) :
    (cofiberSequenceGeneratedBy f).obj = cofiberSequenceGeneratedByObj f := rfl

/-- The map function of `cofiberSequenceGeneratedBy f` is `cofiberSequenceGeneratedByMap f`. -/
theorem cofiberSequenceGeneratedBy_map {X Y : BasedSpace} (f : X ⟶ Y) :
    (cofiberSequenceGeneratedBy f).map = cofiberSequenceGeneratedByMap f := rfl

/-- Stage `0` of the generated cofiber sequence is `X`. -/
@[simp] theorem cofiberSequenceGeneratedBy_obj_zero {X Y : BasedSpace} (f : X ⟶ Y) :
    (cofiberSequenceGeneratedBy f).obj 0 = X := rfl

/-- Stage `1` of the generated cofiber sequence is `Y`. -/
@[simp] theorem cofiberSequenceGeneratedBy_obj_one {X Y : BasedSpace} (f : X ⟶ Y) :
    (cofiberSequenceGeneratedBy f).obj 1 = Y := rfl

/-- Stage `2` of the generated cofiber sequence is the homotopy cofiber `C_f`. -/
@[simp] theorem cofiberSequenceGeneratedBy_obj_two {X Y : BasedSpace} (f : X ⟶ Y) :
    (cofiberSequenceGeneratedBy f).obj 2 = homotopyCofiber f := rfl

/-- The first map in the generated cofiber sequence is `f : X ⟶ Y`. -/
@[simp] theorem cofiberSequenceGeneratedBy_map_zero {X Y : BasedSpace} (f : X ⟶ Y) :
    (cofiberSequenceGeneratedBy f).map 0 = f := rfl

/-- The second map in the generated cofiber sequence is the target inclusion `Y ⟶ C_f`. -/
@[simp] theorem cofiberSequenceGeneratedBy_map_one {X Y : BasedSpace} (f : X ⟶ Y) :
    (cofiberSequenceGeneratedBy f).map 1 = homotopyCofiberTargetInclusion f := rfl

/-- The third map in the generated cofiber sequence is the structure map `C_f ⟶ Σᵇ X`. -/
@[simp] theorem cofiberSequenceGeneratedBy_map_two {X Y : BasedSpace} (f : X ⟶ Y) :
    (cofiberSequenceGeneratedBy f).map 2 = cofiberStructureMap f := rfl

/-- The next object after `C_f` is the suspension `Σᵇ X`. -/
@[simp] theorem cofiberSequenceGeneratedBy_obj_three {X Y : BasedSpace} (f : X ⟶ Y) :
    (cofiberSequenceGeneratedBy f).obj 3 = Σᵇ X := rfl

/-- The first suspended map in the generated cofiber sequence is the signed suspension of `f`. -/
@[simp] theorem cofiberSequenceGeneratedBy_map_three {X Y : BasedSpace} (f : X ⟶ Y) :
    (cofiberSequenceGeneratedBy f).map 3 = signedBasedSuspensionMap f := rfl

/-- Stage `4` of the generated cofiber sequence is the suspension `Σᵇ Y`. -/
@[simp] theorem cofiberSequenceGeneratedBy_obj_four {X Y : BasedSpace} (f : X ⟶ Y) :
    (cofiberSequenceGeneratedBy f).obj 4 = Σᵇ Y := rfl

/-- Stage `5` of the generated cofiber sequence is the suspension `Σᵇ C_f`. -/
@[simp] theorem cofiberSequenceGeneratedBy_obj_five {X Y : BasedSpace} (f : X ⟶ Y) :
    (cofiberSequenceGeneratedBy f).obj 5 = Σᵇ (homotopyCofiber f) := rfl

/-- After stage `2`, the generated cofiber sequence is obtained by applying `Σ` recursively. -/
@[simp] theorem cofiberSequenceGeneratedBy_obj_add_three {X Y : BasedSpace} (f : X ⟶ Y)
    (n : ℕ) :
    (cofiberSequenceGeneratedBy f).obj (n + 3) =
      Σᵇ ((cofiberSequenceGeneratedBy f).obj n) := rfl

/-- After stage `2`, the generated cofiber sequence maps are obtained by recursively applying the
signed suspension map. -/
@[simp] theorem cofiberSequenceGeneratedBy_map_add_three {X Y : BasedSpace} (f : X ⟶ Y)
    (n : ℕ) :
    (cofiberSequenceGeneratedBy f).map (n + 3) =
      signedBasedSuspensionMap ((cofiberSequenceGeneratedBy f).map n) := rfl
