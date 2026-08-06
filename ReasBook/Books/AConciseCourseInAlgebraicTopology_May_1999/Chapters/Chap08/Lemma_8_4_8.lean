import Mathlib.CategoryTheory.CommSq
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_4_5

open CategoryTheory Limits

noncomputable section

local notation "BasedSpace" => Under (⊤_ TopCat)

-- Semantic recall via `lean_leansearch`: no verified canonical suspension-of-cofiber comparison
-- surfaced in the current environment, while the local Chapter 8 owners are
-- `homotopyCofiber`, `Σ`, `cofiberStructureMap`, and `signedBasedSuspensionMap`.
-- The source-faithful statement is therefore recorded directly on these based-space models, with
-- compatibility and naturality expressed through the canonical square owner `CommSq`.

/-- The reduced cone construction is functorial in based maps. -/
private def basedConeMap {X Y : BasedSpace} (g : X ⟶ Y) :
    basedCone X ⟶ basedCone Y :=
  smashProductMap g (𝟙 basedUnitInterval)

/-- The reduced-cone map intertwines the base inclusions. -/
private theorem basedConeMap_baseInclusion_naturality {X X' : BasedSpace} (u : X ⟶ X') :
    basedConeBaseInclusion X ≫ basedConeMap u = u ≫ basedConeBaseInclusion X' := sorry

/-- A commuting square of based maps induces the corresponding map on homotopy cofibers. -/
def homotopyCofiberMap {X Y X' Y' : BasedSpace}
    (f : X ⟶ Y) (g : X' ⟶ Y') (u : X ⟶ X') (v : Y ⟶ Y')
    (sq : CommSq f u v g) :
    homotopyCofiber f ⟶ homotopyCofiber g :=
  pushout.map f (basedConeBaseInclusion X) g (basedConeBaseInclusion X')
    v (basedConeMap u) u sq.w (basedConeMap_baseInclusion_naturality u)

/-- The signed suspension construction preserves commuting squares of based maps. -/
private theorem signedBasedSuspensionMap_commSq {X Y X' Y' : BasedSpace}
    (f : X ⟶ Y) (g : X' ⟶ Y') (u : X ⟶ X') (v : Y ⟶ Y')
    (sq : CommSq f u v g) :
    CommSq (signedBasedSuspensionMap f) (signedBasedSuspensionMap u)
      (signedBasedSuspensionMap v) (signedBasedSuspensionMap g) := by
  refine ⟨?_⟩
  sorry

/-- A commuting square of based maps induces the corresponding map on the chosen homotopy
cofibers of the signed suspension maps. -/
def signedSuspensionHomotopyCofiberMap {X Y X' Y' : BasedSpace}
    (f : X ⟶ Y) (g : X' ⟶ Y') (u : X ⟶ X') (v : Y ⟶ Y')
    (sq : CommSq f u v g) :
    homotopyCofiber (signedBasedSuspensionMap f) ⟶
      homotopyCofiber (signedBasedSuspensionMap g) :=
  homotopyCofiberMap
    (signedBasedSuspensionMap f)
    (signedBasedSuspensionMap g)
    (signedBasedSuspensionMap u)
    (signedBasedSuspensionMap v)
    (signedBasedSuspensionMap_commSq f g u v sq)

/-- The forward comparison morphism `ΣC_f ⟶ C_(Σf)` descends from the cone on the structure map
`C_f ⟶ ΣX`. -/
private theorem suspensionHomotopyCofiberIsoHom_w {X Y : BasedSpace} (f : X ⟶ Y) :
    collapseToOnePoint (homotopyCofiber f) ≫
        constantBasedMap onePointBasedSpace (homotopyCofiber (signedBasedSuspensionMap f)) =
      basedConeBaseInclusion (homotopyCofiber f) ≫
        basedConeMap (cofiberStructureMap f) ≫
          homotopyCofiberConeInclusion (signedBasedSuspensionMap f) := sorry

/-- The forward comparison morphism `ΣC_f ⟶ C_(Σf)` induced by the structure map
`π(f) : C_f ⟶ ΣX`. -/
def suspensionHomotopyCofiberIsoHom {X Y : BasedSpace} (f : X ⟶ Y) :
    Σᵇ (homotopyCofiber f) ⟶ homotopyCofiber (signedBasedSuspensionMap f) :=
  pushout.desc
    (constantBasedMap onePointBasedSpace (homotopyCofiber (signedBasedSuspensionMap f)))
    (basedConeMap (cofiberStructureMap f) ≫
      homotopyCofiberConeInclusion (signedBasedSuspensionMap f))
    (suspensionHomotopyCofiberIsoHom_w f)

/-- The inverse comparison descends from the suspended target inclusion on `ΣY` together with an
explicit cone-side map into the cone summand of `ΣC_f`. -/
private theorem suspensionHomotopyCofiberIsoInv_w {X Y : BasedSpace} (f : X ⟶ Y) :
    signedBasedSuspensionMap f ≫
        signedBasedSuspensionMap (homotopyCofiberTargetInclusion f) =
      basedConeBaseInclusion (basedSuspension X) ≫
        basedConeMap
          (constantBasedMap (basedSuspension X) (homotopyCofiber f)) ≫
            basedSuspensionConeInclusion (homotopyCofiber f) := sorry

/-- The inverse comparison morphism `C_(Σf) ⟶ ΣC_f` underlying Lemma 8.4.8. -/
noncomputable def suspensionHomotopyCofiberIsoInv {X Y : BasedSpace} (f : X ⟶ Y) :
    homotopyCofiber (signedBasedSuspensionMap f) ⟶ Σᵇ (homotopyCofiber f) :=
  pushout.desc
    (signedBasedSuspensionMap (homotopyCofiberTargetInclusion f))
    (basedConeMap (constantBasedMap (basedSuspension X) (homotopyCofiber f)) ≫
      basedSuspensionConeInclusion (homotopyCofiber f))
    (suspensionHomotopyCofiberIsoInv_w f)

/-- The forward and inverse comparison morphisms for `ΣC_f ≅ C_(Σf)` satisfy the first triangle
identity. -/
theorem suspensionHomotopyCofiberIso_hom_inv_id {X Y : BasedSpace} (f : X ⟶ Y) :
    suspensionHomotopyCofiberIsoHom f ≫ suspensionHomotopyCofiberIsoInv f =
      𝟙 (Σᵇ (homotopyCofiber f)) := sorry

/-- The forward and inverse comparison morphisms for `ΣC_f ≅ C_(Σf)` satisfy the second triangle
identity. -/
theorem suspensionHomotopyCofiberIso_inv_hom_id {X Y : BasedSpace} (f : X ⟶ Y) :
    suspensionHomotopyCofiberIsoInv f ≫ suspensionHomotopyCofiberIsoHom f =
      𝟙 (homotopyCofiber (signedBasedSuspensionMap f)) := sorry

/-- Lemma 8.4.8 (1). For any based map `f`, the canonical comparison
`Σᵇ (homotopyCofiber f) ≅ homotopyCofiber (signedBasedSuspensionMap f)` identifies
the suspension of the homotopy cofiber with the homotopy cofiber of the signed suspension map. -/
noncomputable def suspensionHomotopyCofiberIso {X Y : BasedSpace} (f : X ⟶ Y) :
    Σᵇ (homotopyCofiber f) ≅ homotopyCofiber (signedBasedSuspensionMap f) where
  hom := suspensionHomotopyCofiberIsoHom f
  inv := suspensionHomotopyCofiberIsoInv f
  hom_inv_id := suspensionHomotopyCofiberIso_hom_inv_id f
  inv_hom_id := suspensionHomotopyCofiberIso_inv_hom_id f

/-- The comparison `suspensionHomotopyCofiberIso f` sends the suspended target inclusion to the
target inclusion for the cofiber of `signedBasedSuspensionMap f`. -/
theorem suspensionHomotopyCofiberIso_targetInclusion_commSq {X Y : BasedSpace} (f : X ⟶ Y) :
    CommSq
      (signedBasedSuspensionMap (homotopyCofiberTargetInclusion f))
      (𝟙 (Σᵇ Y))
      (suspensionHomotopyCofiberIso f).hom
      (homotopyCofiberTargetInclusion (signedBasedSuspensionMap f)) := by
  refine ⟨?_⟩
  sorry

/-- The comparison `suspensionHomotopyCofiberIso f` identifies the suspended structure map with
the cofiber structure map of `signedBasedSuspensionMap f`. -/
theorem suspensionHomotopyCofiberIso_structureMap_commSq {X Y : BasedSpace} (f : X ⟶ Y) :
    CommSq
      (suspensionHomotopyCofiberIso f).hom
      (signedBasedSuspensionMap (cofiberStructureMap f))
      (cofiberStructureMap (signedBasedSuspensionMap f))
      (𝟙 (Σᵇ (Σᵇ X))) := by
  refine ⟨?_⟩
  sorry

/-- Lemma 8.4.8 (2). The canonical comparison `suspensionHomotopyCofiberIso f` is compatible
with the suspended cofiber sequence, with the suspension-coordinate sign absorbed by
`signedBasedSuspensionMap`. -/
theorem suspensionHomotopyCofiberIso_compatible {X Y : BasedSpace} (f : X ⟶ Y) :
    CommSq
        (signedBasedSuspensionMap (homotopyCofiberTargetInclusion f))
        (𝟙 (Σᵇ Y))
        (suspensionHomotopyCofiberIso f).hom
        (homotopyCofiberTargetInclusion (signedBasedSuspensionMap f)) ∧
      CommSq
        (suspensionHomotopyCofiberIso f).hom
        (signedBasedSuspensionMap (cofiberStructureMap f))
        (cofiberStructureMap (signedBasedSuspensionMap f))
        (𝟙 (Σᵇ (Σᵇ X))) :=
  ⟨
    suspensionHomotopyCofiberIso_targetInclusion_commSq f,
    suspensionHomotopyCofiberIso_structureMap_commSq f
  ⟩

/-- Lemma 8.4.8 (3). For a commuting square `sq : CommSq f u v g` of based maps, the comparison
isomorphisms `suspensionHomotopyCofiberIso` are natural with
respect to the induced maps on `Σᵇ (homotopyCofiber _)` and
`homotopyCofiber (signedBasedSuspensionMap _)`. -/
theorem suspensionHomotopyCofiberIso_natural {X Y X' Y' : BasedSpace}
    (f : X ⟶ Y) (g : X' ⟶ Y') (u : X ⟶ X') (v : Y ⟶ Y')
    (sq : CommSq f u v g) :
    CommSq
      (signedBasedSuspensionMap (homotopyCofiberMap f g u v sq))
      (suspensionHomotopyCofiberIso f).hom
      (suspensionHomotopyCofiberIso g).hom
      (signedSuspensionHomotopyCofiberMap f g u v sq) := by
  refine ⟨?_⟩
  sorry
