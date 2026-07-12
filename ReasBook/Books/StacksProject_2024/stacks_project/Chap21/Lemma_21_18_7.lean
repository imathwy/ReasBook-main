import StacksProject_2024.Chap21.Lemma_21_18_1
import StacksProject_2024.Chap21.Lemma_21_18_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CochainComplex

noncomputable section

universe u

namespace SheafOfModules.RingedSite

section

/-
Domain-style sampling for Lemma 21.18.7:
- primary domain: pullback of K-flat cochain complexes of module sheaves on a ringed site;
- inspected owner declarations:
  `CochainComplex.IsKFlat`,
  `CochainComplex.isKFlat_iff`,
  `ringedSiteUnderlyingStructureMap`,
  `pullbackFunctor`;
- best owner abstraction: K-flatness is already owned by `CochainComplex.IsKFlat`, while the
  site-presented inverse-image functor is already owned in this chapter by `pullbackFunctor`;
- primitive data: the site-presented structure morphism encoded by `φ`, the pullback functor it
  induces on module sheaves, and the complex `K`;
- derived API: the enough-points pullback preservation theorem for `K.IsKFlat`.

Source/core/bridge triage:
- `source-facing`: pullback preserves K-flatness under the enough-points hypothesis;
- `core/canonical`: `CochainComplex.IsKFlat`;
- `bridge/view`: the shared Chapter 21 bridge owners `ringedSiteUnderlyingStructureMap` and
  `pullbackFunctor` from `21_18_0_1`.
-/

variable {C : Type u} [Category.{u} C] {C' : Type u} [Category.{u} C']
variable {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J'.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{u}} {𝒪' : Sheaf J' CommRingCat.{u}}
variable [MonoidalCategory (SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪))]
variable [MonoidalPreadditive
  (SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪))]
variable [MonoidalCategory (SheafOfModules ((sheafCompose J' (forget₂ CommRingCat RingCat)).obj 𝒪'))]
variable [MonoidalPreadditive
  (SheafOfModules ((sheafCompose J' (forget₂ CommRingCat RingCat)).obj 𝒪'))]

variable (F : C' ⥤ C) [Functor.IsContinuous F J' J]
variable (φ : 𝒪' ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J' J).obj 𝒪)

local notation "ModC" => ringedSiteModuleCategory J 𝒪
local notation "ModC'" => ringedSiteModuleCategory J' 𝒪'

/-- Helper for Lemma 21.18.7: the stalk of the pulled-back complex at a source point should be
identified with a scalar-extension complex over a target stalk, and that identification is the
only remaining obstruction to closing the theorem. This stays as theorem-level proof debt rather
than placeholder isomorphism data. -/
private theorem stalkComplex_pullback_isKFlat
    (K : CochainComplex ModC' ℤ) (hK : K.IsKFlat)
    (p : GrothendieckTopology.Point.{u} J) :
    (stalkComplex 𝒪 (pullbackComplex F φ K) p).IsKFlat := by
  -- Route correction: the target point must come from the inverse-image topos point attached to
  -- `F`; the earlier `Point.comap` route added hypotheses not present in Lemma 21.18.7.
  -- The remaining proof uses the Chapter 18 stalk comparison for pullback together with
  -- `pullback_stalk_linearEquiv_tensor`, `stalkComplex_isKFlat_of_isKFlat`, and
  -- `extendScalarsComplex_isKFlat`.
  sorry

-- Proof sketch: use Lemma `21.18.6` to reduce K-flatness on the source ringed site to K-flatness
-- of all stalk complexes, which is valid because `(C, J)` has enough points. For a
-- source point, identify the stalk of the pulled-back complex with extension of scalars of the
-- corresponding target stalk via Lemma `18.36.4`, and then apply the module-theoretic extension
-- of scalars preservation of K-flatness from Lemma `15.59.3` to the stalkwise K-flatness coming
-- from the target complex.
/-- Lemma 21.18.7: if the source site of a site-presented morphism of ringed topoi has enough
points, then the pullback of a K-flat complex of `𝒪'`-modules is a K-flat complex of
`𝒪`-modules. -/
@[stacks 0DEP]
theorem pullback_isKFlat_of_isKFlat_of_hasEnoughPoints
    [GrothendieckTopology.HasEnoughPoints.{u} J]
    (K : CochainComplex ModC' ℤ) (hK : K.IsKFlat) :
    (pullbackComplex F φ K).IsKFlat := by
  -- Route correction: the main theorem now uses the enough-points reduction directly; only the
  -- source-faithful stalkwise pullback-versus-base-change comparison remains in the helper above.
  -- Reduce the global statement to the source stalk complexes of the pulled-back complex.
  refine isKFlat_of_stalkComplex_isKFlat_of_hasEnoughPoints
    𝒪 (pullbackComplex F φ K) ?_
  intro p
  -- The stalkwise comparison has been isolated so the main theorem follows once each source stalk
  -- is proved K-flat by the Chapter 18 and Chapter 15 bridge route.
  exact stalkComplex_pullback_isKFlat F φ K hK p

end

end SheafOfModules.RingedSite
