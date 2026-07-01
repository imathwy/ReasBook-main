import Mathlib
import stacks_project.Chap06.Definition_6_26_1
import stacks_project.Chap17.Definition_17_28_10
import stacks_project.Chap18.Lemma_18_33_11

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopologicalSpace AlgebraicGeometry.RingedSpace.Hom
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry RingedSite.Hom RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X X' S S' : RingedSpace.{u}}

/- Domain-style sampling for Lemma 17.28.12:
- primary domain: base change for relative differentials in a commutative square of ringed spaces;
- sampled owner declarations:
  `RingedSpace.Hom.pullback`,
  `AlgebraicGeometry.RingedSpace.Ω[_]`,
  `AlgebraicGeometry.RingedSpace.d[_]`,
  `RingedSite.Hom.pullbackDifferentialsComparison`,
  `RingedSite.Hom.existsUnique_pullbackDifferentialsComparison`;
- best owner abstraction:
  the Chapter 18 bundled owner theorem on `RingedSite.Hom`, specialized to the site of opens of a
  ringed space;
- primitive data:
  only the four morphisms `f`, `g`, `h`, `h'` and the commutative square `CommSq f h' h g`;
- derived API:
  the ringed-space comparison map `pullbackDifferentialsComparison` and its sectionwise
  characterization/uniqueness.

Source/core/bridge triage:
- `source-facing`: the ringed-space map `c_f : f^* Ω[h] ⟶ Ω[h']`;
- `core/canonical`: `RingedSite.Hom.pullbackDifferentialsComparison` and its existence/uniqueness
  theorem;
- `bridge/view`: the passage from a ringed space to the ringed site of opens together with
  `RingedSpace.Hom.toRingCatSheafHom`.

The previous file stored an objectwise pushed-forward derivation and its compatibility as public
primitive data. That was duplicated bridge scaffolding. The public ringed-space API should expose
only the comparison morphism and its intrinsic sectionwise characterization. -/

variable (f : X' ⟶ X) (g : S' ⟶ S) (h : X ⟶ S) (h' : X' ⟶ S')

private abbrev opensRingedSite (X : RingedSpace.{u}) : RingedSite :=
  RingedSite.ofCommRingSheaf (Opens.grothendieckTopology X) X.sheaf

private noncomputable abbrev opensRingedSiteHom {A B : RingedSpace.{u}} (φ : A ⟶ B) :
    opensRingedSite A ⟶ opensRingedSite B where
  base := Opens.map φ.hom.base
  structureSheafMap := toRingCatSheafHom φ

private theorem opensRingedSiteHom_hcomm
    (sq : CommSq f h' h g) :
    opensRingedSiteHom f ≫ opensRingedSiteHom h =
      opensRingedSiteHom h' ≫ opensRingedSiteHom g := by
  simpa using congrArg opensRingedSiteHom sq.w

private theorem opensRingedSite_inverseImageStructureSheafMap_eq
    {A B : RingedSpace.{u}} (φ : A ⟶ B) :
    RingedSite.Hom.inverseImageStructureSheafMap (opensRingedSiteHom φ) =
      inverseImageStructureSheafHomComm φ := by
  sorry

private noncomputable abbrev opensRingedSiteDifferentials {A B : RingedSpace.{u}} (φ : A ⟶ B) :
    SheafOfModules (opensRingedSite A).structureSheaf :=
  relativeDifferentials (RingedSite.Hom.inverseImageStructureSheafMap (opensRingedSiteHom φ))

private theorem opensRingedSite_differentials_eq
    {A B : RingedSpace.{u}} (φ : A ⟶ B) :
    opensRingedSiteDifferentials φ = Ω[φ] := by
  simpa [opensRingedSiteDifferentials, RingedSite.Hom.differentials,
    AlgebraicGeometry.RingedSpace.differentials_def] using
    congrArg relativeDifferentials (opensRingedSite_inverseImageStructureSheafMap_eq φ)

private theorem opensRingedSite_modulePullback_differentials_eq
    {A B C : RingedSpace.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    (RingedSite.Hom.modulePullback (opensRingedSiteHom φ)).obj
        (opensRingedSiteDifferentials ψ) =
      (φ^*).obj Ω[ψ] := by
  rw [RingedSite.Hom.modulePullback, RingedSpace.Hom.pullback, opensRingedSiteHom]
  exact congrArg (RingedSpace.Hom.pullback φ).obj (opensRingedSite_differentials_eq ψ)

-- Proof sketch: transport the Chapter 18 owner
-- `RingedSite.Hom.pullbackDifferentialsComparison` from the opens-site presentation of the four
-- ringed spaces back to the Chapter 17 ringed-space surface.
/-- The canonical base-change map on relative differentials associated to a commutative square of
ringed spaces. This is the ringed-space specialization of
`RingedSite.Hom.pullbackDifferentialsComparison`. -/
noncomputable abbrev pullbackDifferentialsComparison
    (sq : CommSq f h' h g) :
    (f^*).obj Ω[h] ⟶ Ω[h'] :=
  eqToHom (opensRingedSite_modulePullback_differentials_eq f h).symm ≫
    RingedSite.Hom.pullbackDifferentialsComparison
      (opensRingedSiteHom f)
      (opensRingedSiteHom g)
      (opensRingedSiteHom h)
      (opensRingedSiteHom h')
      (opensRingedSiteHom_hcomm f g h h' sq) ≫
    eqToHom (opensRingedSite_differentials_eq h')

/-- The source-facing sectionwise characterization property for the base-change morphism on
relative differentials. -/
def pullbackDifferentialsComparisonProperty
    (τ : (f^*).obj Ω[h] ⟶ Ω[h']) : Prop :=
  ∀ {U : (Opens X)ᵒᵖ} (t : X.presheaf.obj U),
    let U' := (Opens.map f.hom.base).op.obj U
    let fSharpU := (toRingCatSheafHom f).hom.app U
    ((((SheafOfModules.pullbackPushforwardAdjunction
          (toRingCatSheafHom f)).homEquiv _ _)
        τ).val.app U)
      (((d[h]).app U).d t) =
      ((d[h']).app U').d (fSharpU t)

-- Proof sketch: specialize the Chapter 18 characterization theorem along the opens-site bridge
-- and transport source/target through the equalities above.
/-- The canonical comparison morphism is characterized by sending `d_{X/S}(t)` to
`d_{X'/S'}(f^\sharp t)` after passage to the adjoint map `Ω_{X/S} → f_* Ω_{X'/S'}`. -/
theorem pullbackDifferentialsComparison_characterizing
    (sq : CommSq f h' h g) :
    pullbackDifferentialsComparisonProperty f h h'
      (pullbackDifferentialsComparison f g h h' sq) := by
  sorry

-- Proof sketch: transport the Chapter 18 uniqueness theorem along the same opens-site bridge.
/-- A morphism `f^* \Omega_{X/S} \to \Omega_{X'/S'}` is the canonical comparison morphism once its
adjoint sends `d_{X/S}(t)` to `d_{X'/S'}(f^\sharp t)` on local sections. -/
theorem pullbackDifferentialsComparison_unique
    (sq : CommSq f h' h g)
    (τ : (f^*).obj Ω[h] ⟶ Ω[h'])
    (hτ : pullbackDifferentialsComparisonProperty f h h' τ) :
    τ = pullbackDifferentialsComparison f g h h' sq := by
  sorry

-- Proof sketch: existence is witnessed by the canonical specialized owner morphism above, and
-- uniqueness is the preceding theorem.
/-- Lemma 17.28.12: for a commutative square of ringed spaces
`X' \xrightarrow{f} X`, `S' \xrightarrow{g} S`, there exists a unique
`\mathcal O_{X'}`-module morphism
`c_f : f^* \Omega_{X/S} \to \Omega_{X'/S'}`
whose adjoint sends `d_{X/S}(t)` to `d_{X'/S'}(f^\sharp t)` on every local section `t` of
`\mathcal O_X`. -/
theorem existsUnique_pullbackDifferentialsComparison
    (sq : CommSq f h' h g) :
    ∃! τ : (f^*).obj Ω[h] ⟶ Ω[h'],
      pullbackDifferentialsComparisonProperty f h h' τ := by
  refine ⟨pullbackDifferentialsComparison f g h h' sq, ?_, ?_⟩
  · exact pullbackDifferentialsComparison_characterizing f g h h' sq
  · intro τ hτ
    exact pullbackDifferentialsComparison_unique f g h h' sq τ hτ

end AlgebraicGeometry.RingedSpace
