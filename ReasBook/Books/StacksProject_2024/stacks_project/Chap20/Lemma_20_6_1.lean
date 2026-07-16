import StacksProject_2024.stacks_project.Chap07.Example_7_33_5
import StacksProject_2024.stacks_project.Chap07.Definition_7_38_1
import StacksProject_2024.stacks_project.Chap17.Definition_17_25_9
import StacksProject_2024.stacks_project.Chap17.Lemma_17_25_4
import StacksProject_2024.stacks_project.Chap18.Lemma_18_40_3
import StacksProject_2024.stacks_project.Chap21.Lemma_21_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open SheafOfModules.RingedSite
open scoped RingedSpacePicard

noncomputable section

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for Lemma 20.6.1:
- primary domain: units sheaves and Picard groups of ringed spaces, with the source statement
  comparing `H¹(X, 𝒪_Xˣ)` to the Picard group of `X`;
- sampled owner declarations:
  `Pic(X)`,
  `IsLocallyRingedSite`,
  `ringedSitePicardGroup`,
  `ringedSiteUnitsAddSheaf`,
  `ringedSiteUnitsSheaf_H1_equiv_picardGroup`,
  `RingedSpace.hasLocalUnitDichotomy_of_stalk_isLocalRing`,
  `isIso_oneNeverZeroEqualizerMap_iff_stalkwise_nontrivial`;
- best owner abstraction: the canonical owner theorem is the ringed-site comparison
  `ringedSiteUnitsSheaf_H1_equiv_picardGroup`, and the Chapter 20 item should be only its
  ringed-space specialization between `ringedSiteUnitsAddSheaf X.sheaf` and `Pic(X)`,
  with the Chapter 17 stalk-local-ring bridge feeding the Chapter 18 owner
  `IsLocallyRingedSite`, rather than keeping the local-unit and equalizer clauses as parallel ad
  hoc data in the main declaration;
- primitive data: the ringed space `X` and the source-facing stalkwise local-ring hypothesis;
- derived API: the degree-`1` cohomology group of the units sheaf and the ringed-space Picard
  group `Pic(X)`, compared by a theorem-level bijective additive map.

Source/core/bridge triage:
- `source-facing`: the ringed-space comparison `H¹(X, 𝒪_Xˣ) ≃ Pic(X)` under
  stalkwise local-ring hypotheses;
- `core/canonical`: `ringedSiteUnitsSheaf_H1_equiv_picardGroup`,
  `ringedSiteUnitsAddSheaf`, `ringedSitePicardGroup`, `IsLocallyRingedSite`,
  `RingedSpace.hasLocalUnitDichotomy_of_stalk_isLocalRing`, and
  `isIso_oneNeverZeroEqualizerMap_iff_stalkwise_nontrivial`;
- `bridge/view`: specialization of the ringed-site owners to the structure sheaf `X.sheaf`.
-/

private theorem pointGrothendieckTopology_sourcePointRing_nontrivial_of_stalk_isLocalRing
    (X : RingedSpace)
    (x : X)
    [IsLocalRing (X.presheaf.stalk x)] :
    Nontrivial (sourcePointRing X.sheaf (Opens.pointGrothendieckTopology x)) := by
  let e :
      ↑(sourcePointRing X.sheaf (Opens.pointGrothendieckTopology x)) ≃+*
        ↑(X.presheaf.stalk x) :=
    Iso.commRingCatIsoToRingEquiv (pointGrothendieckTopology_sheafFiber_obj_iso_stalk x X.sheaf)
  let _ : IsLocalRing (sourcePointRing X.sheaf (Opens.pointGrothendieckTopology x)) :=
    RingEquiv.isLocalRing e.symm
  infer_instance

/-- If all stalks of the structure sheaf of a ringed space are local rings, then the opens
ringed site is canonically locally ringed. -/
instance instOpensSheafIsLocallyRingedSiteOfStalkIsLocalRing
    (X : RingedSpace)
    [∀ x : X, IsLocalRing (X.presheaf.stalk x)] :
    IsLocallyRingedSite X.sheaf := by
  let _ : HasLocalUnitDichotomy (Opens.grothendieckTopology X) X.sheaf :=
    hasLocalUnitDichotomy_of_stalk_isLocalRing inferInstance
  let _ : IsIso (oneNeverZeroEqualizerMap X.sheaf) :=
    (GrothendieckTopology.isConservativePointFamily_iff
      (fun x : X ↦ Opens.pointGrothendieckTopology x)).1
        (Opens.isConservativeFamilyOfPoints_pointsGrothendieckTopology X)
        (oneNeverZeroEqualizerMap X.sheaf) <| by
          intro x
          exact
            (point_fiber_oneNeverZeroEqualizerMap_isIso_iff_nontrivial
              X.sheaf (Opens.pointGrothendieckTopology x)).2
              (pointGrothendieckTopology_sourcePointRing_nontrivial_of_stalk_isLocalRing
                X x)
  infer_instance

/-- Lemma 20.6.1: if all stalks of the structure sheaf of a ringed space are local rings, then
there exists a bijective additive comparison map from the first cohomology of the units sheaf
`𝒪_Xˣ` to the Picard group of `X`. This is the ringed-space specialization of the
theorem-level Chapter 21 owner `ringedSiteUnitsSheaf_H1_equiv_picardGroup`. -/
@[stacks 09NU]
theorem unitsSheaf_H1_equiv_picardGroup_of_stalk_isLocalRing
    (X : RingedSpace)
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x))
    [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat RingCat)]
    [(Opens.grothendieckTopology X).HasSheafCompose (forget AddCommGrpCat)]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
    [HasExt (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)]
    [MonoidalCategory (Modules X)] [SymmetricCategory (Modules X)] :
    ∃ e : ((ringedSiteUnitsAddSheaf X.sheaf).H 1) →+ Pic(X), Function.Bijective e := by
  let _ : ∀ x : X, IsLocalRing (X.presheaf.stalk x) := hlocal
  let _ : IsLocallyRingedSite X.sheaf := inferInstance
  let h :
      ∃ e : ((ringedSiteUnitsAddSheaf X.sheaf).H 1) →+ Pic(X), Function.Bijective e :=
    ringedSiteUnitsSheaf_H1_equiv_picardGroup (Opens.grothendieckTopology X) X.sheaf
  exact h

end AlgebraicGeometry.RingedSpace
