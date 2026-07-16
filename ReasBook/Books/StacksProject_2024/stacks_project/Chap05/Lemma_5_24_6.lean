import StacksProject_2024.stacks_project.Chap05.Lemma_5_24_4
import StacksProject_2024.stacks_project.Chap05.Lemma_5_24_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits

section

variable {J : Type v} [Category.{w} J] [IsCofiltered J]
variable {F : J ⥤ TopCat.{max v w}} [∀ j : J, SpectralSpace (F.obj j)]

/- Domain-style sampling for Lemma 5.24.6:
- primary domain: cofiltered inverse limits of spectral spaces, with descent of quasi-compact
  opens and eventual stagewise inclusion;
- inspected owner-level declarations:
  `open_eq_preimage_of_isLimit_of_isConstructible`,
  `constructible_eq_preimage_of_isLimit`,
  `limit_projection_preimage_subset_iff_exists_stage_preimage_subset`,
  `spectralSpace_of_isLimit_of_cofiltered_spectral_diagram`;
- best owner abstraction first: the spectral/constructible descent owner for part `(1)` is
  `open_eq_preimage_of_isLimit_of_isConstructible`, whose output already lives in
  `CompactOpens`; `limit_projection_preimage_subset_iff_exists_stage_preimage_subset` is the
  chapter-level owner for eventual stagewise inclusion in part `(2)`;
- primitive data: the cofiltered spectral diagram and the limit-side or stagewise `CompactOpens`;
- derived API: part `(1)` as the chosen-limit specialization of open constructible descent, then
  the common-refinement inclusion criterion and the finite union/intersection descent statements.

Source/core/bridge triage:
- `source-facing`: the numbered Lemma 5.24.6 statements about quasi-compact opens on the chosen
  inverse limit and their eventual stagewise behavior;
- `core/canonical`: `Topology.IsConstructible` together with `CompactOpens` and the chapter 5.24
  cofiltered-limit descent owners;
- `bridge/view`: part `(1)` is the chosen-limit specialization of
  `open_eq_preimage_of_isLimit_of_isConstructible`, turning a limit-side `CompactOpens` object into
  its stagewise `CompactOpens` ancestor.

The finite-family parts are stated over an arbitrary `Fintype` rather than `Fin n`: the source
mathematics uses only finiteness, so the `Fin n` encoding would be presentation-level bookkeeping
rather than primitive data.
-/

-- Proof sketch: a compact open subset of the inverse limit is constructible and open, so the
-- chapter-level spectral descent theorem `open_eq_preimage_of_isLimit_of_isConstructible`
-- descends it to a stagewise compact open.
/-- Lemma 5.24.6 (1): every quasi-compact open subset of the inverse limit of a cofiltered diagram
of spectral spaces with spectral transition maps is the pullback of a quasi-compact open subset
from some stage. -/
theorem compact_open_eq_preimage_of_limit
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    (W : CompactOpens ↥(limit F)) :
    ∃ (i : J) (Wi : CompactOpens (F.obj i)),
      (W : Set ↥(limit F)) = (limit.π F i) ⁻¹' (Wi : Set (F.obj i)) := by
  let C : Cone F := limit.cone F
  have hC : IsLimit C := by
    simpa [C] using limit.isLimit F
  haveI : SpectralSpace ↥C.pt :=
    spectralSpace_of_isLimit_of_cofiltered_spectral_diagram hC (fun {j k} a ↦ hF a)
  let W' : CompactOpens ↥C.pt := by
    simpa [C] using W
  have hW_constructible : IsConstructible (W' : Set ↥C.pt) :=
    W'.isCompact.isConstructible W'.isOpen
  have hdesc : ∃ (i : J) (Wi : CompactOpens (F.obj i)),
      C.π.app i ⁻¹' (Wi : Set (F.obj i)) = (W' : Set ↥C.pt) := by
    exact open_eq_preimage_of_isLimit_of_isConstructible hC hF hW_constructible W'.isOpen
  simpa [eq_comm, C, W'] using hdesc

-- Proof sketch: specialize
-- `limit_projection_preimage_subset_iff_exists_stage_preimage_subset` from Lemma `5.24.3` to the
-- constructibly closed set `Ui` and the constructibly open set `Uj`, then use cofilteredness to
-- compare the two stage indices on a common refinement.
/-- Lemma 5.24.6 (2): if the pullback of a quasi-compact open from one stage is contained in the
pullback of a quasi-compact open from another stage, then this inclusion already holds after
pullback to some common refinement stage. -/
theorem exists_common_refinement_of_preimage_subset
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i j : J} (Ui : CompactOpens (F.obj i)) (Uj : CompactOpens (F.obj j))
    (hsub : (limit.π F i) ⁻¹' (Ui : Set (F.obj i)) ⊆
      (limit.π F j) ⁻¹' (Uj : Set (F.obj j))) :
    ∃ (k : J) (a : k ⟶ i) (b : k ⟶ j),
      (F.map a) ⁻¹' (Ui : Set (F.obj i)) ⊆ (F.map b) ⁻¹' (Uj : Set (F.obj j)) := sorry

-- Proof sketch: descend the quasi-compact open on the limit to one stage by part `(1)`, then use
-- part `(2)` to descend each inclusion in the finite union and cofilteredness to dominate the
-- resulting finite set of stages by a single refinement.
/-- Lemma 5.24.6 (3): if the pullback of a quasi-compact open from a stage is a finite union of
pullbacks of quasi-compact opens from the same stage, then after pulling back along some morphism
to that stage the corresponding finite union identity already holds there. -/
theorem exists_stage_of_preimage_eq_iUnion
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i : J} {ι : Type u} [Fintype ι] (Ui : CompactOpens (F.obj i))
    (V : ι → CompactOpens (F.obj i))
    (hcover : (limit.π F i) ⁻¹' (Ui : Set (F.obj i)) =
      ⋃ t, (limit.π F i) ⁻¹' (V t : Set (F.obj i))) :
    ∃ (j : J) (a : j ⟶ i),
      (F.map a) ⁻¹' (Ui : Set (F.obj i)) = ⋃ t, (F.map a) ⁻¹' (V t : Set (F.obj i)) := sorry

-- Proof sketch: argue exactly as in part `(3)`, replacing finite unions by finite intersections
-- and using that inverse images commute with intersections.
/-- Lemma 5.24.6 (4): if the pullback of a quasi-compact open from a stage is a finite
intersection of pullbacks of quasi-compact opens from the same stage, then after pulling back
along some morphism to that stage the corresponding finite intersection identity already holds
there. -/
theorem exists_stage_of_preimage_eq_iInter
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i : J} {ι : Type u} [Fintype ι] (Ui : CompactOpens (F.obj i))
    (V : ι → CompactOpens (F.obj i))
    (hcover : (limit.π F i) ⁻¹' (Ui : Set (F.obj i)) =
      ⋂ t, (limit.π F i) ⁻¹' (V t : Set (F.obj i))) :
    ∃ (j : J) (a : j ⟶ i),
      (F.map a) ⁻¹' (Ui : Set (F.obj i)) = ⋂ t, (F.map a) ⁻¹' (V t : Set (F.obj i)) := sorry

end
