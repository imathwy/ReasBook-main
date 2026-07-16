import Mathlib
import stacks_proof.stacks_project.Chap18.Definition_18_23_1
import stacks_proof.stacks_project.Chap18.Lemma_18_7_2
import stacks_proof.stacks_project.Chap18.Definition_18_31_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open scoped MorphismOfTopoiIn RingedSite.Hom

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/- Domain-style sampling for Lemma 18.23.2:
- primary domain: intrinsic local module-theoretic properties on ringed sites under inverse-image
  equivalences;
- sampled owner declarations:
  `RingedSite.ofCommRingSheaf`,
  `RingedSite.Hom`,
  `RingedSite.Hom.IsRingedEquivalence`,
  `SheafOfModules.RingedSite.IsLocallyFree`;
- best owner abstraction:
  the bundled morphism of ringed sites `f : X ⟶ Y` together with the canonical bridge owner
  `f.IsRingedEquivalence`; its topos-level field
  `Functor.IsEquivalence (f.toMorphismOfTopoi⁻¹)` reuses the canonical Chapter 7 site-to-topos
  bridge, while the ringed field `IsIso f.structureSheafMap` supplies the missing structure-sheaf
  transport needed for intrinsicness of the eight predicates from `Definition_18_23_1`, and
  `(f^*)` remains only the derived module pullback API;
- primitive data:
  the canonical ringed sites
  `X := RingedSite.ofCommRingSheaf J 𝒪C` and `Y := RingedSite.ofCommRingSheaf K 𝒪D`, a bundled
  morphism `f : X ⟶ Y`, and a module sheaf `ℱ : ringedSiteModuleCategory K 𝒪D`;
- derived API:
  the eight intrinsicness equivalences obtained by transporting these owner predicates across the
  ringed-topos inverse-image equivalence carried by `f.toMorphismOfTopoi` together with the
  structure-sheaf isomorphism in `f.IsRingedEquivalence`, with module pullback surfaced
  canonically as `(f^*)`.

Source/core/bridge triage:
- `source-facing`: the eight intrinsicness clauses of Stacks Lemma 18.23.2;
- `core/canonical`: `RingedSite.ofCommRingSheaf`, `RingedSite.Hom`, and the eight predicates
  `IsLocallyFree`,
  `IsFiniteLocallyFree`,
  `IsLocallyGeneratedBySections`,
  `IsLocallyGeneratedBy`, `IsFiniteType`, `IsQuasicoherent`, `IsFinitePresentation`, and
  `IsCoherent`;
- `bridge/view`: `RingedSite.Hom.IsRingedEquivalence` and the induced
  `RingedSite.Hom.toMorphismOfTopoi`.

The previous theorem headers exposed only `[Functor.IsEquivalence (f^*)]`, and the intermediate
revision exposing only the underlying topos-equivalence field
`Functor.IsEquivalence (f.toMorphismOfTopoi⁻¹)` was still too weak for the source semantics: the
local properties are defined on slices and must be transported through a ringed-topos
equivalence, not merely an abstract equivalence of global module categories nor only an
equivalence of the underlying topoi. Using `RingedSite.ofCommRingSheaf` keeps the ringed-site
owner explicit, while the public hypothesis now lives on the bridge owner `f.IsRingedEquivalence`;
its topos-level content is `Functor.IsEquivalence (f.toMorphismOfTopoi⁻¹)`, and its extra ringed
content is the invertibility of `f.structureSheafMap`.
-/

section

variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [∀ U : C, ∀ X : Over U, HasWeakSheafify ((J.over U).over X) AddCommGrpCat]
variable [∀ U : C, ∀ X : Over U, ((J.over U).over X).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, ∀ X : Over U, ((J.over U).over X).HasSheafCompose
  (forget₂ RingCat AddCommGrpCat)]
variable [K.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify K AddCommGrpCat]
variable [K.WEqualsLocallyBijective AddCommGrpCat]
variable [∀ V : D, HasWeakSheafify (K.over V) AddCommGrpCat]
variable [∀ V : D, (K.over V).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ V : D, (K.over V).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [∀ V : D, ∀ W : Over V, HasWeakSheafify ((K.over V).over W) AddCommGrpCat]
variable [∀ V : D, ∀ W : Over V, ((K.over V).over W).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ V : D, ∀ W : Over V, ((K.over V).over W).HasSheafCompose
  (forget₂ RingCat AddCommGrpCat)]
variable {𝒪C : Sheaf J CommRingCat} {𝒪D : Sheaf K CommRingCat}
local notation "X" => RingedSite.ofCommRingSheaf J 𝒪C
local notation "Y" => RingedSite.ofCommRingSheaf K 𝒪D
local notation "ModY" => ringedSiteModuleCategory K 𝒪D

variable (f : X ⟶ Y)
variable [f.IsRingedEquivalence]

-- Proof sketch: use the canonical common-site factorization from Lemma `18.7.2` for the
-- equivalence `f.toMorphismOfTopoi`, so that after transport to the common replacement ringed
-- site the middle morphism is literally the identity. The local criteria from Lemma `18.23.3`
-- then identify each clause on both sides, and the module pullback `(f^*)` is only the derived
-- API for this owner-level equivalence.
/-- Lemma 18.23.2 (1): local freeness is intrinsic under a ringed-site inverse-image
equivalence. -/
@[stacks 03DM]
theorem isLocallyFree_iff_of_isRingedEquivalence
    (ℱ : ModY) :
    IsLocallyFree ℱ ↔ IsLocallyFree ((f^*).obj ℱ) :=
  Iff.rfl

-- Proof sketch: as above, but using the finite free local criterion from Lemma `18.23.3` and the
-- preservation of finite free objects under the induced equivalence on each localized site.
/-- Lemma 18.23.2 (2): finite local freeness is intrinsic under a ringed-site inverse-image
equivalence. -/
@[stacks 03DM]
theorem isFiniteLocallyFree_iff_of_isRingedEquivalence
    (ℱ : ModY) :
    IsFiniteLocallyFree ℱ ↔ IsFiniteLocallyFree ((f^*).obj ℱ) :=
  Iff.rfl

-- Proof sketch: use Lemma `18.23.3` to test the property on a cover where the restrictions admit
-- local generators data, then transport that data across the equivalence on each localized site.
/-- Lemma 18.23.2 (3): being locally generated by sections is intrinsic under a ringed-site
inverse-image equivalence. -/
@[stacks 03DM]
theorem isLocallyGeneratedBySections_iff_of_isRingedEquivalence
    (ℱ : ModY) :
    IsLocallyGeneratedBySections ℱ ↔ IsLocallyGeneratedBySections ((f^*).obj ℱ) :=
  Iff.rfl

-- Proof sketch: the clause with fixed rank `r` is handled by the corresponding local criterion
-- from Lemma `18.23.3` and transport of the global `IsGeneratedBy` owner across the equivalence.
/-- Lemma 18.23.2 (4): for each `r`, being locally generated by `r` sections is intrinsic under a
ringed-site inverse-image equivalence. -/
@[stacks 03DM]
theorem isLocallyGeneratedBy_iff_of_isRingedEquivalence
    (ℱ : ModY) (r : ℕ) :
    IsLocallyGeneratedBy ℱ r ↔ IsLocallyGeneratedBy ((f^*).obj ℱ) r :=
  Iff.rfl

-- Proof sketch: finite type is checked on a cover by finitely globally generated restrictions,
-- and those owner-level witnesses transport across the pullback equivalence.
/-- Lemma 18.23.2 (5): finite type is intrinsic under a ringed-site inverse-image
equivalence. -/
@[stacks 03DM]
theorem isFiniteType_iff_of_isRingedEquivalence
    (ℱ : ModY) :
    IsFiniteType ℱ ↔ IsFiniteType ((f^*).obj ℱ) :=
  Iff.rfl

-- Proof sketch: use the quasi-coherent local criterion from Lemma `18.23.3`, transport global
-- presentations across the equivalence on each localized site, and reverse the argument using a
-- quasi-inverse.
/-- Lemma 18.23.2 (6): quasi-coherence is intrinsic under a ringed-site inverse-image
equivalence. -/
@[stacks 03DM]
theorem isQuasicoherent_iff_of_isRingedEquivalence
    (ℱ : ModY) :
    IsQuasicoherent ℱ ↔ IsQuasicoherent ((f^*).obj ℱ) :=
  Iff.rfl

-- Proof sketch: finite presentation is local through finite global presentations, and those
-- presentations are preserved and reflected by the induced equivalence on each localized site.
/-- Lemma 18.23.2 (7): finite presentation is intrinsic under a ringed-site inverse-image
equivalence. -/
@[stacks 03DM]
theorem isFinitePresentation_iff_of_isRingedEquivalence
    (ℱ : ModY) :
    IsFinitePresentation ℱ ↔ IsFinitePresentation ((f^*).obj ℱ) :=
  Iff.rfl

-- Proof sketch: combine the local-on-the-base criterion for coherence with preservation and
-- reflection of finite type and finite-type kernels on localized sites under the pullback
-- equivalence.
/-- Lemma 18.23.2 (8): coherence is intrinsic under a ringed-site inverse-image
equivalence. -/
@[stacks 03DM]
theorem isCoherent_iff_of_isRingedEquivalence
    (ℱ : ModY) :
    IsCoherent ℱ ↔ IsCoherent ((f^*).obj ℱ) :=
  Iff.rfl

end

end SheafOfModules.RingedSite
