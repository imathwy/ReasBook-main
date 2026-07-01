import Mathlib
import stacks_project.Chap18.Definition_18_7_1
import stacks_project.Chap18.Definition_18_40_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open scoped RingedSite.Hom

universe u v

namespace CategoryTheory

/-
Domain-style sampling for Lemma 18.40.5:
- primary domain: locally ringed commutative ringed sites under inverse image and equivalence;
- sampled owner declarations:
  `IsLocallyRingedSite`,
  `RingedSite.ofCommRingSheaf`,
  `RingedSite.Hom.IsRingedEquivalence`,
  `RingedSite.Hom.toMorphismOfTopoi`;
- best owner abstraction:
  the equivalence case is naturally owned by a bundled morphism
  `f : RingedSite.ofCommRingSheaf J 𝒪 ⟶ RingedSite.ofCommRingSheaf K 𝒪'`
  together with the bundled ringed-equivalence class on `f`, while the raw inverse-image statement
  for a continuous functor remains the source-facing owner for the non-equivalence case, and the
  site-presented equivalence statement belongs to the bridge layer only after assuming the induced
  inverse-image functor on sheaves is an equivalence;
- primitive data:
  for part (1), the continuous functor `F` and the commutative structure sheaf `𝒪`;
  for part (2), the bundled ringed-site morphism `f` and its ringed-equivalence structure;
- derived API:
  transport across a structure-sheaf isomorphism, preservation of local ringedness by inverse
  image, and the site-presented bridge theorem with an equivalence hypothesis on the induced
  inverse-image functor on sheaves.

Source/core/bridge triage:
- `source-facing`: the inverse-image preservation statement of part (1);
- `core/canonical`: `IsLocallyRingedSite`;
- `bridge/view`: `RingedSite.ofCommRingSheaf` and the bundled ringed-equivalence class on a
  ringed-site morphism for the equivalence case, together with the site-presented
  inverse-image-equivalence bridge theorem.
-/

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Being locally ringed depends only on the isomorphism class of the commutative structure sheaf
on a fixed site. -/
-- Proof sketch: transport the two defining clauses of `IsLocallyRingedSite` across the sheaf
-- isomorphism. The equalizer/empty-cover condition and the local unit dichotomy are both stated
-- purely in terms of sections and restriction maps, so they are preserved under objectwise ring
-- isomorphisms induced by `e`.
theorem isLocallyRingedSite_iff_of_iso
    {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}} (e : 𝒪 ≅ 𝒪') :
    IsLocallyRingedSite 𝒪 ↔ IsLocallyRingedSite 𝒪' := sorry

end

namespace RingedSite.Hom

section

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [K.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}} {𝒪' : Sheaf K CommRingCat.{max u v}}

local notation "X" => RingedSite.ofCommRingSheaf J 𝒪
local notation "Y" => RingedSite.ofCommRingSheaf K 𝒪'

-- Proof sketch: one implication transports local ringedness along the structure-sheaf
-- isomorphism supplied by the ringed-equivalence hypothesis on `f`, after applying inverse-image
-- preservation to the base morphism. The converse applies the same argument to a quasi-inverse
-- ringed-site equivalence.
/-- Lemma 18.40.5 (2), owner form: a bundled equivalence of commutative ringed sites preserves and
reflects the locally ringed property. -/
theorem isLocallyRingedSite_iff_of_isRingedEquivalence
    (f : X ⟶ Y) [f.IsRingedEquivalence] :
    IsLocallyRingedSite 𝒪 ↔ IsLocallyRingedSite 𝒪' := sorry

end

end RingedSite.Hom

section

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (F : C ⥤ D) [Functor.IsContinuous F J K]
variable [((F.sheafPushforwardContinuous CommRingCat.{max u v} J K).IsRightAdjoint)]

-- Proof sketch: pull back the two defining clauses of `IsLocallyRingedSite J 𝒪` along the exact
-- inverse-image functor `F.sheafPullback CommRingCat J K`. Exactness preserves the empty sheaf,
-- the terminal sheaf, equalizers, products, isomorphisms, and epimorphisms, so the
-- `0 = 1`-implies-empty condition and the local unit dichotomy descend to the inverse-image
-- structure sheaf.
/-- Lemma 18.40.5 (1): for a site-presented morphism of topoi with inverse image induced by a
continuous functor `F : \mathcal C \to \mathcal C'`, if `(\mathcal C, \mathcal O)` is locally
ringed, then `(\mathcal C', F^{-1}\mathcal O)` is locally ringed. -/
theorem pullback_isLocallyRingedSite
    {𝒪 : Sheaf J CommRingCat.{max u v}} [IsLocallyRingedSite 𝒪] :
    IsLocallyRingedSite ((F.sheafPullback CommRingCat.{max u v} J K).obj 𝒪) := sorry

-- Proof sketch: combine the equivalence hypothesis on the induced inverse-image functor on
-- sheaves with the structure-sheaf isomorphism `α`, then apply the bundled owner theorem
-- `RingedSite.Hom.isLocallyRingedSite_iff_of_isRingedEquivalence` after packaging this data into
-- the corresponding site-presented ringed-topos equivalence.
/-- Lemma 18.40.5 (2), bridge form: for a site-presented equivalence of ringed topoi whose
induced inverse-image functor on sheaves is an equivalence and whose inverse-image structure sheaf
`F^{-1}\mathcal O` is identified with `\mathcal O'`, the locally ringed property is equivalent
for `(\mathcal C, \mathcal O)` and `(\mathcal C', \mathcal O')`. -/
theorem isLocallyRingedSite_iff_of_inverseImage_isEquivalence
    [Functor.IsEquivalence (F.sheafPullback (Type (max u v)) J K)]
    {𝒪 : Sheaf J CommRingCat.{max u v}} {𝒪' : Sheaf K CommRingCat.{max u v}}
    (α : (F.sheafPullback CommRingCat.{max u v} J K).obj 𝒪 ≅ 𝒪') :
    IsLocallyRingedSite 𝒪 ↔ IsLocallyRingedSite 𝒪' := sorry

end

end CategoryTheory
