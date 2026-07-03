import Mathlib
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_18_40_1 (from Chap18) -/
open CategoryTheory Opposite Limits

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type (max u v))]

/- Domain-style sampling for Lemma 18.40.1:
- primary domain: local surjectivity of morphisms of set-valued sheaves attached to the structure
  sheaf of a ringed site;
- sampled owner declarations:
  `HasLocalUnitDichotomy`,
  `Sheaf.IsLocallySurjective`,
  `GrothendieckTopology.sheafifiedRepresentableCoverMap`,
  `Limits.coprod.desc`,
  `Limits.prod.lift`;
- best owner abstraction: the intrinsic binary factorization morphism in `Sheaf J (Type _)`
  from the coproduct of two copies of `O ⨯ O` to `O ⨯ O`, where `O` is the underlying
  set-valued structure sheaf;
- primitive data: the two component morphisms `O ⨯ O ⟶ O ⨯ O` sending `(f, a)` to `(f, af)` and
  `(f, b)` to `(f, b(1 - f))`;
- derived API: local surjectivity of the canonical coproduct map and its sectionwise
  factorization reformulation.
-/

variable (𝒪 : Sheaf J CommRingCat.{max u v})

private abbrev underlyingTypeSheaf (𝒪 : Sheaf J CommRingCat.{max u v}) :
    Sheaf J (Type (max u v)) :=
  (sheafCompose J (forget CommRingCat)).obj 𝒪

local notation "O" => underlyingTypeSheaf 𝒪

private def binaryFactorizationLeftSecond : O ⨯ O ⟶ O :=
  { hom :=
      { app := fun U x ↦ by
          let a : 𝒪.obj.obj U := (prod.snd : O ⨯ O ⟶ O).hom.app U x
          let f : 𝒪.obj.obj U := (prod.fst : O ⨯ O ⟶ O).hom.app U x
          show 𝒪.obj.obj U
          exact a * f
        naturality := by
          intro U V f
          ext x
          have hsnd : (prod.snd : O ⨯ O ⟶ O).hom.app V ((O ⨯ O).obj.map f x) =
              (𝒪.obj.map f).hom ((prod.snd : O ⨯ O ⟶ O).hom.app U x) := by
            simpa using congr_fun ((prod.snd : O ⨯ O ⟶ O).hom.naturality f) x
          have hfst : (prod.fst : O ⨯ O ⟶ O).hom.app V ((O ⨯ O).obj.map f x) =
              (𝒪.obj.map f).hom ((prod.fst : O ⨯ O ⟶ O).hom.app U x) := by
            simpa using congr_fun ((prod.fst : O ⨯ O ⟶ O).hom.naturality f) x
          dsimp
          rw [hsnd, hfst]
          simp } }

private def binaryFactorizationRightSecond : O ⨯ O ⟶ O :=
  { hom :=
      { app := fun U x ↦ by
          let b : 𝒪.obj.obj U := (prod.snd : O ⨯ O ⟶ O).hom.app U x
          let f : 𝒪.obj.obj U := (prod.fst : O ⨯ O ⟶ O).hom.app U x
          show 𝒪.obj.obj U
          exact b * (1 - f)
        naturality := by
          intro U V f
          ext x
          have hsnd : (prod.snd : O ⨯ O ⟶ O).hom.app V ((O ⨯ O).obj.map f x) =
              (𝒪.obj.map f).hom ((prod.snd : O ⨯ O ⟶ O).hom.app U x) := by
            simpa using congr_fun ((prod.snd : O ⨯ O ⟶ O).hom.naturality f) x
          have hfst : (prod.fst : O ⨯ O ⟶ O).hom.app V ((O ⨯ O).obj.map f x) =
              (𝒪.obj.map f).hom ((prod.fst : O ⨯ O ⟶ O).hom.app U x) := by
            simpa using congr_fun ((prod.fst : O ⨯ O ⟶ O).hom.naturality f) x
          dsimp
          rw [hsnd, hfst]
          simp } }

private def binaryFactorizationLeft : O ⨯ O ⟶ O ⨯ O :=
  prod.lift prod.fst (binaryFactorizationLeftSecond 𝒪)

private def binaryFactorizationRight : O ⨯ O ⟶ O ⨯ O :=
  prod.lift prod.fst (binaryFactorizationRightSecond 𝒪)

local instance binaryFactorizationHasColimit : HasColimit (pair (O ⨯ O) (O ⨯ O)) := by
  let _ : HasColimitsOfShape (Discrete WalkingPair) (Type (max u v)) := inferInstance
  let _ : HasColimitsOfShape (Discrete WalkingPair) (Sheaf J (Type (max u v))) :=
    (Sheaf.instHasColimitsOfShape :
      HasColimitsOfShape (Discrete WalkingPair) (Sheaf J (Type (max u v))))
  infer_instance

/-- The binary factorization morphism from Stacks `18.40.1 (3)`, expressed as a morphism of
set-valued sheaves. With `O` the underlying set-valued sheaf of `𝒪`, this is the canonical
morphism `((O ⨯ O) ⨿ (O ⨯ O)) ⟶ (O ⨯ O)` whose left summand sends `(f, a)` to `(f, af)` and
whose right summand sends `(f, b)` to `(f, b(1 - f))`. -/
def binaryFactorizationMap : (O ⨯ O) ⨿ (O ⨯ O) ⟶ O ⨯ O :=
  coprod.desc (binaryFactorizationLeft 𝒪) (binaryFactorizationRight 𝒪)

variable {𝒪}

/-- Unfolding `Sheaf.IsLocallySurjective (binaryFactorizationMap 𝒪)` gives the sectionwise local
factorization formula from Stacks `18.40.1 (3)`. This remains companion API, while the main owner
clause is the local surjectivity of the named sheaf morphism. -/
theorem isLocallySurjective_binaryFactorizationMap_iff :
    Sheaf.IsLocallySurjective (binaryFactorizationMap 𝒪) ↔
      ∀ (U : C) (f c : 𝒪.obj.obj (op U)),
        ∃ S : J.Cover U, ∀ I : S.Arrow,
          (∃ a : 𝒪.obj.obj (op I.Y),
              (𝒪.obj.map I.f.op).hom c = a * (𝒪.obj.map I.f.op).hom f) ∨
            ∃ b : 𝒪.obj.obj (op I.Y),
              (𝒪.obj.map I.f.op).hom c = b * (1 - (𝒪.obj.map I.f.op).hom f) := sorry

-- Proof sketch: `(1) → (2)` is the induction on the number of generators from the source text.
-- `(2) → (1)` is the singleton case applied to the finite set `{f, 1 - f}`. Clause `(3)` is the
-- owner-level local-surjectivity statement for `binaryFactorizationMap 𝒪`.
/-- Lemma 18.40.1: for a ringed site `(\mathcal C, \mathcal O)`, the local dichotomy that every
section is locally either invertible or complementary-invertible, the local unit-ideal criterion
for finitely many sections, and the local surjectivity of the binary factorization map are
equivalent. -/
theorem ringed_site_local_unit_tfae
    (𝒪 : Sheaf J CommRingCat) :
    List.TFAE [
      HasLocalUnitDichotomy J 𝒪,
      ∀ (U : C) (s : Set (𝒪.obj.obj (op U))), s.Finite → s.Nonempty →
        Ideal.span s = ⊤ →
          ∃ S : J.Cover U, ∀ I : S.Arrow,
            ∃ g ∈ s, IsUnit ((𝒪.obj.map I.f.op).hom g),
      Sheaf.IsLocallySurjective (binaryFactorizationMap 𝒪)
    ] := sorry

end CategoryTheory

/-! ### Lemma_18_40_2 (from Chap18) -/
open CategoryTheory Opposite

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/- Domain-style sampling for Lemma 18.40.2:
- primary domain: point stalks of sheaves of commutative rings on a site, together with enough
  points and the chapter-local unit-dichotomy owner for ringed sites;
- sampled owner declarations:
  `HasLocalUnitDichotomy`,
  `GrothendieckTopology.Point.sheafFiber`,
  `sourcePointRing`,
  `GrothendieckTopology.HasEnoughPoints`,
  `IsLocalRing.of_isUnit_or_isUnit_one_sub_self`;
- best owner abstraction: the source-facing local section hypothesis is the chapter owner
  `HasLocalUnitDichotomy J 𝒪`; the chapter stalk-ring owner is `sourcePointRing`, so the theorem
  surface should use that owner directly rather than repeating the full typed fiber expression;
- primitive data: the sheaf `𝒪` and the point `p`;
- derived API: the stalkwise “zero or local” conclusion and its enough-points equivalence.

Source/core/bridge triage:
- `source-facing`: the forward implication and the enough-points equivalence below;
- `core/canonical`: `GrothendieckTopology.Point.sheafFiber` and
  `GrothendieckTopology.HasEnoughPoints`;
- `bridge/view`: `HasLocalUnitDichotomy`, the chapter stalk-ring bridge `sourcePointRing`, and the
  local-ring dichotomy on stalks.

The previous single conjunction-valued theorem repeated both the local-dichotomy hypothesis and the
raw stalk expression. This file should reuse the existing chapter owners and expose the two source-
facing clauses atomically.
-/

-- Proof sketch: represent a stalk element by a section, apply the local
-- invertibility/complement-invertibility cover from `HasLocalUnitDichotomy J 𝒪`, and use the point
-- axiom to refine to one member of the cover. This shows that every element of the stalk ring is
-- either a unit or has unit complement; Lemma `10.18.3` then yields that the stalk ring is either
-- trivial or local.
/-- Lemma 18.40.2, forward direction: if every local section is locally either a unit or has unit
complement, then every point stalk is either the zero ring or a local ring. -/
theorem stalkwise_zero_or_local_of_hasLocalUnitDichotomy
    (𝒪 : Sheaf J CommRingCat.{w}) (h : HasLocalUnitDichotomy J 𝒪)
    (p : J.Point) :
    Subsingleton (sourcePointRing 𝒪 p) ∨ IsLocalRing (sourcePointRing 𝒪 p) := sorry

-- Proof sketch: use Lemma `18.40.1` to identify `HasLocalUnitDichotomy J 𝒪` with local
-- surjectivity of the canonical binary factorization map, check this map is stalkwise surjective
-- because each stalk ring is zero or local by Lemma `10.18.3`, and then reflect local
-- surjectivity from stalks using enough points.
/-- Lemma 18.40.2: if the site has enough points, then the local unit dichotomy is equivalent to
every point stalk being either the zero ring or a local ring. -/
theorem hasLocalUnitDichotomy_iff_stalkwise_zero_or_local
    [GrothendieckTopology.HasEnoughPoints.{w} J]
    (𝒪 : Sheaf J CommRingCat.{w}) :
    HasLocalUnitDichotomy J 𝒪 ↔
      ∀ p : J.Point,
        Subsingleton (sourcePointRing 𝒪 p) ∨ IsLocalRing (sourcePointRing 𝒪 p) := sorry

end CategoryTheory

/-! ### Lemma_18_40_3 (from Chap18) -/
open CategoryTheory Opposite Limits

universe u v

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-
Domain-style sampling for Lemma 18.40.3:
- primary domain: point stalks of sheaves of commutative rings on a site, together with
  conservativity of point-fiber functors under enough points;
- sampled relevant declarations:
  `oneNeverZeroEqualizerMap`,
  `GrothendieckTopology.Point.sheafFiber`,
  `sourcePointRing`,
  `point_stalk_ring`,
  `GrothendieckTopology.HasEnoughPoints.exists_objectProperty`;
- best owner abstraction: the source-facing chapter map `oneNeverZeroEqualizerMap 𝒪`, with the
  stalk condition expressed through the chapter bridge owner `sourcePointRing 𝒪 p`, which is the
  commutative-ring view of `GrothendieckTopology.Point.sheafFiber`; `point_stalk_ring` is the
  presheaf-level ring-stalk companion in the same domain;
- primitive data: the sheaf `𝒪` and the point `p`;
- derived API: stalkwise nontriviality and the enough-points reflection equivalence.

Source/core/bridge triage:
- `source-facing`: the implication from the `18.40.2.1` isomorphism to nontriviality of every
  stalk, and the converse under enough points;
- `core/canonical`: `oneNeverZeroEqualizerMap`, `Point.sheafFiber`, and the enough-points
  conservativity machinery;
- `bridge/view`: the earlier ring-valued stalk abbreviations `sourcePointRing` and
  `point_stalk_ring`, which are derived views of `Point.sheafFiber` / `Point.presheafFiber`.

The old single conjunction-valued theorem bundled two mathematically separate clauses and repeated
the raw stalk object expression. This file should expose the two source-facing clauses as atomic
theorems, while stating the stalk condition through the canonical chapter bridge `sourcePointRing`.
-/

-- Proof sketch: apply the stalk functor at a point `p` to the canonical morphism
-- `\emptyset^\# \to \operatorname{Equalizer}(0,1 : * \to \mathcal O)`. The source stalk remains
-- initial, while the target stalk identifies with the equalizer of `0, 1 : PUnit ⟶ \mathcal O_p`,
-- which is empty exactly when `0 ≠ 1` in the stalk ring, i.e. exactly when the stalk is
-- nontrivial. This gives `(1) → (2)`. If `J` has enough points, then the stalk functors are
-- conservative on sheaves, so the converse follows by checking that the displayed map is an
-- isomorphism on every point stalk.
/-- Lemma 18.40.3, forward direction: if the canonical morphism
`\emptyset^\# \to \operatorname{Equalizer}(0,1 : * \to \mathcal O)` from `18.40.2.1` is an
isomorphism, then every point stalk `\mathcal O_p` is nonzero. -/
theorem stalkwise_nontrivial_of_isIso_oneNeverZeroEqualizerMap
    (𝒪 : Sheaf J CommRingCat.{max u v}) (h : IsIso (oneNeverZeroEqualizerMap 𝒪))
    (p : GrothendieckTopology.Point.{max u v} J) :
    Nontrivial (sourcePointRing 𝒪 p) := sorry

/-- Lemma 18.40.3: if `(\mathcal C, J)` has enough points, then the canonical morphism
`\emptyset^\# \to \operatorname{Equalizer}(0,1 : * \to \mathcal O)` from `18.40.2.1` is an
isomorphism exactly when every point stalk `\mathcal O_p` is nonzero. -/
theorem isIso_oneNeverZeroEqualizerMap_iff_stalkwise_nontrivial
    [GrothendieckTopology.HasEnoughPoints.{max u v} J]
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    IsIso (oneNeverZeroEqualizerMap 𝒪) ↔
      ∀ p : GrothendieckTopology.Point.{max u v} J,
        Nontrivial (sourcePointRing 𝒪 p) := sorry

end CategoryTheory

/-! ### Definition_18_40_4 (from Chap18) -/
open CategoryTheory Opposite Limits

noncomputable section

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Every local section is locally either a unit or has unit complement. -/
class HasLocalUnitDichotomy
    (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{w}) : Prop where
  local_unit_dichotomy :
    ∀ (U : C) (f : 𝒪.obj.obj (op U)),
      ∃ S : J.Cover U, ∀ I : S.Arrow,
        IsUnit ((𝒪.obj.map I.f.op).hom f) ∨
          IsUnit (1 - (𝒪.obj.map I.f.op).hom f)

/-- Definition 18.40.4: a commutative ringed site `(\mathcal C, \mathcal O)` is locally ringed
if the canonical morphism `\emptyset^\# \to \operatorname{Equalizer}(0,1 : * \to \mathcal O)` of
`18.40.2.1` is an isomorphism and the local unit dichotomy from Lemma `18.40.1` holds. -/
class IsLocallyRingedSite (𝒪 : Sheaf J CommRingCat.{max u v}) : Prop
    extends IsIso (oneNeverZeroEqualizerMap 𝒪), HasLocalUnitDichotomy J 𝒪

/-- Any commutative ringed site satisfying the `18.40.2.1` isomorphism and the local unit
dichotomy carries the canonical locally ringed-site instance. -/
instance instIsLocallyRingedSiteOfConditions
    (𝒪 : Sheaf J CommRingCat.{max u v})
    [IsIso (oneNeverZeroEqualizerMap 𝒪)]
    [HasLocalUnitDichotomy J 𝒪] :
    IsLocallyRingedSite 𝒪 :=
  { toIsIso := inferInstance
    toHasLocalUnitDichotomy := inferInstance }

end CategoryTheory

/-! ### Lemma_18_40_5 (from Chap18) -/
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

/-! ### Definition_18_40_6 (from Chap18) -/
open CategoryTheory Opposite

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

end CategoryTheory

/- Domain-style sampling for Definition 18.40.6:
- primary domain: locally ringed Grothendieck sites and their site-presented ringed topoi;
- sampled relevant declarations:
  `CategoryTheory.IsLocallyRingedSite`,
  `CategoryTheory.oneNeverZeroEqualizerMap`,
  `CategoryTheory.instIsLocallyRingedSiteOfConditions`,
  `CategoryTheory.ringed_site_local_unit_tfae`;
- owner abstraction: the chapter owner is `CategoryTheory.IsLocallyRingedSite`, introduced in
  `Definition_18_40_4`;
- primitive data: the empty-equalizer isomorphism from `18.40.2.1` and the local unit dichotomy;
- derived API: the site-presented topos reading of the same owner, and TFAE reformulations of the
  local unit dichotomy.

Source/core/bridge triage:
- `source-facing`: the Stacks definition that a site-presented ringed topos is locally ringed;
- `core/canonical`: `CategoryTheory.IsLocallyRingedSite`;
- `bridge/view`: the observation that for a presented topos `(\mathit{Sh}(\mathcal C), \mathcal O)`,
  no second owner beyond the presenting site predicate is needed.

The reusable auxiliary owner `CategoryTheory.HasLocalUnitDichotomy` already lives in
`Definition_18_40_4`, so this numbered item is recall-only: it reuses the existing owner
`CategoryTheory.IsLocallyRingedSite` instead of introducing parallel `IsLocallyRingedSite` or
`IsLocallyRingedTopos` declarations. -/

/- Definition 18.40.6: a ringed topos `(\mathit{Sh}(\mathcal C), \mathcal O)` is locally ringed
exactly when the presenting ringed site `(\mathcal C, \mathcal O)` satisfies the canonical chapter
owner predicate `CategoryTheory.IsLocallyRingedSite`. -/
recall CategoryTheory.IsLocallyRingedSite

/-! ### Lemma_18_40_7 (from Chap18) -/
open CategoryTheory Opposite

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [∀ U : C, ∀ X : Over U, HasWeakSheafify ((J.over U).over X) AddCommGrpCat.{max u v}]
variable [∀ U : C, ∀ X : Over U, ((J.over U).over X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : C, ∀ X : Over U, ((J.over U).over X).HasSheafCompose
  (forget₂ RingCat AddCommGrpCat)]

local notation "Mod" => ringedSiteModuleCategory J 𝒪

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]

/- Domain-style sampling for Lemma 18.40.7:
- primary domain: rank-one finite locally free modules and invertible modules on a ringed site;
- sampled owner declarations:
  `SheafOfModules.RingedSite.IsFiniteLocallyFreeOfRank`,
  `SheafOfModules.RingedSite.IsInvertible`,
  `CategoryTheory.HasLocalUnitDichotomy`,
  `CategoryTheory.IsLocallyRingedSite`;
- best owner abstractions:
  the source-facing clauses should be expressed directly in terms of the Chapter 18 owners
  `IsFiniteLocallyFreeOfRank`, `IsInvertible`, and the local-dichotomy owner
  `HasLocalUnitDichotomy`, rather than by repeating the latter as an ad hoc quantified hypothesis;
- primitive data:
  the module `ℒ` and the ambient local unit dichotomy on the structure sheaf;
- derived API:
  the invertibility instance for rank-one locally free modules and the converse rank-one local
  freeness statement under the local unit dichotomy.

Source/core/bridge triage:
- `source-facing`: the two clauses of Stacks Lemma 18.40.7;
- `core/canonical`: `IsFiniteLocallyFreeOfRank`, `IsInvertible`,
  `CategoryTheory.HasLocalUnitDichotomy`;
- `bridge/view`: the local unit dichotomy is reused through its chapter owner, not restated as a
  parallel quantified parameter.
-/

-- Proof sketch: for a rank-one local trivialization, the evaluation map
-- `\mathcal L \otimes_{\mathcal O} \mathcal H\!\mathit{om}_{\mathcal O}(\mathcal L, \mathcal O)
-- \to \mathcal O` is locally identified with the standard evaluation map for
-- `\mathcal O_U`, hence is an isomorphism on a cover; Lemma `18.32.2` then gives invertibility.
/-- Lemma 18.40.7 (1): on a ringed site, a locally free `\mathcal O`-module of rank `1` is
invertible. -/
instance isInvertible_of_isFiniteLocallyFreeOfRank_one
    (ℒ : Mod)
    [IsFiniteLocallyFreeOfRank 1 ℒ] :
    IsInvertible ℒ := sorry

-- Proof sketch: by Lemma `18.32.2`, an invertible module is locally a direct summand of a finite
-- free module. Over a cover satisfying the local unit-dichotomy for the structure sheaf, the
-- corresponding idempotent matrices split as finite locally free modules of constant rank, and
-- invertibility forces that local rank to be `1`.
/-- Lemma 18.40.7 (2): if every section of the structure sheaf is locally either invertible or has
invertible complement, then every invertible `\mathcal O`-module is locally free of rank `1`. -/
theorem isFiniteLocallyFreeOfRank_one_of_isInvertible_of_local_unit_dichotomy
    (ℒ : Mod)
    [IsInvertible ℒ]
    [HasLocalUnitDichotomy J 𝒪] :
    IsFiniteLocallyFreeOfRank 1 ℒ := sorry

end SheafOfModules.RingedSite

/-! ### Lemma_18_40_8 (from Chap18) -/
open CategoryTheory Opposite

noncomputable section

universe u

/-
Domain-style sampling for Lemma 18.40.8:
- primary domain: locally ringed morphisms of site-presented topoi, with the induced stalk maps
  viewed through both the source-side cartesian-units condition and the ring-theoretic bridge
  predicate `IsLocalHom`;
- sampled owner declarations:
  `IsLocallyRingedSite`,
  `IsLocalHom`,
  `inverseImageUnitsCartesianForLocallyRingedMorphism`,
  `unitsSquareCartesianForLocallyRingedMorphism`,
  `CategoryTheory.IsMorphismOfLocallyRingedTopoi`;
- best owner abstraction: the source-facing Chapter 18 owner is the global cartesian-units
  condition `inverseImageUnitsCartesianForLocallyRingedMorphism`, interpreted in the locally
  ringed setting via `IsLocallyRingedSite`; the stalkwise predicate `IsLocalHom` is only a bridge
  reformulation and becomes the textbook local-ring-homomorphism condition only after separately
  knowing the relevant stalk rings are local;
- primitive data: the unbundled inverse-image structure-sheaf morphism `fSharp`, together with
  the ambient locally ringed-site hypotheses when the source text speaks about local ring
  homomorphisms on stalks;
- derived API: the induced objectwise maps `fSharp.hom.app (op U)`, the stalk maps
  `p.sheafFiber.map fSharp`, the objectwise/stalkwise cartesian-units conditions, and the
  `IsLocalHom` bridge criterion on those stalk maps.

Source/core/bridge triage:
- `source-facing`: the sectionwise-to-stalkwise implications and conservative-family criteria of
  Lemma 18.40.8, with clauses `(3)` and `(5)` read in the locally ringed setting;
- `core/canonical`: `IsLocallyRingedSite`,
  `inverseImageUnitsCartesianForLocallyRingedMorphism`, and
  `unitsSquareCartesianForLocallyRingedMorphism`;
- `bridge/view`: the direct stalkwise map `p.sheafFiber.map fSharp` and its ring-theoretic
  `IsLocalHom` reformulation.

This file should therefore reuse the existing Chapter 18 owner for the global units-square
condition, and keep the direct `IsLocalHom` reformulation only as bridge data rather than as the
main source-facing locally ringed statement.
-/

section

variable {R : Type u} {S : Type u} [CommRing R] [CommRing S]

-- Proof sketch: an element of the pullback is a source element whose image is a unit; lifting it
-- to a source unit is exactly the unit-reflection property, namely `IsLocalHom φ`.
/-- The units square for a ring map is cartesian exactly when the map reflects units. -/
theorem unitsSquareCartesian_iff_isLocalHom (φ : R →+* S) :
    unitsSquareCartesianForLocallyRingedMorphism φ ↔ IsLocalHom φ := sorry

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

variable (F : D ⥤ C) [Functor.IsContinuous F JD JC]
variable [(F.sheafPushforwardContinuous CommRingCat.{u} JD JC).IsRightAdjoint]
variable (𝒪C : Sheaf JC CommRingCat.{u}) (𝒪D : Sheaf JD CommRingCat.{u})

local notation "f⁻¹𝒪" => inverseImageStructureSheafForLocallyRingedMorphism F 𝒪D

variable (fSharp : f⁻¹𝒪 ⟶ 𝒪C)

-- Proof sketch: taking the stalk at a point preserves finite limits, so an objectwise cartesian
-- units square on the source site yields a cartesian units square on every stalk.
/-- Lemma 18.40.8 (1): the cartesian units square on the inverse-image structure sheaf implies the
corresponding cartesian units square on every stalk. -/
theorem inverseImageUnitsCartesian_implies_stalkUnitsCartesian :
    inverseImageUnitsCartesianForLocallyRingedMorphism F 𝒪C 𝒪D fSharp →
      ∀ p : GrothendieckTopology.Point.{u} JC,
        unitsSquareCartesianForLocallyRingedMorphism ((p.sheafFiber.map fSharp).hom) := sorry

-- Proof sketch: with enough points, cartesianness of the units square can be checked stalkwise,
-- since the comparison morphism to the pullback is an isomorphism exactly when it is so on all
-- stalks.
/-- Lemma 18.40.8 (2): if the source site has enough points, the cartesian units square condition
for `f^\sharp` is equivalent to the stalkwise cartesian units square condition. -/
theorem inverseImageUnitsCartesian_iff_stalkUnitsCartesian_of_hasEnoughPoints
    [GrothendieckTopology.HasEnoughPoints.{u} JC] :
    inverseImageUnitsCartesianForLocallyRingedMorphism F 𝒪C 𝒪D fSharp ↔
      ∀ p : GrothendieckTopology.Point.{u} JC,
        unitsSquareCartesianForLocallyRingedMorphism ((p.sheafFiber.map fSharp).hom) := sorry

-- Proof sketch: for each point, the displayed stalk square is cartesian exactly when the stalk map
-- reflects units, which is precisely the owner predicate `IsLocalHom`.
/-- Companion bridge: the stalkwise cartesian units square condition is equivalent to the
ring-theoretic unit-reflection predicate `IsLocalHom` on the induced stalk maps. By itself this
does not assert that the stalk rings are local. -/
theorem stalkUnitsCartesian_iff_stalkMapsAreLocalHom :
    (∀ p : GrothendieckTopology.Point.{u} JC,
      unitsSquareCartesianForLocallyRingedMorphism ((p.sheafFiber.map fSharp).hom)) ↔
      ∀ p : GrothendieckTopology.Point.{u} JC,
        IsLocalHom ((p.sheafFiber.map fSharp).hom) := sorry

-- Proof sketch: after assuming both structure sheaves are locally ringed, every source and target
-- stalk ring is local, so the previous `IsLocalHom` bridge becomes the textbook local-ring-map
-- condition on stalks.
/-- Lemma 18.40.8 (3): if both structure sheaves define locally ringed sites, then the stalkwise
cartesian units square condition is equivalent to requiring the induced stalk maps to be local
ring homomorphisms. -/
theorem stalkUnitsCartesian_iff_stalkMapsAreLocal
    [IsLocallyRingedSite 𝒪C] [IsLocallyRingedSite 𝒪D] :
    (∀ p : GrothendieckTopology.Point.{u} JC,
      unitsSquareCartesianForLocallyRingedMorphism ((p.sheafFiber.map fSharp).hom)) ↔
      ∀ p : GrothendieckTopology.Point.{u} JC,
        IsLocalRing (sourcePointRing f⁻¹𝒪 p) ∧
          IsLocalRing (sourcePointRing 𝒪C p) ∧
        IsLocalHom ((p.sheafFiber.map fSharp).hom) := sorry

variable (P : ObjectProperty (GrothendieckTopology.Point.{u} JC))

-- Proof sketch: apply conservativity of the chosen family of point functors to the comparison map
-- from `f^{-1}(\mathcal O_\mathcal D^*)` to the pullback sheaf; if all stalk squares in the
-- family are cartesian, then the comparison is an isomorphism globally.
/-- Lemma 18.40.8 (4): if a conservative family of points of the source site satisfies the
stalkwise cartesian units square condition, then the global units square for `f^\sharp` is
cartesian. -/
theorem inverseImageUnitsCartesian_of_stalkUnitsCartesian_of_conservativeFamily
    (hP : P.IsConservativeFamilyOfPoints)
    (h : ∀ p : GrothendieckTopology.Point.{u} JC, P p →
      unitsSquareCartesianForLocallyRingedMorphism ((p.sheafFiber.map fSharp).hom)) :
    inverseImageUnitsCartesianForLocallyRingedMorphism F 𝒪C 𝒪D fSharp := sorry

-- Proof sketch: convert the stalkwise `IsLocalHom` hypothesis into the stalkwise cartesian units
-- square hypothesis using the previous bridge equivalence, then apply the conservative-family
-- criterion.
/-- Companion bridge: if a conservative family of source points yields stalk maps satisfying
`IsLocalHom`, then the global units square for `f^\sharp` is cartesian. This is the ring-theoretic
bridge underlying Lemma 18.40.8 (5). -/
theorem inverseImageUnitsCartesian_of_stalkMapsAreLocalHom_of_conservativeFamily
    (hP : P.IsConservativeFamilyOfPoints)
    (h : ∀ p : GrothendieckTopology.Point.{u} JC, P p →
      IsLocalHom ((p.sheafFiber.map fSharp).hom)) :
    inverseImageUnitsCartesianForLocallyRingedMorphism F 𝒪C 𝒪D fSharp := sorry

-- Proof sketch: in the locally ringed setting, the stalk hypotheses assert that the induced maps
-- are local ring homomorphisms, and hence satisfy the `IsLocalHom` bridge criterion; the previous
-- companion theorem then yields the canonical owner condition that `f^\sharp` defines a morphism
-- of locally ringed topoi.
/-- Lemma 18.40.8 (5): if both structure sheaves define locally ringed sites and a conservative
family of source points yields local ring maps on the stalks of `f^\sharp`, then the global units
square for `f^\sharp` is cartesian, equivalently `f^\sharp` is a morphism of locally ringed
topoi. -/
theorem isMorphismOfLocallyRingedTopoi_of_stalkMapsAreLocal_of_conservativeFamily
    [IsLocallyRingedSite 𝒪C] [IsLocallyRingedSite 𝒪D]
    (hP : P.IsConservativeFamilyOfPoints)
    (h : ∀ p : GrothendieckTopology.Point.{u} JC, P p →
      IsLocalRing (sourcePointRing f⁻¹𝒪 p) ∧
        IsLocalRing (sourcePointRing 𝒪C p) ∧
      IsLocalHom ((p.sheafFiber.map fSharp).hom)) :
    IsMorphismOfLocallyRingedTopoi F 𝒪C 𝒪D fSharp := sorry

end

/-! ### Definition_18_40_9 (from Chap18) -/
open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

/-- The inverse-image commutative structure sheaf attached to a site-presented morphism of
topoi. -/
abbrev inverseImageStructureSheafForLocallyRingedMorphism
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (F : D ⥤ C) [Functor.IsContinuous F JD JC]
    [(F.sheafPushforwardContinuous CommRingCat.{max u v} JD JC).IsRightAdjoint]
    (𝒪D : Sheaf JD CommRingCat.{max u v}) :
    Sheaf JC CommRingCat.{max u v} :=
  (F.sheafPullback CommRingCat.{max u v} JD JC).obj 𝒪D

/-- The set-theoretic pullback of the units inclusion along a commutative ring homomorphism. -/
def unitsSquarePullbackForLocallyRingedMorphism
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :=
  { x : Sˣ × R // (x.1 : S) = φ x.2 }

/-- The canonical comparison from source units to the pullback of the units square. -/
def unitsSquareComparisonForLocallyRingedMorphism
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :
    Rˣ → unitsSquarePullbackForLocallyRingedMorphism φ :=
  fun u ↦ ⟨⟨Units.map φ u, (u : R)⟩, rfl⟩

/-- The units square of a commutative ring map is cartesian when the canonical comparison to the
set-theoretic pullback is bijective. -/
def unitsSquareCartesianForLocallyRingedMorphism
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) : Prop :=
  Function.Bijective (unitsSquareComparisonForLocallyRingedMorphism φ)

/-- The inverse-image units square is cartesian when it is objectwise cartesian on every object of
the source site. -/
def inverseImageUnitsCartesianForLocallyRingedMorphism
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (F : D ⥤ C) [Functor.IsContinuous F JD JC]
    [(F.sheafPushforwardContinuous CommRingCat.{max u v} JD JC).IsRightAdjoint]
    (𝒪C : Sheaf JC CommRingCat.{max u v}) (𝒪D : Sheaf JD CommRingCat.{max u v})
    (fSharp : (F.sheafPullback CommRingCat.{max u v} JD JC).obj 𝒪D ⟶ 𝒪C) : Prop :=
  ∀ U : C,
    unitsSquareCartesianForLocallyRingedMorphism ((fSharp.hom.app (Opposite.op U)).hom)

/-- Definition 18.40.9 (1): a site-presented morphism of locally ringed topoi is a morphism
whose inverse-image structure-sheaf map makes the units square
`f^{-1}(\mathcal O_\mathcal D^\times) \to \mathcal O_\mathcal C^\times` over
`f^{-1}\mathcal O_\mathcal D \to \mathcal O_\mathcal C` cartesian. -/
class IsMorphismOfLocallyRingedTopoi
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (F : D ⥤ C) [Functor.IsContinuous F JD JC]
    [(F.sheafPushforwardContinuous CommRingCat.{max u v} JD JC).IsRightAdjoint]
    (𝒪C : Sheaf JC CommRingCat.{max u v}) (𝒪D : Sheaf JD CommRingCat.{max u v})
    [IsLocallyRingedSite 𝒪C] [IsLocallyRingedSite 𝒪D]
    (fSharp : (F.sheafPullback CommRingCat.{max u v} JD JC).obj 𝒪D ⟶ 𝒪C) : Prop where
  /-- The inverse-image units square attached to the structure-sheaf map is cartesian. -/
  inverseImage_units_cartesian :
    inverseImageUnitsCartesianForLocallyRingedMorphism F 𝒪C 𝒪D fSharp

/-- A morphism of locally ringed topoi carries the canonical inverse-image cartesian-units
condition. -/
instance
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (F : D ⥤ C) [Functor.IsContinuous F JD JC]
    [(F.sheafPushforwardContinuous CommRingCat.{max u v} JD JC).IsRightAdjoint]
    (𝒪C : Sheaf JC CommRingCat.{max u v}) (𝒪D : Sheaf JD CommRingCat.{max u v})
    [IsLocallyRingedSite 𝒪C] [IsLocallyRingedSite 𝒪D]
    (fSharp : (F.sheafPullback CommRingCat.{max u v} JD JC).obj 𝒪D ⟶ 𝒪C)
    [IsMorphismOfLocallyRingedTopoi F 𝒪C 𝒪D fSharp] :
    inverseImageUnitsCartesianForLocallyRingedMorphism F 𝒪C 𝒪D fSharp :=
  IsMorphismOfLocallyRingedTopoi.inverseImage_units_cartesian

-- Proof sketch: unpack the class field in one direction, and in the other direction rebuild the
-- class from the cartesian-units hypothesis.
/-- A morphism of locally ringed topoi is equivalently characterized by the cartesianness of its
inverse-image units square. -/
theorem isMorphismOfLocallyRingedTopoi_iff
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (F : D ⥤ C) [Functor.IsContinuous F JD JC]
    [(F.sheafPushforwardContinuous CommRingCat.{max u v} JD JC).IsRightAdjoint]
    (𝒪C : Sheaf JC CommRingCat.{max u v}) (𝒪D : Sheaf JD CommRingCat.{max u v})
    [IsLocallyRingedSite 𝒪C] [IsLocallyRingedSite 𝒪D]
    (fSharp : (F.sheafPullback CommRingCat.{max u v} JD JC).obj 𝒪D ⟶ 𝒪C) :
    IsMorphismOfLocallyRingedTopoi F 𝒪C 𝒪D fSharp ↔
      inverseImageUnitsCartesianForLocallyRingedMorphism F 𝒪C 𝒪D fSharp := sorry

/-- Definition 18.40.9 (2): in the site-presented setting, a morphism of locally ringed sites is
simply a morphism of locally ringed topoi for the associated morphism of topoi. -/
abbrev IsMorphismOfLocallyRingedSites
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (F : D ⥤ C) [Functor.IsContinuous F JD JC]
    [(F.sheafPushforwardContinuous CommRingCat.{max u v} JD JC).IsRightAdjoint]
    (𝒪C : Sheaf JC CommRingCat.{max u v}) (𝒪D : Sheaf JD CommRingCat.{max u v})
    [IsLocallyRingedSite 𝒪C] [IsLocallyRingedSite 𝒪D]
    (fSharp : (F.sheafPullback CommRingCat.{max u v} JD JC).obj 𝒪D ⟶ 𝒪C) : Prop :=
  IsMorphismOfLocallyRingedTopoi F 𝒪C 𝒪D fSharp

/-- The site-level and topos-level locally ringed morphism predicates coincide in the presented
setting. -/
theorem isMorphismOfLocallyRingedSites_iff
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (F : D ⥤ C) [Functor.IsContinuous F JD JC]
    [(F.sheafPushforwardContinuous CommRingCat.{max u v} JD JC).IsRightAdjoint]
    (𝒪C : Sheaf JC CommRingCat.{max u v}) (𝒪D : Sheaf JD CommRingCat.{max u v})
    [IsLocallyRingedSite 𝒪C] [IsLocallyRingedSite 𝒪D]
    (fSharp : (F.sheafPullback CommRingCat.{max u v} JD JC).obj 𝒪D ⟶ 𝒪C) :
    IsMorphismOfLocallyRingedSites F 𝒪C 𝒪D fSharp ↔
      IsMorphismOfLocallyRingedTopoi F 𝒪C 𝒪D fSharp :=
  Iff.rfl

end CategoryTheory

/-! ### Lemma_18_40_10 (from Chap18) -/
open CategoryTheory

noncomputable section

universe u

namespace RingedSite.Hom

section

variable {C : Type u} [Category.{u} C]
variable {D : Type u} [Category.{u} D]
variable {E : Type u} [Category.{u} E]
variable {JC : GrothendieckTopology C}
variable {JD : GrothendieckTopology D}
variable {JE : GrothendieckTopology E}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JE.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify JC CommRingCat.{u}]
variable [HasWeakSheafify JD CommRingCat.{u}]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [HasWeakSheafify JD AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪X : Sheaf JC CommRingCat.{u}}
variable {𝒪Y : Sheaf JD CommRingCat.{u}}
variable {𝒪Z : Sheaf JE CommRingCat.{u}}

local notation "X" => RingedSite.ofCommRingSheaf JC 𝒪X
local notation "Y" => RingedSite.ofCommRingSheaf JD 𝒪Y
local notation "Z" => RingedSite.ofCommRingSheaf JE 𝒪Z

local instance instBaseIsContinuousLemma184010 {A B : RingedSite.{u, u}} (f : A ⟶ B) :
    Functor.IsContinuous f.base B.siteTopology A.siteTopology :=
  f.isMorphismOfSites.toIsContinuous

/- Domain-style sampling for Lemma 18.40.10:
- primary domain: composition of site-presented morphisms of locally ringed topoi;
- sampled owner declarations:
  `RingedSite.Hom.comp`,
  `RingedSite.Hom.inverseImageStructureSheafMap`,
  `CategoryTheory.IsMorphismOfLocallyRingedTopoi`,
  `CategoryTheory.isMorphismOfLocallyRingedTopoi_iff`;
- best owner abstraction: the bundled source-facing morphism owner `RingedSite.Hom`;
- primitive data: the bundled ringed-site morphisms `f : X ⟶ Y` and `g : Y ⟶ Z`;
- derived API: the inverse-image structure-sheaf maps
  `inverseImageStructureSheafMap f`,
  `inverseImageStructureSheafMap g`, and
  `inverseImageStructureSheafMap (f ≫ g)`, together with the Chapter 18 class
  `CategoryTheory.IsMorphismOfLocallyRingedTopoi`; the needed sheaf-pushforward right adjoints are
  canonical derived instances from continuity and `HasWeakSheafify`, not primitive theorem data.

Source/core/bridge triage:
- `source-facing`: the closure statement that the composite of two morphisms of locally ringed
  topoi is again such a morphism;
- `core/canonical`: `CategoryTheory.IsMorphismOfLocallyRingedTopoi`;
- `bridge/view`: `RingedSite.Hom.inverseImageStructureSheafMap`, converting the bundled ringed-site
  morphism to the inverse-image form expected by the canonical owner.

Accordingly, this file should not introduce a second owner such as `CommRingedToposIn` or
`CommRingedToposMorphismIn`; the textbook statement lives directly on `RingedSite.Hom.comp`. -/

variable (f : X ⟶ Y) (g : Y ⟶ Z)
variable [IsLocallyRingedSite 𝒪X]
variable [IsLocallyRingedSite 𝒪Y]
variable [IsLocallyRingedSite 𝒪Z]
variable [IsMorphismOfLocallyRingedTopoi
  f.base 𝒪X 𝒪Y (inverseImageStructureSheafMap f)]
variable [IsMorphismOfLocallyRingedTopoi
  g.base 𝒪Y 𝒪Z (inverseImageStructureSheafMap g)]

-- Proof sketch: by Definition `18.40.9`, the locally ringed condition is the cartesianness of the
-- inverse-image units square. That condition is stable under composition because pullback along the
-- composite inverse-image functor is the composite of the pullbacks for `f` and `g`, and the
-- cartesian-units squares compose.
/-- Lemma 18.40.10: the composite of two morphisms of locally ringed topoi is again a morphism of
locally ringed topoi. -/
@[instance]
theorem isMorphismOfLocallyRingedTopoi_comp :
    IsMorphismOfLocallyRingedTopoi
      (f ≫ g).base 𝒪X 𝒪Z (inverseImageStructureSheafMap (f ≫ g)) := sorry

end

end RingedSite.Hom

/-! ### Lemma_18_40_11 (from Chap18) -/
open CategoryTheory Opposite

noncomputable section

universe u v

namespace CategoryTheory

/- Domain-style sampling for Lemma 18.40.11:
- primary domain: inverse image for locally ringed sites, with the units construction tracked at
  the source-facing units subsheaf level before passing to the Chapter 18 cartesian-units owner;
- sampled owner declarations:
  `inverseImageStructureSheafForLocallyRingedMorphism`,
  `ringedSiteUnitsSubsheaf`,
  `sheaf_pullback_forget`,
  `unitsSquareCartesianForLocallyRingedMorphism`,
  `pullback_isLocallyRingedSite`;
- best owner abstractions:
  the inverse-image structure sheaf itself should be spoken about through the Chapter 18 owner
  `inverseImageStructureSheafForLocallyRingedMorphism`;
  clause `(1)` is source-facing and should compare the actual inverse-image units sheaf
  `F^{-1}(\mathcal O^*)` with the units subsheaf `(F^{-1}\mathcal O)^*` of the inverse-image
  structure sheaf, using the Chapter 7 forget-compatibility owner `sheaf_pullback_forget` to
  interpret sections of `F^{-1}\mathcal O` as sections of the underlying sheaf of
  `F^{-1}\mathcal O`;
  the Chapter 18 cartesian-units owner
  `inverseImageUnitsCartesianForLocallyRingedMorphism`, specialized to the identity map on
  `F^{-1}\mathcal O`, is only a bridge/view reformulation of that comparison;
  clause `(2)` is already exactly the canonical preservation theorem
  `pullback_isLocallyRingedSite`;
- primitive data:
  the continuous functor `F` presenting the inverse-image functor and the commutative structure
  sheaf `𝒪`;
- derived API:
  the inverse-image comparison between units sheaves, the corresponding cartesian-units
  reformulation for the identity map on `F^{-1}\mathcal O`, and the pullback preservation of
  local ringedness.

Source/core/bridge triage:
- `source-facing`: the claim that inverse image carries the units subsheaf of `𝒪` to the units
  subsheaf of `F^{-1}\mathcal O`, i.e. `F^{-1}(\mathcal O^*) ≅ (F^{-1}\mathcal O)^*`;
- `core/canonical`: `inverseImageStructureSheafForLocallyRingedMorphism`,
  `ringedSiteUnitsSubsheaf`, and
  `pullback_isLocallyRingedSite`;
- `bridge/view`: `sheaf_pullback_forget`, identifying the pullback of the underlying sheaf of
  sets with the underlying sheaf of the pulled-back structure sheaf, and
  `inverseImageUnitsCartesianForLocallyRingedMorphism` for the later locally ringed-morphism
  reformulation.
-/

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (F : C ⥤ D) [Functor.IsContinuous F J K]
variable [((F.sheafPushforwardContinuous CommRingCat.{max u v} J K).IsRightAdjoint)]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

local notation "f⁻¹𝒪" => inverseImageStructureSheafForLocallyRingedMorphism F 𝒪

section UnitsComparison

variable [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
variable [(forget CommRingCat.{max u v}).PreservesLeftKanExtensions F.op]

private noncomputable def pullbackInverseImageUnitsUnderlying :
    (F.sheafPullback (Type (max u v)) J K).obj (ringedSiteUnitsSubsheaf 𝒪) ⟶
      (sheafCompose K (forget CommRingCat.{max u v})).obj
        (f⁻¹𝒪 : Sheaf K CommRingCat.{max u v}) :=
  (F.sheafPullback (Type (max u v)) J K).map (ringedSiteUnitsSubsheafι 𝒪) ≫
    (((sheaf_pullback_forget J K F).app 𝒪).inv)

private noncomputable def pullbackInverseImageUnitsApp (U : D) :
    ((F.sheafPullback (Type (max u v)) J K).obj (ringedSiteUnitsSubsheaf 𝒪)).1.obj (op U) →
      (f⁻¹𝒪 : Sheaf K CommRingCat.{max u v}).1.obj (op U) :=
  fun s ↦ (pullbackInverseImageUnitsUnderlying F 𝒪).1.app (op U) s

-- Proof sketch: pull back the inclusion `\mathcal O^* \hookrightarrow \mathcal O` as a morphism
-- of sheaves of sets and transport its target across the canonical Chapter 7 forget/pullback
-- comparison; sections of `F^{-1}(\mathcal O^*)` therefore land in unit sections of
-- `F^{-1}\mathcal O`.
private theorem pullback_inverseImageUnitsApp_isUnit
    (U : D)
    (s : ((F.sheafPullback (Type (max u v)) J K).obj (ringedSiteUnitsSubsheaf 𝒪)).1.obj (op U)) :
    IsUnit (pullbackInverseImageUnitsApp F 𝒪 U s) := by
  sorry

private noncomputable def pullbackInverseImageUnitsComparison (U : D) :
    ((F.sheafPullback (Type (max u v)) J K).obj (ringedSiteUnitsSubsheaf 𝒪)).1.obj (op U) →
      (ringedSiteUnitsSubsheaf (f⁻¹𝒪 : Sheaf K CommRingCat.{max u v})).1.obj (op U) :=
  fun s ↦
    ⟨pullbackInverseImageUnitsApp F 𝒪 U s,
      pullback_inverseImageUnitsApp_isUnit F 𝒪 U s⟩

-- Proof sketch: the objectwise comparison maps above assemble into a morphism of sheaves because
-- their underlying sections are the components of the natural transformation obtained by composing
-- the pulled-back inclusion `F^{-1}(\mathcal O^*) → F^{-1}\mathcal O` with the canonical
-- forget/pullback comparison from Chapter 7.
private noncomputable def pullback_inverseImageUnitsHom :
    (F.sheafPullback (Type (max u v)) J K).obj (ringedSiteUnitsSubsheaf 𝒪) ⟶
      ringedSiteUnitsSubsheaf (f⁻¹𝒪 : Sheaf K CommRingCat.{max u v}) :=
  ⟨
    { app := fun U ↦ pullbackInverseImageUnitsComparison F 𝒪 U.unop
      naturality := by
        intro U V f
        funext s
        apply Subtype.ext
        exact congr_fun ((pullbackInverseImageUnitsUnderlying F 𝒪).hom.naturality f) s }⟩

private theorem pullback_inverseImageUnitsHom_app_bijective (U : D) :
    Function.Bijective
      (((pullback_inverseImageUnitsHom F 𝒪 :
          (F.sheafPullback (Type (max u v)) J K).obj (ringedSiteUnitsSubsheaf 𝒪) ⟶
            ringedSiteUnitsSubsheaf (f⁻¹𝒪 : Sheaf K CommRingCat.{max u v})).hom.app
        (op U))) := by
  sorry

-- Proof sketch: the forgetful functor from sheaves to presheaves reflects isomorphisms, and a
-- natural transformation between `Type`-valued presheaves is an isomorphism exactly when each
-- component is bijective. Apply the previous objectwise bijectivity theorem.
private theorem pullback_inverseImageUnitsHom_isIso :
    IsIso
      (pullback_inverseImageUnitsHom F 𝒪 :
        (F.sheafPullback (Type (max u v)) J K).obj (ringedSiteUnitsSubsheaf 𝒪) ⟶
          ringedSiteUnitsSubsheaf (f⁻¹𝒪 : Sheaf K CommRingCat.{max u v})) := by
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf K (Type (max u v))),
    NatTrans.isIso_iff_isIso_app]
  intro U
  rw [isIso_iff_bijective]
  simpa using pullback_inverseImageUnitsHom_app_bijective F 𝒪 U.unop

/-- Lemma 18.40.11 (1), isomorphism form: the actual inverse image of the units subsheaf
`F^{-1}(\mathcal O^*)` is canonically identified with the units subsheaf
`ringedSiteUnitsSubsheaf f⁻¹𝒪` of the inverse-image structure sheaf. -/
noncomputable def pullback_inverseImageUnitsIso :
    (F.sheafPullback (Type (max u v)) J K).obj (ringedSiteUnitsSubsheaf 𝒪) ≅
      ringedSiteUnitsSubsheaf (f⁻¹𝒪 : Sheaf K CommRingCat.{max u v}) := by
  let α :
      (F.sheafPullback (Type (max u v)) J K).obj (ringedSiteUnitsSubsheaf 𝒪) ⟶
        ringedSiteUnitsSubsheaf (f⁻¹𝒪 : Sheaf K CommRingCat.{max u v}) :=
    pullback_inverseImageUnitsHom F 𝒪
  let _ : IsIso α := pullback_inverseImageUnitsHom_isIso F 𝒪
  exact asIso α

end UnitsComparison

attribute [local instance] pullback_isLocallyRingedSite

/-- Companion bridge to the Chapter 18 owner: for the identity map
`f^\sharp : F^{-1}\mathcal O \to F^{-1}\mathcal O`, the inverse-image units square is cartesian. -/
theorem pullback_inverseImageUnitsCartesian :
    inverseImageUnitsCartesianForLocallyRingedMorphism
      F
      (f⁻¹𝒪 : Sheaf K CommRingCat.{max u v})
      𝒪
      (𝟙 _) := by
  intro U
  change
    unitsSquareCartesianForLocallyRingedMorphism
      (RingHom.id ((f⁻¹𝒪 : Sheaf K CommRingCat.{max u v}).1.obj (op U)))
  rw [unitsSquareCartesian_iff_isLocalHom]
  exact isLocalHom_id _

-- Proof sketch: clause `(1)` identifies the inverse image of the units subsheaf with the units
-- subsheaf of the pulled-back structure sheaf, while Lemma `18.40.5` supplies that
-- `F^{-1}\mathcal O` is locally ringed whenever `\mathcal O` is. Thus the site-presented
-- morphism of topoi with `f^\sharp = \mathrm{id}` satisfies the Chapter 18 locally ringed
-- morphism owner.
/-- Lemma 18.40.11 (2): if `(\mathcal C, \mathcal O)` is locally ringed, then the morphism of
topoi induced by `F` together with the identity map
`f^\sharp : F^{-1}\mathcal O \to F^{-1}\mathcal O` is a morphism of locally ringed topoi. -/
theorem pullback_isMorphismOfLocallyRingedTopoi
    [IsLocallyRingedSite 𝒪] :
    IsMorphismOfLocallyRingedTopoi
      F
      (f⁻¹𝒪 : Sheaf K CommRingCat.{max u v})
      𝒪
      (𝟙 _) := by
  exact ⟨pullback_inverseImageUnitsCartesian F 𝒪⟩

end CategoryTheory

/-! ### Lemma_18_40_12 (from Chap18) -/
open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

-- Proof sketch: apply Lemma `18.40.5 (1)` to the localization functor
-- `Over.forget U : C/U ⥤ C`; its inverse image on commutative ring sheaves is exactly the
-- restricted structure sheaf `\mathcal O_U`.
/-- Lemma 18.40.12 (1): if `(\mathcal C, \mathcal O)` is a locally ringed site and `U` is an
object of `\mathcal C`, then the localization `(\mathcal C/U, \mathcal O_U)` is a locally
ringed site. -/
theorem localization_isLocallyRingedSite
    (U : C) [IsLocallyRingedSite 𝒪] :
    IsLocallyRingedSite ((J.overPullback CommRingCat.{max u v} U).obj 𝒪) := sorry

end

end CategoryTheory
