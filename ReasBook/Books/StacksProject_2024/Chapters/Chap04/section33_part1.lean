import Mathlib
import Mathlib.CategoryTheory.FiberedCategory.Cartesian
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_33_1 (from Chap04) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/- Domain-style sampling for Definition 4.33.1:
- primary domain: fibered categories and universal properties of lifts over a base functor.
- inspected owner-level declarations:
  `Functor.IsStronglyCartesian`,
  `IsStronglyCartesian.universal_property'`,
  `IsStronglyCartesian.universal_property`,
  `IsStronglyCartesian.map`.
- core/canonical owner: `Functor.IsStronglyCartesian` from mathlib's fibered-category API.
- primitive data: the owner field `[p.IsHomLift f φ]` and the universal-property field
  `IsStronglyCartesian.universal_property'`.
- derived API: the associated universal-property lemmas such as `IsStronglyCartesian.universal_property`,
  `IsStronglyCartesian.map`, and the chapter bridge from fibredness to existence of strongly
  cartesian lifts.

Primitive-vs-derived split:
- primitive data: the functor `p`, the base arrow `f`, the total-category arrow `φ`, and the
  strongly-cartesian owner predicate on that data;
- derived API: the universal-property access lemma and the induced comparison morphisms built from
  that owner.

Source/core/bridge triage:
- `source-facing`: the Stacks notion of a strongly cartesian morphism.
- `core/canonical`: `Functor.IsStronglyCartesian`.
- `bridge/view`: later chapter lemmas that restate its behavior in slice categories or under
  composition, without introducing a parallel owner. -/

/- Definition 4.33.1: for a functor `p : 𝒳 ⥤ 𝒮`, a base morphism `f`, and a morphism `φ` lying
over it, the Stacks notion of a strongly cartesian morphism is the canonical owner
`Functor.IsStronglyCartesian`. -/
recall IsStronglyCartesian

/-- Companion bridge for Definition 4.33.1: the textbook universal-property formulation of a
strongly cartesian morphism is equivalent to the canonical owner predicate
`Functor.IsStronglyCartesian`. -/
theorem isStronglyCartesian_iff_universal_property
    (p : 𝒳 ⥤ 𝒮) {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) :
    p.IsStronglyCartesian f φ ↔
      p.IsHomLift f φ ∧
        ∀ {R' : 𝒮} {a' : 𝒳} (g : R' ⟶ R) (φ' : a' ⟶ b),
          p.IsHomLift (g ≫ f) φ' →
            ∃! χ : a' ⟶ a, p.IsHomLift g χ ∧ χ ≫ φ = φ' := by
  constructor
  · intro h
    letI : p.IsStronglyCartesian f φ := h
    refine ⟨inferInstance, fun g φ' hφ' ↦ ?_⟩
    letI : p.IsHomLift (g ≫ f) φ' := hφ'
    simpa using IsStronglyCartesian.universal_property p f φ g (g ≫ f) rfl φ'
  · rintro ⟨hφ, h⟩
    refine { toIsHomLift := hφ, universal_property' := ?_ }
    intro a' g φ' hφ'
    exact h g φ' hφ'

end CategoryTheory.Functor

/-! ### Lemma_4_33_2 (from Chap04) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

open IsStronglyCartesian

variable {𝒞 : Type u₁} {𝒮 : Type u₂} [Category.{v₁} 𝒞] [Category.{v₂} 𝒮]

/- Domain-style sampling for Lemma 4.33.2:
- primary domain: strongly cartesian morphisms for a functor and their canonical closure
  properties;
- inspected owner-level declarations:
  `Functor.IsStronglyCartesian.comp`,
  `Functor.IsStronglyCartesian.of_isIso`,
  `Functor.IsStronglyCartesian.isIso_of_base_isIso`;
- best owner abstraction: `Functor.IsStronglyCartesian`;
- primitive data: a functor `p : 𝒮 ⥤ 𝒞`, a base morphism `f`, and a morphism `φ` lying over `f`;
- derived API: closure under composition, stability under isomorphism, and recovery of an
  isomorphism from an isomorphic base arrow.

Source/core/bridge triage:
- `source-facing`: the three textbook closure properties listed in Lemma 4.33.2;
- `core/canonical`: the owner namespace `CategoryTheory.Functor.IsStronglyCartesian`;
- `bridge/view`: this file is a direct canonical recall, so no wrapper theorem or alias is needed.
-/

/- Lemma 4.33.2 (1): the composite of strongly cartesian morphisms is the canonical instance
`comp`. -/
recall comp

/- Lemma 4.33.2 (2): an isomorphism is strongly cartesian over its image in the base category by
the canonical instance `of_isIso`. -/
recall of_isIso

/- Lemma 4.33.2 (3): a strongly cartesian morphism whose image in the base category is an
isomorphism is itself an isomorphism by the canonical theorem
`isIso_of_base_isIso`. -/
recall isIso_of_base_isIso

end CategoryTheory.Functor

/-! ### Lemma_4_33_3 (from Chap04) -/
universe uA uB uC vA vB vC

namespace CategoryTheory.Functor

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]

/- Domain-style sampling for Lemma 4.33.3:
- primary domain: strongly cartesian morphisms for functors and their behavior under composition;
- sampled owner declarations:
  `IsStronglyCartesian`,
  `comp`,
  `of_comp`,
  `map_comp_map`;
- best owner abstraction: `Functor.IsStronglyCartesian`;
- primitive data: a functor pair `F : A ⥤ B`, `G : B ⥤ C`, a morphism `φ : x ⟶ y`, and the two
  strongly cartesian hypotheses for `φ` over `F` and `F.map φ` over `G`;
- derived API: the induced strongly cartesian structure for `φ` over the composite functor
  `F ⋙ G`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma asserting that strong cartesianness is stable under functor
  composition;
- `core/canonical`: the owner predicate `Functor.IsStronglyCartesian`;
- `bridge/view`: none; this file supplies the source-facing functor-composition theorem directly in
  the owner namespace so downstream files reuse one public result instead of carrying private
  duplicates. -/

-- Proof sketch: given a lift `τ` over `g ≫ G.map (F.map φ)`, first use the strong cartesianness
-- of `F.map φ` for `G` to obtain a lift `δ : F.obj a' ⟶ F.obj a` of `g`, then use the strong
-- cartesianness of `φ` for `F` to lift `δ` to `χ : a' ⟶ a`. The universal properties for `G` and
-- `F` then identify `χ` as the unique lift over `g` for the composite functor `F ⋙ G`.
/-- Helper for Lemma 4.33.3: a lift for the composite functor yields a lift for `G` after applying
`F`. -/
private lemma mapped_isHomLift_of_comp_isHomLift
    (F : A ⥤ B) (G : B ⥤ C) {a a' : A}
    {g : G.obj (F.obj a') ⟶ G.obj (F.obj a)} {π : a' ⟶ a}
    (hπ : (F ⋙ G).IsHomLift g π) :
    G.IsHomLift g (F.map π) := by
  -- Rewriting the composite-functor lift equation exposes the outer lift directly.
  refine IsHomLift.of_fac G g (F.map π) rfl rfl ?_
  simpa [Functor.comp_map] using
    (@IsHomLift.fac' _ _ _ _ (F ⋙ G) _ _ _ _ g π hπ).symm

/-- Helper for Lemma 4.33.3: composing the lifts through `F` and `G` gives a lift for `F ⋙ G`. -/
private lemma comp_isHomLift_of_component_lifts
    (F : A ⥤ B) (G : B ⥤ C) {a a' : A}
    {g : G.obj (F.obj a') ⟶ G.obj (F.obj a)}
    {δ : F.obj a' ⟶ F.obj a} {χ : a' ⟶ a}
    (hδ : G.IsHomLift g δ) (hχ : F.IsHomLift δ χ) :
    (F ⋙ G).IsHomLift g χ := by
  -- The base map of the composite lift is the composite of the two component base maps.
  refine IsHomLift.of_fac (F ⋙ G) g χ rfl rfl ?_
  have hδ' : G.map δ = g := by
    simpa using (@IsHomLift.fac' _ _ _ _ G _ _ _ _ g δ hδ)
  have hχ' : F.map χ = δ := by
    simpa using (@IsHomLift.fac' _ _ _ _ F _ _ _ _ δ χ hχ)
  simpa using
    calc
      g = G.map δ := hδ'.symm
      _ = G.map (F.map χ) := by rw [hχ'.symm]

/-- Lemma 4.33.3: if `φ : a ⟶ b` is strongly cartesian for `F : A ⥤ B` and `F.map φ` is strongly
cartesian for `G : B ⥤ C`, then `φ` is strongly cartesian for the composite functor `F ⋙ G`. -/
theorem isStronglyCartesian_map_comp
    (F : A ⥤ B) (G : B ⥤ C) {a b : A} (φ : a ⟶ b)
    [F.IsStronglyCartesian (F.map φ) φ]
    [G.IsStronglyCartesian (G.map (F.map φ)) (F.map φ)] :
    (F ⋙ G).IsStronglyCartesian ((F ⋙ G).map φ) φ := by
  refine
    { toIsHomLift := by
        exact IsHomLift.map φ
      universal_property' := ?_ }
  intro a' g τ hτ
  have hτG :
      G.IsHomLift (g ≫ G.map (F.map φ)) (F.map τ) :=
    mapped_isHomLift_of_comp_isHomLift F G hτ
  have hτfac : G.map (F.map τ) = g ≫ G.map (F.map φ) := by
    simpa using
      (@IsHomLift.fac' _ _ _ _ G _ _ _ _ (g ≫ G.map (F.map φ)) (F.map τ) hτG)
  -- First lift `F.map τ` through `G` to produce the middle-stage base morphism.
  let δ : F.obj a' ⟶ F.obj a :=
    IsStronglyCartesian.map G (G.map (F.map φ)) (F.map φ) hτfac (F.map τ)
  have hδlift : G.IsHomLift g δ := by
    dsimp [δ]
    infer_instance
  have hδ : δ ≫ F.map φ = F.map τ := by
    dsimp [δ]
    exact IsStronglyCartesian.fac G (G.map (F.map φ)) (F.map φ) hτfac (F.map τ)
  -- Then lift `δ` through `F` to obtain the desired composite lift upstairs.
  let χ : a' ⟶ a :=
    IsStronglyCartesian.map F (F.map φ) φ hδ.symm τ
  have hχlift : F.IsHomLift δ χ := by
    dsimp [χ]
    infer_instance
  have hχ : χ ≫ φ = τ := by
    dsimp [χ]
    exact IsStronglyCartesian.fac F (F.map φ) φ hδ.symm τ
  have hχcomp : (F ⋙ G).IsHomLift g χ :=
    comp_isHomLift_of_component_lifts F G hδlift hχlift
  refine ⟨χ, ⟨hχcomp, hχ⟩, ?_⟩
  intro π hπ
  -- Uniqueness follows by comparing first after applying `F`, then upstairs over `A`.
  have hπG : G.IsHomLift g (F.map π) :=
    mapped_isHomLift_of_comp_isHomLift F G hπ.1
  have hFπ : F.map π = δ := by
    -- The two candidate `G`-lifts agree because they have the same composite with `F.map φ`.
    exact
      @IsStronglyCartesian.ext _ _ _ _ G _ _ _ _
        (G.map (F.map φ)) (F.map φ) inferInstance _ _ g (F.map π) δ hπG hδlift <| by
          calc
            F.map π ≫ F.map φ = F.map (π ≫ φ) := by
              simp
            _ = F.map τ := by
              rw [hπ.2]
            _ = δ ≫ F.map φ := hδ.symm
  have hπF : F.IsHomLift δ π := by
    refine IsHomLift.of_fac F δ π rfl rfl ?_
    simpa using hFπ.symm
  -- Comparing the two lifts through `F` proves uniqueness in `A`.
  exact
    @IsStronglyCartesian.ext _ _ _ _ F _ _ _ _
      (F.map φ) φ inferInstance _ _ δ π χ hπF hχlift <| by
        rw [hπ.2, hχ]

end CategoryTheory.Functor

/-! ### Lemma_4_33_4 (from Chap04) -/
open CategoryTheory
open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

/- Domain-style sampling for Lemma 4.33.4:
- primary domain: strongly cartesian morphisms for a functor together with pullback squares in the
  base category;
- sampled owner API:
  `Functor.IsStronglyCartesian`,
  `IsStronglyCartesian.map`,
  `Functor.IsHomLift`,
  `IsHomLift.fac'`,
  `CategoryTheory.IsPullback`;
- source-facing layer: the Stacks lemma asserting that a strongly cartesian lift of the second base
  pullback projection produces a pullback square in the total category;
- core/canonical owners: `Functor.IsStronglyCartesian` for the induced comparison morphism and
  `IsPullback` for the resulting square;
- bridge/view: the left leg upstairs is derived by `IsStronglyCartesian.map`, and the needed base
  comparison is read off from the owner-level `IsHomLift` API.

Primitive-vs-derived split:
- primitive data: the morphisms `φ`, `ψ`, `a`, the base pullback, and the two
  `IsStronglyCartesian` instances;
- derived API: the owner-level comparison morphism from `IsStronglyCartesian.map`, the base
  compatibility lemma identifying it with the pullback cospan, and the resulting `IsPullback`
  statement. -/

open IsStronglyCartesian IsHomLift

variable {C : Type u₁} [Category.{v₁} C]
variable {E : Type u₂} [Category.{v₂} E]

section

variable (p : E ⥤ C) {x y z w : E} (φ : x ⟶ y) (ψ : z ⟶ y)

-- Proof sketch: for a cone `t` over `φ` and `ψ`, the base pullback square provides a comparison
-- map `p.obj t.pt ⟶ R`; strong cartesianness of `a` lifts `t.snd` through that comparison, and
-- strong cartesianness of `φ` identifies the composite with `t.fst`.
/-- Lemma 4.33.4: if the square formed by `p.map χ`, `p.map a`, `p.map φ`, and `p.map ψ` is a
pullback square in the base category, `φ` is strongly cartesian over its base map, and `a` is
strongly cartesian over the other base leg, then the square `χ, a, φ, ψ` is a pullback square in
the total category. -/
theorem isPullback_of_isPullback_of_isStronglyCartesian
    {R : C} {f : R ⟶ p.obj x} {g : R ⟶ p.obj z} {χ : w ⟶ x} (hbase : IsPullback f g (p.map φ) (p.map ψ))
    (a : w ⟶ z) [p.IsHomLift f χ] [p.IsStronglyCartesian (p.map φ) φ]
    [p.IsStronglyCartesian g a] (hχ : χ ≫ φ = a ≫ ψ) :
    IsPullback χ a φ ψ := by
  have hw : p.obj w = R := IsHomLift.domain_eq p g a
  let baseMap (t : PullbackCone φ ψ) : p.obj t.pt ⟶ R :=
    hbase.lift (p.map t.fst) (p.map t.snd) (by
      simpa using congrArg (Functor.map p) t.condition)
  have baseMap_fst (t : PullbackCone φ ψ) : baseMap t ≫ f = p.map t.fst := by
    simp [baseMap]
  have baseMap_snd (t : PullbackCone φ ψ) : p.map t.snd = baseMap t ≫ g := by
    simpa [baseMap] using
      (hbase.lift_snd (p.map t.fst) (p.map t.snd) (congrArg (Functor.map p) t.condition)).symm
  let lift (t : PullbackCone φ ψ) : t.pt ⟶ w :=
    IsStronglyCartesian.map p g a (baseMap_snd t) t.snd
  refine IsPullback.of_isLimit' ⟨hχ⟩ ?_
  refine PullbackCone.IsLimit.mk _ lift ?_ ?_ ?_
  · intro t
    have hlift : lift t ≫ a = t.snd := by
      dsimp [lift]
      exact IsStronglyCartesian.fac p g a (baseMap_snd t) t.snd
    letI : p.IsHomLift (baseMap t ≫ f) (lift t ≫ χ) := inferInstance
    letI : p.IsHomLift (p.map t.fst) (lift t ≫ χ) := by
      exact (baseMap_fst t) ▸ inferInstance
    apply IsStronglyCartesian.ext p (p.map φ) φ (p.map t.fst)
    calc
      (lift t ≫ χ) ≫ φ = lift t ≫ (χ ≫ φ) := by simp [Category.assoc]
      _ = lift t ≫ (a ≫ ψ) := by rw [hχ]
      _ = (lift t ≫ a) ≫ ψ := by simp [Category.assoc]
      _ = t.snd ≫ ψ := by rw [hlift]
      _ = t.fst ≫ φ := by simpa using t.condition.symm
  · intro t
    dsimp [lift]
    exact IsStronglyCartesian.fac p g a (baseMap_snd t) t.snd
  · intro t m hmfst hmsnd
    have hχbase : p.map χ = eqToHom hw ≫ f := by
      simpa [hw] using IsHomLift.fac' p f χ
    have habase : p.map a = eqToHom hw ≫ g := by
      simpa [hw] using IsHomLift.fac' p g a
    have hmfst' : (p.map m ≫ eqToHom hw) ≫ f = p.map t.fst := by
      calc
        (p.map m ≫ eqToHom hw) ≫ f = p.map m ≫ p.map χ := by simp [Category.assoc, hχbase]
        _ = p.map t.fst := by
          simpa [Functor.map_comp] using congrArg (Functor.map p) hmfst
    have hmsnd' : (p.map m ≫ eqToHom hw) ≫ g = p.map t.snd := by
      calc
        (p.map m ≫ eqToHom hw) ≫ g = p.map m ≫ p.map a := by simp [Category.assoc, habase]
        _ = p.map t.snd := by
          simpa [Functor.map_comp] using congrArg (Functor.map p) hmsnd
    have hm : p.map m ≫ eqToHom hw = baseMap t := by
      apply hbase.hom_ext
      · exact hmfst'.trans (baseMap_fst t).symm
      · exact hmsnd'.trans (baseMap_snd t)
    have hm' : p.map m = baseMap t ≫ eqToHom hw.symm := by
      calc
        p.map m = (p.map m ≫ eqToHom hw) ≫ eqToHom hw.symm := by simp [Category.assoc]
        _ = baseMap t ≫ eqToHom hw.symm := by
          simpa [Category.assoc] using congrArg (fun k ↦ k ≫ eqToHom hw.symm) hm
    letI : p.IsHomLift (baseMap t) m := by
      refine IsHomLift.of_fac' p (baseMap t) m rfl hw ?_
      simpa using hm'
    dsimp [lift]
    exact IsStronglyCartesian.map_uniq p g a (baseMap_snd t) t.snd m hmsnd

/- Companion bridge: specialize Lemma 4.33.4 to the canonical chosen pullback of `p.map φ` and
`p.map ψ` in the base category. -/
theorem strongly_cartesian_pullback_isPullback
    {a : w ⟶ z} [HasPullback (p.map φ) (p.map ψ)] [p.IsStronglyCartesian (p.map φ) φ]
    [p.IsStronglyCartesian (pullback.snd (p.map φ) (p.map ψ)) a] :
    IsPullback
      (IsStronglyCartesian.map p (p.map φ) φ
        (IsPullback.of_hasPullback (p.map φ) (p.map ψ)).w.symm
        (a ≫ ψ))
      a φ ψ := by
  let hbase : IsPullback
      (pullback.fst (p.map φ) (p.map ψ))
      (pullback.snd (p.map φ) (p.map ψ))
      (p.map φ)
      (p.map ψ) :=
    IsPullback.of_hasPullback (p.map φ) (p.map ψ)
  exact isPullback_of_isPullback_of_isStronglyCartesian p φ ψ hbase a
    (IsStronglyCartesian.fac p (p.map φ) φ hbase.w.symm (a ≫ ψ))

end

end CategoryTheory.Functor

/-! ### Definition_4_33_5 (from Chap04) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory
namespace Functor

variable {𝒞 : Type u₁} {𝒮 : Type u₂} [Category.{v₁} 𝒞] [Category.{v₂} 𝒮]

/- Domain-style sampling for Definition 4.33.5:
- primary domain: fibered categories over a base functor.
- inspected owner-level declarations:
  `Functor.IsFibered`,
  `Functor.IsPreFibered.exists_isCartesian`,
  `Functor.IsFibered.isStronglyCartesian_of_isCartesian`,
  `Functor.IsFibered.of_exists_isStronglyCartesian`.
- best owner abstraction: `Functor.IsFibered`.
- primitive data: the functor `p : 𝒮 ⥤ 𝒞` together with the owner predicate `p.IsFibered`,
  whose primitive lift datum is cartesian lift existence.
- derived API: the source-facing characterization by existence of strongly cartesian lifts.

Source/core/bridge triage:
- `source-facing`: the textbook characterization of fibredness by strongly cartesian lifts.
- `core/canonical`: `Functor.IsFibered`.
- `bridge/view`: the theorem `isFibered_iff_exists_isStronglyCartesian`, which translates the
  source phrasing to the canonical owner API without introducing a parallel owner. -/

/- Definition 4.33.5: the Stacks notion that a category over `𝒞` is fibred is the canonical
owner predicate `Functor.IsFibered`. -/
recall IsFibered

-- Proof sketch: one direction uses that in a fibered category every cartesian lift is strongly
-- cartesian, via `Functor.IsFibered.isStronglyCartesian_of_isCartesian` and the chosen lift from
-- `Functor.IsPreFibered.exists_isCartesian`; the converse is the constructor
-- `Functor.IsFibered.of_exists_isStronglyCartesian`.
/- Companion bridge: this source-facing characterization records the textbook strongly cartesian
lift criterion for fibredness. The owner abstraction remains `Functor.IsFibered`; this theorem is
the companion bridge from the source wording to that canonical predicate. -/
theorem isFibered_iff_exists_isStronglyCartesian (p : 𝒮 ⥤ 𝒞) :
    p.IsFibered ↔
      ∀ (x : 𝒮) (V : 𝒞) (f : V ⟶ p.obj x),
        ∃ (fx : 𝒮) (φ : fx ⟶ x), p.IsStronglyCartesian f φ := by
  constructor
  · intro hp x V f
    letI : p.IsFibered := hp
    obtain ⟨fx, φ, hφ⟩ := IsPreFibered.exists_isCartesian p rfl f
    letI : p.IsCartesian f φ := hφ
    exact ⟨fx, φ, IsFibered.isStronglyCartesian_of_isCartesian p f φ⟩
  · exact IsFibered.of_exists_isStronglyCartesian
end Functor
end CategoryTheory

/-! ### Definition_4_33_6 (from Chap04) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Functor Fiber

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

/- Domain-style sampling for Definition 4.33.6:
- primary domain: fibered categories and chosen strongly cartesian pullbacks in standard fibers.
- inspected owner-level declarations:
  `Functor.IsStronglyCartesian.map`,
  `Functor.IsStronglyCartesian.map_self`,
  `Functor.IsStronglyCartesian.map_comp_map`,
  `Functor.IsStronglyCartesian.ext`,
  `Functor.IsFibered`,
  `Functor.IsFibered.isStronglyCartesian_of_isCartesian`.
- best owner abstraction for the derived standard-fiber action: `Functor.IsStronglyCartesian`.
- primitive data: the source-facing explicit pullback-choice package `PullbackChoice p`.
- derived API: `PullbackChoice.isFibered` and the induced pullback functors on standard fibers,
  with the action on morphisms read directly from the strong-cartesian universal property.

Source/core/bridge triage:
- `source-facing`: `PullbackChoice p`, matching the textbook's explicit chosen pullbacks.
- `core/canonical`: `Functor.IsFibered`.
- `bridge/view`: the constructions deriving fibredness and pullback functors from a given
  `PullbackChoice`.

This file keeps the explicit choice data as the source-facing parameter and does not expose a
public global witness built from mathlib's noncanonical `pullbackObj`/`pullbackMap` choices. -/

/-- Definition 4.33.6: a choice of pullbacks for `p : S ⥤ C` consists of, for
every morphism `f : V ⟶ U` and every object `x` of the standard fiber over `U`, a chosen strongly
cartesian morphism `f^*x ⟶ x` lying over `f`. -/
structure PullbackChoice (p : S ⥤ C) where
  /-- The chosen pullback object `f^*x` in the fiber over the domain of `f`. -/
  obj {U V : C} (f : V ⟶ U) (x : Fiber p U) : Fiber p V
  /-- The chosen strongly cartesian morphism `f^*x ⟶ x` lying over `f`. -/
  map {U V : C} (f : V ⟶ U) (x : Fiber p U) : (obj f x).1 ⟶ x.1
  /-- The chosen comparison morphism is strongly cartesian over `f`. -/
  isStronglyCartesian {U V : C} (f : V ⟶ U) (x : Fiber p U) :
    p.IsStronglyCartesian f (map f x)

attribute [instance] PullbackChoice.isStronglyCartesian

end CategoryTheory

/- The chosen pullback object of `x` along `f` for the pullback choice `hc`. -/
notation:90 f:90 " ^*[" hc "] " x:91 => CategoryTheory.PullbackChoice.obj hc f x

namespace CategoryTheory

open Category Functor Fiber

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

namespace PullbackChoice

variable {p : S ⥤ C}

/-- A pullback choice already exhibits `p` as a fibred category. -/
theorem isFibered (hc : PullbackChoice p) : p.IsFibered :=
  IsFibered.of_exists_isStronglyCartesian fun x _ f ↦
    let x' : Fiber p (p.obj x) := .mk rfl
    ⟨(f ^*[hc] x').1, hc.map f x', hc.isStronglyCartesian f x'⟩

/-- A chosen pullback system induces the canonical fibred-category structure on `p`. -/
instance (hc : PullbackChoice p) : p.IsFibered :=
  hc.isFibered

variable (hc : PullbackChoice p)

/-- The map on morphisms induced by a chosen pullback system on a fibred category. -/
private noncomputable def pullbackMap
    {U V : C} (f : V ⟶ U) {x y : Fiber p U} (φ : x ⟶ y) :
    f ^*[hc] x ⟶ f ^*[hc] y :=
  let ψ : (f ^*[hc] x).1 ⟶ y.1 := hc.map f x ≫ φ.1
  letI : p.IsHomLift (𝟙 U) φ.1 := φ.2
  letI : p.IsHomLift f ψ := IsHomLift.comp_lift_id_right' p f (hc.map f x) U φ.1
  ⟨IsStronglyCartesian.map p f (hc.map f y) (id_comp f).symm ψ, inferInstance⟩

@[reassoc]
private theorem pullbackMap_fac
    {U V : C} (f : V ⟶ U) {x y : Fiber p U} (φ : x ⟶ y) :
    (hc.pullbackMap f φ).1 ≫ hc.map f y = hc.map f x ≫ φ.1 := by
  -- Unfold the chosen lift and read off its defining factorization through `hc.map f y`.
  simp [pullbackMap]

/-- The chosen pullback construction sends identity morphisms in a fiber to identity morphisms. -/
private theorem pullbackMap_id
    {U V : C} (f : V ⟶ U) (x : Fiber p U) :
    hc.pullbackMap f (𝟙 x) = 𝟙 (f ^*[hc] x) := by
  let η : f ^*[hc] x ⟶ f ^*[hc] x := 𝟙 (f ^*[hc] x)
  -- It is enough to compare the underlying arrows in the ambient category.
  apply Fiber.hom_ext
  change (hc.pullbackMap f (𝟙 x)).1 = η.1
  -- Both candidates are lifts over `𝟙 V` into the same strongly cartesian arrow `hc.map f x`.
  letI : p.IsHomLift (𝟙 V) (hc.pullbackMap f (𝟙 x)).1 := (hc.pullbackMap f (𝟙 x)).2
  letI : p.IsHomLift (𝟙 V) η.1 := η.2
  apply IsStronglyCartesian.ext p f (hc.map f x) (𝟙 V)
  -- After postcomposition with `hc.map f x`, both arrows become `hc.map f x`.
  calc
    (hc.pullbackMap f (𝟙 x)).1 ≫ hc.map f x
        = hc.map f x ≫ (𝟙 x : x ⟶ x).1 := by
            rw [pullbackMap_fac]
    _ = hc.map f x := by
          change hc.map f x ≫ 𝟙 x.1 = hc.map f x
          simp
    _ = η.1 ≫ hc.map f x := by
          change hc.map f x = 𝟙 (f ^*[hc] x).1 ≫ hc.map f x
          simp

/-- The chosen pullback construction respects composition in each fiber. -/
private theorem pullbackMap_comp
    {U V : C} (f : V ⟶ U) {x y z : Fiber p U} (φ : x ⟶ y) (ψ : y ⟶ z) :
    hc.pullbackMap f (φ ≫ ψ) =
      hc.pullbackMap f φ ≫ hc.pullbackMap f ψ := by
  -- It is enough to compare the underlying lifts in the ambient category.
  apply Fiber.hom_ext
  -- Reduce from equality in the fiber to equality of the ambient arrows.
  change (hc.pullbackMap f (φ ≫ ψ)).1 = (hc.pullbackMap f φ ≫ hc.pullbackMap f ψ).1
  -- The uniqueness lemma needs the projected fiber morphisms as explicit ambient lifts.
  letI : p.IsHomLift (𝟙 V) (hc.pullbackMap f (φ ≫ ψ)).1 := (hc.pullbackMap f (φ ≫ ψ)).2
  letI : p.IsHomLift (𝟙 V) (hc.pullbackMap f φ ≫ hc.pullbackMap f ψ).1 :=
    (hc.pullbackMap f φ ≫ hc.pullbackMap f ψ).2
  -- Both arrows are lifts over `𝟙 V` into the same strongly cartesian morphism `hc.map f z`.
  apply IsStronglyCartesian.ext p f (hc.map f z) (𝟙 V)
  -- After postcomposition with `hc.map f z`, both sides become the same composite.
  calc
    (hc.pullbackMap f (φ ≫ ψ)).1 ≫ hc.map f z
        = hc.map f x ≫ (φ ≫ ψ).1 := by
            rw [pullbackMap_fac]
    _ = (hc.map f x ≫ φ.1) ≫ ψ.1 := by
          change hc.map f x ≫ (φ.1 ≫ ψ.1) = (hc.map f x ≫ φ.1) ≫ ψ.1
          simp [Category.assoc]
    _ = ((hc.pullbackMap f φ).1 ≫ hc.map f y) ≫ ψ.1 := by
          rw [pullbackMap_fac]
    _ = (hc.pullbackMap f φ).1 ≫ (hc.map f y ≫ ψ.1) := by
          simp [Category.assoc]
    _ = (hc.pullbackMap f φ).1 ≫ ((hc.pullbackMap f ψ).1 ≫ hc.map f z) := by
          rw [← pullbackMap_fac]
    _ = (hc.pullbackMap f φ ≫ hc.pullbackMap f ψ).1 ≫ hc.map f z := by
          change
            (hc.pullbackMap f φ).1 ≫ ((hc.pullbackMap f ψ).1 ≫ hc.map f z) =
              ((hc.pullbackMap f φ).1 ≫ (hc.pullbackMap f ψ).1) ≫ hc.map f z
          simp [Category.assoc]

/-- The pullback functor on standard fibers associated to a chosen pullback system. -/
noncomputable def pullbackFunctor
    {U V : C} (f : V ⟶ U) :
    Fiber p U ⥤ Fiber p V where
  obj := fun x ↦ f ^*[hc] x
  map := hc.pullbackMap f
  map_id := hc.pullbackMap_id f
  map_comp := hc.pullbackMap_comp f

end PullbackChoice

end CategoryTheory

/-! ### Lemma_4_33_7 (from Chap04) -/
/-!
# Compatibility owner for Lemma 4.33.7

The source-text comparison, unit, and coherence package for chosen pullbacks now lives under the
slim `Chap04.CanonicalFiberPseudofunctor` owners. This file remains as a compatibility reexport
for callers that still import `Chap04.Lemma_4_33_7`.
-/

/-! ### Lemma_4_33_8 (from Chap04) -/
universe v u vS uS

namespace CategoryTheory

open BasedFunctor
open Bicategory
open Functor IsHomLift IsStronglyCartesian
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {X Y : BasedCategory.{vS, uS} C}

/- Domain-style sampling for Lemma 4.33.8:
- primary domain: fibered categories over a fixed base, and invariance of strong cartesianness /
  fibredness under equivalence in `Cat/C`;
- sampled owner API:
  `BasedFunctor.IsEquivalenceOverBase`,
  `Functor.IsStronglyCartesian`,
  `Functor.IsFibered`,
  `Functor.isFibered_iff_exists_isStronglyCartesian`,
  `BasedCategory` and `BasedFunctor`;
- best owner abstractions: `BasedFunctor.IsEquivalenceOverBase` for equivalences in `Cat/C`,
  together with `Functor.IsStronglyCartesian` and `Functor.IsFibered` for the transported owner
  properties.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma that a based equivalence over `C` preserves fibredness;
- `core/canonical`: `BasedFunctor.IsEquivalenceOverBase`, `Functor.IsStronglyCartesian`, and
  `Functor.IsFibered`;
- `bridge/view`: the explicit `EquivalenceOverBase` data attached to an owner-level
  `IsEquivalenceOverBase` hypothesis, used to transport strongly cartesian lifts across the
  quasi-inverse and the vertical unit/counit isomorphisms.

Primitive-vs-derived split:
- primitive data: the based categories `X`, `Y`, the based functor `F : X ⥤ᵇ Y`, the owner
  predicate `F.IsEquivalenceOverBase`, and the upstream owner predicates on the projection
  functors `X.p` and `Y.p`;
- derived API: the transport theorem for strongly cartesian morphisms and the resulting
  equivalence-invariance statement for fibredness. -/

namespace BasedFunctor

/-- Helper for Lemma 4.33.8: pulling a lifting problem back across the inverse in an explicit
equivalence over the base preserves the same base morphism. -/
lemma inverse_transport_lift_over_base
    (F : X ⥤ᵇ Y) (e : EquivalenceOverBase F)
    {x y : X.obj} (φ : x ⟶ y)
    {z : Y.obj} (g : Y.p.obj z ⟶ Y.p.obj (F.obj x))
    (ψ : z ⟶ F.obj y)
    [Y.p.IsHomLift (g ≫ Y.p.map (F.map φ)) ψ] :
    X.p.IsHomLift (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ)
      (e.inverse.map ψ ≫ e.unitIso.inv.app y) := by
  -- Rewrite the target lifting problem into the source base coordinates using the over-base
  -- equation attached to `F`.
  have hψY : Y.p.IsHomLift (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ) ψ := by
    refine IsHomLift.of_fac Y.p _ ψ rfl (F.w_obj y) ?_
    have hbase :
        g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ = Y.p.map ψ ≫ eqToHom (F.w_obj y) := by
      calc
        g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ
            = g ≫ Y.p.map (F.map φ) ≫ eqToHom (F.w_obj y) := by
                simpa [Category.assoc] using
                  (congrArg (fun k ↦ g ≫ k ≫ eqToHom (F.w_obj y))
                    (Functor.congr_hom F.w φ)).symm
        _ = Y.p.map ψ ≫ eqToHom (F.w_obj y) := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ k ≫ eqToHom (F.w_obj y))
                  (IsHomLift.eq_of_isHomLift Y.p (g ≫ Y.p.map (F.map φ)) ψ)
    simpa [Category.assoc] using hbase
  -- Pull the given lifted arrow back across the quasi-inverse.
  have hψX : X.p.IsHomLift (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ) (e.inverse.map ψ) :=
    (e.inverse.isHomLift_iff (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ) ψ).2 hψY
  -- The unit component is vertical, so composing with it keeps the same base map.
  have hη : X.p.IsHomLift (𝟙 (X.p.obj y)) (e.unitIso.inv.app y) := by
    simpa using BasedNatTrans.isHomLift e.unitIso.inv (rfl : X.p.obj y = X.p.obj y)
  exact @IsHomLift.comp_lift_id_right' _ _ _ _ X.p _ _ _ _ _
    (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ) (e.inverse.map ψ) hψX
    (X.p.obj y) (e.unitIso.inv.app y) hη

/-- Helper for Lemma 4.33.8: pushing a lifted morphism forward across the chosen equivalence over
the base preserves the same base morphism. -/
lemma forward_transport_lift_over_base
    (F : X ⥤ᵇ Y) (e : EquivalenceOverBase F)
    {x : X.obj} {z : Y.obj} (g : Y.p.obj z ⟶ X.p.obj x)
    (ξ : e.inverse.obj z ⟶ x)
    [X.p.IsHomLift g ξ] :
    Y.p.IsHomLift g (e.toEquivalence.counit.inv.app z ≫ F.map ξ) := by
  let E := e.toEquivalence
  -- Push the source lift forward along `F`, then precompose with the vertical counit inverse.
  have hξY : Y.p.IsHomLift g (F.map ξ) :=
    (F.isHomLift_iff g ξ).2 (show X.p.IsHomLift g ξ from inferInstance)
  -- The counit component is vertical, so precomposing with it preserves the base map.
  have hε : Y.p.IsHomLift (𝟙 (Y.p.obj z)) (E.counit.inv.app z) := by
    simpa [E] using BasedNatTrans.isHomLift E.counit.inv
      (rfl : Y.p.obj z = Y.p.obj z)
  exact @IsHomLift.comp_lift_id_left' _ _ _ _ Y.p _ _ _
    (Y.p.obj z) (E.counit.inv.app z) hε _ _ g (F.map ξ) hξY

/-- Helper for Lemma 4.33.8: appending the canonical base-change isomorphism from `F.w_obj`
does not change whether a target morphism is a lift. -/
lemma isHomLift_over_target_eq_iff
    (F : X ⥤ᵇ Y) {z : Y.obj} {x : X.obj}
    (g : Y.p.obj z ⟶ Y.p.obj (F.obj x))
    (θ : z ⟶ F.obj x) :
    Y.p.IsHomLift g θ ↔ Y.p.IsHomLift (g ≫ eqToHom (F.w_obj x)) θ := by
  -- The extra `eqToHom` only rewrites the codomain to the source-side base coordinates.
  simpa using IsHomLift.lift_comp_eqToHom_iff Y.p g θ (F.w_obj x)

/-- Helper for Lemma 4.33.8: a target-side factorization pulls back along the inverse together
with the unit inverse to the corresponding source-side factorization. -/
lemma pullback_factorization_of_map_factorization
    (F : X ⥤ᵇ Y) (e : EquivalenceOverBase F)
    {x y : X.obj} (φ : x ⟶ y)
    {z : Y.obj} {τ' : z ⟶ F.obj x} {ψ' : z ⟶ F.obj y}
    (hτ' : τ' ≫ F.map φ = ψ') :
    (e.inverse.map τ' ≫ e.unitIso.inv.app x) ≫ φ =
      e.inverse.map ψ' ≫ e.unitIso.inv.app y := by
  -- Rewrite the pulled-back `F.map φ` term using naturality of the unit inverse.
  calc
    (e.inverse.map τ' ≫ e.unitIso.inv.app x) ≫ φ
        = e.inverse.map τ' ≫ (e.unitIso.inv.app x ≫ φ) := by
            simp [Category.assoc]
    _ = e.inverse.map τ' ≫ (e.inverse.map (F.map φ) ≫ e.unitIso.inv.app y) := by
          simpa [Category.assoc] using
            (congrArg (fun k ↦ e.inverse.map τ' ≫ k) (e.unitIso.inv.naturality φ)).symm
    _ = e.inverse.map (τ' ≫ F.map φ) ≫ e.unitIso.inv.app y := by
          simp [Functor.map_comp, Category.assoc]
    _ = e.inverse.map ψ' ≫ e.unitIso.inv.app y := by
          rw [hτ']

/-- Helper for Lemma 4.33.8: after forgetting the based data, the component of the adjointified
left triangle is exactly the corresponding component equality of ordinary natural isomorphisms. -/
lemma adjointified_left_triangle_component_iso
    (F : X ⥤ᵇ Y) (e : EquivalenceOverBase F) (x : X.obj) :
    ((BasedNatTrans.forgetful X Y).mapIso
        (Bicategory.leftZigzagIso e.toEquivalence.unit e.toEquivalence.counit)).hom.app x =
      ((BasedNatTrans.forgetful X Y).mapIso
        (λ_ e.toEquivalence.hom ≪≫ (ρ_ e.toEquivalence.hom).symm)).hom.app x := by
  -- Forget the based 2-isomorphism to the ordinary functor category and evaluate at `x`.
  let Φ := congrArg (Functor.mapIso (BasedNatTrans.forgetful X Y)) e.toEquivalence.left_triangle
  -- This is the component form of the adjointified left triangle in the underlying category.
  exact congrArg (fun η => η.hom.app x) Φ

/-- Helper for Lemma 4.33.8: the inverse component of the forgotten adjointified left triangle is
the raw inverse comparison that underlies the desired push-pull identity. -/
lemma adjointified_left_triangle_inverse_component_iso
    (F : X ⥤ᵇ Y) (e : EquivalenceOverBase F) (x : X.obj) :
    ((BasedNatTrans.forgetful X Y).mapIso
        (Bicategory.leftZigzagIso e.toEquivalence.unit e.toEquivalence.counit)).inv.app x =
      ((BasedNatTrans.forgetful X Y).mapIso
        (λ_ e.toEquivalence.hom ≪≫ (ρ_ e.toEquivalence.hom).symm)).inv.app x := by
  -- Take the inverse component of the same forgotten left-triangle isomorphism.
  let Φ := congrArg (Functor.mapIso (BasedNatTrans.forgetful X Y)) e.toEquivalence.left_triangle
  -- This is the unsimplified inverse triangle comparison used in the remaining blocker.
  exact congrArg (fun η => η.inv.app x) Φ

/-- Helper for Lemma 4.33.8: the strict associator component in the forgotten functor-category
left-triangle comparison is the identity map on each object. -/
lemma forgotten_triangle_associator_component_eq_id
    (F : X ⥤ᵇ Y) (e : EquivalenceOverBase F) (x : X.obj) :
    (CategoryTheory.Bicategory.associator (e.toEquivalence.hom) (e.toEquivalence.inv) F).hom.app x =
      𝟙 (((e.toEquivalence.hom ≫ e.toEquivalence.inv) ≫ F).obj x) := by
  -- In the strict bicategory of categories over `C`, the associator is an `eqToIso`, so its
  -- component forgets to the identity arrow.
  simp [CategoryTheory.Bicategory.Strict.associator_eqToIso]
  rfl

/-- Helper for Lemma 4.33.8: the left unitor component on a based functor is the identity on each
object after forgetting to the underlying functor category. -/
lemma forgotten_triangle_left_unitor_component_eq_id
    (F : X ⥤ᵇ Y) (x : X.obj) :
    (CategoryTheory.Bicategory.leftUnitor (B := BasedCategory C) F).hom.app x = 𝟙 (F.obj x) := by
  -- The strict left unitor is also an `eqToIso`, hence has identity components.
  simp [CategoryTheory.Bicategory.Strict.leftUnitor_eqToIso]
  rfl

/-- Helper for Lemma 4.33.8: the inverse right-unitor component on a based functor is the
identity on each object after forgetting to the underlying functor category. -/
lemma forgotten_triangle_right_unitor_inv_component_eq_id
    (F : X ⥤ᵇ Y) (x : X.obj) :
    (CategoryTheory.Bicategory.rightUnitor (B := BasedCategory C) F).inv.app x =
      𝟙 (F.obj x) := by
  -- The strict right unitor is an `eqToIso`, so its inverse component is still the identity.
  simp [CategoryTheory.Bicategory.Strict.rightUnitor_eqToIso]
  rfl

/-- Helper for Lemma 4.33.8: the forgotten left-zigzag component is the ordinary composite of the
unit component followed by the counit component. -/
lemma forgotten_left_zigzag_hom_app
    (F : X ⥤ᵇ Y) (e : EquivalenceOverBase F) (x : X.obj) :
    (CategoryTheory.Bicategory.leftZigzag e.toEquivalence.unit.hom
        e.toEquivalence.counit.hom).app x =
      F.map (e.unitIso.hom.app x) ≫ e.toEquivalence.counit.hom.app (F.obj x) := by
  -- Expand the inserted bicategorical coherence, then collapse the strict associator and the
  -- whiskered identity component.
  change F.map (e.unitIso.hom.app x) ≫
      ((CategoryTheory.BicategoricalCoherence.iso.hom :
        ((e.toEquivalence.hom ≫ e.toEquivalence.inv) ≫ e.toEquivalence.hom) ⟶
          e.toEquivalence.hom ≫ (e.toEquivalence.inv ≫ e.toEquivalence.hom)).app x) ≫
      e.toEquivalence.counit.hom.app (F.obj x) = _
  dsimp [CategoryTheory.BicategoricalCoherence.iso, CategoryTheory.BicategoricalCoherence.assoc]
  change F.map (e.unitIso.hom.app x) ≫
      ((α_ e.toEquivalence.hom e.toEquivalence.inv e.toEquivalence.hom).hom.app x ≫
        (CategoryTheory.BasedCategory.whiskerRight
          (CategoryTheory.BasedNatTrans.id F) (e.inverse ⋙ F)).app x) ≫
      e.toEquivalence.counit.hom.app (F.obj x) = _
  have hassoc :
      (α_ e.toEquivalence.hom e.toEquivalence.inv e.toEquivalence.hom).hom.app x =
        𝟙 (((e.toEquivalence.hom ≫ e.toEquivalence.inv) ≫ e.toEquivalence.hom).obj x) := by
    -- The strict associator contributes only the identity component after forgetting.
    simpa using forgotten_triangle_associator_component_eq_id F e x
  rw [hassoc]
  simp [CategoryTheory.BasedCategory.whiskerRight, CategoryTheory.BasedNatTrans.id]

/-- Helper for Lemma 4.33.8: the forgotten hom-side right-hand comparison in the left triangle is
the identity map on each object. -/
lemma forgotten_left_triangle_rhs_hom_app_eq_id
    (F : X ⥤ᵇ Y) (e : EquivalenceOverBase F) (x : X.obj) :
    ((λ_ e.toEquivalence.hom).hom ≫ (ρ_ e.toEquivalence.hom).inv).app x = 𝟙 (F.obj x) := by
  -- Both unitors are strict identities in `BasedCategory`, so the composite stays the identity.
  change (CategoryTheory.BasedNatTrans.comp (CategoryTheory.BasedNatTrans.id F)
      (CategoryTheory.BasedNatTrans.id F)).app x = _
  rw [CategoryTheory.BasedNatTrans.comp]
  simp [CategoryTheory.BasedNatTrans.id]

/-- Helper for Lemma 4.33.8: after forgetting the based adjointified left triangle, the hom-side
component reduces to the ordinary unit-counit cancellation formula. -/
lemma forgotten_left_triangle_hom_component_simplified
    (F : X ⥤ᵇ Y) (e : EquivalenceOverBase F) (x : X.obj) :
    F.map (e.unitIso.hom.app x) ≫ e.toEquivalence.counit.hom.app (F.obj x) = 𝟙 (F.obj x) := by
  -- Route correction: evaluate the bicategorical left triangle at `x`, then rewrite its two sides
  -- into the ordinary unit-counit composite and the identity map on `F.obj x`.
  have htriangle :=
    congrArg (fun η ↦ η.app x) (CategoryTheory.Bicategory.Equivalence.left_triangle_hom
      e.toEquivalence)
  have htriangle' :
      (CategoryTheory.Bicategory.leftZigzag e.toEquivalence.unit.hom
          e.toEquivalence.counit.hom).app x =
        ((λ_ e.toEquivalence.hom).hom ≫ (ρ_ e.toEquivalence.hom).inv).app x := by
    simpa using htriangle
  -- The adapter lemmas identify the two bicategorical sides with the ordinary maps used
  -- downstream in the transport proof.
  exact (forgotten_left_zigzag_hom_app F e x).symm.trans <|
    htriangle'.trans (forgotten_left_triangle_rhs_hom_app_eq_id F e x)

/-- Helper for Lemma 4.33.8: the inverse counit component of the adjointified equivalence
cancels the raw unit inverse on each target object. -/
lemma adjointified_left_triangle_inverse_component_simplified
    (F : X ⥤ᵇ Y) (e : EquivalenceOverBase F) (x : X.obj) :
    e.toEquivalence.counit.inv.app (F.obj x) ≫ F.map (e.unitIso.inv.app x) = 𝟙 (F.obj x) := by
  -- Package the forgotten based data as an ordinary equivalence and use its inverse triangle
  -- identity instead of normalizing the inverse left-triangle component directly.
  let E : X.obj ≌ Y.obj :=
    CategoryTheory.Equivalence.mk'
      F.toFunctor e.inverse.toFunctor
      ((BasedNatTrans.forgetful X X).mapIso e.unitIso)
      ((BasedNatTrans.forgetful Y Y).mapIso e.toEquivalence.counit)
      (fun x ↦ by
        simpa using forgotten_left_triangle_hom_component_simplified F e x)
  simpa [E] using E.counitIso_functor_comp x

/-- Helper for Lemma 4.33.8: pushing the pulled-back morphism forward with the adjointified
counit inverse recovers the original target morphism. -/
lemma pushforward_pullback_eq
    (F : X ⥤ᵇ Y) (e : EquivalenceOverBase F)
    {x : X.obj} {z : Y.obj} (θ : z ⟶ F.obj x) :
    e.toEquivalence.counit.inv.app z ≫
        F.map (e.inverse.map θ ≫ e.unitIso.inv.app x) = θ := by
  -- Move `θ` across the counit inverse, then collapse the remaining counit-unit tail.
  rw [Functor.map_comp]
  have hnat :
      e.toEquivalence.counit.inv.app z ≫ F.map (e.inverse.map θ) ≫
          F.map (e.unitIso.inv.app x) =
        θ ≫ e.toEquivalence.counit.inv.app (F.obj x) ≫
          F.map (e.unitIso.inv.app x) := by
    simpa [Functor.comp_map, Category.assoc] using
      (congrArg (fun k ↦ k ≫ F.map (e.unitIso.inv.app x))
        (e.toEquivalence.counit.inv.naturality θ)).symm
  have htail :
      θ ≫ e.toEquivalence.counit.inv.app (F.obj x) ≫ F.map (e.unitIso.inv.app x) = θ := by
    simpa [Category.assoc] using
      congrArg (fun k ↦ θ ≫ k)
        (adjointified_left_triangle_inverse_component_simplified F e x)
  exact hnat.trans htail

/-- An equivalence over the base category sends strongly cartesian morphisms to strongly
cartesian morphisms. The base map is taken in the owner form from the source morphism `φ`. -/
theorem isStronglyCartesian_map_of_isEquivalenceOverBase
    (F : X ⥤ᵇ Y) (hF : F.IsEquivalenceOverBase)
    {x y : X.obj} (φ : x ⟶ y)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ) :
    Y.p.IsStronglyCartesian (Y.p.map (F.map φ)) (F.map φ) := by
  let e : EquivalenceOverBase F := Classical.choice hF.nonempty
  refine
    { toIsHomLift := by
        infer_instance
      universal_property' := ?_ }
  intro z g ψ' hψ'
  -- Pull the problem back to `X` and solve it there using the strong cartesianness of `φ`.
  let ψX : e.inverse.obj z ⟶ y := e.inverse.map ψ' ≫ e.unitIso.inv.app y
  have hψXlift :
      X.p.IsHomLift ((g ≫ eqToHom (F.w_obj x)) ≫ X.p.map φ) ψX :=
    by simpa [ψX] using inverse_transport_lift_over_base F e φ g ψ'
  letI : X.p.IsHomLift ((g ≫ eqToHom (F.w_obj x)) ≫ X.p.map φ) ψX := hψXlift
  obtain ⟨ξ, hξ, hξuniq⟩ :=
    IsStronglyCartesian.universal_property X.p (X.p.map φ) φ
      (g ≫ eqToHom (F.w_obj x))
      (((g ≫ eqToHom (F.w_obj x)) ≫ X.p.map φ)) rfl ψX
  -- Push the source lift forward along the adjointified counit.
  let E := e.toEquivalence
  letI : X.p.IsHomLift (g ≫ eqToHom (F.w_obj x)) ξ := hξ.1
  let ξ' : z ⟶ F.obj x := E.counit.inv.app z ≫ F.map ξ
  have hξ'base :
      Y.p.IsHomLift (g ≫ eqToHom (F.w_obj x)) ξ' :=
    forward_transport_lift_over_base F e (g ≫ eqToHom (F.w_obj x)) ξ
  have hξ' : Y.p.IsHomLift g ξ' :=
    (isHomLift_over_target_eq_iff F g ξ').mpr hξ'base
  have hpushψ : E.counit.inv.app z ≫ F.map ψX = ψ' := by
    change e.toEquivalence.counit.inv.app z ≫
        F.map (e.inverse.map ψ' ≫ e.unitIso.inv.app y) = ψ'
    simpa [ψX, E, Functor.map_comp, Category.assoc] using
      pushforward_pullback_eq F e ψ'
  refine ⟨ξ', ⟨hξ', ?_⟩, ?_⟩
  · -- The pushed-forward lift factors through `F.map φ` by the pull-push comparison lemma.
    have hstep1 : ξ' ≫ F.map φ = E.counit.inv.app z ≫ F.map (ξ ≫ φ) := by
      simp [ξ', E, Functor.map_comp, Category.assoc]
    have hstep2 : E.counit.inv.app z ≫ F.map (ξ ≫ φ) = E.counit.inv.app z ≫ F.map ψX := by
      simpa [E] using congrArg (fun k ↦ E.counit.inv.app z ≫ F.map k) hξ.2
    exact hstep1.trans <| hstep2.trans hpushψ
  · intro η hη
    -- Pull any competing target lift back to `X` and compare there by uniqueness.
    have hηbase :
        Y.p.IsHomLift (g ≫ eqToHom (F.w_obj x)) η :=
      (isHomLift_over_target_eq_iff F g η).mp hη.1
    have hηpull :
        X.p.IsHomLift (g ≫ eqToHom (F.w_obj x))
          (e.inverse.map η ≫ e.unitIso.inv.app x) := by
      have hηpre : X.p.IsHomLift (g ≫ eqToHom (F.w_obj x)) (e.inverse.map η) :=
        (e.inverse.isHomLift_iff (g ≫ eqToHom (F.w_obj x)) η).2 hηbase
      have hηunit : X.p.IsHomLift (𝟙 (X.p.obj x)) (e.unitIso.inv.app x) := by
        simpa using BasedNatTrans.isHomLift e.unitIso.inv (rfl : X.p.obj x = X.p.obj x)
      exact @IsHomLift.comp_lift_id_right' _ _ _ _ X.p _ _ _ _ _
        (g ≫ eqToHom (F.w_obj x)) (e.inverse.map η) hηpre
        (X.p.obj x) (e.unitIso.inv.app x) hηunit
    have hηfac :
        (e.inverse.map η ≫ e.unitIso.inv.app x) ≫ φ = ψX := by
      simpa [ψX] using pullback_factorization_of_map_factorization F e φ hη.2
    have hηeq : e.inverse.map η ≫ e.unitIso.inv.app x = ξ :=
      hξuniq _ ⟨hηpull, hηfac⟩
    -- Push the equality back to the target using the same comparison lemma.
    have hpushη :
        η = E.counit.inv.app z ≫ F.map (e.inverse.map η ≫ e.unitIso.inv.app x) := by
      symm
      change e.toEquivalence.counit.inv.app z ≫
          F.map (e.inverse.map η ≫ e.unitIso.inv.app x) = η
      simpa [E, Functor.map_comp, Category.assoc] using
        pushforward_pullback_eq F e η
    have hstepη :
        E.counit.inv.app z ≫ F.map (e.inverse.map η ≫ e.unitIso.inv.app x) =
          E.counit.inv.app z ≫ F.map ξ := by
      simpa [E] using congrArg (fun k ↦ E.counit.inv.app z ≫ F.map k) hηeq
    exact hpushη.trans <| hstepη.trans rfl

/-- Helper for Lemma 4.33.8: if a morphism is already strongly cartesian, then any other lift of
the same arrow through the same morphism has the same strong-cartesian structure. -/
lemma isStronglyCartesian_rebase_of_same_lift
    {𝒮 : Type u} {𝒳 : Type uS} [Category.{v} 𝒮] [Category.{vS} 𝒳]
    (p : 𝒳 ⥤ 𝒮)
    {a b : 𝒳} {f f' : p.obj a ⟶ p.obj b} (φ : a ⟶ b)
    [p.IsStronglyCartesian f φ] [p.IsHomLift f' φ] :
    p.IsStronglyCartesian f' φ := by
  -- Both lift witnesses identify their base arrows with `p.map φ`, so the structure rebases by
  -- substitution.
  have hf : f = p.map φ := IsHomLift.eq_of_isHomLift p f φ
  have hf' : f' = p.map φ := IsHomLift.eq_of_isHomLift p f' φ
  subst hf
  subst hf'
  infer_instance

/-- Helper for Lemma 4.33.8: an owner-level strong-cartesian structure rebases along any external
lift witness for the same morphism. -/
lemma isStronglyCartesian_of_external_hom_lift
    {𝒮 : Type u} {𝒳 : Type uS} [Category.{v} 𝒮] [Category.{vS} 𝒳]
    (p : 𝒳 ⥤ 𝒮)
    {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} (φ : a ⟶ b)
    [p.IsStronglyCartesian (p.map φ) φ] [p.IsHomLift f φ] :
    p.IsStronglyCartesian f φ := by
  -- Normalize the external base objects to the actual source and target of `φ`, then rebase
  -- along the two lift witnesses for the same morphism.
  have ha : p.obj a = R := IsHomLift.domain_eq p f φ
  have hb : p.obj b = S := IsHomLift.codomain_eq p f φ
  subst ha
  subst hb
  exact isStronglyCartesian_rebase_of_same_lift (p := p) (f := p.map φ) (f' := f) φ

/-- Helper for Lemma 4.33.8: if the codomain of a strongly cartesian morphism is identified with
an external target object, then the strong-cartesian structure rebases to the owner map
`p.map φ`. -/
lemma isStronglyCartesian_rebase_over_target_eq
    {𝒮 : Type u} {𝒳 : Type uS} [Category.{v} 𝒮] [Category.{vS} 𝒳]
    (p : 𝒳 ⥤ 𝒮)
    {R S : 𝒮} {a b : 𝒳} (hb : p.obj b = S)
    {f : R ⟶ S} (φ : a ⟶ b)
    [p.IsStronglyCartesian f φ] :
    p.IsStronglyCartesian (p.map φ) φ := by
  -- Reindex both ends of the external base morphism to the actual source and target of `φ`.
  have ha : p.obj a = R := IsHomLift.domain_eq p f φ
  subst ha
  subst hb
  exact isStronglyCartesian_rebase_of_same_lift (p := p) (f := f) (f' := p.map φ) φ

/-- Helper for Lemma 4.33.8: an equivalence over the base sends fibredness forward. -/
private theorem isFibered_of_isEquivalenceOverBase
    (F : X ⥤ᵇ Y) (hF : F.IsEquivalenceOverBase) :
    X.p.IsFibered → Y.p.IsFibered := by
  intro hX
  let e : EquivalenceOverBase F := Classical.choice hF.nonempty
  -- Use the strongly-cartesian lift criterion, transporting a chosen source lift and then
  -- composing with the vertical counit component to land over the original target object.
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro y V f
  letI : X.p.IsFibered := hX
  obtain ⟨x, φ, hφcart⟩ := IsPreFibered.exists_isCartesian X.p (e.inverse.w_obj y) f
  letI : X.p.IsCartesian f φ := hφcart
  -- Route correction: first rebase the chosen source lift to its owner map, then transport it
  -- across `F` and compose with the vertical counit component over `y`.
  have hφstrong : X.p.IsStronglyCartesian f φ :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian X.p f φ
  have hφowner : X.p.IsStronglyCartesian (X.p.map φ) φ := by
    letI : X.p.IsStronglyCartesian f φ := hφstrong
    exact isStronglyCartesian_rebase_over_target_eq (p := X.p) (hb := e.inverse.w_obj y)
      (f := f) φ
  have hFφstrong_owner : Y.p.IsStronglyCartesian (Y.p.map (F.map φ)) (F.map φ) :=
    isStronglyCartesian_map_of_isEquivalenceOverBase F hF φ hφowner
  have hFφlift : Y.p.IsHomLift f (F.map φ) :=
    (F.isHomLift_iff f φ).2 (show X.p.IsHomLift f φ from inferInstance)
  have hFφstrong : Y.p.IsStronglyCartesian f (F.map φ) := by
    -- Rebase the owner-level strong-cartesian structure using the explicit external lift over `f`.
    letI : Y.p.IsStronglyCartesian (Y.p.map (F.map φ)) (F.map φ) := hFφstrong_owner
    letI : Y.p.IsHomLift f (F.map φ) := hFφlift
    exact isStronglyCartesian_of_external_hom_lift (p := Y.p) (f := f) (φ := F.map φ)
  have hεlift : Y.p.IsHomLift (𝟙 (Y.p.obj y)) (e.counitIso.hom.app y) := by
    simpa using BasedNatTrans.isHomLift e.counitIso.hom (rfl : Y.p.obj y = Y.p.obj y)
  have hεstrong : Y.p.IsStronglyCartesian (𝟙 (Y.p.obj y)) (e.counitIso.hom.app y) := by
    let epsIso := (BasedNatTrans.forgetful Y Y).mapIso e.counitIso
    refine
      { toIsHomLift := hεlift
        universal_property' := ?_ }
    intro z g τ hτ
    -- Any lifting problem through the vertical counit is solved by composing with its inverse.
    let χ : z ⟶ F.obj (e.inverse.obj y) := τ ≫ e.counitIso.inv.app y
    have hτ' : Y.p.IsHomLift g τ := by
      simpa using hτ
    have hεinv : Y.p.IsHomLift (𝟙 (Y.p.obj y)) (e.counitIso.inv.app y) := by
      simpa using BasedNatTrans.isHomLift e.counitIso.inv (rfl : Y.p.obj y = Y.p.obj y)
    have hχ : Y.p.IsHomLift g χ := by
      exact @IsHomLift.comp_lift_id_right' _ _ _ _ Y.p _ _ _ _ _
        g τ hτ' (Y.p.obj y) (e.counitIso.inv.app y) hεinv
    refine ⟨χ, ⟨hχ, ?_⟩, ?_⟩
    · simpa [χ, epsIso, Category.assoc] using
        congrArg (fun k ↦ τ ≫ k) (epsIso.inv_hom_id_app y)
    · intro η hη
      have hηcomp : η = η ≫ e.counitIso.hom.app y ≫ e.counitIso.inv.app y := by
        rw [← Category.assoc]
        simpa [epsIso] using
          congrArg (fun k ↦ η ≫ k) (epsIso.hom_inv_id_app y).symm
      calc
        η = η ≫ e.counitIso.hom.app y ≫ e.counitIso.inv.app y := hηcomp
        _ = τ ≫ e.counitIso.inv.app y := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ k ≫ e.counitIso.inv.app y) hη.2
        _ = χ := rfl
  let ψ : F.obj x ⟶ y := F.map φ ≫ e.counitIso.hom.app y
  have hψstrong : Y.p.IsStronglyCartesian f ψ := by
    let epsIso := (BasedNatTrans.forgetful Y Y).mapIso e.counitIso
    -- First record that the composite `ψ` still lies over the original external base map `f`.
    have hψlift : Y.p.IsHomLift f ψ := by
      simpa [ψ, Category.assoc] using
        @IsHomLift.comp_lift_id_right' _ _ _ _ Y.p _ _ _ _ _
          f (F.map φ) hFφlift (Y.p.obj y) (e.counitIso.hom.app y) hεlift
    refine
      { toIsHomLift := hψlift
        universal_property' := ?_ }
    intro z g τ hτ
    -- Cancel the vertical counit component on the right and solve the remaining lifting problem
    -- through `F.map φ`.
    let τ' : z ⟶ F.obj (e.inverse.obj y) := τ ≫ e.counitIso.inv.app y
    have hτ' : Y.p.IsHomLift (g ≫ f) τ' := by
      have hτlift : Y.p.IsHomLift (g ≫ f) τ := by
        simpa using hτ
      have hεinv : Y.p.IsHomLift (𝟙 (Y.p.obj y)) (e.counitIso.inv.app y) := by
        simpa using BasedNatTrans.isHomLift e.counitIso.inv (rfl : Y.p.obj y = Y.p.obj y)
      simpa [τ'] using
        @IsHomLift.comp_lift_id_right' _ _ _ _ Y.p _ _ _ _ _
          (g ≫ f) τ hτlift (Y.p.obj y) (e.counitIso.inv.app y) hεinv
    letI : Y.p.IsStronglyCartesian f (F.map φ) := hFφstrong
    letI : Y.p.IsHomLift (g ≫ f) τ' := hτ'
    obtain ⟨χ, hχ, hχuniq⟩ :=
      IsStronglyCartesian.universal_property Y.p f (F.map φ) g (g ≫ f) rfl τ'
    refine ⟨χ, ⟨hχ.1, ?_⟩, ?_⟩
    · -- Compose the solved factorization back with the counit component to recover `τ`.
      have hτcancel : τ' ≫ e.counitIso.hom.app y = τ := by
        calc
          τ' ≫ e.counitIso.hom.app y
              = τ ≫ (e.counitIso.inv.app y ≫ e.counitIso.hom.app y) := by
                  simp [τ', Category.assoc]
          _ = τ := by
                simpa [Category.assoc] using
                  congrArg (fun k ↦ τ ≫ k) (epsIso.inv_hom_id_app y)
      have hχψ : χ ≫ ψ = τ' ≫ e.counitIso.hom.app y := by
        calc
          χ ≫ ψ = (χ ≫ F.map φ) ≫ e.counitIso.hom.app y := by
              simp [ψ, Category.assoc]
          _ = τ' ≫ e.counitIso.hom.app y := by
                simpa [Category.assoc] using
                  congrArg (fun k ↦ k ≫ e.counitIso.hom.app y) hχ.2
      exact hχψ.trans (by simpa using hτcancel)
    · intro η hη
      have hηcancel : (η ≫ ψ) ≫ e.counitIso.inv.app y = η ≫ F.map φ := by
        calc
          (η ≫ ψ) ≫ e.counitIso.inv.app y
              = η ≫ F.map φ ≫ (e.counitIso.hom.app y ≫ e.counitIso.inv.app y) := by
                  simp [ψ, Category.assoc]
          _ = η ≫ F.map φ := by
                simpa [Category.assoc] using
                  congrArg (fun k ↦ η ≫ F.map φ ≫ k) (epsIso.hom_inv_id_app y)
      have hηfac :
          η ≫ F.map φ = τ' := by
        have hηstep2 : (η ≫ ψ) ≫ e.counitIso.inv.app y = τ ≫ e.counitIso.inv.app y := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ k ≫ e.counitIso.inv.app y) hη.2
        have hηstep3 : τ ≫ e.counitIso.inv.app y = τ' := by
          simpa [τ']
        exact hηcancel.symm.trans (hηstep2.trans hηstep3)
      exact hχuniq _ ⟨hη.1, hηfac⟩
  exact ⟨F.obj x, ψ, hψstrong⟩

/-- Lemma 4.33.8: if `F : X ⥤ᵇ Y` is an equivalence over `C`, then `X` is fibred over `C` if and
only if `Y` is fibred over `C`. -/
theorem isFibered_iff_of_equivalence_over_base
    (F : X ⥤ᵇ Y) (hF : F.IsEquivalenceOverBase) :
    X.p.IsFibered ↔ Y.p.IsFibered := by
  let e : EquivalenceOverBase F := Classical.choice hF.nonempty
  constructor
  · -- Transport fibredness forward along `F`.
    exact isFibered_of_isEquivalenceOverBase F hF
  · -- Apply the same forward argument to the chosen quasi-inverse.
    exact isFibered_of_isEquivalenceOverBase e.inverse e.inverse_isEquivalenceOverBase

end BasedFunctor

end CategoryTheory
