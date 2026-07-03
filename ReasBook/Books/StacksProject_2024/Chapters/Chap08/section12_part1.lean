import Mathlib
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_8_12_1 (from Chap08) -/
open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open Limits CategoricalPullback

universe uC uD uS vC vD vS

namespace CategoryTheory

section

/- Domain-style sampling for Lemma 8.12.1:
- primary domain: fibred categories and categorical pullbacks of functors.
- inspected owner-level declarations:
  `Functor.IsFibered`,
  `Functor.IsFibered.of_exists_isStronglyCartesian`,
  `CategoricalPullback`,
  `CategoricalPullback.π₁`.
- best owner abstraction: the canonical owner predicate is `Functor.IsFibered`, applied to the
  pullback projection `π₁ u p`; `CategoricalPullback u p` is the canonical pullback model.
- primitive data: a functor `u : C ⥤ D`, a fibred functor `p : S ⥤ D`, and the pullback category
  `CategoricalPullback u p`.
- derived API: the induced fibred structure on `π₁ u p`.

Source/core/bridge triage:
- `source-facing`: `pullback_projection_is_fibered`.
- `core/canonical`: `Functor.IsFibered` and `CategoricalPullback`.
- `bridge/view`: the instance on `π₁ u p`, derived from the source-facing theorem without adding a
  parallel owner. -/

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]
variable (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]

/-- Lemma 8.12.1: if `p : S ⥤ D` is a fibred category over `D` and `u : C ⥤ D`, then the
pullback category `u^p S`, modeled by the categorical pullback `CategoricalPullback u p`, is a
fibred category over `C` via the first projection. -/
-- Proof sketch: for an arrow `a : U ⟶ U'` in `C` and an object of the pullback category over
-- `U'`, choose a strongly cartesian lift in `S` of `u.map a`; pairing it with `a` gives a lift in
-- the pullback category. Strong-cartesianness in the pullback is detected on the second
-- component, so the existence of such lifts in `S` upgrades to fibredness of the first
-- projection.
theorem pullback_projection_is_fibered
    : (π₁ u p).IsFibered := by
  refine IsFibered.of_exists_isStronglyCartesian ?_
  intro x R f
  let baseMap : u.obj R ⟶ p.obj x.snd := u.map f ≫ x.iso.hom
  obtain ⟨y, ψ, hψcart⟩ := IsPreFibered.exists_isCartesian p rfl baseMap
  letI : p.IsCartesian baseMap ψ := hψcart
  letI : p.IsStronglyCartesian baseMap ψ :=
    IsFibered.isStronglyCartesian_of_isCartesian p baseMap ψ
  have hy : p.obj y = u.obj R := IsHomLift.domain_eq p baseMap ψ
  let y' : CategoricalPullback u p :=
    { fst := R
      snd := y
      iso := eqToIso hy.symm }
  let φ : y' ⟶ x :=
    { fst := f
      snd := ψ
      w := by
        dsimp [y', baseMap]
        have hψfac : p.map ψ = eqToHom hy ≫ baseMap := by
          simpa [baseMap] using (IsHomLift.fac' p baseMap ψ)
        calc
          baseMap = eqToHom hy.symm ≫ (eqToHom hy ≫ baseMap) := by simp
          _ = eqToHom hy.symm ≫ p.map ψ := by rw [hψfac] }
  refine ⟨y', φ, ?_⟩
  change (π₁ u p).IsStronglyCartesian f φ
  refine
    { toIsHomLift := by
        simpa [φ] using
          (show (π₁ u p).IsHomLift ((π₁ u p).map φ) φ from inferInstance)
      universal_property' := ?_ }
  intro z g θ hθ
  have hθfst : g ≫ f = θ.fst := IsHomLift.eq_of_isHomLift (π₁ u p) (g ≫ f) θ
  have hθsnd : p.map θ.snd = (z.iso.inv ≫ u.map g) ≫ baseMap := by
    calc
      p.map θ.snd = z.iso.inv ≫ (z.iso.hom ≫ p.map θ.snd) := by simp
      _ = z.iso.inv ≫ (u.map θ.fst ≫ x.iso.hom) := by rw [θ.w]
      _ = z.iso.inv ≫ u.map g ≫ u.map f ≫ x.iso.hom := by
        rw [← hθfst]
        simp [Functor.map_comp, Category.assoc]
      _ = (z.iso.inv ≫ u.map g) ≫ baseMap := by
        simp [baseMap, Category.assoc]
  letI : p.IsHomLift ((z.iso.inv ≫ u.map g) ≫ baseMap) θ.snd :=
    IsHomLift.of_fac' p (((z.iso.inv ≫ u.map g) ≫ baseMap)) θ.snd rfl rfl (by
      simpa using hθsnd)
  obtain ⟨χ, hχ, hχuniq⟩ :=
    IsStronglyCartesian.universal_property p baseMap ψ (z.iso.inv ≫ u.map g)
      (((z.iso.inv ≫ u.map g) ≫ baseMap)) rfl θ.snd
  letI : p.IsHomLift (z.iso.inv ≫ u.map g) χ := hχ.1
  let χ' : z ⟶ y' :=
    { fst := g
      snd := χ
      w := by
        have hχfac : p.map χ = eqToHom rfl ≫ (z.iso.inv ≫ u.map g) ≫ eqToHom hy.symm := by
          simpa using (IsHomLift.fac' p (z.iso.inv ≫ u.map g) χ)
        dsimp [y']
        calc
          u.map g ≫ eqToHom hy.symm = z.iso.hom ≫ (z.iso.inv ≫ u.map g) ≫ eqToHom hy.symm := by
            simp [Category.assoc]
          _ = z.iso.hom ≫ p.map χ := by
            rw [hχfac]
            simp [Category.assoc] }
  refine ⟨χ', ⟨by
    simpa [χ'] using
      (show (π₁ u p).IsHomLift ((π₁ u p).map χ') χ' from inferInstance), ?_⟩, ?_⟩
  · ext
    · simpa [χ', φ] using hθfst
    · exact hχ.2
  · intro τ hτ
    have hτfst : g = τ.fst := by
      simpa using
        (@IsHomLift.eq_of_isHomLift _ _ _ _ (π₁ u p) _ _ g τ hτ.1)
    apply CategoricalPullback.hom_ext
    · simpa [χ'] using hτfst.symm
    · have hτsnd : p.map τ.snd = z.iso.inv ≫ u.map g ≫ eqToHom hy.symm := by
        calc
          p.map τ.snd = z.iso.inv ≫ (z.iso.hom ≫ p.map τ.snd) := by simp
          _ = z.iso.inv ≫ (u.map τ.fst ≫ y'.iso.hom) := by
            rw [← τ.w]
          _ = z.iso.inv ≫ (u.map τ.fst ≫ eqToHom hy.symm) := by
            dsimp [y']
          _ = z.iso.inv ≫ u.map g ≫ eqToHom hy.symm := by
            simp [hτfst]
      letI : p.IsHomLift (z.iso.inv ≫ u.map g) τ.snd :=
        IsHomLift.of_fac' p (z.iso.inv ≫ u.map g) τ.snd rfl hy (by
          simpa using hτsnd)
      have hτcomp : τ.snd ≫ ψ = θ.snd := by
        simpa using congrArg CategoricalPullback.Hom.snd hτ.2
      exact hχuniq τ.snd ⟨inferInstance, hτcomp⟩

instance
    : (π₁ u p).IsFibered :=
  pullback_projection_is_fibered u p

end

end CategoryTheory

/-! ### Lemma_8_12_2 (from Chap08) -/
open CategoryTheory.Limits

universe uC uD uS vC vD vS

namespace CategoryTheory

section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)

/-- Helper for Lemma 8.12.2: the canonical fiber pseudofunctor of the pullback projection along
`u` inherits the stack condition from `p` over `(D, K)`. -/
theorem pullback_projection_canonicalFiber_isStack
    [Functor.IsContinuous u J K]
    (p : S ⥤ D) [IsStackOnSite K p] :
    Pseudofunctor.IsStack (canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)) J := by
  sorry

/-- Lemma 8.12.2: if `u : C ⥤ D` is a continuous functor of sites and `X` is a stack over
`(D, K)` with projection `p : S ⥤ D`, then the pullback category `u^p S`, modeled by the
categorical pullback `CategoricalPullback u p`, is a stack over `(C, J)`. -/
theorem continuous_pullback_isStackOnSite
    [Functor.IsContinuous u J K]
    (p : S ⥤ D) [IsStackOnSite K p] :
    IsStackOnSite J (CategoricalPullback.π₁ u p) := by
  letI :
      Pseudofunctor.IsStack (canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)) J :=
    pullback_projection_canonicalFiber_isStack (J := J) (K := K) u p
  infer_instance

end

end CategoryTheory

/-! ### Lemma_8_12_3 (from Chap08) -/
open CategoryTheory.Limits
open Functor

universe uC uD uS vC vD vS

namespace CategoryTheory

section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D) (p : S ⥤ D)

/- Domain-style sampling for Lemma 8.12.3:
- primary domain: stacks in groupoids over sites and their pullback along a continuous functor.
- inspected owner-level declarations:
  `IsStackInGroupoids`,
  `continuous_pullback_isStackOnSite`,
  the canonical `IsFibered` instance on `CategoricalPullback.π₁ u p`,
  `IsFibredInGroupoids`.
- best owner abstraction: the source-facing result should stay the canonical owner statement
  `IsStackInGroupoids J (CategoricalPullback.π₁ u p)`, assembled from the already-canonical
  stack-on-site pullback theorem and the fibred-in-groupoids owner on the pullback projection.
- primitive data: the functor `u`, the projection `p`, and the owner hypothesis
  `[IsStackInGroupoids K p]`.
- derived API: the pulled-back stack-in-groupoids structure on `CategoricalPullback.π₁ u p`.

Source/core/bridge triage:
- `source-facing`: `continuous_pullback_hasStackInGroupoidsStructure`.
- `core/canonical`: `IsStackInGroupoids`, `IsFibredInGroupoids`,
  `continuous_pullback_isStackOnSite`, and `CategoricalPullback.π₁`.
- `bridge/view`: `continuous_pullback_isFibredInGroupoids`, obtained from the canonical owner
  theorem `isFibredInGroupoids_of_isFibered_and_fiber_groupoid` after checking that each pullback
  fiber is a groupoid. -/

private theorem pullbackProjection_fiberHom_isIso [IsFibredInGroupoids p]
    (U : C) {X Y : (CategoricalPullback.π₁ u p).Fiber U} (φ : X ⟶ Y) :
    IsIso φ := by
  letI : (CategoricalPullback.π₁ u p).IsHomLift (𝟙 U) φ.1 := φ.2
  have hfst := IsHomLift.fac' (CategoricalPullback.π₁ u p) (𝟙 U) φ.1
  letI : IsIso φ.1.fst := by
    change IsIso ((CategoricalPullback.π₁ u p).map φ.1)
    rw [hfst]
    infer_instance
  have hsnd : p.map φ.1.snd = X.1.iso.inv ≫ u.map φ.1.fst ≫ Y.1.iso.hom := by
    calc
      p.map φ.1.snd = X.1.iso.inv ≫ (X.1.iso.hom ≫ p.map φ.1.snd) := by
        simp
      _ = X.1.iso.inv ≫ (u.map φ.1.fst ≫ Y.1.iso.hom) := by
        rw [← φ.1.w]
      _ = X.1.iso.inv ≫ u.map φ.1.fst ≫ Y.1.iso.hom := by
        simp
  letI : IsIso (p.map φ.1.snd) := by
    rw [hsnd]
    infer_instance
  letI : IsIso φ.1.snd :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso p (p.map φ.1.snd) φ.1.snd
  letI : IsIso φ.1 :=
    (Limits.CategoricalPullback.isIso_iff u p φ.1).2 ⟨inferInstance, inferInstance⟩
  letI : (CategoricalPullback.π₁ u p).IsHomLift (𝟙 U) (asIso φ.1).hom := by
    simpa using (φ.2 : (CategoricalPullback.π₁ u p).IsHomLift (𝟙 U) φ.1)
  letI : (CategoricalPullback.π₁ u p).IsHomLift (𝟙 U) (inv φ.1) := by
    simpa using
      (IsHomLift.lift_id_inv (CategoricalPullback.π₁ u p) U (asIso φ.1))
  refine ⟨?_⟩
  use ⟨inv φ.1, inferInstance⟩
  constructor
  · apply Functor.Fiber.hom_ext
    change φ.1 ≫ inv φ.1 = 𝟙 X.1
    simp
  · apply Functor.Fiber.hom_ext
    change inv φ.1 ≫ φ.1 = 𝟙 Y.1
    simp

private instance pullbackProjection_fiber_isGroupoid [IsFibredInGroupoids p] (U : C) :
    IsGroupoid ((CategoricalPullback.π₁ u p).Fiber U) where
  all_isIso := pullbackProjection_fiberHom_isIso u p U

/-- The pullback of a category fibred in groupoids along `u` is again fibred in groupoids. -/
theorem continuous_pullback_isFibredInGroupoids [IsFibredInGroupoids p] :
    IsFibredInGroupoids (CategoricalPullback.π₁ u p) := by
  refine
    isFibredInGroupoids_of_isFibered_and_fiber_groupoid
      (CategoricalPullback.π₁ u p) inferInstance ?_
  intro U
  infer_instance

instance [IsFibredInGroupoids p] :
    IsFibredInGroupoids (CategoricalPullback.π₁ u p) :=
  continuous_pullback_isFibredInGroupoids u p

/-- Lemma 8.12.3: if `u : C ⥤ D` is a continuous functor of sites and `p : S ⥤ D` is a stack in
groupoids over `(D, K)`, then the pullback category `u^p S`, modeled by
`CategoricalPullback.π₁ u p`, is a stack in groupoids over `(C, J)`. -/
theorem continuous_pullback_hasStackInGroupoidsStructure
    [Functor.IsContinuous u J K] [IsStackInGroupoids K p] :
    IsStackInGroupoids J (CategoricalPullback.π₁ u p) := by
  letI : IsFibredInGroupoids (CategoricalPullback.π₁ u p) :=
    continuous_pullback_isFibredInGroupoids u p
  let h :
      (q : S ⥤ D) → [IsStackOnSite K q] → IsStackOnSite J (CategoricalPullback.π₁ u q) :=
    continuous_pullback_isStackOnSite u
  letI : IsStackOnSite J (CategoricalPullback.π₁ u p) := h p
  infer_instance

end

end CategoryTheory

/-! ### Definition_8_12_4 (from Chap08) -/
open CategoryTheory.Limits

universe u v

namespace CategoryTheory

section

variable {C : Type u} {D : Type u}
variable [Category.{v} C] [Category.{v} D]
variable (u : C ⥤ D) (X : FibredCategoryOver D)

/- Domain-style sampling for Definition 8.12.4:
- primary domain: fibred categories under pullback along a functor, modeled by categorical
  pullbacks.
- inspected owner-level declarations:
  `FibredCategoryOver.ofFunctor`,
  `CategoricalPullback`,
  `CategoricalPullback.π₁`,
  the canonical instance on `CategoricalPullback.π₁ u X.p`.
- best owner abstraction: `FibredCategoryOver.pullback u X`, the bundled fibred category over `C`
  built directly from the canonical pullback projection `π₁ u X.p`.
- primitive data: the canonical pullback projection `π₁ u X.p`.
- derived API: the scoped notation `uᵖ X` and the projection lemma
  `FibredCategoryOver.pullback_p`.

Source/core/bridge triage:
- `source-facing`: `FibredCategoryOver.pullback u X`, notation `uᵖ X`.
- `core/canonical`: `FibredCategoryOver.ofFunctor (CategoricalPullback.π₁ u X.p)`.
- `bridge/view`: the scoped notation `uᵖ X`. -/

namespace FibredCategoryOver

/-- Definition 8.12.4: the pullback fibred category `uᵖ X` of a fibred category `X` over `D`
along a functor `u : C ⥤ D` is the canonical bundled fibred category built from the first
projection `π₁ u X.p`. In the setting of a morphism of sites, this is the fibred category
denoted `f_* X` in the Stacks Project. -/
abbrev pullback (u : C ⥤ D) (X : FibredCategoryOver D) : FibredCategoryOver C :=
  let p := CategoricalPullback.π₁ u X.p
  letI : p.IsFibered := pullback_projection_is_fibered u X.p
  ofFunctor p

-- Proof sketch: unfold `pullback`; it is the canonical fibred category over `C` obtained from
-- the pullback projection `CategoricalPullback.π₁ u X.p` via `ofFunctor`.
/-- Helper for Definition 8.12.4: unfolding `pullback` identifies it with the canonical fibred
category attached to the pullback projection `π₁ u X.p`. -/
theorem pullback_def (u : C ⥤ D) (X : FibredCategoryOver D) :
    pullback u X = ofFunctor (CategoricalPullback.π₁ u X.p) := by
  -- Unfolding the abbreviation exposes the canonical owner construction on the pullback
  -- projection, so both sides are definitionally equal.
  rfl

/- Textbook notation for the pullback fibred category of `X` along `u`. -/
scoped infixr:100 " ᵖ " => pullback

end FibredCategoryOver

open scoped FibredCategoryOver

namespace FibredCategoryOver

/-- Helper for Definition 8.12.4: the projection of `FibredCategoryOver.pullback u X`, written
`uᵖ X`, is the canonical pullback projection `π₁ u X.p`. -/
@[simp] theorem pullback_p :
    (pullback u X).p = CategoricalPullback.π₁ u X.p := by
  -- Unfolding the bundled pullback leaves exactly the first projection from the categorical
  -- pullback model.
  rfl

end FibredCategoryOver

end

end CategoryTheory

/-! ### Lemma_8_12_5 (from Chap08) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open Limits CategoricalPullback

universe uC uD uS vC vD vS w

namespace CategoryTheory
namespace Limits

/-- A functor preserves finite nonempty limits if it preserves limits of every finite nonempty
shape. -/
class PreservesFiniteNonemptyLimits
    {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Category.{vD} D] (F : C ⥤ D) : Prop where
  /-- Preservation of a single finite nonempty limit shape. -/
  out (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J] :
    PreservesLimitsOfShape J F := by
      infer_instance

attribute [instance] PreservesFiniteNonemptyLimits.out

/-- Any functor preserving finite limits also preserves finite nonempty limits. -/
instance preservesFiniteNonemptyLimits_of_preservesFiniteLimits
    {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Category.{vD} D] (F : C ⥤ D) [PreservesFiniteLimits F] :
    PreservesFiniteNonemptyLimits F where
  out _ := inferInstance

/-- A functor preserving finite nonempty limits preserves limits of each finite nonempty shape. -/
instance preservesLimitsOfShape_of_preservesFiniteNonemptyLimits
    {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Category.{vD} D] (F : C ⥤ D) [PreservesFiniteNonemptyLimits F]
    (J : Type w) [SmallCategory J] [FinCategory J] [Nonempty J] :
    PreservesLimitsOfShape J F := by
  apply preservesLimitsOfShape_of_equiv (FinCategory.equivAsType J)

attribute [instance 100] preservesLimitsOfShape_of_preservesFiniteNonemptyLimits

end Limits

section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

/- Domain-style sampling for Lemma 8.12.5:
- primary domain: pushforward of fibred categories along a functor, organized through a
  categorical pullback and localization at strongly cartesian vertical morphisms.
- inspected owner-level declarations:
  `CategoricalPullback`,
  `Functor.IsStronglyCartesian`,
  `MorphismProperty.HasRightCalculusOfFractions`,
  `Localization`.
- best owner abstraction: the functor-owned construction
  `Functor.pushforwardSource u p`, `Functor.pushforwardFractions u p`, `Functor.pushforward u p`,
  and `Functor.pushforwardProjection u p`.
- primitive data: the categorical pullback
  `CategoricalPullback (Comma.snd (𝟭 D) u) p` and the morphism property cutting out vertical
  strongly cartesian arrows.
- derived API: the scoped notation `u ₚₚ p`, the localized notation `u ₚ p`, and the canonical
  projection to `D`.

Source/core/bridge triage:
- `source-facing`: `Functor.pushforwardSource u p`, `Functor.pushforwardFractions u p`,
  `Functor.pushforward u p`.
- `core/canonical`: `CategoricalPullback`, `Functor.IsStronglyCartesian`,
  `MorphismProperty.HasRightCalculusOfFractions`, `Localization`.
- `bridge/view`: the notations `u ₚₚ p`, `u ₚ p`, and `Functor.pushforwardProjection u p`. -/

namespace Functor

/-- The category `u_{pp} S`, modeled as the explicit fibred `2`-fibre product of the comma
projection `Comma.snd (𝟭 D) u : Comma (𝟭 D) u ⥤ C` with the fibred category `p : S ⥤ C`. -/
abbrev pushforwardSource (u : C ⥤ D) (p : S ⥤ C) :=
  CategoricalPullback (Comma.snd (𝟭 D) u) p

/- Textbook notation for the prelocalized pushforward category `u_{pp} S`. -/
scoped infixr:100 " ₚₚ " => pushforwardSource

open scoped Functor

/-- A morphism in `u_{pp} S` is vertical over the `D`-object `V` if its left component is an
identity after identifying the source and target `D`-objects. -/
private def pushforwardSourceVertical
    (u : C ⥤ D) (p : S ⥤ C)
    {X Y : u ₚₚ p} (f : X ⟶ Y) : Prop :=
  ∃ hV : X.fst.left = Y.fst.left, f.fst.left = eqToHom hV

/-- The morphism property on `u_{pp} S` cut out by morphisms of the form `(a, id_V, α)` with
`α` strongly cartesian over its canonical base map `p.map α`. -/
def pushforwardFractions (u : C ⥤ D) (p : S ⥤ C) :
    MorphismProperty (u ₚₚ p) := fun {_ _} f ↦
  pushforwardSourceVertical u p f ∧
    p.IsStronglyCartesian (p.map f.snd) f.snd

/-- The category `u_p S`, obtained by localizing `u_{pp} S` at the right-fraction property from
Lemma `8.12.5`. -/
abbrev pushforward (u : C ⥤ D) (p : S ⥤ C) :=
  (pushforwardFractions u p).Localization

/- Textbook notation for the localized pushforward category `u_p S`. -/
scoped infixr:100 " ₚ " => pushforward

/-- The projection from `u_{pp} S` to `D`, given by the `D`-object in the comma-category
component. -/
private abbrev pushforwardSourceProjection (u : C ⥤ D) (p : S ⥤ C) :
    u ₚₚ p ⥤ D :=
  π₁ (Comma.snd (𝟭 D) u) p ⋙ Comma.fst (𝟭 D) u

/-- Helper for Lemma 8.12.5: an object of `uₚₚ p` determines the canonical map from its `D`-part
to the image under `u` of the base of its `S`-part. -/
private abbrev pushforwardSourceObjectArrow
    (u : C ⥤ D) (p : S ⥤ C) (X : u ₚₚ p) :
    X.fst.left ⟶ u.obj (p.obj X.snd) :=
  X.fst.hom ≫ u.map X.iso.hom

/-- Helper for Lemma 8.12.5: the canonical `D`-arrow attached to an object of `uₚₚ p` is natural
with respect to morphisms, after expressing the base map through the `S`-component. -/
private theorem pushforwardSourceObjectArrow_naturality
    (u : C ⥤ D) (p : S ⥤ C) {X Y : u ₚₚ p} (f : X ⟶ Y) :
    f.fst.left ≫ pushforwardSourceObjectArrow u p Y =
      pushforwardSourceObjectArrow u p X ≫ u.map (p.map f.snd) := by
  dsimp [pushforwardSourceObjectArrow]
  calc
    f.fst.left ≫ Y.fst.hom ≫ u.map Y.iso.hom =
        X.fst.hom ≫ u.map f.fst.right ≫ u.map Y.iso.hom := by
      simpa [Category.assoc] using congrArg (fun k => k ≫ u.map Y.iso.hom) f.fst.w
    _ = X.fst.hom ≫ u.map (f.fst.right ≫ Y.iso.hom) := by
      simp [Functor.map_comp]
    _ = X.fst.hom ≫ u.map (X.iso.hom ≫ p.map f.snd) := by
      simpa using congrArg (fun k => X.fst.hom ≫ u.map k) f.w
    _ = X.fst.hom ≫ u.map X.iso.hom ≫ u.map (p.map f.snd) := by
      simp [Functor.map_comp]
    _ = (X.fst.hom ≫ u.map X.iso.hom) ≫ u.map (p.map f.snd) := by
      simp [Category.assoc]

/-- Helper for Lemma 8.12.5: transporting the source of a strongly cartesian base arrow along the
canonical source-base equality preserves strong cartesianness. -/
private theorem stronglyCartesian_of_eqToHom_domain_comp
    (p : S ⥤ C) {R T : C} {a b : S} (f : R ⟶ T) (φ : a ⟶ b)
    [p.IsStronglyCartesian f φ] (ha : p.obj a = R) :
    p.IsStronglyCartesian (eqToHom ha ≫ f) φ := by
  subst ha
  simpa using (inferInstance : p.IsStronglyCartesian f φ)

-- Proof sketch: a morphism in `u.pushforwardFractions p` has identity `D`-component by
-- definition, so its image under the prelocalized projection is an isomorphism in `D`.
/-- The prelocalized projection inverts the right-fraction morphisms used to define `u_p S`. -/
private theorem pushforwardSourceProjection_invertsFractions
    (u : C ⥤ D) (p : S ⥤ C) :
    (u.pushforwardFractions p).IsInvertedBy (pushforwardSourceProjection u p) := by
  intro X Y f hf
  rcases hf with ⟨⟨hV, hleft⟩, _⟩
  -- The projection remembers only the `D`-component, which is an identity transport for
  -- morphisms in the fraction property.
  change IsIso f.fst.left
  rw [hleft]
  infer_instance

/-- The canonical functor `u_p S ⥤ D` extending the projection `u_{pp} S ⥤ D` through the
localization. -/
noncomputable abbrev pushforwardProjection
    (u : C ⥤ D) (p : S ⥤ C) :
    u ₚ p ⥤ D :=
  Localization.lift
    (pushforwardSourceProjection u p)
    (pushforwardSourceProjection_invertsFractions u p)
    (u.pushforwardFractions p).Q

/-- Helper for Lemma 8.12.5: the vertical strongly cartesian morphisms in `uₚₚ p` contain
identities and are closed under composition. -/
private lemma pushforwardFractions_isMultiplicative
    (u : C ⥤ D) (p : S ⥤ C) :
    (u.pushforwardFractions p).IsMultiplicative where
  id_mem X := by
    constructor
    · -- Identities are vertical because their `D`-component is literally the identity.
      refine ⟨rfl, ?_⟩
      simp
    · -- Identities are strongly cartesian because they are isomorphisms over identity maps.
      simpa using (inferInstance : p.IsStronglyCartesian (𝟙 (p.obj X.snd)) (𝟙 X.snd))
  comp_mem f g hf hg := by
    rcases hf with ⟨⟨hfV, hfleft⟩, hfStrong⟩
    rcases hg with ⟨⟨hgV, hgleft⟩, hgStrong⟩
    constructor
    · -- The `D`-components compose as identity transports, so the composite stays vertical.
      refine ⟨hfV.trans hgV, ?_⟩
      simp [hfleft, hgleft]
    · -- Strongly cartesian morphisms are stable under composition in a fibered category.
      let _ : p.IsStronglyCartesian (p.map f.snd) f.snd := hfStrong
      let _ : p.IsStronglyCartesian (p.map g.snd) g.snd := hgStrong
      simpa using
        (inferInstance : p.IsStronglyCartesian (p.map f.snd ≫ p.map g.snd) (f.snd ≫ g.snd))

/-- Helper for Lemma 8.12.5: if two morphisms become equal after postcomposing with a denominator
in `u.pushforwardFractions p`, then their left `D`-components already agree. -/
private theorem pushforwardFractions_left_component_eq_of_comp_eq
    (u : C ⥤ D) (p : S ⥤ C)
    {X Y Y' : u ₚₚ p} {f₁ f₂ : X ⟶ Y} {s : Y ⟶ Y'}
    (hs : u.pushforwardFractions p s) (hcomp : f₁ ≫ s = f₂ ≫ s) :
    f₁.fst.left = f₂.fst.left := by
  rcases hs.1 with ⟨hV, hleft⟩
  have hfstcomp :
      f₁.fst.left ≫ s.fst.left = f₂.fst.left ≫ s.fst.left := by
    exact congrArg CategoryTheory.CommaMorphism.left
      (congrArg Limits.CategoricalPullback.Hom.fst hcomp)
  -- Cancel the vertical left component of `s`.
  rw [← cancel_mono (eqToHom hV)]
  simpa [hleft] using hfstcomp

/-- Helper for Lemma 8.12.5: the equality after postcomposition also forces the source object
arrow to equalize the two base maps in `C`. -/
private theorem pushforwardFractions_equalizes_base_maps
    (u : C ⥤ D) (p : S ⥤ C)
    {X Y Y' : u ₚₚ p} {f₁ f₂ : X ⟶ Y} {s : Y ⟶ Y'}
    (hs : u.pushforwardFractions p s) (hcomp : f₁ ≫ s = f₂ ≫ s) :
    pushforwardSourceObjectArrow u p X ≫ u.map (p.map f₁.snd) =
      pushforwardSourceObjectArrow u p X ≫ u.map (p.map f₂.snd) := by
  have hfst := pushforwardFractions_left_component_eq_of_comp_eq u p hs hcomp
  have h₁ := pushforwardSourceObjectArrow_naturality u p f₁
  have h₂ := pushforwardSourceObjectArrow_naturality u p f₂
  -- Replace both sides by the common transported arrow to `u.obj (p.obj Y.snd)`.
  calc
    pushforwardSourceObjectArrow u p X ≫ u.map (p.map f₁.snd) =
        f₁.fst.left ≫ pushforwardSourceObjectArrow u p Y := by
          simpa [Category.assoc] using h₁.symm
    _ = f₂.fst.left ≫ pushforwardSourceObjectArrow u p Y := by
          rw [hfst]
    _ = pushforwardSourceObjectArrow u p X ≫ u.map (p.map f₂.snd) := by
          simpa [Category.assoc] using h₂

/-- Helper for Lemma 8.12.5: if the denominator `s : Y ⟶ Z` is vertical on the `D`-side, then
the canonical source-object arrow of `X` factors through the pullback of the two base maps coming
from `f : X ⟶ Z` and `s`. -/
private theorem pushforwardSourceObjectArrow_pullback_factor
    (u : C ⥤ D) (p : S ⥤ C)
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u]
    {X Y Z : u ₚₚ p} (f : X ⟶ Z) (s : Y ⟶ Z)
    (hV : Y.fst.left = Z.fst.left) (hleft : s.fst.left = eqToHom hV) :
    ∃ (δ : X.fst.left ⟶ u.obj (pullback (p.map f.snd) (p.map s.snd))),
      δ ≫ u.map (pullback.fst (p.map f.snd) (p.map s.snd)) =
        pushforwardSourceObjectArrow u p X ∧
      δ ≫ u.map (pullback.snd (p.map f.snd) (p.map s.snd)) =
        f.fst.left ≫ eqToHom hV.symm ≫ pushforwardSourceObjectArrow u p Y := by
  let a := p.map f.snd
  let b := p.map s.snd
  let q₁ : X.fst.left ⟶ u.obj (p.obj X.snd) := pushforwardSourceObjectArrow u p X
  let q₂ : X.fst.left ⟶ u.obj (p.obj Y.snd) :=
    f.fst.left ≫ eqToHom hV.symm ≫ pushforwardSourceObjectArrow u p Y
  have hq₁ : q₁ ≫ u.map a = f.fst.left ≫ pushforwardSourceObjectArrow u p Z := by
    simpa [a, q₁, Category.assoc] using (pushforwardSourceObjectArrow_naturality u p f).symm
  have hs_nat := pushforwardSourceObjectArrow_naturality u p s
  have hq₂ : q₂ ≫ u.map b = f.fst.left ≫ pushforwardSourceObjectArrow u p Z := by
    calc
      q₂ ≫ u.map b =
          f.fst.left ≫ eqToHom hV.symm ≫
            (pushforwardSourceObjectArrow u p Y ≫ u.map b) := by
              simp [q₂, b, Category.assoc]
      _ = f.fst.left ≫ eqToHom hV.symm ≫ (s.fst.left ≫ pushforwardSourceObjectArrow u p Z) := by
            simpa [Category.assoc] using congrArg (fun k => f.fst.left ≫ eqToHom hV.symm ≫ k) hs_nat.symm
      _ = f.fst.left ≫ pushforwardSourceObjectArrow u p Z := by
            simp [hleft]
  let _ : HasPullback (u.map a) (u.map b) := hasPullback_of_preservesPullback u a b
  let δ_pb : X.fst.left ⟶ pullback (u.map a) (u.map b) :=
    pullback.lift q₁ q₂ (hq₁.trans hq₂.symm)
  let δ : X.fst.left ⟶ u.obj (pullback a b) := δ_pb ≫ (PreservesPullback.iso u a b).inv
  refine ⟨δ, ?_, ?_⟩
  · -- Read off the first pullback projection through the preserved-pullback comparison.
    calc
      δ ≫ u.map (pullback.fst a b) =
          δ_pb ≫ (PreservesPullback.iso u a b).inv ≫ u.map (pullback.fst a b) := by
            simp [δ, Category.assoc]
      _ = δ_pb ≫ pullback.fst (u.map a) (u.map b) := by
            simpa only [Category.assoc] using
              congrArg (fun k => δ_pb ≫ k) (PreservesPullback.iso_inv_fst u a b)
      _ = q₁ := by
            simpa [δ_pb] using pullback.lift_fst q₁ q₂ (hq₁.trans hq₂.symm)
      _ = pushforwardSourceObjectArrow u p X := rfl
  · -- The second pullback projection records the transported arrow toward `Y`.
    calc
      δ ≫ u.map (pullback.snd a b) =
          δ_pb ≫ (PreservesPullback.iso u a b).inv ≫ u.map (pullback.snd a b) := by
            simp [δ, Category.assoc]
      _ = δ_pb ≫ pullback.snd (u.map a) (u.map b) := by
            simpa only [Category.assoc] using
              congrArg (fun k => δ_pb ≫ k) (PreservesPullback.iso_inv_snd u a b)
      _ = q₂ := by
            simpa [δ_pb] using pullback.lift_snd q₁ q₂ (hq₁.trans hq₂.symm)
      _ = f.fst.left ≫ eqToHom hV.symm ≫ pushforwardSourceObjectArrow u p Y := rfl

/-- Helper for Lemma 8.12.5: an equalizing relation on the two base maps out of `X`
factors the canonical source-object arrow of `X` through the preserved equalizer. -/
private theorem pushforwardSourceObjectArrow_equalizer_factor
    (u : C ⥤ D) (p : S ⥤ C) [HasEqualizers C]
    [PreservesLimitsOfShape WalkingParallelPair u] (X : u ₚₚ p)
    {B : C} (a₁ a₂ : p.obj X.snd ⟶ B)
    (h :
      pushforwardSourceObjectArrow u p X ≫ u.map a₁ =
        pushforwardSourceObjectArrow u p X ≫ u.map a₂) :
    ∃ (δ : X.fst.left ⟶ u.obj (equalizer a₁ a₂)),
      δ ≫ u.map (equalizer.ι a₁ a₂) = pushforwardSourceObjectArrow u p X := by
  let _ : HasEqualizer (u.map a₁) (u.map a₂) :=
    ⟨⟨⟨_, isLimitOfHasEqualizerOfPreservesLimit u a₁ a₂⟩⟩⟩
  let δ_eq : X.fst.left ⟶ equalizer (u.map a₁) (u.map a₂) :=
    equalizer.lift (pushforwardSourceObjectArrow u p X) h
  let δ : X.fst.left ⟶ u.obj (equalizer a₁ a₂) :=
    δ_eq ≫ (PreservesEqualizer.iso u a₁ a₂).inv
  refine ⟨δ, ?_⟩
  -- The comparison isomorphism from equalizer preservation turns the ordinary equalizer map
  -- back into the desired source-object arrow.
  calc
    δ ≫ u.map (equalizer.ι a₁ a₂) =
        δ_eq ≫ (PreservesEqualizer.iso u a₁ a₂).inv ≫ u.map (equalizer.ι a₁ a₂) := by
          simp [δ, Category.assoc]
    _ = δ_eq ≫ equalizer.ι (u.map a₁) (u.map a₂) := by
          simpa only [Category.assoc] using
            congrArg (fun k => δ_eq ≫ k) (PreservesEqualizer.iso_inv_ι u a₁ a₂)
    _ = pushforwardSourceObjectArrow u p X := by
          simpa [δ_eq] using equalizer.lift_ι (pushforwardSourceObjectArrow u p X) h

/-- Helper for Lemma 8.12.5: a left fraction in `u.pushforwardFractions p` admits the pullback
right-fraction data predicted by the textbook Ore-square construction. -/
private theorem pushforwardFractions_exists_rightFraction_data
    (u : C ⥤ D) (p : S ⥤ C) [p.IsFibered]
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u]
    {X Y : u ₚₚ p} (φ : (u.pushforwardFractions p).LeftFraction X Y) :
    ∃ (X' : u ₚₚ p) (t : X' ⟶ X) (g : X' ⟶ Y),
      u.pushforwardFractions p t ∧ t ≫ φ.f = g ≫ φ.s := by
  rcases φ.hs with ⟨⟨hV, hleft⟩, hsStrong⟩
  let a := p.map φ.f.snd
  let b := p.map φ.s.snd
  -- First factor the source-object arrow through the preserved pullback on the base maps.
  obtain ⟨δ, hδfst, hδsnd⟩ :=
    pushforwardSourceObjectArrow_pullback_factor u p φ.f φ.s hV hleft
  -- Next choose a cartesian lift of the first pullback projection.
  obtain ⟨x', t_snd, htcart⟩ := IsPreFibered.exists_isCartesian p rfl (pullback.fst a b)
  have htstrong : p.IsStronglyCartesian (pullback.fst a b) t_snd :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian p (pullback.fst a b) t_snd
  let hdom : p.obj x' = pullback a b := IsHomLift.domain_eq p (pullback.fst a b) t_snd
  have ht_map : p.map t_snd = eqToHom hdom ≫ pullback.fst a b := by
    simpa using CategoryTheory.IsHomLift.fac' p (pullback.fst a b) t_snd
  have ht_lift :
      eqToHom hdom.symm ≫ p.map t_snd = pullback.fst a b := by
    simpa [Category.assoc] using
      congrArg (fun k => eqToHom hdom.symm ≫ k) ht_map
  have htstrong_map : p.IsStronglyCartesian (p.map t_snd) t_snd := by
    simpa [ht_map, Category.assoc] using
      (stronglyCartesian_of_eqToHom_domain_comp p (pullback.fst a b) t_snd hdom :
        p.IsStronglyCartesian (eqToHom hdom ≫ pullback.fst a b) t_snd)
  let Xpb : u ₚₚ p :=
    { fst :=
        { left := X.fst.left
          right := p.obj x'
          hom := δ ≫ u.map (eqToHom hdom.symm) }
      snd := x'
      iso := Iso.refl _ }
  let t : Xpb ⟶ X :=
    { fst :=
        { left := 𝟙 X.fst.left
          right := p.map t_snd ≫ X.iso.inv
          w := by
            have hw :
                (𝟭 D).map (𝟙 X.fst.left) ≫ X.fst.hom =
                  (δ ≫ u.map (eqToHom hdom.symm)) ≫ u.map (p.map t_snd ≫ X.iso.inv) := by
              calc
                (𝟭 D).map (𝟙 X.fst.left) ≫ X.fst.hom = X.fst.hom := by simp
                _ = pushforwardSourceObjectArrow u p X ≫ u.map X.iso.inv := by
                      simp [pushforwardSourceObjectArrow, Category.assoc]
                _ = δ ≫ u.map (pullback.fst a b) ≫ u.map X.iso.inv := by
                      rw [← hδfst]
                      simp [a, b, Category.assoc]
                _ = (δ ≫ u.map (eqToHom hdom.symm)) ≫ u.map (p.map t_snd ≫ X.iso.inv) := by
                      rw [← ht_lift]
                      simp [Functor.map_comp, Category.assoc]
            simpa [Xpb] using hw }
      snd := t_snd
      w := by
        simp [Xpb, Category.assoc] }
  have ht_mem : u.pushforwardFractions p t := by
    constructor
    · -- The pullback denominator fixes the `D`-object, so it is vertical by construction.
      refine ⟨rfl, ?_⟩
      simp [t, Xpb]
    · -- Route correction: rewrite the chosen lift to the owner-style base map before reusing
      -- the strong-cartesian structure produced from fiberedness.
      simpa [t] using htstrong_map
  have ht_snd_fac :
      p.map (t_snd ≫ φ.f.snd) = (eqToHom hdom ≫ pullback.snd a b) ≫ b := by
    -- The pullback relation replaces the composite through `φ.f.snd` by the one through
    -- `φ.s.snd`, matching the base arrow needed for strong cartesianness of `φ.s.snd`.
    calc
      p.map (t_snd ≫ φ.f.snd) = p.map t_snd ≫ a := by
        simp [a, Functor.map_comp]
      _ = (eqToHom hdom ≫ pullback.fst a b) ≫ a := by
        rw [ht_map]
      _ = eqToHom hdom ≫ (pullback.fst a b ≫ a) := by
        simp [Category.assoc]
      _ = eqToHom hdom ≫ (pullback.snd a b ≫ b) := by
        rw [pullback.condition]
      _ = (eqToHom hdom ≫ pullback.snd a b) ≫ b := by
        simp [Category.assoc]
  letI : p.IsStronglyCartesian b φ.s.snd := hsStrong
  -- Strong cartesianness of the denominator factors the composite through `φ.s.snd`.
  obtain ⟨g_snd, hg_snd, _hg_snd_uniq⟩ :=
    Functor.IsStronglyCartesian.universal_property p b φ.s.snd
      (eqToHom hdom ≫ pullback.snd a b)
      (p.map (t_snd ≫ φ.f.snd))
      (by simpa [Functor.map_comp, Category.assoc] using ht_snd_fac)
      (t_snd ≫ φ.f.snd)
  haveI : p.IsHomLift (eqToHom hdom ≫ pullback.snd a b) g_snd := hg_snd.1
  have hg_map : p.map g_snd = eqToHom hdom ≫ pullback.snd a b := by
    simpa using
      (CategoryTheory.IsHomLift.eq_of_isHomLift p (eqToHom hdom ≫ pullback.snd a b) g_snd).symm
  have hg_lift : eqToHom hdom.symm ≫ p.map g_snd = pullback.snd a b := by
    simpa [Category.assoc] using congrArg (fun k => eqToHom hdom.symm ≫ k) hg_map
  let g : Xpb ⟶ Y :=
    { fst :=
        { left := φ.f.fst.left ≫ eqToHom hV.symm
          right := p.map g_snd ≫ Y.iso.inv
          w := by
            have hw :
                (𝟭 D).map (φ.f.fst.left ≫ eqToHom hV.symm) ≫ Y.fst.hom =
                  (δ ≫ u.map (eqToHom hdom.symm)) ≫ u.map (p.map g_snd ≫ Y.iso.inv) := by
              calc
                (𝟭 D).map (φ.f.fst.left ≫ eqToHom hV.symm) ≫ Y.fst.hom =
                    (φ.f.fst.left ≫ eqToHom hV.symm ≫
                      pushforwardSourceObjectArrow u p Y) ≫ u.map Y.iso.inv := by
                      simp [pushforwardSourceObjectArrow, Category.assoc]
                _ = (δ ≫ u.map (pullback.snd a b)) ≫ u.map Y.iso.inv := by
                      rw [← hδsnd]
                _ = (δ ≫ u.map (eqToHom hdom.symm)) ≫ u.map (p.map g_snd ≫ Y.iso.inv) := by
                      rw [← hg_lift]
                      simp [Functor.map_comp, Category.assoc]
            simpa [Xpb] using hw }
      snd := g_snd
      w := by
        simp [Xpb, Category.assoc] }
  refine ⟨Xpb, t, g, ht_mem, ?_⟩
  -- Compare the two composites componentwise in the categorical pullback.
  apply CategoricalPullback.hom_ext
  · apply CategoryTheory.Comma.hom_ext
    · -- On the `D`-component, the pullback square only transports along the vertical equality.
      simp [t, g, Xpb, hleft, Category.assoc]
    · -- On the comma right component, use the factorization equality supplied by strong
      -- cartesianness and then cancel the target comparison isomorphism.
      apply (cancel_mono φ.Y'.iso.hom).1
      calc
        ((t ≫ φ.f).fst.right) ≫ φ.Y'.iso.hom =
            p.map t_snd ≫ X.iso.inv ≫ φ.f.fst.right ≫ φ.Y'.iso.hom := by
              simp [t, Category.assoc]
        _ = p.map (t_snd ≫ φ.f.snd) := by
              simpa [Functor.map_comp, Category.assoc] using
                congrArg (fun k => p.map t_snd ≫ X.iso.inv ≫ k) φ.f.w
        _ = p.map (g_snd ≫ φ.s.snd) := by
          simpa [Functor.map_comp] using congrArg p.map hg_snd.2.symm
        _ = p.map g_snd ≫ Y.iso.inv ≫ φ.s.fst.right ≫ φ.Y'.iso.hom := by
              simpa [Functor.map_comp, Category.assoc] using
                (congrArg (fun k => p.map g_snd ≫ Y.iso.inv ≫ k) φ.s.w).symm
        _ = ((g ≫ φ.s).fst.right) ≫ φ.Y'.iso.hom := by
              simp [g, Category.assoc]
  · -- The `S`-components are exactly the universal-property factorization.
    simpa [t, g, Category.assoc] using hg_snd.2.symm

-- Proof sketch: verify the right-calculus-of-fractions axioms `RMS1`, `RMS2`, and `RMS3`. For
-- `RMS1`, compositions of strongly cartesian arrows remain strongly cartesian. For `RMS2`, use
-- pullbacks in `C` and the fibred pullback construction in `S` to complete a right Ore square
-- with identity left component over `D`. For `RMS3`, use equalizers in `C`, preserved by `u`, and
-- then take a strongly cartesian lift of the equalizer map in `S`.
/-- Lemma 8.12.5: let `p : S ⥤ C` be a fibred category, assume `C` has pullbacks and equalizers,
and assume `u : C ⥤ D` preserves pullbacks and equalizers. In the category `u ₚₚ p`, the
morphisms whose `D`-component is the identity and whose `S`-component is strongly cartesian form
a right multiplicative system, i.e. `u.pushforwardFractions p` has right calculus of fractions. -/
theorem pushforwardFractions_hasRightCalculusOfFractions
    (u : C ⥤ D) (p : S ⥤ C) [p.IsFibered]
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    (u.pushforwardFractions p).HasRightCalculusOfFractions := by
  classical
  refine
    { toIsMultiplicative := pushforwardFractions_isMultiplicative u p
      exists_rightFraction := ?_
      ext := ?_ }
  · intro X Y φ
    -- The Ore square is packaged by the dedicated pullback helper above.
    obtain ⟨X', t, g, ht_mem, hfac⟩ :=
      pushforwardFractions_exists_rightFraction_data u p φ
    exact ⟨⟨t, ht_mem, g⟩, hfac⟩
  · intro X Y Y' f₁ f₂ s hs hcomp
    have hfst := pushforwardFractions_left_component_eq_of_comp_eq u p hs hcomp
    have heq := pushforwardFractions_equalizes_base_maps u p hs hcomp
    let a₁ := p.map f₁.snd
    let a₂ := p.map f₂.snd
    obtain ⟨δ₀, hδ₀⟩ :=
      pushforwardSourceObjectArrow_equalizer_factor u p X a₁ a₂ <| by
        simpa [a₁, a₂] using heq
    obtain ⟨x', t_snd, htcart⟩ := IsPreFibered.exists_isCartesian p rfl (equalizer.ι a₁ a₂)
    have htstrong : p.IsStronglyCartesian (equalizer.ι a₁ a₂) t_snd :=
      Functor.IsFibered.isStronglyCartesian_of_isCartesian p (equalizer.ι a₁ a₂) t_snd
    let hdom : p.obj x' = equalizer a₁ a₂ := IsHomLift.domain_eq p (equalizer.ι a₁ a₂) t_snd
    have ht_map : p.map t_snd = eqToHom hdom ≫ equalizer.ι a₁ a₂ := by
      simpa using CategoryTheory.IsHomLift.fac' p (equalizer.ι a₁ a₂) t_snd
    have ht_lift :
        eqToHom hdom.symm ≫ p.map t_snd = equalizer.ι a₁ a₂ := by
      simpa [Category.assoc] using
        congrArg (fun k => eqToHom hdom.symm ≫ k)
          ht_map
    have htstrong_map : p.IsStronglyCartesian (p.map t_snd) t_snd := by
      simpa [ht_map, Category.assoc] using
        (stronglyCartesian_of_eqToHom_domain_comp p (equalizer.ι a₁ a₂) t_snd hdom :
          p.IsStronglyCartesian (eqToHom hdom ≫ equalizer.ι a₁ a₂) t_snd)
    have ht_eq₁ :
        p.map (t_snd ≫ f₁.snd) = eqToHom hdom ≫ equalizer.ι a₁ a₂ ≫ a₁ := by
      calc
        p.map (t_snd ≫ f₁.snd) = p.map t_snd ≫ a₁ := by
          simp [a₁, Functor.map_comp]
        _ = eqToHom hdom ≫ equalizer.ι a₁ a₂ ≫ a₁ := by
          rw [ht_map]
          simp [Category.assoc]
    have ht_eq₂ :
        p.map (t_snd ≫ f₂.snd) = eqToHom hdom ≫ equalizer.ι a₁ a₂ ≫ a₂ := by
      calc
        p.map (t_snd ≫ f₂.snd) = p.map t_snd ≫ a₂ := by
          simp [a₂, Functor.map_comp]
        _ = eqToHom hdom ≫ equalizer.ι a₁ a₂ ≫ a₂ := by
          rw [ht_map]
          simp [Category.assoc]
    let Xeq : u ₚₚ p :=
      { fst :=
          { left := X.fst.left
            right := p.obj x'
            hom := δ₀ ≫ u.map (eqToHom hdom.symm) }
        snd := x'
        iso := Iso.refl _ }
    let t : Xeq ⟶ X :=
      { fst :=
          { left := 𝟙 X.fst.left
            right := p.map t_snd ≫ X.iso.inv
            w := by
              have hw :
                  (𝟭 D).map (𝟙 X.fst.left) ≫ X.fst.hom =
                    (δ₀ ≫ u.map (eqToHom hdom.symm)) ≫ u.map (p.map t_snd ≫ X.iso.inv) := by
                calc
                  (𝟭 D).map (𝟙 X.fst.left) ≫ X.fst.hom = X.fst.hom := by simp
                  _ = pushforwardSourceObjectArrow u p X ≫ u.map X.iso.inv := by
                        simp [pushforwardSourceObjectArrow, Category.assoc]
                  _ = δ₀ ≫ u.map (equalizer.ι a₁ a₂) ≫ u.map X.iso.inv := by
                        rw [← hδ₀]
                        simp [Category.assoc]
                  _ = (δ₀ ≫ u.map (eqToHom hdom.symm)) ≫ u.map (p.map t_snd ≫ X.iso.inv) := by
                        rw [← ht_lift]
                        simp [Functor.map_comp, Category.assoc]
              simpa [Xeq] using hw }
        snd := t_snd
        w := by
          simp [Xeq, Category.assoc] }
    have ht_mem : u.pushforwardFractions p t := by
      constructor
      · -- The denominator is vertical because its `D`-component is the identity.
        refine ⟨rfl, ?_⟩
        simp [t, Xeq]
      · -- Route correction: convert the chosen equalizer lift to the owner-style base map and
        -- then reuse the strongly cartesian instance coming from fiberedness.
        simpa [t] using htstrong_map
    have hbase_eq : equalizer.ι a₁ a₂ ≫ a₁ = equalizer.ι a₁ a₂ ≫ a₂ := equalizer.condition a₁ a₂
    have hsnd_comp :
        (t_snd ≫ f₁.snd) ≫ s.snd = (t_snd ≫ f₂.snd) ≫ s.snd := by
      have hsnd :=
        congrArg Limits.CategoricalPullback.Hom.snd hcomp
      simpa [Category.assoc] using congrArg (fun k => t_snd ≫ k) hsnd
    have hsnd_base :
        p.map (t_snd ≫ f₁.snd) = p.map (t_snd ≫ f₂.snd) := by
      calc
        p.map (t_snd ≫ f₁.snd) = eqToHom hdom ≫ equalizer.ι a₁ a₂ ≫ a₁ := ht_eq₁
        _ = eqToHom hdom ≫ equalizer.ι a₁ a₂ ≫ a₂ := by
              rw [hbase_eq]
        _ = p.map (t_snd ≫ f₂.snd) := ht_eq₂.symm
    have hsnd_eq : t_snd ≫ f₁.snd = t_snd ≫ f₂.snd := by
      letI : p.IsStronglyCartesian (p.map s.snd) s.snd := hs.2
      haveI : p.IsHomLift (p.map (t_snd ≫ f₁.snd)) (t_snd ≫ f₁.snd) := inferInstance
      haveI : p.IsHomLift (p.map (t_snd ≫ f₁.snd)) (t_snd ≫ f₂.snd) :=
        IsHomLift.of_fac' p (p.map (t_snd ≫ f₁.snd)) (t_snd ≫ f₂.snd)
          (rfl) (rfl) (by simpa using hsnd_base.symm)
      exact
        Functor.IsStronglyCartesian.ext (p := p) (f := p.map s.snd) (φ := s.snd)
          (g := p.map (t_snd ≫ f₁.snd)) hsnd_comp
    refine ⟨Xeq, t, ht_mem, ?_⟩
    -- Compare the two ambient morphisms componentwise in the categorical pullback.
    apply CategoricalPullback.hom_ext
    · apply CategoryTheory.Comma.hom_ext
      · simpa [t, Xeq, Category.assoc] using congrArg (fun k => 𝟙 X.fst.left ≫ k) hfst
      · apply (cancel_mono Y.iso.hom).1
        calc
          ((t ≫ f₁).fst.right) ≫ Y.iso.hom =
              p.map t_snd ≫ X.iso.inv ≫ f₁.fst.right ≫ Y.iso.hom := by
                simp [t, Category.assoc]
          _ = p.map (t_snd ≫ f₁.snd) := by
                simpa [Functor.map_comp, Category.assoc] using
                  congrArg (fun k => p.map t_snd ≫ X.iso.inv ≫ k) f₁.w
          _ = p.map (t_snd ≫ f₂.snd) := by
                simpa using congrArg p.map hsnd_eq
          _ = p.map t_snd ≫ X.iso.inv ≫ f₂.fst.right ≫ Y.iso.hom := by
                simpa [Functor.map_comp, Category.assoc] using
                  (congrArg (fun k => p.map t_snd ≫ X.iso.inv ≫ k) f₂.w).symm
          _ = ((t ≫ f₂).fst.right) ≫ Y.iso.hom := by
                simp [t, Category.assoc]
    · simpa [t, Category.assoc] using hsnd_eq

instance
    (u : C ⥤ D) (p : S ⥤ C) [p.IsFibered]
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    (u.pushforwardFractions p).HasRightCalculusOfFractions :=
  pushforwardFractions_hasRightCalculusOfFractions u p

end Functor

end

end CategoryTheory
