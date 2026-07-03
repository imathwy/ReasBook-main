import Mathlib
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_4_36_1 (from Chap04) -/
universe w v u

namespace CategoryTheory
namespace Pseudofunctor.CoGrothendieck

open Functor
open Opposite
open scoped Bicategory

variable {𝒞 : Type u} [Category.{v} 𝒞]
variable {F : 𝒞ᵒᵖ ⥤ Cat.{v, w}}

/- Domain-style sampling for Example 4.36.1:
- primary domain: split fibred categories arising from contravariant `Cat`-valued functors via the
  co-Grothendieck construction.
- sampled owner API:
  `Functor.toPseudofunctor'`,
  `forget`,
  `domainCartesianLift`,
  `cartesianLift`.
- best owner abstraction: the canonical owner remains the pseudofunctorial co-Grothendieck
  projection and its lift API, but the source-facing surface for this example is the ordinary
  functor `F : 𝒞ᵒᵖ ⥤ Cat` together with the bridge `F.toPseudofunctor'`.

Primitive-vs-derived split:
- primitive data: an object `a : F.obj (op S)` and a base morphism `f : R ⟶ S`.
- derived API: the projection `forget (F.toPseudofunctor')`, the lifted domain object, the
  morphism `(f, 𝟙)` over `f`, its strong-cartesian property, and the induced `IsFibered`
  instance.

Source/core/bridge triage:
- `source-facing`: the textbook explicit lift `(f, 𝟙)` in the category over `𝒞` attached to an
  ordinary contravariant functor `F : 𝒞ᵒᵖ ⥤ Cat`.
- `core/canonical`: `forget`, `domainCartesianLift`, `cartesianLift`,
  `isHomLift_cartesianLift`, and `isStronglyCartesian_homCartesianLift` for the induced
  pseudofunctor.
- `bridge/view`: `Functor.toPseudofunctor'`, which promotes the ordinary functor to the canonical
  pseudofunctor owner used by the co-Grothendieck construction. -/

/- Example 4.36.1 uses the canonical bridge from the ordinary contravariant functor `F` to the
underlying pseudofunctor needed by the co-Grothendieck construction. -/
recall toPseudofunctor'

/- Example 4.36.1: the category over `𝒞` associated to `F : 𝒞ᵒᵖ ⥤ Cat` is the canonical
projection `forget (F.toPseudofunctor') : ∫ᶜ F.toPseudofunctor' ⥤ 𝒞`. -/
example : ∫ᶜ F.toPseudofunctor' ⥤ 𝒞 :=
  forget F.toPseudofunctor'

section CartesianLift

variable {R S : 𝒞} (a : F.toPseudofunctor'.obj ⟨op S⟩) (f : R ⟶ S)

/- Example 4.36.1: the domain object of the textbook lift over `f` is the canonical
`domainCartesianLift` for `F.toPseudofunctor'`. Here `(F.toPseudofunctor').obj ⟨op S⟩` is
definitionally the same category as `F.obj (op S)`. -/
example : ∫ᶜ F.toPseudofunctor' :=
  domainCartesianLift a f

/- Example 4.36.1: the textbook lift `(f, 𝟙)` is the canonical morphism `cartesianLift` in the
associated category over `𝒞`. -/
example : domainCartesianLift a f ⟶ ⟨S, a⟩ :=
  cartesianLift a f

/- Example 4.36.1: the textbook lift `(f, 𝟙)` canonically lies over `f`; this is the
source-facing specialization of `isHomLift_cartesianLift` along `F.toPseudofunctor'`. -/
example : IsHomLift (forget F.toPseudofunctor') f (cartesianLift a f) :=
  isHomLift_cartesianLift a f

/- Example 4.36.1: the canonical morphism `(f, 𝟙) = cartesianLift a f` is strongly cartesian over
`f`; this is exactly the textbook lift in the split category associated to the ordinary functor
`F`. -/
example : IsStronglyCartesian (forget F.toPseudofunctor') f (cartesianLift a f) :=
  isStronglyCartesian_homCartesianLift a f

end CartesianLift

/- Companion example: the associated projection `forget (F.toPseudofunctor')` is fibred. -/
example : (forget F.toPseudofunctor').IsFibered := inferInstance

end Pseudofunctor.CoGrothendieck
end CategoryTheory

/-! ### Definition_4_36_2 (from Chap04) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open BasedFunctor
open Functor IsHomLift IsStronglyCartesian
open Opposite
open scoped CategoryTheory.Bicategory
open scoped BasedFunctor
variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

namespace Functor

open Pseudofunctor

/- Domain-style sampling for Definition 4.36.2:
- primary domain: fibred categories over a fixed base and split models coming from contravariant
  `Cat`-valued functors via the co-Grothendieck construction.
- inspected owner-level declarations:
  `Functor.IsFibered`,
  `Functor.toPseudofunctor'`,
  `CoGrothendieck.forget`,
  `BasedCategory.ofFunctor`,
  `BasedFunctor.IsEquivalenceOverBase`.
- best owner abstraction: the source-facing predicate `Functor.IsSplitFibredCategory p`, built
  directly from the canonical co-Grothendieck model and the canonical category-over-base owner
  `BasedCategory`, with the comparison expressed as an isomorphism in `Cat/C`.
- primitive data: the functor `p : S ⥤ C` together with a contravariant functor
  `F : Cᵒᵖ ⥤ Cat` and an isomorphism over `C` from `p` to the associated co-Grothendieck model.
- derived API: the induced fibredness of `p`, transported from the canonical fibredness instance on
  `Pseudofunctor.CoGrothendieck.forget (F.toPseudofunctor')` via the isomorphism's induced
  equivalence-over-base.

Source/core/bridge triage:
- `source-facing`: `Functor.IsSplitFibredCategory p`.
- `core/canonical`: `Functor.IsFibered`.
- `bridge/view`: `Functor.toPseudofunctor'`, `Pseudofunctor.CoGrothendieck.forget`, and the
  canonical isomorphism in `Cat/C`, together with the transport theorem
  `BasedFunctor.isFibered_iff_of_equivalence_over_base` applied to its forward morphism. -/

/-- Definition 4.36.2: a functor `p : S ⥤ C` is a split fibred category if it is isomorphic over
`C` to the co-Grothendieck construction attached to a contravariant category-valued functor on
`C`; the fibredness of `p` is then derived from this model. -/
class IsSplitFibredCategory (p : S ⥤ C) : Prop where
  existsCoGrothendieckModel :
    ∃ (F : Cᵒᵖ ⥤ Cat.{v₂, u₂})
      (e : BasedCategory.ofFunctor p ⥤ᵇ
        BasedCategory.ofFunctor (CoGrothendieck.forget (F.toPseudofunctor')))
      (eInv : BasedCategory.ofFunctor (CoGrothendieck.forget (F.toPseudofunctor')) ⥤ᵇ
        BasedCategory.ofFunctor p),
      e ⋙ eInv = 𝟙 (BasedCategory.ofFunctor p) ∧
        eInv ⋙ e = 𝟙 (BasedCategory.ofFunctor (CoGrothendieck.forget (F.toPseudofunctor')))

namespace IsSplitFibredCategory

variable {X Y : BasedCategory.{v₂, u₂} C}

/-- Helper for Definition 4.36.2: adjointifying the counit of explicit equivalence-over-base data
produces the canonical bicategorical equivalence over the base. -/
private noncomputable abbrev adjointifiedEquivalence
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F) :
    X ≌ Y :=
  Bicategory.Equivalence.mkOfAdjointifyCounit e.unitIso e.counitIso

/-- Helper for Definition 4.36.2: pulling a lifting problem back across the inverse in an
equivalence over the base preserves the same base morphism after translating along `F.w_obj`. -/
private theorem inverse_transport_lift_over_base
    (F : X ⥤ᵇ Y) (e : EquivalenceOverBase F)
    {x y : X.obj} (φ : x ⟶ y)
    {z : Y.obj} (g : Y.p.obj z ⟶ Y.p.obj (F.obj x))
    (ψ : z ⟶ F.obj y)
    [Y.p.IsHomLift (g ≫ Y.p.map (F.map φ)) ψ] :
    X.p.IsHomLift (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ)
      (e.inverse.map ψ ≫ e.unitIso.inv.app y) := by
  -- First rewrite the target lifting problem into the source base coordinates.
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
  -- Pull the lifted arrow back across the chosen quasi-inverse.
  have hψX : X.p.IsHomLift (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ) (e.inverse.map ψ) :=
    (e.inverse.isHomLift_iff (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ) ψ).2 hψY
  -- The unit component is vertical, so postcomposing with it keeps the same base map.
  have hη : X.p.IsHomLift (𝟙 (X.p.obj y)) (e.unitIso.inv.app y) := by
    simpa using BasedNatTrans.isHomLift e.unitIso.inv (rfl : X.p.obj y = X.p.obj y)
  exact @IsHomLift.comp_lift_id_right' _ _ _ _ X.p _ _ _ _ _
    (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ) (e.inverse.map ψ) hψX
    (X.p.obj y) (e.unitIso.inv.app y) hη

/-- Helper for Definition 4.36.2: pushing a source lift forward across the equivalence and then
precomposing with the counit inverse preserves the same base morphism. -/
private theorem forward_transport_lift_over_base
    (F : X ⥤ᵇ Y) (e : EquivalenceOverBase F)
    {x : X.obj} {z : Y.obj} (g : Y.p.obj z ⟶ X.p.obj x)
    (ξ : e.inverse.obj z ⟶ x)
    [X.p.IsHomLift g ξ] :
    Y.p.IsHomLift g (e.toEquivalence.counit.inv.app z ≫ F.map ξ) := by
  let E := e.toEquivalence
  -- First push the source lift forward along `F`.
  have hξY : Y.p.IsHomLift g (F.map ξ) :=
    (F.isHomLift_iff g ξ).2 (show X.p.IsHomLift g ξ from inferInstance)
  -- Then precompose with the vertical counit inverse.
  have hε : Y.p.IsHomLift (𝟙 (Y.p.obj z)) (E.counit.inv.app z) := by
    simpa [E] using BasedNatTrans.isHomLift E.counit.inv
      (rfl : Y.p.obj z = Y.p.obj z)
  exact @IsHomLift.comp_lift_id_left' _ _ _ _ Y.p _ _ _
    (Y.p.obj z) (E.counit.inv.app z) hε _ _ g (F.map ξ) hξY

/-- Helper for Definition 4.36.2: appending the canonical base-change isomorphism from `F.w_obj`
does not change whether a target morphism is a lift. -/
private theorem isHomLift_over_target_eq_iff
    (F : X ⥤ᵇ Y) {z : Y.obj} {x : X.obj}
    (g : Y.p.obj z ⟶ Y.p.obj (F.obj x))
    (θ : z ⟶ F.obj x) :
    Y.p.IsHomLift g θ ↔ Y.p.IsHomLift (g ≫ eqToHom (F.w_obj x)) θ := by
  -- The trailing `eqToHom` only rewrites the target object into source coordinates.
  simpa using IsHomLift.lift_comp_eqToHom_iff Y.p g θ (F.w_obj x)

/-- Helper for Definition 4.36.2: a target-side factorization pulls back along the inverse and the
unit inverse to the corresponding source-side factorization. -/
private theorem pullback_factorization_of_map_factorization
    (F : X ⥤ᵇ Y) (e : EquivalenceOverBase F)
    {x y : X.obj} (φ : x ⟶ y)
    {z : Y.obj} {τ' : z ⟶ F.obj x} {ψ' : z ⟶ F.obj y}
    (hτ' : τ' ≫ F.map φ = ψ') :
    (e.inverse.map τ' ≫ e.unitIso.inv.app x) ≫ φ =
      e.inverse.map ψ' ≫ e.unitIso.inv.app y := by
  -- Move the source morphism past the unit inverse using naturality.
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

/-- Helper for Definition 4.36.2: the inverse counit component of the adjointified equivalence
cancels the raw unit inverse on each target object. -/
private theorem adjointified_counit_unit_inverse_comp
    (F : X ⥤ᵇ Y) (e : EquivalenceOverBase F) (x : X.obj) :
    e.toEquivalence.counit.inv.app (F.obj x) ≫ F.map (e.unitIso.inv.app x) = 𝟙 (F.obj x) := by
  -- Reuse the earlier equivalence-over-base triangle comparison from Lemma 4.33.8.
  exact BasedFunctor.adjointified_left_triangle_inverse_component_simplified F e x

/-- Helper for Definition 4.36.2: pushing the pulled-back morphism forward with the adjointified
counit inverse recovers the original target morphism. -/
private theorem pushforward_pullback_eq
    (F : X ⥤ᵇ Y) (e : EquivalenceOverBase F)
    {x : X.obj} {z : Y.obj} (θ : z ⟶ F.obj x) :
    e.toEquivalence.counit.inv.app z ≫
        F.map (e.inverse.map θ ≫ e.unitIso.inv.app x) = θ := by
  -- Reuse the established push-pull comparison over an equivalence of based categories.
  exact BasedFunctor.pushforward_pullback_eq F e θ

/-- Helper for Definition 4.36.2: an equivalence over the base sends strongly cartesian morphisms
to strongly cartesian morphisms after applying the based functor. -/
private theorem isStronglyCartesian_map_of_isEquivalenceOverBase
    (F : X ⥤ᵇ Y) (hF : F.IsEquivalenceOverBase)
    {x y : X.obj} (φ : x ⟶ y)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ) :
    Y.p.IsStronglyCartesian (Y.p.map (F.map φ)) (F.map φ) := by
  -- The strong-cartesian transport statement is already proved in Lemma 4.33.8.
  exact BasedFunctor.isStronglyCartesian_map_of_isEquivalenceOverBase F hF φ hφ

/-- Helper for Definition 4.36.2: fibredness transports forward along an equivalence over the base
category. -/
private theorem isFibered_of_isEquivalenceOverBase
    (F : X ⥤ᵇ Y) (hF : F.IsEquivalenceOverBase) :
    X.p.IsFibered → Y.p.IsFibered := by
  intro hX
  -- Transport fibredness forward using the earlier equivalence-over-base invariance theorem.
  exact (BasedFunctor.isFibered_iff_of_equivalence_over_base F hF).mp hX

/-- Helper for Definition 4.36.2: fibredness transports backward along an equivalence over the
base category. -/
private theorem isFibered_of_equivalence_over_base
    {X : BasedCategory.{v₂, u₂} C}
    {Y : BasedCategory.{max v₁ v₂, max u₁ u₂} C}
    (F : X ⥤ᵇ Y) (G : Y ⥤ᵇ X)
    (hFG : F ⋙ G = 𝟙 X) (hGF : G ⋙ F = 𝟙 Y)
    (hY : Y.p.IsFibered) :
    X.p.IsFibered := by
  let hFGfun : F.toFunctor ⋙ G.toFunctor = 𝟭 X.obj := congrArg BasedFunctor.toFunctor hFG
  let hGFfun : G.toFunctor ⋙ F.toFunctor = 𝟭 Y.obj := congrArg BasedFunctor.toFunctor hGF
  letI : F.toFunctor.IsEquivalence :=
    Functor.IsEquivalence.mk' G.toFunctor (eqToIso hFGfun.symm) (eqToIso hGFfun)
  -- The proof follows the source construction: choose a strongly cartesian lift in the model
  -- and pull it back along the strict inverse over the base.
  refine (Functor.isFibered_iff_exists_isStronglyCartesian X.p).2 ?_
  intro x V f
  rcases (Functor.isFibered_iff_exists_isStronglyCartesian Y.p).1 hY (F.obj x) V
      (f ≫ eqToHom (F.w_obj x).symm) with ⟨z, ψ, hψ⟩
  let ξ : G.obj z ⟶ x :=
    G.map ψ ≫ eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj x) hFG)
  refine ⟨G.obj z, ξ, ?_⟩
  refine { toIsHomLift := ?_, universal_property' := ?_ }
  · -- The pulled-back comparison morphism lies over the original base arrow after rewriting the
    -- strict inverse relation on the codomain.
    have hGψ : X.p.IsHomLift (f ≫ eqToHom (F.w_obj x).symm) (G.map ψ) :=
      (G.isHomLift_iff (f ≫ eqToHom (F.w_obj x).symm) ψ).2
        (show Y.p.IsHomLift (f ≫ eqToHom (F.w_obj x).symm) ψ from hψ.toIsHomLift)
    have hEq : X.p.IsHomLift (𝟙 (X.p.obj x))
        (eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj x) hFG)) :=
      IsHomLift.eqToHom_codomain_lift_id (p := X.p)
        (congrArg (fun H : X ⥤ᵇ X => H.obj x) hFG) (rfl : X.p.obj x = X.p.obj x)
    have hComp : X.p.IsHomLift (f ≫ eqToHom (F.w_obj x).symm) ξ := by
      exact @IsHomLift.comp_lift_id_right' _ _ _ _ X.p _ _ _ _ _
        (f ≫ eqToHom (F.w_obj x).symm) (G.map ψ) hGψ
        (X.p.obj x) (eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj x) hFG)) hEq
    simpa [ξ] using hComp
  · intro w g τ hτ
    -- Push the source lifting problem into the model category and solve it there using the
    -- strongly cartesian lift `ψ`.
    have hτYbase : Y.p.IsHomLift (g ≫ f) (F.map τ) :=
      (F.isHomLift_iff (g ≫ f) τ).2 (show X.p.IsHomLift (g ≫ f) τ from hτ)
    have hτY : Y.p.IsHomLift (g ≫ (f ≫ eqToHom (F.w_obj x).symm)) (F.map τ) := by
      have : Y.p.IsHomLift ((g ≫ f) ≫ eqToHom (F.w_obj x).symm) (F.map τ) :=
        (IsHomLift.lift_comp_eqToHom_iff Y.p (g ≫ f) (F.map τ) (F.w_obj x).symm).2 hτYbase
      simpa [Category.assoc] using this
    letI : Y.p.IsHomLift (g ≫ (f ≫ eqToHom (F.w_obj x).symm)) (F.map τ) := hτY
    obtain ⟨χ', hχ', hχ'uniq⟩ :=
      IsStronglyCartesian.universal_property Y.p (f ≫ eqToHom (F.w_obj x).symm) ψ g _ rfl
        (F.map τ)
    let χ : w ⟶ G.obj z :=
      eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj w) hFG).symm ≫ G.map χ'
    refine ⟨χ, ⟨?_, ?_⟩, ?_⟩
    · -- Pull the model-side factor back across the strict inverse on the source object.
      have hGχ' : X.p.IsHomLift g (G.map χ') :=
        (G.isHomLift_iff g χ').2 (show Y.p.IsHomLift g χ' from hχ'.1)
      have hEq : X.p.IsHomLift (𝟙 (X.p.obj w))
          (eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj w) hFG).symm) :=
        IsHomLift.eqToHom_domain_lift_id (p := X.p)
          (congrArg (fun H : X ⥤ᵇ X => H.obj w) hFG).symm (rfl : X.p.obj w = X.p.obj w)
      have hComp : X.p.IsHomLift g χ := by
        exact @IsHomLift.comp_lift_id_left' _ _ _ _ X.p _ _ _
          (X.p.obj w) (eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj w) hFG).symm) hEq
          _ _ g (G.map χ') hGχ'
      simpa [χ] using hComp
    · -- The strict inverse equations turn the pulled-back factorization into the original one.
      dsimp [χ, ξ]
      calc
        (eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj w) hFG).symm ≫ G.map χ') ≫
            (G.map ψ ≫ eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj x) hFG))
            = eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj w) hFG).symm ≫
                G.map (χ' ≫ ψ) ≫ eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj x) hFG) := by
                  simp [Functor.map_comp, Category.assoc]
        _ = eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj w) hFG).symm ≫
              G.map (F.map τ) ≫ eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj x) hFG) := by
                rw [hχ'.2]
        _ = τ := by
              have hτraw : G.map (F.map τ) =
                  eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj w) hFG) ≫ τ ≫
                    eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj x) hFG).symm := by
                simpa [Functor.comp_map] using Functor.congr_hom hFGfun τ
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj w) hFG).symm ≫ k ≫
                    eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj x) hFG))
                  hτraw
    · intro κ hκ
      -- Push any competing factor back to the model and use uniqueness there.
      have hκY : Y.p.IsHomLift g
          (F.map κ ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF)) := by
        have hFκ : Y.p.IsHomLift g (F.map κ) :=
          (F.isHomLift_iff g κ).2 (show X.p.IsHomLift g κ from hκ.1)
        have hEq : Y.p.IsHomLift (𝟙 (Y.p.obj z))
            (eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF)) :=
          IsHomLift.eqToHom_codomain_lift_id (p := Y.p)
            (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF) (rfl : Y.p.obj z = Y.p.obj z)
        exact @IsHomLift.comp_lift_id_right' _ _ _ _ Y.p _ _ _ _ _
          g (F.map κ) hFκ
          (Y.p.obj z) (eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF)) hEq
      have hκfac :
          (F.map κ ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF)) ≫ ψ = F.map τ := by
        have hψnat :
            F.map (G.map ψ) ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj (F.obj x)) hGF) =
              eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF) ≫ ψ := by
          have hψraw : F.map (G.map ψ) =
              eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF) ≫ ψ ≫
                eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj (F.obj x)) hGF).symm := by
            simpa [Functor.comp_map] using Functor.congr_hom hGFfun ψ
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ k ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj (F.obj x)) hGF))
              hψraw
        have hFGmap :
            F.map (eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj x) hFG)) =
              eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj (F.obj x)) hGF) := by
          simp [eqToHom_map]
        have hstep0 :
            (F.map κ ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF)) ≫ ψ =
              F.map κ ≫
                (F.map (G.map ψ) ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj (F.obj x)) hGF)) := by
          calc
            (F.map κ ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF)) ≫ ψ
                = F.map κ ≫
                    (eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF) ≫ ψ) := by
                      simp [Category.assoc]
            _ = F.map κ ≫
                  (F.map (G.map ψ) ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj (F.obj x)) hGF)) := by
                    simpa [Category.assoc] using
                      congrArg
                        (fun t ↦ F.map κ ≫ t)
                        hψnat.symm
        have hstep1 :
            F.map (κ ≫ G.map ψ) ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj (F.obj x)) hGF) =
              F.map (κ ≫ G.map ψ) ≫
                F.map (eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj x) hFG)) := by
          simpa [Category.assoc] using
            congrArg (fun t ↦ F.map (κ ≫ G.map ψ) ≫ t) hFGmap.symm
        have hstep2 :
            F.map κ ≫
                (F.map (G.map ψ) ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj (F.obj x)) hGF)) =
              F.map (κ ≫ G.map ψ) ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj (F.obj x)) hGF) := by
          simp [Functor.map_comp, Category.assoc]
        have hstep3 :
            F.map (κ ≫ G.map ψ) ≫
                F.map (eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj x) hFG)) =
              F.map (κ ≫ G.map ψ ≫ eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj x) hFG)) := by
          simp [Functor.map_comp, Category.assoc]
        have hstep4 :
            F.map (κ ≫ G.map ψ ≫ eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj x) hFG)) = F.map τ := by
          simpa [ξ, Functor.map_comp, Category.assoc] using congrArg F.map hκ.2
        exact hstep0.trans <| hstep2.trans <| hstep1.trans <| hstep3.trans hstep4
      have hκeq : F.map κ ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF) = χ' :=
        hχ'uniq _ ⟨hκY, hκfac⟩
      have hχmap : F.map χ = χ' ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF).symm := by
        have hχraw : F.map (G.map χ') =
            eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj (F.obj w)) hGF) ≫ χ' ≫
              eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF).symm := by
          simpa [Functor.comp_map] using Functor.congr_hom hGFfun χ'
        dsimp [χ]
        calc
          F.map (eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj w) hFG).symm ≫ G.map χ')
              = F.map (eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj w) hFG).symm) ≫ F.map (G.map χ') := by
                  simp [Functor.map_comp]
          _ = χ' ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF).symm := by
                simp [eqToHom_map, hχraw]
      have hstep1 : F.map κ =
          (F.map κ ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF)) ≫
            eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF).symm := by
        simp [Category.assoc]
      have hstep2 :
          (F.map κ ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF)) ≫
              eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF).symm =
            χ' ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF).symm := by
        simpa [Category.assoc] using
          congrArg
            (fun k ↦ k ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF).symm)
            hκeq
      have hκmap : F.map κ = F.map χ := by
        rw [hstep1, hstep2, hχmap]
      exact F.toFunctor.map_injective hκmap

theorem isFibered {p : S ⥤ C} (hp : Functor.IsSplitFibredCategory p) : p.IsFibered := by
  -- Unpack the split model promised by the definition.
  rcases hp.existsCoGrothendieckModel with ⟨F, e, eInv, hη, hε⟩
  -- Transfer fibredness from the canonical co-Grothendieck model back to `p`.
  let hModel : (CoGrothendieck.forget (F.toPseudofunctor')).IsFibered := inferInstance
  exact
    isFibered_of_equivalence_over_base
      (X := BasedCategory.ofFunctor p)
      (Y := BasedCategory.ofFunctor (CoGrothendieck.forget (F.toPseudofunctor')))
      e eInv hη hε
      (show (BasedCategory.ofFunctor (CoGrothendieck.forget (F.toPseudofunctor'))).p.IsFibered from
        hModel)

end IsSplitFibredCategory

instance (p : S ⥤ C) [Functor.IsSplitFibredCategory p] : p.IsFibered :=
  IsSplitFibredCategory.isFibered inferInstance

end Functor

end CategoryTheory

/-! ### Lemma_4_36_3 (from Chap04) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open BasedFunctor
open Functor Fiber
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type (max u₁ u₂)} [Category.{max v₁ v₂} S]

/- Domain-style sampling for Lemma 4.36.3:
- primary domain: split fibred categories, chosen pullback systems on standard fibers, and the
  canonical pseudofunctor/co-Grothendieck bridge.
- inspected owner-level declarations:
  `PullbackChoice`,
  `PullbackChoice.pullbackFunctor`,
  `PullbackChoice.pullbackCompIso`,
  `PullbackChoice.pullbackIdIso`,
  `Functor.IsSplitFibredCategory`.
  together with strict composition for its pullback functors.  Since this formalization keeps
  identity pullbacks only up to the canonical unit isomorphism from Lemma 4.33.7, a literal
  ordinary `Cat`-valued functor also needs a strict unit normalization.
- primitive data: the chosen pullback system `hc : PullbackChoice p`.
- derived API: the composition-on-the-nose equations
  `hc.pullbackFunctor (g ≫ f) = hc.pullbackFunctor f ⋙ hc.pullbackFunctor g`, and separately the
  optional strict unit normalization `hc.pullbackFunctor (𝟙 U) = 𝟭 (Fiber p U)`.

Source/core/bridge triage:
- `source-facing`: the Stacks statement is an equality criterion for a split cleavage. With the
  present `PullbackChoice` API, identity and composition comparisons live as canonical
  isomorphisms from Lemma 4.33.7; the formal theorem below therefore records the normalized strict
  data needed to build an ordinary contravariant `Cat`-valued functor.
- `core/canonical`: `p.IsSplitFibredCategory`.
- `bridge/view`: the co-Grothendieck model attached to the strict fiber functor. -/

-- Proof sketch: a normalized pullback system with strict unit and composition determines an
-- ordinary contravariant `Cat`-valued functor on the fibers. Its co-Grothendieck construction is
-- split by definition. If the original `p` is explicitly identified over `C` with that strict
-- model, splitness of `p` follows by packaging this identification in Definition 4.36.2.
/-- Helper for Lemma 4.36.3: a strict pullback choice determines the ordinary contravariant
`Cat`-valued functor on the standard fibers. -/
private noncomputable def strict_pullback_functor
    {p : S ⥤ C} (hc : PullbackChoice p)
    (hid : ∀ U : C, hc.pullbackFunctor (𝟙 U) = 𝟭 (Fiber p U))
    (hcomp : ∀ {U V W : C} (f : V ⟶ U) (g : W ⟶ V),
      hc.pullbackFunctor (g ≫ f) = hc.pullbackFunctor f ⋙ hc.pullbackFunctor g) :
    Cᵒᵖ ⥤ CategoryTheory.Cat where
  obj := fun U ↦ CategoryTheory.Cat.of (Fiber p (unop U))
  map := fun f ↦ (hc.pullbackFunctor f.unop).toCatHom
  map_id := by
    -- The strict unit hypothesis turns pullback along identities into the literal identity functor.
    intro U
    apply CategoryTheory.Cat.ext
    simpa using hid (unop U)
  map_comp := by
    -- The strict composition hypothesis is exactly the functoriality law on the fibers.
    intro U V W f g
    apply CategoryTheory.Cat.ext
    simpa using hcomp f.unop g.unop

/-- A bare strict composition law for chosen pullback functors only makes the identity pullback
functor idempotent. The normalized strict model below therefore records the identity law as a
separate hypothesis rather than deriving it from composition. -/
theorem PullbackChoice.pullbackFunctor_id_idempotent_of_compStrict
    {p : S ⥤ C} (hc : PullbackChoice p)
    (hcomp : ∀ {U V W : C} (f : V ⟶ U) (g : W ⟶ V),
      hc.pullbackFunctor (g ≫ f) = hc.pullbackFunctor f ⋙ hc.pullbackFunctor g)
    (U : C) :
    hc.pullbackFunctor (𝟙 U) =
      hc.pullbackFunctor (𝟙 U) ⋙ hc.pullbackFunctor (𝟙 U) := by
  simpa using hcomp (𝟙 U) (𝟙 U)

/-- Helper for Lemma 4.36.3: transporting along an equality of pullback functors does not change
the ambient chosen pullback arrow after forgetting to the total category. -/
private theorem pullbackEqToHomComponentPostcomposeEq
    {p : S ⥤ C} (hc : PullbackChoice p)
    {U V : C} {f g : V ⟶ U} (e : f = g) (x : Fiber p U) :
    Fiber.fiberInclusion.map ((eqToHom (congrArg (fun k ↦ hc.pullbackFunctor k) e)).app x) ≫
        hc.map g x =
      hc.map f x := by
  -- Reduce the transport comparison to the reflexive case, where the component is the identity.
  cases e
  simp

/-- Helper for Lemma 4.36.3: a morphism into a chosen pullback object is determined by its
postcomposition with the chosen pullback arrow. -/
private theorem pullbackHom_ext
    {p : S ⥤ C} (hc : PullbackChoice p)
    {U V : C} (f : V ⟶ U) {x : Fiber p U} {y : Fiber p V}
    {ψ ψ' : y ⟶ (hc.pullbackFunctor f).obj x}
    (h : ψ.1 ≫ hc.map f x = ψ'.1 ≫ hc.map f x) :
    ψ = ψ' := by
  -- Forget to the ambient category and use uniqueness for lifts into the chosen cartesian arrow.
  apply Fiber.hom_ext
  change ψ.1 = ψ'.1
  letI : p.IsHomLift (𝟙 V) ψ.1 := ψ.2
  letI : p.IsHomLift (𝟙 V) ψ'.1 := ψ'.2
  have hψ : p.IsHomLift (𝟙 V) ψ.1 := inferInstance
  have hψ' : p.IsHomLift (𝟙 V) ψ'.1 := inferInstance
  exact
    @IsStronglyCartesian.ext _ _ _ _ p _ _ _ _
      f (hc.map f x) inferInstance _ _ (𝟙 V) ψ.1 ψ'.1 hψ hψ' h

/-- Helper for Lemma 4.36.3: the explicit source-side identity-comparison chain postcomposes with
the chosen pullback arrow to the expected composite pullback map. -/
private theorem pullbackIdSourceTransportPostcomposeEq
    {p : S ⥤ C} (hc : PullbackChoice p)
    {U T : C} (f : U ⟶ T) (x : Fiber p T) :
    Fiber.fiberInclusion.map
        ((hc.pullbackCompIso f (𝟙 U)).hom.app x ≫
          (hc.pullbackIdIso U).inv.app ((hc.pullbackFunctor f).obj x)) ≫
        hc.map f x =
      hc.map (𝟙 U ≫ f) x := by
  -- Expand the comparison chain and collapse it using the component factorization laws.
  have hstep1 :
      Fiber.fiberInclusion.map
          ((hc.pullbackCompIso f (𝟙 U)).hom.app x ≫
            (hc.pullbackIdIso U).inv.app ((hc.pullbackFunctor f).obj x)) ≫
          hc.map f x =
        ((hc.pullbackCompIso f (𝟙 U)).hom.app x).1 ≫
          hc.map (𝟙 U) ((hc.pullbackFunctor f).obj x) ≫
            hc.map f x := by
    rw [Functor.map_comp]
    simpa [PullbackChoice.pullbackIdIso, Category.assoc] using
      congrArg
        (fun k ↦ ((hc.pullbackCompIso f (𝟙 U)).hom.app x).1 ≫ k ≫ hc.map f x)
        (hc.pullbackIdComponentIso_inv_eq U ((hc.pullbackFunctor f).obj x))
  have hstep2 :
      ((hc.pullbackCompIso f (𝟙 U)).hom.app x).1 ≫
          hc.map (𝟙 U) ((hc.pullbackFunctor f).obj x) ≫
            hc.map f x =
        hc.map (𝟙 U ≫ f) x := by
    simpa [PullbackChoice.pullbackCompIso, Category.assoc] using
      hc.pullbackCompComponentIso_fac (f := f) (g := 𝟙 U) x
  exact hstep1.trans hstep2

/-- Helper for Lemma 4.36.3: the explicit target-side identity-comparison chain postcomposes with
the composite pullback arrow to the original chosen pullback map. -/
private theorem pullbackIdTargetTransportPostcomposeEq
    {p : S ⥤ C} (hc : PullbackChoice p)
    {U T : C} (f : U ⟶ T) (x : Fiber p T) :
    Fiber.fiberInclusion.map
        ((hc.pullbackIdIso U).hom.app ((hc.pullbackFunctor f).obj x) ≫
          (hc.pullbackCompIso f (𝟙 U)).inv.app x) ≫
        hc.map (𝟙 U ≫ f) x =
      hc.map f x := by
  -- Route correction: normalize the target transport through the unit comparison first, then
  -- apply the inverse comparison-factorization law.
  have hstep1 :
      Fiber.fiberInclusion.map
          ((hc.pullbackIdIso U).hom.app ((hc.pullbackFunctor f).obj x) ≫
            (hc.pullbackCompIso f (𝟙 U)).inv.app x) ≫
          hc.map (𝟙 U ≫ f) x =
        ((hc.pullbackIdIso U).hom.app ((hc.pullbackFunctor f).obj x)).1 ≫
          hc.map (𝟙 U) ((hc.pullbackFunctor f).obj x) ≫
            hc.map f x := by
    rw [Functor.map_comp]
    simpa [PullbackChoice.pullbackIdIso, Category.assoc] using
      congrArg
        (fun k ↦ ((hc.pullbackIdIso U).hom.app ((hc.pullbackFunctor f).obj x)).1 ≫ k)
        (hc.pullbackCompComponentIso_inv_fac (f := f) (g := 𝟙 U) x)
  have hstep2 :
      ((hc.pullbackIdIso U).hom.app ((hc.pullbackFunctor f).obj x)).1 ≫
          hc.map (𝟙 U) ((hc.pullbackFunctor f).obj x) ≫
            hc.map f x =
        hc.map f x := by
    have hfac :
        ((hc.pullbackIdIso U).hom.app ((hc.pullbackFunctor f).obj x)).1 ≫
            hc.map (𝟙 U) ((hc.pullbackFunctor f).obj x) =
          𝟙 ((hc.pullbackFunctor f).obj x).1 := by
      simpa [PullbackChoice.pullbackIdIso] using
        hc.pullbackIdComponentIso_fac U ((hc.pullbackFunctor f).obj x)
    calc
      ((hc.pullbackIdIso U).hom.app ((hc.pullbackFunctor f).obj x)).1 ≫
            hc.map (𝟙 U) ((hc.pullbackFunctor f).obj x) ≫
              hc.map f x
          =
        (((hc.pullbackIdIso U).hom.app ((hc.pullbackFunctor f).obj x)).1 ≫
              hc.map (𝟙 U) ((hc.pullbackFunctor f).obj x)) ≫
            hc.map f x := by
              simp [Category.assoc]
      _ = hc.map f x := by
            rw [hfac]
            simp
  exact hstep1.trans hstep2

/-- Helper for Lemma 4.36.3: the object transport induced by `Category.id_comp` agrees with the
explicit source-side identity comparison chain. -/
private theorem pullbackIdEqToHom
    {p : S ⥤ C} (hc : PullbackChoice p)
    {U T : C} (f : U ⟶ T) (x : Fiber p T) :
    eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj x) (Category.id_comp f)) =
      (hc.pullbackCompIso f (𝟙 U)).hom.app x ≫
        (hc.pullbackIdIso U).inv.app ((hc.pullbackFunctor f).obj x) := by
  -- Compare the two candidate transports after postcomposing with the chosen pullback arrow.
  apply pullbackHom_ext hc f
  have hleft :
      Fiber.fiberInclusion.map
          (eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj x) (Category.id_comp f))) ≫
          hc.map f x =
        hc.map (𝟙 U ≫ f) x := by
    have htransport :
        Fiber.fiberInclusion.map
            ((eqToHom (congrArg (fun k ↦ hc.pullbackFunctor k) (Category.id_comp f))).app x) ≫
            hc.map f x =
          hc.map (𝟙 U ≫ f) x :=
      pullbackEqToHomComponentPostcomposeEq hc (e := Category.id_comp f) x
    simpa using htransport
  have hright :
      Fiber.fiberInclusion.map
          ((hc.pullbackCompIso f (𝟙 U)).hom.app x ≫
            (hc.pullbackIdIso U).inv.app ((hc.pullbackFunctor f).obj x)) ≫
          hc.map f x =
        hc.map (𝟙 U ≫ f) x := by
    have htransport := pullbackIdSourceTransportPostcomposeEq hc (f := f) (x := x)
    rw [Functor.map_comp] at htransport
    simpa [Category.assoc] using htransport
  exact hleft.trans hright.symm

/-- Helper for Lemma 4.36.3: the inverse transport induced by `Category.id_comp` agrees with the
explicit target-side identity comparison chain. -/
private theorem pullbackIdEqToHomSymm
    {p : S ⥤ C} (hc : PullbackChoice p)
    {U T : C} (f : U ⟶ T) (x : Fiber p T) :
    eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj x) (Category.id_comp f)).symm =
      (hc.pullbackIdIso U).hom.app ((hc.pullbackFunctor f).obj x) ≫
        (hc.pullbackCompIso f (𝟙 U)).inv.app x := by
  -- Compare the two inverse transports after postcomposing with the composite pullback arrow.
  apply pullbackHom_ext hc (𝟙 U ≫ f)
  have hleft :
      Fiber.fiberInclusion.map
          (eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj x) (Category.id_comp f)).symm) ≫
          hc.map (𝟙 U ≫ f) x =
        hc.map f x := by
    have htransport :
        Fiber.fiberInclusion.map
            ((eqToHom (congrArg (fun k ↦ hc.pullbackFunctor k)
              (Category.id_comp f)).symm).app x) ≫
            hc.map (𝟙 U ≫ f) x =
          hc.map f x :=
      pullbackEqToHomComponentPostcomposeEq hc (f := f) (g := 𝟙 U ≫ f)
        (e := (Category.id_comp f).symm) x
    simpa using htransport
  have hright :
      Fiber.fiberInclusion.map
          ((hc.pullbackIdIso U).hom.app ((hc.pullbackFunctor f).obj x) ≫
            (hc.pullbackCompIso f (𝟙 U)).inv.app x) ≫
          hc.map (𝟙 U ≫ f) x =
        hc.map f x := by
    have htransport := pullbackIdTargetTransportPostcomposeEq hc (f := f) (x := x)
    rw [Functor.map_comp] at htransport
    simpa [Category.assoc] using htransport
  exact hleft.trans hright.symm

/-- Helper for Lemma 4.36.3: forgetting an equality morphism in a standard fiber recovers the
corresponding equality morphism in the ambient category. -/
private theorem fiberEqToHom_map
    {p : S ⥤ C} {U : C} {P Q : Fiber p U} (h : P = Q) :
    Fiber.fiberInclusion.map (eqToHom h) = eqToHom (congrArg Subtype.val h) := by
  -- Equality morphisms in the fiber are defined by the same underlying arrows in the total
  -- category.
  cases h
  rfl

/-- Helper for Lemma 4.36.3: factor a total-category arrow through the chosen pullback of its
target along its image in the base. -/
private noncomputable def factorToPullback
    {p : S ⥤ C} (hc : PullbackChoice p) {x y : S} (φ : x ⟶ y) :
    let xF : Fiber p (p.obj x) := ⟨x, rfl⟩
    let yF : Fiber p (p.obj y) := ⟨y, rfl⟩
    xF ⟶ (hc.pullbackFunctor (p.map φ)).obj yF := by
  dsimp
  let xF : Fiber p (p.obj x) := ⟨x, rfl⟩
  let yF : Fiber p (p.obj y) := ⟨y, rfl⟩
  letI : p.IsHomLift (p.map φ) φ := inferInstance
  let m := IsStronglyCartesian.map p (p.map φ) (hc.map (p.map φ) yF)
    (Category.id_comp (p.map φ)).symm φ
  have hm : p.IsHomLift (𝟙 (p.obj x)) m := by
    dsimp [m]
    exact IsStronglyCartesian.map_isHomLift p (p.map φ) (hc.map (p.map φ) yF)
      (Category.id_comp (p.map φ)).symm φ
  exact ⟨m, hm⟩

/-- Helper for Lemma 4.36.3: the factorization through a chosen pullback recomposes to the original
total-category arrow. -/
private theorem factorToPullback_fac
    {p : S ⥤ C} (hc : PullbackChoice p) {x y : S} (φ : x ⟶ y) :
    let yF : Fiber p (p.obj y) := ⟨y, rfl⟩
    (factorToPullback hc φ).1 ≫ hc.map (p.map φ) yF = φ := by
  dsimp [factorToPullback]
  let yF : Fiber p (p.obj y) := ⟨y, rfl⟩
  change IsStronglyCartesian.map p (p.map φ) (hc.map (p.map φ) yF)
    (Category.id_comp (p.map φ)).symm φ ≫ hc.map (p.map φ) yF = φ
  exact IsStronglyCartesian.fac p (p.map φ) (hc.map (p.map φ) yF)
    (Category.id_comp (p.map φ)).symm φ

/-- Helper for Lemma 4.36.3: the tautological pullback choice on a split co-Grothendieck model. -/
private noncomputable def modelPullbackChoice
    (F : Cᵒᵖ ⥤ CategoryTheory.Cat.{v₂, u₂}) :
    PullbackChoice (Pseudofunctor.CoGrothendieck.forget (F.toPseudofunctor')) where
  obj := by
    intro U V f x
    rcases x with ⟨X, hX⟩
    subst hX
    exact ⟨Pseudofunctor.CoGrothendieck.domainCartesianLift X.fiber f, rfl⟩
  map := by
    intro U V f x
    rcases x with ⟨X, hX⟩
    subst hX
    exact Pseudofunctor.CoGrothendieck.cartesianLift X.fiber f
  isStronglyCartesian := by
    intro U V f x
    rcases x with ⟨X, hX⟩
    subst hX
    exact Pseudofunctor.CoGrothendieck.isStronglyCartesian_homCartesianLift X.fiber f

/-- Helper for Lemma 4.36.3: the strict co-Grothendieck model attached to a strict pullback
choice is split by construction. -/
private theorem strictPullbackModel_isSplit
    {p : S ⥤ C} (hc : PullbackChoice p)
    (hid : ∀ U : C, hc.pullbackFunctor (𝟙 U) = 𝟭 (Fiber p U))
    (hcomp : ∀ {U V W : C} (f : V ⟶ U) (g : W ⟶ V),
      hc.pullbackFunctor (g ≫ f) = hc.pullbackFunctor f ⋙ hc.pullbackFunctor g) :
    Functor.IsSplitFibredCategory
      (Pseudofunctor.CoGrothendieck.forget ((strict_pullback_functor hc hid hcomp).toPseudofunctor')) := by
  -- This target is literally the co-Grothendieck model used in the definition of splitness.
  refine ⟨?_⟩
  refine ⟨strict_pullback_functor hc hid hcomp, ?_, ?_, ?_, ?_⟩
  · exact 𝟙 (BasedCategory.ofFunctor _)
  · exact 𝟙 (BasedCategory.ofFunctor _)
  · simp
  · simp

/-- Lemma 4.36.3, strict model direction: a normalized choice of pullbacks whose pullback
functors compose on the nose gives the split co-Grothendieck model associated to the induced
contravariant `Cat`-valued functor.

In the formalization of Definition 4.33.6, identity pullbacks are only canonically isomorphic to
the identity functor by `PullbackChoice.pullbackIdIso`; literal equality of identity pullback
functors is therefore recorded as part of the normalized strict data. -/
theorem Functor.isSplit_of_strict_pullbackChoice_model
    {p : S ⥤ C} (hc : PullbackChoice p)
    (hid : ∀ U : C, hc.pullbackFunctor (𝟙 U) = 𝟭 (Fiber p U))
    (hcomp : ∀ {U V W : C} (f : V ⟶ U) (g : W ⟶ V),
      hc.pullbackFunctor (g ≫ f) = hc.pullbackFunctor f ⋙ hc.pullbackFunctor g) :
    Functor.IsSplitFibredCategory
      (Pseudofunctor.CoGrothendieck.forget
        ((strict_pullback_functor hc hid hcomp).toPseudofunctor')) :=
  strictPullbackModel_isSplit hc hid hcomp

/-- Formal bridge for Lemma 4.36.3: a normalized strict pullback choice proves splitness of any
fibred category that is identified over the base with the strict co-Grothendieck model built from
that choice.

The extra based isomorphism data is the formal coherence missing from the bare statement
`hc.pullbackFunctor (g ≫ f) = hc.pullbackFunctor f ⋙ hc.pullbackFunctor g`: in this
formalization, identity pullback arrows are only canonically isomorphic to identities, so the
comparison with `p` itself cannot be recovered from functor equality alone. -/
theorem Functor.isSplit_of_strict_pullbackChoice_model_iso
    {p : S ⥤ C} (hc : PullbackChoice p)
    (hid : ∀ U : C, hc.pullbackFunctor (𝟙 U) = 𝟭 (Fiber p U))
    (hcomp : ∀ {U V W : C} (f : V ⟶ U) (g : W ⟶ V),
      hc.pullbackFunctor (g ≫ f) = hc.pullbackFunctor f ⋙ hc.pullbackFunctor g)
    (e : BasedCategory.ofFunctor p ⥤ᵇ
      BasedCategory.ofFunctor
        (Pseudofunctor.CoGrothendieck.forget
          ((strict_pullback_functor hc hid hcomp).toPseudofunctor')))
    (eInv : BasedCategory.ofFunctor
      (Pseudofunctor.CoGrothendieck.forget
        ((strict_pullback_functor hc hid hcomp).toPseudofunctor')) ⥤ᵇ
        BasedCategory.ofFunctor p)
    (hη : e ⋙ eInv = 𝟙 (BasedCategory.ofFunctor p))
    (hε : eInv ⋙ e =
      𝟙 (BasedCategory.ofFunctor
        (Pseudofunctor.CoGrothendieck.forget
          ((strict_pullback_functor hc hid hcomp).toPseudofunctor')))) :
    p.IsSplitFibredCategory := by
  exact ⟨⟨strict_pullback_functor hc hid hcomp, e, eInv, hη, hε⟩⟩

/-- Existential form of the normalized strict-pullback model criterion for Lemma 4.36.3.

Besides strict identity and composition of pullback functors, the hypothesis includes explicit
based inverse data identifying `p` with the strict co-Grothendieck model built from those
pullbacks. This is the formal coherence that the paper proof suppresses in the phrase “immediate
from the definitions”: with the current `PullbackChoice` structure, functor equality alone does
not encode the chosen identity pullback arrows or the comparison with the total category. -/
theorem Functor.isSplit_of_exists_strict_pullbackChoice_model_iso
    {p : S ⥤ C}
    (h :
      ∃ (hc : PullbackChoice p)
        (hid : ∀ U : C, hc.pullbackFunctor (𝟙 U) = 𝟭 (Fiber p U))
        (hcomp : ∀ {U V W : C} (f : V ⟶ U) (g : W ⟶ V),
          hc.pullbackFunctor (g ≫ f) = hc.pullbackFunctor f ⋙ hc.pullbackFunctor g),
        ∃ (e : BasedCategory.ofFunctor p ⥤ᵇ
          BasedCategory.ofFunctor
            (Pseudofunctor.CoGrothendieck.forget
              ((strict_pullback_functor hc hid hcomp).toPseudofunctor')))
          (eInv : BasedCategory.ofFunctor
            (Pseudofunctor.CoGrothendieck.forget
              ((strict_pullback_functor hc hid hcomp).toPseudofunctor')) ⥤ᵇ
              BasedCategory.ofFunctor p),
          e ⋙ eInv = 𝟙 (BasedCategory.ofFunctor p) ∧
            eInv ⋙ e =
              𝟙 (BasedCategory.ofFunctor
                (Pseudofunctor.CoGrothendieck.forget
                  ((strict_pullback_functor hc hid hcomp).toPseudofunctor')))) :
    p.IsSplitFibredCategory := by
  rcases h with ⟨hc, hid, hcomp, e, eInv, hη, hε⟩
  exact Functor.isSplit_of_strict_pullbackChoice_model_iso hc hid hcomp e eInv hη hε

/-- Companion spelling of the normalized strict-pullback model criterion. -/
theorem Functor.isSplit_of_strict_pullbackChoice_model'
    {p : S ⥤ C} (hc : PullbackChoice p)
    (hid : ∀ U : C, hc.pullbackFunctor (𝟙 U) = 𝟭 (Fiber p U))
    (hcomp : ∀ {U V W : C} (f : V ⟶ U) (g : W ⟶ V),
      hc.pullbackFunctor (g ≫ f) = hc.pullbackFunctor f ⋙ hc.pullbackFunctor g) :
    Functor.IsSplitFibredCategory
      (Pseudofunctor.CoGrothendieck.forget
        ((strict_pullback_functor hc hid hcomp).toPseudofunctor')) :=
  Functor.isSplit_of_strict_pullbackChoice_model hc hid hcomp

end CategoryTheory

/-! ### Lemma_4_36_4 (from Chap04) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Bicategory
open scoped CategoryTheory.Bicategory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type (max u₁ u₂)} [Category.{max v₁ v₂} S]

/-- Lemma 4.36.4: every fibred category `p : S ⥤ C` admits a split strictification over
`C` and a based equivalence over `C` from `p` to that strictification. The strictification target
uses the larger object universe needed to store a base arrow in each strictified object. -/
lemma exists_split_fibred_category_over_base
    (p : S ⥤ C) [p.IsFibered] :
    ∃ (Y : FibredCategoryOver.{v₁, u₁, max u₁ (max u₂ v₁), max v₁ v₂} C)
      (F : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor Y.p),
      F.IsEquivalenceOverBase ∧ Functor.IsSplitFibredCategory Y.p := by
  exact exists_split_fibred_category_over_base_aux p

end CategoryTheory
