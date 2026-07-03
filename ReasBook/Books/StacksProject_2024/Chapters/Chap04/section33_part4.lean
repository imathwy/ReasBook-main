import Mathlib
import Mathlib.CategoryTheory.FiberedCategory.Cartesian
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_4_33_11 (from Chap04) -/
open CategoryTheory
open CategoryTheory.Over
open CategoryTheory.IsHomLift
open CategoryTheory.Functor.IsStronglyCartesian

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]

/- Domain-style sampling for Lemma 4.33.11:
- primary domain: fibred categories over a slice category and transport of cartesian structure
  across the slice forgetful functor.
- inspected owner-level declarations:
  `Functor.IsHomLift.of_fac`,
  `Functor.IsStronglyCartesian.universal_property`,
  `Functor.IsPreFibered.exists_isCartesian`,
  `Functor.IsFibered.isStronglyCartesian_of_isCartesian`.
- best owner abstraction: `Functor.IsFibered` on the slice-valued functor `p' : S ⥤ Over U`;
  the slice forgetful comparison is a bridge, not a second owner.
- primitive data: the underlying morphism `f.left` in `C` and the owner-level lift/cartesian
  predicates for `p' ⋙ Over.forget U`.
- derived API: the induced slice-level `IsHomLift`, `IsStronglyCartesian`, and `IsFibered`
  structures on `p'`, including the typeclass instances below for `p'.IsStronglyCartesian` and
  `p'.IsFibered`.

Source/core/bridge triage:
- `source-facing`: `isStronglyCartesian_of_comp_over_forget` and
  `isFibered_of_comp_over_forget`.
- `core/canonical`: `Functor.IsHomLift`, `Functor.IsStronglyCartesian`, and
  `Functor.IsFibered`.
- `bridge/view`: the public equivalence
  `isHomLift_over_iff_comp_over_forget` between slice lifts and underlying lifts in `C`.
-/

/-- Bridge lemma for Lemma 4.33.11: a morphism in `Over U` is a lift for `p'` exactly when its
underlying morphism in `C` is a lift for `p' ⋙ Over.forget U`. -/
theorem isHomLift_over_iff_comp_over_forget {U : C} (p' : S ⥤ Over U)
    {a b : S} {A : Over U} {f : A ⟶ p'.obj a} {φ : b ⟶ a}
    : p'.IsHomLift f φ ↔ (p' ⋙ Over.forget U).IsHomLift f.left φ := by
  let q := p' ⋙ Over.forget U
  constructor
  · intro
    refine IsHomLift.of_fac q f.left φ ?_ rfl ?_
    · simpa [q] using congrArg (fun X ↦ X.left) (domain_eq p' f φ)
    · simpa [q] using congrArg (fun m ↦ m.left) (fac p' f φ)
  · intro
    have hdom : (p'.obj b).left = A.left := domain_eq q f.left φ
    have hA : p'.obj b = A := by
      exact CostructuredArrow.obj_ext (p'.obj b) A hdom <| by
        simpa [q, Category.assoc, ← w f] using
          (congrArg (fun k ↦ k ≫ (p'.obj a).hom) ((fac' q f.left φ).symm)).trans
            (w (p'.map φ))
    subst A
    refine IsHomLift.of_fac' p' f φ rfl rfl ?_
    apply OverMorphism.ext
    simpa [q] using (fac' q f.left φ)

/-- If a morphism over `Over U` is strongly cartesian after composing with the slice forgetful
functor, then it is already strongly cartesian in the slice. -/
theorem isStronglyCartesian_of_comp_over_forget {U : C} (p' : S ⥤ Over U)
    {a b : S} {A : Over U} {f : A ⟶ p'.obj a} {φ : b ⟶ a}
    [(p' ⋙ Over.forget U).IsStronglyCartesian f.left φ] :
    p'.IsStronglyCartesian f φ := by
  let q := p' ⋙ Over.forget U
  haveI : p'.IsHomLift f φ := (isHomLift_over_iff_comp_over_forget p').2 inferInstance
  have hA : A = p'.obj b := (domain_eq p' f φ).symm
  subst A
  refine { universal_property' := ?_ }
  intro c g φ' hφ'
  haveI : q.IsHomLift (g ≫ f).left φ' :=
    (isHomLift_over_iff_comp_over_forget p').1 inferInstance
  obtain ⟨χ, hχ, hχuniq⟩ :=
    universal_property q f.left φ g.left ((g ≫ f).left) (by simp) φ'
  refine ⟨χ, ⟨?_, hχ.2⟩, ?_⟩
  · haveI : q.IsHomLift g.left χ := hχ.1
    exact (isHomLift_over_iff_comp_over_forget p').2 inferInstance
  · intro ψ hψ
    haveI : p'.IsHomLift g ψ := hψ.1
    apply hχuniq ψ
    haveI : q.IsHomLift g.left ψ :=
      (isHomLift_over_iff_comp_over_forget p').1 inferInstance
    exact ⟨inferInstance, hψ.2⟩

instance {U : C} (p' : S ⥤ Over U)
    {a b : S} {A : Over U} {f : A ⟶ p'.obj a} {φ : b ⟶ a}
    [(p' ⋙ Over.forget U).IsStronglyCartesian f.left φ] :
    p'.IsStronglyCartesian f φ :=
  isStronglyCartesian_of_comp_over_forget p'

-- Proof sketch: choose a cartesian lift of the underlying arrow `f.left` for
-- `p' ⋙ Over.forget U` using the owner API `Functor.IsPreFibered.exists_isCartesian`, upgrade it
-- to a strongly cartesian lift via
-- `Functor.IsFibered.isStronglyCartesian_of_isCartesian`, and transport that structure to `Over U`
-- with `isStronglyCartesian_of_comp_over_forget`.
/-- Lemma 4.33.11: if a functor `p' : S ⥤ Over U` becomes fibred after composing with the slice
forgetful functor `Over.forget U : Over U ⥤ C`, then `p'` is itself fibred over `Over U`.
Equivalently, if a fibred category over `C` factors through the slice category `C/U`, then the
induced functor to `C/U` is fibred. -/
theorem isFibered_of_comp_over_forget {U : C} (p' : S ⥤ Over U)
    [(p' ⋙ Over.forget U).IsFibered] :
    p'.IsFibered := by
  let q := p' ⋙ Over.forget U
  haveI : q.IsFibered := by
    dsimp [q]
    infer_instance
  exact IsFibered.of_exists_isStronglyCartesian fun a A f ↦ by
    obtain ⟨b, φ, hφ⟩ :=
      IsPreFibered.exists_isCartesian q rfl f.left
    letI : q.IsCartesian f.left φ := hφ
    letI : q.IsStronglyCartesian f.left φ :=
      IsFibered.isStronglyCartesian_of_isCartesian q f.left φ
    haveI : (p' ⋙ Over.forget U).IsStronglyCartesian f.left φ := by
      simpa [q] using (show q.IsStronglyCartesian f.left φ from inferInstance)
    exact ⟨b, φ, inferInstance⟩

instance {U : C} (p' : S ⥤ Over U) [(p' ⋙ Over.forget U).IsFibered] :
    p'.IsFibered :=
  isFibered_of_comp_over_forget p'

end CategoryTheory.Functor

/-! ### Lemma_4_33_12 (from Chap04) -/
universe uA uB uC vA vB vC

namespace CategoryTheory.Functor

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]

/- Domain-style sampling for Lemma 4.33.12:
- primary domain: fibred functors and strongly cartesian lifts under composition;
- sampled owner declarations:
  `Functor.IsFibered`,
  `Functor.IsFibered.of_exists_isStronglyCartesian`,
  `Functor.IsPreFibered.exists_isCartesian`,
  `Functor.isStronglyCartesian_map_comp`, proved in Lemma 4.33.3;
- best owner abstraction: `Functor.IsFibered`;
- primitive data: fibred structures on `F` and `G` together with the cartesian lifts supplied by
  `IsPreFibered.exists_isCartesian`;
- derived API: the induced fibred structure on the composite functor `F ⋙ G`.

Source/core/bridge triage:
- `source-facing`: the Stacks statement that the composite of fibred functors is fibred;
- `core/canonical`: the owner predicate `Functor.IsFibered`;
- `bridge/view`: the instance below deriving the composite owner from the two input owners. -/

-- Proof sketch: choose cartesian lifts first for `G` and then for `F`; in a fibred category these
-- lifts are strongly cartesian, and Lemma 4.33.3 upgrades the resulting lift to a strongly
-- cartesian morphism for the composite functor.
/-- Lemma 4.33.12: if `F : A ⥤ B` is fibred and `G : B ⥤ C` is fibred, then the composite functor
`F ⋙ G : A ⥤ C` is fibred. -/
instance isFibered_comp
    (F : A ⥤ B) (G : B ⥤ C) [F.IsFibered] [G.IsFibered] :
    (F ⋙ G).IsFibered :=
  IsFibered.of_exists_isStronglyCartesian fun a R f ↦ by
    obtain ⟨b, ψ, hψ⟩ := IsPreFibered.exists_isCartesian G rfl f
    obtain ⟨a', φ, hφ⟩ := IsPreFibered.exists_isCartesian F rfl ψ
    letI : G.IsCartesian f ψ := hψ
    letI : F.IsCartesian ψ φ := hφ
    have hb : F.obj a' = b := IsHomLift.domain_eq F ψ φ
    subst b
    have hφ_base : ψ = F.map φ := by
      simpa using (IsHomLift.eq_of_isHomLift F ψ φ)
    subst ψ
    have hR : G.obj (F.obj a') = R := IsHomLift.domain_eq G f (F.map φ)
    subst R
    have hf : f = (F ⋙ G).map φ := by
      simpa [Functor.comp_map] using (IsHomLift.eq_of_isHomLift G f (F.map φ))
    subst f
    letI : F.IsCartesian (F.map φ) φ := hφ
    letI : G.IsCartesian (G.map (F.map φ)) (F.map φ) := by
      simpa [Functor.comp_map] using hψ
    exact ⟨a', φ, isStronglyCartesian_map_comp F G φ⟩

end CategoryTheory.Functor

/-! ### Lemma_4_33_13 (from Chap04) -/
open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

open IsPreFibered

section

variable {C : Type u₁} [Category.{v₁} C]
variable {E : Type u₂} [Category.{v₂} E]

/- Domain-style sampling for Lemma 4.33.13:
- primary domain: fibred categories, strongly cartesian morphisms, and pullbacks in the total
  category;
- inspected owner-level declarations:
  `Functor.IsFibered`,
  `Functor.IsPreFibered.pullbackObj`,
  `Functor.IsPreFibered.pullbackMap`,
  `Functor.IsPreFibered.pullbackObj_proj`,
  `Functor.IsFibered.isStronglyCartesian_of_isCartesian`,
  `strongly_cartesian_pullback_isPullback`;
- best owner abstraction: `Functor.IsFibered`, with the canonical chosen pullback lift supplied by
  `Functor.IsPreFibered.pullbackObj` / `Functor.IsPreFibered.pullbackMap`, and pullback existence
  upstairs derived from the owner-level `IsPullback` theorem in Lemma 4.33.4;
- primitive data: the fibred functor `p`, the strongly cartesian morphism `φ`, and the base
  pullback of `p.map φ` and `p.map ψ`;
- derived API: the canonical chosen pullback lift of the second base projection, the resulting
  source-facing pullback square upstairs, and the weaker `HasPullback φ ψ` corollary.

Source/core/bridge triage:
- `source-facing`: a chosen pullback square above the base pullback, whose second projection is
  strongly cartesian;
- `core/canonical`: `Functor.IsFibered` and `strongly_cartesian_pullback_isPullback`;
- `bridge/view`: `Functor.IsPreFibered.pullbackMap` as the canonical chosen lift, and the theorem
  `hasPullback_of_isStronglyCartesian`, which repackages the canonical pullback square as a
  `HasPullback` instance. -/
-- Proof sketch: use mathlib's canonical pullback lift
-- `IsPreFibered.pullbackObj rfl (pullback.snd (p.map φ) (p.map ψ))` and
-- `IsPreFibered.pullbackMap rfl (pullback.snd (p.map φ) (p.map ψ))`. In a fibered category this
-- map is cartesian, hence strongly cartesian by
-- `IsFibered.isStronglyCartesian_of_isCartesian`; the owner-level theorem
-- `strongly_cartesian_pullback_isPullback` then identifies the resulting chosen square upstairs as
-- a pullback square.
/-- Lemma 4.33.13: if `p : E ⥤ C` is fibered, `φ : x ⟶ y` is strongly cartesian, and the pullback
of `p.map φ` and `p.map ψ` exists in the base, then the canonical pullback lift of
`pullback.snd (p.map φ) (p.map ψ)` forms a pullback square of `φ` and `ψ` in the total category.
Its apex lies over the base pullback by `pullbackObj_proj`, and its right leg is strongly
cartesian by the canonical `IsFibered` pullback-lift instance. -/
theorem chosen_pullback_isPullback_of_isStronglyCartesian
    (p : E ⥤ C) [p.IsFibered]
    {x y z : E} (φ : x ⟶ y) (ψ : z ⟶ y)
    [HasPullback (p.map φ) (p.map ψ)] [p.IsStronglyCartesian (p.map φ) φ] :
    IsPullback
      (IsStronglyCartesian.map p (p.map φ) φ
        (IsPullback.of_hasPullback (p.map φ) (p.map ψ)).w.symm
        (pullbackMap rfl (pullback.snd (p.map φ) (p.map ψ)) ≫ ψ))
      (pullbackMap rfl (pullback.snd (p.map φ) (p.map ψ)))
      φ ψ := by
  -- The canonical lift of the second base projection is cartesian, hence strongly cartesian.
  letI :
      p.IsStronglyCartesian (pullback.snd (p.map φ) (p.map ψ))
        (pullbackMap rfl (pullback.snd (p.map φ) (p.map ψ))) :=
    IsFibered.isStronglyCartesian_of_isCartesian p
      (pullback.snd (p.map φ) (p.map ψ))
      (pullbackMap rfl (pullback.snd (p.map φ) (p.map ψ)))
  -- Lemma 4.33.4 identifies this canonical strongly cartesian lift with the desired pullback
  -- square upstairs.
  simpa using
    (strongly_cartesian_pullback_isPullback (p := p) (φ := φ) (ψ := ψ)
      (a := pullbackMap rfl (pullback.snd (p.map φ) (p.map ψ))))

/- Companion bridge: forgetting the chosen strongly cartesian right leg recovers the ordinary
existence of a pullback of `φ` and `ψ` in the total category. -/
-- Proof sketch: apply `HasPullback.of_isPullback` to the canonical pullback square from
-- `chosen_pullback_isPullback_of_isStronglyCartesian`.
theorem hasPullback_of_isStronglyCartesian
    (p : E ⥤ C) [p.IsFibered]
    {x y z : E} (φ : x ⟶ y) (ψ : z ⟶ y)
    [HasPullback (p.map φ) (p.map ψ)] [p.IsStronglyCartesian (p.map φ) φ] :
    HasPullback φ ψ := by
  -- Forget the chosen pullback square and retain only the existence of the pullback upstairs.
  exact
    (chosen_pullback_isPullback_of_isStronglyCartesian (p := p) (φ := φ)
      (ψ := ψ)).hasPullback

end

end CategoryTheory.Functor
