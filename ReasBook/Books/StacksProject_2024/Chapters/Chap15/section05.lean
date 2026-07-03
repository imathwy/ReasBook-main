import Mathlib
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Category.Ring.Under.Limits
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.Away.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_5_1 (from Chap15) -/
universe u

section

open AlgHom
open scoped BigOperators

variable {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
variable [Algebra R A] [Algebra R B] [Algebra R C]

/-
Domain-style sampling:
- primary domain: finite-type and finite-module arguments for fibre products in commutative
  algebra;
- sampled owner declarations: `AlgHom.equalizer`, `AlgHom.mem_equalizer`,
  `AlgHom.Finite.of_surjective`, and the Artin-Tate consequence
  `Subalgebra.finiteType_of_finite`.
- primitive data: the two comparison maps into `B`, the finite-type hypotheses on `A` and `C`,
  the surjectivity of `f`, and the finiteness of `g`;
- derived API: the finite-type conclusion for the fibre product comes from the Artin-Tate bridge
  once `A × C` is finite over the equalizer.

Source/core/bridge triage:
- `source-facing`: the fibre product is the canonical owner `AlgHom.equalizer` of the two maps
  `A × C →ₐ[R] B`;
- `bridge/view`: the internal module-finite bridge showing that `A × C` is finite as a module
  over that equalizer;
- `core/canonical`: once that bridge is available, the finite-type conclusion is the canonical
  Artin-Tate consequence `Subalgebra.finiteType_of_finite`.
-/
-- Proof sketch: realize `A ×_B C` as the equalizer subalgebra of the two maps
-- `A × C →ₐ[R] B`. Internally, the module-finite bridge identifies `A × C` as finite over that
-- equalizer, and the finite-type conclusion is then the canonical Artin-Tate consequence
-- `Subalgebra.finiteType_of_finite`.
/-- Bridge lemma for Lemma 15.5.1: under the surjective/finite hypotheses, the ambient product
`A × C` is finite as a module over the equalizer subalgebra defining the fibre product. -/
theorem moduleFinite_prod_over_equalizer_of_surjective_of_finite
    (f : A →ₐ[R] B) (g : C →ₐ[R] B) (hf : Function.Surjective f) (hg : g.Finite) :
    Module.Finite (equalizer (f.comp (fst R A C)) (g.comp (snd R A C))) (A × C) := by
  sorry

variable [IsNoetherianRing R] [Algebra.FiniteType R A] [Algebra.FiniteType R C]

/-- Lemma 15.5.1: if `R` is Noetherian, `A` and `C` are of finite type over `R`,
`f : A →ₐ[R] B` is surjective, and `g : C →ₐ[R] B` is finite, then the fibre product
`A ×_B C`, realized as the equalizer subalgebra of `A × C`, is of finite type over `R`. -/
theorem finiteType_fiberProduct_of_surjective_of_finite
    (f : A →ₐ[R] B) (g : C →ₐ[R] B) (hf : Function.Surjective f) (hg : g.Finite) :
    Algebra.FiniteType R (equalizer (f.comp (fst R A C)) (g.comp (snd R A C))) := by
  let left : A × C →ₐ[R] B := f.comp (fst R A C)
  let right : A × C →ₐ[R] B := g.comp (snd R A C)
  let T : Subalgebra R (A × C) := equalizer left right
  change Algebra.FiniteType R T
  let _ : Module.Finite T (A × C) := by
    simpa [T, left, right] using moduleFinite_prod_over_equalizer_of_surjective_of_finite f g hf hg
  exact Subalgebra.finiteType_of_finite T

end

/-! ### Lemma_15_5_2 (from Chap15) -/
open CategoryTheory Limits CommRingCat

universe u

section

variable {ι R : Type u} [Finite ι] [CommRing R]
variable {P Q : Type u} {A B : ι → Type u}
variable [CommRing P] [CommRing Q] [∀ i, CommRing (A i)] [∀ i, CommRing (B i)]
variable [Algebra R P] [Algebra R Q] [∀ i, Algebra R (A i)] [∀ i, Algebra R (B i)]

/- Domain-style sampling:
- primary domain: finite-type stability for finite fibre products of commutative `R`-algebras,
  expressed through pullback squares in `CommRingCat`;
- sampled owner declarations:
  `CommRingCat.pullbackCone`,
  `CommRingCat.pullbackConeIsLimit`,
  `AlgHom.equalizer`,
  `finiteType_fiberProduct_of_surjective_of_finite`;
- best owner abstraction: the source-facing data is the finite family of comparison maps together
  with a categorical pullback witness in `CommRingCat`, while the canonical owner for the
  underlying binary fibre-product ring is still the equalizer/fibre-product API from
  `Lemma_15_5_1`;
- primitive data: the families `φ`, `ψ`, the maps `f`, `g`, the pointwise surjectivity
  hypotheses, and the pullback witness `hcart`;
- derived API: the finite-type conclusion for the pullback ring `P`.

Source/core/bridge triage:
- `source-facing`: the statement about an arbitrary pullback square in `CommRingCat`;
- `core/canonical`: `CommRingCat.pullbackCone` for the categorical owner and
  `finiteType_fiberProduct_of_surjective_of_finite` for the binary algebraic fibre-product
  owner;
- `bridge/view`: passing from the abstract pullback witness `hcart` to the canonical fibre-product
  presentation used by the binary finite-type theorem. -/

-- Proof sketch: induct on the finite index type `ι`. For the inductive step, split off one index
-- `i₀`, apply the induction hypothesis to the pullback defined by the remaining family, and then
-- apply Lemma 15.5.1 to the resulting binary fibre product square with `A i₀ → B i₀`.
/-- Lemma 15.5.2: for a finite family of surjections `Aᵢ → Bᵢ` and `Q → Bᵢ` over a Noetherian
base ring `R`, any pullback ring `P` of `Q → ∏ i, B i` and `∏ i, A i → ∏ i, B i` is of finite
type over `R` as soon as `Q` and all `Aᵢ` are of finite type over `R`; finite type of each `Bᵢ`
is derived from the surjections `Q → Bᵢ`. -/
theorem finiteType_of_isPullback_pi_of_surjective
    [IsNoetherianRing R] [Algebra.FiniteType R Q]
    [∀ i, Algebra.FiniteType R (A i)]
    (φ : ∀ i, A i →ₐ[R] B i) (ψ : ∀ i, Q →ₐ[R] B i) (f : P →ₐ[R] Q)
    (g : P →ₐ[R] ∀ i, A i) (hφ : ∀ i, Function.Surjective (φ i))
    (hψ : ∀ i, Function.Surjective (ψ i)) (hcart : IsPullback (ofHom f.toRingHom)
      (ofHom g.toRingHom) (ofHom (Pi.algHom R B ψ).toRingHom)
      (ofHom (Pi.algHom R B fun i ↦ (φ i).comp (Pi.evalAlgHom R A i)).toRingHom)) :
    Algebra.FiniteType R P := sorry

end

/-! ### Lemma_15_5_3 (from Chap15) -/
open CategoryTheory Limits CommRingCat
open IsLocalization.Away

universe u

namespace CategoryTheory
namespace IsPullback

section

variable {R R' B B' Bg Rf Bh Rh : Type u}
variable [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
variable [CommRing Bg] [CommRing Rf] [CommRing Bh] [CommRing Rh]
variable {s : B →+* R} {t : R' →+* R} {left : B' →+* B} {right : B' →+* R'}
variable (h : B')
variable [Algebra B Bg] [IsLocalization.Away (left h) Bg]
variable [Algebra R' Rf] [IsLocalization.Away (right h) Rf]
variable [Algebra B' Bh] [IsLocalization.Away h Bh]
variable [Algebra R Rh] [IsLocalization.Away (s (left h)) Rh]

/- Domain-style sampling for Lemma 15.5.3:
- primary domain: pullback squares in `CommRingCat` together with localization-away base change;
- sampled owner API:
  `CategoryTheory.IsPullback`,
  `CategoryTheory.Under.pushout`,
  `CommRingCat.Under.preservesFiniteLimits_of_flat`,
  `CommRingCat.isPushout_of_isLocalization`;
- best owner abstraction: base change in the under-category via
  `CategoryTheory.Under.pushout`, with the public statement still phrased by the source-facing
  owner `CategoryTheory.IsPullback`;
- primitive-vs-derived split:
  primitive data: the original pullback witness
    `IsPullback (ofHom left) (ofHom right) (ofHom s) (ofHom t)`
    together with the localization-away instances at `h`, `left h`, `right h`, and the common
    image of `h` in `R`;
  derived API: the four localized comparison maps
    `IsLocalization.Away.map ...`, where the `R'_right(h) → R_common` map uses the pullback
    commutativity to identify `t (right h)` with `s (left h)`, obtained by base change along
    `ofHom (algebraMap B' Bh)`, and the resulting localized pullback square.

This item is therefore a `bridge/view` theorem: the canonical engine is that pushout along the
localization map `B' ⟶ B'_h` preserves finite limits because localizations are flat, while
`CommRingCat.isPushout_of_isLocalization` identifies the pushed-out objects with the usual
away-localizations. The source-facing output remains the localized `IsPullback` square. -/

/- Source/core/bridge triage for Lemma 15.5.3:
- source-facing: localizing a cartesian square of commutative rings away from an element of the
  pullback ring;
- core/canonical: `CategoryTheory.IsPullback` together with base change by
  `CategoryTheory.Under.pushout`;
- bridge/view: the localized square built from the canonical localization maps
  `IsLocalization.Away.map`, with the target-side `R'_right(h) → R_common` map derived from the
  pullback commutativity. -/

lemma away_right_of_localization_away (hsq : IsPullback (ofHom left) (ofHom right) (ofHom s)
    (ofHom t)) : IsLocalization.Away (t (right h)) Rh := by
  have hcomm : s (left h) = t (right h) := by
    simpa [CommRingCat.hom_comp, RingHom.comp_apply] using congr(($hsq.w) h)
  simpa [hcomm] using (inferInstance : IsLocalization.Away (s (left h)) Rh)

/-- The canonical localized comparison map `R'[1 / right(h)] → R[1 / s(left(h))]` induced by the
pullback square. -/
noncomputable def localizationAwayRightMap
    (hsq : IsPullback (ofHom left) (ofHom right) (ofHom s) (ofHom t)) :
    Rf →+* Rh :=
  letI : IsLocalization.Away (t (right h)) Rh := away_right_of_localization_away h hsq
  IsLocalization.Away.map Rf Rh t (right h)

/-- Lemma 15.5.3: localizing a cartesian square of commutative rings away from an element of the
pullback ring again gives a cartesian square. -/
-- Proof sketch: start from the owner witness `hsq : IsPullback ...`. The localized comparison maps
-- are the canonical maps between away-localizations, with the target-side map packaged as the
-- explicit bridge `localizationAwayRightMap h hsq`. Regard the square as a pullback in
-- `Under (CommRingCat.of B')`, apply base change along `ofHom (algebraMap B' Bh)`, and use
-- `CommRingCat.Under.preservesFiniteLimits_of_flat` for the flat localization map. Finally
-- identify the pushed-out objects with the away-localizations via
-- `CommRingCat.isPushout_of_isLocalization`.
theorem localization_away
    (hsq : IsPullback (ofHom left) (ofHom right) (ofHom s) (ofHom t)) :
    IsPullback (ofHom (IsLocalization.Away.map Bh Bg left h))
      (ofHom (IsLocalization.Away.map Bh Rf right h))
      (ofHom (IsLocalization.Away.map Bg Rh s (left h)))
      (ofHom (localizationAwayRightMap h hsq)) := by
  letI : IsLocalization.Away (t (right h)) Rh := away_right_of_localization_away h hsq
  let base : of B' ⟶ of Bh := ofHom (algebraMap B' Bh)
  let baseChange : Under (of B') ⥤ Under (of Bh) :=
    Under.pushout base
  have hflat : RingHom.Flat (algebraMap B' Bh) := by
    rw [RingHom.flat_algebraMap_iff]
    exact IsLocalization.flat Bh (Submonoid.powers h)
  let _ : PreservesFiniteLimits baseChange :=
    CommRingCat.Under.preservesFiniteLimits_of_flat base hflat
  -- Convert the original square to `Under (CommRingCat.of B')`, apply `IsPullback.map` to the
  -- flat base-change functor `baseChange`, and then identify the pushed-out objects with the
  -- away-localizations via the canonical localization pushout squares.
  sorry

end

end IsPullback
end CategoryTheory

/-! ### Lemma_15_5_4 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.CategoricalPullback

universe u

noncomputable section

section

variable {R R' B B' : Type u}
variable [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
variable {s : B →+* R} {t : R' →+* R} (f : B' →+* B) (g : B' →+* R')
variable (hcomm : s.comp f = t.comp g)

local notation "PullbackModuleCat" =>
  CategoricalPullback (ModuleCat.extendScalars s) (ModuleCat.extendScalars t)

/- Domain-style sampling for Lemma 15.5.4:
- primary domain: categorical base change for module categories over a commutative square of
  commutative rings, together with the kernel model of the fibre-product module;
- sampled owner declarations:
  `CategoricalPullback.CatCommSqOver`,
  `CategoricalPullback.π₂`,
  `moduleCatBaseChangeToCategoricalPullback`,
  `CategoryTheory.CommSq`,
  `Limits.ker`;
- best owner abstraction: the source-facing right adjoint is the kernel of the canonical
  `Arrow (ModuleCat B')`-valued functor attached to the defining difference morphism;
- primitive data: the product source functor, the common target functor, and the defining
  difference natural transformation between them;
- derived API: the induced `Arrow`-valued functor, the kernel-valued right adjoint, the universal
  lift into that kernel, and the adjunction with base change.

Source/core/bridge triage:
- `source-facing`: `module_tensor_pullback_right_adjoint`,
  `module_tensor_pullback_right_adjoint_lift`,
  `module_tensor_pullback_adjunction`;
- `core/canonical`: `Arrow (ModuleCat B')`, `Limits.ker`, and the chapter owner
  `moduleCatBaseChangeToCategoricalPullback`;
- `bridge/view`: the explicit difference morphism whose kernel realizes the fibre-product module. -/

private abbrev rightAdjointSourceObj
    (f : B' →+* B) (g : B' →+* R') (X : PullbackModuleCat) : ModuleCat B' :=
  Limits.prod ((ModuleCat.restrictScalars f).obj X.fst) ((ModuleCat.restrictScalars g).obj X.snd)

private abbrev rightAdjointTargetObj
    (g : B' →+* R') (X : PullbackModuleCat) : ModuleCat B' :=
  (ModuleCat.restrictScalars (t.comp g)).obj ((ModuleCat.extendScalars t).obj X.snd)

/-- The left comparison map from the first component to the common target, obtained from the unit of
extension-restriction of scalars and the structural isomorphism in the categorical pullback. -/
abbrev module_tensor_pullback_left_map
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g) (X : PullbackModuleCat) :
    (ModuleCat.restrictScalars f).obj X.fst ⟶
      (ModuleCat.restrictScalars (t.comp g)).obj ((ModuleCat.extendScalars t).obj X.snd) :=
  (ModuleCat.restrictScalars f).map ((ModuleCat.extendRestrictScalarsAdj s).unit.app X.fst) ≫
    (ModuleCat.restrictScalarsComp f s).inv.app ((ModuleCat.extendScalars s).obj X.fst) ≫
    (ModuleCat.restrictScalars (s.comp f)).map X.iso.hom ≫
    (eqToIso (congrArg
      (fun u ↦ (ModuleCat.restrictScalars u).obj ((ModuleCat.extendScalars t).obj X.snd))
      hcomm)).hom

/-- The right comparison map from the second component to the common target, corresponding to the
element `m' ↦ 1 ⊗ m'`. -/
abbrev module_tensor_pullback_right_map
    (g : B' →+* R') (X : PullbackModuleCat) :
    (ModuleCat.restrictScalars g).obj X.snd ⟶
      (ModuleCat.restrictScalars (t.comp g)).obj ((ModuleCat.extendScalars t).obj X.snd) :=
  (ModuleCat.restrictScalars g).map ((ModuleCat.extendRestrictScalarsAdj t).unit.app X.snd) ≫
    (ModuleCat.restrictScalarsComp g t).inv.app ((ModuleCat.extendScalars t).obj X.snd)

private abbrev rightAdjointLeftMap
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g) (X : PullbackModuleCat) :
    rightAdjointSourceObj f g X ⟶ rightAdjointTargetObj g X :=
  Limits.prod.fst ≫ module_tensor_pullback_left_map f g hcomm X

private abbrev rightAdjointRightMap
    (f : B' →+* B) (g : B' →+* R') (X : PullbackModuleCat) :
    rightAdjointSourceObj f g X ⟶ rightAdjointTargetObj g X :=
  Limits.prod.snd ≫ module_tensor_pullback_right_map g X

/-- The difference of the two comparison maps whose kernel is the fibre product module
`N ×_φ M'`. -/
private abbrev rightAdjointDifference
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g) (X : PullbackModuleCat) :
    rightAdjointSourceObj f g X ⟶ rightAdjointTargetObj g X :=
  rightAdjointLeftMap f g hcomm X - rightAdjointRightMap f g X

/-- The ambient product modules assemble functorially over the categorical pullback. -/
private def rightAdjointSourceFunctor
    (f : B' →+* B) (g : B' →+* R') : PullbackModuleCat ⥤ ModuleCat B'
    where
  obj X := rightAdjointSourceObj f g X
  map φ := Limits.prod.map ((ModuleCat.restrictScalars f).map φ.fst)
    ((ModuleCat.restrictScalars g).map φ.snd)
  map_id X := by
    ext <;> simp
  map_comp φ ψ := by
    ext <;> simp

/-- The common targets assemble functorially over the categorical pullback. -/
private def rightAdjointTargetFunctor
    (g : B' →+* R') : PullbackModuleCat ⥤ ModuleCat B'
    where
  obj X := rightAdjointTargetObj g X
  map φ := (ModuleCat.restrictScalars (t.comp g)).map ((ModuleCat.extendScalars t).map φ.snd)
  map_id X := by
    simp
  map_comp φ ψ := by
    simp

-- Proof sketch: expand the two comparison morphisms on both sides. Naturality of the adjunction
-- unit, of `restrictScalarsComp`, and of the structural morphism `φ.w` in the categorical pullback
-- gives commutativity for the left and right comparison maps separately; subtract the two resulting
-- identities.
/-- Compatibility of the defining difference morphism with morphisms in the categorical pullback of
module categories. -/
private theorem rightAdjointDifference_naturality
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    {X Y : PullbackModuleCat}
    (φ : X ⟶ Y) :
    (rightAdjointSourceFunctor f g).map φ ≫
      rightAdjointDifference f g hcomm Y =
    rightAdjointDifference f g hcomm X ≫
      (rightAdjointTargetFunctor g).map φ := sorry

/-- The defining difference maps form a natural transformation on the categorical pullback. -/
private def rightAdjointDifferenceNatTrans
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g) :=
  let T : PullbackModuleCat ⥤ ModuleCat B' := rightAdjointTargetFunctor g
  show rightAdjointSourceFunctor f g ⟶ T from
    { app := fun X ↦ rightAdjointDifference f g hcomm X
      naturality := by
        intro X Y φ
        exact rightAdjointDifference_naturality f g hcomm φ }

/-- The canonical `Arrow (ModuleCat B')`-valued functor whose pointwise kernels are the
fibre-product modules attached to objects of the categorical pullback. -/
private def rightAdjointArrow
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g) :
    PullbackModuleCat ⥤ Arrow (ModuleCat B') where
  obj X := Arrow.mk ((rightAdjointDifferenceNatTrans f g hcomm).app X)
  map {X Y} φ :=
    Arrow.homMk'
      ((rightAdjointSourceFunctor f g).map φ)
      ((rightAdjointTargetFunctor g).map φ)
      ((rightAdjointDifferenceNatTrans f g hcomm).naturality φ)

/-- The explicit right adjoint to the module tensor pullback functor, sending a pullback object
`(N, M', φ)` to the fibre product module `N ×_φ M'`. -/
abbrev module_tensor_pullback_right_adjoint
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g) :
    PullbackModuleCat ⥤ ModuleCat B' :=
  rightAdjointArrow f g hcomm ⋙ Limits.ker (ModuleCat B')


-- Proof sketch: compose the given pair of maps into the ambient product module. The compatibility
-- hypothesis is precisely the condition that this product morphism equalizes the two comparison
-- maps, hence annihilates their difference; the universal property of the kernel then produces the
-- desired map into the fibre-product module.
private theorem rightAdjointLift_condition
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    {L : ModuleCat B'}
    {X : PullbackModuleCat}
    (u : L ⟶ (ModuleCat.restrictScalars f).obj X.fst)
    (v : L ⟶ (ModuleCat.restrictScalars g).obj X.snd)
    (hcompat : CommSq u v (module_tensor_pullback_left_map f g hcomm X)
      (module_tensor_pullback_right_map g X)) :
    Limits.prod.lift u v ≫ rightAdjointDifference f g hcomm X = 0 := by
  rw [rightAdjointDifference, Preadditive.comp_sub, sub_eq_zero]
  calc
    Limits.prod.lift u v ≫ rightAdjointLeftMap f g hcomm X =
        u ≫ module_tensor_pullback_left_map f g hcomm X := by
          rw [rightAdjointLeftMap, ← Category.assoc, Limits.prod.lift_fst]
    _ = v ≫ module_tensor_pullback_right_map g X := by
          simpa using hcompat.w
    _ = Limits.prod.lift u v ≫ rightAdjointRightMap f g X := by
          symm
          rw [rightAdjointRightMap, ← Category.assoc, Limits.prod.lift_snd]

/-- The universal morphism into the fibre-product module `N ×_φ M'` attached to a compatible pair
of maps into `N` and `M'`. -/
abbrev module_tensor_pullback_right_adjoint_lift
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    {L : ModuleCat B'}
    {X : PullbackModuleCat}
    (u : L ⟶ (ModuleCat.restrictScalars f).obj X.fst)
    (v : L ⟶ (ModuleCat.restrictScalars g).obj X.snd)
    (hcompat : CommSq u v (module_tensor_pullback_left_map f g hcomm X)
      (module_tensor_pullback_right_map g X)) :
    L ⟶ (module_tensor_pullback_right_adjoint f g hcomm).obj X :=
  kernel.lift
    (rightAdjointDifference f g hcomm X)
    (Limits.prod.lift u v)
    (rightAdjointLift_condition f g hcomm u v hcompat)

-- Proof sketch: for `L' : ModuleCat B'` and `X = (N, M', φ)` in the categorical pullback, use the
-- adjunctions `extendScalars ⊣ restrictScalars` for `f`, `g`, and `t`, together with the kernel
-- description of `module_tensor_pullback_fiber_product`, to identify morphisms
-- `L' ⟶ N ×_φ M'` with pairs of morphisms to `N` and `M'` satisfying the pullback compatibility.
-- This is exactly the hom-set description of maps from
-- `(moduleCatBaseChangeToCategoricalPullback s t f g hcomm).obj L'` to `X`.
private def rightAdjointHomEquiv
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    (L' : ModuleCat B') (X : PullbackModuleCat) :
    ((moduleCatBaseChangeToCategoricalPullback s t f g hcomm).obj L' ⟶ X) ≃
      (L' ⟶ kernel (rightAdjointDifference f g hcomm X)) where
  toFun φ :=
    let u : L' ⟶ (ModuleCat.restrictScalars f).obj X.fst :=
        (ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _
          (by simpa using φ.fst)
    let v : L' ⟶ (ModuleCat.restrictScalars g).obj X.snd :=
      (ModuleCat.extendRestrictScalarsAdj g).homEquiv _ _
        (by simpa using φ.snd)
    module_tensor_pullback_right_adjoint_lift f g hcomm u v (by
      sorry)
  invFun ψ :=
    { fst :=
        (by
          simpa using
            ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm
              (ψ ≫
                kernel.ι (rightAdjointDifference f g hcomm X) ≫
                Limits.prod.fst))
      snd :=
        (by
          simpa using
            ((ModuleCat.extendRestrictScalarsAdj g).homEquiv _ _).symm
              (ψ ≫
                kernel.ι (rightAdjointDifference f g hcomm X) ≫
                Limits.prod.snd))
      w := by
        sorry }
  left_inv φ := by
    ext <;> sorry
  right_inv ψ := by
    sorry

/-- Lemma 15.5.4: the base-change functor
`Mod_{B'} → Mod_B ×[Mod_R] Mod_{R'}`
is left adjoint to the fibre-product module functor
`(N, M', φ) ↦ N ×_φ M'`. -/
def module_tensor_pullback_adjunction
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g) :
    moduleCatBaseChangeToCategoricalPullback s t f g hcomm ⊣
      module_tensor_pullback_right_adjoint f g hcomm :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun L' X ↦ by
        simpa [module_tensor_pullback_right_adjoint] using
          rightAdjointHomEquiv f g hcomm L' X
      homEquiv_naturality_left_symm := by
        intro L₁ L₂ X a b
        sorry
      homEquiv_naturality_right := by
        intro L' X Y a b
        sorry }

/-- The counit of `module_tensor_pullback_adjunction` is an isomorphism, so the composite from the
categorical pullback back to itself through the fibre-product module functor and base change is the
identity functor up to canonical isomorphism. -/
theorem module_tensor_pullback_adjunction_counit_isIso
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g) :
    IsIso
      ((module_tensor_pullback_adjunction f g hcomm).counit :
        module_tensor_pullback_right_adjoint f g hcomm ⋙
            moduleCatBaseChangeToCategoricalPullback s t f g hcomm ⟶
          𝟭 PullbackModuleCat) := sorry

instance : (moduleCatBaseChangeToCategoricalPullback s t f g hcomm).IsLeftAdjoint :=
  (module_tensor_pullback_adjunction f g hcomm).isLeftAdjoint

instance : (module_tensor_pullback_right_adjoint f g hcomm).IsRightAdjoint :=
  (module_tensor_pullback_adjunction f g hcomm).isRightAdjoint

end
