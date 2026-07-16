import StacksProject_2024.stacks_project.Chap18.Definition_18_28_1
import StacksProject_2024.stacks_project.Chap12.Lemma_12_7_2
import StacksProject_2024.stacks_project.Chap10.Lemma_10_75_5
import StacksProject_2024.stacks_project.Chap21.Definition_21_17_14

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
variable [HasProjectiveResolutions (ringedSiteModuleCategory J 𝒪)]

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "Tor[" p "](" ℱ ", " 𝒢 ")" => SheafOfModules.RingedSite.tor p ℱ 𝒢

/-- Helper for Lemma 21.17.15: the ambient category of `𝒪`-modules on the ringed site is
abelian. -/
local instance : Abelian Mod :=
  SheafOfModules.instAbelian (ringSheaf J 𝒪)

/-- Helper for Lemma 21.17.15: if tensoring on the right by `ℱ` sends every short exact sequence
to a short exact sequence, then `ℱ` is flat. -/
private theorem isFlatOfMapsShortExact
    (ℱ : Mod)
    (hℱ : ∀ T : ShortComplex Mod,
      T.ShortExact → (T.map (tensorRight ℱ)).ShortExact) :
    IsFlat 𝒪 ℱ := by
  -- Proof comment: this should be the Chapter 12 exact-functor criterion applied to
  -- `tensorRight ℱ`.
  -- TODO: restore the ambient `Abelian Mod` owner path for
  -- `functor_exact_iff_maps_shortExact_to_exact_mono_epi`, then finish by packaging the mapped
  -- short exact rows supplied by `hℱ`.
  sorry

/-- Helper for Lemma 21.17.15: right tensoring is always right exact, so it preserves exactness
at the middle term of a short exact row and keeps the right map epimorphic. -/
private theorem tensorRightMapsShortExactToExactEpi
    (ℱ : Mod)
    (T : ShortComplex Mod)
    (hT : T.ShortExact) :
    (ComposableArrows.mk₂ ((tensorRight ℱ).map T.f) ((tensorRight ℱ).map T.g)).Exact ∧
      Epi ((tensorRight ℱ).map T.g) := by
  -- Proof comment: the intended route is the standard right exactness of tensor product in the
  -- second variable, followed by the Chapter 12 short-exact-sequence criterion.
  -- TODO: expose the missing `PreservesFiniteColimits (tensorRight ℱ)` / right-exactness owner
  -- for ringed-site modules under the current ambient hypotheses, then apply the recalled
  -- `functor_rightExact_iff_maps_shortExact_to_exact_epi`.
  sorry

/-- Helper for Lemma 21.17.15: `Tor[1](ℱ, 𝒢)` is the first left-derived object of
`tensorRight ℱ` evaluated at `𝒢`. -/
private lemma torOneIsoTensorRightLeftDerived
    (ℱ 𝒢 : Mod) :
    Tor[1](ℱ, 𝒢) ≅ ((tensorRight ℱ).leftDerived 1).obj 𝒢 := by
  let eFlip :
      Tor[1](ℱ, 𝒢) ≅ (((Functor.flip (Tor' Mod 1)).obj ℱ).obj 𝒢) :=
    asIso (((tor_flip_iso Mod 1).app ℱ).hom.app 𝒢)
  let eResolution :
      (((Functor.flip (Tor' Mod 1)).obj ℱ).obj 𝒢) ≅
        ((tensorRight ℱ).leftDerived 1).obj 𝒢 := by
    -- Proof comment: after flipping the Tor variables, the chosen projective resolution of `𝒢`
    -- computes the first left-derived object of `tensorRight ℱ`.
    simpa [Tor', Functor.flip] using
      ((CategoryTheory.projectiveResolution 𝒢).isoLeftDerivedObj (tensorRight ℱ) 1)
  -- Proof comment: compose the braided flip with the standard projective-resolution computation.
  exact eFlip ≪≫ eResolution

/-- Helper for Lemma 21.17.15: exactness of `tensorRight ℱ` forces the degree-one Tor object
`Tor[1](ℱ, 𝒢)` to vanish. -/
private theorem isZeroTorOneOfExactTensor
    (ℱ 𝒢 : Mod)
    (hExact : exactFunctor Mod Mod (tensorRight ℱ)) :
    IsZero (Tor[1](ℱ, 𝒢)) := by
  let e := torOneIsoTensorRightLeftDerived (𝒪 := 𝒪) ℱ 𝒢
  -- Proof comment: first normalize `Tor[1](ℱ, 𝒢)` to the degree-one left-derived object of
  -- `tensorRight ℱ`, so the only remaining step is the exact-functor vanishing statement.
  -- TODO: prove `IsZero (((tensorRight ℱ).leftDerived 1).obj 𝒢)` from `hExact` by computing the
  -- chosen projective resolution of `𝒢` and using exactness of the mapped resolution complex.
  sorry

/-- Helper for Lemma 21.17.15: if `Tor[1](ℱ, -)` vanishes on every object, then tensoring a
short exact row on the right by `ℱ` remains short exact. -/
private theorem shortExactMapTensorRightOfTorOneZero
    (ℱ : Mod)
    (hTor : ∀ 𝒢 : Mod, IsZero (Tor[1](ℱ, 𝒢)))
    (T : ShortComplex Mod)
    (hT : T.ShortExact) :
    (T.map (tensorRight ℱ)).ShortExact := by
  let hExactEpi := tensorRightMapsShortExactToExactEpi (𝒪 := 𝒪) ℱ T hT
  -- Proof comment: right exactness already gives exactness and the epimorphic right map; the
  -- missing monomorphism on the left should come from the low-degree long exact Tor sequence and
  -- the vanishing hypothesis on `Tor[1](ℱ, T.X₃)`.
  let hTorDerived :
      IsZero (((tensorRight ℱ).leftDerived 1).obj T.X₃) := by
    -- Proof comment: rewrite the `Tor₁` vanishing hypothesis into the left-derived owner used by
    -- the long exact homology sequence of `tensorRight ℱ`.
    exact IsZero.of_iso (hTor T.X₃) (torOneIsoTensorRightLeftDerived (𝒪 := 𝒪) ℱ T.X₃).symm
  -- TODO: isolate the degree-zero/degree-one homology-sequence bridge that upgrades the left map
  -- to a monomorphism from `hTor T.X₃`.
  let _hExact :
      (ComposableArrows.mk₂ ((tensorRight ℱ).map T.f) ((tensorRight ℱ).map T.g)).Exact :=
    hExactEpi.1
  let _hEpi : Epi ((tensorRight ℱ).map T.g) := hExactEpi.2
  -- TODO: apply `Functor.homologySequenceComposableArrows₅_exact` to the triangle of `T`,
  -- identify the degree-zero terms with `(tensorRight ℱ).obj T.X₁` and `(tensorRight ℱ).obj T.X₂`
  -- via `leftDerivedZeroIsoSelf`, and use `hTorDerived` to deduce mono on `((tensorRight ℱ).map T.f)`.
  sorry

/- Domain-style sampling for Lemma 21.17.15:
- primary domain: flat sheaves of modules on a ringed site and the first left-derived tensor
  functor on the ambient monoidal abelian category `Mod`;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `SheafOfModules.RingedSite.IsFlat`,
  `CategoryTheory.Tor`,
  `Definition_21_17_14`'s chapter-21 specialization `Tor Mod p`;
- best owner abstraction: flatness is already owned by `SheafOfModules.RingedSite.IsFlat`, while
  the Tor side of the criterion is already owned by the canonical ringed-site specialization
  `Tor[1](ℱ, 𝒢)` from Definition `21.17.14`; this item stays a source-facing criterion theorem and
  reuses that owner directly;
- primitive data: the module `ℱ : Mod`;
- derived API: the vanishing condition `∀ 𝒢 : Mod, IsZero (Tor[1](ℱ, 𝒢))`.

Source/core/bridge triage:
- `source-facing`: the flatness criterion stated as vanishing of `Tor₁`;
- `core/canonical`: `SheafOfModules.RingedSite.IsFlat` and `Tor[1](ℱ, 𝒢)`;
- `bridge/view`: no extra bridge is needed here, because Definition `21.17.14` already records the
  ringed-site specialization of the canonical Tor owner. -/

-- Proof sketch: if `ℱ` is flat, then tensoring with `ℱ` is exact, so its first left derived
-- functor vanishes and hence `Tor₁` is zero against every `𝒢`. Conversely, apply the long exact
-- `Tor` sequence to a short exact sequence `0 ⟶ 𝒢 ⟶ ℋ ⟶ 𝒬 ⟶ 0`; vanishing of `Tor[1](ℱ, 𝒬)` forces
-- tensoring with `ℱ` to preserve monomorphisms, which is the flatness criterion.
/-- Lemma 21.17.15: a sheaf of `𝒪`-modules on a ringed site is flat if and only if
`Tor[1](ℱ, 𝒢)` vanishes for every `𝒪`-module `𝒢`. -/
@[stacks 08FG]
theorem isFlat_iff_isZero_tor_one
    (ℱ : Mod) :
    IsFlat 𝒪 ℱ ↔
      ∀ 𝒢 : Mod, IsZero (Tor[1](ℱ, 𝒢)) := by
  constructor
  · intro hFlat 𝒢
    -- Proof comment: a flat module makes `tensorRight ℱ` exact, and the first Tor group is the
    -- first left derived object of that exact functor.
    exact isZeroTorOneOfExactTensor (𝒪 := 𝒪) ℱ 𝒢 hFlat.exact_tensor
  · intro hTor
    -- Proof comment: it is enough to show that tensoring by `ℱ` preserves short exact rows.
    exact isFlatOfMapsShortExact (𝒪 := 𝒪) ℱ fun T hT ↦
      shortExactMapTensorRightOfTorOneZero (𝒪 := 𝒪) ℱ hTor T hT

/-- Forward companion to Lemma 21.17.15: flat modules have vanishing first Tor against every
module. -/
theorem isZero_tor_one_of_isFlat
    (ℱ : Mod) (hFlat : IsFlat 𝒪 ℱ) (𝒢 : Mod) :
    IsZero (Tor[1](ℱ, 𝒢)) :=
  (isFlat_iff_isZero_tor_one ℱ).1 hFlat 𝒢

/-- Typeclass form of the forward direction of Lemma 21.17.15: if `ℱ` is flat, then
`Tor[1](ℱ, 𝒢)` is zero for every `𝒪`-module `𝒢`. -/
instance instIsZeroTorOneOfIsFlat
    (ℱ 𝒢 : Mod) [hFlat : IsFlat 𝒪 ℱ] :
    IsZero (Tor[1](ℱ, 𝒢)) :=
  isZero_tor_one_of_isFlat ℱ hFlat 𝒢

/-- Converse companion to Lemma 21.17.15: vanishing of first Tor against every module detects
flatness. -/
theorem isFlat_of_isZero_tor_one
    (ℱ : Mod) (hTor : ∀ 𝒢 : Mod, IsZero (Tor[1](ℱ, 𝒢))) :
    IsFlat 𝒪 ℱ :=
  (isFlat_iff_isZero_tor_one ℱ).2 hTor

end SheafOfModules.RingedSite
