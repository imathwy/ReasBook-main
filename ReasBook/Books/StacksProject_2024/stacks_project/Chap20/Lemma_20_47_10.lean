import StacksProject_2024.Chap20.Lemma_20_47_9

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X.carrier).HasSheafCompose
  (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [∀ U : Opens X.carrier,
  HasWeakSheafify ((Opens.grothendieckTopology X.carrier).over U) AddCommGrpCat.{u}]
variable [∀ U : Opens X.carrier,
  ((Opens.grothendieckTopology X.carrier).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ U : Opens X.carrier,
  ((Opens.grothendieckTopology X.carrier).over U).HasSheafCompose
    (forget₂ RingCat.{u} AddCommGrpCat.{u})]

local notation "ModX" => X.Modules

/- Domain-style sampling for Lemma 20.47.10:
- primary domain: pseudo-coherence of `𝒪_X`-modules viewed through the Chapter 20
  module-sheaf owner `ℱ.IsMPseudoCoherent m`;
- sampled owner declarations:
  `ModuleDerived`,
  `IsMPseudoCoherent`,
  `SheafOfModules.IsFiniteType`,
  `SheafOfModules.IsFinitePresentation`;
- best owner abstraction: the module-sheaf owner `ℱ.IsMPseudoCoherent m` already packages the
  canonical degree-zero embedding into `D(𝒪_X)`, so the source-facing finite-type and
  finite-presentation characterizations below should use that owner directly rather than restating
  the derived single-object expression;
- primitive data: a module sheaf `ℱ : ModX`;
- derived API: the two iff characterizations below.

Source/core/bridge triage:
- `source-facing`: the two finite-type / finite-presentation characterizations for module sheaves;
- `core/canonical`: `ℱ.IsMPseudoCoherent m`, `ℱ.IsFiniteType`, and `ℱ.IsFinitePresentation`;
- `bridge/view`: the two equivalences below.
-/

-- Proof sketch: for the forward implication, apply Lemma `20.47.9` to the degree-zero derived
-- object `ℱ[0]`, whose higher cohomology sheaves vanish, and transport the resulting finite-type
-- structure on `H⁰(ℱ[0])` across the canonical identification `H⁰(ℱ[0]) ≅ ℱ`. For the converse,
-- work locally on an affine open cover: finite type of the restricted module sheaf becomes the
-- corresponding finite-generation statement for an ordinary module, and Lemma `15.65.4` identifies
-- that module-theoretic condition with `0`-pseudo-coherence of the associated degree-zero derived
-- object. These local witnesses glue back to `ℱ.IsMPseudoCoherent 0` via Definition `20.47.1`.
/-- Lemma 20.47.10 (1): a sheaf of `𝒪_X`-modules, viewed in `D(𝒪_X)` as a
complex concentrated in degree `0`, is `0`-pseudo-coherent if and only if it is of finite type. -/
@[stacks 09V9]
theorem isZeroPseudoCoherent_iff_isFiniteType
    (ℱ : ModX) :
    ℱ.IsMPseudoCoherent 0 ↔ ℱ.IsFiniteType := sorry

/-- A `0`-pseudo-coherent sheaf of `𝒪_X`-modules is of finite type. -/
instance instIsFiniteTypeOfIsZeroPseudoCoherent
    (ℱ : ModX) (hℱ : ℱ.IsMPseudoCoherent 0) :
    ℱ.IsFiniteType :=
  (isZeroPseudoCoherent_iff_isFiniteType ℱ).mp hℱ

-- Proof sketch: for the forward implication, apply Lemma `20.47.9` with `m = -1` to `ℱ[0]`; the
-- vanishing of cohomology in degrees `> 0` shows that `H⁰(ℱ[0])`, hence `ℱ`, is finitely
-- presented. For the converse, again argue locally on affine opens: finite presentation of the
-- restricted module sheaf becomes finite presentation of an ordinary module, and Lemma `15.65.4`
-- identifies that local algebra statement with `(-1)`-pseudo-coherence of the degree-zero derived
-- object. The local criterion in Definition `20.47.1` then yields `ℱ.IsMPseudoCoherent (-1)`.
/-- Lemma 20.47.10 (2): a sheaf of `𝒪_X`-modules, viewed in `D(𝒪_X)` as a
complex concentrated in degree `0`, is `(-1)`-pseudo-coherent if and only if it is of finite
presentation. -/
@[stacks 09V9]
theorem isMinusOnePseudoCoherent_iff_isFinitePresentation
    (ℱ : ModX) :
    ℱ.IsMPseudoCoherent (-1) ↔ ℱ.IsFinitePresentation := sorry

/-- A `(-1)`-pseudo-coherent sheaf of `𝒪_X`-modules is finitely presented. -/
instance instIsFinitePresentationOfIsMinusOnePseudoCoherent
    (ℱ : ModX) (hℱ : ℱ.IsMPseudoCoherent (-1)) :
    ℱ.IsFinitePresentation :=
  (isMinusOnePseudoCoherent_iff_isFinitePresentation ℱ).mp hℱ

end SheafOfModules
