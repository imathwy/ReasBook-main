import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_17_25_1 (from Chap17) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open SheafOfModules.RingedSite
open TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}

local notation "ModX" => RingedSpace.Modules X
local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : ModX)

/- Domain-style sampling for Definition 17.25.1:
- primary domain: invertible sheaves of modules on a ringed space, as the ringed-space
  specialization of the ringed-site module theory;
- inspected owner declarations:
  `RingedSpace.Modules`,
  `ringedSiteModuleCategory`,
  `tensorLeft`,
  `CategoryTheory.tensorLeft_isEquivalence_iff_tensorRight_isEquivalence`,
  `SheafOfModules.RingedSite.IsInvertible`,
  `SheafOfModules.RingedSite.unit_isInvertible`;
- best owner abstraction: the canonical owner is the Chapter 18 ringed-site class
  `SheafOfModules.RingedSite.IsInvertible`, specialized to the ringed-space owner
  `X.Modules`; the left-tensor equivalence is the source-facing companion bridge;
- primitive data: a module sheaf `ℒ : ModX`;
- derived API: the bridge theorem `isInvertible_iff_tensorLeft_isEquivalence` and the
  source-facing triviality predicate `IsTrivial ℒ`.

Layer triage:
- `source-facing`: the textbook bridge from invertibility to the left-tensor criterion, and
  trivial `\mathcal O_X`-modules;
- `core/canonical`: `SheafOfModules.RingedSite.IsInvertible`;
- `bridge/view`: the equivalence between left and right tensor criteria on `ModX`.
-/

section Invertible

variable [MonoidalCategory ModX]

/- Definition 17.25.1 (1): on a ringed space, an invertible `\mathcal O_X`-module is the
canonical ringed-site owner `SheafOfModules.RingedSite.IsInvertible`, specialized to `ModX`. -/
recall SheafOfModules.RingedSite.IsInvertible

variable (ℒ : ModX)

/-- On a ringed space, the canonical owner `IsInvertible` is equivalent to the source-facing
left-tensor criterion. -/
theorem isInvertible_iff_tensorLeft_isEquivalence :
    IsInvertible ℒ ↔ (tensorLeft ℒ).IsEquivalence :=
  ⟨fun hℒ ↦
      let _ : IsInvertible ℒ := hℒ
      (tensorLeft_isEquivalence_iff_tensorRight_isEquivalence ℒ).2 inferInstance,
    fun hℒ ↦
      let _ : Functor.IsEquivalence (tensorRight ℒ) :=
        (tensorLeft_isEquivalence_iff_tensorRight_isEquivalence ℒ).1 hℒ
      inferInstance⟩

end Invertible

/-- Definition 17.25.1 (2): an invertible `\mathcal O_X`-module is trivial if it is isomorphic,
as an `\mathcal O_X`-module, to the structure sheaf. -/
abbrev IsTrivial (ℒ : ModX) : Prop :=
  Nonempty (ℒ ≅ 𝒪X)

-- Proof sketch: the structure sheaf is trivially isomorphic to itself via the identity
-- isomorphism.
/-- The structure sheaf is trivial as an `\mathcal O_X`-module. -/
theorem unit_isTrivial :
    IsTrivial 𝒪X :=
  ⟨Iso.refl _⟩

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_17_25_2 (from Chap17) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open SheafOfModules.RingedSite
open TopologicalSpace

noncomputable section

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}

variable [MonoidalCategory (RingedSpace.Modules X)]
variable [SymmetricCategory (RingedSpace.Modules X)]

local notation "ModX" => RingedSpace.Modules X
local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : ModX)
local notation:70 A " ⊗ₘ " B => (tensorObj A B : ModX)
local notation "IsInvertible" =>
  @SheafOfModules.RingedSite.IsInvertible _ _ (Opens.grothendieckTopology X) X.sheaf _ _
/- Domain-style sampling for Lemma 17.25.2:
- primary domain: invertible `\mathcal O_X`-modules on a ringed space, viewed through the
  canonical ringed-site owner and its source-facing tensor-inverse consequences;
- inspected owner declarations:
  `AlgebraicGeometry.RingedSpace.isInvertible_iff_tensorLeft_isEquivalence`,
  `SheafOfModules.RingedSite.isInvertible_iff_exists_tensor_inverse`,
  `SheafOfModules.RingedSite.isLocallyDirectSummandOfFiniteFree_of_isInvertible`,
  `SheafOfModules.RingedSite.nonempty_iso_ringedSiteModuleDual_of_tensor_inverse`,
  `SheafOfModules.RingedSite.ringedSiteModuleDual`;
- best owner abstraction: `SheafOfModules.RingedSite.IsInvertible`, specialized to `ModX`; the
  tensor-left equivalence and tensor-inverse statements are source-facing bridge/view results;
- primitive data: a module `ℒ : ModX`, and when needed an explicit tensor trivialization
  `e : ℒ ⊗ₘ 𝒩 ≅ 𝒪X`;
- derived API: the existence of a tensor inverse, the local direct-summand consequence, and the
  comparison of any tensor inverse with the source-facing internal Hom
  `\mathcal{H}\!\mathit{om}_{\mathcal O_X}(ℒ, \mathcal O_X)`.

Source/core/bridge triage:
- `source-facing`: the textbook one-sided tensor-trivialization and internal-Hom comparison on a
  ringed space;
- `core/canonical`: `IsInvertible` and the ringed-site theorems listed above;
- `bridge/view`: the ringed-space specialization of the Chapter 18 invertibility theorems.
-/

/- Lemma 17.25.2: for a ringed space, the tensor-inverse criterion for invertibility is exactly
the Chapter 18 owner theorem
`SheafOfModules.RingedSite.isInvertible_iff_exists_tensor_inverse`, specialized to the site of
opens of `X`. -/
recall SheafOfModules.RingedSite.isInvertible_iff_exists_tensor_inverse

-- Proof sketch: combine the canonical owner bridge from Definition `17.25.1` with the main
-- tensor-inverse criterion above.
/-- Companion form of Lemma 17.25.2: tensoring with `ℒ` is an auto-equivalence exactly when `ℒ`
admits a tensor inverse. -/
theorem tensorLeft_isEquivalence_iff_exists_tensor_inverse
    (ℒ : ModX) :
    (tensorLeft ℒ).IsEquivalence ↔
      ∃ 𝒩 : ModX, Nonempty ((ℒ ⊗ₘ 𝒩) ≅ 𝒪X) := by
  exact
    (AlgebraicGeometry.RingedSpace.isInvertible_iff_tensorLeft_isEquivalence ℒ).symm.trans
      (SheafOfModules.RingedSite.isInvertible_iff_exists_tensor_inverse ℒ)

-- Proof sketch: choose a tensor inverse `𝒩`, use the main equivalence to obtain that `ℒ` is
-- invertible, and then apply the local duality argument of Lemma `17.18.2` to deduce that `ℒ` is
-- locally a retract of a finite free module sheaf.
/-- If `ℒ` admits a tensor inverse, then locally `ℒ` is a direct summand of a finite free
`\mathcal O_X`-module. -/
theorem exists_tensor_inverse_locallyDirectSummandOfFiniteFree
    (ℒ : ModX)
    (hℒ : ∃ 𝒩 : ModX, Nonempty ((ℒ ⊗ₘ 𝒩) ≅ 𝒪X)) :
    ℒ.IsLocallyDirectSummandOfFiniteFree := by
  sorry

section InternalHom

variable [MonoidalClosed (RingedSpace.Modules X)]

-- Proof sketch: specialize the Chapter 18 comparison
-- `nonempty_iso_ringedSiteModuleDual_of_tensor_inverse` to `ModX` using the given explicit
-- trivialization `e`, then compose with the canonical tensor-unit identification
-- `(ihom ℒ).mapIso unitIsoTensorUnit.symm : ringedSiteModuleDual ℒ ≅ (ihom ℒ).obj 𝒪X`.
/-- Lemma 17.25.2 (internal-Hom clause): any tensor inverse `𝒩` of `ℒ` is isomorphic to
`\mathcal{H}\!\mathit{om}_{\mathcal O_X}(ℒ, \mathcal O_X)`. -/
theorem tensor_inverse_iso_internalHom_unit
    (ℒ 𝒩 : ModX)
    (e : (ℒ ⊗ₘ 𝒩) ≅ 𝒪X) :
    Nonempty (𝒩 ≅ (ihom ℒ).obj 𝒪X) := by
  sorry

end InternalHom

end SheafOfModules

/-! ### Lemma_17_25_3 (from Chap17) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open SheafOfModules.RingedSite
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X
local notation "ModY" => RingedSpace.Modules Y
local notation "IsInvertibleX" =>
  @SheafOfModules.RingedSite.IsInvertible _ _ (Opens.grothendieckTopology X) X.sheaf _ _
local notation "IsInvertibleY" =>
  @SheafOfModules.RingedSite.IsInvertible _ _ (Opens.grothendieckTopology Y) Y.sheaf _ _

/- Domain-style sampling for Lemma 17.25.3:
- primary domain: invertible `\mathcal O_X`-modules under pullback along a morphism of ringed
  spaces;
- inspected owner declarations:
  `SheafOfModules.RingedSite.IsInvertible`,
  `AlgebraicGeometry.RingedSpace.Hom.pullback`,
  `SheafOfModules.RingedSite.pullback_isInvertible`,
  `SheafOfModules.RingedSite.isInvertible_iff_exists_tensor_inverse`;
- best owner abstraction: the canonical owner is `SheafOfModules.RingedSite.IsInvertible`,
  specialized to `RingedSpace.Modules`; the source-facing pullback statement is therefore a
  ringed-space specialization of the Chapter 18 ringed-site theorem, not a separate existential
  tensor-inverse wrapper;
- primitive data: a morphism of ringed spaces `f : X ⟶ Y` and a module `ℒ : Y.Modules`;
- derived API: the theorem and global instance asserting that the pullback
  `(RingedSpace.Hom.pullback f).obj ℒ` is invertible whenever `ℒ` is.

Source/core/bridge triage:
- `source-facing`: invertibility of the pulled-back module on a ringed space;
- `core/canonical`: `SheafOfModules.RingedSite.IsInvertible` and the pullback owner
  `RingedSpace.Hom.pullback`;
- `bridge/view`: the specialization of
  `SheafOfModules.RingedSite.pullback_isInvertible` from ringed sites to ringed spaces.
-/

variable [MonoidalCategory X.Modules] [MonoidalCategory Y.Modules]

-- Proof sketch: this is the Chapter 18 pullback-preserves-invertibility theorem specialized from
-- ringed sites to the opens site of a ringed space.
/-- Lemma 17.25.3: for a morphism of ringed spaces `f : (X, \mathcal O_X) → (Y, \mathcal O_Y)`,
the pullback of an invertible `\mathcal O_Y`-module is invertible. -/
theorem pullback_isInvertible
    (f : X ⟶ Y)
    (ℒ : ModY)
    [IsInvertibleY ℒ] :
    IsInvertibleX ((f^*).obj ℒ) := by
  simpa using
    (SheafOfModules.RingedSite.pullback_isInvertible
      (Opens.map f.hom.base)
      (RingedSpace.Hom.toRingCatSheafHom f)
      ℒ)

instance instIsInvertiblePullback
    (f : X ⟶ Y)
    (ℒ : ModY)
    [IsInvertibleY ℒ] :
    IsInvertibleX ((f^*).obj ℒ) :=
  pullback_isInvertible f ℒ

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_17_25_4 (from Chap17) -/
open CategoryTheory Opposite
open AlgebraicGeometry
open SheafOfModules.RingedSite
open TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}

/- Domain-style sampling for Lemma 17.25.4:
- primary domain: invertible `\mathcal O_X`-modules and finite locally free rank-one modules on a
  ringed space, viewed as the opens-site specialization of the Chapter 18 ringed-site theory;
- inspected owner declarations:
  `CategoryTheory.HasLocalUnitDichotomy`,
  `SheafOfModules.RingedSite.IsInvertible`,
  `SheafOfModules.IsFiniteLocallyFreeOfRank`,
  `SheafOfModules.RingedSite.isInvertible_of_isFiniteLocallyFreeOfRank_one`,
  `RingedSpace.isUnit_res_basicOpen`;
- best owner abstraction: the public statements should stay at the canonical owners
  `SheafOfModules.RingedSite.IsInvertible`,
  `SheafOfModules.IsFiniteLocallyFreeOfRank`, and the Chapter 18 owner theorem
  `SheafOfModules.RingedSite.isInvertible_of_isFiniteLocallyFreeOfRank_one`; the only genuinely
  local bridge in this file is that stalk-locality on a ringed space implies the opens-site
  local-unit dichotomy;
- primitive data: a module sheaf `ℒ : RingedSpace.Modules X`, plus in clause `(2)` the stalkwise
  local-ring hypothesis;
- derived API: the Chapter 18 rank-one invertibility owner specialized by direct recall, and the
  converse rank-one local freeness statement obtained by feeding the local-unit-dichotomy bridge
  into the Chapter 18 owner theorem.

Source/core/bridge triage:
- `source-facing`: the two clauses of Stacks Lemma 17.25.4 on a ringed space;
- `core/canonical`: `SheafOfModules.RingedSite.IsInvertible`,
  `SheafOfModules.IsFiniteLocallyFreeOfRank`, `CategoryTheory.HasLocalUnitDichotomy`, and the
  Chapter 18 owner theorem
  `SheafOfModules.RingedSite.isInvertible_of_isFiniteLocallyFreeOfRank_one`;
- `bridge/view`: the opens-site local-unit-dichotomy theorem derived from the stalk-local-ring
  hypothesis, then used to specialize the Chapter 18 converse theorem. -/

theorem hasLocalUnitDichotomy_of_stalk_isLocalRing
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    HasLocalUnitDichotomy (Opens.grothendieckTopology X) X.sheaf := by
  refine ⟨?_⟩
  intro U f
  let f' : X.presheaf.obj (op U) := f
  let Y : Bool → Opens X := fun
    | false => X.basicOpen f'
    | true => X.basicOpen (1 - f')
  let π : (b : Bool) → Y b ⟶ U := fun
    | false => homOfLE (X.basicOpen_le f')
    | true => homOfLE (X.basicOpen_le (1 - f'))
  let S : (Opens.grothendieckTopology X).Cover U := ⟨Sieve.ofArrows Y π, by
    intro x hxU
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (X.presheaf.germ U x hxU f') with h | h
    · refine ⟨Y false, π false, Sieve.ofArrows_mk Y π false, ?_⟩
      exact (X.mem_basicOpen f' x hxU).2 h
    · refine ⟨Y true, π true, Sieve.ofArrows_mk Y π true, ?_⟩
      exact (X.mem_basicOpen (1 - f') x hxU).2 (by simpa using h)⟩
  refine ⟨S, ?_⟩
  intro I
  change
    IsUnit ((X.presheaf.map I.f.op).hom f') ∨
      IsUnit (1 - (X.presheaf.map I.f.op).hom f')
  rcases (Sieve.mem_ofArrows_iff Y π I.f).1 I.hf with ⟨b, a, ha⟩
  cases b with
  | false =>
      left
      simpa [π, ha] using
        RingHom.isUnit_map ((X.presheaf.map a.op).hom) (X.isUnit_res_basicOpen f')
  | true =>
      right
      have hunit :
          IsUnit ((X.presheaf.map I.f.op).hom (1 - f')) := by
        simpa [π, ha] using
          RingHom.isUnit_map ((X.presheaf.map a.op).hom) (X.isUnit_res_basicOpen (1 - f'))
      simpa [map_sub] using hunit

variable [MonoidalCategory (RingedSpace.Modules X)]

/- Lemma 17.25.4 (1): on a ringed space, rank-one finite locally free modules are invertible by
direct specialization of the Chapter 18 owner theorem on ringed sites. -/
recall SheafOfModules.RingedSite.isInvertible_of_isFiniteLocallyFreeOfRank_one

-- Proof sketch: invertibility gives that each stalk `ℒ_x` is an invertible module over the stalk
-- ring `𝒪_{X, x}`. Over a local ring, every invertible module is free of rank `1`; then Lemma
-- `17.11.7` upgrades the stalkwise free rank-one statement to a neighbourhood trivialization,
-- yielding finite local freeness of rank `1`.
/-- Lemma 17.25.4 (2): if every stalk `\mathcal O_{X, x}` is a local ring, then every invertible
`\mathcal O_X`-module is locally free of rank `1`. -/
theorem isFiniteLocallyFreeOfRank_one_of_isInvertible_of_stalk_isLocalRing
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x))
    (ℒ : (RingedSpace.Modules X)) [IsInvertible ℒ] :
    SheafOfModules.IsFiniteLocallyFreeOfRank 1 ℒ := by
  let _ : HasLocalUnitDichotomy (Opens.grothendieckTopology X) X.sheaf :=
    hasLocalUnitDichotomy_of_stalk_isLocalRing hlocal
  sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_17_25_5 (from Chap17) -/
open AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 17.25.5:
- primary domain: invertible `\mathcal O_X`-modules and their duality in the symmetric monoidal
  closed category `RingedSpace.Modules X`;
- inspected owner declarations:
  `SheafOfModules.RingedSite.IsInvertible`,
  `SheafOfModules.RingedSite.isInvertible_tensor_of_isInvertible`,
  `SheafOfModules.RingedSite.isInvertible_internalHom_unit_of_isInvertible`,
  `SheafOfModules.RingedSite.isIso_internalHom_unit_evaluation_of_isInvertible`;
- best owner abstraction: the Chapter 18 ringed-site theorems above, specialized to the opens site
  of a ringed space;
- primitive data: invertible modules `ℒ`, `𝒩 : X.Modules`;
- derived API: invertibility of `ℒ ⊗ 𝒩`, invertibility of the internal-Hom dual of `ℒ`, and the
  evaluation-isomorphism statement at the unit object.

Source/core/bridge triage:
- `source-facing`: the three clauses of Stacks Lemma 17.25.5 for ringed spaces;
- `core/canonical`: the Chapter 18 ringed-site owner theorems;
- `bridge/view`: the opens-site specialization from a ringed site to a ringed space.

This file is therefore a canonical-recall item: the ringed-space statements add no new
mathematics beyond the already-owned ringed-site theorems, so the duplicate local theorem shells
should be deleted rather than preserved under parallel names.
-/

/- Lemma 17.25.5 (1): on a ringed space, the tensor product of two invertible
`\mathcal O_X`-modules is invertible. This is the opens-site specialization of the Chapter 18
owner theorem. -/
recall SheafOfModules.RingedSite.isInvertible_tensor_of_isInvertible

/- Lemma 17.25.5 (2): on a ringed space, the internal-Hom dual
`\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal L, \mathcal O_X)` of an invertible
`\mathcal O_X`-module is invertible. This is the same opens-site specialization. -/
recall SheafOfModules.RingedSite.isInvertible_internalHom_unit_of_isInvertible

/- Lemma 17.25.5 (3): on a ringed space, the evaluation morphism
`\mathcal L \otimes_{\mathcal O_X} \mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal L,
\mathcal O_X) \to \mathcal O_X` is an isomorphism for invertible `\mathcal O_X`-modules. This is
again the opens-site specialization of the Chapter 18 owner theorem. -/
recall SheafOfModules.RingedSite.isIso_internalHom_unit_evaluation_of_isInvertible

end AlgebraicGeometry.RingedSpace

/-! ### Definition_17_25_6 (from Chap17) -/
open CategoryTheory
open AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open SheafOfModules.RingedSite

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}

local notation "ModX" => SheafOfModules (RingedSpace.ringCatSheaf X)
local notation "𝒪X" => SheafOfModules.unit (RingedSpace.ringCatSheaf X)
local notation:70 A " ⊗ₘ " B => (tensorObj A B : ModX)

/- Domain-style sampling for Definition 17.25.6:
- primary domain: tensor powers of an invertible sheaf on a ringed space, viewed both through the
  tensor autoequivalence `tensorLeft ℒ` and through the chapter's recursive `ℤ`-indexed model;
- inspected owner declarations:
  `tensorLeft`,
  `Functor.asEquivalence`,
  `CategoryTheory.Equivalence.pow`,
  `SheafOfModules.unitToTensorUnit`,
  `AlgebraicGeometry.ringedSpaceRingCatSheaf`,
  `AlgebraicGeometry.RingedSpace.tensorPowerSheaf`,
  `AlgebraicGeometry.RingedSpace.tensorPowerSheaf_succ`,
  `SheafOfModules.RingedSite.isLocallyDirectSummandOfFiniteFree_of_isInvertible`,
  `SheafOfModules.RingedSite.ringedSiteModuleDual_exactPairing`,
  `ringedSiteModuleDual`,
  `SheafOfModules.unit ((RingedSpace.ringCatSheaf X))`;
- best owner abstraction: the source-facing object is the image of the structure sheaf under the
  `n`th power of the tensor autoequivalence `(tensorLeft ℒ).asEquivalence`; the recursive
  `ℤ`-indexed tensor-power owner is the concrete chapter model used to compute with that source
  object, while the tensor-power multiplication maps are derived companion isomorphisms;
- primitive data: an invertible sheaf `ℒ : ModX`;
- derived API: the invertible-sheaf tensor-power owner `tensorPowerSheafInt ℒ n`, its textbook
  notation, the companion comparison isomorphism with the tensor autoequivalence, the branch
  recursion lemmas, and the canonical multiplication morphisms.

Layer triage:
- `source-facing`: the invertible-sheaf tensor-power family `tensorPowerSheafInt ℒ n`, with
  companion comparison to the tensor autoequivalence power
  `((tensorLeft ℒ).asEquivalence ^ n).functor.obj \mathcal O_X`;
- `core/canonical`: `tensorLeft ℒ`, `Functor.asEquivalence`, the recursive positive owner
  `tensorPowerSheaf`, the canonical dual owner `ringedSiteModuleDual ℒ`, and the exact-pairing
  bridge for `ringedSiteModuleDual ℒ`;
- `bridge/view`: the comparison isomorphism from the recursive model to the tensor autoequivalence
  power, and the additive tensor-power isomorphisms.
 -/

/-- Definition 17.25.6: for an invertible sheaf `\mathcal L`, the integral tensor powers
`\mathcal L^{\otimes n}` are represented by the chapter's recursive `\mathbf Z`-indexed family,
using the usual nonnegative tensor powers and the canonical dual
`\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal L, \mathcal O_X)` in negative degrees. -/
noncomputable def tensorPowerSheafInt [MonoidalCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertible ℒ] : ℤ → ModX
  | .ofNat n => tensorPowerSheaf ℒ n
  | .negSucc n => tensorPowerSheaf (ringedSiteModuleDual ℒ) (n + 1)

/-- Textbook notation for the integral tensor powers `\mathcal L^{\otimes n}` of an invertible
sheaf. -/
infixr:80 " ^⊗ " => AlgebraicGeometry.RingedSpace.tensorPowerSheafInt

private noncomputable instance tensorLeftIsEquivalenceOfIsInvertible
    [MonoidalCategory ModX] (ℒ : ModX) [IsInvertible ℒ] :
    (tensorLeft ℒ).IsEquivalence :=
  (CategoryTheory.tensorLeft_isEquivalence_iff_tensorRight_isEquivalence ℒ).2 inferInstance

private theorem tensorLeftPowUnitNatSuccEq
    [MonoidalCategory ModX] [MonoidalClosed ModX] (ℒ : ModX) [IsInvertible ℒ] (n : ℕ) :
    (((tensorLeft ℒ).asEquivalence ^ ((n + 2 : ℕ) : ℤ)).functor.obj 𝒪X) =
      ℒ ⊗ₘ (((tensorLeft ℒ).asEquivalence ^ ((n + 1 : ℕ) : ℤ)).functor.obj 𝒪X) := by
  sorry

private theorem tensorLeftPowUnitOneEq
    [MonoidalCategory ModX] [MonoidalClosed ModX] (ℒ : ModX) [IsInvertible ℒ] :
    (((tensorLeft ℒ).asEquivalence ^ (1 : ℤ)).functor.obj 𝒪X) = ℒ ⊗ₘ 𝒪X := by
  sorry

private theorem tensorLeftPowUnitNegSuccEq
    [MonoidalCategory ModX] [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertible ℒ] (n : ℕ) :
    (((tensorLeft ℒ).asEquivalence ^ Int.negSucc (n + 1)).functor.obj 𝒪X) =
      ((tensorLeft ℒ).asEquivalence.inverse.obj
        (((tensorLeft ℒ).asEquivalence ^ Int.negSucc n).functor.obj 𝒪X)) := by
  sorry

private theorem tensorLeftPowUnitNegOneEq
    [MonoidalCategory ModX] [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertible ℒ] :
    (((tensorLeft ℒ).asEquivalence ^ Int.negSucc 0).functor.obj 𝒪X) =
      ((tensorLeft ℒ).asEquivalence.inverse.obj 𝒪X) := by
  sorry

private noncomputable def tensorPowerSheafNatIsoTensorLeftPowUnit
    [MonoidalCategory ModX] [MonoidalClosed ModX] (ℒ : ModX) [IsInvertible ℒ] :
    (n : ℕ) → tensorPowerSheaf ℒ n ≅ (((tensorLeft ℒ).asEquivalence ^ (n : ℤ)).functor.obj 𝒪X)
  | 0 => Iso.refl 𝒪X
  | 1 => by
      calc
        tensorPowerSheaf ℒ 1 ≅ moduleTensor ℒ (tensorPowerSheaf ℒ 0) :=
          eqToIso (by simpa using tensorPowerSheaf_succ ℒ 0)
        _ ≅ ℒ ⊗ₘ tensorPowerSheaf ℒ 0 :=
          moduleTensorIsoTensorObj ℒ (tensorPowerSheaf ℒ 0)
        _ ≅ ℒ ⊗ₘ 𝒪X :=
          eqToIso rfl
        _ ≅ (((tensorLeft ℒ).asEquivalence ^ (1 : ℤ)).functor.obj 𝒪X) :=
          (eqToIso (tensorLeftPowUnitOneEq ℒ)).symm
  | n + 2 => by
      calc
        tensorPowerSheaf ℒ (n + 2) ≅ moduleTensor ℒ (tensorPowerSheaf ℒ (n + 1)) :=
          eqToIso (by simpa using tensorPowerSheaf_succ ℒ (n + 1))
        _ ≅ ℒ ⊗ₘ tensorPowerSheaf ℒ (n + 1) :=
          moduleTensorIsoTensorObj ℒ (tensorPowerSheaf ℒ (n + 1))
        _ ≅ ℒ ⊗ₘ (((tensorLeft ℒ).asEquivalence ^ ((n + 1 : ℕ) : ℤ)).functor.obj 𝒪X) :=
          Iso.refl ℒ ⊗ᵢ tensorPowerSheafNatIsoTensorLeftPowUnit ℒ (n + 1)
        _ ≅ (((tensorLeft ℒ).asEquivalence ^ ((n + 2 : ℕ) : ℤ)).functor.obj 𝒪X) :=
          (eqToIso (tensorLeftPowUnitNatSuccEq ℒ n)).symm

private noncomputable def tensorPowerSheafIntEvaluation
    [MonoidalCategory ModX] [SymmetricCategory ModX] [MonoidalClosed ModX] (ℒ : ModX) :
    (ℒ ⊗ₘ ringedSiteModuleDual ℒ) ⟶ 𝒪X :=
  show (ℒ ⊗ₘ ringedSiteModuleDual ℒ) ⟶ 𝒪X from
    (ℒ ◁ (ihom ℒ).map (asIso SheafOfModules.unitToTensorUnit).inv) ≫
      (ihom.ev ℒ).app 𝒪X

private theorem isIso_tensorPowerSheafIntEvaluation
    [MonoidalCategory ModX] [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertible ℒ] :
    IsIso (tensorPowerSheafIntEvaluation ℒ) := by
  let f :
      (ℒ ⊗ₘ ringedSiteModuleDual ℒ) ⟶ (ℒ ⊗ₘ (ihom ℒ).obj 𝒪X) :=
    ℒ ◁ (ihom ℒ).map (asIso SheafOfModules.unitToTensorUnit).inv
  let g : (ℒ ⊗ₘ (ihom ℒ).obj 𝒪X) ⟶ 𝒪X :=
    (ihom.ev ℒ).app 𝒪X
  have hf : IsIso f := by
    dsimp [f]
    infer_instance
  have hg : IsIso g := by
    simpa [g] using
      (SheafOfModules.RingedSite.isIso_internalHom_unit_evaluation_of_isInvertible ℒ)
  have hcomp : IsIso (f ≫ g) := by
    infer_instance
  simpa [tensorPowerSheafIntEvaluation, f, g] using hcomp

private noncomputable def tensorPowerSheafIntEvaluationIso
    [MonoidalCategory ModX] [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertible ℒ] :
    (ℒ ⊗ₘ ringedSiteModuleDual ℒ) ≅ 𝒪X := by
  letI : IsIso (tensorPowerSheafIntEvaluation ℒ) :=
    isIso_tensorPowerSheafIntEvaluation ℒ
  exact asIso (tensorPowerSheafIntEvaluation ℒ)

private noncomputable def tensorLeftInverseIsoRingedSiteModuleDual
    [MonoidalCategory ModX] [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertible ℒ] :
    ((tensorLeft ℒ).asEquivalence).inverse ≅ tensorLeft (ringedSiteModuleDual ℒ) := by
  let E₁ : ModX ≌ ModX := (tensorLeft ℒ).asEquivalence
  let e₁ : (ℒ ⊗ₘ ringedSiteModuleDual ℒ) ≅ 𝟙_ ModX :=
    tensorPowerSheafIntEvaluationIso ℒ ≪≫ asIso SheafOfModules.unitToTensorUnit
  let e₂ : (ringedSiteModuleDual ℒ ⊗ₘ ℒ) ≅ 𝟙_ ModX :=
    β_ (ringedSiteModuleDual ℒ) ℒ ≪≫ e₁
  let η : 𝟭 ModX ≅ tensorLeft ℒ ⋙ tensorLeft (ringedSiteModuleDual ℒ) :=
    (leftUnitorNatIso ModX).symm ≪≫
      (tensoringLeft ModX).mapIso e₂.symm ≪≫
      tensorLeftTensor (ringedSiteModuleDual ℒ) ℒ
  let ε : tensorLeft (ringedSiteModuleDual ℒ) ⋙ tensorLeft ℒ ≅ 𝟭 ModX :=
    (tensorLeftTensor ℒ (ringedSiteModuleDual ℒ)).symm ≪≫
      (tensoringLeft ModX).mapIso e₁ ≪≫
      leftUnitorNatIso ModX
  letI : (tensorLeft ℒ).IsEquivalence :=
    Functor.IsEquivalence.mk'
      (tensorLeft (ringedSiteModuleDual ℒ))
      η
      ε
  let E₂ : ModX ≌ ModX := (tensorLeft ℒ).asEquivalence
  have hInv : E₁.inverse ≅ E₂.inverse :=
    Iso.isoInverseOfIsoFunctor (Iso.refl (tensorLeft ℒ))
  have hChosen : tensorLeft (ringedSiteModuleDual ℒ) ≅ E₂.inverse :=
    (Iso.isoCompInverse ε) ≪≫ Functor.leftUnitor E₂.inverse
  exact hInv ≪≫ hChosen.symm

private noncomputable def tensorPowerSheafNegSuccIsoTensorLeftPowUnit
    [MonoidalCategory ModX] [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertible ℒ] :
    (n : ℕ) →
      tensorPowerSheaf (ringedSiteModuleDual ℒ) (n + 1) ≅
        (((tensorLeft ℒ).asEquivalence ^ Int.negSucc n).functor.obj 𝒪X)
  | 0 => by
      calc
        tensorPowerSheaf (ringedSiteModuleDual ℒ) 1 ≅
            moduleTensor (ringedSiteModuleDual ℒ)
              (tensorPowerSheaf (ringedSiteModuleDual ℒ) 0) :=
          eqToIso (by simpa using tensorPowerSheaf_succ (ringedSiteModuleDual ℒ) 0)
        _ ≅ ringedSiteModuleDual ℒ ⊗ₘ tensorPowerSheaf (ringedSiteModuleDual ℒ) 0 :=
          moduleTensorIsoTensorObj (ringedSiteModuleDual ℒ)
            (tensorPowerSheaf (ringedSiteModuleDual ℒ) 0)
        _ ≅ (tensorLeft (ringedSiteModuleDual ℒ)).obj 𝒪X :=
          eqToIso rfl
        _ ≅ ((tensorLeft ℒ).asEquivalence.inverse.obj 𝒪X) :=
          ((tensorLeftInverseIsoRingedSiteModuleDual ℒ).app 𝒪X).symm
        _ ≅ (((tensorLeft ℒ).asEquivalence ^ Int.negSucc 0).functor.obj 𝒪X) :=
          (eqToIso (tensorLeftPowUnitNegOneEq ℒ)).symm
  | n + 1 => by
      calc
        tensorPowerSheaf (ringedSiteModuleDual ℒ) (n + 2) ≅
            moduleTensor (ringedSiteModuleDual ℒ)
              (tensorPowerSheaf (ringedSiteModuleDual ℒ) (n + 1)) :=
          eqToIso (by simpa using tensorPowerSheaf_succ (ringedSiteModuleDual ℒ) (n + 1))
        _ ≅ ringedSiteModuleDual ℒ ⊗ₘ tensorPowerSheaf (ringedSiteModuleDual ℒ) (n + 1) :=
          moduleTensorIsoTensorObj (ringedSiteModuleDual ℒ)
            (tensorPowerSheaf (ringedSiteModuleDual ℒ) (n + 1))
        _ ≅ ringedSiteModuleDual ℒ ⊗ₘ
            (((tensorLeft ℒ).asEquivalence ^ Int.negSucc n).functor.obj 𝒪X) :=
          Iso.refl (ringedSiteModuleDual ℒ) ⊗ᵢ
            tensorPowerSheafNegSuccIsoTensorLeftPowUnit ℒ n
        _ ≅ (tensorLeft (ringedSiteModuleDual ℒ)).obj
            (((tensorLeft ℒ).asEquivalence ^ Int.negSucc n).functor.obj 𝒪X) :=
          eqToIso rfl
        _ ≅ ((tensorLeft ℒ).asEquivalence.inverse.obj
            (((tensorLeft ℒ).asEquivalence ^ Int.negSucc n).functor.obj 𝒪X)) :=
          ((tensorLeftInverseIsoRingedSiteModuleDual ℒ).app
            (((tensorLeft ℒ).asEquivalence ^ Int.negSucc n).functor.obj 𝒪X)).symm
        _ ≅ (((tensorLeft ℒ).asEquivalence ^ Int.negSucc (n + 1)).functor.obj 𝒪X) :=
          (eqToIso (tensorLeftPowUnitNegSuccEq ℒ n)).symm

/-- Definition 17.25.6: for an invertible sheaf `\mathcal L`, the tensor power
`\mathcal L^{\otimes n}` is the image of the structure sheaf under the `n`th power of the tensor
autoequivalence `tensorLeft ℒ`. The recursive owner `ℒ ^⊗ n` is the chapter's concrete model for
this source-defined object. -/
noncomputable def tensorPowerSheafIntIsoTensorLeftPowUnit
    [MonoidalCategory ModX] [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertible ℒ] (n : ℤ) :
    ℒ ^⊗ n ≅ (((tensorLeft ℒ).asEquivalence ^ n).functor.obj 𝒪X) := by
  cases n with
  | ofNat n =>
      exact tensorPowerSheafNatIsoTensorLeftPowUnit ℒ n
  | negSucc n =>
      exact tensorPowerSheafNegSuccIsoTensorLeftPowUnit ℒ n

/-- The first positive tensor power is `\mathcal L` tensored with the preceding nonnegative power.
-/
theorem tensorPowerSheafInt_natSucc
    [MonoidalCategory ModX] [MonoidalClosed ModX] (ℒ : ModX) [IsInvertible ℒ] (n : ℕ) :
    ℒ ^⊗ (((n + 1 : ℕ) : ℤ)) = moduleTensor ℒ (ℒ ^⊗ (n : ℤ)) :=
  tensorPowerSheaf_succ ℒ n

/-- The `(-1)`st tensor power is the first tensor power of the canonical internal-Hom inverse
sheaf. -/
theorem tensorPowerSheafInt_negOne
    [MonoidalCategory ModX] [MonoidalClosed ModX] (ℒ : ModX) [IsInvertible ℒ] :
    ℒ ^⊗ (-1 : ℤ) = moduleTensor (ringedSiteModuleDual ℒ) 𝒪X := by
  simpa using tensorPowerSheaf_succ (ringedSiteModuleDual ℒ) 0

/-- Adding a nonnegative exponent to a nonnegative exponent stays on the nonnegative branch of the
integral tensor-power owner. -/
theorem tensorPowerSheafInt_natAdd_eq
    [MonoidalCategory ModX] [MonoidalClosed ModX] (ℒ : ModX) [IsInvertible ℒ] (m n : ℕ) :
    ℒ ^⊗ ((m : ℤ) + n) = ℒ ^⊗ (((m + n : ℕ) : ℤ)) := by
  exact congrArg (fun k : ℤ ↦ ℒ ^⊗ k) (by exact_mod_cast rfl)

/-- Beyond `\mathcal L^{-1}`, each further negative tensor power is obtained by tensoring once
more with the canonical internal-Hom inverse sheaf. -/
theorem tensorPowerSheafInt_negSucc_succ
    [MonoidalCategory ModX] [MonoidalClosed ModX] (ℒ : ModX) [IsInvertible ℒ] (n : ℕ) :
    ℒ ^⊗ (Int.negSucc (n + 1)) =
      moduleTensor (ringedSiteModuleDual ℒ) (ℒ ^⊗ Int.negSucc n) := by
  simpa using tensorPowerSheaf_succ (ringedSiteModuleDual ℒ) (n + 1)

/-- The zeroth tensor power `\mathcal L^{\otimes 0}` is the tensor unit, that is, the structure
sheaf viewed through the ambient monoidal-category owner. -/
theorem tensorPowerSheafInt_zero
    [MonoidalCategory ModX] [MonoidalClosed ModX] (ℒ : ModX) [IsInvertible ℒ] :
    ℒ ^⊗ (0 : ℤ) = 𝒪X := rfl

/-- Adding `1` to `-1` lands at the zeroth tensor power. -/
theorem tensorPowerSheafInt_negSucc_add_one_zero
    [MonoidalCategory ModX] [MonoidalClosed ModX] (ℒ : ModX) [IsInvertible ℒ] :
    ℒ ^⊗ (Int.negSucc 0 + 1) = 𝒪X := by
  have h : Int.negSucc 0 + 1 = (0 : ℤ) := by decide
  calc
    ℒ ^⊗ (Int.negSucc 0 + 1) = ℒ ^⊗ (0 : ℤ) := congrArg (fun k : ℤ ↦ ℒ ^⊗ k) h
    _ = 𝒪X := tensorPowerSheafInt_zero ℒ

/-- Adding `1` to a strictly smaller negative exponent shifts one step toward zero. -/
theorem tensorPowerSheafInt_negSucc_add_one_succ
    [MonoidalCategory ModX] [MonoidalClosed ModX] (ℒ : ModX) [IsInvertible ℒ] (n : ℕ) :
    ℒ ^⊗ (Int.negSucc (n + 1) + 1) = ℒ ^⊗ Int.negSucc n := by
  exact congrArg (fun k : ℤ ↦ ℒ ^⊗ k) (by omega)

private noncomputable def tensorPowerSheafIntUnitLeftIso
    [MonoidalCategory ModX] [MonoidalClosed ModX] (ℱ : ModX) :
    (𝒪X ⊗ₘ ℱ) ≅ ℱ :=
  (SheafOfModules.unitIsoTensorUnit ▷ᵢ ℱ) ≪≫ λ_ ℱ

private noncomputable def tensorPowerSheafIntNatSuccIso
    [MonoidalCategory ModX] [MonoidalClosed ModX] (ℒ : ModX) [IsInvertible ℒ] (n : ℕ) :
    ℒ ^⊗ (((n + 1 : ℕ) : ℤ)) ≅ ℒ ⊗ₘ (ℒ ^⊗ (n : ℤ)) :=
  eqToIso (tensorPowerSheafInt_natSucc ℒ n) ≪≫
    moduleTensorIsoTensorObj ℒ (ℒ ^⊗ (n : ℤ))

private noncomputable def tensorPowerSheafIntNegOneIso
    [MonoidalCategory ModX] [MonoidalClosed ModX] (ℒ : ModX) [IsInvertible ℒ] :
    ℒ ^⊗ (-1 : ℤ) ≅ ringedSiteModuleDual ℒ ⊗ₘ 𝒪X :=
  eqToIso (tensorPowerSheafInt_negOne ℒ) ≪≫
    moduleTensorIsoTensorObj (ringedSiteModuleDual ℒ) 𝒪X

private noncomputable def tensorPowerSheafIntNegSuccSuccIso
    [MonoidalCategory ModX] [MonoidalClosed ModX] (ℒ : ModX) [IsInvertible ℒ] (n : ℕ) :
    ℒ ^⊗ (Int.negSucc (n + 1)) ≅ ringedSiteModuleDual ℒ ⊗ₘ (ℒ ^⊗ Int.negSucc n) :=
  eqToIso (tensorPowerSheafInt_negSucc_succ ℒ n) ≪≫
    moduleTensorIsoTensorObj (ringedSiteModuleDual ℒ) (ℒ ^⊗ Int.negSucc n)

private noncomputable def tensorPowerSheafIntOneAddIsoAux
    [MonoidalCategory ModX] [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertible ℒ] :
    (n : ℤ) → (ℒ ⊗ₘ (ℒ ^⊗ n)) ≅ ℒ ^⊗ (n + 1)
  | .ofNat n =>
      (tensorPowerSheafIntNatSuccIso ℒ n).symm
  | .negSucc 0 =>
      (Iso.refl ℒ ⊗ᵢ tensorPowerSheafIntNegOneIso ℒ) ≪≫
        (α_ ℒ (ringedSiteModuleDual ℒ) 𝒪X).symm ≪≫
        (tensorPowerSheafIntEvaluationIso ℒ ▷ᵢ 𝒪X) ≪≫
        tensorPowerSheafIntUnitLeftIso 𝒪X ≪≫
        eqToIso (tensorPowerSheafInt_zero ℒ).symm
  | .negSucc (n + 1) =>
      (Iso.refl ℒ ⊗ᵢ tensorPowerSheafIntNegSuccSuccIso ℒ n) ≪≫
        (α_ ℒ (ringedSiteModuleDual ℒ) (ℒ ^⊗ Int.negSucc n)).symm ≪≫
        (tensorPowerSheafIntEvaluationIso ℒ ▷ᵢ (ℒ ^⊗ Int.negSucc n)) ≪≫
        tensorPowerSheafIntUnitLeftIso (ℒ ^⊗ Int.negSucc n) ≪≫
        eqToIso (tensorPowerSheafInt_negSucc_add_one_succ ℒ n).symm

private noncomputable def tensorPowerSheafIntNatAddIsoAux
    [MonoidalCategory ModX] [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertible ℒ] :
    (m : ℕ) → (n : ℤ) →
      ((ℒ ^⊗ (m : ℤ)) ⊗ₘ (ℒ ^⊗ n)) ≅ ℒ ^⊗ ((m : ℤ) + n)
  | 0, n =>
      eqToIso (tensorPowerSheafInt_zero ℒ) ▷ᵢ (ℒ ^⊗ n) ≪≫
        tensorPowerSheafIntUnitLeftIso (ℒ ^⊗ n) ≪≫
        eqToIso (congrArg (fun k : ℤ ↦ ℒ ^⊗ k) (by omega))
  | m + 1, n =>
      let h : (((m : ℤ) + n) + 1) = (((m + 1 : ℕ) : ℤ) + n) := by
        omega
      (tensorPowerSheafIntNatSuccIso ℒ m ▷ᵢ (ℒ ^⊗ n)) ≪≫
        α_ ℒ (ℒ ^⊗ (m : ℤ)) (ℒ ^⊗ n) ≪≫
        (Iso.refl ℒ ⊗ᵢ tensorPowerSheafIntNatAddIsoAux ℒ m n) ≪≫
        tensorPowerSheafIntOneAddIsoAux ℒ ((m : ℤ) + n) ≪≫
        eqToIso (congrArg (fun k : ℤ ↦ ℒ ^⊗ k) h)

/-- Tensoring once by `\mathcal L` shifts the integral tensor-power owner by one degree. For
negative degrees this uses the canonical evaluation isomorphism
`\mathcal L \otimes \mathcal L^{-1} \cong \mathcal O_X` of an invertible sheaf. -/
noncomputable def tensorPowerSheafIntOneAddIso
    [MonoidalCategory ModX] [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertible ℒ] (n : ℤ) :
    (ℒ ⊗ₘ (ℒ ^⊗ n)) ≅ ℒ ^⊗ (n + 1) :=
  tensorPowerSheafIntOneAddIsoAux ℒ n

/-- Tensoring `\mathcal L^{\otimes m}` with `\mathcal L^{\otimes n}` for `m,n \in \mathbf N`
canonically identifies with `\mathcal L^{\otimes (m+n)}`. -/
noncomputable def tensorPowerSheafIntNatAddIso
    [MonoidalCategory ModX] [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertible ℒ] (m n : ℕ) :
    ((ℒ ^⊗ (m : ℤ)) ⊗ₘ (ℒ ^⊗ (n : ℤ))) ≅
      ℒ ^⊗ (((m + n : ℕ) : ℤ)) :=
  tensorPowerSheafIntNatAddIsoAux ℒ m (n : ℤ) ≪≫
    eqToIso (tensorPowerSheafInt_natAdd_eq ℒ m n)

/-- Companion: tensoring two recursive-model powers
`\mathcal L^{\otimes m}` and `\mathcal L^{\otimes n}` canonically identifies with
`\mathcal L^{\otimes (m+n)}`. For negative exponents this is obtained by rewriting
`\mathcal L^{\otimes (-r)}` as a positive tensor power of the canonical dual and using the
evaluation isomorphism of an invertible sheaf. -/
noncomputable def tensorPowerSheafIntAddIso
    [MonoidalCategory ModX] [SymmetricCategory ModX] [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertible ℒ] (m n : ℤ) :
    ((ℒ ^⊗ m) ⊗ₘ (ℒ ^⊗ n)) ≅ ℒ ^⊗ (m + n) := by
  cases m with
  | ofNat m =>
      exact tensorPowerSheafIntNatAddIsoAux ℒ m n
  | negSucc a =>
      cases n with
      | ofNat n =>
          exact (β_ (ℒ ^⊗ Int.negSucc a) (ℒ ^⊗ (n : ℤ))) ≪≫
            tensorPowerSheafIntNatAddIsoAux ℒ n (Int.negSucc a) ≪≫
            eqToIso (congrArg (fun k : ℤ ↦ ℒ ^⊗ k) (Int.add_comm (n : ℤ) (Int.negSucc a)))
      | negSucc b =>
          exact (eqToIso rfl ⊗ᵢ eqToIso rfl) ≪≫
            tensorPowerSheafIntNatAddIso (ringedSiteModuleDual ℒ) (a + 1) (b + 1) ≪≫
            eqToIso (
              calc
                (ringedSiteModuleDual ℒ) ^⊗ ((((a + 1) + (b + 1) : ℕ) : ℤ)) =
                    (ringedSiteModuleDual ℒ) ^⊗ (((a + b + 2 : ℕ) : ℤ)) := by
                      exact congrArg (fun k : ℤ ↦ (ringedSiteModuleDual ℒ) ^⊗ k) (by omega)
                _ = ℒ ^⊗ Int.negSucc (a + b + 1) := rfl
                _ = ℒ ^⊗ (Int.negSucc a + Int.negSucc b) := by
                      exact congrArg (fun k : ℤ ↦ ℒ ^⊗ k) (by omega)
            )

end AlgebraicGeometry.RingedSpace

/-! ### Definition_17_25_7 (from Chap17) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open Opposite
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry DirectSum

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}

local notation "ModX" => RingedSpace.Modules X
local notation "ΓX" => X.presheaf.obj (op ⊤)
local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : ModX)
local notation:70 A " ⊗ₘ " B => (tensorObj A B : ModX)

local instance : VAdd ℕ ℤ where
  vadd n i := (n : ℤ) + i

/- Domain-style sampling for Definition 17.25.7:
- primary domain: graded global sections attached to a sheaf of `\mathcal O_X`-modules, together
  with the `\mathbb Z`-graded twisted version attached to an invertible sheaf;
- inspected owner declarations:
  `RingedSpace.Modules`,
  `tensorPowerSheaf`,
  `tensorPowerSheafInt`,
  `ringedSiteModuleDual`,
  `SheafOfModules.unitToTensorUnit`,
  `DirectSum.GCommRing`,
  `DirectSum.Gmodule`,
  `moduleTensor`;
- best owner abstraction: the source-facing owners are the direct sums
  `\Gamma_*(X, \mathcal L)` and `\Gamma_*(X, \mathcal L, \mathcal F)`, equipped with the canonical
  graded ring and graded module structures supplied by mathlib's direct-sum graded owners;
- primitive data: a sheaf `ℒ : ModX` for the ring owner, and an invertible sheaf `ℒ : ModX`
  together with `ℱ : ModX` for the twisted module owner;
- derived API: the top-open `ModuleCat ΓX` summands, the tensoring maps on homogeneous pieces, and
  the resulting external direct-sum ring/module owners, with the ring multiplication coming from
  the nonnegative tensor-power owner `tensorPowerSheaf` and the twisted action map coming from
  `tensorPowerSheafIntMul` in Definition 17.25.6.

Layer triage:
- `source-facing`: `\Gamma_*(X, \mathcal L)` and `\Gamma_*(X, \mathcal L, \mathcal F)`;
- `core/canonical`: the chapter owner `RingedSpace.Modules X`, the nonnegative tensor-power owner
  `T^[n] ℒ`, the integral tensor-power owner `ℒ ^⊗ n`, the twist owner `moduleTensor ℱ (ℒ ^⊗ n)`,
  the canonical tensor-unit comparison `unitToTensorUnit`, and the graded direct-sum owners
  `DirectSum.GCommRing` / `DirectSum.Gmodule`, with the negative branch using the canonical dual
  owner `ringedSiteModuleDual ℒ`;
- `bridge/view`: the degreewise identification theorems and the pure-degree multiplication/action
  maps, with the ring multiplication obtained by recursively tensoring the nonnegative tensor-power
  owner and the twisted module action obtained from associativity, symmetry, and whiskering of
  `tensorPowerSheafIntMul`.
-/

/-- The degree-`n` homogeneous piece of `\Gamma_*(X, \mathcal L)`. -/
abbrev gradedGlobalSectionsDegree
    (ℒ : ModX) (n : ℕ) : ModuleCat ΓX :=
  (T^[n] ℒ).val.obj (op ⊤)

/-- The degree-`n` homogeneous piece of `\Gamma_*(X, \mathcal L, \mathcal F)`. -/
abbrev gradedTwistedGlobalSectionsDegree
    [MonoidalCategory ModX]
    [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertible ℒ] (ℱ : ModX) (n : ℤ) :
    ModuleCat ΓX :=
  (moduleTensor ℱ (ℒ ^⊗ n)).val.obj (op ⊤)

/-- Definition 17.25.7 (1): `\Gamma_*(X, \mathcal L)` is the direct sum of the nonnegative
tensor-power global sections. -/
abbrev gradedGlobalSections
    (ℒ : ModX) : Type _ :=
  ⨁ n : ℕ, gradedGlobalSectionsDegree ℒ n

/-- Definition 17.25.7 (2): `\Gamma_*(X, \mathcal L, \mathcal F)` is the direct sum of the
integer-indexed twisted global sections. -/
abbrev gradedTwistedGlobalSections
    [MonoidalCategory ModX]
    [MonoidalClosed ModX]
    (ℒ : ModX) [IsInvertible ℒ] (ℱ : ModX) : Type _ :=
  ⨁ n : ℤ, gradedTwistedGlobalSectionsDegree ℒ ℱ n

/-- Textbook notation for the graded ring of global sections `\Gamma_*(X, \mathcal L)`. -/
scoped[AlgebraicGeometry] notation3:max "Γ_*(" ℒ ")" =>
  AlgebraicGeometry.RingedSpace.gradedGlobalSections ℒ

/-- Textbook notation for the graded module of twisted global sections
`\Gamma_*(X, \mathcal L, \mathcal F)`. -/
scoped[AlgebraicGeometry] notation3:max "Γ_*(" ℒ ", " ℱ ")" =>
  AlgebraicGeometry.RingedSpace.gradedTwistedGlobalSections ℒ ℱ

private noncomputable def tensorPowerSheafUnitLeftIso
    [MonoidalCategory ModX]
    [MonoidalClosed ModX]
    (ℱ : ModX) :
    (𝒪X ⊗ₘ ℱ) ≅ ℱ :=
  (SheafOfModules.unitIsoTensorUnit ▷ᵢ ℱ) ≪≫ λ_ ℱ

private noncomputable def tensorTopHom
    [MonoidalCategory ModX]
    [MonoidalClosed ModX]
    (ℱ 𝒢 : ModX) :
    (PresheafOfModules.Monoidal.tensorObj ℱ.val 𝒢.val).obj (op ⊤) ⟶
      (moduleTensor ℱ 𝒢).val.obj (op ⊤) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (show PresheafOfModules X.ringCatSheaf.obj from
      PresheafOfModules.Monoidal.tensorObj ℱ.val 𝒢.val)).app (op ⊤)

private noncomputable def tensorPowerSheafNatAddIso
    [MonoidalCategory ModX]
    [SymmetricCategory ModX]
    [MonoidalClosed ModX]
    (ℒ : ModX) :
    (m n : ℕ) →
      ((tensorPowerSheaf ℒ m) ⊗ₘ (tensorPowerSheaf ℒ n)) ≅ tensorPowerSheaf ℒ (m + n)
  | 0, n =>
      let zeroIso :
          ((tensorPowerSheaf ℒ 0) ⊗ₘ tensorPowerSheaf ℒ n) ≅
            (𝒪X ⊗ₘ tensorPowerSheaf ℒ n) :=
        eqToIso rfl ▷ᵢ tensorPowerSheaf ℒ n
      let unitIso :
          (𝒪X ⊗ₘ tensorPowerSheaf ℒ n) ≅ tensorPowerSheaf ℒ n :=
        tensorPowerSheafUnitLeftIso (tensorPowerSheaf ℒ n)
      let reindexIso :
          tensorPowerSheaf ℒ n ≅ tensorPowerSheaf ℒ (0 + n) :=
        eqToIso (congrArg (tensorPowerSheaf ℒ) (by simp))
      zeroIso ≪≫ unitIso ≪≫ reindexIso
  | m + 1, n =>
      let succIso :
          ((tensorPowerSheaf ℒ (m + 1)) ⊗ₘ tensorPowerSheaf ℒ n) ≅
            ((((ℒ ⊗ₘ tensorPowerSheaf ℒ m : ModX)) ⊗ₘ tensorPowerSheaf ℒ n) : ModX) :=
        moduleTensorIsoTensorObj ℒ (tensorPowerSheaf ℒ m) ▷ᵢ tensorPowerSheaf ℒ n
      let assocIso :
          ((((ℒ ⊗ₘ tensorPowerSheaf ℒ m : ModX)) ⊗ₘ tensorPowerSheaf ℒ n) : ModX) ≅
            (ℒ ⊗ₘ ((tensorPowerSheaf ℒ m) ⊗ₘ tensorPowerSheaf ℒ n) : ModX) :=
        α_ ℒ (tensorPowerSheaf ℒ m) (tensorPowerSheaf ℒ n)
      let mulIso :
          (ℒ ⊗ₘ ((tensorPowerSheaf ℒ m) ⊗ₘ tensorPowerSheaf ℒ n) : ModX) ≅
            (ℒ ⊗ₘ tensorPowerSheaf ℒ (m + n) : ModX) :=
        Iso.refl ℒ ⊗ᵢ tensorPowerSheafNatAddIso ℒ m n
      let targetIso :
          (ℒ ⊗ₘ tensorPowerSheaf ℒ (m + n) : ModX) ≅ tensorPowerSheaf ℒ ((m + n) + 1) :=
        (moduleTensorIsoTensorObj ℒ (tensorPowerSheaf ℒ (m + n))).symm
      let h : (m + n) + 1 = (m + 1) + n := by
        omega
      let reindexIso :
          tensorPowerSheaf ℒ ((m + n) + 1) ≅ tensorPowerSheaf ℒ ((m + 1) + n) :=
        eqToIso (congrArg (tensorPowerSheaf ℒ) h)
      succIso ≪≫ assocIso ≪≫ mulIso ≪≫ targetIso ≪≫ reindexIso

private noncomputable def tensorTopToTensorObjHom
    [MonoidalCategory ModX]
    [MonoidalClosed ModX]
    (ℱ 𝒢 : ModX) :
    (PresheafOfModules.Monoidal.tensorObj ℱ.val 𝒢.val).obj (op ⊤) ⟶
      ((ℱ ⊗ₘ 𝒢 : ModX).val.obj (op ⊤)) :=
  tensorTopHom ℱ 𝒢 ≫ (moduleTensorIsoTensorObj ℱ 𝒢).hom.val.app (op ⊤)

private noncomputable def gradedGlobalSectionsMul
    [MonoidalCategory ModX]
    [MonoidalClosed ModX]
    [SymmetricCategory ModX]
    (ℒ : ModX) (m n : ℕ)
    (x : gradedGlobalSectionsDegree ℒ m) (y : gradedGlobalSectionsDegree ℒ n) :
    gradedGlobalSectionsDegree ℒ (m + n) :=
  let mulApp :
      ((tensorObj (tensorPowerSheaf ℒ m) (tensorPowerSheaf ℒ n) : ModX).val.obj (op ⊤)) ⟶
        gradedGlobalSectionsDegree ℒ (m + n) :=
    show ((tensorObj (tensorPowerSheaf ℒ m) (tensorPowerSheaf ℒ n) : ModX).val.obj (op ⊤)) ⟶
        (tensorPowerSheaf ℒ (m + n)).val.obj (op ⊤) from
      (tensorPowerSheafNatAddIso ℒ m n).hom.val.app (op ⊤)
  let mulHom :
      (PresheafOfModules.Monoidal.tensorObj
        (tensorPowerSheaf ℒ m).val (tensorPowerSheaf ℒ n).val).obj (op ⊤) ⟶
        gradedGlobalSectionsDegree ℒ (m + n) :=
    tensorTopToTensorObjHom (tensorPowerSheaf ℒ m) (tensorPowerSheaf ℒ n) ≫ mulApp
  mulHom (x ⊗ₜ y)

private noncomputable def gradedTwistedGlobalSectionsSheafSmul
    [MonoidalCategory ModX]
    [MonoidalClosed ModX]
    [SymmetricCategory ModX]
    (ℒ : ModX) [IsInvertible ℒ] (ℱ : ModX) :
    (m : ℕ) → (n : ℤ) →
      ((ℒ ^⊗ (m : ℤ)) ⊗ₘ moduleTensor ℱ (ℒ ^⊗ n) : ModX) ⟶
        (moduleTensor ℱ (ℒ ^⊗ ((m : ℤ) + n)) : ModX)
  | m, n =>
      let shiftLeft :
          ((ℒ ^⊗ (m : ℤ)) ⊗ₘ moduleTensor ℱ (ℒ ^⊗ n) : ModX) ⟶
            ((ℒ ^⊗ (m : ℤ)) ⊗ₘ (ℱ ⊗ₘ (ℒ ^⊗ n)) : ModX) :=
        show ((ℒ ^⊗ (m : ℤ)) ⊗ₘ moduleTensor ℱ (ℒ ^⊗ n) : ModX) ⟶
            ((ℒ ^⊗ (m : ℤ)) ⊗ₘ (ℱ ⊗ₘ (ℒ ^⊗ n)) : ModX) from
          ((ℒ ^⊗ (m : ℤ)) ◁ (moduleTensorIsoTensorObj ℱ (ℒ ^⊗ n)).hom)
      let assocLeft :
          ((ℒ ^⊗ (m : ℤ)) ⊗ₘ (ℱ ⊗ₘ (ℒ ^⊗ n)) : ModX) ⟶
            (((ℒ ^⊗ (m : ℤ)) ⊗ₘ ℱ) ⊗ₘ (ℒ ^⊗ n) : ModX) :=
        show ((ℒ ^⊗ (m : ℤ)) ⊗ₘ (ℱ ⊗ₘ (ℒ ^⊗ n)) : ModX) ⟶
            (((ℒ ^⊗ (m : ℤ)) ⊗ₘ ℱ) ⊗ₘ (ℒ ^⊗ n) : ModX) from
          (α_ (ℒ ^⊗ (m : ℤ)) ℱ (ℒ ^⊗ n)).inv
      let braiding :
          (((ℒ ^⊗ (m : ℤ)) ⊗ₘ ℱ) ⊗ₘ (ℒ ^⊗ n) : ModX) ⟶
            ((ℱ ⊗ₘ (ℒ ^⊗ (m : ℤ))) ⊗ₘ (ℒ ^⊗ n) : ModX) :=
        show (((ℒ ^⊗ (m : ℤ)) ⊗ₘ ℱ) ⊗ₘ (ℒ ^⊗ n) : ModX) ⟶
            ((ℱ ⊗ₘ (ℒ ^⊗ (m : ℤ))) ⊗ₘ (ℒ ^⊗ n) : ModX) from
          ((β_ (ℒ ^⊗ (m : ℤ)) ℱ).hom ▷ (ℒ ^⊗ n))
      let assocRight :
          ((ℱ ⊗ₘ (ℒ ^⊗ (m : ℤ))) ⊗ₘ (ℒ ^⊗ n) : ModX) ⟶
            (ℱ ⊗ₘ ((ℒ ^⊗ (m : ℤ)) ⊗ₘ (ℒ ^⊗ n)) : ModX) :=
        show ((ℱ ⊗ₘ (ℒ ^⊗ (m : ℤ))) ⊗ₘ (ℒ ^⊗ n) : ModX) ⟶
            (ℱ ⊗ₘ ((ℒ ^⊗ (m : ℤ)) ⊗ₘ (ℒ ^⊗ n)) : ModX) from
          (α_ ℱ (ℒ ^⊗ (m : ℤ)) (ℒ ^⊗ n)).hom
      let mulWhisker :
          (ℱ ⊗ₘ ((ℒ ^⊗ (m : ℤ)) ⊗ₘ (ℒ ^⊗ n)) : ModX) ⟶
            (ℱ ⊗ₘ (ℒ ^⊗ ((m : ℤ) + n)) : ModX) :=
        show (ℱ ⊗ₘ ((ℒ ^⊗ (m : ℤ)) ⊗ₘ (ℒ ^⊗ n)) : ModX) ⟶
            (ℱ ⊗ₘ (ℒ ^⊗ ((m : ℤ) + n)) : ModX) from
          (ℱ ◁ (tensorPowerSheafIntAddIso ℒ (m : ℤ) n).hom)
      let shiftRight :
          (ℱ ⊗ₘ (ℒ ^⊗ ((m : ℤ) + n)) : ModX) ⟶
            (moduleTensor ℱ (ℒ ^⊗ ((m : ℤ) + n)) : ModX) :=
        show (ℱ ⊗ₘ (ℒ ^⊗ ((m : ℤ) + n)) : ModX) ⟶
            (moduleTensor ℱ (ℒ ^⊗ ((m : ℤ) + n)) : ModX) from
          (moduleTensorIsoTensorObj ℱ (ℒ ^⊗ ((m : ℤ) + n))).inv
      shiftLeft ≫ assocLeft ≫ braiding ≫ assocRight ≫ mulWhisker ≫ shiftRight

private noncomputable def gradedTwistedGlobalSectionsSmul
    [MonoidalCategory ModX]
    [MonoidalClosed ModX]
    [SymmetricCategory ModX]
    (ℒ : ModX) [IsInvertible ℒ] (ℱ : ModX) (m : ℕ) (n : ℤ)
    (x : gradedGlobalSectionsDegree ℒ m) (y : gradedTwistedGlobalSectionsDegree ℒ ℱ n) :
    gradedTwistedGlobalSectionsDegree ℒ ℱ ((m : ℤ) + n) :=
  let smulApp :
      (((ℒ ^⊗ (m : ℤ)) ⊗ₘ moduleTensor ℱ (ℒ ^⊗ n)).val.obj (op ⊤)) ⟶
        (moduleTensor ℱ (ℒ ^⊗ ((m : ℤ) + n))).val.obj (op ⊤) :=
    show (((ℒ ^⊗ (m : ℤ)) ⊗ₘ moduleTensor ℱ (ℒ ^⊗ n)).val.obj (op ⊤)) ⟶
        (moduleTensor ℱ (ℒ ^⊗ ((m : ℤ) + n))).val.obj (op ⊤) from
      (gradedTwistedGlobalSectionsSheafSmul ℒ ℱ m n).val.app (op ⊤)
  let smulHom :
      (PresheafOfModules.Monoidal.tensorObj
        ((ℒ ^⊗ (m : ℤ)).val) ((moduleTensor ℱ (ℒ ^⊗ n)).val)).obj (op ⊤) ⟶
        gradedTwistedGlobalSectionsDegree ℒ ℱ ((m : ℤ) + n) :=
    tensorTopToTensorObjHom (ℒ ^⊗ (m : ℤ)) (moduleTensor ℱ (ℒ ^⊗ n)) ≫ smulApp
  smulHom (x ⊗ₜ y)

/-- The homogeneous pieces of `Γ_*(ℒ)` form the canonical graded commutative ring owner. -/
instance
    [MonoidalCategory ModX]
    [MonoidalClosed ModX]
    [SymmetricCategory ModX]
    (ℒ : ModX) :
    DirectSum.GCommRing (fun n ↦ gradedGlobalSectionsDegree ℒ n) where
  one := show gradedGlobalSectionsDegree ℒ 0 from (1 : ΓX)
  mul := fun {m n} x y ↦ gradedGlobalSectionsMul ℒ m n x y
  one_mul := by
    intro a
    sorry
  mul_one := by
    intro a
    sorry
  mul_assoc := by
    intro a b c
    sorry
  mul_zero := by
    intro m n x
    sorry
  zero_mul := by
    intro m n y
    sorry
  mul_add := by
    intro m n x y z
    sorry
  add_mul := by
    intro m n x y z
    sorry
  natCast n := show gradedGlobalSectionsDegree ℒ 0 from (n : ΓX)
  natCast_zero := by
    sorry
  natCast_succ := by
    intro n
    sorry
  intCast z := show gradedGlobalSectionsDegree ℒ 0 from (z : ΓX)
  intCast_ofNat := by
    intro n
    sorry
  intCast_negSucc_ofNat := by
    intro n
    sorry
  mul_comm := by
    intro a b
    sorry
  gnpow_zero' := by
    sorry
  gnpow_succ' := by
    sorry

/-- The homogeneous pieces of `Γ_*(ℒ, ℱ)` form the canonical graded module over `Γ_*(ℒ)`. -/
instance
    [MonoidalCategory ModX]
    [MonoidalClosed ModX]
    [SymmetricCategory ModX]
    (ℒ : ModX) [IsInvertible ℒ] (ℱ : ModX) :
    DirectSum.Gmodule
      (fun n ↦ gradedGlobalSectionsDegree ℒ n)
      (fun n ↦ gradedTwistedGlobalSectionsDegree ℒ ℱ n) where
  smul := fun {m n} x y ↦ gradedTwistedGlobalSectionsSmul ℒ ℱ m n x y
  one_smul := by
    intro a
    sorry
  mul_smul := by
    intro a b c
    sorry
  smul_add := by
    intro m n x y z
    sorry
  smul_zero := by
    intro m n x
    sorry
  add_smul := by
    intro m n x y z
    sorry
  zero_smul := by
    intro m n y
    sorry

/-- The source-facing owner `Γ_*(ℒ)` carries its canonical commutative ring structure. -/
instance
    [MonoidalCategory ModX]
    [MonoidalClosed ModX]
    [SymmetricCategory ModX]
    (ℒ : ModX) :
    CommRing (Γ_*(ℒ)) :=
  inferInstance

/-- The source-facing owner `Γ_*(ℒ, ℱ)` carries its canonical module structure over `Γ_*(ℒ)`. -/
instance
    [MonoidalCategory ModX]
    [MonoidalClosed ModX]
    [SymmetricCategory ModX]
    (ℒ : ModX) [IsInvertible ℒ] (ℱ : ModX) :
    Module (Γ_*(ℒ)) (Γ_*(ℒ, ℱ)) :=
  inferInstance

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_17_25_8 (from Chap17) -/
namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 17.25.8:
- primary domain: categorical smallness of invertible `\mathcal O_X`-modules on a ringed space,
  expressed as a set of representatives up to isomorphism;
- inspected owner declarations:
  `SheafOfModules.RingedSite.exists_set_of_invertible_module_representatives`,
  `SheafOfModules.RingedSite.invertibleModuleProperty_essentiallySmall`,
  `CategoryTheory.ObjectProperty.EssentiallySmall.exists_small`,
  `SheafOfModules.exists_set_of_finiteType_module_representatives`;
- best owner abstraction: the Chapter 18 ringed-site theorem
  `SheafOfModules.RingedSite.exists_set_of_invertible_module_representatives`, specialized to the
  opens site of a ringed space;
- primitive data: a ringed space `X`, equivalently its structure sheaf on `Opens X`;
- derived API: the representative set obtained from the canonical
  `ObjectProperty.EssentiallySmall.exists_small` skeleton construction.

Source/core/bridge triage:
- `source-facing`: the Stacks Project assertion that invertible `\mathcal O_X`-modules admit a
  set of representatives up to isomorphism;
- `core/canonical`: the ringed-site theorem
  `SheafOfModules.RingedSite.exists_set_of_invertible_module_representatives`;
- `bridge/view`: the opens-site specialization from a ringed site to a ringed space.

This item is a canonical-recall item: the ringed-space statement adds no new mathematics beyond
that site-level owner theorem, so the file should reuse the owner directly rather than keeping a
parallel local theorem with the same interface.
-/

/- Lemma 17.25.8: on a ringed space `X`, there is a set of invertible `\mathcal O_X`-modules
containing exactly one representative of each isomorphism class. This is exactly the opens-site
specialization of the canonical ringed-site theorem. -/
recall SheafOfModules.RingedSite.exists_set_of_invertible_module_representatives

end AlgebraicGeometry.RingedSpace

/-! ### Definition_17_25_9 (from Chap17) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped RingedSitePicard

noncomputable section

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Definition 17.25.9:
- primary domain: Picard groups of ringed spaces, viewed through the monoidal category of
  `\mathcal O_X`-modules;
- inspected owner declarations:
  `RingedSpace.Modules`,
  `ringedSitePicardGroup`,
  `Pic(𝒪)`,
  `X.sheaf`;
- best owner abstraction: the core owner remains the ringed-site Picard group
  `ringedSitePicardGroup`, while the Chapter 17 source-facing bridge should be the ringed-space
  notation `Pic(X)` itself, defined directly from the structure sheaf of `X` rather than leaving
  the public surface one bridge lower at `Pic(X.sheaf)`;
- primitive data: the ringed space `X`, equivalently its structure sheaf `X.sheaf`;
- derived API: the ringed-space module category `RingedSpace.Modules X`, the thin bridge owner
  `RingedSpace.picardGroup X`, and the source-facing notation `Pic(X)`.

Layer triage:
- `source-facing`: the textbook notation `\mathrm{Pic}(X)`, surfaced here as `Pic(X)`;
- `core/canonical`: `ringedSitePicardGroup (Opens.grothendieckTopology X) X.sheaf`;
- `bridge/view`: the ringed-space module owner `RingedSpace.Modules X` together with the thin
  owner `RingedSpace.picardGroup X` and the notation bridge `Pic(X)`.
-/

/- Thin ringed-space bridge to the canonical Picard-group owner of the structure sheaf. -/
abbrev picardGroup (X : RingedSpace) [MonoidalCategory (RingedSpace.Modules X)] : Type _ :=
  _root_.ringedSitePicardGroup (Opens.grothendieckTopology X) X.sheaf

variable (X : RingedSpace)
variable [MonoidalCategory (RingedSpace.Modules X)]

/- Textbook notation for the Picard group `\mathrm{Pic}(X)` of a ringed space. -/
scoped[RingedSpacePicard] notation:max "Pic(" X ")" =>
  AlgebraicGeometry.RingedSpace.picardGroup X

open scoped RingedSpacePicard

/- Definition 17.25.9: the Picard group `\mathrm{Pic}(X)` of a ringed space is the canonical
ringed-site Picard group of its structure sheaf, i.e. the additive type of isomorphism classes of
invertible `\mathcal O_X`-modules under tensor product. -/
#check Pic(X)

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_17_25_10 (from Chap17) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open SheafOfModules.RingedSite

namespace SectionNonvanishingOpen

/- Lean parses bare `X_[s]` as indexed access, so the reusable owner-level notation is
parenthesized: `(X)_[s]`. In a local context with a fixed ambient variable `X`, one can then add
`local notation "X_[" s "]" => (X)_[s]` to recover the exact textbook surface. -/
set_option quotPrecheck false in
scoped macro:1075 X:term noWs "_[" s:term noWs "]" : term => do
  let sectionNonvanishingOpen :=
    Lean.mkIdent `AlgebraicGeometry.RingedSpace.sectionNonvanishingOpen
  `($sectionNonvanishingOpen $X _ $s)

end SectionNonvanishingOpen

open scoped SectionNonvanishingOpen

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable (X : RingedSpace.{u})

local notation "ModX" => RingedSpace.Modules X
local notation "IsInvertible" =>
  @SheafOfModules.RingedSite.IsInvertible _ _ (Opens.grothendieckTopology X) X.sheaf _ _

/- Domain-style sampling for Lemma 17.25.10:
- primary domain: nonvanishing loci of global sections of invertible `\mathcal O_X`-modules on a
  ringed space;
- inspected owner declarations:
  `RingedSpace.stalkModuleCat`,
  `SheafOfModules.over`,
  `SheafOfModules.unitHomEquiv`,
  `SheafOfModules.pushforwardSections`,
  `SheafOfModules.RingedSite.IsInvertible`;
- best owner abstraction: the source-facing owners are the nonvanishing locus/open of a section,
  while the core canonical layer is the invertibility owner `IsInvertible` together with the
  bundled stalk owner `RingedSpace.stalkModuleCat`; the restricted section map
  `\mathcal O_U \to \mathcal L|_U` is bridge/view data built from the unit/sections adjunction on
  `ℒ.over U`;
- primitive data: a module `ℒ : ModX` and a global section `s : ℒ.sections`;
- derived API: openness of the nonvanishing locus, the associated open subset `(X)_[s]`, and the
  restricted section morphism on that open.

Source/core/bridge triage:
- `source-facing`: `sectionNonvanishingLocus` and `sectionNonvanishingOpen`;
- `core/canonical`: `IsInvertible`, `RingedSpace.stalkModuleCat`, `SheafOfModules.over`, and
  `SheafOfModules.unitHomEquiv`;
- `bridge/view`: `sectionOverHom` and its specialization to `sectionNonvanishingOpen`.
-/

/-- The morphism `\mathcal O_U \to \mathcal L|_U` induced by restricting a global section of
`\mathcal L` to an open subset `U`. -/
noncomputable abbrev sectionOverHom (ℒ : ModX) (s : ℒ.sections) (U : Opens X) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ ℒ.over U :=
  (ℒ.over U).unitHomEquiv.symm
    (SheafOfModules.pushforwardSections (𝟙 (X.ringCatSheaf.over U)) s)

section Nonvanishing

variable [∀ x : X, IsLocalRing (X.presheaf.stalk x)]

/-- The source-defined nonvanishing locus of a section of an `\mathcal O_X`-module. -/
def sectionNonvanishingLocus (ℒ : ModX) (s : ℒ.sections) : Set X :=
  {x | (TopCat.Presheaf.Γgerm ℒ.val.presheaf x (s.1 (op ⊤))) ∉
    ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
      (⊤ : Submodule (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℒ x)))}

-- Proof sketch: for a point where the stalk germ of `s` is not in
-- `\mathfrak m_x \mathcal L_x`, invertibility identifies `\mathcal L_x` with a free rank-one
-- module over the local ring `\mathcal O_{X,x}`; Nakayama then shows that the germ of `s`
-- generates `\mathcal L_x`. Choosing local dual sections with evaluation `1` gives an open
-- neighbourhood basis inside the locus, hence the locus is open.
section Invertible

variable [monoidalModX : MonoidalCategory ModX]

local instance ringedSiteMonoidalCategory :
    MonoidalCategory (ringedSiteModuleCategory (Opens.grothendieckTopology X) X.sheaf) := by
  simpa using monoidalModX

/-- Lemma 17.25.10: for an invertible `\mathcal O_X`-module `\mathcal L` and a global section
`s`, the set of points where the germ of `s` is not contained in
`\mathfrak m_x \mathcal L_x` is open. -/
theorem sectionNonvanishingLocus_isOpen (ℒ : ModX)
    [IsInvertible ℒ]
    (s : ℒ.sections) :
    IsOpen (sectionNonvanishingLocus X ℒ s) := sorry

/-- The open subset cut out by the nonvanishing locus of a section of an invertible
`\mathcal O_X`-module. -/
def sectionNonvanishingOpen (ℒ : ModX)
    [IsInvertible ℒ]
    (s : ℒ.sections) : Opens X :=
  ⟨sectionNonvanishingLocus X ℒ s, sectionNonvanishingLocus_isOpen X ℒ s⟩

-- Proof sketch: on the open locus from the previous theorem, each stalk germ of `s` is a basis
-- vector of the rank-one free stalk `\mathcal L_x`. A morphism of sheaves of modules is an
-- isomorphism iff it is an isomorphism on all stalks, so the restricted map
-- `\mathcal O_{(X)_[s]} \to \mathcal L|_{(X)_[s]}` induced by `s` is an isomorphism.
/-- On the nonvanishing open `(X)_[s]`, the restricted section induces an isomorphism
`\mathcal O_{(X)_[s]} \cong \mathcal L|_{(X)_[s]}`. -/
instance isIso_sectionOverHom_sectionNonvanishingOpen (ℒ : ModX)
    [IsInvertible ℒ]
    (s : ℒ.sections) :
    IsIso (sectionOverHom X ℒ s ((X)_[s])) := sorry
end Invertible

end Nonvanishing

end AlgebraicGeometry.RingedSpace
