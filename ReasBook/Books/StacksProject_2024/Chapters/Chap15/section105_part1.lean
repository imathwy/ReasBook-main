import Mathlib
import Mathlib.Data.List.TFAE
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Ideal.Pure
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Unramified.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_105_1 (from Chap15) -/
open scoped TensorProduct

universe u v w

variable (A : Type u) [CommRing A]

/-- Definition 15.105.1 (1): a commutative ring is absolutely flat if every `A`-module is flat
over `A`. We package the standard equivalent elementwise criterion so the owner is independent of
the module universe; the flatness of arbitrary `A`-modules is exposed as derived API below. -/
class IsAbsolutelyFlatRing : Prop where
  /-- Every element of `A` admits a von Neumann regular factorization. -/
  exists_factor (a : A) : ∃ b : A, a = a ^ 2 * b

/-- Every additive `A`-module is flat over an absolutely flat ring. -/
instance {M : Type w} [AddCommGroup M] [Module A M] [IsAbsolutelyFlatRing A] : Module.Flat A M :=
  sorry

section

variable (K : Type u) [Field K]

/-- Every field is an absolutely flat ring. -/
instance : IsAbsolutelyFlatRing K := sorry

end

section

variable {ι : Type u} (A : ι → Type v) [∀ i, CommRing (A i)] [∀ i, IsAbsolutelyFlatRing (A i)]

/-- Coordinatewise products of absolutely flat rings are absolutely flat. -/
instance : IsAbsolutelyFlatRing ((i : ι) → A i) where
  exists_factor a := by
    classical
    choose b hb using fun i ↦ (inferInstance : IsAbsolutelyFlatRing (A i)).exists_factor (a i)
    refine ⟨b, ?_⟩
    ext i
    simpa [pow_two] using hb i

end

namespace Algebra

variable (B : Type v) [CommRing B] [Algebra A B]

/-- Definition 15.105.1 (2): a ring map `A → B` is weakly étale, or absolutely flat, if `B` is
flat over `A` and the multiplication map `B ⊗[A] B → B` is flat. -/
class IsWeaklyEtale : Prop where
  /-- The structure map `A → B` is flat, expressed on the underlying `A`-module `B`. -/
  moduleFlat : Module.Flat A B
  /-- The multiplication map `B ⊗[A] B → B` is flat. -/
  flat_tensorSquareMultiplication :
    (Algebra.TensorProduct.lmul' A : B ⊗[A] B →ₐ[A] B).Flat

/-- A weakly étale `A`-algebra is flat over `A`. -/
instance [h : IsWeaklyEtale A B] : Module.Flat A B :=
  h.moduleFlat

namespace IsWeaklyEtale

/-- The structure map of a weakly étale algebra is flat. -/
theorem flat (h : IsWeaklyEtale A B) : (algebraMap A B).Flat :=
  RingHom.flat_algebraMap_iff.mpr h.moduleFlat

end IsWeaklyEtale

section

variable {A}

/-- The identity map of a commutative ring is weakly étale. -/
instance : IsWeaklyEtale A A := sorry

end

end Algebra

/-! ### Lemma_15_105_2 (from Chap15) -/
open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable {N : Type w} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]

/- Domain triage:
- primary domain: commutative algebra of flat modules and the tensor-square criterion for weakly
  étale morphisms;
- source-facing layer: this Stacks lemma transferring flatness of a module from the base ring `A`
  to the algebra `B` under flatness of the multiplication map `B ⊗[A] B → B`;
- core/canonical owners: `Module.Flat`, `Module.Flat.baseChange`, `Module.Flat.trans`,
  `Algebra.IsWeaklyEtale`, and `(lmul' A).Flat`;
- bridge/view: the owner-level companion `Module.Flat.of_isWeaklyEtale`, obtained by feeding the
  tensor-square flatness field of `Algebra.IsWeaklyEtale A B` into the source-facing theorem.

The numbered theorem remains source-facing: there is no exact upstream owner theorem with this
interface, so the refinement is to keep the textbook statement while exposing the direct
owner-facing bridge separately.
-/

-- Proof sketch: tensoring a short exact sequence of `B`-modules with `N` over `A` is exact
-- because `N` is `A`-flat. Reinterpret this as extension of scalars from `B` to `B ⊗[A] B`,
-- and then descend exactness back along the flat multiplication map
-- `B ⊗[A] B → B`, so tensoring over `B` with `N` is exact.
/-- Lemma 15.105.2: if the multiplication map `B ⊗[A] B → B` is flat and `N` is flat as an
`A`-module, then `N` is flat as a `B`-module. -/
theorem flat_of_flat_base_and_flat_tensorSquareMultiplication
    (hflatMul : (lmul' A : B ⊗[A] B →ₐ[A] B).Flat)
    (hflatN : Module.Flat A N) :
    Module.Flat B N := sorry

/-- Bridge/view: over a weakly étale map `A → B`, every `A`-flat `B`-module is `B`-flat. -/
theorem Module.Flat.of_isWeaklyEtale [Algebra.IsWeaklyEtale A B]
    (hflatN : Module.Flat A N) :
    Module.Flat B N :=
  flat_of_flat_base_and_flat_tensorSquareMultiplication
    ‹Algebra.IsWeaklyEtale A B›.flat_tensorSquareMultiplication hflatN

end

/-! ### Definition_15_105_3 (from Chap15) -/
open CategoryTheory

universe u

section

variable (A : Type u) [CommRing A]

/-
Domain-style sampling:
- primary domain: weak dimension of commutative rings, viewed as a uniform tor-dimension bound on
  modules;
- sampled owner declarations:
  `CategoryTheory.ModuleHasTorDimensionLE`,
  `ModuleCat.HasFiniteFlatResolutionLengthLE`,
  `ModuleCat.hasTorDimensionLE_iff_hasFiniteFlatResolutionLengthLE`,
  `HasGlobalDimensionLE`;
- best owner abstraction: `HasWeakDimensionLE A d` remains the source-facing ring-level owner, but
  its primitive field should be the canonical module owner `ModuleHasTorDimensionLE` rather than
  the derived flat-resolution presentation;
- primitive vs. derived:
  primitive data is the uniform tor-dimension bound on all `A`-modules;
  derived API is the finite-flat-resolution formulation supplied by Lemma `15.67.6`.
-/

/-- Definition 15.105.3: a ring `A` has weak dimension at most `d` if every `A`-module admits a
finite flat resolution of length at most `d`, equivalently has tor dimension at most `d`. -/
class HasWeakDimensionLE (d : ℕ) : Prop where
  hasTorDimensionLE (M : ModuleCat.{u} A) : ModuleHasTorDimensionLE M d

/-- Over a ring of weak dimension at most `d`, every `A`-module has tor dimension at most `d`. -/
instance (d : ℕ) [HasWeakDimensionLE A d] (M : ModuleCat.{u} A) :
    ModuleHasTorDimensionLE M d :=
  HasWeakDimensionLE.hasTorDimensionLE M

/-- Over a ring of weak dimension at most `d`, every `A`-module admits a finite flat resolution of
length at most `d`. -/
instance (d : ℕ) [HasWeakDimensionLE A d] (M : ModuleCat.{u} A) :
    ModuleCat.HasFiniteFlatResolutionLengthLE M d := by
  let hwd : HasWeakDimensionLE A d := inferInstance
  have hM : ModuleHasTorDimensionLE M d := hwd.hasTorDimensionLE M
  exact ModuleCat.ModuleHasTorDimensionLE.hasFiniteFlatResolutionLengthLE M hM

/-- A ring of global dimension at most `d` has weak dimension at most `d`. -/
instance (d : ℕ) [HasGlobalDimensionLE A d] : HasWeakDimensionLE A d where
  hasTorDimensionLE M := by
    sorry

end

/-! ### Lemma_15_105_4 (from Chap15) -/
universe u v

open CategoryTheory

section

variable (A : Type u) [CommRing A]
variable (B : Type v) [CommRing B] [Algebra A B]
variable (d : ℕ) [HasWeakDimensionLE A d]

/- Domain triage:
- primary domain: weak dimension of commutative rings and its behavior under weakly étale maps;
- sampled owner declarations:
  `HasWeakDimensionLE`,
  `ModuleHasTorDimensionLE`,
  `ModuleCat.hasTorDimensionLE_iff_hasFiniteFlatResolutionLengthLE`,
  `Algebra.IsWeaklyEtale`;
- best owner abstraction: the ring-level owner is `HasWeakDimensionLE`, with the explicit owner
  input `hAB : Algebra.IsWeaklyEtale A B` supplying the flatness input on the structure map and
  tensor-square multiplication;
- primitive vs. derived:
  the primitive data live in the owner classes `HasWeakDimensionLE A d` and
  `Algebra.IsWeaklyEtale A B`;
  the source-facing transfer theorem below and the resulting owner instance on `B` are derived API.

Source/core/bridge triage:
- `source-facing`: `hasWeakDimensionLE_of_isWeaklyEtale`;
- `core/canonical`: `HasWeakDimensionLE` and `Algebra.IsWeaklyEtale`;
- `bridge/view`: the tor-dimension/flat-resolution comparison from Lemma `15.67.6` and the
  owner-level flatness transfer theorem `Module.Flat.of_isWeaklyEtale`.
-/

-- Proof sketch: for `N : ModuleCat B`, restrict scalars to `A`. The owner
-- `HasWeakDimensionLE A d` gives tor dimension at most `d` over `A`, hence by Lemma `15.67.6`
-- a finite flat `A`-resolution of length `d`. Its final syzygy is `A`-flat, so
-- `Module.Flat.of_isWeaklyEtale` upgrades that top term to `B`-flat. Converting the resulting
-- length-`d` flat `B`-resolution back through Lemma `15.67.6` yields tor dimension at most `d`
-- over `B`.
/-- Lemma 15.105.4: if `A → B` is weakly étale and `A` has weak dimension at most `d`, then `B`
has weak dimension at most `d`. -/
theorem hasWeakDimensionLE_of_isWeaklyEtale
    (hAB : Algebra.IsWeaklyEtale A B)
    : HasWeakDimensionLE B d where
  hasTorDimensionLE N := by
    let _ : (algebraMap A B).Flat := hAB.flat
    sorry

-- This transfer is intentionally not registered as a global instance. Unlike base change in
-- Lemma `15.105.7`, the source ring `A` of a weakly étale map `A → B` is not determined by the
-- target owner `HasWeakDimensionLE B d`, so typeclass search would have to guess a noncanonical
-- ambient algebra `A → B`.

end

/-! ### Lemma_15_105_5 (from Chap15) -/
universe u

section

variable (A : Type u) [CommRing A]

/- Domain-style sampling:
- primary domain: commutative algebra of weak dimension, absolute flatness, zero-dimensional
  reduced rings, and prime localizations;
- sampled owner declarations:
  `HasWeakDimensionLE`,
  `ModuleCat.hasTorDimensionLE_zero_iff_flat`,
  `IsAbsolutelyFlatRing`,
  `Ring.KrullDimLE.of_isLocalization`,
  `Ring.KrullDimLE.isField_of_isReduced`;
- best owner abstraction: the source-facing clause `(1)` should use the chapter owner
  `HasWeakDimensionLE A 0`, with the module-level zero-step bridge supplied canonically by
  `ModuleCat.hasTorDimensionLE_zero_iff_flat`; clause `(2)` should use the project owner
  `IsAbsolutelyFlatRing`, and clauses `(3)` and `(4)` should use the canonical mathlib owners
  `Ring.KrullDimLE 0` and `Localization.AtPrime`;
- primitive vs. derived:
  primitive data is just the ring `A` together with these owner predicates on `A` and its prime
  localizations;
  the only source-facing declaration needed here is the four-way `TFAE`, so no extra wrapper
  theorem is warranted.

Source/core/bridge triage:
- `source-facing`: the four-way equivalence matching the Stacks clause list;
- `core/canonical`: `HasWeakDimensionLE`, `IsAbsolutelyFlatRing`, `Ring.KrullDimLE 0`, and
  `Localization.AtPrime`;
- `bridge/view`: the `TFAE` theorem itself, which compares the source clauses directly without
  introducing any extra packaged interface.
-/

-- Proof sketch: `(1) ↔ (2)` follows by unpacking weak dimension `≤ 0` and using that tor
-- dimension `≤ 0` is flatness for every module. For `(2) → (3)`, absolute flatness makes every
-- finitely generated ideal pure, hence idempotent-generated, so basic opens are clopen; this
-- forces every prime ideal to be maximal, and nilpotents vanish. For `(3) → (4)`, transport
-- `Ring.KrullDimLE 0 A` to each `Localization.AtPrime p.asIdeal` via
-- `Ring.KrullDimLE.of_isLocalization`, then combine with reducedness and
-- `Ring.KrullDimLE.isField_of_isReduced`. For `(4) → (2)`, flatness is local at prime
-- localizations, and modules over fields are flat.
/-- Lemma 15.105.5: for a commutative ring `A`, the following are equivalent: `A` has weak
dimension at most `0`; `A` is absolutely flat; `A` is reduced and every prime ideal is maximal,
formalized as `IsReduced A ∧ Ring.KrullDimLE 0 A`; and every canonical prime localization
`Localization.AtPrime p.asIdeal` is a field. -/
theorem weakDimensionLEZero_tfae :
    List.TFAE
      [ HasWeakDimensionLE A 0
      , IsAbsolutelyFlatRing A
      , IsReduced A ∧ Ring.KrullDimLE 0 A
      , ∀ p : PrimeSpectrum A, IsField (Localization.AtPrime p.asIdeal)
      ] := sorry

/-- An absolutely flat commutative ring has weak dimension at most `0`. -/
theorem hasWeakDimensionLEZero_of_isAbsolutelyFlatRing [IsAbsolutelyFlatRing A] :
    HasWeakDimensionLE A 0 := by
  have h : IsAbsolutelyFlatRing A ↔ HasWeakDimensionLE A 0 :=
    (weakDimensionLEZero_tfae A).out 1 0
  exact h.mp inferInstance

/-- A commutative ring of weak dimension at most `0` is absolutely flat. -/
theorem isAbsolutelyFlatRing_of_hasWeakDimensionLEZero [HasWeakDimensionLE A 0] :
    IsAbsolutelyFlatRing A := by
  have h : HasWeakDimensionLE A 0 ↔ IsAbsolutelyFlatRing A :=
    (weakDimensionLEZero_tfae A).out 0 1
  exact h.mp inferInstance

/-- An absolutely flat commutative ring is reduced. -/
theorem isReduced_of_isAbsolutelyFlatRing [IsAbsolutelyFlatRing A] :
    IsReduced A := by
  have h : IsAbsolutelyFlatRing A ↔ IsReduced A ∧ Ring.KrullDimLE 0 A :=
    (weakDimensionLEZero_tfae A).out 1 2
  exact (h.mp inferInstance).1

end

/-! ### Lemma_15_105_6 (from Chap15) -/
universe u v

section

variable {ι : Type u} (K : ι → Type v) [∀ i, Field (K i)]

/- Domain-style sampling:
- primary domain: commutative algebra of absolutely flat rings and coordinatewise product rings;
- sampled owner declarations:
  `IsAbsolutelyFlatRing`,
  the field instance for `IsAbsolutelyFlatRing`,
  the coordinatewise product instance for `IsAbsolutelyFlatRing`,
  `Pi.commRing`;
- best owner abstraction: `IsAbsolutelyFlatRing` on each factor is the primitive data, while
  absolute flatness of the product ring is the owner-derived coordinatewise instance now living
  upstream in `Definition_15_105_1`. The source-facing product-of-fields item should therefore be
  a direct specialization of that owner rather than a second local instance.
-
- Source/core/bridge triage:
- `source-facing`: the product-of-fields specialization below;
- `core/canonical`: the upstream coordinatewise instance
  `[∀ i, IsAbsolutelyFlatRing (K i)] → IsAbsolutelyFlatRing ((i : ι) → K i)`;
- `bridge/view`: the factorwise field instances from `Definition_15_105_1`.
-/

/- Lemma 15.105.6: a product of fields is an absolutely flat ring, by specializing the canonical
coordinatewise product instance for absolutely flat rings to the field case. -/
#synth IsAbsolutelyFlatRing ((i : ι) → K i)

end

/-! ### Lemma_15_105_7 (from Chap15) -/
open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

section

variable {A : Type u} {A' : Type v} {B : Type w}
variable [CommRing A] [CommRing A'] [CommRing B] [Algebra A B] [Algebra A A']

local notation "B'" => A' ⊗[A] B

/- Domain-style sampling for weakly étale base change:
- primary domain: commutative algebra of flat ring maps and weakly étale morphisms under tensor
  base change;
- source-facing layer: part `(1)` is the tensor-square flatness clause in the weakly étale
  criterion after base change;
- core/canonical owner: the chapter-local ring-map owner `Algebra.IsWeaklyEtale`;
- sampled bridge API: `RingHom.Flat.tensorProductMap` for tensor-product flatness and
  `Algebra.TensorProduct.cancelBaseChange` / `assoc` for the canonical identification of the
  base-changed tensor square;
- primitive data: flatness of `lmul' A`;
- derived API: flatness of `lmul' A'` and the owner theorem `Algebra.IsWeaklyEtale.baseChange`.
-/

namespace Algebra

-- Proof sketch: identify the multiplication map
-- `(A' ⊗[A] B) ⊗[A'] (A' ⊗[A] B) → A' ⊗[A] B` with the base change of
-- `B ⊗[A] B → B` along `A → A'`, and then apply flat base change from Lemma `10.39.7`.
/-- Lemma 15.105.7 (1): if the multiplication map `B ⊗[A] B → B` is flat, then the multiplication
map `(A' ⊗[A] B) ⊗[A'] (A' ⊗[A] B) → A' ⊗[A] B` is flat. -/
theorem tensorSquareMul_flat_baseChange
    (hflatMul : (lmul' A : B ⊗[A] B →ₐ[A] B).Flat) :
    let _ : Algebra (B' ⊗[A'] B') B' := (lmul' A').toAlgebra
    Module.Flat (B' ⊗[A'] B') B' := by
  sorry

-- Proof sketch: flatness of the structure map after base change is canonical, and part `(1)`
-- gives the tensor-square multiplication clause.
namespace IsWeaklyEtale

/-- Lemma 15.105.7 (2): if `A → B` is weakly étale, then the base-changed map
`A' → A' ⊗[A] B` is weakly étale. -/
theorem baseChange (hAB : IsWeaklyEtale A B) : IsWeaklyEtale A' B' := by
  sorry

end IsWeaklyEtale

/- Bridge/view: weakly étaleness is preserved under tensor base change. -/
attribute [instance] IsWeaklyEtale.baseChange

end Algebra

end

/-! ### Lemma_15_105_8 (from Chap15) -/
universe u v

section

open scoped TensorProduct

variable {A : Type u} [CommRing A]
variable {B : Type v} [CommRing B] [Algebra A B]

/- Domain-style sampling:
- primary domain: commutative algebra of weakly étale ring maps, absolute flatness, and
  reducedness ascent along flat maps with reduced fibers;
- sampled owner declarations:
  `IsAbsolutelyFlatRing`,
  `Algebra.IsWeaklyEtale`,
  `hasWeakDimensionLE_of_isWeaklyEtale`,
  `isReduced_of_flat_of_fiber`,
  `Ideal.Fiber`,
  `isReduced_of_isAbsolutelyFlatRing`;
- best owner abstraction: the ambient map property is the chapter owner
  `Algebra.IsWeaklyEtale`, while absolute flatness and reducedness remain owner predicates on the
  source and target rings;
- primitive vs. derived: the primitive data are the owner classes `IsAbsolutelyFlatRing A`,
  `IsReduced A`, and `Algebra.IsWeaklyEtale A B`; the two transfer theorems below are derived API;
- source/core/bridge triage:
  `source-facing`: the two Stacks transfer lemmas below;
  `core/canonical`: `IsAbsolutelyFlatRing`, `IsReduced`, `Algebra.IsWeaklyEtale`,
    `hasWeakDimensionLE_of_isWeaklyEtale`, `Ideal.Fiber`, `isReduced_of_flat_of_fiber`, and
    `isReduced_of_isAbsolutelyFlatRing`;
  `bridge/view`: the zero-weak-dimension TFAE and weakly étale base change to residue-field
    fibers, with part `(1)` upgrading those field fibers to absolutely flat rings and hence
    reduced rings.

This file should therefore expose the source-facing consequences directly in terms of the explicit
owner input `hAB : Algebra.IsWeaklyEtale A B`, reusing the chapter ascent owners instead of
introducing parallel local reducedness or absolute-flatness wrappers. For reducedness, the
source-facing weakly étale fiber theorem below is the bridge into the general ascent owner
`isReduced_of_flat_of_fiber`.
-/

-- Proof sketch: by Lemma `15.105.5`, absolute flatness of `A` is equivalent to weak dimension at
-- most `0`. Lemma `15.105.4` transports that owner property across the weakly étale map `A → B`,
-- and Lemma `15.105.5` then turns weak dimension at most `0` back into absolute flatness of `B`.
/-- Lemma 15.105.8 (1): if `A` is absolutely flat and `A → B` is weakly étale, then `B` is
absolutely flat. -/
theorem isAbsolutelyFlatRing_of_isWeaklyEtale
    (hAB : Algebra.IsWeaklyEtale A B) [IsAbsolutelyFlatRing A] :
    IsAbsolutelyFlatRing B := by
  letI : HasWeakDimensionLE A 0 := hasWeakDimensionLEZero_of_isAbsolutelyFlatRing A
  have hB : HasWeakDimensionLE B 0 := hasWeakDimensionLE_of_isWeaklyEtale A B 0 hAB
  letI : HasWeakDimensionLE B 0 := hB
  exact isAbsolutelyFlatRing_of_hasWeakDimensionLEZero B

-- After base change to a residue field, a weakly étale map stays weakly étale. Over a field, part
-- `(1)` makes the fiber absolutely flat, and reducedness is the thin companion from
-- Lemma `15.105.5`.
/-- Every fiber ring `p.asIdeal.Fiber B = κ(p) ⊗[A] B` of a weakly étale map `A → B` is
absolutely flat. -/
theorem isAbsolutelyFlatRing_fiber_of_isWeaklyEtale
    (hAB : Algebra.IsWeaklyEtale A B) (p : PrimeSpectrum A) :
    IsAbsolutelyFlatRing (p.asIdeal.Fiber B) := by
  let hfiber : Algebra.IsWeaklyEtale p.asIdeal.ResidueField (p.asIdeal.Fiber B) := hAB.baseChange
  exact isAbsolutelyFlatRing_of_isWeaklyEtale hfiber

/-- Every fiber ring `p.asIdeal.Fiber B = κ(p) ⊗[A] B` of a weakly étale map `A → B` is
reduced. -/
theorem isReduced_fiber_of_isWeaklyEtale
    (hAB : Algebra.IsWeaklyEtale A B) (p : PrimeSpectrum A) :
    IsReduced (p.asIdeal.Fiber B) := by
  letI : IsAbsolutelyFlatRing (p.asIdeal.Fiber B) :=
    isAbsolutelyFlatRing_fiber_of_isWeaklyEtale hAB p
  exact isReduced_of_isAbsolutelyFlatRing (p.asIdeal.Fiber B)

/-- Lemma 15.105.8 (2): if `A` is reduced and `A → B` is weakly étale, then `B` is reduced. -/
theorem isReduced_of_isWeaklyEtale
    (hAB : Algebra.IsWeaklyEtale A B) [IsReduced A] :
    IsReduced B := by
  have hfiber : ∀ p : PrimeSpectrum A, IsReduced (p.asIdeal.Fiber B) :=
    isReduced_fiber_of_isWeaklyEtale hAB
  sorry

end

/-! ### Lemma_15_105_9 (from Chap15) -/
open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

namespace Algebra

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/- Domain triage:
- primary domain: commutative algebra of weakly étale ring maps and tensor-square multiplication
  under composition;
- source-facing layer: part `(1)` is the tensor-square flatness statement for the composite;
- core/canonical owners sampled for this file:
  `Algebra.IsWeaklyEtale`,
  `Module.Flat.trans`,
  and `RingHom.Flat.comp`;
- primitive data: the two flat tensor-square multiplication maps, together with the owner facts on
  `A → B` and `B → C` for the composition theorem in part `(2)`;
- derived API: the source-facing tensor-square flatness theorem `tensorSquareMul_flat_comp`;
- bridge/view: there is no separate upstream ring-map owner in this environment, so part `(2)` is
  the owner theorem `Algebra.IsWeaklyEtale.comp` itself.
-/

-- Proof sketch: factor `C ⊗[A] C → C` through the base change of `B ⊗[A] B → B` along
-- `B ⊗[A] B → C ⊗[A] C`, identify the intermediate map with `C ⊗[B] C → C`, and apply flat base
-- change together with stability of flat ring maps under composition.
/-- Lemma 15.105.9 (1): if the multiplication maps `B ⊗[A] B → B` and `C ⊗[B] C → C` are flat,
then the multiplication map `C ⊗[A] C → C` is flat. -/
theorem tensorSquareMul_flat_comp
    (hAB : (lmul' A : B ⊗[A] B →ₐ[A] B).Flat)
    (hBC : (lmul' B : C ⊗[B] C →ₐ[B] C).Flat) :
    (lmul' A : C ⊗[A] C →ₐ[A] C).Flat := by
  sorry

namespace IsWeaklyEtale

-- Proof sketch: compose flatness of `A → B` and `B → C` by `Module.Flat.trans`, and use part
-- `(1)` for the tensor-square multiplication clause of the composite.
/-- Lemma 15.105.9 (2): the composite of weakly étale ring maps is weakly étale. -/
theorem comp (hAB : IsWeaklyEtale A B) (hBC : IsWeaklyEtale B C) : IsWeaklyEtale A C := by
  letI : Module.Flat A B := hAB.moduleFlat
  letI : Module.Flat B C := hBC.moduleFlat
  exact
    { moduleFlat := Module.Flat.trans A B C
      flat_tensorSquareMultiplication :=
        tensorSquareMul_flat_comp hAB.flat_tensorSquareMultiplication
          hBC.flat_tensorSquareMultiplication }

end IsWeaklyEtale

end

end Algebra

/-! ### Lemma_15_105_10 (from Chap15) -/
open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

namespace Algebra

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/- Domain triage:
- primary domain: commutative algebra of faithfully flat descent for weakly étale ring maps;
- source-facing layer: part `(1)` is the tensor-square flatness descent statement appearing in the
  source text;
- core/canonical owners sampled for this file: `RingHom.FaithfullyFlat`,
  `flat_iff_flat_baseChange_of_faithfullyFlat`,
  `algebraMap_flat_of_flat_of_faithfullyFlat`, and the owner class `IsWeaklyEtale`;
- primitive data: faithful flatness of `B → C` and an explicit weakly étale owner proof on
  `A → C`;
- derived API: flatness of `A → B` and of the tensor-square multiplication `B ⊗[A] B → B`.

The file remains source-facing: there is no exact upstream owner theorem with this interface. The
refinement is to keep part `(1)` as the bridge theorem and expose part `(2)` as an owner theorem in
`IsWeaklyEtale`, matching the chapter's existing weakly étale API.
-/

-- Proof sketch: view `C ⊗[A] C → C` as the faithfully flat base change of
-- `B ⊗[A] B → B` along `B → C`. Then apply the flatness descent criterion of Lemma `10.39.9` to
-- descend flatness of `C` as a module over `C ⊗[A] C` to flatness of `B` as a module over
-- `B ⊗[A] B`.
/-- Lemma 15.105.10 (1): if `B → C` is faithfully flat and the multiplication map
`C ⊗[A] C → C` is flat, then the multiplication map `B ⊗[A] B → B` is flat. -/
theorem tensorSquareMul_flat_of_faithfullyFlat
    (hBC_ff : (algebraMap B C).FaithfullyFlat)
    (hflatMul : (lmul' A : C ⊗[A] C →ₐ[A] C).Flat) :
    (lmul' A : B ⊗[A] B →ₐ[A] B).Flat := sorry

namespace IsWeaklyEtale

-- Proof sketch: weakly étale means flatness of `A → C` together with flatness of the
-- multiplication map `C ⊗[A] C → C`. Use the derived owner theorem `IsWeaklyEtale.flat` for
-- `A → C`, convert it back to the module-flat instance needed by Lemma `10.39.10`, and descend
-- along the faithfully flat map `B → C`. Then descend the tensor-square flatness by part `(1)`.
/-- Lemma 15.105.10 (2): if `B → C` is faithfully flat and `A → C` is weakly étale, then
`A → B` is weakly étale. -/
theorem of_faithfullyFlat
    (hBC_ff : (algebraMap B C).FaithfullyFlat)
    (hAC : IsWeaklyEtale A C) :
    IsWeaklyEtale A B := by
  sorry

end IsWeaklyEtale

end

end Algebra

/-! ### Lemma_15_105_11 (from Chap15) -/
open scoped TensorProduct
open Algebra.TensorProduct

namespace Algebra
namespace IsWeaklyEtale

universe u v w

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

attribute [local instance] TensorProduct.rightAlgebra

/- Domain triage:
- primary domain: commutative algebra of weakly étale ring maps in an algebra tower;
- source-facing layer: the Stacks closure lemma asserting that in a tower `A → B → C`, if both
  `A → B` and `A → C` are weakly étale, then so is `B → C`;
- core/canonical owners sampled for this file: `Algebra.IsWeaklyEtale`,
  `Algebra.IsWeaklyEtale.baseChange`, `Algebra.IsWeaklyEtale.of_faithfullyFlat`, and the
  canonical tensor-product map `Algebra.TensorProduct.lift`;
- primitive data: the two weakly étale owner facts on `A → B` and `A → C`;
- derived API: the base-changed weakly étale fact on `B → B ⊗[A] C`, faithful flatness of
  `C → B ⊗[A] C`, and the resulting owner fact on `B → C`.

This item remains source-facing. Its canonical proof route is the owner chain
`Algebra.IsWeaklyEtale.baseChange` followed by `Algebra.IsWeaklyEtale.of_faithfullyFlat`, with the
tensor-product map `C → B ⊗[A] C` handled as the split flat base change of `A → B`.
-/

-- Proof sketch: base change `A → C` along `A → B` to obtain the owner fact
-- `IsWeaklyEtale B (B ⊗[A] C)`. The base-changed map `C → B ⊗[A] C` is flat because `A → B` is
-- flat, and it has a retraction given by tensor-product multiplication, hence it is faithfully
-- flat. Then descend weak étaleness from `B → B ⊗[A] C` to `B → C` using the owner theorem
-- `Algebra.IsWeaklyEtale.of_faithfullyFlat`.
/-- Lemma 15.105.11: in a tower `A → B → C`, if both `A → B` and `A → C` are weakly étale, then
`B → C` is weakly étale. -/
theorem of_tower (hAB : IsWeaklyEtale A B) (hAC : IsWeaklyEtale A C) :
    IsWeaklyEtale B C := by
  sorry

end

end IsWeaklyEtale
end Algebra

/-! ### Lemma_15_105_12 (from Chap15) -/
open scoped TensorProduct
open Algebra.TensorProduct

universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/- Domain triage:
- primary domain: commutative algebra of tensor-square criteria for formally unramified ring maps;
- source-facing layer: triviality of the Kähler differentials `Ω[B⁄A]` under flatness of the
  tensor-square multiplication map `lmul' A`, exactly the Stacks conclusion of Lemma `15.105.12`;
- core/canonical owners sampled for this file: `Algebra.FormallyUnramified`,
  `Algebra.formallyUnramified_iff`, `Algebra.WeaklyEtale`, `Ideal.Pure`, and
  `Ideal.isIdempotentElem_of_pure`;
- primitive data: flatness of `lmul' A`;
- derived API: the source-facing conclusion `Subsingleton Ω[B⁄A]`, and the companion bridge
  `Algebra.FormallyUnramified.of_tensorSquareMul_flat`.

The file stays source-facing: the numbered theorem concludes `Subsingleton Ω[B⁄A]`, while
formal unramifiedness is recovered only through the canonical owner
`Algebra.FormallyUnramified`.
-/

namespace Algebra.FormallyUnramified

-- Proof sketch: let `I = KaehlerDifferential.ideal A B`, the diagonal ideal in `B ⊗[A] B`.
-- Since `I = ker(B ⊗[A] B → B)` for the multiplication map, surjectivity and flatness make the
-- quotient `(B ⊗[A] B) ⧸ I` flat, so `I` is a pure ideal. Hence `I` is idempotent, and the
-- cotangent presentation `Ω[B⁄A] = I/I²` collapses to zero.
/-- Companion bridge: flatness of the tensor-square multiplication map implies that `B` is formally
unramified over `A`. -/
theorem of_tensorSquareMul_flat
    (hflatMul : (lmul' A : B ⊗[A] B →ₐ[A] B).Flat) :
    FormallyUnramified A B := by
  refine (Algebra.formallyUnramified_iff A B).2 ?_
  rw [KaehlerDifferential, Ideal.cotangent_subsingleton_iff]
  let I : Ideal (B ⊗[A] B) := KaehlerDifferential.ideal A B
  letI : Algebra (B ⊗[A] B) B := (lmul' A).toRingHom.toAlgebra
  letI : Module.Flat (B ⊗[A] B) B := hflatMul
  let f : B ⊗[A] B →ₐ[B ⊗[A] B] B := { lmul' A with commutes' := fun _ ↦ rfl }
  have hsurj : Function.Surjective f := by
    intro b
    exact ⟨1 ⊗ₜ[A] b, by simp [f]⟩
  let e : (B ⊗[A] B ⧸ I) ≃ₐ[B ⊗[A] B] B :=
    by
      simpa [I, KaehlerDifferential.ideal] using
        (Ideal.quotientKerAlgEquivOfSurjective hsurj)
  letI : I.Pure := Module.Flat.of_linearEquiv e.toLinearEquiv
  simpa [I] using Ideal.isIdempotentElem_of_pure I

end Algebra.FormallyUnramified

/-- If the tensor-square multiplication map is flat, then the module of Kähler differentials
`Ω[B⁄A]` is trivial. This is the source-facing form of Lemma `15.105.12`. -/
theorem subsingleton_kaehlerDifferential_of_tensorSquareMul_flat
    (hflatMul : (lmul' A : B ⊗[A] B →ₐ[A] B).Flat) :
    Subsingleton Ω[B⁄A] :=
  (Algebra.formallyUnramified_iff A B).1 <|
    Algebra.FormallyUnramified.of_tensorSquareMul_flat hflatMul

end

/-! ### Lemma_15_105_13 (from Chap15) -/
open scoped TensorProduct
open Algebra.TensorProduct

universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/- Domain-style sampling for Lemma 15.105.13:
- primary domain: finite-type and finite-presentation criteria for unramified and étale
  commutative algebra maps;
- sampled owner declarations:
  `Algebra.FormallyUnramified.of_tensorSquareMul_flat`,
  `WeaklyEtale`,
  `Algebra.Unramified`,
  `Algebra.Etale.of_formallyUnramified_of_flat`,
  `Algebra.IsWeaklyEtale`;
- best owner abstraction: this file is `bridge/view`, taking the tensor-square flatness criterion
  from Lemma `15.105.12` to the canonical owners `Algebra.Unramified` and `Algebra.Etale`;
- primitive data: flatness of the tensor-square multiplication map `lmul' A`, plus the standard
  finiteness and flatness owner assumptions;
- derived API: the source-facing conclusions that `A → B` is unramified or étale.

There is no new owner to define here: the file should reuse the canonical owner classes directly
and keep only the source-facing bridge theorems.
-/

/-- Lemma 15.105.13 (1): if the tensor-square multiplication map `B ⊗[A] B → B` is flat and
`A → B` is of finite type, then `A → B` is unramified. -/
theorem unramified_of_tensorSquareMul_flat_of_finiteType [Algebra.FiniteType A B]
    (hflatMul : (lmul' A : B ⊗[A] B →ₐ[A] B).Flat) :
    Algebra.Unramified A B := by
  letI : Algebra.FormallyUnramified A B :=
    Algebra.FormallyUnramified.of_tensorSquareMul_flat hflatMul
  exact ⟨inferInstance, inferInstance⟩

/-- Lemma 15.105.13 (2): if the tensor-square multiplication map `B ⊗[A] B → B` is flat and
`A → B` is flat of finite presentation, then `A → B` is étale. -/
theorem etale_of_tensorSquareMul_flat_of_finitePresentation_of_flat
    [Algebra.FinitePresentation A B] [Module.Flat A B]
    (hflatMul : (lmul' A : B ⊗[A] B →ₐ[A] B).Flat) :
    Algebra.Etale A B := by
  letI : Algebra.FormallyUnramified A B :=
    Algebra.FormallyUnramified.of_tensorSquareMul_flat hflatMul
  exact Algebra.Etale.of_formallyUnramified_of_flat

/-- Lemma 15.105.13 (3): in particular, a weakly étale ring map of finite presentation is
étale. -/
theorem etale_of_isWeaklyEtale_of_finitePresentation
    [Algebra.FinitePresentation A B] [Algebra.IsWeaklyEtale A B] :
    Algebra.Etale A B := by
  letI : Algebra.FormallyUnramified A B :=
    Algebra.FormallyUnramified.of_tensorSquareMul_flat
      ‹Algebra.IsWeaklyEtale A B›.flat_tensorSquareMultiplication
  exact Algebra.Etale.of_formallyUnramified_of_flat

end

/-! ### Lemma_15_105_14 (from Chap15) -/
open CategoryTheory MorphismProperty
open CommRingCat
open scoped TensorProduct

universe u v

namespace RingHom

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- An `R`-algebra map `f : R →+* S` is a filtered colimit of weakly étale `R`-algebras. This
thin source-facing wrapper hides the same-universe `ULift` bookkeeping needed to express the
canonical owner
`CategoryTheory.MorphismProperty.ind (RingHom.toMorphismProperty (fun f ↦ Algebra.IsWeaklyEtale _ _))`. -/
abbrev IsFilteredColimitOfWeaklyEtale (f : R →+* S) : Prop :=
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra R (ULift S) := ULift.algebra
  let _ : Algebra (ULift.{v} R) (ULift S) := ULift.algebra' R (ULift S)
  ind.{max u v, max u v, max u v + 1}
    (toMorphismProperty fun {R S} [CommRing R] [CommRing S] (f : R →+* S) ↦
      let _ : Algebra R S := f.toAlgebra
      Algebra.IsWeaklyEtale R S)
    (ofHom (algebraMap (ULift.{v} R) (ULift S)))

end

end RingHom

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/- Domain-style sampling for Lemma 15.105.14:
- primary domain: weakly étale commutative algebra and filtered-colimit presentations of ring maps;
- sampled owner declarations:
  `Algebra.IsWeaklyEtale`,
  `CategoryTheory.MorphismProperty.ind`,
  `RingHom.toMorphismProperty`,
  `RingHom.IsFilteredColimitOfWeaklyEtale`,
  `RingHom.algebraMap_isFilteredColimitOfEtale_of_isColimit`;
- best owner abstraction: the filtered-colimit hypothesis is the source-facing ring-hom owner
  `(algebraMap A B).IsFilteredColimitOfWeaklyEtale`, whose hidden core/canonical content is
  `CategoryTheory.MorphismProperty.ind (RingHom.toMorphismProperty (fun f ↦ Algebra.IsWeaklyEtale _ _))`;
- primitive data: the owner class `Algebra.IsWeaklyEtale` on each stage map;
- derived API: the source-facing closure statement that the colimit map `A → B` is weakly étale.

This file should therefore expose the filtered-colimit hypothesis through the ring-hom owner
`RingHom.IsFilteredColimitOfWeaklyEtale`, rather than through a raw `toMorphismProperty ... .ind`
term in theorem statements.
-/

-- Proof sketch: a localization map is étale by the canonical mathlib instance
-- `Algebra.Etale.of_isLocalizationAway` in the away-localization case, and more generally the
-- Stacks lemma allows one to view localizations as weakly étale directly. The weakly étale
-- statement then follows from the defining flatness properties of localization.
/-- Lemma 15.105.14 (1): if `B` is a localization of `A`, then the ring map `A → B` is weakly
étale. -/
theorem isWeaklyEtale_of_isLocalization (M : Submonoid A) [IsLocalization M B] :
    Algebra.IsWeaklyEtale A B := sorry

/-- Lemma 15.105.14 (2): every étale ring map `A → B` is weakly étale. -/
instance isWeaklyEtale_of_etale [Algebra.Etale A B] :
    Algebra.IsWeaklyEtale A B := sorry

-- Proof sketch: filtered colimits preserve flatness of the structural map `A → B`, and the
-- tensor-square multiplication map of the colimit is the filtered colimit of the corresponding
-- tensor-square multiplication maps of the stages. Since each stage is weakly étale, both
-- flatness conditions pass to the colimit.
/-- Lemma 15.105.14 (3): a filtered colimit of weakly étale `A`-algebras is weakly étale over
`A`. -/
theorem isWeaklyEtale_of_isFilteredColimitOfWeaklyEtale
    (hcolim : (algebraMap A B).IsFilteredColimitOfWeaklyEtale) :
    Algebra.IsWeaklyEtale A B := sorry

/-- If `A → B` is a filtered colimit of étale `A`-algebras, then it is weakly étale. -/
theorem isWeaklyEtale_of_isFilteredColimitOfEtale
    (hcolim : (algebraMap A B).IsFilteredColimitOfEtale) :
    Algebra.IsWeaklyEtale A B := sorry

end

/-! ### Lemma_15_105_15 (from Chap15) -/
open scoped TensorProduct
open IntermediateField

universe u

section

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/- Domain triage:
- primary domain: field extensions viewed through the weakly étale / formally unramified tensor
  square criterion;
- source-facing layer: the Stacks consequence that flatness of `L ⊗[K] L → L` forces `L/K`
  to be separable;
- sampled core/canonical owners:
  `tensorSquareMul_flat_of_faithfullyFlat`,
  `Algebra.FormallyUnramified.of_tensorSquareMul_flat`,
  `Algebra.FormallyUnramified.isSeparable`,
  `IntermediateField.isSeparable_adjoin_simple_iff_isSeparable`;
- primitive data: flatness of the tensor-square multiplication map;
- derived API: separability of each simple intermediate field `K⟮x⟯`, hence of `L/K`.

The refinement stays source-facing. The public theorem is still the field-theoretic conclusion,
but its proof now routes entirely through the canonical owner abstractions instead of a bespoke
local argument shell.
-/

-- Proof sketch: first descend the flatness hypothesis along finitely generated intermediate
-- subextensions, then use the finite-type criterion that formal unramifiedness of a field
-- extension is equivalent to separability; algebraicity is absorbed by the canonical separability
-- class for field extensions.
/-- Lemma 15.105.15: if the multiplication map `L ⊗[K] L → L` is flat, then `L/K` is an
algebraic separable extension. In mathlib this is expressed by the canonical class
`Algebra.IsSeparable K L`. -/
theorem isSeparable_of_flat_tensorSquareMultiplication
    (hflat : (Algebra.TensorProduct.lmul' K : L ⊗[K] L →ₐ[K] L).Flat) :
    Algebra.IsSeparable K L := by
  refine ⟨fun x ↦ ?_⟩
  let M : IntermediateField K L := K⟮x⟯
  letI : Algebra M L := M.val.toAlgebra
  letI : IsScalarTower K M L := inferInstance
  have hML : (algebraMap M L).FaithfullyFlat := by
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    exact Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hMflat : (Algebra.TensorProduct.lmul' K : M ⊗[K] M →ₐ[K] M).Flat :=
    Algebra.tensorSquareMul_flat_of_faithfullyFlat hML hflat
  letI : Algebra.FormallyUnramified K M :=
    Algebra.FormallyUnramified.of_tensorSquareMul_flat hMflat
  letI : Algebra.EssFiniteType K M := (IntermediateField.essFiniteType_iff).2 <|
    by simpa [M] using IntermediateField.fg_adjoin_finset ({x} : Finset L)
  have : Algebra.IsSeparable K M := Algebra.FormallyUnramified.isSeparable K M
  exact (isSeparable_adjoin_simple_iff_isSeparable K L).mp <| by simpa [M] using this

end

/-! ### Lemma_15_105_16 (from Chap15) -/
open scoped TensorProduct

universe u v

section TFAE

variable {K B : Type u} [Field K] [CommRing B] [Algebra K B]

/- Domain-style sampling for Lemma 15.105.16:
- primary domain: weakly étale algebras over a field and their filtered-colimit presentations by
  étale algebras;
- sampled owner declarations:
  `Algebra.IsWeaklyEtale`,
  `Algebra.Etale`,
  `RingHom.IsFilteredColimitOfEtale`,
  `Subalgebra.fg_iff_finiteType`;
- best owner abstraction: `Algebra.IsWeaklyEtale K B` is the core/canonical owner on the map
  `K → B`, while `(algebraMap K B).IsFilteredColimitOfEtale` is the source-facing
  filtered-colimit bridge already owned upstream in Chapter 10;
- primitive data: the owner class `Algebra.IsWeaklyEtale K B` and finite generation of a
  `K`-subalgebra expressed by `A.FG`;
- derived API: the TFAE below and the later `FiniteType` specialization obtained from
  `Subalgebra.fg_iff_finiteType`.

This file keeps the source-facing `FG` theorem as the owner statement for finitely generated
subalgebras and leaves `FiniteType` as a downstream bridge, rather than maintaining parallel public
copies of the same result.
-/

-- Proof sketch: over a field, every `K`-algebra is flat over `K`, so flatness of the tensor-square
-- multiplication map is equivalent to weakly étaleness. The implication from a filtered colimit of
-- étale `K`-algebras to weakly étale is Lemma `15.105.14`, while the converse is proved by showing
-- that every finitely generated `K`-subalgebra is étale and then expressing `B` as the filtered
-- colimit of its finitely generated `K`-subalgebras.
/-- Lemma 15.105.16: for a `K`-algebra `B`, the following are equivalent: the multiplication map
`B ⊗[K] B → B` is flat, the structure map `K → B` is weakly étale, and `B` is a filtered colimit
of étale `K`-algebras. -/
theorem weaklyEtale_over_field_tfae :
    List.TFAE
      [ (Algebra.TensorProduct.lmul' K : B ⊗[K] B →ₐ[K] B).Flat,
        Algebra.IsWeaklyEtale K B,
        (algebraMap K B).IsFilteredColimitOfEtale ] := sorry

end TFAE

section

variable {K : Type u} {B : Type v} [Field K] [CommRing B] [Algebra K B]

-- Proof sketch: assume `K → B` is weakly étale. For a finitely generated `K`-subalgebra `A ⊆ B`,
-- every localization `B_𝔮` at a prime is weakly étale over `K`, hence a separable algebraic field
-- extension of `K`. The residue fields of the minimal primes of `A` are therefore finite
-- separable over `K`, so `A` is reduced and zero-dimensional. A reduced finite type `K`-algebra of
-- dimension zero is a finite product of finite separable field extensions, hence étale over `K`.
/-- Every finitely generated `K`-subalgebra of a weakly étale `K`-algebra is étale over `K`. -/
theorem etale_of_fg_subalgebra_of_isWeaklyEtale
    [Algebra.IsWeaklyEtale K B] (A : Subalgebra K B) (hA : A.FG) :
    Algebra.Etale K A := sorry

end

/-! ### Lemma_15_105_17 (from Chap15) -/
universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/- Domain-style sampling for Lemma 15.105.17:
- primary domain: weakly étale commutative algebra and the induced residue-field extensions along
  primes in a fiber;
- sampled owner declarations:
  `Algebra.IsWeaklyEtale`,
  `Algebra.IsWeaklyEtale.baseChange`,
  `weaklyEtale_over_field_tfae`,
  `Ideal.primesOver`;
- best owner abstraction: the theorem is `source-facing`, but the prime-over-prime input should be
  expressed by the canonical owner set `p.primesOver B` rather than by a raw ideal plus separate
  `[IsPrime]` and `[LiesOver]` arguments;
- primitive data: the weakly étale owner on `A → B`, the prime `p : Ideal A`, and the chosen
  prime over `p` packaged as `q : p.primesOver B`;
- derived API: the induced `p.ResidueField`-algebra structure on `q.1.ResidueField`, together
  with the algebraicity and separability assertions and their atomic projection lemmas.

Source/core/bridge triage:
- `source-facing`: `residueField_isAlgebraic_and_separable_of_isWeaklyEtale`;
- `core/canonical`: `Algebra.IsWeaklyEtale`, `Ideal.primesOver`, and `Ideal.ResidueField`;
- `bridge/view`: base change to the fiber over `p` via `Algebra.IsWeaklyEtale.baseChange`,
  followed by the field-case filtered-colimit characterization `weaklyEtale_over_field_tfae`.
-/

-- Proof sketch: base change the weakly étale map `A → B` along `A → κ(p)` using Lemma
-- `15.105.7`, so `κ(p) → B ⊗[A] κ(p)` is weakly étale. By Lemma `15.105.16`, the fiber algebra is
-- a filtered colimit of étale `κ(p)`-algebras. For a prime `q` over `p`, the residue field
-- `κ(q)` is the residue field of a prime of this fiber algebra, so Algebra Lemma `10.143.4`
-- yields algebraicity and separability over `κ(p)`.
/-- Lemma 15.105.17: if `A → B` is weakly étale, then for every prime `q` of `B` lying over a
prime `p` of `A`, the induced residue-field extension `κ(q) / κ(p)` is algebraic and separable. -/
theorem residueField_isAlgebraic_and_separable_of_isWeaklyEtale
    [Algebra.IsWeaklyEtale A B]
    (p : Ideal A) [p.IsPrime] (q : p.primesOver B) :
    Algebra.IsAlgebraic p.ResidueField q.1.ResidueField ∧
      Algebra.IsSeparable p.ResidueField q.1.ResidueField := sorry

/-- Companion to
`residueField_isAlgebraic_and_separable_of_isWeaklyEtale`: the induced residue-field extension
along a weakly étale map is algebraic. -/
theorem residueField_isAlgebraic_of_isWeaklyEtale
    [Algebra.IsWeaklyEtale A B]
    (p : Ideal A) [p.IsPrime] (q : p.primesOver B) :
    Algebra.IsAlgebraic p.ResidueField q.1.ResidueField := by
  exact (residueField_isAlgebraic_and_separable_of_isWeaklyEtale p q).1

/-- Companion to
`residueField_isAlgebraic_and_separable_of_isWeaklyEtale`: the induced residue-field extension
along a weakly étale map is separable. -/
theorem residueField_isSeparable_of_isWeaklyEtale
    [Algebra.IsWeaklyEtale A B]
    (p : Ideal A) [p.IsPrime] (q : p.primesOver B) :
    Algebra.IsSeparable p.ResidueField q.1.ResidueField := by
  exact (residueField_isAlgebraic_and_separable_of_isWeaklyEtale p q).2

end

/-! ### Lemma_15_105_18 (from Chap15) -/
universe u v

section

variable (A : Type u) [CommRing A]

/- Domain-style sampling:
- primary domain: commutative algebra of weak dimension, flatness criteria for ideals and
  submodules, and the valuation-ring criterion on prime localizations;
- sampled owner declarations:
  `HasWeakDimensionLE`,
  `Module.Flat`,
  `ValuationRing`,
  `ValuationRing.iff_local_bezout_domain`;
- best owner abstraction: clause `(1)` should use the chapter owner `HasWeakDimensionLE A 1`,
  clauses `(2)` through `(4)` should stay as the source-facing flatness conditions on ideals and
  `A`-modules, with clause `(4)` quantified over the canonical owner `ModuleCat A`; clause `(5)`
  should use the canonical mathlib owner `ValuationRing` directly rather than a one-off local
  wrapper;
- primitive vs. derived:
  primitive data is only the ring `A` together with the owner predicates on ideals, submodules,
  and prime localizations;
  derived API is the TFAE bridge among these five formulations, so no extra public packaging is
  warranted here.

Source/core/bridge triage:
- `source-facing`: the five-way equivalence matching the Stacks lemma;
- `core/canonical`: `HasWeakDimensionLE`, `Module.Flat`, `PrimeSpectrum`, `Localization.AtPrime`,
  and `ValuationRing`;
- `bridge/view`: the theorem itself, whose last clause presents the Stacks “`A_p` is a valuation
  ring” wording via the minimal existential witness needed to supply the domain instance required
  by the canonical owner `ValuationRing`.
-/

-- Proof sketch: `(1) → (2)` uses the short exact sequence `0 → I → A → A ⧸ I → 0` and the
-- characterization of weak dimension `≤ 1` by vanishing of higher tors. `(2) ↔ (3)` is the
-- filtered-colimit argument reducing arbitrary ideals to finitely generated ones. `(2) → (4)`
-- writes a flat module as a filtered colimit of finite free modules and filters submodules by
-- ideals. `(4) → (1)` resolves an arbitrary module by a free module with flat kernel. `(1) → (5)`
-- localizes weak dimension `≤ 1` and uses the local criterion that finitely generated flat ideals
-- in a local ring are principal, giving a valuation ring on each canonical prime localization.
-- `(5) → (3)` checks finitely generated ideals after localizing at primes and applies the local
-- criterion for flatness.
/-- Lemma 15.105.18: for a commutative ring `A`, the following are equivalent: `A` has weak
dimension at most `1`; every ideal of `A` is flat; every finitely generated ideal of `A` is flat;
every submodule of a flat `A`-module is flat; and every localization `Aₚ` at a prime ideal is a
valuation ring. -/
theorem weakDimensionLEOne_idealFlat_fgIdealFlat_submoduleFlat_localizations_valuationRing_tfae :
    List.TFAE
      [ HasWeakDimensionLE A 1
      , ∀ I : Ideal A, Module.Flat A I
      , ∀ I : Ideal A, I.FG → Module.Flat A I
      , ∀ (M : ModuleCat.{v} A) [Module.Flat A M] (N : Submodule A M),
          Module.Flat A N
      , ∀ p : PrimeSpectrum A,
          ∃ (_ : IsDomain (Localization.AtPrime p.asIdeal)),
            ValuationRing (Localization.AtPrime p.asIdeal)
      ] := sorry

end

/-! ### Lemma_15_105_19 (from Chap15) -/
universe u v w

section

variable {J : Type u}

/-
Domain-style sampling:
- primary domain: commutative algebra of weak dimension, valuation rings, and localization of
  product rings;
- sampled owner declarations:
  `HasWeakDimensionLE`,
  `ValuationRing`,
  `IsFractionRing`,
  `IsLocalization`;
- best owner abstraction:
  part `(1)` is genuinely source-facing, but its public owner is still the chapter class
  `HasWeakDimensionLE`, so the target surface should provide that owner directly for the product
  ring;
  part `(2)` is exact-interface reuse of the canonical product-localization `IsLocalization`
  instance, so it should be exposed by direct instance synthesis rather than restated behind a
  duplicate local theorem name.

Primitive-vs-derived split:
- primitive data: the family of valuation rings `A j`, and for part `(2)` the family of fraction
  rings `K j` together with the canonical `CommRing`, `Algebra`, and `IsFractionRing` instances;
- derived API: the product weak-dimension statement in part `(1)`, and the product localization
  statement in part `(2)`, which is already owned canonically by `IsLocalization`.

Source/core/bridge triage:
- `source-facing`: part `(1)`, the Stacks weak-dimension statement for products of valuation
  rings;
- `core/canonical`: `HasWeakDimensionLE`, `ValuationRing`, `IsFractionRing`, and
  `IsLocalization`;
- `bridge/view`: part `(2)` is only a direct specialization of the canonical localization owner,
  so it should stay as direct instance synthesis rather than a parallel wrapper theorem.
-/

variable {A : J → Type v}
variable [∀ j, CommRing (A j)] [∀ j, IsDomain (A j)] [∀ j, ValuationRing (A j)]

-- Proof sketch: apply Lemma `15.105.18` to the product ring `∏ j, A j`. A finitely generated ideal
-- in a product ring is the product of its component ideals by Proposition `10.89.2`, each component
-- ideal in a valuation ring is principal by Lemma `10.50.15`, and principal idempotent ideals are
-- direct summands, hence flat. This gives weak dimension at most `1`.
/-- Lemma 15.105.19 (1): the product of a family of valuation rings has weak dimension at most
`1`. -/
instance : HasWeakDimensionLE ((j : J) → A j) 1 := by
  sorry

variable {K : J → Type w}
variable [∀ j, CommRing (K j)] [∀ j, Algebra (A j) (K j)] [∀ j, IsFractionRing (A j) (K j)]

-- Proof sketch: for each factor `j`, `K j` is the localization of `A j` at the nonzerodivisors of
-- `A j`. The canonical product-localization `IsLocalization` instance then identifies the product
-- `∀ j, K j` as the localization of `∀ j, A j` at the product submonoid of componentwise
-- nonzerodivisors. The field structure on each fraction ring is derived from `IsFractionRing`, so
-- it does not belong in the public hypotheses for this direct localization recall.
/- Lemma 15.105.19 (2): if each `K j` is a fraction ring of `A j`, then the canonical map
`((j : J) → A j) → ((j : J) → K j)` is the localization at the product submonoid of componentwise
nonzerodivisors. This is direct instance inference from the canonical product-localization owner
in mathlib. -/
#synth IsLocalization (Submonoid.pi Set.univ fun j ↦ nonZeroDivisors (A j)) ((j : J) → K j)

end

/-! ### Lemma_15_105_20 (from Chap15) -/
open CategoryTheory Limits
open CommRingCat

universe u

section

variable {A : Type u} {K : Type u} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
variable [IsFractionRing A K] [IsIntegrallyClosed A]

/-
Domain-style sampling:
- primary domain: commutative algebra of normal domains, valuation-theoretic presentations of
  fraction fields, and cartesian squares in `CommRingCat`;
- sampled owner declarations:
  `CategoryTheory.IsPullback`,
  `HasWeakDimensionLE`,
  `RingHom.Flat`,
  `CategoryTheory.Epi`;
- best owner abstraction: the source-facing object here is the cartesian square over the canonical
  map `A → K`, and the correct square owner is `IsPullback` itself rather than a new local
  package. The Stacks lemma is a single existence statement, so the lower-left weak-dimension
  condition and the flat/injective/epimorphism properties of the bottom map belong on the same
  witness instead of being split into parallel existential theorems.

Primitive-vs-derived split:
- primitive data: rings `V` and `L`, morphisms `i`, `j`, `k`, and the pullback witness
  `IsPullback i (ofHom (algebraMap A K)) k j` together with the properties
  `HasWeakDimensionLE V 1`, `k.hom.Flat`, `Function.Injective k.hom`, and `Epi k`;
- derived API: forgetful consequences such as the existence of the cartesian square alone are
  derived from the single source-facing witness and do not need separate public owners here.

Source/core/bridge triage:
- `source-facing`: the Stacks existence assertion for one cartesian square over `A → K` carrying
  all listed properties at once;
- `core/canonical`: `IsPullback`, `HasWeakDimensionLE`, `Function.Injective`, and `Epi`;
- `bridge/view`: no additional bridge object is needed here, because the categorical pullback
  square is already the owner abstraction used downstream.
-/

-- Proof sketch: for each `x : K` outside the image of `A`, choose a valuation subring `Vₓ ⊆ K`
-- containing `A` but not `x` by Lemma `10.50.11`. Take `V` to be the product of these valuation
-- rings and `L` the product of the ambient field `K`; the induced square with `A → K` is
-- cartesian by the intersection description of a normal domain inside its fraction field. Lemma
-- `15.105.19` gives weak dimension at most `1` for this product and identifies `V → L` as a
-- localization. Localizations are flat and epimorphisms, and here the map is also injective
-- because each component `Vₓ → K` is injective.
/-- Lemma 15.105.20: if `A` is a normal domain with fraction field `K`, then there exists a
cartesian square
\[
\require{AMScd}
\begin{CD}
A @>>> K \\
@VVV @VVV \\
V @>>> L
\end{CD}
\]
of commutative rings where `V` has weak dimension at most `1` and the bottom map `V → L` is flat,
injective, and an epimorphism. -/
theorem exists_cartesian_square_over_fractionField_with_weakDimensionLEOne_and_flat_injective_epi :
    ∃ (V L : CommRingCat.{u}) (i : of A ⟶ V) (k : V ⟶ L) (j : of K ⟶ L),
      IsPullback i (ofHom (algebraMap A K)) k j ∧
        HasWeakDimensionLE V 1 ∧
        k.hom.Flat ∧ Function.Injective k.hom ∧ Epi k := sorry

end

/-! ### Lemma_15_105_21 (from Chap15) -/
universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/- Domain-style sampling:
- primary domain: commutative algebra of integrally closed extensions and flat epimorphisms of
  rings;
- sampled owner declarations:
  `IsIntegrallyClosedIn`,
  `HasWeakDimensionLE`,
  `Algebra.IsEpi`,
  `RingHom.surjective_iff_epi_and_finite`;
- best owner abstraction: this lemma is `source-facing`, but its epimorphism input should use the
  algebra-level owner `Algebra.IsEpi A B`; the category-theoretic condition
  `Epi (CommRingCat.ofHom (algebraMap A B))` is only a bridge, via `CommRingCat.epi_iff_epi`;
- primitive vs. derived:
  primitive data is the weak-dimension hypothesis on `A`, flatness of `B` over `A`, injectivity
  of `algebraMap A B`, and the owner predicate `Algebra.IsEpi A B`;
  derived API is the conclusion `IsIntegrallyClosedIn A B`, so no extra local wrapper around ring
  epimorphisms is warranted here.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma asserting integral closedness of `A` inside `B`;
- `core/canonical`: `IsIntegrallyClosedIn`, `HasWeakDimensionLE`, `Module.Flat`, `Algebra.IsEpi`;
- `bridge/view`: the category-theoretic epimorphism formulation in `CommRingCat`, used only when a
  categorical pushout/pullback argument is needed.
-/

-- Proof sketch: if `x : B` is integral over `A`, let `A' := A[x] ⊆ B`. By finite generation of
-- simple integral extensions, `A'` is finite over `A`. Since `A` has weak dimension at most `1`
-- and `B` is flat over `A`, Lemma `15.105.18` gives flatness of the finite `A`-submodule `A'`.
-- The multiplication map `A' ⊗[A] A' → A'` factors through `B`, and injectivity of `A → B`
-- together with the ring-epimorphism hypothesis forces `A → A'` to be an epimorphism. Then
-- `RingHom.surjective_iff_epi_and_finite` makes `A → A'` surjective, so `x` comes from `A`.
/-- Lemma 15.105.21: if `A` has weak dimension at most `1` and `A → B` is a flat, injective
epimorphism of commutative rings, then `A` is integrally closed in `B`. -/
theorem isIntegrallyClosedIn_of_hasWeakDimensionLEOne_of_flat_of_injective_of_epi
    [HasWeakDimensionLE A 1] [Module.Flat A B]
    (hinj : Function.Injective (algebraMap A B)) [Algebra.IsEpi A B] :
    IsIntegrallyClosedIn A B := sorry

end

/-! ### Lemma_15_105_22 (from Chap15) -/
open scoped TensorProduct

universe u v w

section

variable {A : Type u} {B : Type v} {K : Type w}
variable [CommRing A] [CommRing B] [Field K]
variable [Algebra A B] [Algebra A K] [IsFractionRing A K]
variable [IsIntegrallyClosed A] [Algebra.IsWeaklyEtale A B]

/- Domain-style sampling:
- primary domain: commutative algebra of normal domains, weakly étale base change, and integral
  closedness in tensor-product overrings of the fraction field;
- sampled owner declarations:
  `IsIntegrallyClosedIn`,
  `Algebra.IsWeaklyEtale`,
  `hasWeakDimensionLE_of_isWeaklyEtale`,
  `isIntegrallyClosedIn_of_hasWeakDimensionLEOne_of_flat_of_injective_of_epi`;
- best owner abstraction: this theorem is `source-facing`, but its public statement should remain
  the canonical owner predicate `IsIntegrallyClosedIn B (B ⊗[A] K)`. The weak-dimension transfer,
  weakly étale base change, and flat-epimorphism integrally closedness results already have owner
  declarations upstream, so the cartesian square from Lemma `15.105.20` is only bridge data and
  should not be repackaged locally;
- primitive data: the normal domain `A`, its fraction field `K`, and the weakly étale owner
  `Algebra.IsWeaklyEtale A B`;
- derived API: the weak-dimension and epimorphism facts after tensor base change, and the final
  `IsIntegrallyClosedIn` conclusion.

Source/core/bridge triage:
- `source-facing`: `isIntegrallyClosedIn_tensorProduct_fractionField_of_isWeaklyEtale`;
- `core/canonical`: `IsIntegrallyClosedIn`, `Algebra.IsWeaklyEtale`, `HasWeakDimensionLE`,
  `Algebra.IsEpi`;
- `bridge/view`: the cartesian-square witness from Lemma `15.105.20`, together with the tensor
  base-change bridge from Lemma `10.107.3` and the weakly étale base-change theorem
  `Algebra.IsWeaklyEtale.baseChange`.
-/

-- Proof sketch: choose the cartesian square `A → K`, `V → L` from Lemma `15.105.20`. Base change
-- the weakly étale map `A → B` along `A → V`; by `Algebra.IsWeaklyEtale.baseChange`, the map
-- `V → B ⊗[A] V` is weakly étale, so `hasWeakDimensionLE_of_isWeaklyEtale` upgrades the weak
-- dimension bound on `V` to one on `B ⊗[A] V`. The bottom map `B ⊗[A] V → B ⊗[A] L` remains a
-- flat, injective epimorphism after tensor base change, using the canonical epimorphism base
-- change theorem `algebra_isEpi_tensorProduct_of_isEpi`; then Lemma `15.105.21` gives
-- `IsIntegrallyClosedIn (B ⊗[A] V) (B ⊗[A] L)`. The original cartesian square is bridge data used
-- only to descend this owner statement to `IsIntegrallyClosedIn B (B ⊗[A] K)`.
/-- Lemma 15.105.22: if `A` is a normal domain with fraction field `K` and `A → B` is weakly
étale, then `B` is integrally closed in `B ⊗[A] K`. -/
theorem isIntegrallyClosedIn_tensorProduct_fractionField_of_isWeaklyEtale :
    IsIntegrallyClosedIn B (B ⊗[A] K) := sorry

end

/-! ### Lemma_15_105_23 (from Chap15) -/
open IsLocalRing

universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-
Domain-style sampling for Lemma 15.105.23:
- primary domain: local commutative algebra of integral extensions of henselian and strictly
  henselian local rings, together with the induced residue-field extension;
- sampled owner declarations:
  `HenselianLocalRing`,
  `StrictHenselianLocalRing`,
  `finite_local_henselianLocalRing`,
  `algebraMap_isLocalHom_of_finite_local`,
  `IsLocalHom (algebraMap A B)`,
  `IsLocalRing.ResidueField.algebraOfIsIntegral`,
  `Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed`,
  `Algebra.IsAlgebraic.isSepClosed`;
- best owner abstraction: the integral-domain transfer statements here are `source-facing`, while
  the local/integral and residue-field-purely-inseparable steps are `bridge/view` results that
  should expose the canonical owner classes above rather than source-specific packages;
- primitive data: the integral `A`-algebra structure on the domain `B`;
- derived API: the henselian local structure on `B`, the locality of `A → B`, and the resulting
  purely inseparable residue-field extension.

Source/core/bridge triage:
- `source-facing`:
  `henselianLocalRing_of_henselianLocalRing_of_integral_domain`,
  `strictHenselianLocalRing_of_strictHenselianLocalRing_of_integral_domain`;
- `core/canonical`: `HenselianLocalRing`, `StrictHenselianLocalRing`, `IsLocalHom`,
  `finite_local_henselianLocalRing`, `algebraMap_isLocalHom_of_finite_local`,
  `IsPurelyInseparable`;
- `bridge/view`: the canonical residue-field algebraicity instance for local integral maps and the
  canonical bridge theorems
  `algebraMap_isLocalHom_of_isLocalRing_of_integral` and
  `residueField_isPurelyInseparable_of_isSepClosed_of_localHom_of_integral`, which expose the
  induced residue-field extension through the local-map interface and feed the source-facing
  corollaries below.
 -/

section LocalIntegralBridge

variable [IsLocalRing A] [IsLocalRing B] [Algebra.IsIntegral A B]

/-- An integral algebra map between local rings is a local ring homomorphism. -/
theorem algebraMap_isLocalHom_of_isLocalRing_of_integral :
    IsLocalHom (algebraMap A B) := by
  sorry

end LocalIntegralBridge

section ResidueFieldBridge

variable [IsLocalRing A] [IsSepClosed (ResidueField A)]
variable [IsLocalRing B] [IsLocalHom (algebraMap A B)] [Algebra.IsIntegral A B]

/-- The residue-field extension induced by an integral local homomorphism from a local ring with
separably closed residue field is purely inseparable. -/
theorem residueField_isPurelyInseparable_of_isSepClosed_of_localHom_of_integral :
    IsPurelyInseparable (ResidueField A) (ResidueField B) := by
  sorry

end ResidueFieldBridge

section Henselian

variable [HenselianLocalRing A]

-- Proof sketch: write `B` as a filtered colimit of finite `A`-subalgebras and apply the finite
-- henselian case to each stage. Since `B` is a domain, each finite local factor is forced to be
-- unique, and Lemma `10.154.8` upgrades the filtered colimit to a henselian local ring.
/-- Lemma 15.105.23 (1): if `A → B` is an integral ring map, `A` is henselian local, and `B` is a
domain, then `B` is a henselian local ring. -/
theorem henselianLocalRing_of_henselianLocalRing_of_integral_domain
    (A : Type u) [CommRing A] [Algebra A B] [HenselianLocalRing A] [Algebra.IsIntegral A B]
    [IsDomain B] : HenselianLocalRing B := sorry

/-- Lemma 15.105.23 (2): if `A → B` is an integral ring map, `A` is henselian local, and `B` is a
domain, then `A → B` is a local homomorphism. -/
theorem algebraMap_isLocalHom_of_henselianLocalRing_of_integral_domain [Algebra.IsIntegral A B]
    [IsDomain B] : IsLocalHom (algebraMap A B) := by
  let _ : HenselianLocalRing B :=
    henselianLocalRing_of_henselianLocalRing_of_integral_domain A
  exact algebraMap_isLocalHom_of_isLocalRing_of_integral

end Henselian

section StrictHenselian

variable [StrictHenselianLocalRing A]

/-- Lemma 15.105.23 (4): for an integral local homomorphism from a strictly henselian local ring,
the induced residue-field extension is purely inseparable. -/
theorem residueField_isPurelyInseparable_of_strictHenselianLocalRing_of_localHom_of_integral
    [IsLocalRing B] [IsLocalHom (algebraMap A B)] [Algebra.IsIntegral A B] :
    IsPurelyInseparable (ResidueField A) (ResidueField B) := by
  exact residueField_isPurelyInseparable_of_isSepClosed_of_localHom_of_integral

-- Proof sketch: once clause (1) gives that `B` is henselian local and clause (2) gives that
-- `A → B` is local, clause (4) upgrades the induced residue-field extension to a purely
-- inseparable extension. We then reuse the canonical algebraic-extension owner to conclude that
-- `ResidueField B` is separably closed.
/-- Lemma 15.105.23 (3): if `A` is strictly henselian in addition to the integral-domain
hypotheses, then `B` is strictly henselian. -/
theorem strictHenselianLocalRing_of_strictHenselianLocalRing_of_integral_domain
    (A : Type u) [CommRing A] [Algebra A B] [StrictHenselianLocalRing A] [Algebra.IsIntegral A B]
    [IsDomain B] :
    StrictHenselianLocalRing B := by
  let _ : HenselianLocalRing B :=
    henselianLocalRing_of_henselianLocalRing_of_integral_domain A
  let _ : IsLocalHom (algebraMap A B) :=
    algebraMap_isLocalHom_of_isLocalRing_of_integral
  let hPure : IsPurelyInseparable (ResidueField A) (ResidueField B) :=
    residueField_isPurelyInseparable_of_isSepClosed_of_localHom_of_integral
  let _ : Algebra.IsAlgebraic (ResidueField A) (ResidueField B) :=
    hPure.isAlgebraic
  let _ : IsSepClosed (ResidueField B) :=
    Algebra.IsAlgebraic.isSepClosed (F := ResidueField A) (E := ResidueField B)
  exact
    { toHenselianLocalRing := inferInstance
      toIsSepClosed := inferInstance }

end StrictHenselian

section IntegralClosure

variable {L : Type v} [Field L] [Algebra A L]

/-- The integral closure of a henselian local ring in a field is henselian local. -/
instance integralClosure_henselianLocalRing [HenselianLocalRing A] :
    HenselianLocalRing (integralClosure A L) := by
  let _ : Algebra.IsIntegral A (integralClosure A L) := IsIntegralClosure.isIntegral_algebra A L
  exact
    (henselianLocalRing_of_henselianLocalRing_of_integral_domain A :
      HenselianLocalRing (integralClosure A L))

/-- The integral closure of a strictly henselian local ring in a field is strictly henselian. -/
instance integralClosure_strictHenselianLocalRing [StrictHenselianLocalRing A] :
    StrictHenselianLocalRing (integralClosure A L) := by
  let _ : Algebra.IsIntegral A (integralClosure A L) := IsIntegralClosure.isIntegral_algebra A L
  exact
    (strictHenselianLocalRing_of_strictHenselianLocalRing_of_integral_domain A :
      StrictHenselianLocalRing (integralClosure A L))

end IntegralClosure

end
