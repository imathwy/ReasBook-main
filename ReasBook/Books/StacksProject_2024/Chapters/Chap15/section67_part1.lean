import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_67_1 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open ModuleCat.MonoidalCategory
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "Mod" => ModuleCat R
local notation "DMod" => DerivedCategory Mod
local notation "H" => homologyFunctor Mod
private abbrev single₀ : Mod ⥤ DMod := DerivedCategory.singleFunctor Mod (0 : ℤ)

/- Domain-style sampling for Definition 15.67.1:
- primary domain: tor-amplitude and finite tor dimension in the derived category `D(R)`;
- sampled owner declarations:
  `CategoryTheory.derivedTensorProduct`,
  `DerivedTensorProduct` notation `⊗[R]^L`,
  `DerivedCategory.singleFunctor`,
  `DerivedCategory.homologyFunctor`;
- best owner abstraction: this file is the `source-facing` owner for the tor-amplitude and
  finite-tor-dimension predicates on `D(R)`, while the derived tensor product itself is already
  canonically owned upstream by `derivedTensorProduct` and its notation;
- primitive vs. derived:
  primitive data are the derived object `K`, the interval bounds `a, b`, and the test module
  `M : ModuleCat R`;
  derived API is the existential finite-tor-dimension predicate and the module-level
  specializations;
- unlike projective and injective dimension, there is no separate upstream module-level canonical
  flat/tor-dimension invariant already available in mathlib or earlier Chapter 15 files, so the
  module predicates remain source-facing owners here rather than wrappers around a stricter owner;
- source/core/bridge triage:
  `source-facing`: `HasTorAmplitudeIn`, `HasFiniteTorDimension`;
  `core/canonical`: `derivedTensorProduct`, `⊗[R]^L`, `DerivedCategory.singleFunctor`, and `H`;
  `bridge/view`: the degree-zero embedding `(single₀).obj M : D(R)` of an `R`-module together with
    the module-level specializations `ModuleHasTorDimensionLE` and
    `ModuleHasFiniteTorDimension`. -/

/-- Definition 15.67.1 (1): an object `K` of `D(R)` has tor-amplitude in `[a, b]` if for every
`R`-module `M`, the homology of `K \otimes_R^{\mathbf L} M[0]` vanishes outside the interval
`[a, b]`. -/
def HasTorAmplitudeIn (K : DMod) (a b : ℤ) : Prop :=
  ∀ (M : Mod) (i : ℤ), i ∉ Set.Icc a b →
    IsZero ((H i).obj (K ⊗[R]^L (single₀.obj M)))

/-- Definition 15.67.1 (2): an object of `D(R)` has finite tor dimension if it has tor-amplitude
in some finite interval `[a, b]`. -/
def HasFiniteTorDimension (K : DMod) : Prop :=
  ∃ a b : ℤ, HasTorAmplitudeIn K a b

/-- An object of `D(R)` has finite tor dimension exactly when it has tor-amplitude in some finite
interval `[a, b]`. -/
theorem hasFiniteTorDimension_iff (K : DMod) :
    HasFiniteTorDimension K ↔ ∃ a b : ℤ, HasTorAmplitudeIn K a b :=
  Iff.rfl

/-- Tor-amplitude in a fixed finite interval implies finite tor dimension. -/
theorem HasTorAmplitudeIn.hasFiniteTorDimension
    {K : DMod} {a b : ℤ}
    (hK : HasTorAmplitudeIn K a b) :
    HasFiniteTorDimension K :=
  ⟨a, b, hK⟩

/-- Definition 15.67.1 (3): an `R`-module `M` has tor dimension at most `d` if the degree-zero
derived object `M[0]` has tor-amplitude in `[-d, 0]`. -/
abbrev ModuleHasTorDimensionLE (M : Mod) (d : ℕ) : Prop :=
  HasTorAmplitudeIn (single₀.obj M) (-(d : ℤ)) 0

/-- Definition 15.67.1 (4): an `R`-module has finite tor dimension if its degree-zero derived
object has finite tor dimension in `D(R)`. -/
abbrev ModuleHasFiniteTorDimension (M : Mod) : Prop :=
  HasFiniteTorDimension (single₀.obj M)

end

end CategoryTheory

/-! ### Lemma_15_67_2 (from Chap15) -/
noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

open CategoryTheory.Limits
open DerivedCategory

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

namespace CochainComplex

/- Domain-style sampling:
- primary domain: lower-bounded tor-amplitude in `D(R)` and the source-facing flatness of the
  syzygy `cokernel (K.dFrom (a - 1))` of a bounded-above flat cochain representative;
- sampled owner declarations:
  `HasTorAmplitudeGE`,
  `CochainComplex.IsKFlat`,
  `CochainComplex.IsTermwiseFlat`,
  `CochainComplex.minus`;
- source/core/bridge triage:
  `source-facing`: flatness of `cokernel (K.dFrom (a - 1))` under the source hypotheses on `K`;
  `core/canonical`: the chapter owners `HasTorAmplitudeGE (Q.obj K) a`, `K.IsKFlat`,
    `K.IsTermwiseFlat`, and `CochainComplex.minus (ModuleCat R) K`;
  `bridge/view`: exactness of the degree-zero tensor complexes computing lower tor-amplitude once
    `K` is known to be K-flat.

Primitive data are the bounded-above hypothesis on `K`, its termwise flatness, and the canonical
derived owner `HasTorAmplitudeGE (Q.obj K) a`. The exactness statements after tensoring with
degree-zero modules are derived bridge data, while representative-level K-flatness is supplied by
the existing bridge theorem `CochainComplex.isKFlat_of_boundedAbove_of_flat` rather than by any
parallel local wrapper.
-/

-- Proof sketch: apply `CochainComplex.isKFlat_of_boundedAbove_of_flat` to replace the
-- bounded-above termwise-flat representative by the canonical owner predicate `K.IsKFlat`. Then
-- lower-bounded tor-amplitude of `Q.obj K` gives exactness of `K ⊗ M` at degree `a - 1` for
-- every `R`-module `M`. Since the terms of `K` are flat and `K` is bounded above, the tail
-- ending in `cokernel (K.dFrom (a - 1))` is a flat resolution, so `Tor₁` of that cokernel with
-- any `M` vanishes. Apply the flatness criterion from Lemma `10.75.8`.
/-- Lemma 15.67.2: if the derived object represented by a bounded above cochain complex of flat
`R`-modules has tor-amplitude in `[a, ∞]`, then the cokernel of
`K.dFrom (a - 1) : K^(a - 1) ⟶ K^a` is flat. -/
theorem flat_cokernel_dFrom_of_boundedAbove_of_termwiseFlat_of_hasTorAmplitudeGE
    (K : CochainComplex (ModuleCat R) ℤ) (a : ℤ)
    (hbounded : CochainComplex.minus (ModuleCat R) K)
    (hFlat : K.IsTermwiseFlat)
    (hTor : HasTorAmplitudeGE (Q.obj K) a) :
    Module.Flat R ↑((cokernel (K.dFrom (a - 1)) : ModuleCat R)) := sorry

end CochainComplex

end

end CategoryTheory

/-! ### Lemma_15_67_3 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling:
- primary domain: tor-amplitude in the derived category of modules, expressed through bounded flat
  cochain representatives;
- sampled owner declarations:
  `CategoryTheory.HasTorAmplitudeIn`,
  `CochainComplex.IsTermwiseFlat`,
  `CategoryTheory.HasProjectiveAmplitudeIn`,
  `CategoryTheory.HasInjectiveAmplitudeIn`;
- best owner abstraction: `HasTorAmplitudeIn` is the source-facing/core predicate in this chapter,
  while existence of a bounded flat representative is bridge data describing that owner through a
  concrete model in `CochainComplex (ModuleCat R) ℤ`;
- primitive data: the representative complex `E`, its support conditions `E.IsStrictlyGE a` and
  `E.IsStrictlyLE b`, its termwise flatness `E.IsTermwiseFlat`, and an isomorphism
  `K ≅ DerivedCategory.Q.obj E`;
- derived API: the existential representative criterion for `HasTorAmplitudeIn`. The flat
  representative data should not be promoted to a parallel public owner, since the chapter already
  organizes the domain around tor-amplitude/projective-amplitude/injective-amplitude predicates.

Source/core/bridge triage:
- `source-facing`: tor-amplitude in `[a, b]` for an object of `D(R)`;
- `core/canonical`: `HasTorAmplitudeIn`;
- `bridge/view`: existence of a bounded termwise-flat cochain representative.
-/

-- Proof sketch: for the forward implication, use the tor-amplitude hypothesis together with the
-- bounded-above replacement from Derived Categories, Lemma `13.19.3`, then truncate below `a`
-- and apply Lemma `15.67.2` to identify the new degree-`a` term as flat. For the reverse
-- implication, compute derived tensor products using the flat representative and read off the
-- vanishing of homology outside `[a, b]` from the strict support of the representative complex.
/-- Lemma 15.67.3: an object `K^•` of `D(R)` has tor-amplitude in `[a, b]` if and only if it is
isomorphic in `D(R)` to a cochain complex `E^•` of flat `R`-modules with `E^i = 0` for
`i ∉ [a, b]`. -/
theorem hasTorAmplitudeIn_iff_exists_flat_representative
    (K : DMod) (a b : ℤ) :
    HasTorAmplitudeIn K a b ↔
      ∃ (E : Cpx) (_ : K ≅ DerivedCategory.Q.obj E),
        E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧ E.IsTermwiseFlat := sorry

end

end CategoryTheory

/-! ### Lemma_15_67_4 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => homologyFunctor (ModuleCat R)
local notation "Q" => DerivedCategory.Q
local notation "single₀" => singleFunctor (ModuleCat R) (0 : ℤ)

/- Domain-style sampling for Lemma 15.67.4:
- primary domain: lower-bounded tor-amplitude in `D(R)` and representative complexes computing
  derived tensor products with degree-zero modules;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.isGE_iff`,
  `CochainComplex.IsKFlat`,
  `CochainComplex.IsTermwiseFlat`;
- best owner abstraction: the lower-bound condition should be phrased through the canonical
  t-structure owner `IsGE` on each derived tensor product `K ⊗[R]^L M[0]`, while the
  representative side should expose the primitive complex predicates directly instead of bundling
  them into a new wrapper class;
- primitive vs. derived:
  primitive data are a representative complex `E`, its support condition `E.IsStrictlyGE a`, its
  K-flatness and termwise flatness, and an isomorphism `K ≅ Q.obj E`;
  derived API is the lower-bounded tor-amplitude predicate on `K`, together with the equivalence
  between that predicate and the existence of such a representative;
- source/core/bridge triage:
  `source-facing`: `HasTorAmplitudeGE` and the main equivalence theorem below;
  `core/canonical`: `DerivedCategory.IsGE`, `DerivedCategory.isGE_iff`, `CochainComplex.IsKFlat`,
    `CochainComplex.IsTermwiseFlat`, and `CochainComplex.IsStrictlyGE`;
  `bridge/view`: the use of `K ⊗[R]^L M[0]` to transport the derived-category lower-bound
    condition to a concrete K-flat flat representative.
-/

/-- An object of `D(R)` has tor-amplitude in `[a, ∞]` if tensoring with any degree-zero
`R`-module produces an object of the derived category lying in degrees `≥ a`. -/
def HasTorAmplitudeGE (K : DMod) (a : ℤ) : Prop :=
  ∀ M : ModuleCat R, (K ⊗[R]^L (single₀).obj M).IsGE a

/-- Finite-interval tor-amplitude in `[a, b]` implies lower tor-amplitude in `[a, ∞]`. -/
theorem HasTorAmplitudeIn.hasTorAmplitudeGE {K : DMod} {a b : ℤ}
    (hK : HasTorAmplitudeIn K a b) :
    HasTorAmplitudeGE K a := by
  intro M
  rw [isGE_iff]
  intro i hi
  exact hK M i fun hmem ↦ (not_lt_of_ge hmem.1 hi).elim

-- Proof sketch: unfold `HasTorAmplitudeGE` and rewrite the derived-category `IsGE` condition by
-- the canonical t-structure characterization in terms of vanishing of homology below degree `a`.
/-- An object of `D(R)` has tor-amplitude in `[a, ∞]` exactly when tensoring with any degree-zero
`R`-module has vanishing homology in every degree `< a`. -/
theorem hasTorAmplitudeGE_iff
    (K : DMod) (a : ℤ) :
    HasTorAmplitudeGE K a ↔
      ∀ (M : ModuleCat R) (i : ℤ), i < a →
        IsZero ((H i).obj (K ⊗[R]^L (single₀).obj M)) := by
  simp [HasTorAmplitudeGE, isGE_iff]

-- Proof sketch: for `(→)`, choose a termwise-flat K-flat resolution of a representative of `K`,
-- use the tor-amplitude hypothesis to show the cokernel in degree `a` is flat, truncate below `a`,
-- and apply the K-flat closure lemmas to the resulting short exact sequence. For `(←)`, tensor the
-- chosen K-flat representative with any degree-zero module and compute the derived tensor product
-- on the nose; since the tensor complex is strictly supported in degrees `≥ a`, its homology
-- vanishes below `a`.
/-- Lemma 15.67.4: an object `K` of `D(R)` has tor-amplitude in `[a, ∞]` if and only if it is
quasi-isomorphic to a K-flat cochain complex of flat `R`-modules that vanishes in every degree
`< a`. -/
theorem hasTorAmplitudeGE_iff_exists_representative
    (K : DMod) (a : ℤ) :
    HasTorAmplitudeGE K a ↔
      ∃ (E : Cpx) (_ : K ≅ Q.obj E),
        E.IsStrictlyGE a ∧ E.IsKFlat ∧ E.IsTermwiseFlat := sorry

end

end CategoryTheory

/-! ### Lemma_15_67_5 (from Chap15) -/
open CategoryTheory Pretriangulated

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]
variable {a b : ℤ}

local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling for Lemma 15.67.5:
- primary domain: tor-amplitude in the derived category `D(R)` and its behavior with respect to
  shifts and distinguished triangles;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `Triangle.rotate`,
  `Triangle.invRotate`,
  `rot_of_distTriang`,
  `inv_rot_of_distTriang`;
- best owner abstraction: the source-facing owner is `HasTorAmplitudeIn K a b`; distinguished
  triangle closure is derived API built from the canonical triangulated operations `rotate` and
  `invRotate`, together with the shift behavior of tor-amplitude;
- primitive vs. derived:
  primitive data are the tor-amplitude predicate from Definition `15.67.1` and its canonical
  shift transport;
  derived API are the three `obj₁`/`obj₂`/`obj₃` closure statements for distinguished triangles;
- source/core/bridge triage:
  `source-facing`: the three numbered closure statements below;
  `core/canonical`: the owner predicate `HasTorAmplitudeIn`;
  `bridge/view`: the owner-level shift theorem below and the use of `Triangle.rotate` /
    `Triangle.invRotate`
    to move between the three source-facing clauses.

This file keeps the textbook statements as the public surface, but treats clause `(1)` as the
primitive distinguished-triangle propagation statement. Clauses `(2)` and `(3)` are then expressed
as derived consequences via the canonical shift theorem and rotation operators rather than as
independent peer API. -/

-- Proof sketch: compare the homology of `K⟦1⟧ ⊗[R]^L M[0]` with the shifted homology of
-- `K ⊗[R]^L M[0]` using the standard shift isomorphism on the homology functors.
/-- Tor-amplitude shifts with the derived-category translation functor: shifting `K` by `n`
translates the tor-amplitude interval by the same amount. -/
theorem hasTorAmplitudeIn_shift_iff (K : DMod) (n a b : ℤ) :
    HasTorAmplitudeIn (K⟦n⟧) a b ↔ HasTorAmplitudeIn K (a + n) (b + n) := by
  sorry

-- Proof sketch: choose a tor-amplitude interval for `K`, translate it by `n` using
-- `hasTorAmplitudeIn_shift_iff`, and conversely shift the interval back by `-n`.
/-- Finite tor dimension is invariant under shifts in the derived category. -/
theorem hasFiniteTorDimension_shift_iff (K : DMod) (n : ℤ) :
    HasFiniteTorDimension (K⟦n⟧) ↔ HasFiniteTorDimension K := by
  sorry

-- Proof sketch: apply `- ⊗[R]^L N[0]` to the distinguished triangle, use that derived tensor
-- preserves distinguished triangles, and read off the vanishing range for the third term from the
-- associated long exact homology sequence.
/-- Lemma 15.67.5 (1): in a distinguished triangle in `D(R)`, if the first term has
tor-amplitude in `[a + 1, b + 1]` and the second term has tor-amplitude in `[a, b]`, then the
third term has tor-amplitude in `[a, b]`. -/
theorem hasTorAmplitudeIn_obj₃_of_distinguishedTriangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : HasTorAmplitudeIn T.obj₁ (a + 1) (b + 1))
    (h₂ : HasTorAmplitudeIn T.obj₂ a b) :
    HasTorAmplitudeIn T.obj₃ a b := sorry

-- Proof sketch: tensor with an arbitrary module placed in degree `0`, use the long exact
-- homology sequence of the distinguished triangle, and apply two-out-of-three for vanishing in
-- degrees outside `[a, b]`.
/-- Lemma 15.67.5 (2): in a distinguished triangle in `D(R)`, if the first and third terms have
tor-amplitude in `[a, b]`, then the second term has tor-amplitude in `[a, b]`. -/
theorem hasTorAmplitudeIn_obj₂_of_distinguishedTriangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : HasTorAmplitudeIn T.obj₁ a b)
    (h₃ : HasTorAmplitudeIn T.obj₃ a b) :
    HasTorAmplitudeIn T.obj₂ a b := by
  -- Apply part `(1)` to the inverse-rotated triangle
  -- `T.obj₃⟦-1⟧ ⟶ T.obj₁ ⟶ T.obj₂ ⟶ T.obj₃`.
  have h₃' : HasTorAmplitudeIn (T.obj₃⟦(-1 : ℤ)⟧) (a + 1) (b + 1) := by
    have h₃'' : HasTorAmplitudeIn T.obj₃ ((a + 1) + (-1)) ((b + 1) + (-1)) := by
      simpa [add_assoc] using h₃
    exact (hasTorAmplitudeIn_shift_iff T.obj₃ (-1) (a + 1) (b + 1)).2 h₃''
  exact
    hasTorAmplitudeIn_obj₃_of_distinguishedTriangle T.invRotate
      (inv_rot_of_distTriang T hT) h₃' h₁

-- Proof sketch: rotate the distinguished triangle and reduce to the first closure statement,
-- which shifts the tor-amplitude bounds by one on the first vertex exactly as required.
/-- Lemma 15.67.5 (3): in a distinguished triangle in `D(R)`, if the second term has
tor-amplitude in `[a + 1, b + 1]` and the third term has tor-amplitude in `[a, b]`, then the
first term has tor-amplitude in `[a + 1, b + 1]`. -/
theorem hasTorAmplitudeIn_obj₁_of_distinguishedTriangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₂ : HasTorAmplitudeIn T.obj₂ (a + 1) (b + 1))
    (h₃ : HasTorAmplitudeIn T.obj₃ a b) :
    HasTorAmplitudeIn T.obj₁ (a + 1) (b + 1) := by
  -- Apply part `(1)` to the rotated triangle
  -- `T.obj₂ ⟶ T.obj₃ ⟶ T.obj₁⟦1⟧ ⟶ T.obj₂⟦1⟧`,
  -- then shift back.
  have hshift :
      HasTorAmplitudeIn (T.obj₁⟦(1 : ℤ)⟧) a b :=
    hasTorAmplitudeIn_obj₃_of_distinguishedTriangle T.rotate
      (rot_of_distTriang T hT) h₂ h₃
  exact (hasTorAmplitudeIn_shift_iff T.obj₁ 1 a b).1 hshift

end

end CategoryTheory

/-! ### Lemma_15_67_6 (from Chap15) -/
universe u

open CategoryTheory

section

variable {R : Type u} [CommRing R]

namespace ModuleCat

variable (M : ModuleCat R)

/- Domain-style sampling:
- primary domain: tor dimension of modules over a commutative ring and its source-facing
  description by finite flat resolutions;
- sampled owner declarations:
  `CategoryTheory.ModuleHasTorDimensionLE`,
  `CategoryTheory.hasTorAmplitudeIn_iff_exists_flat_representative`,
  `ModuleCat.HasFiniteProjectiveResolutionLengthLE`,
  `CochainComplex.IsTermwiseFlat`;
- best owner abstraction: the chapter-level core owner remains
  `CategoryTheory.ModuleHasTorDimensionLE`, while the source-facing finite-resolution notion in
  this file should live alongside the analogous projective-resolution owner
  `ModuleCat.HasFiniteProjectiveResolutionLengthLE` rather than as a parallel global predicate;
- primitive vs. derived:
  primitive data are the flat modules `F i`, the differentials `δ`, the augmentation `π`, and the
  exactness/surjectivity/injectivity conditions expressing a finite flat resolution of `M`;
  derived API are the zero-length characterization and the equivalence with tor dimension at most
  `d`.

Source/core/bridge triage:
- `source-facing`: `ModuleCat.HasFiniteFlatResolutionLengthLE`;
- `core/canonical`: `CategoryTheory.ModuleHasTorDimensionLE`;
- `bridge/view`: the bounded flat representative criterion from Lemma `15.67.3`, which explains
  why the source-facing resolution predicate is equivalent to the tor-dimension owner.
-/

/-- A finite flat resolution of an `R`-module `M` of length at most `d`. For `d = 0` this is
just flatness of `M`; for `d = n + 1` it is an exact sequence
`0 ⟶ F_{n + 1} ⟶ F_n ⟶ ⋯ ⟶ F₀ ⟶ M ⟶ 0`
whose terms `Fᵢ` are flat. -/
def HasFiniteFlatResolutionLengthLE (d : ℕ) : Prop :=
  match d with
  | 0 => Module.Flat R M
  | n + 1 =>
      ∃ (F : Fin (n + 2) → ModuleCat R),
        (∀ i, Module.Flat R (F i)) ∧
          ∃ (δ : (i : Fin (n + 1)) → F i.succ ⟶ F i.castSucc)
            (π : F 0 ⟶ M),
            Function.Surjective π ∧
              Function.Exact (δ 0) π ∧
              (∀ i : Fin n, Function.Exact (δ i.succ) (δ i.castSucc)) ∧
              Function.Injective (δ (Fin.last n))

-- Proof sketch: unfold `HasFiniteFlatResolutionLengthLE`; the `d = 0` branch is defined to be
-- flatness of `M`.
/-- A finite flat resolution of length at most `0` is exactly flatness. -/
theorem hasFiniteFlatResolutionLengthLE_zero_iff :
    HasFiniteFlatResolutionLengthLE M 0 ↔ Module.Flat R M :=
  Iff.rfl

-- Proof sketch: the forward implication rewrites tor dimension `≤ d` as tor-amplitude in
-- `[-d, 0]` for `M[0]` and then applies Lemma `15.67.3` to obtain a flat representative
-- supported in that range, which is exactly a flat resolution of length at most `d`. For the
-- reverse implication, such a flat resolution gives a flat representative of `M[0]` in the same
-- range, so Lemma `15.67.3` yields tor-amplitude in `[-d, 0]`.
/-- Lemma 15.67.6: an `R`-module `M` has tor dimension at most `d` if and only if it admits a
finite flat resolution of length at most `d`. -/
theorem hasTorDimensionLE_iff_hasFiniteFlatResolutionLengthLE (d : ℕ) :
    ModuleHasTorDimensionLE M d ↔ HasFiniteFlatResolutionLengthLE M d := sorry

/-- A module of tor dimension at most `d` admits a finite flat resolution of length at most
`d`. -/
theorem ModuleHasTorDimensionLE.hasFiniteFlatResolutionLengthLE {d : ℕ}
    (hM : ModuleHasTorDimensionLE M d) :
    HasFiniteFlatResolutionLengthLE M d :=
  (hasTorDimensionLE_iff_hasFiniteFlatResolutionLengthLE M d).1 hM

/-- A finite flat resolution of length at most `d` gives tor dimension at most `d`. -/
theorem HasFiniteFlatResolutionLengthLE.hasTorDimensionLE {d : ℕ}
    (hM : HasFiniteFlatResolutionLengthLE M d) :
    ModuleHasTorDimensionLE M d :=
  (hasTorDimensionLE_iff_hasFiniteFlatResolutionLengthLE M d).2 hM

-- Proof sketch: specialize `hasTorDimensionLE_iff_hasFiniteFlatResolutionLengthLE` to
-- `d = 0` and use `hasFiniteFlatResolutionLengthLE_zero_iff`.
/-- An `R`-module has tor dimension at most `0` exactly when it is flat. -/
theorem hasTorDimensionLE_zero_iff_flat :
    ModuleHasTorDimensionLE M 0 ↔ Module.Flat R M :=
  (hasTorDimensionLE_iff_hasFiniteFlatResolutionLengthLE M 0).trans
    (hasFiniteFlatResolutionLengthLE_zero_iff M)

end ModuleCat

end

/-! ### Lemma_15_67_7 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.ObjectProperty
open ObjectProperty.IsStableUnderRetracts
open DerivedCategory

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]
variable {a b : ℤ}

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "single₀" => singleFunctor (ModuleCat R) (0 : ℤ)
local notation "H" => homologyFunctor (ModuleCat R)
local notation "TorAmp" => fun K : DMod ↦ HasTorAmplitudeIn K a b

/- Domain-style sampling for Lemma 15.67.7:
- primary domain: tor-amplitude as an object property on `D(R)`, together with the generic
  retract/direct-summand API for object properties in additive categories;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `ObjectProperty.IsStableUnderRetracts`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_left`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_right`;
- best owner abstraction: the owner layer is the object property
  `fun K : DMod ↦ HasTorAmplitudeIn K a b` together with its retract-stability instance; the
  biproduct/summand statements are derived API from the canonical generic lemmas `of_biprod_left`
  and `of_biprod_right`;
- primitive vs. derived:
  primitive data are the tor-amplitude owner predicate `HasTorAmplitudeIn`;
  derived API is its retract stability and the direct-summand consequences.

Source/core/bridge triage:
- `source-facing`: the textbook direct-summand consequences for tor-amplitude;
- `core/canonical`: `ObjectProperty.IsStableUnderRetracts` on
  `fun K : DMod ↦ HasTorAmplitudeIn K a b`;
- `bridge/view`: the specialization of the generic owner lemmas `of_biprod_left` and
  `of_biprod_right` to this tor-amplitude predicate.

This file therefore keeps the genuinely new owner instance and derives the textbook biproduct
clauses directly from the canonical owner API instead of maintaining parallel local copies.
-/

-- Proof sketch: unfold tor-amplitude, transport a retract `K ↪ L ↠ K` through tensoring with a
-- degree-zero module and then through the homology functor, and use retract-stability of the
-- zero-object property on `ModuleCat R`.
/-- Objects of `D(R)` with tor-amplitude in `[a, b]` are stable under retracts/direct summands. -/
instance hasTorAmplitudeIn_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts TorAmp where
  of_retract h hK M i hi :=
    prop_of_retract IsZero (h.map (derivedTensorProduct ((single₀).obj M) ⋙ H i)) (hK M i hi)

/- Lemma 15.67.7 (1): if `K ⊞ L` has tor-amplitude in `[a, b]`, then `K` has tor-amplitude in
`[a, b]`. This is the canonical direct-summand lemma
`ObjectProperty.IsStableUnderRetracts.of_biprod_left`, specialized to the tor-amplitude owner
predicate. -/
theorem hasTorAmplitudeIn_left_of_biprod
    (K L : DMod)
    (hKL : HasTorAmplitudeIn (K ⊞ L) a b) :
    HasTorAmplitudeIn K a b :=
  of_biprod_left TorAmp hKL

/- Lemma 15.67.7 (2): if `K ⊞ L` has tor-amplitude in `[a, b]`, then `L` has tor-amplitude in
`[a, b]`. This is the canonical direct-summand lemma
`ObjectProperty.IsStableUnderRetracts.of_biprod_right`, specialized to the tor-amplitude owner
predicate. -/
theorem hasTorAmplitudeIn_right_of_biprod
    (K L : DMod)
    (hKL : HasTorAmplitudeIn (K ⊞ L) a b) :
    HasTorAmplitudeIn L a b :=
  of_biprod_right TorAmp hKL

end

end CategoryTheory

/-! ### Lemma_15_67_8 (from Chap15) -/
noncomputable section

open CategoryTheory
open DerivedCategory
open scoped CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "Mod" => ModuleCat R
local notation "single₀" => DerivedCategory.singleFunctor Mod (0 : ℤ)

/- Domain-style sampling for Lemma 15.67.8:
- primary domain: tor-amplitude in `D(R)` for objects represented by bounded cochain complexes of
  `R`-modules;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `HasFiniteTorDimension`,
  `ModuleHasFiniteTorDimension`,
  `Compᵇ(Mod)`;
- best owner abstraction: `HasTorAmplitudeIn` is the tor-amplitude owner, while the presenting
  bounded cochain complex should use the chapter owner `Compᵇ(Mod)` rather than an
  unbundled complex plus a separate boundedness witness;
- primitive vs. derived:
  primitive data are the bounded complex `K : Compᵇ(Mod)`, with underlying cochain
  complex `K.obj`, and the termwise tor-amplitude hypotheses on the shifted single-term objects
  `((single₀).obj (K.obj.X i))⟦i⟧`;
  derived API is the finite-tor-dimension statement, which packages the interval choice after the
  main tor-amplitude theorem rather than introducing a second owner;
- source/core/bridge triage:
  `source-facing`: `hasTorAmplitudeIn_of_bounded_of_termwise_hasTorAmplitudeIn`;
  `core/canonical`: `HasTorAmplitudeIn`, `HasFiniteTorDimension`, and
    `Compᵇ(Mod)`;
  `bridge/view`: the forgetful passage from the bounded cochain complex `K` to its underlying
  cochain complex `K.obj`, then to the shifted degree-zero terms `((single₀).obj (K.obj.X i))⟦i⟧`,
  and finally to the derived object `Q.obj K.obj`.

This keeps the textbook theorem source-facing, but moves its boundedness input to the canonical
chapter owner category and its termwise hypothesis to the intrinsic shifted derived objects rather
than the coordinate-level interval formula `a - i, b - i`.
-/

-- Proof sketch: argue by induction on the length of the bounded complex using stupid
-- truncations. The induction step writes the image of `K` in `D(R)` in a distinguished triangle
-- whose left vertex is a shift of a single term `K.obj.X i`, so Lemma `15.67.5` propagates the
-- shifted tor-amplitude bounds from the terms to the whole complex.
/-- Lemma 15.67.8 (1): if a bounded cochain complex of `R`-modules has each term `K^i`
tor-amplitude in `[a - i, b - i]`, equivalently if the shifted single-term object
`K^i[i] = ((single₀).obj (K.obj.X i))⟦i⟧` has tor-amplitude in `[a, b]`, then the associated
object of `D(R)` has tor-amplitude in `[a, b]`. -/
theorem hasTorAmplitudeIn_of_bounded_of_termwise_hasTorAmplitudeIn
    (a b : ℤ)
    (K : Compᵇ(Mod))
    (hterm :
      ∀ i : ℤ,
        HasTorAmplitudeIn (((single₀).obj (K.obj.X i))⟦i⟧) a b) :
    HasTorAmplitudeIn (Q.obj K.obj) a b := sorry

-- Proof sketch: for each nonzero term `K.obj.X i`, choose a finite tor-amplitude interval;
-- boundedness of `K` leaves only finitely many relevant indices, so these intervals admit common
-- endpoints `a ≤ b`. Transport those bounds to the shifted objects `K^i[i]` via
-- `hasTorAmplitudeIn_shift_iff`, apply the first part with the common interval `[a, b]`, and then
-- package the result via `HasTorAmplitudeIn.hasFiniteTorDimension`.
/-- Lemma 15.67.8 (2): a bounded cochain complex of `R`-modules whose terms all have finite tor
dimension has finite tor dimension in `D(R)`. -/
theorem hasFiniteTorDimension_of_bounded_of_termwise_hasFiniteTorDimension
    (K : Compᵇ(Mod))
    (hterm : ∀ i : ℤ, ModuleHasFiniteTorDimension (K.obj.X i)) :
    HasFiniteTorDimension (Q.obj K.obj) := sorry

end

end CategoryTheory

/-! ### Lemma_15_67_9 (from Chap15) -/
noncomputable section

open DerivedCategory
open scoped CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "Mod" => ModuleCat R
local notation "DbMod" => Dᵇ(Mod)
local notation "Hb" => boundedDerivedHomologyFunctor Mod

/- Domain-style sampling for Lemma 15.67.9:
- primary domain: tor-amplitude and finite tor dimension in the bounded derived category `D^b(R)`,
  read through the canonical bounded-derived cohomology functors;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `HasFiniteTorDimension`,
  `ModuleHasFiniteTorDimension`,
  `Dᵇ(ModuleCat R)`,
  `boundedDerivedHomologyFunctor`,
  `shiftedCohomology`,
  `hasTorAmplitudeIn_shift_iff`;
- best owner abstraction: the tor-amplitude owner is `HasTorAmplitudeIn K a b`, boundedness is
  carried canonically by `K : DbMod`; the cohomology modules of such a bounded object should
  be read through the chapter owner `Hb i : Dᵇ(ModuleCat R) ⥤ ModuleCat R`, and finite tor
  dimension for those modules should use the module-level owner
  `ModuleHasFiniteTorDimension` instead of re-expanding it through the degree-zero embedding; the
  intrinsic shifted cohomology object attached to `H^i(K)` should be read through the chapter owner
  `shiftedCohomology Mod K.obj i` rather than through a local
  `M[0][i]` spelling; the only bridge-level input needed on the public surface is the companion
  shift theorem `hasTorAmplitudeIn_shift_iff`, which lets the hypotheses be read on the intrinsic
  shifted cohomology objects
  `shiftedCohomology Mod K.obj i`, rather than as raw `singleFunctor` packaging or as a second
  coordinate-level interval API;
- primitive vs. derived:
  primitive data are the bounded derived object `K` and the termwise tor-amplitude hypotheses on
  its intrinsic shifted bounded-derived cohomology objects `shiftedCohomology Mod K.obj i`;
  derived API is the finite-tor-dimension consequence, obtained by packaging interval existence;
- source/core/bridge triage:
  `source-facing`: the two textbook bounded-derived theorems below;
  `core/canonical`: `HasTorAmplitudeIn`, `HasFiniteTorDimension`,
  `ModuleHasFiniteTorDimension`, `Dᵇ(ModuleCat R)`, `Hb`, and `shiftedCohomology`;
  `bridge/view`: the boundedness owner on `K`, the degree-zero embedding `M ↦ M[0]`, and the
    shift-transport bridge `hasTorAmplitudeIn_shift_iff`.

This file therefore keeps the source-facing bounded-derived statements, while reusing the chapter
owners `boundedDerivedHomologyFunctor`, `shiftedCohomology`,
`ModuleHasFiniteTorDimension`, and the Chapter 13 bounded-object/cohomology bridge instead of
spelling a parallel representative API here.
-/

/-- Lemma 15.67.9: if `K` is a bounded derived object of `R`-modules and each cohomology module
`H^i(K)`, placed in cohomological degree `i`, has tor-amplitude in `[a, b]`, then `K` has
tor-amplitude in `[a, b]`. The canonical owner for that shifted cohomology object is
`shiftedCohomology Mod K.obj i`. -/
theorem hasTorAmplitudeIn_of_bounded_of_homology_hasTorAmplitudeIn
    (a b : ℤ) (K : DbMod)
    (hH : ∀ i : ℤ, HasTorAmplitudeIn (shiftedCohomology Mod K.obj i) a b) :
    HasTorAmplitudeIn K.obj a b := sorry

-- Proof sketch: boundedness leaves only finitely many possibly nonzero cohomology modules, so the
-- finite tor-dimension intervals for the degree-zero cohomology modules admit common endpoints;
-- transport those intervals to the intrinsic shifted cohomology objects
-- `shiftedCohomology Mod K.obj i` by `hasTorAmplitudeIn_shift_iff`, then apply the first theorem.
/-- If every cohomology module of a bounded derived object has finite tor dimension, then the
bounded derived object itself has finite tor dimension. -/
theorem hasFiniteTorDimension_of_bounded_of_homology_hasFiniteTorDimension
    (K : DbMod)
    (hH : ∀ i : ℤ, ModuleHasFiniteTorDimension ((Hb i).obj K)) :
    HasFiniteTorDimension K.obj := sorry

end

end CategoryTheory

/-! ### Lemma_15_67_10 (from Chap15) -/
noncomputable section

open CategoryTheory
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {a b c d : ℤ}

local notation "DModB" => DerivedCategory (ModuleCat B)

/- Domain-style sampling for Lemma 15.67.10:
- primary domain: derived change of rings and tor-amplitude in derived categories of modules;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `derivedTensorProduct`,
  `(ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory`,
  `derivedTensorProduct_associator`;
- best owner abstraction: this lemma is a `source-facing` change-of-rings bridge whose statement
  should stay on the tor-amplitude owner `HasTorAmplitudeIn`; the tensor product and restriction
  steps are already canonically owned by `derivedTensorProduct`, its associativity isomorphism
  `derivedTensorProduct_associator`, and the exact functor
  `(ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory`, so no parallel wrapper API
  is introduced here;
- primitive data: the objects `K, L : D(B)` and the tor-amplitude hypotheses on `K` over `B`
  and on the restricted object
  `((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L` over `A`;
- derived API: the tor-amplitude bound for the restricted tensor product object
  `((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj (K ⊗[B]^L L)`.

Source/core/bridge triage:
- `source-facing`: the Stacks-project tor-amplitude bound after tensoring over `B` and then
  restricting to `A`;
- `core/canonical`: `HasTorAmplitudeIn`, `derivedTensorProduct`, and exact
  `Functor.mapDerivedCategory` for restriction of scalars;
- `bridge/view`: restriction of scalars applied via the exact derived functor
  `(ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory`. -/

-- Proof sketch: choose a flat representative of `K` over `B` supported in `[a, b]` using
-- Lemma `15.67.3`, test the restricted derived tensor product against an arbitrary degree-zero
-- `A`-module, rewrite the resulting iterated derived tensor product with the canonical
-- associativity isomorphism `derivedTensorProduct_associator`, and use the tor-amplitude bound on
-- `L` over `A` together with the double-complex spectral sequence to bound the resulting
-- cohomology degrees by `[a + c, b + d]`.
/-- Lemma 15.67.10: if `K^•` has tor-amplitude in `[a, b]` over `B` and `L^•`, viewed as a
complex of `A`-modules by restriction of scalars, has tor-amplitude in `[c, d]`, then
`K^• \otimes_B^{\mathbf L} L^•`, viewed as a complex of `A`-modules, has tor-amplitude in
`[a + c, b + d]`. -/
theorem hasTorAmplitudeIn_restrictScalars_derivedTensorProduct
    (K L : DModB)
    (hK : HasTorAmplitudeIn K a b)
    (hL :
      HasTorAmplitudeIn
        (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L) c d) :
    HasTorAmplitudeIn
      (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj
        (K ⊗[B]^L L))
      (a + c) (b + d) := sorry

end

end CategoryTheory

/-! ### Lemma_15_67_11 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
variable {a b : ℤ}

local notation "DModB" => DerivedCategory (ModuleCat B)

/- Domain-style sampling:
- primary domain: tor-amplitude in derived categories of module categories under flat restriction
  of scalars;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `hasTorAmplitudeIn_restrictScalars_derivedTensorProduct`,
  `(ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory`,
  `derivedTensorProduct`;
- best owner abstraction: the public statement should stay on the tor-amplitude owner
  `HasTorAmplitudeIn`, with restriction of scalars expressed directly by the canonical derived
  functor `(ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory`;
- primitive vs. derived:
  primitive data are the ring map `A → B`, the flatness hypothesis, the derived `B`-object `K`,
  and its tor-amplitude interval `[a, b]`;
  derived API is just the restricted object
  `((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)`.

Source/core/bridge triage:
- `source-facing`: flat restriction of scalars preserves the tor-amplitude interval of a derived
  `B`-complex;
- `core/canonical`: `HasTorAmplitudeIn` and exact `Functor.mapDerivedCategory` for
  `ModuleCat.restrictScalars`;
- `bridge/view`: the degree-zero `B`-module `B[0]` used in the proof sketch to reduce to
  Lemma `15.67.10`.

The old file introduced a private alias for the derived restriction functor. That alias carried no
mathematics beyond the canonical owner operation, so the theorem surface below uses the canonical
expression directly, with this lemma understood as the flat `B[0]` specialization of
`hasTorAmplitudeIn_restrictScalars_derivedTensorProduct`.
-/

-- Proof sketch: apply `hasTorAmplitudeIn_restrictScalars_derivedTensorProduct` with
-- `L := (ModuleCat.single0Functor : ModuleCat B ⥤ DModB).obj (ModuleCat.of B B)`. The degree-zero
-- `B`-module is flat over `A`, so after restriction to `A` it has tor-amplitude in `[0, 0]`;
-- then identify `K ⊗_B^L B[0]` with `K`.
/-- Lemma 15.67.11: if `K^•` has tor-amplitude in `[a, b]` over `B` and `B` is flat over `A`,
then `K^•`, viewed as a complex of `A`-modules by restriction of scalars, has tor-amplitude in
`[a, b]`. -/
theorem hasTorAmplitudeIn_restrictScalars_of_flat
    (K : DModB) (hK : HasTorAmplitudeIn K a b) :
    HasTorAmplitudeIn
      ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K) a b :=
  sorry

end

end CategoryTheory

/-! ### Lemma_15_67_12 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {a b : ℤ} {d : ℕ}

local notation "DModB" => DerivedCategory (ModuleCat B)

/- Domain-style sampling for Lemma 15.67.12:
- primary domain: tor-amplitude in derived categories under restriction of scalars;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `ModuleHasTorDimensionLE`,
  `hasTorAmplitudeIn_restrictScalars_derivedTensorProduct`,
  `ModuleCat.single0Functor`,
  `(ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory`;
- best owner abstraction: the source-facing statement remains a tor-amplitude bound after
  restriction of scalars, while the canonical owner layer is `HasTorAmplitudeIn` together with the
  exact derived restriction functor itself; this file is the source-facing specialization of
  `hasTorAmplitudeIn_restrictScalars_derivedTensorProduct` obtained by testing against the
  canonical degree-zero object `B[0]`, not a new local wrapper around restriction of scalars;
- primitive data: the derived `B`-complex `K` and the module-level tor-dimension hypothesis on
  `B` over `A`;
- derived API: the restricted derived object
  `((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)`.

Source/core/bridge triage:
- `source-facing`: `hasTorAmplitudeIn_restrictScalars_of_moduleHasTorDimensionLE`;
- `core/canonical`: `HasTorAmplitudeIn`, `ModuleHasTorDimensionLE`, and exact
  `Functor.mapDerivedCategory` for restriction of scalars;
- `bridge/view`: the canonical degree-zero embedding `ModuleCat.single0Functor` for `B[0]`,
  together with viewing a derived `B`-complex as a derived `A`-complex by restriction. -/

-- Proof sketch: view the degree-zero object `B[0]` in `D(B)`; the hypothesis
-- `ModuleHasTorDimensionLE (ModuleCat.of A B) d` says that, after restriction to `A`, it has
-- tor-amplitude in `[-d, 0]`. Apply Lemma `15.67.10` to `K` and `B[0]`, and then identify
-- `K ⊗_B^L B[0]` with `K` to obtain the interval `[a - d, b]` over `A`.
/-- Lemma 15.67.12: if `B` has tor dimension at most `d` as an `A`-module and `K^•` has
tor-amplitude in `[a, b]` over `B`, then `K^•`, viewed as a complex of `A`-modules by
restriction of scalars, has tor-amplitude in `[a - d, b]`. -/
theorem hasTorAmplitudeIn_restrictScalars_of_moduleHasTorDimensionLE
    (K : DModB)
    (hB : ModuleHasTorDimensionLE (ModuleCat.of A B) d)
    (hK : HasTorAmplitudeIn K a b) :
    HasTorAmplitudeIn
      ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)
      (a - (d : ℤ)) b := sorry

end

end CategoryTheory

/-! ### Lemma_15_67_13 (from Chap15) -/
noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModB" => DerivedCategory (ModuleCat B)

/- Domain-style sampling for Lemma 15.67.13:
- primary domain: tor-amplitude in derived categories under derived scalar extension;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `derivedTensorWithAlgebra`,
  `DerivedTensorWithAlgebra` notation `⊗[A]^L[B]`,
  `ModuleCat.extendScalars`;
- best owner abstraction: this theorem is `source-facing`, while the core/canonical owners are the
  tor-amplitude predicate `HasTorAmplitudeIn` and the derived scalar-extension owner
  `derivedTensorWithAlgebra (algebraMap A B)`;
- primitive vs. derived:
  primitive data are the derived `A`-complex `K` and its tor-amplitude interval `[a, b]`;
  the base-changed object `K ⊗[A]^L[B]` is derived API through the canonical owner notation, so
  this file should depend directly on the owner file `15_60_1_1` rather than the later
  change-of-rings bridge in `Lemma_15_60_1`;
- source/core/bridge triage:
  `source-facing`: preservation of tor-amplitude under base change along `A → B`;
  `core/canonical`: `HasTorAmplitudeIn` and `derivedTensorWithAlgebra`;
  `bridge/view`: the notation `K ⊗[A]^L[B]` for the owner applied to `K`. -/

-- Proof sketch: choose a flat representative of `K` concentrated in degrees `[a, b]` using
-- Lemma `15.67.3`; after tensoring termwise with `B`, the resulting complex is still concentrated
-- in `[a, b]`, and its terms are flat over `B` by flat base change. This new flat representative
-- computes `K ⊗_A^L B`, so Lemma `15.67.3` gives the claimed tor-amplitude interval over `B`.
/-- Lemma 15.67.13: if an object `K^•` of `D(A)` has tor-amplitude in `[a, b]`, then its derived
base change `K^• \otimes_A^{\mathbf L} B` has tor-amplitude in `[a, b]` as an object of
`D(B)`. -/
theorem hasTorAmplitudeIn_derivedTensorWithAlgebra
    (K : DModA) (a b : ℤ) (hK : HasTorAmplitudeIn K a b) :
    HasTorAmplitudeIn (K ⊗[A]^L[B]) a b := sorry

end

end CategoryTheory

/-! ### Lemma_15_67_14 (from Chap15) -/
noncomputable section

open CategoryTheory
universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "Ext" => ModuleCat.extendScalars (algebraMap A B)
local notation "single₀" =>
  (ModuleCat.single0Functor : ModuleCat A ⥤ DerivedCategory (ModuleCat A))

/- Domain-style sampling for Lemma 15.67.14:
- primary domain: tor-amplitude and module tor dimension under flat scalar extension in derived
  categories of module categories;
- sampled owner declarations:
  `ModuleHasTorDimensionLE`,
  `HasTorAmplitudeIn`,
  `hasTorAmplitudeIn_derivedTensorWithAlgebra`,
  `ModuleCat.extendScalars`,
  `ModuleCat.single0Functor`;
- best owner abstraction: the core/canonical owner is the chapter tor-amplitude predicate
  `HasTorAmplitudeIn` on degree-zero derived objects, with `hasTorAmplitudeIn_derivedTensorWithAlgebra`
  as the upstream base-change owner theorem; the module statement here is only the degree-zero
  `bridge/view` consequence for ordinary scalar extension;
- primitive vs. derived:
  primitive data are the ring map `A → B`, the flatness hypothesis, and the module `M` viewed via
  `ModuleHasTorDimensionLE M d`, equivalently via the chapter owner
  `single₀`;
  the conclusion for `((Ext).obj M)` is derived API obtained
  by applying the owner theorem to the degree-zero derived object and then comparing with ordinary
  scalar extension in degree `0`.

Source/core/bridge triage:
- `source-facing`: preservation of module tor dimension under flat extension of scalars;
- `core/canonical`: `HasTorAmplitudeIn` and `hasTorAmplitudeIn_derivedTensorWithAlgebra`;
- `bridge/view`: `ModuleHasTorDimensionLE` for ordinary modules. -/

-- Proof sketch: rewrite `ModuleHasTorDimensionLE M d` as tor-amplitude in `[-d, 0]` for the
-- degree-zero owner object of `M`, apply `hasTorAmplitudeIn_derivedTensorWithAlgebra`, and then
-- use flatness of `A → B` to identify derived base change with ordinary scalar extension on
-- degree-zero modules.
/-- Lemma 15.67.14: for a flat ring map `A → B`, if an `A`-module `M` has tor dimension at most
`d`, then its scalar extension `M ⊗_A B` has tor dimension at most `d` as a `B`-module. -/
theorem moduleHasTorDimensionLE_extendScalars
    (hflat : (algebraMap A B).Flat) (M : ModuleCat A) (d : ℕ)
    (hM : ModuleHasTorDimensionLE M d) :
    ModuleHasTorDimensionLE ((Ext).obj M) d := by
  sorry

end

end CategoryTheory

/-! ### Lemma_15_67_15 (from Chap15) -/
noncomputable section

open CategoryTheory
universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} {B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {a b : ℤ}

local notation "DModB" => DerivedCategory (ModuleCat B)

local instance extendScalars_additive_atPrime (q : PrimeSpectrum B) :
    (ModuleCat.extendScalars.{u, u, u}
      (algebraMap B (Localization.AtPrime q.asIdeal))).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
    (algebraMap B (Localization.AtPrime q.asIdeal))).left_adjoint_additive

local instance extendScalars_preservesFiniteLimits_atPrime (q : PrimeSpectrum B) :
    Limits.PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u}
        (algebraMap B (Localization.AtPrime q.asIdeal))) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr <|
      IsLocalization.flat (Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl)

/- Domain sampling pass:
* primary domain: tor-amplitude in derived categories of module categories under restriction of
  scalars and prime localization;
* sampled owner declarations:
  - `HasTorAmplitudeIn` from `Definition_15_67_1`, the chapter owner for tor-amplitude;
  - `(ModuleCat.extendScalars f).mapDerivedCategory`, the canonical exact derived localization
    functor for flat scalar extension;
  - `(ModuleCat.restrictScalars f).mapDerivedCategory`, the canonical derived restriction functor;
  - `Localization.localRingHom`, the canonical owner for the localized map
    `A_(q ∩ A) → B_q`;
  - `hasTorAmplitudeIn_restrictScalars_of_flat` from `Lemma_15_67_11`, the chapter-local reuse
    point for passing tor-amplitude across flat restriction of scalars.

Source/core/bridge triage:
* `source-facing`: `hasTorAmplitudeIn_over_base_tfae_of_localizations`;
* `core/canonical`: `HasTorAmplitudeIn`, `ModuleCat.extendScalars`,
  `Localization.localRingHom`, and `mapDerivedCategory`;
* `bridge/view`: the localized restricted derived object over the contracted prime, written
  directly from those canonical owners in the prime-local and maximal-local clauses.

Primitive data is only the derived object `K : DModB` together with the canonical localization and
restriction functors. The public theorem below is kept source-facing as a `TFAE`, and its local
clauses are stated directly from those owners, using only theorem-local names to avoid repeating
the same dependent-type expression in every clause.
-/

-- Proof sketch: the implication from the global statement to the prime-local and maximal-local
-- statements comes from exactness of derived localization and restriction of scalars. For the
-- converse, test the homology modules of `K ⊗_A^L M` at maximal ideals of `B`; by the localized
-- hypotheses these stalks vanish outside `[a, b]`, so Lemma `10.23.1` forces the global homology
-- modules to vanish.
/-- Lemma 15.67.15: for a derived `B`-complex `K`, the following are equivalent: `K`, viewed over
`A`, has tor-amplitude in `[a, b]`; for every prime `q` of `B`, the localization `K_q` has
tor-amplitude in `[a, b]` over `A_(q ∩ A)`; and it is enough to check this only at maximal ideals
of `B`. -/
theorem hasTorAmplitudeIn_over_base_tfae_of_localizations (K : DModB) :
    let restrictedK : DerivedCategory (ModuleCat A) :=
      (ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K
    let localizedOverBase :
        (q : PrimeSpectrum B) →
          DerivedCategory (ModuleCat (Localization.AtPrime (q.asIdeal.under A))) :=
      fun q ↦
        (ModuleCat.restrictScalars
            (Localization.localRingHom (q.asIdeal.under A) q.asIdeal (algebraMap A B) rfl)).mapDerivedCategory.obj
          ((ModuleCat.extendScalars
              (algebraMap B (Localization.AtPrime q.asIdeal))).mapDerivedCategory.obj K)
    List.TFAE [
      HasTorAmplitudeIn restrictedK a b,
      ∀ q : PrimeSpectrum B, HasTorAmplitudeIn (localizedOverBase q) a b,
      ∀ m : MaximalSpectrum B,
        HasTorAmplitudeIn (localizedOverBase m.toPrimeSpectrum) a b
    ] := by
  sorry

end

end CategoryTheory

/-! ### Lemma_15_67_16 (from Chap15) -/
noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]
variable {ι : Type*} [Finite ι]

local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling:
- primary domain: tor-amplitude descent in derived categories under localization-away base change;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `derivedTensorWithAlgebra`,
  `hasTorAmplitudeIn_of_faithfullyFlat_baseChange`;
- source/core/bridge triage:
  `source-facing`: local descent of tor-amplitude from a finite principal-open cover;
  `core/canonical`: `HasTorAmplitudeIn` on `DerivedCategory (ModuleCat R)`;
  `bridge/view`: the localization-away base changes `K ⊗[R]^L[Localization.Away (f i)]`.

Primitive data here is the derived object `K` together with its tor-amplitude after canonical
base change to each `Localization.Away (f i)`, indexed by an arbitrary finite type `ι`. The old
coordinate model `Fin r` carried no mathematical structure used by the statement, so the theorem
below uses the chapter's canonical finite-family surface directly. Its proof route should factor
through the chapter owner `hasTorAmplitudeIn_of_faithfullyFlat_baseChange`, rather than reaching
back to the lower-level derived scalar-extension construction file.
-/

-- Proof sketch: pass from the family `f` to the canonical faithfully flat map from `R` to the
-- finite product of the principal localizations `∏ i, Localization.Away (f i)` attached to the
-- unit-ideal hypothesis. The localized tor-amplitude assumptions give tor-amplitude after this
-- single faithfully flat base change, and Lemma `15.67.17` then descends `HasTorAmplitudeIn`
-- back to `K`.
/-- Lemma 15.67.16: if a finite family `f : ι → R` generates the unit ideal and each
localization of `K` away from `f i` has tor-amplitude in `[a, b]`, then `K` has tor-amplitude in
`[a, b]`. -/
theorem hasTorAmplitudeIn_of_localizationAway_unitIdeal
    (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤)
    (K : DMod) (a b : ℤ)
    (hloc : ∀ i,
      HasTorAmplitudeIn (K ⊗[R]^L[Localization.Away (f i)]) a b) :
    HasTorAmplitudeIn K a b := sorry

end

end CategoryTheory

/-! ### Lemma_15_67_17 (from Chap15) -/
noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R R' : Type u} [CommRing R] [CommRing R']

local notation "DModR" => DerivedCategory (ModuleCat R)

/- Domain-style sampling:
- primary domain: tor-amplitude descent for objects of `D(R)` under faithfully flat derived base
  change;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `derivedTensorWithAlgebra`,
  `(ModuleCat.restrictScalars (algebraMap R R')).mapDerivedCategory`;
- source/core/bridge triage:
  `source-facing`: faithful-flat descent of tor-amplitude for a derived `R`-complex along an
    explicit ring map `f : R →+* R'`;
  `core/canonical`: the chapter owner `HasTorAmplitudeIn` on `DerivedCategory (ModuleCat R)`;
  `bridge/view`: the passage from the explicit owner object `((derivedTensorWithAlgebra f).obj K)`
    to the standard derived base-change notation `K ⊗[R]^L[R']` after passing to `f.toAlgebra`.

The old file encoded the same mathematics by quantifying over exactness of tensor complexes for a
chosen cochain representative. That representative-level formulation is derived API: the primitive
data is just the ring map `f`, the derived object `K`, and its tor-amplitude after faithfully
flat base change along `f`. The canonical owner-level statement below therefore replaces the
duplicate complex-level wrapper.
-/

-- Proof sketch: to verify `HasTorAmplitudeIn K a b`, fix an `R`-module `M` and a degree
-- `i ∉ [a, b]`. After tensoring the homology object `H_i(K ⊗_R^L M[0])` with `R'`, use the
-- standard derived base-change/associativity comparison to identify it with the degree-`i`
-- homology of `(K ⊗_R^L R') ⊗_{R'}^L ((R' ⊗_R M)[0])`, which vanishes by `hK`. Since `R'` is
-- faithfully flat over `R`, tensoring with `R'` reflects zero modules, so the original homology
-- object already vanishes.
/-- Lemma 15.67.17: if the derived base change of a derived `R`-complex `K` along a faithfully
flat ring map `R → R'` has tor-amplitude in `[a, b]`, then `K` already has tor-amplitude in
`[a, b]`. -/
theorem hasTorAmplitudeIn_of_faithfullyFlat_baseChange
    (f : R →+* R') (K : DModR) (a b : ℤ)
    (hff : f.FaithfullyFlat)
    (hK : HasTorAmplitudeIn ((derivedTensorWithAlgebra f).obj K) a b) :
    HasTorAmplitudeIn K a b := sorry

end

end CategoryTheory

/-! ### Lemma_15_67_18 (from Chap15) -/
noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

local notation "DModA" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.67.18:
- primary domain: relative tor-amplitude in derived categories under faithfully flat base change
  of the ambient algebra;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `derivedTensorWithAlgebra`,
  `(ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory`,
  `(ModuleCat.restrictScalars (algebraMap R B)).mapDerivedCategory`;
- best owner abstraction: the source-facing statement is an `iff` about the canonical owner
  `HasTorAmplitudeIn` after applying the two exact derived restriction functors, so the theorem
  should speak directly in that owner language instead of rebuilding a local wrapper around the
  restricted complexes;
- primitive vs. derived:
  primitive data are the scalar tower `R → A → B`, the faithfully flat hypothesis on `A → B`, and
  the derived `A`-complex `K`;
  the restricted objects
  `((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K)` and
  `((ModuleCat.restrictScalars (algebraMap R B)).mapDerivedCategory.obj (K ⊗[A]^L[B]))` are
  derived API obtained by viewing the same source-facing complex over `R` before and after base
  change.

Source/core/bridge triage:
- `source-facing`: faithful-flat invariance of tor-amplitude over the base ring `R`;
- `core/canonical`: `HasTorAmplitudeIn` on derived module categories;
- `bridge/view`: the exact derived restriction objects
  `((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K)` and
  `((ModuleCat.restrictScalars (algebraMap R B)).mapDerivedCategory.obj (K ⊗[A]^L[B]))`,
  together with the derived base-change object `K ⊗[A]^L[B]`. -/

-- Proof sketch: the forward implication is tor-amplitude preservation under derived base change,
-- applied after viewing `K` as an object of `D(R)`. For the reverse implication, apply faithful
-- flat descent for tor-amplitude to the restricted `R`-linear complex after base change along
-- `A → B`, using the compatibility between restriction of scalars and derived tensor base change.
/-- Lemma 15.67.18: for ring maps `R → A → B` with `A → B` faithfully flat, an object `K` of
`D(A)` has tor-amplitude in `[a, b]` over `R` if and only if its derived base change
`K \otimes_A^{\mathbf L} B`, regarded as an object of `D(R)`, has tor-amplitude in `[a, b]`
over `R`. -/
theorem hasTorAmplitudeIn_restrictScalars_iff_of_faithfullyFlat_baseChange
    (K : DModA) (a b : ℤ)
    (hff : RingHom.FaithfullyFlat (algebraMap A B)) :
    HasTorAmplitudeIn
        (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory).obj K) a b ↔
      HasTorAmplitudeIn
        (((ModuleCat.restrictScalars (algebraMap R B)).mapDerivedCategory).obj (K ⊗[A]^L[B]))
        a b := sorry

end

end CategoryTheory

/-! ### Lemma_15_67_19 (from Chap15) -/
noncomputable section

open CategoryTheory
open DerivedCategory.TStructure

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "Bounded" => (t.bounded : ObjectProperty DMod)

/- Domain-style sampling for Lemma 15.67.19:
- primary domain: tor-amplitude in the derived category of modules, boundedness via the
  derived-category t-structure, and weak-dimension bounds on the ring;
- sampled owner declarations:
  `HasWeakDimensionLE`,
  `ModuleHasTorDimensionLE`,
  `HasTorAmplitudeIn`,
  `HasFiniteTorDimension`,
  `t.bounded`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.IsLE`;
- best owner abstraction: the ring-side primitive datum for these tor-dimension conclusions is the
  weak-dimension owner `HasWeakDimensionLE R d`, whose module-level consequence is the canonical
  owner `ModuleHasTorDimensionLE`; the stronger Chapter 10 owner `HasGlobalDimensionLE R d`
  belongs only to the bridge layer through the instance from Definition `15.105.3`; the canonical
  way to say that `K` has cohomology concentrated in `[a, b]` is the t-structure owner data
  `K.IsGE a` and `K.IsLE b`, not a parallel pointwise vanishing hypothesis;
- primitive vs. derived:
  primitive data are the ring bound `[HasWeakDimensionLE R d]` and the bounded-support owner
  data `K.IsGE a`, `K.IsLE b`;
  derived API is the resulting tor-amplitude interval and the bounded-derived equivalence;
- source/core/bridge triage:
  `source-facing`: the two tor-dimension consequences below;
  `core/canonical`: `HasWeakDimensionLE`, `ModuleHasTorDimensionLE`, `HasTorAmplitudeIn`,
    `HasFiniteTorDimension`, `t.bounded`, `K.IsGE a`, and `K.IsLE b`;
  `bridge/view`: the instance chain
    `HasGlobalDimensionLE R d ⟹ HasWeakDimensionLE R d ⟹ ModuleHasTorDimensionLE M d`, together
    with the cohomology-vanishing characterization of `K.IsGE a` and `K.IsLE b`; the former stays
    a bridge rather than a primitive hypothesis in this file.
-/

-- Proof sketch: if `K.IsGE a` and `K.IsLE b`, then `H^i(K)` vanishes unless `a ≤ i ≤ b`. For
-- the nonvanishing cohomology objects, the weak-dimension owner gives tor dimension at most `d`,
-- so their degree-zero derived objects have tor-amplitude in
-- `[(-d) - i, -i]`, hence in `[(a - d) - i, b - i]`. Apply Lemma `15.67.9`.
/-- If `R` has weak dimension at most `d` and the cohomology of `K` is concentrated in `[a, b]`,
then `K` has tor-amplitude in `[(a - d), b]`. -/
theorem hasTorAmplitudeIn_of_cohomology_concentrated_of_hasWeakDimensionLE
    (d : ℕ) [HasWeakDimensionLE R d] (K : DMod) (a b : ℤ) (hGE : K.IsGE a) (hLE : K.IsLE b) :
    HasTorAmplitudeIn K (a - (d : ℤ)) b := sorry

-- Proof sketch: if `K` has finite tor dimension, test the defining tor-amplitude condition
-- against the unit module `R[0]` to see that the cohomology of `K` is supported in a finite
-- interval, hence `K` is bounded. Conversely, if `K` is bounded, choose an interval containing its
-- cohomology, apply the previous theorem to obtain finite tor-amplitude, and conclude that `K`
-- has finite tor dimension.
/-- Lemma 15.67.19: over a ring of weak dimension at most `d`, an object of `D(R)` has finite
tor dimension if and only if it satisfies the canonical boundedness owner `t.bounded`, i.e. if
and only if it belongs to the bounded derived category `D^b(R)`. -/
theorem hasFiniteTorDimension_iff_mem_boundedDerivedCategory
    (d : ℕ) [HasWeakDimensionLE R d] (K : DMod) :
    HasFiniteTorDimension K ↔ Bounded K := sorry

end

end CategoryTheory

/-! ### Lemma_15_67_20 (from Chap15) -/
noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R' R : Type u} [CommRing R'] [CommRing R] [Algebra R' R]

local notation "DModRPrime" => DerivedCategory (ModuleCat R')

/- Domain-style sampling for Lemma 15.67.20:
- primary domain: tor-amplitude in derived categories under derived scalar extension across a
  nilpotent thickening;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `derivedTensorWithAlgebra`,
  `DerivedTensorWithAlgebra` notation `⊗[R']^L[R]`,
  `hasTorAmplitudeIn_derivedTensorWithAlgebra`;
- best owner abstraction: the source-facing statement is an equivalence on the chapter owner
  predicate `HasTorAmplitudeIn` before and after applying the canonical base-change owner
  `derivedTensorWithAlgebra (algebraMap R' R)`;
- primitive vs. derived:
  primitive data are the nilpotent thickening hypotheses on `R' → R`, the derived object
  `K' : D(R')`, and the interval bounds `a, b`;
  the base-changed object `K' ⊗[R']^L[R]` is derived API through the existing scalar-extension
  owner, so this file should depend directly on the owner file `15_60_1_1` rather than on the
  later change-of-rings bridge in `Lemma_15_60_1`;
- source/core/bridge triage:
  `source-facing`: tor-amplitude is equivalent before and after base change along a surjective map
    with nilpotent kernel;
  `core/canonical`: `HasTorAmplitudeIn` and `derivedTensorWithAlgebra`;
  `bridge/view`: the notation `K' ⊗[R']^L[R]` for applying the owner functor to `K'`. -/

-- Proof sketch: the forward implication is Lemma `15.67.13`, since tor-amplitude is preserved by
-- derived base change. For the converse, induct on the nilpotence exponent of
-- `RingHom.ker (algebraMap R' R)` and use the distinguished triangle attached to
-- `0 → I M' → M' → M' / I M' → 0` for an arbitrary `R'`-module `M'`, reducing first to the case
-- where the kernel acts trivially so that `M'` descends to an `R`-module.
/-- Lemma 15.67.20: for a surjective ring map `R' → R` with nilpotent kernel, an object
`K'` of `D(R')` has tor-amplitude in `[a, b]` if and only if its derived base change
`K' \otimes_{R'}^{\mathbf L} R` has tor-amplitude in `[a, b]` in `D(R)`. -/
theorem hasTorAmplitudeIn_derivedTensorWithAlgebra_iff_of_surjective_of_nilpotent_ker
    (hsurj : Function.Surjective (algebraMap R' R))
    (hker : IsNilpotent (RingHom.ker (algebraMap R' R)))
    (K' : DModRPrime) (a b : ℤ) :
    HasTorAmplitudeIn (K' ⊗[R']^L[R]) a b ↔
      HasTorAmplitudeIn K' a b := sorry

end

end CategoryTheory
