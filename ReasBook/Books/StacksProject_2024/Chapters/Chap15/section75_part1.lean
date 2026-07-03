import Mathlib
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.LinearAlgebra.Dimension.Finite

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_75_1 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

variable {R : Type u} [Ring R]

attribute [local instance] HasDerivedCategory.standard

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "DMod" => DerivedCategory (ModuleCat R)
private abbrev Q : Cpx ⥤ DMod := DerivedCategory.Q

namespace CochainComplex

/-- A cochain complex of `R`-modules is bounded finite projective if it is bounded on both sides
and each term is a finite projective `R`-module. -/
class IsBoundedFiniteProjective (L : Cpx) : Prop where
  /-- The complex is bounded on both sides. -/
  bounded : ∃ a b : ℤ, L.IsStrictlyGE a ∧ L.IsStrictlyLE b
  /-- Each term is a finite `R`-module. -/
  finite (n : ℤ) : Module.Finite R (L.X n)
  /-- Each term is a projective `R`-module. -/
  projective (n : ℤ) : Module.Projective R (L.X n)

/-- A bounded finite-projective complex is exactly a bounded complex with termwise finite
projective terms. -/
theorem isBoundedFiniteProjective_iff (L : Cpx) :
    IsBoundedFiniteProjective L ↔
      (∃ a b : ℤ, L.IsStrictlyGE a ∧ L.IsStrictlyLE b) ∧
        (∀ n : ℤ, Module.Finite R (L.X n)) ∧
          ∀ n : ℤ, Module.Projective R (L.X n) := by
  constructor
  · intro h
    exact ⟨h.bounded, h.finite, h.projective⟩
  · rintro ⟨hbounded, hfinite, hprojective⟩
    exact ⟨hbounded, hfinite, hprojective⟩

/-- Terms of a bounded finite projective complex are finite modules. -/
instance (L : Cpx) [h : IsBoundedFiniteProjective L] (n : ℤ) :
    Module.Finite R (L.X n) :=
  h.finite n

/-- Terms of a bounded finite projective complex are projective modules. -/
instance (L : Cpx) [h : IsBoundedFiniteProjective L] (n : ℤ) :
    Module.Projective R (L.X n) :=
  h.projective n

end CochainComplex

namespace DerivedCategory

/-- Definition 15.75.1 (1): An object of `D(R)` is perfect if it is isomorphic in the derived
category to a bounded cochain complex of finite projective `R`-modules. -/
def IsPerfect (K : DMod) : Prop :=
  ∃ (L : Cpx) (_ : K ≅ Q.obj L),
    CochainComplex.IsBoundedFiniteProjective L

instance isPerfect_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (IsPerfect : ObjectProperty DMod) where
  of_iso e hK := by
    rcases hK with ⟨L, hL, hfinite⟩
    exact ⟨L, e.symm ≪≫ hL, hfinite⟩

end DerivedCategory

namespace ModuleCat

/-- Definition 15.75.1 (2): An `R`-module is perfect if its degree-zero complex is a perfect
object of `D(R)`. -/
abbrev IsPerfect (M : ModuleCat R) : Prop :=
  DerivedCategory.IsPerfect ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)

end ModuleCat

/-! ### Lemma_15_75_2 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "ModR" => ModuleCat R
local notation "Cpx" => CochainComplex ModR ℤ
local notation "DMod" => DerivedCategory ModR

/- Domain-style sampling for Lemma 15.75.2:
- primary domain: perfect objects in `D(R)` and their concrete finite-projective representatives;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `DerivedCategory.IsPseudoCoherent`,
  `HasTorAmplitudeIn`,
  `finiteProjectiveModuleProperty`,
  `CochainComplex.MinusWithTermsIn`;
- best owner abstraction: the main perfectness predicate is the source-facing owner
  `K.IsPerfect`, while explicit representative data should reuse the existing bounded-above owner
  `CochainComplex.MinusWithTermsIn (finiteProjectiveModuleProperty R)` rather than re-bundling
  boundedness through `CochainComplex.IsBoundedFiniteProjective` when the theorem already
  specifies the exact support interval `[a, b]`;
- primitive vs. derived:
  primitive data are the derived object `K`, the tor-amplitude interval `[a, b]`, and a
  representative complex with termwise finite-projective terms and explicit support bounds;
  the global boundedness package `CochainComplex.IsBoundedFiniteProjective` is derived from those
  explicit bounds and should not be duplicated in the representative theorem below;
- source/core/bridge triage:
  `source-facing`: perfectness characterized by pseudo-coherence and finite tor dimension;
  `core/canonical`: `K.IsPerfect`, `K.IsPseudoCoherent`, `HasFiniteTorDimension K`, and the owner
    `CochainComplex.MinusWithTermsIn (finiteProjectiveModuleProperty R)`;
  `bridge/view`: the representative theorem below, which presents perfectness data through a
    chosen bounded-above finite-projective model with fixed support bounds.
-/

-- Proof sketch: combine the bounded finite-projective representative from `IsPerfect` with
-- Lemma `15.65.5` and Lemma `15.67.3` to obtain pseudo-coherence and finite tor dimension, and
-- conversely use a bounded flat representative in the given tor-amplitude range together with
-- Lemma `15.67.2` and Algebra, Lemma `10.78.2` to replace the leftmost flat term by a finite
-- projective module.
/-- Lemma 15.75.2: an object `K^•` of `D(R)` is perfect if and only if it is pseudo-coherent and
has finite tor dimension. -/
theorem isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension
    (K : DMod) :
    K.IsPerfect ↔ K.IsPseudoCoherent ∧ HasFiniteTorDimension K := sorry

-- Proof sketch: choose a bounded-above finite-free representative from pseudo-coherence, truncate
-- it below `a` using the tor-amplitude hypothesis, apply Lemma `15.67.2` to show the new degree
-- `a` term is flat, and then invoke Algebra, Lemma `10.78.2` to upgrade that finite flat module
-- to a finite projective one. The bounded-above finite-projective data are then recorded through
-- the canonical owner `CochainComplex.MinusWithTermsIn (finiteProjectiveModuleProperty R)`, while
-- the explicit lower and upper support bounds remain separate source-facing data.
/-- For a pseudo-coherent object, tor-amplitude in `[a, b]` yields a
representative by finite projective `R`-modules concentrated in degrees `[a, b]`. -/
theorem exists_strictlySupported_finiteProjective_complex_of_isPseudoCoherent_of_hasTorAmplitudeIn
    {K : DMod} {a b : ℤ}
    (hKpc : K.IsPseudoCoherent) (hamp : HasTorAmplitudeIn K a b) :
    ∃ E : CochainComplex.MinusWithTermsIn (finiteProjectiveModuleProperty R),
      ∃ (_ : K ≅ DerivedCategory.Q.obj (E : Cpx)),
        (E : Cpx).IsStrictlyGE a ∧ (E : Cpx).IsStrictlyLE b := sorry

end

end CategoryTheory

/-! ### Lemma_15_75_3 (from Chap15) -/
universe u

open CategoryTheory

section

variable {R : Type u} [CommRing R]

namespace ModuleCat

/- The module-level perfectness owner is the degree-zero specialization of the derived owner
`DerivedCategory.IsPerfect`, so the canonical characterization from Lemma `15.75.2` should be
available directly at this owner level. -/
/-- An `R`-module is perfect exactly when it is pseudo-coherent and has finite tor dimension. -/
theorem isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension
    (M : ModuleCat R) :
    M.IsPerfect ↔ M.IsPseudoCoherent ∧ ModuleHasFiniteTorDimension M := by
  simpa [ModuleCat.IsPerfect, ModuleCat.IsPseudoCoherent, ModuleHasFiniteTorDimension] using
    (CategoryTheory.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension
      (ModuleCat.single0Functor.obj M))

/- Domain-style sampling for Lemma 15.75.3:
- primary domain: perfect modules over a commutative ring, compared with bounded finite
  projective resolutions;
- sampled owner declarations:
  `ModuleCat.IsPerfect`,
  `CategoryTheory.HasProjectiveDimensionLE`,
  `ModuleCat.HasFiniteProjectiveResolutionLengthLEWithFiniteTerms`,
  `CategoryTheory.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension`;
- best owner abstraction: the source-facing owner remains `M.IsPerfect`, while the concrete
  finite-resolution side should reuse the existing Chapter 10 owner
  `HasFiniteProjectiveResolutionLengthLEWithFiniteTerms` rather than a new local wrapper;
- primitive vs. derived:
  primitive data are the module `M` and the chosen resolution length `d`;
  the finite-projective resolution itself is owned upstream in Chapter 10, and the perfectness
  predicate is owned by Definition `15.75.1`;
- source/core/bridge triage:
  `source-facing`: the equivalence below;
  `core/canonical`: `ModuleCat.IsPerfect` and
    `HasFiniteProjectiveResolutionLengthLEWithFiniteTerms`;
  `bridge/view`: Chapter 10's projective-dimension interface sitting behind the proof.

This file should therefore keep the textbook equivalence, but phrase it directly in terms of the
existing owners instead of introducing any parallel resolution packaging.
-/

-- Proof sketch: identify perfect modules with pseudo-coherent modules of finite tor dimension via
-- Lemma `15.75.2`; then use the finite-free resolution description of pseudo-coherence together
-- with the truncation argument from the text to replace the leftmost sufficiently high syzygy by a
-- finite projective module, producing a finite projective resolution. Conversely, a finite
-- projective resolution is a bounded finite-projective complex representing `M[0]`, hence `M` is
-- perfect.
/-- Lemma 15.75.3: an `R`-module is perfect if and only if there exists a finite resolution
`0 ⟶ F_d ⟶ ⋯ ⟶ F₁ ⟶ F₀ ⟶ M ⟶ 0` in which every `Fᵢ` is a finite projective `R`-module. -/
theorem isPerfect_iff_exists_finiteProjectiveResolutionLengthLEWithFiniteTerms
    (M : ModuleCat R) :
    M.IsPerfect ↔ ∃ d : ℕ, HasFiniteProjectiveResolutionLengthLEWithFiniteTerms M d := sorry

-- Proof sketch: choose the finite projective resolution supplied by the previous equivalence and
-- forget the projective structure to obtain a finite flat resolution of the same length. Then use
-- the canonical tor-dimension/flat-resolution bridge from Lemma `15.67.6`.
/-- A perfect `R`-module has tor dimension at most some finite integer. -/
theorem exists_moduleHasTorDimensionLE_of_isPerfect
    (M : ModuleCat R) (hM : M.IsPerfect) :
    ∃ d : ℕ, ModuleHasTorDimensionLE M d := by
  rcases
      (isPerfect_iff_exists_finiteProjectiveResolutionLengthLEWithFiniteTerms M).1 hM with
    ⟨d, hd⟩
  refine ⟨d, ?_⟩
  apply ModuleCat.HasFiniteFlatResolutionLengthLE.hasTorDimensionLE
  cases d with
  | zero =>
      change Module.Flat R M
      let _ : Module.Projective R M := by
        simpa [ModuleCat.HasFiniteProjectiveResolutionLengthLEWithFiniteTerms] using hd.1
      infer_instance
  | succ n =>
      rcases hd with ⟨P, δ, π, hπ, hδπ, hδ, hinj⟩
      refine ⟨fun i ↦ (P i).obj, ?_, ⟨fun i ↦ (δ i).hom, π, hπ, hδπ, hδ, hinj⟩⟩
      intro i
      let _ : Module.Projective R (P i).obj := (P i).property.2
      infer_instance

end ModuleCat

end

/-! ### Lemma_15_75_4 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "PerfectObj" => (DerivedCategory.IsPerfect : ObjectProperty DMod)

/- Domain-style sampling for Lemma 15.75.4:
- primary domain: perfect objects in the derived category `D(R)` as an object property and their
  behavior with respect to distinguished triangles;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `CochainComplex.IsBoundedFiniteProjective`,
  `ObjectProperty.IsTriangulated`,
  `ObjectProperty.IsStableUnderShift`;
- best owner abstraction: the canonical owner is the object property `PerfectObj`, and this file
  should expose its `ObjectProperty.IsTriangulated` instance directly rather than introducing a
  parallel eta-expanded surface for the same object property;
- primitive vs. derived:
  primitive data are the perfectness predicate `DerivedCategory.IsPerfect` and its defining
  bounded finite-projective representatives from Definition `15.75.1`;
  derived API is the triangulated closure statement for the perfectness object property;
- source/core/bridge triage:
  `source-facing`: the textbook two-out-of-three statement for perfect complexes in distinguished
    triangles;
  `core/canonical`: `ObjectProperty.IsTriangulated PerfectObj`;
  `bridge/view`: concrete bounded finite-projective representatives witnessing perfectness.

This file targets the `core/canonical` layer so downstream files can reuse the owner instance
directly instead of redeclaring parallel local copies.
-/
-- Proof sketch: use the canonical owner-level two-out-of-three statement for perfect complexes in
-- distinguished triangles, regarding perfectness as the object property on `D(R)` defined by
-- bounded finite-projective representatives.
/-- Lemma 15.75.4: the object property of being a perfect complex in `D(R)` is triangulated.
Equivalently, in a distinguished triangle of `D(R)`, if two of the three objects are perfect,
then so is the third. -/
instance perfectObjectProperty_isTriangulated :
    ObjectProperty.IsTriangulated PerfectObj := by
  sorry

end

end CategoryTheory

/-! ### Lemma_15_75_5 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty.IsStableUnderRetracts

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "PerfectObj" => (DerivedCategory.IsPerfect : ObjectProperty DMod)

/- Domain-style sampling for Lemma 15.75.5:
- primary domain: perfect objects in the derived category `D(R)` as an object property, together
  with the generic retract/direct-summand API for additive categories;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `ObjectProperty.IsStableUnderRetracts`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_left`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_right`;
- best owner abstraction: the `core/canonical` owner is the object property `PerfectObj`; the
  textbook biproduct statement is a `bridge/view` specialization of the generic direct-summand API;
- primitive vs. derived:
  primitive data are the perfectness owner `DerivedCategory.IsPerfect` and its representative-based
  definition from Definition `15.75.1`;
  derived API is retract stability and the direct-summand consequence below.
-/

-- Proof sketch: choose a bounded finite-projective complex representing `K ⊞ L`; the projection
-- maps onto `K` and `L` split in the derived category, so degreewise splitting by projectivity
-- yields bounded finite-projective representatives of both summands.
/-- Perfect objects of `D(R)` are stable under retracts/direct summands. -/
instance perfectObjectProperty_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts PerfectObj where
  of_retract {X Y} h hY := by
    sorry

/-- Lemma 15.75.5: if the biproduct `K^• ⊕ L^•` is perfect, then both summands `K^•` and
`L^•` are perfect. -/
theorem isPerfect_summands_of_biprod
    (K L : DMod) (hKL : (K ⊞ L).IsPerfect) :
    K.IsPerfect ∧ L.IsPerfect :=
  ⟨of_biprod_left PerfectObj hKL, of_biprod_right PerfectObj hKL⟩

end

end CategoryTheory

/-! ### Lemma_15_75_6 (from Chap15) -/
noncomputable section

open CategoryTheory
open DerivedCategory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

private abbrev Q : CochainComplex (ModuleCat.{u} R) ℤ ⥤ DerivedCategory (ModuleCat.{u} R) :=
  DerivedCategory.Q
private abbrev single₀ : ModuleCat.{u} R ⥤ DerivedCategory (ModuleCat.{u} R) :=
  DerivedCategory.singleFunctor (ModuleCat.{u} R) (0 : ℤ)

/- Domain-style sampling for Lemma 15.75.6:
- primary domain: perfect complexes in `D(R)` represented by bounded cochain complexes of
  `R`-modules, together with the chapter owners for pseudo-coherence and finite tor dimension;
- sampled owner declarations:
  `Compᵇ((ModuleCat R))`,
  `Q.obj`,
  `single₀`,
  `DerivedCategory.IsPerfect`,
  `CochainComplex.isPseudoCoherent_of_boundedAbove_of_termwise`,
  `hasFiniteTorDimension_of_bounded_of_termwise_hasFiniteTorDimension`,
  `isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension`,
  `ModuleCat.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension`;
- best owner abstraction: the source-facing theorem should take its bounded complex through the
  chapter owner `Compᵇ(ModuleCat R)` rather than a raw cochain complex together with a separate
  boundedness witness, while the target owner remains the perfectness predicate on `D(R)`;
- primitive vs. derived:
  primitive data are the bounded representative `K : Compᵇ((ModuleCat R))` and the termwise
  perfectness hypotheses `(K.obj.X i).IsPerfect`;
  derived API is the perfectness of `Q.obj K.obj`, assembled from the canonical owners
  `IsPseudoCoherent` and `HasFiniteTorDimension`;
- source/core/bridge triage:
  `source-facing`: the textbook statement that a bounded complex with perfect terms is perfect;
  `core/canonical`: `Compᵇ(ModuleCat R)`, `DerivedCategory.IsPerfect`,
    `IsPseudoCoherent`, `HasFiniteTorDimension`;
  `bridge/view`: passage from the chosen bounded representative `K.obj` to its derived image
    `Q.obj K.obj`.

This file therefore stays `source-facing`, while rewriting the boundedness input to the canonical
bounded owner and using the chapter's perfectness characterization instead of a parallel local
induction wrapper.
-/

-- Proof sketch: use the module-level perfectness characterization from Lemma `15.75.3` to obtain
-- pseudo-coherence and finite tor dimension termwise. Then Lemmas `15.65.9` and `15.67.8` apply
-- to the bounded representative `K`, and Lemma `15.75.2` reassembles the resulting derived object
-- as perfect.
/-- Lemma 15.75.6: a bounded cochain complex of perfect `R`-modules is a perfect complex in
`D(R)`. -/
theorem cochainComplex_isPerfect_of_bounded_of_termwise
    (K : Compᵇ((ModuleCat R)))
    (hterm : ∀ i : ℤ, (K.obj.X i).IsPerfect) :
    (Q.obj K.obj).IsPerfect := by
  have hterm' : ∀ i : ℤ,
      (K.obj.X i).IsPseudoCoherent ∧ HasFiniteTorDimension ((single₀).obj (K.obj.X i)) := by
    intro i
    let M : ModuleCat.{u} R := K.obj.X i
    have hM : M.IsPerfect := by simpa [M] using hterm i
    have hM' : M.IsPseudoCoherent ∧ ModuleHasFiniteTorDimension M :=
      (ModuleCat.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension M).1 hM
    simpa [M, ModuleHasFiniteTorDimension] using hM'
  have hboundedAbove : CochainComplex.minus (ModuleCat.{u} R) K.obj := K.property.2
  have hpc : ∀ i : ℤ, (K.obj.X i).IsPseudoCoherent := fun i ↦ (hterm' i).1
  refine
    (isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension (Q.obj K.obj)).2 ?_
  exact ⟨CochainComplex.isPseudoCoherent_of_boundedAbove_of_termwise K.obj hboundedAbove hpc,
    hasFiniteTorDimension_of_bounded_of_termwise_hasFiniteTorDimension K
      (fun i ↦ by
        simpa [ModuleHasFiniteTorDimension] using (hterm' i).2)⟩

end

end CategoryTheory

/-! ### Lemma_15_75_7 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DbMod" => boundedDerivedCategory (ModuleCat R)
local notation "Hb" => boundedDerivedHomologyFunctor (ModuleCat R)

/- Domain-style sampling for Lemma 15.75.7:
- primary domain: perfect objects in the bounded derived category `D^b(R)`, with the cohomology
  modules viewed through the chapter owners `DerivedCategory.IsPerfect` and `ModuleCat.IsPerfect`;
- sampled owner declarations:
  `boundedDerivedCategory`,
  `boundedDerivedHomologyFunctor`,
  `DerivedCategory.IsPerfect`,
  `ModuleCat.IsPerfect`,
  `boundedAbove_isPseudoCoherent_of_homology`,
  `hasFiniteTorDimension_of_bounded_of_homology_hasFiniteTorDimension`,
  `isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension`;
- best owner abstraction: this item is `source-facing`, while the `core/canonical` owners are the
  bounded derived category `DbMod`, the perfectness owner `K.obj.IsPerfect`, and the owner-level
  reductions to pseudo-coherence and finite tor dimension;
- primitive vs. derived:
  primitive data are the bounded derived object `K` and the degreewise hypotheses that each
  bounded-derived cohomology module `((Hb i).obj K)` is perfect;
  derived API is the conclusion that the bounded derived object itself is perfect, obtained by
  reusing the chapter owners for pseudo-coherence and tor dimension rather than introducing a
  parallel local wrapper;
- source/core/bridge triage:
  `source-facing`: the theorem below about bounded derived complexes with perfect cohomology;
  `core/canonical`: `DbMod`, `DerivedCategory.IsPerfect`, `K.IsPseudoCoherent`, and
    `HasFiniteTorDimension K`;
  `bridge/view`: the bounded-derived cohomology functors `Hb i` landing in modules, where
    perfectness is read by the module-level owner `ModuleCat.IsPerfect`.

This file should therefore keep the source-facing bounded-derived theorem, while phrasing its
surface directly with the chapter owners instead of a parallel local API.
-/

-- Proof sketch: apply `boundedAbove_isPseudoCoherent_of_homology` to the bounded object `K.obj`
-- and the perfect cohomology hypotheses to obtain pseudo-coherence, use
-- `hasFiniteTorDimension_of_bounded_of_homology_hasFiniteTorDimension` degreewise to obtain
-- finite tor dimension, and conclude by
-- `isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension`.
/-- Lemma 15.75.7: if a bounded derived `R`-complex has perfect cohomology modules in every
degree, then the complex itself is perfect. -/
theorem isPerfect_of_bounded_of_homology_isPerfect
    (K : DbMod)
    (hH : ∀ i : ℤ, ((Hb i).obj K).IsPerfect) :
    K.obj.IsPerfect := sorry

end

end CategoryTheory

/-! ### Lemma_15_75_8 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModB" => DerivedCategory (ModuleCat B)

/- Domain-style sampling for Lemma 15.75.8:
- primary domain: perfect objects in derived categories under restriction of scalars along the
  algebra map `A → B`;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `ModuleCat.IsPerfect`,
  `isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension`,
  `isPseudoCoherent_iff_restrictScalars`,
  `hasTorAmplitudeIn_restrictScalars_of_moduleHasTorDimensionLE`;
- best owner abstraction: this theorem is a `source-facing` restriction-of-scalars bridge for
  perfectness, while the actual restriction construction is owned canonically by the exact derived
  functor `(ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory`; the assumption that
  `B` is perfect as an `A`-module is kept as the source-faithful hypothesis rather than being
  replaced by the later ring-map owner `RingHom.IsPerfectRingMap`, which lives at a different
  layer;
- primitive vs. derived:
  primitive data are the derived `B`-complex `K`, the perfectness hypothesis on the `A`-module
  `B`, and the perfectness hypothesis on `K`;
  derived API is the perfectness statement for the restricted object
  `((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)`;
- source/core/bridge triage:
  `source-facing`: `isPerfect_restrictScalars_of_module_isPerfect`;
  `core/canonical`: `K.IsPerfect`, `(ModuleCat.of A B).IsPerfect`, and the functor
    `(ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory`;
  `bridge/view`: the restriction-of-scalars image
    `((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)`.
-/

-- Proof sketch: apply Lemma `15.75.2` to the perfect `A`-module `B` and to the perfect
-- `B`-complex `K` to obtain pseudo-coherence and finite tor dimension. Use
-- `isPseudoCoherent_iff_restrictScalars` for the pseudo-coherent part and
-- `hasTorAmplitudeIn_restrictScalars_of_moduleHasTorDimensionLE` for a finite tor-amplitude
-- interval after restriction of scalars. Then reassemble perfection with Lemma `15.75.2`.
/-- Lemma 15.75.8: if `A → B` is a ring map, `B` is perfect as an `A`-module, and `K^•` is
perfect over `B`, then `K^•` is perfect over `A` after restriction of scalars. -/
theorem isPerfect_restrictScalars_of_module_isPerfect
    (K : DModB) (hB : (ModuleCat.of A B).IsPerfect) (hK : K.IsPerfect) :
    (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K : DModA)).IsPerfect :=
      sorry

end

end CategoryTheory

/-! ### Lemma_15_75_9 (from Chap15) -/
noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "DModA" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.75.9:
- primary domain: preservation of perfect objects in derived categories under derived scalar
  extension;
- sampled owner declarations:
  `K.IsPerfect`,
  `derivedTensorWithAlgebra`,
  `derivedTensorWithAlgebra_isPseudoCoherent`,
  `hasTorAmplitudeIn_derivedTensorWithAlgebra`;
- best owner abstraction: the theorem is source-facing, while the core/canonical owners are
  `K.IsPerfect` and the derived base-change object `K ⊗[A]^L[B]`;
- primitive vs. derived:
  primitive data are the perfect object `K` and the algebra map `A → B`;
  the preservation statement is derived API over those existing owners, so the public surface
  should use the owner notation rather than a raw functor application term;
- source/core/bridge triage:
  `source-facing`: perfectness is preserved by derived base change;
  `core/canonical`: `K.IsPerfect` and `derivedTensorWithAlgebra`;
  `bridge/view`: the notation `K ⊗[A]^L[B]` for the owner applied to `K`. -/

-- Proof sketch: combine Lemma `15.75.2`, which characterizes perfect objects as the
-- pseudo-coherent objects of finite tor dimension, with Lemma `15.65.12` for preservation of
-- pseudo-coherence under derived scalar extension and Lemma `15.67.13` for preservation of tor
-- amplitude, hence of finite tor dimension.
/-- Lemma 15.75.9: if `K^•` is a perfect complex of `A`-modules, then its derived base change
`K^• \otimes_A^{\mathbf L} B` is a perfect complex of `B`-modules. -/
theorem derivedTensorWithAlgebra_isPerfect
    (K : DModA) (hK : K.IsPerfect) :
    (K ⊗[A]^L[B]).IsPerfect := sorry

end

end CategoryTheory

/-! ### Lemma_15_75_10 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "Ext" => ModuleCat.extendScalars (algebraMap A B)

/- Domain-style sampling for Lemma 15.75.10:
- primary domain: perfect modules viewed in degree `0` inside derived module categories and then
  transported across flat scalar extension;
- sampled owner declarations:
  `ModuleCat.IsPerfect`,
  `ModuleCat.IsPseudoCoherent`,
  `ModuleHasTorDimensionLE`,
  `CategoryTheory.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension`,
  `ModuleCat.exists_moduleHasTorDimensionLE_of_isPerfect`;
- best owner abstraction: this file is a `bridge/view`; the source-facing module statement should
  keep `ModuleCat.IsPerfect` as the owner, but derive the base-change statement from the canonical
  perfectness characterization by pseudo-coherence and finite tor dimension, together with the
  existing module-level flat base-change bridges for those two ingredients;
- primitive vs. derived:
  primitive data are the flat map `A → B`, the module `M`, and the owner hypothesis `M.IsPerfect`;
  the derived API used here is pseudo-coherence and finite tor dimension of `M[0]`, repackaged
  canonically as `M.IsPseudoCoherent` and `ModuleHasFiniteTorDimension M`, then transported across
  flat scalar extension and reassembled into perfectness;
- source/core/bridge triage:
  `source-facing`: perfectness is preserved by flat scalar extension for modules;
  `core/canonical`: `DerivedCategory.IsPerfect`, `ModuleCat.IsPerfect`,
    `ModuleCat.IsPseudoCoherent`, and `HasFiniteTorDimension`;
  `bridge/view`: the module-level flat base-change theorems for pseudo-coherence and tor
    dimension. -/

-- Proof sketch: decompose `hM : M.IsPerfect` into pseudo-coherence plus finite tor dimension
-- using the owner theorem `ModuleCat.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension`.
-- Transport pseudo-coherence by Lemma `15.65.13` and a finite tor-dimension bound by
-- Lemma `15.67.14`, then reassemble perfectness over `B` with the same owner theorem.
/-- Lemma 15.75.10: for a flat ring map `A → B`, the base change of a perfect `A`-module is a
perfect `B`-module. This is the module-level bridge/view of Lemma `15.75.9`. -/
theorem isPerfect_extendScalars
    (hflat : (algebraMap A B).Flat) (M : ModuleCat.{u} A) (hM : M.IsPerfect) :
    ((Ext).obj M).IsPerfect := by
  have hpcA : M.IsPseudoCoherent :=
    (ModuleCat.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension M).1 hM |>.1
  have hpcB : ((Ext).obj M).IsPseudoCoherent :=
    isPseudoCoherent_extendScalars hflat M hpcA
  rcases ModuleCat.exists_moduleHasTorDimensionLE_of_isPerfect M hM with ⟨d, hd⟩
  have htorB : ModuleHasFiniteTorDimension ((Ext).obj M) :=
    (moduleHasTorDimensionLE_extendScalars hflat M d hd).hasFiniteTorDimension
  exact
    (ModuleCat.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension ((Ext).obj M)).2
      ⟨hpcB, htorB⟩

end

end CategoryTheory

/-! ### Lemma_15_75_11 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.MonoidalCategory
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling for Lemma 15.75.11:
- primary domain: closure of perfect objects in derived module categories under the monoidal tensor
  on `D(R)` and its source-facing derived-tensor presentation;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `derivedCategory_tensorObj_iso_derivedTensorProduct`,
  the owner tensor object `K ⊗ L`,
  `derivedTensorWithAlgebra_isPerfect` as the base-change analogue;
- best owner abstraction: the `core/canonical` owner is the monoidal tensor object `K ⊗ L`,
  while the textbook notation `K ⊗[R]^L L` is a `bridge/view` through
  `derivedCategory_tensorObj_iso_derivedTensorProduct`;
- primitive vs. derived:
  primitive data are the perfect objects `K` and `L`;
  closure under tensor is derived API and should use the owner tensor `K ⊗ L`; the source-facing
  notation `K ⊗[R]^L L` is derived from that owner via the canonical comparison isomorphism;
- source/core/bridge triage:
  `source-facing`: perfect objects are stable under the textbook derived tensor product;
  `core/canonical`: `DerivedCategory.IsPerfect` and the monoidal tensor `K ⊗ L`;
  `bridge/view`: `derivedCategory_tensorObj_iso_derivedTensorProduct` identifying `K ⊗ L` with
    `K ⊗[R]^L L`. -/

-- Proof sketch: by Lemma `15.75.2`, it suffices to show that the derived tensor product of two
-- perfect objects is pseudo-coherent and has finite tor dimension. Pseudo-coherence follows from
-- Lemma `15.65.16 (2)`, while finite tor dimension is obtained by choosing tor-amplitude
-- intervals for `K` and `L` from Lemma `15.75.2` and applying Lemma `15.67.10` with `A = B = R`.
/-- Core owner form of Lemma 15.75.11: the monoidal tensor of two perfect objects of `D(R)` is
again perfect. -/
theorem tensor_isPerfect_of_isPerfect
    (K L : DMod)
    (hK : K.IsPerfect)
    (hL : L.IsPerfect) :
    (K ⊗ L).IsPerfect := sorry

/-- Lemma 15.75.11: if `K` and `L` are perfect objects of `D(R)`, then their derived tensor
product `K \otimes_R^{\mathbf L} L` is again a perfect object. -/
theorem isPerfect_derivedTensorProduct
    (K L : DMod)
    (hK : K.IsPerfect)
    (hL : L.IsPerfect) :
    (K ⊗[R]^L L).IsPerfect := by
  let P : ObjectProperty DMod := DerivedCategory.IsPerfect
  exact
    P.prop_of_iso
      (derivedCategory_tensorObj_iso_derivedTensorProduct K L)
      (tensor_isPerfect_of_isPerfect K L hK hL)

end

end CategoryTheory

/-! ### Lemma_15_75_12 (from Chap15) -/
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

/- Domain-style sampling for Lemma 15.75.12:
- primary domain: local-global perfection in `D(R)` under localization away from a finite
  principal-open cover;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `isPseudoCoherent_of_localizationAway_unitIdeal`,
  `hasTorAmplitudeIn_of_localizationAway_unitIdeal`,
  `isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension`;
- best owner abstraction: this item is `source-facing`, while the canonical owners are
  `DerivedCategory.IsPerfect` with object-prefix theorem surface `K.IsPerfect`,
  `K.IsPseudoCoherent`, and `HasFiniteTorDimension K`;
- primitive vs. derived:
  the primitive data are the finite family `f`, the unit-ideal hypothesis, and the localized
  perfectness assumptions;
  pseudo-coherence and finite tor dimension are derived owner-level consequences and should not be
  stored as parallel local data;
- source/core/bridge triage:
  `source-facing`: perfection descends from a finite localization-away cover;
  `core/canonical`: the perfectness characterization by pseudo-coherence and finite tor dimension;
  `bridge/view`: the localized derived base-change objects
    `K ⊗[R]^L[Localization.Away (f i)]`. -/

-- Proof sketch: use Lemma `15.75.2` to reduce perfection to pseudo-coherence and finite tor
-- dimension. Pseudo-coherence descends directly by Lemma `15.65.14 (2)`. For finite tor
-- dimension, choose a tor-amplitude interval on each localization, enlarge them to one common
-- interval over the finite index set, descend that uniform tor-amplitude by Lemma `15.67.16`, and
-- then reassemble perfection with Lemma `15.75.2`.
/-- Lemma 15.75.12: if a finite family `f : ι → R` generates the unit ideal and each derived
localization `K^• ⊗_R R_{f_i}` is perfect, then `K^•` is perfect. -/
theorem isPerfect_of_localizationAway_unitIdeal
    (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤) (K : DMod)
    (hloc : ∀ i, (K ⊗[R]^L[Localization.Away (f i)]).IsPerfect) :
    K.IsPerfect := sorry

end

end CategoryTheory

/-! ### Lemma_15_75_13 (from Chap15) -/
noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R R' : Type u} [CommRing R] [CommRing R']

/- Domain-style sampling for Lemma 15.75.13:
- primary domain: faithful-flat descent of perfect objects in derived module categories;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension`,
  `isPseudoCoherent_of_faithfullyFlat_baseChange`,
  `derivedTensorWithAlgebra`,
  `hasTorAmplitudeIn_of_faithfullyFlat_baseChange`;
- best owner abstraction: this item is `source-facing`, while the `core/canonical` owner is
  `DerivedCategory.IsPerfect`; the ring map itself should remain explicit in the public statement,
  and the derived scalar-extension owner should appear directly as `derivedTensorWithAlgebra f`,
  with the algebra-based tensor notation reserved for the bridge view;
- primitive vs. derived:
  primitive data are the ring map `f`, the derived object `K`, the faithfully flatness of `f`,
  and the perfectness of the derived base change;
  pseudo-coherence and tor-amplitude are derived API used to recover the owner predicate, so they
  should not be repackaged as parallel public data here;
- source/core/bridge triage:
  `source-facing`: faithful-flat descent of perfectness;
  `core/canonical`: `DerivedCategory.IsPerfect`;
  `bridge/view`: the passage from `((derivedTensorWithAlgebra f).obj K)` to the standard derived
    base-change notation `K ⊗[R]^L[R']` after passing from `f` to `f.toAlgebra`.

This file therefore stays at the `source-facing` layer but uses the chapter owner predicate and
the standard derived base-change surface, while keeping the ring map explicit instead of hiding it
in an ambient algebra instance.
-/

-- Proof sketch: use Lemma `15.75.2` to reduce perfection to pseudo-coherence plus finite tor
-- dimension. Descend pseudo-coherence from the faithfully flat base change by Lemma `15.65.15`,
-- and descend finite tor dimension from the faithfully flat base change by Lemma `15.67.17`
-- through the tor-amplitude characterization.
/-- Lemma 15.75.13: if the derived base change of `K^•` along a faithfully flat ring map
`R → R'` is perfect, then `K^•` is already perfect. -/
theorem isPerfect_of_faithfullyFlat_baseChange
    (f : R →+* R') (K : DerivedCategory (ModuleCat.{u} R)) (hff : f.FaithfullyFlat)
    (hK : ((derivedTensorWithAlgebra f).obj K).IsPerfect) :
    K.IsPerfect := by
  let K' : DerivedCategory (ModuleCat.{u} R') := (derivedTensorWithAlgebra f).obj K
  have hK' : K'.IsPerfect := by
    simpa [K'] using hK
  have hbase :
      K'.IsPseudoCoherent ∧ HasFiniteTorDimension K' :=
    (isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension K').1 hK'
  refine (isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension K).2 ?_
  refine ⟨?_, ?_⟩
  · exact isPseudoCoherent_of_faithfullyFlat_baseChange f K hff hbase.1
  · rcases (hasFiniteTorDimension_iff K').1 hbase.2 with ⟨a, b, htor⟩
    exact
      (hasTorAmplitudeIn_of_faithfullyFlat_baseChange f K a b hff
        htor).hasFiniteTorDimension

end

end CategoryTheory

/-! ### Lemma_15_75_14 (from Chap15) -/
noncomputable section

open CategoryTheory
open DerivedCategory.TStructure

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {R : Type u} [CommRing R] [IsRegularRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "Bounded" => (t.bounded : ObjectProperty DMod)
local notation:max "H^" i:max => DerivedCategory.homologyFunctor (ModuleCat R) i

/- Domain-style sampling for Lemma 15.75.14:
- primary domain: perfect objects in derived categories of modules over a regular ring;
- sampled owner declarations:
  `ModuleCat.IsPerfect`,
  `DerivedCategory.IsPerfect`,
  `t.bounded`,
  `DerivedCategory.homologyFunctor`;
- best owner abstraction:
  part `(1)` is `source-facing` at the module level, while part `(2)` is `source-facing` on
  `D(R)` with boundedness read through the canonical owner `t.bounded`
  and cohomology read through the canonical owner `DerivedCategory.homologyFunctor`;
- primitive vs. derived:
  primitive data are a module `M` or a derived object `K`;
  derived API is perfectness, boundedness, and the degreewise finiteness condition on the
  cohomology modules;
- source/core/bridge triage:
  `source-facing`: the two equivalences below;
  `core/canonical`: `ModuleCat.IsPerfect`, `DerivedCategory.IsPerfect`, and
    `t.bounded`;
  `bridge/view`: the cohomology functors `H^i` landing in `ModuleCat R`.

This file should therefore keep the textbook equivalences, but phrase boundedness through the
canonical `t`-structure owner directly and avoid depending on the later parallel bounded-derived
API file.
-/

namespace ModuleCat

-- Proof sketch: for the forward implication, unwind perfection to a bounded finite-projective
-- representative and note that its degree-zero homology is finite over the Noetherian ring `R`.
-- For the converse, apply Lemma `15.75.3` together with regularity of `R` to obtain a finite
-- projective resolution of a finite module, hence a perfect representative.
/-- Lemma 15.75.14 (1): over a regular ring `R`, an `R`-module is perfect if and only if it is a
finite `R`-module. -/
theorem isPerfect_iff_finite (M : ModuleCat R) :
    M.IsPerfect ↔ Module.Finite R M := sorry

end ModuleCat

-- Proof sketch: if `K` is perfect, represent it by a bounded complex of finite projective
-- modules; this gives bounded cohomology and finite homology modules. Conversely, if `K` lies in
-- `D^b(R)` with finite cohomology, apply part `(1)` degreewise to see that each `H^i(K)` is a
-- perfect module, then use Lemma `15.75.7` to recover perfection of `K`.
/-- Lemma 15.75.14 (2): over a regular ring `R`, a derived `R`-complex is perfect if and only if
it belongs to `D^b(R)` and each cohomology module is finite. -/
theorem isPerfect_iff_bounded_and_finite_homology
    (K : DMod) :
    K.IsPerfect ↔
      Bounded K ∧
        ∀ i : ℤ, Module.Finite R ((H^i).obj K) := sorry

end

/-! ### Lemma_15_75_15 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open Opposite

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "RHomPkg" => MonoidalClosed DMod
local notation "𝓗" => DerivedCategory.homologyFunctor (ModuleCat A)

open scoped DerivedInternalHom
open scoped DerivedExt
open scoped DerivedTensorProduct

/- Domain-style sampling for Lemma 15.75.15:
- primary domain: rigid duality for perfect objects of `D(A)`, expressed through the canonical
  tensor owner `derivedTensorProduct`, the monoidal-closed owner `MonoidalClosed DMod`, and the
  monoidal duality owner `ExactPairing`;
- sampled owner declarations:
  `CategoryTheory.derivedTensorProduct`,
  the source-facing notation `RHom[H](K, L)`,
  `CategoryTheory.MonoidalClosed.derivedTensorAdj`,
  `CategoryTheory.derivedInternalHom_comp`,
  `CategoryTheory.derivedHom_cohomology_iso_shiftedHom`,
  `CategoryTheory.ExactPairing`;
- best owner abstraction:
  `source-facing`: the derived dual `K^∨ = RHom_A(K, A[0])` and the canonical comparison maps
  appearing in parts `(2)` to `(4)`;
  `core/canonical`: `derivedTensorProduct`, `RHom[H](K, L)`, `ExactPairing`, and the chapter owner
  `derivedHom_cohomology_iso_shiftedHom` for `H^n(RHom)` versus `ShiftedHom`;
  `bridge/view`: the right-unit identifications for `A[0]`, the bidual comparison morphism, the
  tensor-to-Hom comparison natural transformation below, and the degree-zero passage from
  `ShiftedHom K L 0` to `K ⟶ L`.

Primitive data are only the chosen monoidal-closed owner `H` and the canonical tensor unit
`A[0]`. The bidual map, tensor/Hom comparison, degree-zero comparison, and exact-pairing package
are derived API and should therefore be exposed as actual morphisms and natural transformations,
not hidden behind `Nonempty` wrappers.
-/

/-- The derived dual `K^\vee = R\mathrm{Hom}_A(K, A[0])` attached to a chosen derived
internal-Hom package on `D(A)`. -/
abbrev derivedDual (H : RHomPkg) (K : DMod) : DMod :=
  RHom[H](K, ringSingle)

notation:max K:max "ᵛ⟮" H:max "⟯" => derivedDual H K

/-- The contravariant map on derived duals induced by a morphism in `D(A)`. -/
abbrev derivedDualMap
    (H : RHomPkg) {K L : DMod} (f : K ⟶ L) :
    Lᵛ⟮H⟯ ⟶ Kᵛ⟮H⟯ :=
  derivedInternalHomMap H f (𝟙 ringSingle)

/-- The canonical evaluation morphism
`K^\vee \otimes_A^{\mathbf L} K \to A[0]`. -/
private noncomputable def derivedDualEvaluationDerivedTensor
    (H : RHomPkg) (K : DMod) :
    Kᵛ⟮H⟯ ⊗[A]^L K ⟶ ringSingle :=
  (H.derivedTensorAdj K).counit.app ringSingle

private noncomputable def derivedDualTensorEvaluation
    (H : RHomPkg) (K : DMod) :
    K ⊗[A]^L Kᵛ⟮H⟯ ⟶ ringSingle :=
  (derivedTensorProduct_comm K Kᵛ⟮H⟯).hom ≫
    derivedDualEvaluationDerivedTensor H K

private noncomputable def derivedInternalHomIdUnit
    (H : RHomPkg) (K : DMod) :
    ringSingle ⟶ RHom[H](K, K) :=
  letI : MonoidalClosed DMod := H
  (H.derivedTensorAdj K).homEquiv ringSingle K (singleZeroDerivedTensorIso K).hom

private noncomputable def derivedInternalHomUnitComparison
    (H : RHomPkg) (L : DMod) :
    L ⟶ RHom[H](ringSingle, L) :=
  letI : MonoidalClosed DMod := H
  (H.derivedTensorAdj ringSingle).homEquiv L L
    ((derivedTensorProduct_comm L ringSingle ≪≫ singleZeroDerivedTensorIso L).hom)

-- Proof sketch: this is the evaluation morphism
-- `K \otimes_A^{\mathbf L} K^\vee \to A[0]` transposed across the adjunction
-- `- \otimes_A^{\mathbf L} K^\vee ⊣ R\mathrm{Hom}_A(K^\vee, -)`.
/-- The canonical bidual comparison morphism
`K \to (K^\vee)^\vee`. -/
noncomputable def derivedDualBidualComparison
    (H : RHomPkg) (K : DMod) :
    K ⟶ (Kᵛ⟮H⟯)ᵛ⟮H⟯ :=
  (H.derivedTensorAdj Kᵛ⟮H⟯).homEquiv K ringSingle
    (derivedDualTensorEvaluation H K)

-- Proof sketch: choose a bounded finite-projective representative of `K`. Lemma `15.74.2`
-- identifies `RHom_A(K, A)` with the termwise dual complex, whose terms remain finite projective,
-- so the resulting object is again represented by a bounded finite-projective complex.
/-- Lemma 15.75.15 (1): if `K` is a perfect object of `D(A)`, then its derived dual
`K^\vee = R\mathrm{Hom}_A(K, A[0])` is again perfect. -/
theorem derivedDual_isPerfect
    (H : RHomPkg) {K : DMod}
    (hK : DerivedCategory.IsPerfect K) :
    DerivedCategory.IsPerfect Kᵛ⟮H⟯ := sorry

-- Proof sketch: represent `K` by a bounded finite-projective complex. Degreewise evaluation on
-- finite projective modules identifies that complex with its double dual, and the induced map in
-- the derived category is the canonical bidual comparison defined above.
/-- Lemma 15.75.15 (2): for a perfect object `K`, the canonical bidual comparison
`K \to (K^\vee)^\vee` is an isomorphism. -/
theorem perfect_iso_derivedDual_derivedDual
    (H : RHomPkg) {K : DMod}
    (hK : DerivedCategory.IsPerfect K) :
    IsIso (derivedDualBidualComparison H K) := sorry

/-- The canonical natural transformation
`- \otimes_A^{\mathbf L} K^\vee \to R\mathrm{Hom}_A(K, -)`. -/
noncomputable def derivedDualTensorComparison
    (H : RHomPkg) (K : DMod) :
    letI := H
    derivedTensorProduct Kᵛ⟮H⟯ ⟶ ihom K where
  app L :=
    (derivedTensorProduct Kᵛ⟮H⟯).map
        (derivedInternalHomUnitComparison H L) ≫
      derivedInternalHom_comp H K ringSingle L
  naturality {L₁ L₂} f := by
    sorry

/-- The canonical comparison
`K \otimes_A^{\mathbf L} K^\vee \to R\mathrm{Hom}_A(K, K)`. -/
abbrev derivedDualTensorToEnd
    (H : RHomPkg) (K : DMod) :
    K ⊗[A]^L Kᵛ⟮H⟯ ⟶ RHom[H](K, K) :=
  (derivedDualTensorComparison H K).app K

-- Proof sketch: choose a bounded finite-projective representative of `K`, let `E^•` be its
-- termwise dual, and use the left-dual pairing from Section `15.73` to identify the totalized
-- tensor functor `- ⊗_A E^•` with the Hom complex functor `Hom^•(K^•,-)`. Passing to derived
-- categories yields the canonical natural transformation above, and it is an isomorphism for a
-- perfect source complex.
/-- Lemma 15.75.15 (3): if `K` is perfect, then the canonical natural transformation
`- \otimes_A^{\mathbf L} K^\vee \to R\mathrm{Hom}_A(K,-)` is an isomorphism. -/
theorem tensor_derivedDual_iso_derivedInternalHom
    (H : RHomPkg) {K : DMod}
    (hK : DerivedCategory.IsPerfect K) :
    IsIso (derivedDualTensorComparison H K) := sorry

/-- For a perfect object, the canonical comparison
`K \otimes_A^{\mathbf L} K^\vee \to R\mathrm{Hom}_A(K, K)` is an isomorphism. -/
theorem derivedDualTensorToEnd_isIso_of_isPerfect
    (H : RHomPkg) {K : DMod}
    (hK : DerivedCategory.IsPerfect K) :
    IsIso (derivedDualTensorToEnd H K) := sorry

/-- The canonical coevaluation morphism
`A[0] \to K \otimes_A^{\mathbf L} K^\vee`,
obtained from the identity of `K` via the tensor-to-endomorphism comparison. -/
private noncomputable def derivedDualCoevaluationDerivedTensor
    (H : RHomPkg) (K : DMod)
    [IsIso (derivedDualTensorToEnd H K)] :
    ringSingle ⟶ K ⊗[A]^L Kᵛ⟮H⟯ :=
  derivedInternalHomIdUnit H K ≫
    inv (derivedDualTensorToEnd H K)

/-- The canonical evaluation morphism
`K^\vee ⊗ K \to \mathbb{1}` in the monoidal category `D(A)`. -/
noncomputable def derivedDualEvaluation
    (H : RHomPkg) (K : DMod) :
    Kᵛ⟮H⟯ ⊗ K ⟶ 𝟙_ DMod :=
  (derivedCategory_tensorObj_iso_derivedTensorProduct Kᵛ⟮H⟯ K).hom ≫
    derivedDualEvaluationDerivedTensor H K ≫
      (singleZeroIsoTensorUnit : ringSingle ≅ 𝟙_ DMod).hom

/-- The canonical coevaluation morphism
`\mathbb{1} \to K ⊗ K^\vee` in the monoidal category `D(A)`. -/
noncomputable def derivedDualCoevaluation
    (H : RHomPkg) (K : DMod)
    [IsIso (derivedDualTensorToEnd H K)] :
    𝟙_ DMod ⟶ K ⊗ Kᵛ⟮H⟯ :=
  (singleZeroIsoTensorUnit : ringSingle ≅ 𝟙_ DMod).inv ≫
    derivedDualCoevaluationDerivedTensor H K ≫
      (derivedCategory_tensorObj_iso_derivedTensorProduct K Kᵛ⟮H⟯).inv

-- Proof sketch: after transporting across the inverse of
-- `K \otimes_A^{\mathbf L} K^\vee \to R\mathrm{Hom}_A(K, K)`, the first triangle identity becomes
-- the identity of `K^\vee`.
/-- The canonical coevaluation and evaluation maps for the derived dual satisfy the first triangle
identity. -/
theorem derivedDual_coevaluation_evaluation
    (H : RHomPkg) {K : DMod}
    [IsIso (derivedDualTensorToEnd H K)] :
    Kᵛ⟮H⟯ ◁ derivedDualCoevaluation H K ≫
        (α_ _ _ _).inv ≫
        derivedDualEvaluation H K ▷ Kᵛ⟮H⟯ =
      (ρ_ Kᵛ⟮H⟯).hom ≫
        (λ_ Kᵛ⟮H⟯).inv := sorry

-- Proof sketch: transport the identity of `K` through the same tensor-to-endomorphism
-- isomorphism.
/-- The canonical coevaluation and evaluation maps for the derived dual satisfy the second
triangle identity. -/
theorem derivedDual_evaluation_coevaluation
    (H : RHomPkg) {K : DMod}
    [IsIso (derivedDualTensorToEnd H K)] :
    derivedDualCoevaluation H K ▷ K ≫
        (α_ _ _ _).hom ≫
        K ◁ derivedDualEvaluation H K =
      (λ_ K).hom ≫ (ρ_ K).inv := sorry

/-- The derived dual together with its canonical coevaluation and evaluation maps gives a left
dual once the tensor-to-endomorphism comparison is an isomorphism. -/
@[reducible] noncomputable def derivedDualExactPairingOfIsIso
    (H : RHomPkg) (K : DMod)
    [IsIso (derivedDualTensorToEnd H K)] :
    ExactPairing Kᵛ⟮H⟯ K :=
  letI : ExactPairing K Kᵛ⟮H⟯ :=
    { coevaluation' := derivedDualCoevaluation H K
      evaluation' := derivedDualEvaluation H K
      coevaluation_evaluation' := derivedDual_coevaluation_evaluation H
      evaluation_coevaluation' := derivedDual_evaluation_coevaluation H }
  BraidedCategory.exactPairing_swap K Kᵛ⟮H⟯

/-- For a perfect object, the derived dual is the canonical left dual furnished by the evaluation
and coevaluation maps above. -/
noncomputable abbrev derivedDualExactPairing
    (H : RHomPkg) {K : DMod}
    (hK : DerivedCategory.IsPerfect K) :
    ExactPairing Kᵛ⟮H⟯ K :=
  letI : IsIso (derivedDualTensorToEnd H K) :=
    derivedDualTensorToEnd_isIso_of_isPerfect H hK
  derivedDualExactPairingOfIsIso H K

/-- The induced degree-zero comparison
`H^0(L \otimes_A^{\mathbf L} K^\vee) \to H^0(R\mathrm{Hom}_A(K, L))`. -/
noncomputable def derivedDualTensorZeroCohomologyComparison
    (H : RHomPkg) (K L : DMod) :
    (𝓗 0).obj (L ⊗[A]^L Kᵛ⟮H⟯) ⟶
      (𝓗 0).obj (RHom[H](K, L)) :=
  (𝓗 0).map ((derivedDualTensorComparison H K).app L)

-- Proof sketch: apply degree-zero cohomology to the tensor/Hom comparison from part `(3)`.
/-- If `K` is perfect, then the induced degree-zero comparison
`H^0(L \otimes_A^{\mathbf L} K^\vee) \to H^0(R\mathrm{Hom}_A(K, L))` is an isomorphism. -/
theorem derivedDualTensorZeroCohomologyComparison_isIso_of_isPerfect
    (H : RHomPkg)
    {K : DMod} (hK : DerivedCategory.IsPerfect K) (L : DMod) :
    IsIso (derivedDualTensorZeroCohomologyComparison H K L) := sorry

/-- The canonical degree-zero bridge from `Ext^0_A(K, L) = ShiftedHom K L 0` to
`Hom_{D(A)}(K, L)`. -/
private noncomputable abbrev shiftedHomZeroLinearEquiv (K L : DMod) :
    Ext^((0 : ℤ))(K, L) ≃ₗ[A] (K ⟶ L) :=
  (LinearEquiv.ofBijective
      { toFun := ShiftedHom.mk₀ (0 : ℤ) rfl
        map_add' := by
          intro f g
          simp
        map_smul' := by
          intro r f
          simpa using ShiftedHom.mk₀_smul (0 : ℤ) rfl r f }
      (by
        constructor
        · intro f g hfg
          exact (ShiftedHom.homEquiv (0 : ℤ) rfl).injective <| by
            simpa using hfg
        · intro x
          refine ⟨(ShiftedHom.homEquiv (0 : ℤ) rfl).symm x, ?_⟩
          exact (ShiftedHom.homEquiv (0 : ℤ) rfl).apply_symm_apply x)).symm

/-- The canonical degree-zero comparison
`H^0(L \otimes_A^{\mathbf L} K^\vee) \to \operatorname{Ext}^0_A(K, L)`. -/
noncomputable def derivedDualTensorExtZeroComparison
    (H : RHomPkg) (K L : DMod) :
    ((𝓗 0).obj (L ⊗[A]^L Kᵛ⟮H⟯)) →ₗ[A] Ext^((0 : ℤ))(K, L) :=
  (derivedHom_cohomology_iso_shiftedHom H K L (0 : ℤ)).toLinearMap.comp
    (derivedDualTensorZeroCohomologyComparison H K L).hom

-- Proof sketch: apply degree-zero cohomology to the tensor/Hom comparison from part `(3)`, then
-- identify the target with the chapter owner `Ext^0_A(K, L)` via the standard degree-zero
-- cohomology/internal-Hom comparison.
/-- Lemma 15.75.15 (4): if `K` is perfect, then the induced degree-zero comparison
`H^0(L \otimes_A^{\mathbf L} K^\vee) \to \operatorname{Ext}^0_A(K, L)` is bijective. -/
theorem derivedDualTensorZeroCohomology_iso_extZero
    (H : RHomPkg)
    {K : DMod} (hK : DerivedCategory.IsPerfect K) (L : DMod) :
    Function.Bijective (derivedDualTensorExtZeroComparison H K L) := by
  let f := (derivedHom_cohomology_iso_shiftedHom H K L (0 : ℤ)).toLinearMap
  have hf : Function.Bijective f := by
    simpa [f] using (derivedHom_cohomology_iso_shiftedHom H K L (0 : ℤ)).bijective
  letI : IsIso (derivedDualTensorZeroCohomologyComparison H K L) :=
    derivedDualTensorZeroCohomologyComparison_isIso_of_isPerfect H hK L
  let hg := ConcreteCategory.bijective_of_isIso
    (derivedDualTensorZeroCohomologyComparison H K L)
  refine ⟨?_, ?_⟩
  · intro x y hxy
    exact hg.1 (hf.1 hxy)
  · intro z
    obtain ⟨w, hw⟩ := hf.2 z
    obtain ⟨x, hx⟩ := hg.2 w
    refine ⟨x, ?_⟩
    simpa [derivedDualTensorExtZeroComparison, hw] using (congrArg f hx).trans hw

/-- For a perfect object `K`, the degree-zero comparison identifies
`H^0(L \otimes_A^{\mathbf L} K^\vee)` with `\operatorname{Ext}^0_A(K, L)` as an `A`-linear
equivalence. -/
noncomputable def derivedDualTensorExtZeroEquiv
    (H : RHomPkg) {K : DMod} (hK : DerivedCategory.IsPerfect K) (L : DMod) :
    ((𝓗 0).obj (L ⊗[A]^L Kᵛ⟮H⟯)) ≃ₗ[A] Ext^((0 : ℤ))(K, L) :=
  LinearEquiv.ofBijective
    (derivedDualTensorExtZeroComparison H K L)
    (derivedDualTensorZeroCohomology_iso_extZero H hK L)

/-- Companion bridge: the degree-zero comparison specialized from `Ext^0_A(K, L)` to the ordinary
morphism module `Hom_{D(A)}(K, L)`. -/
noncomputable def derivedDualTensorZeroLinearComparison
    (H : RHomPkg) (K L : DMod) :
    ((𝓗 0).obj (L ⊗[A]^L Kᵛ⟮H⟯)) →ₗ[A] (K ⟶ L) :=
  (shiftedHomZeroLinearEquiv K L).toLinearMap.comp
    (derivedDualTensorExtZeroComparison H K L)

/-- Companion bridge: for a perfect object `K`, the degree-zero comparison identifies
`H^0(L \otimes_A^{\mathbf L} K^\vee)` with `Hom_{D(A)}(K, L)` after transporting
`Ext^0_A(K, L)` across the canonical degree-zero equivalence. -/
noncomputable def derivedDualTensorZeroLinearEquiv
    (H : RHomPkg) {K : DMod} (hK : DerivedCategory.IsPerfect K) (L : DMod) :
    ((𝓗 0).obj (L ⊗[A]^L Kᵛ⟮H⟯)) ≃ₗ[A] (K ⟶ L) :=
  (derivedDualTensorExtZeroEquiv H hK L).trans (shiftedHomZeroLinearEquiv K L)

end

end CategoryTheory

/-! ### Remark_15_75_16 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedExt
open scoped DerivedInternalHom

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A]
local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "RHomPkg" => MonoidalClosed DMod
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)
local notation "𝓗" => DerivedCategory.homologyFunctor (ModuleCat A)

variable (H : RHomPkg)

/- Domain-style sampling for Remark 15.75.16:
- primary domain: tor-amplitude in `D(A)` together with the chapter's derived-duality owner;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `HasTorAmplitudeIn`,
  `HasProjectiveAmplitudeIn`,
  `CategoryTheory.derivedDual`,
  `CategoryTheory.derivedDual_isPerfect`,
  `CategoryTheory.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension`,
  `projectiveAmplitudeIn_ext_vanishing_tfae`;
- best owner abstraction:
  `source-facing`: the tor-amplitude interval of the derived dual of a perfect complex;
  `core/canonical`: `K.IsPerfect`, `HasTorAmplitudeIn`, `HasProjectiveAmplitudeIn`, and
    `derivedDual`;
  `bridge/view`: derive projective amplitude from perfectness plus tor-amplitude via Lemma
    `15.78.4`, convert it to unrestricted Ext-vanishing via Lemma `15.69.2`, and transport that
    vanishing across the canonical tensor/Hom comparison for the derived dual.

Primitive data are the perfect object `K` and its tor-amplitude interval `[a, b]`.
Pseudo-coherence is derived API here, obtained from the chapter owner `K.IsPerfect` by
Lemma `15.75.2`, so it should not replace perfectness in the public theorem header. The derived dual itself is
already owned upstream by `derivedDual`, so this file should reuse that owner directly, with the
chapter notation `Kᵛ⟮H⟯` as the source-facing theorem surface, rather than introducing a parallel
local dual API.
-/

-- Proof sketch: perfectness plus tor-amplitude in `[a, b]` gives projective amplitude in
-- `[a, b]` by Lemma `15.78.4`, hence Ext-vanishing outside `[-b, -a]` by Lemma `15.69.2`.
-- The tensor/Hom comparison from Lemma `15.75.15` identifies
-- `M[0] ⊗^L K^\vee` with `RHom_A(K, M[0])`, and `15.74.0.2` rewrites the latter cohomology as
-- Ext. This transports the Ext-vanishing to the required tor-amplitude bounds for `K^\vee`.
/-- Remark 15.75.16: if `K` is perfect and has tor-amplitude in `[a, b]`, then its derived dual
`K^\vee = R\mathrm{Hom}_A(K, A)` has tor-amplitude in `[-b, -a]`. -/
theorem derivedDual_hasTorAmplitudeIn_neg_swap
    (H : RHomPkg) {K : DMod} {a b : ℤ}
    (hK : K.IsPerfect) (hamp : HasTorAmplitudeIn K a b) :
    HasTorAmplitudeIn Kᵛ⟮H⟯ (-b) (-a) := by
  have hKpc : K.IsPseudoCoherent :=
    (isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension K).1 hK |>.1
  have hPerfectTor : K.IsPerfect ∧ HasTorAmplitudeIn K a b := ⟨hK, hamp⟩
  have hprojAmp : HasProjectiveAmplitudeIn K a b :=
    ((projectiveAmplitudeIn_perfect_finitelyPresented_ext_tfae_of_isPseudoCoherent
      K a b hKpc).out 1 0).mp hPerfectTor
  have hExt :
      ∀ (M : ModuleCat A) (i : ℤ), i ∉ Set.Icc (-b) (-a) →
        ∀ e : Ext^i(K, (single₀).obj M), e = 0 :=
    ((projectiveAmplitudeIn_ext_vanishing_tfae K a b).out 0 1).mp hprojAmp
  intro M i hi
  let Kdual : DMod := Kᵛ⟮H⟯
  have hExtSub : Subsingleton (Ext^i(K, (single₀).obj M)) :=
    (subsingleton_iff_forall_eq 0).2 fun e ↦ hExt M i hi e
  letI : Subsingleton (Ext^i(K, (single₀).obj M)) := hExtSub
  have hRHomZero : IsZero ((𝓗 i).obj (RHom[H](K, (single₀).obj M))) := by
    let e := derivedHom_cohomology_iso_shiftedHom H K ((single₀).obj M) i
    letI : Subsingleton (((𝓗 i).obj (RHom[H](K, (single₀).obj M))) : Type u) :=
      e.injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  letI : IsIso (derivedDualTensorComparison H K) :=
    tensor_derivedDual_iso_derivedInternalHom H hK
  have hTensorZero :
      IsZero ((𝓗 i).obj ((derivedTensorProduct Kdual).obj ((single₀).obj M))) :=
    IsZero.of_iso hRHomZero <|
      (𝓗 i).mapIso (asIso ((derivedDualTensorComparison H K).app ((single₀).obj M)))
  exact IsZero.of_iso hTensorZero <|
    (𝓗 i).mapIso (derivedTensorProduct_comm Kdual ((single₀).obj M))

end

end CategoryTheory

/-! ### Lemma_15_75_17 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open MonoidalClosed
open Opposite
open scoped DerivedInternalHom
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "RHomPkg" => MonoidalClosed DMod

/- Domain-style sampling for Lemma 15.75.17:
- primary domain: derived duality for perfect objects in `D(A)` together with the Chapter 13
  homotopy-colimit / derived-limit owners for sequential diagrams;
- sampled owner declarations:
  `CategoryTheory.SequentialInverseSystem`,
  `CategoryTheory.MonoidalClosed.internalHom`,
  `CategoryTheory.tensor_derivedDual_iso_derivedInternalHom`,
  `CategoryTheory.derivedDualMap`,
  `CategoryTheory.IsHomotopyColimitOf`,
  `CategoryTheory.IsDerivedLimit`;
- best owner abstraction:
  `source-facing`: the tensor-dual inverse system `n ↦ E ⊗_A^{\mathbf L} K_n^\vee` from the
    Stacks statement, now exposed directly as a `SequentialInverseSystem DMod`, together with the
    derived-limit conclusion for `RHom_A(K, E)`;
  `core/canonical`: the sequential inverse-system owner `SequentialInverseSystem DMod`, the
    source-variable internal-Hom owner `MonoidalClosed.internalHom.flip.obj E`, the notation
    `RHom[H](K, E)`, and the Chapter 13 predicates `IsHomotopyColimitOf` and `IsDerivedLimit`;
  `bridge/view`: the inverse-system isomorphism
    `derivedDualTensorInverseSystemIsoInternalHomTower`, whose components are the perfect-stage
    comparison isomorphisms from Lemma `15.75.15`.

Primitive data are only the sequential diagram `K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯`, the chosen monoidal-closed
owner `H`, and the fixed tensor target `E`. The source-facing tensor-dual inverse system is the
right owner for the textbook statement, while the canonical owner-level inverse system is the
source-variable internal-Hom tower `(Functor.ofSequence f).op ⋙
MonoidalClosed.internalHom.flip.obj E`. Lemma `15.75.15` supplies the stagewise bridge between
these two owners.
-/

/-- The source-facing inverse system
`\cdots \to E \otimes_A^{\mathbf L} K_{n + 1}^\vee \to E \otimes_A^{\mathbf L} K_n^\vee`
attached to a sequential diagram `K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯` in `D(A)`. -/
abbrev derivedDualTensorInverseSystem
    (H : RHomPkg) (E : DMod) (K : ℕ → DMod) (f : ∀ n, K n ⟶ K (n + 1)) :
    SequentialInverseSystem DMod :=
  let X : ℕ → DMod := fun n ↦ E ⊗[A]^L (K n)ᵛ⟮H⟯
  Functor.ofOpSequence <| fun n ↦
    show X (n + 1) ⟶ X n from
      (derivedTensorProductMap H (derivedDualMap H (f n))).app E

/-- For a sequential diagram of perfect objects, the source-facing tensor-dual inverse system is
canonically isomorphic to the owner-level internal-Hom tower
`(Functor.ofSequence f).op ⋙ MonoidalClosed.internalHom.flip.obj E`. -/
noncomputable def derivedDualTensorInverseSystemIsoInternalHomTower
    (H : RHomPkg) (E : DMod) (K : ℕ → DMod) (f : ∀ n, K n ⟶ K (n + 1))
    (hperfect : ∀ n, DerivedCategory.IsPerfect (K n)) :
    letI := H
    derivedDualTensorInverseSystem H E K f ≅
      (Functor.ofSequence f).op ⋙ (MonoidalClosed.internalHom).flip.obj E := by
  letI : RHomPkg := H
  refine NatIso.ofComponents
    (fun n ↦
      letI : IsIso (derivedDualTensorComparison H (K n.unop)) :=
        tensor_derivedDual_iso_derivedInternalHom H (hperfect n.unop)
      (asIso (derivedDualTensorComparison H (K n.unop))).app E)
    (fun {X Y} g ↦ by
      sorry)

/-- Lemma 15.75.17: if `K` is a chosen homotopy colimit of a sequential system of perfect objects
`K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯` in `D(A)`, then for every `E : D(A)` the derived internal Hom
`R\mathrm{Hom}_A(K,E)` is a derived limit of the source-facing inverse system
`n ↦ E \otimes_A^{\mathbf L} K_n^\vee`, where `K_n^\vee = R\mathrm{Hom}_A(K_n, A)`.
Lemma `15.75.15` supplies the stagewise bridge from this tensor-dual tower to the canonical
inverse system `n ↦ R\mathrm{Hom}_A(K_n, E)`. -/
-- Proof sketch: for each stage `n`, perfectness makes the canonical comparison
-- `E ⊗^L_A K_n^\vee ⟶ RHom_A(K_n, E)` an isomorphism by Lemma `15.75.15`. After replacing the
-- source-facing tower by the canonically isomorphic owner-level internal-Hom tower
-- `(Functor.ofSequence f).op ⋙ MonoidalClosed.internalHom.flip.obj E`, the source-variable
-- internal-Hom owner `MonoidalClosed.internalHom.flip.obj E` sends the homotopy-colimit triangle
-- for `K` to the Milnor triangle computing the derived limit of `RHom_A(K_n, E)`.
theorem derivedInternalHom_isDerivedLimit_of_homotopyColimit
    (H : RHomPkg) (K : ℕ → DMod) (f : ∀ n, K n ⟶ K (n + 1)) {Khocolim : DMod}
    [HasCoproduct (Functor.ofSequence f).obj]
    (hperfect : ∀ n, DerivedCategory.IsPerfect (K n))
    (hKhocolim : IsHomotopyColimitOf (Functor.ofSequence f) Khocolim) (E : DMod) :
    IsDerivedLimit
      (derivedDualTensorInverseSystem H E K f)
      (RHom[H](Khocolim, E)) := sorry

end

end CategoryTheory
