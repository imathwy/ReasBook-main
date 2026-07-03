import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_84_1 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

local notation "DModA" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Definition 15.84.1:
- primary domain: relative perfectness in derived categories of modules over a base algebra;
- sampled owner declarations:
  `DerivedCategory.IsPseudoCoherent`,
  `HasFiniteTorDimension`,
  `DerivedCategory.IsPerfect`,
  `RingHom.IsPerfectRingMap`;
- best owner abstraction: this file is the `source-facing` owner for the relative object
  predicate `K.IsPerfectOver R` on `D(A)`, built from the chapter owners `K.IsPseudoCoherent`
  and finite tor dimension after restricting scalars to the base ring;
- primitive vs. derived:
  primitive data are exactly those two owner predicates;
  derived API is the downstream closure, tensor-product, and base-change theory for
  `K.IsPerfectOver R`;
- source/core/bridge triage:
  `source-facing`: `DerivedCategory.IsPerfectOver`;
  `core/canonical`: `DerivedCategory.IsPseudoCoherent`, `HasFiniteTorDimension`, and the
    canonical derived restriction-of-scalars functor;
  `bridge/view`: regarding an object of `D(A)` as an object of `D(R)` via restriction of scalars.
-/

namespace DerivedCategory

/-- Definition 15.84.1: for a flat ring map of finite presentation `R → A`, an object `K` of
`D(A)` is `R`-perfect, or perfect relative to `R`, if it is pseudo-coherent over `A` and has
finite tor dimension over `R`. -/
def IsPerfectOver (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (K : DerivedCategory (ModuleCat A)) : Prop :=
  K.IsPseudoCoherent ∧
    HasFiniteTorDimension ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K)

end DerivedCategory

end

end CategoryTheory

/-! ### Lemma_15_84_2 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open scoped ZeroObject

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/- Domain-style sampling for Lemma 15.84.2:
- primary domain: triangulated object properties in derived categories of modules, together with
  restriction of scalars along `R → A`;
- sampled owner declarations:
  `DerivedCategory.IsPerfectOver`,
  `ObjectProperty.IsStableUnderRetracts`,
  `ObjectProperty.IsTriangulated`,
  `(P.inverseImage F).IsTriangulated`,
  `(P ⊓ P').IsTriangulated`;
- best owner abstraction: the source-facing owner is `DerivedCategory.IsPerfectOver R`, while the
  retract and distinguished-triangle closure statements belong canonically to `ObjectProperty`;
- primitive vs. derived:
  primitive data are the two defining owner predicates `K.IsPseudoCoherent` and finite tor
  dimension after applying the canonical derived restriction-of-scalars functor;
  derived API are retract stability and triangulated closure of their intersection;
- source/core/bridge triage:
  `source-facing`: `DerivedCategory.IsPerfectOver R`;
  `core/canonical`: `ObjectProperty.IsStableUnderRetracts` and
    `ObjectProperty.IsTriangulated`;
  `bridge/view`: inverse image along the canonical derived restriction-of-scalars functor.

Accordingly, this file exposes the closure result at the owner layer as an
`ObjectProperty.IsTriangulated` instance for `DerivedCategory.IsPerfectOver R`, deriving it from
the canonical object-property owners rather than maintaining a parallel closure API. -/

private theorem hasTorAmplitudeIn_mono {K : DModR} {a b a' b' : ℤ}
    (hK : HasTorAmplitudeIn K a b) (ha : a' ≤ a) (hb : b ≤ b') :
    HasTorAmplitudeIn K a' b' := by
  intro M i hi
  exact hK M i <| by
    intro hi'
    exact hi ⟨le_trans ha hi'.1, le_trans hi'.2 hb⟩

private theorem hasFiniteTorDimension_obj₂_of_distinguishedTriangle
    (T : Triangle DModR) (hT : T ∈ distTriang DModR)
    (h₁ : HasFiniteTorDimension T.obj₁) (h₃ : HasFiniteTorDimension T.obj₃) :
    HasFiniteTorDimension T.obj₂ := by
  rcases h₁ with ⟨a₁, b₁, h₁⟩
  rcases h₃ with ⟨a₃, b₃, h₃⟩
  refine ⟨min a₁ a₃, max b₁ b₃, ?_⟩
  exact hasTorAmplitudeIn_obj₂_of_distinguishedTriangle T hT
    (hasTorAmplitudeIn_mono h₁ (min_le_left _ _) (le_max_left _ _))
    (hasTorAmplitudeIn_mono h₃ (min_le_right _ _) (le_max_right _ _))

/-- Objects of `D(R)` with finite tor dimension are stable under retracts/direct summands. -/
instance hasFiniteTorDimension_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts (fun K : DModR ↦ HasFiniteTorDimension K) where
  of_retract h hK := by
    rcases hK with ⟨a, b, hK⟩
    exact ⟨a, b, prop_of_retract (fun K : DModR ↦ HasTorAmplitudeIn K a b) h hK⟩

private theorem hasFiniteTorDimension_zero : HasFiniteTorDimension (0 : DModR) := by
  refine ⟨0, 0, ?_⟩
  intro M i hi
  letI : (derivedTensorProduct ((single₀).obj M)).IsTriangulated :=
    derivedTensorProduct_isTriangulated ((single₀).obj M)
  letI : (derivedTensorProduct ((single₀).obj M)).Additive := inferInstance
  letI : (derivedTensorProduct ((single₀).obj M)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  simpa using
    (H i).map_isZero <|
      (derivedTensorProduct ((single₀).obj M)).map_isZero (isZero_zero DModR)

private instance hasFiniteTorDimension_containsZero :
    ObjectProperty.ContainsZero (fun K : DModR ↦ HasFiniteTorDimension K) where
  exists_zero := by
    exact ⟨0, isZero_zero DModR, hasFiniteTorDimension_zero⟩

private instance hasFiniteTorDimension_isStableUnderShift :
    ObjectProperty.IsStableUnderShift (fun K : DModR ↦ HasFiniteTorDimension K) ℤ where
  isStableUnderShiftBy n := .mk <| by
    intro K hK
    exact (hasFiniteTorDimension_shift_iff K n).2 hK

private instance hasFiniteTorDimension_isTriangulatedClosed₂ :
    ObjectProperty.IsTriangulatedClosed₂ (fun K : DModR ↦ HasFiniteTorDimension K) :=
  .mk' fun T hT h₁ h₃ ↦ hasFiniteTorDimension_obj₂_of_distinguishedTriangle T hT h₁ h₃

/-- Objects of `D(R)` with finite tor dimension form a triangulated object property. -/
instance hasFiniteTorDimension_isTriangulated :
    ObjectProperty.IsTriangulated (fun K : DModR ↦ HasFiniteTorDimension K) where
  toContainsZero := hasFiniteTorDimension_containsZero
  toIsStableUnderShift := hasFiniteTorDimension_isStableUnderShift
  toIsTriangulatedClosed₂ := hasFiniteTorDimension_isTriangulatedClosed₂

-- Proof sketch: `DerivedCategory.IsPerfectOver R` is definitionally the intersection of the
-- pseudo-coherent owner property on `D(A)` and the inverse image, along the canonical derived
-- restriction-of-scalars functor, of the finite-tor-dimension owner property on `D(R)`. The
-- retract stability statement is therefore the canonical `⊓`-instance.
/-- `R`-perfect objects of `D(A)` are stable under retracts/direct summands. -/
instance isPerfectOver_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts
      (fun K : DModA ↦ DerivedCategory.IsPerfectOver R K) := by
  let P₁ : ObjectProperty DModA := fun K ↦ K.IsPseudoCoherent
  let P₂ : ObjectProperty DModR := fun K ↦ HasFiniteTorDimension K
  let F : DModA ⥤ DModR := (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory
  letI : P₁.IsStableUnderRetracts := by
    simpa [P₁] using
      (inferInstance : ObjectProperty.IsStableUnderRetracts (fun K : DModA ↦ K.IsPseudoCoherent))
  letI : P₂.IsStableUnderRetracts := by
    simpa [P₂] using
      (inferInstance :
        ObjectProperty.IsStableUnderRetracts (fun K : DModR ↦ HasFiniteTorDimension K))
  simpa [DerivedCategory.IsPerfectOver, P₁, P₂, F, ObjectProperty.inverseImage] using
    (inferInstance :
      ObjectProperty.IsStableUnderRetracts (P₁ ⊓ P₂.inverseImage F))

-- Proof sketch: the same definitional decomposition identifies `DerivedCategory.IsPerfectOver R`
-- with the intersection of a pseudo-coherent triangulated object property on `D(A)` and the
-- inverse image, along the canonical derived restriction-of-scalars functor, of the
-- finite-tor-dimension triangulated object property on `D(R)`. The instance is then the canonical
-- `⊓`-instance for triangulated object properties.
/-- Lemma 15.84.2: the `R`-perfect objects of `D(A)` form a saturated triangulated strictly full
subcategory; the flat finite-presentation hypotheses from the source are not needed for this
closure statement. -/
instance isPerfectOver_isTriangulated :
    ObjectProperty.IsTriangulated
      (fun K : DModA ↦ DerivedCategory.IsPerfectOver R K) := by
  let P₁ : ObjectProperty DModA := fun K ↦ K.IsPseudoCoherent
  let P₂ : ObjectProperty DModR := fun K ↦ HasFiniteTorDimension K
  let F : DModA ⥤ DModR := (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory
  letI : P₁.IsTriangulated := by
    simpa [P₁] using
      (inferInstance : ObjectProperty.IsTriangulated (fun K : DModA ↦ K.IsPseudoCoherent))
  letI : P₂.IsTriangulated := by
    simpa [P₂] using
      (inferInstance :
        ObjectProperty.IsTriangulated (fun K : DModR ↦ HasFiniteTorDimension K))
  simpa [DerivedCategory.IsPerfectOver, P₁, P₂, F, ObjectProperty.inverseImage] using
    (inferInstance : ObjectProperty.IsTriangulated (P₁ ⊓ P₂.inverseImage F))

end

end CategoryTheory

/-! ### Lemma_15_84_3 (from Chap15) -/
noncomputable section

open CategoryTheory
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

local notation "DModA" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.84.3:
- primary domain: relative perfectness in derived categories of modules over a base algebra, and
  its behavior under the canonical derived tensor product over that algebra;
- sampled owner declarations:
  `DerivedCategory.IsPerfectOver`,
  `DerivedCategory.IsPerfect`,
  `isPerfect_restrictScalars_of_module_isPerfect`,
  `(ModuleCat.of R A).IsPerfect`;
- best owner abstraction: the theorem is `source-facing` on the chapter owner
  `DerivedCategory.IsPerfectOver R`, while absolute perfectness of `K` should be fed into that
  owner through the existing restriction-of-scalars bridge with the primitive perfectness
  hypothesis on `A` as an `R`-module, rather than through a local duplicate helper or a stronger
  ring-map hypothesis package;
- primitive vs. derived:
  primitive data are the perfect `R`-module `(ModuleCat.of R A)`, the absolute perfect object
  `K : D(A)`, and the relatively perfect object `M : D(A)`;
  pseudo-coherence and finite tor dimension over `R` are derived ingredients supplied by the
  existing owner API, not primitive public data for this file;
- source/core/bridge triage:
  `source-facing`: the tensor-stability theorem below for `DerivedCategory.IsPerfectOver R`;
  `core/canonical`: `DerivedCategory.IsPerfectOver`, `DerivedCategory.IsPerfect`, the tensor
    object `K ⊗[A]^L M`, and the perfect `R`-module `(ModuleCat.of R A)`;
  `bridge/view`: the canonical restriction-of-scalars theorem
    `isPerfect_restrictScalars_of_module_isPerfect`, which upgrades absolute perfectness over `A`
    to relative perfectness over `R` without introducing a new local owner.
-/

-- Proof sketch: first pass from `hK : K.IsPerfect` to `DerivedCategory.IsPerfectOver R K` through
-- the canonical restriction-of-scalars bridge `isPerfect_restrictScalars_of_module_isPerfect`,
-- using the primitive hypothesis that `A`, viewed as an `R`-module, is perfect. Then
-- unfold `DerivedCategory.IsPerfectOver` for `M`, use Lemma `15.65.16` to propagate
-- pseudo-coherence through `K ⊗[A]^L M`, and combine the tor-amplitude interval extracted from
-- the perfect complex `K` with the finite tor-dimension interval of `M` via Lemma `15.67.10`.
/-- Lemma 15.84.3: if `K, M ∈ D(A)`, then `K ⊗_A^{\mathbf L} M` is perfect relative to `R`
whenever `K` is perfect and `M` is perfect relative to `R`. -/
theorem isPerfectOver_derivedTensorProduct
    (K M : DModA)
    (hA : (ModuleCat.of R A).IsPerfect)
    (hK : K.IsPerfect)
    (hM : DerivedCategory.IsPerfectOver R M) :
    DerivedCategory.IsPerfectOver R (K ⊗[A]^L M) := sorry

end

end CategoryTheory

/-! ### Lemma_15_84_4 (from Chap15) -/
noncomputable section

open CategoryTheory
open ComplexShape
open scoped CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

/- Domain-style sampling for Lemma 15.84.4:
- primary domain: relative perfectness in the derived category `D(A)` and its description by
  bounded cochain representatives;
- sampled owner declarations:
  `DerivedCategory.IsPerfectOver`,
  `CochainComplex.IsTermwiseFlat`,
  `Compᵇ((ModuleCat A))`,
  `Functor.mapHomologicalComplex`,
  `CategoryTheory.IsIsomorphic`;
- best owner abstraction: the source-facing theorem belongs on the chapter owner
  `DerivedCategory.IsPerfectOver R`, while the representative-side condition should live on the
  bounded owner `P : Compᵇ((ModuleCat A))` through its ambient complex `P.obj`, together with the
  canonical restriction-of-scalars functor
  `(ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (up ℤ)` and the genuinely
  extra termwise `Module.FinitePresentation A` hypothesis;
- primitive vs. derived:
  primitive data are the bounded representative `P : Compᵇ((ModuleCat A))`, canonical termwise
  `R`-flatness of the restricted ambient complex
  `((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (up ℤ)).obj P.obj`,
  termwise finite presentation over `A`, and the isomorphism class of the represented derived
  object `DerivedCategory.Q.obj P.obj`;
  derived API is the iff-criterion identifying `DerivedCategory.IsPerfectOver R` with the
  existence of such a representative;
- source/core/bridge triage:
  `source-facing`: the representative criterion of Lemma 15.84.4;
  `core/canonical`: `DerivedCategory.IsPerfectOver`, `Compᵇ((ModuleCat A))`, and
    `CategoryTheory.IsIsomorphic`, together with the owner predicate
    `CochainComplex.IsTermwiseFlat`;
  `bridge/view`: the ambient restriction-of-scalars functor
    `(ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (up ℤ)` acting on the
    underlying ambient complex `P.obj`.
-/

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable [Module.Flat R A] [Algebra.FinitePresentation R A]

local notation "BoundedCpxA" => Compᵇ((ModuleCat A))
local notation "DModA" => DerivedCategory (ModuleCat A)

-- Proof sketch: for `(→)`, represent `K` by a bounded-above finite-free complex using
-- pseudo-coherence, then truncate it using the finite tor-amplitude bounds and Lemma `15.67.2`
-- to obtain a bounded representative with termwise `R`-flat finitely presented terms. For `(←)`,
-- each term of a bounded representative is pseudo-coherent over `A` and has finite tor dimension
-- over `R`, hence is perfect over `R`; closure of `R`-perfect objects under shifts and cones from
-- Lemma `15.84.2` gives perfection of the whole complex.
variable (R) in
/-- Lemma 15.84.4: for a flat ring map `R → A` of finite presentation, an object `K` of `D(A)` is
perfect over `R` if and only if it is isomorphic in `D(A)` to a bounded cochain complex of
`A`-modules with `R`-flat finitely presented terms. -/
theorem isPerfectOver_iff_exists_bounded_flat_finitePresentation_representative
    (K : DModA) :
    DerivedCategory.IsPerfectOver R K ↔
      ∃ P : BoundedCpxA,
        CochainComplex.IsTermwiseFlat
          (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (up ℤ)).obj
            P.obj) ∧
          (∀ i : ℤ, Module.FinitePresentation A (P.obj.X i)) ∧
          IsIsomorphic K (DerivedCategory.Q.obj P.obj) := sorry

end

end
end CategoryTheory

/-! ### Lemma_15_84_5 (from Chap15) -/
noncomputable section

open CategoryTheory
open scoped TensorProduct DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace CategoryTheory

section

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']

local notation "Aprime" => A ⊗[R] R'
local notation "DModA" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.84.5:
- primary domain: base change for relative perfect objects in derived categories of module
  categories;
- sampled owner declarations:
  `DerivedCategory.IsPerfectOver`,
  `derivedTensorWithAlgebra_isPseudoCoherent`,
  `derivedTensorBaseChangeIso`,
  `hasTorAmplitudeIn_derivedTensorWithAlgebra`;
- best owner abstraction: this theorem is `source-facing` on the chapter owner
  `DerivedCategory.IsPerfectOver`, while the core/canonical owners are the derived scalar
  extension `K ⊗[A]^L[Aprime]`, the canonical base-change comparison `derivedTensorBaseChangeIso`,
  and the tor-amplitude base-change theorem;
- primitive vs. derived:
  primitive data are the algebra maps `R → A` and `R → R'`, the base change ring
  `Aprime = A ⊗[R] R'`, and the hypothesis that `K` is perfect over `R`;
  the base-changed object `K ⊗[A]^L[Aprime]` and its relative-perfectness conclusion are derived
  API over those owners;
- source/core/bridge triage:
  `source-facing`: preservation of `DerivedCategory.IsPerfectOver` under base change in the base
    ring;
  `core/canonical`: `DerivedCategory.IsPerfectOver`, `derivedTensorWithAlgebra`,
    `derivedTensorBaseChangeIso`, and `HasFiniteTorDimension`;
  `bridge/view`: the notation `K ⊗[A]^L[Aprime]` for the scalar-extension owner applied to `K`. -/

-- Proof sketch: use Lemma `15.82.12` to preserve pseudo-coherence relative to the base under the
-- derived scalar extension `A → Aprime`. Then identify the restricted derived base change with
-- `K ⊗_R^L R'` using Lemma `15.61.2`, and apply Lemma `15.67.13` together with finite tor
-- dimension over `R` to conclude finite tor dimension over `R'`. The source phrases this lemma
-- under additional flatness and finite-presentation assumptions on `R → A`, but those hypotheses
-- are redundant for the canonical owner decomposition used here.
/-- Lemma 15.84.5: let `R → A` and `R → R'` be ring maps, and set `A' = A ⊗[R] R'`. If an object
of `D(A)` is perfect relative to `R`, then its derived base change to `A'` is perfect relative
to `R'`. The flatness and finite-presentation assumptions on `R → A` appearing in the source are
redundant for this conclusion. -/
theorem derivedTensorWithAlgebra_isPerfectOver_of_baseChange
    {K : DModA}
    (hK : DerivedCategory.IsPerfectOver R K) :
    DerivedCategory.IsPerfectOver R' (K ⊗[A]^L[Aprime]) :=
  sorry

end

end CategoryTheory

/-! ### Lemma_15_84_6 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open Opposite
open scoped DerivedTensorWithAlgebra
open scoped DerivedInternalHom
open scoped ModuleComplexInternalHom
open scoped TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace CategoryTheory

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable [Module.Flat R A] [Algebra.FinitePresentation R A]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "CpxR" => CochainComplex (ModuleCat R) ℤ
local notation "CpxA" => CochainComplex (ModuleCat A) ℤ
local notation "MinusCpxA" => CochainComplex.minus (ModuleCat A)
local notation "BoundedCpxA" => CochainComplex.bounded (ModuleCat A)
local notation "PlusCpxA" => CochainComplex.plus (ModuleCat A)

/-
Domain-style sampling for Lemma 15.84.6:
- primary domain: derived internal-Hom in `D(A)` for a pseudo-coherent source and an
  `R`-perfect target, computed by the chapter owner `module_complex_internal_hom` through concrete
  cochain representatives over `A`;
- sampled owner declarations:
  `DerivedCategory.IsPseudoCoherent`,
  `DerivedCategory.IsPerfectOver`,
  `isPerfectOver_iff_exists_bounded_flat_finitePresentation_representative`,
  `CochainComplex.minus`,
  `CochainComplex.bounded`,
  `CochainComplex.plus`,
  `CochainComplex.IsTermwiseFiniteFree`,
  `module_complex_internal_hom`,
  `RHom[H](K, L)`,
  `module_complex_internal_hom_represents_derivedInternalHom_of_boundedAbove_projective`,
  `CochainComplex.IsTermwiseFlat`;
- best owner abstraction: the primitive owner data live upstream on `K.IsPseudoCoherent` and
  `DerivedCategory.IsPerfectOver R L`, together with the representative criterion
  `isPerfectOver_iff_exists_bounded_flat_finitePresentation_representative`; the concrete
  complexes `P`, `F`, and `⟪P, F⟫` here are therefore bridge/view data over those owners,
  expressed with the canonical boundedness owners
  `CochainComplex.minus`, `CochainComplex.bounded`, and `CochainComplex.plus`;
- primitive vs. derived:
  primitive data are the chosen bounded-above finite-free representative of `K` and bounded
  termwise `R`-flat finitely presented representative of `L`, with the latter obtained from
  `hL` through Lemma `15.84.4` under the ambient flat finite-presentation hypotheses on `R → A`;
  derived API is the resulting bounded-below flat finitely presented Hom-complex representative,
  together with the base-change and finite-presentation companion lemmas for fixed
  representatives;
- source/core/bridge triage:
  `source-facing`: the existential representative theorem immediately below;
  `core/canonical`: `DerivedCategory.IsPseudoCoherent`, `DerivedCategory.IsPerfectOver`,
    `CochainComplex.IsTermwiseFiniteFree`, `⟪P, F⟫`, and the canonical scalar-restriction and
    scalar-extension functors on cochain complexes;
  `bridge/view`: the fixed-representative Hom-complex theorems that follow.
-/

-- Proof sketch: unpack `hK : K.IsPseudoCoherent` to choose a bounded-above termwise finite-free
-- representative `P^•` of `K`, and use Lemma `15.84.4` under `[Module.Flat R A]` and
-- `[Algebra.FinitePresentation R A]` to choose a bounded termwise `R`-flat representative `F^•`
-- of `L` with finitely presented terms. The fixed-representative companion theorems below then
-- show that `Hom^•(P^•, F^•)` is bounded below, termwise `R`-flat after restriction of scalars,
-- has finitely presented terms, and computes the chosen derived internal-Hom object
-- `RHom[H](K, L)`.
/-- Lemma 15.84.6: let `R → A` be a flat ring map of finite presentation. If `K` is
pseudo-coherent and `L` is perfect over `R`, then one can choose a bounded-above termwise
finite-free representative `P^•` of `K` and a bounded termwise `R`-flat representative `F^•` of
`L` with finitely presented terms such that
`Hom^•(P^•, F^•)` is bounded below, termwise `R`-flat after restriction of scalars, has finitely
presented terms, and represents the chosen derived internal-Hom object
`R\mathrm{Hom}_A(K, L)`. -/
theorem exists_homComplex_termwiseFlat_finitePresentation_representative_of_isPseudoCoherent_of_isPerfectOver
    (H : MonoidalClosed DModA) {K L : DModA}
    (hK : K.IsPseudoCoherent)
    (hL : DerivedCategory.IsPerfectOver R L) :
    ∃ P F : CpxA,
      MinusCpxA P ∧
        P.IsTermwiseFiniteFree ∧
        IsIsomorphic (DerivedCategory.Q.obj P) K ∧
        BoundedCpxA F ∧
        CochainComplex.IsTermwiseFlat
          (((Functor.mapHomologicalComplex
            (ModuleCat.restrictScalars (algebraMap R A))
            (up ℤ)).obj F : CpxR)) ∧
        (∀ i : ℤ, Module.FinitePresentation A (F.X i)) ∧
        IsIsomorphic (DerivedCategory.Q.obj F) L ∧
        PlusCpxA ⟪P, F⟫ ∧
        CochainComplex.IsTermwiseFlat
          (((Functor.mapHomologicalComplex
            (ModuleCat.restrictScalars (algebraMap R A))
            (up ℤ)).obj ⟪P, F⟫ : CpxR)) ∧
        (∀ n : ℤ, Module.FinitePresentation A ((⟪P, F⟫).X n)) ∧
        IsIsomorphic (DerivedCategory.Q.obj ⟪P, F⟫) (RHom[H](K, L)) := sorry

-- Proof sketch: `P` is bounded above and termwise finite free, while `F` is bounded and termwise
-- `R`-flat, so `Hom^•(P^•, F^•)` is bounded below and its degree-`n` terms are finite direct sums
-- of `R`-flat modules. The standard K-projective Hom-complex computation identifies
-- `Hom^•(P^•, F^•)` with the canonical chosen derived internal-Hom object `RHom[H](K, L)` in
-- `D(A)`.
/-- Companion bridge for Lemma 15.84.6: once `P^•` and `F^•` are already chosen as above, the
Hom complex `\mathrm{Hom}^\bullet(P^•, F^•)` is a bounded-below termwise `R`-flat representative
of `R\mathrm{Hom}_A(K, L)`. -/
theorem homComplex_isBoundedBelowTermwiseFlatRepresentativeOverBase
    (H : MonoidalClosed DModA) {K L : DModA}
    (P F : CpxA)
    (hPbounded : MinusCpxA P)
    (hPfiniteFree : P.IsTermwiseFiniteFree)
    (hPiso : IsIsomorphic (DerivedCategory.Q.obj P) K)
    (hFbounded : BoundedCpxA F)
    (hFflat :
      CochainComplex.IsTermwiseFlat
        (((Functor.mapHomologicalComplex
          (ModuleCat.restrictScalars (algebraMap R A))
          (up ℤ)).obj F : CpxR)))
    (hFiso : IsIsomorphic (DerivedCategory.Q.obj F) L) :
    PlusCpxA ⟪P, F⟫ ∧
      CochainComplex.IsTermwiseFlat
        (((Functor.mapHomologicalComplex
          (ModuleCat.restrictScalars (algebraMap R A))
          (up ℤ)).obj ⟪P, F⟫ : CpxR)) ∧
      IsIsomorphic (DerivedCategory.Q.obj ⟪P, F⟫) (RHom[H](K, L)) := sorry

end

section

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']

local notation "Aprime" => A ⊗[R] R'
local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModAprime" => DerivedCategory (ModuleCat Aprime)
local notation "CpxR" => CochainComplex (ModuleCat R) ℤ
local notation "CpxA" => CochainComplex (ModuleCat A) ℤ
local notation "CpxR'" => CochainComplex (ModuleCat R') ℤ
local notation "CpxAprime" => CochainComplex (ModuleCat Aprime) ℤ
local notation "MinusCpxA" => CochainComplex.minus (ModuleCat A)
local notation "BoundedCpxA" => CochainComplex.bounded (ModuleCat A)
local notation "PlusCpxA" => CochainComplex.plus (ModuleCat A)
local notation "PlusCpxAprime" => CochainComplex.plus (ModuleCat Aprime)
local instance commRingAprime : CommRing Aprime := by infer_instance
local instance algebraRprimeAprime : Algebra R' Aprime := by infer_instance
local instance algebraAAprime : Algebra A Aprime := by infer_instance

-- Proof sketch: extend scalars degreewise from `A` to `A' = A ⊗[R] R'`. Because `P` is termwise
-- finite free, internal Homs commute with this scalar extension termwise, and the resulting
-- complex stays bounded below and computes the canonical derived internal-Hom object over `A'` of
-- the base-changed representatives.
/-- After any base change `R → R'`, the scalar extension of `Hom^•(P^•, F^•)` to
`A' = A ⊗[R] R'` is bounded below. -/
theorem baseChange_homComplex_isBoundedBelow
    (P F : CpxA)
    (hPbounded : MinusCpxA P)
    (hPfiniteFree : P.IsTermwiseFiniteFree)
    (hFboundedBelow : PlusCpxA F) :
    PlusCpxAprime
      (((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (algebraMap A Aprime))
          (up ℤ)).obj ⟪P, F⟫ : CpxAprime)) := sorry

/-- After any base change `R → R'`, the scalar extension of `Hom^•(P^•, F^•)` to
`A' = A ⊗[R] R'` is termwise `R'`-flat after restriction of scalars. -/
theorem baseChange_homComplex_isTermwiseFlatOverBase
    (P F : CpxA)
    (hPbounded : MinusCpxA P)
    (hPfiniteFree : P.IsTermwiseFiniteFree)
    (hFbounded : BoundedCpxA F)
    (hFflat :
      CochainComplex.IsTermwiseFlat
        (((Functor.mapHomologicalComplex
          (ModuleCat.restrictScalars (algebraMap R A))
          (up ℤ)).obj F : CpxR))) :
    CochainComplex.IsTermwiseFlat
      (((Functor.mapHomologicalComplex
          (ModuleCat.restrictScalars (algebraMap R' Aprime))
          (up ℤ)).obj
          (((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (algebraMap A Aprime))
              (up ℤ)).obj ⟪P, F⟫ : CpxAprime)) : CpxR')) :=
      sorry

/-- After any base change `R → R'`, the scalar extension of `Hom^•(P^•, F^•)` to
`A' = A ⊗[R] R'` represents the derived internal-Hom of the actual derived base changes of the
objects represented by `P^•` and `F^•`. -/
theorem baseChange_homComplex_represents_derivedInternalHom
    (H' : MonoidalClosed DModAprime)
    {K L : DModA} (P F : CpxA)
    (hPbounded : MinusCpxA P)
    (hPfiniteFree : P.IsTermwiseFiniteFree)
    (hPiso : IsIsomorphic (DerivedCategory.Q.obj P) K)
    (hFbounded : BoundedCpxA F)
    (hFflat :
      CochainComplex.IsTermwiseFlat
        (((Functor.mapHomologicalComplex
          (ModuleCat.restrictScalars (algebraMap R A))
          (up ℤ)).obj F : CpxR)))
    (hFiso : IsIsomorphic (DerivedCategory.Q.obj F) L) :
    IsIsomorphic
      (DerivedCategory.Q.obj
        (((Functor.mapHomologicalComplex
            (ModuleCat.extendScalars (algebraMap A Aprime))
            (up ℤ)).obj ⟪P, F⟫ : CpxAprime)))
      (RHom[H'](K ⊗[A]^L[Aprime], L ⊗[A]^L[Aprime])) := sorry

end

section

variable {A : Type u} [CommRing A]

local notation "CpxA" => CochainComplex (ModuleCat A) ℤ
local notation "MinusCpxA" => CochainComplex.minus (ModuleCat A)
local notation "BoundedCpxA" => CochainComplex.bounded (ModuleCat A)

-- Proof sketch: because `P` is bounded above and termwise finite free while `F` is bounded, each
-- degree of `Hom^•(P^•, F^•)` is a finite direct sum of copies of finitely presented terms of
-- `F`; finite presentation is stable under finite direct sums.
/-- If `P^•` is bounded above and termwise finite free, and `F^•` is bounded with finitely
presented terms, then every degree of `Hom^•(P^•, F^•)` is a finitely presented `A`-module. -/
theorem homComplex_term_finitePresentation_of_boundedAbove_of_bounded_of_termwiseFiniteFree
    (P F : CpxA)
    (hPbounded : MinusCpxA P)
    (hPfiniteFree : P.IsTermwiseFiniteFree)
    (hFbounded : BoundedCpxA F)
    (hFfinitePresentation : ∀ i : ℤ, Module.FinitePresentation A (F.X i)) :
    ∀ n : ℤ, Module.FinitePresentation A ((⟪P, F⟫).X n) := sorry

end

end CategoryTheory

/-! ### Lemma_15_84_7 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedTensorWithAlgebra
open scoped TensorProduct

universe u v

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace CategoryTheory

section

variable {I : Type v} [Preorder I] [IsFiltered I]
variable (F : I ⥤ CommRingCat.{u}) [HasColimit F] (i₀ : I)
variable (A₀ : Type u) [CommRing A₀] [Algebra (F.obj i₀) A₀]

/- Domain-style sampling for Lemma 15.84.7:
- primary domain: filtered-colimit descent and Hom comparison for derived scalar extension along
  `A₀ → A₀ ⊗[R₀] R_j` and `A₀ → A₀ ⊗[R₀] colim_i R_i`;
- sampled owner declarations in this domain:
  `DerivedCategory.IsPerfectOver`,
  `derivedTensorWithAlgebra`,
  `derivedTensorWithAlgebraCompIso`,
  `Lemma_15_75_18.stageToColimitHomMap`;
- best owner abstraction: the public source-facing layer here is the stagewise factorization and
  eventual-equality API for Homs after base change, while the iterated-vs-direct scalar-extension
  comparisons remain private bridges built from `derivedTensorWithAlgebraCompIso`;
- primitive vs. derived:
  primitive data are the filtered diagram `F`, the base stage `i₀`, the induced algebra maps
  `F.obj i₀ → F.obj j` and `F.obj j → colimit F`, and the canonical scalar-tower algebra maps
  they induce on `A₀ ⊗[F.obj i₀] F.obj j`;
  the Hom transition maps and descent/equality theorems are derived API over those canonical maps;
- source/core/bridge triage:
  `source-facing`: the three numbered descent/factorization/eventual-equality statements;
  `core/canonical`: `DerivedCategory.IsPerfectOver`, `derivedTensorWithAlgebra`, and
    `derivedTensorWithAlgebraCompIso`;
  `bridge/view`: the canonical scalar-tower / tensor-product transition maps and
    iterated-vs-direct comparison isomorphisms used to define the source-facing Hom maps. -/

private abbrev ringColimit : CommRingCat.{u} :=
  colimit F

instance stageAlgebra (j : Set.Ici i₀) : Algebra (F.obj i₀) (F.obj j.1) :=
  (F.map (homOfLE j.2)).hom.toAlgebra

instance colimitAlgebra : Algebra (F.obj i₀) (ringColimit F) :=
  (colimit.ι F i₀).hom.toAlgebra

private instance stageToColimitAlgebra (j : Set.Ici i₀) :
    Algebra (F.obj j.1) (ringColimit F) :=
  (colimit.ι F j.1).hom.toAlgebra

omit [IsFiltered I] in
private theorem stageToColimitRingHom_comp_eq (j : Set.Ici i₀) :
    (colimit.ι F j.1).hom.comp (F.map (homOfLE j.2)).hom = (colimit.ι F i₀).hom := by
  rw [← CommRingCat.hom_comp]
  simpa using congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE j.2))

omit [IsFiltered I] in
private theorem stageTransitionRingHom_comp_eq {j k : Set.Ici i₀} (h : j ⟶ k) :
    (F.map h).hom.comp (F.map (homOfLE j.2)).hom = (F.map (homOfLE k.2)).hom := by
  sorry

omit [IsFiltered I] in
private instance stageToColimitIsScalarTower (j : Set.Ici i₀) :
    IsScalarTower (F.obj i₀) (F.obj j.1) (ringColimit F) :=
  IsScalarTower.of_algebraMap_eq' (stageToColimitRingHom_comp_eq F i₀ j).symm

private abbrev stageTransitionTensorMap {j k : Set.Ici i₀} (h : j ⟶ k) :
    A₀ ⊗[F.obj i₀] F.obj j.1 →+* A₀ ⊗[F.obj i₀] F.obj k.1 :=
  letI : Algebra (F.obj j.1) (F.obj k.1) := (F.map h).hom.toAlgebra
  letI : IsScalarTower (F.obj i₀) (F.obj j.1) (F.obj k.1) :=
    IsScalarTower.of_algebraMap_eq' (stageTransitionRingHom_comp_eq F i₀ h).symm
  Algebra.TensorProduct.map (AlgHom.id (F.obj i₀) A₀)
    (IsScalarTower.toAlgHom (F.obj i₀) (F.obj j.1) (F.obj k.1))

private abbrev stageToColimitTensorMap (j : Set.Ici i₀) :
    A₀ ⊗[F.obj i₀] F.obj j.1 →+* A₀ ⊗[F.obj i₀] ringColimit F :=
  Algebra.TensorProduct.map (AlgHom.id (F.obj i₀) A₀)
    (IsScalarTower.toAlgHom (F.obj i₀) (F.obj j.1) (ringColimit F))

private theorem stageToColimitTensorMap_comp_eq (j : Set.Ici i₀) :
    (stageToColimitTensorMap F i₀ A₀ j).comp
      (algebraMap A₀ (A₀ ⊗[F.obj i₀] F.obj j.1)) =
        algebraMap A₀ (A₀ ⊗[F.obj i₀] ringColimit F) := sorry

private theorem stageTransitionTensorMap_comp_eq {j k : Set.Ici i₀} (h : j ⟶ k) :
    (stageTransitionTensorMap F i₀ A₀ h).comp
      (algebraMap A₀ (A₀ ⊗[F.obj i₀] F.obj j.1)) =
      algebraMap A₀ (A₀ ⊗[F.obj i₀] F.obj k.1) := sorry

local notation "DModA0" => DerivedCategory (ModuleCat A₀)

private instance stageToColimitTensorAlgebra (j : Set.Ici i₀) :
    Algebra (A₀ ⊗[F.obj i₀] F.obj j.1) (A₀ ⊗[F.obj i₀] ringColimit F) :=
  (stageToColimitTensorMap F i₀ A₀ j).toAlgebra

private abbrev stageBaseChange (j : Set.Ici i₀) :
    DModA0 ⥤ DerivedCategory (ModuleCat (A₀ ⊗[F.obj i₀] F.obj j.1)) :=
  derivedTensorWithAlgebra (algebraMap A₀ (A₀ ⊗[F.obj i₀] F.obj j.1))

private abbrev colimitBaseChange :
    DModA0 ⥤ DerivedCategory (ModuleCat (A₀ ⊗[F.obj i₀] ringColimit F)) :=
  derivedTensorWithAlgebra (algebraMap A₀ (A₀ ⊗[F.obj i₀] ringColimit F))

private abbrev stageToColimitBaseChange (j : Set.Ici i₀) :
    DerivedCategory (ModuleCat (A₀ ⊗[F.obj i₀] F.obj j.1)) ⥤
      DerivedCategory (ModuleCat (A₀ ⊗[F.obj i₀] ringColimit F)) :=
  derivedTensorWithAlgebra (stageToColimitTensorMap F i₀ A₀ j)

private abbrev stageTransitionBaseChange {j k : Set.Ici i₀} (h : j ⟶ k) :
    DerivedCategory (ModuleCat (A₀ ⊗[F.obj i₀] F.obj j.1)) ⥤
      DerivedCategory (ModuleCat (A₀ ⊗[F.obj i₀] F.obj k.1)) :=
  derivedTensorWithAlgebra (stageTransitionTensorMap F i₀ A₀ h)

private noncomputable abbrev stageToColimitBaseChangeIso (j : Set.Ici i₀) :
    stageBaseChange F i₀ A₀ j ⋙ stageToColimitBaseChange F i₀ A₀ j ≅
      colimitBaseChange F i₀ A₀ :=
  derivedTensorWithAlgebraCompIso
    (algebraMap A₀ (A₀ ⊗[F.obj i₀] F.obj j.1))
    (stageToColimitTensorMap F i₀ A₀ j)
    (algebraMap A₀ (A₀ ⊗[F.obj i₀] ringColimit F))
    (stageToColimitTensorMap_comp_eq F i₀ A₀ j)

private noncomputable abbrev stageTransitionBaseChangeIso {j k : Set.Ici i₀} (h : j ⟶ k) :
    stageBaseChange F i₀ A₀ j ⋙ stageTransitionBaseChange F i₀ A₀ h ≅
      stageBaseChange F i₀ A₀ k :=
  derivedTensorWithAlgebraCompIso
    (algebraMap A₀ (A₀ ⊗[F.obj i₀] F.obj j.1))
    (stageTransitionTensorMap F i₀ A₀ h)
    (algebraMap A₀ (A₀ ⊗[F.obj i₀] F.obj k.1))
    (stageTransitionTensorMap_comp_eq F i₀ A₀ h)

/-- The canonical image in the colimit Hom-set of a stagewise morphism. -/
noncomputable def stageToColimitHomMap (j : Set.Ici i₀)
    {K₀ L₀ : DModA0}
    (β :
      (K₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1]) ⟶
        (L₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1])) :
    (K₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] (colimit F : CommRingCat.{u})]) ⟶
      (L₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] (colimit F : CommRingCat.{u})]) :=
  let e := stageToColimitBaseChangeIso F i₀ A₀ j
  (e.app K₀).inv ≫ (stageToColimitBaseChange F i₀ A₀ j).map β ≫ (e.app L₀).hom

/-- The canonical image in a later-stage Hom-set of a stagewise morphism. -/
noncomputable def stageTransitionHomMap {j k : Set.Ici i₀} (h : j ⟶ k)
    {K₀ L₀ : DModA0}
    (β :
      (K₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1]) ⟶
        (L₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1])) :
    (K₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj k.1]) ⟶
      (L₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj k.1]) :=
  let e := stageTransitionBaseChangeIso F i₀ A₀ h
  (e.app K₀).inv ≫ (stageTransitionBaseChange F i₀ A₀ h).map β ≫ (e.app L₀).hom

-- Proof sketch: the cocone relation `R_j → R_k → colim F = R_j → colim F` induces the matching
-- equality for the tensor-product ring maps `A_j → A_k → A = A_j → A`. Naturality of the
-- iterated-vs-direct comparison isomorphisms then identifies the two induced maps on Hom-sets.
/-- The canonical images in the colimit Hom-set are compatible with transition to later stages.
This is the coherence needed for the source-facing filtered Hom-colimit comparison in
Lemma `15.84.7 (2)`. -/
theorem stageToColimitHomMap_transition
    {K₀ L₀ : DModA0} {j k : Set.Ici i₀} (h : j ⟶ k)
    (β :
      (K₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1]) ⟶
        (L₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1])) :
    stageToColimitHomMap F i₀ A₀ k (stageTransitionHomMap F i₀ A₀ h β) =
      stageToColimitHomMap F i₀ A₀ j β := by
  sorry

section

variable [Module.Flat (F.obj i₀) A₀] [Algebra.FinitePresentation (F.obj i₀) A₀]

-- Proof sketch: combine the finite-presentation descent for flat finitely presented modules with
-- the representative criterion for `R`-perfect objects from Lemma `15.84.4`, then descend the
-- finitely many terms of a bounded representative to some stage `j ≥ i₀`.
/-- Lemma 15.84.7 (1): for `A_j = A₀ ⊗[R₀] R_j` and
`A = A₀ ⊗[R₀] \operatorname{colim}_i R_i`, every object of `D(A)` that is perfect over the
colimit ring descends to some stage as an object of `D(A_j)` that is perfect over `R_j`. -/
theorem exists_stage_of_isPerfectOver_filtered_base_change
    (K : DerivedCategory (ModuleCat (A₀ ⊗[F.obj i₀] (colimit F : CommRingCat.{u}))))
    (hK : DerivedCategory.IsPerfectOver (colimit F : CommRingCat.{u}) K) :
    ∃ (j : Set.Ici i₀) (Kj : DerivedCategory (ModuleCat (A₀ ⊗[F.obj i₀] F.obj j.1))),
      DerivedCategory.IsPerfectOver (F.obj j.1) Kj ∧
        IsIsomorphic K
          (Kj ⊗[A₀ ⊗[F.obj i₀] F.obj j.1]^L[
            A₀ ⊗[F.obj i₀] (colimit F : CommRingCat.{u})]) := sorry

-- Proof sketch: represent the morphism group after base change to `A` by the bounded Hom complex
-- from Lemma `15.84.6`, descend the finitely presented terms of that complex to a sufficiently
-- large stage using filtered-colimit exactness, and read off a stage morphism inducing `α`.
/-- Lemma 15.84.7 (2): if `K₀, L₀ ∈ D(A₀)` with `K₀` pseudo-coherent and `L₀` of finite tor
dimension over `R₀`, then every morphism after base change to
`A = A₀ ⊗[R₀] \operatorname{colim}_i R_i` comes from some stage
`A_j = A₀ ⊗[R₀] R_j`. -/
theorem exists_stage_factorization_of_hom_of_pseudoCoherent_of_finiteTorDimension
    (K₀ L₀ : DModA0) (hK₀ : K₀.IsPseudoCoherent)
    (hL₀ :
      HasFiniteTorDimension
        (((ModuleCat.restrictScalars (algebraMap (F.obj i₀) A₀)).mapDerivedCategory).obj L₀))
    (α :
      (K₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] (colimit F : CommRingCat.{u})]) ⟶
        (L₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] (colimit F : CommRingCat.{u})])) :
    ∃ (j : Set.Ici i₀)
      (β :
        (K₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1]) ⟶
          (L₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1])),
      α = stageToColimitHomMap F i₀ A₀ j β := sorry

-- Proof sketch: compute equality in the final Hom group by the same descended Hom complex as in
-- part `(2)`; filtered-colimit exactness implies that two stage classes with equal image in the
-- colimit agree after passing to a sufficiently large later stage.
/-- Lemma 15.84.7 (3): under the same hypotheses on `K₀` and `L₀`, if two morphisms at some
stage `A_j` become equal after base change to `A`, then they already become equal after further
base change to a later stage `A_k` with `k ≥ j`. Together with part `(2)`, this is the Hom-side
filtered-colimit description from the lemma. -/
theorem eventually_eq_of_stage_morphisms_with_equal_colimit_images
    (K₀ L₀ : DModA0) (hK₀ : K₀.IsPseudoCoherent)
    (hL₀ :
      HasFiniteTorDimension
        (((ModuleCat.restrictScalars (algebraMap (F.obj i₀) A₀)).mapDerivedCategory).obj L₀))
    (j : Set.Ici i₀)
    (β₁ β₂ :
      (K₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1]) ⟶
        (L₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1]))
    (hβ :
      stageToColimitHomMap F i₀ A₀ j β₁ =
        stageToColimitHomMap F i₀ A₀ j β₂) :
    ∃ (k : Set.Ici i₀) (hjk : j ⟶ k),
      stageTransitionHomMap F i₀ A₀ hjk β₁ =
        stageTransitionHomMap F i₀ A₀ hjk β₂ := sorry

/- The three statements above give the essential-surjectivity and filtered Hom-colimit data
expressing that the triangulated category of `R`-perfect complexes over `A` is the filtered
colimit of the triangulated categories of `R_j`-perfect complexes over `A_j`. -/

end

end

end CategoryTheory

/-! ### Lemma_15_84_8 (from Chap15) -/
noncomputable section

open CategoryTheory
open scoped TensorProduct DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace CategoryTheory

section

variable {R' A' R : Type u} [CommRing R'] [CommRing A'] [CommRing R]
variable [Algebra R' A'] [Algebra R' R]
variable [Module.Flat R' A']

local notation "A" => A' ⊗[R'] R
local notation "DModA'" => DerivedCategory (ModuleCat A')

/- Domain-style sampling for Lemma 15.84.8:
- primary domain: descent of relative perfectness in derived categories of module categories across
  a nilpotent thickening of the base ring;
- sampled owner declarations:
  `DerivedCategory.IsPerfectOver`,
  `derivedTensorBaseChange`,
  `isPseudoCoherent_derivedTensorWithAlgebra_iff_of_surjective_of_nilpotent_ker`,
  `hasTorAmplitudeIn_derivedTensorWithAlgebra_iff_of_surjective_of_nilpotent_ker`;
- best owner abstraction: the source-facing statement belongs on the chapter owner predicate
  `DerivedCategory.IsPerfectOver`, while the comparison between restriction of
  `K' ⊗[A']^L[A]` to `R` and base change of `K'` restricted to `R'` is a bridge/view supplied by
  `derivedTensorBaseChange`;
- primitive vs. derived:
  primitive data are the flat algebra map `R' → A'`, the nilpotent thickening `R' → R`, and the
  object `K' : D(A')`;
  pseudo-coherence descent, tor-amplitude descent, and the base-change comparison are derived API
  over those owners;
- source/core/bridge triage:
  `source-facing`: descent of `DerivedCategory.IsPerfectOver` across `R' → R`;
  `core/canonical`: `DerivedCategory.IsPerfectOver`, `HasFiniteTorDimension`, and the nilpotent
    descent theorems for pseudo-coherence and tor amplitude;
  `bridge/view`: `derivedTensorBaseChange` and its Tor-independent isomorphism from
    `Lemma_15_61_2`.
-/

-- Proof sketch: unfold `DerivedCategory.IsPerfectOver`. Pseudo-coherence descends directly by
-- Lemma `15.76.4`. For finite tor dimension over the base, use the Tor-independent base-change
-- comparison from Lemma `15.61.2` to identify the restricted object
-- `(K' ⊗[A']^L[A])|_R` with the derived base change of `K'|_{R'}` to `R`, where Tor
-- independence comes from the flatness of `A'` over `R'`; then apply Lemma `15.67.20` across the
-- surjection `R' → R`. The source also assumes that `R' → A'` is of finite presentation, but
-- that hypothesis is redundant for this descent step.
/-- Lemma 15.84.8: let `R' → A'` be a flat ring map, let `R' → R` be a surjective ring map with
nilpotent kernel, and set `A = A' ⊗[R'] R`. If the derived base change
`K' \otimes_{A'}^{\mathbf L} A` is perfect relative to `R`, then `K'` is perfect relative to
`R'`. The finite-presentation hypothesis on `R' → A'` from the source is not needed here. -/
theorem isPerfectOver_of_derivedTensorWithAlgebra_of_surjective_of_nilpotent_ker
    (hsurj : Function.Surjective (algebraMap R' R))
    (hker : IsNilpotent (RingHom.ker (algebraMap R' R)))
    {K' : DModA'}
    (hK :
      DerivedCategory.IsPerfectOver R (K' ⊗[A']^L[A])) :
    DerivedCategory.IsPerfectOver R' K' := by
  sorry

end

end CategoryTheory

/-! ### Lemma_15_84_9 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open IsLocalRing
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModR" => DerivedCategory (ModuleCat R)

/- Domain-style sampling:
- primary domain: pseudo-coherent derived complexes under prime localization and tor-amplitude over
  the base ring;
- sampled owner declarations:
  `derivedTensorWithAlgebra`,
  `primeResidueFieldDerivedHomology`,
  `HasTorAmplitudeIn`,
  `(ModuleCat.restrictScalars _).mapDerivedCategory`;
- best owner abstraction: the source-facing theorem should be stated directly on the canonical
  localized derived object `K ⊗[A]^L[Localization.AtPrime q.asIdeal]`, its restriction of scalars
  to `Localization.AtPrime p.asIdeal` and `R`, and the residue-field-fiber owner
  `primeResidueFieldDerivedHomology`, rather than through parallel local wrapper definitions;
- primitive vs. derived:
  primitive data are the chosen prime pair `p`, `q`, the localization map
  `Localization.localRingHom ...`, and the pseudo-coherent object `K`;
  derived API is the tor-amplitude conclusion for `KqOverR` and the residue-field homology
  vanishing condition for `KqOverRp`.
-/

-- Proof sketch: use the surjective polynomial presentation to view `K` as pseudo-coherent over
-- `R[x_1, …, x_d]`, which lets one reduce to the polynomial ring case by Lemma `15.83.8`. For
-- `R_𝔭 → A_𝔮`, apply Lemma `15.78.6` to the localized complex using the assumed vanishing of
-- `K_𝔮 ⊗_{R_𝔭}^{\mathbf L} κ(\mathfrak p)` outside `[a, b]`; this gives tor-amplitude
-- `[(a - d), b]` over `R_𝔭`. Finally descend the same tor-amplitude bound to `R` by the flatness
-- of `R_𝔭` over `R` via Lemma `15.67.11`.
/-- Lemma 15.84.9: let `A` be an `R`-algebra admitting a surjective polynomial presentation in
`d` variables and flat over `R`. Let `𝔮 ⊂ A` lie over `𝔭 ⊂ R`, and let `K ∈ D(A)` be
pseudo-coherent. If the localized derived fiber
`K_𝔮 \otimes_{R_𝔭}^{\mathbf L} κ(\mathfrak p)` has vanishing homology outside `[a, b]`, then
`K_𝔮`, viewed over `R`, has tor-amplitude in `[a - d, b]`. -/
theorem localized_hasTorAmplitudeIn_over_base_of_pseudoCoherent_of_baseResidueFieldHomology_vanishing
    (d : ℕ) (π : MvPolynomial (Fin d) R →ₐ[R] A) (hπ : Function.Surjective π)
    (p : PrimeSpectrum R) (q : PrimeSpectrum A)
    (hq : Ideal.comap (algebraMap R A) q.asIdeal = p.asIdeal)
    (K : DModA) (a b : ℤ) [Module.Flat R A]
    (hK : K.IsPseudoCoherent)
    (hκ :
      let Aq := Localization.AtPrime q.asIdeal
      let KqOverRp : DerivedCategory (ModuleCat (Localization.AtPrime p.asIdeal)) :=
        ((ModuleCat.restrictScalars
            (Localization.localRingHom p.asIdeal q.asIdeal (algebraMap R A) hq.symm)).mapDerivedCategory.obj
          (K ⊗[A]^L[Aq]))
      ∀ i : ℤ, i ∉ Set.Icc a b →
        IsZero
          (primeResidueFieldDerivedHomology
            (closedPoint (Localization.AtPrime p.asIdeal))
            KqOverRp
            i)) :
    let Aq := Localization.AtPrime q.asIdeal
    let KqOverR : DModR :=
      ((ModuleCat.restrictScalars
          ((algebraMap A Aq).comp (algebraMap R A))).mapDerivedCategory.obj
        (K ⊗[A]^L[Aq]))
    HasTorAmplitudeIn KqOverR (a - (d : ℤ)) b := sorry

end

end CategoryTheory

/-! ### Lemma_15_84_10 (from Chap15) -/
noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable [Module.Flat R A] [Algebra.FinitePresentation R A]

local notation "DModA" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.84.10:
- primary domain: relative perfectness in derived categories and residue-field fibers over primes
  of the base ring;
- sampled owner declarations:
  `DerivedCategory.IsPerfectOver`,
  `derivedTensorWithAlgebra`,
  the scoped notation `K ⊗[R]^L[S]`,
  `DerivedCategory.IsGE`;
- best owner abstraction: this lemma is `source-facing` on the chapter owner
  `DerivedCategory.IsPerfectOver R`, while the fiber test should use the existing derived
  scalar-extension owner `derivedTensorWithAlgebra (algebraMap R p.asIdeal.ResidueField)` applied
  to the restricted object over `R`, rather than a local duplicate fiber functor;
- primitive vs. derived:
  primitive data are the pseudo-coherent object `K : D(A)`, its bounded-below condition in
  `D(A)`, and the bounded-below conditions on its residue-field fibers after restricting scalars
  to `R`;
  the derived-fiber construction itself is already owned upstream by `derivedTensorWithAlgebra`,
  so this file should not keep a parallel local abbreviation for it;
- source/core/bridge triage:
  `source-facing`: the iff criterion below;
  `core/canonical`: `DerivedCategory.IsPerfectOver`, `derivedTensorWithAlgebra`, and `K.IsGE`;
  `bridge/view`: the canonical restriction-of-scalars functor
    `(ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory`.
-/

-- Proof sketch: for `→`, relative perfection already gives finite tor dimension over `R`, hence
-- `K` is bounded below and every derived residue-field fiber is bounded below. For `←`, use the
-- flat finite-presentation reduction to a polynomial algebra, apply the local residue-field
-- criterion to get perfectness after localizing at primes of `A`, deduce global perfectness from
-- the bounded-below hypothesis, and then conclude relative perfectness over `R`.
/-- Lemma 15.84.10: let `R → A` be flat and of finite presentation, and let `K ∈ D(A)` be
pseudo-coherent. Then `K` is `R`-perfect if and only if `K` is bounded below and, for every prime
ideal `𝔭 ⊂ R`, the derived fiber `K ⊗_R^{\mathbf L} κ(𝔭)` is bounded below. -/
theorem isPerfectOver_iff_boundedBelow_and_primeResidueFields_boundedBelow
    (K : DModA) (hK : K.IsPseudoCoherent) :
    DerivedCategory.IsPerfectOver R K ↔
      (∃ n : ℤ, K.IsGE n) ∧
        ∀ p : PrimeSpectrum R,
          ∃ n : ℤ,
            (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K) ⊗[R]^L[
              p.asIdeal.ResidueField]).IsGE n :=
  sorry

end

end CategoryTheory
