import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_82_1 (from Chap15) -/
noncomputable section

open CategoryTheory
open Polynomial

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "ev0" => Polynomial.evalRingHom 0

/- Domain-style sampling for Lemma 15.82.1:
- primary domain: derived base change for the polynomial evaluation map `R[X] → R`;
- sampled owner declarations:
  `Polynomial.evalRingHom`,
  `derivedTensorWithAlgebra`,
  `(ModuleCat.restrictScalars f).mapDerivedCategory`,
  `CategoryTheory.IsIsomorphic`;
- best owner abstraction: the source-facing theorem should use the chapter owner
  `derivedTensorWithAlgebra (Polynomial.evalRingHom 0)`, with restriction of scalars along
  `Polynomial.evalRingHom 0` kept as the bridge/view that places `K` in `D(R[X])`; since the
  comparison is only needed as an object-level existence statement, the public surface should
  remain at the theorem-level `IsIsomorphic` API rather than expose a chosen concrete isomorphism;
- primitive data: the ring hom `R[X] →+* R`;
- derived API: the derived restriction functor, the owner functor
  `derivedTensorWithAlgebra (Polynomial.evalRingHom 0)`, and the theorem that the displayed
  object is isomorphic to `K ⊞ K⟦(1 : ℤ)⟧`.

Source/core/bridge triage:
- `source-facing`: the main isomorphism theorem below;
- `core/canonical`: `Polynomial.evalRingHom`, `derivedTensorWithAlgebra`,
  `ModuleCat.restrictScalars`;
- `bridge/view`: the derived restriction-of-scalars functor
  `(ModuleCat.restrictScalars (Polynomial.evalRingHom 0)).mapDerivedCategory` along
  `Polynomial.evalRingHom 0`. -/

-- Proof sketch: resolve `K` by an `R`-flat complex, view it over `R[X]` via the action with
-- `X = 0`, compute the derived tensor product using the two-term free resolution
-- `R[X] \xrightarrow{X} R[X]` of `R`, and identify the resulting total complex with the split
-- object `K ⊞ K[1]`.
/-- Lemma 15.82.1: if a derived `R`-complex is viewed as an `R[X]`-complex through the map
`R[X] → R` sending `X` to `0`, then derived tensoring back with `R` over `R[X]` is isomorphic to
`K^• ⊞ K^•[1]` in `D(R)`. -/
theorem derivedTensor_restrictScalars_evalAtZero_isomorphic_biprod_shift
    (K : DModR) :
    IsIsomorphic
      ((derivedTensorWithAlgebra ev0).obj
        (((ModuleCat.restrictScalars ev0).mapDerivedCategory).obj K))
      (K ⊞ K⟦(1 : ℤ)⟧) := by
  sorry

end

end CategoryTheory

/-! ### Lemma_15_82_2 (from Chap15) -/
noncomputable section

open CategoryTheory
open Polynomial

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

private abbrev DModR := DerivedCategory.{u + 1, u, u + 1} (ModuleCat R)
local notation "ev0" => Polynomial.evalRingHom (0 : R)

/- Domain-style sampling for Lemma 15.82.2:
- primary domain: pseudo-coherence in derived categories under restriction of scalars along the
  polynomial evaluation map;
- sampled owner declarations:
  `isMPseudoCoherent_iff_restrictScalars`,
  `isPseudoCoherent_iff_restrictScalars`,
  `Polynomial.evalRingHom`,
  `(ModuleCat.restrictScalars f).mapDerivedCategory`;
- best owner abstraction: the chapter owner theorem
  `isMPseudoCoherent_iff_restrictScalars`; the evaluation map `R[X] → R` is bridge data selecting
  the ring hom to which that owner theorem is specialized;
- primitive data: the canonical map `ev0` and the proof that `R`, viewed as an
  `R[X]`-module through that map, is pseudo-coherent;
- derived API: the specialized equivalence below between pseudo-coherence over `R` and over
  `R[X]`, expressed through the canonical derived restriction functor
  `(ModuleCat.restrictScalars ev0).mapDerivedCategory`.

Source/core/bridge triage:
- `source-facing`: the specialized equivalence below for the evaluation-at-zero map;
- `core/canonical`: `isMPseudoCoherent_iff_restrictScalars`;
- `bridge/view`: `(ModuleCat.restrictScalars ev0).mapDerivedCategory`. -/

private theorem regularModule_isPseudoCoherent_evalAtZero :
    ((ModuleCat.restrictScalars ev0).obj (ModuleCat.of R R)).IsPseudoCoherent := by
  -- Proof sketch: use the two-term finite free resolution
  -- `0 → R[X] --·X→ R[X] → R → 0` of `R` over `R[X]`.
  sorry

/-- Lemma 15.82.2: for the polynomial evaluation map `R[X] → R` sending `X` to `0`, a derived
`R`-complex is `m`-pseudo-coherent exactly when the same object viewed by restriction of scalars
as a derived `R[X]`-complex is `m`-pseudo-coherent. -/
theorem isMPseudoCoherent_iff_restrictScalars_evalAtZero
    (K : DModR) (m : ℤ) :
    K.IsMPseudoCoherent m ↔
      ((ModuleCat.restrictScalars ev0).mapDerivedCategory.obj K).IsMPseudoCoherent m := by
  have hB : ((ModuleCat.restrictScalars ev0).obj (ModuleCat.of R R)).IsPseudoCoherent :=
    regularModule_isPseudoCoherent_evalAtZero
  simpa using isMPseudoCoherent_iff_restrictScalars ev0 K m hB

end

end CategoryTheory

/-! ### Lemma_15_82_3 (from Chap15) -/
noncomputable section

open CategoryTheory
open ComplexShape

universe u v

attribute [local instance] HasDerivedCategory.standard

section

variable {R : Type u} {A : Type v}
variable [CommRing R] [CommRing A] [Algebra R A]

local notation "CpxA" => CochainComplex (ModuleCat A) ℤ

/- Domain-style sampling for Lemma 15.82.3:
- primary domain: pseudo-coherence for cochain complexes after restriction along surjective
  polynomial presentations of an `R`-algebra `A`, with finite type only needed for the
  some-presentation/every-presentation equivalences;
- sampled owner declarations:
  `CochainComplex.IsMPseudoCoherent`,
  `CochainComplex.IsPseudoCoherent`,
  `isMPseudoCoherent_iff_restrictScalars_evalAtZero`,
  `cochainComplex_pseudoCoherent_tfae`;
- best owner abstraction: the canonical owner is the restricted cochain complex over the
  presentation ring, together with the project-level cochain-complex predicates
  `CochainComplex.IsMPseudoCoherent` and `CochainComplex.IsPseudoCoherent`; the “some/every
  presentation” formulations are source-facing quantifiers over that owner, not separate public
  data;
- primitive vs. derived:
  primitive data are a surjective polynomial presentation
  `α : MvPolynomial (Fin n) R →ₐ[R] A` and the associated restricted complex;
  derived API is the existential or universal quantification over all such presentations;
- source/core/bridge triage:
  `source-facing`: the two equivalences in Lemma 15.82.3;
  `core/canonical`: `CochainComplex.IsMPseudoCoherent` and
    `CochainComplex.IsPseudoCoherent`;
  `bridge/view`: restriction of scalars along a polynomial presentation.
- layer: this file stays source-facing and deletes redundant public wrappers around the bridge
  data. -/

namespace CochainComplex

/-- Restrict a cochain complex of `A`-modules along a polynomial presentation of `A` over `R`. -/
abbrev polynomialPresentationRestriction
    (K : CochainComplex (ModuleCat A) ℤ) {n : ℕ}
    (α : MvPolynomial (Fin n) R →ₐ[R] A) :
    CochainComplex (ModuleCat (MvPolynomial (Fin n) R)) ℤ :=
  ((ModuleCat.restrictScalars α.toRingHom).mapHomologicalComplex (up ℤ)).obj K

end CochainComplex

-- Proof sketch: compare a chosen surjective polynomial presentation with an arbitrary one by
-- adjoining both sets of variables and mapping the added variables to chosen lifts. After a change
-- of coordinates, the comparison maps are iterated evaluation-at-zero maps, so repeated
-- applications of Lemma `15.82.2` transfer `m`-pseudo-coherence from the chosen presentation to
-- every presentation, and the converse direction is immediate.
/-- Lemma 15.82.3: for a finite type ring map `R → A`, a cochain complex of `A`-modules is
`m`-pseudo-coherent over some surjective polynomial presentation of `A` over `R` if and only if it
is `m`-pseudo-coherent over every such presentation. -/
theorem cochainComplex_isMPseudoCoherentOverSomePolynomialPresentation_iff_overEveryPolynomialPresentation
    [Algebra.FiniteType R A] (K : CpxA) (m : ℤ) :
    (∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
      Function.Surjective α ∧ (K.polynomialPresentationRestriction α).IsMPseudoCoherent m) ↔
      ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
        Function.Surjective α → (K.polynomialPresentationRestriction α).IsMPseudoCoherent m :=
    sorry

-- Proof sketch: use the previous equivalence for every integer `m`; then invoke Lemma `15.65.5`
-- on each presentation ring to pass between pseudo-coherence and `m`-pseudo-coherence for all
-- `m`.
/-- Pseudo-coherence relative to `R` can likewise be checked on one surjective polynomial
presentation of the finite type `R`-algebra `A`. -/
theorem cochainComplex_isPseudoCoherentOverSomePolynomialPresentation_iff_overEveryPolynomialPresentation
    [Algebra.FiniteType R A] (K : CpxA) :
    (∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
      Function.Surjective α ∧ (K.polynomialPresentationRestriction α).IsPseudoCoherent) ↔
      ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
        Function.Surjective α → (K.polynomialPresentationRestriction α).IsPseudoCoherent := sorry

end

/-! ### Definition_15_82_4 (from Chap15) -/
noncomputable section

open CategoryTheory
open ComplexShape

universe u v

attribute [local instance] HasDerivedCategory.standard

section

variable {R : Type u} {A : Type v}
variable [CommRing R] [CommRing A] [Algebra R A]

local notation "CpxA" => CochainComplex (ModuleCat A) ℤ
/- Domain-style sampling for Definition 15.82.4:
- primary domain: relative pseudo-coherence for cochain complexes and modules over an `R`-algebra
  `A` of finite type over `R`;
- sampled owner declarations:
  `CochainComplex.IsMPseudoCoherent`,
  `CochainComplex.IsPseudoCoherent`,
  `cochainComplex_isMPseudoCoherentOverSomePolynomialPresentation_iff_overEveryPolynomialPresentation`,
  `cochainComplex_isPseudoCoherentOverSomePolynomialPresentation_iff_overEveryPolynomialPresentation`;
- best owner abstraction: the source-facing owners are the relative predicates
  `CochainComplex.IsMPseudoCoherentRelativeTo` and
  `CochainComplex.IsPseudoCoherentRelativeTo`; the absolute pseudo-coherence owners on the
  restricted complexes over polynomial presentation rings remain the canonical core notions;
- primitive vs. derived:
  primitive data are the universal tests over surjective polynomial presentations of the finite
  type `R`-algebra `A`;
  derived API is the "some presentation" criterion and the module specialization
  `M ↦ M[0]`, exposed both for bundled `ModuleCat A` objects and for ordinary unbundled
  `A`-modules;
- source/core/bridge triage:
  `source-facing`: the relative pseudo-coherence predicates for cochain complexes and modules;
  `core/canonical`: `CochainComplex.IsMPseudoCoherent` and `CochainComplex.IsPseudoCoherent` over
    the presentation rings;
  `bridge/view`: restriction of scalars along a polynomial presentation, plus the thin unbundled
    module surface `Module.IsMPseudoCoherentRelativeTo` /
    `Module.IsPseudoCoherentRelativeTo`.
- layer: this file stays source-facing and reuses the established presentationwise owner API
  instead of keeping redundant local `_def` / `_iff` wrappers around definitional equalities.
-/

namespace CochainComplex

/-- Definition 15.82.4 (1): a cochain complex of `A`-modules is `m`-pseudo-coherent relative to
`R` if it satisfies the equivalent conditions of Lemma `15.82.3`, equivalently if it is
`m`-pseudo-coherent over every surjective polynomial presentation of `A` over `R`. -/
abbrev IsMPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (K : CochainComplex (ModuleCat A) ℤ) (m : ℤ) : Prop :=
  ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A) (_ : Function.Surjective α),
    (K.polynomialPresentationRestriction α).IsMPseudoCoherent m

/-- Relative `m`-pseudo-coherence can be checked on some surjective polynomial presentation of the
finite type `R`-algebra `A`. -/
theorem isMPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation
    [Algebra.FiniteType R A] (K : CpxA) (m : ℤ) :
    K.IsMPseudoCoherentRelativeTo R m ↔
      ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
        Function.Surjective α ∧ (K.polynomialPresentationRestriction α).IsMPseudoCoherent m := by
  simpa [IsMPseudoCoherentRelativeTo] using
    (cochainComplex_isMPseudoCoherentOverSomePolynomialPresentation_iff_overEveryPolynomialPresentation
      K m).symm

/-- Definition 15.82.4 (2): a cochain complex of `A`-modules is pseudo-coherent relative to `R`
if it is `m`-pseudo-coherent relative to `R` for every integer `m`. -/
abbrev IsPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (K : CochainComplex (ModuleCat A) ℤ) : Prop :=
  ∀ m : ℤ, K.IsMPseudoCoherentRelativeTo R m

/-- Relative pseudo-coherence is equivalent to pseudo-coherence over every surjective polynomial
presentation of the finite type `R`-algebra `A`. -/
theorem isPseudoCoherentRelativeTo_iff_overEveryPolynomialPresentation
    [Algebra.FiniteType R A]
    (K : CpxA) :
    K.IsPseudoCoherentRelativeTo R ↔
      ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A) (_ : Function.Surjective α),
        (K.polynomialPresentationRestriction α).IsPseudoCoherent := by
  constructor
  · intro hK n α hα
    exact
      ((cochainComplex_pseudoCoherent_tfae (K.polynomialPresentationRestriction α)).out 1 0).mp
        (fun m ↦ hK m n α hα)
  · intro hK m n α hα
    have hPresentation :
        ∀ m : ℤ, (K.polynomialPresentationRestriction α).IsMPseudoCoherent m :=
      ((cochainComplex_pseudoCoherent_tfae (K.polynomialPresentationRestriction α)).out 0 1).mp
        (hK n α hα)
    exact hPresentation m

/-- Relative pseudo-coherence can be checked on some surjective polynomial presentation of the
finite type `R`-algebra `A`. -/
theorem isPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation
    [Algebra.FiniteType R A] (K : CpxA) :
    K.IsPseudoCoherentRelativeTo R ↔
      ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
        Function.Surjective α ∧ (K.polynomialPresentationRestriction α).IsPseudoCoherent := by
  calc
    K.IsPseudoCoherentRelativeTo R ↔
        ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A) (_ : Function.Surjective α),
          (K.polynomialPresentationRestriction α).IsPseudoCoherent :=
      isPseudoCoherentRelativeTo_iff_overEveryPolynomialPresentation K
    _ ↔
        ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
          Function.Surjective α ∧ (K.polynomialPresentationRestriction α).IsPseudoCoherent := by
      simpa using
        (cochainComplex_isPseudoCoherentOverSomePolynomialPresentation_iff_overEveryPolynomialPresentation
          K).symm

end CochainComplex

/-- Definition 15.82.4 (3): an `A`-module is `m`-pseudo-coherent relative to `R` if the
degree-zero cochain complex `M[0]` is `m`-pseudo-coherent relative to `R`. -/
abbrev ModuleCat.IsMPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (M : ModuleCat A) (m : ℤ) : Prop :=
  ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj M).IsMPseudoCoherentRelativeTo R m

/-- Definition 15.82.4 (4): an `A`-module is pseudo-coherent relative to `R` if the degree-zero
cochain complex `M[0]` is pseudo-coherent relative to `R`. -/
abbrev ModuleCat.IsPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (M : ModuleCat A) : Prop :=
  ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj M).IsPseudoCoherentRelativeTo R

namespace Module

/-- Relative `m`-pseudo-coherence for an ordinary `A`-module, viewed through the canonical bundled
module object. -/
abbrev IsMPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (M : Type u_1) [AddCommGroup M] [Module A M] (m : ℤ) : Prop :=
  (ModuleCat.of A M).IsMPseudoCoherentRelativeTo R m

/-- Relative pseudo-coherence for an ordinary `A`-module, viewed through the canonical bundled
module object. -/
abbrev IsPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (M : Type u_1) [AddCommGroup M] [Module A M] : Prop :=
  (ModuleCat.of A M).IsPseudoCoherentRelativeTo R

end Module

end

/-! ### Lemma_15_82_5 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R A B : Type u}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable [Algebra.FiniteType R A] [Module.Finite A B]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModB" => DerivedCategory (ModuleCat B)
local notation "restrictScalarsDerived" =>
  CategoryTheory.Functor.mapDerivedCategory (ModuleCat.restrictScalars (algebraMap A B))

private theorem finiteType_over_base
    (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FiniteType R A] [Module.Finite A B] :
    Algebra.FiniteType R B := by
  exact
    Algebra.FiniteType.trans
      (inferInstance : Algebra.FiniteType R A)
      (inferInstance : Algebra.FiniteType A B)

/-
Domain-style sampling for Lemma 15.82.5:
- primary domain: relative pseudo-coherence in derived categories under restriction of scalars
  along a finite algebra map;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherentRelativeTo`,
  `DerivedCategory.IsPseudoCoherentRelativeTo`,
  `isMPseudoCoherent_iff_restrictScalars`,
  `isPseudoCoherent_iff_restrictScalars`;
- best owner abstraction: the source-facing content is the pair of comparison theorems below,
  while the canonical owner predicates are
  `DerivedCategory.IsMPseudoCoherentRelativeTo` and
  `DerivedCategory.IsPseudoCoherentRelativeTo`; the restriction construction itself is owned by
  `(ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory`;
- primitive vs. derived:
  primitive data are the relative pseudo-coherence owners, the finite-type structure on `A` over
  `R`, and the finite map hypothesis `[Module.Finite A B]`;
  the induced finite-type structure on `B` over `R` is derived internally by the canonical
  transitivity instance for finite type algebras;
- source/core/bridge triage:
  `source-facing`: the two comparison theorems below;
  `core/canonical`: `DerivedCategory.IsMPseudoCoherentRelativeTo`,
    `DerivedCategory.IsPseudoCoherentRelativeTo`, and `Functor.mapDerivedCategory`;
  `bridge/view`: restriction of scalars along `algebraMap A B`, together with the internal
    finite-type witness on `R → B`.
-/

-- Proof sketch: for any surjective polynomial presentation `P → A`, compose with the finite map
-- `A → B` to view `B` as a finite `P`-algebra, then apply Lemma `15.65.11` over `P` to compare
-- `m`-pseudo-coherence of `K` with that of its restriction along `A → B`.
/-- Lemma 15.82.5: let `R` be a ring, let `A → B` be a finite map of finite type `R`-algebras,
let `m ∈ ℤ`, and let `K` be a derived `B`-complex. Then `K` is `m`-pseudo-coherent relative to
`R` if and only if the same object, viewed by restriction of scalars as a derived `A`-complex, is
`m`-pseudo-coherent relative to `R`. -/
theorem isMPseudoCoherentRelativeTo_iff_restrictScalars_of_finite
    (K : DModB) (m : ℤ) :
    by
      letI : Algebra.FiniteType R B := finiteType_over_base R A B
      exact
        K.IsMPseudoCoherentRelativeTo R m ↔
          ((restrictScalarsDerived).obj K).IsMPseudoCoherentRelativeTo R m := by
  sorry

-- Proof sketch: apply the previous theorem for each integer `m`, using the canonical owner
-- `IsPseudoCoherentRelativeTo` as the universal quantification of the `m`-relative notion.
/-- Under the same finite-map hypotheses, relative pseudo-coherence over `R` is unchanged by
restricting scalars from `B` to `A`. -/
theorem isPseudoCoherentRelativeTo_iff_restrictScalars_of_finite
    (K : DModB) :
    by
      letI : Algebra.FiniteType R B := finiteType_over_base R A B
      exact
        K.IsPseudoCoherentRelativeTo R ↔
          ((restrictScalarsDerived).obj K).IsPseudoCoherentRelativeTo R := by
  sorry

end

end CategoryTheory

/-! ### Lemma_15_82_6 (from Chap15) -/
noncomputable section

open CategoryTheory ObjectProperty Pretriangulated

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} {A : Type v}
variable [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]

local notation "DModA" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.82.6:
- primary domain: relative pseudo-coherent object properties in the derived category `D(A)` and
  their closure under distinguished triangles for a finite type ring map `R → A`;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherentRelativeTo`,
  `DerivedCategory.IsPseudoCoherentRelativeTo`,
  `ObjectProperty.IsTriangulatedClosed₂`,
  `ObjectProperty.IsTriangulated`;
- best owner abstraction: the fixed-`m` closure owner is the object property
  `fun K : DModA ↦ K.IsMPseudoCoherentRelativeTo R m`, while the pseudo-coherent owner is
  `fun K : DModA ↦ K.IsPseudoCoherentRelativeTo R`;
- primitive vs. derived:
  primitive data are the relative `m`-pseudo-coherent and pseudo-coherent predicates from
  Definition `15.82.4` and Lemma `15.82.10`;
  derived API is the distinguished-triangle closure, with parts `(1)`-`(3)` providing the
  degreewise `m`-pseudo-coherent input and parts `(4)`-`(6)` derived from the owner abstraction;
- source/core/bridge triage:
  `source-facing`: the six textbook closure statements for relative pseudo-coherence in a
    distinguished triangle;
  `core/canonical`: `ObjectProperty.IsTriangulatedClosed₂
    (fun K : DModA ↦ K.IsMPseudoCoherentRelativeTo R m)` for the fixed-`m` layer, and
    `ObjectProperty.IsTriangulated
    (fun K : DModA ↦ K.IsPseudoCoherentRelativeTo R)`;
  `bridge/view`: deriving the pseudo-coherent `obj₁`/`obj₂`/`obj₃` statements from that owner.
- layer: this file keeps the source-facing statements, but it targets the `core/canonical` layer
  first for fixed-`m` clause `(2)` and then for the pseudo-coherent part, so downstream files
  reuse the triangulated owner rather than a parallel family of standalone lemmas.
-/

-- Proof sketch: fix a surjective polynomial presentation `P → A`, restrict the distinguished
-- triangle from `D(A)` to `D(P)`, and apply the distinguished-triangle closure of
-- `m`-pseudo-coherence over the polynomial ring `P`.
/-- Lemma 15.82.6 (1): for a finite type ring map `R → A` and a distinguished triangle in
`D(A)`, if the first term is `(m + 1)`-pseudo-coherent relative to `R` and the second term is
`m`-pseudo-coherent relative to `R`, then the third term is `m`-pseudo-coherent relative to
`R`. -/
theorem isMPseudoCoherentRelativeTo_obj₃_of_distinguishedTriangle
    {m : ℤ} (T : Triangle DModA) (hT : T ∈ distTriang DModA)
    (h₁ : T.obj₁.IsMPseudoCoherentRelativeTo R (m + 1))
    (h₂ : T.obj₂.IsMPseudoCoherentRelativeTo R m) :
    T.obj₃.IsMPseudoCoherentRelativeTo R m := sorry

instance isMPseudoCoherentRelativeTo_isClosedUnderIsomorphisms (m : ℤ) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun K : DModA ↦ K.IsMPseudoCoherentRelativeTo R m) where
  of_iso _ _ := by
    sorry

/-- For fixed `m`, relative `m`-pseudo-coherent objects of `D(A)` satisfy the canonical
`ObjectProperty.IsTriangulatedClosed₂` two-out-of-three axiom. -/
instance isMPseudoCoherentRelativeTo_isTriangulatedClosed₂ (m : ℤ) :
    ObjectProperty.IsTriangulatedClosed₂
      (fun K : DModA ↦ K.IsMPseudoCoherentRelativeTo R m) := by
  sorry

-- Proof sketch: fix a surjective polynomial presentation `P → A`, restrict the distinguished
-- triangle from `D(A)` to `D(P)`, and apply the second distinguished-triangle closure statement
-- for `m`-pseudo-coherence over `P`.
/-- Lemma 15.82.6 (2): for a finite type ring map `R → A` and a distinguished triangle in
`D(A)`, if the first and third terms are `m`-pseudo-coherent relative to `R`, then the second
term is `m`-pseudo-coherent relative to `R`. -/
theorem isMPseudoCoherentRelativeTo_obj₂_of_distinguishedTriangle
    {m : ℤ} (T : Triangle DModA) (hT : T ∈ distTriang DModA)
    (h₁ : T.obj₁.IsMPseudoCoherentRelativeTo R m)
    (h₃ : T.obj₃.IsMPseudoCoherentRelativeTo R m) :
    T.obj₂.IsMPseudoCoherentRelativeTo R m := by
  sorry

-- Proof sketch: fix a surjective polynomial presentation `P → A`, restrict the distinguished
-- triangle from `D(A)` to `D(P)`, and apply the third distinguished-triangle closure statement
-- for `m`-pseudo-coherence over `P`.
/-- Lemma 15.82.6 (3): for a finite type ring map `R → A` and a distinguished triangle in
`D(A)`, if the second term is `(m + 1)`-pseudo-coherent relative to `R` and the third term is
`m`-pseudo-coherent relative to `R`, then the first term is `(m + 1)`-pseudo-coherent relative
to `R`. -/
theorem isMPseudoCoherentRelativeTo_obj₁_of_distinguishedTriangle
    {m : ℤ} (T : Triangle DModA) (hT : T ∈ distTriang DModA)
    (h₂ : T.obj₂.IsMPseudoCoherentRelativeTo R (m + 1))
    (h₃ : T.obj₃.IsMPseudoCoherentRelativeTo R m) :
    T.obj₁.IsMPseudoCoherentRelativeTo R (m + 1) := sorry

instance isPseudoCoherentRelativeTo_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun K : DModA ↦ K.IsPseudoCoherentRelativeTo R) where
  of_iso _ _ := by
    sorry

-- Proof sketch: combine the degreewise distinguished-triangle closure from parts `(1)`-`(3)` with
-- the defining universal quantification of `IsPseudoCoherentRelativeTo`, exactly as in the
-- absolute analogue `Lemma 15.65.6`. The previous instance supplies the needed closure under
-- isomorphisms for the owner object property.
/-- Canonical owner form of Lemma 15.82.6 (4)-(6): pseudo-coherent objects of `D(A)` relative to
`R` form a triangulated object property. -/
instance isPseudoCoherentRelativeTo_isTriangulated :
    ObjectProperty.IsTriangulated
      (fun K : DModA ↦ K.IsPseudoCoherentRelativeTo R) := by
  sorry

-- Proof sketch: unfold relative pseudo-coherence as relative `m`-pseudo-coherence for all
-- integers `m`, equivalently apply the `obj₁`-`obj₂` to `obj₃` consequence of the triangulated
-- owner instance above.
/-- Lemma 15.82.6 (4): for a finite type ring map `R → A` and a distinguished triangle in
`D(A)`, if the first two terms are pseudo-coherent relative to `R`, then the third term is
pseudo-coherent relative to `R`. -/
theorem isPseudoCoherentRelativeTo_obj₃_of_distinguishedTriangle
    (T : Triangle DModA) (hT : T ∈ distTriang DModA)
    (h₁ : T.obj₁.IsPseudoCoherentRelativeTo R)
    (h₂ : T.obj₂.IsPseudoCoherentRelativeTo R) :
    T.obj₃.IsPseudoCoherentRelativeTo R := by
  sorry

-- Proof sketch: unfold relative pseudo-coherence as relative `m`-pseudo-coherence for all
-- integers `m`, equivalently apply the `obj₁`-`obj₃` to `obj₂` consequence of the triangulated
-- owner instance above.
/-- Lemma 15.82.6 (5): for a finite type ring map `R → A` and a distinguished triangle in
`D(A)`, if the first and third terms are pseudo-coherent relative to `R`, then the second term
is pseudo-coherent relative to `R`. -/
theorem isPseudoCoherentRelativeTo_obj₂_of_distinguishedTriangle
    (T : Triangle DModA) (hT : T ∈ distTriang DModA)
    (h₁ : T.obj₁.IsPseudoCoherentRelativeTo R)
    (h₃ : T.obj₃.IsPseudoCoherentRelativeTo R) :
    T.obj₂.IsPseudoCoherentRelativeTo R := by
  sorry

-- Proof sketch: unfold relative pseudo-coherence as relative `m`-pseudo-coherence for all
-- integers `m`, equivalently apply the `obj₂`-`obj₃` to `obj₁` consequence of the triangulated
-- owner instance above.
/-- Lemma 15.82.6 (6): for a finite type ring map `R → A` and a distinguished triangle in
`D(A)`, if the second and third terms are pseudo-coherent relative to `R`, then the first term
is pseudo-coherent relative to `R`. -/
theorem isPseudoCoherentRelativeTo_obj₁_of_distinguishedTriangle
    (T : Triangle DModA) (hT : T ∈ distTriang DModA)
    (h₂ : T.obj₂.IsPseudoCoherentRelativeTo R)
    (h₃ : T.obj₃.IsPseudoCoherentRelativeTo R) :
    T.obj₁.IsPseudoCoherentRelativeTo R := by
  sorry

end

end CategoryTheory

/-! ### Lemma_15_82_7 (from Chap15) -/
noncomputable section

universe u v w

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

section

variable {R : Type u} {A : Type v} {M : Type w}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module A M]
variable [Algebra.FiniteType R A]

/- Domain-style sampling:
- primary domain: relative pseudo-coherence for modules over a finite type algebra;
- sampled owner declarations:
  `Module.IsMPseudoCoherentRelativeTo`,
  `Module.IsPseudoCoherentRelativeTo`,
  `ModuleCat.IsMPseudoCoherentRelativeTo`,
  `ModuleCat.IsPseudoCoherentRelativeTo`,
  `Module.FinitePresentationRelativeTo`,
  `Module.HasLengthFiniteFreeResolution`;
- best owner abstraction: the thin unbundled module bridge owners
  `Module.IsMPseudoCoherentRelativeTo R A M` and
  `Module.IsPseudoCoherentRelativeTo R A M`, which reuse the chapter owners on `ModuleCat`;
- primitive data: the bundled module object `ModuleCat.of A M` together with the existing relative
  pseudo-coherence owner from `Definition_15_82_4`;
- derived API: finite / finitely presented / finite-free-resolution criteria obtained by testing
  the restricted module over every surjective polynomial presentation of `A`.

Source/core/bridge triage:
- `source-facing`: the four equivalences of Lemma `15.82.7`;
- `core/canonical`: `ModuleCat.IsMPseudoCoherentRelativeTo`,
  `ModuleCat.IsPseudoCoherentRelativeTo`,
  `Module.FinitePresentationRelativeTo`,
  `Module.HasLengthFiniteFreeResolution`,
  and Lemma `15.65.4`;
- `bridge/view`: the presentationwise finite-free-resolution criteria on the right-hand sides of
  parts `(3)` and `(4)`.

The canonical owner remains the chapter predicate on `ModuleCat`, but the ordinary theorem surface
for unbundled modules should use the thin bridge `Module.IsMPseudoCoherentRelativeTo` /
`Module.IsPseudoCoherentRelativeTo` rather than repeating `ModuleCat.of A M`. -/

-- Proof sketch: for each surjective polynomial presentation `α`, apply Lemma `15.65.4 (1)` over
-- `MvPolynomial (Fin n) R` to identify `0`-pseudo-coherence with finite generation. Finite
-- generation descends and ascends along the surjection `α`, so the pointwise condition is
-- equivalent to finite generation over `A`.
/-- Lemma 15.82.7 (1): an `A`-module is `0`-pseudo-coherent relative to `R` exactly when it is a
finite `A`-module. -/
theorem Module.isZeroPseudoCoherentRelativeTo_iff_finite :
    Module.IsMPseudoCoherentRelativeTo R A M 0 ↔ Module.Finite A M := sorry

-- Proof sketch: apply Lemma `15.65.4 (2)` to each surjective polynomial presentation of `A` over
-- `R`. Then use Lemma `15.81.1` to pass between finite presentation over one presentation and over
-- every presentation.
/-- Lemma 15.82.7 (2): an `A`-module is `(-1)`-pseudo-coherent relative to `R` exactly when it is
finitely presented relative to `R`. -/
theorem Module.isMinusOnePseudoCoherentRelativeTo_iff_finitePresentationRelativeTo :
    Module.IsMPseudoCoherentRelativeTo R A M (-1) ↔
      Module.FinitePresentationRelativeTo R A M := sorry

-- Proof sketch: for each surjective polynomial presentation `α`, apply Lemma `15.65.4 (3)` over
-- the polynomial ring `MvPolynomial (Fin n) R`; this identifies `(-(d : ℤ))`-pseudo-coherence
-- with the existence of a length-`d` finite free resolution over that presentation ring.
/-- Lemma 15.82.7 (3): for `d : ℕ`, an `A`-module is `(-d)`-pseudo-coherent relative to `R`
exactly when for every surjective polynomial presentation of `A` over `R`, the induced module
admits a length-`d` finite free resolution. -/
theorem Module.isNegPseudoCoherentRelativeTo_iff_hasLengthFiniteFreeResolutionRelativeTo
    (d : ℕ) :
    Module.IsMPseudoCoherentRelativeTo R A M (-(d : ℤ)) ↔
      ∀ n : ℕ,
        let P := MvPolynomial (Fin n) R
        ∀ (α : P →ₐ[R] A) (_ : Function.Surjective α),
          let _ : Module P M := Module.compHom M α.toRingHom
          Module.HasLengthFiniteFreeResolution P M d := sorry

-- Proof sketch: apply Lemma `15.65.4 (4)` over each surjective polynomial presentation of `A`
-- over `R`; the pointwise pseudo-coherence condition is equivalent to the existence of an infinite
-- finite free resolution over every such presentation ring.
/-- Lemma 15.82.7 (4): an `A`-module is pseudo-coherent relative to `R` exactly when for every
surjective polynomial presentation of `A` over `R`, the induced module admits an infinite
resolution by finite free modules. -/
theorem Module.isPseudoCoherentRelativeTo_iff_hasInfiniteFiniteFreeResolutionRelativeTo :
    Module.IsPseudoCoherentRelativeTo R A M ↔
      ∀ n : ℕ,
        let P := MvPolynomial (Fin n) R
        ∀ (α : P →ₐ[R] A) (_ : Function.Surjective α),
          let _ : Module P M := Module.compHom M α.toRingHom
          ∃ (F : ChainComplex (ModuleCat P) ℕ)
            (π : F ⟶ (ChainComplex.single₀ (ModuleCat P)).obj (ModuleCat.of P M)),
            ChainComplex.IsFiniteFreeResolution π := sorry

end

/-! ### Lemma_15_82_8 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.ObjectProperty.IsStableUnderRetracts

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} {A : Type v}
variable [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]

local notation "DModA" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.82.8:
- primary domain: relative pseudo-coherence in `D(A)` for a finite type `R`-algebra `A`;
- sampled owner declarations:
  `CategoryTheory.ObjectProperty.IsStableUnderRetracts`,
  `DerivedCategory.IsMPseudoCoherentRelativeTo`,
  `DerivedCategory.IsPseudoCoherentRelativeTo`,
  `isMPseudoCoherent_isStableUnderRetracts`;
- best owner abstraction: the chapter-standard owner layer is
  `ObjectProperty.IsStableUnderRetracts (fun K : DModA ↦ K.IsMPseudoCoherentRelativeTo R m)` and
  `ObjectProperty.IsStableUnderRetracts (fun K : DModA ↦ K.IsPseudoCoherentRelativeTo R)`;
- primitive vs. derived:
  primitive data are the relative pseudo-coherence owners from Definition `15.82.4` and
  Lemma `15.82.10`;
  derived API is the source-facing direct-summand consequence, obtained from retract-stability via
  `of_biprod_left` and `of_biprod_right`;
- source/core/bridge triage:
  `source-facing`: the direct-summand statements of Lemma `15.82.8`;
  `core/canonical`: retract-stability for the relative pseudo-coherence object properties;
  `bridge/view`: restriction to each surjective polynomial presentation of `A` over `R`, where the
    absolute retract-stability instances apply.
- layer: this file now targets the `core/canonical` owner layer first and derives the textbook
  biproduct lemmas from it, matching the Chapter 15 pattern of `Lemma_15_65_8`.
-/

-- Proof sketch: for each surjective polynomial presentation `α : R[x₁, ..., xₙ] → A`, map a
-- retract `K ⟶ L ⟶ K` through the derived restriction-of-scalars functor to `D(R[x₁, ..., xₙ])`
-- and apply the absolute retract-stability of `m`-pseudo-coherence there.
/-- Relative `m`-pseudo-coherent objects of `D(A)` are stable under retracts/direct summands. -/
instance isMPseudoCoherentRelativeTo_isStableUnderRetracts (m : ℤ) :
    ObjectProperty.IsStableUnderRetracts
      (fun K : DModA ↦ K.IsMPseudoCoherentRelativeTo R m) where
  of_retract h hK := by
    intro n α hα
    exact
      prop_of_retract
        (fun K : DerivedCategory (ModuleCat (MvPolynomial (Fin n) R)) ↦ K.IsMPseudoCoherent m)
        (h.map ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory))
        (hK n α hα)

-- Proof sketch: apply the previous retract-stability instance degreewise in `m`.
/-- Relative pseudo-coherent objects of `D(A)` are stable under retracts/direct summands. -/
instance isPseudoCoherentRelativeTo_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts
      (fun K : DModA ↦ K.IsPseudoCoherentRelativeTo R) where
  of_retract h hK := by
    intro m
    exact
      prop_of_retract
        (fun K : DModA ↦ K.IsMPseudoCoherentRelativeTo R m)
        h (hK m)

/-- If `K ⊞ L` is `m`-pseudo-coherent relative to `R`, then `K` is `m`-pseudo-coherent relative to
`R`. -/
theorem isMPseudoCoherentRelativeTo_left_of_biprod
    (K L : DModA) (m : ℤ)
    (hKL : (K ⊞ L).IsMPseudoCoherentRelativeTo R m) :
    K.IsMPseudoCoherentRelativeTo R m := by
  exact of_biprod_left (fun X : DModA ↦ X.IsMPseudoCoherentRelativeTo R m) hKL

/-- If `K ⊞ L` is `m`-pseudo-coherent relative to `R`, then `L` is `m`-pseudo-coherent relative to
`R`. -/
theorem isMPseudoCoherentRelativeTo_right_of_biprod
    (K L : DModA) (m : ℤ)
    (hKL : (K ⊞ L).IsMPseudoCoherentRelativeTo R m) :
    L.IsMPseudoCoherentRelativeTo R m := by
  exact of_biprod_right (fun X : DModA ↦ X.IsMPseudoCoherentRelativeTo R m) hKL

-- Proof sketch: combine the left and right summand statements for relative `m`-pseudo-coherence.
/-- Lemma 15.82.8 (1): if `K^• ⊞ L^•` is `m`-pseudo-coherent relative to `R`, then both `K^•`
and `L^•` are `m`-pseudo-coherent relative to `R`. -/
theorem isMPseudoCoherentRelativeTo_summands_of_biprod
    (K L : DModA) (m : ℤ)
    (hKL : (K ⊞ L).IsMPseudoCoherentRelativeTo R m) :
    K.IsMPseudoCoherentRelativeTo R m ∧ L.IsMPseudoCoherentRelativeTo R m := by
  exact
    ⟨isMPseudoCoherentRelativeTo_left_of_biprod K L m hKL,
      isMPseudoCoherentRelativeTo_right_of_biprod K L m hKL⟩

/-- If `K ⊞ L` is pseudo-coherent relative to `R`, then `K` is pseudo-coherent relative to `R`. -/
theorem isPseudoCoherentRelativeTo_left_of_biprod
    (K L : DModA)
    (hKL : (K ⊞ L).IsPseudoCoherentRelativeTo R) :
    K.IsPseudoCoherentRelativeTo R := by
  exact of_biprod_left (fun X : DModA ↦ X.IsPseudoCoherentRelativeTo R) hKL

/-- If `K ⊞ L` is pseudo-coherent relative to `R`, then `L` is pseudo-coherent relative to `R`. -/
theorem isPseudoCoherentRelativeTo_right_of_biprod
    (K L : DModA)
    (hKL : (K ⊞ L).IsPseudoCoherentRelativeTo R) :
    L.IsPseudoCoherentRelativeTo R := by
  exact of_biprod_right (fun X : DModA ↦ X.IsPseudoCoherentRelativeTo R) hKL

-- Proof sketch: combine the left and right pseudo-coherent summand statements.
/-- Lemma 15.82.8 (2): if `K^• ⊞ L^•` is pseudo-coherent relative to `R`, then both `K^•` and
`L^•` are pseudo-coherent relative to `R`. -/
theorem isPseudoCoherentRelativeTo_summands_of_biprod
    (K L : DModA)
    (hKL : (K ⊞ L).IsPseudoCoherentRelativeTo R) :
    K.IsPseudoCoherentRelativeTo R ∧ L.IsPseudoCoherentRelativeTo R := by
  exact
    ⟨isPseudoCoherentRelativeTo_left_of_biprod K L hKL,
      isPseudoCoherentRelativeTo_right_of_biprod K L hKL⟩

end

end CategoryTheory

/-! ### Lemma_15_82_9 (from Chap15) -/
noncomputable section

open CategoryTheory
open ComplexShape

universe u v

attribute [local instance] HasDerivedCategory.standard

section

variable {R : Type u} {A : Type v}
variable [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]

local notation "CpxA" => CochainComplex (ModuleCat A) ℤ

/- Domain-style sampling for Lemma 15.82.9:
- primary domain: relative pseudo-coherence for bounded-above cochain complexes of `A`-modules
  over a finite type `R`-algebra `A`;
- sampled owner declarations:
  `CochainComplex.minus`,
  `CochainComplex.IsMPseudoCoherentRelativeTo`,
  `CochainComplex.IsPseudoCoherentRelativeTo`,
  `CochainComplex.isMPseudoCoherent_of_boundedAbove_of_termwise`;
- best owner abstraction: the source-facing owners are the relative predicates
  `CochainComplex.IsMPseudoCoherentRelativeTo` and
  `CochainComplex.IsPseudoCoherentRelativeTo`, while bounded-above should be expressed through the
  chapter owner `CochainComplex.minus` rather than the duplicate existential presentation
  `∃ b, K.IsStrictlyLE b`;
- primitive vs. derived:
  primitive data are the bounded-above cochain complex `K : CpxA` and the termwise relative
  pseudo-coherence hypotheses on `K.X i`;
  derived API is the resulting relative pseudo-coherence of `K`;
- source/core/bridge triage:
  `source-facing`: the two termwise bounded-above criteria below;
  `core/canonical`: `CochainComplex.minus`, `CochainComplex.IsMPseudoCoherentRelativeTo`, and
    `CochainComplex.IsPseudoCoherentRelativeTo`;
  `bridge/view`: restriction along surjective polynomial presentations together with the absolute
    bounded-above criterion of `CochainComplex.isMPseudoCoherent_of_boundedAbove_of_termwise`.
- layer: this file stays source-facing and reuses the existing bounded-above owner instead of
  restating it as an existential bound. -/

-- Proof sketch: fix a surjective polynomial presentation `α : R[x_1, ..., x_n] → A`. By the
-- relative hypotheses, every term of the restricted complex is `(m - i)`-pseudo-coherent over the
-- polynomial ring. Apply Lemma `15.65.9` to that restricted bounded-above complex, and then
-- quantify over all presentations.
/-- Lemma 15.82.9 (1): if `R → A` is finite type and a bounded-above cochain complex of
`A`-modules has term `K.X i` `(m - i)`-pseudo-coherent relative to `R` for every `i`, then the
complex is `m`-pseudo-coherent relative to `R`. -/
theorem cochainComplex_isMPseudoCoherentRelativeTo_of_boundedAbove_of_termwise
    (K : CpxA) (m : ℤ)
    (hbounded : CochainComplex.minus (ModuleCat A) K)
    (hterm : ∀ i : ℤ, (K.X i).IsMPseudoCoherentRelativeTo R (m - i)) :
    K.IsMPseudoCoherentRelativeTo R m := sorry

-- Proof sketch: for each surjective polynomial presentation of `A` over `R`, every term of the
-- restricted complex is pseudo-coherent over the polynomial ring. Apply Lemma `15.65.9` in its
-- pseudo-coherent form to the restricted bounded-above complex, and then quantify over all
-- presentations.
/-- Lemma 15.82.9 (2): if `R → A` is finite type and a bounded-above cochain complex of
`A`-modules has pseudo-coherent terms relative to `R`, then the complex is pseudo-coherent
relative to `R`. -/
theorem cochainComplex_isPseudoCoherentRelativeTo_of_boundedAbove_of_termwise
    (K : CpxA)
    (hbounded : CochainComplex.minus (ModuleCat A) K)
    (hterm : ∀ i : ℤ, (K.X i).IsPseudoCoherentRelativeTo R) :
    K.IsPseudoCoherentRelativeTo R := sorry

end

/-! ### Lemma_15_82_10 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable [Algebra.FiniteType R A]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModAMinus" => boundedAboveDerivedCategory (ModuleCat A)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)

private abbrev polynomialPresentationRestrictionDerived {n : ℕ}
    (α : MvPolynomial (Fin n) R →ₐ[R] A) (K : DModA) :
    DerivedCategory (ModuleCat (MvPolynomial (Fin n) R)) :=
  (ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K

/-- A derived `A`-complex is `m`-pseudo-coherent relative to `R` if it becomes
`m`-pseudo-coherent after restriction along every surjective polynomial presentation of `A`
over `R`. -/
abbrev DerivedCategory.IsMPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] ⦃A : Type v⦄ [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (K : DerivedCategory (ModuleCat A)) (m : ℤ) : Prop :=
  ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A), Function.Surjective α →
    (polynomialPresentationRestrictionDerived α K).IsMPseudoCoherent m

/-- A derived `A`-complex is pseudo-coherent relative to `R` if it is `m`-pseudo-coherent
relative to `R` for every integer `m`. -/
abbrev DerivedCategory.IsPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] ⦃A : Type v⦄ [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (K : DerivedCategory (ModuleCat A)) : Prop :=
  ∀ m : ℤ, K.IsMPseudoCoherentRelativeTo R m

/- Domain-style sampling for Lemma 15.82.10:
- primary domain: relative pseudo-coherence in `D(A)` for a finite type `R`-algebra `A`;
- sampled owner declarations:
  `CochainComplex.IsMPseudoCoherentRelativeTo`,
  `ModuleCat.IsMPseudoCoherentRelativeTo`,
  `DerivedCategory.IsMPseudoCoherentRelativeTo`,
  `boundedAbove_isMPseudoCoherent_of_homology`;
- best owner abstraction: the canonical owner for the derived notion is
  `DerivedCategory.IsMPseudoCoherentRelativeTo`, with the ambient algebra inferred strictly from
  the derived object;
- primitive vs. derived:
  primitive data are the relative pseudo-coherence predicates from Definition `15.82.4` together
  with the derived-category owner `DerivedCategory.IsMPseudoCoherentRelativeTo` introduced here;
  derived API is the bounded-above homology criterion proved here by applying the absolute lemma
  presentationwise after restriction of scalars;
- source/core/bridge triage:
  `source-facing`: the bounded-above homology criteria from Lemma `15.82.10`;
  `core/canonical`: the existing relative pseudo-coherence owners `IsMPseudoCoherentRelativeTo`
    and `IsPseudoCoherentRelativeTo`;
  `bridge/view`: passage to each surjective polynomial presentation and application of
    `boundedAbove_isMPseudoCoherent_of_homology`.
- layer: this file stays source-facing and reuses the existing canonical owners instead of keeping
  a parallel `...RelativeToBase` vocabulary.
-/

-- Proof sketch: fix a surjective polynomial presentation `α : R[x₁, ..., xₙ] → A`. The
-- cohomology modules of the restricted complex are exactly the cohomology modules of `K` viewed as
-- modules over `R[x₁, ..., xₙ]`, so the hypothesis gives the `(m - i)`-pseudo-coherence needed to
-- apply Lemma `15.65.10` over the polynomial ring.
/-- Lemma 15.82.10 (1): if a bounded-above derived `A`-complex has cohomology modules that are
`(m - i)`-pseudo-coherent relative to `R` in every degree, then the complex is `m`-pseudo-coherent
relative to `R`. -/
theorem boundedAbove_isMPseudoCoherentRelativeTo_of_homology
    (K : DModAMinus) (m : ℤ)
    (hH :
      ∀ i : ℤ,
        ((H i).obj K.obj).IsMPseudoCoherentRelativeTo R (m - i)) :
    K.obj.IsMPseudoCoherentRelativeTo R m := sorry

-- Proof sketch: for each surjective polynomial presentation of `A` over `R`, the restricted
-- cohomology modules are pseudo-coherent over that presentation ring by hypothesis. Apply the
-- pseudo-coherent variant of Lemma `15.65.10` presentationwise.
/-- Lemma 15.82.10 (2): if every cohomology module of a bounded-above derived `A`-complex is
pseudo-coherent relative to `R`, then the complex itself is pseudo-coherent relative to `R`. -/
theorem boundedAbove_isPseudoCoherentRelativeTo_of_homology
    (K : DModAMinus)
    (hH :
      ∀ i : ℤ,
        ((H i).obj K.obj).IsPseudoCoherentRelativeTo R) :
    K.obj.IsPseudoCoherentRelativeTo R := by
  intro m
  exact boundedAbove_isMPseudoCoherentRelativeTo_of_homology K m fun i ↦ hH i (m - i)

end

end CategoryTheory

/-! ### Lemma_15_82_11 (from Chap15) -/
noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]
variable (f : R) [Algebra R A] [Algebra (Localization.Away f) A]
variable [IsScalarTower R (Localization.Away f) A]
variable [Algebra.FiniteType (Localization.Away f) A]

local notation "DModA" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.82.11:
- primary domain: relative pseudo-coherence in `D(A)` under localization of the target algebra;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherentRelativeTo`,
  `DerivedCategory.IsPseudoCoherentRelativeTo`,
  `derivedTensorWithAlgebra_isMPseudoCoherentRelativeTo_of_isPseudoCoherentRingMap`,
  `derivedTensorWithAlgebra_isPseudoCoherentRelativeTo_of_torIndependent`;
- best owner abstraction: the chapter owner is the derived-category predicate
  `DerivedCategory.IsMPseudoCoherentRelativeTo` / `IsPseudoCoherentRelativeTo`, with the ambient
  finite-type algebra inferred from the derived object;
- primitive vs. derived:
  primitive data are the localized derived object `K ⊗[A]^L[Localization.Away g]` and the
  finite-type descent from `R_f → A` to `R → A`;
  derived API is the relative pseudo-coherence statement for that localized object;
- source/core/bridge triage:
  `source-facing`: Lemma `15.82.11` itself;
  `core/canonical`: the derived-category relative pseudo-coherence owners;
  `bridge/view`: the finite-type descent `R_f → A` to `R → A`, after which the localized target
    uses the canonical finite-type localization instance.
- layer: source-facing statement using the canonical owner, with the localized target handled by
  the canonical localization API rather than a parallel local finite-type bridge.
-/

include f in
private theorem finiteType_base_over_base : Algebra.FiniteType R A :=
  Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType R (Localization.Away f))
    (inferInstance : Algebra.FiniteType (Localization.Away f) A)

-- Proof sketch: first replace each surjective polynomial presentation over `Localization.Away f`
-- by one over `R` with one extra variable inverting `f`, which shows `K` is already
-- `m`-pseudo-coherent relative to `R`. Then apply derived scalar extension along `A → A_g`, and
-- use that `A_g` is finite type over `R`.
/-- Lemma 15.82.11: if `R_f → A` is finite type and a derived `A`-complex `K` is
`m`-pseudo-coherent relative to `Localization.Away f`, then its localization
`K ⊗_A A_g` is `m`-pseudo-coherent relative to `R`. -/
theorem isMPseudoCoherentRelativeTo_localizationAway_from_localizedBase
    (g : A) (K : DModA) (m : ℤ)
    (hK : K.IsMPseudoCoherentRelativeTo (Localization.Away f) m) :
    by
      letI : Algebra.FiniteType R (Localization.Away g) :=
        Algebra.FiniteType.trans
          (finiteType_base_over_base f)
          (inferInstance : Algebra.FiniteType A (Localization.Away g))
      exact (K ⊗[A]^L[Localization.Away g]).IsMPseudoCoherentRelativeTo R m := sorry

-- Proof sketch: pseudo-coherence is relative `m`-pseudo-coherence for all integers `m`, so apply
-- the preceding theorem to each degree bound after unfolding the hypothesis.
/-- Localization away from `g` carries pseudo-coherent derived `A`-complexes relative to
`Localization.Away f` to pseudo-coherent complexes relative to `R`. -/
theorem isPseudoCoherentRelativeTo_localizationAway_from_localizedBase
    (g : A) (K : DModA)
    (hK : K.IsPseudoCoherentRelativeTo (Localization.Away f)) :
    by
      letI : Algebra.FiniteType R (Localization.Away g) :=
        Algebra.FiniteType.trans
          (finiteType_base_over_base f)
          (inferInstance : Algebra.FiniteType A (Localization.Away g))
      exact (K ⊗[A]^L[Localization.Away g]).IsPseudoCoherentRelativeTo R := sorry

end

end CategoryTheory

/-! ### Lemma_15_82_12 (from Chap15) -/
noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace CategoryTheory

section

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']
variable [Algebra.FiniteType R A]

local notation "Aprime" => A ⊗[R] R'
local notation "DModA" => DerivedCategory (ModuleCat A)

/-- The base-changed algebra `A ⊗[R] R'` is finite type over the new base ring `R'`. -/
local instance instFiniteTypeAprime : Algebra.FiniteType R' Aprime :=
  Algebra.FiniteType.equiv
    (inferInstance : Algebra.FiniteType R' (R' ⊗[R] A))
    (Algebra.TensorProduct.commRight R R' A)

-- Proof sketch: for each surjective polynomial presentation `P → A`, base change to the
-- surjective presentation `P ⊗[R] R' → A ⊗[R] R'`, use Lemma `15.61.2` to identify the derived
-- base change of the restricted complex with restriction of the base-changed complex to
-- `P ⊗[R] R'`, then apply Lemma `15.65.12` over the polynomial ring over `R'`.
/-- Lemma 15.82.12 (1): if `K^•` is `m`-pseudo-coherent relative to `R` and `A` and `R'` are Tor
independent over `R`, then the derived base change
`K^• \otimes_A^{\mathbf L} (A ⊗[R] R')` is `m`-pseudo-coherent relative to `R'`. -/
theorem derivedTensorWithAlgebra_isMPseudoCoherentRelativeTo_of_torIndependent
    (K : DModA) (m : ℤ) (hTor : IsTorIndependent R A R')
    (hK : K.IsMPseudoCoherentRelativeTo R m) :
    (K ⊗[A]^L[Aprime]).IsMPseudoCoherentRelativeTo R' m :=
    sorry

-- Proof sketch: apply part `(1)` presentationwise for every integer `m`, or equivalently replace
-- Lemma `15.65.12` by its pseudo-coherent variant after the same Tor-independent base-change
-- comparison from Lemma `15.61.2`.
/-- Lemma 15.82.12 (2): if `K^•` is pseudo-coherent relative to `R` and `A` and `R'` are Tor
independent over `R`, then the derived base change
`K^• \otimes_A^{\mathbf L} (A ⊗[R] R')` is pseudo-coherent relative to `R'`. -/
theorem derivedTensorWithAlgebra_isPseudoCoherentRelativeTo_of_torIndependent
    (K : DModA) (hTor : IsTorIndependent R A R')
    (hK : K.IsPseudoCoherentRelativeTo R) :
    (K ⊗[A]^L[Aprime]).IsPseudoCoherentRelativeTo R' :=
    sorry

end

end CategoryTheory

/-! ### Lemma_15_82_13 (from Chap15) -/
noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R A B : Type u}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable [Algebra.FiniteType R A]
variable [(algebraMap A B).IsPseudoCoherentRingMap]

local notation "DModA" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.82.13:
- primary domain: relative pseudo-coherence in derived categories under derived scalar extension
  along a pseudo-coherent ring map;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherentRelativeTo`,
  `DerivedCategory.IsPseudoCoherentRelativeTo`,
  `derivedTensorWithAlgebra`,
  `RingHom.IsPseudoCoherentRingMap`;
- best owner abstraction: this file is `source-facing`, while the canonical owners are the
  relative pseudo-coherence predicates on `DerivedCategory (ModuleCat A)` together with the
  derived scalar-extension owner `derivedTensorWithAlgebra`;
- primitive vs. derived:
  primitive data are the finite-type hypothesis on `R → A` and the pseudo-coherent ring-map
  hypothesis on `A → B`;
  the finite-type structure on `R → B` is derived by transitivity and should not remain primitive
  public data.
-/

-- Proof sketch: fix a surjective polynomial presentation of `A` over `R`, adjoin finitely many
-- variables to obtain a polynomial presentation of `B`, and use the pseudo-coherent ring-map
-- hypothesis to choose a finite free resolution of `B` over that intermediate polynomial algebra.
-- Rewrite derived tensor product with `B` as the total complex of tensoring `K` with this
-- resolution, then combine Lemma `15.82.12` with the distinguished-triangle closure of relative
-- `m`-pseudo-coherence from Lemma `15.82.6`.
/-- Lemma 15.82.13 (1): if `R → A` is finite type, `A → B` is a pseudo-coherent ring map, and a
derived `A`-complex `K^•` is `m`-pseudo-coherent relative to `R`, then
`K^• \otimes_A^{\mathbf L} B` is `m`-pseudo-coherent relative to `R`. -/
theorem derivedTensorWithAlgebra_isMPseudoCoherentRelativeTo_of_isPseudoCoherentRingMap
    (K : DModA) (m : ℤ) (hK : K.IsMPseudoCoherentRelativeTo R m) :
    by
      letI : Algebra.FiniteType R B :=
        Algebra.FiniteType.trans
          (inferInstance : Algebra.FiniteType R A)
          (inferInstance : Algebra.FiniteType A B)
      exact (K ⊗[A]^L[B]).IsMPseudoCoherentRelativeTo R m := sorry

-- Proof sketch: unfold relative pseudo-coherence as relative `m`-pseudo-coherence for every
-- integer `m`, and apply part `(1)` to each bound.
/-- Lemma 15.82.13 (2): if `R → A` is finite type, `A → B` is a pseudo-coherent ring map, and a
derived `A`-complex `K^•` is pseudo-coherent relative to `R`, then
`K^• \otimes_A^{\mathbf L} B` is pseudo-coherent relative to `R`. -/
theorem derivedTensorWithAlgebra_isPseudoCoherentRelativeTo_of_isPseudoCoherentRingMap
    (K : DModA) (hK : K.IsPseudoCoherentRelativeTo R) :
    by
      letI : Algebra.FiniteType R B :=
        Algebra.FiniteType.trans
          (inferInstance : Algebra.FiniteType R A)
          (inferInstance : Algebra.FiniteType A B)
      exact (K ⊗[A]^L[B]).IsPseudoCoherentRelativeTo R := by
        intro m
        exact
          derivedTensorWithAlgebra_isMPseudoCoherentRelativeTo_of_isPseudoCoherentRingMap
            K m (hK m)

end

end CategoryTheory

/-! ### Lemma_15_82_14 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R A B : Type u}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable [Algebra.FiniteType R A]
variable [(algebraMap A B).IsPseudoCoherentRingMap]

/- Domain-style sampling for Lemma 15.82.14:
- primary domain: relative pseudo-coherence for modules under ordinary scalar extension along a
  flat pseudo-coherent ring map;
- sampled owner declarations:
  `ModuleCat.IsMPseudoCoherentRelativeTo`,
  `ModuleCat.IsPseudoCoherentRelativeTo`,
  `derivedTensorWithAlgebra_isMPseudoCoherentRelativeTo_of_isPseudoCoherentRingMap`,
  `RingHom.IsPseudoCoherentRingMap`;
- best owner abstraction: the core/canonical owner is the derived scalar-extension theorem
  `derivedTensorWithAlgebra_isMPseudoCoherentRelativeTo_of_isPseudoCoherentRingMap`; this file is
  only the module-level `bridge/view` specialization obtained from a degree-zero complex and the
  flat identification of derived with ordinary scalar extension;
- primitive vs. derived:
  primitive data are the finite-type hypothesis on `R → A`, the pseudo-coherent ring-map owner on
  `A → B`, and the flatness hypothesis on `A → B`;
  the finite-type structure on `R → B` is derived canonically and should not remain ambient public
  data in this bridge file.
-/

-- Proof sketch: regard `M` as the degree-zero object of `D(A)`, apply
-- `derivedTensorWithAlgebra_isMPseudoCoherentRelativeTo_of_isPseudoCoherentRingMap`, and use
-- flatness of `A → B` to identify the derived tensor product with ordinary extension of scalars on
-- a module concentrated in degree `0`.
/-- Lemma 15.82.14: if `R → A → B` are finite type ring maps, `A → B` is flat, and `A → B` is
pseudo-coherent, then relative `m`-pseudo-coherence over `R` is preserved by extension of scalars
from `A` to `B`. -/
theorem isMPseudoCoherentRelativeTo_extendScalars
    (hflat : (algebraMap A B).Flat) (M : ModuleCat A) (m : ℤ)
    (hM : M.IsMPseudoCoherentRelativeTo R m) :
    by
      letI : Algebra.FiniteType R B :=
        Algebra.FiniteType.trans
          (inferInstance : Algebra.FiniteType R A)
          (inferInstance : Algebra.FiniteType A B)
      exact
        ((ModuleCat.extendScalars (algebraMap A B)).obj M).IsMPseudoCoherentRelativeTo R m := sorry

-- Proof sketch: unfold relative pseudo-coherence as relative `m`-pseudo-coherence for every
-- integer `m`, and apply the previous theorem to each bound.
/-- Ordinary scalar extension along a flat pseudo-coherent finite type ring map preserves relative
pseudo-coherent modules over the base ring. -/
theorem isPseudoCoherentRelativeTo_extendScalars
    (hflat : (algebraMap A B).Flat) (M : ModuleCat A)
    (hM : M.IsPseudoCoherentRelativeTo R) :
    by
      letI : Algebra.FiniteType R B :=
        Algebra.FiniteType.trans
          (inferInstance : Algebra.FiniteType R A)
          (inferInstance : Algebra.FiniteType A B)
      exact
        ((ModuleCat.extendScalars (algebraMap A B)).obj M).IsPseudoCoherentRelativeTo R := sorry

end

end CategoryTheory

/-! ### Lemma_15_82_15 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable [Algebra.FiniteType R A] [Algebra.FiniteType A B]

local notation "DModB" => DerivedCategory (ModuleCat B)

/- Domain-style sampling for Lemma 15.82.15:
- primary domain: relative pseudo-coherence in derived categories over a tower `R → A → B` of
  finite type algebras;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherentRelativeTo`,
  `DerivedCategory.IsPseudoCoherentRelativeTo`,
  `Module.IsPseudoCoherentRelativeTo`,
  `boundedAbove_isMPseudoCoherentRelativeTo_of_homology`,
  `derivedTensorWithAlgebra_isMPseudoCoherentRelativeTo_of_isPseudoCoherentRingMap`;
- best owner abstraction: the chapter owner predicates
  `DerivedCategory.IsMPseudoCoherentRelativeTo R K m` and
  `DerivedCategory.IsPseudoCoherentRelativeTo R K`, together with the thin module bridge
  `Module.IsPseudoCoherentRelativeTo R A A` for the intermediate algebra;
- primitive vs. derived:
  primitive data are the finite-type hypotheses on `R → A` and `A → B` together with the
  pseudo-coherence of `A` relative to `R`; the finite-type structure on `R → B` is derived by the
  canonical transitivity instance and should not remain on the public theorem surface;
- source/core/bridge triage:
  `source-facing`: the comparison lemmas below for relative pseudo-coherence across the
    intermediate algebra `A`;
  `core/canonical`: the owner predicates `DerivedCategory.IsMPseudoCoherentRelativeTo` and
    `DerivedCategory.IsPseudoCoherentRelativeTo`;
  `bridge/view`: the internal passage from the tower hypotheses to the induced finite-type
    structure on `R → B`.
- layer: this refinement stays source-facing and keeps the induced `R → B` finite-type witness
  internal, without adding a public wrapper.
-/

-- Proof sketch: expand relative pseudo-coherence over `A` using a surjective polynomial
-- presentation `A[y₁, ..., yₙ] → B`. Choose a surjective polynomial presentation `R[x₁, ..., xₘ] → A`.
-- By the hypothesis on `A`, the algebra `A[y₁, ..., yₙ]` is pseudo-coherent over the polynomial
-- ring `R[x₁, ..., xₘ, y₁, ..., yₙ]` via flat base change, using Lemma `15.65.13`. Then apply
-- Lemma `15.65.11` to compare `m`-pseudo-coherence over these two presentation rings, and quantify
-- over all presentations.
/-- Lemma 15.82.15 (1): if `A → B` is a finite type map of finite type `R`-algebras and `A`,
viewed as an `A`-module, is pseudo-coherent relative to `R`, then a derived `B`-complex is
`m`-pseudo-coherent relative to `A` if and only if it is `m`-pseudo-coherent relative to `R`. -/
theorem isMPseudoCoherentRelativeTo_iff_of_intermediate_isPseudoCoherentRelativeTo
    (K : DModB) (m : ℤ)
    (hA : (ModuleCat.of A A).IsPseudoCoherentRelativeTo R) :
    by
      letI : Algebra.FiniteType R B :=
        Algebra.FiniteType.trans
          (inferInstance : Algebra.FiniteType R A)
          (inferInstance : Algebra.FiniteType A B)
      exact K.IsMPseudoCoherentRelativeTo A m ↔ K.IsMPseudoCoherentRelativeTo R m := sorry

-- Proof sketch: apply part `(1)` for every integer `m`. Pseudo-coherence is equivalent to
-- `m`-pseudo-coherence for all `m`, so the relative pseudo-coherent statement follows by
-- unfolding the definition on both sides.
/-- Lemma 15.82.15 (2): under the same hypotheses, a derived `B`-complex is pseudo-coherent
relative to `A` if and only if it is pseudo-coherent relative to `R`. -/
theorem isPseudoCoherentRelativeTo_iff_of_intermediate_isPseudoCoherentRelativeTo
    (K : DModB)
    (hA : (ModuleCat.of A A).IsPseudoCoherentRelativeTo R) :
    by
      letI : Algebra.FiniteType R B :=
        Algebra.FiniteType.trans
          (inferInstance : Algebra.FiniteType R A)
          (inferInstance : Algebra.FiniteType A B)
      exact K.IsPseudoCoherentRelativeTo A ↔ K.IsPseudoCoherentRelativeTo R := sorry

end

end CategoryTheory

/-! ### Lemma_15_82_16 (from Chap15) -/
noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable [Algebra.FiniteType R A]
variable {ι : Type*} [Finite ι]

local notation "DModA" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.82.16:
- primary domain: relative pseudo-coherence in `D(A)` and its locality on a finite principal-open
  cover of `Spec A`;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherentRelativeTo`,
  `DerivedCategory.IsPseudoCoherentRelativeTo`,
  `isMPseudoCoherent_iff_localizationAway_unitIdeal`,
  `derivedTensorWithAlgebra_isMPseudoCoherentRelativeTo_of_isPseudoCoherentRingMap`;
- best owner abstraction: this item is `source-facing`, while the core/canonical owners are the
  relative pseudo-coherence predicates `K.IsMPseudoCoherentRelativeTo R m` and
  `K.IsPseudoCoherentRelativeTo R` on derived `A`-complexes;
- primitive vs. derived:
  primitive data are the finite family `f : ι → A`, the unit-ideal hypothesis, and the localized
  derived objects `K ⊗[A]^L[Localization.Away (f i)]`;
  derived API is the relative pseudo-coherence conclusion on `K`, so the file should not keep a
  parallel coordinate-level `Fin r` interface or explicit functor application as the public
  surface;
- source/core/bridge triage:
  `source-facing`: the local-global equivalences below;
  `core/canonical`: the owner predicates `IsMPseudoCoherentRelativeTo` and
    `IsPseudoCoherentRelativeTo`;
  `bridge/view`: the localized derived scalar-extension objects
    `K ⊗[A]^L[Localization.Away (f i)]`.
-/

-- Proof sketch: for `←`, restrict the complex along any surjective polynomial presentation
-- `P → A`; the hypotheses identify each localization over `A_{f i}` with the corresponding
-- localization of the restricted `P`-complex, and Lemma `15.65.14` descends `m`-pseudo-coherence
-- from the principal-open cover because the images of the `f i` still generate the unit ideal.
-- For `→`, localize a relative `m`-pseudo-coherent approximation; this is the relative
-- localization statement proved earlier in the chapter.
/-- Lemma 15.82.16 (1): for a finite type ring map `R → A`, a derived `A`-complex `K^•`, an
integer `m`, and finitely many elements `f i : A` generating the unit ideal, `K^•` is
`m`-pseudo-coherent relative to `R` if and only if each principal localization
`K^• \otimes_A^{\mathbf L} A_{f i}` is `m`-pseudo-coherent relative to `R`. -/
theorem isMPseudoCoherentRelativeTo_iff_localizationAway_unitIdeal
    (f : ι → A) (hunit : Ideal.span (Set.range f) = ⊤) (K : DModA) (m : ℤ) :
    (∀ i, (K ⊗[A]^L[Localization.Away (f i)]).IsMPseudoCoherentRelativeTo R m) ↔
      K.IsMPseudoCoherentRelativeTo R m := sorry

-- Proof sketch: combine part `(1)` for every integer `m` with the definitions of relative
-- pseudo-coherence and ordinary pseudo-coherence as `m`-pseudo-coherence in all degrees.
/-- Lemma 15.82.16 (2): under the same hypotheses, `K^•` is pseudo-coherent relative to `R` if
and only if each principal localization `K^• \otimes_A^{\mathbf L} A_{f i}` is pseudo-coherent
relative to `R`. -/
theorem isPseudoCoherentRelativeTo_iff_localizationAway_unitIdeal
    (f : ι → A) (hunit : Ideal.span (Set.range f) = ⊤) (K : DModA) :
    (∀ i, (K ⊗[A]^L[Localization.Away (f i)]).IsPseudoCoherentRelativeTo R) ↔
      K.IsPseudoCoherentRelativeTo R := by
  constructor
  · intro hK m
    exact (isMPseudoCoherentRelativeTo_iff_localizationAway_unitIdeal f hunit K m).mp
      (fun i ↦ hK i m)
  · intro hK i m
    exact ((isMPseudoCoherentRelativeTo_iff_localizationAway_unitIdeal f hunit K m).mpr
      (hK m)) i

end

end CategoryTheory
