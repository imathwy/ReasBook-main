import Mathlib
import StacksProject_2024.Chap29.Lemma_29_51_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open PrimeSpectrum
open scoped AlgebraicGeometry PrimeSpectrum

noncomputable section

namespace AlgebraicGeometry

/- Semantic recall: `lean_leansearch` surfaced the canonical morphism owners
`QuasiCompact`, `LocallyOfFiniteType`, `QuasiSeparated`, and the affine-restriction API
`f ∣_ U`. Local Chapter 29 precedent from Lemma 29.51.1 supplies
`genericPointsOfIrreducibleComponents` and the exact affine-neighborhood conditions whose
quasi-separated hypothesis this example shows is necessary. The source tag evidence agrees on
`03HY`. -/

/-- The product ring `A = \prod_{n \in \mathbb N} \mathbf F_2` used in
Example 29.51.2. -/
@[stacks 03HY]
abbrev example29512Ring :=
  ℕ → ZMod 2

/-- The affine scheme `X = \operatorname{Spec}(A)` used in Example 29.51.2. -/
@[stacks 03HY]
abbrev example29512Scheme : Scheme :=
  Spec (CommRingCat.of example29512Ring)

/-- The projection map `A -> \mathbf F_2` onto the `n`-th factor. -/
@[stacks 03HY]
abbrev example29512Projection (n : ℕ) : example29512Ring →+* ZMod 2 :=
  Pi.evalRingHom (fun _ : ℕ ↦ ZMod 2) n

/-- The point of `\operatorname{Spec}(A)` defined by the `n`-th projection
`A -> \mathbf F_2`. -/
@[stacks 03HY]
def example29512ProjectionPoint (n : ℕ) : PrimeSpectrum example29512Ring :=
  PrimeSpectrum.comap (example29512Projection n) (IsLocalRing.closedPoint (ZMod 2))

/-- Example 29.51.2 (1): every element of
`A = \prod_{n \in \mathbb N} \mathbf F_2` is idempotent. -/
@[stacks 03HY]
theorem example29512Ring_element_idempotent (a : example29512Ring) :
    a * a = a := sorry

/-- Example 29.51.2 (2): every prime ideal of
`A = \prod_{n \in \mathbb N} \mathbf F_2` is maximal. -/
@[stacks 03HY]
theorem example29512Ring_primeIdeal_isMaximal (p : PrimeSpectrum example29512Ring) :
    p.asIdeal.IsMaximal := sorry

/-- Example 29.51.2 (3): the residue field at every prime of
`A = \prod_{n \in \mathbb N} \mathbf F_2` is `\mathbf F_2`. -/
@[stacks 03HY]
theorem example29512Ring_residueField_equiv_zmod_two
    (p : PrimeSpectrum example29512Ring) :
    Nonempty (p.asIdeal.ResidueField ≃+* ZMod 2) := sorry

/-- Example 29.51.2 (4): the topology on
`X = \operatorname{Spec}(A)` is totally disconnected. -/
@[stacks 03HY]
theorem example29512Scheme_totallyDisconnected :
    TotallyDisconnectedSpace example29512Scheme := sorry

/-- Example 29.51.2 (5): the affine scheme
`X = \operatorname{Spec}(A)` is quasi-compact. -/
@[stacks 03HY]
theorem example29512Scheme_quasiCompact :
    CompactSpace example29512Scheme := sorry

/-- Example 29.51.2 (6): the projection maps `A -> \mathbf F_2` define open points of
`\operatorname{Spec}(A)`. -/
@[stacks 03HY]
theorem example29512ProjectionPoint_isOpen (n : ℕ) :
    IsOpen ({example29512ProjectionPoint n} : Set (PrimeSpectrum example29512Ring)) := sorry

/-- Example 29.51.2 (7): since `X = \operatorname{Spec}(A)` is quasi-compact, not every point of
`X` is open; in particular there is a closed point which is not open. -/
@[stacks 03HY]
theorem exists_example29512_closedPoint_not_open :
    ∃ x : example29512Scheme,
      IsClosed ({x} : Set example29512Scheme) ∧
        ¬ IsOpen ({x} : Set example29512Scheme) := sorry

/-- Auxiliary neighborhood datum for the finite restriction obstruction in
Example 29.51.2. -/
@[stacks 03HY]
structure Example29512FiniteFiberNeighborhood
    (x : example29512Scheme) {Y : Scheme} (f : Y ⟶ example29512Scheme)
    (U : Y.Opens) (V : example29512Scheme.Opens) : Prop where
  sourceAffine : IsAffineOpen U
  targetAffine : IsAffineOpen V
  memTarget : x ∈ V
  lePreimage : U ≤ f ⁻¹ᵁ V
  containsFiber : ∀ y : Y, f.base y = x → y ∈ U
  finiteRestriction : IsFinite (f.resLE V U lePreimage)

/-- Auxiliary affine-neighborhood datum for the finite restriction obstruction in
Example 29.51.2. -/
@[stacks 03HY]
structure Example29512FiniteNeighborhood
    (x : example29512Scheme) {Y : Scheme} (f : Y ⟶ example29512Scheme)
    (V : example29512Scheme.Opens) : Prop where
  targetAffine : IsAffineOpen V
  memTarget : x ∈ V
  finiteRestriction : IsFinite (f ∣_ V)

/-- Source-facing predicate collecting the doubled-point counterexample properties from
Example 29.51.2. -/
@[stacks 03HY]
structure Example29512DoubledPointCounterexample
    (x : example29512Scheme) (Y : Scheme) (f : Y ⟶ example29512Scheme) : Prop where
  closedPoint : IsClosed ({x} : Set example29512Scheme)
  notOpenPoint : ¬ IsOpen ({x} : Set example29512Scheme)
  genericComponent : x ∈ genericPointsOfIrreducibleComponents example29512Scheme
  quasiCompact : QuasiCompact f
  locallyOfFiniteType : LocallyOfFiniteType f
  finiteFibers : ∀ s : example29512Scheme, ({y : Y | f.base y = s} : Set Y).Finite
  notQuasiSeparated : ¬ QuasiSeparated f
  preimageNonaffine :
    ∀ U : example29512Scheme.Opens, x ∈ U → ¬ IsAffine (f ⁻¹ᵁ U).toScheme
  noFiberAffineFiniteRestriction :
    ¬ ∃ (U : Y.Opens) (V : example29512Scheme.Opens),
      Example29512FiniteFiberNeighborhood x f U V
  noAffineFiniteNeighborhood :
    ¬ ∃ V : example29512Scheme.Opens, Example29512FiniteNeighborhood x f V

/-- Example 29.51.2 (8): doubling a closed non-open point `x` of
`X = \operatorname{Spec}(\prod_n \mathbf F_2)` gives a morphism `f : Y -> X` which is
quasi-compact, locally of finite type, finite-fibered, non-quasi-separated, with the affine
neighborhood conclusions `(3)` and `(4)` of Lemma 29.51.1 failing. -/
@[stacks 03HY]
theorem exists_example29512_doubledPoint_counterexample :
    ∃ (x : example29512Scheme) (Y : Scheme) (f : Y ⟶ example29512Scheme),
      Example29512DoubledPointCounterexample x Y f := sorry

end AlgebraicGeometry
