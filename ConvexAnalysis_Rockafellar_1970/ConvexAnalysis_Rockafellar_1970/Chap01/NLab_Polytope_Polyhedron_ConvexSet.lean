import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Homeomorph.Defs

/-!
# nLab-facing convex-set, polytope, and polyhedron notions

This file records lightweight owner predicates matching the terminology used on the nLab pages
`convex set`, `polytope`, and `polyhedron`.

The important distinction is terminological:
* nLab's `convex space` page gives an "unbiased" version using `n`-ary convex-linear
  combinations: weights `p_i` in an ordered scalar semiring with `∑ i, p_i = 1` and points
  `x_i`, sent to
  `∑ i, p_i x_i`. The first owner below records exactly that finite-weighted-operation surface.
* nLab's `convex set` page describes a subset of a real affine space closed under line segments.
  The owner below is therefore stated on an affine space `P` modelled on a real vector space `V`,
  and uses affine line segments rather than taking `Convex` as primitive.
* nLab's `polytope` page treats polytopes as the polygon/polyhedron sequence in arbitrary
  dimension. The convex-analysis owner below uses the standard convex-geometry specialization:
  the convex hull of finitely many points.
* nLab's `polyhedron` page is explicitly about the algebraic-topology meaning: a topological
  space homeomorphic to the geometric realization of a finite simplicial complex. This is not the
  same notion as Rockafellar's polyhedral convex set, which is a finite intersection of closed
  half-spaces.

References:
* https://ncatlab.org/nlab/show/convex+space
* https://ncatlab.org/nlab/show/convex+set
* https://ncatlab.org/nlab/show/polytope
* https://ncatlab.org/nlab/show/polyhedron
-/

universe u v w

namespace NLab

section UnbiasedConvexSpace

/-- nLab's unbiased finite convex-weight data: a finite list/family of coefficients
`p_i` whose sum is `1`.

The finite type `ι` is the Lean form of the list index set `{1, ..., n}` in the nLab formula. -/
structure ConvexWeights (R : Type u) (ι : Type v) [Semiring R] [PartialOrder R] [Fintype ι]
    where
  /-- The coefficient `p_i`. -/
  weight : ι → R
  /-- Each coefficient is nonnegative, hence lies in `[0,1]` once the total sum is `1`. -/
  nonneg : ∀ i : ι, 0 ≤ weight i
  /-- The coefficients sum to `1`. -/
  sum_eq_one : ∑ i, weight i = 1

namespace ConvexWeights

variable {R : Type u} [Semiring R] [PartialOrder R]

/-- Reindex a finite family of convex weights along an equivalence of finite index types. -/
def reindex {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    (p : ConvexWeights R κ) (e : ι ≃ κ) : ConvexWeights R ι where
  weight i := p.weight (e i)
  nonneg i := p.nonneg (e i)
  sum_eq_one := by
    classical
    exact (Fintype.sum_equiv e (fun i ↦ p.weight (e i)) p.weight (fun _ ↦ rfl)).trans
      p.sum_eq_one

end ConvexWeights

/-- Finite distributions with coefficients in `R`: finitely supported functions
`X → R`, pointwise nonnegative, with total mass `1`.

This is the concrete carrier of the finite distribution/free convex-space monad referenced by
nLab. -/
structure FiniteDistribution (R : Type u) (X : Type v) [Semiring R] [PartialOrder R] where
  /-- The finitely supported mass function. -/
  mass : X →₀ R
  /-- All masses are nonnegative. -/
  nonneg : ∀ x : X, 0 ≤ mass x
  /-- The total mass is `1`. -/
  total_mass : mass.sum (fun _ r ↦ r) = 1

namespace FiniteDistribution

variable {R : Type u} {X : Type v} [Semiring R] [PartialOrder R]

/-- The Dirac finite distribution at a point. -/
noncomputable def pure [ZeroLEOneClass R] (x : X) : FiniteDistribution R X where
  mass := Finsupp.single x 1
  nonneg y := by
    by_cases h : y = x
    · subst h
      simp
    · rw [Finsupp.single_eq_of_ne h]
  total_mass := by
    simp

/-- A finite distribution on the finite index type determined by convex weights. -/
noncomputable def ofWeightsIndex {ι : Type w} [Fintype ι] [Finite ι]
    (p : ConvexWeights R ι) : FiniteDistribution R ι where
  mass := Finsupp.equivFunOnFinite.symm p.weight
  nonneg i := by
    change 0 ≤ p.weight i
    exact p.nonneg i
  total_mass := by
    rw [Finsupp.sum_fintype]
    · exact p.sum_eq_one
    · simp

/-- Push a finite distribution forward along a map. This is the functorial action of the
finite-distribution monad. -/
noncomputable def map {Y : Type w} [AddLeftMono R] (f : X → Y)
    (d : FiniteDistribution R X) : FiniteDistribution R Y where
  mass := Finsupp.mapDomain f d.mass
  nonneg y := by
    classical
    rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
    apply Finset.sum_nonneg
    intro x _hx
    by_cases h : f x = y
    · simp [h, d.nonneg x]
    · simp [h]
  total_mass := by
    rw [Finsupp.sum_mapDomain_index]
    · exact d.total_mass
    · simp
    · intro b a c
      rfl

/-- The formal finite convex combination `∑ i, p_i x_i` as an element of the free convex space
on `X`: first form the distribution on the finite index set, then push it forward along the
chosen points. -/
noncomputable def ofWeights {ι : Type w} [Fintype ι] [Finite ι] [AddLeftMono R]
    (p : ConvexWeights R ι) (x : ι → X) : FiniteDistribution R X :=
  map x (ofWeightsIndex p)

end FiniteDistribution

/-- nLab's monadic abstraction layer for convex spaces.

The `convex space` page says equivalently that convex spaces are algebras of a finitary monad:
the monad assigning to a set the free convex space on that set. This owner records that layer
directly. The formal expression `∑ i, p_i x_i` is not another arbitrary operation here: it is the
standard pushforward `FiniteDistribution.ofWeights p x`. `FiniteDistribution.pure` and `bind` are
the unit and Kleisli extension of the monad. -/
class FinitaryConvexCombinationMonad (R : Type u)
    [Semiring R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
    extends Monad (fun X : Type (max u v) ↦ FiniteDistribution R X),
      LawfulMonad (fun X : Type (max u v) ↦ FiniteDistribution R X) where
  /-- The monad unit is the Dirac finite distribution. -/
  pure_eq :
    ∀ {X : Type (max u v)} (x : X),
      Pure.pure (f := fun Z : Type (max u v) ↦ FiniteDistribution R Z) x =
        FiniteDistribution.pure x
  /-- Kleisli substitution distributes across a standard finite convex combination. This is the
  monadic form of substituting formal convex combinations for the variables in `∑ i, p_i x_i`. -/
  bind_ofWeights :
    ∀ {X Y : Type (max u v)} {ι : Type v} [Fintype ι] [Finite ι]
      (p : ConvexWeights R ι) (x : ι → X) (f : X → FiniteDistribution R Y),
      Bind.bind (m := fun Z : Type (max u v) ↦ FiniteDistribution R Z)
        (FiniteDistribution.ofWeights p x) f =
        Bind.bind (m := fun Z : Type (max u v) ↦ FiniteDistribution R Z)
          (FiniteDistribution.ofWeights p (fun i ↦ f (x i)))
          (fun y : FiniteDistribution R Y ↦ y)
  /-- Formal nested standard convex combinations flatten by multiplying weights. This is the free
  convex-space monad multiplication written in the finite-index presentation. -/
  ofWeights_assoc :
    ∀ {X : Type (max u v)} {ι : Type v} {κ : ι → Type v} [Fintype ι] [Finite ι]
      [Fintype (Sigma κ)] [Finite (Sigma κ)] [∀ i : ι, Fintype (κ i)]
      [∀ i : ι, Finite (κ i)]
      (p : ConvexWeights R ι) (q : ∀ i : ι, ConvexWeights R (κ i))
      (x : ∀ i : ι, κ i → X) (flat : ConvexWeights R (Sigma κ)),
      (∀ ij : Sigma κ, flat.weight ij = p.weight ij.1 * (q ij.1).weight ij.2) →
        Bind.bind (m := fun Z : Type (max u v) ↦ FiniteDistribution R Z)
          (FiniteDistribution.ofWeights p (fun i ↦ FiniteDistribution.ofWeights (q i) (x i)))
          (fun y : FiniteDistribution R X ↦ y) =
          FiniteDistribution.ofWeights flat (fun ij ↦ x ij.1 ij.2)

/-- Algebra over the finitary convex-combination monad. This is the categorical owner behind the
nLab statement that convex spaces are algebras of a finitary monad. -/
class FinitaryConvexCombinationAlgebra
    (R : Type u) [Semiring R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
    [FinitaryConvexCombinationMonad.{u, v} R] (X : Type (max u v)) where
  /-- Evaluate a formal convex combination in the algebra. -/
  eval : FiniteDistribution R X → X
  /-- The algebra evaluates a monadic generator to itself. -/
  eval_pure :
    ∀ x : X, eval (Pure.pure (f := fun Z : Type (max u v) ↦ FiniteDistribution R Z) x) = x
  /-- Algebra associativity: evaluating after monadic substitution agrees with evaluating the
  outer formal combination after evaluating the inner formal combinations. -/
  eval_bind :
    ∀ (x : FiniteDistribution R (FiniteDistribution R X)),
      eval (Bind.bind (m := fun Z : Type (max u v) ↦ FiniteDistribution R Z) x
        (fun y ↦ Pure.pure (f := fun Z : Type (max u v) ↦ FiniteDistribution R Z) (eval y))) =
        eval (Bind.bind (m := fun Z : Type (max u v) ↦ FiniteDistribution R Z) x
          (fun y : FiniteDistribution R X ↦ y))

namespace FinitaryConvexCombinationAlgebra

variable {R : Type u} [Semiring R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
variable [FinitaryConvexCombinationMonad.{u, v} R] {X : Type (max u v)}
variable [_root_.NLab.FinitaryConvexCombinationAlgebra.{u, v} R X]

/-- The n-ary convex-combination operation induced on an algebra over the finitary
finite-distribution monad. This is the monadic route from nLab's free convex space to the
unbiased operation `c_p(x)`. -/
noncomputable def convexCombination {ι : Type v} [Fintype ι] [Finite ι]
    (p : ConvexWeights R ι) (x : ι → X) : X :=
  _root_.NLab.FinitaryConvexCombinationAlgebra.eval (FiniteDistribution.ofWeights p x)

end FinitaryConvexCombinationAlgebra

/-- nLab's unbiased convex-space operation surface: for every finite nonempty list of weights
`p := (p_i)` with `∑ i, p_i = 1` and every list of points `x := (x_i)`, there is an abstract
convex-linear combination `c_p(x)`.

This records the n-ary, unbiased presentation mentioned on nLab, together with the basic
coherence requirements expected of such operations: reindexing invariance, irrelevance of
zero-weight entries, constant-family idempotence, and associativity by flattening nested finite
convex combinations. Categorically, this is the algebra-level presentation of the finitary
convex-combination monad above. -/
class UnbiasedConvexSpace (R : Type u) (X : Type v) [Semiring R] [PartialOrder R] where
  convexCombination :
    ∀ {ι : Type w} [Fintype ι] [Nonempty ι], ConvexWeights R ι → (ι → X) → X
  convexCombination_reindex :
    ∀ {ι : Type w} {κ : Type w} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
      (e : ι ≃ κ) (p : ConvexWeights R κ) (x : κ → X),
      convexCombination (ConvexWeights.reindex p e) (fun i ↦ x (e i)) =
        convexCombination p x
  convexCombination_congr_zero :
    ∀ {ι : Type w} [Fintype ι] [Nonempty ι] (p : ConvexWeights R ι) {x y : ι → X},
      (∀ i : ι, p.weight i ≠ 0 → x i = y i) →
        convexCombination p x = convexCombination p y
  convexCombination_const :
    ∀ {ι : Type w} [Fintype ι] [Nonempty ι] (p : ConvexWeights R ι) (x : X),
      convexCombination p (fun _ ↦ x) = x
  convexCombination_assoc :
    ∀ {ι : Type w} {κ : ι → Type w} [Fintype ι] [Nonempty ι]
      [Fintype (Sigma κ)] [Nonempty (Sigma κ)]
      [∀ i : ι, Fintype (κ i)] [∀ i : ι, Nonempty (κ i)]
      (p : ConvexWeights R ι) (q : ∀ i : ι, ConvexWeights R (κ i))
      (x : ∀ i : ι, κ i → X) (flat : ConvexWeights R (Sigma κ)),
      (∀ ij : Sigma κ, flat.weight ij = p.weight ij.1 * (q ij.1).weight ij.2) →
        convexCombination p (fun i ↦ convexCombination (q i) (x i)) =
          convexCombination flat (fun ij ↦ x ij.1 ij.2)

/-- Apply the nLab unbiased convex-combination operation. -/
abbrev unbiasedConvexCombination {R : Type u} {X : Type v}
    [Semiring R] [PartialOrder R] [UnbiasedConvexSpace R X]
    {ι : Type w} [Fintype ι] [Nonempty ι] (p : ConvexWeights R ι) (x : ι → X) : X :=
  UnbiasedConvexSpace.convexCombination p x

/-- A subset of an unbiased convex space is closed under all finite convex-linear combinations. -/
def IsClosedUnderUnbiasedConvexCombinations {R : Type u} {X : Type v}
    [Semiring R] [PartialOrder R] [UnbiasedConvexSpace R X]
    (s : Set X) : Prop :=
  ∀ {ι : Type w} [Fintype ι] [Nonempty ι] (p : ConvexWeights R ι) (x : ι → X),
    (∀ i : ι, x i ∈ s) → unbiasedConvexCombination p x ∈ s

section ConcreteRealizations

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {ι : Type v} [Fintype ι]

/-- The concrete vector-space formula from nLab's unbiased paragraph:
`c_p(x) = ∑ i, p_i x_i`. -/
def linearConvexCombination {E : Type w} [AddCommMonoid E] [Module R E]
    (p : ConvexWeights R ι) (x : ι → E) : E :=
  ∑ i, p.weight i • x i

variable [Nonempty ι]

variable {R' : Type u} [Ring R'] [PartialOrder R']

/-- The corresponding affine-space version of the same finite weighted combination, using
mathlib's affine-combination API. The hypothesis `p.sum_eq_one` is stored in `p`, so this is the
affine expression represented by `∑ i, p_i x_i`. -/
noncomputable def affineConvexCombination {V : Type v} {P : Type w}
    [AddCommGroup V] [Module R' V] [AddTorsor V P]
    (p : ConvexWeights R' ι) (x : ι → P) : P :=
  (Finset.univ.affineCombination R' x) p.weight

end ConcreteRealizations

end UnbiasedConvexSpace

section ConvexSet

variable {R : Type u} {V : Type v} {P : Type w}
variable [Ring R] [PartialOrder R] [AddCommGroup V] [Module R V] [AddTorsor V P]

/-- The nLab-style affine combination `t x + (1 - t) y` in an affine space.

In an affine space the expression is represented by the affine map from `y` to `x`, evaluated at
`t`; in a vector space this is `(1 - t) • y + t • x`, the same point as
`t • x + (1 - t) • y`. -/
def scalarAffineCombination (x y : P) (t : R) : P :=
  AffineMap.lineMap y x t

/-- The straight line segment connecting two points in an affine space, as used in nLab's
definition of convex set. -/
def scalarAffineSegment (x y : P) : Set P :=
  {z : P | ∃ t : R, 0 ≤ t ∧ t ≤ 1 ∧ z = scalarAffineCombination x y t}

/-- Membership in the nLab affine segment, expanded into its interval parameter. -/
theorem mem_scalarAffineSegment_iff {x y z : P} :
    z ∈ scalarAffineSegment (R := R) x y ↔
      ∃ t : R, 0 ≤ t ∧ t ≤ 1 ∧ z = scalarAffineCombination x y t :=
  Iff.rfl

/-- nLab `convex set`: a subset `S` of a real affine space is convex when for any two points
`x, y ∈ S`, the straight line segment connecting `x` with `y` is contained in `S`. -/
def IsConvexSet (s : Set P) : Prop :=
  ∀ ⦃x y : P⦄, x ∈ s → y ∈ s → scalarAffineSegment (R := R) x y ⊆ s

end ConvexSet

section Polytope

variable {𝕜 : Type u} {E : Type v}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

/-- nLab-facing convex-geometric polytope: the convex hull of finitely many points.

This captures the convex-geometry reading of nLab's `polytope` page, distinct from the
algebraic-topology reading of `polyhedron` below. -/
def IsConvexPolytope (s : Set E) : Prop :=
  ∃ V : Finset E, s = convexHull 𝕜 (V : Set E)

/-- The point case in nLab's polytope sequence: a convex `0`-polytope is represented here as a
singleton set. -/
def IsPointPolytope (s : Set E) : Prop :=
  ∃ x : E, s = ({x} : Set E)

/-- Every point polytope is a convex polytope. -/
theorem IsPointPolytope.isConvexPolytope {s : Set E} (hs : IsPointPolytope s) :
    IsConvexPolytope (𝕜 := 𝕜) s := by
  rcases hs with ⟨x, rfl⟩
  refine ⟨{x}, ?_⟩
  simp [convexHull_singleton]

end Polytope

section RealPolytope

variable {E : Type v}
variable [AddCommGroup E] [Module ℝ E]

/-- A convex polytope is a convex set in the explicit nLab line-segment sense. -/
theorem IsConvexPolytope.convex {s : Set E} (hs : IsConvexPolytope (𝕜 := ℝ) s) :
    IsConvexSet (R := ℝ) (V := E) s := by
  rcases hs with ⟨V, rfl⟩
  have hconv : Convex ℝ (convexHull ℝ (V : Set E)) :=
    convex_convexHull ℝ (V : Set E)
  intro x y hx hy z hz
  rcases hz with ⟨t, ht0, ht1, rfl⟩
  change AffineMap.lineMap y x t ∈ convexHull ℝ (V : Set E)
  rw [AffineMap.lineMap_apply_module]
  exact (convex_iff_add_mem.mp hconv) hy hx (sub_nonneg.mpr ht1) ht0 (by ring)

end RealPolytope

section SimplicialPolyhedron

variable {𝕜 : Type u} {E : Type v}
variable [Ring 𝕜] [PartialOrder 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]

/-- A finite geometric simplicial complex, phrased using mathlib's geometric simplicial complex
API. Finiteness means that the set of faces is finite. -/
def IsFiniteSimplicialComplex (K : Geometry.SimplicialComplex 𝕜 E) : Prop :=
  K.faces.Finite

/-- nLab-facing geometric polyhedron inside an ambient module: the underlying space of a finite
simplicial complex.

This is the convex-geometric realization of the nLab algebraic-topology sentence "homeomorphic to
the geometric realization of a finite simplicial complex", specialized to a subset already sitting
in an ambient module. -/
def IsSimplicialPolyhedron (s : Set E) : Prop :=
  ∃ K : Geometry.SimplicialComplex 𝕜 E, IsFiniteSimplicialComplex K ∧ s = K.space

end SimplicialPolyhedron

section TopologicalPolyhedron

/-- nLab `polyhedron`, in its algebraic-topology sense: a topological space homeomorphic to the
realization of a finite simplicial complex.

The realization side is represented by mathlib's geometric simplicial complex `K` and its
underlying space `K.space`. This deliberately remains separate from `Set.IsPolyhedral`, the
Rockafellar/convex-analysis finite-half-space-intersection notion. -/
def IsTopologicalPolyhedron (X : Type u) [TopologicalSpace X] : Prop :=
  ∃ (E : Type u) (_ : AddCommGroup E) (_ : Module ℝ E) (_ : TopologicalSpace E),
    ∃ K : Geometry.SimplicialComplex ℝ E,
      IsFiniteSimplicialComplex K ∧ Nonempty (K.space ≃ₜ X)

end TopologicalPolyhedron

end NLab
