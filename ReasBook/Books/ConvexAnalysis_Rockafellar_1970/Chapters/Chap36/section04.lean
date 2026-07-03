import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_36_4_1 (from Chap07) -/
/-!
Source/core/bridge triage:

- `source-facing`: Definition 36.4.1 introduces the inverse bifunction `F_*`, characterized by
  `(F_* x) u = - (F u) x`.
- `core/canonical`: the primitive mathematical content is the canonical function expression
  `-Function.swap F`.
- `bridge/view`: this file uses textbook notation `F_*` directly for that canonical expression,
  without introducing a separate wrapper owner.

Domain-style sampling used here:
- `Bifunction.adjoint` from `Chap06.Lemma_31_0_8`, which keeps a source-facing bifunction
  owner while defining it as a thin bridge to canonical function-level operations;
- `Bifunction.objective` from `Chap06.Definition_6_29_12`, which exposes a chapter owner with only
  atomic companion lemmas;
- `Bifunction.lowerClosure_swap_apply` from `Chap07.Defn_34_1`, which already uses
  `Function.swap` as the chapter's canonical variable-exchange bridge;
- the canonical primitive `Function.swap`, which already supplies the underlying variable exchange.

Primitive data vs derived API:
- primitive input: a bifunction `F : U → X → L`;
- primitive core expression: `-Function.swap F`;
- derived API: the defining application formula and the involution law.

Layer target: `source-facing`.

Notation decision:
- the source writes `F_*`; this file therefore exposes that textbook surface as scoped notation
  directly on the canonical expression `-Function.swap F`;
- nearby theorem surfaces use the corresponding Lean notation `F _*` explicitly.
-/

universe u v w

noncomputable section

namespace Rockafellar

/- Textbook notation for the inverse bifunction from Definition 36.4.1. -/
scoped[Rockafellar] notation:max F " _*" => -Function.swap F

end Rockafellar

namespace Bifunction

section

variable {U : Type u} {X : Type v} {L : Type w}

open scoped Rockafellar

/- Primitive bridge from the textbook inverse notation to the canonical core expression. -/
theorem inverse_eq_neg_swap
    [Neg L] (F : U → X → L) :
    F _* = -Function.swap F :=
  rfl

@[simp] theorem inverse_apply
    [Neg L] (F : U → X → L) (x : X) (u : U) :
    F _* x u = -F u x :=
  rfl

/- The notation-level inverse maps are mutual inverses between swapped bifunction spaces. -/
theorem inverse_leftInverse
    [InvolutiveNeg L] :
    Function.LeftInverse
      (fun G : X → U → L => G _*)
      (fun F : U → X → L => F _*) := by
  intro F
  funext u x
  simp

/- Symmetric notation-level inverse law with swapped source/target spaces. -/
theorem inverse_rightInverse
    [InvolutiveNeg L] :
    Function.RightInverse
      (fun G : X → U → L => G _*)
      (fun F : U → X → L => F _*) :=
  inverse_leftInverse

@[simp] theorem inverse_inverse
    [InvolutiveNeg L] (F : U → X → L) :
    (F _*) _* = F :=
  inverse_leftInverse F

end

end Bifunction

/-! ### Proposition_36_4_2 (from Chap07) -/
noncomputable section

universe u v w z

open scoped Rockafellar
open Function

namespace Rockafellar

local notation "IsClosedProperConvex[" 𝕜 "]" =>
  Function.IsClosedProperConvex (𝕜 := 𝕜)

local notation "IsClosedProperConcave[" 𝕜 "]" =>
  Function.IsClosedProperConcave (𝕜 := 𝕜)

/-- Source-facing closed-proper-convex owner for a bifunction graph function. -/
scoped[Rockafellar] notation:70 "cpconvᵇ[" 𝕜 "](" F ")" =>
  IsClosedProperConvex[𝕜] (Function.uncurry F)

/-- Source-facing closed-proper-concave owner for a bifunction graph function. -/
scoped[Rockafellar] notation:70 "cpconcᵇ[" 𝕜 "](" F ")" =>
  IsClosedProperConcave[𝕜] (Function.uncurry F)

end Rockafellar

namespace Bifunction

section Convexity

variable {𝕜 : Type z} {U : Type u} {X : Type v} {α : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid U] [SMul 𝕜 U]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable [AddCommGroup α] [SMul 𝕜 α] [LE α]

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 36.4.2 studies the inverse bifunction `F_*`, owned in this chapter
  by `Bifunction.inverse`.
- `core/canonical`: the natural owner layer for the convexity clauses is the graph-function API
  `Function.uncurry`, together with the Chapter 6 convex/concave source notations
  `convᵇ[𝕜](F)` and `concᵇ[𝕜](F)`, and the closed-proper source notations
  `cpconvᵇ[𝕜](F)` and `cpconcᵇ[𝕜](F)` on
  `WithTopBot α`.
- `bridge/view`: the source-facing inverse object `F _*` is studied directly through those
  existing owners, with no file-local convex-bifunction wrapper alias.

Domain-style sampling used here:
- `Function.uncurry`;
- `Bifunction.inverse`;
- `convᵇ[𝕜](F)`;
- `concᵇ[𝕜](F)`.
- `cpconvᵇ[𝕜](F)`;
- `cpconcᵇ[𝕜](F)`.

Primitive data vs derived API:
- primitive datum: a bifunction `F : U → X → WithTopBot α`;
- source-facing inverse object: `F _*`;
- derived clauses: convexity/concavity exchange, preservation of the closed-proper classes, and
  involutivity.

Layer target: `source-facing`, using the chapter owners and source notation.
-/

-- Proof sketch: `Function.uncurry (inverse F)` is obtained from `Function.uncurry F` by
-- precomposing with coordinate swap and negating values; swapping preserves affine combinations,
-- while negation exchanges convexity and concavity.
/-- Proposition 36.4.2 (1): if a bifunction is convex through its graph-function owner, then its
inverse bifunction is concave. -/
theorem inverse_isConcave_of_isConvex
    {F : U → X → WithTopBot α} (hF : convᵇ[𝕜](F)) :
    concᵇ[𝕜](F _*) := sorry

-- Proof sketch: apply the same swap-and-negation transformation in the opposite direction:
-- concavity of the graph function becomes convexity after negation, and the coordinate swap keeps
-- the affine structure of the product domain.
/-- Second clause: if a bifunction is concave, then its inverse bifunction is convex through the
canonical graph-function owner. -/
theorem inverse_isConvex_of_isConcave
    {F : U → X → WithTopBot α} (hF : concᵇ[𝕜](F)) :
    convᵇ[𝕜](F _*) := sorry

/-- Involution bridge for Proposition 36.4.2 (1)-(2): inverse concavity and original graph
convexity are equivalent. -/
theorem inverse_isConcave_iff_isConvex
    {F : U → X → WithTopBot α} :
    concᵇ[𝕜](F _*) ↔ convᵇ[𝕜](F) := by
  constructor
  · intro hFstar
    simpa [inverse_inverse] using
      (inverse_isConvex_of_isConcave (F := F _*) hFstar)
  · intro hF
    exact inverse_isConcave_of_isConvex (F := F) hF

/-- Involution bridge for Proposition 36.4.2 (1)-(2): inverse graph convexity and original
concavity are equivalent. -/
theorem inverse_isConvex_iff_isConcave
    {F : U → X → WithTopBot α} :
    convᵇ[𝕜](F _*) ↔ concᵇ[𝕜](F) := by
  constructor
  · intro hFstar
    simpa [inverse_inverse] using
      (inverse_isConcave_of_isConvex (F := F _*) hFstar)
  · intro hF
    exact inverse_isConvex_of_isConcave (F := F) hF

end Convexity

section ClosedProper

variable {𝕜 : Type z} {U : Type u} {X : Type v} {α : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [TopologicalSpace U] [AddCommMonoid U] [SMul 𝕜 U]
variable [TopologicalSpace X] [AddCommMonoid X] [SMul 𝕜 X]
variable [TopologicalSpace (WithTopBot α)] [AddCommGroup α] [SMul 𝕜 α] [Preorder α]

-- Proof sketch: the inverse bifunction is the negated swapped graph function, so the closed proper
-- convex owner on `F` is transported to the closed proper concave owner on
-- the inverse by the same sign-swap transformation as in the convexity clauses.
/-- Third clause: if `F` has closed-proper-convex graph function, then its inverse bifunction has
closed-proper-concave graph function. -/
theorem inverse_isClosedProperConcave_of_isClosedProperConvex
    {F : U → X → WithTopBot α}
    (hF : cpconvᵇ[𝕜](F)) :
    cpconcᵇ[𝕜](F _*) := sorry

-- Proof sketch: rewrite closed proper concavity of `F` as closed proper convexity of `-uncurry F`,
-- then apply the same sign-swap transport to the inverse bifunction.
/-- Fourth clause: if `F` has closed-proper-concave graph function, then its inverse bifunction has
closed-proper-convex graph function. -/
theorem inverse_isClosedProperConvex_of_isClosedProperConcave
    {F : U → X → WithTopBot α}
    (hF : cpconcᵇ[𝕜](F)) :
    cpconvᵇ[𝕜](F _*) := sorry

/-- Involution bridge for Proposition 36.4.2 (3)-(4): inverse closed-proper concavity and
original closed-proper convexity are equivalent. -/
theorem inverse_isClosedProperConcave_iff_isClosedProperConvex
    {F : U → X → WithTopBot α} :
    cpconcᵇ[𝕜](F _*) ↔ cpconvᵇ[𝕜](F) := by
  constructor
  · intro hFstar
    simpa [inverse_inverse] using
      (inverse_isClosedProperConvex_of_isClosedProperConcave (F := F _*) hFstar)
  · intro hF
    exact inverse_isClosedProperConcave_of_isClosedProperConvex (F := F) hF

/-- Involution bridge for Proposition 36.4.2 (3)-(4): inverse closed-proper convexity and
original closed-proper concavity are equivalent. -/
theorem inverse_isClosedProperConvex_iff_isClosedProperConcave
    {F : U → X → WithTopBot α} :
    cpconvᵇ[𝕜](F _*) ↔ cpconcᵇ[𝕜](F) := by
  constructor
  · intro hFstar
    simpa [inverse_inverse] using
      (inverse_isClosedProperConcave_of_isClosedProperConvex (F := F _*) hFstar)
  · intro hF
    exact inverse_isClosedProperConvex_of_isClosedProperConcave (F := F) hF

end ClosedProper

section Involution

variable {U : Type u} {X : Type v} {α : Type w}
variable [InvolutiveNeg (WithTopBot α)]

/- Fifth clause: the inverse-bifunction operation `F ↦ -Function.swap F` is already the canonical
involution theorem `inverse_inverse`. -/
recall inverse_inverse

end Involution

end Bifunction

/-! ### Proposition_36_4_3 (from Chap07) -/
noncomputable section

open scoped Rockafellar

universe u v u' v' w

namespace Bifunction

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'} {α : Type w}
variable [ConditionallyCompleteLinearOrder α] [AddCommGroup α]
variable [HasPairing U UStar α] [HasPairing X XStar α]

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 36.4.3 says that the inverse operation `F ↦ F_*` commutes with the
  adjoint operation, producing the common bifunction denoted in the text by `F_*^*`.
- `core/canonical`: the built layer already provides the inverse notation `F _*` together with
  `Bifunction.adjoint`, and Definition 6.30.15 now supplies the source-facing owner
  `Bifunction.concaveAdjoint` as the matching concave-side bridge owner.
- `bridge/view`: this file records the commutation law directly as equalities between those owner
  operations, split into the convex-side and concave-side clauses because the two adjoint
  operations live on different source layers.

Domain-style sampling used here:
- notation `F _*` from `Definition_36_4_1`;
- `Bifunction.adjoint` from `Chap06.Definition_6_30_14`, available through the built
  Chapter 7 bridge import `Definition_36_4_5`;
- `Bifunction.concaveAdjoint` from `Chap06.Definition_6_30_15`;
- `Bifunction.inverse_adjoint` from `Definition_36_4_5`, which already owns the common
  `⨆ x, ⨆ u` formula for `(F⋆) _*`;
- the owner-level inverse involution from `Definition_36_4_1`.

Primitive data vs derived API:
- primitive data: a bifunction `F : U → X → WithBotTop α`;
- primitive owner expressions: `concaveAdjoint UStar XStar (F _*)` and `(F⋆) _*`;
- derived API: the commutation equalities showing that these two source constructions coincide.

Layer target: `bridge/view`.
-/

section ConvexClause

variable [Neg UStar] [HasPairingNegRight U UStar α]

-- Proof sketch: rewrite `concaveAdjoint` of `F _*` by the Chapter 6 textbook `⨆ x, ⨆ u`
-- formula, then reuse the Chapter 7 owner theorem `inverse_adjoint_apply`, which gives
-- the same formula for `(F⋆) _*`.
/-- Proposition 36.4.3 (1): taking the inverse first and then the concave adjoint agrees with
taking the convex adjoint first and then the inverse. -/
theorem concaveAdjoint_inverse_eq_inverse_adjoint
    (F : U → X → WithBotTop α) :
    concaveAdjoint UStar XStar (F _*) = (F⋆) _* := by
  funext uStar xStar
  rw [concaveAdjoint_eq_iSup_iSup (XStar := UStar) (UStar := XStar)]
  simpa [add_left_comm, add_comm] using
    (inverse_adjoint_apply (F := F) uStar xStar).symm

end ConvexClause

section ConcaveClause

variable [Neg XStar] [HasPairingNegRight X XStar α]

-- Proof sketch: expand the same three owners in the opposite order. The convex adjoint of
-- `G _*` is definitionally the same sign-swapped formula as the inverse of the concave
-- adjoint of `G`.
/-- Proposition 36.4.3 (2): taking the inverse first and then the convex adjoint agrees with
taking the concave adjoint first and then the inverse. -/
theorem adjoint_inverse_eq_inverse_concaveAdjoint
    (G : U → X → WithBotTop α) :
    (G _*)⋆ =
      (concaveAdjoint XStar UStar G) _* := by
  simpa [inverse_inverse] using
    congrArg (fun H => H _*)
      (concaveAdjoint_inverse_eq_inverse_adjoint (G _*)).symm

end ConcaveClause

end Bifunction

/-! ### Proposition_36_4_4 (from Chap07) -/
noncomputable section

universe u v

open scoped Rockafellar
open Function

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 36.4.4 says that for a convex bifunction `F`, the source operator
  `F_*^*` is again convex, and that applying the same source operator once more yields the usual
  bifunction biconjugate `F^{**}` on the paired-space Chapter 36 owner surface. In the stronger
  self-dual finite-dimensional setting over an ordered scalar field, Chapter 6 then identifies
  this ordinary biconjugate with `cl F`.
- `core/canonical`: the relevant owner layer is already present in the project:
  `Function.IsConvex 𝕜 (uncurry F)`, the Chapter 6 adjoint owner `F⋆`,
  the Chapter 7 inverse owner `F _*`, and the self-dual biconjugate surface
  `(F⋆⋆ : U → X → L)` for the specialization `F^{**}`. On the general paired-space
  layer, the ordinary biconjugate owner is `concaveAdjoint U X (F⋆)`.
- `bridge/view`: the textbook object `F_*^*` is the existing source-facing owner `((F⋆) _*)`,
  while its iterate is `((((F⋆) _*)⋆) _*)`. Proposition 36.4.3 already identifies that iterate
  with the canonical paired-space biconjugate owner `concaveAdjoint U X (F⋆)`, so this
  file stays on those owners rather than rebuilding the same construction through a local wrapper.

Domain-style sampling used here:
- `Function.IsConvex` on the graph-function owner from `Definition33_0_28`;
- the Chapter 12 convex-conjugate convexity owner theorem;
- the Chapter 6 owner `Bifunction.concaveAdjoint`;
- the Chapter 7 commutation theorem
  `Bifunction.adjoint_inverse_eq_inverse_concaveAdjoint`;
- the stable self-dual closure theorem `Bifunction.biadjointFunction_eq_closure`.

Primitive data vs derived API:
- primitive input: a convex bifunction `F : U → X → WithBotTop 𝕜`;
- primitive source-facing owner expression for `F_*^*`: `((F⋆) _*)`;
- derived API: convexity of that source object on the linear-pairing layer, its identification
  with the ordinary paired-space bifunction biconjugate after one more application of
  `G ↦ G_*^*`, the stronger self-dual `(F⋆⋆ : U → X → L)` specialization, and the recalled
  closure formula for that self-dual biconjugate.

Layer target: `bridge/view`, stated directly on the canonical chapter owners.
-/

section

variable {𝕜 : Type*} {α : Type*} {U : Type u} {X : Type v} {UStar : Type*} {XStar : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid UStar] [SMul 𝕜 UStar]
variable [AddCommMonoid XStar] [SMul 𝕜 XStar]
variable [ConditionallyCompleteLinearOrder α] [AddCommGroup α] [SMul 𝕜 α] [LE α]
variable [Neg UStar]
variable [HasPairing U UStar α] [HasPairing X XStar α]

variable (F : U → X → WithBotTop α)

local notation "F⋆" => (adjoint XStar UStar F : XStar → UStar → WithBotTop α)

/-- Primitive owner bridge for Proposition 36.4.4 (1): concavity of the adjoint owner `F⋆`
implies convexity of the source owner `F_*^*`. -/
theorem isConvex_inverse_adjoint_of_isConcave_adjoint
    (hFstar : concᵇ[𝕜](F⋆)) :
    convᵇ[𝕜]((F _*^*) : UStar → XStar → WithBotTop α) := by
  simpa using
    (inverse_isConvex_of_isConcave (𝕜 := 𝕜) (F := F⋆) hFstar)

end

section

variable {𝕜 : Type*} {U : Type u} {X : Type v} {UStar : Type*} {XStar : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup UStar] [Module 𝕜 UStar]
variable [AddCommGroup XStar] [Module 𝕜 XStar]
variable [HasLinearPairing U UStar 𝕜] [HasLinearPairing X XStar 𝕜]

variable (F : U → X → WithBotTop 𝕜)

local notation "F⋆" => (adjoint XStar UStar F : XStar → UStar → WithBotTop 𝕜)

-- Proof sketch: `- uncurry (F⋆)` is a Fenchel conjugate of `uncurry F` after the linear
-- coordinate change `(x⋆, u⋆) ↦ (-u⋆, x⋆)`, so Chapter 12 convexity of conjugates gives
-- concavity of `F⋆`. Proposition 36.4.2 then turns that concavity into convexity of its inverse
-- bifunction, which is exactly the source object `F_*^* = ((F⋆) _*)`.
/-- Proposition 36.4.4 (1): if `F` is a convex bifunction, then the source bifunction `F_*^*`,
rendered here as `((F⋆) _*)`, is again convex. -/
theorem isConvex_inverse_adjointFunction_of_isConvex
    (hF : convᵇ[𝕜](F)) :
    convᵇ[𝕜]((F _*^*) : UStar → XStar → WithBotTop 𝕜) := sorry

end

section

variable {α : Type*} {U : Type u} {X : Type v} {UStar : Type*} {XStar : Type*}
variable [ConditionallyCompleteLinearOrder α] [AddCommGroup α]
variable [Neg U] [Neg UStar]
variable [HasPairing U UStar α] [HasPairing X XStar α]
variable [HasPairing XStar X α] [HasPairing UStar U α]
variable [HasPairingNegRight UStar U α]

variable (F : U → X → WithBotTop α)

local notation "F⋆" => (adjoint XStar UStar F : XStar → UStar → WithBotTop α)

-- Proof sketch: Proposition 36.4.3 already says that adjoint-after-inverse equals
-- inverse-after-concave-adjoint. Applying that owner theorem to `F⋆` and then using the inverse
-- involution collapses the second iterate of `G ↦ G_*^*` to the ordinary paired-space
-- biconjugate owner `concaveAdjoint U X (F⋆)`.
/-- Proposition 36.4.4 (2), paired-space owner form: applying `G ↦ G_*^*` to
`G = F_*^* = ((F⋆) _*)` yields the ordinary bifunction biconjugate `F^{**}`, rendered on the
general paired-space owner layer as `concaveAdjoint U X (F⋆)`. -/
theorem iteratedInverseAdjoint_eq_concaveAdjoint_adjoint
    : ((((F⋆) _*)⋆) _*) = concaveAdjoint U X F⋆ := sorry

end

section

variable {U : Type u} {X : Type v} {L : Type*}
variable [Sub L] [Neg L] [SupSet L]
variable [Neg U] [Neg X]
variable [HasPairing (U × X) (U × X) L]
variable [HasPairing (X × U) (X × U) L]

variable (F : U → X → L)

-- Proof sketch: on the self-dual owner layer, the source iterate `G ↦ G_*^*` evaluated twice is
-- exactly the same owner-level object as `(F⋆⋆ : U → X → L)`, so this identity is independent of
-- convexity hypotheses and of any specific ordered-codomain specialization.
/-- Self-dual owner identity: for bifunctions on the primitive adjoint/inverse codomain layer,
the iterated source operator is the stable Chapter 6 bifunction biconjugate owner `F⋆⋆`. -/
theorem biadjointFunction_eq_iteratedInverseAdjointFunction
    : adjoint U X (adjoint X U F) = ((adjoint X U ((adjoint X U F) _*)) _*) := sorry

end

section

variable {𝕜 : Type*} {U : Type u} {X : Type v}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology 𝕜]
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [IsTopologicalAddGroup U] [ContinuousSMul 𝕜 U] [FiniteDimensional 𝕜 U] [T2Space U]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [IsTopologicalAddGroup X] [ContinuousSMul 𝕜 X] [FiniteDimensional 𝕜 X] [T2Space X]
variable [HasLinearPairing U U 𝕜] [HasContinuousPairing U U 𝕜]
variable [HasLinearPairing X X 𝕜] [HasContinuousPairing X X 𝕜]

/- Proposition 36.4.4 (3): for a convex bifunction, the bifunction biconjugate `F^{**}` equals
the source-facing bifunction closure `closure F` on the self-dual finite-dimensional owner layer. -/
recall biadjointFunction_eq_closure

end

end Bifunction

/-! ### Theorem_36_4 (from Chap07) -/
noncomputable section

universe u v

open Set
open scoped Rockafellar

namespace Bifunction

section Minimax

variable {U : Type u} {X : Type v}
variable [TopologicalSpace U] [TopologicalSpace X]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 36.4 says that equivalent saddle-functions determine the same minimax
  problem: they have the same row-infimum function, the same column-supremum function, therefore
  the same lower and upper minimax values, and the same saddle-points.
- `core/canonical`: the Chapter 34 owner for equivalence is `K ∼ L`, i.e. equality of the
  partial closures `cl₁` and `cl₂`; the Chapter 6/7 owner layer for the row and column aggregate
  functions is `perturbationFunction` and `upperPerturbationFunction`, and the Chapter 36
  saddle-point owner is `Bifunction.IsSaddlePointOn`.
- `bridge/view`: the source row/column formulas are companion views of those canonical owners, and
  the saddle-point transfer is mediated by Definition 36.1.1's attained-`iInf`/`iSup`
  characterization of `Bifunction.IsSaddlePointOn`.

Domain-style sampling used here:
- `Bifunction.equivalent_iff` from `Defn_34_4`;
- `Bifunction.perturbationFunction` from `Chap06.Definition_6_29_1`;
- `Bifunction.upperPerturbationFunction` from `Chap06.Definition_6_30_11`;
- `Bifunction.maximinValueOn`, `Bifunction.minimaxValueOn`, and `Bifunction.HasSaddleValueOn` from
  `Definition_36_0_1`;
- whole-space owner bridges `Bifunction.maximinValue`, `Bifunction.minimaxValue`,
  `Bifunction.HasSaddleValue` from `Definition_36_0_1`;
- `Bifunction.isSaddlePointOn_iff_iInf_eq_value_and_iSup_eq_value` from `Definition_36_1_1`;
- whole-space owner bridge `Bifunction.IsSaddlePoint` from `Chap06.Definition_6_28_7`;
- `cl(·)`, `lowerSemicontinuousHull_le`, and `le_lowerSemicontinuousHull` from Chapter 2;
- `concaveClosure` from Chapter 6.

Primitive data vs derived API:
- primitive owner data: two saddle-functions `K`, `K'` and an equivalence proof `K ∼ K'`;
- derived API: equality of the canonical owner functions `perturbationFunction K` and
  `upperPerturbationFunction (Function.swap K)`, their source-facing row/column companion
  formulas, equality of the two Chapter 36 minimax-value owners on the one-sided set-indexed
  layers `C × univ` and `univ × D`, the induced whole-space owner equalities
  `maximinValue`, `minimaxValue`, `HasSaddleValue`, and invariance of the whole-space saddle-point
  owner `IsSaddlePoint`.

Layer target: `bridge/view`. The source theorem compares two equivalent saddle-functions, while
  the public API should reuse the chapter equivalence owner and the canonical saddle-point owner
  instead of introducing a second saddle-value package.

Codomain-layer split used in this file:
- the bridge from `K ∼ K'` to row/column aggregate equality is stated at codomain
  `WithTopBot 𝕜`, using the Chapter 34 partial-closure owners `cl₁`/`cl₂` together with the
  codomain assumptions needed by the closure-to-`iInf`/`iSup` transport;
- once those aggregate equalities are available, transport of maximin/minimax values and
  saddle-value existence is stated at the primitive codomain layer `SupSet`/`InfSet`;
- source-order saddle-point transport is then stated at the codomain-generic
  `CompleteLattice` layer via `Bifunction.IsSaddlePointOn`.
-/

section EquivalentBridge

variable {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [NoMinOrder 𝕜] [Nonempty 𝕜] [OrderTopology 𝕜] [NoBotOrder 𝕜]

private theorem iSup_concaveClosure_eq_iSup
    [AddCommGroup 𝕜] [IsOrderedAddMonoid 𝕜] (g : U → WithTopBot 𝕜) :
    (⨆ u, concaveClosure g u) = ⨆ u, g u := by
  have hcl :
      -((⨅ u, cl(-g) u) : WithTopBot 𝕜) = ⨆ u, -(cl(-g) u) := by
    refine le_antisymm ?_ ?_
    · exact (WithBotTop.neg_le).2 <| le_iInf fun u ↦
        by simpa [neg_neg] using
          (WithBotTop.neg_le_neg_iff).2 (le_iSup (fun u ↦ -(cl(-g) u)) u)
    · refine iSup_le fun u ↦ ?_
      exact (WithBotTop.neg_le_neg_iff).2 (iInf_le (fun u ↦ cl(-g) u) u)
  have hg :
      -((⨅ u, -g u) : WithTopBot 𝕜) = ⨆ u, g u := by
    refine le_antisymm ?_ ?_
    · exact (WithBotTop.neg_le).2 <| le_iInf fun u ↦
        (WithBotTop.neg_le_neg_iff).2 (le_iSup (fun u ↦ g u) u)
    · refine iSup_le fun u ↦ ?_
      exact (WithBotTop.le_neg).2 (iInf_le (fun u ↦ -g u) u)
  calc
    (⨆ u, concaveClosure g u) = ⨆ u, -(cl(-g) u) := by
      simp [concaveClosure_eq_neg_lowerSemicontinuousHull_neg]
    _ = -((⨅ u, cl(-g) u) : WithTopBot 𝕜) := hcl.symm
    _ = -((⨅ u, -g u) : WithTopBot 𝕜) := by
      simpa using congrArg Neg.neg (iInf_lowerSemicontinuousHull_eq_iInf (-g))
    _ = ⨆ u, g u := hg

/-- Equivalent saddle-functions have the same canonical row-infimum owner
`perturbationFunction`. -/
theorem perturbationFunction_eq_of_equivalent
    {K K' : U → X → WithTopBot 𝕜} (hKK' : K ∼ K') :
    perturbationFunction K = perturbationFunction K' := by
  funext u
  rcases (equivalent_iff K K').1 hKK' with ⟨-, h₂⟩
  calc
    perturbationFunction K u = ⨅ x, cl(K u) x := by
      rw [perturbationFunction_apply]
      exact (iInf_lowerSemicontinuousHull_eq_iInf (K u)).symm
    _ = ⨅ x, cl(K' u) x := by
      simpa [closure2_apply] using congrArg (fun F : U → X → WithTopBot 𝕜 ↦ ⨅ x, F u x) h₂
    _ = perturbationFunction K' u := by
      rw [perturbationFunction_apply]
      exact iInf_lowerSemicontinuousHull_eq_iInf (K' u)

/-- Equivalent saddle-functions have the same row-infimum function `u ↦ inf_x K(u, x)`. -/
theorem iInf_eq_iInf_of_equivalent {K K' : U → X → WithTopBot 𝕜} (hKK' : K ∼ K') :
    (fun u ↦ ⨅ x, K u x) = fun u ↦ ⨅ x, K' u x := by
  simpa [perturbationFunction_apply] using perturbationFunction_eq_of_equivalent hKK'

@[simp] theorem iInf_eq_iInf_of_equivalent_apply
    {K K' : U → X → WithTopBot 𝕜} (hKK' : K ∼ K') (u : U) :
    (⨅ x, K u x) = ⨅ x, K' u x := by
  simpa using congrArg (fun F : U → WithTopBot 𝕜 ↦ F u) (iInf_eq_iInf_of_equivalent hKK')

/-- Equivalent saddle-functions have the same canonical column-supremum owner, written on the
swapped kernel as `upperPerturbationFunction (Function.swap K)`. -/
theorem upperPerturbationFunction_swap_eq_of_equivalent
    [AddCommGroup 𝕜] [IsOrderedAddMonoid 𝕜]
    {K K' : U → X → WithTopBot 𝕜} (hKK' : K ∼ K') :
    upperPerturbationFunction (Function.swap K) =
      upperPerturbationFunction (Function.swap K') := by
  funext x
  rcases (equivalent_iff K K').1 hKK' with ⟨h₁, -⟩
  calc
    upperPerturbationFunction (Function.swap K) x =
        ⨆ u, concaveClosure (fun u' ↦ K u' x) u := by
      rw [upperPerturbationFunction_apply]
      exact (iSup_concaveClosure_eq_iSup fun u' ↦ K u' x).symm
    _ = ⨆ u, concaveClosure (fun u' ↦ K' u' x) u := by
      simpa [closure1_apply] using congrArg (fun F : U → X → WithTopBot 𝕜 ↦ ⨆ u, F u x) h₁
    _ = upperPerturbationFunction (Function.swap K') x := by
      rw [upperPerturbationFunction_apply]
      exact iSup_concaveClosure_eq_iSup fun u' ↦ K' u' x

/-- Equivalent saddle-functions have the same column-supremum function `x ↦ sup_u K(u, x)`. -/
theorem iSup_eq_iSup_of_equivalent
    [AddCommGroup 𝕜] [IsOrderedAddMonoid 𝕜]
    {K K' : U → X → WithTopBot 𝕜} (hKK' : K ∼ K') :
    (fun x ↦ ⨆ u, K u x) = fun x ↦ ⨆ u, K' u x := by
  simpa [upperPerturbationFunction_apply, Function.swap] using
    upperPerturbationFunction_swap_eq_of_equivalent hKK'

@[simp] theorem iSup_eq_iSup_of_equivalent_apply
    [AddCommGroup 𝕜] [IsOrderedAddMonoid 𝕜]
    {K K' : U → X → WithTopBot 𝕜} (hKK' : K ∼ K') (x : X) :
    (⨆ u, K u x) = ⨆ u, K' u x := by
  simpa using congrArg (fun F : X → WithTopBot 𝕜 ↦ F x) (iSup_eq_iSup_of_equivalent hKK')

end EquivalentBridge

section CodomainGeneric

variable {β : Type*}
variable {U' : Type*} {X' : Type*}

section

/-- If two bifunctions have the same row-infimum function, they have the same Chapter 36
maximin value on `C × D`. -/
theorem maximinValueOn_eq_of_iInf₂_eq
    [SupSet β] [InfSet β]
    {K K' : U' → X' → β}
    (C : Set U') (D : Set X')
    (hRow : (fun u ↦ ⨅ x ∈ D, K u x) = fun u ↦ ⨅ x ∈ D, K' u x) :
    maximinValueOn C D K = maximinValueOn C D K' := by
  simpa [maximinValueOn] using congrArg (fun F : U' → β ↦ ⨆ u ∈ C, F u) hRow

/-- If two bifunctions have the same column-supremum function, they have the same Chapter 36
minimax value on `C × D`. -/
theorem minimaxValueOn_eq_of_iSup₂_eq
    [SupSet β] [InfSet β]
    {K K' : U' → X' → β}
    (C : Set U') (D : Set X')
    (hCol : (fun x ↦ ⨆ u ∈ C, K u x) = fun x ↦ ⨆ u ∈ C, K' u x) :
    minimaxValueOn C D K = minimaxValueOn C D K' := by
  simpa [minimaxValueOn] using congrArg (fun F : X' → β ↦ ⨅ x ∈ D, F x) hCol

/-- If two bifunctions have the same row-infimum function, they have the same Chapter 36
maximin value on `C × univ`. -/
theorem maximinValueOn_eq_of_iInf_eq_right_univ
    [SupSet β] [InfSet β]
    {K K' : U' → X' → β}
    (hRow : (fun u ↦ ⨅ x, K u x) = fun u ↦ ⨅ x, K' u x) (C : Set U') :
    maximinValueOn C univ K = maximinValueOn C univ K' := by
  have hRow' :
      (fun u ↦ ⨅ x ∈ (univ : Set X'), K u x) =
        fun u ↦ ⨅ x ∈ (univ : Set X'), K' u x := by
    funext u
    calc
      (⨅ x ∈ (univ : Set X'), K u x) = ⨅ x, K u x := by simp
      _ = ⨅ x, K' u x := by
        simpa using congrArg (fun F : U' → β ↦ F u) hRow
      _ = (⨅ x ∈ (univ : Set X'), K' u x) := by simp
  simpa using maximinValueOn_eq_of_iInf₂_eq C (univ : Set X') hRow'

/-- If two bifunctions have the same column-supremum function, they have the same Chapter 36
minimax value on `univ × D`. -/
theorem minimaxValueOn_eq_of_iSup_eq_left_univ
    [SupSet β] [InfSet β]
    {K K' : U' → X' → β}
    (hCol : (fun x ↦ ⨆ u, K u x) = fun x ↦ ⨆ u, K' u x) (D : Set X') :
    minimaxValueOn univ D K = minimaxValueOn univ D K' := by
  have hCol' :
      (fun x ↦ ⨆ u ∈ (univ : Set U'), K u x) =
        fun x ↦ ⨆ u ∈ (univ : Set U'), K' u x := by
    funext x
    calc
      (⨆ u ∈ (univ : Set U'), K u x) = ⨆ u, K u x := by simp
      _ = ⨆ u, K' u x := by
        simpa using congrArg (fun F : X' → β ↦ F x) hCol
      _ = (⨆ u ∈ (univ : Set U'), K' u x) := by simp
  simpa using minimaxValueOn_eq_of_iSup₂_eq (univ : Set U') D hCol'

/-- If two bifunctions have the same row-infimum function, they have the same Chapter 36
maximin value on `univ × univ`. -/
theorem maximinValueOn_univ_eq_of_iInf_eq
    [SupSet β] [InfSet β]
    {K K' : U' → X' → β}
    (hRow : (fun u ↦ ⨅ x, K u x) = fun u ↦ ⨅ x, K' u x) :
    maximinValueOn univ univ K = maximinValueOn univ univ K' := by
  simpa using maximinValueOn_eq_of_iInf_eq_right_univ hRow (univ : Set U')

/-- If two bifunctions have the same column-supremum function, they have the same Chapter 36
minimax value on `univ × univ`. -/
theorem minimaxValueOn_univ_eq_of_iSup_eq
    [SupSet β] [InfSet β]
    {K K' : U' → X' → β}
    (hCol : (fun x ↦ ⨆ u, K u x) = fun x ↦ ⨆ u, K' u x) :
    minimaxValueOn univ univ K = minimaxValueOn univ univ K' := by
  simpa using minimaxValueOn_eq_of_iSup_eq_left_univ hCol (univ : Set X')

/-- If two bifunctions have the same row-infimum function, they have the same whole-space Chapter
36 maximin value. -/
theorem maximinValue_eq_of_iInf_eq
    [SupSet β] [InfSet β]
    {K K' : U' → X' → β}
    (hRow : (fun u ↦ ⨅ x, K u x) = fun u ↦ ⨅ x, K' u x) :
    maximinValue K = maximinValue K' := by
  simpa [maximinValue] using maximinValueOn_univ_eq_of_iInf_eq hRow

/-- If two bifunctions have the same column-supremum function, they have the same whole-space
Chapter 36 minimax value. -/
theorem minimaxValue_eq_of_iSup_eq
    [SupSet β] [InfSet β]
    {K K' : U' → X' → β}
    (hCol : (fun x ↦ ⨆ u, K u x) = fun x ↦ ⨆ u, K' u x) :
    minimaxValue K = minimaxValue K' := by
  simpa [minimaxValue] using minimaxValueOn_univ_eq_of_iSup_eq hCol

/-- Row-infimum and column-supremum equality imply simultaneous Chapter 36 saddle-value existence
on `C × D`. -/
theorem hasSaddleValueOn_iff_of_iInf₂_iSup₂_eq
    [SupSet β] [InfSet β]
    {K K' : U' → X' → β}
    (C : Set U') (D : Set X')
    (hRow : (fun u ↦ ⨅ x ∈ D, K u x) = fun u ↦ ⨅ x ∈ D, K' u x)
    (hCol : (fun x ↦ ⨆ u ∈ C, K u x) = fun x ↦ ⨆ u ∈ C, K' u x) :
    HasSaddleValueOn C D K ↔ HasSaddleValueOn C D K' := by
  rw [HasSaddleValueOn, HasSaddleValueOn,
    maximinValueOn_eq_of_iInf₂_eq C D hRow,
    minimaxValueOn_eq_of_iSup₂_eq C D hCol]

/-- Row-infimum and column-supremum equality imply simultaneous Chapter 36 saddle-value existence
on `univ × univ`. -/
theorem hasSaddleValueOn_univ_iff_of_iInf_iSup_eq
    [SupSet β] [InfSet β]
    {K K' : U' → X' → β}
    (hRow : (fun u ↦ ⨅ x, K u x) = fun u ↦ ⨅ x, K' u x)
    (hCol : (fun x ↦ ⨆ u, K u x) = fun x ↦ ⨆ u, K' u x) :
    HasSaddleValueOn univ univ K ↔ HasSaddleValueOn univ univ K' := by
  have hRow' :
      (fun u ↦ ⨅ x ∈ (univ : Set X'), K u x) =
        fun u ↦ ⨅ x ∈ (univ : Set X'), K' u x := by
    funext u
    calc
      (⨅ x ∈ (univ : Set X'), K u x) = ⨅ x, K u x := by simp
      _ = ⨅ x, K' u x := by
        simpa using congrArg (fun F : U' → β ↦ F u) hRow
      _ = (⨅ x ∈ (univ : Set X'), K' u x) := by simp
  have hCol' :
      (fun x ↦ ⨆ u ∈ (univ : Set U'), K u x) =
        fun x ↦ ⨆ u ∈ (univ : Set U'), K' u x := by
    funext x
    calc
      (⨆ u ∈ (univ : Set U'), K u x) = ⨆ u, K u x := by simp
      _ = ⨆ u, K' u x := by
        simpa using congrArg (fun F : X' → β ↦ F x) hCol
      _ = (⨆ u ∈ (univ : Set U'), K' u x) := by simp
  simpa using hasSaddleValueOn_iff_of_iInf₂_iSup₂_eq
    (univ : Set U') (univ : Set X') hRow' hCol'

/-- Row-infimum and column-supremum equality imply simultaneous whole-space Chapter 36
saddle-value existence. -/
theorem hasSaddleValue_iff_of_iInf_iSup_eq
    [SupSet β] [InfSet β]
    {K K' : U' → X' → β}
    (hRow : (fun u ↦ ⨅ x, K u x) = fun u ↦ ⨅ x, K' u x)
    (hCol : (fun x ↦ ⨆ u, K u x) = fun x ↦ ⨆ u, K' u x) :
    HasSaddleValue K ↔ HasSaddleValue K' := by
  simpa [HasSaddleValue] using
    hasSaddleValueOn_univ_iff_of_iInf_iSup_eq hRow hCol

end

section

variable [CompleteLattice β]

/-- Equality of the row-infimum and column-supremum functions on `C × D` implies equality of the
source-order saddle-point predicates on `C × D`. -/
theorem isSaddlePointOn_iff_of_iInf₂_iSup₂_eq
    {K K' : U' → X' → β}
    (C : Set U') (D : Set X')
    (hRow : (fun u ↦ ⨅ x ∈ D, K u x) = fun u ↦ ⨅ x ∈ D, K' u x)
    (hCol : (fun x ↦ ⨆ u ∈ C, K u x) = fun x ↦ ⨆ u ∈ C, K' u x)
    {u : U'} (hu : u ∈ C) {x : X'} (hx : x ∈ D) :
    IsSaddlePointOn C D K u x ↔ IsSaddlePointOn C D K' u x := by
  have hRow_u : (⨅ v' ∈ D, K u v') = ⨅ v' ∈ D, K' u v' := by
    simpa using congrArg (fun F : U' → β ↦ F u) hRow
  have hCol_x : (⨆ u' ∈ C, K u' x) = ⨆ u' ∈ C, K' u' x := by
    simpa using congrArg (fun F : X' → β ↦ F x) hCol
  rw [isSaddlePointOn_iff_iInf_eq_value_and_iSup_eq_value hu hx]
  rw [isSaddlePointOn_iff_iInf_eq_value_and_iSup_eq_value hu hx]
  have transport {L M : U' → X' → β}
      (hRowLM : (⨅ v' ∈ D, L u v') = ⨅ v' ∈ D, M u v')
      (hColLM : (⨆ u' ∈ C, L u' x) = ⨆ u' ∈ C, M u' x) :
      ((⨅ v' ∈ D, L u v') = L u x ∧ (⨆ u' ∈ C, L u' x) = L u x) →
        ((⨅ v' ∈ D, M u v') = M u x ∧ (⨆ u' ∈ C, M u' x) = M u x) := by
    intro hL
    have hEq : (⨅ v' ∈ D, M u v') = ⨆ u' ∈ C, M u' x := by
      calc
        (⨅ v' ∈ D, M u v') = ⨅ v' ∈ D, L u v' := hRowLM.symm
        _ = L u x := hL.1
        _ = ⨆ u' ∈ C, L u' x := hL.2.symm
        _ = ⨆ u' ∈ C, M u' x := hColLM
    refine ⟨?_, ?_⟩
    · apply le_antisymm
      · exact iInf₂_le x hx
      · calc
          M u x ≤ ⨆ u' ∈ C, M u' x := le_iSup₂_of_le u hu le_rfl
          _ = ⨅ v' ∈ D, M u v' := hEq.symm
    · apply le_antisymm
      · calc
          ⨆ u' ∈ C, M u' x = ⨅ v' ∈ D, M u v' := hEq.symm
          _ ≤ M u x := iInf₂_le x hx
      · exact le_iSup₂_of_le u hu le_rfl
  constructor
  · simpa using transport hRow_u hCol_x
  · simpa using transport hRow_u.symm hCol_x.symm

/-- Equality of the row-infimum and column-supremum functions implies equality of the source-order
saddle-point predicates on `univ × univ`. -/
theorem isSaddlePointOn_iff_of_iInf_iSup_eq
    {K K' : U' → X' → β}
    (hRow : (fun u ↦ ⨅ x, K u x) = fun u ↦ ⨅ x, K' u x)
    (hCol : (fun x ↦ ⨆ u, K u x) = fun x ↦ ⨆ u, K' u x)
    {u : U'} {x : X'} :
    IsSaddlePointOn univ univ K u x ↔
      IsSaddlePointOn univ univ K' u x := by
  have hRow' :
      (fun u ↦ ⨅ x ∈ (univ : Set X'), K u x) =
        fun u ↦ ⨅ x ∈ (univ : Set X'), K' u x := by
    funext u
    calc
      (⨅ x ∈ (univ : Set X'), K u x) = ⨅ x, K u x := by simp
      _ = ⨅ x, K' u x := by
        simpa using congrArg (fun F : U' → β ↦ F u) hRow
      _ = (⨅ x ∈ (univ : Set X'), K' u x) := by simp
  have hCol' :
      (fun x ↦ ⨆ u ∈ (univ : Set U'), K u x) =
        fun x ↦ ⨆ u ∈ (univ : Set U'), K' u x := by
    funext x
    calc
      (⨆ u ∈ (univ : Set U'), K u x) = ⨆ u, K u x := by simp
      _ = ⨆ u, K' u x := by
        simpa using congrArg (fun F : X' → β ↦ F x) hCol
      _ = (⨆ u ∈ (univ : Set U'), K' u x) := by simp
  simpa using isSaddlePointOn_iff_of_iInf₂_iSup₂_eq
    (univ : Set U') (univ : Set X') hRow' hCol' (u := u) (x := x) (by simp) (by simp)

/-- Equality of the row-infimum and column-supremum functions implies equality of the source-order
saddle-point owners on the whole space. -/
theorem isSaddlePoint_iff_of_iInf_iSup_eq
    {K K' : U' → X' → β}
    (hRow : (fun u ↦ ⨅ x, K u x) = fun u ↦ ⨅ x, K' u x)
    (hCol : (fun x ↦ ⨆ u, K u x) = fun x ↦ ⨆ u, K' u x)
    {u : U'} {x : X'} :
    IsSaddlePoint K u x ↔ IsSaddlePoint K' u x := by
  simpa [IsSaddlePoint] using
    isSaddlePointOn_iff_of_iInf_iSup_eq hRow hCol

end
end CodomainGeneric

section EquivalentBridge

variable {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [NoMinOrder 𝕜] [Nonempty 𝕜] [OrderTopology 𝕜] [NoBotOrder 𝕜]

/-- Equivalent saddle-functions have the same Chapter 36 maximin value on `C × univ`. -/
theorem maximinValueOn_eq_of_equivalent_right_univ
    {K K' : U → X → WithTopBot 𝕜} (hKK' : K ∼ K') (C : Set U) :
    maximinValueOn C univ K = maximinValueOn C univ K' := by
  exact maximinValueOn_eq_of_iInf_eq_right_univ (iInf_eq_iInf_of_equivalent hKK') C

/-- Equivalent saddle-functions have the same Chapter 36 minimax value on `univ × D`. -/
theorem minimaxValueOn_eq_of_equivalent_left_univ
    [AddCommGroup 𝕜] [IsOrderedAddMonoid 𝕜]
    {K K' : U → X → WithTopBot 𝕜} (hKK' : K ∼ K') (D : Set X) :
    minimaxValueOn univ D K = minimaxValueOn univ D K' := by
  exact minimaxValueOn_eq_of_iSup_eq_left_univ (iSup_eq_iSup_of_equivalent hKK') D

/-- Equivalent saddle-functions have the same whole-space Chapter 36 maximin value. -/
theorem maximinValue_eq_of_equivalent {K K' : U → X → WithTopBot 𝕜} (hKK' : K ∼ K') :
    maximinValue K = maximinValue K' := by
  exact maximinValue_eq_of_iInf_eq (iInf_eq_iInf_of_equivalent hKK')

/-- Equivalent saddle-functions have the same whole-space Chapter 36 minimax value. -/
theorem minimaxValue_eq_of_equivalent
    [AddCommGroup 𝕜] [IsOrderedAddMonoid 𝕜]
    {K K' : U → X → WithTopBot 𝕜} (hKK' : K ∼ K') :
    minimaxValue K = minimaxValue K' := by
  exact minimaxValue_eq_of_iSup_eq (iSup_eq_iSup_of_equivalent hKK')

/-- Equivalent saddle-functions have a saddle value simultaneously on the whole space. -/
theorem hasSaddleValue_iff_of_equivalent
    [AddCommGroup 𝕜] [IsOrderedAddMonoid 𝕜]
    {K K' : U → X → WithTopBot 𝕜} (hKK' : K ∼ K') :
    HasSaddleValue K ↔ HasSaddleValue K' := by
  exact hasSaddleValue_iff_of_iInf_iSup_eq
    (iInf_eq_iInf_of_equivalent hKK')
    (iSup_eq_iSup_of_equivalent hKK')

/-- Theorem 36.4, saddle-point clause: equivalent saddle-functions have exactly the same
source-order saddle-points on the whole space. -/
theorem isSaddlePoint_iff_of_equivalent
    [AddCommGroup 𝕜] [IsOrderedAddMonoid 𝕜]
    {K K' : U → X → WithTopBot 𝕜} (hKK' : K ∼ K') {u : U} {x : X} :
    IsSaddlePoint K u x ↔ IsSaddlePoint K' u x := by
  exact isSaddlePoint_iff_of_iInf_iSup_eq
    (iInf_eq_iInf_of_equivalent hKK')
    (iSup_eq_iSup_of_equivalent hKK')

end EquivalentBridge

end Minimax

end Bifunction

/-! ### Definition_36_4_5 (from Chap07) -/
noncomputable section

universe u v u' v'

open scoped Rockafellar

namespace Rockafellar

/- Textbook notation for the Chapter 36 mixed inverse-adjoint owner. -/
scoped postfix:max " _*^*" => fun F ↦ (F⋆) _*

end Rockafellar

namespace Bifunction

section

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'} {α : Type*}
variable [AddCommGroup α] [ConditionallyCompleteLinearOrder α]
variable [Neg UStar]
variable [HasPairing U UStar α] [HasPairing X XStar α]
variable [HasPairingNegRight U UStar α]
variable (F : U → X → WithTopBot α)

omit [ConditionallyCompleteLinearOrder α] in
private theorem pairing_neg_right_withTopBot (u : U) (uStar : UStar) :
    (⟪u, -uStar⟫ₚ : WithTopBot α) = -(⟪u, uStar⟫ₚ : WithTopBot α) := by
  change ((⟪u, -uStar⟫ₚ : α) : WithTopBot α) = -((⟪u, uStar⟫ₚ : α) : WithTopBot α)
  simpa using
    congrArg ((↑) : α → WithTopBot α)
      (HasPairingNegRight.pairing_neg_right u uStar)

/-!
Source/core/bridge triage:

- `source-facing`: Definition 36.4.5 says the inverse bifunction operation commutes with the
  adjoint-side source formula `F_*^*`, now exposed directly by scoped notation on the canonical
  owner expression `((adjoint XStar UStar F) _*)`.
- `core/canonical`: upstream already supplies the inverse notation layer `F _*` from
  `Definition_36_4_1` and the owner `Bifunction.adjoint` from `Chap06.Definition_6_30_14`.
- `bridge/view`: this file keeps the source formula as a bridge for the existing owner
  `((adjoint XStar UStar F) _*)`.

Domain-style sampling used here:
- `Bifunction.inverse_apply` and notation `F _*` from `Definition_36_4_1`;
- `Bifunction.adjoint` and `Bifunction.adjoint_apply` from `Chap06.Definition_6_30_14`;
- product-pairing owner `pairing_prod` from `Chap01.HasPairing`.

Primitive data vs derived API:
- primitive layer: the notation `F _*` and owner `adjoint`;
- derived API: the function-level source formula and its pointwise evaluation theorem.

Layer target: `bridge/view`, on the pairing-based dual owner layer instead of a concrete
inner-product self-dual model.
-/

/-- Definition 36.4.5, bridge form: the source object `F_*^*` is exactly the source `sup`-formula
with dual variables `(uStar, xStar)`. -/
theorem inverse_adjoint :
    (F _*^*) =
      fun (uStar : UStar) (xStar : XStar) ↦
        ⨆ x : X, ⨆ u : U,
          F _* x u +
            ((⟪x, xStar⟫ₚ : WithTopBot α) - (⟪u, uStar⟫ₚ : WithTopBot α)) := by
  funext uStar xStar
  simp only [inverse_apply, adjoint_apply, neg_neg, WithTopBot.sub_eq_add_neg]
  calc
    (⨆ p : U × X, (⟪p, (-uStar, xStar)⟫ₚ : WithTopBot α) - F p.1 p.2)
      = ⨆ p : U × X,
          F _* p.2 p.1 +
            ((⟪p.2, xStar⟫ₚ : WithTopBot α) - (⟪p.1, uStar⟫ₚ : WithTopBot α)) := by
        simp [inverse_apply, pairing_prod, pairing_neg_right_withTopBot, add_left_comm, add_comm]
    _ = ⨆ q : X × U,
          F _* q.1 q.2 +
            ((⟪q.1, xStar⟫ₚ : WithTopBot α) - (⟪q.2, uStar⟫ₚ : WithTopBot α)) := by
        let g : X × U → WithTopBot α := fun q ↦
          F _* q.1 q.2 +
            ((⟪q.1, xStar⟫ₚ : WithTopBot α) - (⟪q.2, uStar⟫ₚ : WithTopBot α))
        simpa [g] using (Equiv.prodComm U X).surjective.iSup_comp g
    _ = ⨆ x : X, ⨆ u : U,
          F _* x u +
            ((⟪x, xStar⟫ₚ : WithTopBot α) - (⟪u, uStar⟫ₚ : WithTopBot α)) := by
        rw [iSup_prod']

/-- Pointwise form of Definition 36.4.5. -/
theorem inverse_adjoint_apply (uStar : UStar) (xStar : XStar) :
    (F _*^*) uStar xStar =
      ⨆ x : X, ⨆ u : U,
        F _* x u +
          ((⟪x, xStar⟫ₚ : WithTopBot α) - (⟪u, uStar⟫ₚ : WithTopBot α)) := by
  simpa using congrFun (congrFun (inverse_adjoint (F := F)) uStar) xStar

end

end Bifunction

/-! ### Proposition_36_4_6 (from Chap07) -/
noncomputable section

universe u u' v

open scoped Rockafellar

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 36.4.6 studies the bifunction on `UStar × X` given by the
  explicit infimum formula `(uStar, x) ↦ inf_u (⟪u, uStar⟫ₚ + F u x)`.
- `core/canonical`: the theorem owner is the Chapter 34 representative
  `upperConcavePairing (F _*)`, with conclusion in `SaddleFunction.IsConcaveConvex`.
- `bridge/view`: the Chapter 6 owner `lagrangian (toOrderDual F)` and the explicit `iInf` formula
  are downstream companion views, via `lagrangian_toOrderDual_eq_upperConcavePairing_inverse` and
  `lagrangian_eq_iInf_pairing_add`.

Domain-style sampling used here:
- `HasLinearPairing` and the derived pairing notation `⟪·, ·⟫ₚ` from `Chap01.HasPairing`;
- `Bifunction.toOrderDual` from `Chap01.EOrder.Basic`;
- `(Function.uncurry F).IsConvex 𝕜` from `Chap01.Theorem_4_2`;
- `Bifunction.lagrangian` from `Chap06.Definition_6_30_13`;
- `lagrangian_toOrderDual_eq_upperConcavePairing_inverse` and
  `lagrangian_eq_iInf_pairing_add` from `Chap07.Theorem_36_5`;
- `SaddleFunction.IsConcaveConvex` from `Chap07.Definition33_0_1`;

Primitive data vs derived API:
- primitive input: `F : U → X → WithBotTop 𝕜` with the convex-bifunction owner
  `(Function.uncurry F).IsConvex 𝕜`;
- primitive pairing owner: `HasLinearPairing U UStar 𝕜`, whose canonical raw and extended-codomain
  pairing views are derived upstream;
- primitive chapter owner: `upperConcavePairing (F _*)`;
- derived companion views: `lagrangian (toOrderDual F)` and the explicit infimum formula.

Layer target: `core/canonical`. The dual-variable concavity side is kept on the chapter's
linear-pairing owner layer rather than on a raw `HasPairing`, because the pairing term must stay
affine in `uStar`.
-/

section Shape

variable {𝕜 : Type*} {U : Type u} {UStar : Type u'} {X : Type v}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid UStar] [Module 𝕜 UStar]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [HasLinearPairing U UStar 𝕜]

open SaddleFunction

local instance : HasPairing UStar U (WithBotTop 𝕜) := HasPairing.swap

/-- Proposition 36.4.6 on the intrinsic Chapter 34 owner: if `F` is jointly convex, then the
inverse-slice upper representative `upperConcavePairing (F _*)` is concave-convex. -/
theorem upperConcavePairing_inverse_isConcaveConvex_of_isConvex
    (F : U → X → WithBotTop 𝕜) (hF : (Function.uncurry F).IsConvex 𝕜) :
    IsConcaveConvex 𝕜 ((upperConcavePairing (F _*)) : UStar → X → WithBotTop 𝕜) := by
  sorry

/-- Companion bridge form of Proposition 36.4.6 on the Chapter 6 kernel
`lagrangian (toOrderDual F)`. -/
theorem lagrangian_toOrderDual_isConcaveConvex_of_isConvex
    (F : U → X → WithBotTop 𝕜) (hF : (Function.uncurry F).IsConvex 𝕜) :
    IsConcaveConvex 𝕜 ((lagrangian (toOrderDual F)) : UStar → X → WithBotTop 𝕜) := by
  sorry

-- Rewrite the bridge owner through `lagrangian_eq_iInf_pairing_add`; the source formula is a
-- companion-only surface to the intrinsic owner theorem above.
/-- Companion source formula form: if `F` is jointly convex, then
`(uStar, x) ↦ inf_u (⟪u, uStar⟫ₚ + F u x)` is concave in `uStar` and convex in `x`. -/
theorem lagrangianFormula_isConcaveConvex_of_isConvex
    (F : U → X → WithBotTop 𝕜) (hF : (Function.uncurry F).IsConvex 𝕜) :
    IsConcaveConvex 𝕜 (fun (uStar : UStar) x ↦ ⨅ u : U, ⟪u, uStar⟫ₚ + F u x) := by
  sorry

/-!
The two companion surfaces are intentionally downstream:
- `lagrangian (toOrderDual F)` is a bridge equality rewrite of `upperConcavePairing (F _*)`;
- the explicit `iInf` kernel is a second bridge rewrite of that same owner theorem.
-/

end Shape

end Bifunction
