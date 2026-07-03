import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_12_3_1 (from Chap03) -/
noncomputable section

universe u v

section

open scoped Rockafellar

variable {E : Type u} {L : Type v}
variable [SupSet L] [Sub L]
variable [HasPairing E E L]

/-- Corollary 12.3.1 (canonical owner form): if `f` is fixed by Fenchel biconjugation, then
invariance of `f` under a family of pairing-compatible bijections is equivalent to invariance of
its Fenchel conjugate under the same family. -/
theorem invariant_under_equiv_iff_convexConjugate_invariant_of_biconjugate
    (f : E → L) (G : Set (E ≃ E))
    (hG_pair :
      ∀ A ∈ G, ∀ x xStar : E, (⟪A x, xStar⟫ₚ : L) = ⟪x, A.symm xStar⟫ₚ)
    (hf_biconj : f⋆⋆ = f) :
    (∀ A ∈ G, f ∘ A = f) ↔
      ∀ A ∈ G, f⋆ ∘ A = f⋆ := by
  have hconj_comp (g : E → L) (A : E ≃ E)
      (hA : ∀ x xStar : E, (⟪A x, xStar⟫ₚ : L) = ⟪x, A.symm xStar⟫ₚ) :
      (g ∘ A)⋆ = g⋆ ∘ A := by
    funext xStar
    change convexConjugate (g ∘ A) xStar = convexConjugate g (A xStar)
    rw [convexConjugate_eq_iSup_pairing_sub, convexConjugate_eq_iSup_pairing_sub]
    change
      (⨆ x : E, ((⟪x, xStar⟫ₚ : L) - g (A x))) =
        ⨆ y : E, ((⟪y, A xStar⟫ₚ : L) - g y)
    calc
      (⨆ x : E, ((⟪x, xStar⟫ₚ : L) - g (A x)))
          = ⨆ x : E, ((⟪A x, A xStar⟫ₚ : L) - g (A x)) := by
            refine iSup_congr ?_
            intro x
            congr 1
            simpa using (hA x (A xStar)).symm
      _ = ⨆ y : E, ((⟪y, A xStar⟫ₚ : L) - g y) := by
            simpa using
              (A.surjective.iSup_comp
                (g := fun y : E ↦ ((⟪y, A xStar⟫ₚ : L) - g y)))
  constructor
  · intro hf_invariant A hA
    calc
      f⋆ ∘ A = (f ∘ A)⋆ := (hconj_comp f A (hG_pair A hA)).symm
      _ = f⋆ := by rw [hf_invariant A hA]
  · intro hconj_invariant A hA
    have hbiconj_invariant : f⋆⋆ ∘ A = f⋆⋆ := by
      calc
        f⋆⋆ ∘ A = (f⋆ ∘ A)⋆ := (hconj_comp f⋆ A (hG_pair A hA)).symm
        _ = f⋆⋆ := by
          rw [hconj_invariant A hA]
          rfl
    calc
      f ∘ A = f⋆⋆ ∘ A := by
        simpa using congrArg (fun g : E → L ↦ g ∘ A) hf_biconj.symm
      _ = f⋆⋆ := hbiconj_invariant
      _ = f := hf_biconj

end

/-! ### Text_12_3_1 (from Chap03) -/
noncomputable section

open scoped Rockafellar

section Graph

variable {𝕜 X Y : Type*}
  [Ring 𝕜]
  [AddCommGroup X] [Module 𝕜 X]
  [AddCommGroup Y] [Module 𝕜 Y]

local notation "X⋆" => Module.Dual 𝕜 X
local notation "Y⋆" => Module.Dual 𝕜 Y
local notation "P" => X × Y
local notation "P⋆" => X⋆ × Y⋆

/-!
Abstraction checks:
- codomain/ambient layer: the support-cut owner is the chapter-canonical
  `Function.toWithTopBotOn`, so theorem surfaces stay on `WithTopBot 𝕜` without exposing raw
  piecewise plumbing.
- scalar structure: `LinearMap.dualMap`, affine-map algebra, and subtraction only require
  `[Ring 𝕜]`; no commutativity assumption is used.
- owner choice: declarations are exposed under `AffineMap` (intrinsic owner of the graph data),
  not under the over-concrete namespace `ConvexERealFunction`.
- topology/intrinsic language: this item is affine-pairing algebraic; no ambient topology owner is
  needed.
- naming/notation: the existing conjugate notation `f⋆` and graph owner `AffineMap.graph` already
  give the source-facing surface without extra custom notation.

Source/core/bridge triage for this item.

- `source-facing`: Text 12.3.1 gives the conjugate formula for a partial affine function with
  finite locus cut out by an affine graph.
- `core/canonical`: the owner operations are `convexConjugate` for Fenchel conjugation,
  the intrinsic support-cut owner `Function.toWithTopBotOn` for the finite-domain cut, and
  `AffineMap.graph` for the affine graph on which the function is finite.
- `bridge/view`: concrete coordinate specializations are downstream bridges. The core theorem
  itself lives at the pairing layer with dual variables in `Module.Dual`.

Domain-style sampling used here:
- `convexConjugate`;
- `Function.toWithTopBotOn`;
- `AffineMap.graph`;
- `AffineSubspace.map` (with `AffineEquiv.prodComm`);
- `LinearMap.dualMap`;
- the indicator/support-cut bridge language from Chapter 1.

Primitive data vs derived API:
- primitive inputs here: the affine functional `g : X →ᵃ[𝕜] 𝕜` and the affine graph map
  `T : X →ᵃ[𝕜] Y`;
- the intrinsic source-facing owner is the partial-affine support cut
  `realBranch.toWithTopBotOn support` on an affine graph;
- the affine-dual graph map `conjugateGraphMap g T` is derived API from those primitives.

Layer target: `core/canonical`. The main theorem is stated on the primal/dual pairing layer
`(X × Y, X⋆ × Y⋆)` and keeps concrete coordinate specializations as downstream bridges.
-/

namespace AffineMap

/-- The affine map cutting out the dual graph support in the conjugate of a partial-affine
support cut along `T.graph`. -/
def conjugateGraphMap (g : X →ᵃ[𝕜] 𝕜) (T : X →ᵃ[𝕜] Y) : Y⋆ →ᵃ[𝕜] X⋆ :=
  (-(LinearMap.dualMap T.linear)).toAffineMap +
    AffineMap.const 𝕜 Y⋆ g.linear

section Conjugate

variable [SupSet (WithTopBot 𝕜)]

/-- Text 12.3.1 in intrinsic affine-support form: the conjugate of a partial affine support cut on
the graph of `T` is again partial affine, now supported on the graph of the canonical dual affine
map `conjugateGraphMap g T`. -/
theorem convexConjugate_partialAffine_on_graph
    (g : X →ᵃ[𝕜] 𝕜) (T : X →ᵃ[𝕜] Y) :
    ((fun z : P ↦ g z.1).toWithTopBotOn T.graph)⋆ =
      (fun zStar : P⋆ ↦ ⟪T 0, zStar.2⟫ₚ - g 0).toWithTopBotOn
        (((conjugateGraphMap g T).graph).map (AffineEquiv.prodComm 𝕜 Y⋆ X⋆)) := sorry

end Conjugate

end AffineMap

end Graph

/-! ### Text_12_3_2 (from Chap03) -/
noncomputable section

open Matrix
open LinearMap.BilinMap
open scoped Rockafellar
open scoped RealInnerProductSpace

attribute [local instance] Classical.propDecidable

section

variable {𝕜 : Type*} [Semiring 𝕜]
variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E]

namespace LinearMap

/-- `T'` is a range pseudoinverse of `T` when both composites with `T` agree with a projection
onto `range(T)` in the canonical `LinearMap.IsProj` sense, and the image of `T'` lies in
`range(T)`. This owner is purely linear-algebraic and does not depend on any inner-product model.
-/
def IsRangePseudoinverse (T T' : E →ₗ[𝕜] E) : Prop :=
  ∃ p : E →ₗ[𝕜] E,
    LinearMap.IsProj T.range p ∧
      T ∘ₗ T' = p ∧
      T' ∘ₗ T = p ∧
      T'.range ≤ T.range

/-- The identity endomorphism is a range pseudoinverse of itself. -/
@[simp] theorem id_isRangePseudoinverse :
    (LinearMap.id : E →ₗ[𝕜] E).IsRangePseudoinverse (LinearMap.id : E →ₗ[𝕜] E) := by
  refine ⟨LinearMap.id, ?_, ?_, ?_, ?_⟩
  · simpa using (LinearMap.IsProj.top (S := 𝕜) (M := E))
  · simp
  · simp
  · exact le_rfl

end LinearMap

end

section

variable {𝕜 : Type*} [Field 𝕜]
variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E] [HasLinearPairing E E 𝕜]

local instance : HasPairing E E (WithTopBot 𝕜) := instHasPairingWithTopBot

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 12.3.2 computes the conjugate of a quadratic source function and then
  specializes to the matrix pseudoinverse formula.
- `core/canonical`: the owner abstractions are `convexConjugate`, `QuadraticForm 𝕜 E`,
  `LinearMap.halfPairingQuadratic`, `LinearMap.BilinMap.toQuadraticMap`, `HasLinearPairing`,
  `LinearMap.IsProj`, and `LinearMap.range`. The quadratic branch is therefore pairing-owned,
  not tied to one concrete self-dual inner-product model.
- `bridge/view`: real inner-product and Euclidean-matrix statements are downstream specializations
  of this pairing-level owner.

Domain-style sampling used here:
- `convexConjugate`;
- `QuadraticForm 𝕜 E`;
- `LinearMap.halfPairingQuadratic`;
- `LinearMap.BilinMap.toQuadraticMap`;
- `HasLinearPairing`;
- `LinearMap.IsProj`;
- `LinearMap.range`.

Primitive data vs derived API:
- primitive core data: a pairing `HasLinearPairing E E 𝕜`, an endomorphism `T`, its
  pseudoinverse candidate `T'`, and pairing-side nonnegativity of `x ↦ ⟪x, T x⟫ₚ`;
- owner-derived data: the quadratic form
  `(1 / 2 : 𝕜) • toQuadraticMap (HasLinearPairing.pairingLinear.compl₂ T)` and `T.range`;
- derived API: the piecewise conjugate formula, with real inner-product and matrix statements
  recovered as bridges.

Layer target: `core/canonical`. The source-facing theorem is kept at the pairing-level owner and
weaker scalar layer; concrete inner-product and matrix forms remain bridge declarations only.
-/

namespace LinearMap

/-- Pairing-root quadratic owner `x ↦ (1 / 2) ⟪x, T x⟫ₚ`, viewed in `WithTopBot 𝕜`. -/
def halfPairingQuadratic (T : E →ₗ[𝕜] E) : E → WithTopBot 𝕜 :=
  Function.toWithTopBot
    ((1 / 2 : 𝕜) •
      toQuadraticMap ((HasLinearPairing.pairingLinear : E →ₗ[𝕜] Module.Dual 𝕜 E).compl₂ T))

/-- Unfolding bridge for `halfPairingQuadratic`. -/
@[simp] theorem halfPairingQuadratic_eq_toWithTopBot (T : E →ₗ[𝕜] E) :
    halfPairingQuadratic T =
      ((⇑((1 / 2 : 𝕜) •
          toQuadraticMap
            ((HasLinearPairing.pairingLinear : E →ₗ[𝕜] Module.Dual 𝕜 E).compl₂ T))).toWithTopBot) :=
  rfl

-- Proof sketch: maximize the concave quadratic
-- `x ↦ ⟪xStar, x⟫ₚ - (1 / 2) ⟪x, T x⟫ₚ`.
/-- Pairing-level quadratic conjugate formula: for a pseudoinverse on `range(T)`, the Fenchel
conjugate of `x ↦ (1 / 2) ⟪x, T x⟫ₚ` is the corresponding pseudoinverse quadratic on `range(T)` and
`⊤` outside `range(T)`. -/
theorem convexConjugate_halfPairingQuadratic_eq_if_mem_range_of_isRangePseudoinverse
    (T T' : E →ₗ[𝕜] E)
    [Preorder 𝕜] [SupSet (WithTopBot 𝕜)]
    (hT_nonneg : ∀ x : E, 0 ≤ (⟪x, T x⟫ₚ : 𝕜))
    (hT' : T.IsRangePseudoinverse T') :
    (halfPairingQuadratic T)⋆ =
      fun xStar : E ↦
        if xStar ∈ T.range then
          halfPairingQuadratic T' xStar
        else ⊤ := by
  let _ := hT_nonneg
  let _ := hT'
  sorry

/-- Intrinsic full-range specialization of the quadratic conjugate formula: when `range(T) = ⊤`,
the outside branch disappears and the conjugate is exactly the pseudoinverse quadratic. -/
theorem convexConjugate_halfPairingQuadratic_eq_of_isRangePseudoinverse_of_range_eq_top
    (T T' : E →ₗ[𝕜] E)
    [Preorder 𝕜] [SupSet (WithTopBot 𝕜)]
    (hT_nonneg : ∀ x : E, 0 ≤ (⟪x, T x⟫ₚ : 𝕜))
    (hT' : T.IsRangePseudoinverse T')
    (hT_range : T.range = ⊤) :
    (halfPairingQuadratic T)⋆ = halfPairingQuadratic T' := by
  simpa [hT_range] using
    convexConjugate_halfPairingQuadratic_eq_if_mem_range_of_isRangePseudoinverse
      T T' hT_nonneg hT'

end LinearMap

end

section

variable {ι : Type*} [Fintype ι]

attribute [local instance] Classical.decEq

local notation "E" => EuclideanSpace ℝ ι
local notation "M" => Matrix ι ι ℝ

local instance : HasPairing E E (WithTopBot ℝ) := instHasPairingWithTopBot

/-!
Matrix specialization for Text 12.3.2.

- `source-facing`: the textbook statement is phrased for a symmetric positive semidefinite matrix
  `Q` and its Moore-Penrose pseudoinverse `Q'`.
- `core/canonical`: this is a bridge specialization of the pairing-level owner
  `LinearMap.halfPairingQuadratic` and the operator pseudoinverse relation on `Q.toEuclideanLin`.
- `bridge/view`: the declarations below are the Euclidean-matrix specializations of that owner and
  keep the source wording without reintroducing a parallel matrix-root definition.
-/

-- Proof sketch: specialize the operator-level quadratic-conjugate theorem to `Q.toEuclideanLin`
-- and `Q'.toEuclideanLin`, and obtain pairing-side nonnegativity from
-- `Matrix.isPositive_toEuclideanLin_iff`.
/-- Text 12.3.2: if `Q` is positive semidefinite and `Q'` is its Moore-Penrose pseudoinverse, then
the conjugate of `x ↦ (1 / 2) ⟪x, Qx⟫` is the quadratic function of `Q'` on `range(Q)` and `⊤`
outside `range(Q)`. -/
theorem convexConjugate_matrixQuadraticMap_eq_if_mem_range_of_isRangePseudoinverse
    (Q Q' : M) (hQ : Q.PosSemidef)
    (hQ' : Q.toEuclideanLin.IsRangePseudoinverse Q'.toEuclideanLin) :
    (LinearMap.halfPairingQuadratic Q.toEuclideanLin)⋆ =
      fun xStar : E ↦
        if xStar ∈ Q.toEuclideanLin.range then
          LinearMap.halfPairingQuadratic Q'.toEuclideanLin xStar
        else ⊤ := by
  have hQlin : Q.toEuclideanLin.IsPositive := by
    exact
      ((show Q.toEuclideanLin.IsPositive ↔ Q.PosSemidef from
          Matrix.isPositive_toEuclideanLin_iff).2 hQ)
  have hQ_nonneg : ∀ x : E, 0 ≤ (⟪x, Q.toEuclideanLin x⟫ₚ : ℝ) := by
    intro x
    simpa using hQlin.inner_nonneg_right x
  simpa using
    LinearMap.convexConjugate_halfPairingQuadratic_eq_if_mem_range_of_isRangePseudoinverse
      Q.toEuclideanLin Q'.toEuclideanLin hQ_nonneg hQ'

-- Proof sketch: for a positive-definite matrix, `Q.toEuclideanLin.range = ⊤`, so the outside
-- branch of the piecewise formula disappears. The Moore-Penrose pseudoinverse is then the
-- ordinary inverse matrix.
/-- In the positive-definite case, the conjugate of `x ↦ (1 / 2) ⟪x, Qx⟫` is the quadratic
function attached to `Q⁻¹`. -/
theorem convexConjugate_matrixQuadraticMap_eq_inverse {Q : M} (hQ : Q.PosDef) :
    (LinearMap.halfPairingQuadratic Q.toEuclideanLin)⋆ =
      LinearMap.halfPairingQuadratic (Q⁻¹).toEuclideanLin := by
  have hQlin : Q.toEuclideanLin.IsPositive := by
    exact
      ((show Q.toEuclideanLin.IsPositive ↔ Q.PosSemidef from
          Matrix.isPositive_toEuclideanLin_iff).2 hQ.posSemidef)
  have hQ_nonneg : ∀ x : E, 0 ≤ (⟪x, Q.toEuclideanLin x⟫ₚ : ℝ) := by
    intro x
    simpa using hQlin.inner_nonneg_right x
  have hQinv : Q.toEuclideanLin.IsRangePseudoinverse (Q⁻¹).toEuclideanLin := by
    sorry
  have hQrange : Q.toEuclideanLin.range = ⊤ := by
    sorry
  simpa using
    LinearMap.convexConjugate_halfPairingQuadratic_eq_of_isRangePseudoinverse_of_range_eq_top
      Q.toEuclideanLin (Q⁻¹).toEuclideanLin hQ_nonneg hQinv hQrange

end

/-! ### Text_12_3_3 (from Chap03) -/
noncomputable section

attribute [local instance] Classical.propDecidable

/-!
Source/core/bridge triage for this item.

- `source-facing`: the item identifies partial quadratic convex functions directly by the
  canonical support-cut presentation `branch.toWithTopBotOn M` with quadratic branch
  `branch x = Q x + φ x` on a nonempty affine support `M`.
- `core/canonical`: the owner predicates are the chapter declarations `Function.IsConvex` and
  `Function.IsProper`, the source-facing owner predicate `Function.IsPartiallyQuadratic`, the
  chapter support-cut owner `Function.toWithTopBotOn` together with its source-facing bridge
  `branch.toWithTopBot + δ(· | support)`, the codomain lift `Function.toWithTopBot`, together
  with the structural objects `QuadraticForm 𝕜 E`, `AffineSubspace 𝕜 E`, and `AffineMap 𝕜 E 𝕜`.
- `bridge/view`: coordinate finite-dimensional normal forms belong in downstream bridge files; this
  item keeps the source owner at the intrinsic support-cut layer and does not expose a `Fin n` API.
- Primitive data vs derived API:
  - primitive data: a `𝕜`-valued quadratic branch `fun x ↦ Q x + φ x` together with an affine
    support subspace `M`, with nonemptiness recorded intrinsically as `(M : Set E).Nonempty`;
  - owner-side consequences: `Function.IsConvex f` and `Function.IsProper f`;
  - derived API: the support-cut presentation
    `branch.toWithTopBotOn support`,
    and the owner consequences `f.IsConvex 𝕜` and `f.IsProper`.

Domain-style sampling used here:
- `QuadraticForm 𝕜 E` from mathlib;
- `AffineSubspace 𝕜 E` from mathlib;
- `AffineMap 𝕜 E 𝕜` from mathlib;
- `Function.toWithTopBotOn`, `indicatorFunction`, its notation `δ(· | C)`, and
  `Function.toWithTopBot` from the earlier chapter support-cut layer;
- `Function.isConvex_toWithTopBotOn_iff` from Remark 4.4.5.

Layer target:
- the source-facing owner layer is the predicate `Function.IsPartiallyQuadratic`, whose primitive
  content is the intrinsic support-cut presentation on the ordered commutative scalar module/affine
  ambient rather than a chosen finite-coordinate realization.
- this file keeps only that intrinsic owner layer; concrete coordinate normal forms are
  downstream bridge views.
-/

section Owner

variable {𝕜 : Type*} [CommRing 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]

namespace Function

variable {f : E → WithTopBot 𝕜}

section OwnerLayer

variable [LE 𝕜]

/-- Owner alias for partial quadratic functions: the canonical support-cut extension of a
nonnegative quadratic-plus-affine `𝕜`-branch to `WithTopBot 𝕜` along a nonempty affine
subspace. -/
abbrev IsPartiallyQuadratic (f : E → WithTopBot 𝕜) : Prop :=
  ∃ (Q : QuadraticForm 𝕜 E) (φ : E →ᵃ[𝕜] 𝕜) (M : AffineSubspace 𝕜 E),
    (∀ x, 0 ≤ Q x) ∧ (M : Set E).Nonempty ∧
      f = (fun x ↦ Q x + φ x).toWithTopBotOn M

/-- Text 12.3.3 at the intrinsic owner layer: a function is partially quadratic exactly when it
is a support-cut extension of a nonnegative quadratic-plus-affine branch along a nonempty affine
support subspace. -/
theorem isPartiallyQuadratic_iff
    (f : E → WithTopBot 𝕜) :
    f.IsPartiallyQuadratic ↔
      ∃ (Q : QuadraticForm 𝕜 E) (φ : E →ᵃ[𝕜] 𝕜) (M : AffineSubspace 𝕜 E),
        (∀ x, 0 ≤ Q x) ∧ (M : Set E).Nonempty ∧
          f = (fun x ↦ Q x + φ x).toWithTopBotOn M := by
  rfl

end OwnerLayer

namespace IsPartiallyQuadratic

section Convex

variable [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Any function admitting the source-facing partial-quadratic support-cut presentation is
convex. -/
theorem isConvex (hf : f.IsPartiallyQuadratic) :
    f.IsConvex 𝕜 := sorry

end Convex

section Proper

variable [Preorder 𝕜]

/-- Any function admitting the source-facing partial-quadratic support-cut presentation is
proper. -/
theorem isProper (hf : f.IsPartiallyQuadratic) :
    f.IsProper := sorry

end Proper

end IsPartiallyQuadratic

end Function

end Owner

/-! ### Theorem_12_3 (from Chap03) -/
noncomputable section

universe u v w

open scoped Rockafellar

section WithTopBotPairingCompat

variable {X : Type u} {Y : Type v} {α : Type w}
variable [HasPairing X Y α]

/-- Lift left-addition pairing compatibility from `α` to `WithTopBot α`. -/
instance instHasPairingAddLeftWithTopBot
    [Add X] [Add α] [HasPairingAddLeft X Y α] :
    HasPairingAddLeft X Y (WithTopBot α) where
  pairing_add_left x₁ x₂ y := by
    simpa [coe_add] using
      congrArg (fun t : α ↦ (t : WithTopBot α))
        (HasPairingAddLeft.pairing_add_left (X := X) (Y := Y) (𝕜 := α) x₁ x₂ y)

/-- Lift right-subtraction pairing compatibility from `α` to `WithTopBot α`. -/
instance instHasPairingSubRightWithTopBot
    [Sub Y] [AddGroup α] [HasPairingSubRight X Y α] :
    HasPairingSubRight X Y (WithTopBot α) where
  pairing_sub_right x y₁ y₀ := by
    simpa [coe_sub] using
      congrArg (fun t : α ↦ (t : WithTopBot α))
        (HasPairingSubRight.pairing_sub_right (X := X) (Y := Y) (𝕜 := α) x y₁ y₀)

end WithTopBotPairingCompat

section

variable {X : Type u} {Y : Type v} {α : Type w}
variable [SupSet (WithTopBot α)] [Add (WithTopBot α)] [Sub (WithTopBot α)]
variable [Sub X] [Sub Y]
variable [HasPairing X Y (WithTopBot α)]
variable [HasPairingAddLeft X Y (WithTopBot α)] [HasPairingSubRight X Y (WithTopBot α)]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 12.3 gives the affine-conjugation formula
  `(fun x ↦ h (A (x - a)) + ⟪x, a⋆⟫ₚ + β)⋆`.
- `core/canonical`: the owner declaration is `convexConjugate` on the pairing layer
  `HasPairing X Y (WithTopBot α)`, with chapter-facing codomain `WithTopBot α`, together with
  the minimal pairing-compatibility owners needed by the affine-shift algebra
  (`HasPairingAddLeft`, `HasPairingSubRight`).
- `bridge/view`: the textbook dual inverse `A^{*-1}` is modeled by an explicit dual-side
  bijection parameter `AStar.symm`, with the pairing-compatibility hypothesis
  `⟪A x, x⋆⟫ₚ = ⟪x, AStar x⋆⟫ₚ`.

Domain-style sampling used here:
- `convexConjugate` together with the chapter notation `f⋆`;
- `convexConjugate_eq_iSup_pairing_sub`;
- the pairing notation owner `⟪·, ·⟫ₚ`;
- dual-bijection transport on the dual side through `AStar`.

Primitive data vs derived API:
- primitive inputs: the `WithTopBot α`-valued function `h`, bijections `A` and `AStar`, the
  pairing-compatibility witness `hAStar`, the vectors `a`, `a⋆`, and the scalar shift `β`;
- primitive owner-side data already upstream: the conjugation operator on pairings;
- primitive compatibility owners used by the affine-shift formula:
  `HasPairingAddLeft X Y (WithTopBot α)` and `HasPairingSubRight X Y (WithTopBot α)`.
- derived API here: the single textbook affine-change formula for the transformed function.

Layer target: `source-facing`; this file keeps the textbook formula as the public theorem while
moving the owner to the intrinsic pairing layer and removing dependence on inner-product
self-duality.
-/

-- Proof sketch: expand both conjugates with `convexConjugate_eq_iSup_pairing_sub`; reindex the
-- primal variable by the translation `x ↦ x + a`; move the finite affine term outside the
-- supremum; and use the compatibility identity `hAStar` to rewrite the transformed pairing term
-- through `AStar.symm`.
theorem convexConjugate_affineChange
    (h : X → WithTopBot α) (A : X ≃ X) (AStar : Y ≃ Y)
    (hAStar : ∀ x xStar, ⟪A x, xStar⟫ₚ = ⟪x, AStar xStar⟫ₚ)
    (a : X) (aStar : Y) (β : WithTopBot α) :
    (fun x ↦ h (A (x - a)) + ⟪x, aStar⟫ₚ + β)⋆ =
      fun xStar ↦
        h⋆ (AStar.symm (xStar - aStar)) +
          (⟪a, xStar⟫ₚ - β - ⟪a, aStar⟫ₚ) := by
  sorry

end

/-! ### Text_12_3_4 (from Chap03) -/
noncomputable section

universe u v w

open scoped Rockafellar

section

variable {𝕜 : Type w} [AddCommGroup 𝕜] [ConditionallyCompleteLattice 𝕜]
variable [IsOrderedAddMonoid 𝕜]
variable {X : Type u} {Y : Type v}
variable [Zero X] [Zero Y]
variable [HasPairing X Y 𝕜] [HasPairing Y X 𝕜]

namespace Function

/-- `f` is zero-normalized when both its global infimum and its value at the origin are `0`. -/
def IsZeroNormalized (f : X → WithTopBot 𝕜) : Prop :=
  (⨅ x : X, f x) = 0 ∧ f 0 = 0

namespace IsZeroNormalized

variable (f : X → WithTopBot 𝕜)

-- Proof sketch: evaluate `convexConjugate_eq_iSup_pairing_sub` at `0` to rewrite `f⋆ 0` as the
-- supremum of `-f x`, then use `WithBotTop.negOrderIso.map_iInf` to identify that supremum with
-- `- (⨅ x, f x)`. Applying the same origin formula to `f⋆` on the dual side rewrites the infimum
-- of the conjugate in terms of `(f⋆)⋆` at `0`; the owner equation
-- `(f⋆)⋆ = f` then turns each pair of normalization
-- equalities into the other.
/-- Core normalization bridge on dual pairings: if `f` equals its dual Fenchel biconjugate, then
`inf_x f(x) = f(0) = 0` is equivalent to `inf_y f*(y) = f*(0) = 0`. -/
theorem iff_conjugate_of_eq_dual_biconjugate
    (hf_biconj : (f⋆)⋆ = f)
    [HasPairingZeroRight X Y 𝕜] [HasPairingZeroRight Y X 𝕜] :
    f.IsZeroNormalized ↔ (f⋆).IsZeroNormalized := by
  have hneg_iInf_X (g : X → WithTopBot 𝕜) : - (⨅ x : X, g x) = ⨆ x : X, -g x := by
    exact congrArg OrderDual.ofDual (WithBotTop.negOrderIso.map_iInf fun x ↦ g x)
  have hneg_iInf_Y (g : Y → WithTopBot 𝕜) : - (⨅ y : Y, g y) = ⨆ y : Y, -g y := by
    exact congrArg OrderDual.ofDual (WithBotTop.negOrderIso.map_iInf fun y ↦ g y)
  have hconj_zero : f⋆ (0 : Y) = - (⨅ x : X, f x) := by
    calc
      f⋆ (0 : Y) = ⨆ x : X, ⟪x, (0 : Y)⟫ₚ - f x := by
        rw [convexConjugate_eq_iSup_pairing_sub]
      _ = ⨆ x : X, (((⟪x, (0 : Y)⟫ₚ : 𝕜) : WithTopBot 𝕜) - f x) := by
        rfl
      _ = ⨆ x : X, -f x := by
        refine iSup_congr ?_
        intro x
        simp
      _ = - (⨅ x : X, f x) := by
        exact (hneg_iInf_X f).symm
  have hconj_conj_zero : (f⋆)⋆ 0 = - (⨅ y : Y, f⋆ y) := by
    calc
      (f⋆)⋆ 0 = ⨆ y : Y, ⟪y, (0 : X)⟫ₚ - f⋆ y := by
        simpa using convexConjugate_convexConjugate_eq_iSup_pairing_sub (f := f) (x := (0 : X))
      _ = ⨆ y : Y, (((⟪y, (0 : X)⟫ₚ : 𝕜) : WithTopBot 𝕜) - f⋆ y) := by
        rfl
      _ = ⨆ y : Y, -f⋆ y := by
        refine iSup_congr ?_
        intro y
        simp
      _ = - (⨅ y : Y, f⋆ y) := by
        exact (hneg_iInf_Y f⋆).symm
  constructor
  · rintro ⟨hinf, hzero⟩
    refine ⟨?_, ?_⟩
    · have hneg : -f 0 = ⨅ y : Y, f⋆ y := by
        simpa [hf_biconj] using congrArg Neg.neg hconj_conj_zero
      simpa [hzero] using hneg.symm
    · simpa [hinf] using hconj_zero
  · rintro ⟨hinf_conj, hzero_conj⟩
    refine ⟨?_, ?_⟩
    · have hneg : -f⋆ (0 : Y) = ⨅ x : X, f x := by
        simpa using congrArg Neg.neg hconj_zero
      simpa [hzero_conj] using hneg.symm
    · have hzero : f 0 = - (⨅ y : Y, f⋆ y) := by
        simpa [hf_biconj] using hconj_conj_zero
      simpa [hinf_conj] using hzero

end IsZeroNormalized

end Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 12.3.4 states that for a closed convex function on `R^n`, the
  normalization condition `inf_x f(x) = f(0) = 0` is equivalent to the same normalization
  condition for the conjugate `f*`. The source's separate properness hypothesis is redundant here,
  because either normalization clause already forces properness.
- `core/canonical`: the chapter owner for conjugation is `convexConjugate`, and the canonical Lean
  form of the global infimum is the complete-lattice expression `⨅ x, f x` on each pairing side.
- `bridge/view`: the textbook proof uses the chapter bridge
  `convexConjugate_eq_iSup_pairing_sub` at `0`, together with the order-isomorphism identity
  `WithBotTop.negOrderIso.map_iInf`; concrete closed-convex self-pairing specializations are
  obtained upstream from the dual biconjugacy owner equation.

Domain-style sampling used here:
- `convexConjugate` and `convexConjugate_eq_iSup_pairing_sub` from `Defn_12_2`;
- the dual pairing owners `HasPairing X Y 𝕜` and `HasPairing Y X 𝕜`;
- the primitive zero-pairing owner assumptions on both pairing orientations;
- the dual biconjugacy owner hypothesis `(f⋆)⋆ = f`.

Primitive data vs derived API:
- primitive input: a function `f : X → WithTopBot 𝕜`;
- primitive owner hypothesis for the core theorem:
  `(f⋆)⋆ = f`;
- primitive pairing bridges used at the theorem surface:
  `[HasPairingZeroRight X Y 𝕜]` and `[HasPairingZeroRight Y X 𝕜]`;
- source-facing normalization owner:
  `f.IsZeroNormalized` and `(f⋆).IsZeroNormalized`;
- derived API: the chapter-facing long-name restatement on the self-pairing specialization.

Layer target: `core/canonical` and `source-facing` aligned: the core theorem is now on the
primitive dual-biconjugate owner layer, and concrete closed-convex self-pairing hypotheses are
handled upstream.
-/

variable {E : Type u} [Zero E] [HasPairing E E 𝕜]

/-- Self-pairing specialization of the dual normalization bridge under `f⋆⋆ = f`. -/
theorem
    Function.IsZeroNormalized.iff_conjugate_of_eq_biconjugate
    (f : E → WithTopBot 𝕜) (hf_biconj : f⋆⋆ = f)
    [HasPairingZeroRight E E 𝕜] :
    f.IsZeroNormalized ↔ (f⋆).IsZeroNormalized := by
  have hf_biconj' : (f⋆)⋆ = f := by
    simpa [convexBiconjugate] using hf_biconj
  simpa using
    (Function.IsZeroNormalized.iff_conjugate_of_eq_dual_biconjugate
      (f := f) hf_biconj')

/-- Chapter-facing normalization equivalence under the canonical biconjugacy owner equation.
This keeps the historical theorem name while exposing the abstraction layer directly. -/
theorem infimum_and_origin_value_eq_zero_iff_conjugate_infimum_and_origin_value_eq_zero
    (f : E → WithTopBot 𝕜) (hf_biconj : f⋆⋆ = f)
    [HasPairingZeroRight E E 𝕜] :
    f.IsZeroNormalized ↔ (f⋆).IsZeroNormalized := by
  simpa using
    (Function.IsZeroNormalized.iff_conjugate_of_eq_biconjugate
      f hf_biconj)

end

/-! ### Text_12_3_5 (from Chap03) -/
noncomputable section

open scoped RealInnerProductSpace
open scoped Rockafellar

universe u v

section

variable {E : Type u} [SeminormedAddGroup E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 12.3.5 characterizes the functions on a real Euclidean space invariant
  under all orthogonal transformations as exactly the functions factoring through the Euclidean
  norm, and then characterizes which such radial functions are closed proper convex.
- `core/canonical`: the owner abstractions are `LinearIsometryEquiv` for orthogonal
  transformations, the norm `‖x‖`, the canonical nonnegative-ray type `NNReal`,
  ray, `ConvexOn ℝ (Set.Ici (0 : ℝ))` for convexity of the radial profile, `Monotone`,
  `LowerSemicontinuous`, and `Function.IsClosedProperConvex`.
- `bridge/view`: the textbook profile `g : [0, +∞) → ...` is encoded directly as a function on the
  type `NNReal`, and its ambient-line convexity is expressed by the canonical bridge
  `Function.extendByTop`.

Domain-style sampling used here:
- `LinearIsometryEquiv.norm_map`;
- `reflection_sub`, which gives an orthogonal map sending one vector to another of the same norm;
- `ConvexOn` on `Set.Ici (0 : ℝ)`;
- `Monotone` and `LowerSemicontinuous` on `NNReal`;
- the chapter predicate `Function.IsClosedProperConvex`.

Primitive data vs derived API:
- primitive bridge data: `radialExtension`;
- source-facing ray-side owner:
  `Function.IsMonotoneClosedConvexOnNonnegativeRay`, bundling lower semicontinuity and
  monotonicity on `NNReal`, finiteness at the origin, and convexity of the canonical ambient-line
  extension on `Set.Ici (0 : ℝ)`;
- derived API: the orthogonal-invariance characterization and the closed-proper-convex
  characterization for radial extensions.

Layer target: `source-facing`; the item is stated directly in terms of orthogonal invariance, the
norm, and one-variable radial profiles. The radial-extension owner itself lives on the
minimal seminormed-space layer, the orthogonal-invariance theorem refines the ambient `R^n` source
semantics to the intrinsic real inner-product-space level, and the closed-proper-convex theorem
lives on the weaker real normed-space layer already used by `ConvexOn`, `LowerSemicontinuous`, and
`Function.IsClosedProperConvex`.
-/

/-- The radial extension of a function on `[0, +∞)` to a seminormed additive group, obtained by
composing with the norm. -/
def radialExtension (E : Type u) [SeminormedAddGroup E] {α : Type v}
    (g : NNReal → α) : E → α :=
  fun x ↦ g ‖x‖₊

-- Proof sketch: unfold `radialExtension`; the value at `x` is, by definition, the profile `g`
-- evaluated at the nonnegative radius `‖x‖`.
/-- Evaluating the radial extension at `x` means evaluating the profile at the radius `‖x‖`. -/
@[simp] theorem radialExtension_apply {α : Type v} (g : NNReal → α) (x : E) :
    radialExtension E g x = g ‖x‖₊ :=
  rfl

end

section

namespace Function

/-- A `WithTopBot α`-valued profile on `[0, +∞)` is lower semicontinuous and nondecreasing on the
ray subtype, its canonical ambient-line extension `Function.extendByTop g` is convex on the ray,
and its value at the origin is finite. -/
class IsMonotoneClosedConvexOnNonnegativeRay
    {α : Type v} [TopologicalSpace (WithTopBot α)] [AddCommMonoid α] [SMul ℝ α]
    [PartialOrder (WithTopBot α)]
    (g : NNReal → WithTopBot α) : Prop where
  lowerSemicontinuous : LowerSemicontinuous g
  convexOn : ConvexOn ℝ (Set.Ici (0 : ℝ)) (Function.extendByTop g)
  finite_zero : ⊥ < g 0 ∧ g 0 < ⊤
  monotone : Monotone g

end Function

-- Proof sketch: the zero profile on `[0, +∞)` is constant, hence monotone, convex, and lower
-- semicontinuous; its value at the origin is the finite extended value `0`.
/-- The zero profile is a canonical monotone closed convex profile on `[0, +∞)`. -/
instance instIsMonotoneClosedConvexOnNonnegativeRayZero :
    Function.IsMonotoneClosedConvexOnNonnegativeRay
      (fun _ : NNReal ↦ (0 : WithTopBot ℝ)) := sorry

end

section

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Proof sketch: for `→`, evaluate the invariance condition along orthogonal maps sending a fixed
-- vector to another vector with the same norm, so `f` depends only on `‖x‖`. For `←`, a radial
-- extension is unchanged by every orthogonal transformation because such maps preserve norms.
/-- Text 12.3.5: a function on a real inner-product space is invariant under every orthogonal
transformation if and only if it is the radial extension of a profile on `[0, +∞)`. -/
theorem orthogonallyInvariant_iff_exists_radialExtension
    {α : Type v} (f : E → α) :
    (∀ U : E ≃ₗᵢ[ℝ] E, f ∘ U = f) ↔
      ∃ g : NNReal → α, f = radialExtension E g := sorry

end

section

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)

-- Proof sketch: when the ambient space is nontrivial, restrict the radial extension to the ray
-- `t ↦ t • e` for a unit vector `e`, obtaining the scalar profile, then use convexity,
-- lower semicontinuity, and
-- properness of `f` together with radial symmetry to derive the four listed ray conditions. For
-- `←`, compose a monotone closed convex ray profile with the norm; the norm is convex
-- and continuous, and monotonicity of the profile upgrades convexity along radii to convexity on
-- all of the ambient space. The nontriviality hypothesis excludes the degenerate zero space, where
-- `radialExtension g` depends only on `g 0`.
/-- In a nontrivial real normed space, a radial extension `x ↦ g(‖x‖)` is closed proper
convex exactly when
the profile `g` is convex on `[0, +∞)`, nondecreasing, lower semicontinuous, and finite at `0`. -/
theorem radialExtension_isClosedProperConvex_iff
    {α : Type v} [TopologicalSpace (WithTopBot α)] [AddCommMonoid α] [SMul ℝ α]
    [PartialOrder (WithTopBot α)]
    [Nontrivial E] (g : NNReal → WithTopBot α) :
    IsClosedProperConvex[ℝ] (radialExtension E g) ↔
      g.IsMonotoneClosedConvexOnNonnegativeRay := sorry

end

/-! ### Text_12_3_6 (from Chap03) -/
noncomputable section

universe u v

open scoped RealInnerProductSpace Rockafellar

section

variable {𝕜 : Type*} {E : Type u} {α : Type v}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [TopologicalSpace E] [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommMonoid α] [SMul 𝕜 α] [Preorder α]

/-!
Core owner triage for the closed/proper/convex predicate used throughout Chapter 12.

- `core/canonical`: the owner abstraction is the class `f.IsClosedProperConvex`, bundling the
  chapter predicates `f.IsConvex` and `f.IsProper` with mathlib's `LowerSemicontinuous`, on a
  topological `𝕜`-module and the canonical extended codomain layer `WithTopBot α`.
- primitive data: the function `f : E → WithTopBot α`;
- derived API: the projection lemmas extracting convexity, properness, and lower semicontinuity.

Domain-style sampling used here:
- the chapter owner `Function.IsConvex` from `Chap01/Theorem_4_2`, which already lives on the
  additive-module layer;
- the chapter owner `Function.IsProper` from `Chap01/Definition_4_6`, which adds no ambient
  structure;
- mathlib's `LowerSemicontinuous` from `Topology/Semicontinuity/Defs`, which only needs a
  topological domain.

Layer target: `core/canonical`; this owner is chapter-wide and is not part of the later
orthant-specific `R^n` bridge layer.
-/

namespace Function

variable (𝕜)
/-- A `WithTopBot α`-valued function on a topological `𝕜`-module is closed proper convex when it is
convex, proper, and lower semicontinuous. -/
class IsClosedProperConvex [TopologicalSpace (WithTopBot α)] (f : E → WithTopBot α) : Prop where
  convex : f.IsConvex 𝕜
  proper : f.IsProper
  closed : LowerSemicontinuous f

variable [TopologicalSpace (WithTopBot α)]
local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

/-- The closed-proper-convex owner expands to convexity, properness, and lower semicontinuity. -/
theorem isClosedProperConvex_iff (f : E → WithTopBot α) :
    IsClosedProperConvex[𝕜] f ↔
      f.IsConvex 𝕜 ∧ f.IsProper ∧ LowerSemicontinuous f := by
  constructor
  · intro hf
    exact ⟨hf.convex, hf.proper, hf.closed⟩
  · rintro ⟨hconvex, hproper, hlowerSemicontinuous⟩
    exact ⟨hconvex, hproper, hlowerSemicontinuous⟩

namespace IsClosedProperConvex

/-- Lower semicontinuity extracted from the closed-proper-convex owner. -/
theorem lowerSemicontinuous {f : E → WithTopBot α}
    (hf : IsClosedProperConvex[𝕜] f) :
    LowerSemicontinuous f :=
  hf.closed

end IsClosedProperConvex

end Function

end

section

variable {𝕜 : Type*} {E : Type u} {α : Type v}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [TopologicalSpace E] [AddCommMonoid E] [SMul 𝕜 E]
variable [TopologicalSpace (WithTopBot α)] [AddCommMonoid α] [Preorder α]
variable [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α]
local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

/-- The indicator of a nonempty closed convex set is a closed proper convex function. -/
theorem indicatorFunction_isClosedProperConvex_of_nonempty
    {C : Set E} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C) :
    IsClosedProperConvex[𝕜] (δ[α](· | C)) := by
  rw [Function.isClosedProperConvex_iff (𝕜 := 𝕜)]
  refine ⟨(indicator_isConvex_iff (𝕜 := 𝕜) (α := α) C).2 hC_convex, ?_, ?_⟩
  · rw [Function.isProper_iff]
    refine ⟨?_, ?_⟩
    · rcases hC_nonempty with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      simpa [hx] using (show (0 : WithTopBot α) < ⊤ by simp)
    · intro x
      by_cases hx : x ∈ C <;> simp [hx]
  · have hC_open_compl : IsOpen Cᶜ := hC_closed.isOpen_compl
    simpa [indicator_eq_setIndicator_compl_top] using
      hC_open_compl.lowerSemicontinuous_indicator
        (show (0 : WithTopBot α) ≤ ⊤ by simp)

end

section

variable {ι : Type u} {𝕜 : Type*}
variable [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

local notation "E" => ι → 𝕜
local notation "Quadrant" => orthant[𝕜](E)

/-- The distinguished origin point in the nonnegative orthant subtype. -/
def orthantOrigin : Quadrant :=
  ⟨0, by
    change (0 : E) ≤ 0
    exact le_rfl⟩

@[simp] theorem orthantOrigin_fst : (orthantOrigin : Quadrant).1 = 0 := rfl

/-!
Source/core/bridge triage for this item.

- `source-facing`: the item studies functions on `ℝ^n` of the form `f(x) = g(|x|)`, where `|x|`
  means coordinatewise absolute value and `g` is defined on the nonnegative orthant.
- `core/canonical`: the owner abstractions already present in the project are
  `Quadrant`, surfaced as `orthant[𝕜](E)`,
  `Function.IsConvex`, `Function.IsProper`, `LowerSemicontinuous`, `ConvexOn`, and
  `convexConjugate`.
- `bridge/view`: the source orthant profile is best treated as a function
  `Quadrant → WithTopBot α`; clause (2) uses the same codomain layer for conjugation.
  The upstream bridge `Function.extendByTop` from Definition 12.4
  extends an orthant function by `⊤` off the orthant, while `orthantAbsExtension` composes it
  with `coordinatewiseAbsQuadrant`.

Primitive data vs derived API:
- primitive source-facing data: `coordinatewiseAbsQuadrant`, `orthantAbsExtension`, and the
  orthant-native owner `IsMonotoneClosedConvexOnQuadrant g`, whose primitive fields are lower
  semicontinuity of `g`, intrinsic convexity of `g` on the orthant subtype, finiteness of `g` at
  `0`, and the genuinely extra orthant-order monotonicity condition;
- derived bridge API: the orthant evaluation lemmas for `Function.extendByTop`, the
  bridge from intrinsic orthant convexity of `g` to convexity of `Function.extendByTop g` on the
  orthant set,
  ambient closed/proper/convex bridge
  `IsMonotoneClosedConvexOnQuadrant.extendByTop_isClosedProperConvex`, the source-facing
  closed-proper-convex equivalence, and the conjugate formula through the inherited orthant-side
  Fenchel owner `convexConjugate g`.

Layer target: this item stays `source-facing`. The main declarations remain the equivalence for
`f(x) = g(|x|)` and the conjugate formula, while reusing the canonical project owners for convexity,
closedness, properness, the orthant order, and Fenchel conjugation.
-/

/-- The point `|x|`, regarded as a point of the canonical nonnegative orthant subtype. -/
def coordinatewiseAbsQuadrant (x : E) : Quadrant :=
  ⟨fun i ↦ |x i|, fun i ↦ abs_nonneg (x i)⟩

/-- The canonical orthant absolute-value map is coordinatewise absolute value. -/
@[simp] theorem coordinatewiseAbsQuadrant_apply (x : E) (i : ι) :
    (coordinatewiseAbsQuadrant x).1 i = |x i| :=
  rfl

@[simp] theorem coordinatewiseAbsQuadrant_zero :
    coordinatewiseAbsQuadrant (0 : E) = orthantOrigin := by
  ext i
  simp [coordinatewiseAbsQuadrant]

/-- The extension of a function on the nonnegative orthant to all of `R^n` by composition with the
coordinatewise absolute value map. -/
def orthantAbsExtension {β : Type*} (g : Quadrant → β) : E → β :=
  g ∘ coordinatewiseAbsQuadrant

section ClosedProperConvex

variable {α : Type v}
variable [TopologicalSpace (ι → 𝕜)]
variable [TopologicalSpace (WithTopBot α)] [AddCommMonoid α] [SMul 𝕜 α]
variable [PartialOrder α]
local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)
namespace Function

/-- A function on the nonnegative orthant has the Chapter 12 orthant profile when its canonical
ambient `⊤`-extension is used only as derived bridge API. Primitive owner data are lower
semicontinuity and intrinsic convexity of the orthant function itself, origin finiteness, and
orthant-order monotonicity. -/
class IsMonotoneClosedConvexOnQuadrant (g : Quadrant → WithTopBot α) : Prop where
  lowerSemicontinuous : LowerSemicontinuous g
  convex : g.IsConvex 𝕜
  finite_origin : ⊥ < g orthantOrigin ∧ g orthantOrigin < ⊤
  monotone : Monotone g

namespace IsMonotoneClosedConvexOnQuadrant

variable [SMul 𝕜 (WithTopBot α)]
variable [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α]

/-- Bridge API: intrinsic convexity of an orthant function yields convexity of its canonical
ambient `⊤`-extension on the orthant set. -/
theorem convexOn_extendByTop {g : Quadrant → WithTopBot α}
    (hg : g.IsMonotoneClosedConvexOnQuadrant) :
    ConvexOn 𝕜 Quadrant (Function.extendByTop g) := by
  sorry

/-- The orthant owner canonically upgrades to the ambient closed-proper-convex owner on the
`⊤`-extension `Function.extendByTop g`. -/
theorem extendByTop_isClosedProperConvex {g : Quadrant → WithTopBot α}
    (hg : g.IsMonotoneClosedConvexOnQuadrant) :
    IsClosedProperConvex[𝕜] (Function.extendByTop g) := by
  sorry

end IsMonotoneClosedConvexOnQuadrant

end Function

variable [SMul 𝕜 (WithTopBot α)]
variable [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α]

-- Proof sketch: for the forward implication, restrict `f(x) = g(|x|)` to the nonnegative
-- orthant to recover `g`, then use symmetry under sign changes and convexity to obtain orthant
-- monotonicity and finiteness at `0`. For the reverse implication, compose `g` with the
-- coordinatewise absolute value map, using convexity and lower semicontinuity of `g` on the
-- orthant together with orthant monotonicity to transfer those properties to all of `R^n`, and use
-- finiteness at `0` to obtain properness.
/-- Text 12.3.6 (1): for `f(x) = g(|x|)`, the function `f` is closed proper convex on `R^n` if and
only if `g` is lower semicontinuous and convex on the nonnegative orthant, is finite at `0`, and
is nondecreasing for the orthant order there. -/
theorem orthantAbsExtension_isClosedProperConvex_iff
    (g : Quadrant → WithTopBot α) :
    IsClosedProperConvex[𝕜] (orthantAbsExtension g) ↔
      g.IsMonotoneClosedConvexOnQuadrant := sorry

end ClosedProperConvex

-- Proof sketch: write the Fenchel conjugate of `orthantAbsExtension g` as the supremum of
-- `⟪x⋆, x⟫ - g(|x|)` over all `x`. For fixed `x⋆`, choose the sign of each coordinate of `x` to
-- match the sign of `x⋆`, so the pairing becomes `⟪|x⋆|, |x|⟫`; then rename `|x|` as a vector in
-- the nonnegative orthant. The resulting supremum is exactly the orthant Fenchel conjugate
-- `convexConjugate g` of the restricted orthant function, evaluated at `|x⋆|` as an orthant
-- point; no extra closedness,
-- convexity, or monotonicity hypothesis on `g` enters this algebraic identity.
/-- Text 12.3.6 (2): the conjugate of `x ↦ g(|x|)` is the orthant Fenchel conjugate
`convexConjugate g`
restricted to the nonnegative orthant, evaluated at the coordinatewise absolute value of the dual
variable. In particular, this identity applies under the orthant-side hypotheses of clause (1). -/
theorem convexConjugate_orthantAbsExtension_eq_convexConjugate_comp_coordinatewiseAbsQuadrant
    {α : Type v} [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [IsOrderedAddMonoid α]
    [HasPairing E E (WithTopBot α)]
    [HasPairing Quadrant Quadrant (WithTopBot α)]
    (g : Quadrant → WithTopBot α) :
    (orthantAbsExtension g)⋆ = (g⋆) ∘ coordinatewiseAbsQuadrant := sorry

end
