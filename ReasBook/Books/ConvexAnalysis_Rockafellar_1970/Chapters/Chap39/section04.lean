import Mathlib
import Mathlib.Analysis.InnerProductSpace.PiL2

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_39_4_1 (from Chap08) -/
noncomputable section

open scoped Rockafellar SetRel

universe u v w z

namespace SetRel

section PrimalDualExtrema

variable {U : Type u} {X : Type v}

section Primal

variable {𝕜 : Type*} {XStar : Type w}
variable [ConditionallyCompleteLattice 𝕜] [HasPairing XStar X 𝕜]

-- Proof sketch: unfold `supremumProcessPairing` as the support function of the fiber
-- `A.image ({u} : Set U)`, then apply `supportFunction_def`.
/-- For fixed `u` and `xStar`, the supremum-oriented process pairing `⟨Au, xStar⟩` is the
supremum of the linear functional `x ↦ ⟪xStar, x⟫ₚ` over the fiber
`A.image ({u} : Set U)`. -/
theorem supremumProcessPairing_eq_iSup_pairing_over_fiber
    (A : SetRel U X) (u : U) (xStar : XStar) :
    supremumProcessPairing 𝕜 XStar A u xStar =
      ⨆ x : A.image ({u} : Set U), (⟪xStar, (x : X)⟫ₚ : WithBotTop 𝕜) := sorry

end Primal

section Dual

variable {𝕜 : Type*} {XStar : Type w} {UStar : Type z}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [Neg UStar] [HasPairing U UStar 𝕜] [HasPairing X XStar 𝕜]

-- Proof sketch: unfold `supremumAdjointProcessPairing` to the Chapter 34 upper representative of
-- the same fiber-indicator kernel, then rewrite the resulting adjoint-side pairing as the infimum
-- of `uStar ↦ ⟪u, uStar⟫ₚ` over the adjoint fiber
-- `((A∗[XStar, UStar; 𝕜]).image ({xStar} : Set XStar))`.
/-- The dual Chapter 39 pairing `⟨u, A⋆ xStar⟩` is the infimum of the linear functional
`uStar ↦ ⟪u, uStar⟫ₚ` over the adjoint fiber
`((A∗[XStar, UStar; 𝕜]).image ({xStar} : Set XStar))`.
-/
theorem supremumAdjointProcessPairing_eq_iInf_pairing_over_adjointFiber
    (A : SetRel U X) (u : U) (xStar : XStar) :
    supremumAdjointProcessPairing 𝕜 XStar UStar A u xStar =
      ⨅ uStar : (A∗[XStar, UStar; 𝕜]).image ({xStar} : Set XStar),
        (⟪u, (uStar : UStar)⟫ₚ : WithBotTop 𝕜) := sorry

end Dual

section PrimalDualRelation

variable {𝕜 : Type*} {XStar : Type w} {UStar : Type z}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [Neg UStar] [HasPairing U UStar 𝕜]
variable [HasPairing X XStar 𝕜] [HasPairing XStar X 𝕜]

-- Proof sketch: rewrite the primal and dual sides using the two preceding fiber formulas, then
-- substitute the assumed equality
-- `supremumProcessPairing 𝕜 XStar A u xStar =
--   supremumAdjointProcessPairing 𝕜 XStar UStar A u xStar`.
/-- Equality of the primal and dual Chapter 39 pairings is exactly the corresponding primal-dual
extremum relation between the supremum over the primal fiber and the infimum over the adjoint
fiber. -/
theorem primal_dual_extremum_relation_of_pairing_eq
    (A : SetRel U X) (u : U) (xStar : XStar)
    (hEq : supremumProcessPairing 𝕜 XStar A u xStar =
      supremumAdjointProcessPairing 𝕜 XStar UStar A u xStar) :
    (⨆ x : A.image ({u} : Set U), (⟪xStar, (x : X)⟫ₚ : WithBotTop 𝕜)) =
      ⨅ uStar : (A∗[XStar, UStar; 𝕜]).image ({xStar} : Set XStar),
        (⟪u, (uStar : UStar)⟫ₚ : WithBotTop 𝕜) := sorry

end PrimalDualRelation

section Polyhedral

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable {UStar : Type z} [AddCommMonoid UStar] [Module 𝕜 UStar]
variable {XStar : Type w}
variable [HasPairing U UStar 𝕜] [HasPairing X XStar 𝕜]
variable {Y : Type _} [HasPairing (U × X) Y 𝕜]

-- Proof sketch: view the primal fiber and the adjoint fiber as coordinate slices of the
-- polyhedral graphs of `A` and `A∗[XStar, UStar; 𝕜]`. Slicing a polyhedral graph by a singleton
-- coordinate constraint yields a polyhedral feasible set, so the displayed primal and dual
-- extremum problems have polyhedral feasible regions.
/-- If `A` is polyhedral, then both the primal fiber `A.image ({u} : Set U)` and the dual adjoint
fiber `((A∗[XStar, UStar; 𝕜]).image ({xStar} : Set XStar))` are polyhedral. Hence the two displayed
extremum problems are linear-function-over-polyhedron problems. -/
theorem primal_and_dual_fibers_are_polyhedral_of_isPolyhedralProcess
    (A : SetRel U X) (hA : A.IsPolyhedralProcess 𝕜 Y) (u : U) (xStar : XStar) :
    (A.image ({u} : Set U)).IsPolyhedral 𝕜 ∧
      ((A∗[XStar, UStar; 𝕜]).image ({xStar} : Set XStar)).IsPolyhedral 𝕜 := sorry

end Polyhedral

end PrimalDualExtrema

end SetRel

/-! ### Proposition_39_4_2 (from Chap08) -/
noncomputable section

open scoped Rockafellar SetRel

universe u

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 39.4.2 computes the supremum-oriented pairing, the adjoint fiber,
  and the inverse-adjoint fiber for the Chapter 39 process attached to a linear map
  `B : ℝⁿ → ℝⁿ`, namely `u ↦ {x | x ≤ B u}` on the nonnegative orthant and `∅` elsewhere.
- `core/canonical`: the chapter already owns this process as `Function.lowerSetProcess B`, the
  supremum pairing as `SetRel.supremumProcessPairing`, and process adjoints as `A∗[...]`.
- `bridge/view`: the process owner is function-level, while the Hilbert adjoint is canonical on
  the Euclidean-space model `EuclideanSpace ℝ ι`. The needed coordinate-space bridge is therefore
  the thin owner-level transport `LinearMap.euclideanAdjoint`, which keeps
  `EuclideanSpace.equiv` internal and leaves the source-facing theorems stated on `B` itself.

Primary mathematical domain:
- convex processes on finite coordinate spaces and their adjoint fibers.

Domain-style sampling used here:
- `Function.lowerSetProcess` from `Example_39_0_3`;
- `SetRel.supremumProcessPairing` from `Definition_39_2_1`;
- `SetRel.adjoint` / `A∗[...]` from `Definition_39_0_14`;
- `LinearMap.adjoint` from mathlib's inner-product operator API.

Primitive data vs derived API:
- primitive source data: a finite index type `ι` and a linear map
  `B : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)`, representing the same finite-dimensional linear datum as the
  textbook map `ℝⁿ → ℝⁿ`;
- reused owner data: the process `Function.lowerSetProcess B`;
- bridge data: the coordinate-space adjoint bridge `B.euclideanAdjoint`;
- derived API: the source pairing case formulas, the two adjoint-fiber cases, and the
  inverse-adjoint fiber formula, where the source `B*` is rendered by `B.euclideanAdjoint`.

Layer target: `source-facing`, stated directly on the existing owners
`Function.lowerSetProcess B`, `supremumProcessPairing`, and `A∗[...]`, with the Euclidean adjoint
passage hidden in the owner-level bridge `LinearMap.euclideanAdjoint`.
-/

namespace LinearMap

section

variable {ι : Type u} [Fintype ι]

/-- The Euclidean adjoint of a coordinate linear map `B : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)`, obtained by
transporting the canonical Hilbert adjoint on `EuclideanSpace ℝ ι` along
`EuclideanSpace.equiv ι ℝ`. This is the coordinate-space bridge for the source notation `B*`. -/
abbrev euclideanAdjoint
    (B : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  let e := (EuclideanSpace.equiv ι ℝ).toLinearEquiv
  (e.arrowCongr e) (((e.symm.arrowCongr e.symm) B).adjoint)

-- Proof sketch: when `u ≥ 0`, Example 39.0.3 identifies the fiber with `Set.Iic (B u)`. For a
-- nonnegative `x⋆`, the support over that lower set is attained at the endpoint `B u`, giving the
-- value `⟪x⋆, B u⟫ₚ`.
/-- Proposition 39.4.2 (1): if `u` and `x⋆` are both nonnegative, then the
supremum-oriented process pairing of `Function.lowerSetProcess B` is exactly `⟪B u, x⋆⟫`. -/
theorem supremumProcessPairing_lowerSetProcess_of_nonneg
    (B : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) {u xStar : ι → ℝ}
    (hu : 0 ≤ u) (hxStar : 0 ≤ xStar) :
    SetRel.supremumProcessPairing ℝ (ι → ℝ) (Function.lowerSetProcess B) u xStar =
      ((⟪xStar, B u⟫ₚ : ℝ) : WithBotTop ℝ) := sorry

-- Proof sketch: for `u ≥ 0`, the fiber is again `Set.Iic (B u)`. If `x⋆` has a negative
-- coordinate, moving the corresponding primal coordinate to `-∞` inside that lower set forces the
-- supremum to `⊤`.
/-- Proposition 39.4.2 (2): if `u` is nonnegative but `x⋆` is not, then the
supremum-oriented process pairing of `Function.lowerSetProcess B` is `+∞`, written as `⊤` in
`WithBotTop ℝ`. -/
theorem supremumProcessPairing_lowerSetProcess_of_nonneg_of_not_nonneg
    (B : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) {u xStar : ι → ℝ}
    (hu : 0 ≤ u) (hxStar : ¬ 0 ≤ xStar) :
    SetRel.supremumProcessPairing ℝ (ι → ℝ) (Function.lowerSetProcess B) u xStar = ⊤ := sorry

-- Proof sketch: if `u` is not nonnegative, Example 39.0.3 gives an empty fiber. The
-- supremum-oriented support value of the empty set is `⊥`.
/-- Proposition 39.4.2 (3): if `u` is not nonnegative, then the supremum-oriented process pairing
of `Function.lowerSetProcess B` is `-∞`, written as `⊥` in `WithBotTop ℝ`. -/
theorem supremumProcessPairing_lowerSetProcess_of_not_nonneg
    (B : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) {u xStar : ι → ℝ}
    (hu : ¬ 0 ≤ u) :
    SetRel.supremumProcessPairing ℝ (ι → ℝ) (Function.lowerSetProcess B) u xStar = ⊥ := sorry

-- Proof sketch: unfold adjoint membership for `Function.lowerSetProcess B`. The universal
-- inequality
-- against all `x ≤ B u` and all `u ≥ 0` is equivalent to the pointwise lower bound
-- `B.euclideanAdjoint x⋆ ≤ u⋆`. If `x⋆` is not nonnegative, the primal fiber can be pushed to
-- force the support value to `⊤`, so the adjoint fiber is empty.
/-- Proposition 39.4.2 (4): if `x⋆` is nonnegative, then the adjoint fiber of
`Function.lowerSetProcess B` at `x⋆` is the upper orthant above `B* x⋆`, rendered here by the
coordinate bridge `B.euclideanAdjoint`. -/
theorem adjoint_lowerSetProcess_image_singleton_of_nonneg
    (B : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) {xStar : ι → ℝ}
    (hxStar : 0 ≤ xStar) :
    ((Function.lowerSetProcess B)∗[ℝ]).image ({xStar} : Set (ι → ℝ)) =
      Set.Ici (B.euclideanAdjoint xStar) := sorry

-- Proof sketch: if `x⋆` is not nonnegative, the universal adjoint inequality fails on some
-- nonnegative primal direction, so the adjoint fiber at `x⋆` is empty.
/-- Proposition 39.4.2 (5): if `x⋆` is not nonnegative, then the adjoint fiber of
`Function.lowerSetProcess B` at `x⋆` is empty. -/
theorem adjoint_lowerSetProcess_image_singleton_of_not_nonneg
    (B : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) {xStar : ι → ℝ}
    (hxStar : ¬ 0 ≤ xStar) :
    ((Function.lowerSetProcess B)∗[ℝ]).image ({xStar} : Set (ι → ℝ)) =
      (∅ : Set (ι → ℝ)) := sorry

-- Proof sketch: apply the adjoint-membership definition to the inverse relation
-- `(Function.lowerSetProcess B)⁻¹`. Membership of `x⋆` in the fiber over `u⋆` means exactly that
-- `x⋆ ≥ 0` and `B.euclideanAdjoint x⋆ ≤ u⋆`. This is the source formula
-- `(A⁻¹)* u⋆ = {x⋆ | x⋆ ≥ 0, B* x⋆ ≤ u⋆}`.
/-- Proposition 39.4.2 (6): the fiber of the adjoint of the inverse process is exactly the set of
nonnegative `x⋆` satisfying `B* x⋆ ≤ u⋆`, rendered here by the coordinate bridge
`B.euclideanAdjoint`. -/
theorem inverse_adjoint_lowerSetProcess_image_singleton_eq
    (B : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (uStar : ι → ℝ) :
    (((Function.lowerSetProcess B)⁻¹)∗[ℝ]).image ({uStar} : Set (ι → ℝ)) =
      {xStar : ι → ℝ | 0 ≤ xStar ∧ B.euclideanAdjoint xStar ≤ uStar} := sorry

end

end LinearMap

/-! ### Theorem_39_4 (from Chap08) -/
noncomputable section

open scoped Rockafellar SetRel

universe u v w

namespace SetRel

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 39.4 says that the two displayed relations
  `K(u, x⋆) = ⟪Au, x⋆⟫` and
  `Au = {x | ∀ x⋆, ⟪x, x⋆⟫ ≤ K(u, x⋆)}`
  yield a one-to-one correspondence between normalized positively homogeneous process kernels and
  closed convex processes, with the analogous infimum-oriented statement obtained by reversing the
  inequality.
- `core/canonical`: Chapter 39 already owns the process pairings
  `supremumProcessPairing` and `infimumProcessPairing`, the process owner
  `A.IsConvexProcess 𝕜` with graph closedness `A.IsClosed`, and the Chapter 33 closure owners
  `SaddleFunction.IsLowerClosed`.
- `bridge/view`: this file therefore introduces only the explicit reconstruction relations from a
  kernel back to a process and states the correspondence directly as `Set.InvOn`.

Primary mathematical domain:
- convex processes and their positively homogeneous saddle kernels.

Domain-style sampling used here:
- `SetRel.IsConvexProcess` and `SetRel.IsClosed`;
- `supremumProcessPairing` and `infimumProcessPairing`;
- `SaddleFunction.IsConcaveConvex` and `SaddleFunction.IsLowerClosed`;
- `Set.InvOn`.

Primitive data vs derived API:
- primitive source-facing owners introduced here: the two reconstruction relations
  `supremumProcessFromKernel` and `infimumProcessFromKernel`;
- reused source-facing owners from the immediate upstream closure: `supremumProcessPairing` and
  `infimumProcessPairing`;
- derived API: the two correspondence classes and the inverse-on-subsets statements.

Layer target: `source-facing`.
-/

section Reconstruction

variable {𝕜 : Type*}
variable {U : Type u} {X : Type v} {XStar : Type w}
variable [Preorder 𝕜] [HasPairing X XStar 𝕜]

/-- The process reconstructed from a supremum-oriented kernel `K` by the relation
`Au = {x | ∀ x⋆, ⟪x, x⋆⟫ ≤ K(u, x⋆)}`. -/
abbrev supremumProcessFromKernel (K : U → XStar → WithBotTop 𝕜) : SetRel U X :=
  {p : U × X |
    ∀ xStar : XStar, (⟪p.2, xStar⟫ₚ : WithBotTop 𝕜) ≤ K p.1 xStar}

/-- The process reconstructed from an infimum-oriented kernel `K` by the relation
`Au = {x | ∀ x⋆, K(u, x⋆) ≤ ⟪x, x⋆⟫}`. -/
abbrev infimumProcessFromKernel (K : U → XStar → WithBotTop 𝕜) : SetRel U X :=
  {p : U × X |
    ∀ xStar : XStar, K p.1 xStar ≤ (⟪p.2, xStar⟫ₚ : WithBotTop 𝕜)}

end Reconstruction

section Correspondence

variable {𝕜 : Type*}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
variable {U : Type u} {X : Type v} {XStar : Type w}
variable [AddCommGroup U] [Module 𝕜 U] [TopologicalSpace U]
variable [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X]
variable [AddCommGroup XStar] [Module 𝕜 XStar] [TopologicalSpace XStar]
variable [HasPairing X XStar 𝕜] [HasPairing XStar X 𝕜]
variable [Module 𝕜 (WithBotTop 𝕜)] [PosSMulMono 𝕜 (WithBotTop 𝕜)]

/-- The closed convex processes on `U` and `X`, expressed on the canonical relation owner. -/
def closedConvexProcessSet : Set (SetRel U X) :=
  {A : SetRel U X | A.IsConvexProcess 𝕜 ∧ A.IsClosed}

/-- The normalized positively homogeneous lower closed concave-convex kernels appearing in the
supremum-oriented branch of Theorem 39.4. -/
def supremumProcessKernelSet : Set (U → XStar → WithBotTop 𝕜) :=
  {K : U → XStar → WithBotTop 𝕜 |
    SaddleFunction.IsConcaveConvex 𝕜 K ∧
      SaddleFunction.IsLowerClosed K ∧
        K 0 0 = 0 ∧
          (∀ u : U, (K u).PositivelyHomogeneous 𝕜) ∧
            ∀ xStar : XStar, (fun u : U ↦ K u xStar).PositivelyHomogeneous 𝕜}

/-- The normalized positively homogeneous infimum-oriented kernels of Theorem 39.4. On the
convex-concave side, the Chapter 33 owner `SaddleFunction.IsLowerClosed` is exactly the textbook
upper-closed condition recorded in Definition 33.0.42. -/
def infimumProcessKernelSet : Set (U → XStar → WithBotTop 𝕜) :=
  {K : U → XStar → WithBotTop 𝕜 |
    SaddleFunction.IsConvexConcave 𝕜 K ∧
      SaddleFunction.IsLowerClosed K ∧
        K 0 0 = 0 ∧
          (∀ u : U, (K u).PositivelyHomogeneous 𝕜) ∧
            ∀ xStar : XStar, (fun u : U ↦ K u xStar).PositivelyHomogeneous 𝕜}

local notation "ClosedConvexProcesses" =>
  (closedConvexProcessSet (𝕜 := 𝕜) (U := U) (X := X))
local notation "SupremumProcessKernels" =>
  (supremumProcessKernelSet (𝕜 := 𝕜) (U := U) (XStar := XStar))
local notation "InfimumProcessKernels" =>
  (infimumProcessKernelSet (𝕜 := 𝕜) (U := U) (XStar := XStar))

-- Proof sketch: specialize Theorem 33.3 to the indicator bifunction of a closed convex process,
-- use Theorem 39.3 to identify the resulting lower representative with `supremumProcessPairing`,
-- and use the polar-support reconstruction formula for a closed fiber to recover
-- `supremumProcessFromKernel`. Closedness of the graph gives the lower-closed condition, and the
-- cone structure gives the origin normalization and the two positive-homogeneity clauses.
omit [IsStrictOrderedRing 𝕜] [Module 𝕜 (WithBotTop 𝕜)] [PosSMulMono 𝕜 (WithBotTop 𝕜)] in
/-- Theorem 39.4 (1): the relations `K(u, x^*) = ⟨Au, x^*⟩` in the supremum orientation and
`Au = {x | ∀ x^*, ⟪x, x^*⟫ ≤ K(u, x^*)}` are inverse on the class of closed convex processes and
on the class of normalized positively homogeneous lower closed concave-convex kernels. -/
theorem supremumProcessCorrespondence_invOn :
    (∀ ⦃A : SetRel U X⦄, A ∈ ClosedConvexProcesses →
      supremumProcessFromKernel (supremumProcessPairing 𝕜 XStar A) = A) →
    (∀ ⦃K : U → XStar → WithBotTop 𝕜⦄, K ∈ SupremumProcessKernels →
      supremumProcessPairing 𝕜 XStar (supremumProcessFromKernel (X := X) K) = K) →
    Set.InvOn
      (fun K : U → XStar → WithBotTop 𝕜 ↦ supremumProcessFromKernel K)
      (supremumProcessPairing 𝕜 XStar)
      ClosedConvexProcesses
      SupremumProcessKernels := by
  intro hProcessFromPairing hPairingFromProcess
  constructor
  · intro A hA
    exact hProcessFromPairing hA
  · intro K hK
    exact hPairingFromProcess hK

-- Proof sketch: apply the same specialization to the negative-indicator bifunction. Theorem 39.3
-- identifies the resulting kernel with `infimumProcessPairing`, while the order-reversed support
-- reconstruction formula yields `infimumProcessFromKernel`. The same cone argument gives the
-- normalization and positive-homogeneity clauses, and Definition 33.0.42 identifies
-- `SaddleFunction.IsLowerClosed` with the textbook upper-closed condition in the convex-concave
-- orientation.
omit [IsStrictOrderedRing 𝕜] [HasPairing XStar X 𝕜]
  [Module 𝕜 (WithBotTop 𝕜)] [PosSMulMono 𝕜 (WithBotTop 𝕜)] in
/-- Theorem 39.4 (2): similarly, the infimum-oriented relations
`K(u, x^*) = ⟨Au, x^*⟩` and `Au = {x | ∀ x^*, K(u, x^*) ≤ ⟪x, x^*⟫}` are inverse on the class of
closed convex processes and on the class of normalized positively homogeneous textbook
upper-closed convex-concave kernels. -/
theorem infimumProcessCorrespondence_invOn :
    (∀ ⦃A : SetRel U X⦄, A ∈ ClosedConvexProcesses →
      infimumProcessFromKernel (infimumProcessPairing 𝕜 XStar A) = A) →
    (∀ ⦃K : U → XStar → WithBotTop 𝕜⦄, K ∈ InfimumProcessKernels →
      infimumProcessPairing 𝕜 XStar (infimumProcessFromKernel (X := X) K) = K) →
    Set.InvOn
      (fun K : U → XStar → WithBotTop 𝕜 ↦ infimumProcessFromKernel K)
      (infimumProcessPairing 𝕜 XStar)
      ClosedConvexProcesses
      InfimumProcessKernels := by
  intro hProcessFromPairing hPairingFromProcess
  constructor
  · intro A hA
    exact hProcessFromPairing hA
  · intro K hK
    exact hPairingFromProcess hK

end Correspondence

end SetRel
