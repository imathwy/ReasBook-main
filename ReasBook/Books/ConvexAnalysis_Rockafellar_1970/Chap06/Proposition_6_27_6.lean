import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_23_0_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_27_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v} [AddZeroClass 𝕜] [Preorder 𝕜]
variable {E : Type u} [Sub E]

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 6.27.6 says that a point belongs to the minimum set of a function
  exactly when the zero functional belongs to the subdifferential there.
- `core/canonical`: the chapter owners are `minimumSet` and `_root_.subdifferentialAt`, so the
  dual-side condition is written directly as zero membership in `subdifferentialAt f x`.
- `bridge/view`: in inner-product spaces, the same criterion is transported through the
  Fréchet-Riesz bridge owner to zero membership in `Function.subdifferentialAt`.

Domain-style sampling used here:
- the Chapter 6 minimum-set owner `minimumSet` from `Definition_6_27_3`;
- the Chapter 23 dual-valued owner `_root_.subdifferentialAt` from `Definition_23_0_6`;
- the Euclidean bridge `Function.subdifferentialAt` from the same file;
- mathlib's canonical dual owner `StrongDual 𝕜 E`;
- mathlib's inner-product-space bridge owner `Function.subdifferentialAt`.

Primitive data vs derived API:
- primitive inputs: only `f : E → WithTopBot 𝕜` and the point `x : E`;
- primitive owner statement: membership in `minimumSet f` versus zero membership in
  `subdifferentialAt f x`;
- derived API: the textbook zero-vector bridge
  `(0 : E) ∈ Function.subdifferentialAt f x`.

Semantic note:
- the equivalence uses only the defining inequality of the minimum set and the zero-subgradient
  membership criterion, so the source assumptions "proper convex" are redundant for this
  statement and are not kept in the main Lean header.
-/

-- Proof sketch: unfold the two owner membership conditions. In any pairing model where pairing
-- against the distinguished zero element vanishes (through the canonical
-- `HasPairingZeroRight` owner),
-- `0 ∈ subdifferentialAt f x Y` is exactly the pointwise inequality `∀ z, f x ≤ f z`, and this
-- is exactly the primitive minimum-set membership criterion.
/-- Pairing-level minimizer criterion: in any pairing model where the zero dual element pairs to
zero, a point belongs to the minimum set exactly when that zero element is a subgradient there. -/
theorem mem_minimumSet_iff_zero_mem_subdifferentialAt_pairing
    {Y : Type (max u v)} [Zero Y] [HasPairing E Y 𝕜] [HasPairingZeroRight E Y 𝕜]
    {f : E → WithTopBot 𝕜} {x : E} :
    x ∈ minimumSet f ↔ (0 : Y) ∈ (∂[Y]f(x)) := by
  rw [mem_minimumSet_iff, mem_subdifferentialAt_pairing]
  constructor
  · intro hx z
    simpa [pairing_zero_right (x := z - x)] using hx z
  · intro hx z
    simpa [pairing_zero_right (x := z - x)] using hx z

end

section

variable {𝕜 : Type v} [NormedField 𝕜] [Preorder 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

-- Proof sketch: specialize the pairing-level criterion to the canonical continuous-dual model
-- `StrongDual 𝕜 E`.
/-- Proposition 6.27.6: a point belongs to the minimum set of an extended-valued function if
and only if the zero continuous linear functional is a subgradient there. This is the canonical
dual-valued form of the textbook minimizer criterion. -/
theorem mem_minimumSet_iff_zero_mem_subdifferentialAt
    {f : E → WithTopBot 𝕜} {x : E} :
    x ∈ minimumSet f ↔ (0 : StrongDual 𝕜 E) ∈ (∂ f at x) := by
  exact
    mem_minimumSet_iff_zero_mem_subdifferentialAt_pairing
      (𝕜 := 𝕜) (E := E) (Y := StrongDual 𝕜 E) (f := f) (x := x)

end

section

variable {𝕜 : Type v} [RCLike 𝕜] [Preorder 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

-- Proof sketch: unfold both owners. In the Euclidean bridge theorem
-- `Function.mem_subdifferentialAt`, the zero vector pairing term vanishes, so the primitive
-- minimum-set membership criterion applies directly.
/-- The textbook `x⋆ = 0` formulation of the minimizer criterion in an inner-product-space model.
-/
theorem mem_minimumSet_iff_zero_mem_subdifferentialAt_vector
    {f : E → WithTopBot 𝕜} {x : E} :
    x ∈ minimumSet f ↔ 0 ∈ (∂ᵥf(x)) := by
  rw [mem_minimumSet_iff, Function.mem_subdifferentialAt]
  simp

end
