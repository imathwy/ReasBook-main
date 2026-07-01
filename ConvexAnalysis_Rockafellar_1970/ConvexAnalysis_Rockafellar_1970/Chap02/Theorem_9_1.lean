import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_4_2

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Rockafellar

section

variable
    {𝕜 : Type*} [Semiring 𝕜] [LE 𝕜]
    {E F : Type*}
    [AddCommGroup E] [Module 𝕜 E]
    [AddCommMonoid F] [Module 𝕜 F]

namespace LinearMap

/-- Kernel-vs-lineality side condition from Theorem 9.1:
every recession direction of `C` in `A.ker` lies in `lin[𝕜](C)`. -/
def recessionKernelLeLineality (A : E →ₗ[𝕜] F) (C : Set E) : Prop :=
  0⁺[𝕜] C ∩ (A.ker : Set E) ⊆ lin[𝕜](C)

/-- Trivial-kernel-recession side condition from Theorem 9.1 (3):
the only recession direction of `C` in `A.ker` is `0`. -/
def recessionKernelTrivial (A : E →ₗ[𝕜] F) (C : Set E) : Prop :=
  0⁺[𝕜] C ∩ (A.ker : Set E) ⊆ ({0} : Set E)

/-- Upstream owner bridge: the trivial-kernel recession condition implies the
kernel-vs-lineality condition. -/
theorem recessionKernelLeLineality_of_recessionKernelTrivial
    {A : E →ₗ[𝕜] F} {C : Set E}
    (hkernel_trivial : A.recessionKernelTrivial C) :
    A.recessionKernelLeLineality C := by
  intro z hz
  have hz0 : z = 0 := by
    have hz_mem : z ∈ ({0} : Set E) := hkernel_trivial hz
    simpa using hz_mem
  subst hz0
  rw [Set.mem_lineal_iff]
  constructor <;> rw [Set.mem_recessionCone_iff] <;>
    intro x hx a ha <;> simpa [zero_smul, add_zero] using hx

end LinearMap

section

variable
    {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
    [IsStrictOrderedRing 𝕜]
    {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]
    [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F]
    [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [T2Space F]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 9.1 gives a closed-image criterion for a convex set under a linear map,
  together with the corresponding recession-cone image formula for the canonical closed image. The
  source states this in Euclidean spaces, but the intrinsic owner-level formulation only needs a
  finite-dimensional Hausdorff topological vector space over an ordered topological scalar field `𝕜`
  as source and a Hausdorff topological vector space over `𝕜` as target.
- `core/canonical`: the owner abstractions already present in the chapter are `Convex 𝕜 C`,
  `closure`, the set image `A '' C` of a `LinearMap`, the kernel owner `A.ker`,
  `0⁺[𝕜] C`, and `lin[𝕜](C)`.
- `bridge/view`: Rockafellar's notation `0⁺ C` is the real specialization (`𝕜 = ℝ`) of
  `0⁺[𝕜] C`, while the lineality space of `cl C` is rendered by `lin[𝕜](closure C)`. Under the
  part (1) hypothesis, the source's closed image `cl (A C)` is canonically the set `A '' closure C`,
  so part (2) is best exposed directly on that owner. The auxiliary source-facing predicate
  `RecedesInDirection` is only the nonzero view on `recessionCone`, so it is not the owner
  abstraction for the main hypotheses here.
- Domain-style sampling used here: `image_closure_subset_closure_image`,
  `LinearMap.continuous_of_finiteDimensional`, `LinearMap.isClosedEmbedding_of_injective`,
  `Submodule.closed_of_finiteDimensional`, `LinearMap.ker`, `recessionCone`, and
  `Set.lineal`.
- Primitive data vs derived API: the primitive inputs are the convex set `C`, the linear map `A`,
  and the owner-level kernel-versus-lineality hypothesis on recession directions of an ambient set,
  phrased intrinsically through the kernel submodule `A.ker`; in Theorem 9.1 this ambient set is
  `closure C`, passed explicitly in the theorem hypotheses. The core closed-image owner statement
  is first exposed as `IsClosed (A '' K)` on a closed convex ambient set `K`; the recession-cone
  image formula is likewise first exposed on such a closed convex nonempty ambient owner `K`. The
  source-facing closure/recession statements for `C` are then direct corollaries at
  `K = closure C`. The closure identity is derived directly from those data and does not need a
  nonemptiness hypothesis because it remains true for `C = ∅`; by contrast, the recession-cone
  image formula still genuinely needs nonemptiness, taken on the primitive source owner `C`.
  No norm structure and no finite-dimensional structure on the codomain are primitive data here.
  The Hausdorff codomain assumption is primitive for the closed-image clauses, because the canonical
  closed owner `A '' closure C` and the finite-dimensional linear-image closedness facts used in
  the background rely on the codomain Hausdorff condition, while continuity of `A` still follows
  from finite dimensionality of the Hausdorff source.
- Layer target: part (1) and part (2) stay `source-facing`, stated directly in the owner language
  already used throughout the chapter; part (3) is the corresponding source-facing closed-image
  corollary, backed by a core closed-image owner theorem.
-/

namespace LinearMap

variable {C : Set E} (A : E →ₗ[𝕜] F)

/-- Core closed-image owner theorem for Theorem 9.1:
if `K` is closed and convex and the kernel slice of its recession cone lies in its lineality
space, then the linear image `A '' K` is closed. -/
-- Proof sketch: this is the intrinsic closed-owner form of Theorem 9.1 (1). The source-facing
-- closure identity `closure (A '' C) = A '' closure C` is recovered by applying this theorem to
-- `K = closure C`.
theorem isClosed_image_of_recessionKernelLeLineality
    {K : Set E}
    (hK : Convex 𝕜 K) (hK_closed : IsClosed K)
    (hkernel_lineality : A.recessionKernelLeLineality K) :
    IsClosed (A '' K) := sorry

/-- Theorem 9.1 (1): if the kernel slice of the recession cone of `closure C` is contained in the
lineality space of `closure C`, then the closure of the image `A '' C` is exactly the image of
the closure `A '' closure C`. The textbook source is recovered by specializing `𝕜 = ℝ`. -/
-- Proof sketch: the inclusion `A '' closure C ⊆ closure (A '' C)` is the general continuity
-- inclusion from Theorem 6.6. For the reverse inclusion, intersect `closure C` with a complement
-- to the common subspace `lin[𝕜](closure C) ∩ (A.ker : Set E)` and use the hypothesis to
-- show the resulting approximate fibers are bounded. Apply Theorem 8.4 to those closed convex
-- slices and then pass to a nested-intersection argument to recover a preimage point in
-- `closure C`.
theorem closure_image_eq_image_closure_of_recessionKernelLeLineality
    (hC : Convex 𝕜 C)
    (hkernel_lineality : A.recessionKernelLeLineality (closure C))
    :
    closure (A '' C) = A '' closure C := sorry

/-- Core recession-cone-image owner theorem for Theorem 9.1:
if `K` is closed, convex, and nonempty and the kernel slice of its recession cone lies in its
lineality space, then the recession cone of `A '' K` is exactly the image under `A` of the
recession cone of `K`. -/
theorem recessionCone_image_eq_image_recessionCone_of_recessionKernelLeLineality
    {K : Set E}
    (hK : Convex 𝕜 K) (hK_closed : IsClosed K)
    (hkernel_lineality : A.recessionKernelLeLineality K)
    (hK_nonempty : K.Nonempty) :
    0⁺[𝕜] (A '' K) = A '' 0⁺[𝕜] K := sorry

/-- Theorem 9.1 (2): under the same kernel-slice inclusion hypothesis, the recession cone of the
canonical closed image `A '' closure C` is exactly the image under `A` of the recession cone of
`closure C`. The textbook source is recovered by specializing `𝕜 = ℝ`. -/
-- Proof sketch: first use part (1) to identify the source's closed image `closure (A '' C)` with
-- the canonical owner `A '' closure C`. Then apply the homogenization argument from the source
-- proof and use Theorem 8.2 to identify the zero-height slices of the relevant closures with the
-- recession cones of `closure C` and `A '' closure C`.
theorem recessionCone_image_closure_eq_image_recessionCone
    (hC : Convex 𝕜 C)
    (hkernel_lineality : A.recessionKernelLeLineality (closure C))
    (hC_nonempty : C.Nonempty) :
    0⁺[𝕜] (A '' closure C) = A '' 0⁺[𝕜] (closure C) := sorry

/-- Theorem 9.1 (3): if `C` is a closed convex set and the only recession direction of `C`
annihilated by `A` is the zero vector, then the linear image `A '' C` is closed. The textbook
source is recovered by specializing `𝕜 = ℝ`. -/
-- Proof sketch: since `C` is closed, rewrite `closure C` as `C` in part (1). The stronger kernel
-- hypothesis implies the lineality hypothesis there, because the only kernel direction in
-- `0⁺[𝕜] C` is `0`. The resulting equality `closure (A '' C) = A '' C` is exactly the
-- closedness of the image.
theorem isClosed_image_of_recessionKernelTrivial
    (hC : Convex 𝕜 C) (hC_closed : IsClosed C)
    (hkernel_trivial : A.recessionKernelTrivial C) :
    IsClosed (A '' C) := sorry

end LinearMap

end

end
