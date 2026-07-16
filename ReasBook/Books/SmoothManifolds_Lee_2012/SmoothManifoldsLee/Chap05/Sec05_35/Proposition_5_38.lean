import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_35.Notation_5_35_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

section SubmanifoldTangentSpace

universe u𝕜 uE uE' uF uH uH' uG uM uN

open Manifold

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {G : Type uG} [TopologicalSpace G]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace G N]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I ∞ M]
variable {J : ModelWithCorners 𝕜 E' H'} {S : Set M}
variable [ChartedSpace H' S] [IsManifold J ∞ S]
variable {K : ModelWithCorners 𝕜 F G} [IsManifold K ∞ N]

/-- A local defining map on `U` cuts out `S` as the fiber through each point of `S ∩ U` and has
surjective differential on `U`. -/
structure IsLocalDefiningMapOn (I : ModelWithCorners 𝕜 E H) (K : ModelWithCorners 𝕜 F G)
    (S U : Set M) (Φ : M → N) : Prop where
  isOpen_source : IsOpen U
  smoothOn : ContMDiffOn I K ∞ Φ U
  mem_iff_eq {p q : M} : p ∈ S → p ∈ U → q ∈ U → (q ∈ S ↔ Φ q = Φ p)
  surjective_mfderiv {p : M} : p ∈ U → Function.Surjective (mfderiv I K Φ p)

-- Proof sketch: differentiate the identity `Φ ∘ Subtype.val = constant` along `S` to show that
-- the image of the inclusion derivative lies in the kernel, then use surjectivity of `dΦₚ` and
-- finite-dimensional rank-nullity to identify the two subspaces by dimension.
/-- Proposition 5.38: if `Φ` is a local defining map for the embedded submanifold `S` on `U`, then
the tangent space of `S` at `p`, viewed inside `TangentSpace I (p : M)` via the inclusion
`Subtype.val : S → M`, is the kernel of `dΦₚ`. -/
theorem tangentSpace_eq_ker_mfderiv_of_isLocalDefiningMapOn {U : Set M} {Φ : M → N}
    (hS : IsSmoothEmbedding J I ∞ (Subtype.val : S → M))
    (hΦ : IsLocalDefiningMapOn I K S U Φ)
    (p : S) (hpU : (p : M) ∈ U) :
    T[J; p] = (mfderiv I K Φ (p : M)).ker := sorry

end SubmanifoldTangentSpace
