import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

-- Domain sampling pass:
-- * primary domain: smooth maps between manifolds and their action on tangent vectors;
-- * source-facing owner: the chapter predicate `VectorField.f_related`;
-- * relevant canonical mathlib owners sampled before refinement:
--   `mfderiv I I'`, `tangentMap I I'`, `ContMDiffMap`, and `VectorField.mpullback`.
-- The primitive data of Lee's notion is a smooth map together with the pointwise pushforward
-- identity. A bare `mfderiv` equality for an arbitrary map is not source-faithful because
-- `mfderiv` uses a junk value off the differentiable locus.

section

universe u𝕜 uE uH uM uE' uH' uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (∞ : ℕ∞ω) M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {I' : ModelWithCorners 𝕜 E' H'}
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' (∞ : ℕ∞ω) N]

namespace VectorField

variable {F : M → N}
variable {X : ∀ p : M, TangentSpace I p}
variable {Y : ∀ q : N, TangentSpace I' q}

/-- Definition 8.57-extra-1: vector fields `X` on `M` and `Y` on `N` are `F`-related if, for
every `p : M`, applying the differential of `F` at `p` to `X p` produces the vector `Y (F p)` at
`F p`. In Lee's smooth setting, the smoothness of `F` is part of the primitive data of the
relation. -/
def f_related (F : M → N) (X : ∀ p : M, TangentSpace I p) (Y : ∀ q : N, TangentSpace I' q) :
    Prop :=
  ContMDiff I I' (∞ : ℕ∞ω) F ∧ ∀ p : M, mfderiv I I' F p (X p) = Y (F p)

/- An `F`-related pair of vector fields is attached to a smooth map `F`. -/
omit [IsManifold I (∞ : ℕ∞ω) M] [IsManifold I' (∞ : ℕ∞ω) N] in
theorem f_related.contMDiff (hXY : f_related F X Y) :
    ContMDiff I I' (∞ : ℕ∞ω) F :=
  hXY.1

/- Pointwise form of the `F`-related condition. -/
omit [IsManifold I (∞ : ℕ∞ω) M] [IsManifold I' (∞ : ℕ∞ω) N] in
theorem f_related_apply (hXY : f_related F X Y) (p : M) :
    mfderiv I I' F p (X p) = Y (F p) :=
  hXY.2 p

end VectorField

end
