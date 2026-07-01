import Mathlib.Geometry.Manifold.SmoothEmbedding

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold

universe u𝕜 uE uH uM uE' uH'

section SubmanifoldsWithBoundary

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners 𝕜 E H) [IsManifold I ⊤ M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable (J : ModelWithCorners 𝕜 E' H') (S : Set M)
variable [ChartedSpace H' S] [IsManifold J ⊤ S]

/- Definition 5.36-extra-1, immersed form: once the manifold-with-boundary structure on the
subtype `S` is fixed, the owner abstraction is the canonical immersion predicate for the subtype
inclusion. -/
#check Manifold.IsImmersion J I ⊤ (Subtype.val : S → M)

/- Definition 5.36-extra-1, embedded form: the corresponding embedded notion is the canonical
smooth-embedding predicate for the same subtype inclusion. -/
#check Manifold.IsSmoothEmbedding J I ⊤ (Subtype.val : S → M)

end SubmanifoldsWithBoundary
