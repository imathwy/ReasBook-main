import Mathlib.Topology.VectorBundle.Constructions

-- Declarations for this item will be appended below by the statement pipeline.

open Bundle

universe uA uB uF uE u𝕜

-- Semantic recall via `lean_leansearch`: `Bundle.Pullback` is the pullback family `f *ᵖ E`, and
-- `VectorBundle.pullback` is the canonical vector-bundle structure on such pullback families.

section

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {A : Type uA} [TopologicalSpace A]
variable {B : Type uB} [TopologicalSpace B]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : B → Type uE}
variable [TopologicalSpace (Bundle.TotalSpace F E)]
variable [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
variable [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
variable [VectorBundle 𝕜 F E]
variable (f : ContinuousMap A B)

/- Construction 23.1.2: Pullback of a vector bundle along `f : A → B` produces the pullback bundle
`f *ᵖ E` over `A`; mathlib provides its vector-bundle structure by the canonical instance
`VectorBundle.pullback`. -/
#check VectorBundle.pullback
#check f *ᵖ E
#check (inferInstance : VectorBundle 𝕜 F (f *ᵖ E))

end
