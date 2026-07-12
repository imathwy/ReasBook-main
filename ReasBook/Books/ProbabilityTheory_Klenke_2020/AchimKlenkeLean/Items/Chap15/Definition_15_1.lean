import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open BoundedContinuousFunction
open scoped BoundedContinuousFunction

universe u

variable {E : Type u} [TopologicalSpace E]

/- Recall: for `𝕜 = ℝ` or `𝕜 = ℂ`, an algebra of bounded continuous `𝕜`-valued functions on `E`
is canonically a subalgebra of the bounded continuous function algebra `E →ᵇ 𝕜`. -/
#check (Subalgebra ℝ (E →ᵇ ℝ))
#check (Subalgebra ℂ (E →ᵇ ℂ))

/- The canonical bridge from bounded continuous functions to continuous maps is the algebra
homomorphism `toContinuousMapₐ`. -/
#check (toContinuousMapₐ ℝ : (E →ᵇ ℝ) →ₐ[ℝ] C(E, ℝ))
#check (toContinuousMapₐ ℂ : (E →ᵇ ℂ) →ₐ[ℂ] C(E, ℂ))

/- Definition 15.1: for a bounded-continuous-function algebra on `E`, the textbook
point-separation notion is the owner predicate `Subalgebra.SeparatesPoints` on the mapped
subalgebra of `C(E, 𝕜)`. Thus the primitive data is the subalgebra `A`, and the separation clause
is derived after applying `A.map (toContinuousMapₐ 𝕜)`. -/
#check (fun A : Subalgebra ℝ (E →ᵇ ℝ) ↦ (A.map (toContinuousMapₐ ℝ)).SeparatesPoints)
#check (fun A : Subalgebra ℂ (E →ᵇ ℂ) ↦ (A.map (toContinuousMapₐ ℂ)).SeparatesPoints)
