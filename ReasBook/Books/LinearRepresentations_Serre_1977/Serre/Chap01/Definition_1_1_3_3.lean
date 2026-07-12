import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w w₀ x

section

variable {k : Type u} {G : Type v} {W : Type w} {W₀ : Type w₀}
variable [Semiring k] [Monoid G]
variable [AddCommMonoid W] [Module k W]
variable [AddCommMonoid W₀] [Module k W₀]
variable (ρW : Representation k G W) (ρW₀ : Representation k G W₀)

/- Definition 1-1.3-3: the direct sum of two representations is the canonical product
representation `ρW.prod ρW₀`; its vectors are pairs `(w, w₀)` and the action is given
componentwise, corresponding to the block-diagonal matrix description. -/
recall Representation.prod

/-- The direct-sum representation acts componentwise on pairs. -/
-- Proof sketch: unfold the product representation; its underlying monoid homomorphism is the
-- product of the two actions, so evaluation on `(w, w₀)` is componentwise.
theorem prod_apply_pair (g : G) (w : W) (w₀ : W₀) :
    (ρW.prod ρW₀) g (w, w₀) = (ρW g w, ρW₀ g w₀) := rfl

section

variable {ι : Type x} {V : ι → Type w}
variable [(i : ι) → AddCommMonoid (V i)] [(i : ι) → Module k (V i)]
variable (ρ : (i : ι) → Representation k G (V i))

/- Finite direct sums of representations are realized by the canonical family-level construction
`Representation.directSum`; when `ι` is finite, this matches the final sentence of the definition.
-/
recall Representation.directSum

end

end
