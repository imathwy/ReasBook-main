import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

variable {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V] [Module K V]
variable {ι : Sort w}

/- Proposition 1.4.4: for a family `Vᵢ` of subspaces of a `K`-vector space `V`, the carrier of
the infimum `⨅ i, Vᵢ i` is exactly the set-theoretic intersection `⋂ i, Vᵢ i`; equivalently, the
intersection of any family of subspaces is again a subspace. Source-facingly this lives on
`Subspace K V`, while the canonical owner theorem is `Submodule.coe_iInf`. -/
#check (Submodule.coe_iInf : (Vᵢ : ι → Subspace K V) →
  (↑(⨅ i, Vᵢ i) : Set V) = ⋂ i, ↑(Vᵢ i))
