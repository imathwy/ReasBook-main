module

public import Mathlib.Algebra.DirectSum.Module

public section

namespace AddMonoidHom

universe u v w

variable {ι : Type u} {G : ι → Type v} {H : Type w}
variable [∀ α, AddCommGroup (G α)] [AddCommGroup H]

/-- Definition 67.4. An abelian group `H` is the external direct sum of an indexed family of
abelian groups `G`, relative to monomorphisms `i α : G α →+ H`, when the ranges of the maps are
independent and generate `H`. -/
class IsExternalDirectSum (i : ∀ α, G α →+ H) : Prop where
  /-- Each summand embeds in the ambient group. -/
  injective (α : ι) : Function.Injective (i α)
  /-- The ranges of the embeddings are independent. -/
  iSupIndep_range : iSupIndep (fun α ↦ (i α).range)
  /-- The ranges of the embeddings generate the ambient group. -/
  iSup_range_eq_top : (⨆ α, (i α).range) = ⊤

end AddMonoidHom
