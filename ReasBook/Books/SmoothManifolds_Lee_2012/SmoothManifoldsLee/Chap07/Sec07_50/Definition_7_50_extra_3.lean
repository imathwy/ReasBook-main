import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

-- `lean_leansearch` was unavailable in this environment; the canonical owner below was verified
-- directly against mathlib's `GroupTheory/GroupAction/Hom` API.

section

universe uG uH uM uN

variable {G : Type uG} [Group G]
variable {H : Type uH} [Group H]
variable {M : Type uM} [MulAction G M]
variable {N : Type uN} [MulAction G N]
variable [MulAction H N]
variable (φ : G →* H)

/- Definition 7.50-extra-3 is recall-only.

mathlib's canonical owner for equivariant maps between left `G`-actions is `MulActionHom`,
written `M →[G] N`. More generally, if the actions are related by a homomorphism `φ : G →* H`,
the corresponding notion is `M →ₑ[φ] N`.

Right `G`-actions are represented in mathlib as left actions of the opposite group `Gᵐᵒᵖ`, so an
equivariant map for right actions is expressed as a morphism `M →[Gᵐᵒᵖ] N`. -/
recall MulActionHom
#check M →[G] N
#check M →ₑ[φ] N

end

section

universe uG uM uN

variable {G : Type uG} [Group G]
variable {M : Type uM} [MulAction Gᵐᵒᵖ M]
variable {N : Type uN} [MulAction Gᵐᵒᵖ N]

#check M →[Gᵐᵒᵖ] N

end
