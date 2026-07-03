import Mathlib
import stacks_project.Chap19.Proposition_19_11_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MorphismProperty

universe w v u

section

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C)
variable {I : Type w} (𝒢 : I → Sheaf K AddCommGrpCat.{max u v})

-- Proof sketch: replace the family `(𝒢 i)` by its coproduct, consider the underlying set of all
-- sections of that coproduct, and choose an ordinal whose cofinality is strictly larger than that
-- cardinal. Then apply the canonical Grothendieck-abelian smallness criterion for monomorphisms
-- to each `𝒢 i`; the single regular cardinal dominates all relevant subobject cardinals at once,
-- so every member of the family is small for the same ordinal bound.
/-- Lemma 19.7.2: for a family of abelian sheaves on a site, there is a single ordinal `β` such
that every member of the family is `β`-small with respect to monomorphisms; equivalently, maps
from any `𝒢 i` into a `β`-stage transfinite composition of monomorphisms factor through some
earlier stage. -/
theorem abelianSheaf_family_exists_uniform_smallness_bound_wrt_monomorphisms
    : ∃ β : Ordinal, ∀ i : I, is_alpha_small_wrt (𝒢 i) (monomorphisms _) β := sorry

end
