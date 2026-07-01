import stacks_project.Chap10.Definition_10_84_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Module

section

variable (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M]

/-- A module has the finite-free complement summand property if, after splitting off any finite
free direct summand, every element of the complementary summand lies in a free direct summand of
that complement. -/
def HasFiniteFreeComplementSummandProperty : Prop :=
  ∀ ⦃N N' : Submodule R M⦄, IsCompl N N' → Module.Finite R N' → Module.Free R N' →
    ∀ x : N, ∃ F F' : Submodule R N, x ∈ F ∧ Module.Free R F ∧ IsCompl F F'

end

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

-- Proof sketch: choose a countable generating sequence `x₁, x₂, …` for `M` and inductively split
-- off finite free direct summands `F₁, F₂, …` so that `F₁ ⊕ ⋯ ⊕ Fₙ` contains the first `n`
-- generators. The hypothesis applied to the complement after stage `n` produces `Fₙ₊₁`, and the
-- resulting countable direct-sum decomposition exhibits `M` as a free module.
/-- Lemma 10.85.2: a countably generated `R`-module is free if, whenever `M = N ⊕ N'` with `N'`
finite free, every element of `N` lies in a free direct summand of `N`. -/
theorem free_of_countablyGenerated_of_hasFiniteFreeComplementSummandProperty
    (hcg : CountablyGenerated R M)
    (hM : HasFiniteFreeComplementSummandProperty R M) :
    Module.Free R M := sorry

end

end Module
