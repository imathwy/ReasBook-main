import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Module (End toModuleEnd)

variable {A : Type u} [Ring A] [IsSimpleRing A]

/-- Lemma 11.3.1: if `A` is a simple ring and `M` is a nonzero right ideal of `A`, then the
canonical right-multiplication map from `Aᵐᵒᵖ` to the bicommutant
`End (End Aᵐᵒᵖ M) M` is bijective. In owner-abstraction form this is the canonical
map `toModuleEnd`, while the textbook `Algebra.lsmul ℤ (End Aᵐᵒᵖ M) M` is the
same action viewed as an algebra homomorphism. -/
-- Proof sketch: injectivity comes from simplicity of `A`, since a nonzero right ideal makes the
-- bicommutant nontrivial. For surjectivity, show that the image is a nonzero right ideal in the
-- bicommutant and then use the simplicity argument from the textbook to force it to be all of the
-- bicommutant.
theorem rightIdeal_bicommutant_bijective (M : Submodule Aᵐᵒᵖ A) (hM : M ≠ ⊥) :
    Function.Bijective (toModuleEnd (End Aᵐᵒᵖ M) M : Aᵐᵒᵖ →+* _) := sorry

/-- Companion bridge: the textbook `ℤ`-algebra form of Lemma 11.3.1 is the same canonical map. -/
theorem rightIdeal_bicommutant_lsmul_bijective (M : Submodule Aᵐᵒᵖ A) (hM : M ≠ ⊥) :
    Function.Bijective (Algebra.lsmul ℤ (End Aᵐᵒᵖ M) M : Aᵐᵒᵖ →ₐ[ℤ] _) := by
  simpa using rightIdeal_bicommutant_bijective M hM

/-- Owner abstraction underlying Lemma 11.3.1: the bicommutant of a nonzero right ideal of a
simple ring recovers the original opposite ring. -/
noncomputable def rightIdeal_double_centralizer (M : Submodule Aᵐᵒᵖ A) (hM : M ≠ ⊥) :
    Aᵐᵒᵖ ≃+* End (End Aᵐᵒᵖ M) M :=
  RingEquiv.ofBijective (toModuleEnd (End Aᵐᵒᵖ M) M : Aᵐᵒᵖ →+* _)
    (rightIdeal_bicommutant_bijective M hM)

end
