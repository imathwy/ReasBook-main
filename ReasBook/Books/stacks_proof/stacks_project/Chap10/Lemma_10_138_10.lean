import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u

section

variable {A B C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
variable [Algebra.FormallySmooth A C]

-- Proof sketch: Lemma `10.131.9` gives a surjection
-- `KaehlerDifferential.mapBaseChange A B C : C ⊗[B] Ω[B⁄A] →ₗ[C] Ω[C⁄A]`.
-- By Proposition `10.138.8`, formal smoothness of `A → C` implies that `Ω[C⁄A]` is a
-- projective `C`-module, so this surjection admits a `C`-linear section. Together with the
-- exactness statement of Lemma `10.131.9`, this is exactly the split exactness of
-- `0 → J/J² → Ω[B⁄A] ⊗[B] C → Ω[C⁄A] → 0`.
/-- Lemma 10.138.10: if `A → C` is formally smooth and `B → C` is surjective with kernel `J`, then
the exact sequence
`0 → J/J² → Ω[B⁄A] ⊗[B] C → Ω[C⁄A] → 0`
of Lemma `10.131.9` is split exact. In canonical library form, the surjection
`KaehlerDifferential.mapBaseChange A B C : C ⊗[B] Ω[B⁄A] →ₗ[C] Ω[C⁄A]`
admits a `C`-linear section. -/
@[stacks 06A6]
theorem kaehlerDifferential_mapBaseChange_has_section_of_formallySmooth
    (hsurj : Function.Surjective (algebraMap B C)) :
    ∃ σ : Ω[C⁄A] →ₗ[C] C ⊗[B] Ω[B⁄A],
      (KaehlerDifferential.mapBaseChange A B C).comp σ = LinearMap.id := by
  simpa using
    Module.projective_lifting_property
      (KaehlerDifferential.mapBaseChange A B C)
      LinearMap.id
      (KaehlerDifferential.mapBaseChange_surjective A B C hsurj)

end
