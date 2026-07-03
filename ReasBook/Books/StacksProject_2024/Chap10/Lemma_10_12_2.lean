import Mathlib.RingTheory.IsTensorProduct
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w z z'

section

variable {R : Type u} {M : Type v} {N : Type w}
  [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/- Lemma 10.12.2: the canonical bilinear map `TensorProduct.mk R M N` exhibits `M ⊗[R] N` as the
tensor product of `M` and `N`, so every `R`-bilinear map out of `M × N` factors uniquely through
`M ⊗[R] N`. -/
recall TensorProduct.isTensorProduct

variable {T : Type z} {T' : Type z'}
  [AddCommMonoid T] [Module R T]
  [AddCommMonoid T'] [Module R T']

/-- Any two realizations of the tensor product of `M` and `N` are uniquely linearly equivalent over
their defining bilinear maps. -/
theorem isTensorProduct_existsUnique_linearEquiv
    {g : M →ₗ[R] N →ₗ[R] T} {g' : M →ₗ[R] N →ₗ[R] T'}
    (hg : IsTensorProduct g) (hg' : IsTensorProduct g') :
    ∃! j : T ≃ₗ[R] T', ∀ x y, j (g x y) = g' x y := by
  refine ⟨hg.equiv.symm ≪≫ₗ hg'.equiv, ?_, ?_⟩
  · intro x y
    simp
  · intro j hj
    ext z
    refine hg.inductionOn z ?_ (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
    · simp
    · rw [hj x y]
      simp
    · simp [hx, hy]

end
