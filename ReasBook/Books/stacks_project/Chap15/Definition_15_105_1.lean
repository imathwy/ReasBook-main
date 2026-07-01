import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

variable (A : Type u) [CommRing A]

/-- Definition 15.105.1 (1): a commutative ring is absolutely flat if every `A`-module is flat
over `A`. We package the standard equivalent elementwise criterion so the owner is independent of
the module universe; the flatness of arbitrary `A`-modules is exposed as derived API below. -/
class IsAbsolutelyFlatRing : Prop where
  /-- Every element of `A` admits a von Neumann regular factorization. -/
  exists_factor (a : A) : ∃ b : A, a = a ^ 2 * b

/-- Every additive `A`-module is flat over an absolutely flat ring. -/
instance {M : Type w} [AddCommGroup M] [Module A M] [IsAbsolutelyFlatRing A] : Module.Flat A M :=
  sorry

section

variable (K : Type u) [Field K]

/-- Every field is an absolutely flat ring. -/
instance : IsAbsolutelyFlatRing K := sorry

end

section

variable {ι : Type u} (A : ι → Type v) [∀ i, CommRing (A i)] [∀ i, IsAbsolutelyFlatRing (A i)]

/-- Coordinatewise products of absolutely flat rings are absolutely flat. -/
instance : IsAbsolutelyFlatRing ((i : ι) → A i) where
  exists_factor a := by
    classical
    choose b hb using fun i ↦ (inferInstance : IsAbsolutelyFlatRing (A i)).exists_factor (a i)
    refine ⟨b, ?_⟩
    ext i
    simpa [pow_two] using hb i

end

namespace Algebra

variable (B : Type v) [CommRing B] [Algebra A B]

/-- Definition 15.105.1 (2): a ring map `A → B` is weakly étale, or absolutely flat, if `B` is
flat over `A` and the multiplication map `B ⊗[A] B → B` is flat. -/
class IsWeaklyEtale : Prop where
  /-- The structure map `A → B` is flat, expressed on the underlying `A`-module `B`. -/
  moduleFlat : Module.Flat A B
  /-- The multiplication map `B ⊗[A] B → B` is flat. -/
  flat_tensorSquareMultiplication :
    (Algebra.TensorProduct.lmul' A : B ⊗[A] B →ₐ[A] B).Flat

/-- A weakly étale `A`-algebra is flat over `A`. -/
instance [h : IsWeaklyEtale A B] : Module.Flat A B :=
  h.moduleFlat

namespace IsWeaklyEtale

/-- The structure map of a weakly étale algebra is flat. -/
theorem flat (h : IsWeaklyEtale A B) : (algebraMap A B).Flat :=
  RingHom.flat_algebraMap_iff.mpr h.moduleFlat

end IsWeaklyEtale

section

variable {A}

/-- The identity map of a commutative ring is weakly étale. -/
instance : IsWeaklyEtale A A := sorry

end

end Algebra
