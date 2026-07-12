import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {A : Type u} [CommRing A]

namespace Ideal

/-- If `I` and `J` are coprime ideals of `A` with trivial intersection, then `A` is canonically
ring-isomorphic to the product of the two quotient rings. -/
noncomputable def ringEquivQuotientProd (I J : Ideal A)
    (hIJ : IsCoprime I J) (hbot : I ⊓ J = ⊥) : A ≃+* (A ⧸ I) × A ⧸ J :=
  (RingEquiv.quotientBot A).symm.trans <|
    (Ideal.quotEquivOfEq hbot.symm).trans (Ideal.quotientInfEquivQuotientProd I J hIJ)

end Ideal

-- Proof sketch: for a ring equivalence `A ≃+* A₁ × A₂`, transport the two coordinate ideals
-- `⊥ × A₂` and `A₁ × ⊥` back to ideals of `A`; they are coprime and intersect trivially.
-- Conversely, if `I₁` and `I₂` are coprime with `I₁ ⊓ I₂ = ⊥`, use the canonical bridge
-- `Ideal.ringEquivQuotientProd I₁ I₂ hIJ hbot`.
/-- Proposition 1.1.100: a commutative ring is isomorphic to a direct product of two commutative
rings if and only if it contains two coprime ideals whose intersection is zero. -/
theorem exists_ringEquiv_prod_iff_exists_coprime_ideals_inf_eq_bot :
    (∃ (A₁ A₂ : Type u) (_ : CommRing A₁) (_ : CommRing A₂), Nonempty (A ≃+* A₁ × A₂)) ↔
    ∃ I₁ I₂ : Ideal A, IsCoprime I₁ I₂ ∧ I₁ ⊓ I₂ = ⊥ := by
  constructor
  · rintro ⟨A₁, A₂, _, _, ⟨e⟩⟩
    -- Work on the product side first: the two coordinate ideals are the textbook witnesses.
    let J₁ : Ideal (A₁ × A₂) := Ideal.prod (⊥ : Ideal A₁) (⊤ : Ideal A₂)
    let J₂ : Ideal (A₁ × A₂) := Ideal.prod (⊤ : Ideal A₁) (⊥ : Ideal A₂)
    -- Transport those ideals back along the ring equivalence.
    refine ⟨e.idealComapOrderIso J₁, e.idealComapOrderIso J₂, ?_, ?_⟩
    · rw [Ideal.isCoprime_iff_exists]
      -- The two complementary idempotents already sum to `1` in the product ring.
      refine ⟨e.symm (0, 1), ?_, e.symm (1, 0), ?_, ?_⟩
      · change e (e.symm (0, 1)) ∈ J₁
        simp [J₁]
      · change e (e.symm (1, 0)) ∈ J₂
        simp [J₂]
      · apply e.injective
        simp
    · ext a
      change e a ∈ J₁ ∧ e a ∈ J₂ ↔ a = 0
      constructor
      · rintro ⟨ha1, ha2⟩
        have h1 : (e a).1 = 0 := by
          simpa [J₁] using ha1
        have h2 : (e a).2 = 0 := by
          simpa [J₂] using ha2
        have h : e a = e 0 := by
          ext <;> simp [h1, h2]
        exact e.injective h
      · rintro rfl
        simp [J₁, J₂]
  · rintro ⟨I₁, I₂, hIJ, hbot⟩
    -- For the converse, use the canonical CRT equivalence from coprime ideals with zero infimum.
    refine ⟨A ⧸ I₁, A ⧸ I₂, inferInstance, inferInstance, ?_⟩
    exact ⟨I₁.ringEquivQuotientProd I₂ hIJ hbot⟩

end
