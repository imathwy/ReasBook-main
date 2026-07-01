import Mathlib

noncomputable section

universe u

namespace ConjClasses

section

variable {G : Type u} [Monoid G]

/-- Passing to `n`th powers descends to conjugacy classes. -/
def pow (n : ℕ) : ConjClasses G → ConjClasses G :=
  Quotient.lift (fun g : G ↦ ConjClasses.mk (g ^ n)) fun _ _ hxy ↦ by
    exact ConjClasses.mk_eq_mk_iff_isConj.2 (hxy.pow n)

@[simp] theorem pow_mk (n : ℕ) (g : G) :
    ConjClasses.pow n (ConjClasses.mk g) = ConjClasses.mk (g ^ n) :=
  rfl

end

section

variable {G : Type u} [Group G]

/-- Inversion preserves conjugacy, so it descends to conjugacy classes. -/
theorem isConj_inv {x y : G} (hxy : IsConj x y) : IsConj x⁻¹ y⁻¹ := by
  rcases isConj_iff.mp hxy with ⟨a, ha⟩
  refine isConj_iff.mpr ⟨a, ?_⟩
  calc
    a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ := conj_inv.symm
    _ = y⁻¹ := by rw [ha]

/-- Inversion on representatives descends to inversion on conjugacy classes. -/
instance : Inv (ConjClasses G) where
  inv := Quotient.map' (fun g : G ↦ g⁻¹) fun _ _ hxy ↦ isConj_inv hxy

instance : InvolutiveInv (ConjClasses G) where
  inv_inv c := by
    refine Quotient.inductionOn c fun g ↦ ?_
    change (ConjClasses.mk (g⁻¹⁻¹) : ConjClasses G) = ConjClasses.mk g
    simp

/-- Inverting the conjugacy class of `g` gives the conjugacy class of `g⁻¹`. -/
@[simp] theorem inv_mk (g : G) :
    (ConjClasses.mk g : ConjClasses G)⁻¹ = ConjClasses.mk g⁻¹ :=
  rfl

end

section

variable {G : Type u} [Group G] [Finite G]

/-- If `n` is coprime to `|G|`, the induced power map on conjugacy classes is a permutation. -/
noncomputable def powCoprimeEquiv (n : ℕ) (hn : (Nat.card G).Coprime n) :
    ConjClasses G ≃ ConjClasses G :=
  Equiv.ofBijective (ConjClasses.pow n)
    ((show Function.Surjective (ConjClasses.pow n : ConjClasses G → ConjClasses G) from by
        intro c
        obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
        refine ⟨ConjClasses.mk ((powCoprime hn).symm g), ?_⟩
        simpa using
          congrArg ConjClasses.mk ((powCoprime hn).apply_symm_apply g)).bijective_of_finite)

end

end ConjClasses
