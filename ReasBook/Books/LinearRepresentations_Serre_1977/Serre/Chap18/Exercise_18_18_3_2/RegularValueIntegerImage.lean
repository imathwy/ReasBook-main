import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.IntegerQuotientImage
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.RegularIntegerDiagonalQuotient

noncomputable section

open scoped BigOperators

universe u

namespace Representation

section RegularValueIntegerImage

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]

local instance regularValueIntegerImageFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

/-- The coordinatewise integer-to-regular-value quotient map before passing to the diagonal
quotient. In coordinate `c` it is the integer map
`ℤ → K / A · |C_G(c)|_p`. -/
noncomputable def regularIntegerFunctionToRegularValueProduct :
    (PRegularConjClass G p → ℤ) →+
      ((c : PRegularConjClass G p) →
        K ⧸ integerQuotientImageSubmodule
          (A := A) (K := K) (ConjClasses.centralizerPPart p c.1)) where
  toFun f c :=
    integerQuotientImageHom
      (A := A) (K := K) (ConjClasses.centralizerPPart p c.1) (f c)
  map_zero' := by
    ext c
    simp
  map_add' f g := by
    ext c
    simp

omit [IsLocalRing A] [IsDomain A] [IsFractionRing A K] [CharZero K]
  [CharP (IsLocalRing.ResidueField A) p] in
@[simp]
theorem regularIntegerFunctionToRegularValueProduct_apply
    (f : PRegularConjClass G p → ℤ) (c : PRegularConjClass G p) :
    regularIntegerFunctionToRegularValueProduct (p := p) (A := A) (K := K) (G := G) f c =
      integerQuotientImageHom (A := A) (K := K)
        (ConjClasses.centralizerPPart p c.1) (f c) :=
  rfl

/-- The source-side integer quotient map into Serre's coordinatewise fraction-field quotient.

It is only the integer image inside each quotient `K / dA`, not the full quotient. -/
noncomputable def regularIntegerDiagonalQuotientToRegularValueProduct :
    ((PRegularConjClass G p → ℤ) ⧸
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup) →+
      ((c : PRegularConjClass G p) →
        K ⧸ integerQuotientImageSubmodule
          (A := A) (K := K) (ConjClasses.centralizerPPart p c.1)) := by
  let D : AddSubgroup (PRegularConjClass G p → ℤ) :=
    (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup
  exact QuotientAddGroup.lift D
    (regularIntegerFunctionToRegularValueProduct (p := p) (A := A) (K := K) (G := G))
    (by
    intro f hf
    ext c
    have hfD : f ∈ regularIntegerDiagonalSubmodule (p := p) (G := G) := by
      simpa [D] using hf
    rcases (mem_regularIntegerDiagonalSubmodule_iff (p := p) (G := G) f).1 hfD c with
      ⟨a, ha⟩
    exact
      integerQuotientImageHom_eq_zero_of_mem_zmultiples
        (A := A) (K := K) (ConjClasses.centralizerPPart p c.1)
        (Int.mem_zmultiples_iff.mpr ⟨a, by simp [ha, mul_comm]⟩))

omit [IsLocalRing A] [IsDomain A] [IsFractionRing A K] [CharZero K]
  [CharP (IsLocalRing.ResidueField A) p] in
@[simp]
theorem regularIntegerDiagonalQuotientToRegularValueProduct_mk
    (f : PRegularConjClass G p → ℤ) :
    regularIntegerDiagonalQuotientToRegularValueProduct
        (p := p) (A := A) (K := K) (G := G)
        (QuotientAddGroup.mk'
          (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup f) =
      regularIntegerFunctionToRegularValueProduct
        (p := p) (A := A) (K := K) (G := G) f := by
  rw [regularIntegerDiagonalQuotientToRegularValueProduct]
  rfl

/-- The source-side integer quotient embeds into the product of fraction-field quotients.

This is the formal version of the warning that the displayed product quotients are not themselves
finite: only the integer image subgroup is the expected finite product. -/
theorem regularIntegerDiagonalQuotientToRegularValueProduct_injective :
    Function.Injective
      (regularIntegerDiagonalQuotientToRegularValueProduct
        (p := p) (A := A) (K := K) (G := G)) := by
  rw [← AddMonoidHom.ker_eq_bot_iff]
  apply le_antisymm
  · intro q hq
    rw [AddSubgroup.mem_bot]
    revert hq
    refine QuotientAddGroup.induction_on q ?_
    intro f hf
    have hcoord :
        ∀ c : PRegularConjClass G p,
          integerQuotientImageHom
              (A := A) (K := K) (ConjClasses.centralizerPPart p c.1) (f c) =
            0 := by
      intro c
      have h := congrFun hf c
      have hmk :=
        congrFun
          (regularIntegerDiagonalQuotientToRegularValueProduct_mk
            (p := p) (A := A) (K := K) (G := G) f) c
      simpa only [regularIntegerFunctionToRegularValueProduct_apply] using hmk.symm.trans h
    have hfD : f ∈ regularIntegerDiagonalSubmodule (p := p) (G := G) := by
      refine (mem_regularIntegerDiagonalSubmodule_iff (p := p) (G := G) f).2 ?_
      intro c
      rcases ConjClasses.centralizerPPart_eq_prime_pow (p := p) c.1 with
        ⟨e, he⟩
      have hker :
          f c ∈
            (integerQuotientImageHom
              (A := A) (K := K) (ConjClasses.centralizerPPart p c.1)).ker := by
        simpa [AddMonoidHom.mem_ker] using hcoord c
      have hz :
          f c ∈ AddSubgroup.zmultiples (ConjClasses.centralizerPPart p c.1 : ℤ) := by
        simpa [
          integerQuotientImageHom_ker_eq_zmultiples_of_eq_prime_pow
            (p := p) (A := A) (K := K) (d := ConjClasses.centralizerPPart p c.1)
            (e := e) he] using hker
      rcases Int.mem_zmultiples_iff.mp hz with ⟨a, ha⟩
      exact ⟨a, by simpa using ha⟩
    exact
      (QuotientAddGroup.eq_zero_iff
        (N := (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup) f).2
        (by simpa using hfD)
  · exact bot_le

/-- The integer image in Serre's coordinatewise fraction-field quotient is the expected finite
product of cyclic groups. -/
noncomputable def regularIntegerDiagonalQuotientToRegularValueProductRangeAddEquivPiZMod :
    (regularIntegerDiagonalQuotientToRegularValueProduct
      (p := p) (A := A) (K := K) (G := G)).range ≃+
      ∀ c : PRegularConjClass G p,
        ZMod (ConjClasses.centralizerPPart p c.1) :=
  (AddMonoidHom.ofInjective
      (regularIntegerDiagonalQuotientToRegularValueProduct_injective
        (p := p) (A := A) (K := K) (G := G))).symm.trans
    (regularIntegerQuotient_addEquiv_pi_centralizerPPart (p := p) (G := G))

/-- Nonempty packaging of the source-side integer-image cyclic product. -/
theorem regularIntegerDiagonalQuotientToRegularValueProductRange_nonempty_addEquiv_pi :
    Nonempty
      ((regularIntegerDiagonalQuotientToRegularValueProduct
          (p := p) (A := A) (K := K) (G := G)).range ≃+
        ∀ c : PRegularConjClass G p,
          ZMod (ConjClasses.centralizerPPart p c.1)) :=
  ⟨regularIntegerDiagonalQuotientToRegularValueProductRangeAddEquivPiZMod
    (p := p) (A := A) (K := K) (G := G)⟩

end RegularValueIntegerImage

end Representation
