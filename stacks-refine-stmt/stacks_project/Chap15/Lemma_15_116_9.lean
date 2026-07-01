import Mathlib
import stacks_project.Chap10.Definition_10_162_1
import stacks_project.Chap15.Definition_15_112_1

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal IsLocalRing
open IsExtensionOfDiscreteValuationRings
open scoped TensorProduct

universe u v w x y

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [NagataRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsExtensionOfDiscreteValuationRings A B]
variable [IsExtensionOfDiscreteValuationRings B C]
variable [IsExtensionOfDiscreteValuationRings A C]
variable {K : Type x} {L : Type y} {M : Type (max x y)}
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L]
variable [Field M] [Algebra C M] [IsFractionRing C M]
variable [Algebra L M] [Algebra K M] [IsScalarTower K L M]
variable [FiniteDimensional L M] [IsPurelyInseparable L M]
variable {p : ℕ}

/-- The extension `C` is generated over `B` by a `p`th root of the chosen uniformizer `π`. -/
private def IsGeneratedByPthRootOfUniformizer
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (p : ℕ) (π : A) : Prop :=
  ∃ x : C, x ^ p = algebraMap A C π ∧ Algebra.adjoin B ({x} : Set C) = ⊤

/-- The separable base-change alternative from the ramification-elimination lemma. It records a
degree-`p` separable extension `K1 / K` that is totally ramified with respect to `A`, makes
`L ⊗[K] K1` and `M ⊗[K] K1` into fields, and whose induced maps on the corresponding integral
closures are weakly unramified extensions of discrete valuation rings. -/
private def HasWeaklyUnramifiedSeparableBaseChange
    (A : Type u) (B : Type v) (C : Type w) (K : Type x) (L : Type y) (M : Type (max x y))
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsExtensionOfDiscreteValuationRings A B]
    [IsExtensionOfDiscreteValuationRings B C]
    [IsExtensionOfDiscreteValuationRings A C]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L]
    [Field M] [Algebra C M] [IsFractionRing C M]
    [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    (p : ℕ) : Prop :=
  ∃ (K1 : Type (max u v w x y)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
    (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1) (_ : Algebra.IsSeparable K K1),
      Module.finrank K K1 = p ∧
        ∃ (P : Ideal (integralClosure A K1)) (_ : P.IsMaximal)
          (_ : P.LiesOver (maximalIdeal A)),
          (∀ (Q : Ideal (integralClosure A K1)) (_ : Q.IsMaximal)
            (_ : Q.LiesOver (maximalIdeal A)), Q = P) ∧
            Function.Bijective
              (Ideal.ResidueField.map (maximalIdeal A) P
                (algebraMap A (integralClosure A K1)) (P.over_def (maximalIdeal A))) ∧
            Ideal.ramificationIdx (maximalIdeal A) P = p ∧
              let A1 := integralClosure A K1
              let L1 := TensorProduct K L K1
              let M1 := TensorProduct K M K1
              let B1 := integralClosure B L1
              let C1 := integralClosure C M1
              ∃ (_ : IsField L1) (_ : IsField M1)
                (_ : IsDomain A1) (_ : IsDiscreteValuationRing A1)
                (_ : IsDomain B1) (_ : IsDiscreteValuationRing B1)
                (_ : IsDomain C1) (_ : IsDiscreteValuationRing C1)
                (_ : Algebra A1 B1) (_ : Algebra B1 C1)
                (_ : IsExtensionOfDiscreteValuationRings A1 B1)
                (_ : IsExtensionOfDiscreteValuationRings B1 C1),
                  WeaklyUnramified A1 B1 ∧ WeaklyUnramified B1 C1

-- Proof sketch: let `e` be the ramification index of `C` over `B`. If `e = 1`, transitivity gives
-- the weakly unramified case for `A → C`. Otherwise the purely inseparable degree-`p` hypothesis
-- forces `e = p`; writing a uniformizer of `C` as a `p`th root of `uπ`, either `u` is already a
-- `p`th power in `B`, which gives `C = B[π^(1/p)]`, or after adjoining the totally ramified
-- degree-`p` separable extension furnished by Lemma `15.116.7`, Lemma `15.116.8` makes both
-- induced maps on the integral closures weakly unramified.
/-- Lemma 15.116.9: let `A ⊆ B ⊆ C` be extensions of discrete valuation rings with fraction fields
`K ⊆ L ⊆ M`, let `π ∈ A` be a uniformizer, assume `B` is Nagata and `A ⊆ B` is weakly
unramified, and assume `M / L` is purely inseparable of degree `p`. Then either `A → C` is
weakly unramified, or `C` is generated over `B` by a `p`th root of `π`, or there exists a
degree-`p` separable extension `K1 / K` totally ramified with respect to `A` such that
`L1 = L ⊗[K] K1` and `M1 = M ⊗[K] K1` are fields and the induced maps on the corresponding
integral closures `A1 → B1 → C1` are weakly unramified extensions of discrete valuation rings. -/
theorem ramification_elimination_of_purelyInseparable_degree_p
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    (hAB : WeaklyUnramified A B) (hLM : Module.finrank L M = p) :
    WeaklyUnramified A C ∨
      IsGeneratedByPthRootOfUniformizer A B C p π ∨
      HasWeaklyUnramifiedSeparableBaseChange
        A B C K L M p := sorry

end
