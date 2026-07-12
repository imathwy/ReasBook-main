import StacksProject_2024.Chap22.PropertyI

open CategoryTheory Limits Opposite

noncomputable section

universe u v w

namespace DGModuleContext
namespace PropertyIFiltration

section

variable {𝒜 : DGModuleContext} {I : 𝒜.moduleCat}
variable [HasCountableProducts 𝒜.moduleCat]

/- Lemma 22.21.1 is source-facing at the Chapter 22 layer: for a chosen property `(I)`
filtration of `I`, the quotient tower `i ↦ I / F_i I` gives the dual Milnor product sequence
`0 ⟶ I ⟶ ∏ i, F.quotientFamily i ⟶ ∏ i, F.quotientFamily i ⟶ 0`.

The bridge to the Chapter 13 canonical owner is the Milnor difference map
`derivedLimitDifferenceMap F.tower`, together with the comparison morphism from
`I ≅ limit F.tower` to the ambient product of the quotient stages. -/

/-- The quotient family `i ↦ I / F_i I` attached to a property `(I)` filtration. -/
abbrev quotientFamily (F : PropertyIFiltration 𝒜 I) : ℕ → 𝒜.moduleCat :=
  inverseSystemFamily F.tower

/-- The canonical map from the inverse limit of the quotient tower to the product of its stages. -/
abbrev limitToProduct (F : PropertyIFiltration 𝒜 I) :
    limit F.tower ⟶ ∏ᶜ F.quotientFamily :=
  Pi.lift fun n ↦ limit.π F.tower (op n)

@[reassoc, simp]
theorem limitToProduct_comp_π (F : PropertyIFiltration 𝒜 I) (n : ℕ) :
    F.limitToProduct ≫ Pi.π F.quotientFamily n = limit.π F.tower (op n) := by
  rw [PropertyIFiltration.limitToProduct, Pi.lift_π]

/-- The canonical comparison from `I` to the product of the quotient stages `I / F_i I`. -/
abbrev productComparison (F : PropertyIFiltration 𝒜 I) :
    I ⟶ ∏ᶜ F.quotientFamily :=
  F.limitComparison.hom ≫ F.limitToProduct

@[reassoc, simp]
theorem productComparison_comp_π (F : PropertyIFiltration 𝒜 I) (n : ℕ) :
    F.productComparison ≫ Pi.π F.quotientFamily n =
      F.limitComparison.hom ≫ limit.π F.tower (op n) := by
  rw [PropertyIFiltration.productComparison, Category.assoc, limitToProduct_comp_π]

/-- The product comparison lands in the kernel of the Milnor difference map for the quotient
tower. -/
theorem productComparison_comp_difference_zero (F : PropertyIFiltration 𝒜 I) :
    F.productComparison ≫ derivedLimitDifferenceMap F.tower = 0 := by
  have hπsucc (n : ℕ) :
      F.productComparison ≫ Pi.π F.quotientFamily (n + 1) ≫
          F.tower.transitionMap (Nat.le_succ n) =
        F.limitComparison.hom ≫ limit.π F.tower (op (n + 1)) ≫
          F.tower.transitionMap (Nat.le_succ n) := by
    rw [PropertyIFiltration.productComparison, Category.assoc, limitToProduct_comp_π_assoc]
  have hlimit (n : ℕ) :
      F.limitComparison.hom ≫ limit.π F.tower (op (n + 1)) ≫
          F.tower.transitionMap (Nat.le_succ n) =
        F.limitComparison.hom ≫ limit.π F.tower (op n) := by
    calc
      F.limitComparison.hom ≫ limit.π F.tower (op (n + 1)) ≫
          F.tower.transitionMap (Nat.le_succ n) =
        F.limitComparison.hom ≫
          (limit.π F.tower (op (n + 1)) ≫ F.tower.transitionMap (Nat.le_succ n)) := by
            simp
      _ = F.limitComparison.hom ≫ limit.π F.tower (op n) := by
            rw [limit.w F.tower ((homOfLE (Nat.le_succ n)).op)]
  apply Pi.hom_ext
  intro n
  calc
    (F.productComparison ≫ derivedLimitDifferenceMap F.tower) ≫ Pi.π F.quotientFamily n =
        F.productComparison ≫ Pi.π F.quotientFamily n -
          F.productComparison ≫ Pi.π F.quotientFamily (n + 1) ≫
            F.tower.transitionMap (Nat.le_succ n) := by
          simpa [Category.assoc, Preadditive.comp_sub] using
            congrArg (fun t ↦ F.productComparison ≫ t)
              (derivedLimitDifferenceMap_comp_π F.tower n)
    _ =
        F.limitComparison.hom ≫ limit.π F.tower (op n) -
          F.limitComparison.hom ≫ limit.π F.tower (op (n + 1)) ≫
            F.tower.transitionMap (Nat.le_succ n) := by
          rw [productComparison_comp_π, hπsucc]
    _ = 0 := by
          rw [hlimit]
          simp
    _ = 0 ≫ Pi.π F.quotientFamily n := by simp

/-- The short complex
`I ⟶ ∏ i, F.quotientFamily i ⟶ ∏ i, F.quotientFamily i`
attached to the quotient tower of a property `(I)` filtration. -/
abbrev productShortComplex (F : PropertyIFiltration 𝒜 I) : ShortComplex 𝒜.moduleCat :=
  ShortComplex.mk F.productComparison (derivedLimitDifferenceMap F.tower)
    F.productComparison_comp_difference_zero

/-- Lemma 22.21.1: for a chosen property `(I)` filtration, the dual Milnor product sequence
`0 ⟶ I ⟶ ∏ i, F.quotientFamily i ⟶ ∏ i, F.quotientFamily i ⟶ 0`
is short exact. The first map is the canonical comparison from the inverse limit identification
`I ≅ limit F.tower`, and the second map is the Milnor difference map `1 - shift`
of the quotient tower. -/
@[stacks 09KR]
theorem productShortExact (F : PropertyIFiltration 𝒜 I) :
    F.productShortComplex.ShortExact := by
  sorry

end

end PropertyIFiltration
end DGModuleContext
