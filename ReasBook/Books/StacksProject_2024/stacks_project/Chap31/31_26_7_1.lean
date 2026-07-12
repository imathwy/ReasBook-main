import StacksProject_2024.Chap31.Definition_31_26_7

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

section

variable (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
variable [Scheme.PrimeDivisorDiscreteValuationRings X]

/-- 31.26.7.1: formalizing the exact quotient segment
`\operatorname{Prin}(X) \to \operatorname{Div}(X) \to \operatorname{Cl}(X) \to 0`, where
`Cl(X)` is the quotient of Weil divisors by principal Weil divisors. This is the source-facing
exactness statement for the subgroup inclusion `\operatorname{Prin}(X) \hookrightarrow
\operatorname{Div}(X)` and the quotient map to `Cl(X)`. -/
theorem principalWeilDivisor_exact_quotientMap :
    Function.Exact
      (Prin(X)).subtype
      (weilDivisorClassGroupMk X) := by
  intro D
  constructor
  · intro hD
    change QuotientAddGroup.mk' (Prin(X)) D = 0 at hD
    refine ⟨⟨D, (QuotientAddGroup.eq_zero_iff D).1 hD⟩, rfl⟩
  · rintro ⟨E, rfl⟩
    change QuotientAddGroup.mk' (Prin(X)) ((Prin(X)).subtype E) = 0
    exact (QuotientAddGroup.eq_zero_iff ((Prin(X)).subtype E)).2 E.2

/-- 31.26.7.1: formalizing the exact quotient segment
`\operatorname{Prin}(X) \to \operatorname{Div}(X) \to \operatorname{Cl}(X) \to 0`, where
`Cl(X)` is the quotient of Weil divisors by principal Weil divisors. This is the source-facing
exactness statement for the subgroup inclusion `\operatorname{Prin}(X) \hookrightarrow
\operatorname{Div}(X)` and the quotient map to `Cl(X)`. -/
theorem weilDivisorClass_exactSequence :
    Function.Exact
      (Prin(X)).subtype
      (weilDivisorClassGroupMk X) ∧
      Function.Surjective
        (weilDivisorClassGroupMk X) := by
  exact ⟨principalWeilDivisor_exact_quotientMap X, weilDivisorClassGroupMk_surjective X⟩

end
