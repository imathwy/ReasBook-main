import Mathlib
import StacksProject_2024.Chap28.Lemma_28_25_1

-- Declarations for this item will be appended below by the statement pipeline.

open MvPolynomial

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced the away-localization and multivariable-polynomial
-- quotient owners, while the local source-facing comparison map is
-- `idealPowerHomColimitToComplementSections` from `Lemma_28_25_1`.

/-- Example 28.25.2 (1): for the ring
`A = k[x, y, z_1, z_2, \ldots]/(x^n z_n \mid n \ge 1)` and the ideal `I = (x)`, the canonical map
`colim_n Hom_A(I^n, A) → Γ(Spec(A) \setminus V(I), \widetilde A)` is not surjective. -/
@[stacks 01PN]
theorem idealPowerHomColimitToComplementSections_notSurjective_countablePowerExample
    (k : Type u) [Field k] :
    let A₀ : Type u := MvPolynomial (Bool ⊕ ℕ+) k
    let x₀ : A₀ := X (Sum.inl false)
    let J : Ideal A₀ := Ideal.span (Set.range fun n : ℕ+ ↦ x₀ ^ (n : ℕ) * X (Sum.inr n))
    let A : Type u := A₀ ⧸ J
    let _ : Module A A := Semiring.toModule
    let x : A := Ideal.Quotient.mk J x₀
    let I : Ideal A := Ideal.span ({x} : Set A)
    ¬ Function.Surjective
      (idealPowerHomColimitToComplementSections
        I
        (Submodule.fg_span_singleton x)
        (ModuleCat.of A A)).hom := sorry

/-- Example 28.25.2 (2): for the ring
`A = k[f, g, x, y, {a_n, b_n}_{n \ge 1}] /(fy - gx, a_n f^n + b_n g^n \mid n \ge 1)` and the
ideal `I = (f, g)`, the canonical map
`colim_n Hom_A(I^n, A) → Γ(Spec(A) \setminus V(I), \widetilde A)` is not surjective. -/
@[stacks 01PN]
theorem idealPowerHomColimitToComplementSections_notSurjective_gluedFractionExample
    (k : Type u) [Field k] :
    let A₀ : Type u := MvPolynomial (Fin 4 ⊕ (Bool × ℕ+)) k
    let f₀ : A₀ := X (Sum.inl 0)
    let g₀ : A₀ := X (Sum.inl 1)
    let x₀ : A₀ := X (Sum.inl 2)
    let y₀ : A₀ := X (Sum.inl 3)
    let fg : Fin 2 → A₀ := Fin.cases f₀ fun _ ↦ g₀
    let J : Ideal A₀ :=
      Ideal.span <|
        ({f₀ * y₀ - g₀ * x₀} :
          Set A₀) ∪
          Set.range
            (fun n : ℕ+ ↦ X (Sum.inr (false, n)) * f₀ ^ (n : ℕ) +
              X (Sum.inr (true, n)) * g₀ ^ (n : ℕ))
    let A : Type u := A₀ ⧸ J
    let _ : Module A A := Semiring.toModule
    let f : A := Ideal.Quotient.mk J f₀
    let g : A := Ideal.Quotient.mk J g₀
    let I : Ideal A := Ideal.span (Set.range fun i : Fin 2 ↦ Ideal.Quotient.mk J (fg i))
    ¬ Function.Surjective
      (idealPowerHomColimitToComplementSections
        I
        (Submodule.fg_span (Set.finite_range fun i : Fin 2 ↦ Ideal.Quotient.mk J (fg i)))
        (ModuleCat.of A A)).hom := sorry

end AlgebraicGeometry.Scheme.Modules
