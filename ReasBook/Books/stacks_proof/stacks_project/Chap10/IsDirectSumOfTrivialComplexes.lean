import StacksProject_2024.Chap10.Lemma_10_102_2.Basic
import StacksProject_2024.Chap10.Situation_10_102_1

open CategoryTheory CategoryTheory.Limits ChainComplex HomologicalComplex

universe u

section

variable {R : Type u} [CommRing R]

/-- A chain complex is a direct sum of trivial complexes if it is obtained from degree-zero single
complexes and two-term identity-disk complexes by finitely many binary biproducts, up to
isomorphism. -/
inductive IsDirectSumOfTrivialComplexes : ChainComplex (ModuleCat R) ℕ → Prop
  | single₀ (n : ℕ) :
      IsDirectSumOfTrivialComplexes
        ((ChainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R (Fin n → R)))
  | disk (i n : ℕ) :
      IsDirectSumOfTrivialComplexes
        (HomologicalComplex.double
          (𝟙 (ModuleCat.of R (Fin n → R)))
          (show (ComplexShape.down ℕ).Rel (i + 1) i from rfl))
  | identityDisk {e : ℕ} (i : Fin e) :
      IsDirectSumOfTrivialComplexes (FiniteFreeComplex.identityDiskComplex (R := R) i)
  | biprod {C₁ C₂ : ChainComplex (ModuleCat R) ℕ} :
      IsDirectSumOfTrivialComplexes C₁ →
      IsDirectSumOfTrivialComplexes C₂ →
      IsDirectSumOfTrivialComplexes (biprod C₁ C₂)
  | of_iso {C₁ C₂ : ChainComplex (ModuleCat R) ℕ} :
      IsDirectSumOfTrivialComplexes C₁ →
      (e : C₁ ≅ C₂) →
      IsDirectSumOfTrivialComplexes C₂

end
