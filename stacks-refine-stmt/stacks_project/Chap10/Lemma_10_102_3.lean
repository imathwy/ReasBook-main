import stacks_project.Chap10.Lemma_10_102_2
import stacks_project.Chap10.Situation_10_102_1
import stacks_project.Chap10.Definition_10_72_1

open CategoryTheory CategoryTheory.Limits ChainComplex HomologicalComplex

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
variable {e : ℕ}

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
  | biprod {C₁ C₂ : ChainComplex (ModuleCat R) ℕ} :
      IsDirectSumOfTrivialComplexes C₁ →
      IsDirectSumOfTrivialComplexes C₂ →
      IsDirectSumOfTrivialComplexes (biprod C₁ C₂)
  | of_iso {C₁ C₂ : ChainComplex (ModuleCat R) ℕ} :
      IsDirectSumOfTrivialComplexes C₁ →
      (e : C₁ ≅ C₂) →
      IsDirectSumOfTrivialComplexes C₂

variable [IsLocalRing R] [IsNoetherianRing R]

/- Domain triage:
* primary domain: finite free chain complexes over a Noetherian local ring, together with the
  chapter's depth-zero criterion for the base ring;
* sampled owner declarations of the same kind:
  `Ideal.depth`,
  `moduleDepth`,
  `associatedPrimes R R`,
  `moduleDepth_eq_firstNonzeroResidueFieldExtIndex`;
* best owner abstraction: the chapter owner `Ideal.depth` and its local bridge `moduleDepth`,
  with associated-prime membership only as a bridge criterion;
* source/core/bridge layers here:
  `source-facing`: `IsDirectSumOfTrivialComplexes` as the decomposition notion from the item;
  `core/canonical`: depth, via `Ideal.depth`;
  `bridge/view`: `moduleDepth R R` and the associated-prime characterization of depth zero.

Primitive data are the finite free complex and its exactness. The depth-zero hypothesis should sit
at the owner layer, while associated-prime membership remains proof data rather than the main
public interface.
-/

-- Proof sketch: choose a nonzero element annihilated by the maximal ideal from the associated
-- prime criterion for the depth-zero hypothesis. Induct on the total positive-degree rank. If a
-- highest nonzero term occurs in degree `i > 0`, exactness forces a unit entry in the displayed
-- differential; apply Lemma `10.102.2` to split off a trivial disk and continue the induction.
-- The remaining degree-zero piece is a trivial single complex.
/-- Lemma 10.102.3: in Situation 10.102.1, if the bounded finite free complex
`0 → R^{n_e} → R^{n_{e-1}} → ⋯ → R^{n_0}` is exact in degrees `e, …, 1` and `R` has depth `0`,
then the complex is isomorphic to a direct sum of trivial complexes. -/
theorem finiteFreeComplex_isDirectSumOfTrivialComplexes_of_exact_of_depthZero
    (C : FiniteFreeComplex R e)
    (hexact : ∀ j : ℕ, 1 ≤ j → j ≤ e → C.toChainComplex.ExactAt j)
    (hdepth0 : moduleDepth R R = 0) :
    IsDirectSumOfTrivialComplexes C.toChainComplex := sorry

end
