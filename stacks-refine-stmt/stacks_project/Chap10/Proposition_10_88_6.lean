import Mathlib
import stacks_project.Chap10.Definition_10_88_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe u v w

section HomInverseSystem

variable {R : Type u} [Ring R]
variable {I : Type v} [Preorder I]

/-- The inverse system `i ↦ Hom_R(M_i, N)` attached to a directed system of `R`-modules. -/
abbrev colimitPresentationHomInverseSystem
    (F : I ⥤ ModuleCat.{max v w} R) (N : ModuleCat.{max v w} R) :
    Iᵒᵖ ⥤ Type (max v w) :=
  F.op ⋙ preadditiveYoneda.obj N ⋙ forget AddCommGrpCat

end HomInverseSystem

section

variable {R : Type u} [CommRing R]
variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {M : Type (max v w)} [AddCommGroup M] [Module R M]

-- Proof sketch: prove `(1) ↔ (2)` by factoring a finitely presented target through a stage of the
-- colimit and using the domination-to-factorization criterion with finitely presented cokernel;
-- prove `(2) ↔ (3)` by the same criterion applied to the transition maps; `(3) → (4) → (5)` is
-- immediate from the definition of Mittag-Leffler for the Hom inverse systems; and `(5) → (3)` is
-- obtained by evaluating eventual image stabilization on the product module `∏ s, M_s` and then on
-- the `j`-th projection.
/-- Proposition 10.88.6: for a directed system `F` of finitely presented `R`-modules with colimit
`M`, the five standard domination, factorization, and Hom-Mittag-Leffler conditions on the
presentation are equivalent. -/
theorem directed_colimit_presentation_mittag_leffler_tfae
    (F : I ⥤ ModuleCat.{max v w} R)
    (hfp : ∀ i, Module.FinitePresentation R (F.obj i))
    (c : colimit F ≅ ModuleCat.of R M) :
    List.TFAE
      [ (∀ (P : ModuleCat.{max v w} R) [Module.FinitePresentation R P] (f : P →ₗ[R] M),
            ∃ (Q : ModuleCat.{max v w} R) (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q),
              ∀ N : ModuleCat.{max v w} R,
                LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)),
        (∀ i : I, ∃ (j : I) (hij : i ≤ j),
            ((F.map (homOfLE hij)).hom).Dominates ((colimit.ι F i ≫ c.hom).hom)),
        (∀ i : I, ∃ (j : I) (hij : i ≤ j),
            ∀ (k : I) (hik : i ≤ k), ∃ h : F.obj k ⟶ F.obj j,
              F.map (homOfLE hij) = F.map (homOfLE hik) ≫ h),
        (∀ N : ModuleCat.{max v w} R, (colimitPresentationHomInverseSystem F N).IsMittagLeffler),
        (colimitPresentationHomInverseSystem F
            (ModuleCat.of R ((s : I) → F.obj s))).IsMittagLeffler ] := sorry

end
