import Mathlib
import StacksProject_2024.Chap25.Lemma_25_4_2
import StacksProject_2024.Chap25.Lemma_25_4_3

noncomputable section

universe w v u

namespace CategoryTheory

open Opposite
open CategoryTheory.Limits
open AlgebraicTopology
open scoped Simplicial

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasSheafify J AddCommGrpCat.{max w v}]
variable {K : SimplicialObject (Cᵒᵖ ⥤ Type (max w v))}
variable {𝒢 : Cᵒᵖ ⥤ Type (max w v)}

-- Semantic search note: `lean_leansearch` recalled the canonical owners
-- `SimplicialObject.Augmented`, `Presheaf.IsLocallySurjective`, and
-- `SimplicialObject.isCoskeletal_iff_isIso`; this item keeps the source hypotheses as
-- local-surjectivity statements for the augmentation, degree-`1` pullback map, and higher
-- coskeleton-unit components.

/-- The degree-`0` augmentation map `K₀ ⟶ 𝒢` of an augmented simplicial presheaf. -/
abbrev simplicialPresheafZeroMap
    (augmentation :
      K ⟶ (SimplicialObject.const (Cᵒᵖ ⥤ Type (max w v))).obj 𝒢) :
    K.obj (op ⦋0⦌) ⟶ 𝒢 :=
  augmentation.app (op ⦋0⦌)

/-- The two degree-`1` face maps become equal after composing with the degree-`0` augmentation. -/
theorem simplicialPresheafOneMap_condition
    (augmentation :
      K ⟶ (SimplicialObject.const (Cᵒᵖ ⥤ Type (max w v))).obj 𝒢) :
    K.δ 0 ≫ simplicialPresheafZeroMap augmentation =
      K.δ 1 ≫ simplicialPresheafZeroMap augmentation := by
  have h₀ := augmentation.naturality (SimplexCategory.δ (0 : Fin 2)).op
  have h₁ := augmentation.naturality (SimplexCategory.δ (1 : Fin 2)).op
  simpa using h₀.trans h₁.symm

/-- The degree-`1` comparison map `(d^1_0, d^1_1) : K₁ ⟶ K₀ ×_𝒢 K₀` induced by the augmentation.
-/
noncomputable def simplicialPresheafOneMap
    (augmentation :
      K ⟶ (SimplicialObject.const (Cᵒᵖ ⥤ Type (max w v))).obj 𝒢) :
    K.obj (op ⦋1⦌) ⟶
      (pullback
        (simplicialPresheafZeroMap augmentation)
        (simplicialPresheafZeroMap augmentation) : Cᵒᵖ ⥤ Type (max w v)) :=
  (pullback.lift
    (K.δ 0)
    (K.δ 1)
    (simplicialPresheafOneMap_condition augmentation) :
      K.obj (op ⦋1⦌) ⟶
        (pullback
          (simplicialPresheafZeroMap augmentation)
          (simplicialPresheafZeroMap augmentation) : Cᵒᵖ ⥤ Type (max w v)))

/-- The degree-`n + 1` comparison map `K_{n + 1} ⟶ (\operatorname{cosk}_n \operatorname{sk}_n
K)_{n + 1}`. -/
abbrev simplicialPresheafHigherMap
    (K : SimplicialObject (Cᵒᵖ ⥤ Type (max w v))) (n : ℕ)
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ (Cᵒᵖ ⥤ Type (max w v)),
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    K.obj (op ⦋n + 1⦌) ⟶
      ((SimplicialObject.cosk n).obj K).obj (op ⦋n + 1⦌) :=
  ((SimplicialObject.coskAdj n).unit.app K).app (op ⦋n + 1⦌)

/-- Lemma 25.4.4 (1): if the degree-`0` augmentation, the degree-`1` pullback comparison map,
and all higher coskeleton comparison maps become surjective after sheafification, then the
positive-degree homology sheaves of `K` vanish. -/
theorem simplicialPresheafHomology_succ_isZero_of_augmentedLocalHypercover
    (augmentation :
      K ⟶ (SimplicialObject.const (Cᵒᵖ ⥤ Type (max w v))).obj 𝒢)
    (h0 : Presheaf.IsLocallySurjective J (simplicialPresheafZeroMap augmentation))
    (h1 : Presheaf.IsLocallySurjective J (simplicialPresheafOneMap augmentation))
    (hHigher : ∀ n : ℕ, 1 ≤ n →
      ∀ [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ (Cᵒᵖ ⥤ Type (max w v)),
          (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F],
        Presheaf.IsLocallySurjective J (simplicialPresheafHigherMap K n))
    (n : ℕ) :
    IsZero (simplicialPresheafHomology J K (n + 1)) := sorry

/-- Lemma 25.4.4 (2): under the same local-surjectivity hypotheses, the canonical degree-`0`
comparison map identifies `H₀(K)` with the free abelian sheaf `\mathbf{Z}_{\mathcal G}^\#`. -/
theorem simplicialPresheafHomology_zeroToFreeAbelianSheaf_isIso_of_augmentedLocalHypercover
    (augmentation :
      K ⟶ (SimplicialObject.const (Cᵒᵖ ⥤ Type (max w v))).obj 𝒢)
    (h0 : Presheaf.IsLocallySurjective J (simplicialPresheafZeroMap augmentation))
    (h1 : Presheaf.IsLocallySurjective J (simplicialPresheafOneMap augmentation))
    (hHigher : ∀ n : ℕ, 1 ≤ n →
      ∀ [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ (Cᵒᵖ ⥤ Type (max w v)),
          (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F],
        Presheaf.IsLocallySurjective J (simplicialPresheafHigherMap K n)) :
    IsIso (simplicialPresheafHomology_zeroToFreeAbelianSheaf J augmentation) := sorry

end

end CategoryTheory
