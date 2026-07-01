import Mathlib
import stacks_project.Chap15.Situation_15_92_15
import stacks_project.Chap15.Lemma_15_92_16
import stacks_project.Chap15.«15_74_0_2»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open ComplexShape
open Opposite
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A] {r : ℕ}

local notation "DMod" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.92.17:
- primary domain: the canonical comparison from `K` to a chosen derived limit of the powered
  Koszul tensor tower in `D(A)`;
- sampled owner declarations:
  `derivedCompletionKoszulPowerTensorDerivedInverseSystem`,
  `CategoryTheory.IsDerivedLimit`,
  `CategoryTheory.HasMilnorTriangle.WithMap`,
  `K.IsDerivedCompleteWithRespectTo I`;
- best owner abstraction: the Chapter `13` owner
  `HasMilnorTriangle.WithMap
    (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f) ι`, together with the
  source-facing stagewise equations asserting that a map `c : K ⟶ L` induces the canonical stage
  maps coming from the augmentation `A[0] ⟶ K_n^\bullet`;
- primitive data: the tower
  `derivedCompletionKoszulPowerTensorDerivedInverseSystem K f`, a chosen product map
  `ι : L ⟶ ∏ K_n`, a Milnor-triangle witness
  `HasMilnorTriangle.WithMap (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f) ι`,
  a comparison morphism `c : K ⟶ L`, and the canonical stage maps from `K` into the tensor
  stages;
- derived API: the induced `IsDerivedLimit` witness and the isomorphism criterion for `c`.

Source/core/bridge triage:
- `source-facing`: the comparison predicate below for maps from `K` to a chosen derived limit of
  the powered Koszul tensor tower;
- `core/canonical`: `derivedCompletionKoszulPowerTensorDerivedInverseSystem K f`,
  `IsDerivedLimit`, `HasMilnorTriangle.WithMap`, and
  `K.IsDerivedCompleteWithRespectTo (Ideal.span (Set.range f))`;
- `bridge/view`: the explicit stagewise formula against the canonical map
  `K ⟶ K_n^\bullet \otimes_A^{\mathbf L} K`. -/

/-- The canonical map from `K` to the `n`th stage
`K_n^\bullet \otimes_A^{\mathbf L} K` of the powered Koszul tensor tower. -/
abbrev derivedCompletionKoszulPowerTensorToStage
    (K : DMod) (f : Fin r → A) (n : ℕ) :
    K ⟶ (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f).obj (op n) :=
  (singleZeroDerivedTensorIso K).inv ≫
    (derivedTensorProduct K).map
      (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
          (ModuleCat.of A A)).hom ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.extendSingleIso embeddingDownNat (ModuleCat.of A A)
              (0 : ℕ) (0 : ℤ) rfl).inv ≫
            HomologicalComplex.extendMap (koszulPowerAugmentation f n) embeddingDownNat))

/-- A morphism `c : K ⟶ L` is the canonical comparison from `K` to a chosen derived limit of the
powered Koszul tensor tower if `L` sits in the Milnor triangle of that tower and the stage
projections recover the canonical maps
`K ⟶ K_n^\bullet \otimes_A^{\mathbf L} K`. -/
def IsDerivedCompletionKoszulPowerTensorComparison
    (f : Fin r → A) (K L : DMod) (c : K ⟶ L) : Prop :=
  ∃ _ : HasProduct
      (inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f)),
    ∃ ι :
        L ⟶
          ∏ᶜ inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f),
      HasMilnorTriangle.WithMap
          (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f) ι ∧
        ∀ n : ℕ,
          c ≫ ι ≫
              Pi.π
                (inverseSystemFamily
                  (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
                n =
            derivedCompletionKoszulPowerTensorToStage K f n

/-- A derived-completion comparison presents its target as a derived limit of the powered Koszul
tensor tower. -/
theorem IsDerivedCompletionKoszulPowerTensorComparison.isDerivedLimit
    {f : Fin r → A} {K L : DMod} {c : K ⟶ L}
    (hc : IsDerivedCompletionKoszulPowerTensorComparison f K L c) :
    IsDerivedLimit (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f) L := by
  rcases hc with ⟨hP, _, hι, _⟩
  let _ : HasProduct
      (inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f)) := hP
  exact ⟨hP, hι.hasMilnorTriangle (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f)⟩

-- Proof sketch: if `c` is a compatible comparison to a chosen derived limit of the powered Koszul
-- tensor tower, then the target is derived complete by Lemma `15.92.16`, so an isomorphism `c`
-- forces derived completeness of `K`. Conversely, assume `K` is derived complete with respect to
-- `I = (f_1, ..., f_r)`. Filter each powered Koszul complex by stupid truncations, apply the
-- exactness of `E ↦ R lim (K ⊗_A^L E)` from Lemma `15.88.11`, and use the vanishing of the
-- negative graded pieces supplied by derived completeness to deduce that the comparison map is an
-- isomorphism.
/-- Lemma 15.92.17: in Situation `15.92.15`, for any comparison morphism
`c : K ⟶ L` formalizing the canonical map
`K \to R\!\varprojlim (K \otimes_A^{\mathbf L} K_n^\bullet)`, the object `K` is derived complete
with respect to `I = (f_1, \ldots, f_r)` if and only if `c` is an isomorphism. -/
theorem isDerivedCompleteWithRespectTo_spanRange_iff_isIso_derivedCompletionComparison
    (f : Fin r → A) {K L : DMod} (c : K ⟶ L)
    (hc : IsDerivedCompletionKoszulPowerTensorComparison f K L c) :
    K.IsDerivedCompleteWithRespectTo (Ideal.span (Set.range f)) ↔ IsIso c := sorry

end

end CategoryTheory
