import Mathlib
import stacks_project.Chap15.Lemma_15_94_1
import stacks_project.Chap15.Lemma_15_92_17
import stacks_project.Chap15.Lemma_15_95_1
import stacks_project.Chap15.Proposition_15_95_2
import stacks_project.Chap15.Remark_15_92_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped IdealPowerTorsion PrincipalIdeal

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "single0" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)

private theorem range_fin1_power (f : A) (n : ℕ) :
    Set.range (fun _ : Fin 1 ↦ f ^ (n + 1)) = ({f ^ (n + 1)} : Set A) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    simp
  · intro hx
    refine ⟨0, ?_⟩
    simpa using hx.symm

private theorem principalPowerSingletonIdeal_eq (f : A) (n : ℕ) :
    koszulPowerIdeal (fun _ : Fin 1 ↦ f) n = principalPowerIdeal f (n + 1) := by
  rw [koszulPowerIdeal, principalPowerIdeal, range_fin1_power, Ideal.span_singleton_pow]

private theorem principalPowerQuotientDerivedStage_eq (f : A) (n : ℕ) :
    (derivedCompletionPowerQuotientDerivedInverseSystem (fun _ : Fin 1 ↦ f)).obj (op n) =
      idealPowerQuotientDerivedStage ((f) : Ideal A) n := by
  simpa [derivedCompletionPowerQuotientDerivedInverseSystem, idealPowerQuotientDerivedStage,
    koszulPowerQuotientStage] using
    congrArg (fun I : Ideal A ↦ (single0).obj (ModuleCat.of A (A ⧸ I)))
      (principalPowerSingletonIdeal_eq f n)

private abbrev principalPowerQuotientDerivedStageIso (f : A) (n : ℕ) :
    (derivedCompletionPowerQuotientDerivedInverseSystem (fun _ : Fin 1 ↦ f)).obj (op n) ≅
      idealPowerQuotientDerivedStage ((f) : Ideal A) n :=
  eqToIso (principalPowerQuotientDerivedStage_eq f n)

private abbrev principalPowerCompletionStageMap (f : A) (K : DMod) (n : ℕ) :
    (derivedCompletionKoszulPowerTensorDerivedInverseSystem K (fun _ : Fin 1 ↦ f)).obj (op n) ⟶
      (idealPowerQuotientTensorDerivedInverseSystem ((f) : Ideal A) K).obj (op n) :=
  (derivedTensorProduct K).map ((principalPowerKoszulToQuotientRep f).hom.app (op n)) ≫
    (derivedTensorProduct K).map (principalPowerQuotientDerivedStageIso f n).hom

namespace CategoryTheory

/-- A natural transformation from principal derived completion to a functor
`K ↦ naiveDerivedCompletionFunctor.obj K` is the source-facing comparison to naive principal-power
completion if, objectwise, the source and target are presented by the canonical Milnor-triangle
comparisons and those presentations are compatible with the stagewise map induced by
`principalPowerKoszulToQuotientRep`. -/
def IsPrincipalDerivedCompletionQuotientComparison
    (f : A)
    {naiveDerivedCompletionFunctor : DMod ⥤ DMod}
    (toNaiveDerivedCompletion : 𝟭 DMod ⟶ naiveDerivedCompletionFunctor)
    (comparison :
      DerivedCategory.derivedCompletion ((f) : Ideal A) (principalIdeal_fg f) ⟶
        naiveDerivedCompletionFunctor) : Prop :=
  ∀ K : DMod,
    ∃ _ : HasProduct
        (inverseSystemFamily
          (derivedCompletionKoszulPowerTensorDerivedInverseSystem K (fun _ : Fin 1 ↦ f))),
      ∃ _ : HasProduct
          (inverseSystemFamily
            (idealPowerQuotientTensorDerivedInverseSystem ((f) : Ideal A) K)),
        ∃ ιhat :
            DerivedCategory.derivedCompletionOf ((f) : Ideal A) (principalIdeal_fg f) K ⟶
              ∏ᶜ inverseSystemFamily
                (derivedCompletionKoszulPowerTensorDerivedInverseSystem K (fun _ : Fin 1 ↦ f)),
          ∃ ι' :
              naiveDerivedCompletionFunctor.obj K ⟶
                ∏ᶜ inverseSystemFamily
                  (idealPowerQuotientTensorDerivedInverseSystem ((f) : Ideal A) K),
            HasMilnorTriangle.WithMap
                (derivedCompletionKoszulPowerTensorDerivedInverseSystem K (fun _ : Fin 1 ↦ f))
                ιhat ∧
              HasMilnorTriangle.WithMap
                  (idealPowerQuotientTensorDerivedInverseSystem ((f) : Ideal A) K)
                  ι' ∧
                (∀ n : ℕ,
                  DerivedCategory.toDerivedCompletion ((f) : Ideal A) (principalIdeal_fg f) K ≫
                      ιhat ≫
                      Pi.π
                        (inverseSystemFamily
                          (derivedCompletionKoszulPowerTensorDerivedInverseSystem
                            K (fun _ : Fin 1 ↦ f)))
                        n =
                    derivedCompletionKoszulPowerTensorToStage K (fun _ : Fin 1 ↦ f) n) ∧
                (∀ n : ℕ,
                  toNaiveDerivedCompletion.app K ≫
                      ι' ≫
                      Pi.π
                        (inverseSystemFamily
                          (idealPowerQuotientTensorDerivedInverseSystem ((f) : Ideal A) K))
                        n =
                    idealPowerQuotientTensorToStage ((f) : Ideal A) K n) ∧
                ∀ n : ℕ,
                  CommSq
                    (comparison.app K)
                    (ιhat ≫
                      Pi.π
                        (inverseSystemFamily
                          (derivedCompletionKoszulPowerTensorDerivedInverseSystem
                            K (fun _ : Fin 1 ↦ f)))
                        n)
                    (ι' ≫
                      Pi.π
                        (inverseSystemFamily
                          (idealPowerQuotientTensorDerivedInverseSystem ((f) : Ideal A) K))
                        n)
                    (principalPowerCompletionStageMap f K n)

end CategoryTheory

/- Domain-style sampling for Lemma 15.94.2:
- primary domain: principal derived completion versus naive principal-power completion in `D(A)`,
  expressed through the chapter derived-completion owner, the quotient-tower derived-limit owner,
  and the principal tower comparison from Lemma `15.94.1`;
- sampled owner declarations:
  `DerivedCategory.derivedCompletion`,
  `CategoryTheory.IsDerivedCompletionKoszulPowerTensorComparison`,
  `CategoryTheory.IsDerivedCompletionIdealPowerQuotientTensorComparison`,
  `CategoryTheory.IsPrincipalDerivedCompletionQuotientComparison`,
  `idealPowerQuotientTensorDerivedInverseSystem`,
  `principalIdeal` together with the owner notation `(f)`,
  `principalPowerKoszulToQuotientRep`,
  `HasMilnorTriangle.WithMap`;
- best owner abstraction: the left-hand functor should be the canonical owner
  `DerivedCategory.derivedCompletion ((f) : Ideal A) ...`, while the right-hand source-facing
  data should be the chapter owner
  `IsDerivedCompletionIdealPowerQuotientTensorComparison ((f) : Ideal A)` and the source-facing
  bridge owner `CategoryTheory.IsPrincipalDerivedCompletionQuotientComparison`, which packages
  the compatible Milnor-triangle presentations and the thin principal bridge from
  Lemma `15.94.1`;
- primitive vs. derived: primitive data are the ring `A`, the element `f`, the canonical map
  `K ⟶ R lim (K ⊗_A^{\mathbf L} A/f^(n+1))`, and the stagewise compatibility with the principal
  Koszul-to-quotient tower map from Lemma `15.94.1`; the bounded `f`-power torsion criterion is
  derived API, not extra structure on the completion functor.

Source/core/bridge triage:
- `source-facing`: the comparison between principal derived completion and naive principal-power
  completion, specified objectwise by the actual Koszul and quotient towers and the induced map
  on their chosen derived limits, now packaged by
  `CategoryTheory.IsPrincipalDerivedCompletionQuotientComparison`;
- `core/canonical`: `DerivedCategory.derivedCompletion`,
  `IsDerivedCompletionKoszulPowerTensorComparison`,
  `IsDerivedCompletionIdealPowerQuotientTensorComparison`, and the chapter owner `(f)` for the
  principal ideal;
- `bridge/view`: the principal one-generator specialization and the induced comparison map
  determined by `principalPowerKoszulToQuotientRep`. -/

-- Proof sketch: if the `f`-power torsion is bounded, Lemma `15.94.1` upgrades the canonical
-- stagewise principal Koszul-to-quotient maps to a pro-isomorphism, so the induced canonical map
-- on chosen derived limits is an isomorphism. Conversely, if the canonical comparison from
-- principal derived completion to naive principal-power completion is an isomorphism, apply the
-- Milnor-triangle criterion from Lemma `15.88.11` to the cone tower, then test on `K = A` and on
-- a countable direct sum of copies of `A` to force the torsion tower `(A[f^(n+1)])_n` to be
-- eventually constant, equivalently `A[f^∞] = A[f^c]` for some `c`.
/-- Lemma 15.94.2: let `A` be a ring and `f ∈ A`. Let
`DerivedCategory.derivedCompletion ((f) : Ideal A) (principalIdeal_fg f)` be the
canonical derived completion functor `K ↦ R lim (K ⊗_A^{\mathbf L} (A \xrightarrow{f^(n+1)} A))`.
Suppose `toNaiveDerivedCompletion : 𝟭 ⟶ naiveDerivedCompletionFunctor` presents the right-hand
functor objectwise as the canonical derived limit of the principal-power quotient tower
`K ↦ R lim (K ⊗_A^{\mathbf L} (A / f^(n+1) A)[0])`, and suppose `comparison` is objectwise the
canonical map induced by the principal Koszul-to-quotient tower morphism of Lemma `15.94.1`.
The source canonicality, target canonicality, and stagewise compatibility with
`principalPowerKoszulToQuotientRep` are recorded by
`CategoryTheory.IsPrincipalDerivedCompletionQuotientComparison`.
Then this canonical comparison natural transformation is an isomorphism if and only if the
`f`-power torsion of `A` is bounded.
-/
theorem isIso_principalDerivedCompletionComparison_iff_exists_powerTorsionStabilizes
    (f : A)
    {naiveDerivedCompletionFunctor : DMod ⥤ DMod}
    (toNaiveDerivedCompletion : 𝟭 DMod ⟶ naiveDerivedCompletionFunctor)
    (comparison :
      DerivedCategory.derivedCompletion ((f) : Ideal A) (principalIdeal_fg f) ⟶
        naiveDerivedCompletionFunctor)
    (hcomparison :
      CategoryTheory.IsPrincipalDerivedCompletionQuotientComparison
        f toNaiveDerivedCompletion comparison) :
    IsIso comparison ↔ ∃ c : ℕ, A[f^∞] = A[f ^ c] := sorry

end
