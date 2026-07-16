import Mathlib
import stacks_proof.stacks_project.Chap04.Example_4_22_6
import stacks_proof.stacks_project.Chap15.Situation_15_92_15
import stacks_proof.stacks_project.Chap15.Lemma_15_102_Basic

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open SequentialProObjectMorphismRep
open scoped IdealPowerSubmodule
universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A] {r : ℕ}

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "single0" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)

/- Domain-style sampling for Lemma 15.102.5:
- primary domain: sequential pro-object comparisons in `D(A)` between ideal-power towers and the
  derived powered-Koszul tower attached to a finite generating family;
- sampled owner declarations:
  `idealPowerStage`,
  `idealPowerSubmoduleInclusionNatTrans`,
  `derivedCompletionKoszulPowersDerivedInverseSystem`,
  `Functor.ofOpSequence`,
  `SequentialProObjectMorphismRep.toProObjectHom`;
- best owner abstraction: the ideal-power side should be built from the chapter owner
  `idealPowerStage I n (ModuleCat.of A A)` and its canonical inclusion maps, while the comparison
  itself should be expressed by a sequential representative together with the owner morphism
  `a.toProObjectHom`;
- primitive data: an ideal `I : Ideal A`, or concretely `Ideal.span (Set.range f)`, together with
  the canonical powered-Koszul tower from Situation `15.92.15`;
- derived API: the derived-category ideal-power tower and the induced isomorphism of the
  associated sequential pro-objects.

Source/core/bridge triage:
- `source-facing`: the pro-isomorphism from the ideal-power tower for `I = (f_1, …, f_r)` to the
  derived powered-Koszul tower;
- `core/canonical`: `idealPowerStage`, `idealPowerSubmoduleInclusionNatTrans`,
  `derivedCompletionKoszulPowersDerivedInverseSystem`, and
  `SequentialProObjectMorphismRep.toProObjectHom`;
- `bridge/view`: the specialization `I = Ideal.span (Set.range f)`. -/

/-- The `n`th ideal-power stage `(I^[n+1] A)[0]` in `D(A)`, using the chapter owner
`idealPowerStage`. -/
abbrev idealPowerDerivedStage (I : Ideal A) (n : ℕ) : DMod :=
  (single0).obj (idealPowerStage I (n + 1) (ModuleCat.of A A))

/-- The transition morphism `(I^[n+2] A)[0] ⟶ (I^[n+1] A)[0]` in the ideal-power tower. -/
abbrev idealPowerDerivedStep (I : Ideal A) (n : ℕ) :
    idealPowerDerivedStage I (n + 1) ⟶ idealPowerDerivedStage I n :=
  (single0).map
    ((idealPowerSubmoduleInclusionNatTrans I (Nat.le_succ (n + 1))).app (ModuleCat.of A A))

/-- The inverse system `((I^[n+1] A)[0])_n` in `D(A)`. -/
abbrev idealPowerDerivedInverseSystem (I : Ideal A) : ℕᵒᵖ ⥤ DMod :=
  Functor.ofOpSequence (idealPowerDerivedStep I)

variable [IsNoetherianRing A]

-- Proof sketch: use the augmentation triangles for the powered Koszul complexes to compare the
-- truncated tower `(I_n^\bullet)_n` with the quotient tower from Lemma `15.95.1`; the cone tower
-- is pro-zero by the Noetherian argument from that lemma, and Lemma `13.42.4` then identifies the
-- ideal-power tower with `(I_n^\bullet)_n` up to pro-isomorphism.
/-- Lemma 15.102.5: in Situation `15.92.15`, let `I = (f_1, \ldots, f_r)` and assume `A` is
Noetherian. Then the inverse system `((I^[n+1] A)[0])_n`, equivalently `((I^(n+1))[0])_n`, is
isomorphic as a sequential pro-object of `D(A)` to the inverse system `(I_n^\bullet)_n`, where
`I_n^\bullet` is represented by the truncation of the powered Koszul complex
`K(A; f_1^(n+1), \ldots, f_r^(n+1))`. This item-file indexing convention has stage `0`
corresponding to the textbook stage `n = 1`. -/
@[stacks 0G3M]
theorem exists_pro_isomorphism_ideal_powers_to_derived_completion_koszul_ideal_tower
    (f : Fin r → A) :
    ∃ a :
        SequentialProObjectMorphismRep
          (idealPowerDerivedInverseSystem (Ideal.span (Set.range f)))
          (derivedCompletionKoszulPowersDerivedInverseSystem f),
      IsIso a.toProObjectHom := sorry

end
