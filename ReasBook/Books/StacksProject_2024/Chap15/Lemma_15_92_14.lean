import Mathlib
import StacksProject_2024.Chap13.Definition_13_34_1
import StacksProject_2024.Chap15.Definition_15_92_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open Opposite

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)

/-
Domain-style sampling:
- primary domain: derived completeness in `D(A)` and its behavior under sequential derived limits;
- sampled owner-side declarations:
  `DerivedCategory.IsDerivedCompleteWithRespectTo`,
  `DerivedCategory.isDerivedCompleteWithRespectTo_iff`,
  `CategoryTheory.IsDerivedLimit`,
  `CategoryTheory.DerivedCategory.localizationAwayT_isDerivedLimit`;
- best owner abstraction: the canonical predicate `K.IsDerivedCompleteWithRespectTo I` together
  with the ambient derived-limit owner `IsDerivedLimit Ksys K'`;
- primitive data: the ideal `I`, the inverse system `Ksys`, a stagewise derived-completeness
  witness, and a chosen derived-limit witness;
- derived API: the stronger source-facing bridge where stagewise derived completeness is produced
  from the textbook power-zero hypothesis.

Layer triage:
- `source-facing`: the power-zero formulation from the Stacks-project statement;
- `core/canonical`: derived completeness of each stage and the owner predicate `IsDerivedLimit`;
- `bridge/view`: the passage from stagewise power-zero actions to stagewise derived completeness. -/

-- Proof sketch: derived completeness with respect to `I` is defined by vanishing of the
-- localization-away objects `T(-, f)` for `f ∈ I`. For a fixed `f`, Lemma `15.92.1` realizes
-- `T(-, f)` as a derived limit of the tower with transition map `f • 𝟙`, so applying it to a
-- Milnor triangle for `Ksys` reduces the claim to the fact that zero objects are preserved under
-- sequential derived limits when every stage already satisfies the vanishing condition.
/-- Any derived limit of a sequential inverse system of `I`-derived-complete objects is again
derived complete with respect to `I`. -/
theorem isDerivedCompleteWithRespectTo_of_isDerivedLimit_of_stagewise
    (I : Ideal A) (Ksys : ℕᵒᵖ ⥤ DMod) (K' : DMod)
    (hstage :
      ∀ n : ℕ, (Ksys.obj (op n)).IsDerivedCompleteWithRespectTo I)
    (hlim : IsDerivedLimit Ksys K') :
    K'.IsDerivedCompleteWithRespectTo I := sorry

-- Proof sketch: for each stage `K_n` and each `f ∈ I`, if some power `f^e` acts by zero on
-- `K_n`, then after inverting `f` the identity of `K_n` vanishes, so `K_n` is derived complete
-- with respect to `I`. Apply the canonical stagewise derived-completeness theorem above to the
-- resulting tower.
/-- Lemma 15.92.14: if `(K_n)` is a sequential inverse system in `D(A)` such that for every
`f ∈ I` and every `n` some power `f^e` acts by zero on `K_n`, then any derived limit of `(K_n)`
is derived complete with respect to `I`. The textbook object
`R \!\varprojlim_n (K \otimes_A^{\mathbf L} K_n)` is the intended application, since its stages
inherit the same annihilation property. -/
theorem isDerivedCompleteWithRespectTo_of_isDerivedLimit_of_stagewise_power_zero
    (I : Ideal A) (Ksys : ℕᵒᵖ ⥤ DMod) (K' : DMod)
    (hpow :
      ∀ f ∈ I, ∀ n : ℕ, ∃ e : ℕ, (f ^ e : A) • 𝟙 (Ksys.obj (op n)) = 0)
    (hlim : IsDerivedLimit Ksys K') :
    K'.IsDerivedCompleteWithRespectTo I := by
  apply isDerivedCompleteWithRespectTo_of_isDerivedLimit_of_stagewise I Ksys K'
  · intro n
    sorry
  · exact hlim

end

end CategoryTheory
