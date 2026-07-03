import StacksProject_2024.Chap04.Example_4_22_6
import StacksProject_2024.Chap15.Lemma_15_92_16

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open SequentialProObjectMorphismRep

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A] {r : ℕ}

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "single0" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)

/- Domain-style sampling for Lemma 15.95.1:
- primary domain: sequential pro-object comparison between the powered Koszul tower in `D(A)` and
  the degree-zero image of the powered quotient tower from Situation `15.92.15`;
- sampled owner declarations:
  `koszulPowerQuotientStage`,
  `koszulPowerQuotientInverseSystem`,
  `derivedCompletionKoszulPowersDerivedInverseSystem`,
  `SequentialProObjectMorphismRep.toProObjectHom`;
- best owner abstraction: the quotient side should reuse the source-facing module-level owner
  `koszulPowerQuotientInverseSystem` and pass to `D(A)` by whiskering with the canonical degree-zero
  single functor, while the comparison itself should be expressed through a sequential
  representative together with the induced owner-level morphism of pro-objects
  `a.toProObjectHom`;
- primitive data: the powered quotient modules `A / (f_1^(n+1), \ldots, f_r^(n+1))` from
  Situation `15.92.15`;
- derived API: their images in `D(A)` and the resulting pro-isomorphism statement.

Source/core/bridge triage:
- `source-facing`: the pro-isomorphism between the powered Koszul tower and the quotient tower;
- `core/canonical`: `koszulPowerQuotientInverseSystem`,
  `derivedCompletionKoszulPowersDerivedInverseSystem`, `SequentialProObjectMorphismRep`, and
  `SequentialProObjectMorphismRep.toProObjectHom`;
- `bridge/view`: the degree-zero single-functor realization of the quotient tower inside `D(A)`. -/

/-- The `n`th quotient stage `A / (f_1^(n+1), \ldots, f_r^(n+1))`, viewed in degree `0` in
`D(A)`. -/
abbrev derivedCompletionPowerQuotientDerivedStage
    (f : Fin r → A) (n : ℕ) : DMod :=
  (single0).obj (koszulPowerQuotientStage f n)

/-- The inverse system of quotient objects
`(A / (f_1^(n+1), \ldots, f_r^(n+1)))[0]` in `D(A)`, obtained by applying the degree-zero single
functor to the owner tower `koszulPowerQuotientInverseSystem f` from Situation `15.92.15`. -/
abbrev derivedCompletionPowerQuotientDerivedInverseSystem
    (f : Fin r → A) : ℕᵒᵖ ⥤ DMod :=
  koszulPowerQuotientInverseSystem f ⋙ single0

end

end CategoryTheory

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {r : ℕ}

local notation "DMod" => DerivedCategory (ModuleCat A)

-- Proof sketch: for each `n`, the powered Koszul complex `K_n^•` fits into the canonical
-- distinguished triangle whose degree-zero term is the quotient `A/(f_1^(n+1), …, f_r^(n+1))`.
-- By the pro-truncation criterion from the derived-category references cited in the textbook, it
-- suffices to show that the negative truncation tower is pro-zero; for bounded powered Koszul
-- complexes over a Noetherian ring, this reduces to eventual vanishing of the negative cohomology
-- transition maps, which follows from Artin-Rees together with the annihilation statement of
-- Lemma `15.28.6`.
/-- Lemma 15.95.1: if `A` is Noetherian, then the powered Koszul tower
`(K(A; f_1^(n+1), \ldots, f_r^(n+1)))_n` and the quotient tower
`(A / (f_1^(n+1), \ldots, f_r^(n+1)))[0]_n`, viewed as sequential pro-objects of `D(A)`, are
isomorphic. This is the item-file indexing convention in which stage `0` corresponds to the
textbook stage `n = 1`. -/
theorem exists_pro_isomorphism_derived_completion_koszul_powers_to_power_quotients
    (f : Fin r → A) :
    ∃ a :
        SequentialProObjectMorphismRep
          (derivedCompletionKoszulPowersDerivedInverseSystem f)
          (derivedCompletionPowerQuotientDerivedInverseSystem f),
      IsIso a.toProObjectHom := sorry

end
