import Mathlib
import StacksProject_2024.stacks_project.Chap13.Definition_13_11_3
import StacksProject_2024.stacks_project.Chap13.Definition_13_27_1
import StacksProject_2024.stacks_project.Chap15.Definition_15_70_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_70_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open IsLocalRing
open scoped CategoryTheory
open scoped DerivedExt

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

local notation "Mod" => ModuleCat R
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)
local notation "κ" => ResidueField R
local notation "κ₀" => Functor.obj single₀ (ModuleCat.of R κ)

/- Domain-style sampling:
- primary domain: finite injective dimension in `DerivedCategory (ModuleCat R)` for local
  Noetherian rings, tested by eventual vanishing of `Ext` from the residue field;
- sampled owner declarations:
  `D⁺(Mod)`,
  `HasFiniteInjectiveDimension`,
  `finiteInjectiveDimension_iff_exists_ext_vanishing_ideal_quotients_ge`,
  `ringJacobson_eq_maximalIdeal`,
  `ResidueField`,
  `DerivedCategory.t.plus`;
- best owner abstraction: the owner remains `HasFiniteInjectiveDimension`; this item is a
  `bridge/view` specialization of Lemma `15.70.6` along the canonical local-ring data
  `maximalIdeal R` and `ResidueField R`, with the bounded-below input carried by the Chapter `13`
  owner `K : D⁺(Mod)`, not by a second explicit witness;
- primitive data: `K : D⁺(Mod)` and finite cohomology modules;
- derived API: eventual vanishing of `Ext^i(κ₀, K)`, with the raw `ShiftedHom` owner kept
  implicit behind the Chapter `13` notation;
- abstraction check: `ResidueField R` is already the canonical quotient `R ⧸ maximalIdeal R`, so
  no local wrapper around the residue-field test object should be introduced. -/

-- Proof sketch: specialize Lemma `15.70.6` to the ideal `maximalIdeal R`. In a local ring,
-- `Ring.jacobson R = maximalIdeal R`, so the ideal-quotient test family collapses to the single
-- quotient `R / maximalIdeal R = ResidueField R`.
/-- Lemma 15.70.7: for a local Noetherian ring `R` and an object `K ∈ D⁺(R)` with finite
cohomology modules, `K` has finite injective dimension if and only if the groups
`Ext^i_R(ResidueField R, K)` vanish for all sufficiently large `i`. -/
lemma finiteInjectiveDimension_iff_eventually_residueField_ext_vanishes
    (K : D⁺(Mod))
    (hKfinite : ∀ i : ℤ, Module.Finite R ((H i).obj K.obj)) :
    HasFiniteInjectiveDimension K.obj ↔
      ∃ b : ℤ,
        ∀ i : ℤ, b < i → ∀ e : Ext^i(κ₀, K.obj), e = 0 := by
  have hcriterion :=
    finiteInjectiveDimension_iff_exists_ext_vanishing_ideal_quotients_ge
      (maximalIdeal R) (by simpa [ringJacobson_eq_maximalIdeal R]) K hKfinite
  constructor
  · intro hK
    rcases hcriterion.mp hK with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    intro i hi e
    simpa [ResidueField] using hb (maximalIdeal R) le_rfl i hi e
  · rintro ⟨b, hb⟩
    refine hcriterion.mpr ⟨b, ?_⟩
    intro J hJ i hi e
    by_cases htop : J = ⊤
    · subst htop
      let _ : Subsingleton (R ⧸ (⊤ : Ideal R)) := inferInstance
      have hzero : IsZero ((single₀).obj (ModuleCat.of R (R ⧸ (⊤ : Ideal R)))) :=
        (single₀).map_isZero
          (ModuleCat.isZero_of_subsingleton (ModuleCat.of R (R ⧸ (⊤ : Ideal R))))
      exact hzero.eq_of_src e 0
    · have hJ_eq : maximalIdeal R = J :=
        Ideal.IsMaximal.eq_of_le (maximalIdeal.isMaximal R) htop hJ
      subst hJ_eq
      simpa [ResidueField] using hb i hi e

end

end CategoryTheory
