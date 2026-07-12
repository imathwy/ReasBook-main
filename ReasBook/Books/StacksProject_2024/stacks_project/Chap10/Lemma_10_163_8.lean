import Mathlib
import StacksProject_2024.Chap10.Lemma_10_157_4_Serre_s_criterion_for_normality
import StacksProject_2024.Chap10.Lemma_10_163_4
import StacksProject_2024.Chap10.Lemma_10_163_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S] [IsNormalRing R]

/-
Domain-style sampling pass:
* primary domain: Noetherian commutative algebra of ascent of normality along flat maps;
* sampled owner declarations of the same kind:
  - `IsNormalRing`, the chapter owner for ring normality;
  - `isNormalRing_iff_serreConditionR_one_and_serreConditionS_two`, the canonical Serre-criterion
    owner-level characterization of normality;
  - `serreConditionR_of_flat_of_fiber`, the chapter ascent theorem for `(R₁)`;
  - `serreConditionS_of_flat_of_fiber`, the chapter ascent theorem for `(S₂)`;
  - `Algebra.EssFiniteType.isNoetherianRing`, the canonical Noetherianity owner for the fiber
    ring `p.asIdeal.Fiber S` via the upstream instance `Algebra.EssFiniteType R p.asIdeal.ResidueField`.

Best owner abstraction:
* the public target stays the source-facing normality theorem, but its proof should pass entirely
  through the owner predicates `IsNormalRing`, `SerreConditionR`, and `SerreConditionS`, rather
  than duplicating local wheel definitions for the Serre conditions.

Primitive data vs. derived API:
* primitive data: the flat algebra `R → S`, the Noetherian hypotheses on `R` and `S`, the normal
  base-ring owner `[IsNormalRing R]`, and the fiberwise normality hypothesis `hfiber`;
* derived API: the `(R₁)` and `(S₂)` instances for the base and the fibers, obtained canonically
  from the Serre criterion, together with fiberwise Noetherianity obtained canonically from
  `Algebra.EssFiniteType.isNoetherianRing`, and then fed into the existing ascent theorems.

Source/core/bridge triage:
* `source-facing`: `isNormalRing_of_flat_of_fiber`, the textbook ascent statement for normality;
* `core/canonical`: `IsNormalRing`, `SerreConditionR`, `SerreConditionS`, and the criterion
  `isNormalRing_iff_serreConditionR_one_and_serreConditionS_two`;
* `bridge/view`: the two ascent theorems for `(R₁)` and `(S₂)` along the flat map.
-/

-- Proof sketch: by Serre's criterion, it is enough to prove that `S` satisfies `(R_1)` and
-- `(S_2)`. The normality of `R` and of each fiber ring gives these Serre conditions on `R` and on
-- every fiber. Apply Lemmas `10.163.5` and `10.163.4` to ascend `(R_1)` and `(S_2)` along the flat
-- map `R → S`, and conclude that `S` is normal by Serre's criterion again.
/-- Lemma 10.163.8: for a flat ring map `R → S` between Noetherian rings, if `R` is normal and
every fiber ring `κ(𝔭) ⊗[R] S`, formalized as `p.asIdeal.Fiber S`, is normal, then `S` is a
normal ring. -/
theorem isNormalRing_of_flat_of_fiber
    (hfiber : ∀ p : PrimeSpectrum R, IsNormalRing (p.asIdeal.Fiber S)) :
    IsNormalRing S := by
  have hR :
      R ⊧ (R₁) ∧ R ⊧ (S₂) :=
    isNormalRing_iff_serreConditionR_one_and_serreConditionS_two.1 inferInstance
  let _ : R ⊧ (R₁) := hR.1
  let _ : R ⊧ (S₂) := hR.2
  have hfiberSerre (p : PrimeSpectrum R) :
      (p.asIdeal.Fiber S) ⊧ (R₁) ∧ (p.asIdeal.Fiber S) ⊧ (S₂) := by
    let _ : Algebra.EssFiniteType S (S ⊗[R] p.asIdeal.ResidueField) := inferInstance
    let _ : IsNoetherianRing (S ⊗[R] p.asIdeal.ResidueField) :=
      Algebra.EssFiniteType.isNoetherianRing S (S ⊗[R] p.asIdeal.ResidueField)
    let _ : IsNoetherianRing (p.asIdeal.Fiber S) :=
      isNoetherianRing_of_ringEquiv (S ⊗[R] p.asIdeal.ResidueField)
        (Algebra.TensorProduct.comm R p.asIdeal.ResidueField S).toRingEquiv.symm
    exact isNormalRing_iff_serreConditionR_one_and_serreConditionS_two.1 (hfiber p)
  have hSR : S ⊧ (R₁) :=
    serreConditionR_of_flat_of_fiber fun p ↦ (hfiberSerre p).1
  have hSS : S ⊧ (S₂) :=
    serreConditionS_of_flat_of_fiber fun p ↦ (hfiberSerre p).2
  exact isNormalRing_iff_serreConditionR_one_and_serreConditionS_two.2 ⟨hSR, hSS⟩

end
