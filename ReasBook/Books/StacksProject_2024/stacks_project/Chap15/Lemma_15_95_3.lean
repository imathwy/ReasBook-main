import Mathlib
import StacksProject_2024.Chap13.Situation_13_15_1
import StacksProject_2024.Chap15.Lemma_15_27_3
import StacksProject_2024.Chap15.Lemma_15_87_10
import StacksProject_2024.Chap15.Proposition_15_95_2
import StacksProject_2024.Chap15.Remark_15_92_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.DerivedCategory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.SequentialInverseSystem
open ModuleCat
open AdicCompletion
open Opposite

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "DModMinus" => boundedAboveDerivedCategory (ModuleCat A)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)
local notation "single₀" => (ModuleCat.single0Functor : ModuleCat A ⥤ DMod)

/- Domain-style sampling for Lemma 15.95.3:
- primary domain: derived `I`-adic completion in `D(A)` and the Milnor short exact sequence for
  the quotient-tensor inverse system `(K ⊗_A^L (A / I^(n+1))[0])_n`;
- sampled owner declarations:
  `DerivedCategory.derivedCompletionOf`,
  `CategoryTheory.derivedLimit_cohomology_shortExact`,
  `CategoryTheory.IsDerivedCompletionIdealPowerQuotientTensorComparison`,
  `idealPowerQuotientTorInverseSystem`,
  `SequentialInverseSystem.shift`;
- best owner abstraction: the public statements should be source-facing short exact sequences on
  the canonical owner `K^∧[I, hI]`; the chosen quotient-tower presentation is bridge/view data
  internal to the proof, owned by
  `IsDerivedCompletionIdealPowerQuotientTensorComparison`, while the module case should expose the
  source-facing Tor tower through the canonical shifted owner
  `(idealPowerQuotientTorInverseSystem I M p).shift 1`;
- primitive vs. derived:
  primitive data are the ideal `I`, the object `K` or module `M`, and the canonical derived
  completion owner `K^∧[I, hI]`;
  derived API is the Milnor short exact sequence, specialized for modules to the canonical Tor
  tower together with the explicit shifted bridge from the quotient-tensor homology tower, and for
  bounded-above objects to the canonical quotient-tensor cohomology tower.

Source/core/bridge triage:
- `source-facing`: the two short exact sequence theorems below for `M^∧` and `K^∧`;
- `core/canonical`: `DerivedCategory.derivedCompletionOf`,
  `CategoryTheory.derivedLimit_cohomology_shortExact`, and
  `CategoryTheory.IsDerivedCompletionIdealPowerQuotientTensorComparison`;
- `bridge/view`: any chosen Milnor-triangle or stagewise identification used to compare the
  canonical owner with the quotient tower. -/

private theorem cohomology_shortExact_of_derivedIdealPowerQuotientCompletionComparison
    [IsNoetherianRing A] (I : Ideal A)
    {K L : DMod} {c : K ⟶ L}
    (hc : IsDerivedCompletionIdealPowerQuotientTensorComparison I K L c)
    (i : ℕ) :
    ∃ (ι :
        firstDerivedLimit
            (idealPowerQuotientTensorDerivedInverseSystem I K ⋙ H (-(i : ℤ) - 1)) ⟶
          (H (-(i : ℤ))).obj L)
      (π :
        (H (-(i : ℤ))).obj L ⟶
          limit (idealPowerQuotientTensorDerivedInverseSystem I K ⋙ H (-(i : ℤ))))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := by
  simpa using
    derivedLimit_cohomology_shortExact
      (idealPowerQuotientTensorDerivedInverseSystem I K) L hc.isDerivedLimit (-(i : ℤ))

section

variable (I : Ideal A)
variable (M : Type u) [AddCommGroup M] [Module A M]

/-- Bridge/view companion for Lemma `15.95.3`: for a module `M`, the cohomology tower of the
quotient-tensor inverse system
`((single₀.obj M) \otimes_A^{\mathbf L} (A / I^(n+1))[0])_n`
in degree `-p` is canonically the shifted Tor tower
`(Tor_p^A(M, A / I^(n+1)))_n`, realized by the chapter owner
`(idealPowerQuotientTorInverseSystem I M p).shift 1`. -/
theorem idealPowerQuotientTensorSingle_homology_eq_shiftedTor
    (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] (p : ℕ) :
    idealPowerQuotientTensorDerivedInverseSystem I ((single₀).obj (ModuleCat.of A M)) ⋙
        H (-(p : ℤ)) =
      (idealPowerQuotientTorInverseSystem I M p).shift 1 := by
  sorry

private theorem moduleDerivedCompletion_cohomology_shortExact_of_comparison
    [IsNoetherianRing A] (I : Ideal A)
    (M : Type u) [AddCommGroup M] [Module A M]
    (i : ℕ)
    (hc :
      IsDerivedCompletionIdealPowerQuotientTensorComparison I
        ((single₀).obj (ModuleCat.of A M))
        (((single₀).obj (ModuleCat.of A M))^∧[I, I.fg_of_isNoetherianRing])
        (DerivedCategory.toDerivedCompletion I I.fg_of_isNoetherianRing
          ((single₀).obj (ModuleCat.of A M)))) :
    ∃ (ι :
        ((idealPowerQuotientTorInverseSystem I M (i + 1)).shift 1).firstDerivedLimit ⟶
          (H (-(i : ℤ))).obj
            (((single₀).obj (ModuleCat.of A M))^∧[I, I.fg_of_isNoetherianRing]))
      (π :
        (H (-(i : ℤ))).obj
            (((single₀).obj (ModuleCat.of A M))^∧[I, I.fg_of_isNoetherianRing]) ⟶
          limit ((idealPowerQuotientTorInverseSystem I M i).shift 1))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := by
  have hTorSucc :
      idealPowerQuotientTensorDerivedInverseSystem I ((single₀).obj (ModuleCat.of A M)) ⋙
          H (-(i : ℤ) - 1) =
        (idealPowerQuotientTorInverseSystem I M (i + 1)).shift 1 := by
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      idealPowerQuotientTensorSingle_homology_eq_shiftedTor I M (i + 1)
  have hTor :
      idealPowerQuotientTensorDerivedInverseSystem I ((single₀).obj (ModuleCat.of A M)) ⋙
          H (-(i : ℤ)) =
        (idealPowerQuotientTorInverseSystem I M i).shift 1 := by
    simpa using idealPowerQuotientTensorSingle_homology_eq_shiftedTor I M i
  simpa [firstDerivedLimit] using
    (hTorSucc ▸ hTor ▸
      cohomology_shortExact_of_derivedIdealPowerQuotientCompletionComparison I hc i)

end

section

variable [IsNoetherianRing A]
variable (I : Ideal A)
variable (M : Type u) [AddCommGroup M] [Module A M]

/-- Lemma 15.95.3: for an `A`-module `M`, the canonical derived `I`-adic completion
`((single₀).obj (ModuleCat.of A M))^∧[I, I.fg_of_isNoetherianRing]` fits into the short exact
sequence
`0 → R^1 \!\varprojlim Tor_{i + 1}^A(M, A / I^(n+1)) → H^{-i}(M^∧) →
\varprojlim Tor_i^A(M, A / I^(n+1)) → 0`, expressed on the source-facing tower by the shifted
chapter owner `(idealPowerQuotientTorInverseSystem I M p).shift 1`, whose stage `n` is
`Tor_p^A(M, A / I^(n+1))`. -/
theorem derivedCompletionOfModule_cohomology_shortExact
    (i : ℕ) :
    ∃ (ι :
        ((idealPowerQuotientTorInverseSystem I M (i + 1)).shift 1).firstDerivedLimit ⟶
          (H (-(i : ℤ))).obj
            (((single₀).obj (ModuleCat.of A M))^∧[I, I.fg_of_isNoetherianRing]))
      (π :
        (H (-(i : ℤ))).obj
            (((single₀).obj (ModuleCat.of A M))^∧[I, I.fg_of_isNoetherianRing]) ⟶
          limit ((idealPowerQuotientTorInverseSystem I M i).shift 1))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := by
  let c :
      (single₀).obj (ModuleCat.of A M) ⟶
        ((single₀).obj (ModuleCat.of A M))^∧[I, I.fg_of_isNoetherianRing] :=
    DerivedCategory.toDerivedCompletion I I.fg_of_isNoetherianRing
      ((single₀).obj (ModuleCat.of A M))
  have hc :
      IsDerivedCompletionIdealPowerQuotientTensorComparison I
        ((single₀).obj (ModuleCat.of A M))
        (((single₀).obj (ModuleCat.of A M))^∧[I, I.fg_of_isNoetherianRing])
        c := by
    sorry
  simpa [c] using
    moduleDerivedCompletion_cohomology_shortExact_of_comparison I M i hc

end

section

variable [IsNoetherianRing A]

/-- The bounded-above analogue of Lemma `15.95.3`: for `K ∈ D^-(A)`, the canonical derived
completion `(K.obj)^∧[I, I.fg_of_isNoetherianRing]` fits into the Milnor short exact sequence
attached to the quotient-tensor tower
`(K.obj ⊗_A^{\mathbf L} (A / I^(n+1))[0])_n`. -/
theorem boundedAboveDerivedCompletion_cohomology_shortExact
    (I : Ideal A) (K : DModMinus) (i : ℕ) :
    ∃ (ι :
        firstDerivedLimit
            (idealPowerQuotientTensorDerivedInverseSystem I K.obj ⋙ H (-(i : ℤ) - 1)) ⟶
          (H (-(i : ℤ))).obj ((K.obj)^∧[I, I.fg_of_isNoetherianRing]))
      (π :
        (H (-(i : ℤ))).obj ((K.obj)^∧[I, I.fg_of_isNoetherianRing]) ⟶
          limit (idealPowerQuotientTensorDerivedInverseSystem I K.obj ⋙ H (-(i : ℤ))))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := by
  let c :
      K.obj ⟶ (K.obj)^∧[I, I.fg_of_isNoetherianRing] :=
    DerivedCategory.toDerivedCompletion I I.fg_of_isNoetherianRing K.obj
  have hc :
      IsDerivedCompletionIdealPowerQuotientTensorComparison I
        K.obj ((K.obj)^∧[I, I.fg_of_isNoetherianRing]) c := by
    sorry
  simpa [c] using
    cohomology_shortExact_of_derivedIdealPowerQuotientCompletionComparison I hc i

end

end
