import Mathlib
import StacksProject_2024.Chap12.Definition_12_31_2
import StacksProject_2024.Chap15.Lemma_15_87_10
import StacksProject_2024.Chap15.Lemma_15_95_4
import StacksProject_2024.Chap15.Proposition_15_95_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem

universe u v

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)

/- Domain-style sampling for Lemma 15.98.6:
- primary domain: Milnor short exact sequences for derived inverse limits, specialized to the
  ideal-power quotient-tensor tower computing derived completion;
- sampled owner declarations:
  `CategoryTheory.derivedLimit_cohomology_shortExact`,
  `DerivedCategory.homologyCompletionComparison`,
  `DerivedCategory.homologyCompletionComparison_isIso`,
  `IsDerivedCompletionIdealPowerQuotientTensorComparison`;
- best owner abstraction: this numbered item is `source-facing`, but its primitive comparison data
  are still owned by the canonical Milnor short exact sequence and the derived-completion
  comparison morphism. Any chosen `ι` and `π` from the Milnor sequence are only `bridge/view`
  witnesses and should not remain in the public theorem surface;
- primitive vs. derived:
  primitive data are the ideal `I`, the derived object `K`, the degree `i`, the finite cohomology
  hypothesis, and the Mittag-Leffler hypothesis on the previous-degree tower;
  derived API is the resulting canonical object-level isomorphism between
  `(H^i(K))^∧` and `lim H^i(K_n)`, while the chosen Milnor comparison
  `H^i(K^∧) ⟶ lim H^i(K_n)` remains internal bridge data. -/

/-- The quotient module `M / I^(n + 1) M`. -/
abbrev idealPowerModuleQuotient (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M]
    (n : ℕ) : Type v :=
  M ⧸ (I ^ (n + 1) • (⊤ : Submodule A M))

/-- The `n`th quotient stage `M / I^(n + 1) M` in the ideal-power inverse system of an
`A`-module. -/
abbrev idealPowerQuotientStage (I : Ideal A) (M : ModuleCat A) (n : ℕ) :
    ModuleCat A :=
  ModuleCat.of A (idealPowerModuleQuotient I M n)

/-- The transition morphism `M / I^(n + 2) M ⟶ M / I^(n + 1) M` in the ideal-power quotient
inverse system. -/
abbrev idealPowerQuotientStep (I : Ideal A) (M : ModuleCat A) (n : ℕ) :
    idealPowerQuotientStage I M (n + 1) ⟶
      idealPowerQuotientStage I M n :=
  ModuleCat.ofHom (AdicCompletion.transitionMap I M (Nat.le_succ (n + 1)))

/-- The sequential inverse system `(M / I^(n + 1) M)_n` attached to an `A`-module `M`. -/
abbrev idealPowerQuotientInverseSystem (I : Ideal A) (M : ModuleCat A) :
    SequentialInverseSystem (ModuleCat.{u} A) :=
  Functor.ofOpSequence (idealPowerQuotientStep I M)

/-- The inverse system
`(H^i((A / I^(n+1))[0] ⊗_A^{\mathbf L} K))_n`, which is canonically identified with the textbook
tower `(H^i(K ⊗_A^{\mathbf L} A / I^(n+1)))_n` over a commutative base ring. -/
abbrev idealPowerQuotientTensorHomologyInverseSystem
    (I : Ideal A) (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    SequentialInverseSystem (ModuleCat.{u} A) :=
  (idealPowerQuotientTensorDerivedInverseSystem I K) ⋙ H i

private theorem toDerivedCompletion_isDerivedCompletionIdealPowerQuotientTensorComparison
    (I : Ideal A) (K : DMod) :
    IsDerivedCompletionIdealPowerQuotientTensorComparison I
      K
      (K^∧[I, I.fg_of_isNoetherianRing])
      (DerivedCategory.toDerivedCompletion I I.fg_of_isNoetherianRing K) := by
  sorry

private theorem exists_homologyDerivedCompletionToLimit
    (I : Ideal A) (K : DMod) (i : ℤ) :
    ∃ (π :
        (H i).obj (K^∧[I, I.fg_of_isNoetherianRing]) ⟶
          limit (idealPowerQuotientTensorHomologyInverseSystem I K i))
      (ι :
        firstDerivedLimit (idealPowerQuotientTensorHomologyInverseSystem I K (i - 1)) ⟶
          (H i).obj (K^∧[I, I.fg_of_isNoetherianRing]))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := by
  let c :
      K ⟶ K^∧[I, I.fg_of_isNoetherianRing] :=
    DerivedCategory.toDerivedCompletion I I.fg_of_isNoetherianRing K
  have hc :
      IsDerivedCompletionIdealPowerQuotientTensorComparison I
        K (K^∧[I, I.fg_of_isNoetherianRing]) c :=
    toDerivedCompletion_isDerivedCompletionIdealPowerQuotientTensorComparison I K
  rcases CategoryTheory.derivedLimit_cohomology_shortExact
      (idealPowerQuotientTensorDerivedInverseSystem I K)
      (K^∧[I, I.fg_of_isNoetherianRing]) hc.isDerivedLimit i with
    ⟨ι, π, h, hshort⟩
  refine ⟨π, ι, h, ?_⟩
  simpa [c, idealPowerQuotientTensorHomologyInverseSystem, sub_eq_add_neg] using hshort

/-- If `π : H^i(K^∧) ⟶ \varprojlim_n H^i(K_n)` appears in the Milnor short exact sequence for the
quotient-tensor tower and the previous-degree tower is Mittag-Leffler, then composing `π` with the
canonical comparison `(H^i(K))^∧ → H^i(K^∧)` from Lemma `15.95.4` yields an isomorphism. -/
private theorem homologyCompletionComparison_comp_isIso_of_shortExact
    (I : Ideal A) (K : DMod) (i : ℤ)
    (hKfinite : ∀ j : ℤ, Module.Finite A ((H j).obj K))
    (ι :
      firstDerivedLimit (idealPowerQuotientTensorHomologyInverseSystem I K (i - 1)) ⟶
        (H i).obj (K^∧[I, I.fg_of_isNoetherianRing]))
    (π :
      (H i).obj (K^∧[I, I.fg_of_isNoetherianRing]) ⟶
        limit (idealPowerQuotientTensorHomologyInverseSystem I K i))
    (h : ι ≫ π = 0)
    (hshort : (ShortComplex.mk ι π h).ShortExact)
    (hML_prev : (idealPowerQuotientTensorHomologyInverseSystem I K (i - 1)).IsMittagLeffler) :
    IsIso (DerivedCategory.homologyCompletionComparison I K i hKfinite ≫ π) := by
  have hzero :
      IsZero (firstDerivedLimit (idealPowerQuotientTensorHomologyInverseSystem I K (i - 1))) := by
    sorry
  haveI : IsIso π := (ShortComplex.ShortExact.isIso_g_iff hshort).2 hzero
  haveI : IsIso (DerivedCategory.homologyCompletionComparison I K i hKfinite) :=
    DerivedCategory.homologyCompletionComparison_isIso I K i hKfinite
  infer_instance

-- Proof sketch: Proposition `15.95.2` identifies derived completion with the derived inverse
-- limit of the ideal-power tensor tower. Lemma `15.95.4` identifies `H^i` of that derived
-- completion with the `I`-adic completion of `H^i(K)`, i.e. the inverse limit of the quotients
-- `H^i(K) / I^(n+1) H^i(K)`. Lemma `15.88.4` gives the Milnor short exact sequence for the right
-- derived inverse limit, whose left term is `R^1 lim H^{i-1}(K_n)`, and the Mittag-Leffler
-- hypothesis in degree `i - 1` kills that obstruction via Lemma `15.88.1`.
/-- Lemma 15.98.6 (Kollár-Kovács): let `I` be an ideal of the Noetherian ring `A`, let `K ∈ D(A)`,
and set `K_n = K ⊗_A^{\mathbf L} A / I^(n+1)`. If every `H^j(K)` is a finite `A`-module and the
inverse system `(H^{i - 1}(K_n))_n` satisfies the Mittag-Leffler condition, then there exists a
Milnor comparison from `(H^i(K))^∧` to `\varprojlim_n H^i(K_n)`, obtained by composing the
canonical map `(H^i(K))^∧ → H^i(K^∧)` with a Milnor comparison
`H^i(K^∧) → \varprojlim_n H^i(K_n)`. Since that Milnor comparison is chosen only through the
owner theorem `derivedLimit_cohomology_shortExact`, the public surface is the resulting canonical
object-level isomorphism between the completion of `H^i(K)` and the limit of the tower
`(H^i(K_n))_n`. The Lean indexing starts at `n = 0`, corresponding to the textbook power `I^1`. -/
theorem homology_idealPowerQuotient_limit_iso_tensorQuotient_homology_limit
    (I : Ideal A) (K : DMod) (i : ℤ)
    (hKfinite : ∀ j : ℤ, Module.Finite A ((H j).obj K))
    (hML_prev : (idealPowerQuotientTensorHomologyInverseSystem I K (i - 1)).IsMittagLeffler) :
    IsIsomorphic
      (ModuleCat.of A (AdicCompletion I ((H i).obj K)))
      (limit (idealPowerQuotientTensorHomologyInverseSystem I K i)) := by
  rcases exists_homologyDerivedCompletionToLimit I K i with ⟨π, ι, h, hshort⟩
  let φ :
      ModuleCat.of A (AdicCompletion I ((H i).obj K)) ⟶
        limit (idealPowerQuotientTensorHomologyInverseSystem I K i) :=
    DerivedCategory.homologyCompletionComparison I K i hKfinite ≫ π
  have hφ : IsIso φ := by
    simpa [φ] using
      homologyCompletionComparison_comp_isIso_of_shortExact
        I K i hKfinite ι π h hshort hML_prev
  let _ := hφ
  exact ⟨asIso φ⟩

end
