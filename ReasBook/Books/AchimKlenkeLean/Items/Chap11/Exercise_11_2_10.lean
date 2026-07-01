import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section

variable (μ : Measure Ω) [IsFiniteMeasure μ]
variable (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)

local notation "TerminalValueSpace" => lpMeas ℝ ℝ (⨆ n, ℱ n) 1 μ
local notation "ProcessSpace" => ℕ → Lp ℝ 1 μ

/- Exercise 11.2.10 is `source-facing`: it identifies the actual vector space of uniformly
integrable `ℱ`-martingales with the terminal-value space `L¹(⨆ n, ℱ n)`. The
`core/canonical` owner abstractions are the existing martingale and uniform-integrability APIs on
processes, together with the `L¹` conditional-expectation operator `condExpL1CLM`. The quotient
level codomain is therefore organized as the submodule of `L¹`-classes admitting an actual
uniformly integrable martingale representative, while the conditional-expectation process map is
the `bridge/view` from a terminal class to that submodule. -/

/-- The `Lp`-valued conditional-expectation martingale attached to an `L¹(ℱ∞)` terminal class. -/
noncomputable def terminalValueMartingaleProcess :
    TerminalValueSpace →ₗ[ℝ] ProcessSpace where
  toFun X := fun n ↦ condExpL1CLM ℝ (ℱ.le n) μ (X : Lp ℝ 1 μ)
  map_add' := by
    intro X Y
    funext n
    exact map_add (condExpL1CLM ℝ (ℱ.le n) μ) (X : Lp ℝ 1 μ) (Y : Lp ℝ 1 μ)
  map_smul' := by
    intro c X
    funext n
    exact map_smul (condExpL1CLM ℝ (ℱ.le n) μ) c (X : Lp ℝ 1 μ)

/-- A quotient-level process is a uniformly integrable `ℱ`-martingale if it admits an actual
uniformly integrable martingale representative. -/
def IsUiMartingaleProcess (f : ProcessSpace) : Prop :=
  ∃ X : ℕ → Ω → ℝ, Martingale X ℱ μ ∧ UniformIntegrable X 1 μ ∧
    ∀ n, (f n : Ω → ℝ) =ᵐ[μ] X n

omit [IsFiniteMeasure μ] in
private theorem uniformIntegrable_zero_process :
    UniformIntegrable (0 : ℕ → Ω → ℝ) 1 μ := by
  refine ⟨fun _ ↦ aestronglyMeasurable_zero, ?_, ⟨0, fun _ ↦ by simp⟩⟩
  intro ε hε
  refine ⟨1, zero_lt_one, fun _ _ _ _ ↦ by simp⟩

omit [IsFiniteMeasure μ] in
private theorem uniformIntegrable_add {f g : ℕ → Ω → ℝ}
    (hf : UniformIntegrable f 1 μ) (hg : UniformIntegrable g 1 μ) :
    UniformIntegrable (f + g) 1 μ := by
  refine ⟨fun n ↦ (hf.aestronglyMeasurable n).add (hg.aestronglyMeasurable n), ?_, ?_⟩
  · exact hf.unifIntegrable.add hg.unifIntegrable le_rfl
      (fun n ↦ hf.aestronglyMeasurable n) (fun n ↦ hg.aestronglyMeasurable n)
  · rcases hf.2.2 with ⟨Cf, hCf⟩
    rcases hg.2.2 with ⟨Cg, hCg⟩
    refine ⟨Cf + Cg, fun n ↦ ?_⟩
    exact (eLpNorm_add_le (hf.aestronglyMeasurable n) (hg.aestronglyMeasurable n) le_rfl).trans
      (add_le_add (hCf n) (hCg n))

private theorem uniformIntegrable_smul (c : ℝ) {f : ℕ → Ω → ℝ}
    (hf : UniformIntegrable f 1 μ) :
    UniformIntegrable (c • f) 1 μ := by
  sorry

/-- The quotient-level vector space of uniformly integrable `ℱ`-martingales. -/
def uiMartingaleSubmodule : Submodule ℝ ProcessSpace where
  carrier := {f | IsUiMartingaleProcess μ ℱ f}
  zero_mem' := by
    refine ⟨0, martingale_zero ℝ ℱ μ, uniformIntegrable_zero_process μ,
      fun _ ↦ Lp.coeFn_zero ℝ 1 μ⟩
  add_mem' := by
    sorry
  smul_mem' := by
    sorry

local notation "UiMartingaleSpace" => uiMartingaleSubmodule μ ℱ

/-- Each terminal `L¹(ℱ∞)` class yields a uniformly integrable martingale after taking its
conditional expectations. -/
theorem terminalValueMartingaleProcess_is_ui_martingale (X : TerminalValueSpace) :
    Martingale (fun n ↦ terminalValueMartingaleProcess μ ℱ X n) ℱ μ ∧
      UniformIntegrable (fun n ↦ terminalValueMartingaleProcess μ ℱ X n) 1 μ := by
  sorry

private theorem terminalValueMartingaleProcess_mem_uiMartingaleSubmodule (X : TerminalValueSpace) :
    terminalValueMartingaleProcess μ ℱ X ∈ UiMartingaleSpace := by
  refine ⟨fun n ↦ terminalValueMartingaleProcess μ ℱ X n,
    (terminalValueMartingaleProcess_is_ui_martingale μ ℱ X).1,
    (terminalValueMartingaleProcess_is_ui_martingale μ ℱ X).2,
    fun _ ↦ .of_forall fun _ ↦ rfl⟩

/-- Source-facing form of Exercise 11.2.10: a quotient-level `L¹` process lies in the canonical
space of uniformly integrable martingales exactly when it is the conditional-expectation
martingale of some terminal `L¹(ℱ∞)` class. -/
theorem mem_uiMartingaleSpace_iff_exists_terminalValue (f : ProcessSpace) :
    f ∈ UiMartingaleSpace ↔
      ∃ X : TerminalValueSpace, ∀ n, f n = terminalValueMartingaleProcess μ ℱ X n := by
  sorry

private theorem terminalValueMartingaleProcess_injective :
    Function.Injective (terminalValueMartingaleProcess μ ℱ) := by
  intro X Y hXY
  sorry

/-- Exercise 11.2.10: the vector space of uniformly integrable `ℱ`-martingales is linearly
equivalent to the terminal-value space `L¹(⨆ n, ℱ n)`. -/
noncomputable def terminalValueToUiMartingale :
    TerminalValueSpace →ₗ[ℝ] UiMartingaleSpace where
  toFun X := ⟨terminalValueMartingaleProcess μ ℱ X,
    terminalValueMartingaleProcess_mem_uiMartingaleSubmodule μ ℱ X⟩
  map_add' := by
    sorry
  map_smul' := by
    sorry

/-- Exercise 11.2.10: the canonical bridge from terminal `L¹(ℱ∞)` classes to uniformly
integrable `ℱ`-martingales is a linear isomorphism. -/
noncomputable def terminalValueToUiMartingale_isomorphism :
    TerminalValueSpace ≃ₗ[ℝ] UiMartingaleSpace := by
  refine LinearEquiv.ofBijective (terminalValueToUiMartingale μ ℱ) ?_
  constructor
  · intro X Y hXY
    exact terminalValueMartingaleProcess_injective μ ℱ (by
      simpa [terminalValueToUiMartingale] using congrArg Subtype.val hXY)
  · intro f
    rcases (mem_uiMartingaleSpace_iff_exists_terminalValue μ ℱ f.1).mp f.2 with
      ⟨X, hX⟩
    refine ⟨X, ?_⟩
    apply Subtype.ext
    funext n
    exact (hX n).symm

/-- The linear equivalence is induced by the canonical conditional-expectation process map. -/
theorem terminalValueToUiMartingale_isomorphism_apply (X : TerminalValueSpace) :
    terminalValueToUiMartingale_isomorphism μ ℱ X =
      terminalValueToUiMartingale μ ℱ X :=
  rfl

end
