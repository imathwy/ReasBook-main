import StacksProject_2024.stacks_project.Chap15.PrincipalIdeal
import StacksProject_2024.stacks_project.Chap15.Lemma_15_89_9
import StacksProject_2024.stacks_project.Chap20.Global_sections_cohomology_delta_functor
import StacksProject_2024.stacks_project.Chap20.Lemma_20_11_2
import StacksProject_2024.stacks_project.Chap20.Lemma_20_35_3
import StacksProject_2024.stacks_project.Chap20.Lemma_20_36_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open CategoryTheory.DerivedCategory
open scoped PrincipalIdeal

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.36.2:
- primary domain: inverse-limit topologies and kernel filtrations on sequential cohomology systems
  of `Γ(X, 𝒪_X)`-modules;
- sampled owner declarations:
  * `CategoryTheory.inverseLimitTopology`;
  * `CategoryTheory.inverseLimitKernelFiltration`;
  * `moduleCohomologyDegreeAtOpen`;
  * `principalIdeal`;
  * `Ideal.adicModuleTopology`;
  * `moduleCohomologyAtOpen`.
- owner choice:
  * `source-facing`: the two cohomological consequences below for a tower satisfying
    `stepShortExactCondition`;
  * `core/canonical`: `inverseLimitTopology`, `inverseLimitKernelFiltration`, and the project
    owners `moduleCohomologyDegreeAtOpen`, `moduleCohomologyAtOpen`, and `principalIdeal`;
  * `bridge/view`: the cohomology system `ℱ ⋙ moduleCohomologyDegreeAtOpen TopOpen p`.
- primitive data: `f`, `ℱ`, the degree `p`, and the short-exactness hypothesis
  `stepShortExactCondition f ℱ`;
- derived API: the inverse limit `limit Hsys`, its kernel filtration, and its inverse-limit
  topology. -/

section

variable {X : RingedSpace.{u}}
variable (f : globalSectionsRing X) (ℱ : ℕᵒᵖ ⥤ RingedSpace.Modules X) (p : ℕ)

local notation "ΓX" => globalSectionsRing X
local notation "ModΓX" => ModuleCat ΓX
local notation "TopOpen" => (⊤ : Opens X.carrier)

private abbrev topOpenCohomologyDegree (p : ℕ) :
    RingedSpace.Modules X ⥤ ModΓX :=
  moduleCohomologyDegreeAtOpen TopOpen p

private abbrev cohomologySystem
    (ℱ : ℕᵒᵖ ⥤ RingedSpace.Modules X) (p : ℕ) :
    ℕᵒᵖ ⥤ ModΓX :=
  ℱ ⋙ topOpenCohomologyDegree p

local notation "Hsys" => cohomologySystem ℱ p
local notation "Hlim" => (limit Hsys : ModΓX)

/-- Helper for Lemma 20.36.2: under the step short exactness hypothesis, the stage
`ℱ_c` is annihilated by `f^c` for every `c ≥ 1`. -/
lemma globalSectionMulPow_stage_eq_zero
    (hℱ : stepShortExactCondition f ℱ) (c : ℕ) (hc : 1 ≤ c) :
    globalSectionMulPow f (ℱ.obj (op c)) c = 0 := by
  let π : ℱ.obj (op (c + 1)) ⟶ ℱ.obj (op c) :=
    SequentialInverseSystem.stepMap ℱ c
  let σ : ℱ.obj (op (c + 1)) ⟶ ℱ.obj (op 1) :=
    SequentialInverseSystem.transitionMap ℱ (Nat.succ_le_succ (Nat.zero_le c))
  have hpower : powerShortExactCondition f ℱ :=
    (powerShortExactCondition_iff_stepShortExactCondition f ℱ).2 hℱ
  have hpowerc :
      ∃ (ι : ℱ.obj (op 1) ⟶ ℱ.obj (op (c + 1))) (hιπ : ι ≫ π = 0),
        (ShortComplex.mk ι π hιπ).ShortExact ∧
          σ ≫ ι = globalSectionMulPow f (ℱ.obj (op (c + 1))) c := by
    simpa [π, σ] using hpower c hc
  rcases hpowerc with ⟨ι, hιπ, hshort, hσι⟩
  letI : Epi π := hshort.epi_g
  -- The source power map factors through the kernel of the transition `π`.
  have hzero : globalSectionMulPow f (ℱ.obj (op (c + 1))) c ≫ π = 0 := by
    rw [← hσι, Category.assoc, hιπ, comp_zero]
  -- Naturality moves the same power map to stage `c`.
  have hzero' : π ≫ globalSectionMulPow f (ℱ.obj (op c)) c = 0 := by
    calc
      π ≫ globalSectionMulPow f (ℱ.obj (op c)) c
          = globalSectionMulPow f (ℱ.obj (op (c + 1))) c ≫ π := by
              simpa using (globalSectionMulPow_natural f π c).symm
      _ = 0 := hzero
  -- Since `π` is epi in the short exact row, the stage-`c` power map itself vanishes.
  apply (cancel_epi π).1
  simpa using hzero'

/-- Helper for Lemma 20.36.2: on the degree-`p` branch of the canonical global cohomology owner,
`globalSectionMulPow` acts as scalar multiplication by `f ^ n`. -/
lemma cohomology_map_globalSectionMulPow_eq_smul
    (𝒜 : RingedSpace.Modules X) (n : ℕ) :
    ((globalCohomologyDeltaFunctor X p).obj).map (globalSectionMulPow f 𝒜 n) =
      ((f ^ n) • 𝟙 ((((globalCohomologyDeltaFunctor X p).obj).obj 𝒜))) := by
  sorry

/-- Helper for Lemma 20.36.2: the obvious inclusion `f^c H^p ⊆ ker(H^p → H^p(X, ℱ_c))`
comes from the fact that stage `c` is annihilated by `f^c`. -/
lemma pow_smul_top_le_inverseLimitKernelFiltration
    (hℱ : stepShortExactCondition f ℱ) (c : ℕ) (hc : 1 ≤ c) :
    ((((f) : Ideal ΓX) ^ c) • (⊤ : Submodule ΓX Hlim)) ≤
      inverseLimitKernelFiltration Hsys c := by
  have hann :
      (((f) : Ideal ΓX) ^ c) ≤ Module.annihilator ΓX Hlim := by
    sorry
  have hpowTop :
      ((((f) : Ideal ΓX) ^ c) • (⊤ : Submodule ΓX Hlim)) = ⊥ :=
    smul_top_eq_bot_of_le_annihilator ((((f) : Ideal ΓX) ^ c)) hann
  sorry

-- Proof sketch: for fixed `c ≥ 1`, the stepwise short exact sequences from
-- `stepShortExactCondition f ℱ` iterate to short exact sequences
-- `0 → ℱ_(n - c)`, then multiplication by `f^c`, then `ℱ_n → ℱ_c → 0` for `n ≥ c`.
-- Passing to the corresponding long exact cohomology sequences and then to the inverse limit
-- identifies the kernel of `H^p → H^p(X, ℱ_c)` with the image of multiplication by `f^c`.
/-
Lemma 20.36.2 (1): if the tower `(ℱ_n)` satisfies condition `(1)` of
Lemma `20.36.1` and `H^p = lim H^p(X, ℱ_n)`, then for every `c ≥ 1` the
submodule `f^c H^p` is the kernel of the projection `H^p → H^p(X, ℱ_c)`. In this
formalization `f^c H^p` is represented by the action of the `c`th power of the principal ideal
generated by `f`.
-/
-- Route correction: the easy inclusion should pass through the canonical Chapter 15 owner
-- `smul_top_eq_bot_of_le_annihilator`; the remaining source-faithful blocker is the reverse
-- inclusion, which still needs the compatible-lift construction along the fixed-stage rows
-- `0 → ℱ_(n + 1) → ℱ_(n + c + 1) → ℱ_c → 0`.
-- TODO: follow the source proof via the fixed-stage short exact rows
-- `0 → ℱ_(n + 1) → ℱ_(n + c + 1) → ℱ_c → 0`, then pass to the long exact cohomology sequence.
-- The remaining blocker is the tower-level bridge that turns those stagewise kernel/range
-- identifications into an equality inside `limit Hsys`.
/-- Helper for Lemma 20.36.2: the reverse inclusion should be proved by forming the fixed-stage
preimage tower of lifts and applying the countable Mittag-Leffler nonempty-sections theorem. -/
-- Route correction: the source proof does not hand-correct incompatible lifts one stage at a
-- time. Instead it uses the constant left term `H^(p - 1)(X, ℱ_c)` to package the chosen lifts
-- into a preimage inverse system, then extracts a compatible section globally.
-- TODO: define the fixed-stage preimage system over `Hsys.shift 1`, prove every stage is
-- nonempty from `ShortComplex.ShortExact.homology_exact₃`, show the system is Mittag-Leffler via
-- `Functor.IsMittagLeffler.toPreimages`, and convert the resulting section back to an element of
-- `limit Hsys` whose `f^c`-multiple is the given `x`.
lemma mem_pow_smul_top_of_mem_inverseLimitKernelFiltration
    (hℱ : stepShortExactCondition f ℱ) {c : ℕ} (hc : 1 ≤ c)
    {x : Hlim}
    (hx : x ∈ inverseLimitKernelFiltration Hsys c) :
    x ∈ ((((f) : Ideal ΓX) ^ c) • (⊤ : Submodule ΓX Hlim)) := by
  sorry

@[stacks 0EHA]
theorem cohomologyLimit_pow_eq_inverseLimitKernelFiltration
    (hℱ : stepShortExactCondition f ℱ) (c : ℕ) (hc : 1 ≤ c) :
    ((((f) : Ideal ΓX) ^ c) • (⊤ : Submodule ΓX Hlim)) =
      inverseLimitKernelFiltration Hsys c := by
  apply le_antisymm
  · -- This is the source proof's easy direction: `f^c H^p` dies in stage `c`.
    exact pow_smul_top_le_inverseLimitKernelFiltration f ℱ p hℱ c hc
  · -- Route correction: the remaining inclusion must follow the source's compatible-lift
    -- argument through the fixed-stage rows `0 → ℱ_(n + 1) → ℱ_(n + c + 1) → ℱ_c → 0`.
    intro x hx
    -- Delegate the hard direction to the source-faithful compatible-lift lemma above.
    exact mem_pow_smul_top_of_mem_inverseLimitKernelFiltration f ℱ p hℱ hc hx

theorem cohomologyLimit_pow_eq_kernel_projection
    (hℱ : stepShortExactCondition f ℱ) (c : ℕ) (hc : 1 ≤ c) :
    LinearMap.ker ((limit.π Hsys (op c)).hom) =
      ((((f) : Ideal ΓX) ^ c) • (⊤ : Submodule ΓX Hlim)) := by
  simpa [inverseLimitKernelFiltration] using
    (cohomologyLimit_pow_eq_inverseLimitKernelFiltration f ℱ p hℱ c hc).symm

-- Proof sketch: by part `(1)`, the neighborhoods of `0` in the inverse-limit topology are exactly
-- the kernels of the projections to `H^p(X, ℱ_c)`, hence exactly the powers of the
-- principal ideal generated by `f`. This matches the defining neighborhood basis of the
-- `f`-adic topology.
/-
Lemma 20.36.2 (2): under the same hypotheses, the limit topology on
`H^p = lim H^p(X, ℱ_n)` is the `f`-adic topology. -/
-- TODO: once part `(1)` identifies `inverseLimitKernelFiltration Hsys c` with `((f)^c) • ⊤`,
-- compare the neighborhood bases at `0` for `inverseLimitTopology Hsys` and
-- `Ideal.adicModuleTopology ((f) : Ideal ΓX)`.
@[stacks 0EHA]
theorem cohomologyLimitTopology_eq_adic_of_stepShortExactCondition
    (hℱ : stepShortExactCondition f ℱ) :
    inverseLimitTopology Hsys =
      Ideal.adicModuleTopology ((f) : Ideal ΓX) Hlim := by
  sorry

end

end AlgebraicGeometry.RingedSpace
