import Mathlib
import DifferentialForms_Cartan_1970.cartan.V.section18.«0002_Definition_V_1_extra_2»
import DifferentialForms_Cartan_1970.cartan.V.section20.«0001_Definition_V_3_extra_1»

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

-- Domain sampling: this file is source-facing in the complex infinite-product / normal-convergence
-- domain. The chapter owner on a fixed compact set is `NormallyMultipliableOn`, and the generic
-- compact-majorant owner for series is the earlier project declaration
-- `NormallyConvergentOnCompacta`. Primitive data for the compacta product notion: for each
-- compact `K ⊆ D`, the fixed-compact owner `NormallyMultipliableOn f D K`, which already packages
-- the slit-plane logarithmic tail. Derived API: the canonical uniform and locally uniform product
-- limits.

/-- Definition V.3-extra-2 (1): the infinite product `∏ n, f n z` converges normally on compact
subsets of `D` when every compact subset `K ⊆ D` satisfies the fixed-compact owner
`NormallyMultipliableOn f D K`. -/
abbrev NormallyMultipliableOnCompacta (f : ℕ → ℂ → ℂ) (D : Set ℂ) : Prop :=
  ∀ ⦃K : Set ℂ⦄, IsCompact K → K ⊆ D → NormallyMultipliableOn f D K

/-- If an infinite product converges normally on compact subsets of `D`, then each compact
`K ⊆ D` carries the canonical uniform product limit. -/
theorem NormallyMultipliableOnCompacta.hasProdUniformlyOn {f : ℕ → ℂ → ℂ} {D K : Set ℂ}
    (h : NormallyMultipliableOnCompacta f D) (hK : IsCompact K) (hKD : K ⊆ D) :
    HasProdUniformlyOn f (fun z ↦ ∏' n, f n z) K := by
  exact (h hK hKD).hasProdUniformlyOn hK

/-- Normal convergence of the product on compact subsets forces the domain `D` to be open. -/
theorem NormallyMultipliableOnCompacta.isOpen_domain {f : ℕ → ℂ → ℂ} {D : Set ℂ}
    (h : NormallyMultipliableOnCompacta f D) :
    IsOpen D :=
  (h isCompact_empty (Set.empty_subset D)).isOpen_domain

/-- Normal convergence of the product on compact subsets forces each factor to be continuous on
`D`. -/
theorem NormallyMultipliableOnCompacta.continuousOn {f : ℕ → ℂ → ℂ} {D : Set ℂ}
    (h : NormallyMultipliableOnCompacta f D) (n : ℕ) :
    ContinuousOn (f n) D :=
  (h isCompact_empty (Set.empty_subset D)).continuousOn n

/-- On an open set `D`, compact-normal convergence supplies the canonical locally uniform product
limit on `D`. -/
theorem NormallyMultipliableOnCompacta.hasProdLocallyUniformlyOn {f : ℕ → ℂ → ℂ} {D : Set ℂ}
    (h : NormallyMultipliableOnCompacta f D) :
    HasProdLocallyUniformlyOn f (fun z ↦ ∏' n, f n z) D := by
  apply hasProdLocallyUniformlyOn_of_forall_compact h.isOpen_domain
  intro K hKD hK
  exact h.hasProdUniformlyOn hK hKD

/-- At each point `z ∈ D`, compact-normal convergence supplies the canonical pointwise product
limit. -/
theorem NormallyMultipliableOnCompacta.hasProd {f : ℕ → ℂ → ℂ} {D : Set ℂ}
    (h : NormallyMultipliableOnCompacta f D) {z : ℂ} (hz : z ∈ D) :
    HasProd (fun n ↦ f n z) (∏' n, f n z) := by
  have hsubset : ({z} : Set ℂ) ⊆ D := by
    intro w hw
    simpa [Set.mem_singleton_iff.mp hw] using hz
  have hsingleton : HasProdUniformlyOn f (fun w ↦ ∏' n, f n w) ({z} : Set ℂ) :=
    h.hasProdUniformlyOn isCompact_singleton hsubset
  simpa using hsingleton.hasProd (by simp)

/-- At each point `z ∈ D`, compact-normal convergence yields pointwise multipliability of the
factor sequence. -/
theorem NormallyMultipliableOnCompacta.multipliable {f : ℕ → ℂ → ℂ} {D : Set ℂ}
    (h : NormallyMultipliableOnCompacta f D) {z : ℂ} (hz : z ∈ D) :
    Multipliable (fun n ↦ f n z) :=
  (h.hasProd hz).multipliable

/-- Definition V.3-extra-2 (2): for factors written as `f n z = 1 + u n z`, normal convergence of
the product on compact subsets of `D` is equivalent to normal convergence of `∑ n, u n z` on
compact subsets of `D` in the fixed-compact sense of Definition V.3-extra-1, uniformly for every
compact `K ⊆ D`. -/
theorem normallyMultipliableOnCompacta_one_add_iff {u : ℕ → ℂ → ℂ} {D : Set ℂ} :
    NormallyMultipliableOnCompacta (fun n z ↦ 1 + u n z) D ↔
      IsOpen D ∧ (∀ n, ContinuousOn (u n) D) ∧
        ∀ ⦃K : Set ℂ⦄, IsCompact K → K ⊆ D →
          ∃ N : ℕ, (∀ n, Set.MapsTo (fun z ↦ 1 + u (n + N) z) K Complex.slitPlane) ∧
            NormallySummableOn (fun n z ↦ Complex.log (1 + u (n + N) z)) K := by
  constructor
  · intro h
    refine ⟨h.isOpen_domain, ?_, ?_⟩
    · intro n
      have hcont : ContinuousOn (fun z ↦ (1 + u n z) - 1) D :=
        (h.continuousOn n).sub continuousOn_const
      simpa using hcont
    · intro K hK hKD
      rcases (normallyMultipliableOn_one_add_iff.mp (h hK hKD)) with ⟨_, _, _, htail⟩
      exact htail
  · rintro ⟨hD, hu_cont, htail⟩
    intro K hK hKD
    exact (normallyMultipliableOn_one_add_iff.mpr ⟨hD, hKD, hu_cont, htail hK hKD⟩)

section OneAdd

variable {X R : Type*} [TopologicalSpace X] [NormedCommRing R] [NormOneClass R]
  [CompleteSpace R]

/-- Definition V.3-extra-2 (3): if `∑ n, u n z` is normally convergent on compact subsets of `D`
and the perturbations `u n` are continuous on `D`, then for every compact `K ⊆ D` the partial
products `∏ n ∈ Finset.range N, (1 + u n z)` converge uniformly on `K` to
`∏' n, (1 + u n z)`. -/
theorem NormallyConvergentOnCompacta.hasProdUniformlyOn_compact_one_add {u : ℕ → X → R}
    {D K : Set X} (h : NormallyConvergentOnCompacta u D) (hu_cont : ∀ n, ContinuousOn (u n) D)
    (hK : IsCompact K) (hKD : K ⊆ D) :
    HasProdUniformlyOn (fun n z ↦ 1 + u n z) (fun z ↦ ∏' n, (1 + u n z)) K := by
  rcases h hK hKD with ⟨a, ha, hbound⟩
  exact ha.hasProdUniformlyOn_nat_one_add hK
    (by
      rw [Filter.eventually_atTop]
      exact ⟨0, fun n _ z hz ↦ hbound n z hz⟩)
    (fun n ↦ (hu_cont n).mono hKD)

section LocallyCompact

variable [LocallyCompactSpace X]

/-- Under the hypotheses of Definition V.3-extra-2 (3), the product `∏' n, (1 + u n z)`
converges locally uniformly on `D`. -/
theorem NormallyConvergentOnCompacta.hasProdLocallyUniformlyOn_one_add {u : ℕ → X → R}
    {D : Set X} (h : NormallyConvergentOnCompacta u D) (hD : IsOpen D)
    (hu_cont : ∀ n, ContinuousOn (u n) D) :
    HasProdLocallyUniformlyOn (fun n z ↦ 1 + u n z) (fun z ↦ ∏' n, (1 + u n z)) D := by
  apply hasProdLocallyUniformlyOn_of_forall_compact hD
  intro K hKD hK
  exact h.hasProdUniformlyOn_compact_one_add hu_cont hK hKD

/-- Definition V.3-extra-2 (4): under the same compact-normal summability hypothesis, the limit
function `z ↦ ∏' n, (1 + u n z)` is continuous on `D`. -/
theorem NormallyConvergentOnCompacta.continuousOn_tprod_one_add {u : ℕ → X → R} {D : Set X}
    (h : NormallyConvergentOnCompacta u D) (hD : IsOpen D)
    (hu_cont : ∀ n, ContinuousOn (u n) D) :
    ContinuousOn (fun z ↦ ∏' n, (1 + u n z)) D := by
  let hprod := h.hasProdLocallyUniformlyOn_one_add hD hu_cont
  exact hprod.tendstoLocallyUniformlyOn_finsetRange.continuousOn <|
    Filter.Frequently.of_forall fun N ↦
      continuousOn_finsetProd (Finset.range N) fun n _ ↦ (hu_cont n).const_add (1 : R)

end LocallyCompact
end OneAdd
