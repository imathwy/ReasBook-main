module

public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.SetTheory.Cardinal.Defs

public section

universe u v

namespace IsCoveringMap

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- Helper for Exercise 53.3: near any point, the fiber of a covering map is equivalent to
every fiber over a common open neighborhood. -/
private lemma exists_open_fiberEquiv {p : E → B} (hp : IsCoveringMap p) (b : B) :
    ∃ U : Set B, IsOpen U ∧ b ∈ U ∧
      ∀ b' ∈ U, Nonempty ((p ⁻¹' {b}) ≃ (p ⁻¹' {b'})) := by
  -- Retain the local product chart supplied by the covering map at `b`.
  rcases hp b with ⟨hDiscrete, U, hbU, hU, hpU, H, hH⟩
  refine ⟨U, hU, hbU, fun b' hb'U ↦ ?_⟩
  -- The same chart evenly covers each `b' ∈ U`, with the fiber over `b` as model fiber.
  have hb' : IsEvenlyCovered p b' (p ⁻¹' {b}) :=
    ⟨hDiscrete, U, hb'U, hU, hpU, H, hH⟩
  exact ⟨hb'.fiberHomeomorph.toEquiv⟩

/-- Helper for Exercise 53.3: the cardinality of the fiber of a covering map is locally
constant on the base. -/
private lemma isLocallyConstant_fiberCardinal {p : E → B} (hp : IsCoveringMap p) :
    IsLocallyConstant (fun b : B ↦ Cardinal.mk (p ⁻¹' {b})) := by
  -- Use local fiber equivalences as the neighborhood criterion for local constancy.
  rw [IsLocallyConstant.iff_exists_open]
  intro b
  obtain ⟨U, hU, hbU, hEquiv⟩ := exists_open_fiberEquiv hp b
  refine ⟨U, hU, hbU, fun b' hb'U ↦ ?_⟩
  -- Equivalent fibers have equal cardinals, with the orientation required by the criterion.
  exact (Cardinal.eq.mpr (hEquiv b' hb'U)).symm

omit [TopologicalSpace E] [TopologicalSpace B] in
/-- Helper for Exercise 53.3: a singleton preimage is the set described by its fiber equation. -/
private lemma preimage_singleton_eq_fiber (p : E → B) (b : B) :
    p ⁻¹' {b} = {e | p e = b} := by
  -- Normalize membership in both presentations of the fiber.
  ext e
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]

/-- Exercise 53.3. Any two fibers of a covering map over a connected base are equivalent. -/
theorem fiberEquiv [ConnectedSpace B] {p : E → B} (hp : IsCoveringMap p) (b₀ b : B) :
    Nonempty ({e : E // p e = b₀} ≃ {e : E // p e = b}) := by
  -- Connectedness makes the locally constant fiber cardinal take the same value at both points.
  have hCardinal : Cardinal.mk (p ⁻¹' {b₀}) = Cardinal.mk (p ⁻¹' {b}) :=
    (isLocallyConstant_fiberCardinal hp).apply_eq_of_preconnectedSpace b₀ b
  -- Convert cardinal equality to an equivalence, then cross the two fiber presentations.
  obtain ⟨e⟩ := Cardinal.eq.mp hCardinal
  have hSource := preimage_singleton_eq_fiber p b₀
  have hTarget := preimage_singleton_eq_fiber p b
  exact ⟨(Equiv.setCongr hSource.symm).trans (e.trans (Equiv.setCongr hTarget))⟩

/-- Helper for Exercise 53.3: if one fiber of a covering map over a connected base has exactly
`k` elements, then every fiber has exactly `k` elements. -/
theorem fiberEquivFin [ConnectedSpace B] {p : E → B} (hp : IsCoveringMap p)
    {b₀ : B} {k : ℕ} (h₀ : Nonempty ({e : E // p e = b₀} ≃ Fin k)) (b : B) :
    Nonempty ({e : E // p e = b} ≃ Fin k) := by
  obtain ⟨e⟩ := hp.fiberEquiv b₀ b
  obtain ⟨e₀⟩ := h₀
  exact ⟨e.symm.trans e₀⟩

end IsCoveringMap
