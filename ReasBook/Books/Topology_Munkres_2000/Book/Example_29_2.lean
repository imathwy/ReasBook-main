module

public import Topology_Munkres_2000.Book.Definition_29_1.LocalCompactness
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Instances.Real.Lemmas

public section

/- Example 29.2 (1): Every finite power `Fin n → ℝ` is weakly locally compact. -/
#check fun n : ℕ ↦ (inferInstance : WeaklyLocallyCompactSpace (Fin n → ℝ))

/-- Example 29.2 (2): No point of the countable product `ℕ → ℝ` has a compact neighborhood. -/
theorem realSequences_not_isWeaklyLocallyCompactAt (x : ℕ → ℝ) :
    ¬ IsWeaklyLocallyCompactAt x := by
  classical
  rw [isWeaklyLocallyCompactAt_iff]
  rintro ⟨K, hKcompact, hKnhds⟩
  -- Every compact coordinate image omits a real number.
  have hproper (n : ℕ) : (fun z : ℕ → ℝ ↦ z n) '' K ≠ Set.univ :=
    (hKcompact.image (continuous_apply n)).ne_univ
  have hescape : ∀ n : ℕ, ∃ r : ℝ, r ∉ (fun z : ℕ → ℝ ↦ z n) '' K := by
    intro n
    exact (Set.ne_univ_iff_exists_notMem _).mp (hproper n)
  choose y hy using hescape
  -- A product neighborhood contains a point agreeing with `y` off finitely many coordinates.
  obtain ⟨I, hI⟩ := exists_finset_piecewise_mem_of_mem_nhds hKnhds y
  obtain ⟨n, hn⟩ := Infinite.exists_notMem_finset I
  -- At an unrestricted coordinate, membership in `K` contradicts the diagonal choice.
  apply hy n
  refine ⟨I.piecewise x y, hI, ?_⟩
  exact I.piecewise_eq_of_notMem x y hn

/-- Consequence for Example 29.2: The countable product `ℕ → ℝ` is not weakly locally compact. -/
theorem realSequences_not_weaklyLocallyCompact :
    ¬ WeaklyLocallyCompactSpace (ℕ → ℝ) := by
  intro h
  exact realSequences_not_isWeaklyLocallyCompactAt 0 (weaklyLocallyCompactSpace_iff.mp h 0)
