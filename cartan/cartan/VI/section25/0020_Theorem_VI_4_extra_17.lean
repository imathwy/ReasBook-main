import Mathlib
import cartan.III.section11.«0003_Theorem_III_5_extra_2»

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: no `lean_leansearch` MCP tool was exposed in this session, so the
-- statement surface below follows the local `ω dz` / oriented-boundary residue-theorem API.

/-- Theorem VI.4-extra-17: theorem of residues for a single oriented boundary. Here `ω` is the
holomorphic coefficient of the differential form `ω(z) dz`, `E` is the closed singular
set, and `s` is an explicit enumeration of the finitely many points of `E ∩ K`. If the oriented
boundary `Γ` of the compact set `K` avoids `E`, then the integral of `ω(z) dz` along `Γ` is
`2π i` times the sum of the residues at the points of `E` situated in `K`. -/
theorem theorem_of_residues_on_oriented_boundary
    {K E : Set ℂ} (Γ : ClosedPath ℂ) {ω residue : ℂ → ℂ} (s : Finset ℂ)
    (hΓ : IsOrientedBoundaryOf K (fun _ : Unit ↦ Γ))
    (hΓE : Disjoint (Set.range Γ.toPath) E)
    (hE_closed : IsClosed E)
    (hs : (↑s : Set ℂ) = E ∩ K)
    (hω_holomorphic : DifferentiableOn ℂ ω Eᶜ)
    (hres :
      ∀ z ∈ s,
        IsolatedLocalResidueCircle K (interior K ∪ Eᶜ) s ω z (residue z)) :
    ∫ᶜ z in Γ.toPath, (ω dz) z =
      (2 * Real.pi * Complex.I : ℂ) * Finset.sum s residue := by
  have hfrontier_eq : Set.range Γ.toPath = frontier K := by
    rw [← hΓ.iUnion_range_eq_frontier]
    ext z
    simp
  have hfrontierE : Disjoint (frontier K) E := by
    simpa [hfrontier_eq] using hΓE
  have hKD : K ⊆ interior K ∪ Eᶜ := by
    intro z hzK
    by_cases hzInt : z ∈ interior K
    · exact Or.inl hzInt
    · have hzFront : z ∈ frontier K := by
        have hK_closed : IsClosed K := hΓ.isCompact.isClosed
        exact ⟨by simpa [hK_closed.closure_eq] using hzK, hzInt⟩
      have hzNotE : z ∉ E := by
        intro hzE
        exact (Set.disjoint_left.1 hfrontierE) hzFront hzE
      exact Or.inr hzNotE
  have hD : IsOpen (interior K ∪ Eᶜ) := isOpen_interior.union hE_closed.isOpen_compl
  have hhol : DifferentiableOn ℂ ω ((interior K ∪ Eᶜ) \ (↑s : Set ℂ)) := by
    refine hω_holomorphic.mono ?_
    intro z hz
    rcases hz with ⟨hzD, hzNotS⟩
    by_cases hzE : z ∈ E
    · have hzInt : z ∈ interior K := by
        rcases hzD with hzInt | hzEc
        · exact hzInt
        · exact False.elim (hzEc hzE)
      exact False.elim <| hzNotS <| by
        rw [hs]
        exact ⟨hzE, interior_subset hzInt⟩
    · exact hzE
  simpa using
    orientedBoundary_sum_curveIntegral_eq_two_pi_I_mul_sum_residue
      (fun _ : Unit ↦ Γ) s residue hΓ hKD hD hhol hres
