import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Topology.Algebra.Module.Basic

noncomputable section

open AffineMap

section NormedFieldSpan

variable {𝕜 V P : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [PseudoMetricSpace P] [NormedAddTorsor V P]

/-- Local affine-basis extension theorem over a nontrivially normed field. This project-owned
version avoids modifying vendored mathlib and provides the scalar-general statement needed by local
downstream files. -/
theorem IsOpen.exists_between_affineIndependent_span_eq_top_of_nontriviallyNormedField
    {s u : Set P} (hu : IsOpen u) (hsu : s ⊆ u) (hne : s.Nonempty)
    (h : AffineIndependent 𝕜 ((↑) : s → P)) :
    ∃ t : Set P, s ⊆ t ∧ t ⊆ u ∧ AffineIndependent 𝕜 ((↑) : t → P) ∧ affineSpan 𝕜 t = ⊤ := by
  obtain ⟨q, hq⟩ := hne
  obtain ⟨t, ht₁, ht₂, ht₃⟩ := exists_subset_affineIndependent_affineSpan_eq_top h
  have hcu : ∀ p ∈ t, p ∉ s → ∃ c : 𝕜ˣ, lineMap q p (c : 𝕜) ∈ u := by
    intro p hp hps
    let g : 𝕜 → P := fun c => c • (p -ᵥ q : V) +ᵥ q
    have hsmul :
        Filter.Tendsto (fun c : 𝕜 => c • (p -ᵥ q : V)) (nhds (0 : 𝕜)) (nhds (0 : V)) := by
      simpa [zero_smul] using
        ((Filter.tendsto_id : Filter.Tendsto (fun c : 𝕜 => c) (nhds (0 : 𝕜))
            (nhds (0 : 𝕜))).smul_const (p -ᵥ q : V))
    have hg : Filter.Tendsto g (nhds (0 : 𝕜)) (nhds q) := by
      simpa [g] using
        hsmul.vadd
          (tendsto_const_nhds : Filter.Tendsto (fun _ : 𝕜 => q) (nhds (0 : 𝕜)) (nhds q))
    have hg' : Filter.Tendsto g (nhdsWithin (0 : 𝕜) ({0}ᶜ)) (nhds q) :=
      hg.mono_left (nhdsWithin_le_nhds : nhdsWithin (0 : 𝕜) ({0}ᶜ) ≤ nhds (0 : 𝕜))
    have hmem : {c : 𝕜 | g c ∈ u} ∈ nhdsWithin (0 : 𝕜) ({0}ᶜ) :=
      hg'.eventually (hu.mem_nhds (hsu hq))
    have hmem' : ({c : 𝕜 | g c ∈ u} ∩ ({0}ᶜ : Set 𝕜)) ∈ nhdsWithin (0 : 𝕜) ({0}ᶜ) :=
      Filter.inter_mem hmem eventually_mem_nhdsWithin
    rcases Filter.nonempty_of_mem hmem' with ⟨c, hc⟩
    have hcU : g c ∈ u := hc.1
    have hc0 : c ≠ 0 := by simpa using hc.2
    refine ⟨Units.mk0 c hc0, ?_⟩
    simpa [g, lineMap_apply] using hcU
  classical
  let w : t → 𝕜ˣ := fun p => if hp : (p : P) ∈ s then 1 else Classical.choose (hcu (↑p) p.2 hp)
  refine ⟨Set.range fun p : t => lineMap q p (w p : 𝕜), ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact ⟨⟨p, ht₁ hp⟩, by simp [w, hp]⟩
  · rintro y ⟨⟨p, hp⟩, rfl⟩
    by_cases hps : p ∈ s
    · simpa [w, hps] using hsu hps
    · simpa [w, hps] using Classical.choose_spec (hcu p hp hps)
  · exact (ht₂.units_lineMap ⟨q, ht₁ hq⟩ w).range
  · rw [affineSpan_eq_affineSpan_lineMap_units (ht₁ hq) w, ht₃]

/-- A nonempty open set in a normed affine space over a nontrivially normed field contains an
affine-independent subset spanning the whole space. -/
theorem IsOpen.exists_subset_affineIndependent_span_eq_top_of_nontriviallyNormedField
    {u : Set P} (hu : IsOpen u) (hne : u.Nonempty) :
    ∃ s ⊆ u, AffineIndependent 𝕜 ((↑) : s → P) ∧ affineSpan 𝕜 s = ⊤ := by
  rcases hne with ⟨x, hx⟩
  have hxind : AffineIndependent 𝕜 ((↑) : ({x} : Set P) → P) :=
    by simpa using (affineIndependent_of_subsingleton (k := 𝕜)
      ((↑) : ({x} : Set P) → P))
  rcases hu.exists_between_affineIndependent_span_eq_top_of_nontriviallyNormedField
      (Set.singleton_subset_iff.mpr hx) (Set.singleton_nonempty x) hxind
    with ⟨s, -, hsu, hs⟩
  exact ⟨s, hsu, hs⟩

/-- The affine span of a nonempty open set is `⊤` over a nontrivially normed field. -/
theorem IsOpen.affineSpan_eq_top_of_nontriviallyNormedField {u : Set P} (hu : IsOpen u)
    (hne : u.Nonempty) : affineSpan 𝕜 u = ⊤ := by
  rcases (IsOpen.exists_subset_affineIndependent_span_eq_top_of_nontriviallyNormedField
      (𝕜 := 𝕜) (V := V) (P := P) hu hne) with
    ⟨s, hsu, -, hs'⟩
  exact top_unique <| hs' ▸ affineSpan_mono _ hsu

end NormedFieldSpan
