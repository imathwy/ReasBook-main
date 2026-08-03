import BauschkeLean.Chap21.Theorem_21_9
import BauschkeLean.Chap23.Corollary_23_11
import BauschkeLean.Chap23.Proposition_23_8

-- Semantic recall: `lean_leansearch` surfaced the generic convex-topology owners
-- `closedConvexHull`, `closedConvexHull_eq_closure_convexHull`, and
-- `subset_closedConvexHull`; this item keeps the source-facing conclusion on
-- `closure (convexHull ℝ (Set.range T))` and uses the verified local Chapter 23 owners
-- `FirmlyNonexpansiveOn` and `FirmlyNonexpansive`.

open scoped Pointwise SetValuedOperator
open ERealFunction

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Theorem 23.15 extends a firmly nonexpansive map from a nonempty subset.
- `core/canonical`: the extension owner is a maximally monotone extension of
  `((ofFunction D T)⁻¹ - id.toSetValuedOperator)`.
- `bridge/view`: the ambient extension map is the canonical resolvent realizer
  `resolventMap Atilde hAtilde (1 : PosReal)`. -/

/-- Theorem 23.15: if `D` is nonempty and `T : D → H` is firmly nonexpansive on `D`, then there
exists a firmly nonexpansive ambient extension `Ttilde : H → H` such that `Ttilde` agrees with
`T` on `D`, written as `∀ x : D, Ttilde x = T x`, and
`Set.range Ttilde ⊆ closure (convexHull ℝ (Set.range T))`. -/
theorem exists_firmlyNonexpansive_extension_range_subset_closure_convexHull_range
    (D : Set H) (hD : D.Nonempty) (T : D → H) (hT : FirmlyNonexpansiveOn D T) :
    ∃ Ttilde : H → H,
      FirmlyNonexpansive Ttilde ∧
        (∀ x : D, Ttilde x = T x) ∧
          Set.range Ttilde ⊆ closure (convexHull ℝ (Set.range T)) := by
  let A : SetValuedOperator H H := (ofFunction D T)⁻¹ - id.toSetValuedOperator
  have hJ : J[A] = ofFunction D T := by
    simpa [A] using resolvent_sub_id_inverse_ofFunction_eq_ofFunction D T
  have hA_mono : A.IsMonotone := by
    exact (isMonotone_iff_firmlyNonexpansiveOn_of_resolvent_eq_ofFunction A D T hJ).2 hT
  have hA_graph : (gra A).Nonempty := by
    rcases hD with ⟨x, hx⟩
    let xD : D := ⟨x, hx⟩
    have hTx_mem : T xD ∈ J[A] (xD : H) := by
      rw [hJ, ofFunction_apply_of_mem D T xD.2]
      simp
    refine ⟨(T xD, (xD : H) - T xD), ?_⟩
    simpa using
      (mem_resolvent_smul_iff_mem_graph A (1 : PosReal) (xD : H) (T xD)).1 <| by
        simpa using hTx_mem
  obtain ⟨Atilde, hAext, hAmax, hAtilde_dom⟩ :=
    exists_isMaximallyMonotone_extension_dom_subset_convexHull_dom A hA_mono hA_graph
  let Ttilde : H → H := resolventMap Atilde hAmax (1 : PosReal)
  refine ⟨Ttilde, ?_, ?_, ?_⟩
  · exact
      resolvent_smul_firmlyNonexpansive_of_toSetValuedOperator_eq
        Atilde hAmax (1 : PosReal) Ttilde (resolventMap_toSetValuedOperator_eq Atilde hAmax _)
  · intro x
    have hTx_mem : T x ∈ J[A] (x : H) := by
      rw [hJ, ofFunction_apply_of_mem D T x.2]
      simp
    have hTx_graph : (T x, (x : H) - T x) ∈ gra A := by
      simpa using
        (mem_resolvent_smul_iff_mem_graph A (1 : PosReal) (x : H) (T x)).1 <| by
          simpa using hTx_mem
    have hTx_graph_tilde : (T x, (x : H) - T x) ∈ gra Atilde := by
      rw [SetValuedOperator.mem_graph] at hTx_graph ⊢
      exact hAext _ hTx_graph
    have hTx_mem_tilde : T x ∈ J[((1 : ℝ) • Atilde)] (x : H) := by
      exact
        (mem_resolvent_smul_iff_mem_graph Atilde (1 : PosReal) (x : H) (T x)).2 <| by
          simpa using hTx_graph_tilde
    have hsingleton : J[((1 : ℝ) • Atilde)] (x : H) = ({Ttilde (x : H)} : Set H) := by
      simpa [Ttilde] using
        resolvent_smul_eq_singleton_resolventMap_of_maximal
          Atilde hAmax (1 : PosReal) (x : H)
    rw [hsingleton, Set.mem_singleton_iff] at hTx_mem_tilde
    simpa [Ttilde] using hTx_mem_tilde.symm
  · rintro y ⟨x, rfl⟩
    have hsingleton : J[((1 : ℝ) • Atilde)] x = ({Ttilde x} : Set H) := by
      simpa [Ttilde] using
        resolvent_smul_eq_singleton_resolventMap_of_maximal
          Atilde hAmax (1 : PosReal) x
    have hTx_mem : Ttilde x ∈ J[((1 : ℝ) • Atilde)] x := by
      rw [hsingleton]
      simp [Ttilde]
    have hTx_graph : (Ttilde x, x - Ttilde x) ∈ gra Atilde := by
      simpa [Ttilde] using
        (mem_resolvent_smul_iff_mem_graph Atilde (1 : PosReal) x (Ttilde x)).1 hTx_mem
    have hTx_dom : Ttilde x ∈ Atilde.dom := by
      rw [SetValuedOperator.mem_dom_iff]
      exact ⟨x - Ttilde x, by simpa [SetValuedOperator.mem_graph] using hTx_graph⟩
    have hA_dom_subset : A.dom ⊆ Set.range T := by
      intro z hz
      rcases (SetValuedOperator.mem_dom_iff A z).1 hz with ⟨u, hu⟩
      have hu' :
          ∃ w, z ∈ ofFunction D T w ∧ w - z = u := by
        simpa [A] using hu
      rcases hu' with ⟨w, hw, _⟩
      rcases hw with ⟨hwD, hwT⟩
      exact ⟨⟨w, hwD⟩, hwT.symm⟩
    exact
      subset_closure <|
        (convexHull_mono hA_dom_subset) (hAtilde_dom hTx_dom)

end SetValuedOperator
