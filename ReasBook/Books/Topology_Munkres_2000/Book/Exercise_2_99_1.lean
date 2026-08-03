module

public import Mathlib.Topology.Algebra.Group.Defs

public section

universe u

/-- A group is a topological group exactly when its division map is continuous. -/
theorem isTopologicalGroup_iff_continuousDiv (G : Type u) [TopologicalSpace G] [Group G] :
    IsTopologicalGroup G ↔ ContinuousDiv G := by
  constructor
  · -- A topological group has continuous division by the standard mathlib instance.
    intro htop
    letI : IsTopologicalGroup G := htop
    infer_instance
  · -- Restrict division to `(1, x)` to recover continuity of inversion.
    intro hdiv
    letI : ContinuousDiv G := hdiv
    have hinv : Continuous fun x : G ↦ x⁻¹ := by
      have hOneDiv : Continuous fun x : G ↦ (1 : G) / x :=
        (continuous_const : Continuous fun _ : G ↦ (1 : G)).div' continuous_id
      refine hOneDiv.congr ?_
      intro x
      exact one_div x
    -- Applying division to `(x, y⁻¹)` then recovers continuous multiplication.
    have hmul : Continuous fun p : G × G ↦ p.1 * p.2 := by
      refine (continuous_fst.div' (hinv.comp continuous_snd)).congr ?_
      intro p
      exact div_inv_eq_mul p.1 p.2
    exact { continuous_mul := hmul, continuous_inv := hinv }

/-- Exercise 2.99.1: The group operations are continuous exactly when the map
`(x, y) ↦ x * y⁻¹` is continuous. The source's `T₁` assumption is not needed for this
equivalence. -/
theorem isTopologicalGroup_iff_continuous_mul_inv (H : Type u) [TopologicalSpace H] [Group H] :
    IsTopologicalGroup H ↔ Continuous (fun p : H × H ↦ p.1 * p.2⁻¹) := by
  constructor
  · -- Convert the canonical continuous-division conclusion to multiplication by inverse.
    intro htop
    have hdiv : ContinuousDiv H := (isTopologicalGroup_iff_continuousDiv H).mp htop
    simpa only [div_eq_mul_inv] using hdiv.continuous_div'
  · -- Package the source-facing map as continuous division and use the companion equivalence.
    intro hmulInv
    have hdiv : Continuous fun p : H × H ↦ p.1 / p.2 := by
      simpa only [div_eq_mul_inv] using hmulInv
    exact (isTopologicalGroup_iff_continuousDiv H).mpr ⟨hdiv⟩
