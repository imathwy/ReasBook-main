import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Separation.CompletelyRegular

-- Declarations for this item will be appended below by the statement pipeline.

open Set Topology OnePoint

universe u

section

variable {X : Type u} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]

/- Domain-style sampling for the Stone-Cech unit over a locally compact Hausdorff space:
- owner abstraction: `Topology.IsOpenEmbedding (stoneCechUnit : X → StoneCech X)`
- same-domain declarations inspected:
  `OnePoint.isOpenEmbedding_coe`,
  `continuous_stoneCechExtend`,
  `isDenseEmbedding_stoneCechUnit`,
  `Function.LeftInverse.isClosed_range`

Layer triage:
- `source-facing`: the canonical map identifies `X` with an open subspace of `StoneCech X`
- `core/canonical`: `Topology.IsOpenEmbedding` for `stoneCechUnit`
- `bridge/view`: extend the one-point compactification embedding along `stoneCechUnit`

Primitive data is just the canonical Stone-Cech unit together with the locally compact Hausdorff
hypothesis. The auxiliary maps into the open preimage subset are derived bridge data used only to
prove openness of the range, so this file should reuse the canonical owner declarations above
instead of introducing any parallel public wrapper for the image of `stoneCechUnit`.
-/
/-- Lemma 5.25.2: if `X` is Hausdorff and locally quasi-compact, then the canonical map from `X`
to its Stone-Cech compactification identifies `X` with an open subspace of `StoneCech X`. -/
theorem stoneCechUnit_isOpenEmbedding_of_locallyCompact_t2 :
    IsOpenEmbedding (stoneCechUnit : X → StoneCech X) := by
  have hcoe : IsOpenEmbedding ((↑) : X → OnePoint X) := OnePoint.isOpenEmbedding_coe
  haveI : T35Space X := hcoe.isEmbedding.t35Space
  set φ : StoneCech X → OnePoint X :=
    stoneCechExtend (OnePoint.continuous_coe : Continuous ((↑) : X → OnePoint X)) with hφ
  set rangeCoe : Set (OnePoint X) := Set.range ((↑) : X → OnePoint X) with hRangeCoe
  set U : Set (StoneCech X) := φ ⁻¹' rangeCoe with hU
  set R : Set (StoneCech X) := Set.range (stoneCechUnit : X → StoneCech X) with hR
  have hsub : R ⊆ U := by
    rintro _ ⟨x, rfl⟩
    rw [hU, hRangeCoe]
    exact ⟨x, by simp [hφ]⟩
  let i : R → U := Set.inclusion hsub
  let e : ((↑) : X → OnePoint X) ⁻¹' rangeCoe ≃ₜ rangeCoe :=
    hcoe.isEmbedding.homeomorphOfSubsetRange (by simp [hRangeCoe])
  have hu_mem (u : U) : φ u.1 ∈ rangeCoe := by
    show u.1 ∈ φ ⁻¹' rangeCoe
    rw [← hU]
    exact u.2
  let q : U → rangeCoe := fun u ↦ ⟨φ u.1, hu_mem u⟩
  let toX : U → X := fun u ↦ (e.symm (q u)).1
  let p : U → R := fun u ↦
    Set.rangeFactorization (stoneCechUnit : X → StoneCech X) (toX u)
  have hp_left : Function.LeftInverse p i := by
    intro r
    apply Subtype.ext
    rcases r with ⟨z, hz⟩
    rcases hz with ⟨x, rfl⟩
    change stoneCechUnit (toX (i ⟨stoneCechUnit x, ⟨x, rfl⟩⟩)) = stoneCechUnit x
    have hqix : q (i ⟨stoneCechUnit x, ⟨x, rfl⟩⟩) = e ⟨x, by simp [hRangeCoe]⟩ := by
      apply Subtype.ext
      simp [q, i, hφ, e]
    have hx : e.symm (e ⟨x, by simp [hRangeCoe]⟩) = ⟨x, by simp [hRangeCoe]⟩ :=
      e.symm_apply_apply ⟨x, by simp [hRangeCoe]⟩
    change stoneCechUnit ((e.symm (q (i ⟨stoneCechUnit x, ⟨x, rfl⟩⟩))).1) = stoneCechUnit x
    rw [hqix]
    exact congrArg (fun y ↦ stoneCechUnit y.1) hx
  have hφ_cont : Continuous φ := by
    simpa [hφ] using
      (continuous_stoneCechExtend
        (OnePoint.continuous_coe : Continuous ((↑) : X → OnePoint X)))
  have hq_cont : Continuous q := by
    exact (hφ_cont.comp continuous_subtype_val).subtype_mk hu_mem
  have htoX_cont : Continuous toX := by
    exact continuous_subtype_val.comp (Continuous.comp e.symm.continuous hq_cont)
  have hp_cont : Continuous p := by
    exact continuous_stoneCechUnit.rangeFactorization.comp htoX_cont
  have hi_cont : Continuous i := by
    simpa [i] using continuous_inclusion hsub
  have hclosed : IsClosed (Set.range i) := hp_left.isClosed_range hp_cont hi_cont
  have hdense : DenseRange i := by
    rw [show i = Set.inclusion hsub by rfl]
    rw [denseRange_inclusion_iff hsub]
    intro u hu
    have hclosure : closure R = Set.univ := by
      rw [hR]
      exact DenseRange.closure_range denseRange_stoneCechUnit
    rw [hclosure]
    simp
  have hrange : Set.range i = Set.univ := by
    rw [← hclosed.closure_eq, DenseRange.closure_range hdense]
  have hUR : U ⊆ R := by
    intro z hz
    have hz_range : (⟨z, hz⟩ : U) ∈ Set.range i := by
      rw [hrange]
      simp
    rcases hz_range with ⟨r, hr⟩
    have hEq : (r : StoneCech X) = z := congrArg Subtype.val hr
    exact hEq ▸ r.2
  have hUeqR : U = R := Set.Subset.antisymm hUR hsub
  have hUopen : IsOpen U := by
    rw [hU]
    simpa [hRangeCoe] using hcoe.isOpen_range.preimage hφ_cont
  have hRopen : IsOpen R := hUeqR.symm ▸ hUopen
  exact ⟨isEmbedding_stoneCechUnit, by simpa [hR] using hRopen⟩

end
