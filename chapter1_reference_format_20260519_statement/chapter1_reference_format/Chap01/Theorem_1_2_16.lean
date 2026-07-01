import Mathlib
import chapter1_reference_format.Chap01.Definition_1_2_15

-- Declarations for this item will be appended below by the statement pipeline.

open AbsoluteValue

universe u w

variable {K : Type u} [Field K] (v : AbsoluteValue K ℝ)

/- Auxiliary recall: the canonical completion of `v` is realized by the canonical embedding
`v.completionEmbedding : K →+* v.Completion`, and the source-facing owner `IsCompletion`
records exactly the existence data from Definition 1.2.15:
completeness, preservation of the absolute value, and density of the image. -/
#check (inferInstance : IsCompletion v v.completionEmbedding)

variable {L : Type w} [NormedField L]

-- Proof sketch: the owner abstraction `AbsoluteValue.IsCompletion v f` packages exactly the
-- primitive data of a completion from Definition 1.2.15: completeness of `L`, preservation of
-- the absolute value, and density of the image of `f`. From that data, extend `f` uniquely from
-- `K` to `v.Completion` via `Isometry.extensionHom`; density of the image makes the extended
-- isometric ring hom surjective, hence it upgrades to the uniquely determined isometric field
-- isomorphism extending `f`. The uniqueness is the field-level form of the canonical comparison
-- equivalence between two completion packages of the same uniform space.
/-- Theorem 1.2.16: any completion of the absolute value `v` is uniquely isometrically
field-isomorphic to the canonical completion `v.Completion`, via an isomorphism extending the
given embedding of `K`. -/
theorem absoluteValue_completion_unique
    (f : K →+* L) [IsCompletion v f] :
    ∃! e : v.Completion ≃+* L, Isometry e ∧
      ∀ x : K, e (v.completionEmbedding x) = f x := by
  let hf : IsCompletion v f := inferInstance
  let hnorm : ∀ x : WithAbs v, ‖(f.comp (WithAbs.equiv v).toRingHom) x‖ = v x.ofAbs :=
    fun x ↦ by simpa using hf.norm_eq x.ofAbs
  let g : v.Completion →+* L :=
    AbsoluteValue.Completion.extensionEmbedding_of_comp
      (v := v) (f := f.comp (WithAbs.equiv v).toRingHom) hnorm
  -- Extend the source embedding from `K` to the canonical completion.
  have hg_isometry : Isometry g := by
    simpa [g] using
      AbsoluteValue.Completion.isometry_extensionEmbedding_of_comp
        (v := v) (f := f.comp (WithAbs.equiv v).toRingHom) hnorm
  -- On the dense copy of `K`, the extension agrees with the given embedding.
  have hg_apply (x : K) : g (v.completionEmbedding x) = f x := by
    have hg_apply_coe (x : K) : g x = f x := by
      convert
        (AbsoluteValue.Completion.extensionEmbedding_of_comp_coe
          (v := v) (f := f.comp (WithAbs.equiv v).toRingHom) hnorm x) using 1
    simpa [AbsoluteValue.completionEmbedding] using hg_apply_coe x
  -- The image of the isometric extension is closed, and it contains the dense image of `f`.
  have hg_surj : Function.Surjective g := by
    intro y
    have hclosed : IsClosed (Set.range g) := by
      simpa [g] using hg_isometry.isUniformInducing.isComplete_range.isClosed
    have hsubset : Set.range f ⊆ Set.range g := by
      rintro _ ⟨x, rfl⟩
      exact ⟨v.completionEmbedding x, hg_apply x⟩
    have hy : y ∈ closure (Set.range g) := by
      have hy' : y ∈ closure (Set.range f) := by
        rw [(inferInstance : IsCompletion v f).denseRange.closure_range]
        simp
      exact closure_mono hsubset hy'
    rw [hclosed.closure_eq] at hy
    simpa [Set.mem_range] using hy
  let e : v.Completion ≃+* L := RingEquiv.ofBijective g ⟨hg_isometry.injective, hg_surj⟩
  refine ⟨e, ?_, ?_⟩
  · -- Package the bijective extension as the desired isometric field isomorphism.
    constructor
    · simpa [e] using hg_isometry
    · intro x
      exact hg_apply x
  · intro e' he'
    rcases he' with ⟨he'_isometry, he'_apply⟩
    -- Two continuous extensions out of the canonical completion agree once they agree on `K`.
    apply RingEquiv.ext
    intro z
    have hfun : (fun y : v.Completion ↦ e y) = fun y : v.Completion ↦ e' y :=
      DenseRange.equalizer (inferInstance : IsCompletion v v.completionEmbedding).denseRange
        (show Continuous fun y : v.Completion ↦ e y from hg_isometry.continuous)
        (show Continuous fun y : v.Completion ↦ e' y from he'_isometry.continuous)
        <| funext fun x ↦ by simpa using Eq.trans (hg_apply x) (he'_apply x).symm
    exact (congrFun hfun z).symm
