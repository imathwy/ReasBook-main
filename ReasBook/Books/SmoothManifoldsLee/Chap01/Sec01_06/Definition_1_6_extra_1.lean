import Mathlib

noncomputable section

open scoped Topology Manifold ContDiff

variable {n k : ℕ} [NeZero n]
variable {U : Set (EuclideanHalfSpace n)}
variable {f : EuclideanHalfSpace n → EuclideanSpace ℝ (Fin k)}

/- Definition 1.6-extra-1: smoothness on an open subset of the Euclidean half-space is expressed
by `ContMDiffOn (𝓡∂ n) (𝓡 k) ∞ f U` for the standard manifold-with-boundary model. -/
recall ContMDiffOn

/-- Helper for Definition 1.6-extra-1: on the Euclidean half-space, `ContMDiffOn` in the boundary
model is exactly `ContDiffOn` on the ambient half-space image. -/
lemma contMDiffOn_halfSpace_iff_contDiffOn_image :
    ContMDiffOn (𝓡∂ n) (𝓡 k) ∞ f U ↔
      ContDiffOn ℝ ∞
        (fun z : EuclideanSpace ℝ (Fin n) ↦ f ((𝓡∂ n).symm z))
        ((𝓡∂ n) '' U) := by
  -- The source has a single global boundary chart, and the Euclidean target chart is the identity.
  simpa [Function.comp, extChartAt_self_eq, extChartAt_model_space_eq_id] using
    (contMDiffOn_iff_of_subset_source' (I := 𝓡∂ n) (I' := 𝓡 k)
      (x := (0 : EuclideanHalfSpace n))
      (y := (0 : EuclideanSpace ℝ (Fin k)))
      (s := U) (f := f)
      (hs := by
        intro x hx
        simp)
      (h2s := by
        intro x hx
        simp))

/-- Helper for Definition 1.6-extra-1: an open subset of the half-space admits an ambient open
neighborhood around each of its points, and the half-space preimage of that neighborhood is still
contained in the subset. -/
lemma open_halfSpace_neighborhood_of_open_subtype_set (hU : IsOpen U) {x : EuclideanHalfSpace n}
    (hx : x ∈ U) :
    ∃ V : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen V ∧ x.1 ∈ V ∧ ((𝓡∂ n) ⁻¹' V) ⊆ U := by
  rcases hU.image_val with ⟨V, hV, hImage⟩
  refine ⟨V, hV, ?_, ?_⟩
  · -- Membership in the ambient open set comes from the image description of `U`.
    have hxImage : x.1 ∈ Subtype.val '' U := ⟨x, hx, rfl⟩
    have hxImage' : x.1 ∈ V ∩ { y : EuclideanSpace ℝ (Fin n) | 0 ≤ y 0 } := by
      exact hImage ▸ hxImage
    exact hxImage'.1
  · -- Any half-space point over `V` lies in `U` because `Subtype.val '' U = V ∩ s`.
    intro y hy
    have hyImage : y.1 ∈ Subtype.val '' U := by
      have hyImage' : y.1 ∈ V ∩ { z : EuclideanSpace ℝ (Fin n) | 0 ≤ z 0 } := ⟨hy, y.2⟩
      exact hImage.symm ▸ hyImage'
    rcases hyImage with ⟨z, hzU, hzEq⟩
    exact Subtype.ext hzEq ▸ hzU

/-- Helper for Definition 1.6-extra-1: agreement on the half-space preimage of an ambient set is
equivalent to agreement on the corresponding ambient points that lie in the half-space image. -/
lemma eqOn_halfSpace_preimage_iff_eqOn_range_inter
    {V : Set (EuclideanSpace ℝ (Fin n))}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k)} :
    Set.EqOn (fun z : EuclideanHalfSpace n ↦ g z.1) f ((𝓡∂ n) ⁻¹' V) ↔
      Set.EqOn g (fun z ↦ f ((𝓡∂ n).symm z)) (V ∩ Set.range (𝓡∂ n)) := by
  constructor
  · intro h z hz
    rcases hz.2 with ⟨x, rfl⟩
    -- On points coming from the half-space, the inverse chart returns the original subtype point.
    simpa [ModelWithCorners.left_inv] using h hz.1
  · intro h z hz
    have hzRange : z.1 ∈ V ∩ Set.range (𝓡∂ n) := by
      refine ⟨hz, ?_⟩
      exact ⟨z, rfl⟩
    have hzSymm : (𝓡∂ n).symm z.1 = z := by
      exact ModelWithCorners.left_inv (I := 𝓡∂ n) z
    -- Applying the ambient equality on `z.1` gives the required equality back on the subtype.
    simpa [hzSymm] using h hzRange

/-- Helper for Definition 1.6-extra-1: if the half-space preimage of an ambient set lies in `U`,
then the ambient points of that set that lie in the half-space image already come from `U`. -/
lemma ambient_range_slice_subset_halfSpace_image
    {V : Set (EuclideanSpace ℝ (Fin n))}
    (hVU : ((𝓡∂ n) ⁻¹' V) ⊆ U) :
    V ∩ Set.range (𝓡∂ n) ⊆ ((𝓡∂ n) '' U) := by
  intro z hz
  rcases hz.2 with ⟨x, rfl⟩
  -- Any point of the ambient slice is represented by a half-space point whose image stays in `U`.
  exact ⟨x, hVU hz.1, rfl⟩

/-- Helper for Definition 1.6-extra-1: the local ambient extension hypothesis implies
`ContDiffOn` on the half-space image in the ambient Euclidean space. -/
lemma contDiffOn_halfSpace_image_of_forall_exists_smoothAmbientExtension
    (hExt :
      ∀ x ∈ U,
        ∃ V : Set (EuclideanSpace ℝ (Fin n)),
          IsOpen V ∧
          x.1 ∈ V ∧
          ((𝓡∂ n) ⁻¹' V) ⊆ U ∧
          ∃ g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k),
            ContDiffOn ℝ ∞ g V ∧
            Set.EqOn (fun z : EuclideanHalfSpace n ↦ g z.1) f ((𝓡∂ n) ⁻¹' V)) :
    ContDiffOn ℝ ∞
      (fun z : EuclideanSpace ℝ (Fin n) ↦ f ((𝓡∂ n).symm z))
      ((𝓡∂ n) '' U) := by
  intro z hz
  rcases hz with ⟨x, hxU, rfl⟩
  rcases hExt x hxU with ⟨V, hV, hxV, hVU, g, hg, hgEq⟩
  have hgAt : ContDiffAt ℝ ∞ g x.1 := (hV.contDiffOn_iff.mp hg) hxV
  have hEqRange :
      Set.EqOn g (fun y ↦ f ((𝓡∂ n).symm y)) (V ∩ Set.range (𝓡∂ n)) :=
    (eqOn_halfSpace_preimage_iff_eqOn_range_inter (f := f) (V := V) (g := g)).mp hgEq
  have hEqImage :
      Set.EqOn
        (fun y : EuclideanSpace ℝ (Fin n) ↦ f ((𝓡∂ n).symm y))
        g
        (((𝓡∂ n) '' U) ∩ V) := by
    intro y hy
    have hyRange : y ∈ Set.range (𝓡∂ n) := by
      rcases hy.1 with ⟨u, huU, rfl⟩
      exact ⟨u, rfl⟩
    -- The image points already lie in the half-space range, so the ambient equality applies.
    exact (hEqRange ⟨hy.2, hyRange⟩).symm
  have hEqEvent :
      (fun y : EuclideanSpace ℝ (Fin n) ↦ f ((𝓡∂ n).symm y)) =ᶠ[𝓝[((𝓡∂ n) '' U)] x.1] g := by
    -- Restricting within `((𝓡∂ n) '' U)` and then to the ambient open set `V` gives local equality.
    refine Filter.eventuallyEq_of_mem
      (inter_mem_nhdsWithin ((𝓡∂ n) '' U) (hV.mem_nhds hxV)) ?_
    exact hEqImage
  have hxImage : x.1 ∈ (𝓡∂ n) '' U := ⟨x, hxU, rfl⟩
  -- Replace the ambient extension by the original function on the half-space image.
  exact hgAt.contDiffWithinAt.congr_of_eventuallyEq_of_mem hEqEvent hxImage

/-- Helper for Definition 1.6-extra-1: an interior point of the half-space image already has an
ambient smooth extension by restricting to an open neighborhood inside the image. -/
lemma interior_halfSpace_image_exists_local_ambient_extension
    (hU : IsOpen U)
    (hCont :
      ContDiffOn ℝ ∞
        (fun z : EuclideanSpace ℝ (Fin n) ↦ f ((𝓡∂ n).symm z))
        ((𝓡∂ n) '' U))
    {x : EuclideanHalfSpace n} (hx : x ∈ U) (hx0 : 0 < x.1 0) :
    ∃ V : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen V ∧
      x.1 ∈ V ∧
      ((𝓡∂ n) ⁻¹' V) ⊆ U ∧
      ∃ g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k),
        ContDiffOn ℝ ∞ g V ∧
        Set.EqOn (fun z : EuclideanHalfSpace n ↦ g z.1) f ((𝓡∂ n) ⁻¹' V) := by
  rcases open_halfSpace_neighborhood_of_open_subtype_set (U := U) hU hx with
    ⟨V₀, hV₀, hxV₀, hV₀U⟩
  refine ⟨V₀ ∩ interior (Set.range (𝓡∂ n)), hV₀.inter isOpen_interior, ?_, ?_, ?_⟩
  · -- Positive first coordinate places `x.1` in the interior of the half-space image.
    have hxInterior : x.1 ∈ interior (Set.range (𝓡∂ n)) := by
      rw [interior_range_modelWithCornersEuclideanHalfSpace n]
      exact hx0
    exact ⟨hxV₀, hxInterior⟩
  · -- Shrinking the ambient neighborhood does not change the already verified preimage inclusion.
    intro y hy
    exact hV₀U hy.1
  · refine ⟨fun z ↦ f ((𝓡∂ n).symm z), ?_, ?_⟩
    · -- On the interior slice, the ambient function is already smooth
      -- on an open subset of the image.
      have hVImage :
          V₀ ∩ interior (Set.range (𝓡∂ n)) ⊆ ((𝓡∂ n) '' U) := by
        intro y hy
        have hyRange : y ∈ Set.range (𝓡∂ n) := by
          rw [interior_range_modelWithCornersEuclideanHalfSpace n] at hy
          have hy0 : 0 < y 0 := by
            simpa using hy.2
          rw [range_modelWithCornersEuclideanHalfSpace n]
          exact le_of_lt hy0
        exact ambient_range_slice_subset_halfSpace_image (U := U) hV₀U ⟨hy.1, hyRange⟩
      exact hCont.mono hVImage
    · -- On actual half-space points, the ambient inverse recovers the original subtype point.
      intro z hz
      have hzSymm : (𝓡∂ n).symm z.1 = z := by
        exact ModelWithCorners.left_inv (I := 𝓡∂ n) z
      simp [hzSymm]

/-- Helper for Definition 1.6-extra-1: at boundary points of the half-space image, the remaining
step is the genuine local ambient `C^∞` extension theorem from the closed half-space. -/
lemma contDiffOn_range_halfSpace_exists_open_extension_at
    {W : Set (EuclideanSpace ℝ (Fin n))}
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k)}
    (hW : IsOpen W) {x : EuclideanSpace ℝ (Fin n)} (hxW : x ∈ W)
    (hxRange : x ∈ Set.range (𝓡∂ n)) (hx0 : x 0 = 0)
    (hF : ContDiffOn ℝ ∞ F (W ∩ Set.range (𝓡∂ n))) :
    ∃ V : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen V ∧
      x ∈ V ∧
      V ⊆ W ∧
      ∃ g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k),
        ContDiffOn ℝ ∞ g V ∧
        Set.EqOn g F (V ∩ Set.range (𝓡∂ n)) := by
  -- TODO: prove the local closed-half-space extension theorem cited in Definition 1.6-extra-1,
  -- producing an ambient smooth extension near a boundary point from `ContDiffOn` on
  -- `W ∩ Set.range (𝓡∂ n)`.
  sorry

/-- Helper for Definition 1.6-extra-1: at boundary points of the half-space image, the remaining
step is the genuine local ambient `C^∞` extension theorem from the closed half-space. -/
lemma boundary_halfSpace_image_exists_local_ambient_extension
    (hU : IsOpen U)
    (hCont :
      ContDiffOn ℝ ∞
        (fun z : EuclideanSpace ℝ (Fin n) ↦ f ((𝓡∂ n).symm z))
        ((𝓡∂ n) '' U))
    {x : EuclideanHalfSpace n} (hx : x ∈ U) (hx0 : x.1 0 = 0) :
    ∃ V : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen V ∧
      x.1 ∈ V ∧
      ((𝓡∂ n) ⁻¹' V) ⊆ U ∧
      ∃ g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k),
        ContDiffOn ℝ ∞ g V ∧
        Set.EqOn (fun z : EuclideanHalfSpace n ↦ g z.1) f ((𝓡∂ n) ⁻¹' V) := by
  rcases open_halfSpace_neighborhood_of_open_subtype_set (U := U) hU hx with
    ⟨V₀, hV₀, hxV₀, hV₀U⟩
  have hxRange : x.1 ∈ Set.range (𝓡∂ n) := ⟨x, rfl⟩
  have hContV₀ :
      ContDiffOn ℝ ∞
        (fun z : EuclideanSpace ℝ (Fin n) ↦ f ((𝓡∂ n).symm z))
        (V₀ ∩ Set.range (𝓡∂ n)) := by
    -- The ambient slice over `V₀` still lies in the global half-space image where `hCont` applies.
    refine hCont.mono ?_
    exact ambient_range_slice_subset_halfSpace_image (U := U) hV₀U
  rcases contDiffOn_range_halfSpace_exists_open_extension_at
      (n := n) (k := k) (W := V₀) (F := fun z ↦ f ((𝓡∂ n).symm z))
      hV₀ hxV₀ hxRange hx0 hContV₀ with
    ⟨V, hV, hxV, hVV₀, g, hg, hEq⟩
  have hVU : ((𝓡∂ n) ⁻¹' V) ⊆ U := by
    -- The local ambient neighborhood stays inside the original half-space neighborhood.
    intro y hy
    exact hV₀U (hVV₀ hy)
  have hEqHalf :
      Set.EqOn (fun z : EuclideanHalfSpace n ↦ g z.1) f ((𝓡∂ n) ⁻¹' V) := by
    -- Convert the ambient equality on `V ∩ Set.range (𝓡∂ n)` back to subtype points.
    exact (eqOn_halfSpace_preimage_iff_eqOn_range_inter
      (f := f) (V := V) (g := g)).mpr hEq
  -- Packaging the ambient extension finishes the boundary branch.
  exact ⟨V, hV, hxV, hVU, g, hg, hEqHalf⟩

/-- Helper for Definition 1.6-extra-1: turning `ContDiffOn` on the half-space image into a local
ambient `C^∞` extension is exactly the missing closed-half-space extension theorem. -/
lemma forall_exists_smoothAmbientExtension_of_contDiffOn_halfSpace_image
    (hU : IsOpen U)
    (hCont :
      ContDiffOn ℝ ∞
        (fun z : EuclideanSpace ℝ (Fin n) ↦ f ((𝓡∂ n).symm z))
        ((𝓡∂ n) '' U)) :
    ∀ x ∈ U,
      ∃ V : Set (EuclideanSpace ℝ (Fin n)),
        IsOpen V ∧
        x.1 ∈ V ∧
        ((𝓡∂ n) ⁻¹' V) ⊆ U ∧
        ∃ g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k),
          ContDiffOn ℝ ∞ g V ∧
          Set.EqOn (fun z : EuclideanHalfSpace n ↦ g z.1) f ((𝓡∂ n) ⁻¹' V) := by
  intro x hx
  rcases lt_or_eq_of_le x.2 with hx0 | hx0
  · -- Interior points are handled by shrinking to an open neighborhood contained in the image.
    exact interior_halfSpace_image_exists_local_ambient_extension
      (U := U) (f := f) hU hCont hx hx0
  · -- Boundary points are the only remaining place where a true extension theorem is needed.
    exact boundary_halfSpace_image_exists_local_ambient_extension
      (U := U) (f := f) hU hCont hx hx0.symm

/-- Definition 1.6-extra-1: on an open subset of the Euclidean half-space, manifold smoothness for
the standard boundary model is equivalent to the textbook local smooth ambient-extension
condition. -/
-- Proof sketch: reduce `ContMDiffOn` to `ContDiffOn` on the ambient half-space image, use the
-- local ambient-extension hypothesis to recover the ambient `ContDiffOn` statement, and note that
-- the only missing ingredient in the opposite direction is the closed-half-space `C^∞` extension
-- theorem isolated in `forall_exists_smoothAmbientExtension_of_contDiffOn_halfSpace_image`.
theorem contMDiffOn_halfSpace_iff_forall_exists_smoothAmbientExtension (hU : IsOpen U) :
    ContMDiffOn (𝓡∂ n) (𝓡 k) ∞ f U ↔
      ∀ x ∈ U,
        ∃ V : Set (EuclideanSpace ℝ (Fin n)),
          IsOpen V ∧
          x.1 ∈ V ∧
          ((𝓡∂ n) ⁻¹' V) ⊆ U ∧
          ∃ g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k),
            ContDiffOn ℝ ∞ g V ∧
            Set.EqOn (fun z : EuclideanHalfSpace n ↦ g z.1) f ((𝓡∂ n) ⁻¹' V) := by
  constructor
  · intro h
    have hCont :
        ContDiffOn ℝ ∞
          (fun z : EuclideanSpace ℝ (Fin n) ↦ f ((𝓡∂ n).symm z))
          ((𝓡∂ n) '' U) :=
      (contMDiffOn_halfSpace_iff_contDiffOn_image (U := U) (f := f)).mp h
    -- The forward implication is exactly the isolated ambient `C^∞` extension step.
    exact forall_exists_smoothAmbientExtension_of_contDiffOn_halfSpace_image
      (U := U) (f := f) hU hCont
  · intro hExt
    have hCont :
        ContDiffOn ℝ ∞
          (fun z : EuclideanSpace ℝ (Fin n) ↦ f ((𝓡∂ n).symm z))
          ((𝓡∂ n) '' U) :=
      contDiffOn_halfSpace_image_of_forall_exists_smoothAmbientExtension
        (U := U) (f := f) hExt
    -- Reassembling the chart reduction recovers the manifold-with-boundary statement.
    exact (contMDiffOn_halfSpace_iff_contDiffOn_image (U := U) (f := f)).mpr hCont
