import SmoothManifolds_Lee_2012.Chap06.Sec06_43.Definition_6_43_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

noncomputable section

universe uM uHM uEM uN uHN uEN

variable {EM : Type uEM} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
variable {HM : Type uHM} [TopologicalSpace HM]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]
variable {I : ModelWithCorners ℝ EM HM} [IsManifold I ⊤ M]

variable {EN : Type uEN} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
variable {HN : Type uHN} [TopologicalSpace HN]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace HN N]
variable {K : ModelWithCorners ℝ EN HN} [IsManifold K ⊤ N]

namespace ContMDiffMap

-- The source-facing smooth homotopy owner is `ContMDiffMap.SmoothHomotopy` from
-- `Definition_6_43_extra_1.lean`; this lemma records that the induced relation
-- `ContMDiffMap.SmoothlyHomotopic` is an equivalence relation.

namespace SmoothHomotopy

/-- Helper for Lemma 6.28: projecting an affine real function back to `I` gives a smooth interval
reparametrization. -/
lemma contMDiff_reverseParam :
    ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞
      (fun t : Set.Icc (0 : ℝ) 1 => Set.projIcc 0 1 zero_le_one ((-1 : ℝ) * (t : ℝ) + 1)) := by
  -- Pull back to `[0, 1] ⊆ ℝ`, where the affine formula lands in `[0, 1]` and composition
  -- with the interval projection is manifestly smooth.
  rw [← contMDiffOn_comp_projIcc_iff (x := (0 : ℝ)) (y := 1) (n := ∞)
      (f := fun t : Set.Icc (0 : ℝ) 1 => Set.projIcc 0 1 zero_le_one ((-1 : ℝ) * (t : ℝ) + 1))]
  have hAffine : ContDiffOn ℝ ∞ (fun x : ℝ => (-1 : ℝ) * x + 1) (Set.Icc (0 : ℝ) 1) := by
    fun_prop
  have hMain : ContMDiffOn 𝓘(ℝ) (𝓡∂ 1) ∞
      (fun x : ℝ => Set.projIcc 0 1 zero_le_one ((-1 : ℝ) * x + 1)) (Set.Icc (0 : ℝ) 1) :=
    (contMDiffOn_projIcc (x := (0 : ℝ)) (y := 1) (n := ∞)).comp hAffine.contMDiffOn fun x hx => by
      constructor <;> linarith [hx.1, hx.2]
  exact hMain.congr fun x hx => by
    simp [Function.comp, Set.projIcc_of_mem zero_le_one hx]

/-- Helper for Lemma 6.28: reversing the interval parameter is a smooth self-map of `I`. -/
def reverseParam : C^∞⟮𝓡∂ 1, Set.Icc (0 : ℝ) 1; 𝓡∂ 1, Set.Icc (0 : ℝ) 1⟯ :=
  ⟨fun t => Set.projIcc 0 1 zero_le_one ((-1 : ℝ) * (t : ℝ) + 1), contMDiff_reverseParam⟩

/-- Helper for Lemma 6.28: the left plateau reparametrization is smooth. -/
lemma contMDiff_leftPlateauParam :
    ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞
      (fun t : Set.Icc (0 : ℝ) 1 => Set.projIcc 0 1 zero_le_one
        (Real.smoothTransition (4 * (t : ℝ)))) := by
  -- The real-valued core is smooth and already lands in `[0, 1]`, so the final projection is just
  -- a codomain packaging step.
  rw [← contMDiffOn_comp_projIcc_iff (x := (0 : ℝ)) (y := 1) (n := ∞)
      (f := fun t : Set.Icc (0 : ℝ) 1 => Set.projIcc 0 1 zero_le_one
        (Real.smoothTransition (4 * (t : ℝ))))]
  have hSmooth : ContDiff ℝ ∞ (fun x : ℝ => Real.smoothTransition (4 * x)) := by
    fun_prop
  have hMain : ContMDiffOn 𝓘(ℝ) (𝓡∂ 1) ∞
      (fun x : ℝ => Set.projIcc 0 1 zero_le_one (Real.smoothTransition (4 * x)))
      (Set.Icc (0 : ℝ) 1) :=
    (contMDiffOn_projIcc (x := (0 : ℝ)) (y := 1) (n := ∞)).comp
      hSmooth.contDiffOn.contMDiffOn fun x hx => by
      constructor
      · exact Real.smoothTransition.nonneg _
      · exact Real.smoothTransition.le_one _
  exact hMain.congr fun x hx => by
    simp [Function.comp, Set.projIcc_of_mem zero_le_one hx]

/-- Helper for Lemma 6.28: the left concatenation branch reaches time `1` before the cutoff. -/
def leftPlateauParam : C^∞⟮𝓡∂ 1, Set.Icc (0 : ℝ) 1; 𝓡∂ 1, Set.Icc (0 : ℝ) 1⟯ :=
  ⟨fun t => Set.projIcc 0 1 zero_le_one (Real.smoothTransition (4 * (t : ℝ))),
    contMDiff_leftPlateauParam⟩

/-- Helper for Lemma 6.28: the right plateau reparametrization is smooth. -/
lemma contMDiff_rightPlateauParam :
    ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞
      (fun t : Set.Icc (0 : ℝ) 1 => Set.projIcc 0 1 zero_le_one
        (Real.smoothTransition (4 * (t : ℝ) - 3))) := by
  -- As above, the real-valued core is smooth and already takes values in `[0, 1]`.
  rw [← contMDiffOn_comp_projIcc_iff (x := (0 : ℝ)) (y := 1) (n := ∞)
      (f := fun t : Set.Icc (0 : ℝ) 1 => Set.projIcc 0 1 zero_le_one
        (Real.smoothTransition (4 * (t : ℝ) - 3)))]
  have hSmooth : ContDiff ℝ ∞ (fun x : ℝ => Real.smoothTransition (4 * x - 3)) := by
    fun_prop
  have hMain : ContMDiffOn 𝓘(ℝ) (𝓡∂ 1) ∞
      (fun x : ℝ => Set.projIcc 0 1 zero_le_one (Real.smoothTransition (4 * x - 3)))
      (Set.Icc (0 : ℝ) 1) :=
    (contMDiffOn_projIcc (x := (0 : ℝ)) (y := 1) (n := ∞)).comp
      hSmooth.contDiffOn.contMDiffOn fun x hx => by
      constructor
      · exact Real.smoothTransition.nonneg _
      · exact Real.smoothTransition.le_one _
  exact hMain.congr fun x hx => by
    simp [Function.comp, Set.projIcc_of_mem zero_le_one hx]

/-- Helper for Lemma 6.28: the right concatenation branch stays at time `0` before the cutoff. -/
def rightPlateauParam : C^∞⟮𝓡∂ 1, Set.Icc (0 : ℝ) 1; 𝓡∂ 1, Set.Icc (0 : ℝ) 1⟯ :=
  ⟨fun t => Set.projIcc 0 1 zero_le_one (Real.smoothTransition (4 * (t : ℝ) - 3)),
    contMDiff_rightPlateauParam⟩

/-- Helper for Lemma 6.28: reverse the interval coordinate while keeping the source point fixed. -/
def reverseSource :
    C^∞⟮K.prod (𝓡∂ 1), N × Set.Icc (0 : ℝ) 1; K.prod (𝓡∂ 1), N × Set.Icc (0 : ℝ) 1⟯ :=
  ContMDiffMap.prodMk ContMDiffMap.fst (reverseParam.comp ContMDiffMap.snd)

/-- Helper for Lemma 6.28: reparametrize the second coordinate for the left concatenation branch. -/
def leftPlateauSource :
    C^∞⟮K.prod (𝓡∂ 1), N × Set.Icc (0 : ℝ) 1; K.prod (𝓡∂ 1), N × Set.Icc (0 : ℝ) 1⟯ :=
  ContMDiffMap.prodMk ContMDiffMap.fst (leftPlateauParam.comp ContMDiffMap.snd)

/-- Helper for Lemma 6.28: reparametrize the second coordinate for the right concatenation branch. -/
def rightPlateauSource :
    C^∞⟮K.prod (𝓡∂ 1), N × Set.Icc (0 : ℝ) 1; K.prod (𝓡∂ 1), N × Set.Icc (0 : ℝ) 1⟯ :=
  ContMDiffMap.prodMk ContMDiffMap.fst (rightPlateauParam.comp ContMDiffMap.snd)

/-- Helper for Lemma 6.28: the cutoff set for the piecewise concatenation is `t ≤ 1 / 2`. -/
abbrev cutoffSet : Set (N × Set.Icc (0 : ℝ) 1) :=
  { p | ((p.2 : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2 }

/-- Helper for Lemma 6.28: every frontier point of the cutoff set lies over `t = 1 / 2`. -/
lemma frontier_cutoff_eq_half {p : N × Set.Icc (0 : ℝ) 1}
    (hp : p ∈ frontier (cutoffSet (N := N))) :
    ((p.2 : Set.Icc (0 : ℝ) 1) : ℝ) = 1 / 2 := by
  -- First show that a frontier point belongs to the closed half-space `t ≤ 1 / 2`.
  have hclosed : IsClosed (cutoffSet (N := N)) := by
    simpa [cutoffSet] using
      (isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const)
  have hle : ((p.2 : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2 :=
    hclosed.closure_subset hp.1
  -- Then rule out the strict inequality `t < 1 / 2`, which would put the point in the interior.
  have hnot_lt : ¬ ((p.2 : Set.Icc (0 : ℝ) 1) : ℝ) < 1 / 2 := by
    intro hlt
    have hopen : IsOpen {q : N × Set.Icc (0 : ℝ) 1 | ((q.2 : Set.Icc (0 : ℝ) 1) : ℝ) < 1 / 2} :=
      isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const
    have hint : p ∈ interior (cutoffSet (N := N)) := by
      rw [mem_interior_iff_mem_nhds]
      exact Filter.mem_of_superset (hopen.mem_nhds hlt) fun q hq => by
        change ((q.2 : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2
        exact le_of_lt hq
    exact hp.2 hint
  linarith

/-- Helper for Lemma 6.28: the reversed interval map sends `0` to `1`. -/
lemma reverseParam_zero : reverseParam (0 : Set.Icc (0 : ℝ) 1) = (1 : Set.Icc (0 : ℝ) 1) := by
  -- At the left endpoint, the affine formula already equals `1`.
  ext
  rw [reverseParam]
  simp

/-- Helper for Lemma 6.28: the reversed interval map sends `1` to `0`. -/
lemma reverseParam_one : reverseParam (1 : Set.Icc (0 : ℝ) 1) = (0 : Set.Icc (0 : ℝ) 1) := by
  -- At the right endpoint, the affine formula already equals `0`.
  ext
  rw [reverseParam]
  simp

/-- Helper for Lemma 6.28: the left plateau map is already at time `1` on `(1 / 4, 1]`. -/
lemma leftPlateauParam_eq_one_of_quarter_lt {t : Set.Icc (0 : ℝ) 1}
    (ht : (1 / 4 : ℝ) < (t : ℝ)) :
    leftPlateauParam t = 1 := by
  -- On this region the clipped affine function is at least `1`, so the projection is the right
  -- endpoint.
  ext
  change (Set.projIcc 0 1 zero_le_one (Real.smoothTransition (4 * (t : ℝ))) : ℝ) = 1
  rw [Set.projIcc_of_mem zero_le_one]
  · exact Real.smoothTransition.one_of_one_le (by linarith)
  · constructor
    · exact Real.smoothTransition.nonneg _
    · exact Real.smoothTransition.le_one _

/-- Helper for Lemma 6.28: the left plateau map starts at `0`. -/
lemma leftPlateauParam_zero : leftPlateauParam (0 : Set.Icc (0 : ℝ) 1) = (0 : Set.Icc (0 : ℝ) 1) := by
  -- The affine formula vanishes at the left endpoint.
  ext
  change (Set.projIcc 0 1 zero_le_one (Real.smoothTransition (4 * ((0 : Set.Icc (0 : ℝ) 1) : ℝ))) : ℝ) = 0
  rw [Set.projIcc_of_mem zero_le_one]
  · simp [Real.smoothTransition.zero]
  · constructor
    · exact Real.smoothTransition.nonneg _
    · exact Real.smoothTransition.le_one _

/-- Helper for Lemma 6.28: the right plateau map is still at time `0` on `[0, 3 / 4)`. -/
lemma rightPlateauParam_eq_zero_of_lt_threeQuarters {t : Set.Icc (0 : ℝ) 1}
    (ht : ((t : ℝ) : ℝ) < 3 / 4) :
    rightPlateauParam t = 0 := by
  -- On this region the clipped affine function is nonpositive, so the projection is the left
  -- endpoint.
  ext
  change (Set.projIcc 0 1 zero_le_one (Real.smoothTransition (4 * (t : ℝ) - 3)) : ℝ) = 0
  rw [Set.projIcc_of_mem zero_le_one]
  · exact Real.smoothTransition.zero_of_nonpos (by linarith)
  · constructor
    · exact Real.smoothTransition.nonneg _
    · exact Real.smoothTransition.le_one _

/-- Helper for Lemma 6.28: the right plateau map ends at `1`. -/
lemma rightPlateauParam_one :
    rightPlateauParam (1 : Set.Icc (0 : ℝ) 1) = (1 : Set.Icc (0 : ℝ) 1) := by
  -- The affine formula equals `1` at the right endpoint.
  ext
  change (Set.projIcc 0 1 zero_le_one (Real.smoothTransition (4 * ((1 : Set.Icc (0 : ℝ) 1) : ℝ) - 3)) : ℝ) = 1
  rw [Set.projIcc_of_mem zero_le_one]
  · exact Real.smoothTransition.one_of_one_le (by norm_num)
  · constructor
    · exact Real.smoothTransition.nonneg _
    · exact Real.smoothTransition.le_one _

/-- A constant-in-time smooth homotopy witnesses reflexivity. -/
def refl (f : C^∞⟮K, N; I, M⟯) : SmoothHomotopy f f where
  toContMDiffMap := f.comp ContMDiffMap.fst
  map_zero_right := fun _ => rfl
  map_one_right := fun _ => rfl

/-- Helper for Lemma 6.28: evaluating the reversed homotopy at `t = 0` recovers the terminal map. -/
lemma symm_map_zero_right {f g : C^∞⟮K, N; I, M⟯} (H : SmoothHomotopy f g) (x : N) :
    (H.toContMDiffMap.comp reverseSource) (x, (0 : Set.Icc (0 : ℝ) 1)) = g x := by
  -- The reparametrization sends `0` to `1`, so the original homotopy ends at `g`.
  change H.toContMDiffMap (x, reverseParam 0) = g x
  simpa [reverseParam_zero] using H.apply_one x

/-- Helper for Lemma 6.28: evaluating the reversed homotopy at `t = 1` recovers the initial map. -/
lemma symm_map_one_right {f g : C^∞⟮K, N; I, M⟯} (H : SmoothHomotopy f g) (x : N) :
    (H.toContMDiffMap.comp reverseSource) (x, (1 : Set.Icc (0 : ℝ) 1)) = f x := by
  -- The reparametrization sends `1` to `0`, so the original homotopy starts at `f`.
  change H.toContMDiffMap (x, reverseParam 1) = f x
  simpa [reverseParam_one] using H.apply_zero x

/-- Reversing the interval parameter turns a smooth homotopy from `f` to `g` into one from `g` to
`f`. -/
def symm {f g : C^∞⟮K, N; I, M⟯} (H : SmoothHomotopy f g) : SmoothHomotopy g f where
  toContMDiffMap := H.toContMDiffMap.comp reverseSource
  map_zero_right := symm_map_zero_right H
  map_one_right := symm_map_one_right H

/-- Helper for Lemma 6.28: the two concatenation branches agree on a neighborhood of every
frontier point of the cutoff set. -/
lemma branchEventuallyEqAtHalf {f g h : C^∞⟮K, N; I, M⟯}
    (H₁ : SmoothHomotopy f g) (H₂ : SmoothHomotopy g h)
    {p : N × Set.Icc (0 : ℝ) 1} (hp : p ∈ frontier (cutoffSet (N := N))) :
    (H₁.toContMDiffMap.comp leftPlateauSource) =ᶠ[nhds p]
      (H₂.toContMDiffMap.comp rightPlateauSource) := by
  -- Route correction: instead of comparing the branches pointwise only at `t = 1 / 2`, prove
  -- they are both literally constant to `g` on a neighborhood of the frontier.
  have hhalf : ((p.2 : Set.Icc (0 : ℝ) 1) : ℝ) = 1 / 2 := frontier_cutoff_eq_half hp
  let u : Set (N × Set.Icc (0 : ℝ) 1) :=
    { q | (1 / 4 : ℝ) < (q.2 : ℝ) ∧ ((q.2 : Set.Icc (0 : ℝ) 1) : ℝ) < 3 / 4 }
  have hu_open : IsOpen u := by
    refine (isOpen_lt continuous_const (continuous_subtype_val.comp continuous_snd)).inter ?_
    exact isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const
  have hp_mem : p ∈ u := by
    constructor <;> linarith
  filter_upwards [hu_open.mem_nhds hp_mem] with q hq
  have hleft : leftPlateauParam q.2 = (1 : Set.Icc (0 : ℝ) 1) :=
    leftPlateauParam_eq_one_of_quarter_lt hq.1
  have hright : rightPlateauParam q.2 = (0 : Set.Icc (0 : ℝ) 1) :=
    rightPlateauParam_eq_zero_of_lt_threeQuarters hq.2
  -- On this neighborhood the left branch is `g` by `H₁.apply_one`, and the right branch is the
  -- same `g` by `H₂.apply_zero`.
  change H₁.toContMDiffMap (q.1, leftPlateauParam q.2) =
      H₂.toContMDiffMap (q.1, rightPlateauParam q.2)
  calc
    H₁.toContMDiffMap (q.1, leftPlateauParam q.2) = H₁ (q.1, 1) := by rw [hleft]
    _ = g q.1 := H₁.apply_one q.1
    _ = H₂ (q.1, 0) := by symm; exact H₂.apply_zero q.1
    _ = H₂.toContMDiffMap (q.1, rightPlateauParam q.2) := by rw [hright]

/-- Helper for Lemma 6.28: the concatenated piecewise map is smooth. -/
lemma trans_toContMDiffMap_contMDiff {f g h : C^∞⟮K, N; I, M⟯}
    (H₁ : SmoothHomotopy f g) (H₂ : SmoothHomotopy g h) :
    ContMDiff (K.prod (𝓡∂ 1)) I ∞
      (Set.piecewise (cutoffSet (N := N))
        (H₁.toContMDiffMap.comp leftPlateauSource)
        (H₂.toContMDiffMap.comp rightPlateauSource)) := by
  -- The branches are smooth and agree near the frontier, so `ContMDiff.piecewise` applies.
  simpa using
    ContMDiff.piecewise
      (H₁.toContMDiffMap.comp leftPlateauSource).contMDiff
      (H₂.toContMDiffMap.comp rightPlateauSource).contMDiff
      (fun p hp ↦ branchEventuallyEqAtHalf H₁ H₂ hp)

/-- Helper for Lemma 6.28: the concatenated homotopy starts at `f`. -/
lemma trans_map_zero_right {f g h : C^∞⟮K, N; I, M⟯}
    (H₁ : SmoothHomotopy f g) (H₂ : SmoothHomotopy g h) (x : N) :
    Set.piecewise (cutoffSet (N := N))
      (H₁.toContMDiffMap.comp leftPlateauSource)
      (H₂.toContMDiffMap.comp rightPlateauSource)
      (x, (0 : Set.Icc (0 : ℝ) 1)) = f x := by
  -- At `t = 0` the cutoff chooses the left branch, whose reparametrization also starts at `0`.
  have hmem : (x, (0 : Set.Icc (0 : ℝ) 1)) ∈ cutoffSet (N := N) := by
    simp [cutoffSet]
  simp [Set.piecewise, hmem]
  change (H₁.toContMDiffMap.comp leftPlateauSource) (x, (0 : Set.Icc (0 : ℝ) 1)) = f x
  change H₁.toContMDiffMap (x, leftPlateauParam 0) = f x
  simpa [leftPlateauParam_zero] using H₁.apply_zero x

/-- Helper for Lemma 6.28: the concatenated homotopy ends at `h`. -/
lemma trans_map_one_right {f g h : C^∞⟮K, N; I, M⟯}
    (H₁ : SmoothHomotopy f g) (H₂ : SmoothHomotopy g h) (x : N) :
    Set.piecewise (cutoffSet (N := N))
      (H₁.toContMDiffMap.comp leftPlateauSource)
      (H₂.toContMDiffMap.comp rightPlateauSource)
      (x, (1 : Set.Icc (0 : ℝ) 1)) = h x := by
  -- At `t = 1` the cutoff chooses the right branch, whose reparametrization ends at `1`.
  have hnotmem : (x, (1 : Set.Icc (0 : ℝ) 1)) ∉ cutoffSet (N := N) := by
    simp [cutoffSet]
    norm_num
  simp [Set.piecewise, hnotmem]
  change (H₂.toContMDiffMap.comp rightPlateauSource) (x, (1 : Set.Icc (0 : ℝ) 1)) = h x
  change H₂.toContMDiffMap (x, rightPlateauParam 1) = h x
  simpa [rightPlateauParam_one] using H₂.apply_one x

/-- Concatenating two smooth homotopies with plateau reparametrizations witnesses transitivity. -/
def trans {f g h : C^∞⟮K, N; I, M⟯}
    (H₁ : SmoothHomotopy f g) (H₂ : SmoothHomotopy g h) : SmoothHomotopy f h where
  toContMDiffMap :=
    ⟨Set.piecewise (cutoffSet (N := N))
      (H₁.toContMDiffMap.comp leftPlateauSource)
      (H₂.toContMDiffMap.comp rightPlateauSource),
      trans_toContMDiffMap_contMDiff H₁ H₂⟩
  map_zero_right := trans_map_zero_right H₁ H₂
  map_one_right := trans_map_one_right H₁ H₂

end SmoothHomotopy

namespace SmoothlyHomotopic

/-- Lemma 6.28: if `N` and `M` are smooth manifolds with or without boundary, smooth homotopy is
an equivalence relation on the set of all smooth maps from `N` to `M`. -/
theorem equivalence :
    Equivalence (fun f g : C^∞⟮K, N; I, M⟯ ↦ SmoothlyHomotopic f g) := by
  -- Package the witness-level operations proved above into the induced relation on maps.
  refine ⟨fun f ↦ ⟨SmoothHomotopy.refl f⟩, ?_, ?_⟩
  · intro f g hfg
    exact hfg.map SmoothHomotopy.symm
  · intro f g h hfg hgh
    rcases hfg with ⟨Hfg⟩
    rcases hgh with ⟨Hgh⟩
    exact ⟨SmoothHomotopy.trans Hfg Hgh⟩

end SmoothlyHomotopic

end ContMDiffMap
