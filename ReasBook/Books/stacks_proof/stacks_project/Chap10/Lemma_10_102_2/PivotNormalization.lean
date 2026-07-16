import stacks_proof.stacks_project.Chap10.Lemma_10_102_2.Basic

open CategoryTheory CategoryTheory.Limits ChainComplex Matrix

noncomputable section

universe u

section

variable {R : Type u} [Ring R]

namespace FiniteFreeComplex

variable {e : ℕ}
/-- Helper for Lemma 10.102.2: the unique-coordinate factor `Fin 1 → R` can be rescaled by a
unit through the canonical `funUnique` identification with `R`. -/
noncomputable def headScaling (u : Units R) : (Fin 1 → R) ≃ₗ[R] (Fin 1 → R) :=
  LinearEquiv.funUnique (Fin 1) R R ≪≫ₗ
    (u⁻¹).mulRightLinearEquiv R ≪≫ₗ
    (LinearEquiv.funUnique (Fin 1) R R).symm

/-- Helper for Lemma 10.102.2: the head-scaling automorphism multiplies the unique coordinate by
the inverse unit. -/
theorem headScaling_apply (u : Units R) (y : Fin 1 → R) :
    headScaling (R := R) u y = fun _ ↦ y 0 * (↑u⁻¹ : R) := by
  ext j
  fin_cases j
  simp [headScaling]

/-- Helper for Lemma 10.102.2: in head-tail product coordinates, subtracting the head coordinate
times a fixed tail vector is an explicit linear automorphism. -/
noncomputable def targetTailShear {nt : ℕ} (tailPivot : Fin nt → R) :
    ((Fin nt → R) × (Fin 1 → R)) ≃ₗ[R] ((Fin nt → R) × (Fin 1 → R)) :=
  LinearEquiv.prodComm R (Fin nt → R) (Fin 1 → R) ≪≫ₗ
    (LinearEquiv.refl R (Fin 1 → R)).skewProd (LinearEquiv.refl R (Fin nt → R))
      (-((LinearMap.proj 0).smulRight tailPivot)) ≪≫ₗ
    LinearEquiv.prodComm R (Fin 1 → R) (Fin nt → R)

/-- Helper for Lemma 10.102.2: the target-side shear fixes the head factor and subtracts the head
coefficient times the chosen pivot tail vector from the tail factor. -/
theorem targetTailShear_apply {nt : ℕ} (tailPivot : Fin nt → R)
    (x : Fin nt → R) (y : Fin 1 → R) :
    targetTailShear (R := R) tailPivot (x, y) = (x - y 0 • tailPivot, y) := by
  -- Rewrite the block-lower-diagonal map after commuting the product factors twice.
  simp [targetTailShear, sub_eq_add_neg, LinearMap.smulRight_apply, smul_eq_mul]

/-- Helper for Lemma 10.102.2: moving the chosen target coordinate to the head factor, rescaling
it to `1`, and then killing the remaining tail part gives the target-side basis change from the
source proof. -/
noncomputable def target_head_normalization
    {ns nt : ℕ}
    (f : (Fin (ns + 1) → R) →ₗ[R] (Fin (nt + 1) → R))
    (a : Fin (ns + 1)) (b : Fin (nt + 1))
    (hu : IsUnit ((f (Pi.single a (1 : R))) b)) :
    (Fin (nt + 1) → R) ≃ₗ[R] (Fin (nt + 1) → R) :=
  let targetSwap :=
    LinearEquiv.piCongrLeft R (fun _ : Fin (nt + 1) ↦ R) (Equiv.swap 0 b)
  let tailPivot :=
    (splitOffUnitLinearEquiv (R := R) nt (targetSwap (f (Pi.single a (1 : R))))).1
  targetSwap ≪≫ₗ
    splitOffUnitLinearEquiv (R := R) nt ≪≫ₗ
    (LinearEquiv.refl R (Fin nt → R)).prodCongr (headScaling (R := R) hu.unit) ≪≫ₗ
    targetTailShear (R := R) tailPivot ≪≫ₗ
    (splitOffUnitLinearEquiv (R := R) nt).symm

/-- Helper for Lemma 10.102.2: swapping the chosen source coordinate into position `0` sends the
distinguished head basis vector to the original basis vector indexed by `a`. -/
theorem source_swap_symm_apply_pure_head
    {n : ℕ} (a : Fin (n + 1)) :
    (LinearEquiv.piCongrLeft R (fun _ : Fin (n + 1) ↦ R) (Equiv.swap 0 a)).symm
        (Pi.single 0 (1 : R)) =
      (Pi.single a (1 : R) : Fin (n + 1) → R) := by
  -- Route correction: prove the swap-on-basis computation directly coordinatewise, instead of
  -- letting later transport goals absorb this elementary basis calculation.
  -- The inverse source swap evaluates at `Equiv.swap 0 a`, so only the cases `j = a`, `j = 0`,
  -- and `j ≠ 0,a` need to be checked.
  ext j
  change
    ((Pi.single 0 (1 : R) : Fin (n + 1) → R) ((Equiv.swap 0 a) j)) =
      ((Pi.single a (1 : R) : Fin (n + 1) → R) j)
  by_cases hja : j = a
  · subst j
    by_cases ha0 : a = 0
    · subst ha0
      change ((Pi.single 0 (1 : R) : Fin (n + 1) → R) 0) = 1
      simp
    · rw [Equiv.swap_apply_right]
      simp
  · by_cases hj0 : j = 0
    · subst j
      have ha0 : a ≠ 0 := by
        intro ha0
        exact hja ha0.symm
      rw [Equiv.swap_apply_left]
      have h0a : (0 : Fin (n + 1)) ≠ a := by
        simpa using ha0.symm
      rw [Pi.single_eq_of_ne ha0, Pi.single_eq_of_ne h0a]
    · rw [Equiv.swap_apply_of_ne_of_ne hj0 hja]
      simp [Pi.single_eq_of_ne hj0, Pi.single_eq_of_ne hja]

/-- Helper for Lemma 10.102.2: the explicit target normalization sends the chosen pivot basis
vector to the distinguished head basis vector. -/
theorem target_head_normalization_map_pivot
    {ns nt : ℕ}
    (f : (Fin (ns + 1) → R) →ₗ[R] (Fin (nt + 1) → R))
    (a : Fin (ns + 1)) (b : Fin (nt + 1))
    (hu : IsUnit ((f (Pi.single a (1 : R))) b)) :
    target_head_normalization (R := R) f a b hu (f (Pi.single a (1 : R))) =
      (Pi.single 0 (1 : R) : Fin (nt + 1) → R) := by
  let targetSwap :=
    LinearEquiv.piCongrLeft R (fun _ : Fin (nt + 1) ↦ R) (Equiv.swap 0 b)
  let pivot := targetSwap (f (Pi.single a (1 : R)))
  let tailPivot := (splitOffUnitLinearEquiv (R := R) nt pivot).1
  -- Rewrite the normalization in the split head-tail coordinates and evaluate it on the pivot.
  change
    (splitOffUnitLinearEquiv (R := R) nt).symm
        (targetTailShear (R := R) tailPivot
          (((LinearEquiv.refl R (Fin nt → R)).prodCongr
            (headScaling (R := R) hu.unit))
            (splitOffUnitLinearEquiv (R := R) nt pivot))) =
      (Pi.single 0 (1 : R) : Fin (nt + 1) → R)
  have hscaled :
      headScaling (R := R) hu.unit ((splitOffUnitLinearEquiv (R := R) nt pivot).2) =
        (fun _ ↦ (1 : R)) := by
    ext j
    fin_cases j
    rw [headScaling_apply, splitOffUnitLinearEquiv_apply_head]
    change pivot 0 * (↑hu.unit⁻¹ : R) = 1
    dsimp [pivot, targetSwap]
    rw [piCongrLeft_swap_apply_zero]
    simpa [hu.unit_spec]
  rw [targetTailShear_apply]
  simp [LinearEquiv.prodCongr_apply, hscaled, tailPivot]
  simpa using splitOffUnitLinearEquiv_symm_apply_pure_head (R := R) nt

/-- Helper for Lemma 10.102.2: after swapping the source pivot into position `0`, the explicit
target normalization sends the head basis vector to the head basis vector. -/
theorem target_head_normalization_map_head
    {ns nt : ℕ}
    (f : (Fin (ns + 1) → R) →ₗ[R] (Fin (nt + 1) → R))
    (a : Fin (ns + 1)) (b : Fin (nt + 1))
    (hu : IsUnit ((f (Pi.single a (1 : R))) b)) :
    let sourceSwap :=
      LinearEquiv.piCongrLeft R (fun _ : Fin (ns + 1) ↦ R) (Equiv.swap 0 a)
    let g :=
      (target_head_normalization (R := R) f a b hu).toLinearMap.comp
        (f.comp sourceSwap.symm.toLinearMap)
    g (Pi.single 0 (1 : R)) = Pi.single 0 1 := by
  let sourceSwap :=
    LinearEquiv.piCongrLeft R (fun _ : Fin (ns + 1) ↦ R) (Equiv.swap 0 a)
  let g :=
    (target_head_normalization (R := R) f a b hu).toLinearMap.comp
      (f.comp sourceSwap.symm.toLinearMap)
  -- The source swap moves `e₀` to the chosen pivot coordinate `a`, where the previous lemma
  -- applies directly.
  have hswap :
      sourceSwap.symm (Pi.single 0 (1 : R)) = (Pi.single a (1 : R) : Fin (ns + 1) → R) := by
    simpa [sourceSwap] using source_swap_symm_apply_pure_head (R := R) a
  change
    target_head_normalization (R := R) f a b hu (f (sourceSwap.symm (Pi.single 0 (1 : R)))) =
      (Pi.single 0 (1 : R) : Fin (nt + 1) → R)
  rw [hswap]
  exact target_head_normalization_map_pivot (R := R) f a b hu

/-- Helper for Lemma 10.102.2: the inverse head-tail splitting sends a pure tail basis vector in
the product model to the corresponding basis vector `Pi.single j.succ 1`. -/
theorem splitOffUnitLinearEquiv_symm_apply_pure_tail
    (n : ℕ) (j : Fin n) :
    (splitOffUnitLinearEquiv (R := R) n).symm (Pi.single j (1 : R), 0) =
      (Pi.single j.succ (1 : R) : Fin (n + 1) → R) := by
  -- The split head-tail coordinates determine the vector uniquely on coordinate `0` and on each
  -- successor coordinate.
  ext k
  obtain ⟨hhead, htail⟩ :=
    splitOffUnitLinearEquiv_symm_apply_head_tail (R := R) n (Pi.single j 1) 0
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨l, rfl⟩
  · simpa using hhead
  · by_cases hlj : l = j
    · subst l
      simpa using htail j
    · rw [htail l]
      simp [Pi.single_eq_of_ne, hlj]

/-- Helper for Lemma 10.102.2: for a source tail vector `x`, this records the head component of
`g` applied to the vector with tail part `x` and zero head part. -/
noncomputable def source_head_coefficient
    {ns nt : ℕ}
    (g : (Fin (ns + 1) → R) →ₗ[R] (Fin (nt + 1) → R)) :
    (Fin ns → R) →ₗ[R] (Fin 1 → R) :=
  let sourceInl :
      (Fin ns → R) →ₗ[R] (Fin (ns + 1) → R) :=
    (splitOffUnitLinearEquiv (R := R) ns).symm.toLinearMap.comp
      (LinearMap.inl R (Fin ns → R) (Fin 1 → R))
  let targetHead :
      (Fin (nt + 1) → R) →ₗ[R] (Fin 1 → R) :=
    (LinearMap.snd R (Fin nt → R) (Fin 1 → R)).comp
      (splitOffUnitLinearEquiv (R := R) nt).toLinearMap
  targetHead.comp (g.comp sourceInl)

/-- Helper for Lemma 10.102.2: the source-side column operation subtracts exactly the head
coefficient created by `g` on a tail input, while fixing the distinguished head summand. -/
noncomputable def source_head_correction
    {ns nt : ℕ}
    (g : (Fin (ns + 1) → R) →ₗ[R] (Fin (nt + 1) → R))
    (_hg : g (Pi.single 0 (1 : R)) = Pi.single 0 1) :
    (Fin (ns + 1) → R) ≃ₗ[R] (Fin (ns + 1) → R) :=
  splitOffUnitLinearEquiv (R := R) ns ≪≫ₗ
    (LinearEquiv.refl R (Fin ns → R)).skewProd
      (LinearEquiv.refl R (Fin 1 → R))
      (source_head_coefficient (R := R) g) ≪≫ₗ
    (splitOffUnitLinearEquiv (R := R) ns).symm

/-- Helper for Lemma 10.102.2: in head-tail product coordinates, the inverse source correction
keeps the tail part fixed and subtracts the recorded head coefficient from the head part. -/
theorem source_head_correction_symm_apply_head_tail
    {ns nt : ℕ}
    (g : (Fin (ns + 1) → R) →ₗ[R] (Fin (nt + 1) → R))
    (hg : g (Pi.single 0 (1 : R)) = Pi.single 0 1)
    (x : Fin ns → R) (y : Fin 1 → R) :
    (splitOffUnitLinearEquiv (R := R) ns)
        ((source_head_correction (R := R) g hg).symm
          ((splitOffUnitLinearEquiv (R := R) ns).symm (x, y))) =
      (x, y - source_head_coefficient (R := R) g x) := by
  -- Unfold the conjugated skew-product once and read off its inverse formula in split
  -- coordinates.
  simp [source_head_correction, source_head_coefficient]

/-- Helper for Lemma 10.102.2: the inverse source correction fixes the distinguished head basis
vector. -/
theorem source_head_correction_symm_apply_pure_head
    {ns nt : ℕ}
    (g : (Fin (ns + 1) → R) →ₗ[R] (Fin (nt + 1) → R))
    (hg : g (Pi.single 0 (1 : R)) = Pi.single 0 1) :
    (source_head_correction (R := R) g hg).symm (Pi.single 0 (1 : R)) =
      (Pi.single 0 (1 : R) : Fin (ns + 1) → R) := by
  rw [← splitOffUnitLinearEquiv_symm_apply_pure_head (R := R) ns]
  have hcoeff_zero : source_head_coefficient (R := R) g 0 = 0 := by
    simpa using (source_head_coefficient (R := R) g).map_zero
  -- In split coordinates, the inverse correction sends `(0, 1)` to `(0, 1 - 0)`.
  apply (splitOffUnitLinearEquiv (R := R) ns).injective
  simpa [hcoeff_zero] using
    source_head_correction_symm_apply_head_tail
      (R := R) (g := g) (hg := hg) (x := 0) (y := fun _ ↦ (1 : R))

/-- Helper for Lemma 10.102.2: after the source-side correction, the codomain head coordinate is
exactly the chosen source head coordinate in split head-tail coordinates. -/
theorem source_head_correction_preserves_split_head
    {ns nt : ℕ}
    (g : (Fin (ns + 1) → R) →ₗ[R] (Fin (nt + 1) → R))
    (hg : g (Pi.single 0 (1 : R)) = Pi.single 0 1)
    (x : Fin ns → R) (y : Fin 1 → R) :
    (splitOffUnitLinearEquiv (R := R) nt
      (g ((source_head_correction (R := R) g hg).symm
        ((splitOffUnitLinearEquiv (R := R) ns).symm (x, y))))).2 = y := by
  let pairHead :
      ((Fin ns → R) × (Fin 1 → R)) →ₗ[R] (Fin 1 → R) :=
    ((LinearMap.snd R (Fin nt → R) (Fin 1 → R)).comp
        (splitOffUnitLinearEquiv (R := R) nt).toLinearMap).comp
      (g.comp (splitOffUnitLinearEquiv (R := R) ns).symm.toLinearMap)
  have hcorrected :
      (source_head_correction (R := R) g hg).symm
          ((splitOffUnitLinearEquiv (R := R) ns).symm (x, y)) =
        (splitOffUnitLinearEquiv (R := R) ns).symm
          (x, y - source_head_coefficient (R := R) g x) := by
    -- Rewrite the inverse correction in split coordinates and use injectivity of the splitter.
    apply (splitOffUnitLinearEquiv (R := R) ns).injective
    simpa using source_head_correction_symm_apply_head_tail
      (R := R) (g := g) (hg := hg) x y
  have hpair_inl :
      pairHead (x, 0) = source_head_coefficient (R := R) g x := by
    -- The `x`-only input is exactly the tail injection used in `source_head_coefficient`.
    ext j
    fin_cases j
    simp [pairHead, source_head_coefficient]
  have hpair_head (w : Fin 1 → R) :
      pairHead (0, w) = w := by
    -- The pure head input is a scalar multiple of the distinguished basis vector, which `g`
    -- sends to itself by `hg`.
    ext j
    fin_cases j
    have hpure :
        (splitOffUnitLinearEquiv (R := R) ns).symm (0, w) =
          (w 0) • (Pi.single 0 (1 : R) : Fin (ns + 1) → R) := by
      rw [split_off_unit_linear_equiv_symm_eq_head_tail_sum (R := R) ns 0 w]
      ext j
      by_cases hj0 : j = 0
      · subst hj0
        simp
      · simp [Pi.single_eq_of_ne hj0]
    change
      ((splitOffUnitLinearEquiv (R := R) nt
          (g ((splitOffUnitLinearEquiv (R := R) ns).symm (0, w)))).2) 0 = w 0
    rw [hpure, map_smul, hg, splitOffUnitLinearEquiv_apply_head]
    simp
  have hpair_split :
      pairHead (x, y - source_head_coefficient (R := R) g x) =
        pairHead (x, 0) + pairHead (0, y - source_head_coefficient (R := R) g x) := by
    -- Split the corrected source coordinates into tail-only and head-only pieces.
    have hsum :
        (x, y - source_head_coefficient (R := R) g x) =
          (x, 0) + (0, y - source_head_coefficient (R := R) g x) := by
      apply Prod.ext
      · ext j
        simp
      · ext k
        fin_cases k
        simp
    rw [hsum, pairHead.map_add]
  -- After that split, the recorded head coefficient cancels with the correction term.
  calc
    (splitOffUnitLinearEquiv (R := R) nt
      (g ((source_head_correction (R := R) g hg).symm
        ((splitOffUnitLinearEquiv (R := R) ns).symm (x, y))))).2 =
        pairHead (x, y - source_head_coefficient (R := R) g x) := by
          rw [hcorrected]
          rfl
    _ = pairHead (x, 0) + pairHead (0, y - source_head_coefficient (R := R) g x) := hpair_split
    _ = source_head_coefficient (R := R) g x +
          (y - source_head_coefficient (R := R) g x) := by
          rw [hpair_inl, hpair_head]
    _ = y := by
          ext j
          fin_cases j
          simp

/-- Helper for Lemma 10.102.2: after precomposing with the source-side correction, the normalized
middle differential still fixes the head basis vector and has zero head coordinate on every tail
basis vector. -/
theorem source_head_correction_zero_head_on_tail
    {ns nt : ℕ}
    (g : (Fin (ns + 1) → R) →ₗ[R] (Fin (nt + 1) → R))
    (hg : g (Pi.single 0 (1 : R)) = Pi.single 0 1) :
    let u := source_head_correction (R := R) g hg
    let g' := g.comp u.symm.toLinearMap
    g' (Pi.single 0 (1 : R)) = Pi.single 0 1 ∧
      ∀ j : Fin ns, (g' (Pi.single j.succ (1 : R))) 0 = 0 := by
  dsimp
  constructor
  · -- The source correction was designed to keep the distinguished head basis vector fixed.
    rw [source_head_correction_symm_apply_pure_head (R := R) (g := g) (hg := hg), hg]
  · intro j
    -- Rewrite the corrected tail basis vector through split coordinates and read its head output.
    have hsplit :
        (splitOffUnitLinearEquiv (R := R) nt
          (g ((source_head_correction (R := R) g hg).symm
            (Pi.single j.succ (1 : R))))).2 = 0 := by
      rw [← splitOffUnitLinearEquiv_symm_apply_pure_tail (R := R) ns j]
      simpa using source_head_correction_preserves_split_head
        (R := R) (g := g) (hg := hg) (x := Pi.single j (1 : R)) (y := 0)
    have hzero := congrArg (fun z : Fin 1 → R => z 0) hsplit
    rw [splitOffUnitLinearEquiv_apply_head] at hzero
    simpa using hzero

end FiniteFreeComplex

end
