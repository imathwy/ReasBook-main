import DifferentialForms_Cartan_1970.IV.section14.«0002_Definition_IV_2_extra_2»
import DifferentialForms_Cartan_1970.IV.section17.«0001_Definition_IV_5_extra_1»

/-- Helper for Theorem IV.5-extra-2: in dimension zero the source is a singleton, so every
function is analytic on any subset. -/
lemma separatelyHolomorphicEmpty_analyticOnNhd
    {D : Set (Fin 0 → ℂ)} {f : (Fin 0 → ℂ) → ℂ} :
    AnalyticOnNhd ℂ f D := by
  intro z hz
  -- Collapse the zero-dimensional source to the unique point, turning `f` into a constant map.
  have hfconst : f = fun _ : Fin 0 → ℂ ↦ f z := by
    funext x
    exact congrArg f (Subsingleton.elim x z)
  rw [hfconst]
  exact analyticAt_const

/-- Helper for Theorem IV.5-extra-2: in one complex variable the unique coordinate slice is the
whole function after composing with evaluation at the single index. -/
lemma separatelyHolomorphicSingleton_analyticOnNhd
    {D : Set (Fin 1 → ℂ)} {f : (Fin 1 → ℂ) → ℂ}
    (hsep : ∀ z ∈ D, ∀ i : Fin 1, AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i)) :
    AnalyticOnNhd ℂ f D := by
  intro z hz
  -- Use the unique coordinate slice as the analytic one-variable model at `z`.
  have hs : AnalyticAt ℂ (fun w ↦ f (Function.update z 0 w)) (z 0) := hsep z hz 0
  -- Evaluation at the unique coordinate is a continuous linear map, hence analytic.
  have hEval : AnalyticAt ℂ (fun x : Fin 1 → ℂ ↦ x 0) z := by
    simpa using (ContinuousLinearMap.analyticAt
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0) z)
  have hcomp : AnalyticAt ℂ (fun x : Fin 1 → ℂ ↦ f (Function.update z 0 (x 0))) z := by
    simpa using (AnalyticAt.comp (f := fun x : Fin 1 → ℂ ↦ x 0) (x := z) hs hEval)
  -- The transported slice function is literally `f` because `Fin 1` has one coordinate.
  have hEq : (fun x : Fin 1 → ℂ ↦ f (Function.update z 0 (x 0))) = f := by
    funext x
    have hupdate : Function.update z 0 (x 0) = x := by
      funext i
      fin_cases i
      simp
    rw [hupdate]
  rw [hEq] at hcomp
  exact hcomp

/-- Helper for Theorem IV.5-extra-2: the inverse transported-coordinate map from
`(Fin (m + 1) → ℂ) × ℂ` back to `Fin (m + 2) → ℂ` is continuous. -/
lemma continuous_succFunEquiv_symm (m : ℕ) :
    Continuous (Fin.succFunEquiv ℂ (m + 1)).symm := by
  have hpair :
      Continuous (fun p : (Fin (m + 1) → ℂ) × ℂ ↦ (p.1, fun _ : Fin 1 ↦ p.2)) := by
    exact continuous_fst.prodMk (continuous_pi fun _ ↦ continuous_snd)
  simpa [Fin.succFunEquiv_symm_apply] using (Fin.continuous_append (m + 1) 1).comp hpair

/-- Helper for Theorem IV.5-extra-2: transporting along `Fin.succFunEquiv` turns the last scalar
coordinate into the final `Function.update` slot. -/
lemma succFunEquiv_symm_last_update
    {m : ℕ} {z : Fin (m + 2) → ℂ} {w : ℂ} :
    (Fin.succFunEquiv ℂ (m + 1)).symm ((Fin.succFunEquiv ℂ (m + 1) z).1, w) =
      Function.update z (Fin.last (m + 1)) w := by
  ext j
  refine Fin.lastCases ?_ ?_ j
  · -- At the final coordinate, the inverse transport reads off the new scalar parameter.
    change
      Fin.append (fun i ↦ z (Fin.castAdd 1 i)) (uniqueElim w)
        (Fin.natAdd (m + 1) (0 : Fin 1)) = _
    simp [Fin.append_right, Function.update]
  · intro k
    -- Away from the last coordinate, the inverse transport leaves the block variables unchanged.
    have hk : k.castSucc ≠ Fin.last (m + 1) := by
      intro h
      exact Nat.ne_of_lt k.is_lt (by simpa [Fin.val_last] using congrArg Fin.val h)
    have hcast : k.castSucc = Fin.castAdd 1 k := rfl
    change
      Fin.append (fun i ↦ z (Fin.castAdd 1 i)) (uniqueElim w) (Fin.castAdd 1 k) = _
    simp [Fin.append_left, Function.update, hk]
    simp [hcast]

/-- Helper for Theorem IV.5-extra-2: transporting a block-coordinate update through
`Fin.succFunEquiv` keeps the last coordinate fixed and updates the transported block. -/
lemma succFunEquiv_symm_block_update
    {m : ℕ} {z : Fin (m + 2) → ℂ} {i : Fin (m + 1)} {u : ℂ} :
    (Fin.succFunEquiv ℂ (m + 1)).symm
        (Function.update (Fin.succFunEquiv ℂ (m + 1) z).1 i u,
          (Fin.succFunEquiv ℂ (m + 1) z).2) =
      Function.update z (Fin.castAdd 1 i) u := by
  ext j
  refine Fin.lastCases ?_ ?_ j
  · -- The untouched last coordinate is exactly the original last entry of `z`.
    have hne : Fin.last (m + 1) ≠ Fin.castAdd 1 i := by
      intro h
      exact Nat.ne_of_lt i.is_lt
        (by simpa [Fin.val_castAdd, Fin.val_last] using congrArg Fin.val h.symm)
    have hlast : Fin.natAdd (m + 1) (0 : Fin 1) = Fin.last (m + 1) := rfl
    change
      Fin.append (Function.update (fun j ↦ z (Fin.castAdd 1 j)) i u)
        (uniqueElim (z (Fin.natAdd (m + 1) (0 : Fin 1))))
        (Fin.natAdd (m + 1) (0 : Fin 1)) = _
    simp [Fin.append_right, Function.update, hne]
    simp [hlast]
  · intro k
    -- On the block coordinates, the transported update is exactly the original block update.
    have hcast : k.castSucc = Fin.castAdd 1 k := rfl
    change
      Fin.append (Function.update (fun j ↦ z (Fin.castAdd 1 j)) i u)
        (uniqueElim (z (Fin.natAdd (m + 1) (0 : Fin 1))))
        (Fin.castAdd 1 k) = _
    by_cases hk : k = i
    · subst hk
      simp [Fin.append_left, Function.update, hcast]
    · simp [Fin.append_left, Function.update, hcast, hk]

/-- Helper for Theorem IV.5-extra-2: the last transported scalar slice is exactly the original
last-coordinate slice, so the separate analyticity hypothesis survives the product transport. -/
lemma transportedLastSlice_analyticAt
    {m : ℕ} {D : Set (Fin (m + 2) → ℂ)} {f : (Fin (m + 2) → ℂ) → ℂ}
    (hsep : ∀ z ∈ D, ∀ i : Fin (m + 2), AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i))
    {z : Fin (m + 2) → ℂ} (hz : z ∈ D) :
    let e := Fin.succFunEquiv ℂ (m + 1)
    let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
    AnalyticAt ℂ (fun w ↦ g ((e z).1, w)) (e z).2 := by
  dsimp
  have hfun :
      (fun w ↦ f ((Fin.succFunEquiv ℂ (m + 1)).symm (fun i ↦ z (Fin.castAdd 1 i), w))) =
        fun w ↦ f (Function.update z (Fin.last (m + 1)) w) := by
    funext w
    -- Rewrite the transported last slice back to the original coordinate update once.
    simpa [Fin.succFunEquiv_apply] using
      congrArg f (succFunEquiv_symm_last_update (m := m) (z := z) (w := w))
  rw [hfun]
  -- The original separate analyticity hypothesis now applies directly.
  simpa [Fin.succFunEquiv_apply] using hsep z hz (Fin.last (m + 1))

/-- Helper for Theorem IV.5-extra-2: each transported block slice is exactly the corresponding
original block-coordinate slice. -/
lemma transportedBlockSlice_analyticAt
    {m : ℕ} {D : Set (Fin (m + 2) → ℂ)} {f : (Fin (m + 2) → ℂ) → ℂ}
    (hsep : ∀ z ∈ D, ∀ i : Fin (m + 2), AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i))
    {z : Fin (m + 2) → ℂ} (hz : z ∈ D) (i : Fin (m + 1)) :
    let e := Fin.succFunEquiv ℂ (m + 1)
    let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
    AnalyticAt ℂ (fun u ↦ g (Function.update (e z).1 i u, (e z).2)) ((e z).1 i) := by
  dsimp
  have hfun :
      (fun u ↦
        f ((Fin.succFunEquiv ℂ (m + 1)).symm
          (Function.update (fun j ↦ z (Fin.castAdd 1 j)) i u,
            z (Fin.natAdd (m + 1) (0 : Fin 1))))) =
        fun u ↦ f (Function.update z (Fin.castAdd 1 i) u) := by
    funext u
    -- Rewrite the transported block slice back to the original coordinate update once.
    simpa [Fin.succFunEquiv_apply] using
      congrArg f (succFunEquiv_symm_block_update (m := m) (z := z) (i := i) (u := u))
  rw [hfun]
  -- The original separate analyticity hypothesis now applies directly.
  simpa [Fin.succFunEquiv_apply] using hsep z hz (Fin.castAdd 1 i)

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: transporting an open neighborhood of a
point in `D` along `Fin.succFunEquiv` produces a smaller product cylinder still contained in the
transported domain. -/
lemma exists_transportCylinder_subset_of_isOpen
    {m : ℕ} {D : Set (Fin (m + 2) → ℂ)}
    (hD : IsOpen D) {z : Fin (m + 2) → ℂ} (hz : z ∈ D) :
    ∃ ρ > 0,
      Metric.ball ((Fin.succFunEquiv ℂ (m + 1) z).1) (ρ / 2) ×ˢ
          Metric.closedBall ((Fin.succFunEquiv ℂ (m + 1) z).2) (ρ / 2) ⊆
        {p | (Fin.succFunEquiv ℂ (m + 1)).symm p ∈ D} := by
  let e := Fin.succFunEquiv ℂ (m + 1)
  have hsymmCont : Continuous e.symm := by
    simpa [e] using (continuous_succFunEquiv_symm (m := m))
  have htransportOpen : IsOpen {p | e.symm p ∈ D} := hD.preimage hsymmCont
  have hzTransport : e z ∈ {p | e.symm p ∈ D} := by
    change e.symm (e z) ∈ D
    simpa using hz
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.isOpen_iff.mp htransportOpen (e z) hzTransport
  refine ⟨ρ, hρpos, ?_⟩
  intro p hp
  have hx : dist p.1 (e z).1 < ρ / 2 := by
    simpa using hp.1
  have hw : dist p.2 (e z).2 ≤ ρ / 2 := by
    simpa [Metric.mem_closedBall] using hp.2
  have hρhalf_lt : ρ / 2 < ρ := by
    linarith
  have hpBall : p ∈ Metric.ball (e z) ρ := by
    simpa [Metric.mem_ball, Prod.dist_eq, dist_eq_norm, Prod.norm_def] using
      (max_lt_iff.mpr ⟨lt_trans hx hρhalf_lt, lt_of_le_of_lt hw hρhalf_lt⟩)
  exact hρsub hpBall
