import ReasLib.Optlib.Algorithm.ADMM.Real_liminf

noncomputable section

open Set InnerProductSpace Topology Filter Real_liminf

-- The image of the subgradient is closed
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {x' g' : E} {x g : ℕ → E}
variable (lscf : LowerSemicontinuous f)--(cf : ConvexOn ℝ univ f)

lemma inequ₁ (y : E) (nonempty : ∀ n, (g n) ∈ SubderivAt f (x n)) :
    ∀ n, f y ≥ f (x n) +  ⟪g n, y - x n⟫_ℝ := fun n => nonempty n y

lemma inequ₃2' (y : E) (x_converge : Tendsto x atTop (𝓝 x')) (g_converge : Tendsto g atTop (𝓝 g')) :
    Tendsto (fun n => ⟪g n, y - x n⟫_ℝ) atTop (𝓝 ⟪g', y - x'⟫_ℝ) := by
  apply Tendsto.inner g_converge
  apply Tendsto.const_sub
  exact x_converge

lemma fx_BddAbove_tendsto (y : E) (x_converge : Tendsto x atTop (𝓝 x'))
    (g_converge : Tendsto g atTop (𝓝 g')) :
    Tendsto (fun n => f y - ⟪g n, y - x n⟫_ℝ) atTop (𝓝 (f y - ⟪ g', y - x'⟫_ℝ)) := by
  apply Tendsto.const_sub
  exact inequ₃2' y x_converge g_converge

lemma fx_BddAbove' (y : E) (x_converge : Tendsto x atTop (𝓝 x'))
    (g_converge : Tendsto g atTop (𝓝 g')) :
    BddAbove (range  (fun n => f y - ⟪ g n, y - x n⟫_ℝ)) := by
  apply Tendsto.bddAbove_range
  apply fx_BddAbove_tendsto y x_converge g_converge

lemma fx_BddAbove'' (y : E) (nonempty : ∀ n, g n ∈ SubderivAt f (x n)) :
    ∀ (a : ℕ), (f ∘ x) a ≤ f y - ⟪g a, y - x a⟫_ℝ :=by
  intro n
  have := inequ₁ y nonempty n
  simp only [Function.comp_apply, ge_iff_le]
  linarith [this]

lemma fx_BddAbove (y : E) (nonempty : ∀ n, (g n) ∈ SubderivAt f (x n))
    (x_converge : Tendsto x atTop (𝓝 x')) (g_converge : Tendsto g atTop (𝓝 g')) :
    BddAbove (range (f ∘ x)) := by
  apply BddAbove.range_mono (fun n => (f y) - ⟪ g n, y - x n⟫_ℝ)
  · apply fx_BddAbove'' y nonempty
  apply fx_BddAbove' y x_converge g_converge

@[simp]
def fx (lscf : LowerSemicontinuous f) (y : E) (nonempty : ∀ n, (g n) ∈ SubderivAt f (x n))
    (x_converge : Tendsto x atTop (𝓝 x')) (g_converge : Tendsto g atTop (𝓝 g')) :
    real_liminf := comp_real_liminf f lscf x' x x_converge
  (fx_BddAbove y nonempty x_converge g_converge)


def gy (y : E) (x_converge : Tendsto x atTop (𝓝 x'))
    (g_converge : Tendsto g atTop (𝓝 g')) : real_liminf :=
  tendsto_real_liminf ( ⟪ g', y - x'⟫_ℝ) (fun n => ⟪ g n, y - x n⟫_ℝ)
  (inequ₃2' y x_converge g_converge)

variable (y : E) (nonempty : ∀ n, (g n) ∈ SubderivAt f (x n)) (lscf : LowerSemicontinuous f)
variable (x_converge : Tendsto x atTop (𝓝 x')) (g_converge : Tendsto g atTop (𝓝 g'))
local notation "F" => fx lscf y nonempty x_converge g_converge
local notation "G" => gy y x_converge g_converge

lemma hax' : (F).x = f ∘ x := rfl

lemma hax : BddAbove (range (F).x) :=by
  rw[hax']
  apply fx_BddAbove y nonempty x_converge g_converge

lemma hag' : (G).x = (fun n => ⟪ g n, y - x n⟫_ℝ) := rfl

lemma hag : BddAbove (range (G).x) :=by
  rw[hag']
  apply Tendsto.bddAbove_range (inequ₃2' y x_converge g_converge)

local notation "hxa" => hax y nonempty lscf x_converge g_converge
local notation "hga" => hag y x_converge g_converge

lemma inequ₂' : lim_inf (const_real_liminf (f y)) ≥
    lim_inf (add_real_liminf F G hxa hga) := by
  apply ge_of_liminf
  apply inequ₁
  exact nonempty

lemma inequ₂ : f y ≥ lim_inf (add_real_liminf F G hxa hga) := by
  have inequ₂'' : lim_inf (const_real_liminf (f y)) =  f y := by
    apply liminf_const_eq
  rw[← inequ₂''];
  exact inequ₂' y nonempty lscf x_converge g_converge

lemma inequ₃1 : lim_inf (F) ≥ f x' := by
  apply le_liminf_of_lowerSemicontinuous f lscf x' x x_converge

lemma inequ₃2 : lim_inf (G) = ⟪ g', y - x'⟫_ℝ := by
  apply Real_liminf.liminf_eq

lemma inequ₃3 : lim_inf (F) + lim_inf (G) ≥  f x' + ⟪ g', y - x'⟫_ℝ := by
  rw[inequ₃2 y x_converge g_converge];
  simp only [ge_iff_le, add_le_add_iff_right];
  apply inequ₃1

lemma inequ₃3' : lim_inf (G) ≥ ⟪ g', y - x'⟫_ℝ :=by
  rw[inequ₃2 y x_converge g_converge];

lemma inequ₃''' : lim_inf (add_real_liminf F G hxa hga)
≥ lim_inf (F)  + lim_inf (G) := by
  apply Real_liminf.add_liminf_ge_liminf_add

lemma inequ₃ : lim_inf (add_real_liminf F G hxa hga)
≥ f x' + ⟪ g', y - x'⟫_ℝ :=by
  calc lim_inf (add_real_liminf F G hxa hga)
    _≥ lim_inf (F)  + lim_inf (G) := inequ₃''' y nonempty lscf x_converge g_converge
    _≥ f x' + ⟪ g', y - x'⟫_ℝ := inequ₃3 y nonempty lscf x_converge g_converge

lemma inequ₄ (y : E) (nonempty : ∀ n, (g n) ∈ SubderivAt f (x n)) (lscf : LowerSemicontinuous f)
    (x_converge : Tendsto x atTop (𝓝 x')) (g_converge : Tendsto g atTop (𝓝 g')) :
    f y ≥  f x' + ⟪ g', y - x'⟫_ℝ := by
  simp
  apply le_trans (inequ₃ y nonempty lscf x_converge g_converge)
    (inequ₂ y nonempty lscf x_converge g_converge)

-- Reference: book p.64, Theorem 2.19
theorem Image_subgradient_closed (nonempty : ∀ n, (g n) ∈ SubderivAt f (x n))
    (lscf : LowerSemicontinuous f) (x_converge : Tendsto x atTop (𝓝 x'))
    (g_converge : Tendsto g atTop (𝓝 g')) : g' ∈ SubderivAt f x' :=by
  intro y
  exact inequ₄ y nonempty lscf x_converge g_converge
