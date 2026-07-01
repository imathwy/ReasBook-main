import Mathlib
import SmoothManifoldsLee.Chap02.Sec02_11.Definition_2_11_extra_2
import SmoothManifoldsLee.Chap02.Sec02_11.Lemma_2_26
import SmoothManifoldsLee.Chap03.Sec03_13.Definition_3_13_extra_3
import SmoothManifoldsLee.Chap03.Sec03_13.Proposition_3_2
import SmoothManifoldsLee.Chap03.Sec03_18.Definition_3_18_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open TopologicalSpace CategoryTheory
open scoped Manifold ContDiff

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type} [TopologicalSpace H]
variable {M : Type} [TopologicalSpace M]
variable {I : ModelWithCorners ℝ E H} [ChartedSpace H M]

namespace TangentSpace

variable {p : M}

private def applyToSmooth (X : TangentSpace I p)
    (f : C^∞⟮I, M; ℝ⟯) : ℝ :=
  mfderiv% f p X

private theorem applyToSmooth_add (X : TangentSpace I p)
    (f g : C^∞⟮I, M; ℝ⟯) :
    applyToSmooth X (f + g) = applyToSmooth X f + applyToSmooth X g := by
  have hf : MDiffAt f p := f.contMDiff.mdifferentiableAt (by simp)
  have hg : MDiffAt g p := g.contMDiff.mdifferentiableAt (by simp)
  simpa [applyToSmooth] using congr($(mfderiv_add hf hg) X)

private theorem applyToSmooth_smul (X : TangentSpace I p)
    (c : ℝ) (f : C^∞⟮I, M; ℝ⟯) :
    applyToSmooth X (c • f) = c * applyToSmooth X f := by
  have hf : MDiffAt f p := f.contMDiff.mdifferentiableAt (by simp)
  simpa [applyToSmooth, smul_eq_mul] using congr($(const_smul_mfderiv hf c) X)

private theorem applyToSmooth_mul (X : TangentSpace I p)
    (f g : C^∞⟮I, M; ℝ⟯) :
    applyToSmooth X (f * g) =
      f p * applyToSmooth X g + g p * applyToSmooth X f := by
  have hf : MDiffAt f p := f.contMDiff.mdifferentiableAt (by simp)
  have hg : MDiffAt g p := g.contMDiff.mdifferentiableAt (by simp)
  simpa [applyToSmooth, PointedContMDiffMap.smul_def, smul_eq_mul, mul_comm, mul_left_comm,
    mul_assoc, add_comm, add_left_comm, add_assoc] using
    fromTangentSpace_mfderiv_smul_apply hf hg X

/-- A tangent vector determines the corresponding point derivation on smooth real-valued functions
at its base point. -/
def toPointDerivation (X : TangentSpace I p) : PointDerivation I p :=
  Derivation.mk'
    { toFun := applyToSmooth X
      map_add' := applyToSmooth_add X
      map_smul' := applyToSmooth_smul X }
    (applyToSmooth_mul X)

/-- Evaluating the point derivation associated to a tangent vector is directional differentiation
along that tangent vector. -/
theorem toPointDerivation_apply (X : TangentSpace I p)
    (f : C^∞⟮I, M; ℝ⟯) :
    toPointDerivation X f = mfderiv% f p X :=
  rfl

end TangentSpace

namespace smooth_germ_derivation_at

local notation "𝒪∞" => smoothSheafCommRing I 𝓘(ℝ) M ℝ
local notation "Γ∞" => C^∞⟮I, (⊤ : Opens M); 𝓘(ℝ), ℝ⟯

variable {p : M}

private def topSection (f : C^∞⟮I, M; ℝ⟯) :
    Γ∞ :=
  ⟨fun x ↦ f x.1, f.contMDiff.comp contMDiff_subtype_val⟩

private theorem topSection_add (f g : C^∞⟮I, M; ℝ⟯) :
    topSection (f + g) = topSection f + topSection g :=
  rfl

private theorem topSection_smul (c : ℝ) (f : C^∞⟮I, M; ℝ⟯) :
    topSection (c • f) = c • topSection f := by
  ext x
  rfl

private theorem topSection_mul (f g : C^∞⟮I, M; ℝ⟯) :
    topSection (f * g) = topSection f * topSection g :=
  rfl

private theorem Γgerm_topSection_add (f g : C^∞⟮I, M; ℝ⟯) :
    𝒪∞.presheaf.Γgerm p (topSection (f + g)) =
      𝒪∞.presheaf.Γgerm p (topSection f) +
        𝒪∞.presheaf.Γgerm p (topSection g) := by
  change ((𝒪∞.presheaf.Γgerm p).hom) (topSection (f + g)) =
      ((𝒪∞.presheaf.Γgerm p).hom) (topSection f) +
        ((𝒪∞.presheaf.Γgerm p).hom) (topSection g)
  rw [topSection_add]
  exact map_add ((𝒪∞.presheaf.Γgerm p).hom) (topSection f) (topSection g)

private theorem Γgerm_topSection_smul (c : ℝ) (f : C^∞⟮I, M; ℝ⟯) :
    𝒪∞.presheaf.Γgerm p (topSection (c • f)) =
      c • 𝒪∞.presheaf.Γgerm p (topSection f) := by
  letI : Algebra ℝ Γ∞ := inferInstance
  change ((𝒪∞.presheaf.Γgerm p).hom) ((algebraMap ℝ Γ∞ c) * topSection f) =
    (algebraMap ℝ C^∞_[p](I) c) *
      ((𝒪∞.presheaf.Γgerm p).hom (topSection f))
  exact map_mul ((𝒪∞.presheaf.Γgerm p).hom) (algebraMap ℝ Γ∞ c) (topSection f)

private theorem Γgerm_topSection_mul (f g : C^∞⟮I, M; ℝ⟯) :
    𝒪∞.presheaf.Γgerm p (topSection (f * g)) =
      𝒪∞.presheaf.Γgerm p (topSection f) *
        𝒪∞.presheaf.Γgerm p (topSection g) := by
  change ((𝒪∞.presheaf.Γgerm p).hom) (topSection (f * g)) =
      ((𝒪∞.presheaf.Γgerm p).hom) (topSection f) *
        ((𝒪∞.presheaf.Γgerm p).hom) (topSection g)
  rw [topSection_mul]
  exact map_mul ((𝒪∞.presheaf.Γgerm p).hom) (topSection f) (topSection g)

private theorem eval_Γgerm_topSection (p : M) (f : C^∞⟮I, M; ℝ⟯) :
    smoothSheafCommRing.eval I 𝓘(ℝ) M ℝ p (𝒪∞.presheaf.Γgerm p (topSection f)) = f p := by
  simpa [TopCat.Presheaf.Γgerm, topSection] using
    smoothSheafCommRing.eval_germ (⊤ : Opens M) p (by simp) (topSection f)

/-- A derivation of smooth germs at `p` induces the corresponding point derivation on global smooth
functions by precomposing with the canonical global-section-to-stalk map. -/
def toPointDerivation (v : smooth_germ_derivation_at I p) :
    PointDerivation I p :=
  Derivation.mk'
    { toFun := fun f ↦ v <| 𝒪∞.presheaf.Γgerm p (topSection f)
      map_add' := by
        intro f g
        have h₁ := congrArg v
          (Γgerm_topSection_add (f : C^∞⟮I, M; ℝ⟯) g)
        have h₂ := v.map_add
          (𝒪∞.presheaf.Γgerm p (topSection (f : C^∞⟮I, M; ℝ⟯)))
          (𝒪∞.presheaf.Γgerm p (topSection g))
        exact h₁.trans h₂
      map_smul' := by
        intro c f
        have h₁ := congrArg v (Γgerm_topSection_smul c
          (f : C^∞⟮I, M; ℝ⟯))
        have h₂ := v.map_smul c (𝒪∞.presheaf.Γgerm p (topSection (f : C^∞⟮I, M; ℝ⟯)))
        simpa using h₁.trans h₂
      }
    (fun f g ↦ by
      have h₁ := congrArg v (Γgerm_topSection_mul
        (f : C^∞⟮I, M; ℝ⟯) g)
      have h₂ := v.leibniz
        (𝒪∞.presheaf.Γgerm p (topSection (f : C^∞⟮I, M; ℝ⟯)))
        (𝒪∞.presheaf.Γgerm p (topSection g))
      have hf_eval := eval_Γgerm_topSection p (f : C^∞⟮I, M; ℝ⟯)
      have hg_eval := eval_Γgerm_topSection p g
      simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra, hf_eval, hg_eval] using h₁.trans h₂)

/-- Helper for Problem 3-7: the point derivation induced by a germ derivation depends only on the
germ of a global smooth function at `p`. -/
theorem toPointDerivation_congr_of_eqOn_nhds (v : smooth_germ_derivation_at I p)
    (f g : C^∞⟮I, M; ℝ⟯) (U : Set M) (hU : IsOpen U) (hpU : p ∈ U) (hfg : Set.EqOn f g U) :
    toPointDerivation v f = toPointDerivation v g := by
  let W : Opens M := ⟨U, hU⟩
  let iW : W ⟶ (⊤ : Opens M) := homOfLE le_top
  have hgerm :
      𝒪∞.presheaf.Γgerm p (topSection f) = 𝒪∞.presheaf.Γgerm p (topSection g) := by
    -- Restrict both global sections to the common neighborhood `U` on which they agree.
    refine (smoothSheafCommRing.germ_eq_iff (I := I) (p := p) (U := (⊤ : Opens M))
      (V := (⊤ : Opens M)) (by simp) (by simp) (topSection f) (topSection g)).2 ?_
    refine ⟨W, hpU, iW, iW, ?_⟩
    apply ContMDiffMap.ext
    intro x
    exact hfg x.2
  -- Apply the germ derivation to the identified stalk element.
  exact congrArg v hgerm

/-- Helper for Problem 3-7: the preferred chart source around `p` as an open set. -/
def chartSource (p : M) : Opens M :=
  ⟨(chartAt H p).source, (chartAt H p).open_source⟩

/-- Helper for Problem 3-7: the base point belongs to its preferred chart source. -/
theorem mem_chartSource (p : M) : p ∈ chartSource (H := H) p :=
  mem_chart_source H p

/-- Helper for Problem 3-7: the preferred chart is smooth on the preferred chart-source subtype. -/
theorem contMDiff_chartSource_extChartAt [IsManifold I ∞ M] (p : M) :
    ContMDiff I 𝓘(ℝ, E) ∞ (fun x : chartSource (H := H) p ↦ extChartAt I p x.1) := by
  simpa [Function.comp] using
    (contMDiffOn_extChartAt (I := I) (n := ∞) (x := p)).comp_contMDiff
      (contMDiff_subtype_val : ContMDiff I I ∞ (Subtype.val : chartSource (H := H) p → M))
      (fun x ↦ x.2)

/-- Helper for Problem 3-7: pull a global smooth model-space test function back to the preferred
chart source around `p`. -/
def chart_pullback_section [IsManifold I ∞ M] (p : M)
    (g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    C^∞⟮I, chartSource (H := H) p; 𝓘(ℝ), ℝ⟯ :=
  ⟨fun x ↦ g (extChartAt I p x.1),
    g.contMDiff.comp (contMDiff_chartSource_extChartAt (H := H) (I := I) p)⟩

/-- Helper for Problem 3-7: pulling back through the preferred chart preserves addition on the
chart source. -/
theorem chart_pullback_section_add [IsManifold I ∞ M] (p : M)
    (f g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    chart_pullback_section (H := H) (I := I) p (f + g) =
      chart_pullback_section (H := H) (I := I) p f +
        chart_pullback_section (H := H) (I := I) p g :=
  rfl

/-- Helper for Problem 3-7: pulling back through the preferred chart preserves scalar
multiplication on the chart source. -/
theorem chart_pullback_section_smul [IsManifold I ∞ M] (p : M)
    (c : ℝ) (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    chart_pullback_section (H := H) (I := I) p (c • f) =
      c • chart_pullback_section (H := H) (I := I) p f := by
  ext x
  rfl

/-- Helper for Problem 3-7: pulling back through the preferred chart preserves products on the
chart source. -/
theorem chart_pullback_section_mul [IsManifold I ∞ M] (p : M)
    (f g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    chart_pullback_section (H := H) (I := I) p (f * g) =
      chart_pullback_section (H := H) (I := I) p f *
        chart_pullback_section (H := H) (I := I) p g :=
  rfl

/-- Helper for Problem 3-7: taking the germ at `p` of chart-pulled-back model-space functions
preserves addition. -/
private theorem germ_chart_pullback_section_add [IsManifold I ∞ M] (p : M)
    (f g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    𝒪∞.presheaf.germ (chartSource (H := H) p) p (mem_chartSource (H := H) p)
        (chart_pullback_section (H := H) (I := I) p (f + g)) =
      𝒪∞.presheaf.germ (chartSource (H := H) p) p (mem_chartSource (H := H) p)
          (chart_pullback_section (H := H) (I := I) p f) +
        𝒪∞.presheaf.germ (chartSource (H := H) p) p (mem_chartSource (H := H) p)
          (chart_pullback_section (H := H) (I := I) p g) := by
  let U : Opens M := chartSource (H := H) p
  let hpU : p ∈ U := mem_chartSource (H := H) p
  -- Push addition through the chart pullback before applying the germ map.
  change ((𝒪∞.presheaf.germ U p hpU).hom)
      (chart_pullback_section (H := H) (I := I) p (f + g)) =
    ((𝒪∞.presheaf.germ U p hpU).hom)
        (chart_pullback_section (H := H) (I := I) p f) +
      ((𝒪∞.presheaf.germ U p hpU).hom)
        (chart_pullback_section (H := H) (I := I) p g)
  rw [chart_pullback_section_add]
  exact map_add ((𝒪∞.presheaf.germ U p hpU).hom)
    (chart_pullback_section (H := H) (I := I) p f)
    (chart_pullback_section (H := H) (I := I) p g)

/-- Helper for Problem 3-7: taking the germ at `p` of chart-pulled-back model-space functions
preserves scalar multiplication. -/
private theorem chartSource_germ_map_algebraMap [IsManifold I ∞ M] (p : M) (c : ℝ) :
    ((𝒪∞.presheaf.germ (chartSource (H := H) p) p (mem_chartSource (H := H) p)).hom)
        (algebraMap ℝ C^∞⟮I, chartSource (H := H) p; 𝓘(ℝ), ℝ⟯ c) =
      algebraMap ℝ C^∞_[p](I) c := by
  let U : Opens M := chartSource (H := H) p
  let hpU : p ∈ U := mem_chartSource (H := H) p
  let iTop : U ⟶ (⊤ : Opens M) := homOfLE le_top
  -- The local constant section and the global constant section agree on the chart source, so they
  -- define the same stalk germ at `p`.
  refine (smoothSheafCommRing.germ_eq_iff (I := I) (p := p) (U := U) (V := (⊤ : Opens M))
    hpU (by simp) (algebraMap ℝ C^∞⟮I, U; 𝓘(ℝ), ℝ⟯ c)
    (algebraMap ℝ C^∞⟮I, (⊤ : Opens M); 𝓘(ℝ), ℝ⟯ c)).2 ?_
  refine ⟨U, hpU, 𝟙 U, iTop, ?_⟩
  apply ContMDiffMap.ext
  intro x
  rfl

/-- Helper for Problem 3-7: taking the germ at `p` of chart-pulled-back model-space functions
preserves scalar multiplication. -/
private theorem chartSource_germ_map_smul [IsManifold I ∞ M] (p : M)
    (c : ℝ) (s : C^∞⟮I, chartSource (H := H) p; 𝓘(ℝ), ℝ⟯) :
    ((𝒪∞.presheaf.germ (chartSource (H := H) p) p (mem_chartSource (H := H) p)).hom)
        ((algebraMap ℝ C^∞⟮I, chartSource (H := H) p; 𝓘(ℝ), ℝ⟯ c) * s) =
      (algebraMap ℝ C^∞_[p](I) c) *
        ((𝒪∞.presheaf.germ (chartSource (H := H) p) p (mem_chartSource (H := H) p)).hom s) := by
  let U : Opens M := chartSource (H := H) p
  let hpU : p ∈ U := mem_chartSource (H := H) p
  letI : Algebra ℝ C^∞⟮I, U; 𝓘(ℝ), ℝ⟯ := inferInstance
  -- This is the same multiplicativity calculation as for global sections, but now on the
  -- preferred chart source stalk.
  change ((𝒪∞.presheaf.germ U p hpU).hom)
      ((algebraMap ℝ C^∞⟮I, U; 𝓘(ℝ), ℝ⟯ c) * s) =
    (algebraMap ℝ C^∞_[p](I) c) *
      ((𝒪∞.presheaf.germ U p hpU).hom s)
  have hconst :
      ((𝒪∞.presheaf.germ U p hpU).hom) (algebraMap ℝ C^∞⟮I, U; 𝓘(ℝ), ℝ⟯ c) =
        algebraMap ℝ C^∞_[p](I) c := by
    -- The germ of a constant section on the chart source is the same constant germ at `p`.
    simpa [U, hpU] using chartSource_germ_map_algebraMap (H := H) (I := I) p c
  -- After separating the constant-section factor, the stalk morphism is multiplicative.
  refine (map_mul ((𝒪∞.presheaf.germ U p hpU).hom)
    (algebraMap ℝ C^∞⟮I, U; 𝓘(ℝ), ℝ⟯ c) s).trans ?_
  exact congrArg (fun x : C^∞_[p](I) ↦ x * ((𝒪∞.presheaf.germ U p hpU).hom s)) hconst

/-- Helper for Problem 3-7: taking the germ at `p` of chart-pulled-back model-space functions
preserves scalar multiplication. -/
private theorem germ_chart_pullback_section_smul [IsManifold I ∞ M] (p : M)
    (c : ℝ) (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    𝒪∞.presheaf.germ (chartSource (H := H) p) p (mem_chartSource (H := H) p)
        (chart_pullback_section (H := H) (I := I) p (c • f)) =
      c • 𝒪∞.presheaf.germ (chartSource (H := H) p) p (mem_chartSource (H := H) p)
        (chart_pullback_section (H := H) (I := I) p f) := by
  let U : Opens M := chartSource (H := H) p
  let hpU : p ∈ U := mem_chartSource (H := H) p
  letI : Algebra ℝ C^∞⟮I, U; 𝓘(ℝ), ℝ⟯ := inferInstance
  -- Rewrite scalar multiplication as multiplication by the constant section before applying the germ
  -- map, so multiplicativity of the stalk morphism does all the work.
  change ((𝒪∞.presheaf.germ U p hpU).hom)
      ((algebraMap ℝ C^∞⟮I, U; 𝓘(ℝ), ℝ⟯ c) *
        chart_pullback_section (H := H) (I := I) p f) =
    (algebraMap ℝ C^∞_[p](I) c) *
      ((𝒪∞.presheaf.germ U p hpU).hom
        (chart_pullback_section (H := H) (I := I) p f))
  -- After rewriting scalar multiplication as multiplication by a constant section, the germ map
  -- handles the calculation by multiplicativity alone.
  simpa [U, hpU] using
    chartSource_germ_map_smul (H := H) (I := I) p c
      (chart_pullback_section (H := H) (I := I) p f)

/-- Helper for Problem 3-7: taking the germ at `p` of chart-pulled-back model-space functions
preserves products. -/
private theorem germ_chart_pullback_section_mul [IsManifold I ∞ M] (p : M)
    (f g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    𝒪∞.presheaf.germ (chartSource (H := H) p) p (mem_chartSource (H := H) p)
        (chart_pullback_section (H := H) (I := I) p (f * g)) =
      𝒪∞.presheaf.germ (chartSource (H := H) p) p (mem_chartSource (H := H) p)
          (chart_pullback_section (H := H) (I := I) p f) *
        𝒪∞.presheaf.germ (chartSource (H := H) p) p (mem_chartSource (H := H) p)
          (chart_pullback_section (H := H) (I := I) p g) := by
  let U : Opens M := chartSource (H := H) p
  let hpU : p ∈ U := mem_chartSource (H := H) p
  -- Push multiplication through the chart pullback before applying the germ map.
  change ((𝒪∞.presheaf.germ U p hpU).hom)
      (chart_pullback_section (H := H) (I := I) p (f * g)) =
    ((𝒪∞.presheaf.germ U p hpU).hom)
        (chart_pullback_section (H := H) (I := I) p f) *
      ((𝒪∞.presheaf.germ U p hpU).hom)
        (chart_pullback_section (H := H) (I := I) p g)
  rw [chart_pullback_section_mul]
  exact map_mul ((𝒪∞.presheaf.germ U p hpU).hom)
    (chart_pullback_section (H := H) (I := I) p f)
    (chart_pullback_section (H := H) (I := I) p g)

/-- Helper for Problem 3-7: evaluating the germ of a chart-pulled-back model-space function at `p`
recovers the original model-space value at the chart point. -/
private theorem eval_chart_pullback_section_germ [IsManifold I ∞ M] (p : M)
    (g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    smoothSheafCommRing.eval I 𝓘(ℝ) M ℝ p
      (𝒪∞.presheaf.germ (chartSource (H := H) p) p (mem_chartSource (H := H) p)
        (chart_pullback_section (H := H) (I := I) p g)) =
      g (extChartAt I p p) := by
  -- Evaluate the germ on the chart source, then unfold the explicit pullback section.
  simpa [chart_pullback_section] using
    smoothSheafCommRing.eval_germ
      (IM := I) (I := 𝓘(ℝ)) (M := M) (R := ℝ) (U := chartSource (H := H) p)
      p (mem_chartSource (H := H) p)
      (chart_pullback_section (H := H) (I := I) p g)

/-- Helper for Problem 3-7: a germ derivation at `p` induces a point derivation on the model space
by acting on the germ of the preferred chart pullback of each test function. -/
def chart_pullback_germ_pointDerivation [IsManifold I ∞ M]
    (p : M) (v : smooth_germ_derivation_at I p) :
    PointDerivation 𝓘(ℝ, E) (extChartAt I p p) :=
  Derivation.mk'
    { toFun := fun g ↦
        v <| 𝒪∞.presheaf.germ (chartSource (H := H) p) p (mem_chartSource (H := H) p)
          (chart_pullback_section (H := H) (I := I) p g)
      map_add' := by
        intro f g
        -- Work directly with the chart-source germ instead of a chosen globalization.
        have h₁ := congrArg v
          (germ_chart_pullback_section_add (H := H) (I := I) p f g)
        have h₂ := v.map_add
          (𝒪∞.presheaf.germ (chartSource (H := H) p) p (mem_chartSource (H := H) p)
            (chart_pullback_section (H := H) (I := I) p f))
          (𝒪∞.presheaf.germ (chartSource (H := H) p) p (mem_chartSource (H := H) p)
            (chart_pullback_section (H := H) (I := I) p g))
        exact h₁.trans h₂
      map_smul' := by
        intro c f
        -- The same chart-source germ route handles scalar multiplication.
        have h₁ := congrArg v
          (germ_chart_pullback_section_smul (H := H) (I := I) p c f)
        have h₂ := v.map_smul c
          (𝒪∞.presheaf.germ (chartSource (H := H) p) p (mem_chartSource (H := H) p)
            (chart_pullback_section (H := H) (I := I) p f))
        simpa using h₁.trans h₂ }
    (fun f g ↦ by
      -- Route correction: the Leibniz computation now stays on the actual chart-source stalk.
      have h₁ := congrArg v
        (germ_chart_pullback_section_mul (H := H) (I := I) p f g)
      have h₂ := v.leibniz
        (𝒪∞.presheaf.germ (chartSource (H := H) p) p (mem_chartSource (H := H) p)
          (chart_pullback_section (H := H) (I := I) p f))
        (𝒪∞.presheaf.germ (chartSource (H := H) p) p (mem_chartSource (H := H) p)
          (chart_pullback_section (H := H) (I := I) p g))
      have hf_eval := eval_chart_pullback_section_germ (H := H) (I := I) p f
      have hg_eval := eval_chart_pullback_section_germ (H := H) (I := I) p g
      simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra, hf_eval, hg_eval] using
        h₁.trans h₂)

/-- Helper for Problem 3-7: evaluating the chart-source germ derivation means applying the germ
derivation to the stalk germ of the preferred chart pullback. -/
theorem chart_pullback_germ_pointDerivation_apply [IsManifold I ∞ M]
    (p : M) (v : smooth_germ_derivation_at I p) (g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    chart_pullback_germ_pointDerivation (H := H) (I := I) p v g =
      v (𝒪∞.presheaf.germ (chartSource (H := H) p) p (mem_chartSource (H := H) p)
        (chart_pullback_section (H := H) (I := I) p g)) :=
  rfl

/-- Helper for Problem 3-7: eventual equality with a global smooth model-space function upgrades the
within-derivative of the chart-written representative to the ordinary derivative of that global
function. -/
theorem fderivWithin_writtenInExtChartAt_eq_fderiv_of_eventuallyEq [IsManifold I ∞ M] (p : M)
    (f : C^∞⟮I, M; ℝ⟯) (g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯)
    (hg : g =ᶠ[nhdsWithin (extChartAt I p p) (Set.range I)]
      writtenInExtChartAt I 𝓘(ℝ) p f)
    (y : E) :
    fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ) p f) (Set.range I) (extChartAt I p p) y =
      fderiv ℝ g (extChartAt I p p) y := by
  let q : E := extChartAt I p p
  have hq_range : q ∈ Set.range I := by
    exact extChartAt_target_subset_range (I := I) p (mem_extChartAt_target (I := I) p)
  have hq_uniqueDiff : UniqueDiffWithinAt ℝ (Set.range I) q := by
    -- The chart point is canonically a point of the model range.
    simpa [q, extChartAt, mem_chart_source] using
      (I.uniqueDiffWithinAt_image (x := chartAt H p p))
  have hderivWithin :
      fderivWithin ℝ g (Set.range I) q =
        fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ) p f) (Set.range I) q :=
    Filter.EventuallyEq.fderivWithin_eq_of_mem (f₁ := g)
      (f := writtenInExtChartAt I 𝓘(ℝ) p f) hg hq_range
  have hg_diff : DifferentiableAt ℝ g q := by
    -- A global smooth model-space map is differentiable at every point.
    exact MDifferentiableAt.differentiableAt <|
      (g.contMDiff q).mdifferentiableAt (by norm_num)
  -- First replace the chart-written function by `g` within `range I`, then remove the `within`.
  calc
    fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ) p f) (Set.range I) q y
      = fderivWithin ℝ g (Set.range I) q y := by
          simpa using congrArg (fun A : E →L[ℝ] ℝ ↦ A y) hderivWithin.symm
    _ = fderiv ℝ g q y := by
          simpa using congrArg (fun A : E →L[ℝ] ℝ ↦ A y)
            (DifferentiableAt.fderivWithin hg_diff hq_uniqueDiff)

/-- Helper for Problem 3-7: choose an ambient open neighborhood around the chart point whose
closed intersection with `range I` stays inside the preferred chart target. -/
theorem closed_chart_neighborhood_within_target [IsManifold I ∞ M] (p : M) :
    ∃ U : Set E, IsOpen U ∧ extChartAt I p p ∈ U ∧
      closure (U ∩ Set.range I) ⊆ (extChartAt I p).target := by
  let q : E := extChartAt I p p
  let S : Set E := (extChartAt I p).target ∪ (Set.range I)ᶜ
  have hS_nhds : S ∈ nhds q := by
    -- The preferred chart target already contains a neighborhood of the chart point inside
    -- `range I`; adjoining the complement of `range I` turns this into an ambient neighborhood.
    simpa [q, S] using
      (extChartAt_target_union_compl_range_mem_nhds_of_mem (I := I)
        (x := p) (hy := mem_extChartAt_target (I := I) p))
  rcases exists_mem_nhds_isClosed_subset hS_nhds with ⟨T, hT_nhds, hT_closed, hTS⟩
  rcases mem_nhds_iff.1 hT_nhds with ⟨U, hUT, hU_open, hqU⟩
  refine ⟨U, hU_open, hqU, ?_⟩
  intro z hz
  have hzS : z ∈ S := by
    -- First keep the closure inside the closed neighborhood `T`, then use `T ⊆ S`.
    apply hTS
    exact closure_minimal (Set.Subset.trans Set.inter_subset_left hUT) hT_closed hz
  have hzRange : z ∈ Set.range I := by
    -- The closure is also taken inside the closed model range.
    exact closure_minimal Set.inter_subset_right I.isClosed_range hz
  rcases hzS with hzTarget | hzCompl
  · exact hzTarget
  · exact False.elim <| hzCompl hzRange

/-- Helper for Problem 3-7: there is a closed neighborhood of the chart point within `range I`
that is still contained in the preferred chart target. This is the closed set on which the
chart-written representative should be extended. -/
theorem exists_closed_chart_point_neighborhood_within_target [IsManifold I ∞ M] (p : M) :
    ∃ A : Set E, IsClosed A ∧
      A ∈ nhdsWithin (extChartAt I p p) (Set.range I) ∧
      A ⊆ (extChartAt I p).target := by
  rcases closed_chart_neighborhood_within_target (I := I) p with
    ⟨U, hU_open, hqU, hclosure⟩
  refine ⟨closure (U ∩ Set.range I), isClosed_closure, ?_, hclosure⟩
  have hU_mem : U ∩ Set.range I ∈ nhdsWithin (extChartAt I p p) (Set.range I) := by
    -- Intersect the ambient open neighborhood with `range I` to get a within-neighborhood.
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    exact ⟨U, hU_open.mem_nhds hqU, by intro y hy; exact ⟨hy.1, hy.2⟩⟩
  -- The closure still contains that within-neighborhood, so it is itself a within-neighborhood.
  exact Filter.mem_of_superset hU_mem subset_closure

/-- Helper for Problem 3-7: the preferred linear identification `ℝ ≃ ℝ¹`. -/
def real_to_r1_equiv : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  ((EuclideanSpace.equiv (Fin 1) ℝ).trans
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)).symm

/-- Helper for Problem 3-7: the chosen map from `ℝ` into `ℝ¹`. -/
def real_to_r1 : ℝ → EuclideanSpace ℝ (Fin 1) :=
  real_to_r1_equiv

/-- Helper for Problem 3-7: the unique coordinate of the preferred `ℝ¹` point recovers the
original scalar. -/
theorem real_to_r1_apply_zero (t : ℝ) :
    real_to_r1 t 0 = t := by
  -- The preferred identification is the inverse of the standard `ℝ¹ ≃ ℝ`.
  simp [real_to_r1, real_to_r1_equiv]

/-- Helper for Problem 3-7: on the preferred chart target, the chart-written representative is the
explicit chart pullback through `extChartAt`. -/
theorem writtenInExtChartAt_eq_on_target [IsManifold I ∞ M] (p : M)
    (f : C^∞⟮I, M; ℝ⟯) {y : E} (hy : y ∈ (extChartAt I p).target) :
    writtenInExtChartAt I 𝓘(ℝ) p f y = f ((extChartAt I p).symm y) := by
  -- On the chart target, the codomain chart for `ℝ` is the identity.
  have hy_target : y ∈ (extChartAt I p).target := hy
  simp only [writtenInExtChartAt, mfld_simps] at hy_target ⊢

/-- Helper for Problem 3-7: on the preferred chart target, the explicit pullback through the
inverse chart is a smooth ambient model-space function. -/
theorem writtenInExtChartAt_pullback_contMDiffOn_target [IsManifold I ∞ M] (p : M)
    (f : C^∞⟮I, M; ℝ⟯) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun y : E ↦ f ((extChartAt I p).symm y))
      ((extChartAt I p).target) := by
  -- Compose the global smooth function `f` with the inverse preferred chart on its natural target.
  simpa [Function.comp] using
    f.contMDiff.comp_contMDiffOn
      (contMDiffOn_extChartAt_symm (I := I) (n := ∞) p)

/-- Helper for Problem 3-7: scalar-valued smooth data on a closed subset extends to a global
smooth model-space function. -/
theorem exists_scalar_contDiff_extension_of_isClosed [FiniteDimensional ℝ E]
    {A U : Set E} (hA : IsClosed A) (hU : IsOpen U) (hAU : A ⊆ U)
    (r : A → ℝ) (hr : r.IsSmoothOn (𝓘(ℝ, E)) 𝓘(ℝ)) :
    ∃ g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯, ∀ x : A, g x = r x := by
  let r1 : A → EuclideanSpace ℝ (Fin 1) := fun x ↦ real_to_r1 (r x)
  have hr1 : r1.IsSmoothOn (𝓘(ℝ, E)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) := by
    rw [Function.isSmoothOn_iff_exists_local_extension] at hr ⊢
    intro x
    rcases hr x with ⟨V, hV_open, hxV, Fext, hFext, hEq⟩
    refine ⟨V, hV_open, hxV, real_to_r1 ∘ Fext, ?_, ?_⟩
    · -- Postcompose each scalar local extension with the fixed linear map `ℝ → ℝ¹`.
      simpa [real_to_r1, Function.comp] using
        real_to_r1_equiv.toContinuousLinearMap.contMDiff.comp_contMDiffOn hFext
    · intro y hy
      -- On the closed subset, the `ℝ¹` extension is just the packaged scalar value.
      simp [r1, hEq y hy, real_to_r1]
  rcases exists_supported_contMDiffMap_extension_of_isClosed
      (M := E) (I := 𝓘(ℝ, E)) (A := A) (U := U) hA hU hAU r1 hr1 with
    ⟨F, hF_eq, _hF_support⟩
  let proj0 :
      C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin 1)), EuclideanSpace ℝ (Fin 1); 𝓘(ℝ), ℝ⟯ :=
    (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)) :
      EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ) :
      C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin 1)), EuclideanSpace ℝ (Fin 1); 𝓘(ℝ), ℝ⟯)
  refine ⟨proj0.comp F, ?_⟩
  intro x
  -- Recover the scalar extension by taking the unique coordinate of the `ℝ¹` extension.
  simpa [proj0, real_to_r1_apply_zero] using congrArg (fun v : EuclideanSpace ℝ (Fin 1) ↦ v 0) (hF_eq x)

/-- Helper for Problem 3-7: choose an ambient open neighborhood around the chart point whose
closure stays inside the safe set consisting of the preferred chart target together with the
complement of `range I`. -/
theorem chart_neighborhood_closure_subset_safe_set [IsManifold I ∞ M] (p : M) :
    ∃ U : Set E, IsOpen U ∧ extChartAt I p p ∈ U ∧
      closure U ⊆ (extChartAt I p).target ∪ (Set.range I)ᶜ := by
  let q : E := extChartAt I p p
  let S : Set E := (extChartAt I p).target ∪ (Set.range I)ᶜ
  have hS_nhds : S ∈ nhds q := by
    -- The safe set is an ambient neighborhood of the chart point.
    simpa [q, S] using
      (extChartAt_target_union_compl_range_mem_nhds_of_mem (I := I)
        (x := p) (hy := mem_extChartAt_target (I := I) p))
  rcases exists_mem_nhds_isClosed_subset hS_nhds with ⟨T, hT_nhds, hT_closed, hTS⟩
  rcases mem_nhds_iff.1 hT_nhds with ⟨U, hUT, hU_open, hqU⟩
  refine ⟨U, hU_open, hqU, ?_⟩
  exact Set.Subset.trans (closure_minimal hUT hT_closed) hTS

/-- Helper for Problem 3-7: near each point of a subset of the preferred chart target, the inverse
chart pullback of a global smooth function admits an ambient-open smooth extension obtained by
composing with the smooth extended-chart transition to a chart centered at that point. -/
theorem chart_transition_local_extension [IsManifold I ∞ M] (p : M)
    (f : C^∞⟮I, M; ℝ⟯) {A : Set E} (hA_target : A ⊆ (extChartAt I p).target) (x : A) :
    ∃ V : Set E, IsOpen V ∧ (x : E) ∈ V ∧
      ∃ G : E → ℝ, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ G V ∧
        ∀ y : A, (y : E) ∈ V → G y = f ((extChartAt I p).symm y) := by
  -- TODO: choose an ambient-open neighborhood whose closed intersection with `range I` stays
  -- inside the smooth extended-chart transition source around `x`, then compose that transition
  -- with `writtenInExtChartAt I 𝓘(ℝ) x₀ f` and extend from the resulting closed subset.
  sorry

/-- Helper for Problem 3-7: the scalar chart-written representative of a global smooth function can
be extended to a global smooth model-space function near the chart point. -/
theorem writtenInExtChartAt_pullback_restrict_isSmoothOn [IsManifold I ∞ M] (p : M)
    (f : C^∞⟮I, M; ℝ⟯) {A : Set E} (hA_target : A ⊆ (extChartAt I p).target) :
    (fun y : A ↦ f ((extChartAt I p).symm y)).IsSmoothOn (𝓘(ℝ, E)) 𝓘(ℝ) := by
  -- Route correction: `extChartAt.target` is only relatively open in `range I`, so the boundary
  -- case needs pointwise ambient-open extensions built from smooth chart transitions.
  rw [Function.isSmoothOn_iff_exists_local_extension]
  intro x
  -- Use the transition to a chart centered at `(extChartAt I p).symm x` as the local extension
  -- mechanism, then package the resulting ambient-open extension.
  exact chart_transition_local_extension (H := H) (I := I) p f hA_target x

/-- Helper for Problem 3-7: once a global model-space representative agrees with the
chart-written representative near the chart point, its chart pullback defines the same stalk germ
as the original global manifold function. -/
theorem chart_pullback_section_germ_eq_topSection_of_eventuallyEq_writtenInExtChartAt
    [IsManifold I ∞ M] (p : M) (f : C^∞⟮I, M; ℝ⟯) (g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯)
    (hg : g =ᶠ[nhdsWithin (extChartAt I p p) (Set.range I)]
      writtenInExtChartAt I 𝓘(ℝ) p f) :
    𝒪∞.presheaf.germ (chartSource (H := H) p) p (mem_chartSource (H := H) p)
        (chart_pullback_section (H := H) (I := I) p g) =
      𝒪∞.presheaf.Γgerm p (topSection f) := by
  let q : E := extChartAt I p p
  have hEq :
      {y : E | g y = writtenInExtChartAt I 𝓘(ℝ) p f y} ∈ nhdsWithin q (Set.range I) := hg
  rcases mem_nhdsWithin.1 hEq with ⟨V, hVopen, hqV, hVeq⟩
  let W : Opens M := ⟨(chartSource (H := H) p : Set M) ∩ (extChartAt I p) ⁻¹' V, by
    dsimp [chartSource]
    simpa using isOpen_extChartAt_preimage (I := I) (H := H) p hVopen⟩
  let iSource : W ⟶ chartSource (H := H) p := homOfLE (by
    intro x hx
    exact hx.1)
  let iTop : W ⟶ (⊤ : Opens M) := homOfLE le_top
  -- Compare the two sections on a common neighborhood where the explicit chart pullback already
  -- agrees pointwise with the original global function.
  refine (smoothSheafCommRing.germ_eq_iff (I := I) (p := p) (U := chartSource (H := H) p)
    (V := (⊤ : Opens M)) (mem_chartSource (H := H) p) (by simp)
    (chart_pullback_section (H := H) (I := I) p g) (topSection f)).2 ?_
  refine ⟨W, ⟨mem_chartSource (H := H) p, hqV⟩, iSource, iTop, ?_⟩
  apply ContMDiffMap.ext
  intro x
  have hxSource : x.1 ∈ (extChartAt I p).source := by
    simpa [chartSource] using x.2.1
  have hxTarget : extChartAt I p x.1 ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hxSource
  have hxRange : extChartAt I p x.1 ∈ Set.range I :=
    extChartAt_target_subset_range (I := I) p hxTarget
  have hxEq :
      g (extChartAt I p x.1) = writtenInExtChartAt I 𝓘(ℝ) p f (extChartAt I p x.1) :=
    hVeq ⟨x.2.2, hxRange⟩
  have hxPull : g (extChartAt I p x.1) = f x.1 := by
    calc
      g (extChartAt I p x.1)
        = writtenInExtChartAt I 𝓘(ℝ) p f (extChartAt I p x.1) := hxEq
      _ = f x.1 := by
            rw [writtenInExtChartAt_eq_on_target (I := I) p f
              (y := extChartAt I p x.1) hxTarget]
            exact congrArg f ((extChartAt I p).left_inv hxSource)
  simpa [chart_pullback_section, topSection] using hxPull

/-- Helper for Problem 3-7: evaluating the chart-source germ derivation on a model-space test
function agreeing with the chart-written representative near the chart point gives the same value
as the original germ derivation on the ambient smooth function. -/
theorem chart_pullback_germ_pointDerivation_eq_toPointDerivation_of_eventuallyEq_writtenInExtChartAt
    [IsManifold I ∞ M] (p : M) (v : smooth_germ_derivation_at I p)
    (f : C^∞⟮I, M; ℝ⟯) (g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯)
    (hg : g =ᶠ[nhdsWithin (extChartAt I p p) (Set.range I)]
      writtenInExtChartAt I 𝓘(ℝ) p f) :
    chart_pullback_germ_pointDerivation (H := H) (I := I) p v g =
      smooth_germ_derivation_at.toPointDerivation v f := by
  calc
    chart_pullback_germ_pointDerivation (H := H) (I := I) p v g
      = v (𝒪∞.presheaf.germ (chartSource (H := H) p) p (mem_chartSource (H := H) p)
          (chart_pullback_section (H := H) (I := I) p g)) := by
            rw [chart_pullback_germ_pointDerivation_apply]
    _ = v (𝒪∞.presheaf.Γgerm p (topSection f)) := by
          congr 1
          exact chart_pullback_section_germ_eq_topSection_of_eventuallyEq_writtenInExtChartAt
            (H := H) (I := I) p f g hg
    _ = smooth_germ_derivation_at.toPointDerivation v f := by
          rfl

/-- Helper for Problem 3-7: the scalar chart-written representative of a global smooth function can
be extended to a global smooth model-space function near the chart point. -/
theorem writtenInExtChartAt_globalize_near_chartPoint [IsManifold I ∞ M]
    [FiniteDimensional ℝ E] (p : M) (f : C^∞⟮I, M; ℝ⟯) :
    ∃ g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯,
      g =ᶠ[nhdsWithin (extChartAt I p p) (Set.range I)] writtenInExtChartAt I 𝓘(ℝ) p f :=
  by
    let q : E := extChartAt I p p
    let u : E → ℝ := fun y ↦ f ((extChartAt I p).symm y)
    rcases exists_closed_chart_point_neighborhood_within_target (I := I) p with
      ⟨A, hA_closed, hA_nhds, hA_target⟩
    let r : A → ℝ := fun y ↦ u y
    have hr_smooth : r.IsSmoothOn (𝓘(ℝ, E)) 𝓘(ℝ) := by
      -- Route correction: after shrinking to a closed within-neighborhood inside the target, the
      -- ambient inverse-chart pullback itself is the required local extension.
      simpa [r, u] using
        writtenInExtChartAt_pullback_restrict_isSmoothOn (H := H) (I := I) p f hA_target
    rcases exists_scalar_contDiff_extension_of_isClosed
        (A := A) (U := Set.univ) hA_closed isOpen_univ (by simp) r hr_smooth with
      ⟨g, hg⟩
    refine ⟨g, ?_⟩
    -- Once the extension agrees with the pullback on the closed within-neighborhood `A`, the
    -- target formula rewrites it back to the chart-written representative near `q`.
    filter_upwards [hA_nhds] with y hyA
    have hyTarget : y ∈ (extChartAt I p).target := hA_target hyA
    calc
      g y = r ⟨y, hyA⟩ := hg ⟨y, hyA⟩
      _ = u y := rfl
      _ = writtenInExtChartAt I 𝓘(ℝ) p f y := by
            rw [writtenInExtChartAt_eq_on_target (I := I) p f hyTarget]

/-- Helper for Problem 3-7: a chart-side representing vector for the chart-source germ derivation
already gives the desired tangent vector without any Hausdorff globalization step. -/
theorem chart_representing_vector_gives_target_derivation_of_chart_pullback_germ
    [IsManifold I ∞ M] [FiniteDimensional ℝ E] (p : M)
    (v : smooth_germ_derivation_at I p) (y : E)
    (hy : ∀ g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯,
      chart_pullback_germ_pointDerivation (H := H) (I := I) p v g =
        fderiv ℝ g (extChartAt I p p) y) :
    let X : TangentSpace I p :=
      mfderiv[Set.range I] (extChartAt I p).symm (extChartAt I p p) y
    TangentSpace.toPointDerivation X = smooth_germ_derivation_at.toPointDerivation v := by
  let q : E := extChartAt I p p
  let X : TangentSpace I p :=
    mfderiv[Set.range I] (extChartAt I p).symm q y
  ext f
  rcases writtenInExtChartAt_globalize_near_chartPoint (H := H) (I := I) p f with ⟨g, hg⟩
  have hderiv :
      fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ) p f) (Set.range I) q y =
        fderiv ℝ g q y :=
    fderivWithin_writtenInExtChartAt_eq_fderiv_of_eventuallyEq
      (H := H) (I := I) p f g hg y
  have hX_eq : X = y := by
    -- In the preferred chart at the base point, the inverse-chart derivative is the identity.
    simpa [X, q] using
      congrArg
        (fun A : TangentSpace 𝓘(ℝ, E) q →L[ℝ] TangentSpace I p ↦ A y)
        (mfderivWithin_range_extChartAt_symm (I := I) (x := p))
  have hf_diff : MDifferentiableAt I 𝓘(ℝ) f p := by
    -- Global smoothness gives the manifold derivative of `f` at `p`.
    exact (f.contMDiff p).mdifferentiableAt (by norm_num)
  have hmfderiv :
      mfderiv I 𝓘(ℝ) f p =
        fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ) p f) (Set.range I) q := by
    -- Rewrite the manifold derivative through the chart-written representative of `f`.
    simpa [q] using
      (MDifferentiableAt.mfderiv (I := I) (I' := 𝓘(ℝ)) (f := f) (x := p) hf_diff)
  have hmfderiv_apply :
      mfderiv I 𝓘(ℝ) f p y =
        fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ) p f) (Set.range I) q y := by
    -- Apply the identified linear maps to the representing tangent vector.
    simpa [q] using congrArg (fun A ↦ A y) hmfderiv
  have hX_apply :
      TangentSpace.toPointDerivation X f =
        fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ) p f) (Set.range I) q y := by
    -- Evaluate the tangent-vector derivation in chart coordinates and replace `X` by `y`.
    rw [TangentSpace.toPointDerivation_apply, hX_eq]
    simpa using hmfderiv_apply
  have hchart :
      chart_pullback_germ_pointDerivation (H := H) (I := I) p v g =
        smooth_germ_derivation_at.toPointDerivation v f :=
    chart_pullback_germ_pointDerivation_eq_toPointDerivation_of_eventuallyEq_writtenInExtChartAt
      (H := H) (I := I) p v f g hg
  calc
    TangentSpace.toPointDerivation X f
      = fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ) p f) (Set.range I) q y := hX_apply
    _ = fderiv ℝ g q y := hderiv
    _ = chart_pullback_germ_pointDerivation (H := H) (I := I) p v g := by
          symm
          exact hy g
    _ = smooth_germ_derivation_at.toPointDerivation v f := hchart

/-- Helper for Problem 3-7: any tangent vector whose induced point derivation equals the given germ
derivation should push forward through the preferred chart to a vector representing the chart-side
germ derivation. -/
theorem chart_pushforward_represents_chart_pullback_germ_pointDerivation [IsManifold I ∞ M]
    [FiniteDimensional ℝ E] (p : M) (v : smooth_germ_derivation_at I p) {X : TangentSpace I p}
    (hX : TangentSpace.toPointDerivation X = smooth_germ_derivation_at.toPointDerivation v) :
    ∀ g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯,
      chart_pullback_germ_pointDerivation (H := H) (I := I) p v g =
        fderiv ℝ g (extChartAt I p p) (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p X) := by
  intro g
  -- TODO: transport `X` to the open chart source using the invertible differential of the open
  -- inclusion, compare its induced derivation on chart-pulled-back sections with the stalk
  -- derivation, and then identify the resulting model-space derivative through `extChartAt`.
  sorry

/-- Helper for Problem 3-7: equality after pushing tangent vectors through the preferred chart
forces equality of the original tangent vectors, without any separation hypothesis on `M`. -/
theorem tangent_eq_of_same_chart_pushforward_local [IsManifold I ∞ M] (p : M)
    {X X' : TangentSpace I p}
    (hpush :
      mfderiv I 𝓘(ℝ, E) (extChartAt I p) p X =
        mfderiv I 𝓘(ℝ, E) (extChartAt I p) p X') :
    X = X' := by
  have happly :
      mfderiv[Set.range I] (extChartAt I p).symm (extChartAt I p p)
          (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p X) =
        mfderiv[Set.range I] (extChartAt I p).symm (extChartAt I p p)
          (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p X') := by
    -- Apply the inverse chart derivative to the equality of pushed-forward vectors.
    exact congrArg
      (fun y : TangentSpace 𝓘(ℝ, E) (extChartAt I p p) ↦
        mfderiv[Set.range I] (extChartAt I p).symm (extChartAt I p p) y)
      hpush
  have hX :
      mfderiv[Set.range I] (extChartAt I p).symm (extChartAt I p p)
          (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p X) = X := by
    -- Differentiating the chart and its inverse shows that this composition is the identity.
    simpa using congrArg
      (fun A : TangentSpace I p →L[ℝ] TangentSpace I p ↦ A X)
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := I)
        (x := p) (y := p) (hy := mem_extChartAt_source (I := I) p))
  have hX' :
      mfderiv[Set.range I] (extChartAt I p).symm (extChartAt I p p)
          (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p X') = X' := by
    -- The same chart/inverse-chart identity holds for the competitor vector `X'`.
    simpa using congrArg
      (fun A : TangentSpace I p →L[ℝ] TangentSpace I p ↦ A X')
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := I)
        (x := p) (y := p) (hy := mem_extChartAt_source (I := I) p))
  exact hX.symm.trans <| happly.trans hX'

section

variable [T2Space M]

/-- Helper for Problem 3-7: a smooth model-space function can be globalized near `p` by
precomposing with the preferred chart and cutting off inside the preferred chart source. -/
theorem chartPullback_globalize_near_basepoint [IsManifold I ∞ M]
    [FiniteDimensional ℝ E] (p : M) (g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    ∃ f : C^∞⟮I, M; ℝ⟯, f =ᶠ[nhds p] (fun x ↦ g (extChartAt I p x)) := by
  classical
  let ψ : SmoothBumpFunction I p :=
    Classical.choice (show Nonempty (SmoothBumpFunction I p) from inferInstance)
  let f0 : M → ℝ := fun x ↦ ψ x * g (extChartAt I p x)
  have hpull_smooth :
      ContMDiffOn I 𝓘(ℝ) ∞ (fun x : M ↦ g (extChartAt I p x)) (chartAt H p).source := by
    -- Pull the global model-space test function back through the preferred chart on its source.
    simpa [Function.comp] using
      g.contMDiff.comp_contMDiffOn
        (contMDiffOn_extChartAt (I := I) (n := ∞) (x := p))
  have hf0_smooth : ContMDiff I 𝓘(ℝ) ∞ f0 := by
    -- The manifold bump function upgrades the local chart pullback to a global smooth function.
    simpa [f0, smul_eq_mul] using
      ψ.contMDiff_smul (g := fun x : M ↦ g (extChartAt I p x)) hpull_smooth
  refine ⟨⟨f0, hf0_smooth⟩, ?_⟩
  have hψ : ψ =ᶠ[nhds p] (1 : M → ℝ) :=
    ψ.eventuallyEq_one
  -- Near the basepoint the bump is identically `1`, so the cutoff disappears.
  filter_upwards [hψ] with x hx
  simp [f0, hx]

/-- Helper for Problem 3-7: if two global smooth manifold functions agree near `p`, the point
derivation induced by a germ derivation assigns them the same value. -/
theorem toPointDerivation_congr_of_eventuallyEq [IsManifold I ∞ M]
    [FiniteDimensional ℝ E] (p : M) (v : smooth_germ_derivation_at I p)
    (f g : C^∞⟮I, M; ℝ⟯) (hfg : f =ᶠ[nhds p] g) :
    smooth_germ_derivation_at.toPointDerivation v f =
      smooth_germ_derivation_at.toPointDerivation v g := by
  have hEq : {x : M | f x = g x} ∈ nhds p := hfg
  rcases mem_nhds_iff.1 hEq with ⟨U, hUsub, hU_open, hpU⟩
  exact smooth_germ_derivation_at.toPointDerivation_congr_of_eqOn_nhds
    (H := H) (I := I) v f g U hU_open hpU fun x hx ↦ hUsub hx

/-- Helper for Problem 3-7: choose a global smooth manifold function agreeing near `p` with the
pullback of a global smooth model-space function through the preferred chart. -/
noncomputable def globalizedChartPullback [IsManifold I ∞ M] [FiniteDimensional ℝ E]
    (p : M) (g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) : C^∞⟮I, M; ℝ⟯ :=
  (chartPullback_globalize_near_basepoint (H := H) (I := I) p g).choose

/-- Helper for Problem 3-7: the chosen globalization of a model-space test function agrees near `p`
with the preferred chart pullback. -/
theorem globalizedChartPullback_eventuallyEq [IsManifold I ∞ M] [FiniteDimensional ℝ E]
    (p : M) (g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    globalizedChartPullback (H := H) (I := I) p g =ᶠ[nhds p]
      fun x ↦ g (extChartAt I p x) :=
  (chartPullback_globalize_near_basepoint (H := H) (I := I) p g).choose_spec

/-- Helper for Problem 3-7: the chosen globalization of a sum agrees near `p` with the sum of the
chosen globalizations. -/
theorem globalizedChartPullback_add_eventuallyEq [IsManifold I ∞ M] [FiniteDimensional ℝ E]
    (p : M) (f g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    globalizedChartPullback (H := H) (I := I) p (f + g) =ᶠ[nhds p]
      globalizedChartPullback (H := H) (I := I) p f
        + globalizedChartPullback (H := H) (I := I) p g := by
  filter_upwards [globalizedChartPullback_eventuallyEq (H := H) (I := I) p (f + g),
    globalizedChartPullback_eventuallyEq (H := H) (I := I) p f,
    globalizedChartPullback_eventuallyEq (H := H) (I := I) p g] with x hfg hf hg
  calc
    globalizedChartPullback (H := H) (I := I) p (f + g) x
      = (f + g) (extChartAt I p x) := hfg
    _ = globalizedChartPullback (H := H) (I := I) p f x
          + globalizedChartPullback (H := H) (I := I) p g x := by
          simp [hf, hg]

/-- Helper for Problem 3-7: the chosen globalization of a scalar multiple agrees near `p` with the
scalar multiple of the chosen globalization. -/
theorem globalizedChartPullback_smul_eventuallyEq [IsManifold I ∞ M] [FiniteDimensional ℝ E]
    (p : M) (c : ℝ) (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    globalizedChartPullback (H := H) (I := I) p (c • f) =ᶠ[nhds p]
      c • globalizedChartPullback (H := H) (I := I) p f := by
  filter_upwards [globalizedChartPullback_eventuallyEq (H := H) (I := I) p (c • f),
    globalizedChartPullback_eventuallyEq (H := H) (I := I) p f] with x hcf hf
  calc
    globalizedChartPullback (H := H) (I := I) p (c • f) x
      = (c • f) (extChartAt I p x) := hcf
    _ = c • globalizedChartPullback (H := H) (I := I) p f x := by
          simp [hf]

/-- Helper for Problem 3-7: the chosen globalization of a product agrees near `p` with the
product of the chosen globalizations. -/
theorem globalizedChartPullback_mul_eventuallyEq [IsManifold I ∞ M] [FiniteDimensional ℝ E]
    (p : M) (f g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    globalizedChartPullback (H := H) (I := I) p (f * g) =ᶠ[nhds p]
      globalizedChartPullback (H := H) (I := I) p f
        * globalizedChartPullback (H := H) (I := I) p g := by
  filter_upwards [globalizedChartPullback_eventuallyEq (H := H) (I := I) p (f * g),
    globalizedChartPullback_eventuallyEq (H := H) (I := I) p f,
    globalizedChartPullback_eventuallyEq (H := H) (I := I) p g] with x hfg hf hg
  calc
    globalizedChartPullback (H := H) (I := I) p (f * g) x
      = (f * g) (extChartAt I p x) := hfg
    _ = globalizedChartPullback (H := H) (I := I) p f x
          * globalizedChartPullback (H := H) (I := I) p g x := by
          simp [hf, hg]

/-- Helper for Problem 3-7: eventual equality in chart coordinates gives eventual equality on the
manifold after precomposition with the preferred chart. -/
theorem pullback_extChartAt_eventuallyEq_of_eventuallyEq_writtenInExtChartAt [IsManifold I ∞ M]
    (p : M) (f : C^∞⟮I, M; ℝ⟯) (g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯)
    (hg : g =ᶠ[nhdsWithin (extChartAt I p p) (Set.range I)]
      writtenInExtChartAt I 𝓘(ℝ) p f) :
    (fun x : M ↦ g (extChartAt I p x)) =ᶠ[nhds p] f := by
  let q : E := extChartAt I p p
  have hEq :
      {y : E | g y = writtenInExtChartAt I 𝓘(ℝ) p f y} ∈ nhdsWithin q (Set.range I) := hg
  rcases mem_nhdsWithin.1 hEq with ⟨V, hVopen, hqV, hVeq⟩
  let U : Set M := (chartSource (H := H) p : Set M) ∩ (extChartAt I p) ⁻¹' V
  have hUopen : IsOpen U := by
    dsimp [U, chartSource]
    simpa using isOpen_extChartAt_preimage (I := I) (H := H) p hVopen
  have hpU : p ∈ U := by
    exact ⟨mem_chartSource (H := H) p, hqV⟩
  have hUnhds : U ∈ nhds p := hUopen.mem_nhds hpU
  refine Filter.mem_of_superset hUnhds ?_
  intro x hx
  have hxSource : x ∈ (extChartAt I p).source := by
    simpa [chartSource] using hx.1
  have hxTarget : extChartAt I p x ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hxSource
  have hxRange : extChartAt I p x ∈ Set.range I := by
    exact extChartAt_target_subset_range (I := I) p hxTarget
  have hlocal :
      g (extChartAt I p x) = writtenInExtChartAt I 𝓘(ℝ) p f (extChartAt I p x) :=
    hVeq ⟨hx.2, hxRange⟩
  calc
    g (extChartAt I p x)
      = writtenInExtChartAt I 𝓘(ℝ) p f (extChartAt I p x) := hlocal
    _ = f x := by
      rw [writtenInExtChartAt_eq_on_target (I := I) p f (y := extChartAt I p x) hxTarget]
      exact congrArg f ((extChartAt I p).left_inv hxSource)

/-- Helper for Problem 3-7: the chart-side point derivation obtained by globalizing model-space
test functions near `p`. -/
theorem globalChartModelPointDerivation_map_add [IsManifold I ∞ M] [FiniteDimensional ℝ E]
    (p : M) (v : smooth_germ_derivation_at I p)
    (f g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    smooth_germ_derivation_at.toPointDerivation v
        (globalizedChartPullback (H := H) (I := I) p (f + g))
      = smooth_germ_derivation_at.toPointDerivation v
          (globalizedChartPullback (H := H) (I := I) p f)
        + smooth_germ_derivation_at.toPointDerivation v
          (globalizedChartPullback (H := H) (I := I) p g) := by
  calc
    smooth_germ_derivation_at.toPointDerivation v
        (globalizedChartPullback (H := H) (I := I) p (f + g))
      = smooth_germ_derivation_at.toPointDerivation v
          (globalizedChartPullback (H := H) (I := I) p f
            + globalizedChartPullback (H := H) (I := I) p g) :=
        toPointDerivation_congr_of_eventuallyEq (H := H) (I := I) p v _ _
          (globalizedChartPullback_add_eventuallyEq (H := H) (I := I) p f g)
    _ = smooth_germ_derivation_at.toPointDerivation v
          (globalizedChartPullback (H := H) (I := I) p f)
        + smooth_germ_derivation_at.toPointDerivation v
          (globalizedChartPullback (H := H) (I := I) p g) := by
          exact (smooth_germ_derivation_at.toPointDerivation v).map_add _ _

/-- Helper for Problem 3-7: the chart-side point derivation obtained by globalizing model-space
test functions is `ℝ`-linear. -/
theorem globalChartModelPointDerivation_map_smul [IsManifold I ∞ M] [FiniteDimensional ℝ E]
    (p : M) (v : smooth_germ_derivation_at I p)
    (c : ℝ) (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    smooth_germ_derivation_at.toPointDerivation v
        (globalizedChartPullback (H := H) (I := I) p (c • f))
      = c * smooth_germ_derivation_at.toPointDerivation v
          (globalizedChartPullback (H := H) (I := I) p f) := by
  calc
    smooth_germ_derivation_at.toPointDerivation v
        (globalizedChartPullback (H := H) (I := I) p (c • f))
      = smooth_germ_derivation_at.toPointDerivation v
          (c • globalizedChartPullback (H := H) (I := I) p f) :=
        toPointDerivation_congr_of_eventuallyEq (H := H) (I := I) p v _ _
          (globalizedChartPullback_smul_eventuallyEq (H := H) (I := I) p c f)
    _ = c * smooth_germ_derivation_at.toPointDerivation v
          (globalizedChartPullback (H := H) (I := I) p f) := by
          exact (smooth_germ_derivation_at.toPointDerivation v).map_smul c _

/-- Helper for Problem 3-7: the chart-side point derivation obtained by globalizing model-space
test functions satisfies the Leibniz rule. -/
theorem globalChartModelPointDerivation_leibniz [IsManifold I ∞ M] [FiniteDimensional ℝ E]
    (p : M) (v : smooth_germ_derivation_at I p)
    (f g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    smooth_germ_derivation_at.toPointDerivation v
        (globalizedChartPullback (H := H) (I := I) p (f * g))
      = f (extChartAt I p p)
          * smooth_germ_derivation_at.toPointDerivation v
              (globalizedChartPullback (H := H) (I := I) p g)
        + g (extChartAt I p p)
          * smooth_germ_derivation_at.toPointDerivation v
              (globalizedChartPullback (H := H) (I := I) p f) := by
  have hf :
      globalizedChartPullback (H := H) (I := I) p f p = f (extChartAt I p p) := by
    simpa using (globalizedChartPullback_eventuallyEq (H := H) (I := I) p f).eq_of_nhds
  have hg :
      globalizedChartPullback (H := H) (I := I) p g p = g (extChartAt I p p) := by
    simpa using (globalizedChartPullback_eventuallyEq (H := H) (I := I) p g).eq_of_nhds
  calc
    smooth_germ_derivation_at.toPointDerivation v
        (globalizedChartPullback (H := H) (I := I) p (f * g))
      = smooth_germ_derivation_at.toPointDerivation v
          (globalizedChartPullback (H := H) (I := I) p f
            * globalizedChartPullback (H := H) (I := I) p g) :=
        toPointDerivation_congr_of_eventuallyEq (H := H) (I := I) p v _ _
          (globalizedChartPullback_mul_eventuallyEq (H := H) (I := I) p f g)
    _ = globalizedChartPullback (H := H) (I := I) p f p
          * smooth_germ_derivation_at.toPointDerivation v
              (globalizedChartPullback (H := H) (I := I) p g)
        + globalizedChartPullback (H := H) (I := I) p g p
          * smooth_germ_derivation_at.toPointDerivation v
              (globalizedChartPullback (H := H) (I := I) p f) := by
          exact point_derivation_leibniz
            (smooth_germ_derivation_at.toPointDerivation v)
            (globalizedChartPullback (H := H) (I := I) p f)
            (globalizedChartPullback (H := H) (I := I) p g)
    _ = f (extChartAt I p p)
          * smooth_germ_derivation_at.toPointDerivation v
              (globalizedChartPullback (H := H) (I := I) p g)
        + g (extChartAt I p p)
          * smooth_germ_derivation_at.toPointDerivation v
              (globalizedChartPullback (H := H) (I := I) p f) := by
          rw [hf, hg]

/-- Helper for Problem 3-7: a germ derivation at `p` induces a chart-side point derivation by
evaluating globalized model-space test functions. -/
noncomputable def globalChartModelPointDerivation [IsManifold I ∞ M] [FiniteDimensional ℝ E]
    (p : M) (v : smooth_germ_derivation_at I p) :
    PointDerivation 𝓘(ℝ, E) (extChartAt I p p) :=
  Derivation.mk'
    { toFun := fun g ↦
        smooth_germ_derivation_at.toPointDerivation v
          (globalizedChartPullback (H := H) (I := I) p g)
      map_add' := globalChartModelPointDerivation_map_add (H := H) (I := I) p v
      map_smul' := globalChartModelPointDerivation_map_smul (H := H) (I := I) p v }
    (globalChartModelPointDerivation_leibniz (H := H) (I := I) p v)

/-- Helper for Problem 3-7: evaluating the chart-side point derivation amounts to applying the
germ derivation to the chosen globalization of the model-space test function. -/
theorem globalChartModelPointDerivation_apply [IsManifold I ∞ M] [FiniteDimensional ℝ E]
    (p : M) (v : smooth_germ_derivation_at I p) (g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    globalChartModelPointDerivation (H := H) (I := I) p v g
      = smooth_germ_derivation_at.toPointDerivation v
          (globalizedChartPullback (H := H) (I := I) p g) :=
  rfl

/-- Helper for Problem 3-7: once a chart-side representing vector acts on all global smooth
model-space test functions, the corresponding tangent vector gives back the original germ
derivation on global smooth functions. -/
theorem chart_representing_vector_gives_target_derivation [IsManifold I ∞ M]
    [FiniteDimensional ℝ E] (p : M) (v : smooth_germ_derivation_at I p) (y : E)
    (hy : ∀ g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯,
      globalChartModelPointDerivation (H := H) (I := I) p v g
        = fderiv ℝ g (extChartAt I p p) y) :
    let X : TangentSpace I p :=
      mfderiv[Set.range I] (extChartAt I p).symm (extChartAt I p p) y
    TangentSpace.toPointDerivation X = smooth_germ_derivation_at.toPointDerivation v := by
  let q : E := extChartAt I p p
  let X : TangentSpace I p :=
    mfderiv[Set.range I] (extChartAt I p).symm q y
  ext f
  rcases writtenInExtChartAt_globalize_near_chartPoint (H := H) (I := I) p f with ⟨g, hg⟩
  have hpull :
      globalizedChartPullback (H := H) (I := I) p g =ᶠ[nhds p] f := by
    exact (globalizedChartPullback_eventuallyEq (H := H) (I := I) p g).trans <|
      pullback_extChartAt_eventuallyEq_of_eventuallyEq_writtenInExtChartAt
        (H := H) (I := I) p f g hg
  have hderiv :
      fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ) p f) (Set.range I) q y =
        fderiv ℝ g q y :=
    fderivWithin_writtenInExtChartAt_eq_fderiv_of_eventuallyEq
      (H := H) (I := I) p f g hg y
  have hX_eq : X = y := by
    -- In the preferred chart at the base point, the inverse-chart derivative is the identity.
    simpa [X, q] using
      congrArg
        (fun A : TangentSpace 𝓘(ℝ, E) q →L[ℝ] TangentSpace I p ↦ A y)
        (mfderivWithin_range_extChartAt_symm (I := I) (x := p))
  have hf_diff : MDifferentiableAt I 𝓘(ℝ) f p := by
    -- Global smoothness gives the manifold derivative of `f` at `p`.
    exact (f.contMDiff p).mdifferentiableAt (by norm_num)
  have hmfderiv :
      mfderiv I 𝓘(ℝ) f p =
        fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ) p f) (Set.range I) q := by
    -- Rewrite the manifold derivative through the chart-written representative of `f`.
    simpa [q] using
      (MDifferentiableAt.mfderiv (I := I) (I' := 𝓘(ℝ)) (f := f) (x := p) hf_diff)
  have hmfderiv_apply :
      mfderiv I 𝓘(ℝ) f p y =
        fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ) p f) (Set.range I) q y := by
    -- Apply the identified linear maps to the representing tangent vector.
    simpa [q] using congrArg (fun A ↦ A y) hmfderiv
  have hX_apply :
      TangentSpace.toPointDerivation X f =
        fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ) p f) (Set.range I) q y := by
    -- Evaluate the tangent-vector derivation in chart coordinates and replace `X` by `y`.
    rw [TangentSpace.toPointDerivation_apply, hX_eq]
    simpa using hmfderiv_apply
  have hglobal :
      globalChartModelPointDerivation (H := H) (I := I) p v g =
        smooth_germ_derivation_at.toPointDerivation v f := by
    calc
      globalChartModelPointDerivation (H := H) (I := I) p v g
        = smooth_germ_derivation_at.toPointDerivation v
            (globalizedChartPullback (H := H) (I := I) p g) := by
            rw [globalChartModelPointDerivation_apply]
      _ = smooth_germ_derivation_at.toPointDerivation v f :=
        toPointDerivation_congr_of_eventuallyEq (H := H) (I := I) p v _ _ hpull
  calc
    TangentSpace.toPointDerivation X f
      = fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ) p f) (Set.range I) q y := hX_apply
    _ = fderiv ℝ g q y := hderiv
    _ = globalChartModelPointDerivation (H := H) (I := I) p v g := by
          symm
          exact hy g
    _ = smooth_germ_derivation_at.toPointDerivation v f := hglobal

/-- Helper for Problem 3-7: any tangent vector whose induced point derivation equals the given germ
derivation pushes forward through the preferred chart to a vector representing the chart-side model
derivation. -/
theorem chart_pushforward_represents_chartModelPointDerivation [IsManifold I ∞ M]
    [FiniteDimensional ℝ E] (p : M) (v : smooth_germ_derivation_at I p) {X : TangentSpace I p}
    (hX : TangentSpace.toPointDerivation X = smooth_germ_derivation_at.toPointDerivation v) :
    ∀ g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯,
      globalChartModelPointDerivation (H := H) (I := I) p v g =
        fderiv ℝ g (extChartAt I p p) (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p X) := by
  intro g
  let q : E := extChartAt I p p
  let hpull : M → ℝ := fun x ↦ g (extChartAt I p x)
  let f := globalizedChartPullback (H := H) (I := I) p g
  have hf :
      f =ᶠ[nhds p] hpull :=
    globalizedChartPullback_eventuallyEq (H := H) (I := I) p g
  have hg_md : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) g q := by
    -- A global smooth model-space test function is differentiable at the chart point.
    exact (g.contMDiff q).mdifferentiableAt (by norm_num)
  have hchart :
      HasMFDerivAt I 𝓘(ℝ, E) (extChartAt I p) p
        (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p) := by
    -- The preferred chart has the expected manifold derivative at the base point.
    exact
      (mdifferentiableAt_extChartAt (I := I) (H := H) (x := p) (y := p)
        (mem_chart_source H p)).hasMFDerivAt
  have hpull_has :
      HasMFDerivAt I 𝓘(ℝ) hpull p
        ((fderiv ℝ g q).comp (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p)) := by
    -- Route correction: differentiate the actual pullback `g ∘ extChartAt I p` first, then use
    -- eventual equality to transfer the derivative to the globalized manifold function `f`.
    have hg_has :
        HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ) g q (fderiv ℝ g q) := by
      simpa [mfderiv_eq_fderiv] using hg_md.hasMFDerivAt
    simpa [hpull, Function.comp, q] using hg_has.comp p hchart
  have hf_mfderiv :
      mfderiv I 𝓘(ℝ) f p =
        (fderiv ℝ g q).comp (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p) := by
    -- Replace `f` by the chart pullback near `p`, where they agree by construction.
    exact (hpull_has.congr_of_eventuallyEq hf).mfderiv
  have hX_apply :
      TangentSpace.toPointDerivation X f =
        fderiv ℝ g q (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p X) := by
    -- Evaluating the tangent-vector derivation is exactly applying the transported derivative.
    rw [TangentSpace.toPointDerivation_apply]
    simpa [q] using congrArg (fun A : TangentSpace I p →L[ℝ] ℝ ↦ A X) hf_mfderiv
  calc
    globalChartModelPointDerivation (H := H) (I := I) p v g
        = smooth_germ_derivation_at.toPointDerivation v f := by
            rw [globalChartModelPointDerivation_apply]
    _ = TangentSpace.toPointDerivation X f := by
          rw [← hX]
    _ = fderiv ℝ g q (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p X) := hX_apply

/-- Helper for Problem 3-7: pushing forward the inverse-chart vector recovers the original
model-space vector at the chart point. -/
theorem chart_pushforward_of_inverse_chart_vector [IsManifold I ∞ M]
    (p : M) (y : E) :
    mfderiv I 𝓘(ℝ, E) (extChartAt I p) p
        (mfderiv[Set.range I] (extChartAt I p).symm (extChartAt I p p) y) = y := by
  -- Differentiate `extChartAt I p ∘ (extChartAt I p).symm = id` at the chart point and apply the
  -- resulting linear-map identity to the chosen model-space vector.
  simpa using
    congrArg
      (fun A : TangentSpace 𝓘(ℝ, E) (extChartAt I p p) →L[ℝ]
          TangentSpace 𝓘(ℝ, E) (extChartAt I p p) ↦ A y)
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' (I := I)
        (x := p) (y := p) (hy := mem_extChartAt_source (I := I) p))

/-- Helper for Problem 3-7: equality after pushing tangent vectors through the preferred chart
forces equality of the original tangent vectors. -/
theorem tangent_eq_of_same_chart_pushforward [IsManifold I ∞ M] (p : M)
    {X X' : TangentSpace I p}
    (hpush :
      mfderiv I 𝓘(ℝ, E) (extChartAt I p) p X =
        mfderiv I 𝓘(ℝ, E) (extChartAt I p) p X') :
    X = X' := by
  -- Apply the derivative of the inverse preferred chart to both pushed-forward vectors.
  have happly :
      mfderiv[Set.range I] (extChartAt I p).symm (extChartAt I p p)
          (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p X) =
        mfderiv[Set.range I] (extChartAt I p).symm (extChartAt I p p)
          (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p X') := by
    exact congrArg
      (fun y : TangentSpace 𝓘(ℝ, E) (extChartAt I p p) ↦
        mfderiv[Set.range I] (extChartAt I p).symm (extChartAt I p p) y)
      hpush
  have hX :
      mfderiv[Set.range I] (extChartAt I p).symm (extChartAt I p p)
          (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p X) = X := by
    -- The chart derivative followed by the inverse-chart derivative is the identity at `p`.
    simpa using congrArg
      (fun A : TangentSpace I p →L[ℝ] TangentSpace I p ↦ A X)
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := I)
        (x := p) (y := p) (hy := mem_extChartAt_source (I := I) p))
  have hX' :
      mfderiv[Set.range I] (extChartAt I p).symm (extChartAt I p p)
          (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p X') = X' := by
    -- The same inverse-chart identity holds for `X'`.
    simpa using congrArg
      (fun A : TangentSpace I p →L[ℝ] TangentSpace I p ↦ A X')
          (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := I)
        (x := p) (y := p) (hy := mem_extChartAt_source (I := I) p))
  exact hX.symm.trans <| happly.trans hX'
end
end smooth_germ_derivation_at

/-- Helper for Problem 3-7: a point derivation on a finite-dimensional model space is evaluation of
the Fréchet derivative along a unique vector. -/
theorem model_point_derivation_existsUnique_vector [FiniteDimensional ℝ E]
    (q : E) (w : PointDerivation 𝓘(ℝ, E) q) :
    ∃! y : E, ∀ f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯, w f = fderiv ℝ f q y := by
  let n : ℕ := Module.finrank ℝ E
  have hfin : Module.finrank ℝ E = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    -- Replace the model space by a Euclidean space of the same finite dimension.
    calc
      Module.finrank ℝ E = n := by simp [n]
      _ = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by simp [EuclideanSpace]
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin n) := ContinuousLinearEquiv.ofFinrankEq hfin
  let eMap :
      C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, EuclideanSpace ℝ (Fin n)), EuclideanSpace ℝ (Fin n)⟯ :=
    ((e : E →L[ℝ] EuclideanSpace ℝ (Fin n)) :
      C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, EuclideanSpace ℝ (Fin n)), EuclideanSpace ℝ (Fin n)⟯)
  let eInvMap :
      C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), EuclideanSpace ℝ (Fin n); 𝓘(ℝ, E), E⟯ :=
    ((e.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] E) :
      C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), EuclideanSpace ℝ (Fin n); 𝓘(ℝ, E), E⟯)
  let w' : PointDerivation 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (e q) := 𝒅 eMap q w
  let z : geometric_tangent_space (e q) :=
    (geometric_to_point_derivation_linear_equiv (n := n) (e q)).symm w'
  refine ⟨e.symm z, ?_, ?_⟩
  · intro f
    have hz : w' = directional_point_derivation (n := n) (e q) z := by
      -- Proposition 3.2 identifies the pushed-forward derivation with a unique Euclidean vector.
      calc
        w' = geometric_to_point_derivation_linear_equiv (n := n) (e q) z := by
          simp [z]
        _ = directional_point_derivation (n := n) (e q) z :=
          geometric_to_point_derivation_linear_equiv_apply (n := n) (e q) z
    have hf : DifferentiableAt ℝ f q := by
      -- Global smoothness on the model space gives ordinary differentiability at `q`.
      exact MDifferentiableAt.differentiableAt <|
        (f.contMDiff q).mdifferentiableAt (by norm_num)
    have hf' : DifferentiableAt ℝ f (e.symm (e q)) := by simpa using hf
    have heinv : DifferentiableAt ℝ (fun x : EuclideanSpace ℝ (Fin n) ↦ e.symm x) (e q) := by
      exact (e.symm.hasFDerivAt).differentiableAt
    calc
      w f = ((𝒅 eMap q) w) (f.comp eInvMap) := by
        -- Pull the test function through the linear equivalence and use the definition of `𝒅`.
        have hcompid : (f.comp eInvMap).comp eMap = f := by
          ext x
          simp [eMap, eInvMap]
        rw [fdifferential_apply]
        exact congrArg w hcompid.symm
      _ = w' (f.comp eInvMap) := rfl
      _ = fderiv ℝ (f.comp eInvMap) (e q) z := by
        -- The Euclidean-space representative acts by directional derivative.
        rw [hz, directional_point_derivation_apply]
      _ = fderiv ℝ f q (e.symm z) := by
        -- Transport the directional derivative back along the linear equivalence.
        change fderiv ℝ (fun x : EuclideanSpace ℝ (Fin n) ↦ f (e.symm x)) (e q) z =
          fderiv ℝ f q (e.symm z)
        have hcomp := fderiv_comp (𝕜 := ℝ)
          (f := fun x : EuclideanSpace ℝ (Fin n) ↦ e.symm x) (g := f) (x := e q) hf' heinv
        have happly := congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ ↦ A z) hcomp
        simpa [ContinuousLinearEquiv.fderiv] using happly
  · intro y hy
    have hy' : ∀ g : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), EuclideanSpace ℝ (Fin n); ℝ⟯,
        w' g = fderiv ℝ g (e q) (e y) := by
      intro g
      have hg : DifferentiableAt ℝ g (e q) := by
        -- Smooth Euclidean test functions are differentiable at the chart point.
        exact MDifferentiableAt.differentiableAt <|
          (g.contMDiff (e q)).mdifferentiableAt (by norm_num)
      have he : DifferentiableAt ℝ (fun x : E ↦ e x) q := by
        exact (e.hasFDerivAt).differentiableAt
      calc
        w' g = w (g.comp eMap) := by
          -- Pushing `w` forward by `e` means precomposing test functions with `e`.
          change ((𝒅 eMap q) w) g = w (g.comp eMap)
          rw [fdifferential_apply]
        _ = fderiv ℝ (g.comp eMap) q y := hy (g.comp eMap)
        _ = fderiv ℝ g (e q) (e y) := by
          -- The same chain-rule computation identifies the pushed-forward vector as `e y`.
          change fderiv ℝ (fun x : E ↦ g (e x)) q y = fderiv ℝ g (e q) (e y)
          have hcomp := fderiv_comp (𝕜 := ℝ) (f := fun x : E ↦ e x) (g := g) (x := q) hg he
          have happly := congrArg (fun A : E →L[ℝ] ℝ ↦ A y) hcomp
          simpa [ContinuousLinearEquiv.fderiv] using happly
    have hyz : directional_point_derivation (n := n) (e q) (e y) = w' := by
      -- The transported vector `e y` gives the same Euclidean derivation as `w'`.
      ext g
      rw [directional_point_derivation_apply]
      exact (hy' g).symm
    have heq : e y = z := by
      -- Uniqueness in Proposition 3.2 identifies the Euclidean vectors.
      apply (geometric_to_point_derivation_linear_equiv (n := n) (e q)).injective
      calc
        geometric_to_point_derivation_linear_equiv (n := n) (e q) (e y)
            = directional_point_derivation (n := n) (e q) (e y) :=
              geometric_to_point_derivation_linear_equiv_apply (n := n) (e q) (e y)
        _ = w' := hyz
        _ = geometric_to_point_derivation_linear_equiv (n := n) (e q) z := by
              simp [z]
    exact e.injective (by simpa using heq)

-- Proof sketch: identify tangent vectors with derivations in local coordinates around `p`, use the
-- locality encoded by germs to show that every germ derivation is determined by its values on
-- coordinate functions, and reconstruct the unique tangent vector from those coordinates.
/-- Problem 3-7: every derivation of the algebra of smooth germs at `p` is represented by a unique
tangent vector whose induced point derivation on global smooth functions is the one associated to
the given germ derivation. -/
theorem smooth_germ_derivation_existsUnique_tangentVector [IsManifold I ∞ M]
    [FiniteDimensional ℝ E] (p : M) (v : smooth_germ_derivation_at I p) :
    ∃! X : TangentSpace I p,
      TangentSpace.toPointDerivation X =
        smooth_germ_derivation_at.toPointDerivation v := by
  let w : PointDerivation 𝓘(ℝ, E) (extChartAt I p p) :=
    smooth_germ_derivation_at.chart_pullback_germ_pointDerivation (H := H) (I := I) p v
  rcases model_point_derivation_existsUnique_vector (q := extChartAt I p p) w with ⟨y, hy, hyuniq⟩
  let X : TangentSpace I p :=
    mfderiv[Set.range I] (extChartAt I p).symm (extChartAt I p p) y
  refine ⟨X, ?_, ?_⟩
  · have hrepr :
        TangentSpace.toPointDerivation X =
          smooth_germ_derivation_at.toPointDerivation v := by
      -- The existence half now closes directly through the chart-source germ derivation.
      simpa [X] using
        smooth_germ_derivation_at.chart_representing_vector_gives_target_derivation_of_chart_pullback_germ
          (H := H) (I := I) p v y hy
    exact hrepr
  · intro X' hX'
    have hpushX :
        mfderiv I 𝓘(ℝ, E) (extChartAt I p) p X = y := by
      -- The chosen tangent vector is defined by transporting `y` back through the inverse chart.
      simpa [X] using
        congrArg
          (fun A : TangentSpace 𝓘(ℝ, E) (extChartAt I p p) →L[ℝ]
              TangentSpace 𝓘(ℝ, E) (extChartAt I p p) ↦ A y)
          (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' (I := I)
            (x := p) (y := p) (hy := mem_extChartAt_source (I := I) p))
    have hreprX' :
        ∀ g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯,
          w g = fderiv ℝ g (extChartAt I p p)
            (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p X') := by
      intro g
      -- The remaining local bridge compares the chart-source germ derivation with any competing
      -- tangent vector that induces the same global point derivation.
      simpa [w] using
        smooth_germ_derivation_at.chart_pushforward_represents_chart_pullback_germ_pointDerivation
          (H := H) (I := I) p v hX' g
    have hpushX' :
        mfderiv I 𝓘(ℝ, E) (extChartAt I p) p X' = y :=
      hyuniq _ hreprX'
    -- Once both tangent vectors push forward to the same chart vector, invert the chart
    -- derivative to recover equality in the manifold tangent space.
    exact
      smooth_germ_derivation_at.tangent_eq_of_same_chart_pushforward_local
        (H := H) (I := I) p (hpushX'.trans hpushX.symm)

namespace smooth_germ_derivation_at

variable {p : M}

/-- Problem 3-7, finite-dimensional bridge: a derivation of smooth germs at `p` determines the
corresponding tangent vector whose associated point derivation agrees with the germ derivation on
global smooth functions. -/
noncomputable def toTangentSpace [IsManifold I ∞ M] [FiniteDimensional ℝ E]
    (v : smooth_germ_derivation_at I p) : TangentSpace I p :=
  (smooth_germ_derivation_existsUnique_tangentVector p v).choose

@[simp] theorem toPointDerivation_toTangentSpace [IsManifold I ∞ M] [FiniteDimensional ℝ E]
    (v : smooth_germ_derivation_at I p) :
    TangentSpace.toPointDerivation (toTangentSpace v) = toPointDerivation v :=
  (smooth_germ_derivation_existsUnique_tangentVector p v).choose_spec.1

theorem eq_toTangentSpace [IsManifold I ∞ M] [FiniteDimensional ℝ E]
    (v : smooth_germ_derivation_at I p) {X : TangentSpace I p}
    (hX : TangentSpace.toPointDerivation X = toPointDerivation v) :
    X = toTangentSpace v := by
  exact (smooth_germ_derivation_existsUnique_tangentVector p v).unique hX
    (toPointDerivation_toTangentSpace v)

end smooth_germ_derivation_at

end
