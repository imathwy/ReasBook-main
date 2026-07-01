import Mathlib
import cartan.II.section05.«0004_Definition_II_1_extra_4»

-- Declarations for this item will be appended below by the statement pipeline.

open Set

universe u v

section

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {a b : ℝ}

/-- The local witness at a parameter value `τ` for a primitive along `γ`: on some neighborhood of
`τ` in the segment, the function agrees with the pullback of a primitive of `ω` defined on an open
neighborhood of `γ τ` contained in `D`. -/
def HasLocalPrimitiveAlongPathAt
    (ω : E → E →L[ℝ] F) (D : Set E)
    (γ : C(Icc a b, E)) (f : C(Icc a b, F)) (τ : Icc a b) : Prop :=
  ∃ s : Set (Icc a b), IsOpen s ∧ τ ∈ s ∧
    ∃ U : Set E, IsOpen U ∧ γ τ ∈ U ∧ U ⊆ D ∧ MapsTo γ s U ∧
      ∃ primitive : E → F,
        (∀ x ∈ U, HasFDerivAt primitive (ω x) x) ∧
          EqOn f (primitive ∘ γ) s

/-- Definition II.1-extra-7: a continuous function on the segment `[a,b]` is a primitive of the
closed differential form `ω` along the path `γ` when this local primitive condition holds at every
parameter value. -/
def IsPrimitiveAlongPath
    (ω : E → E →L[ℝ] F) (D : Set E)
    (γ : C(Icc a b, E)) (f : C(Icc a b, F)) : Prop :=
  ∀ τ : Icc a b, HasLocalPrimitiveAlongPathAt ω D γ f τ

/-- Near every parameter value of the segment, the function agrees with the pullback of a local
primitive of `ω` defined on a neighborhood in `D` of the corresponding point of the path. -/
theorem IsPrimitiveAlongPath.local_primitive
    {ω : E → E →L[ℝ] F} {D : Set E}
    {γ : C(Icc a b, E)} {f : C(Icc a b, F)}
    (hf : IsPrimitiveAlongPath ω D γ f) (τ : Icc a b) :
    HasLocalPrimitiveAlongPathAt ω D γ f τ :=
  hf τ

-- Proof sketch: use the neighborhood `U` from the local primitive witness at `τ`; the center
-- point `γ τ` lies in `U`, and `U ⊆ D`.
/-- A local primitive witness at `τ` forces the image point `γ τ` to lie in the ambient domain
`D`. -/
theorem HasLocalPrimitiveAlongPathAt.mem_domain
    {ω : E → E →L[ℝ] F} {D : Set E}
    {γ : C(Icc a b, E)} {f : C(Icc a b, F)} {τ : Icc a b}
    (hτ : HasLocalPrimitiveAlongPathAt ω D γ f τ) :
    γ τ ∈ D := by
  rcases hτ with ⟨_, _, _, U, _, hγU, hUD, _, _, _, _⟩
  exact hUD hγU

-- Proof sketch: apply `HasLocalPrimitiveAlongPathAt.mem_domain` to the local witness at `τ`.
/-- A primitive along a path is evaluated only at points of the path lying in the ambient domain
`D`. -/
theorem IsPrimitiveAlongPath.mem_domain
    {ω : E → E →L[ℝ] F} {D : Set E}
    {γ : C(Icc a b, E)} {f : C(Icc a b, F)}
    (hf : IsPrimitiveAlongPath ω D γ f) (τ : Icc a b) :
    γ τ ∈ D :=
  (hf.local_primitive τ).mem_domain

section GlobalToPath

variable {x y : E}

/-- Compose a global primitive with a path whose image lies in the primitive domain. -/
noncomputable def IsPrimitiveOn.alongPath
    {D : Set E} {ω : E → E →L[ℝ] F} {primitive : E → F}
    (hprimitive : IsPrimitiveOn D ω primitive) (γ : Path x y) (hγD : Set.range γ ⊆ D) :
    C(Icc (0 : ℝ) 1, F) :=
  ⟨fun t ↦ primitive (γ t), by
    refine continuous_iff_continuousAt.mpr fun t ↦ ?_
    exact (hprimitive (γ t) (hγD ⟨t, rfl⟩)).continuousAt.comp (γ.continuousAt t)⟩

@[simp]
theorem IsPrimitiveOn.alongPath_apply
    {D : Set E} {ω : E → E →L[ℝ] F} {primitive : E → F}
    (hprimitive : IsPrimitiveOn D ω primitive) (γ : Path x y) (hγD : Set.range γ ⊆ D)
    (t : Icc (0 : ℝ) 1) :
    hprimitive.alongPath γ hγD t = primitive (γ t) :=
  rfl

/-- A primitive on an open set restricts to a primitive along every path contained in that set. -/
theorem IsPrimitiveOn.isPrimitiveAlongPath
    {D : Set E} (hD_open : IsOpen D) {ω : E → E →L[ℝ] F} {primitive : E → F}
    (hprimitive : IsPrimitiveOn D ω primitive) (γ : Path x y) (hγD : Set.range γ ⊆ D) :
    IsPrimitiveAlongPath ω D γ (hprimitive.alongPath γ hγD) := by
  intro τ
  refine ⟨Set.univ, isOpen_univ, mem_univ τ, D, hD_open, hγD ⟨τ, rfl⟩, Subset.rfl, ?_, ?_⟩
  · intro t _
    exact hγD ⟨t, rfl⟩
  · refine ⟨primitive, hprimitive, ?_⟩
    intro t _
    rfl

end GlobalToPath

end
