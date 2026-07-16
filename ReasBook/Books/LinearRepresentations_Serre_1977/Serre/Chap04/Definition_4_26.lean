import LinearRepresentations_Serre_1977.Serre.Chap02.Remark_2_2_1_2

-- Semantic recall: `IsClassFunction` is the existing canonical owner for functions constant on
-- conjugacy classes.

universe u

section

variable {G : Type u} [Group G]

/-- A class function is invariant under conjugation. -/
theorem IsClassFunction.map_conj_eq {R : Type*} {f : G → R} (hf : IsClassFunction f)
    (s t : G) : f (s * t * s⁻¹) = f t := by
  simpa [mul_assoc] using
    hf.eq_of_isConj (isConj_iff.2 ⟨s⁻¹, by simp [mul_assoc]⟩)

/-- A function invariant under conjugation is a class function. -/
theorem isClassFunction_of_forall_conj_eq {R : Type*} {f : G → R}
    (hf : ∀ s t : G, f (s * t * s⁻¹) = f t) : IsClassFunction f := by
  refine ⟨?_⟩
  intro u v huv
  rcases isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp huv) with ⟨s, hs⟩
  calc
    f u = f (s * u * s⁻¹) := (hf s u).symm
    _ = f v := by simp [hs]

/-- Definition 4-26: a complex-valued function on `G` is a class function exactly when it satisfies
Serre's source-facing conjugation identity `f (s * t * s⁻¹) = f t` for all `s t : G`. -/
theorem isClassFunction_iff_forall_conj_eq (f : G → ℂ) :
    IsClassFunction f ↔ ∀ s t : G, f (s * t * s⁻¹) = f t := by
  constructor
  · exact IsClassFunction.map_conj_eq
  · exact isClassFunction_of_forall_conj_eq

end
