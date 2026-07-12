import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Subgroup.Basic

-- Semantic recall: mathlib's generic owner is `Representation.ind`; this file records the
-- inversion bridge between the two raw function-space conventions in Remark 4-42.
-- Verified semantic recall: `MonoidHom.map_inv` gives the inversion compatibility needed
-- when `θ` is expressed as a character `S →* A`.

universe uG uA uV

section

variable {G : Type uG} {V : Type uV}
variable [Group G]

/-- Pull a function on a group back along inversion. -/
def inducedConventionInversion (F : G → V) : G → V :=
  fun u ↦ F u⁻¹

@[simp] theorem inducedConventionInversion_apply (F : G → V) (u : G) :
    inducedConventionInversion F u = F u⁻¹ := rfl

/-- `inducedConventionInversion` is an involution on `G → V`. -/
theorem inducedConventionInversion_involutive :
    Function.Involutive (fun F : G → V ↦ inducedConventionInversion F) := by
  intro F
  funext u
  simp [inducedConventionInversion]

@[simp] theorem inducedConventionInversion_inducedConventionInversion (F : G → V) :
    inducedConventionInversion (inducedConventionInversion F) = F :=
  inducedConventionInversion_involutive F

@[simp] theorem inducedConventionInversion_translate_apply (F : G → V) (s u : G) :
    inducedConventionInversion (fun x ↦ F (s⁻¹ * x)) u = inducedConventionInversion F (u * s) := by
  simp [inducedConventionInversion]

/-- Remark 4-42 (2): the same inversion change of variables converts left translation
`x ↦ F (s⁻¹ * x)` into right translation `u ↦ f (u * s)`. -/
theorem inducedConventionInversion_translate (F : G → V) (s : G) :
    inducedConventionInversion (fun x ↦ F (s⁻¹ * x)) =
      fun u ↦ inducedConventionInversion F (u * s) := by
  funext u
  exact inducedConventionInversion_translate_apply F s u

end

section

variable {G : Type uG} {A : Type uA} {V : Type uV}
variable [Group G] [Group A] [MulAction A V]

/-- Remark 4-42 (1): replacing `u` by `u⁻¹` converts the convention
`F (x * h) = (θ h)⁻¹ • F x` into `f (t * u) = θ t • f u`
for a character `θ : S →* A`. -/
theorem inducedConventionInversion_iff
    (S : Subgroup G) (θ : S →* A) (F : G → V) :
    (∀ x : G, ∀ h : S, F (x * h) = (θ h)⁻¹ • F x) ↔
      (∀ u : G, ∀ t : S,
        inducedConventionInversion F (t * u) = θ t • inducedConventionInversion F u) := by
  constructor
  · intro h u t
    simpa [inducedConventionInversion] using h u⁻¹ t⁻¹
  · intro h x t
    simpa [inducedConventionInversion] using h x⁻¹ t⁻¹

end
