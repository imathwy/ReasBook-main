import LinearRepresentations_Serre_1977.Serre.Chap04.Definition_4_9
import Mathlib.Analysis.InnerProductSpace.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Definition 4-10: a Hilbert-space representation of `G` on the complex Hilbert space `H` is a
homomorphism `G →* (H ≃L[ℂ] H)` whose action map `G × H → H`, `(g, v) ↦ ρ(g)(v)`, is
continuous. The bridge to the Chapter 4 continuity owner `Representation.IsContinuous` is exposed
below through `ρ.toRepresentation`. -/
structure HilbertSpaceRepresentation (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    extends G →* (H ≃L[ℂ] H) where
  /-- The action map attached to `ρ` is continuous. -/
  continuous_action : Continuous fun gv : G × H ↦ toMonoidHom gv.1 gv.2

namespace HilbertSpaceRepresentation

instance : CoeFun (HilbertSpaceRepresentation G H) fun _ ↦ G → H ≃L[ℂ] H :=
  ⟨fun ρ ↦ ρ.toMonoidHom⟩

/-- The source continuity condition for `ρ` is continuity of its action map `G × H → H`. -/
theorem continuousAction (ρ : HilbertSpaceRepresentation G H) :
    Continuous fun gv : G × H ↦ ρ gv.1 gv.2 :=
  by simpa using ρ.continuous_action

/-- Each orbit map of a Hilbert-space representation is continuous. -/
theorem continuous_apply (ρ : HilbertSpaceRepresentation G H) (v : H) :
    Continuous fun g ↦ ρ g v :=
  (continuousAction ρ).comp (continuous_id.prodMk continuous_const)

/-- The underlying linear representation attached to a Hilbert-space representation. -/
def toRepresentation (ρ : HilbertSpaceRepresentation G H) : Representation ℂ G H where
  toFun g := (ρ g).toLinearMap
  map_one' := by
    ext v
    change ρ 1 v = v
    rw [map_one]
    rfl
  map_mul' g h := by
    ext v
    change ρ (g * h) v = ρ g (ρ h v)
    rw [map_mul]
    rfl

@[simp]
theorem toRepresentation_apply (ρ : HilbertSpaceRepresentation G H) (g : G) :
    ρ.toRepresentation g = (ρ g).toLinearMap :=
  rfl

@[simp]
theorem toRepresentation_apply_apply (ρ : HilbertSpaceRepresentation G H) (g : G) (v : H) :
    ρ.toRepresentation g v = ρ g v :=
  rfl

/-- The representation underlying a Hilbert-space representation is continuous in the sense of
Definition 4-9. -/
instance instRepresentationIsContinuous (ρ : HilbertSpaceRepresentation G H) :
    Representation.IsContinuous ρ.toRepresentation where
  continuous_action := by
    simpa using ρ.continuous_action

end HilbertSpaceRepresentation

end
