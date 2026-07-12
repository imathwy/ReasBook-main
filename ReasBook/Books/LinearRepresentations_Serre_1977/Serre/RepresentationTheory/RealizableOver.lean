import Mathlib

noncomputable section

universe u v w u₀ u₁

open scoped TensorProduct

namespace Representation

section

variable {k : Type v} [CommRing k]
variable {k₀ : Type u₀} [CommRing k₀] [Algebra k₀ k]
variable {G : Type w} [Group G]
variable {W : Type u₁} [AddCommGroup W] [Module k₀ W]

/-- Scalar extension of a `k₀`-representation along `k₀ → k`. -/
noncomputable def scalarExtension (ρ : Representation k₀ G W) :
    Representation k G (k ⊗[k₀] W) :=
  MonoidHom.comp (Module.End.baseChangeHom k₀ k W).toMonoidHom ρ

end

section

variable {k : Type v} [Field k]
variable {k₀ : Type u₀} [Field k₀] [Algebra k₀ k]
variable {G : Type w} [Group G]
variable {W : Type u₁} [AddCommGroup W] [Module k₀ W]
variable {V : Type u} [AddCommGroup V] [Module k V]

/-- A representation over `k` is realizable over `k₀` if it is obtained, up to equivariant
base-change identification, from a finite-dimensional `k₀`-representation. -/
def IsRealizableOver (k₀ : Type u₀) [Field k₀] [Algebra k₀ k] (ρ : Representation k G V) : Prop :=
  ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module k₀ W) (_ : FiniteDimensional k₀ W)
    (ρ₀ : Representation k₀ G W), Nonempty ((Representation.scalarExtension ρ₀).Equiv ρ)

/-- A realizable representation has the character of a finite-dimensional `k₀`-representation
after applying the coefficientwise algebra map `k₀ → k`. This is the unbundled bridge companion
to `IsRealizableOver`: the primitive owner data is a finite-dimensional `k₀`-representation, and
packaging it into `FDRep` is a separate view. -/
theorem exists_character_eq_of_isRealizableOver
    {ρ : Representation k G V} [FiniteDimensional k V]
    (hρ : IsRealizableOver k₀ ρ) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module k₀ W) (_ : FiniteDimensional k₀ W)
      (ρ₀ : Representation k₀ G W),
      ρ.character = fun g ↦ algebraMap k₀ k (ρ₀.character g) := by
  rcases hρ with ⟨W, _instAddCommGroupW, _instModuleW, _instFiniteDimensionalW, ρ₀, hρ₀⟩
  rcases hρ₀ with ⟨e⟩
  refine ⟨W, inferInstance, inferInstance, inferInstance, ρ₀, ?_⟩
  ext g
  calc
    ρ.character g = (Representation.scalarExtension ρ₀).character g := by
      simpa using congrFun (Representation.char_iso e).symm g
    _ = algebraMap k₀ k (ρ₀.character g) := by
      exact LinearMap.trace_baseChange (ρ₀ g) k

end

section

variable {k : Type u} [Field k]
variable {k₀ : Type u} [Field k₀] [Algebra k₀ k]
variable {G : Type u} [Group G]

namespace FDRep

/-- The finite-dimensional `k`-representation obtained by scalar extension of a finite-dimensional
`k₀`-representation. This is the canonical bundled bridge/view of
`Representation.scalarExtension`. -/
abbrev scalarExtension (ρ : FDRep k₀ G) : FDRep k G :=
  FDRep.of (Representation.scalarExtension ρ.ρ)

end FDRep

end

end Representation
