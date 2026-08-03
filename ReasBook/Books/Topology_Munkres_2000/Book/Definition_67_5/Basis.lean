module

public import Mathlib.LinearAlgebra.Basis.Basic

public section

universe u v w

namespace Module

variable {R : Type w} [Semiring R] {M : Type u} [AddCommMonoid M] [Module R M]
variable {ι : Type v}

/-- An indexed family is a basis when it is linearly independent and spans the module. -/
def IsBasis (R : Type w) [Semiring R] [Module R M] (a : ι → M) : Prop :=
  LinearIndependent R a ∧ Submodule.span R (Set.range a) = ⊤

/-- A bundled basis is a basis as an indexed family. -/
theorem Basis.isBasis (b : Basis ι R M) : IsBasis R (b : ι → M) :=
  ⟨b.linearIndependent, b.span_eq⟩

/-- An indexed family is a basis exactly when it is linearly independent and spans. -/
theorem isBasis_iff (a : ι → M) :
    IsBasis R a ↔ LinearIndependent R a ∧ Submodule.span R (Set.range a) = ⊤ :=
  Iff.rfl

/-- The bundled basis determined by a family satisfying `Module.IsBasis`. -/
noncomputable def IsBasis.toBasis {a : ι → M} (h : IsBasis R a) : Basis ι R M :=
  Basis.mk h.1 h.2.ge

@[simp]
theorem IsBasis.coe_toBasis {a : ι → M} (h : IsBasis R a) :
    (h.toBasis : ι → M) = a :=
  Basis.coe_mk _ _

end Module
