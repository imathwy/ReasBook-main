import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_1

universe u v

open scoped Pointwise

namespace Set

/-- Bundled-cone bridge over the canonical unbundled owner `0⁺[R] C`.
This is kept as a downstream interoperability view. -/
def recessionConeCone {E : Type u} (C : Set E) (R : Type v) [Semiring R] [PartialOrder R]
    [PosMulMono R] [AddCommMonoid E] [Module R E] : ConvexCone R E where
  carrier := 0⁺[R] C
  smul_mem' := by
    intro c hc x hx
    exact (recessionCone_isCone (R := R) (E := E) C).smul_mem hc hx
  add_mem' := by
    intro y hy z hz
    rw [Set.mem_recessionCone_iff] at hy hz ⊢
    intro x hx a ha
    have hxy : x + a • y ∈ C := hy x hx a ha
    have hxyz : x + a • y + a • z ∈ C := hz (x + a • y) hxy a ha
    simpa [smul_add, add_assoc, add_left_comm, add_comm] using hxyz

@[simp] theorem mem_recessionConeCone_iff {R : Type v} [Semiring R] [PartialOrder R]
    [PosMulMono R] {E : Type u} [AddCommMonoid E] [Module R E] {C : Set E} {y : E} :
    y ∈ Set.recessionConeCone C R ↔ y ∈ 0⁺[R] C :=
  Iff.rfl

@[simp] theorem coe_recessionConeCone {R : Type v} [Semiring R] [PartialOrder R]
    [PosMulMono R] {E : Type u} [AddCommMonoid E] [Module R E] (C : Set E) :
    (Set.recessionConeCone C R : Set E) = 0⁺[R] C :=
  rfl

end Set
