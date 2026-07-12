import Mathlib
import Mathlib.Tactic.Recall

open scoped ContDiff Manifold

-- Domain sampling pass:
-- * primary domain: smooth tangent-bundle frames and pointwise spanning/independence in tangent
--   spaces;
-- * inspected owner/API declarations: mathlib's `IsLocalFrameOn`, its `generating` field, and
--   the finite-dimensional span/independence lemmas
--   `LinearIndependent.span_eq_top_of_card_eq_finrank'` and
--   `linearIndependent_of_top_le_span_of_card_eq_finrank`;
-- * core/canonical owner: `IsLocalFrameOn`;
-- * source-facing layer in this file: pointwise linear independence and spanning for tuples of
--   vector fields, with the owner-style `⊤ ≤ span` formulation kept only as a bridge.

-- Semantic recall note: `lean_leansearch` was unavailable in this agent environment, so this item
-- was matched against mathlib's `IsLocalFrameOn` by local source inspection.

section

universe u𝕜 uE uH uM

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]

namespace VectorField

variable {k : ℕ}

/-- Definition 8.55-extra-1 (1): an ordered `k`-tuple of vector fields on `A ⊆ M` is linearly
independent if, at each `p ∈ A`, the values of the vector fields are linearly independent in the
tangent space `TangentSpace I p`. -/
def LinearlyIndependentOn (A : Set M)
    (X : Fin k → (p : M) → TangentSpace I p) : Prop :=
  ∀ p ∈ A, LinearIndependent 𝕜 (X · p)

/-- Pointwise characterization of `LinearlyIndependentOn`. -/
theorem linearlyIndependentOn_iff (A : Set M)
    (X : Fin k → (p : M) → TangentSpace I p) :
    LinearlyIndependentOn A X ↔
      ∀ p ∈ A, LinearIndependent 𝕜 (X · p) :=
  Iff.rfl

/-- Definition 8.55-extra-1 (2): an ordered `k`-tuple of vector fields on `A ⊆ M` spans the
tangent bundle if, at each `p ∈ A`, its values span the tangent space `TangentSpace I p`. -/
def SpansTangentBundleOn (A : Set M)
    (X : Fin k → (p : M) → TangentSpace I p) : Prop :=
  ∀ p ∈ A, Submodule.span 𝕜 (Set.range (X · p)) = ⊤

/-- Pointwise characterization of `SpansTangentBundleOn`. -/
theorem spansTangentBundleOn_iff (A : Set M)
    (X : Fin k → (p : M) → TangentSpace I p) :
    SpansTangentBundleOn A X ↔
      ∀ p ∈ A, Submodule.span 𝕜 (Set.range (X · p)) = ⊤ :=
  Iff.rfl

/-- Bridge from the source-facing span-equality formulation to the owner-style generating
condition `⊤ ≤ Submodule.span ...`. -/
theorem spansTangentBundleOn_iff_top_le_span (A : Set M)
    (X : Fin k → (p : M) → TangentSpace I p) :
    SpansTangentBundleOn A X ↔
      ∀ p ∈ A, ⊤ ≤ Submodule.span 𝕜 (Set.range (X · p)) := by
  constructor
  · intro h p hp
    exact (h p hp).ge
  · intro h p hp
    exact top_unique (h p hp)

section FiniteDimensional

variable [FiniteDimensional 𝕜 E]

/-- For a tuple indexed by `Fin (finrank 𝕜 E)`, pointwise linear independence forces pointwise
spanning in each tangent space. -/
theorem spansTangentBundleOn_of_linearlyIndependentOn
    {A : Set M} {e : Fin (Module.finrank 𝕜 E) → (p : M) → TangentSpace I p}
    (he : LinearlyIndependentOn A e) :
    SpansTangentBundleOn A e := by
  intro p hp
  letI : FiniteDimensional 𝕜 (TangentSpace I p) := by
    simpa [TangentSpace] using (inferInstance : FiniteDimensional 𝕜 E)
  have hcard : Fintype.card (Fin (Module.finrank 𝕜 E)) = Module.finrank 𝕜 (TangentSpace I p) := by
    have hcard' : Fintype.card (Fin (Module.finrank 𝕜 E)) = Module.finrank 𝕜 E :=
      Fintype.card_fin (Module.finrank 𝕜 E)
    simpa only [TangentSpace] using hcard'
  simpa using (he p hp).span_eq_top_of_card_eq_finrank' hcard

end FiniteDimensional

/-- For a tuple indexed by `Fin (finrank 𝕜 E)`, pointwise spanning forces pointwise linear
independence in each tangent space. -/
theorem linearlyIndependentOn_of_spansTangentBundleOn
    {A : Set M} {e : Fin (Module.finrank 𝕜 E) → (p : M) → TangentSpace I p}
    (he : SpansTangentBundleOn A e) :
    LinearlyIndependentOn A e := by
  intro p hp
  have hcard : Fintype.card (Fin (Module.finrank 𝕜 E)) = Module.finrank 𝕜 (TangentSpace I p) := by
    have hcard' : Fintype.card (Fin (Module.finrank 𝕜 E)) = Module.finrank 𝕜 E :=
      Fintype.card_fin (Module.finrank 𝕜 E)
    simpa only [TangentSpace] using hcard'
  exact linearIndependent_of_top_le_span_of_card_eq_finrank (he p hp).ge hcard

end VectorField

section LocalFrame

variable [FiniteDimensional 𝕜 E]
variable [IsManifold I ∞ M]
variable {e : Fin (Module.finrank 𝕜 E) → (p : M) → TangentSpace I p}
variable {U : Set M}

/-
Definition 8.55-extra-1 (3): the canonical owner for a smooth local frame on `U ⊆ M` is
`IsLocalFrameOn I E ∞ e U`.
-/
recall IsLocalFrameOn

/- Definition 8.55-extra-1 (4): a smooth global frame is the specialization of the same owner to
`U = Set.univ`. -/
#check (IsLocalFrameOn I E ∞ e Set.univ : Prop)

namespace IsLocalFrameOn

omit [FiniteDimensional 𝕜 E] in
/-- A smooth local frame yields the textbook pointwise linear independence condition. -/
theorem linearlyIndependentOn (he : IsLocalFrameOn I E ∞ e U) :
    VectorField.LinearlyIndependentOn U e := fun _ hp ↦ he.linearIndependent hp

omit [FiniteDimensional 𝕜 E] in
/-- A smooth local frame yields the textbook pointwise spanning condition. -/
theorem spansTangentBundleOn (he : IsLocalFrameOn I E ∞ e U) :
    VectorField.SpansTangentBundleOn U e :=
  (VectorField.spansTangentBundleOn_iff_top_le_span U e).2 fun _ hp ↦ he.generating hp

end IsLocalFrameOn

end LocalFrame

end
