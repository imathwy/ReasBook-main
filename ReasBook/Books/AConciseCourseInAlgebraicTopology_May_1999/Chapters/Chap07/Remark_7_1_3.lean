import Mathlib.Tactic.Recall
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_1_2

universe u v w

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

-- Semantic recall via `lean_leansearch`: the current environment exposes covering-homotopy
-- lifting for `IsCoveringMap`, but no separate topological `HurewiczFibration` or
-- `SerreFibration` owner. The source-faithful notion for this section is therefore the local
-- class `IsFibration p`, whose lifting field quantifies over arbitrary test spaces `A`.

/- Remark 7.1.3: the fibration notion used here is the Hurewicz fibration notion from
`Definition 7.1.2`. In this file, that notion is formalized by `IsFibration p`, whose
`homotopyLift` field quantifies over every topological test space `A`. A Serre fibration would
restrict the lifting test spaces to cubes `I^n`; no separate Serre-fibration owner is introduced
or used in this discussion. -/
recall IsFibration (p : C(E, B)) : Prop

/- The lifting clause is quantified over an arbitrary topological test space `A`. -/
recall IsFibration.exists_homotopyLift {p : C(E, B)} [IsFibration p] {A : Type w}
    [TopologicalSpace A] [CompactlyGeneratedWeakHausdorffSpace A]
    {f₀ f₁ : C(A, B)} (H : f₀.Homotopy f₁) {g₀ : C(A, E)}
    (hg₀ : p.comp g₀ = f₀) :
    ∃ g₁ : C(A, E), ∃ G : g₀.Homotopy g₁, p.comp G.toContinuousMap = H.toContinuousMap
