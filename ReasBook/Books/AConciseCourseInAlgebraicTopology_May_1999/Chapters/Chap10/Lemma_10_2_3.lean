import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.CellularPushout
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_1_6

open Topology
open Topology.RelCWComplex

noncomputable section

universe u

section

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
variable [CWComplex (Set.univ : Set X)]
variable (A : CWComplex.Subcomplex (Set.univ : Set X)) (f : C(A, Y))

/-- The map of pairs `(A, ∅) ⟶ (Y, ∅)` induced by a continuous map from a subcomplex `A ⊆ X`
to `Y`, with both pairs represented by the Chapter 10 relative-pair owner. -/
def subcomplexMapPairHom :
    relativeSpacePair (A : Set X) (∅ : Set X) ⟶
      relativeSpacePair (Set.univ : Set Y) (∅ : Set Y) where
  hom :=
    TopCat.ofHom
      ⟨fun a ↦ ⟨f a, Set.mem_univ _⟩,
        f.continuous.subtype_mk fun _ ↦ Set.mem_univ _⟩
  map_subspace' := fun {_} hx ↦ False.elim hx

end

section

variable {X Y : Type u} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
variable [CWComplex (Set.univ : Set X)] (A : CWComplex.Subcomplex (Set.univ : Set X))
variable [CWComplex (Set.univ : Set Y)] (f : C(A, Y))

/-- Lemma 10.2.3. If `A` is a subcomplex of a CW complex `X`, `Y` is a CW complex, and
`f : A → Y` is cellular, formalized by `IsCellularMap (subcomplexMapPairHom A f)`, then the
adjunction space `Y ∪_f X`, formalized as `cellularPushout A f`, admits a CW structure containing
the copy of `Y` as a subcomplex and whose complementary `n`-cells are indexed by the `n`-cells of
`X` that do not belong to `A`. -/
theorem cellularPushout_hasCWComplexWithSubcomplexAndRelativeCells
    (hf : IsCellularMap (subcomplexMapPairHom A f)) :
    ∃ cw : CWComplex (Set.univ : Set (cellularPushout (A : Set X) f)),
      letI : CWComplex (Set.univ : Set (cellularPushout (A : Set X) f)) := cw
      ∃ B : CWComplex.Subcomplex (Set.univ : Set (cellularPushout (A : Set X) f)),
        (B : Set (cellularPushout (A : Set X) f)) =
          cellularPushoutLeftRange (A : Set X) f ∧
          ∀ n : ℕ,
            Nonempty
              ({j : cw.cell n // j ∉ (B.I n : Set (cw.cell n))} ≃
                {i : Topology.CWComplex.cell (Set.univ : Set X) n //
                  i ∉ (A.I n : Set (Topology.CWComplex.cell (Set.univ : Set X) n))}) := by
  sorry

/-- The adjunction space `Y ∪_f X` admits a CW structure for which the copy of `Y` is a
subcomplex. -/
theorem cellularPushout_hasCWComplexWithLeftSubcomplex
    (hf : IsCellularMap (subcomplexMapPairHom A f)) :
    ∃ cw : CWComplex (Set.univ : Set (cellularPushout (A : Set X) f)),
      letI : CWComplex (Set.univ : Set (cellularPushout (A : Set X) f)) := cw
      ∃ B : CWComplex.Subcomplex (Set.univ : Set (cellularPushout (A : Set X) f)),
        (B : Set (cellularPushout (A : Set X) f)) =
          cellularPushoutLeftRange (A : Set X) f := by
  sorry

/-- The adjunction space obtained by attaching `X` to `Y` along a cellular map from a subcomplex
is a CW complex. -/
theorem cellularPushout_isCWComplex
    (hf : IsCellularMap (subcomplexMapPairHom A f)) :
    Nonempty (CWComplex (Set.univ : Set (cellularPushout (A : Set X) f))) := by
  sorry

end
