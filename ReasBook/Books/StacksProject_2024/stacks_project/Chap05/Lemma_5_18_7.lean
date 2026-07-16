import StacksProject_2024.stacks_project.Chap05.FiniteUnionOfLocallyClosed
import StacksProject_2024.stacks_project.Chap05.Definition_5_18_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set TopologicalSpace Topology
open scoped Set.Notation
open scoped TopologicalSpace

section

variable {X : Type u} [TopologicalSpace X]

local macro "X₀" : term => `(closedPoints X)

section

variable [JacobsonSpace X]

/-
Domain-style sampling for closed-point traces of finite unions of locally closed subsets:
- primary domain: Jacobson spaces, closed points, and locally closed subset traces along subtype
  inclusions
- inspected owner-level declarations:
  `closedPoints`,
  `JacobsonSpace`,
  `jacobsonSpace_iff_locallyClosed`,
  `IsLocallyClosed.preimage`
- best owner abstraction: the ambient owner `JacobsonSpace X` together with the canonical closed
  point set `X₀`; the actual trace operation is the derived bridge/view
  `X₀ ↓∩ E`

Layer triage:
- `source-facing`: the finite-union closed-point trace correspondence in Lemma 5.18.7
- `core/canonical`: `JacobsonSpace X` and `X₀`
- `bridge/view`: the canonical subtype trace `X₀ ↓∩ E`

Primitive data is the ambient Jacobson owner and the chapter bridge predicate
`IsFiniteUnionOfLocallyClosed`. The trace map itself is derived API and should therefore use the
canonical subtype-trace surface directly, rather than a second local wrapper definition.
-/

-- Proof sketch: traces to the closed-point subtype preserve locally closed
-- subsets and finite unions; surjectivity follows by lifting finite unions of locally closed
-- subsets of `X₀` piecewise from open and closed subsets of `X₀`, while injectivity is the Stacks
-- argument using that every nonempty finite union of locally closed subsets of a Jacobson space
-- meets `X₀`.
/-- Lemma 5.18.7: for a Jacobson space `X`, tracing a subset to the closed-point subspace `X₀`
induces a bijection between finite unions of locally closed subsets of `X` and of `X₀`. -/
theorem finiteUnionOfLocallyClosed_preimage_closedPoints_bijOn :
    Set.BijOn (fun E : Set X ↦ X₀ ↓∩ E)
      {E : Set X | IsFiniteUnionOfLocallyClosed E}
      {F : Set X₀ | IsFiniteUnionOfLocallyClosed F} := sorry

-- Proof sketch: monotonicity of subtype trace gives the forward implication. For the converse, apply
-- injectivity from the bijection theorem to the finite unions of locally closed subsets `E \ E'`
-- and `∅`; if the traces satisfy inclusion, Jacobsonness forces `E \ E' = ∅`.
/-- The closed-point trace correspondence reflects and preserves inclusion on finite unions of
locally closed subsets. -/
theorem finiteUnionOfLocallyClosed_preimage_closedPoints_subset_iff
    {E E' : Set X} (hE : IsFiniteUnionOfLocallyClosed E) (hE' : IsFiniteUnionOfLocallyClosed E') :
    X₀ ↓∩ E ⊆ X₀ ↓∩ E' ↔ E ⊆ E' := sorry

-- Proof sketch: locally closed subsets are finite unions of locally closed subsets with one piece,
-- so the forward implication is by trace preservation. For the converse, use surjectivity of
-- the bijection to lift the locally closed trace to a locally closed subset of `X`, then apply the
-- inclusion-reflecting companion theorem in both directions to identify it with `E`.
/-- Within the closed-point trace correspondence of Lemma 5.18.7, finite unions of locally closed
subsets are locally closed exactly when their traces on `X₀` are locally closed. -/
theorem isLocallyClosed_iff_preimage_closedPoints_subtypeVal_of_isFiniteUnionOfLocallyClosed
    {E : Set X} (hE : IsFiniteUnionOfLocallyClosed E) :
    IsLocallyClosed E ↔ IsLocallyClosed (X₀ ↓∩ E) := sorry

-- Proof sketch: open subsets are locally closed, so the forward implication is by trace of an
-- open set. For the converse, lift the open trace to an open subset of `X` via the bijection and
-- use the inclusion-preserving correspondence to show that this lift equals `E`.
/-- Within the closed-point trace correspondence of Lemma 5.18.7, finite unions of locally closed
subsets are open exactly when their traces on `X₀` are open. -/
theorem isOpen_iff_preimage_closedPoints_subtypeVal_of_isFiniteUnionOfLocallyClosed
    {E : Set X} (hE : IsFiniteUnionOfLocallyClosed E) :
    IsOpen E ↔ IsOpen (X₀ ↓∩ E) := sorry

-- Proof sketch: closed subsets are locally closed, so the forward implication is by trace of a
-- closed set. For the converse, lift the closed trace to a closed subset of `X` via the bijection
-- and again identify that lift with `E` using inclusion reflection.
/-- Within the closed-point trace correspondence of Lemma 5.18.7, finite unions of locally closed
subsets are closed exactly when their traces on `X₀` are closed. -/
theorem isClosed_iff_preimage_closedPoints_subtypeVal_of_isFiniteUnionOfLocallyClosed
    {E : Set X} (hE : IsFiniteUnionOfLocallyClosed E) :
    IsClosed E ↔ IsClosed (X₀ ↓∩ E) := sorry

end

end
