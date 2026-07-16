import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_21_3_3
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_26_0_1
import ConvexAnalysis_Rockafellar_1970.Chap08.Proposition_39_0_2

-- Declarations for this item will be appended below by the statement pipeline.

open Bornology
open scoped Rockafellar SetRel

universe u v w

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 39.1 says that a convex process with full domain and bounded zero fiber
  `A0` is actually a linear transformation.
- `core/canonical`: convex processes in this chapter already live on the relation owner
  `A : SetRel U X` via `A.IsConvexProcess K`, while a single-valued linear transformation is
  canonically represented by the graph relation of a linear map `T : U →ₗ[K] X`.
- `bridge/view`: the source conditions `dom A = R^m` and boundedness of `A0` become
  `A.dom = Set.univ` and `IsBounded (A[[0]])`, and the conclusion “`A` is a linear
  transformation” becomes existence of a linear map whose graph equals `A`.

Primary mathematical domain:
- convex processes as graph relations in ordered normed scalar modules.

Domain-style sampling used here:
- `SetRel.IsConvexProcess` and its graph-closure API from `Chap08.Definition_39_0_1`;
- `SetRel.dom` and singleton-fiber notation `A[[u]]` for relation images from the chapter API;
- `Function.graph`, the canonical relation-level owner for single-valued maps;
- `LinearMap`, the bundled owner for linear transformations.

Primitive data vs derived API:
- primitive owner data: a relation `A : SetRel U X`;
- primitive source assumptions: convex-process structure, full domain, and bounded zero fiber;
- derived/source-facing conclusion: `A` is the graph of a linear map.

Layer target: `source-facing`, stated directly on the chapter's canonical relation owner and
bridged to the canonical graph of a bundled linear map.

Scalar-layer note:
- the source-facing owner is scalar-generic over an ordered normed field `K`, retaining only the
  assumptions needed by the boundedness-to-trivial-recession step.
-/

namespace SetRel.IsConvexProcess

section

variable {K : Type u} [NormedField K] [LinearOrder K] [IsStrictOrderedRing K]
variable {U : Type v} [AddCommGroup U] [Module K U]
variable {X : Type w} [NormedAddCommGroup X] [Module K X] [NormSMulClass K X]

namespace Set.IsConvexCone

/-- A nonempty bounded convex cone in a normed module is trivial. -/
theorem eq_singleton_zero_of_nonempty_isBounded
    {C : Set X} (hC : Set.IsConvexCone K C)
    (hC_nonempty : C.Nonempty) (hC_bounded : IsBounded C) :
    C = ({0} : Set X) := by
  have hC_recession : 0⁺[K] C = ({0} : Set X) :=
    recessionCone_eq_singleton_zero_of_nonempty_isBounded
      (C := C) hC_nonempty hC_bounded
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    have hx_recession : x ∈ 0⁺[K] C := by
      rw [Set.mem_recessionCone_iff]
      intro z hz a ha
      rcases eq_or_lt_of_le ha with rfl | ha_pos
      · simpa using hz
      · have hax : a • x ∈ C := hC.isCone.smul_mem ha_pos hx
        exact hC.add_mem hz hax
    have : x ∈ ({0} : Set X) := by simpa [hC_recession] using hx_recession
    simpa using this
  · intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    rcases hC_nonempty with ⟨z, hz⟩
    have h0 : 0 • z ∈ C := hC.isCone.smul_mem zero_lt_one hz
    simpa using h0

end Set.IsConvexCone

-- Proof sketch: boundedness of the zero fiber forces the convex cone `A[[0]]` to be
-- `{0}`. The convex-process identity `Au + A(-u) ⊆ A0` then makes every fiber a singleton and
-- gives `A(-u) = -A(u)`. Using full domain, pick the unique value in each fiber to define a map
-- `T : U → X`; the graph-cone axioms yield additivity and scalar homogeneity of `T`, so `A` is
-- exactly the graph of a linear map.
/-- For a convex process, boundedness of the zero fiber forces the zero fiber to be trivial. -/
theorem image_zero_eq_singleton_zero_of_isBounded
    {A : SetRel U X} (hA : A.IsConvexProcess K)
    (hA0_bounded : IsBounded (A[[0]])) :
    A[[0]] = ({0} : Set X) := by
  have hA0_nonempty : (A[[0]] : Set X).Nonempty := by
    refine ⟨0, ?_⟩
    simpa using hA.zero_mem_image_zero
  exact Set.IsConvexCone.eq_singleton_zero_of_nonempty_isBounded
    (hC := hA.isConvexCone_image_zero) hA0_nonempty hA0_bounded

/-- Theorem 39.1: if a convex process has full domain and bounded zero fiber
`A[[0]]`, then it is the graph of a linear transformation. -/
theorem exists_graph_eq_linearMap_of_dom_eq_univ_of_isBounded_image_zero
    {A : SetRel U X} (hA : A.IsConvexProcess K)
    (hdom : A.dom = Set.univ)
    (hA0_bounded : IsBounded (A[[0]])) :
    ∃ T : U →ₗ[K] X, Function.graph T = A := by
  let A0 : Set X := A[[0]]
  have hA0_singleton : A0 = ({0} : Set X) := by
    simpa [A0] using hA.image_zero_eq_singleton_zero_of_isBounded hA0_bounded
  have hdom_total : ∀ u : U, ∃ x : X, u ~[A] x := by
    intro u
    have hu : u ∈ A.dom := by
      rw [hdom]
      simp
    exact hu
  have hneg_mem : ∀ {u : U} {x : X}, u ~[A] x → (-u) ~[A] (-x) := by
    intro u x hux
    obtain ⟨y, hy⟩ := hdom_total (-u)
    have hxy_mem : x + y ∈ A0 := by
      refine ⟨0, by simp, ?_⟩
      simpa using hA.add_mem hux hy
    have hxy_zero : x + y = 0 := by
      have : x + y ∈ ({0} : Set X) := by simpa [hA0_singleton] using hxy_mem
      simpa using this
    have hy_eq : y = -x := eq_neg_iff_add_eq_zero.mpr (add_eq_zero_symm hxy_zero)
    simpa [hy_eq] using hy
  have hsingle : ∀ {u : U} {x₁ x₂ : X}, u ~[A] x₁ → u ~[A] x₂ → x₁ = x₂ := by
    intro u x₁ x₂ hx₁ hx₂
    have hx₂neg : (-u) ~[A] (-x₂) := hneg_mem hx₂
    have hsub_mem : x₁ - x₂ ∈ A0 := by
      refine ⟨0, by simp, ?_⟩
      simpa [sub_eq_add_neg] using hA.add_mem hx₁ hx₂neg
    have hsub_zero : x₁ - x₂ = 0 := by
      have : x₁ - x₂ ∈ ({0} : Set X) := by simpa [hA0_singleton] using hsub_mem
      simpa using this
    exact sub_eq_zero.mp hsub_zero
  have hfiber_unique : ∀ u : U, ∃! x : X, u ~[A] x := by
    intro u
    obtain ⟨x, hx⟩ := hdom_total u
    exact ⟨x, hx, fun y hy => (hsingle (u := u) (x₁ := x) (x₂ := y) hx hy).symm⟩
  obtain ⟨f, hf_graph, -⟩ := (SetRel.exists_graph_eq_iff A).2 hfiber_unique
  have hf_mem : ∀ u : U, u ~[A] f u := by
    intro u
    have : u ~[Function.graph f] f u := by simp [Function.mem_graph]
    simpa [hf_graph] using this
  have hf_neg : ∀ u : U, f (-u) = -f u := by
    intro u
    exact hsingle (hf_mem (-u)) (hneg_mem (hf_mem u))
  have hf_zero : f 0 = 0 := hsingle (hf_mem 0) hA.zero_mem
  have hf_add : ∀ u v : U, f (u + v) = f u + f v := by
    intro u v
    exact hsingle (hf_mem (u + v)) (hA.add_mem (hf_mem u) (hf_mem v))
  have hf_smul_pos : ∀ {a : K} (ha : 0 < a) (u : U), f (a • u) = a • f u := by
    intro a ha u
    exact hsingle (hf_mem (a • u)) (hA.smul_mem ha (hf_mem u))
  have hf_smul : ∀ (a : K) (u : U), f (a • u) = a • f u := by
    intro a u
    rcases lt_trichotomy a 0 with ha | rfl | ha
    · have hneg : 0 < -a := neg_pos.mpr ha
      calc
        f (a • u) = f ((-a) • (-u)) := by simp
        _ = (-a) • f (-u) := hf_smul_pos hneg (-u)
        _ = (-a) • (-f u) := by simp [hf_neg]
        _ = a • f u := by simp
    · simp [hf_zero]
    · exact hf_smul_pos ha u
  let T : U →ₗ[K] X :=
    { toFun := f
      map_add' := hf_add
      map_smul' := hf_smul }
  refine ⟨T, ?_⟩
  simpa [T] using hf_graph

end

end SetRel.IsConvexProcess
