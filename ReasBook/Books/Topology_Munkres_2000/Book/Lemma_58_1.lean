module

public import Topology_Munkres_2000.Book.Definition_52_5.Convention

public section

universe u v

namespace FundamentalGroup.LeftToRight

open unitInterval

/-- Helper for Lemma 58.1: the square obtained by evaluating a homotopy along a
path is continuous. -/
private lemma mappedLoopSquare_continuous {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {h k : C(X, Y)} {x₀ : X}
    (F : ContinuousMap.HomotopyRel h k {x₀}) (p : Path x₀ x₀) :
    Continuous (fun z : I × I ↦ F (z.1, p z.2)) := by
  -- Compose the continuous homotopy with the parameter-loop product map.
  fun_prop

/-- Helper for Lemma 58.1: the square obtained from a relative homotopy and a
loop is fixed on both vertical boundary edges. -/
private lemma mappedLoopSquare_fixed {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {h k : C(X, Y)} {x₀ : X}
    (F : ContinuousMap.HomotopyRel h k {x₀}) (p : Path x₀ x₀) :
    ∀ t s, s ∈ ({0, 1} : Set I) → F (t, p s) = h (p s) := by
  -- At either endpoint the loop is at `x₀`, where the homotopy is fixed.
  intro t s hs
  rcases hs with hs | hs
  · subst s
    calc
      F (t, p 0) = F (t, x₀) := congrArg (fun x ↦ F (t, x)) p.source
      _ = h x₀ := F.eq_fst t (Set.mem_singleton x₀)
      _ = h (p 0) := (congrArg h p.source).symm
  · rw [Set.mem_singleton_iff] at hs
    subst s
    calc
      F (t, p 1) = F (t, x₀) := congrArg (fun x ↦ F (t, x)) p.target
      _ = h x₀ := F.eq_fst t (Set.mem_singleton x₀)
      _ = h (p 1) := (congrArg h p.target).symm

/-- Helper for Lemma 58.1: a relative homotopy precomposed with a loop is a
path homotopy after aligning both mapped loops with the target basepoint. -/
private def mappedLoopHomotopyOfHomotopyRel {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {h k : C(X, Y)} {x₀ : X} {y₀ : Y}
    (h_basepoint : h x₀ = y₀) (k_basepoint : k x₀ = y₀)
    (F : ContinuousMap.HomotopyRel h k {x₀}) (p : Path x₀ x₀) :
    Path.Homotopy ((p.map h.continuous).cast h_basepoint.symm h_basepoint.symm)
      ((p.map k.continuous).cast k_basepoint.symm k_basepoint.symm) :=
  -- Assemble the path homotopy from the square's continuity and boundary interface.
  { toFun := fun z ↦ F (z.1, p z.2)
    continuous_toFun := mappedLoopSquare_continuous F p
    map_zero_left := fun t ↦ F.map_zero_left (p t)
    map_one_left := fun t ↦ F.map_one_left (p t)
    prop' := mappedLoopSquare_fixed F p }

/-- Helper for Lemma 58.1: homotopic pointed maps send every representative
loop to homotopic loops at the common target basepoint. -/
private lemma mappedLoopHomotopicOfHomotopicRel {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {h k : C(X, Y)} {x₀ : X} {y₀ : Y}
    (h_basepoint : h x₀ = y₀) (k_basepoint : k x₀ = y₀)
    (H : ContinuousMap.HomotopicRel h k {x₀}) (p : Path x₀ x₀) :
    Path.Homotopic ((p.map h.continuous).cast h_basepoint.symm h_basepoint.symm)
      ((p.map k.continuous).cast k_basepoint.symm k_basepoint.symm) := by
  -- Choose a concrete relative homotopy and package its loop square.
  obtain ⟨F⟩ := H
  exact ⟨mappedLoopHomotopyOfHomotopyRel h_basepoint k_basepoint F p⟩

/-- Helper for Lemma 58.1: homotopic pointed maps induce the same map-and-cast
operation on loop homotopy classes. -/
private lemma mappedLoopClass_eq_of_homotopicRel {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {h k : C(X, Y)} {x₀ : X} {y₀ : Y}
    (h_basepoint : h x₀ = y₀) (k_basepoint : k x₀ = y₀)
    (H : ContinuousMap.HomotopicRel h k {x₀})
    (p : Path.Homotopic.Quotient x₀ x₀) :
    (p.map h).cast h_basepoint.symm h_basepoint.symm =
      (p.map k).cast k_basepoint.symm k_basepoint.symm := by
  -- Descend the representative-level square through the path-homotopy quotient.
  induction p using Path.Homotopic.Quotient.ind with
  | mk path =>
      rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast,
        ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast]
      exact Path.Homotopic.Quotient.eq.mpr
        (mappedLoopHomotopicOfHomotopicRel h_basepoint k_basepoint H path)

/-- Lemma 58.1. Pointed continuous maps joined by a homotopy relative to the source
basepoint induce equal homomorphisms on fundamental groups. -/
theorem mapOfEq_eq_of_homotopicRel {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (h k : C(X, Y))
    (x₀ : X) (y₀ : Y) (h_basepoint : h x₀ = y₀)
    (H : ContinuousMap.HomotopicRel h k {x₀}) :
    mapOfEq h h_basepoint =
      mapOfEq k ((H.fst_eq_snd (Set.mem_singleton x₀)).symm.trans h_basepoint) := by
  -- The relative homotopy identifies the second map's value at the basepoint.
  let k_basepoint : k x₀ = y₀ :=
    (H.fst_eq_snd (Set.mem_singleton x₀)).symm.trans h_basepoint
  -- Evaluate both homomorphisms and compare their underlying loop classes.
  ext p
  rw [mapOfEq_apply, mapOfEq_apply]
  exact congrArg MulOpposite.op
    (mappedLoopClass_eq_of_homotopicRel h_basepoint k_basepoint H p.unop)

end FundamentalGroup.LeftToRight
