module

public import Mathlib.Topology.TietzeExtension

public section

universe u

/-- Helper for Exercise 35.1: inside the union of two disjoint closed sets, the
part lying over the left set is clopen. -/
private lemma isClopen_preimage_left_of_disjoint_closed {X : Type u} [TopologicalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
    IsClopen {x : (A ∪ B : Set X) | (x : X) ∈ A} := by
  -- Closedness is inherited from `A` by the subtype projection.
  constructor
  · exact hA.preimage continuous_subtype_val
  -- The complementary side is exactly the preimage of `B`, hence is closed.
  rw [← isClosed_compl_iff]
  have hcomplement :
      {x : (A ∪ B : Set X) | (x : X) ∈ A}ᶜ =
        {x : (A ∪ B : Set X) | (x : X) ∈ B} := by
    ext x
    constructor
    · intro hx
      rcases x.property with hxA | hxB
      · exact False.elim (hx hxA)
      · exact hxB
    · intro hxB hxA
      exact Set.disjoint_left.mp hAB hxA hxB
  rw [hcomplement]
  exact hB.preimage continuous_subtype_val

/-- Helper for Exercise 35.1: two disjoint closed sets admit a continuous
endpoint-valued map on their union. -/
private lemma exists_continuousMap_union_eq_endpoints {X : Type u} [TopologicalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B)
    {a b : ℝ} (hab : a ≤ b) :
    ∃ f : C((A ∪ B : Set X), Set.Icc a b),
      (∀ x : (A ∪ B : Set X), (x : X) ∈ A → (f x : ℝ) = a) ∧
        ∀ x : (A ∪ B : Set X), (x : X) ∈ B → (f x : ℝ) = b := by
  classical
  let leftSide : Set (A ∪ B : Set X) := {x | (x : X) ∈ A}
  have hleftSide : IsClopen leftSide :=
    isClopen_preimage_left_of_disjoint_closed hA hB hAB
  let leftEndpoint : Set.Icc a b := ⟨a, Set.left_mem_Icc.mpr hab⟩
  let rightEndpoint : Set.Icc a b := ⟨b, Set.right_mem_Icc.mpr hab⟩
  have hfrontier : ∀ x ∈ frontier leftSide,
      (fun _ : (A ∪ B : Set X) ↦ leftEndpoint) x =
        (fun _ : (A ∪ B : Set X) ↦ rightEndpoint) x := by
    intro x hx
    rw [hleftSide.frontier_eq] at hx
    exact False.elim hx
  have hcontinuous : Continuous
      (leftSide.piecewise (fun _ ↦ leftEndpoint) (fun _ ↦ rightEndpoint)) := by
    exact continuous_const.piecewise hfrontier continuous_const
  let f : C((A ∪ B : Set X), Set.Icc a b) :=
    ⟨leftSide.piecewise (fun _ ↦ leftEndpoint) (fun _ ↦ rightEndpoint), hcontinuous⟩
  -- On the left side, the piecewise map selects the left endpoint.
  refine ⟨f, ?_, ?_⟩
  · intro x hxA
    have hpiece : f x = leftEndpoint := by
      exact Set.piecewise_eq_of_mem leftSide (fun _ ↦ leftEndpoint)
        (fun _ ↦ rightEndpoint) hxA
    simpa only [leftEndpoint] using congrArg Subtype.val hpiece
  -- Membership in `B` excludes membership in `A`, so the right branch is selected.
  · intro x hxB
    have hxA : (x : X) ∉ A := by
      intro hxA
      exact Set.disjoint_left.mp hAB hxA hxB
    have hpiece : f x = rightEndpoint := by
      exact Set.piecewise_eq_of_notMem leftSide (fun _ ↦ leftEndpoint)
        (fun _ ↦ rightEndpoint) hxA
    simpa only [rightEndpoint] using congrArg Subtype.val hpiece

/-- Helper for Exercise 35.1: endpoint equations on a closed union pass from a
restricted continuous map to its extension. -/
private lemma extension_eq_endpoints_of_restrict_eq {X : Type u} [TopologicalSpace X]
    {A B : Set X} {a b : ℝ} (f : C((A ∪ B : Set X), Set.Icc a b))
    (hfA : ∀ x : (A ∪ B : Set X), (x : X) ∈ A → (f x : ℝ) = a)
    (hfB : ∀ x : (A ∪ B : Set X), (x : X) ∈ B → (f x : ℝ) = b)
    (g : C(X, Set.Icc a b)) (hgf : ContinuousMap.restrict (A ∪ B) g = f) :
    (∀ x ∈ A, (g x : ℝ) = a) ∧ ∀ x ∈ B, (g x : ℝ) = b := by
  constructor
  · intro x hxA
    have hxUnion : x ∈ A ∪ B := Or.inl hxA
    have heval := DFunLike.congr_fun hgf ⟨x, hxUnion⟩
    -- Evaluating the restriction equality identifies the extension with `f` on `A`.
    calc
      (g x : ℝ) = (f ⟨x, hxUnion⟩ : ℝ) := congrArg Subtype.val heval
      _ = a := hfA ⟨x, hxUnion⟩ hxA
  · intro x hxB
    have hxUnion : x ∈ A ∪ B := Or.inr hxB
    have heval := DFunLike.congr_fun hgf ⟨x, hxUnion⟩
    -- The same restriction calculation gives the prescribed value on `B`.
    calc
      (g x : ℝ) = (f ⟨x, hxUnion⟩ : ℝ) := congrArg Subtype.val heval
      _ = b := hfB ⟨x, hxUnion⟩ hxB

/-- Exercise 35.1. The interval-valued Tietze extension theorem implies the Urysohn lemma. -/
theorem tietzeExtension_implies_urysohn {X : Type u} [TopologicalSpace X]
    (hTietze : ∀ {S : Set X} (hS : IsClosed S) {a b : ℝ} (hab : a ≤ b)
      (f : C(S, Set.Icc a b)),
        ∃ g : C(X, Set.Icc a b), ContinuousMap.restrict S g = f)
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B)
    {a b : ℝ} (hab : a ≤ b) :
    ∃ g : C(X, Set.Icc a b),
      (∀ x ∈ A, (g x : ℝ) = a) ∧ ∀ x ∈ B, (g x : ℝ) = b := by
  -- Prescribe the two endpoint values continuously on the closed union.
  obtain ⟨f, hfA, hfB⟩ :=
    exists_continuousMap_union_eq_endpoints hA hB hAB hab
  -- Tietze extends this map, and the restriction equation preserves its specifications.
  obtain ⟨g, hgf⟩ := hTietze (hA.union hB) hab f
  exact ⟨g, extension_eq_endpoints_of_restrict_eq f hfA hfB g hgf⟩

end
