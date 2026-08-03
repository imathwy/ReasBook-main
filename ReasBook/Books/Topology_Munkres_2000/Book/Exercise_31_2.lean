module

public import Mathlib.Topology.Separation.Regular

public section

universe u

/-- Exercise 31.2: If `X` is normal, then every pair of disjoint closed sets has
open neighborhoods whose closures are disjoint. -/
theorem exists_open_supersets_disjoint_closures {X : Type u} [TopologicalSpace X]
    [NormalSpace X] {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hAB : Disjoint A B) :
    ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ A ⊆ U ∧ B ⊆ V ∧
      Disjoint (closure U) (closure V) := by
  -- First separate the two closed sets by disjoint open supersets.
  obtain ⟨O, P, hO, hP, hAO, hBP, hOP⟩ := normal_separation hA hB hAB
  -- Shrink each closed set so that the new neighborhood's closure stays inside its separator.
  obtain ⟨U, hU, hAU, hUO⟩ := normal_exists_closure_subset hA hO hAO
  obtain ⟨V, hV, hBV, hVP⟩ := normal_exists_closure_subset hB hP hBP
  -- Restrict the disjointness of the separators along the two closure inclusions.
  exact ⟨U, V, hU, hV, hAU, hBV, hOP.mono hUO hVP⟩
