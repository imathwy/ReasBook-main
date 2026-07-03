import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_7_1 (from Chap05) -/
universe u

open Set

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for connectedness in topological spaces:
- primary domain: connected spaces and connected components in point-set topology;
- owner abstractions: `ConnectedSpace`, `connectedComponent`;
- same-domain declarations inspected:
  `ConnectedSpace`,
  `connectedSpace_iff_clopen`,
  `connectedComponent`,
  `IsConnected.subset_connectedComponent`.

Layer triage:
- `source-facing`: the textbook criterion for connected spaces and the characterization of
  connected components as maximal connected subsets;
- `core/canonical`: `ConnectedSpace` and `connectedComponent`;
- `bridge/view`: `connectedSpace_iff_clopen` for clause `(1)`, and the maximality theorem below for
  clause `(2)`.

Primitive data belongs only to the owner declarations `ConnectedSpace` and `connectedComponent`.
The maximality clause is derived API from `connectedComponent`, but there is no exact upstream
theorem with the source-facing `Maximal IsConnected` interface, so the right refinement is a thin
bridge theorem rather than a second owner or a compatibility wrapper. -/

/- Canonical recall: the Stacks notion that a topological space is connected is the canonical
mathlib class `ConnectedSpace`. -/
recall ConnectedSpace

/- Definition 5.7.1: a topological space is connected if and only if it is nonempty and its
only clopen subsets are `∅` and `univ`. This is exactly the canonical theorem
`connectedSpace_iff_clopen`. -/
recall connectedSpace_iff_clopen

/- Canonical recall: the connected component through a point is the canonical mathlib set
`connectedComponent x`. -/
recall connectedComponent

/-
The maximality criterion for connected components is source-facing rather than a bare recall:
mathlib owns connected
components through `connectedComponent`, while the Stacks phrasing uses maximal connected subsets.
The theorem below is the minimal bridge from that source wording to the canonical owner.
-/
/-- A subset of `X` is a connected component if and only if it is a maximal
connected subset, equivalently one of the canonical sets `connectedComponent x`. This is the
source-facing bridge from the textbook maximality criterion to mathlib's owner `connectedComponent`.
-/
theorem maximal_isConnected_iff_eq_connectedComponent (T : Set X) :
    Maximal IsConnected T ↔ ∃ x : X, T = connectedComponent x := by
  constructor
  · intro hT
    obtain ⟨x, hx⟩ := hT.prop.nonempty
    exact ⟨x, hT.eq_of_subset isConnected_connectedComponent (hT.prop.subset_connectedComponent hx)⟩
  · rintro ⟨x, rfl⟩
    exact ⟨isConnected_connectedComponent,
      fun S hS hsubset ↦ hS.subset_connectedComponent (hsubset mem_connectedComponent)⟩

/-! ### Lemma_5_7_2 (from Chap05) -/
universe u v

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/- Domain-style sampling for connectedness under continuous images:
- primary domain: connected subsets of topological spaces
- sampled same-domain declarations:
  `ConnectedSpace`,
  `connectedComponent`,
  `IsConnected.image`,
  `IsConnected.closure`
- best owner abstraction for this item: `IsConnected.image`
- primitive data: a connected subset `s` and a map continuous on `s`
- derived API: the textbook specialization where the map is globally continuous

Layer triage:
- `source-facing`: the image of a connected subset under a continuous map is connected
- `core/canonical`: `IsConnected.image`
- `bridge/view`: `Continuous f` specialized to `hf.continuousOn`

This item is not a second owner theorem; it is the source-facing global-continuity bridge to the
canonical theorem `IsConnected.image`.
-/

/-- Lemma 5.7.2: the image of a connected subset under a continuous map is connected.

This is the textbook global-continuity specialization of the canonical theorem
`IsConnected.image`. -/
theorem isConnected_image {s : Set X} (hs : IsConnected s) {f : X → Y} (hf : Continuous f) :
    IsConnected (f '' s) :=
  hs.image f hf.continuousOn

end

/-! ### Lemma_5_7_3 (from Chap05) -/
universe u

open Set

variable {X : Type u} [TopologicalSpace X]

/- Domain sampling / owner triage for Lemma 5.7.3:
- primary domain: connected subsets and connected components of a topological space
- core/canonical owner: `connectedComponent`
- sampled supporting declarations: `IsConnected.closure`, `isClosed_connectedComponent`,
  `IsConnected.subset_connectedComponent`, `connectedComponent_eq`
- project bridge reused below: `maximal_isConnected_iff_eq_connectedComponent`
- primitive data: the canonical subset `connectedComponent x`
- derived/source-facing API: uniqueness of the connected component containing a connected subset or
  a point, expressed via the chapter bridge `Maximal IsConnected`
-/

/- Lemma 5.7.3 (1): the closure of a connected subset of a topological space is connected.
This is exactly the canonical theorem `IsConnected.closure`. -/
recall IsConnected.closure

/- Lemma 5.7.3 (2): every connected component of a topological space is closed.
This is exactly the canonical theorem `isClosed_connectedComponent`. -/
recall isClosed_connectedComponent

-- Proof sketch: choose `x ∈ T`; then `T ⊆ connectedComponent x` by
-- `IsConnected.subset_connectedComponent`. Any other maximal connected superset is some
-- `connectedComponent y` by `maximal_isConnected_iff_eq_connectedComponent`, and containing `x`
-- forces `connectedComponent y = connectedComponent x` by `connectedComponent_eq`.
/-- Lemma 5.7.3 (1): every connected subset of `X` is contained in a unique connected component of
`X`. -/
theorem existsUnique_connectedComponent_superset_of_isConnected {T : Set X}
    (hT : IsConnected T) :
    ∃! C : Set X, Maximal IsConnected C ∧ T ⊆ C := by
  obtain ⟨x, hx⟩ := hT.nonempty
  refine ⟨connectedComponent x, ?_, ?_⟩
  · exact ⟨(maximal_isConnected_iff_eq_connectedComponent _).2 ⟨x, rfl⟩,
      hT.subset_connectedComponent hx⟩
  · intro C hC
    rcases (maximal_isConnected_iff_eq_connectedComponent C).1 hC.1 with ⟨y, rfl⟩
    exact connectedComponent_eq (hC.2 hx)

-- Proof sketch: apply the previous clause to the singleton `{x}`, which is connected.
/-- Lemma 5.7.3 (2): every point of `X` lies in a unique connected component of `X`, so `X` is the
disjoint union of its connected components. -/
theorem existsUnique_connectedComponent_through_point (x : X) :
    ∃! C : Set X, Maximal IsConnected C ∧ x ∈ C := by
  have hx : IsConnected ({x} : Set X) := isConnected_singleton
  simpa [singleton_subset_iff] using
    existsUnique_connectedComponent_superset_of_isConnected hx

/-! ### Remark_5_7_4 (from Chap05) -/
universe u

open Set

namespace ConnectedComponentClopenCounterexample

/- Domain-style sampling:
- primary domain: point-set topology, specifically connected components and clopen neighborhoods;
- same-domain declarations inspected:
  `maximal_isConnected_iff_eq_connectedComponent`,
  `connectedComponent`,
  `IsClopen.connectedComponent_subset`,
  `connectedComponent_subset_iInter_isClopen`,
  `connectedComponent_eq_iInter_isClopen`;
- best owner abstraction: the canonical owner `connectedComponent x`, with clopen neighborhoods
  expressed through `IsClopen` and the owner theorem
  `connectedComponent_subset_iInter_isClopen`;
- core/canonical: `connectedComponent x`, `IsClopen`, and
  `connectedComponent_subset_iInter_isClopen`;
- source-facing: the explicit Stacks counterexample space from Remark 5.7.4, together with
  the two concrete set computations showing the canonical inclusion can be strict;
- bridge/view layer: the final strict-inclusion theorem is obtained by comparing the source-facing
  computations with the canonical owner theorem above, so no separate local wrapper around that
  owner API is introduced here.

The only primitive data that belongs in this file is the point set and its generated topology; the
connected-component/clopen interface itself is already owned upstream by mathlib. -/

/-- The points of the Stacks counterexample space from Remark 5.7.4. -/
inductive Point where
  | x
  | y
  | z (n : ℕ)
deriving DecidableEq

open Point

/-- The singleton basic open containing only `z n`. -/
private def zSingleton (n : ℕ) : Set Point := {z n}

/-- The tail of all points `z m` with `m ≥ n`. -/
private def zTail (n : ℕ) : Set Point := range fun m ↦ z (n + m)

/-- The basic open `{x, z_n, z_{n + 1}, ...}` from the counterexample topology. -/
private def xTail (n : ℕ) : Set Point := insert x (zTail n)

/-- The basic open `{y, z_n, z_{n + 1}, ...}` from the counterexample topology. -/
private def yTail (n : ℕ) : Set Point := insert y (zTail n)

/-- The canonical topology on the counterexample point set. -/
instance : TopologicalSpace Point :=
  TopologicalSpace.generateFrom
    (range zSingleton ∪ range xTail ∪ range yTail)

/- Canonical owner recall: in any topological space, the connected component of a point is
contained in the intersection of all clopen neighborhoods of that point. This file only supplies a
counterexample showing that the inclusion can be strict. -/
recall connectedComponent_subset_iInter_isClopen {α : Type u} [TopologicalSpace α] {point : α} :
    connectedComponent point ⊆ ⋂ Z : { Z : Set α // IsClopen Z ∧ point ∈ Z }, Z

/-- Helper for Remark 5.7.4: a point `z m` lies in the tail starting at `n` exactly when `n ≤ m`. -/
@[simp] private lemma mem_zTail_iff {m n : ℕ} : z m ∈ zTail n ↔ n ≤ m := by
  constructor
  · rintro ⟨k, hk⟩
    injection hk with hkm
    simpa [hkm] using Nat.le_add_right n k
  · intro h
    rcases Nat.exists_eq_add_of_le h with ⟨k, rfl⟩
    exact ⟨k, rfl⟩

/-- Helper for Remark 5.7.4: later `z`-tails are contained in earlier ones. -/
private lemma zTail_mono {m n : ℕ} (h : m ≤ n) : zTail n ⊆ zTail m := by
  intro p hp
  cases p with
  | x =>
      simp [zTail] at hp
  | y =>
      simp [zTail] at hp
  | z k =>
      rw [mem_zTail_iff] at hp ⊢
      exact h.trans hp

/-- Helper for Remark 5.7.4: later `x`-tails are contained in earlier ones. -/
private lemma xTail_mono {m n : ℕ} (h : m ≤ n) : xTail n ⊆ xTail m := by
  intro p hp
  simp only [xTail, mem_insert_iff] at hp ⊢
  rcases hp with rfl | hp
  · exact Or.inl rfl
  · exact Or.inr (zTail_mono h hp)

/-- Helper for Remark 5.7.4: later `y`-tails are contained in earlier ones. -/
private lemma yTail_mono {m n : ℕ} (h : m ≤ n) : yTail n ⊆ yTail m := by
  intro p hp
  simp only [yTail, mem_insert_iff] at hp ⊢
  rcases hp with rfl | hp
  · exact Or.inl rfl
  · exact Or.inr (zTail_mono h hp)

/-- Helper for Remark 5.7.4: each basic `x`-tail is open in the generated topology. -/
private lemma xTail_isOpen (n : ℕ) : IsOpen (xTail n) := by
  change TopologicalSpace.GenerateOpen (range zSingleton ∪ range xTail ∪ range yTail) (xTail n)
  exact TopologicalSpace.GenerateOpen.basic _ (Or.inl (Or.inr ⟨n, rfl⟩))

/-- Helper for Remark 5.7.4: each basic `y`-tail is open in the generated topology. -/
private lemma yTail_isOpen (n : ℕ) : IsOpen (yTail n) := by
  change TopologicalSpace.GenerateOpen (range zSingleton ∪ range xTail ∪ range yTail) (yTail n)
  exact TopologicalSpace.GenerateOpen.basic _ (Or.inr ⟨n, rfl⟩)

/-- Helper for Remark 5.7.4: each singleton `{z n}` is one of the generating opens. -/
private lemma zSingleton_isOpen (n : ℕ) : IsOpen (zSingleton n) := by
  change TopologicalSpace.GenerateOpen (range zSingleton ∪ range xTail ∪ range yTail)
    (zSingleton n)
  exact TopologicalSpace.GenerateOpen.basic _ (Or.inl (Or.inl ⟨n, rfl⟩))

/-- Helper for Remark 5.7.4: the tail `xTail (n + 1)` avoids the isolated point `z n`. -/
private lemma xTail_succ_subset_zSingleton_compl (n : ℕ) :
    xTail (n + 1) ⊆ (zSingleton n)ᶜ := by
  intro p hp
  cases p with
  | x =>
      simp [zSingleton]
  | y =>
      simp [xTail, zTail] at hp
  | z m =>
      have hm : n + 1 ≤ m := by
        simpa [xTail, mem_zTail_iff] using hp
      simp [zSingleton, Nat.ne_of_gt (lt_of_lt_of_le (Nat.lt_succ_self n) hm)]

/-- Helper for Remark 5.7.4: the tail `yTail (n + 1)` avoids the isolated point `z n`. -/
private lemma yTail_succ_subset_zSingleton_compl (n : ℕ) :
    yTail (n + 1) ⊆ (zSingleton n)ᶜ := by
  intro p hp
  cases p with
  | x =>
      simp [yTail, zTail] at hp
  | y =>
      simp [zSingleton]
  | z m =>
      have hm : n + 1 ≤ m := by
        simpa [yTail, mem_zTail_iff] using hp
      simp [zSingleton, Nat.ne_of_gt (lt_of_lt_of_le (Nat.lt_succ_self n) hm)]

/-- Helper for Remark 5.7.4: a different isolated point stays in the complement of `{z n}`. -/
private lemma zSingleton_subset_zSingleton_compl {m n : ℕ} (h : m ≠ n) :
    zSingleton m ⊆ (zSingleton n)ᶜ := by
  intro p hp
  simp [zSingleton] at hp ⊢
  simpa [hp] using h

/-- Helper for Remark 5.7.4: any open neighborhood of `x` contains one of the basic `x`-tails. -/
private lemma xTail_subset_of_isOpen_of_mem {U : Set Point} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ n : ℕ, xTail n ⊆ U := by
  -- The generated topology can only reach `x` through an `x`-tail, and this persists under
  -- finite intersections and arbitrary unions.
  change TopologicalSpace.GenerateOpen (range zSingleton ∪ range xTail ∪ range yTail) U at hU
  let P : Set Point → Prop := fun V => x ∈ V → ∃ n : ℕ, xTail n ⊆ V
  have hP : ∀ {V : Set Point},
      TopologicalSpace.GenerateOpen (range zSingleton ∪ range xTail ∪ range yTail) V → P V := by
    intro V hV
    induction hV with
    | basic s hs =>
        intro hxS
        rcases hs with hs | hs
        · rcases hs with hs | hs
          · rcases hs with ⟨n, rfl⟩
            simp [zSingleton] at hxS
          · rcases hs with ⟨n, rfl⟩
            exact ⟨n, Subset.rfl⟩
        · rcases hs with ⟨n, rfl⟩
          simp [yTail, zTail] at hxS
    | univ =>
        intro _
        exact ⟨0, subset_univ _⟩
    | inter s t hs ht ihs iht =>
        intro hxST
        rcases ihs hxST.1 with ⟨m, hm⟩
        rcases iht hxST.2 with ⟨n, hn⟩
        refine ⟨max m n, ?_⟩
        intro p hp
        exact ⟨hm (xTail_mono (Nat.le_max_left _ _) hp), hn (xTail_mono (Nat.le_max_right _ _) hp)⟩
    | sUnion S hS ih =>
        intro hxS
        rcases hxS with ⟨V, hV, hxV⟩
        rcases ih V hV hxV with ⟨n, hn⟩
        exact ⟨n, Subset.trans hn (subset_sUnion_of_mem hV)⟩
  exact hP hU hxU

/-- Helper for Remark 5.7.4: any open neighborhood of `y` contains one of the basic `y`-tails. -/
private lemma yTail_subset_of_isOpen_of_mem {U : Set Point} (hU : IsOpen U) (hyU : y ∈ U) :
    ∃ n : ℕ, yTail n ⊆ U := by
  -- This is the symmetric neighborhood-basis statement at `y`.
  change TopologicalSpace.GenerateOpen (range zSingleton ∪ range xTail ∪ range yTail) U at hU
  let P : Set Point → Prop := fun V => y ∈ V → ∃ n : ℕ, yTail n ⊆ V
  have hP : ∀ {V : Set Point},
      TopologicalSpace.GenerateOpen (range zSingleton ∪ range xTail ∪ range yTail) V → P V := by
    intro V hV
    induction hV with
    | basic s hs =>
        intro hyS
        rcases hs with hs | hs
        · rcases hs with hs | hs
          · rcases hs with ⟨n, rfl⟩
            simp [zSingleton] at hyS
          · rcases hs with ⟨n, rfl⟩
            simp [xTail, zTail] at hyS
        · rcases hs with ⟨n, rfl⟩
          exact ⟨n, Subset.rfl⟩
    | univ =>
        intro _
        exact ⟨0, subset_univ _⟩
    | inter s t hs ht ihs iht =>
        intro hyST
        rcases ihs hyST.1 with ⟨m, hm⟩
        rcases iht hyST.2 with ⟨n, hn⟩
        refine ⟨max m n, ?_⟩
        intro p hp
        exact ⟨hm (yTail_mono (Nat.le_max_left _ _) hp), hn (yTail_mono (Nat.le_max_right _ _) hp)⟩
    | sUnion S hS ih =>
        intro hyS
        rcases hyS with ⟨V, hV, hyV⟩
        rcases ih V hV hyV with ⟨n, hn⟩
        exact ⟨n, Subset.trans hn (subset_sUnion_of_mem hV)⟩
  exact hP hU hyU

/-- Helper for Remark 5.7.4: each isolated point `z n` is clopen. -/
private lemma zSingleton_isClopen (n : ℕ) : IsClopen (zSingleton n) := by
  refine ⟨?_, zSingleton_isOpen n⟩
  -- Every point outside `{z n}` has a basic neighborhood still avoiding `z n`.
  rw [← isOpen_compl_iff]
  refine isOpen_iff_mem_nhds.2 ?_
  intro p hp
  cases p with
  | x =>
      refine mem_nhds_iff.mpr ⟨xTail (n + 1), xTail_succ_subset_zSingleton_compl n,
        xTail_isOpen (n + 1), ?_⟩
      simp [xTail]
  | y =>
      refine mem_nhds_iff.mpr ⟨yTail (n + 1), yTail_succ_subset_zSingleton_compl n,
        yTail_isOpen (n + 1), ?_⟩
      simp [yTail]
  | z m =>
      have hm : m ≠ n := by
        simpa [zSingleton] using hp
      refine mem_nhds_iff.mpr ⟨zSingleton m, zSingleton_subset_zSingleton_compl hm,
        zSingleton_isOpen m, ?_⟩
      simp [zSingleton]

/-- Helper for Remark 5.7.4: every clopen neighborhood of `x` also contains `y`. -/
private lemma clopen_neighborhood_of_x_contains_y {Z : Set Point} (hZ : IsClopen Z) (hxZ : x ∈ Z) :
    y ∈ Z := by
  -- The tail basis at `x` and `y` forces every clopen neighborhood of `x` to overlap every open
  -- neighborhood of `y`; taking complements yields the contradiction.
  rcases xTail_subset_of_isOpen_of_mem hZ.isOpen hxZ with ⟨n, hn⟩
  by_contra hyZ
  rcases yTail_subset_of_isOpen_of_mem hZ.compl.isOpen hyZ with ⟨m, hm⟩
  have hzZ : z (n + m) ∈ Z := by
    apply hn
    simp [xTail, mem_zTail_iff]
  have hzCompl : z (n + m) ∈ Zᶜ := by
    apply hm
    simp [yTail, mem_zTail_iff]
  exact hzCompl hzZ

/-- Helper for Remark 5.7.4: the two-point set `{x, y}` is separated by the basic tails. -/
private lemma pair_xy_not_preconnected : ¬ IsPreconnected ({x, y} : Set Point) := by
  intro hxy
  have hcover : ({x, y} : Set Point) ⊆ xTail 0 ∪ yTail 0 := by
    intro p hp
    simp at hp
    rcases hp with rfl | rfl
    · exact Or.inl (by simp [xTail])
    · exact Or.inr (by simp [yTail])
  have hx_nonempty : (({x, y} : Set Point) ∩ xTail 0).Nonempty := by
    refine ⟨x, ?_⟩
    simp [xTail]
  have hy_nonempty : (({x, y} : Set Point) ∩ yTail 0).Nonempty := by
    refine ⟨y, ?_⟩
    simp [yTail]
  rcases hxy (xTail 0) (yTail 0) (xTail_isOpen 0) (yTail_isOpen 0) hcover hx_nonempty hy_nonempty
    with ⟨p, hp⟩
  -- The witness would have to be in `{x, y}` and simultaneously in both disjoint tails.
  cases p <;> simp [xTail, yTail, zTail] at hp

/-- Helper for Remark 5.7.4: clopen singletons exclude every `z n` from the component of `x`. -/
private lemma z_not_mem_connectedComponent_x (n : ℕ) : z n ∉ connectedComponent x := by
  -- The complement of `{z n}` is clopen and contains `x`, so the whole component stays there.
  have hsubset : connectedComponent x ⊆ (zSingleton n)ᶜ :=
    (zSingleton_isClopen n).compl.connectedComponent_subset (by simp [zSingleton])
  intro hz
  have hz' : z n ∈ (zSingleton n)ᶜ := hsubset hz
  simp [zSingleton] at hz'

/-- Helper for Remark 5.7.4: the connected component of `x` cannot also contain `y`. -/
private lemma y_not_mem_connectedComponent_x : y ∉ connectedComponent x := by
  intro hy
  have hsubset : connectedComponent x ⊆ ({x, y} : Set Point) := by
    intro p hp
    cases p with
    | x =>
        simp
    | y =>
        simp
    | z n =>
        exact False.elim (z_not_mem_connectedComponent_x n hp)
  have hsuperset : ({x, y} : Set Point) ⊆ connectedComponent x := by
    intro p hp
    simp at hp
    rcases hp with rfl | rfl
    · exact mem_connectedComponent
    · exact hy
  have hEq : connectedComponent x = ({x, y} : Set Point) := Subset.antisymm hsubset hsuperset
  have hpre : IsPreconnected ({x, y} : Set Point) := by
    rw [← hEq]
    exact isPreconnected_connectedComponent
  exact pair_xy_not_preconnected hpre

/-- Helper for Remark 5.7.4: the clopen neighborhood `({z n})ᶜ` removes `z n` from the total
intersection of clopen neighborhoods of `x`. -/
private lemma z_not_mem_iInter_isClopen_x (n : ℕ) :
    z n ∉ ⋂ Z : { Z : Set Point // IsClopen Z ∧ x ∈ Z }, (Z : Set Point) := by
  intro hz
  let Z : { Z : Set Point // IsClopen Z ∧ x ∈ Z } :=
    ⟨(zSingleton n)ᶜ, (zSingleton_isClopen n).compl, by simp [zSingleton]⟩
  have hz' : z n ∈ (Z : Set Point) := Set.mem_iInter.mp hz Z
  simp [Z, zSingleton] at hz'

/-- The connected component of `x` is the singleton `{x}` in the counterexample space. -/
-- Proof sketch: any connected subset containing `x` cannot contain any `z n`, since `{z n}` is open
-- and closed inside the subset, and `y` is separated from `x` by the basic open tails. Maximality
-- of the connected component then forces `connectedComponent x = {x}`.
theorem connectedComponent_x :
    connectedComponent x = ({x} : Set Point) := by
  -- The component is computed by first removing all `z n` via clopen singletons and then removing
  -- `y` via the explicit separation of `{x, y}`.
  ext p
  cases p with
  | x =>
      -- A point always lies in its own connected component.
      simp [mem_connectedComponent]
  | y =>
      -- The two-point set `{x, y}` is not preconnected, so `y` cannot lie in the component of `x`.
      simp [y_not_mem_connectedComponent_x]
  | z n =>
      -- Each `z n` is cut off by the clopen singleton `{z n}`.
      simp [z_not_mem_connectedComponent_x n]

/-- The intersection of all clopen neighborhoods of `x` is `{x, y}` in the counterexample space. -/
-- Proof sketch: show every clopen neighborhood of `x` must also contain `y`, while the set
-- `{x, y}` itself is the intersection of the clopen supersets obtained from the displayed tails.
theorem iInter_isClopen_x :
    (⋂ Z : { Z : Set Point // IsClopen Z ∧ x ∈ Z }, (Z : Set Point)) = ({x, y} : Set Point) := by
  -- The index type already forces every set in the intersection to contain `x`, and the previous
  -- helper upgrades this to `y`; the clopen complements of the singletons remove the `z n`.
  ext p
  cases p with
  | x =>
      constructor
      · intro _
        simp
      · intro _
        exact Set.mem_iInter.mpr fun Z ↦ Z.2.2
  | y =>
      constructor
      · intro _
        simp
      · intro _
        exact Set.mem_iInter.mpr fun Z ↦ clopen_neighborhood_of_x_contains_y Z.2.1 Z.2.2
  | z n =>
      simp [z_not_mem_iInter_isClopen_x n]

/-- Remark 5.7.4: in general the connected component of a point can be strictly smaller than the
intersection of all clopen neighborhoods containing that point; the space defined here is such a
counterexample. -/
-- Proof sketch: combine the explicit computations `connectedComponent_x` and `iInter_isClopen_x`;
-- equivalently, appeal to the canonical inclusion
-- `connectedComponent_subset_iInter_isClopen` and the explicit identifications of the two sets.
theorem connectedComponent_x_ssubset_iInter_isClopen :
    connectedComponent x ⊂ ⋂ Z : { Z : Set Point // IsClopen Z ∧ x ∈ Z }, (Z : Set Point) := by
  refine ⟨connectedComponent_subset_iInter_isClopen, ?_⟩
  simp [connectedComponent_x, iInter_isClopen_x]

end ConnectedComponentClopenCounterexample

/-! ### Lemma_5_7_5 (from Chap05) -/
universe u v

open Topology

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/- Domain-style sampling for Stacks tag `0377`:
- primary domain: coinducing maps and the induced map on connected components
- same-domain declarations inspected:
  `Topology.isCoinducing_iff_isClosed`,
  `Topology.IsCoinducing.of_isClosed_preimage_iff_isClosed`,
  `Topology.IsCoinducing.continuous`,
  `Topology.IsCoinducing.connectedComponentsMap_bijective`

Layer triage:
- `source-facing`: the Stacks closed-set criterion on subsets of `Y`
- `core/canonical`: the owner predicate `Topology.IsCoinducing`
- `bridge/view`: the induced map on `ConnectedComponents`

Primitive data is the closed-set criterion itself. Continuity of `f` and the connected-components
map are derived API from the owner `IsCoinducing`, so this file should reuse that owner directly
rather than introduce a parallel local wrapper.
-/
/- The source closed-set criterion is the canonical bridge to `Topology.IsCoinducing`. -/
recall IsCoinducing.of_isClosed_preimage_iff_isClosed

/- Canonical library form of Stacks tag `0377`: a coinducing map with connected fibers induces a
bijection on connected components. -/
recall IsCoinducing.connectedComponentsMap_bijective

-- Proof sketch: the closed-set hypothesis is exactly the coinducing criterion, so continuity of
-- `f` is derived rather than primitive. Then apply the canonical connected-components theorem for
-- coinducing maps with connected fibers.
/-- Lemma 5.7.5: if every fiber `f ⁻¹' {y}` is connected, and a subset of `Y` is closed exactly
when its preimage is closed, then the induced map on connected components is bijective. This is
the Stacks-style closed-set bridge to the canonical recalled
`IsCoinducing.connectedComponentsMap_bijective`. -/
theorem connectedComponentsMap_bijective_of_connected_fibers_of_isClosed_iff
    (hfiber : ∀ y : Y, IsConnected (f ⁻¹' {y}))
    (hclosed : ∀ T : Set Y, IsClosed T ↔ IsClosed (f ⁻¹' T)) :
    ((IsCoinducing.of_isClosed_preimage_iff_isClosed
      (fun T ↦ (hclosed T).symm)).continuous.connectedComponentsMap).Bijective := by
  let hf : IsCoinducing f :=
    IsCoinducing.of_isClosed_preimage_iff_isClosed fun T ↦ (hclosed T).symm
  simpa [hf] using hf.connectedComponentsMap_bijective hfiber

end

/-! ### Lemma_5_7_6 (from Chap05) -/
open Set Topology

universe u v

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/- Domain-style sampling for connected components under open quotient maps:
- primary domain: connected components of topological spaces under open/coinducing maps
- earlier chapter owner abstraction: `IsOpenQuotientMap`
- same-domain declarations inspected:
  `IsOpenQuotientMap`,
  `IsOpenQuotientMap.isQuotientMap`,
  `connectedComponentsMap_bijective_of_connected_fibers_of_isClosed_iff`,
  `Topology.IsCoinducing.connectedComponentsMap_bijective`

Layer triage:
- `source-facing`: the Stacks open-map criterion with connected fibers
- `core/canonical`: `IsOpenQuotientMap`, whose quotient-map/coinducing consequences are derived
- `bridge/view`: the induced map `Continuous.connectedComponentsMap` on connected components

Primitive data is just continuity, openness, and the connected-fibre hypothesis. Surjectivity and
the quotient/coinducing package are derived from the owner abstraction, so this file should expose
the owner-level open-quotient theorem and keep the source wording as a thin wrapper.
-/

/- Canonical library form used below: a coinducing map with connected fibers induces a bijection
on connected components. -/
recall Topology.IsCoinducing.connectedComponentsMap_bijective

namespace IsOpenQuotientMap

/-- Canonical open-quotient form of Lemma 5.7.6: an open quotient map with connected fibres
induces a bijection on connected components. -/
theorem connectedComponentsMap_bijective (hf : IsOpenQuotientMap f)
    (hfibers : ∀ y : Y, IsConnected (f ⁻¹' {y})) :
    Function.Bijective hf.continuous.connectedComponentsMap := by
  let hcoind := hf.isQuotientMap.isCoinducing
  simpa using hcoind.connectedComponentsMap_bijective hfibers

end IsOpenQuotientMap

-- Proof sketch: connected fibers force surjectivity, so `f` packages as an `IsOpenQuotientMap`;
-- the source wording is then just the owner-level theorem above.
/-- Lemma 5.7.6: an open continuous map with connected fibres induces a bijection on connected
components. This is the source-wording bridge to the owner theorem
`IsOpenQuotientMap.connectedComponentsMap_bijective`. -/
theorem connectedComponents_bijective_of_isOpenMap_of_connectedFibers
    (hcont : Continuous f) (hopen : IsOpenMap f)
    (hfibers : ∀ y : Y, IsConnected (f ⁻¹' {y})) :
    hcont.connectedComponentsMap.Bijective := by
  let hf : IsOpenQuotientMap f := ⟨fun y ↦ (hfibers y).nonempty, hcont, hopen⟩
  exact hf.connectedComponentsMap_bijective hfibers

end

/-! ### Lemma_5_7_7 (from Chap05) -/
open Set Topology

universe u v

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable [ConnectedSpace Y] {f : X → Y}

/- Domain-style sampling for connected components under open and closed maps:
- owner abstractions:
  `IsOpenMap`,
  `ConnectedComponents`
- same-domain derived API inspected:
  `IsOpenMap.enatCard_connectedComponents_le_encard_preimage_singleton`,
  `IsOpenMap.finite_connectedComponents_of_finite_preimage_singleton_of_connectedSpace`,
  `ConnectedComponents.discreteTopology_iff`,
  `IsClopen.eq_univ`

Layer triage:
- `source-facing`: the finite-cardinality bound on `ConnectedComponents X` in terms of a finite
  fiber of `f`
- `core/canonical`: `IsOpenMap`, `ConnectedComponents`, and the recalled `ENat.card` inequality
- `bridge/view`: the `Nat.card`/`Set.ncard` reformulation of the canonical `ENat.card` inequality

Primitive data are the open and closed map hypotheses together with connectedness of `Y` and
finiteness of one fiber as a set. Finiteness of `ConnectedComponents X` and the
`Nat.card`/`Set.ncard` reformulation are derived API off the `IsOpenMap` owner; they should stay a
thin bridge to the recalled owner statement rather than growing a parallel local convenience
family.
-/

/-
Canonical library form of Stacks tag `07VB`: the cardinality bound is already available in
mathlib in the `ENat.card`/`Set.encard` form, and it does not use the continuity hypothesis.
-/
recall IsOpenMap.enatCard_connectedComponents_le_encard_preimage_singleton
    (hopen : IsOpenMap f) (hclosed : IsClosedMap f) [ConnectedSpace Y] (y : Y) :
    ENat.card (ConnectedComponents X) ≤ (f ⁻¹' {y}).encard

namespace IsOpenMap

/-- Lemma 5.7.7: if `Y` is connected, `f` is open and closed, and the fiber over `y` is finite,
then `X` has at most `|f ⁻¹' {y}|` connected components. This is the finite-cardinal bridge form
of the canonical `ENat.card` inequality
`IsOpenMap.enatCard_connectedComponents_le_encard_preimage_singleton`, expressed with the
primitive set-cardinality `Set.ncard` on the fiber. -/
theorem natCard_connectedComponents_le_ncard_preimage_singleton
    (hopen : IsOpenMap f) (hclosed : IsClosedMap f) {y : Y}
    (hyfin : (f ⁻¹' {y}).Finite) :
    Nat.card (ConnectedComponents X) ≤ (f ⁻¹' {y}).ncard := by
  letI : Finite (ConnectedComponents X) :=
    hopen.finite_connectedComponents_of_finite_preimage_singleton_of_connectedSpace hclosed hyfin
  have hcard : ENat.card (ConnectedComponents X) ≤ (f ⁻¹' {y}).encard :=
    hopen.enatCard_connectedComponents_le_encard_preimage_singleton hclosed y
  exact ENat.coe_le_coe.mp <| by
    simpa [ENat.card_eq_coe_natCard, hyfin.cast_ncard_eq] using hcard

end IsOpenMap

end

/-! ### Definition_5_7_8 (from Chap05) -/
/- Domain-style sampling for total disconnectedness in topological spaces:
- owner abstraction: `TotallyDisconnectedSpace`
- canonical source-facing bridge:
  `totallyDisconnectedSpace_iff_connectedComponent_singleton`
- same-domain declarations inspected:
  `TotallyDisconnectedSpace`,
  `totallyDisconnectedSpace_iff_connectedComponent_subsingleton`,
  `totallyDisconnectedSpace_iff_connectedComponent_singleton`,
  `connectedComponent_eq_singleton`

Layer triage:
- `source-facing`: the textbook criterion that connected components are singletons
- `core/canonical`: the mathlib owner class `TotallyDisconnectedSpace`
- `bridge/view`: the equivalence between the textbook criterion and the owner class

Primitive data belongs to the owner class `TotallyDisconnectedSpace`. The connected-component
singleton criterion is derived API, so this file should recall the owner first and keep the
criterion as a companion bridge. -/

/- Canonical recall for the mathlib class `TotallyDisconnectedSpace`, which is the owner
abstraction for this definition. -/
recall TotallyDisconnectedSpace

/- Definition 5.7.8: a topological space is totally disconnected if all of its connected
components are singletons. This is the canonical bridge between the textbook criterion and the
owner class `TotallyDisconnectedSpace`. -/
recall totallyDisconnectedSpace_iff_connectedComponent_singleton

/-! ### Lemma_5_7_9 (from Chap05) -/
universe u v

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for connected components and totally disconnected targets:
- owner abstractions:
  `ConnectedComponents`,
  `TotallyDisconnectedSpace`
- same-domain declarations inspected:
  `ConnectedComponents.totallyDisconnectedSpace`,
  `Continuous.connectedComponentsLift`,
  `Continuous.connectedComponentsLift_comp_coe`,
  `Continuous.connectedComponentsLift_unique`

Layer triage:
- `source-facing`: the quotient of a space by connected components and the universal factorization
  of a continuous map into a totally disconnected space
- `core/canonical`: the quotient owner `ConnectedComponents` together with the owner class
  `TotallyDisconnectedSpace`
- `bridge/view`: the canonical lift `Continuous.connectedComponentsLift` and its factorization and
  uniqueness theorems

Primitive data are only the quotient owner `ConnectedComponents X`, the target owner class
`TotallyDisconnectedSpace Y`, and a continuous map `f : X → Y`. Total disconnectedness of the
quotient and the universal factorization statements are derived API already owned by mathlib, so
this file should remain a pure recall of those canonical declarations rather than introduce any
parallel local wrapper.
-/
/- Lemma 5.7.9 (first assertion): the quotient of `X` by its connected components is totally
disconnected. This is the canonical mathlib instance
`ConnectedComponents.totallyDisconnectedSpace`. -/
recall ConnectedComponents.totallyDisconnectedSpace

variable {Y : Type v} [TopologicalSpace Y] [TotallyDisconnectedSpace Y]

/- Lemma 5.7.9 (second assertion): for a continuous map `f : X → Y` into a totally disconnected
space, the canonical factorization through `X → ConnectedComponents X` is
`Continuous.connectedComponentsLift`; its continuity, factorization identity, and uniqueness are
the recalled facts below. -/
recall Continuous.connectedComponentsLift
recall Continuous.connectedComponentsLift_continuous
recall Continuous.connectedComponentsLift_comp_coe
recall Continuous.connectedComponentsLift_unique

/-! ### Definition_5_7_10 (from Chap05) -/
universe u

open Topology

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for local connectedness in topological spaces:
- owner abstraction: `LocallyConnectedSpace`
- canonical bridge declarations:
  `locallyConnectedSpace_iff_hasBasis_isOpen_isConnected`,
  `locallyConnectedSpace_iff_connected_basis`,
  `LocallyConnectedSpace.open_connected_basis`,
  `locallyConnectedSpace_of_connected_bases`
- same-domain declarations inspected:
  `LocallyConnectedSpace`,
  `locallyConnectedSpace_iff_hasBasis_isOpen_isConnected`,
  `locallyConnectedSpace_iff_connected_basis`,
  `LocallyConnectedSpace.open_connected_basis`,
  `locallyConnectedSpace_of_connected_bases`

Layer triage:
- `source-facing`: the textbook criterion that every neighborhood filter has a basis of connected
  neighborhoods
- `core/canonical`: the mathlib owner class `LocallyConnectedSpace`
- `bridge/view`: the equivalence between the owner and neighborhood-basis formulations, first with
  open connected neighborhoods, then preconnected neighborhoods, and finally connected
  neighborhoods

Primitive data belongs to the owner class `LocallyConnectedSpace`, whose field uses open connected
neighborhoods. The source-facing “connected neighborhoods” criterion is derived API, so this file
should recall the owner and keep only the thin neighborhood-basis bridge below. -/

/- Canonical recall: the mathlib owner for local connectedness is `LocallyConnectedSpace`. -/
recall LocallyConnectedSpace

/- Companion recall: mathlib’s canonical bridge theorem uses preconnected neighborhoods. -/
recall locallyConnectedSpace_iff_connected_basis

/- Companion recall: a basis of connected neighborhoods canonically rebuilds the owner. -/
recall locallyConnectedSpace_of_connected_bases

/-- Definition 5.7.10: a topological space is locally connected if every point has a fundamental
system of connected neighborhoods, equivalently if each neighborhood filter has a basis of
connected neighborhoods. -/
-- Proof sketch: forget openness from `LocallyConnectedSpace.open_connected_basis` in the forward
-- direction, and rebuild the owner from the connected neighborhood bases using
-- `locallyConnectedSpace_of_connected_bases` in the reverse direction.
theorem locallyConnectedSpace_iff_hasBasis_connected_neighborhoods :
    LocallyConnectedSpace X ↔
      ∀ x, (𝓝 x).HasBasis (fun s : Set X ↦ s ∈ 𝓝 x ∧ IsConnected s) id := by
  constructor
  · intro h x
    letI := h
    refine (LocallyConnectedSpace.open_connected_basis x).to_hasBasis
      (fun s hs ↦ ⟨s, ⟨mem_nhds_iff.mpr ⟨s, subset_rfl, hs.1, hs.2.1⟩, hs.2.2⟩, subset_rfl⟩)
      ?_
    intro s hs
    exact (LocallyConnectedSpace.open_connected_basis x).mem_iff.mp hs.1
  · intro h
    exact locallyConnectedSpace_of_connected_bases (fun _ s ↦ s)
      (fun x s ↦ s ∈ 𝓝 x ∧ IsConnected s) h
      (fun _ _ hs ↦ hs.2.isPreconnected)

/-! ### Lemma_5_7_11 (from Chap05) -/
universe u

open Topology

variable {X : Type u} [TopologicalSpace X] [LocallyConnectedSpace X]

/- Domain-style sampling for locally connected topological spaces:
- owner abstraction: `LocallyConnectedSpace`
- same-domain declarations inspected:
  `LocallyConnectedSpace.open_connected_basis`,
  `IsOpen.locallyConnectedSpace`,
  `isOpen_connectedComponent`,
  `IsOpen.connectedComponentIn`

Layer triage:
- `source-facing`: Lemma 5.7.11 records the standard permanence/open-neighborhood consequences of
  local connectedness
- `core/canonical`: the mathlib owner class `LocallyConnectedSpace`
- `bridge/view`: no extra bridge is needed here, since clause `(4)` is already exactly the owner
  theorem `LocallyConnectedSpace.open_connected_basis`

Primitive data belongs to `LocallyConnectedSpace.open_connected_basis`, whose basis is indexed by
sets. The `OpenNhdsOf x` formulation is derived API, so this file should stop at direct canonical
recall of the owner theorem rather than introduce a parallel local bridge. -/

/- Lemma 5.7.11 (1): open subsets of a locally connected space are locally connected.
This is exactly the canonical theorem `IsOpen.locallyConnectedSpace`. -/
recall IsOpen.locallyConnectedSpace

/- Lemma 5.7.11 (2): in a locally connected space, connected components are open.
This is exactly the canonical theorem `isOpen_connectedComponent`. -/
recall isOpen_connectedComponent

/- Lemma 5.7.11 (3): for an open subset `U`, `connectedComponentIn U x` is open.
This is exactly the canonical theorem `IsOpen.connectedComponentIn`. -/
recall IsOpen.connectedComponentIn

/- Lemma 5.7.11 (4): every point of a locally connected space has a neighbourhood basis of open
connected sets. This is exactly the canonical theorem
`LocallyConnectedSpace.open_connected_basis`. -/
recall LocallyConnectedSpace.open_connected_basis
