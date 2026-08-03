import Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1
import Integer.Chapters.Chap07.section_7_1.ch7_sec7_1_proposition_7_1
import Integer.Chapters.Chap07.section_7_7.ch7_sec7_7_exercise_7_2
import Integer.Chapters.Chap07.section_7_7.ch7_sec7_7_stable_set_relaxations
import Mathlib.GroupTheory.Perm.Fin

open scoped BigOperators

-- Domain sampling for this exercise:
-- * source-facing stable-set owners are reused from `Exercise 7.2`
-- * the graph-relaxation owners `Q`, `FRAC`, and `K` are reused from
--   `ch7_sec7_7_stable_set_relaxations`
-- * the shared support restriction `zero_outside` is reused from `Proposition 7.1`
-- * core/canonical facet owner: Chapter 3's `IsFacetOf`
-- * this file keeps only the exercise-specific support restrictions, graph-support data,
--   and equality-face owners for Exercise 7.19

section Exercise_7_19

variable {V : Type}

variable (G : SimpleGraph V)

/-- The cyclic forward offset from `i` to `j` on `Fin m`, computed modulo `m`. -/
def cyclic_offset {m : ℕ} (i j : Fin m) : ℕ :=
  (j.1 + m - i.1) % m

/-- `cyclic_offset i j` is definitionally the forward modular difference from `i` to `j`. -/
theorem cyclic_offset_eq {m : ℕ} (i j : Fin m) :
    cyclic_offset i j = (j.1 + m - i.1) % m := rfl

/-- A finite cyclic support in the ambient vertex type `V` is an injectively labelled cyclic
vertex set. This is the shared core owner for the cycle, antihole, and web supports below. -/
structure CyclicSupport (V : Type) where
  /-- The number of labelled vertices. -/
  length : ℕ
  /-- The injective cyclic labelling of those vertices. -/
  verts : Fin length ↪ V

/-- A cyclic support can be used as its vertex-labelling map. -/
instance : CoeFun (CyclicSupport V) (fun C ↦ Fin C.length → V) where
  coe C := C.verts

/-- The finite vertex set underlying a cyclic support. -/
def CyclicSupport.vertexFinset (C : CyclicSupport V) : Finset V :=
  Finset.univ.map C.verts

/-- A vertex lies in `C.vertexFinset` exactly when it appears in the cyclic labelling of `C`. -/
theorem CyclicSupport.mem_vertexFinset_iff
    (C : CyclicSupport V) {v : V} :
    v ∈ C.vertexFinset ↔ ∃ i : Fin C.length, C.verts i = v := by
  simp [CyclicSupport.vertexFinset]

/-- A finite cyclic support in the ambient vertex type `V`, represented by an injective cyclic
labelling. -/
structure CycleSupport (V : Type) extends CyclicSupport V where
  /-- A cycle support has at least three vertices. -/
  length_ge_three : 3 ≤ length

/-- A cycle support can be used as its vertex-labelling map. -/
instance : CoeFun (CycleSupport V) (fun C ↦ Fin C.length → V) where
  coe C := C.verts

/-- The finite vertex set underlying a cyclic support. -/
abbrev CycleSupport.vertexFinset (C : CycleSupport V) : Finset V :=
  C.toCyclicSupport.vertexFinset

/-- A vertex lies in `C.vertexFinset` exactly when it appears in the cyclic labelling of `C`. -/
theorem CycleSupport.mem_vertexFinset_iff
    (C : CycleSupport V) {v : V} :
    v ∈ C.vertexFinset ↔ ∃ i : Fin C.length, C.verts i = v := by
  simpa [CycleSupport.vertexFinset] using
    (C.toCyclicSupport.mem_vertexFinset_iff :
      v ∈ C.toCyclicSupport.vertexFinset ↔ ∃ i : Fin C.length, C.verts i = v)

/-- The support `C` is contained in `G` as a cycle when consecutive labelled vertices are
adjacent in `G`. -/
def CycleSupport.IsContainedIn (C : CycleSupport V) (G : SimpleGraph V) : Prop :=
  ∀ i : Fin C.length,
    G.Adj (C.verts i)
      (C.verts
        ⟨(i.1 + 1) % C.length,
          Nat.mod_lt _ (Nat.lt_of_lt_of_le (by decide) C.length_ge_three)⟩)

/-- `C.IsContainedIn G` means exactly that every consecutive pair in the cyclic order is an edge
of `G`. -/
theorem CycleSupport.isContainedIn_iff
    (C : CycleSupport V) (G : SimpleGraph V) :
    C.IsContainedIn G ↔
      ∀ i : Fin C.length,
        G.Adj (C.verts i)
          (C.verts
            ⟨(i.1 + 1) % C.length,
              Nat.mod_lt _ (Nat.lt_of_lt_of_le (by decide) C.length_ge_three)⟩) := Iff.rfl

/-- The support `C` is chordless in `G` when the only edges of `G` between cycle vertices are the
cycle edges themselves. -/
def CycleSupport.IsChordlessIn (C : CycleSupport V) (G : SimpleGraph V) : Prop :=
  C.IsContainedIn G ∧
    ∀ i j : Fin C.length, G.Adj (C.verts i) (C.verts j) →
      cyclic_offset i j = 1 ∨ cyclic_offset j i = 1

/-- `C.IsChordlessIn G` unfolds to containing the cycle edges and forbidding extra chords among
the labelled cycle vertices. -/
theorem CycleSupport.isChordlessIn_iff
    (C : CycleSupport V) (G : SimpleGraph V) :
    C.IsChordlessIn G ↔
      C.IsContainedIn G ∧
        ∀ i j : Fin C.length, G.Adj (C.verts i) (C.verts j) →
          cyclic_offset i j = 1 ∨ cyclic_offset j i = 1 := Iff.rfl

/-- The odd-cycle inequality right-hand side attached to a cyclic support is `(length - 1) / 2`.
-/
def odd_cycle_inequality_rhs (C : CycleSupport V) : ℝ :=
  (((C.length - 1) / 2 : ℕ) : ℝ)

/-- `odd_cycle_inequality_rhs C` is the floor-half right-hand side `(|C| - 1) / 2`. -/
theorem odd_cycle_inequality_rhs_eq
    (C : CycleSupport V) :
    odd_cycle_inequality_rhs C = (((C.length - 1) / 2 : ℕ) : ℝ) := rfl

/-- An antihole support in the ambient vertex type `V`, represented by an injective cyclic
labelling. -/
structure AntiholeSupport (V : Type) extends CyclicSupport V where
  /-- An antihole has at least five vertices. -/
  length_ge_five : 5 ≤ length

/-- An antihole support can be used as its vertex-labelling map. -/
instance : CoeFun (AntiholeSupport V) (fun H ↦ Fin H.length → V) where
  coe H := H.verts

/-- The finite vertex set underlying an antihole support. -/
abbrev AntiholeSupport.vertexFinset (H : AntiholeSupport V) : Finset V :=
  H.toCyclicSupport.vertexFinset

/-- A vertex lies in `H.vertexFinset` exactly when it appears in the antihole labelling. -/
theorem AntiholeSupport.mem_vertexFinset_iff
    (H : AntiholeSupport V) {v : V} :
    v ∈ H.vertexFinset ↔ ∃ i : Fin H.length, H.verts i = v := by
  simpa [AntiholeSupport.vertexFinset] using
    (H.toCyclicSupport.mem_vertexFinset_iff :
      v ∈ H.toCyclicSupport.vertexFinset ↔ ∃ i : Fin H.length, H.verts i = v)

/-- The support `H` is contained in `G` as an antihole when every nonconsecutive labelled pair is
an edge of `G`. -/
def AntiholeSupport.IsContainedIn (H : AntiholeSupport V) (G : SimpleGraph V) : Prop :=
  ∀ i j : Fin H.length,
    i ≠ j →
      2 ≤ cyclic_offset i j →
      2 ≤ cyclic_offset j i →
      G.Adj (H.verts i) (H.verts j)

/-- `H.IsContainedIn G` means that each pair prescribed by the antihole pattern is an edge of
`G`. -/
theorem AntiholeSupport.isContainedIn_iff
    (H : AntiholeSupport V) (G : SimpleGraph V) :
    H.IsContainedIn G ↔
      ∀ i j : Fin H.length,
        i ≠ j →
          2 ≤ cyclic_offset i j →
          2 ≤ cyclic_offset j i →
          G.Adj (H.verts i) (H.verts j) := Iff.rfl

/-- The support `H` is induced in `G` as an antihole when the edges of `G` on its labelled
vertices are exactly the antihole edges. -/
def AntiholeSupport.IsInducedIn (H : AntiholeSupport V) (G : SimpleGraph V) : Prop :=
  ∀ i j : Fin H.length,
    G.Adj (H.verts i) (H.verts j) ↔
      i ≠ j ∧ 2 ≤ cyclic_offset i j ∧ 2 ≤ cyclic_offset j i

/-- `H.IsInducedIn G` unfolds to equality between the induced graph on `H.vertexFinset` and the
antihole edge pattern. -/
theorem AntiholeSupport.isInducedIn_iff
    (H : AntiholeSupport V) (G : SimpleGraph V) :
    H.IsInducedIn G ↔
      ∀ i j : Fin H.length,
        G.Adj (H.verts i) (H.verts j) ↔
          i ≠ j ∧ 2 ≤ cyclic_offset i j ∧ 2 ≤ cyclic_offset j i := Iff.rfl

/-- An induced antihole support is automatically contained as an antihole support. -/
theorem AntiholeSupport.IsInducedIn.isContainedIn
    {H : AntiholeSupport V} {G : SimpleGraph V}
    (hInd : H.IsInducedIn G) :
    H.IsContainedIn G := by
  intro i j hij hij₁ hij₂
  exact (hInd i j).2 ⟨hij, hij₁, hij₂⟩

/-- A web support `W_n^k` in the ambient vertex type `V`, represented by an injective cyclic
labelling of the `n` vertices together with the web width `k`. -/
structure WebSupport (V : Type) extends CyclicSupport V where
  /-- The web parameter `k`. -/
  width : ℕ
  /-- The web parameter is positive. -/
  width_pos : 0 < width
  /-- The web condition `2k + 1 ≤ n`. -/
  width_bound : 2 * width + 1 ≤ length

/-- A web support can be used as its vertex-labelling map. -/
instance : CoeFun (WebSupport V) (fun W ↦ Fin W.length → V) where
  coe W := W.verts

/-- The finite vertex set underlying a web support. -/
abbrev WebSupport.vertexFinset (W : WebSupport V) : Finset V :=
  W.toCyclicSupport.vertexFinset

/-- A vertex lies in `W.vertexFinset` exactly when it appears in the web labelling. -/
theorem WebSupport.mem_vertexFinset_iff
    (W : WebSupport V) {v : V} :
    v ∈ W.vertexFinset ↔ ∃ i : Fin W.length, W.verts i = v := by
  simpa [WebSupport.vertexFinset] using
    (W.toCyclicSupport.mem_vertexFinset_iff :
      v ∈ W.toCyclicSupport.vertexFinset ↔ ∃ i : Fin W.length, W.verts i = v)

/-- The support `W` is contained in `G` as a web when every pair whose cyclic distance is at most
`k = W.width` is adjacent in `G`. -/
def WebSupport.IsContainedIn (W : WebSupport V) (G : SimpleGraph V) : Prop :=
  ∀ i j : Fin W.length,
    i ≠ j →
      (cyclic_offset i j ≤ W.width ∨ cyclic_offset j i ≤ W.width) →
      G.Adj (W.verts i) (W.verts j)

/-- `W.IsContainedIn G` means that the edge pattern prescribed by the web parameters occurs in
`G`. -/
theorem WebSupport.isContainedIn_iff
    (W : WebSupport V) (G : SimpleGraph V) :
    W.IsContainedIn G ↔
      ∀ i j : Fin W.length,
        i ≠ j →
          (cyclic_offset i j ≤ W.width ∨ cyclic_offset j i ≤ W.width) →
          G.Adj (W.verts i) (W.verts j) := Iff.rfl

/-- The web inequality right-hand side is `⌊n / (k + 1)⌋`, implemented by natural-number
division. -/
def web_inequality_rhs (W : WebSupport V) : ℝ :=
  ((W.length / (W.width + 1) : ℕ) : ℝ)

/-- `web_inequality_rhs W` is the floor of `n / (k + 1)` for the web parameters of `W`. -/
theorem web_inequality_rhs_eq
    (W : WebSupport V) :
    web_inequality_rhs W = ((W.length / (W.width + 1) : ℕ) : ℝ) := rfl

section Chvatal

variable [Fintype V]

noncomputable local instance : DecidableEq V := Classical.decEq V

/-- A Chvatal inequality for the edge relaxation `Q(G)` is given by nonnegative multipliers on
the edge inequalities together with nonnegative slack on the nonnegativity constraints, producing
an integral coefficient vector and the floored aggregated right-hand side. -/
noncomputable def IsEdgeRelaxationChvatalInequality
    (G : SimpleGraph V) (c : V → ℝ) (δ : ℝ) : Prop :=
  ∃ μ : Sym2 V → ℝ, ∃ s : V → ℝ,
    (∀ e : Sym2 V, 0 ≤ μ e) ∧
        (∀ e : Sym2 V, μ e ≠ 0 → e ∈ G.edgeSet) ∧
        (∀ v : V, 0 ≤ s v) ∧
          (∀ v : V, ∃ z : ℤ, c v = (z : ℝ)) ∧
            (fun v ↦ (∑ e : Sym2 V, if v ∈ e then μ e else 0) - s v) = c ∧
              δ = ((Int.floor (∑ e : Sym2 V, μ e) : ℤ) : ℝ)

/-- `IsEdgeRelaxationChvatalInequality G c δ` unfolds to the existence of nonnegative edge
multipliers and nonnegative slack coefficients yielding the displayed floored inequality. -/
theorem isEdgeRelaxationChvatalInequality_iff
    (G : SimpleGraph V) (c : V → ℝ) (δ : ℝ) :
    IsEdgeRelaxationChvatalInequality G c δ ↔
      ∃ μ : Sym2 V → ℝ, ∃ s : V → ℝ,
        (∀ e : Sym2 V, 0 ≤ μ e) ∧
          (∀ e : Sym2 V, μ e ≠ 0 → e ∈ G.edgeSet) ∧
            (∀ v : V, 0 ≤ s v) ∧
              (∀ v : V, ∃ z : ℤ, c v = (z : ℝ)) ∧
                (fun v ↦ (∑ e : Sym2 V, if v ∈ e then μ e else 0) - s v) = c ∧
                  δ = ((Int.floor (∑ e : Sym2 V, μ e) : ℤ) : ℝ) := Iff.rfl

/-- A Chvatal inequality for the clique relaxation `K(G)` is given by nonnegative multipliers on
the clique inequalities together with nonnegative slack on the nonnegativity constraints,
producing an integral coefficient vector and the floored aggregated right-hand side. -/
noncomputable def IsCliqueRelaxationChvatalInequality
    (G : SimpleGraph V) (c : V → ℝ) (δ : ℝ) : Prop :=
  ∃ μ : Finset V → ℝ, ∃ s : V → ℝ,
    (∀ K : Finset V, 0 ≤ μ K) ∧
      (∀ K : Finset V, μ K ≠ 0 → G.IsClique K) ∧
        (∀ v : V, 0 ≤ s v) ∧
          (∀ v : V, ∃ z : ℤ, c v = (z : ℝ)) ∧
            (fun v ↦ (∑ K : Finset V, μ K * (if v ∈ K then 1 else 0)) - s v) = c ∧
              δ = ((Int.floor (∑ K : Finset V, μ K) : ℤ) : ℝ)

/-- `IsCliqueRelaxationChvatalInequality G c δ` unfolds to the existence of nonnegative clique
multipliers and nonnegative slack coefficients yielding the displayed floored inequality. -/
theorem isCliqueRelaxationChvatalInequality_iff
    (G : SimpleGraph V) (c : V → ℝ) (δ : ℝ) :
    IsCliqueRelaxationChvatalInequality G c δ ↔
      ∃ μ : Finset V → ℝ, ∃ s : V → ℝ,
        (∀ K : Finset V, 0 ≤ μ K) ∧
        (∀ K : Finset V, μ K ≠ 0 → G.IsClique K) ∧
          (∀ v : V, 0 ≤ s v) ∧
            (∀ v : V, ∃ z : ℤ, c v = (z : ℝ)) ∧
                (fun v ↦ (∑ K : Finset V, μ K * (if v ∈ K then 1 else 0)) - s v) = c ∧
                  δ = ((Int.floor (∑ K : Finset V, μ K) : ℤ) : ℝ) := Iff.rfl

end Chvatal

/-- Dotting `stableSetIndicator S` with `x` recovers the coordinate sum over `S`. -/
theorem stableSetIndicator_dotProduct [Fintype V]
    (S : Finset V) (x : V → ℝ) :
    stableSetIndicator S ⬝ᵥ x = S.sum x := by
  classical
  simp [dotProduct, stableSetIndicator, Finset.sum_ite_mem]

/-- The equality face of `STAB(G)` cut out by the clique inequality on `K`. -/
noncomputable abbrev cliqueFace [Fintype V] (G : SimpleGraph V) (K : Finset V) : Set (V → ℝ) :=
  {x | x ∈ STAB(G) ∧ K.sum x = 1}

/-- Membership in `cliqueFace G K` means belonging to `STAB(G)` and satisfying the clique
equation on `K`. -/
theorem mem_cliqueFace_iff [Fintype V]
    (G : SimpleGraph V) (K : Finset V) (x : V → ℝ) :
    x ∈ cliqueFace G K ↔ x ∈ STAB(G) ∧ K.sum x = 1 := by
  rfl

/-- The equality face cut out on the support restriction of `STAB(G)` by the odd-cycle
inequality attached to `C`. -/
noncomputable abbrev oddCycleFace [Fintype V]
    (G : SimpleGraph V) (C : CycleSupport V) : Set (V → ℝ) :=
  {x |
    x ∈ STAB(G) ∩ zero_outside C.vertexFinset ∧
      C.vertexFinset.sum x = odd_cycle_inequality_rhs C}

/-- Membership in `oddCycleFace G C` means belonging to the support restriction of `STAB(G)` and
satisfying the odd-cycle equality on `C.vertexFinset`. -/
theorem mem_oddCycleFace_iff [Fintype V]
    (G : SimpleGraph V) (C : CycleSupport V) (x : V → ℝ) :
    x ∈ oddCycleFace G C ↔
      x ∈ STAB(G) ∩ zero_outside C.vertexFinset ∧
        C.vertexFinset.sum x = odd_cycle_inequality_rhs C := by
  rfl

/-- The equality face cut out on the support restriction of `STAB(G)` by the antihole
inequality attached to `H`. -/
noncomputable abbrev antiholeFace [Fintype V]
    (G : SimpleGraph V) (H : AntiholeSupport V) : Set (V → ℝ) :=
  {x | x ∈ STAB(G) ∩ zero_outside H.vertexFinset ∧ H.vertexFinset.sum x = 2}

/-- Membership in `antiholeFace G H` means belonging to the support restriction of `STAB(G)` and
satisfying the antihole equality on `H.vertexFinset`. -/
theorem mem_antiholeFace_iff [Fintype V]
    (G : SimpleGraph V) (H : AntiholeSupport V) (x : V → ℝ) :
    x ∈ antiholeFace G H ↔
      x ∈ STAB(G) ∩ zero_outside H.vertexFinset ∧
        H.vertexFinset.sum x = 2 := by
  rfl

/-- Helper for Exercise 7.19: the coordinate-zero equality face of `STAB(G)` at the vertex `v`.
-/
noncomputable abbrev coordinateZeroFace [Fintype V]
    (G : SimpleGraph V) (v : V) : Set (V → ℝ) :=
  {x | x ∈ STAB(G) ∧ x v = 0}

/-- Helper for Exercise 7.19: membership in `coordinateZeroFace G v` means belonging to `STAB(G)`
and vanishing at the coordinate `v`. -/
theorem mem_coordinateZeroFace_iff [Fintype V]
    (G : SimpleGraph V) (v : V) (x : V → ℝ) :
    x ∈ coordinateZeroFace G v ↔ x ∈ STAB(G) ∧ x v = 0 := by
  rfl

section CliqueFacetHelpers

variable [Fintype V]

noncomputable local instance : DecidableEq V := Classical.decEq V
noncomputable local instance : DecidableRel G.Adj := Classical.decRel G.Adj

/-- Helper for Exercise 7.19: every stable-set indicator belongs to the stable-set polytope. -/
private lemma stableSetIndicator_mem_stableSetPolytope {s : Finset V}
    (hs : G.IsIndepSet s) :
    stableSetIndicator s ∈ STAB(G) := by
  -- Stable-set vertices belong to the convex hull that defines `STAB(G)`.
  rw [stableSetPolytope_eq_convexHull]
  apply subset_convexHull
  rw [mem_stableSetVertices_iff]
  exact ⟨s, hs, rfl⟩

/-- Helper for Exercise 7.19: the empty stable set contributes the zero vector. -/
private lemma stableSetIndicatorEmpty :
    stableSetIndicator (∅ : Finset V) = 0 := by
  -- Every coordinate of the empty indicator vanishes.
  ext v
  simp [stableSetIndicator]

/-- Helper for Exercise 7.19: singleton stable sets give coordinate unit vectors. -/
private lemma stableSetIndicatorSingleton (v : V) :
    stableSetIndicator ({v} : Finset V) = Pi.single v 1 := by
  -- The singleton indicator is `1` at `v` and `0` away from `v`.
  ext u
  by_cases huv : u = v
  · subst huv
    simp [stableSetIndicator]
  · simp [stableSetIndicator, huv]

/-- Helper for Exercise 7.19: a two-point indicator splits into the two singleton coordinates. -/
private lemma stableSetIndicatorPairOfNe {u v : V} (huv : u ≠ v) :
    stableSetIndicator ({u, v} : Finset V) = Pi.single u 1 + Pi.single v 1 := by
  -- The two support coordinates contribute `1`, and every other coordinate contributes `0`.
  ext w
  by_cases hwu : w = u
  · subst hwu
    simp [stableSetIndicator, huv]
  · by_cases hwv : w = v
    · subst hwv
      simp [stableSetIndicator, hwu]
    · simp [stableSetIndicator, hwu, hwv]

/-- Helper for Exercise 7.19: `0` together with the coordinate unit vectors is affinely
independent in `ℝ^V`. -/
private lemma affineIndependentNoneOrSingle :
    AffineIndependent ℝ
      (fun o : Option V ↦ Option.elim o (0 : V → ℝ) (fun v ↦ Pi.single v 1)) := by
  classical
  let p : Option V → V → ℝ :=
    fun o ↦ Option.elim o (0 : V → ℝ) (fun v ↦ Pi.single v 1)
  let e : {o : Option V // o ≠ none} → V := fun o ↦
    match o with
    | ⟨none, hnone⟩ => False.elim (hnone rfl)
    | ⟨some v, _⟩ => v
  have he_injective : Function.Injective e := by
    intro a b hab
    rcases a with ⟨oa, hoa⟩
    rcases b with ⟨ob, hob⟩
    cases oa with
    | none => exact False.elim (hoa rfl)
    | some va =>
        cases ob with
        | none => exact False.elim (hob rfl)
        | some vb =>
            simp only [ne_eq] at hab
            subst hab
            rfl
  -- Affine independence reduces to linear independence of the standard basis.
  rw [affineIndependent_iff_linearIndependent_vsub ℝ p none]
  have hvsub :
      (fun i : {o : Option V // o ≠ none} ↦ (p i -ᵥ p none : V → ℝ)) =
        fun i : {o : Option V // o ≠ none} ↦ Pi.single (e i) 1 := by
    funext i
    rcases i with ⟨o, ho⟩
    cases o with
    | none => exact False.elim (ho rfl)
    | some v =>
        simp [p, e, vsub_eq_sub]
  rw [hvsub]
  exact (Pi.linearIndependent_single_one V ℝ).comp e he_injective

/-- Helper for Exercise 7.19: the stable-set polytope spans the whole ambient function space. -/
private theorem stableSetPolytopeAffineSpanEqTop :
    affineSpan ℝ STAB(G) = ⊤ := by
  classical
  let p : Option V → V → ℝ :=
    fun o ↦ Option.elim o (0 : V → ℝ) (fun v ↦ Pi.single v 1)
  have hp : Set.range p ⊆ STAB(G) := by
    intro x hx
    rcases hx with ⟨o, rfl⟩
    cases o with
    | none =>
        -- The origin comes from the empty stable set.
        have h0 : stableSetIndicator (∅ : Finset V) ∈ STAB(G) :=
          stableSetIndicator_mem_stableSetPolytope (G := G) (by simp)
        simpa [p, stableSetIndicatorEmpty] using h0
    | some v =>
        -- Each singleton indicator is also a stable-set vertex.
        have hv : stableSetIndicator ({v} : Finset V) ∈ STAB(G) :=
          stableSetIndicator_mem_stableSetPolytope (G := G) (by simp)
        simpa [p, stableSetIndicatorSingleton] using hv
  have hp_affine : AffineIndependent ℝ p := by
    -- The chosen family is exactly the origin plus the coordinate unit vectors.
    simpa [p] using (affineIndependentNoneOrSingle (V := V))
  have htop : affineSpan ℝ (Set.range p) = ⊤ := by
    -- The family has `|V| + 1` points in an ambient space of dimension `|V|`.
    have hcard : Fintype.card (Option V) = Fintype.card V + 1 := by
      simp
    exact hp_affine.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by
      rw [Module.finrank_fintype_fun_eq_card]
      exact hcard)
  have hmono : affineSpan ℝ (Set.range p) ≤ affineSpan ℝ STAB(G) :=
    affineSpan_mono ℝ hp
  -- A superset of a spanning affine family has full affine span.
  exact top_unique (by simpa [htop] using hmono)

/-- Helper for Exercise 7.19: a nonzero linear functional on `ℝ^V` has codimension-one kernel. -/
private lemma finrankKerEqCardSubOne {L : (V → ℝ) →ₗ[ℝ] ℝ}
    (hL : L ≠ 0) :
    Module.finrank ℝ (LinearMap.ker L) = Fintype.card V - 1 := by
  let f : Module.Dual ℝ (V → ℝ) := L
  have hf : f ≠ 0 := by
    simpa [f] using hL
  have hker_add_one :
      Module.finrank ℝ (LinearMap.ker L) + 1 = Fintype.card V := by
    simpa [f, Module.finrank_fintype_fun_eq_card] using f.finrank_ker_add_one_of_ne_zero hf
  exact Nat.eq_sub_of_add_eq hker_add_one

/-- Helper for Exercise 7.19: the coefficient vector `c` defines the dot-product functional
`x ↦ c ⬝ᵥ x`. -/
private def dotProductLinearMap (c : V → ℝ) : (V → ℝ) →ₗ[ℝ] ℝ :=
  ∑ v, c v • LinearMap.proj v

/-- Helper for Exercise 7.19: `dotProductLinearMap c` evaluates as `c ⬝ᵥ x`. -/
private lemma dotProductLinearMap_apply (c x : V → ℝ) :
    dotProductLinearMap c x = c ⬝ᵥ x := by
  -- The linear map was defined coordinatewise as the dot product with `c`.
  simp [dotProductLinearMap, dotProduct]

/-- Helper for Exercise 7.19: a nonempty valid equality slice is exposed. -/
private lemma equalitySetIsExposed
    {P : Set (V → ℝ)} {c x₀ : V → ℝ} {δ : ℝ}
    (hvalid : ∀ ⦃x : V → ℝ⦄, x ∈ P → c ⬝ᵥ x ≤ δ)
    (hx₀ : x₀ ∈ P)
    (hx₀_eq : c ⬝ᵥ x₀ = δ) :
    IsExposed ℝ P {x : V → ℝ | x ∈ P ∧ c ⬝ᵥ x = δ} := by
  have hvalid' : ∀ ⦃x : V → ℝ⦄, x ∈ P → dotProductLinearMap c x ≤ δ := by
    intro x hx
    simpa [dotProductLinearMap_apply] using hvalid hx
  have hEq :
      {x : V → ℝ | x ∈ P ∧ c ⬝ᵥ x = δ} =
        (⟨dotProductLinearMap c, (dotProductLinearMap c).continuous_of_finiteDimensional⟩ :
          (V → ℝ) →L[ℝ] ℝ).toExposed P := by
    ext x
    constructor
    · rintro ⟨hxP, hxEq⟩
      refine ⟨hxP, fun y hyP ↦ ?_⟩
      calc
        dotProductLinearMap c y ≤ δ := hvalid' hyP
        _ = dotProductLinearMap c x := by simpa [dotProductLinearMap_apply] using hxEq.symm
    · intro hx
      refine ⟨hx.1, ?_⟩
      have hx₀_le : dotProductLinearMap c x₀ ≤ dotProductLinearMap c x := hx.2 x₀ hx₀
      have hx_le : dotProductLinearMap c x ≤ dotProductLinearMap c x₀ := by
        simpa [dotProductLinearMap_apply, hx₀_eq] using hvalid' hx.1
      -- The exposing functional is constant on the equality slice.
      have hmap_eq : dotProductLinearMap c x = dotProductLinearMap c x₀ :=
        le_antisymm hx_le hx₀_le
      simpa [dotProductLinearMap_apply, hx₀_eq] using hmap_eq
  rw [hEq]
  exact ContinuousLinearMap.toExposed.isExposed

/-- Helper for Exercise 7.19: the direction of a tight equality slice lies in the kernel of its
defining linear functional. -/
private lemma equalitySetDirectionLeKer
    {P : Set (V → ℝ)} {c x₀ : V → ℝ} {δ : ℝ}
    (hx₀_eq : c ⬝ᵥ x₀ = δ) :
    (affineSpan ℝ {x : V → ℝ | x ∈ P ∧ c ⬝ᵥ x = δ}).direction ≤
      LinearMap.ker (dotProductLinearMap c) := by
  let F : Set (V → ℝ) := {x : V → ℝ | x ∈ P ∧ c ⬝ᵥ x = δ}
  let H : AffineSubspace ℝ (V → ℝ) :=
    AffineSubspace.mk' x₀ (LinearMap.ker (dotProductLinearMap c))
  have hF_le_H : F ⊆ H := by
    intro x hx
    change x ∈ H
    rw [AffineSubspace.mem_mk']
    refine LinearMap.mem_ker.2 ?_
    rcases hx with ⟨-, hx_eq⟩
    simp [dotProductLinearMap_apply, vsub_eq_sub, hx_eq, hx₀_eq]
  have h_aff_le : affineSpan ℝ F ≤ H := (affineSpan_le).2 hF_le_H
  -- Passing to directions identifies the ambient affine subspace with the kernel.
  simpa [H] using
    (AffineSubspace.direction_le h_aff_le :
      (affineSpan ℝ F).direction ≤ H.direction)

/-- Helper for Exercise 7.19: if a dot-product inequality holds on all stable-set vertices, it
holds on the whole stable-set polytope. -/
private lemma dotProductLeOfMemStableSetPolytope
    {c : V → ℝ} {δ : ℝ}
    (hvertex : ∀ s : Finset V, G.IsIndepSet s → c ⬝ᵥ stableSetIndicator s ≤ δ)
    {x : V → ℝ} (hx : x ∈ STAB(G)) :
    c ⬝ᵥ x ≤ δ := by
  let H : Set (V → ℝ) := {y : V → ℝ | c ⬝ᵥ y ≤ δ}
  have hconvex : Convex ℝ H := by
    -- A dot-product inequality cuts out a linear halfspace.
    simpa [H, dotProductLinearMap_apply] using
      convex_halfSpace_le (dotProductLinearMap c).isLinear δ
  have hsubset : convexHull ℝ (stableSetVertices G) ⊆ H := by
    refine convexHull_min ?_ hconvex
    intro y hy
    rw [mem_stableSetVertices_iff] at hy
    rcases hy with ⟨s, hs, rfl⟩
    exact hvertex s hs
  rw [stableSetPolytope_eq_convexHull] at hx
  exact hsubset hx

/-- Helper for Exercise 7.19: every point of `STAB(G)` has nonnegative coordinates. -/
private lemma coordinateNonneg_on_stableSetPolytope (v : V) {x : V → ℝ}
    (hx : x ∈ STAB(G)) :
    0 ≤ x v := by
  have hvalid :
      (-Pi.single v (1 : ℝ) : V → ℝ) ⬝ᵥ x ≤ 0 :=
    dotProductLeOfMemStableSetPolytope (G := G)
      (c := -Pi.single v (1 : ℝ)) (δ := 0)
      (hvertex := by
        intro s hs
        by_cases hv : v ∈ s
        · simp [stableSetIndicator, hv, dotProduct]
        · simp [stableSetIndicator, hv, dotProduct]) hx
  simpa [dotProduct, Pi.single_apply] using hvalid

/-- Helper for Exercise 7.19: `cliqueLinearMap K` is the linear functional `x ↦ ∑_{u ∈ K} x u`. -/
private def cliqueLinearMap (K : Finset V) : (V → ℝ) →ₗ[ℝ] ℝ :=
  ∑ u ∈ K, LinearMap.proj u

/-- Helper for Exercise 7.19: `cliqueLinearMap K` evaluates as `K.sum x`. -/
private lemma cliqueLinearMap_apply (K : Finset V) (x : V → ℝ) :
    cliqueLinearMap K x = K.sum x := by
  -- The clique functional is the coordinate sum over `K`.
  simp [cliqueLinearMap]

/-- Helper for Exercise 7.19: a stable set meets a clique in at most one vertex. -/
private lemma clique_sum_stableSetIndicator_le_one
    {K s : Finset V} (hK : G.IsClique K) (hs : G.IsIndepSet s) :
    K.sum (fun v ↦ stableSetIndicator s v) ≤ 1 := by
  have hsum :
      K.sum (fun v ↦ stableSetIndicator s v) = ((K.filter fun v ↦ v ∈ s).card : ℝ) := by
    -- Summing the `0/1` coordinates counts the clique vertices that lie in `s`.
    simp [stableSetIndicator, Finset.filter_mem_eq_inter]
  have hcard : (K.filter fun v ↦ v ∈ s).card ≤ 1 := by
    -- Two distinct vertices in the intersection would be both adjacent and nonadjacent.
    refine Finset.card_le_one_iff.2 ?_
    intro a b ha hb
    by_contra hab
    have haK : a ∈ K := (Finset.mem_filter.mp ha).1
    have hbK : b ∈ K := (Finset.mem_filter.mp hb).1
    have has : a ∈ s := (Finset.mem_filter.mp ha).2
    have hbs : b ∈ s := (Finset.mem_filter.mp hb).2
    exact (hs has hbs hab) (hK haK hbK hab)
  rw [hsum]
  exact_mod_cast hcard

/-- Helper for Exercise 7.19: clique inequalities are valid on the stable-set polytope. -/
private lemma clique_sum_le_one_of_mem_stableSetPolytope
    (K : Finset V) (hK : G.IsClique K) {x : V → ℝ}
    (hx : x ∈ STAB(G)) :
    K.sum x ≤ 1 := by
  let H : Set (V → ℝ) := {y : V → ℝ | K.sum y ≤ 1}
  have hconvex : Convex ℝ H := by
    -- The target set is a linear half-space.
    simpa [H, cliqueLinearMap_apply] using
      convex_halfSpace_le (cliqueLinearMap K).isLinear (1 : ℝ)
  have hsubset : convexHull ℝ (stableSetVertices G) ⊆ H := by
    refine convexHull_min ?_ hconvex
    intro y hy
    rw [mem_stableSetVertices_iff] at hy
    rcases hy with ⟨s, hs, rfl⟩
    exact clique_sum_stableSetIndicator_le_one (G := G) hK hs
  rw [stableSetPolytope_eq_convexHull] at hx
  exact hsubset hx

/-- Helper for Exercise 7.19: every vertex outside a maximal clique has a nonneighbor inside that
clique. -/
private lemma maximalCliqueExistsNonadjacentMem
    {K : Finset V} {v : V} (hK : Maximal G.IsClique K) (hv : v ∉ K) :
    ∃ w ∈ K, ¬ G.Adj v w := by
  by_contra h
  have hclique : G.IsClique K := hK.prop
  have hv_adj : ∀ w ∈ K, G.Adj v w := by
    intro w hw
    by_contra hvw
    exact h ⟨w, hw, hvw⟩
  have hinsert : G.IsClique (insert v (↑K : Set V)) := by
    rw [SimpleGraph.isClique_insert_of_notMem]
    · exact ⟨hclique, fun w hw ↦ hv_adj w hw⟩
    · simpa using hv
  exact hv (hK.mem_of_prop_insert hinsert)

/-- Helper for Exercise 7.19: the stable-set witness family attached to a maximal clique is
linearly independent. -/
private lemma cliqueWitnessLinearIndependent
    {K : Finset V} {W : V → Finset V}
    (h_singleton : ∀ v, v ∈ K → W v = {v})
    (h_mem : ∀ v, v ∉ K → v ∈ W v)
    (h_pair : ∀ v, v ∉ K → ∃ w ∈ K, W v = {v, w}) :
    LinearIndependent ℝ (fun v ↦ stableSetIndicator (W v)) := by
  rw [linearIndependent_iff']
  intro s g hsum v hv
  have hOutside : ∀ u ∈ s, u ∉ K → g u = 0 := by
    intro u hu huK
    have hcoord : ∑ t ∈ s, g t • stableSetIndicator (W t) u = 0 := by
      -- Evaluate the dependence relation at the outside coordinate `u`.
      simpa [Finset.sum_apply, Pi.smul_apply] using congrFun hsum u
    have hrest : ∀ t ∈ s, t ≠ u → g t • stableSetIndicator (W t) u = 0 := by
      intro t ht htu
      by_cases htK : t ∈ K
      · -- Clique witnesses contribute only on their own coordinate.
        rw [h_singleton t htK]
        simp [stableSetIndicator, htu.symm]
      · -- A distinct outside witness contributes only on its own outside coordinate.
        obtain ⟨w, hwK, hpair⟩ := h_pair t htK
        have huw : u ≠ w := by
          intro huw
          exact huK (huw ▸ hwK)
        rw [hpair, stableSetIndicatorPairOfNe (by
          intro htw
          exact htK (htw ▸ hwK))]
        simp [htu, huw]
    rw [Finset.sum_eq_single_of_mem u hu hrest] at hcoord
    have hself : stableSetIndicator (W u) u = 1 := by
      -- The witness for an outside vertex contains that vertex.
      rw [stableSetIndicator]
      exact if_pos (h_mem u huK)
    simpa [hself] using hcoord
  by_cases hKv : v ∈ K
  · have hcoord : ∑ t ∈ s, g t • stableSetIndicator (W t) v = 0 := by
      -- Evaluate at the clique coordinate `v`.
      simpa [Finset.sum_apply, Pi.smul_apply] using congrFun hsum v
    have hrest : ∀ t ∈ s, t ≠ v → g t • stableSetIndicator (W t) v = 0 := by
      intro t ht htv
      by_cases htK : t ∈ K
      · rw [h_singleton t htK]
        simp [stableSetIndicator, htv.symm]
      · rw [hOutside t ht htK, zero_smul]
    rw [Finset.sum_eq_single_of_mem v hv hrest] at hcoord
    have hself : stableSetIndicator (W v) v = 1 := by
      -- The clique witness at `v` is exactly `{v}`.
      rw [h_singleton v hKv]
      simp [stableSetIndicator]
    simpa [hself] using hcoord
  · exact hOutside v hv hKv

/-- Helper for Exercise 7.19: a maximal clique yields `|V|` affinely independent tight stable-set
witnesses for its clique face. -/
private theorem maximalCliqueWitnessFamily
    {K : Finset V} (hK : Maximal G.IsClique K) :
    ∃ W : V → Finset V,
      (∀ v, G.IsIndepSet (W v)) ∧
      (∀ v, K.sum (fun u ↦ stableSetIndicator (W v) u) = 1) ∧
      AffineIndependent ℝ (fun v ↦ stableSetIndicator (W v)) := by
  have hpartner :
      ∀ v, v ∉ K → ∃ w ∈ K, ¬ G.Adj v w := fun v hv ↦
        maximalCliqueExistsNonadjacentMem (G := G) hK hv
  choose partner partner_mem partner_nonadj using hpartner
  let witnessSets : V → Finset V := fun v ↦
    if hv : v ∈ K then {v} else {v, partner v hv}
  have hsingle : ∀ v, v ∈ K → witnessSets v = {v} := by
    intro v hv
    simp [witnessSets, hv]
  have hmem : ∀ v, v ∉ K → v ∈ witnessSets v := by
    intro v hv
    simp [witnessSets, hv]
  have hpair : ∀ v, v ∉ K → ∃ w ∈ K, witnessSets v = {v, w} := by
    intro v hv
    refine ⟨partner v hv, partner_mem v hv, ?_⟩
    simp [witnessSets, hv]
  have hindep : ∀ u, G.IsIndepSet (witnessSets u) := by
    intro u
    by_cases hu : u ∈ K
    · -- Clique vertices contribute singleton stable sets.
      rw [hsingle u hu]
      simp
    · -- Outside vertices are paired with a nonneighbor in the clique.
      have hneq : u ≠ partner u hu := by
        intro hEq
        exact hu (hEq ▸ partner_mem u hu)
      rw [show witnessSets u = {u, partner u hu} by simp [witnessSets, hu]]
      rw [SimpleGraph.isIndepSet_iff]
      intro a ha b hb hab
      simp at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact False.elim (hab rfl)
      · exact partner_nonadj u hu
      · simpa [G.symm] using partner_nonadj u hu
      · exact False.elim (hab rfl)
  have htight : ∀ v, K.sum (fun u ↦ stableSetIndicator (witnessSets v) u) = 1 := by
    intro v
    by_cases hv : v ∈ K
    · -- A clique singleton hits the clique sum exactly once.
      rw [hsingle v hv, stableSetIndicatorSingleton]
      simp [hv]
    · -- An outside witness contributes only through its chosen clique partner.
      have hneq : v ≠ partner v hv := by
        intro hEq
        exact hv (hEq ▸ partner_mem v hv)
      rw [show witnessSets v = {v, partner v hv} by simp [witnessSets, hv]]
      rw [stableSetIndicatorPairOfNe hneq]
      simp [Finset.sum_add_distrib, hv, partner_mem v hv]
  refine ⟨witnessSets, hindep, htight, ?_⟩
  -- Linear independence of the witness vectors implies affine independence.
  exact (cliqueWitnessLinearIndependent hsingle hmem hpair).affineIndependent

/-- Helper for Exercise 7.19: the coordinate-zero face at `v` contains the origin and the
singleton indicators away from `v`. -/
private lemma coordinateZeroFaceAffineIndependentFamily (v : V) :
    AffineIndependent ℝ
      (fun o : Option {u : V // u ≠ v} ↦
        Option.elim o (0 : V → ℝ) (fun u ↦ Pi.single u.1 1)) := by
  let U := {u : V // u ≠ v}
  let p : Option U → V → ℝ :=
    fun o ↦ Option.elim o (0 : V → ℝ) (fun u ↦ Pi.single u.1 1)
  let e : {o : Option U // o ≠ none} → U := fun o ↦
    match o with
    | ⟨none, hnone⟩ => False.elim (hnone rfl)
    | ⟨some u, _⟩ => u
  have he_injective : Function.Injective e := by
    intro a b hab
    rcases a with ⟨oa, hoa⟩
    rcases b with ⟨ob, hob⟩
    cases oa with
    | none => exact False.elim (hoa rfl)
    | some ua =>
        cases ob with
        | none => exact False.elim (hob rfl)
        | some ub =>
            simp only [ne_eq] at hab
            subst hab
            rfl
  have hcomp_injective : Function.Injective (fun i : {o : Option U // o ≠ none} ↦ (e i).1) := by
    intro a b hab
    apply he_injective
    exact Subtype.ext hab
  -- Affine independence again reduces to standard basis vectors.
  rw [affineIndependent_iff_linearIndependent_vsub ℝ p none]
  have hvsub :
      (fun i : {o : Option U // o ≠ none} ↦ (p i -ᵥ p none : V → ℝ)) =
        fun i : {o : Option U // o ≠ none} ↦ Pi.single (e i).1 1 := by
    funext i
    rcases i with ⟨o, ho⟩
    cases o with
    | none => exact False.elim (ho rfl)
    | some u =>
        simp [p, e, vsub_eq_sub]
  rw [hvsub]
  exact (Pi.linearIndependent_single_one V ℝ).comp _ hcomp_injective

/-- Helper for Exercise 7.19: the coordinate-zero face of `STAB(G)` is itself a facet. -/
private theorem coordinateZeroFace_isFacetOf [Nonempty V] (v : V) :
    IsFacetOf STAB(G) (coordinateZeroFace G v) := by
  let F : Set (V → ℝ) := coordinateZeroFace G v
  have hzero_mem : (0 : V → ℝ) ∈ F := by
    -- The empty stable set witnesses nonemptiness of the face.
    rw [mem_coordinateZeroFace_iff]
    refine ⟨?_, by simp⟩
    have h0 : stableSetIndicator (∅ : Finset V) ∈ STAB(G) :=
      stableSetIndicator_mem_stableSetPolytope (G := G) (by simp)
    simpa [stableSetIndicatorEmpty] using h0
  have hvalid : ∀ ⦃x : V → ℝ⦄, x ∈ STAB(G) → (-Pi.single v (1 : ℝ) : V → ℝ) ⬝ᵥ x ≤ 0 := by
    intro x hx
    have hxv : 0 ≤ x v := coordinateNonneg_on_stableSetPolytope (G := G) v hx
    simpa [dotProduct, Pi.single_apply] using (neg_nonpos.mpr hxv)
  have hF_exposed : IsExposed ℝ STAB(G) F := by
    -- The coordinate-zero slice is the equality case of the valid nonnegativity inequality.
    have hEq :
        F = {x : V → ℝ | x ∈ STAB(G) ∧ (-Pi.single v (1 : ℝ) : V → ℝ) ⬝ᵥ x = 0} := by
      ext x
      simp [F, coordinateZeroFace, dotProduct, Pi.single_apply]
    have hzero_stab : (0 : V → ℝ) ∈ STAB(G) :=
      (mem_coordinateZeroFace_iff G v 0).1 hzero_mem |>.1
    rw [hEq]
    exact equalitySetIsExposed hvalid hzero_stab (by simp)
  have hdir_le :
      (affineSpan ℝ F).direction ≤ LinearMap.ker (LinearMap.proj v) := by
    -- Differences of tight points preserve the vanishing `v`-coordinate.
    have hEq :
        F = {x : V → ℝ | x ∈ STAB(G) ∧ (Pi.single v (1 : ℝ)) ⬝ᵥ x = 0} := by
      ext x
      simp [F, coordinateZeroFace, dotProduct, Pi.single_apply]
    rw [hEq]
    simpa [dotProductLinearMap, dotProduct] using
      (equalitySetDirectionLeKer
        (P := STAB(G)) (c := Pi.single v (1 : ℝ)) (x₀ := 0) (δ := 0) (by simp) :
          (affineSpan ℝ {x : V → ℝ | x ∈ STAB(G) ∧ (Pi.single v (1 : ℝ)) ⬝ᵥ x = 0}).direction ≤
            LinearMap.ker (dotProductLinearMap (Pi.single v (1 : ℝ))))
  have hface_dim_lower :
      Fintype.card V - 1 ≤ Module.finrank ℝ (affineSpan ℝ F).direction := by
    let U := {u : V // u ≠ v}
    let p : Option U → V → ℝ :=
      fun o ↦ Option.elim o (0 : V → ℝ) (fun u ↦ Pi.single u.1 1)
    have hp_mem : Set.range p ⊆ F := by
      intro x hx
      rcases hx with ⟨o, rfl⟩
      cases o with
      | none =>
          simpa [F, p] using hzero_mem
      | some u =>
          have hu : stableSetIndicator ({u.1} : Finset V) ∈ STAB(G) :=
            stableSetIndicator_mem_stableSetPolytope (G := G) (by simp)
          have huFace : (Pi.single u.1 (1 : ℝ) : V → ℝ) ∈ coordinateZeroFace G v := by
            rw [mem_coordinateZeroFace_iff]
            refine ⟨?_, ?_⟩
            · simpa [stableSetIndicatorSingleton] using hu
            · simp [Pi.single_apply, u.2]
          simpa [F, p] using huFace
    have hp_affine : AffineIndependent ℝ p := by
      simpa [p] using coordinateZeroFaceAffineIndependentFamily (V := V) v
    have hp_dim :
        Module.finrank ℝ (affineSpan ℝ (Set.range p)).direction = Fintype.card V - 1 := by
      have hsubtype_card :
          Fintype.card U = Fintype.card V - 1 := by
        simpa [U] using (Fintype.card_subtype_compl (p := fun u : V ↦ u = v))
      have hcard : Fintype.card (Option U) = Fintype.card V := by
        calc
          Fintype.card (Option U) = Fintype.card U + 1 := by simp
          _ = (Fintype.card V - 1) + 1 := by rw [hsubtype_card]
          _ = Fintype.card V := by
            exact Nat.sub_add_cancel (Nat.succ_le_of_lt Fintype.card_pos)
      rw [direction_affineSpan]
      exact hp_affine.finrank_vectorSpan <| by
        simpa [hcard] using (Nat.sub_add_cancel (Nat.succ_le_of_lt Fintype.card_pos)).symm
    have hspan_le : affineSpan ℝ (Set.range p) ≤ affineSpan ℝ F :=
      affineSpan_mono ℝ hp_mem
    simpa [hp_dim] using Submodule.finrank_mono (AffineSubspace.direction_le hspan_le)
  have hproj_ne : (LinearMap.proj v : (V → ℝ) →ₗ[ℝ] ℝ) ≠ 0 := by
    intro hzero
    have hEval := congrArg (fun L : (V → ℝ) →ₗ[ℝ] ℝ ↦ L (Pi.single v 1)) hzero
    simp at hEval
  have hface_dim_upper :
      Module.finrank ℝ (affineSpan ℝ F).direction ≤ Fintype.card V - 1 := by
    simpa [finrankKerEqCardSubOne (V := V) hproj_ne] using Submodule.finrank_mono hdir_le
  have hpoly_dim :
      Module.finrank ℝ (affineSpan ℝ STAB(G)).direction = Fintype.card V := by
    rw [stableSetPolytopeAffineSpanEqTop (G := G), AffineSubspace.direction_top,
      finrank_top, Module.finrank_fintype_fun_eq_card]
  rw [isFacetOf_iff]
  refine ⟨⟨0, hzero_mem⟩, hF_exposed, ?_⟩
  have hface_dim :
      Module.finrank ℝ (affineSpan ℝ F).direction = Fintype.card V - 1 :=
    le_antisymm hface_dim_upper hface_dim_lower
  calc
    Module.finrank ℝ (affineSpan ℝ F).direction + 1 = Fintype.card V := by
      rw [hface_dim]
      exact Nat.sub_add_cancel (Nat.succ_le_of_lt Fintype.card_pos)
    _ = Module.finrank ℝ (affineSpan ℝ STAB(G)).direction := hpoly_dim.symm

/-- Helper for Exercise 7.19: in a full-dimensional ambient polytope, two facets coincide as soon
as one is contained in the other. -/
private lemma facet_eq_of_subset
    {P F H : Set (V → ℝ)}
    (hP_dim : Module.finrank ℝ (affineSpan ℝ P).direction = Fintype.card V)
    (hF : IsFacetOf P F)
    (hH : IsFacetOf P H)
    (hsubset : F ⊆ H) :
    F = H := by
  rcases hF with ⟨hF_nonempty, hF_exposed, hF_codim⟩
  rcases hH with ⟨hH_nonempty, hH_exposed, hH_codim⟩
  obtain ⟨xF, hxF⟩ := hF_nonempty
  have hxFH : xF ∈ H := hsubset hxF
  have hdim_eq :
      Module.finrank ℝ (affineSpan ℝ F).direction =
        Module.finrank ℝ (affineSpan ℝ H).direction := by
    omega
  have h_aff_le : affineSpan ℝ F ≤ affineSpan ℝ H := affineSpan_mono ℝ hsubset
  have hdir_eq :
      (affineSpan ℝ F).direction = (affineSpan ℝ H).direction := by
    exact Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le h_aff_le) hdim_eq
  have hspan_eq :
      affineSpan ℝ F = affineSpan ℝ H := by
    -- Equal directions and a common point identify the two affine spans.
    refine (AffineSubspace.eq_iff_direction_eq_of_mem
      (subset_affineSpan ℝ _ hxF) (subset_affineSpan ℝ _ hxFH)).2 hdir_eq
  obtain ⟨l, hF_eq⟩ := hF_exposed ⟨xF, hxF⟩
  have hxF_face : xF ∈ l.toExposed P := by
    simpa [hF_eq] using hxF
  have hxF_mem : xF ∈ P := hxF_face.1
  have hxF_max : ∀ y, y ∈ P → l y ≤ l xF := hxF_face.2
  have hlevel : ∀ ⦃x : V → ℝ⦄, x ∈ F → l x = l xF := by
    intro x hx
    have hx_face : x ∈ l.toExposed P := by
      simpa [hF_eq] using hx
    exact le_antisymm (hxF_max x hx_face.1) (hx_face.2 xF hxF_mem)
  have hlevel_aff :
      ∀ ⦃x : V → ℝ⦄, x ∈ affineSpan ℝ F → l x = l xF := by
    intro x hx
    refine affineSpan_induction (k := ℝ) (s := F) (p := fun y : V → ℝ ↦ l y = l xF) hx ?_ ?_
    · intro y hy
      exact hlevel hy
    · intro c u v w hu hv hw
      -- The exposing functional stays constant on the whole affine span of `F`.
      change l (c • (u - v) + w) = l xF
      calc
        l (c • (u - v) + w) = c * (l u - l v) + l w := by
            simp [map_add, map_sub]
        _ = l xF := by
            simp [hu, hv, hw]
  ext x
  constructor
  · intro hx
    exact hsubset hx
  · intro hx
    have hx_aff : x ∈ affineSpan ℝ F := by
      simpa [hspan_eq] using subset_affineSpan ℝ H hx
    have hx_level : l x = l xF := hlevel_aff hx_aff
    have hx_exposed : x ∈ l.toExposed P := by
      refine ⟨hH_exposed.subset hx, ?_⟩
      intro y hy
      calc
        l y ≤ l xF := hxF_max y hy
        _ = l x := hx_level.symm
    simpa [hF_eq] using hx_exposed

end CliqueFacetHelpers

section CyclicCountingHelpers

variable [Fintype V]

/-- Helper for Exercise 7.19: the successor index in the cyclic order on `C.length`. -/
private def cycleNextIndex (C : CycleSupport V) (i : Fin C.length) : Fin C.length :=
  finRotate C.length i

/-- Helper for Exercise 7.19: the predecessor index in the cyclic order on `C.length`. -/
private def cyclePrevIndex (C : CycleSupport V) (i : Fin C.length) : Fin C.length :=
  (finRotate C.length).symm i

/-- Helper for Exercise 7.19: the predecessor index maps back to `i` under one cyclic successor
step. -/
private lemma cycleNextIndex_prev (C : CycleSupport V) (i : Fin C.length) :
    cycleNextIndex C (cyclePrevIndex C i) = i := by
  -- Route correction: the cyclic predecessor/successor API is now normalized through
  -- `finRotate`, so the inverse law is a direct permutation identity.
  simpa [cycleNextIndex, cyclePrevIndex] using
    Equiv.apply_symm_apply (finRotate C.length) i

/-- Helper for Exercise 7.19: applying the predecessor to the cyclic successor returns the original
index. -/
private lemma cyclePrevIndex_next (C : CycleSupport V) (i : Fin C.length) :
    cyclePrevIndex C (cycleNextIndex C i) = i := by
  -- The inverse permutation identity gives the successor-then-predecessor cancellation.
  simpa [cycleNextIndex, cyclePrevIndex] using
    Equiv.symm_apply_apply (finRotate C.length) i

/-- Helper for Exercise 7.19: the predecessor of a cycle index is never the index itself. -/
private lemma cyclePrevIndex_ne (C : CycleSupport V) (i : Fin C.length) :
    cyclePrevIndex C i ≠ i := by
  -- `finRotate` moves every point when the cycle has length at least `2`, so its inverse cannot
  -- fix `i` either.
  have hmove : finRotate C.length i ≠ i := by
    have hsupport : i ∈ (finRotate C.length).support := by
      simpa [support_finRotate_of_le (le_trans (by decide : 2 ≤ 3) C.length_ge_three)]
    exact Equiv.Perm.mem_support.mp hsupport
  intro hprev
  have hfixed : finRotate C.length i = i := by
    have hnext := cycleNextIndex_prev C i
    rw [hprev] at hnext
    simpa [cycleNextIndex] using hnext
  exact hmove hfixed

/-- Helper for Exercise 7.19: the `i`-th cycle edge is the unordered pair of consecutive labelled
vertices. -/
private def cycleEdge (C : CycleSupport V) (i : Fin C.length) : Sym2 V :=
  s(C.verts i, C.verts (cycleNextIndex C i))

/-- Helper for Exercise 7.19: the indexed odd-cycle edge multipliers assign weight `1 / 2` to each
cycle edge occurrence. -/
private noncomputable def oddCycleEdgeMultiplier
    (C : CycleSupport V) : Sym2 V → ℝ :=
  fun e ↦ ∑ i : Fin C.length, if e = cycleEdge C i then (1 / 2 : ℝ) else 0

/-- Helper for Exercise 7.19: every indexed cycle edge is an actual edge of `G` when `C` is
contained in `G`. -/
private lemma cycleEdge_mem_edgeSet
    (C : CycleSupport V) (hC : C.IsContainedIn G) (i : Fin C.length) :
    cycleEdge C i ∈ G.edgeSet := by
  -- The containment hypothesis is exactly the adjacency statement for consecutive cycle
  -- vertices, and `finRotate` agrees with the original modulo-successor index.
  have hnext :
      cycleNextIndex C i =
        ⟨(i.1 + 1) % C.length,
          Nat.mod_lt _ (Nat.lt_of_lt_of_le (by decide) C.length_ge_three)⟩ := by
    simpa [cycleNextIndex, Fin.add_def] using (finRotate_apply (n := C.length) i)
  rw [cycleEdge, SimpleGraph.mem_edgeSet, hnext]
  exact hC i

/-- Helper for Exercise 7.19: the odd-cycle edge multipliers are coordinatewise nonnegative. -/
private lemma oddCycleEdgeMultiplier_nonneg
    (C : CycleSupport V) :
    ∀ e : Sym2 V, 0 ≤ oddCycleEdgeMultiplier C e := by
  intro e
  -- Each summand is either `0` or `1 / 2`.
  refine Finset.sum_nonneg ?_
  intro i hi
  by_cases h : e = cycleEdge C i
  · simp [oddCycleEdgeMultiplier, h]
  · simp [oddCycleEdgeMultiplier, h]

/-- Helper for Exercise 7.19: a nonzero odd-cycle edge multiplier can only occur on an actual edge
of `G`. -/
private lemma oddCycleEdgeMultiplier_support
    (C : CycleSupport V)
    (hC : C.IsContainedIn G) :
    ∀ e : Sym2 V, oddCycleEdgeMultiplier C e ≠ 0 → e ∈ G.edgeSet := by
  intro e he
  by_contra hedgenot
  have hnoMatch : ∀ i : Fin C.length, e ≠ cycleEdge C i := by
    intro i hi
    apply hedgenot
    rw [hi]
    exact cycleEdge_mem_edgeSet (G := G) C hC i
  have hzero : oddCycleEdgeMultiplier C e = 0 := by
    simp [oddCycleEdgeMultiplier, hnoMatch]
  exact he hzero

/-- Helper for Exercise 7.19: the sum of the odd-cycle edge multipliers is `|C| / 2`. -/
private lemma oddCycleEdgeMultiplier_sum
    (C : CycleSupport V) :
    ∑ e : Sym2 V, oddCycleEdgeMultiplier C e = (C.length : ℝ) / 2 := by
  -- Reindex the global `Sym2 V` sum by the cycle index family and collapse each inner singleton.
  calc
    ∑ e : Sym2 V, oddCycleEdgeMultiplier C e
        = ∑ e : Sym2 V, ∑ i : Fin C.length,
            if e = cycleEdge C i then (1 / 2 : ℝ) else 0 := by
              rfl
    _ = ∑ i : Fin C.length, ∑ e : Sym2 V,
            if e = cycleEdge C i then (1 / 2 : ℝ) else 0 := by
              rw [Finset.sum_comm]
    _ = ∑ i : Fin C.length, (1 / 2 : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp
    _ = (C.length : ℝ) / 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp [div_eq_mul_inv]

/-- Helper for Exercise 7.19: a cycle vertex belongs to exactly the two incident indexed cycle
edges, written in the successor-facing `finRotate` normal form. -/
private lemma mem_cycleEdge_iff
    (C : CycleSupport V) (i j : Fin C.length) :
    C.verts j ∈ cycleEdge C i ↔ i = j ∨ cycleNextIndex C i = j := by
  -- Route correction: classify the incident cycle edges through the rotate successor instead of
  -- reopening raw `%` arithmetic on indices.
  rw [cycleEdge, Sym2.mem_iff]
  constructor
  · intro hmem
    rcases hmem with hmem | hmem
    · exact Or.inl (C.verts.injective hmem).symm
    · exact Or.inr (C.verts.injective hmem).symm
  · intro hmem
    rcases hmem with rfl | hmem
    · exact Or.inl rfl
    · exact Or.inr (by rw [hmem])

/-- Helper for Exercise 7.19: vertices outside the cycle support lie on no indexed cycle edge. -/
private lemma not_mem_cycleEdge_of_not_vertex
    (C : CycleSupport V) {v : V}
    (hv : v ∉ C.vertexFinset) (i : Fin C.length) :
    v ∉ cycleEdge C i := by
  -- Each cycle edge endpoint is one of the labelled vertices of `C`.
  intro hmem
  rw [cycleEdge, Sym2.mem_iff] at hmem
  rcases hmem with hmem | hmem
  · exact hv <| (CycleSupport.mem_vertexFinset_iff C).2 ⟨i, hmem.symm⟩
  · exact hv <| (CycleSupport.mem_vertexFinset_iff C).2 ⟨cycleNextIndex C i, hmem.symm⟩

/-- Helper for Exercise 7.19: the odd-cycle edge multipliers aggregate to the indicator of
`C.vertexFinset`. -/
private lemma oddCycleEdgeMultiplier_coefficients
    (C : CycleSupport V) :
    (fun v ↦ ∑ e : Sym2 V, (if v ∈ e then oddCycleEdgeMultiplier C e else 0)) =
      stableSetIndicator C.vertexFinset := by
  classical
  funext v
  by_cases hv : v ∈ C.vertexFinset
  · rcases (CycleSupport.mem_vertexFinset_iff C).1 hv with ⟨j, rfl⟩
    have hincident :
        ∀ i : Fin C.length,
          C.verts j ∈ cycleEdge C i ↔ i = j ∨ i = cyclePrevIndex C j := by
      intro i
      rw [mem_cycleEdge_iff]
      constructor
      · intro hmem
        rcases hmem with rfl | hmem
        · exact Or.inl rfl
        · exact Or.inr <| by
            calc
              i = cyclePrevIndex C (cycleNextIndex C i) := by
                rw [cyclePrevIndex_next]
              _ = cyclePrevIndex C j := by rw [hmem]
      · intro hmem
        rcases hmem with rfl | hmem
        · exact Or.inl rfl
        · exact Or.inr <| by
            calc
              cycleNextIndex C i = cycleNextIndex C (cyclePrevIndex C j) := by rw [hmem]
              _ = j := cycleNextIndex_prev C j
    have htwo :
        (∑ i : Fin C.length, if C.verts j ∈ cycleEdge C i then (1 / 2 : ℝ) else 0) = 1 := by
      have hfilter :
          (Finset.univ.filter fun i : Fin C.length ↦ C.verts j ∈ cycleEdge C i) =
            {j, cyclePrevIndex C j} := by
        ext i
        simp [hincident i]
      rw [← Finset.sum_filter, hfilter]
      have hcard : ({j, cyclePrevIndex C j} : Finset (Fin C.length)).card = 2 :=
        Finset.card_pair (cyclePrevIndex_ne C j).symm
      rw [Finset.sum_const, hcard, nsmul_eq_mul]
      norm_num
    -- Swapping the edge/index sums reduces the coefficient at `C.verts j` to its two
    -- incident `1 / 2` contributions.
    calc
      ∑ e : Sym2 V, (if C.verts j ∈ e then oddCycleEdgeMultiplier C e else 0)
          = ∑ e : Sym2 V, (if C.verts j ∈ e then
              ∑ i : Fin C.length, if e = cycleEdge C i then (1 / 2 : ℝ) else 0
            else 0) := by
              rfl
      _ = ∑ e : Sym2 V, ∑ i : Fin C.length,
            (if C.verts j ∈ e then if e = cycleEdge C i then (1 / 2 : ℝ) else 0 else 0) := by
              refine Finset.sum_congr rfl ?_
              intro e he
              by_cases hmem : C.verts j ∈ e
              · simp [hmem]
              · simp [hmem]
      _ = ∑ i : Fin C.length, ∑ e : Sym2 V,
            (if C.verts j ∈ e then if e = cycleEdge C i then (1 / 2 : ℝ) else 0 else 0) := by
              rw [Finset.sum_comm]
      _ = ∑ i : Fin C.length, (if C.verts j ∈ cycleEdge C i then (1 / 2 : ℝ) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            by_cases hmem : C.verts j ∈ cycleEdge C i
            · rw [Finset.sum_eq_single (cycleEdge C i)]
              · simp [hmem]
              · intro x hx hxeq
                simp [hxeq]
              · simp
            · have hsum :
                (∑ x, if C.verts j ∈ x then if x = cycleEdge C i then (1 / 2 : ℝ) else 0 else 0) =
                  0 := by
                refine Finset.sum_eq_zero ?_
                intro x hx
                by_cases hxeq : x = cycleEdge C i
                · simp [hxeq, hmem]
                · simp [hxeq]
              simpa [hmem] using hsum
      _ = 1 := htwo
      _ = stableSetIndicator C.vertexFinset (C.verts j) := by
            simp [stableSetIndicator, CycleSupport.mem_vertexFinset_iff]
  · have hzero :
      (∑ i : Fin C.length, if v ∈ cycleEdge C i then (1 / 2 : ℝ) else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      simp [not_mem_cycleEdge_of_not_vertex (C := C) hv i]
    -- Outside the cycle support every incidence term vanishes, so the aggregated coefficient is
    -- the zero coordinate of the support indicator.
    calc
      ∑ e : Sym2 V, (if v ∈ e then oddCycleEdgeMultiplier C e else 0)
          = ∑ e : Sym2 V, (if v ∈ e then
              ∑ i : Fin C.length, if e = cycleEdge C i then (1 / 2 : ℝ) else 0
            else 0) := by
              rfl
      _ = ∑ e : Sym2 V, ∑ i : Fin C.length,
            (if v ∈ e then if e = cycleEdge C i then (1 / 2 : ℝ) else 0 else 0) := by
              refine Finset.sum_congr rfl ?_
              intro e he
              by_cases hmem : v ∈ e
              · simp [hmem]
              · simp [hmem]
      _ = ∑ i : Fin C.length, ∑ e : Sym2 V,
            (if v ∈ e then if e = cycleEdge C i then (1 / 2 : ℝ) else 0 else 0) := by
              rw [Finset.sum_comm]
      _ = ∑ i : Fin C.length, (if v ∈ cycleEdge C i then (1 / 2 : ℝ) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            by_cases hmem : v ∈ cycleEdge C i
            · rw [Finset.sum_eq_single (cycleEdge C i)]
              · simp [hmem]
              · intro x hx hxeq
                simp [hxeq]
              · simp
            · have hsum :
                (∑ x, if v ∈ x then if x = cycleEdge C i then (1 / 2 : ℝ) else 0 else 0) = 0 := by
                refine Finset.sum_eq_zero ?_
                intro x hx
                by_cases hxeq : x = cycleEdge C i
                · simp [hxeq, hmem]
                · simp [hxeq]
              simpa [hmem] using hsum
      _ = 0 := hzero
      _ = stableSetIndicator C.vertexFinset v := by
            simp [stableSetIndicator, hv]

/-- Helper for Exercise 7.19: the floored total odd-cycle multiplier equals the odd-cycle
right-hand side. -/
private lemma oddCycleEdgeMultiplier_floor
    (C : CycleSupport V)
    (hodd : Odd C.length) :
    ((Int.floor (∑ e : Sym2 V, oddCycleEdgeMultiplier C e) : ℤ) : ℝ) =
      odd_cycle_inequality_rhs C := by
  rcases hodd.exists_bit1 with ⟨m, hm⟩
  -- Rewrite the odd length as `2 * m + 1`, then evaluate the floor of `m + 1/2`.
  rw [oddCycleEdgeMultiplier_sum, odd_cycle_inequality_rhs_eq, hm]
  have hhalf : ((((2 * m + 1 : ℕ) : ℝ) / 2)) = (m : ℝ) + (1 / 2 : ℝ) := by
    field_simp
    norm_num
  rw [hhalf, Int.floor_natCast_add]
  norm_num

end CyclicCountingHelpers

section ChvatalCountingHelpers

variable [Fintype V]

/-- Helper for Exercise 7.19: the cyclic offset from `i` to `j` is the value of the modular
`Fin` difference `j - i`. -/
private lemma cyclic_offset_eq_sub_val {m : ℕ} [NeZero m] (i j : Fin m) :
    cyclic_offset i j = (j - i).1 := by
  -- Rewrite both sides to the same modular subtraction formula.
  simpa [cyclic_offset_eq] using
    (show ((j - i : Fin m) : ℕ) = (j.1 + m - i.1) % m by
      rw [Fin.sub_def])

/-- Helper for Exercise 7.19: exactly `W.width + 1` cyclic start indices place the labelled
vertex `j` inside a forward web block. -/
private lemma webForwardBlockStartCount
    (W : WebSupport V) (j : Fin W.length) :
    #{i : Fin W.length // cyclic_offset i j ≤ W.width} = W.width + 1 := by
  have hlen_pos : 0 < W.length := by
    omega
  haveI : NeZero W.length := ⟨Nat.ne_of_gt hlen_pos⟩
  have hwidth_le : W.width + 1 ≤ W.length := by
    omega
  -- Reindex the offset condition by the involution `i ↦ j - i`.
  let e :
      {i : Fin W.length // cyclic_offset i j ≤ W.width} ≃
        {t : Fin W.length // t < W.width + 1} where
    toFun i := ⟨j - i.1, by
      -- Convert the offset bound to the standard `< W.width + 1` bound on a `Fin` value.
      simpa [cyclic_offset_eq_sub_val, Nat.lt_succ_iff] using i.2⟩
    invFun t := ⟨j - t.1, by
      -- Applying the same involution again turns the target bound back into the offset bound.
      have htle : t.1.val ≤ W.width := Nat.lt_succ_iff.mp t.2
      simpa [cyclic_offset_eq_sub_val, Nat.lt_succ_iff, sub_sub_cancel] using htle⟩
    left_inv i := by
      simp
    right_inv t := by
      simp
  calc
    #{i : Fin W.length // cyclic_offset i j ≤ W.width}
        = #{t : Fin W.length // t < W.width + 1} := Fintype.card_congr e
    _ = min W.length (W.width + 1) := Fin.card_filter_val_lt (n := W.length) (m := W.width + 1)
    _ = W.width + 1 := min_eq_right hwidth_le

/-- Helper for Exercise 7.19: summing the constant web multiplier `1 / (k + 1)` over the `n`
labelled web blocks has floored total `⌊n / (k + 1)⌋`. -/
private lemma webBlockMultiplier_floor
    (W : WebSupport V) :
    ((Int.floor (∑ _i : Fin W.length, (1 / (W.width + 1 : ℝ))) : ℤ) : ℝ) =
      web_inequality_rhs W := by
  -- Collapse the constant sum to the real quotient `W.length / (W.width + 1)`.
  rw [web_inequality_rhs_eq]
  have hfloor :
      ((Int.floor ((W.length : ℝ) / (W.width + 1)) : ℤ) : ℝ) =
        (((W.length / (W.width + 1) : ℕ) : ℤ) : ℝ) := by
    -- Convert the standard floor/division identity from integers to reals.
    simpa using congrArg (fun z : ℤ ↦ (z : ℝ))
      (Int.floor_div_natCast (a := (W.length : ℝ)) (W.width + 1))
  calc
    ((Int.floor (∑ _i : Fin W.length, (1 / (W.width + 1 : ℝ))) : ℤ) : ℝ)
        = ((Int.floor ((W.length : ℝ) / (W.width + 1)) : ℤ) : ℝ) := by
            -- There are exactly `W.length` equal summands.
            simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm,
              mul_assoc]
    _ = (((W.length / (W.width + 1) : ℕ) : ℤ) : ℝ) := hfloor
    _ = web_inequality_rhs W := by simp [web_inequality_rhs_eq]

/-- Helper for Exercise 7.19: for an odd antihole support, summing the constant multiplier
`2 / (|H| - 1)` over the `|H|` cyclic clique candidates has floored total `2`. -/
private lemma antiholeCliqueMultiplier_floor
    (H : AntiholeSupport V)
    (hodd : Odd H.length) :
    ((Int.floor (∑ _i : Fin H.length, (2 / (H.length - 1 : ℝ))) : ℤ) : ℝ) = 2 := by
  rcases hodd.exists_bit1 with ⟨m, hm⟩
  have hm_two_le : 2 ≤ m := by
    -- The odd antihole has at least five vertices, so the half-length parameter is at least two.
    omega
  have hm_pos : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm_two_le
  have hm_ne : (m : ℝ) ≠ 0 := by positivity
  have hfrac_floor : Int.floor ((1 : ℝ) / m) = 0 := by
    -- The residual fraction lies in `[0, 1)`, so its floor is zero.
    rw [Int.floor_eq_iff]
    constructor
    · positivity
    · have hm_pos_real : (0 : ℝ) < m := by exact_mod_cast hm_pos
      have hm_one_le_real : (1 : ℝ) ≤ m := by exact_mod_cast hm_pos
      rw [show (0 : ℤ) + 1 = (1 : ℤ) by norm_num, Int.cast_one]
      rw [div_lt_iff hm_pos_real]
      linarith
  have hsum :
      (∑ _i : Fin H.length, (2 / (H.length - 1 : ℝ))) = (2 : ℝ) + 1 / m := by
    -- Rewrite the odd length as `2 * m + 1` and simplify the constant sum explicitly.
    rw [hm]
    have hsub : (2 * m + 1 - 1 : ℕ) = 2 * m := by omega
    rw [hsub]
    calc
      (∑ _i : Fin (2 * m + 1), (2 / (2 * m : ℝ)))
          = ((2 * m + 1 : ℕ) : ℝ) * (2 / (2 * m : ℝ)) := by
              simp [Finset.sum_const, nsmul_eq_mul]
      _ = (2 : ℝ) + 1 / m := by
            field_simp [hm_ne]
            ring
  calc
    ((Int.floor (∑ _i : Fin H.length, (2 / (H.length - 1 : ℝ))) : ℤ) : ℝ)
        = ((Int.floor ((2 : ℝ) + 1 / m) : ℤ) : ℝ) := by rw [hsum]
    _ = (((2 + Int.floor ((1 : ℝ) / m) : ℤ)) : ℝ) := by
          rw [Int.floor_natCast_add]
    _ = 2 := by simpa [hfrac_floor]

end ChvatalCountingHelpers

section FacetStatements

variable [Fintype V]

/-- Exercise 7.19 (1). For a clique `K` of `G`, the clique inequality `∑_{v ∈ K} x_v ≤ 1` cuts
out a facet of `STAB(G)` if and only if `K` is a maximal clique. -/
theorem exercise_7_19_clique_inequality_facet_defining_iff_maximal_clique
    [Nonempty V] (K : Finset V) (hK : G.IsClique K) :
    IsFacetOf STAB(G) (cliqueFace G K) ↔
      Maximal G.IsClique K := by
  constructor
  · intro hFacet
    by_contra hmax
    have hmono :
        ∀ ⦃s t : Set V⦄, G.IsClique t → s ⊆ t → G.IsClique s := by
      intro s t ht hst
      exact ht.subset hst
    rcases Set.exists_insert_of_not_maximal (P := G.IsClique) hmono hK hmax with
      ⟨v, hvK, hK'⟩
    have hK'fin : G.IsClique (insert v K : Finset V) := by
      simpa using hK'
    have hsubset_coord :
        cliqueFace G K ⊆ coordinateZeroFace G v := by
      intro x hx
      rcases (mem_cliqueFace_iff G K x).1 hx with ⟨hxStab, hxK⟩
      have hK'le : (insert v K).sum x ≤ 1 :=
        clique_sum_le_one_of_mem_stableSetPolytope (G := G) (insert v K) hK'fin hxStab
      have hxv_nonneg : 0 ≤ x v :=
        coordinateNonneg_on_stableSetPolytope (G := G) v hxStab
      have hxv_zero : x v = 0 := by
        rw [Finset.sum_insert hvK] at hK'le
        linarith
      exact (mem_coordinateZeroFace_iff G v x).2 ⟨hxStab, hxv_zero⟩
    have hcoordFacet : IsFacetOf STAB(G) (coordinateZeroFace G v) :=
      coordinateZeroFace_isFacetOf (G := G) v
    have hpoly_dim :
        Module.finrank ℝ (affineSpan ℝ STAB(G)).direction = Fintype.card V := by
      rw [stableSetPolytopeAffineSpanEqTop (G := G), AffineSubspace.direction_top,
        finrank_top, Module.finrank_fintype_fun_eq_card]
    have hEq :
        cliqueFace G K = coordinateZeroFace G v :=
      facet_eq_of_subset (V := V) (hP_dim := hpoly_dim) hFacet hcoordFacet hsubset_coord
    have hzero_coord : (0 : V → ℝ) ∈ coordinateZeroFace G v := by
      rw [mem_coordinateZeroFace_iff]
      refine ⟨?_, by simp⟩
      have h0 : stableSetIndicator (∅ : Finset V) ∈ STAB(G) :=
        stableSetIndicator_mem_stableSetPolytope (G := G) (by simp)
      simpa [stableSetIndicatorEmpty] using h0
    have hzero_face : (0 : V → ℝ) ∈ cliqueFace G K := by
      simpa [hEq] using hzero_coord
    have hsum_zero : K.sum (0 : V → ℝ) = 1 :=
      (mem_cliqueFace_iff G K 0).1 hzero_face |>.2
    simp at hsum_zero
  · intro hmax
    let F : Set (V → ℝ) := cliqueFace G K
    let c : V → ℝ := stableSetIndicator K
    have hvalid : ∀ ⦃x : V → ℝ⦄, x ∈ STAB(G) → c ⬝ᵥ x ≤ 1 := by
      intro x hx
      simpa [c, stableSetIndicator_dotProduct] using
        clique_sum_le_one_of_mem_stableSetPolytope (G := G) K hK hx
    obtain ⟨W, hW_indep, hW_tight, hW_affine⟩ :=
      maximalCliqueWitnessFamily (G := G) hmax
    have hF_nonempty : F.Nonempty := by
      refine ⟨stableSetIndicator (W (Classical.choice ‹Nonempty V›)), ?_⟩
      rw [mem_cliqueFace_iff]
      refine ⟨stableSetIndicator_mem_stableSetPolytope (G := G) (hW_indep _), ?_⟩
      simpa using hW_tight _
    have hF_exposed : IsExposed ℝ STAB(G) F := by
      obtain ⟨v0⟩ := ‹Nonempty V›
      have hx0 : stableSetIndicator (W v0) ∈ STAB(G) :=
        stableSetIndicator_mem_stableSetPolytope (G := G) (hW_indep v0)
      have hx0_eq : c ⬝ᵥ stableSetIndicator (W v0) = 1 := by
        simpa [c, stableSetIndicator_dotProduct] using hW_tight v0
      have hEq :
          F = {x : V → ℝ | x ∈ STAB(G) ∧ c ⬝ᵥ x = 1} := by
        ext x
        simp [F, c, stableSetIndicator_dotProduct]
      rw [hEq]
      exact equalitySetIsExposed hvalid hx0 hx0_eq
    have hface_dim_lower :
        Fintype.card V - 1 ≤ Module.finrank ℝ (affineSpan ℝ F).direction := by
      let p : V → V → ℝ := fun v ↦ stableSetIndicator (W v)
      have hp_mem : Set.range p ⊆ F := by
        intro x hx
        rcases hx with ⟨v, rfl⟩
        rw [mem_cliqueFace_iff]
        refine ⟨stableSetIndicator_mem_stableSetPolytope (G := G) (hW_indep v), ?_⟩
        simpa [p] using hW_tight v
      have hspan_le : affineSpan ℝ (Set.range p) ≤ affineSpan ℝ F :=
        affineSpan_mono ℝ hp_mem
      have hp_dim :
          Module.finrank ℝ (affineSpan ℝ (Set.range p)).direction = Fintype.card V - 1 := by
        rw [direction_affineSpan]
        exact hW_affine.finrank_vectorSpan <|
          (Nat.sub_add_cancel (Nat.succ_le_of_lt Fintype.card_pos)).symm
      simpa [hp_dim] using
        Submodule.finrank_mono (AffineSubspace.direction_le hspan_le)
    have hdir_le :
        (affineSpan ℝ F).direction ≤ LinearMap.ker (dotProductLinearMap c) := by
      obtain ⟨v0⟩ := ‹Nonempty V›
      have hx0_eq : c ⬝ᵥ stableSetIndicator (W v0) = 1 := by
        simpa [c, stableSetIndicator_dotProduct] using hW_tight v0
      have hEq :
          F = {x : V → ℝ | x ∈ STAB(G) ∧ c ⬝ᵥ x = 1} := by
        ext x
        simp [F, c, stableSetIndicator_dotProduct]
      rw [hEq]
      exact equalitySetDirectionLeKer (P := STAB(G)) (c := c)
        (x₀ := stableSetIndicator (W v0)) (δ := 1) hx0_eq
    have hLinear_nonzero : dotProductLinearMap c ≠ 0 := by
      have hmono :
          ∀ ⦃s t : Set V⦄, G.IsClique t → s ⊆ t → G.IsClique s := by
        intro s t ht hst
        exact ht.subset hst
      have hmax_insert :=
        (Set.maximal_iff_forall_insert (P := G.IsClique) hmono).1 hmax
      have hK_nonempty : K.Nonempty := by
        by_contra hKempty
        have hKeq : K = ∅ := Finset.not_nonempty_iff_eq_empty.mp hKempty
        obtain ⟨v⟩ := ‹Nonempty V›
        have hsingle : G.IsClique (insert v (↑K : Set V)) := by
          simpa [hKeq] using
            (SimpleGraph.isClique_singleton (G := G) v)
        exact hmax_insert.2 v (by simpa [hKeq]) hsingle
      rcases hK_nonempty with ⟨v, hv⟩
      intro hzero
      have hvalue := congrArg (fun L : (V → ℝ) →ₗ[ℝ] ℝ ↦ L (Pi.single v 1)) hzero
      simp [c, dotProductLinearMap, stableSetIndicator, hv] at hvalue
    have hface_dim_upper :
        Module.finrank ℝ (affineSpan ℝ F).direction ≤ Fintype.card V - 1 := by
      simpa [finrankKerEqCardSubOne (V := V) hLinear_nonzero] using
        Submodule.finrank_mono hdir_le
    have hpoly_dim :
        Module.finrank ℝ (affineSpan ℝ STAB(G)).direction = Fintype.card V := by
      rw [stableSetPolytopeAffineSpanEqTop (G := G), AffineSubspace.direction_top,
        finrank_top, Module.finrank_fintype_fun_eq_card]
    rw [isFacetOf_iff]
    refine ⟨hF_nonempty, hF_exposed, ?_⟩
    have hface_dim :
        Module.finrank ℝ (affineSpan ℝ F).direction = Fintype.card V - 1 :=
      le_antisymm hface_dim_upper hface_dim_lower
    calc
      Module.finrank ℝ (affineSpan ℝ F).direction + 1 = Fintype.card V := by
        rw [hface_dim]
        exact Nat.sub_add_cancel (Nat.succ_le_of_lt Fintype.card_pos)
      _ = Module.finrank ℝ (affineSpan ℝ STAB(G)).direction := hpoly_dim.symm

/-- Exercise 7.19 (3). For an odd cycle support `C` contained in `G`, the odd-cycle inequality on
`C.vertexFinset` cuts out a facet of `STAB(G)` restricted to `C.vertexFinset` if and only if `C`
is chordless in `G`. -/
theorem exercise_7_19_odd_cycle_inequality_facet_defining_iff_chordless
    (C : CycleSupport V)
    (hC : C.IsContainedIn G)
    (hodd : Odd C.length) :
    IsFacetOf
      (STAB(G) ∩ zero_outside C.vertexFinset)
      (oddCycleFace G C) ↔
      C.IsChordlessIn G := by
  -- Route correction: the remaining blocker is no longer the odd-cycle Chvatal certificate.
  -- What is still missing is the facet-specific kernel generation on the supported ambient
  -- polytope, together with the nonchordless obstruction by a proper odd subcycle equality.
  sorry

/-- Exercise 7.19 (5). If an odd antihole support `H` is induced in `G`, then the antihole
inequality cuts out a facet of `STAB(G)` restricted to `H.vertexFinset`. -/
theorem exercise_7_19_antihole_inequality_facet_defining
    (H : AntiholeSupport V)
    (hodd : Odd H.length)
    (hInd : H.IsInducedIn G) :
    IsFacetOf
      (STAB(G) ∩ zero_outside H.vertexFinset)
      (antiholeFace G H) := by
  -- Route correction: the remaining blocker is the face-direction generator family from the
  -- consecutive stable pairs of the induced odd antihole, not the surrounding codimension-one
  -- shell. Once those direction generators are in place, the final `IsFacetOf` assembly is
  -- the same supported-kernel argument as in the clique case.
  sorry

end FacetStatements

section ChvatalStatements

variable [Fintype V]

noncomputable local instance : DecidableEq V := Classical.decEq V

/-- Exercise 7.19 (2). For an odd cycle support `C` contained in `G`, the odd-cycle inequality on
`C.vertexFinset` is a Chvatal inequality for the edge relaxation `Q(G)`. -/
theorem exercise_7_19_odd_cycle_inequality_is_chvatal
    (C : CycleSupport V)
    (hC : C.IsContainedIn G)
    (hodd : Odd C.length) :
    IsEdgeRelaxationChvatalInequality
      G
      (stableSetIndicator C.vertexFinset)
      (odd_cycle_inequality_rhs C) := by
  classical
  rw [isEdgeRelaxationChvatalInequality_iff]
  refine ⟨oddCycleEdgeMultiplier C, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The cycle certificate uses only nonnegative `1 / 2` edge multipliers.
    exact oddCycleEdgeMultiplier_nonneg (C := C)
  · -- Nonzero multipliers occur only on the actual cycle edges of `G`.
    exact oddCycleEdgeMultiplier_support (G := G) C hC
  · -- The slack function is identically zero.
    intro v
    simp
  · -- Each coefficient of the stable-set indicator is integral.
    intro v
    by_cases hv : v ∈ C.vertexFinset
    · exact ⟨1, by simp [stableSetIndicator, hv]⟩
    · exact ⟨0, by simp [stableSetIndicator, hv]⟩
  · -- The aggregated incidence vector is exactly the cycle-support indicator.
    simpa [oddCycleEdgeMultiplier_coefficients]
  · -- The floored total multiplier is the odd-cycle right-hand side.
    exact (oddCycleEdgeMultiplier_floor C hodd).symm

/-- Helper for Exercise 7.19: the forward web block starting at `i` contains exactly the labelled
vertices whose forward offset from `i` is at most `W.width`. -/
private noncomputable def webForwardBlock
    (W : WebSupport V) (i : Fin W.length) : Finset V :=
  (Finset.univ.filter fun j : Fin W.length ↦ cyclic_offset i j ≤ W.width).map W.verts

/-- Helper for Exercise 7.19: a labelled vertex lies in the forward block from `i` exactly when
its cyclic offset from `i` is at most `W.width`. -/
private lemma mem_webForwardBlock_iff
    (W : WebSupport V) (i j : Fin W.length) :
    W.verts j ∈ webForwardBlock W i ↔ cyclic_offset i j ≤ W.width := by
  -- Unfold the filtered map and use injectivity of `W.verts` to recover the index condition.
  simp [webForwardBlock]

/-- Helper for Exercise 7.19: two vertices lying in the same forward block have mutual cyclic
distance at most `W.width` in one direction. -/
private lemma cyclicOffset_le_of_common_webStart
    (W : WebSupport V) {i j k : Fin W.length}
    (hj : cyclic_offset i j ≤ W.width)
    (hk : cyclic_offset i k ≤ W.width) :
    cyclic_offset j k ≤ W.width ∨ cyclic_offset k j ≤ W.width := by
  have hlen_pos : 0 < W.length := by
    omega
  letI : NeZero W.length := ⟨Nat.ne_of_gt hlen_pos⟩
  -- Normalize each cyclic offset to `Fin` subtraction and let `fin_omega` compare the offsets.
  rw [cyclic_offset_eq_sub_val, cyclic_offset_eq_sub_val, cyclic_offset_eq_sub_val,
    cyclic_offset_eq_sub_val] at hj hk ⊢
  fin_omega

/-- Helper for Exercise 7.19: each forward web block is a clique of `G` when `W` is contained in
`G`. -/
private lemma webForwardBlock_isClique
    (W : WebSupport V) (hW : W.IsContainedIn G) (i : Fin W.length) :
    G.IsClique (webForwardBlock W i) := by
  -- Compare two block vertices through their common start index `i`, then invoke the web
  -- adjacency rule on the resulting bounded cyclic distance.
  intro a ha b hb hab
  rcases Finset.mem_map.mp ha with ⟨j, hj, rfl⟩
  rcases Finset.mem_map.mp hb with ⟨k, hk, rfl⟩
  have hjle : cyclic_offset i j ≤ W.width := by
    simpa using (Finset.mem_filter.mp hj).2
  have hkle : cyclic_offset i k ≤ W.width := by
    simpa using (Finset.mem_filter.mp hk).2
  have hjk :
      cyclic_offset j k ≤ W.width ∨ cyclic_offset k j ≤ W.width :=
    cyclicOffset_le_of_common_webStart (W := W) hjle hkle
  have hne : j ≠ k := by
    intro hEq
    apply hab
    simpa [hEq]
  exact hW j k hne hjk

/-- Helper for Exercise 7.19: vertices outside `W.vertexFinset` do not belong to any forward web
block. -/
private lemma not_mem_webForwardBlock_of_not_vertex
    (W : WebSupport V) {v : V} (hv : v ∉ W.vertexFinset) (i : Fin W.length) :
    v ∉ webForwardBlock W i := by
  -- Every block vertex is one of the labelled vertices of `W`.
  intro hmem
  rcases Finset.mem_map.mp hmem with ⟨j, -, hj⟩
  exact hv ((WebSupport.mem_vertexFinset_iff W).2 ⟨j, hj.symm⟩)

/-- Helper for Exercise 7.19: the web Chvatal certificate assigns multiplier `1 / (k + 1)` to
each forward block occurrence. -/
private noncomputable def webForwardBlockMultiplier
    (W : WebSupport V) : Finset V → ℝ :=
  fun K ↦ ∑ i : Fin W.length, if K = webForwardBlock W i then (1 / (W.width + 1 : ℝ)) else 0

/-- Helper for Exercise 7.19: the web block multipliers are coordinatewise nonnegative. -/
private lemma webForwardBlockMultiplier_nonneg
    (W : WebSupport V) :
    ∀ K : Finset V, 0 ≤ webForwardBlockMultiplier W K := by
  intro K
  -- Every indexed contribution is either `0` or the positive constant `1 / (k + 1)`.
  refine Finset.sum_nonneg ?_
  intro i hi
  by_cases hEq : K = webForwardBlock W i
  · simp [webForwardBlockMultiplier, hEq]
  · simp [webForwardBlockMultiplier, hEq]

/-- Helper for Exercise 7.19: a nonzero web multiplier can only occur on a clique of `G`. -/
private lemma webForwardBlockMultiplier_support
    (W : WebSupport V) (hW : W.IsContainedIn G) :
    ∀ K : Finset V, webForwardBlockMultiplier W K ≠ 0 → G.IsClique K := by
  intro K hK
  by_contra hnotClique
  have hnoMatch : ∀ i : Fin W.length, K ≠ webForwardBlock W i := by
    intro i hEq
    apply hnotClique
    simpa [hEq] using webForwardBlock_isClique (G := G) W hW i
  have hzero : webForwardBlockMultiplier W K = 0 := by
    simp [webForwardBlockMultiplier, hnoMatch]
  exact hK hzero

/-- Helper for Exercise 7.19: for a fixed start index `i`, summing over all clique variables
collapses to the single forward block `webForwardBlock W i`. -/
private lemma webForwardBlockMultiplier_inner
    (W : WebSupport V) (i : Fin W.length) (v : V) :
    ∑ K : Finset V,
      (if K = webForwardBlock W i then (1 / (W.width + 1 : ℝ)) else 0) *
        (if v ∈ K then 1 else 0) =
      if v ∈ webForwardBlock W i then (1 / (W.width + 1 : ℝ)) else 0 := by
  by_cases hmem : v ∈ webForwardBlock W i
  · -- Only the exact forward block contributes, and there it contributes the constant multiplier.
    rw [Finset.sum_eq_single (webForwardBlock W i)]
    · simp [hmem]
    · intro K hK hne
      simp [hne]
    · simp
  · -- If `v` is outside the block, every clique term vanishes.
    have hsum :
        (∑ K : Finset V,
          (if K = webForwardBlock W i then (1 / (W.width + 1 : ℝ)) else 0) *
            (if v ∈ K then 1 else 0)) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro K hK
      by_cases hEq : K = webForwardBlock W i
      · simp [hEq, hmem]
      · simp [hEq]
    simpa [hmem] using hsum

/-- Helper for Exercise 7.19: the aggregated web block coefficients equal the indicator of the
web support. -/
private lemma webForwardBlockMultiplier_coefficients
    (W : WebSupport V) :
    (fun v ↦ ∑ K : Finset V,
      webForwardBlockMultiplier W K * (if v ∈ K then 1 else 0)) =
      stableSetIndicator W.vertexFinset := by
  classical
  funext v
  by_cases hv : v ∈ W.vertexFinset
  · rcases (WebSupport.mem_vertexFinset_iff W).1 hv with ⟨j, rfl⟩
    -- For a support vertex, the coefficient is the constant block weight times the number of
    -- starts whose forward block contains that vertex.
    calc
      ∑ K : Finset V, webForwardBlockMultiplier W K * (if W.verts j ∈ K then 1 else 0)
          = ∑ K : Finset V,
              (∑ i : Fin W.length,
                (if K = webForwardBlock W i then (1 / (W.width + 1 : ℝ)) else 0) *
                  (if W.verts j ∈ K then 1 else 0)) := by
                simp [webForwardBlockMultiplier, Finset.mul_sum]
      _ = ∑ i : Fin W.length, ∑ K : Finset V,
            (if K = webForwardBlock W i then (1 / (W.width + 1 : ℝ)) else 0) *
              (if W.verts j ∈ K then 1 else 0) := by
              rw [Finset.sum_comm]
      _ = ∑ i : Fin W.length,
            if W.verts j ∈ webForwardBlock W i then (1 / (W.width + 1 : ℝ)) else 0 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact webForwardBlockMultiplier_inner (W := W) i (W.verts j)
      _ = ∑ i in Finset.univ.filter
            (fun i : Fin W.length ↦ cyclic_offset i j ≤ W.width),
            (1 / (W.width + 1 : ℝ)) := by
              simpa [mem_webForwardBlock_iff] using
                (Finset.sum_filter
                  (s := (Finset.univ : Finset (Fin W.length)))
                  (p := fun i : Fin W.length ↦ W.verts j ∈ webForwardBlock W i)
                  (f := fun _ : Fin W.length ↦ (1 / (W.width + 1 : ℝ)))).symm
      _ = ∑ i : {i : Fin W.length // cyclic_offset i j ≤ W.width},
            (1 / (W.width + 1 : ℝ)) := by
              simpa using
                (Finset.sum_subtype_eq_sum_filter
                  (s := (Finset.univ : Finset (Fin W.length)))
                  (p := fun i : Fin W.length ↦ cyclic_offset i j ≤ W.width)
                  (f := fun _ : Fin W.length ↦ (1 / (W.width + 1 : ℝ)))).symm
      _ = (W.width + 1 : ℝ) * (1 / (W.width + 1 : ℝ)) := by
            simp [Finset.sum_const, nsmul_eq_mul, webForwardBlockStartCount (W := W) j]
      _ = 1 := by
            field_simp
      _ = stableSetIndicator W.vertexFinset (W.verts j) := by
            simp [stableSetIndicator, WebSupport.mem_vertexFinset_iff]
  · -- Outside the support every forward block term vanishes, so the coefficient is zero.
    have hzero :
        ∑ i : Fin W.length,
          if v ∈ webForwardBlock W i then (1 / (W.width + 1 : ℝ)) else 0 = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      simp [not_mem_webForwardBlock_of_not_vertex (W := W) hv i]
    calc
      ∑ K : Finset V, webForwardBlockMultiplier W K * (if v ∈ K then 1 else 0)
          = ∑ K : Finset V,
              (∑ i : Fin W.length,
                (if K = webForwardBlock W i then (1 / (W.width + 1 : ℝ)) else 0) *
                  (if v ∈ K then 1 else 0)) := by
                simp [webForwardBlockMultiplier, Finset.mul_sum]
      _ = ∑ i : Fin W.length, ∑ K : Finset V,
            (if K = webForwardBlock W i then (1 / (W.width + 1 : ℝ)) else 0) *
              (if v ∈ K then 1 else 0) := by
              rw [Finset.sum_comm]
      _ = ∑ i : Fin W.length,
            if v ∈ webForwardBlock W i then (1 / (W.width + 1 : ℝ)) else 0 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact webForwardBlockMultiplier_inner (W := W) i v
      _ = 0 := hzero
      _ = stableSetIndicator W.vertexFinset v := by
            simp [stableSetIndicator, hv]

/-- Helper for Exercise 7.19: the total web block multiplier is the constant multiplier summed
over all labelled starts. -/
private lemma webForwardBlockMultiplier_sum
    (W : WebSupport V) :
    ∑ K : Finset V, webForwardBlockMultiplier W K =
      ∑ i : Fin W.length, (1 / (W.width + 1 : ℝ)) := by
  -- Swap the sums and collapse each inner singleton over `Finset V`.
  calc
    ∑ K : Finset V, webForwardBlockMultiplier W K
        = ∑ K : Finset V,
            ∑ i : Fin W.length,
              if K = webForwardBlock W i then (1 / (W.width + 1 : ℝ)) else 0 := by
              rfl
    _ = ∑ i : Fin W.length, ∑ K : Finset V,
          if K = webForwardBlock W i then (1 / (W.width + 1 : ℝ)) else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ i : Fin W.length, (1 / (W.width + 1 : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp

/-- Helper for Exercise 7.19: the `a`-th positive even cyclic offset used in the odd antihole
clique certificate. -/
private def antiholeShift
    (H : AntiholeSupport V) (a : Fin ((H.length - 1) / 2)) : Fin H.length :=
  ⟨2 * (a.1 + 1), by
    -- The `((H.length - 1) / 2)` choices give exactly the positive even offsets below `H.length`.
    have ha : a.1 < (H.length - 1) / 2 := a.2
    omega⟩

/-- Helper for Exercise 7.19: the alternating clique starting at `i` consists of the labelled
vertices at positive even offsets from `i`. -/
private noncomputable def antiholeAlternatingClique
    (H : AntiholeSupport V) (i : Fin H.length) : Finset V :=
  Finset.univ.image fun a : Fin ((H.length - 1) / 2) ↦ H.verts (i + antiholeShift H a)

/-- Helper for Exercise 7.19: a labelled vertex belongs to the alternating antihole clique
starting at `i` exactly when it is reached by one of the chosen even offsets. -/
private lemma mem_antiholeAlternatingClique_iff
    (H : AntiholeSupport V) (i j : Fin H.length) :
    H.verts j ∈ antiholeAlternatingClique H i ↔
      ∃ a : Fin ((H.length - 1) / 2), i + antiholeShift H a = j := by
  -- Unfold the image owner and use injectivity of the antihole labelling.
  constructor
  · intro hj
    rcases Finset.mem_image.mp hj with ⟨a, -, ha⟩
    exact ⟨a, H.verts.injective ha⟩
  · rintro ⟨a, rfl⟩
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩

/-- Exercise 7.19 (4). For an odd antihole support `H` contained in `G`, the antihole inequality
`∑_{v ∈ H.vertexFinset} x_v ≤ 2` is a Chvatal inequality for the clique relaxation `K(G)`. -/
theorem exercise_7_19_antihole_inequality_is_chvatal
    (H : AntiholeSupport V)
    (hH : H.IsContainedIn G)
    (hodd : Odd H.length) :
    IsCliqueRelaxationChvatalInequality
      G
      (stableSetIndicator H.vertexFinset)
      2 := by
  -- Route correction: the floor normalization is now isolated in
  -- `antiholeCliqueMultiplier_floor`. The remaining blocker is the explicit cyclic clique family
  -- and its coefficient-count identity on `H.vertexFinset`.
  sorry

/-- Exercise 7.19 (6). If `W` is a contained web support `W_n^k` in `G` and `n` is not divisible
by `k + 1`, then the web inequality on `W.vertexFinset` is a Chvatal inequality for the clique
relaxation `K(G)`. -/
theorem exercise_7_19_web_inequality_is_chvatal
    (W : WebSupport V)
    (hW : W.IsContainedIn G)
    (hndiv : ¬ (W.width + 1 ∣ W.length)) :
    IsCliqueRelaxationChvatalInequality
      G
      (stableSetIndicator W.vertexFinset)
      (web_inequality_rhs W) := by
  classical
  rw [isCliqueRelaxationChvatalInequality_iff]
  refine ⟨webForwardBlockMultiplier W, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The forward-block certificate uses only the nonnegative constant multiplier `1 / (k + 1)`.
    exact webForwardBlockMultiplier_nonneg (W := W)
  · -- Any nonzero multiplier comes from one of the forward blocks, hence from a clique of `G`.
    exact webForwardBlockMultiplier_support (G := G) W hW
  · -- The slack vector is identically zero.
    intro v
    simp
  · -- The support indicator has integral `0/1` coordinates.
    intro v
    by_cases hv : v ∈ W.vertexFinset
    · exact ⟨1, by simp [stableSetIndicator, hv]⟩
    · exact ⟨0, by simp [stableSetIndicator, hv]⟩
  · -- Summing the forward-block incidences recovers the support indicator of `W`.
    simpa [webForwardBlockMultiplier_coefficients]
  · -- The floored total multiplier is exactly the web right-hand side `⌊n / (k + 1)⌋`.
    calc
      ((Int.floor (∑ K : Finset V, webForwardBlockMultiplier W K) : ℤ) : ℝ)
          = ((Int.floor (∑ i : Fin W.length, (1 / (W.width + 1 : ℝ))) : ℤ) : ℝ) := by
              rw [webForwardBlockMultiplier_sum]
      _ = web_inequality_rhs W := webBlockMultiplier_floor W

end ChvatalStatements

end Exercise_7_19
