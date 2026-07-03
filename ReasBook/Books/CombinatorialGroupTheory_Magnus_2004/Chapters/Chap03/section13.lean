import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_3_13_1 (from Items/Chap03) -/
universe u v

set_option autoImplicit false

noncomputable section

/-!
Primary domain: combinatorial group theory via transitive actions on integer-valued metric spaces.

Layer triage:
- `source-facing`: an integer-valued distance bridge `d` on `V`, its source balls `S_l(v)`, and
  Behr's bounded descending-path condition `(II)`.
- `core/canonical`: `PseudoMetricSpace V`, `IsIsometricSMul G V`, `MulAction.IsPretransitive`,
  `MulAction.stabilizer`, `Relation.ReflTransGen`, and `Group.IsFinitelyPresented`.
- `bridge/view`: `integerClosedBall`, the notation `S[d](v, l)`,
  `HasBoundedDescendingPathsInBall`, and `integerClosedBall_eq_closedBall` connect the source
  integer distance data and Behr's condition `(II)` to the canonical metric closed-ball and
  relation-closure owners.

Primitive vs. derived:
- primitive public data: the integer-valued distance `d`, the step bound `k`, and the ambient
  group action on `V`;
- derived API: the source balls `S[d](v, l)`, the ballwise descending-path predicate
  `HasBoundedDescendingPathsInBall d k v l`, and condition `(II)`, all expressed through the
  canonical relation-closure owner `Relation.ReflTransGen`.

Domain sampling:
1. `PseudoMetricSpace` and `Metric.closedBall` are mathlib's owners for the ambient metric layer.
2. `IsIsometricSMul` is mathlib's owner predicate for distance-preserving scalar actions.
3. `MulAction.IsPretransitive` together with `MulAction.stabilizer` are mathlib's owners for the
   transitivity and vertex-stabilizer layers of the action.
4. `Relation.ReflTransGen` is mathlib's owner abstraction for a finite iterated chain of
   one-step moves, so it is the right core for the bounded descending-path condition and its
   ballwise owner predicate.
-/

section

open MulAction

variable {V : Type u}

/-- The closed radius-`l` ball of the integer-valued distance `d` around `v`. -/
def integerClosedBall (d : V → V → ℕ) (v : V) (l : ℕ) : Set V :=
  {w | d v w ≤ l}

namespace BehrDistance

scoped notation "S[" d "](" v "," l ")" => integerClosedBall d v l

end BehrDistance

open scoped BehrDistance

-- Proof sketch: unfold `integerClosedBall`; its membership predicate is exactly the defining
-- inequality `d v w ≤ l`.
/-- Membership in `integerClosedBall d v l` is exactly the inequality `d v w ≤ l`. -/
@[simp] theorem mem_integerClosedBall (d : V → V → ℕ) (v w : V) (l : ℕ) :
    w ∈ S[d](v, l) ↔ d v w ≤ l :=
  Iff.rfl

/-- When `d` agrees with the ambient metric, the source ball `S[d](v, l)` is the metric closed
ball of radius `l`. -/
theorem integerClosedBall_eq_closedBall [PseudoMetricSpace V]
    (d : V → V → ℕ) (hdist : ∀ v w : V, dist v w = d v w) (v : V) (l : ℕ) :
    S[d](v, l) = Metric.closedBall v l := by
  ext w
  rw [Metric.mem_closedBall', mem_integerClosedBall, hdist, Nat.cast_le]

/-- A bounded descending path from `p` to `q` inside the radius-`l` ball around `v`. -/
def HasBoundedDescendingPathInBall (d : V → V → ℕ) (k : ℕ) (v : V) (l : ℕ) (p q : V) : Prop :=
  Relation.ReflTransGen
    (fun a b ↦ a ∈ S[d](v, l) ∧ b ∈ S[d](v, l) ∧ d a q > d b q ∧ d a b ≤ k)
    p q

/-- Behr's bounded descending-path condition inside the radius-`l` ball around `v`. -/
def HasBoundedDescendingPathsInBall (d : V → V → ℕ) (k : ℕ) (v : V) (l : ℕ) : Prop :=
  ∀ ⦃p q : V⦄, p ∈ S[d](v, l) → q ∈ S[d](v, l) → HasBoundedDescendingPathInBall d k v l p q

/-- Behr's condition `(II)` for the integer-valued distance `d`. -/
def SatisfiesBehrConditionII (d : V → V → ℕ) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ ∀ v : V, ∀ l : ℕ, 1 ≤ l → HasBoundedDescendingPathsInBall d k v l

section

variable {G : Type v} [Group G] [MulAction G V] [PseudoMetricSpace V] [IsIsometricSMul G V]

-- Proof sketch: choose a base vertex `v0` and the finite generating set obtained from the finite
-- ball of radius `k` around `v0`; then follow Behr's rewriting argument using the bounded
-- descending-path hypothesis to control relators and deduce a finite presentation of `G` from a
-- finite presentation of the stabilizer `stabilizer G v0`.
/-- Proposition 3-13-1: if `d` is an integer-valued distance whose balls `S_l(v)` are finite for
`l ≥ 1`, if `d` agrees with the ambient metric on `V`, and if the bounded descending-path
condition `(II)` holds, then any transitive isometric action of `G` on `V` has finitely presented
acting group whenever one vertex stabilizer is finitely presented. -/
theorem isFinitelyPresented_of_finitelyPresented_stabilizer_of_behr_distance_action
    (d : V → V → ℕ)
    (hdist : ∀ v w : V, dist v w = d v w)
    (hfinite : ∀ v : V, ∀ l : ℕ, 1 ≤ l → (S[d](v, l)).Finite)
    (hdesc : SatisfiesBehrConditionII d)
    (v0 : V)
    (htrans : MulAction.IsPretransitive G V)
    (hstab : Group.IsFinitelyPresented (stabilizer G v0)) :
    Group.IsFinitelyPresented G := sorry

end
end

/-! ### Proposition_3_13_2 (from Items/Chap03) -/
universe u v

set_option autoImplicit false

noncomputable section

/-!
Primary domain: combinatorial group theory via locally finite locally convex graphs and
vertex-transitive graph automorphism actions.

Layer triage:
- `source-facing`: a locally finite locally convex graph `Γ`, a group `G` acting transitively on
  its vertices by graph automorphisms, and the finite presentability of one vertex stabilizer.
- `core/canonical`: `SimpleGraph`, `SimpleGraph.Iso`, `SimpleGraph.LocallyFinite`,
  `SimpleGraph.dist`, `PseudoMetricSpace`, `IsIsometricSMul`, `MulAction.stabilizer`,
  `MulAction.IsPretransitive`, and `Group.IsFinitelyPresented`.
- `bridge/view`: `SimpleGraph.IsLocallyConvex` below records the source geodesic-ball convexity
  condition, while the induced vertex action from `ρ : G →* (Γ ≃g Γ)` is expressed canonically by
  `MulAction.compHom V ρ` together with the owner subgroup `MulAction.stabilizer`.

Domain sampling:
1. `SimpleGraph` is mathlib's canonical owner for an undirected incidence graph.
2. `SimpleGraph.Iso` is mathlib's owner abstraction for graph automorphisms.
3. `SimpleGraph.LocallyFinite` and `SimpleGraph.dist` are the canonical owners for finite valence
   and graph metric structure.
4. `PseudoMetricSpace` and `IsIsometricSMul` are the canonical owners for the metric and
   isometric-action layers used by Proposition `3-13-1`.
5. `MulAction.compHom`, `MulAction.stabilizer`, and `Group.IsFinitelyPresented` are the canonical
   owners for the induced vertex action, its stabilizer, and the conclusion.

Primitive vs. derived:
- primitive public data: the graph `Γ`, the graph-isomorphism action `ρ`, and the local convexity
  hypothesis on graph balls;
- derived API: connectedness forced by local convexity, the canonical induced action
  `MulAction.compHom V ρ` on vertices, the stabilizer of a chosen vertex for that action, finite
  closed graph balls in the connected case, bounded descending paths in balls, and the graph-metric
  form of Behr's descending-path condition.
-/

section

open MulAction
open scoped BehrDistance

variable {G : Type u} {V : Type v} [Group G]

namespace SimpleGraph

/-- A graph is locally convex when every closed graph-metric ball is geodesically convex: any two
vertices of the ball are joined by a shortest walk that stays inside the same ball. -/
def IsLocallyConvex (Γ : SimpleGraph V) : Prop :=
  ∀ v : V,
    ∀ l : ℕ,
      ∀ ⦃p q : V⦄,
        p ∈ S[Γ.dist](v, l) →
          q ∈ S[Γ.dist](v, l) →
            ∃ r : Γ.Walk p q,
              r.length = Γ.dist p q ∧
                ∀ w ∈ r.support, w ∈ S[Γ.dist](v, l)

variable (Γ : SimpleGraph V)

/-- Local convexity already forces connectedness on a nonempty graph: for any `p q`, the
radius-`Γ.dist p q` ball around `p` contains both endpoints, hence contains a shortest walk from
`p` to `q`. -/
theorem IsLocallyConvex.connected [Nonempty V] (hconvex : Γ.IsLocallyConvex) : Γ.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  obtain ⟨v⟩ := ‹Nonempty V›
  refine ⟨v, fun w ↦ ?_⟩
  have hv : v ∈ S[Γ.dist](v, Γ.dist v w) := by
    simp [mem_integerClosedBall]
  have hw : w ∈ S[Γ.dist](v, Γ.dist v w) := by
    simp [mem_integerClosedBall]
  obtain ⟨r, -, -⟩ :
      ∃ r : Γ.Walk v w,
        r.length = Γ.dist v w ∧
          ∀ x ∈ r.support, x ∈ S[Γ.dist](v, Γ.dist v w) :=
    hconvex v (Γ.dist v w) hv hw
  exact r.reachable

-- Proof sketch: in a connected graph every vertex of the closed ball is reachable from the
-- center, so `SimpleGraph.dist` no longer sees the off-component junk value `0`. Induct on the
-- radius: the ball of radius `0` is `{v}`, and a vertex at radius at most `l + 1` is either
-- already in the radius-`l` ball or adjacent to a vertex there. Local finiteness makes the
-- resulting neighbor union finite.
/-- Every closed ball in a connected locally finite graph is finite. -/
theorem graphClosedBall_finite_of_locallyFinite_of_connected [Γ.LocallyFinite]
    (hconn : Γ.Connected) (v : V) (l : ℕ) :
    (S[Γ.dist](v, l)).Finite := sorry

-- Proof sketch: choose the geodesic inside the ball from the local-convexity hypothesis. Along a
-- shortest path, each successive step moves to an adjacent vertex and reduces the remaining graph
-- distance to the endpoint by exactly `1`, so this path witnesses condition `(II)` of Proposition
-- `3-13-1` with `k = 1`.
/-- Local convexity gives Behr's bounded descending-path condition with step bound `1`. -/
theorem hasBoundedDescendingPathInBall_of_isLocallyConvex
    (hconvex : Γ.IsLocallyConvex) (v : V) (l : ℕ) {p q : V}
    (hp : p ∈ S[Γ.dist](v, l))
    (hq : q ∈ S[Γ.dist](v, l)) :
    HasBoundedDescendingPathInBall Γ.dist 1 v l p q := sorry

namespace Iso

variable {Γ : SimpleGraph V} {G : Type u} [Group G]

/-- A source-facing transitivity hypothesis for `ρ` yields the canonical `IsPretransitive`
instance on the induced action `MulAction.compHom V ρ`. -/
theorem isPretransitive_compHom (ρ : G →* (Γ ≃g Γ))
    (htrans : ∀ p q : V, ∃ g : G, (ρ g) p = q) :
    letI := MulAction.compHom V ρ
    MulAction.IsPretransitive G V := by
  letI := MulAction.compHom V ρ
  exact ⟨fun p q ↦ by
    obtain ⟨g, hg⟩ := htrans p q
    exact ⟨g, hg⟩⟩

-- Proof sketch: a graph isomorphism sends walks to walks of the same length in both directions,
-- hence preserves reachability and the infimum of walk lengths that defines the graph metric.
/-- A graph automorphism preserves the graph metric. -/
theorem dist_eq (σ : Γ ≃g Γ) (p q : V) :
    Γ.dist (σ p) (σ q) = Γ.dist p q := sorry

end Iso

end SimpleGraph

-- Proof sketch: apply Proposition `3-13-1` to the graph metric `Γ.dist`. Local finiteness gives
-- finite closed balls in the connected case, local convexity gives condition `(II)` with `k = 1`,
-- graph automorphisms preserve graph distance, and the transitivity hypothesis is stated for the
-- action induced by `ρ`. The stabilizer hypothesis is exactly the finite presentability of one
-- vertex stabilizer for that induced action.
/-- Proposition 3-13-2: if a locally finite locally convex graph `Γ` admits a vertex-transitive
action of `G` by graph automorphisms, then finite presentability of one vertex stabilizer implies
finite presentability of `G`. The action is given through the canonical owner
`G →* (Γ ≃g Γ)` of graph automorphisms. -/
theorem isFinitelyPresented_of_finitelyPresented_stabilizer_of_locallyFinite_locallyConvex_graph
    (Γ : SimpleGraph V)
    [Γ.LocallyFinite]
    (hconvex : Γ.IsLocallyConvex)
    (ρ : G →* (Γ ≃g Γ))
    (v0 : V)
    (htrans : ∀ p q : V, ∃ g : G, (ρ g) p = q)
    (hstab : letI : MulAction G V := MulAction.compHom V ρ
      Group.IsFinitelyPresented (stabilizer G v0)) :
    Group.IsFinitelyPresented G := by
  letI : Nonempty V := ⟨v0⟩
  letI : MulAction G V := MulAction.compHom V ρ
  letI : PseudoMetricSpace V := {
    dist := fun x y ↦ Γ.dist x y
    dist_self := by intro x; simp [SimpleGraph.dist_self]
    dist_comm := by intro x y; simp [SimpleGraph.dist_comm]
    dist_triangle := by
      intro x y z
      have h : Γ.dist x z ≤ Γ.dist x y + Γ.dist y z := hconvex.connected.dist_triangle
      exact_mod_cast h
  }
  letI : IsIsometricSMul G V :=
    IsIsometricSMul.mk fun g ↦ by
      refine Isometry.of_dist_eq fun p q ↦ ?_
      change (Γ.dist ((ρ g) p) ((ρ g) q) : ℝ) = (Γ.dist p q : ℝ)
      exact congrArg (fun n : ℕ ↦ (n : ℝ)) ((ρ g).dist_eq p q)
  exact
    isFinitelyPresented_of_finitelyPresented_stabilizer_of_behr_distance_action
      Γ.dist
      (fun _ _ ↦ rfl)
      (fun v l _ ↦ Γ.graphClosedBall_finite_of_locallyFinite_of_connected hconvex.connected v l)
      (by
        refine ⟨1, le_rfl, ?_⟩
        intro v l _ p q hp hq
        exact Γ.hasBoundedDescendingPathInBall_of_isLocallyConvex hconvex v l hp hq)
      v0
      (SimpleGraph.Iso.isPretransitive_compHom ρ htrans)
      (by simpa using hstab)

end
end

/-! ### Lemma_3_13_3 (from Items/Chap03) -/
universe u v

set_option autoImplicit false

section

open MulAction

/-!
Primary domain: group actions on metric spaces and generation by a basepoint stabilizer together
with short orbit-step representatives.

Layer triage:
- `source-facing`: a group `G` acting on a metric space `Ω`, a basepoint `o : Ω`, and subsets
  `X₀`, `X₁ : Set G` whose union is asserted to generate `G`.
- `core/canonical`: `stabilizer G o` is mathlib's owner for the isotropy subgroup of `o`, and
  `Subgroup.closure` is the owner for the subgroup generated by a subset of `G`.
- `bridge/view`: the textbook bounded-step argument is encoded by the predicates
  `dist o (g • o) ≤ k` and by finite products of such short orbit steps.
-/

variable {G : Type u} {Ω : Type v} [Group G] [PseudoMetricSpace Ω] [MulAction G Ω]
variable (o : Ω) (X₀ X₁ : Set G) (k : ℝ)

-- Proof sketch: first show that any short step `g` with `dist o (g • o) ≤ k` lies in
-- `Subgroup.closure (X₀ ∪ X₁)` because `g • o` is also `x • o` for some `x ∈ X₁`, so
-- `x⁻¹ * g ∈ stabilizer G o`, hence the stabilizer hypothesis puts `g` into the closure. For an
-- arbitrary `g : G`, use the bounded-step hypothesis to choose a product of short steps having the
-- same effect on `o` as `g`; the remaining difference again lies in the stabilizer, so `g`
-- belongs to the same closure.
/-- Lemma 3-13-3: if `X₀` generates the stabilizer of the basepoint `o`, every `k`-short orbit
step out of `o` is represented modulo the stabilizer by some element of `X₁`, and every orbit
point `g • o` is reached from `o` by a finite product of such `k`-short steps, then
`X = X₀ ∪ X₁` generates `G`. -/
theorem closure_union_eq_top_of_stabilizer_and_short_orbit_steps
    (hX₀ : Subgroup.closure X₀ = stabilizer G o)
    (hX₁ : ∀ g : G, dist o (g • o) ≤ k → ∃ x ∈ X₁, x • o = g • o)
    (hsteps : ∀ g : G, ∃ l : List G, (∀ a ∈ l, dist o (a • o) ≤ k) ∧ l.prod • o = g • o) :
    Subgroup.closure (X₀ ∪ X₁) = ⊤ := by
  refine (Subgroup.eq_top_iff' _).2 ?_
  intro g
  let H : Subgroup G := Subgroup.closure (X₀ ∪ X₁)
  have hX₀H : Subgroup.closure X₀ ≤ H :=
    Subgroup.closure_mono fun x hx ↦ Or.inl hx
  have hstabH : stabilizer G o ≤ H := by
    simpa [← hX₀] using hX₀H
  have hshortH : ∀ a : G, dist o (a • o) ≤ k → a ∈ H := by
    intro a ha
    rcases hX₁ a ha with ⟨x, hxX₁, hxo⟩
    have hx : x ∈ H := Subgroup.subset_closure (Or.inr hxX₁)
    have hxa : x⁻¹ * a ∈ stabilizer G o := by
      rw [MulAction.mem_stabilizer_iff]
      calc
        (x⁻¹ * a) • o = x⁻¹ • (a • o) := by simpa using mul_smul x⁻¹ a o
        _ = x⁻¹ • (x • o) := by simp [hxo]
        _ = o := by simp
    have hxaH : x⁻¹ * a ∈ H := hstabH hxa
    simpa [mul_assoc] using H.mul_mem hx hxaH
  change g ∈ H
  rcases hsteps g with ⟨l, hlshort, hlg⟩
  have hl : l.prod ∈ H :=
    Subgroup.list_prod_mem H fun a ha ↦ hshortH a (hlshort a ha)
  have hlgH : l.prod⁻¹ * g ∈ H := by
    apply hstabH
    rw [MulAction.mem_stabilizer_iff]
    calc
      (l.prod⁻¹ * g) • o = l.prod⁻¹ • (g • o) := by simpa using mul_smul l.prod⁻¹ g o
      _ = l.prod⁻¹ • (l.prod • o) := by simp [hlg]
      _ = o := by simp
  simpa [mul_assoc] using H.mul_mem hl hlgH

end

/-! ### Lemma_3_13_4 (from Items/Chap03) -/
universe u v

set_option autoImplicit false

/-!
Primary domain: cumulative displacement bounds for isometric scalar actions on pseudometric spaces.

Layer triage:
- `source-facing`: the displacement of a point under a finite successive scalar translate.
- `core/canonical`: `IsIsometricSMul G V` is the owner hypothesis for isometric scalar actions,
  `dist_smul` is the owner one-step invariance lemma, and `List.foldl_append` is the canonical
  snoc decomposition for the successive-translate path.
- `bridge/view`: none; the textbook statement is already a direct estimate on the canonical action.

Domain sampling:
1. `IsIsometricSMul G V` is mathlib's owner predicate for isometric scalar actions.
2. `dist_smul` is the canonical distance-preservation lemma for one translate.
3. `List.foldl_append` is the canonical API for peeling the last step off a successive translate.
4. `dist_triangle` is the owner polygon inequality on a pseudometric space.
-/

section

variable {G : Type u} {V : Type v} [PseudoMetricSpace V] [SMul G V]
variable [IsIsometricSMul G V]

/-- Lemma 3-13-4: for an isometric scalar action on a pseudometric space, the displacement of a point
under a finite successive translate is at most the sum of the individual displacements. -/
theorem dist_foldl_smul_le_sum_dist_smul (v : V) (gs : List G) :
    dist v (gs.foldl (fun x g ↦ g • x) v) ≤ (gs.map fun g ↦ dist v (g • v)).sum := by
  induction gs using List.reverseRecOn with
  | nil =>
      simp
  | append_singleton hs g ih =>
    calc
      dist v ((hs ++ [g]).foldl (fun x g ↦ g • x) v)
          = dist v (g • (hs.foldl successiveTranslate v)) := by
              simp [List.foldl_append]
      _ ≤ dist v (g • v) + dist (g • v) (g • (hs.foldl (fun x g ↦ g • x) v)) := by
            simpa using dist_triangle v (g • v) (g • (hs.foldl (fun x g ↦ g • x) v))
      _ = dist v (g • v) + dist v (hs.foldl (fun x g ↦ g • x) v) := by
            simp
      _ ≤ dist v (g • v) + (hs.map fun h ↦ dist v (h • v)).sum := by
            simpa [add_comm] using add_le_add_left ih (dist v (g • v))
      _ = ((hs ++ [g]).map fun h ↦ dist v (h • v)).sum := by
            simp [List.map_append, add_comm]

end

/-! ### Lemma_3_13_5 (from Items/Chap03) -/
universe u v w

set_option autoImplicit false

noncomputable section

/-!
Primary domain: Behr-style rewriting for group actions on an integer-valued metric space.

Layer triage:
- `source-facing`: a group action of `G` on `V`, a basepoint `o`, a generator alphabet `X` with
  distinguished subset `X₀`, an integer-valued distance, and the three bounded-word /
  bounded-descent hypotheses used in Behr's rewriting argument.
- `core/canonical`: `[MulAction G V]` is mathlib's owner abstraction for the action, `List X` is
  the source owner for finite positive words, `List.map` together with `List.prod` is the
  canonical concrete evaluation API for such words in the ambient group, and Proposition `3-13-1`
  already provides the owner abstractions `integerClosedBall` and
  `HasBoundedDescendingPathsInBall` for the descending-path condition.
- `bridge/view`: the two helper predicates below express the two bounded-word hypotheses against
  the canonical action.

Domain sampling:
1. `[MulAction G V]` is the mathlib owner abstraction for the action, so the lemma should live
   directly over the instance rather than a second packaged graph structure.
2. `List.map` and `List.prod` are the canonical concrete owner API for evaluating a positive
   `List X` word in `G`; equivalently, this is the `FreeMonoid.lift` evaluation specialized to
   the list model of `FreeMonoid`.
3. `integerClosedBall` together with the notation `S[d](o, l)` is the chapter owner for the
   closed ball `S_l(o)`.
4. `HasBoundedDescendingPathsInBall` is the chapter owner for Behr's bounded descending-path
   hypothesis in a fixed ball.

Primitive vs. derived:
- primitive public data: the action of `G` on `V`, the generator interpretation `X → G`, the
  distinguished subset `X₀ ⊆ X`, the step bound `k`, the basepoint `o`, and the distance
  function `d`;
- derived API: bounded word realizations of short metric steps, bounded distinguished words for
  stabilizer loops, and the resulting correction-word existence theorem.
-/

section

open scoped BehrDistance

variable {G : Type u} {V : Type v} {X : Type w}
variable [Group G] [MulAction G V]

/-- Every metric step of size at most `k` is realized by a positive generator word of length at
most `k`. This is the source-facing bridge from the metric Behr graph to the generator alphabet. -/
def HasBoundedStepWordRealization (generators : X → G) (d : V → V → ℕ) (k : ℕ) : Prop :=
  ∀ ⦃p q : V⦄, d p q ≤ k →
    ∃ letters : List X,
      letters.length ≤ k ∧ (letters.map generators).prod • p = q

/-- Every stabilizer element admits a distinguished positive word representative whose prefixes do
not move the chosen base vertex farther from the origin. -/
def HasBoundedDistinguishedStabilizerWords
    (generators : X → G) (X₀ : Set X) (o : V) (d : V → V → ℕ) : Prop :=
  ∀ ⦃v : V⦄ ⦃a : G⦄, a • v = v →
    ∃ letters : List X,
      (letters.map generators).prod = a ∧
        (∀ x ∈ letters, x ∈ X₀) ∧
        ∀ i, i ≤ letters.length →
          d o (((letters.take i).map generators).prod • v) ≤ d o v

variable (generators : X → G) (X₀ : Set X) (k : ℕ) (o : V) (d : V → V → ℕ)

/-- Lemma 3-13-5: assume Behr's bounded descending-path condition in the ball about `o`, together
with bounded generator realizations of short metric steps and bounded distinguished word
representatives for stabilizer loops. Then whenever `u` is obtained from `v` by the positive word
`g`, there is a correction word whose total product cancels `g`, whose tail
`correction.drop (|g| * k)` lies in `X₀`, and whose prefixes keep the intermediate translates of
`u` inside the radius `max {d(o, v), d(o, u)}`. -/
theorem exists_correction_word_with_bounded_prefix_distance
    (hdesc : ∀ l : ℕ, HasBoundedDescendingPathsInBall d k o l)
    (hstep : HasBoundedStepWordRealization generators d k)
    (hstab : HasBoundedDistinguishedStabilizerWords generators X₀ o d)
    (g : List X) (v u : V) (hu : u = (g.map generators).prod • v) :
    ∃ correction : List X,
      ((g ++ correction).map generators).prod = 1 ∧
        (∀ x ∈ correction.drop (g.length * k), x ∈ X₀) ∧
        ∀ i,
          d o (((correction.take i).map generators).prod • u) ≤
            max (d o v) (d o u) := sorry

end

/-! ### Corollary_3_13_6 (from Items/Chap03) -/
universe u v w

set_option autoImplicit false

noncomputable section

/-!
Primary domain: short-word specializations of Behr correction words.

Layer triage:
- `source-facing`: the canonical action of `G` on `V`, a positive generator word `g : List X` of
  length at most `3`, the endpoints `v` and `u`, and the same bounded-step / bounded-stabilizer /
  bounded-descent hypotheses as in Lemma `3-13-5`.
- `core/canonical`: `exists_correction_word_with_bounded_prefix_distance` from Lemma `3-13-5` is
  the chapter owner theorem for the correction-word construction.
- `bridge/view`: this corollary is the thin short-word specialization replacing the general tail
  threshold `g.length * k` by the uniform bound `3 * k`.

Domain sampling:
1. `[MulAction G V]` is the owner action abstraction inherited from Lemma `3-13-5`.
2. `List.map` together with `List.prod` is the canonical concrete evaluation API for a positive
   `List X` word in the ambient group.
3. `S[d](o, l)` from Proposition `3-13-1` is the chapter owner notation for the source ball
   condition used in `hdesc`.
4. `exists_correction_word_with_bounded_prefix_distance` is the owner theorem specialized here.

Primitive vs. derived:
- primitive public data: the action, generators, distinguished subset, step bound, basepoint,
  distance, short positive word `g`, vertices `v` and `u`, and the endpoint hypothesis `hu`;
- derived API: the corollary's uniform `3 * k` bound on the distinguished tail of the correction
  word.
-/

section

open scoped BehrDistance

variable {G : Type u} {V : Type v} {X : Type w}
variable [Group G] [MulAction G V]

variable (generators : X → G) (X₀ : Set X) (k : ℕ) (o : V) (d : V → V → ℕ)
variable
  (hdesc :
    ∀ l : ℕ,
      ∀ ⦃p q : V⦄,
        p ∈ S[d](o, l) →
          q ∈ S[d](o, l) →
            HasBoundedDescendingPathInBall d k o l p q)
  (hstep : HasBoundedStepWordRealization generators d k)
  (hstab : HasBoundedDistinguishedStabilizerWords generators X₀ o d)

/-- Corollary 3-13-6: for a positive generator word of length at most `3`, the correction word
from Lemma `3-13-5` may be chosen with the same bounded-prefix-distance control, and every letter
in the tail `correction.drop (3 * k)` lies in the distinguished subset `X₀`. -/
theorem exists_correction_word_with_bounded_prefix_distance_of_length_le_three
    (g : List X) (v u : V) (hg : g.length ≤ 3) (hu : u = (g.map generators).prod • v) :
    ∃ correction : List X,
      ((g ++ correction).map generators).prod = 1 ∧
        (∀ x ∈ correction.drop (3 * k), x ∈ X₀) ∧
        ∀ i,
          d o (((correction.take i).map generators).prod • u) ≤
            max (d o v) (d o u) := by
  rcases exists_correction_word_with_bounded_prefix_distance
      generators X₀ k o d hdesc hstep hstab g v u hu with
    ⟨correction, hprod, htail, hprefix⟩
  refine ⟨correction, hprod, ?_, hprefix⟩
  intro x hx
  exact htail x <| by
    simpa [List.drop_drop, Nat.add_sub_of_le (Nat.mul_le_mul_right k hg)] using hx

end

/-! ### Proposition_3_13_7 (from Items/Chap03) -/
open scoped MatrixGroups
open CongruenceSubgroup
open ConjAct

set_option autoImplicit false

section

/-!
Primary domain: special linear groups over localizations of `ℤ` and Bass-LinearRepresentations_Serre_1977 amalgams.

Layer triage:
- `source-facing`: the congruence subgroup `Γ₀(p) ≤ SL(2, ℤ)`, the two adjacent-vertex
  stabilizers inside `SL(2, ℤ[1/p])`, and the claim that `SL(2, ℤ[1/p])` is their amalgamated
  free product over the common edge stabilizer.
- `core/canonical`: `SL(2, ℤ)`, `Gamma0 p`, `SL(2, Localization.Away (p : ℤ))`, `Subgroup`, and
  the chapter owner API `Subgroup.amalgamatedProductComparison`.
- `bridge/view`: the integral copy of `SL(2, ℤ)` inside the localization, the diagonal element
  `diag(1, p)` in the ambient general linear group, the induced conjugation of
  `SL(2, ℤ[1/p])`, and the resulting ambient image of `Γ₀(p)`.

Domain sampling:
1. `SL(2, R)` from `Matrix.SpecialLinearGroup` is the canonical owner for determinant-one `2 × 2`
   matrices over a commutative ring `R`.
2. `Gamma0 p` from mathlib is the canonical owner for the subgroup of `SL(2, ℤ)` cut out by the
   condition that the lower-left entry is `0 mod p`.
3. `Localization.Away (p : ℤ)` is the canonical localization model for the source ring `ℤ[1/p]`.
4. `ConjAct.toConjAct` is the canonical owner for conjugation by an ambient invertible element,
   so the adjacent vertex stabilizer should be expressed as the `diag(1, p)`-conjugate of the
   integral stabilizer rather than via an entrywise duplicate embedding.
5. `Subgroup.map` and `Subgroup.range` are the canonical subgroup owners for the integral vertex
  stabilizer, its `diag(1, p)`-conjugate, and the ambient image of `Γ₀(p)`.
6. Proposition `3-12-5` already exposes `Subgroup.amalgamatedProduct` and
   `Subgroup.amalgamatedProductComparison` as the chapter owner API for a two-factor amalgam.

Primitive vs. derived:
- primitive public data: the canonical congruence subgroup `Gamma0 p ≤ SL(2, ℤ)`;
- derived API: the integral vertex stabilizer, its `diag(1, p)`-conjugate adjacent stabilizer,
  the ambient image of `Gamma0 p`, its distinct conjugate copy inside the adjacent vertex
  stabilizer, the identification of the integral copy with the subgroup intersection, and the
  canonical amalgamated-product comparison map supplied by Proposition `3-12-5`.
-/

/-- The integral vertex stabilizer inside `SL(2, ℤ[1/p])`. -/
private noncomputable def integralSpecialLinearEmbedding (p : ℕ) :
    SL(2, ℤ) →* SL(2, Localization.Away (p : ℤ)) :=
  Matrix.SpecialLinearGroup.map (algebraMap ℤ (Localization.Away (p : ℤ)))

/-- The diagonal element `diag(1, p)` in `GL(2, ℤ[1/p])`. -/
private noncomputable def diagonalPrimeGeneralLinear (p : ℕ) :
    GL (Fin 2) (Localization.Away (p : ℤ)) := by
  refine Matrix.GeneralLinearGroup.mk''
    !![1, 0; 0, (algebraMap ℤ (Localization.Away (p : ℤ))) (p : ℤ)] ?_
  have hp : IsUnit (algebraMap ℤ (Localization.Away (p : ℤ)) (p : ℤ)) :=
    IsLocalization.Away.algebraMap_isUnit (p : ℤ)
  simpa [Matrix.det_fin_two] using hp

/-- Conjugation on `SL(2, ℤ[1/p])` by the diagonal element `diag(1, p)`. -/
private noncomputable def diagonalPrimeConjugation (p : ℕ) :
    SL(2, Localization.Away (p : ℤ)) →* SL(2, Localization.Away (p : ℤ)) where
  toFun g := by
    let δ : GL (Fin 2) (Localization.Away (p : ℤ)) := diagonalPrimeGeneralLinear p
    refine ⟨(toConjAct δ) •
      (g : Matrix (Fin 2) (Fin 2) (Localization.Away (p : ℤ))), ?_⟩
    change Matrix.det (((δ : GL (Fin 2) (Localization.Away (p : ℤ))) :
        Matrix (Fin 2) (Fin 2) (Localization.Away (p : ℤ))) *
      (g : Matrix (Fin 2) (Fin 2) (Localization.Away (p : ℤ))) *
      (((δ : GL (Fin 2) (Localization.Away (p : ℤ)))⁻¹ :
        GL (Fin 2) (Localization.Away (p : ℤ))) :
        Matrix (Fin 2) (Fin 2) (Localization.Away (p : ℤ)))) = 1
    simpa [δ] using (Matrix.det_units_conj δ
      (g : Matrix (Fin 2) (Fin 2) (Localization.Away (p : ℤ))))
  map_one' := by
    ext i j
    simp
  map_mul' g h := by
    ext i j
    simp

/-- The integral copy of `SL(2, ℤ)` inside `SL(2, ℤ[1/p])`. -/
noncomputable def integralSpecialLinearSubgroup (p : ℕ) :
    Subgroup (SL(2, Localization.Away (p : ℤ))) :=
  (integralSpecialLinearEmbedding p).range

/-- The adjacent copy of `SL(2, ℤ)` inside `SL(2, ℤ[1/p])`, obtained from the integral copy by
conjugation with `diag(1, p)`. -/
noncomputable def adjacentSpecialLinearSubgroup (p : ℕ) :
    Subgroup (SL(2, Localization.Away (p : ℤ))) :=
  Subgroup.map (diagonalPrimeConjugation p) (integralSpecialLinearSubgroup p)

/-- The ambient copy of `Γ₀(p)` inside `SL(2, ℤ[1/p])`. -/
noncomputable def gamma0Subgroup (p : ℕ) :
    Subgroup (SL(2, Localization.Away (p : ℤ))) :=
  Subgroup.map (integralSpecialLinearEmbedding p) (Gamma0 p)

/-- The ambient image of `Γ₀(p)` is the common edge stabilizer, namely the intersection of the
two adjacent vertex stabilizers. -/
theorem gamma0Subgroup_eq_inf (p : ℕ) :
    gamma0Subgroup p =
      integralSpecialLinearSubgroup p ⊓ adjacentSpecialLinearSubgroup p := by
  sorry

/-- Bridge theorem: the chapter-owner comparison map for the intersection-based amalgam of the two
adjacent vertex stabilizers is bijective. The source-facing edge subgroup remains
`gamma0Subgroup p`, identified with the intersection by `gamma0Subgroup_eq_inf p`. -/
-- Proof sketch: let `SL(2, Localization.Away (p : ℤ))` act on the Behr tree for the prime `p`.
-- The stabilizers of two adjacent vertices are the integral copy and the `diag(1, p)`-conjugate
-- copy of `SL(2, ℤ)`, and their common edge stabilizer is the ambient subgroup
-- `gamma0Subgroup p`, identified with the subgroup intersection by `gamma0Subgroup_eq_inf p`.
-- The quotient graph is a single edge. Bass-LinearRepresentations_Serre_1977 theory then identifies the ambient group with
-- the pushout of those two vertex stabilizers over that edge stabilizer.
private theorem integralAdjacentSpecialLinearSubgroup_amalgamatedProductComparison_bijective
    (p : ℕ) (hp : p.Prime) :
    Function.Bijective
      (Subgroup.amalgamatedProductComparison
        (integralSpecialLinearSubgroup p)
        (adjacentSpecialLinearSubgroup p)) := by
  let _ : Fact p.Prime := ⟨hp⟩
  sorry

/-- Proposition 3-13-7: the canonical comparison map from the source-facing pushout of the two
adjacent copies of `SL(2, ℤ)` in `SL(2, ℤ[1/p])` onto `SL(2, ℤ[1/p])` is bijective. The
source-facing subgroup `gamma0Subgroup p` coming from `Γ₀(p)` is the common edge stabilizer,
identified with the intersection used by the chapter owner API via `gamma0Subgroup_eq_inf p`. -/
theorem specialLinearGroup_away_prime_is_amalgamatedProduct_of_Gamma0
    (p : ℕ) (hp : p.Prime) :
    Function.Bijective
      (Subgroup.amalgamatedProductComparison
        (integralSpecialLinearSubgroup p)
        (adjacentSpecialLinearSubgroup p)) := by
  exact
    integralAdjacentSpecialLinearSubgroup_amalgamatedProductComparison_bijective p hp

end

/-! ### Proposition_3_13_8 (from Items/Chap03) -/
open scoped MatrixGroups

universe u

set_option autoImplicit false

/-!
Primary domain: Bass-LinearRepresentations_Serre_1977 decompositions of matrix groups over polynomial rings.

Layer triage:
- `source-facing`: the two concrete subgroups of `GL(2, F[t])`, namely the constant-coefficient
  copy of `GL(2, F)` and the upper triangular subgroup `T(F[t])`, with common subgroup `T(F)`.
- `core/canonical`: `Subgroup.amalgamatedProduct` and
  `Subgroup.amalgamatedProductComparison` from Proposition `3-12-5`, built on top of mathlib's
  `Monoid.PushoutI`, together with `Matrix.BlockTriangular` for the upper triangular subgroup.
- `bridge/view`: the constant-coefficient embeddings into `GL(2, F[t])` and the coordinate-level
  characterization `g 1 0 = 0` of membership in the upper triangular subgroup.

Domain sampling:
1. Proposition `3-12-5` already exposes `Subgroup.amalgamatedProduct` and
   `Subgroup.amalgamatedProductComparison` as the chapter owner/bridge API for a two-factor
   amalgamated product over a subgroup intersection.
2. `Matrix.BlockTriangular`, `Matrix.blockTriangular_one`, `Matrix.BlockTriangular.mul`, and
   `Matrix.blockTriangular_inv_of_blockTriangular` are the canonical owner lemmas for upper
   triangularity of matrices.
3. `GL (Fin 2) R` is the canonical owner for invertible `2 × 2` matrices over `R`.
4. `Matrix.GeneralLinearGroup.map` is the canonical way to embed `GL(2, F)` into
   `GL(2, F[t])` along the coefficient homomorphism `Polynomial.C`.
5. `Subgroup.map`, `Subgroup.range`, and `Subgroup.inf` are the canonical subgroup-level APIs for
   the constant copy of `GL(2, F)`, the copy of `T(F)`, and the identified intersection.

Primitive vs. derived:
- primitive data: the two actual subgroups inside `GL(2, F[t])`, with the upper triangular one
  defined by the intrinsic `Matrix.BlockTriangular` predicate;
- derived data: the coordinate lemma `g 1 0 = 0` for that subgroup, the constant-coefficient
  image of `T(F)` inside `GL(2, F[t])`, the two-factor amalgamated product, and its canonical
  comparison map into the ambient matrix group.
-/

section

variable {R : Type u} [CommRing R]

/-- The subgroup `T(R)` of invertible upper triangular `2 × 2` matrices over `R`. -/
def upperTriangularSubgroup : Subgroup (GL (Fin 2) R) where
  carrier := {g : GL (Fin 2) R | (g : Matrix (Fin 2) (Fin 2) R).BlockTriangular id}
  one_mem' := by
    simpa using
      (Matrix.blockTriangular_one : Matrix.BlockTriangular (1 : Matrix (Fin 2) (Fin 2) R) id)
  mul_mem' := by
    intro a b ha hb
    simpa using Matrix.BlockTriangular.mul ha hb
  inv_mem' := by
    intro g hg
    let _ := g.invertible
    simpa using
      (Matrix.blockTriangular_inv_of_blockTriangular hg :
        ((g : Matrix (Fin 2) (Fin 2) R)⁻¹).BlockTriangular id)

/-- For `2 × 2` matrices, upper triangularity is equivalent to vanishing lower-left entry. -/
@[simp] theorem mem_upperTriangularSubgroup_iff {g : GL (Fin 2) R} :
    g ∈ upperTriangularSubgroup ↔ g 1 0 = 0 := by
  constructor
  · intro hg
    exact hg (show (0 : Fin 2) < 1 by decide)
  · intro hg i j hij
    have hi : i = 1 := by
      apply Fin.ext
      have hi_lt : (i : ℕ) < 2 := i.2
      have hj_lt : (j : ℕ) < 2 := j.2
      have hji : (j : ℕ) < i := by
        simpa using hij
      omega
    subst hi
    have hj : j = 0 := by
      apply Fin.ext
      have hji : (j : ℕ) < 1 := by
        simpa using hij
      omega
    subst hj
    simpa using hg

end

section

variable (F : Type u) [Field F]

/-- The constant-coefficient copy of `GL(2, F)` inside `GL(2, F[t])`. -/
noncomputable def constantLinearSubgroup : Subgroup (GL (Fin 2) (Polynomial F)) :=
  (Matrix.GeneralLinearGroup.map (Polynomial.C : F →+* Polynomial F)).range

/-- The constant image of `T(F)` is the intersection of the constant copy of `GL(2, F)` with the
upper triangular subgroup of `GL(2, F[t])`. -/
-- Proof sketch: a constant matrix lies in the upper triangular subgroup of `GL(2, F[t])`
-- exactly when its lower-left entry is the zero polynomial, which is equivalent to the original
-- lower-left entry in `F` being zero.
theorem map_upperTriangularSubgroup_eq_inf :
    upperTriangularSubgroup.map
        (Matrix.GeneralLinearGroup.map (Polynomial.C : F →+* Polynomial F)) =
      constantLinearSubgroup F ⊓ upperTriangularSubgroup :=
  sorry

/-- Proposition 3-13-8: the canonical comparison map from the amalgamated free product of the
constant copy of `GL(2, F)` and the upper triangular subgroup `T(F[t])`, with the corresponding
subgroup `T(F)` identified, onto `GL(2, F[t])` is bijective. -/
-- Proof sketch: let `GL(2, F[t])` act on the Behr tree attached to the valuation at infinity on
-- `F(t)`. The quotient graph is an edge; its two vertex stabilizers are the constant copy of
-- `GL(2, F)` and `T(F[t])`, and the edge stabilizer is `T(F)`. Bass-LinearRepresentations_Serre_1977 theory then identifies
-- the ambient group with the amalgamated free product of those two stabilizers; the bridge theorem
-- `map_upperTriangularSubgroup_eq_inf` identifies the constant image of the source-facing subgroup
-- `T(F)` with the intersection used by `Subgroup.amalgamatedProductComparison`.
theorem glPolynomial_amalgamatedProductComparison_bijective :
    Function.Bijective
      (Subgroup.amalgamatedProductComparison
        (constantLinearSubgroup F)
        (upperTriangularSubgroup : Subgroup (GL (Fin 2) (Polynomial F)))) := by
  sorry

end
