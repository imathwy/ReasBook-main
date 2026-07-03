import Mathlib
import Mathlib.CategoryTheory.ConnectedComponents
import Mathlib.GroupTheory.FreeGroup.NielsenSchreier

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_2_1 (from Items/Chap03) -/
universe u v

-- Layer triage:
-- `source-facing`: a `1`-complex with an explicit set of vertices, an explicit set of oriented
-- edges, and a fixed-point-free orientation-reversing involution on edges.
-- `core/canonical`: mathlib's `Quiver` is the owner abstraction for directed multigraph-style
-- edge data, and `Quiver.IsStronglyConnected` on the symmetrified quiver is the owner predicate
-- for zigzag-connectedness.
-- `bridge/view`: a `1`-complex canonically induces a quiver on its vertex type by taking arrows
-- from `v` to `w` to be edges whose initial and terminal vertices are `v` and `w`.
-- Domain sampling:
-- 1. `Quiver` is mathlib's owner abstraction for directed multigraph-style edge data.
-- 2. `Quiver.IsStronglyConnected (Quiver.Symmetrify C)` is the owner predicate for connectedness
--    by zigzags in a reversible graph.
-- 3. `Quiver.RootedConnected` is the owner class for based reachability, so no extra local
--    wrapper around it belongs in the public API.
-- 4. `Digraph` is too coarse here because it forgets the edge set and cannot distinguish
--    parallel edges.
-- 5. `SimpleGraph.Dart` models oriented edges in an undirected simple graph, but the present item
--    starts from a primitive edge set rather than deriving darts from an underlying simple graph.
-- Primitive vs. derived:
-- the primitive data are the vertex type, edge type, endpoint maps, and inverse-edge map; the
-- induced quiver structure and zigzag-connectedness properties are derived.

/-- Definition 3-2-1: A graph, or 1-complex, consists of a vertex set, an edge set, endpoint maps,
and a fixed-point-free involution on edges that reverses orientation. -/
structure OneComplex where
  /-- The vertices of the 1-complex. -/
  Vertex : Type u
  /-- The oriented edges of the 1-complex. -/
  Edge : Type v
  /-- The initial vertex of an oriented edge. -/
  initial : Edge → Vertex
  /-- The terminal vertex of an oriented edge. -/
  terminal : Edge → Vertex
  /-- The edge with the opposite orientation. -/
  edgeInv : Edge → Edge
  /-- Reversing orientation twice gives back the original edge. -/
  edgeInv_involutive : Function.Involutive edgeInv
  /-- No edge is equal to its oppositely oriented edge. -/
  edgeInv_ne (e : Edge) : edgeInv e ≠ e
  /-- The inverse edge starts at the terminal vertex of the original edge. -/
  initial_edgeInv (e : Edge) : initial (edgeInv e) = terminal e

namespace OneComplex

/-- A 1-complex is used through its vertex type. -/
instance : CoeSort OneComplex (Type u) where
  coe := OneComplex.Vertex

variable (C : OneComplex)

/-- The edge type of a 1-complex carries the notation `e⁻¹` for the oppositely oriented edge. -/
instance edgeInvInst : Inv C.Edge := ⟨C.edgeInv⟩

/-- The reverse edge in a 1-complex terminates at the initial vertex of the original edge. -/
theorem terminal_edgeInv (e : C.Edge) : C.terminal e⁻¹ = C.initial e := by
  change C.terminal (C.edgeInv e) = C.initial e
  simpa [C.edgeInv_involutive e] using (C.initial_edgeInv (C.edgeInv e)).symm

/-- A 1-complex determines a quiver on its vertex type by taking arrows to be edges with prescribed
initial and terminal vertices. -/
instance quiver : Quiver C.Vertex where
  Hom v w := { e : C.Edge // C.initial e = v ∧ C.terminal e = w }

/-- The quiver attached to a 1-complex has involutive edge reversal induced by the inverse-edge
operation on oriented edges. -/
instance hasInvolutiveReverse : Quiver.HasInvolutiveReverse C.Vertex where
  reverse' := fun {_ _} e ↦
    ⟨e.1⁻¹, ⟨(C.initial_edgeInv e.1).trans e.2.2, (C.terminal_edgeInv e.1).trans e.2.1⟩⟩
  inv' := fun _ ↦ Subtype.ext (C.edgeInv_involutive _)

/-- The equivalence relation identifying an oriented edge with its reverse. -/
def geometricEdgeSetoid (C : OneComplex.{u, v}) : Setoid C.Edge where
  r e f := e = f ∨ e = f⁻¹
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro e
      exact Or.inl rfl
    · intro e f h
      rcases h with rfl | h
      · exact Or.inl rfl
      · right
        calc
          f = (f⁻¹)⁻¹ := by exact (C.edgeInv_involutive f).symm
          _ = e⁻¹ := by exact (congrArg Inv.inv h).symm
    · intro e f g h₁ h₂
      rcases h₁ with rfl | h₁
      · simpa using h₂
      · rcases h₂ with h₂ | h₂
        · right
          simpa [h₂] using h₁
        · left
          calc
            e = f⁻¹ := h₁
            _ = (g⁻¹)⁻¹ := by rw [h₂]
            _ = g := by exact C.edgeInv_involutive g

/-- The geometric edges of a `1`-complex, i.e. oriented edges modulo reversal. -/
abbrev GeometricEdge (C : OneComplex.{u, v}) :=
  Quotient (geometricEdgeSetoid C)

end OneComplex

/-! ### Definition_3_2_2 (from Items/Chap03) -/
universe u v

-- Layer triage:
-- `source-facing`: for a `1`-complex `C`, a path from `v` to `w` is a finite composable sequence
-- of oriented edges in `C`, together with the vertex-specific empty path and the inverse path
-- obtained by reversing edges.
-- `core/canonical`: `Quiver.Path` is mathlib's owner abstraction for finite composable edge
-- sequences, and it already carries the empty path and length API.
-- `bridge/view`: Definition `3-2-1` equips every `OneComplex` with the quiver structure and
-- involutive edge reversal needed to read the textbook notion directly as `Quiver.Path` and its
-- canonical reverse operation.
-- Domain sampling:
-- 1. `Quiver.Path` is the canonical owner for finite composable edge sequences.
-- 2. `Quiver.Path.nil` gives the empty path at each vertex.
-- 3. `Quiver.Path.length` is the canonical length function on paths.
-- 4. `Quiver.Path.reverse` is the canonical inverse-path operation once arrow reversal is
--    available through `Quiver.HasReverse`.
-- Primitive vs. derived:
-- the primitive owner is `Quiver.Path` itself; the empty path, length, and inverse path are
-- derived canonical API and should be recalled directly rather than repackaged by local wrappers.

variable (C : OneComplex.{u, v})

/- Definition 3-2-2: in a `1`-complex `C`, a path from `v` to `w` is a finite composable
sequence of oriented edges from `v` to `w`. This notion is already owned by `Quiver.Path` on the
quiver underlying `C`, so the file keeps only direct recalls of the canonical owner API. -/
#check (Quiver.Path : C → C → Type _)

/- The empty path at a vertex is the canonical constant `Quiver.Path.nil`. -/
#check Quiver.Path.nil

/- The length of a path is the canonical function `Quiver.Path.length`. -/
#check Quiver.Path.length

/- The textbook inverse of a path is the canonical reversal `Quiver.Path.reverse`. -/
#check Quiver.Path.reverse

/- Reversing a one-edge path gives the one-edge path of the reversed edge. -/
#check Quiver.Path.reverse_toPath

/-! ### Definition_3_2_3 (from Items/Chap03) -/
universe u v

open List Quiver

-- Layer triage:
-- `source-facing`: cyclic permutations of a loop, cyclic paths, reduced paths, and cyclically
-- reduced loops in a `1`-complex.
-- `core/canonical`: `Quiver.Path` is the owner abstraction for finite composable edge sequences,
-- `Quiver.Total` is the owner abstraction for arrows remembered together with their endpoints,
-- and `Cycle.Chain` is the canonical owner predicate for cyclic adjacency on the rotation
-- quotient of total arrows.
-- `bridge/view`: a loop presents a cyclic path by forgetting its basepoint and retaining only its
-- cyclically ordered edge sequence, while path decomposition via `Quiver.Path.comp` expresses the
-- source-facing cyclic-permutation relation on representatives.
-- Domain sampling:
-- 1. `Quiver.Path` is the canonical owner for finite composable paths.
-- 2. `Quiver.Total` is mathlib's canonical type of arrows together with their source and target.
-- 3. `Cycle α` is mathlib's canonical rotation quotient of lists, with `Cycle.Chain` the owner
--    predicate for cyclic adjacency conditions.
-- 4. `Quiver.Path.comp`, together with `List.IsRotated`, is the bridge from a based loop to its
--    intrinsic cyclic edge sequence.

namespace Quiver.Total

variable {V : Type u} [Quiver.{v} V]

/-- Two total arrows are composable when the target of the first equals the source of the
second. -/
def Composable (e f : Total V) : Prop :=
  e.right = f.left

/-- Reversing a total arrow swaps its endpoints and reverses the arrow. -/
def reverse [Quiver.HasReverse V] (e : Total V) : Total V :=
  match e with
  | ⟨a, b, f⟩ => ⟨b, a, Quiver.reverse f⟩

/-- A pair of consecutive total arrows is reduced when the second is not the inverse of the first.
This is the primitive local relation underlying reduced and cyclically reduced paths. -/
def IsReducedPair [Quiver.HasInvolutiveReverse V] (e f : Total V) : Prop :=
  f ≠ reverse e

@[simp] theorem left_reverse [Quiver.HasReverse V] (e : Total V) :
    (reverse e).left = e.right := by
  cases e
  rfl

@[simp] theorem right_reverse [Quiver.HasReverse V] (e : Total V) :
    (reverse e).right = e.left := by
  cases e
  rfl

@[simp] theorem hom_reverse [Quiver.HasReverse V] (e : Total V) :
    (reverse e).hom = Quiver.reverse e.hom := by
  cases e
  rfl

@[simp] theorem composable_reverse_reverse [Quiver.HasReverse V] (e f : Total V) :
    Composable (reverse e) (reverse f) ↔ Composable f e := by
  cases e
  cases f
  exact eq_comm

end Quiver.Total

namespace Quiver.Path

variable {V : Type u} [Quiver.{v} V]

/-- A loop is a path whose initial and terminal vertices coincide. -/
abbrev Loop (V : Type u) [Quiver.{v} V] :=
  Σ a : V, Path a a

/-- The ordered list of edges traversed by a path. -/
def edgeList {a b : V} (p : Path a b) : List (Total V) :=
  match p with
  | .nil => []
  | .cons q e => edgeList q ++ [⟨_, _, e⟩]

/-- Edge lists turn path concatenation into list concatenation. -/
@[simp] private theorem edgeList_comp {a b c : V} (p : Path a b) (q : Path b c) :
    edgeList (p.comp q) = edgeList p ++ edgeList q := by
  induction q with
  | nil =>
      rw [Path.comp_nil]
      simp [edgeList]
  | cons q e ih =>
      simpa [edgeList, List.append_assoc] using
        congrArg (fun L ↦ L ++ [⟨_, _, e⟩]) ih

/-- Every edge in the head position of an edge list starts at the initial vertex of the path. -/
private theorem left_eq_of_mem_head?_edgeList {a b : V} (p : Path a b) :
    ∀ e ∈ (edgeList p).head?, e.left = a := by
  induction p with
  | nil =>
      intro e h
      simp [edgeList] at h
  | cons p e ih =>
      intro f hf
      cases p with
      | nil =>
          have hf' : ⟨a, _, e⟩ = f := by
            simpa [Option.mem_def, edgeList] using hf
          cases hf'
          rfl
      | cons p' e' =>
          have hf' : f ∈ (edgeList (Path.cons p' e')).head? := by
            simpa [edgeList] using hf
          exact ih _ hf'

/-- Every edge in the last position of an edge list ends at the terminal vertex of the path. -/
private theorem right_eq_of_mem_getLast?_edgeList {a b : V} (p : Path a b) :
    ∀ e ∈ (edgeList p).getLast?, e.right = b := by
  induction p with
  | nil =>
      intro e h
      simp [edgeList] at h
  | cons p e ih =>
      intro f hf
      have hf' : ⟨_, _, e⟩ = f := by
        simpa [Option.mem_def, edgeList] using hf
      cases hf'
      rfl

/-- The ordered edge list of a path is composable in the usual linear sense. -/
private theorem edgeList_isChain {a b : V} (p : Path a b) :
    (edgeList p).IsChain Total.Composable := by
  induction p with
  | nil =>
      simp [edgeList]
  | cons p e ih =>
      refine ih.append ?_ ?_
      · simp
      · intro f hf g hg
        have hg' : ⟨_, _, e⟩ = g := by
          simpa [Option.mem_def] using hg
        cases hg'
        simpa [Total.Composable] using right_eq_of_mem_getLast?_edgeList p f hf

/-- The edge list of a loop is a cyclically composable list of total arrows. -/
private theorem edgeList_chain {a : V} (p : Path a a) :
    (edgeList p : Cycle (Total V)).Chain Total.Composable := by
  by_cases hp : edgeList p = []
  · simp [hp]
  · rcases List.exists_cons_of_ne_nil hp with ⟨e, l, hl⟩
    rw [hl, Cycle.chain_coe_cons]
    have hchain : (e :: l).IsChain Total.Composable := hl ▸ edgeList_isChain p
    refine hchain.append ?_ ?_
    · simp
    · intro f hf g hg
      have hg' : e = g := by
        simpa [Option.mem_def] using hg
      cases hg'
      have hf' : f ∈ (edgeList p).getLast? := by simpa [hl] using hf
      have hr : f.right = a := right_eq_of_mem_getLast?_edgeList p f hf'
      have hl' : e.left = a := by
        have he : e ∈ (edgeList p).head? := by
          exact hl ▸ by simp [Option.mem_def]
        exact left_eq_of_mem_head?_edgeList p e he
      simp [Total.Composable, hr, hl']

/-- Two loops differ by a cyclic permutation when one is obtained from the other by cutting it
into two composable pieces and reassembling them in the opposite order. -/
def IsCyclicPermutation (p q : Loop V) : Prop :=
  ∃ p₁ : Path p.1 q.1, ∃ p₂ : Path q.1 p.1,
    p.2 = p₁.comp p₂ ∧ q.2 = p₂.comp p₁

/-- The owner type of cyclic paths is the subtype of cyclic total-edge data satisfying the
canonical cyclic composability condition. -/
abbrev CyclicPath (V : Type u) [Quiver.{v} V] :=
  { c : Cycle (Total V) // c.Chain Total.Composable }

/-- Definition 3-2-3 (1): the cyclic path determined by a loop is its cyclically ordered edge
sequence, with the basepoint forgotten. -/
abbrev cyclicPath (p : Loop V) : CyclicPath V :=
  ⟨edgeList p.2, edgeList_chain p.2⟩

/-- A cyclic permutation of a loop preserves the underlying cyclic path. -/
theorem cyclicPath_eq_of_isCyclicPermutation {p q : Loop V} (h : IsCyclicPermutation p q) :
    cyclicPath p = cyclicPath q := by
  rcases h with ⟨p₁, p₂, hp, hq⟩
  apply Subtype.ext
  apply Cycle.coe_eq_coe.2
  rw [hp, hq, edgeList_comp, edgeList_comp]
  exact List.isRotated_append

section

variable [Quiver.HasInvolutiveReverse V]

/-- Definition 3-2-3 (2): a path is reduced when no consecutive pair of edges is of the form
`e, e⁻¹`. -/
def IsReduced {a b : V} (p : Path a b) : Prop :=
  (edgeList p).IsChain Total.IsReducedPair

/-- A cyclic path is cyclically reduced when no adjacent pair of cyclically consecutive edges is
of the form `e, e⁻¹`. -/
def IsCyclicallyReducedCycle (c : CyclicPath V) : Prop :=
  c.1.Chain Total.IsReducedPair

/-- Definition 3-2-3 (3): a loop is cyclically reduced when its underlying cyclic path is. -/
def IsCyclicallyReduced (p : Loop V) : Prop :=
  IsCyclicallyReducedCycle (cyclicPath p)

/-- For a based loop, the cyclic condition recovers the textbook reduced-plus-endpoint form. -/
theorem isCyclicallyReduced_iff (p : Loop V) :
    IsCyclicallyReduced p ↔
      IsReduced p.2 ∧
        ∀ e ∈ (edgeList p.2).head?, ∀ f ∈ (edgeList p.2).getLast?, Total.IsReducedPair e f := by
  sorry

end

/-- Definition 3-2-3 (4): a path is simple when its visited vertices do not repeat away from the
possible initial-terminal overlap; equivalently, the initial-vertex list and terminal-vertex list
of its traversed edges are both nodup. -/
def IsSimple {a b : V} (p : Path a b) : Prop :=
  Nodup p.vertices.dropLast ∧ Nodup p.vertices.tail

end Quiver.Path

/-! ### Definition_3_2_4 (from Items/Chap03) -/
universe u v w

open Quiver
open Quiver.Path

-- Layer triage:
-- `source-facing`: a 2-complex with its 1-skeleton, oriented faces, boundary cycles, inverse
-- faces, and the derived notions of a vertex lying on a face and of a boundary path.
-- `core/canonical`: `OneComplex` is the owner for the 1-skeleton, while
-- `Quiver.Path.CyclicPath`, `Quiver.Path.cyclicPath`, and the predicates from
-- Definition 3-2-3 are the owner API for cyclic boundary data in that skeleton.
-- `bridge/view`: the inverse-edge operation on a `OneComplex` induces the quiver-reversal
-- structure needed to talk about inverse loops and inverse boundary cycles in the skeleton.
-- Domain sampling:
-- 1. `OneComplex` is the project owner abstraction for the textbook 1-skeleton.
-- 2. `Quiver.Path.Loop` is the canonical owner for based loops in the induced quiver.
-- 3. `Quiver.Path.CyclicPath` is the project owner for the basepoint-free cyclic boundary object.
-- 4. `Quiver.Path.IsCyclicallyReducedCycle` is the owner predicate for cyclically reduced
--    boundary cycles, while `Quiver.Path.IsSimple` remains the owner predicate on representatives
--    used to define simple boundary.

namespace Quiver.Path

variable {V : Type u} [Quiver.{v} V]

/-- Reversing a cycle flips the adjacency relation. -/
theorem Cycle.chain_reverse_iff {α : Type*} {r : α → α → Prop} {c : Cycle α} :
    c.reverse.Chain r ↔ c.Chain (fun a b ↦ r b a) := by
  refine Quotient.inductionOn' c ?_
  intro l
  induction l using List.reverseRecOn with
  | nil =>
      simp
  | append_singleton l a ih =>
      have hne : l ++ [a] ≠ [] := by simp
      simpa [Cycle.reverse_coe, Cycle.chain_coe_cons, Cycle.chain_ne_nil _ hne,
        List.getLast_append_singleton, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.append_assoc] using
        (show (List.reverse (a :: l ++ [a])).IsChain r ↔
            (a :: l ++ [a]).IsChain (fun b c ↦ r c b) from List.isChain_reverse)

/-- The inverse of a cycle is obtained by reversing the cyclic order and inverting each edge. -/
def inverseCycle [Quiver.HasReverse V] (c : CyclicPath V) : CyclicPath V :=
  ⟨c.1.reverse.map Total.reverse, by
    rw [Cycle.chain_map, Cycle.chain_reverse_iff]
    exact c.2.imp fun e f h ↦ (Total.composable_reverse_reverse f e).2 h⟩

/-- Reversing a representative loop presents the inverse cyclic path. -/
theorem inverseCycle_cyclicPath [Quiver.HasReverse V] (p : Loop V) :
    inverseCycle (cyclicPath p) = cyclicPath ⟨p.1, p.2.reverse⟩ := by
  sorry

/-- A cycle is simple when it is represented by a simple loop. -/
def IsSimpleCycle (c : CyclicPath V) : Prop :=
  (c.1.map Total.left).Nodup ∧ (c.1.map Total.right).Nodup

/-- A cycle is simple exactly when some simple loop represents it. -/
theorem isSimpleCycle_iff (c : CyclicPath V) :
    IsSimpleCycle c ↔ ∃ p : Loop V, cyclicPath p = c ∧ IsSimple p.2 := by
  sorry

end Quiver.Path

/-- Definition 3-2-4: A 2-complex consists of a 1-skeleton, a set of oriented faces with a
fixed-point-free inverse-face involution, and a boundary map assigning to each face a cyclically
reduced cycle in the 1-skeleton such that the inverse face has the inverse boundary cycle. -/
structure TwoComplex where
  /-- The underlying 1-skeleton of the 2-complex. -/
  skeleton : OneComplex
  /-- The oriented faces of the 2-complex. -/
  Face : Type w
  /-- The boundary cycle attached to a face. -/
  boundary : Face → CyclicPath skeleton
  /-- Each face boundary is a cyclically reduced cycle in the 1-skeleton. -/
  boundary_cyclicallyReduced (D : Face) : IsCyclicallyReducedCycle (boundary D)
  /-- The inverse face with the opposite orientation. -/
  faceInv : Face → Face
  /-- Inverting the orientation of a face twice returns the original face. -/
  faceInv_involutive : Function.Involutive faceInv
  /-- A face is distinct from its inverse face. -/
  faceInv_ne (D : Face) : faceInv D ≠ D
  /-- The boundary of the inverse face is the inverse of the original boundary cycle. -/
  boundary_faceInv (D : Face) : boundary (faceInv D) = inverseCycle (boundary D)

namespace TwoComplex

/-- Faces in a 2-complex use `D⁻¹` for the oppositely oriented face. -/
instance faceInvInst (C : TwoComplex) : Inv C.Face := ⟨C.faceInv⟩

/-- Faces in a `2`-complex use the textbook notation `∂D` for the attached boundary cycle. -/
scoped notation:max "∂" D => TwoComplex.boundary _ D

/-- The equivalence relation identifying an oriented face with its opposite orientation. -/
def geometricFaceSetoid (C : TwoComplex) : Setoid C.Face where
  r D E := D = E ∨ D = E⁻¹
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro D
      exact Or.inl rfl
    · intro D E h
      rcases h with rfl | h
      · exact Or.inl rfl
      · right
        calc
          E = (E⁻¹)⁻¹ := by exact (C.faceInv_involutive E).symm
          _ = D⁻¹ := by exact (congrArg Inv.inv h).symm
    · intro D E F h₁ h₂
      rcases h₁ with rfl | h₁
      · simpa using h₂
      · rcases h₂ with h₂ | h₂
        · right
          simpa [h₂] using h₁
        · left
          calc
            D = E⁻¹ := h₁
            _ = (F⁻¹)⁻¹ := by rw [h₂]
            _ = F := by exact C.faceInv_involutive F

/-- The geometric faces of a `2`-complex, i.e. oriented faces modulo reversal. -/
abbrev GeometricFace (C : TwoComplex) :=
  Quotient (geometricFaceSetoid C)

/-- A boundary path for a face at a vertex is a closed path based at that vertex whose cyclic
class is the boundary cycle of the face. -/
abbrev BoundaryPath (C : TwoComplex) (D : C.Face) (v : C.skeleton) : Type _ :=
  { p : Quiver.Path v v // cyclicPath ⟨v, p⟩ = ∂D }

/-- A vertex lies on a face when the face has a boundary path based at that vertex. -/
def VertexOnFace (C : TwoComplex) (v : C.skeleton) (D : C.Face) : Prop :=
  Nonempty (C.BoundaryPath D v)

/-- A vertex lies on a face exactly when there exists a boundary path for that face based at the
vertex. -/
-- Proof sketch: unfold `VertexOnFace` and `BoundaryPath`; the existential data is the same on
-- both sides.
theorem vertexOnFace_iff_nonempty_boundaryPath (C : TwoComplex) (v : C.skeleton) (D : C.Face) :
    C.VertexOnFace v D ↔ Nonempty (C.BoundaryPath D v) :=
  Iff.rfl

/-- A face has simple boundary when its boundary cycle is represented by a simple loop. -/
def HasSimpleBoundary (C : TwoComplex) (D : C.Face) : Prop :=
  IsSimpleCycle (∂D)

/-- A face has simple boundary exactly when some based boundary path of the face is simple. -/
-- Proof sketch: unfold `HasSimpleBoundary` and then unfold `IsSimpleCycle`.
theorem hasSimpleBoundary_iff (C : TwoComplex) (D : C.Face) :
    C.HasSimpleBoundary D ↔ ∃ v : C.skeleton, ∃ q : C.BoundaryPath D v, IsSimple q.1 :=
  sorry

/-- A face with simple boundary has at most one boundary path based at any fixed vertex. Together
with `vertexOnFace_iff_nonempty_boundaryPath`, this yields uniqueness at every vertex on the face.
-/
-- Proof sketch: choose a simple representative of the boundary cycle; simplicity implies that two
-- rotations starting at the same vertex coincide, so the corresponding boundary paths are equal.
theorem boundaryPath_subsingleton_of_simple_boundary (C : TwoComplex) (D : C.Face)
    (v : C.skeleton) (hD : C.HasSimpleBoundary D) : Subsingleton (C.BoundaryPath D v) := sorry

end TwoComplex

/-! ### Definition_3_2_5 (from Items/Chap03) -/
-- Layer triage:
-- `source-facing`: in a `2`-complex `C`, paths are paths in the `1`-skeleton, with juxtaposition
-- as partially defined multiplication, vertexwise identity paths, and inverse path.
-- `core/canonical`: `Quiver.Path` is mathlib's owner abstraction for finite composable paths, with
-- `Quiver.Path.comp` for juxtaposition, `Quiver.Path.nil` for identity paths, and
-- `Quiver.Path.reverse` for inverse paths.
-- `bridge/view`: the textbook algebraic structure on `Π(C)` is exactly the standard quiver-path
-- API specialized to the quiver underlying the `1`-skeleton from Definitions `3-2-1` and `3-2-4`.
-- Domain sampling:
-- 1. `Quiver.Path.comp` is the canonical owner operation for concatenating composable paths.
-- 2. `Quiver.Path.comp_assoc` is the canonical associativity theorem for path juxtaposition.
-- 3. `Quiver.Path.nil_comp` and `Quiver.Path.comp_nil` are the canonical left and right identity
--    laws for the empty path at a vertex.
-- 4. `Quiver.Path.reverse` and `Quiver.Path.reverse_comp` are the canonical owner API for inverse
--    paths and the formula `(pq)⁻¹ = q⁻¹ p⁻¹`.
-- Primitive vs. derived:
-- this item contributes no new owner object beyond the canonical path-composition structure
-- already present on `Quiver.Path`, so the file should record direct recalls rather than
-- introducing a parallel local path package.

/- Definition 3-2-5: for a `2`-complex `C`, the set `Π(C)` of all paths in the `1`-skeleton
carries the canonical quiver-path multiplication by juxtaposition of composable paths.

This source-facing algebraic structure is exactly mathlib's path concatenation operation
`Quiver.Path.comp`, specialized to the quiver of the `1`-skeleton. -/
#check Quiver.Path.comp

/- Path juxtaposition is associative whenever the three paths are composable. -/
#check Quiver.Path.comp_assoc

/- The empty path at the initial vertex is a left identity for path juxtaposition. -/
#check Quiver.Path.nil_comp

/- The empty path at the terminal vertex is a right identity for path juxtaposition. -/
#check Quiver.Path.comp_nil

/- The inverse of a path is the canonical reversal of a quiver path. -/
#check Quiver.Path.reverse

/- The inverse of a product path is the product of the inverses in reverse order. -/
#check Quiver.Path.reverse_comp

/-! ### Definition_3_2_6 (from Items/Chap03) -/
universe u v

open CategoryTheory
open Quiver

-- Layer triage:
-- `source-facing`: the `1`-equivalence relation on paths and the resulting fundamental groupoid
-- `Π¹(C)`.
-- `core/canonical`: `CategoryTheory.Paths` is the owner abstraction for the path category,
-- `Relation.EqvGen` is the owner abstraction for generated equivalence relations, and
-- `CategoryTheory.Quotient` is the owner abstraction for quotient categories.
-- `bridge/view`: `Quiver.Path.pathOneHomRel` packages the source relation as a categorical
-- congruence so that `Π¹(C)` is a thin source-facing notation for the quotient category.
-- Domain sampling:
-- 1. `Relation.EqvGen` and `Relation.EqvGen.setoid` encode the generated equivalence relation.
-- 2. `CategoryTheory.Paths` is mathlib's owner category for paths in a quiver.
-- 3. `CategoryTheory.HomRel` and `CategoryTheory.Congruence` are the owner abstractions for a
--    quotient relation compatible with composition.
-- 4. `CategoryTheory.Quotient` is the canonical owner for the quotient category surface.
-- Primitive vs. derived:
-- the primitive source data are the elementary cancellation step and the generated
-- `path_one_equiv`; the quotient-category surface and the resulting groupoid structure are
-- derived from that relation.

namespace Quiver.Path

variable {V : Type u} [Quiver.{v} V] [Quiver.HasInvolutiveReverse V]

/-- A single elementary `1`-equivalence step inserts or deletes one backtracking segment
`ee⁻¹` inside a path. -/
def path_one_reduction_step {a b : V} (p q : Quiver.Path a b) : Prop :=
  ∃ (c d : V) (r : Quiver.Path a c) (e : c ⟶ d) (s : Quiver.Path c b),
    (p = (r.comp (e.toPath.comp (Quiver.reverse e).toPath)).comp s ∧ q = r.comp s) ∨
      (q = (r.comp (e.toPath.comp (Quiver.reverse e).toPath)).comp s ∧ p = r.comp s)

/-- Definition 3-2-6: two paths are `1`-equivalent when one can pass from one to the other by a
finite succession of insertions or deletions of subpaths of the form `ee⁻¹`. -/
def path_one_equiv {a b : V} (p q : Quiver.Path a b) : Prop :=
  Relation.EqvGen path_one_reduction_step p q

/-- `1`-equivalence is reflexive on paths. -/
theorem path_one_equiv_refl {a b : V} (p : Quiver.Path a b) : path_one_equiv p p :=
  Relation.EqvGen.refl p

/-- `1`-equivalence is symmetric on paths. -/
theorem path_one_equiv_symm {a b : V} {p q : Quiver.Path a b} (h : path_one_equiv p q) :
    path_one_equiv q p := by
  exact Relation.EqvGen.symm _ _ h

/-- `1`-equivalence is transitive on paths. -/
theorem path_one_equiv_trans {a b : V} {p q r : Quiver.Path a b}
    (hpq : path_one_equiv p q) (hqr : path_one_equiv q r) : path_one_equiv p r := by
  exact Relation.EqvGen.trans _ _ _ hpq hqr

/-- Path concatenation respects `1`-equivalence on both factors. -/
-- Proof sketch: first show that an elementary cancellation step remains elementary after
-- adjoining fixed prefix and suffix paths, then lift that statement through `Relation.EqvGen`.
theorem path_one_equiv_comp {a b c : V} {p p' : Quiver.Path a b} {q q' : Quiver.Path b c}
    (hp : path_one_equiv p p') (hq : path_one_equiv q q') :
    path_one_equiv (p.comp q) (p'.comp q') := sorry

/-- Path reversal respects `1`-equivalence. -/
-- Proof sketch: reversing an elementary inserted spur `ee⁻¹` produces another spur of the same
-- form inside the reversed path, and then `Relation.EqvGen` lifts this observation.
theorem path_one_equiv_reverse {a b : V} {p q : Quiver.Path a b} (h : path_one_equiv p q) :
    path_one_equiv p.reverse q.reverse := sorry

/-- A path followed by its inverse is `1`-equivalent to the empty path. -/
-- Proof sketch: induct on the path length, peel off the last edge, cancel the resulting terminal
-- backtracking pair, and use transitivity of `path_one_equiv`.
theorem comp_reverse_path_one_equiv_nil {a b : V} (p : Quiver.Path a b) :
    path_one_equiv (p.comp p.reverse) (Path.nil : Quiver.Path a a) := sorry

/-- The congruence on the path category whose quotient is the fundamental groupoid `Π¹(C)`. -/
def pathOneHomRel (V : Type u) [Quiver.{v} V] [Quiver.HasInvolutiveReverse V] :
    HomRel (CategoryTheory.Paths V) :=
  fun _ _ p q ↦ path_one_equiv p q

instance pathOneHomRel_congruence : Congruence (pathOneHomRel (V := V)) where
  equivalence := by
    intro a b
    refine ⟨?_, ?_, ?_⟩
    · intro p
      exact path_one_equiv_refl p
    · intro p q
      exact path_one_equiv_symm
    · intro p q r
      exact path_one_equiv_trans
  comp_left := by
    intro a b c f g g' h
    simpa [pathOneHomRel] using path_one_equiv_comp (path_one_equiv_refl f) h
  comp_right := by
    intro a b c f f' g h
    simpa [pathOneHomRel] using path_one_equiv_comp h (path_one_equiv_refl g)

/-- Definition 3-2-6: the fundamental groupoid `Π¹(C)` is the quotient of the path category by
`1`-equivalence. -/
abbrev pi1 (V : Type u) [Quiver.{v} V] [Quiver.HasInvolutiveReverse V] :=
  CategoryTheory.Quotient (pathOneHomRel (V := V))

notation "Π¹" "(" C ")" => Quiver.Path.pi1 C

private def pi1Inv {a b : Π¹(V)} (f : a ⟶ b) : b ⟶ a :=
  Quot.liftOn f
    (fun p ↦ Quot.mk _ p.reverse)
    (fun _ _ h ↦
      Quot.sound <| by
        rw [HomRel.compClosure_iff_self]
        exact path_one_equiv_reverse <| by
          rw [HomRel.compClosure_iff_self] at h
          exact h)

/-- Every morphism in `Π¹(C)` is invertible, with inverse induced by path reversal. -/
instance pi1_isIso {a b : Π¹(V)} (f : a ⟶ b) : IsIso f where
  out := ⟨pi1Inv f, by sorry, by sorry⟩

/-- The quotient category `Π¹(C)` is a groupoid. -/
noncomputable instance pi1_groupoid : Groupoid (Π¹(V)) :=
  Groupoid.ofIsIso fun f ↦ pi1_isIso f

end Quiver.Path

namespace OneComplex

open CategoryTheory
open scoped Quiver.Path

variable (C : OneComplex.{u, v}) (w : C)

/-- The source-facing fundamental group `π(C, w)` is the endomorphism group at `w` in the
fundamental groupoid `Π¹(C)`. -/
abbrev fundamentalGroup (C : OneComplex.{u, v}) (w : C) :=
  End (⟨w⟩ : Π¹(C))

scoped notation "π(" C ", " w ")" => OneComplex.fundamentalGroup C w

/-- The notation `π(C, w)` is the endomorphism group of the object `w` in the fundamental
groupoid `Π¹(C)`. -/
theorem fundamentalGroup_eq_end (C : OneComplex.{u, v}) (w : C) :
    π(C, w) = End (⟨w⟩ : Π¹(C)) :=
  rfl

/-- The fundamental group at `w` inherits a group structure from the groupoid structure on
`Π¹(C)`. -/
noncomputable instance fundamentalGroupGroup (C : OneComplex.{u, v}) (w : C) :
    Group (π(C, w)) :=
  inferInstance

end OneComplex

/-! ### Definition_3_2_7 (from Items/Chap03) -/
universe u v w

open CategoryTheory
open Quiver
open Quiver.Path
open scoped Quiver.Path

-- Layer triage:
-- `source-facing`: the `2`-equivalence relation on paths in a `2`-complex, its quotient
-- fundamental groupoid `π(C)`, and the canonical map from the `1`-skeleton groupoid to `π(C)`.
-- `core/canonical`: `TwoComplex` is the owner abstraction for the `2`-complex data,
-- `Quiver.Path` is the owner abstraction for paths, `Relation.EqvGen` is the owner abstraction
-- for the generated equivalence relation, and `CategoryTheory.Category` / `Groupoid` are the
-- owner abstractions for the quotient groupoid.
-- `bridge/view`: the fundamental groupoid of the `1`-skeleton is the already defined
-- `Π¹(C.skeleton)`, and the present item adds the quotient functor collapsing
-- boundary paths of faces.
-- Domain sampling:
-- 1. `TwoComplex.BoundaryPath` is the project owner for the based closed boundary paths allowed in
--    `2`-dimensional reduction.
-- 2. `Quiver.Path.path_one_equiv` is the earlier owner relation generated by cancellation of
--    spurs `ee⁻¹`.
-- 3. `Relation.EqvGen` is the canonical owner for the generated congruence relation.
-- 4. `CategoryTheory.Functor` is the canonical owner for the homomorphic image map
--    `π(C¹) ⥤ π(C)`.

namespace TwoComplex

variable (C : TwoComplex)

/-- A single elementary `2`-reduction step inserts or deletes one boundary path of a face inside
a larger path. -/
def boundary_path_reduction_step {a b : C.skeleton} (p₁ p₂ : Quiver.Path a b) : Prop :=
  ∃ (c : C.skeleton) (D : C.Face) (r : Quiver.Path a c) (q : C.BoundaryPath D c)
    (s : Quiver.Path c b),
    (p₁ = (r.comp q.1).comp s ∧ p₂ = r.comp s) ∨
      (p₂ = (r.comp q.1).comp s ∧ p₁ = r.comp s)

/-- A single elementary `2`-reduction step on paths is either a `1`-reduction step or the
insertion/deletion of a boundary path of a face. -/
def path_two_reduction_step {a b : C.skeleton} (p q : Quiver.Path a b) : Prop :=
  path_one_reduction_step p q ∨ C.boundary_path_reduction_step p q

/-- Definition 3-2-7: two paths are `2`-equivalent when one can pass from one to the other by a
finite succession of insertions or deletions of spurs `ee⁻¹` and of boundary paths of faces. -/
def path_two_equiv {a b : C.skeleton} (p q : Quiver.Path a b) : Prop :=
  Relation.EqvGen (C.path_two_reduction_step) p q

/-- Every elementary `2`-reduction step yields a `2`-equivalence. -/
-- Proof sketch: `path_two_equiv` is the equivalence closure generated by
-- `path_two_reduction_step`, so a single step is related by `Relation.EqvGen.rel`.
theorem path_two_equiv_of_reduction_step {a b : C.skeleton} {p q : Quiver.Path a b}
    (h : C.path_two_reduction_step p q) : C.path_two_equiv p q := sorry

/-- Every `1`-equivalence is also a `2`-equivalence. -/
-- Proof sketch: each generating `1`-reduction step is one of the allowed
-- `path_two_reduction_step`s, and `Relation.EqvGen` preserves implication of generators.
theorem path_two_equiv_of_path_one_equiv {a b : C.skeleton} {p q : Quiver.Path a b}
    (h : path_one_equiv p q) : C.path_two_equiv p q := sorry

/-- `2`-equivalence is reflexive on paths. -/
-- Proof sketch: use reflexivity of `Relation.EqvGen`.
theorem path_two_equiv_refl {a b : C.skeleton} (p : Quiver.Path a b) : C.path_two_equiv p p :=
  sorry

/-- `2`-equivalence is symmetric on paths. -/
-- Proof sketch: use symmetry of `Relation.EqvGen`.
theorem path_two_equiv_symm {a b : C.skeleton} {p q : Quiver.Path a b}
    (h : C.path_two_equiv p q) : C.path_two_equiv q p := sorry

/-- `2`-equivalence is transitive on paths. -/
-- Proof sketch: use transitivity of `Relation.EqvGen`.
theorem path_two_equiv_trans {a b : C.skeleton} {p q r : Quiver.Path a b}
    (hpq : C.path_two_equiv p q) (hqr : C.path_two_equiv q r) : C.path_two_equiv p r := sorry

/-- Path concatenation respects `2`-equivalence on both factors. -/
-- Proof sketch: show first that each elementary `2`-reduction step remains elementary after
-- adjoining fixed prefix and suffix paths, then lift this compatibility through `Relation.EqvGen`.
theorem path_two_equiv_comp {a b c : C.skeleton} {p p' : Quiver.Path a b}
    {q q' : Quiver.Path b c} (hp : C.path_two_equiv p p') (hq : C.path_two_equiv q q') :
    C.path_two_equiv (p.comp q) (p'.comp q') := sorry

/-- Path reversal respects `2`-equivalence. -/
-- Proof sketch: reversing a spur again gives a spur, while reversing a boundary path produces a
-- boundary path for the oppositely oriented face via `TwoComplex.boundary_faceInv`; then lift
-- the elementary statement through `Relation.EqvGen`.
theorem path_two_equiv_reverse {a b : C.skeleton} {p q : Quiver.Path a b}
    (h : C.path_two_equiv p q) : C.path_two_equiv p.reverse q.reverse := sorry

/-- A path followed by its inverse is `2`-equivalent to the empty path. -/
-- Proof sketch: this already holds for `1`-equivalence by
-- `Quiver.Path.comp_reverse_path_one_equiv_nil`, and `2`-equivalence contains `1`-equivalence.
theorem comp_reverse_path_two_equiv_nil {a b : C.skeleton} (p : Quiver.Path a b) :
    C.path_two_equiv (p.comp p.reverse) (Path.nil : Quiver.Path a a) := sorry

/-- `2`-equivalence on each path hom-set is a setoid relation. -/
instance path_two_equiv_setoid (a b : C.skeleton) : Setoid (Quiver.Path a b) where
  r := C.path_two_equiv
  iseqv := ⟨C.path_two_equiv_refl, C.path_two_equiv_symm, C.path_two_equiv_trans⟩

/-- The object type of the fundamental groupoid `π(C)` is the vertex type of the `1`-skeleton. -/
structure pi where
  /-- The underlying vertex. -/
  vertex : C.skeleton

/-- The hom-set of `π(C)` from `a` to `b` is the quotient of paths by `2`-equivalence. -/
abbrev pi_hom (a b : C.pi) :=
  Quotient (C.path_two_equiv_setoid a.vertex b.vertex)

/-- The identity morphism in `π(C)` is represented by the empty path. -/
def pi_id (a : C.pi) : C.pi_hom a a :=
  Quotient.mk'' (Path.nil : Quiver.Path a.vertex a.vertex)

/-- Composition in `π(C)` is induced by concatenation of representatives. -/
def pi_comp {a b c : C.pi} (p : C.pi_hom a b) (q : C.pi_hom b c) : C.pi_hom a c :=
  Quotient.liftOn₂ p q
    (fun r s ↦ Quotient.mk'' (r.comp s))
    (fun r s r' s' hr hs ↦
      Quotient.sound
        (show C.path_two_equiv (r.comp s) (r'.comp s') from C.path_two_equiv_comp hr hs))

/-- Inversion in `π(C)` is induced by path reversal. -/
def pi_inv {a b : C.pi} (p : C.pi_hom a b) : C.pi_hom b a :=
  Quotient.liftOn p
    (fun r ↦ Quotient.mk'' r.reverse)
    (fun _ _ h ↦ Quotient.sound (C.path_two_equiv_reverse h))

/-- Composition in `π(C)` is computed by concatenating representatives. -/
-- Proof sketch: unfold `pi_comp` and evaluate `Quotient.liftOn₂` on the chosen representatives.
theorem pi_comp_mk {a b c : C.pi} (p : Quiver.Path a.vertex b.vertex)
    (q : Quiver.Path b.vertex c.vertex) :
    C.pi_comp (Quotient.mk'' p) (Quotient.mk'' q) = Quotient.mk'' (p.comp q) := sorry

/-- Inversion in `π(C)` is computed by reversing representatives. -/
-- Proof sketch: unfold `pi_inv` and evaluate `Quotient.liftOn` on the chosen representative.
theorem pi_inv_mk {a b : C.pi} (p : Quiver.Path a.vertex b.vertex) :
    C.pi_inv (Quotient.mk'' p) = Quotient.mk'' p.reverse := sorry

/-- Left identity holds for composition in `π(C)`. -/
-- Proof sketch: quotient-induct on a representative and reduce to `Quiver.Path.nil_comp`.
theorem pi_id_comp {a b : C.pi} (f : C.pi_hom a b) : C.pi_comp (C.pi_id a) f = f := sorry

/-- Right identity holds for composition in `π(C)`. -/
-- Proof sketch: quotient-induct on a representative and reduce to `Quiver.Path.comp_nil`.
theorem pi_comp_id {a b : C.pi} (f : C.pi_hom a b) : C.pi_comp f (C.pi_id b) = f := sorry

/-- Composition in `π(C)` is associative. -/
-- Proof sketch: quotient-induct on three representatives and reduce to
-- `Quiver.Path.comp_assoc`.
theorem pi_assoc {a b c d : C.pi} (f : C.pi_hom a b) (g : C.pi_hom b c) (h : C.pi_hom c d) :
    C.pi_comp (C.pi_comp f g) h = C.pi_comp f (C.pi_comp g h) := sorry

/-- A morphism class composed with its inverse class is the identity in `π(C)`. -/
-- Proof sketch: quotient-induct on a representative path and then apply
-- `comp_reverse_path_two_equiv_nil`.
theorem pi_comp_inv {a b : C.pi} (f : C.pi_hom a b) : C.pi_comp f (C.pi_inv f) = C.pi_id a :=
  sorry

/-- The inverse class composed with a morphism class is the identity in `π(C)`. -/
-- Proof sketch: quotient-induct on a representative path and apply
-- `comp_reverse_path_two_equiv_nil` to the reversed path.
theorem pi_inv_comp {a b : C.pi} (f : C.pi_hom a b) : C.pi_comp (C.pi_inv f) f = C.pi_id b :=
  sorry

/-- The quotient structure `π(C)` is a category. -/
instance pi_category : Category C.pi where
  Hom a b := C.pi_hom a b
  id := C.pi_id
  comp := C.pi_comp
  id_comp := C.pi_id_comp
  comp_id := C.pi_comp_id
  assoc := C.pi_assoc

/-- Every morphism in `π(C)` is invertible, with inverse represented by path reversal. -/
instance pi_isIso {a b : C.pi} (f : a ⟶ b) : IsIso f where
  out := ⟨C.pi_inv f, C.pi_comp_inv f, C.pi_inv_comp f⟩

/-- The quotient structure `π(C)` is a groupoid. -/
noncomputable instance pi_groupoid : Groupoid C.pi :=
  Groupoid.ofIsIso fun f ↦ C.pi_isIso f

/-- The canonical quiver prefunctor from the `1`-skeleton of `C` to the quotient groupoid `π(C)`. -/
def pi1ToPiPrefunctor : C.skeleton ⥤q C.pi where
  obj := fun a ↦ ⟨a⟩
  map := fun e ↦ Quotient.mk'' e.toPath

/-- The canonical functor `π(C¹) ⥤ π(C)` sends a `1`-equivalence class of paths to its
`2`-equivalence class. -/
def pi1ToPi : Π¹(C.skeleton) ⥤ C.pi :=
  CategoryTheory.Quotient.lift _ (CategoryTheory.Paths.lift C.pi1ToPiPrefunctor)
    (by
      intro x y p q h
      sorry)

/- The functor `pi1ToPi` realizes the textbook statement that `π(C)` is naturally a homomorphic
image of the fundamental groupoid of the `1`-skeleton `π(C¹)`. -/

end TwoComplex

/-! ### Definition_3_2_8 (from Items/Chap03) -/
universe u v w

open CategoryTheory

-- Layer triage:
-- `source-facing`: for a vertex `v` of a `2`-complex `C`, the loops at `v` in the `1`-skeleton
-- form a semigroup, and their image in the fundamental groupoid is the fundamental group
-- `π(C, v)`.
-- `core/canonical`: `CategoryTheory.Paths C.skeleton` is the canonical path category of the
-- `1`-skeleton, `C.pi` is the already defined fundamental groupoid, and `CategoryTheory.End` is
-- the canonical owner for vertex loops in both settings.
-- `bridge/view`: the textbook notations `Π(C, v)` and `π(C, v)` are expressed by the
-- endomorphism types at `v` before and after quotienting by `2`-equivalence.
-- Domain sampling:
-- 1. `CategoryTheory.Paths.categoryPaths` is the canonical category structure on quiver paths.
-- 2. `CategoryTheory.End` is the canonical owner of loops at a chosen object.
-- 3. `CategoryTheory.End.monoid` gives the multiplicative structure on loops in a category.
-- 4. `CategoryTheory.End.group` upgrades this to a group when the ambient category is a groupoid.

namespace TwoComplex

variable (C : TwoComplex) (v : C.skeleton)

/- Definition 3-2-8: for a vertex `v` of a `2`-complex `C`, the fundamental group `π(C, v)` is
the vertex group at `v` in the fundamental groupoid `π(C)`.

The unquotiented loop set `Π(C, v)` is the endomorphism monoid of `v` in the path category of the
`1`-skeleton, while the quotient group is the endomorphism group `End (⟨v⟩ : C.pi)`. -/
#check (CategoryTheory.End (⟨v⟩ : C.pi))

/-- The source-facing loop semigroup `Π(C, v)` is the endomorphism monoid at `v` in the path
category of the `1`-skeleton. -/
abbrev loopSemigroup (C : TwoComplex) (v : C.skeleton) :=
  CategoryTheory.End ((CategoryTheory.Paths.of C.skeleton).obj v)

/-- The source-facing loop semigroup agrees with the endomorphism monoid of `v` in the path
category of the `1`-skeleton. -/
-- Proof sketch: unfold `loopSemigroup`; it is defined to be this endomorphism monoid.
theorem loopSemigroup_eq_end (C : TwoComplex) (v : C.skeleton) :
    loopSemigroup C v = CategoryTheory.End ((CategoryTheory.Paths.of C.skeleton).obj v) := sorry

/-- The source-facing fundamental group `π(C, v)` is the endomorphism group at `v` in the
fundamental groupoid `π(C)`. -/
abbrev fundamentalGroup (C : TwoComplex) (v : C.skeleton) :=
  CategoryTheory.End (⟨v⟩ : C.pi)

scoped notation "π(" C ", " v ")" => TwoComplex.fundamentalGroup C v

/-- The notation `π(C, v)` is the endomorphism group of the object `⟨v⟩` in the fundamental
groupoid `π(C)`. -/
-- Proof sketch: unfold `fundamentalGroup`; the notation is just the corresponding endomorphism
-- group.
theorem fundamentalGroup_eq_end (C : TwoComplex) (v : C.skeleton) :
    π(C, v) = CategoryTheory.End (⟨v⟩ : C.pi) := sorry

/-- The loop semigroup at `v` inherits a semigroup structure from path composition in the
`1`-skeleton. -/
instance loopSemigroupSemigroup (C : TwoComplex) (v : C.skeleton) :
    Semigroup (loopSemigroup C v) :=
  inferInstance

/-- The fundamental group at `v` inherits a group structure from the groupoid structure on
`π(C)`. -/
noncomputable instance fundamentalGroupGroup (C : TwoComplex) (v : C.skeleton) :
    Group (π(C, v)) :=
  inferInstance

end TwoComplex

/-! ### Proposition_3_2_9 (from Items/Chap03) -/
open CategoryTheory
open CategoryTheory.ObjectProperty
open IsFreeGroupoid

namespace OneComplex

-- Layer triage:
-- `source-facing`: a `1`-complex `C`, a vertex `v : C`, and the textbook claim that the
-- fundamental group `π(C, v)` is free.
-- `core/canonical`: `CategoryTheory.ConnectedComponents.Component` is the canonical owner for the
-- connected component of a chosen object, and `IsFreeGroup` is the owner predicate for freeness of
-- a group.
-- `bridge/view`: the chapter-local `OneComplex.fundamentalGroup C v`, written `π(C, v)`, is the
-- source-facing owner for the loop group at `v`; its proof is obtained by restricting the free
-- groupoid structure on `Quiver.Path.pi1 C` to the connected component of `⟨v⟩` and then
-- transporting freeness back along the fully faithful inclusion.
-- Domain sampling:
-- 1. `OneComplex.fundamentalGroup` is the chapter owner for the based fundamental group `π(C, v)`.
-- 2. `CategoryTheory.ConnectedComponents.Component` is the canonical connected-component owner for
--    reducing a loop-group statement to a connected groupoid.
-- 3. `IsFreeGroupoid.endIsFreeOfConnectedFree` is the core freeness theorem for loop groups in a
--    connected free groupoid.
-- 4. `Functor.FullyFaithful.mulEquivEnd` is the canonical bridge transporting the loop group on a
--    connected component back to the ambient endomorphism group.
-- Primitive vs. derived:
-- the primitive data are the `1`-complex `C` and the chosen vertex `v`; the connected component of
-- `⟨v⟩`, the restricted free-groupoid structure on that component, and the endomorphism-group
-- equivalence induced by the inclusion are all derived proof-internal bridge data.

/-- Proposition 3-2-9: if `C` is a `1`-complex and `v` is any vertex of `C`, then the
fundamental group `π(C, v)` is free.

The proof passes to the connected component of `⟨v⟩` in the fundamental groupoid `Π¹(C)`, applies
the canonical free-groupoid theorem there, and transports the resulting free group structure back
along the fully faithful inclusion of that component. No global connectedness hypothesis belongs in
the public statement. -/
theorem fundamentalGroup_isFree (C : OneComplex) (v : C) :
    IsFreeGroup (π(C, v)) := by
  sorry

end OneComplex

/-! ### Proposition_3_2_10 (from Items/Chap03) -/
universe u

open CategoryTheory CategoryTheory.SingleObj Quiver
open IsFreeGroupoid
open IsFreeGroupoid.SpanningTree

noncomputable section

local instance root_loopGroup_isFree {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify <| IsFreeGroupoid.Generators G)) [Arborescence T] :
    IsFreeGroup (End (show G from Quiver.root T)) := by
  simpa using IsFreeGroupoid.SpanningTree.endIsFree T

-- Layer triage:
-- `source-facing`: a finite connected `1`-complex `C`, a base vertex `v : C`, and the rank claim
-- for the fundamental group `π(C, v)`, expressed using the canonical connectedness predicate on
-- the symmetrified quiver and the owner-level notion `OneComplex.GeometricEdge`.
-- `core/canonical`: `OneComplex.fundamentalGroup` is the owner abstraction for `π(C, v)`.
-- `IsFreeGroupoid.SpanningTree.endIsFree`, `Quiver.geodesicSubtree`, and
-- `FreeGroupBasis.cardinal_eq` are the canonical free-groupoid/tree-counting tools behind the
-- proof.
-- `bridge/view`: the spanning-tree complement theorem for a free groupoid loop group is the
-- internal comparison statement from which the source-facing `OneComplex` theorem is derived.
-- Domain sampling:
-- 1. `OneComplex.fundamentalGroup` is the chapter owner for the fundamental group `π(C, v)`.
-- 2. `Quiver.IsStronglyConnected (Quiver.Symmetrify C)` is the intrinsic connectedness owner for
--    the underlying `1`-complex, replacing the bridge-level rooted-connectedness hypothesis.
-- 3. `OneComplex.GeometricEdge` is the owner abstraction for unoriented edges of a `1`-complex.
-- 4. `IsFreeGroupoid.SpanningTree.endIsFree` is the owner theorem giving freeness of the root
--    loop group of a spanning tree in a free groupoid.
-- 5. `Quiver.geodesicSubtree` is the canonical rooted spanning tree attached to a connected quiver.
-- 6. `FreeGroupBasis` is mathlib's canonical structure for “free on a specified generating type”.
-- 7. `IsFreeGroup.Generators` is the canonical generator type used to speak about the rank of a
--    free group via `Nat.card`.
-- 8. `FreeGroupBasis.cardinal_eq` is the standard bridge equating the cardinalities of two bases.

open scoped Classical in
/-- The complement of a spanning tree indexes a free basis of the root loop group. -/
-- Proof sketch: unpack the universal-property construction implicit in
-- `IsFreeGroupoid.SpanningTree.endIsFree`; the non-tree generating edges are exactly the free
-- generators produced by the Nielsen-Schreier spanning-tree argument.
private def root_loopGroup_basis_of_arborescence {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify <| IsFreeGroupoid.Generators G)) [Arborescence T] :
    FreeGroupBasis (((wideSubquiverEquivSetTotal <| wideSubquiverSymmetrify T)ᶜ : Set _))
      (End (show G from Quiver.root T)) :=
  FreeGroupBasis.ofUniqueLift ((wideSubquiverEquivSetTotal <| wideSubquiverSymmetrify T)ᶜ : Set _)
    (fun e ↦ loopOfHom T (of e.val.hom))
    (by
      intro X _ f
      let f' : Labelling (IsFreeGroupoid.Generators G) X := fun a b e ↦
        if h : e ∈ wideSubquiverSymmetrify T a b then 1 else f ⟨⟨a, b, e⟩, h⟩
      rcases unique_lift f' with ⟨F', hF', uF'⟩
      refine ⟨F'.mapEnd _, ?_, ?_⟩
      · suffices ∀ {x y} (q : x ⟶ y), F'.map (loopOfHom T q) = (F'.map q : X) by
          rintro ⟨⟨a, b, e⟩, h⟩
          change F'.map (loopOfHom T (of e)) = f ⟨⟨a, b, e⟩, h⟩
          rw [this, hF']
          exact dif_neg h
        intro x y q
        suffices ∀ {a} (p : Path (root T) a), F'.map (homOfPath T p) = 1 by
          simp only [this, treeHom, comp_as_mul, inv_as_inv, loopOfHom, inv_one, mul_one,
            one_mul, Functor.map_inv, Functor.map_comp]
        intro a p
        induction p with
        | nil =>
            change F'.map (𝟙 (show G from Quiver.root T)) = 1
            rw [F'.map_id, id_as_one]
        | cons p e ih =>
            rw [homOfPath, F'.map_comp, comp_as_mul, ih, mul_one]
            rcases e with ⟨e | e, eT⟩
            · rw [hF']
              exact dif_pos (Or.inl eT)
            · rw [F'.map_inv, inv_as_inv, inv_eq_one, hF']
              exact dif_pos (Or.inr eT)
      · intro E hE
        ext x
        suffices (functorOfMonoidHom T E).map x = F'.map x by
          erw [Functor.mapEnd_apply]
          change E (loopOfHom T x) = F'.map x at this
          change
            E
                (treeHom T (show G from Quiver.root T) ≫ x ≫
                  inv (treeHom T (show G from Quiver.root T))) =
              F'.map x at this
          have hroot : treeHom T (show G from Quiver.root T) = 𝟙 _ := by
            change treeHom T (show G from Quiver.root T) = 𝟙 _
            exact treeHom_root T
          have hx :
              treeHom T (show G from Quiver.root T) ≫ x ≫
                inv (treeHom T (show G from Quiver.root T)) =
              x := by
            rw [hroot]
            calc
              𝟙 _ ≫ x ≫ inv (𝟙 _) = x ≫ inv (𝟙 _) := by
                simp
              _ = x ≫ 𝟙 _ := by rw [IsIso.inv_id]
              _ = x := by simp
          have hxE :
              E
                  (treeHom T (show G from Quiver.root T) ≫ x ≫
                    inv (treeHom T (show G from Quiver.root T))) =
                E x := by
            simpa using congrArg E hx
          exact hxE.symm.trans this
        congr
        apply uF'
        intro a b e
        change E (loopOfHom T (of e)) = dite _ _ _
        split_ifs with h
        · rw [loopOfHom_eq_id T e h, ← End.one_def]
          simpa using E.map_one
        · exact hE ⟨⟨a, b, e⟩, h⟩)

/-- Companion bridge theorem: in a free groupoid with a chosen spanning tree, the root loop group
has rank equal to the number of generating edges outside the tree. -/
private theorem root_loopGroup_rank_eq_card_spanningTree_complement
    {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify <| IsFreeGroupoid.Generators G)) [Arborescence T] :
    Nat.card (IsFreeGroup.Generators (End (show G from Quiver.root T))) =
      Nat.card (((wideSubquiverEquivSetTotal <| wideSubquiverSymmetrify T)ᶜ : Set _)) := by
  have hcard :=
    (root_loopGroup_basis_of_arborescence T).cardinal_eq
      (IsFreeGroup.basis (End (show G from Quiver.root T)))
  simpa [Nat.card, Cardinal.toNat_lift] using congrArg Cardinal.toNat hcard.symm

namespace OneComplex

attribute [local instance] fundamentalGroup_isFree

/-- Proposition 3-2-10: if `C` is a connected `1`-complex with finitely many oriented edges and
`v` is a base vertex, then the fundamental group `π(C, v)` has rank `γ₁ - γ₀ + 1`.

Here `γ₁` is expressed canonically as `Nat.card (GeometricEdge C)` and `γ₀` as `Nat.card C`.
The intrinsic owner hypothesis
`hconnected : Quiver.IsStronglyConnected (Quiver.Symmetrify C)` replaces the bridge-level
rooted-connectedness assumption, while still providing the rooted connectivity needed internally
for the spanning-tree argument. Edge finiteness together with connectedness forces the vertex type
to be finite, so no separate vertex-finiteness binder belongs in the source-facing statement. -/
theorem fundamentalGroup_rank_eq_card_geometricEdges_sub_card_vertices_add_one
    (C : OneComplex.{u, v}) [Finite C.Edge]
    (hconnected : Quiver.IsStronglyConnected (Quiver.Symmetrify C)) (v : C) :
    Nat.card (IsFreeGroup.Generators (π(C, v))) =
      Nat.card (GeometricEdge C) - Nat.card C + 1 := by
  sorry

end OneComplex

/-! ### Proposition_3_2_11 (from Items/Chap03) -/
-- Layer triage:
-- `source-facing`: an actual `2`-complex `C`, a base vertex `v : C.skeleton`, and a
-- presentation map `φ : FreeGroup X →* π(C, v)` whose kernel is exactly the normal closure of the
-- relators `R`; the proposition states that the based fundamental group of this presentation
-- complex is the presented group on `(X; R)`.
-- `core/canonical`: `TwoComplex.fundamentalGroup`, written `π(C, v)`, is the chapter owner for
-- the based fundamental group, `PresentedGroup R` is mathlib's owner for the group presented by
-- relators `R`, and `Subgroup.normalClosure R` is the canonical relator subgroup.
-- `bridge/view`: `quotientKerEquivOfSurjective` and `quotientMulEquivOfEq` provide the quotient
-- comparison proving the source-facing identification.
-- Primitive vs. derived:
-- primitive data: the actual `TwoComplex`, the base vertex, the surjective map
-- `φ : FreeGroup X →* π(C, v)`, and the kernel description `φ.ker = Subgroup.normalClosure R`;
-- derived API: the canonical presentation equivalence `PresentedGroup R ≃* π(C, v)` and its
-- generator-image companion theorem.
-- Domain sampling:
-- 1. `TwoComplex.fundamentalGroup`, written `π(C, v)`, from Definition `3-2-8` is the chapter
--    owner for the based fundamental group.
-- 2. `PresentedGroup R`, together with `PresentedGroup.mk` and `PresentedGroup.of`, is the
--    canonical quotient owner for generators-and-relations groups.
-- 3. `Subgroup.normalClosure R` is the canonical owner for the relator subgroup of `FreeGroup X`.
-- 4. `quotientKerEquivOfSurjective` and `quotientMulEquivOfEq` are the canonical quotient
--    equivalences turning the kernel calculation into an actual multiplicative equivalence.

namespace TwoComplex

/-- Proposition 3-2-11: if the based fundamental group of a presentation complex `K(X; R)` is the
quotient of `FreeGroup X` by the normal closure of the relators `R`, then that fundamental group
is canonically isomorphic to the presented group `PresentedGroup R`. -/
noncomputable def fundamentalGroupMulEquivPresentedGroup
    {X : Type u} {R : Set (FreeGroup X)} (C : TwoComplex) (v : C.skeleton)
    (φ : FreeGroup X →* π(C, v))
    (hφ : Function.Surjective φ)
    (hker : φ.ker = Subgroup.normalClosure R) :
    PresentedGroup R ≃* π(C, v) :=
  (quotientMulEquivOfEq hker.symm).trans (quotientKerEquivOfSurjective φ hφ)

/-- The canonical presentation equivalence sends each presented generator to the corresponding loop
generator in `π(C, v)`. -/
-- Proof sketch: unfold `fundamentalGroupMulEquivPresentedGroup`; it is the quotient
-- identification followed by the first-isomorphism-theorem map, so `PresentedGroup.of x` is sent
-- to `φ (FreeGroup.of x)`.
theorem fundamentalGroupMulEquivPresentedGroup_apply_of
    {X : Type u} {R : Set (FreeGroup X)} (C : TwoComplex) (v : C.skeleton)
    (φ : FreeGroup X →* π(C, v))
    (hφ : Function.Surjective φ)
    (hker : φ.ker = Subgroup.normalClosure R)
    (x : X) :
    fundamentalGroupMulEquivPresentedGroup C v φ hφ hker (PresentedGroup.of x) =
      φ (FreeGroup.of x) := by
  rw [fundamentalGroupMulEquivPresentedGroup, PresentedGroup.of]
  change
    quotientKerEquivOfSurjective φ hφ
        ((quotientMulEquivOfEq hker.symm) ((PresentedGroup.mk R) (FreeGroup.of x))) =
      φ (FreeGroup.of x)
  have hmk :
      (quotientMulEquivOfEq hker.symm) ((PresentedGroup.mk R) (FreeGroup.of x)) =
        QuotientGroup.mk (FreeGroup.of x) := by
    change
      (quotientMulEquivOfEq hker.symm) (QuotientGroup.mk (FreeGroup.of x)) =
        QuotientGroup.mk (FreeGroup.of x)
    exact quotientMulEquivOfEq_mk hker.symm (FreeGroup.of x)
  rw [hmk]
  rfl

end TwoComplex
