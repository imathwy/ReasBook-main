module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Topology.Connected.PathConnected

public section

namespace InvarianceOfDomainSupport

-- Route correction: closed path-connected carriers do not control components of
-- their union; the cover-to-graph argument below explicitly requires openness.

/-- Helper for Theorem 62.1: a path crossing an open cover induces a walk between
any two cover members containing its endpoints. -/
lemma intersectionGraph_reachable_of_joined {X ι : Type*} [TopologicalSpace X]
    (U : ι → Set X) (hOpen : ∀ i, IsOpen (U i)) (hCover : ⋃ i, U i = Set.univ)
    {x y : X} {i j : ι} (hxi : x ∈ U i) (hyj : y ∈ U j) (hxy : Joined x y) :
    (SimpleGraph.fromRel fun i j ↦ (U i ∩ U j).Nonempty).Reachable i j := by
  -- Pull the cover back along a chosen path, so connectedness of the unit interval
  -- produces a chain of pairwise-intersecting cover members.
  let p : Path x y := hxy.somePath
  have hPulledCover : (⋃ k, p ⁻¹' U k) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro t
    have hpt : p t ∈ ⋃ k, U k := by
      rw [hCover]
      exact Set.mem_univ _
    obtain ⟨k, hpk⟩ := Set.mem_iUnion.mp hpt
    exact Set.mem_iUnion.mpr ⟨k, hpk⟩
  have hChain : Relation.TransGen
      (fun a b ↦ ((p ⁻¹' U a) ∩ (p ⁻¹' U b)).Nonempty) i j := by
    apply IsPreconnected.transGen_of_iUnion
    · rw [hPulledCover]
      exact isPreconnected_univ
    · intro k
      exact (hOpen k).preimage p.continuous
    · exact ⟨0, by simpa only [Set.mem_preimage, Path.source] using hxi⟩
    · exact ⟨1, by simpa only [Set.mem_preimage, Path.target] using hyj⟩
  -- Send each overlap in the pulled-back cover to graph reachability; repeated
  -- indices contribute only the reflexive case.
  have hOverlapReachable {a b : ι}
      (hOverlap : ((p ⁻¹' U a) ∩ (p ⁻¹' U b)).Nonempty) :
      (SimpleGraph.fromRel fun i j ↦ (U i ∩ U j).Nonempty).Reachable a b := by
    obtain ⟨t, hta, htb⟩ := hOverlap
    by_cases hab : a = b
    · subst b
      exact SimpleGraph.Reachable.refl a
    · rw [SimpleGraph.reachable_iff_reflTransGen]
      exact Relation.ReflTransGen.single
        ((SimpleGraph.fromRel_adj _ _ _).mpr
          ⟨hab, Or.inl ⟨p t, hta, htb⟩⟩)
  -- Compose the reachability steps along the overlap chain.
  rw [SimpleGraph.reachable_iff_reflTransGen]
  exact Relation.ReflTransGen.trans_induction_on hChain.to_reflTransGen
    (fun _ ↦ Relation.ReflTransGen.refl)
    (fun hOverlap ↦
      (SimpleGraph.reachable_iff_reflTransGen _ _).mp
        (hOverlapReachable hOverlap))
    (fun _ _ h₁ h₂ ↦ h₁.trans h₂)

/-- Helper for Theorem 62.1: reachability in the intersection graph of
path-connected sets joins any chosen basepoints in those sets. -/
lemma joined_basepoints_of_intersectionGraph_reachable {X ι : Type*}
    [TopologicalSpace X] (U : ι → Set X) (hPath : ∀ i, IsPathConnected (U i))
    (b : ι → X) (hb : ∀ i, b i ∈ U i) {i j : ι}
    (hij : (SimpleGraph.fromRel fun i j ↦ (U i ∩ U j).Nonempty).Reachable i j) :
    Joined (b i) (b j) := by
  -- An intersection point joins the two basepoints across one graph edge.
  have hAdjacent {a c : ι}
      (hac : (SimpleGraph.fromRel fun i j ↦ (U i ∩ U j).Nonempty).Adj a c) :
      Joined (b a) (b c) := by
    rcases (SimpleGraph.fromRel_adj _ _ _).mp hac with ⟨_, hac | hca⟩
    · obtain ⟨z, hza, hzc⟩ := hac
      exact ((hPath a).joinedIn (b a) (hb a) z hza).joined.trans
        ((hPath c).joinedIn (b c) (hb c) z hzc).joined.symm
    · obtain ⟨z, hzc, hza⟩ := hca
      exact ((hPath a).joinedIn (b a) (hb a) z hza).joined.trans
        ((hPath c).joinedIn (b c) (hb c) z hzc).joined.symm
  -- Compose these joins along a reflexive-transitive graph walk.
  rw [SimpleGraph.reachable_iff_reflTransGen] at hij
  induction hij with
  | refl => exact Joined.refl _
  | tail _ hac ih => exact ih.trans (hAdjacent hac)

/-- Helper for Theorem 62.1: path components of a space covered by open
path-connected sets are the connected components of the cover's intersection graph. -/
lemma zerothHomotopyEquiv_intersectionGraph {X ι : Type*}
    [TopologicalSpace X] (U : ι → Set X) (hOpen : ∀ i, IsOpen (U i))
    (hPath : ∀ i, IsPathConnected (U i)) (hCover : ⋃ i, U i = Set.univ) :
    Nonempty
      (ZerothHomotopy X ≃
        (SimpleGraph.fromRel fun i j ↦ (U i ∩ U j).Nonempty).ConnectedComponent) := by
  classical
  let G := SimpleGraph.fromRel fun i j ↦ (U i ∩ U j).Nonempty
  -- Choose one basepoint in every cover member and one cover member at every point.
  let b : ι → X := fun i ↦ (hPath i).nonempty.choose
  have hb (i : ι) : b i ∈ U i := (hPath i).nonempty.choose_spec
  have hMemberExists (x : X) : ∃ i, x ∈ U i := by
    have hx : x ∈ ⋃ i, U i := by
      rw [hCover]
      exact Set.mem_univ x
    exact Set.mem_iUnion.mp hx
  let member : X → ι := fun x ↦ (hMemberExists x).choose
  have hMember (x : X) : x ∈ U (member x) := (hMemberExists x).choose_spec
  -- The endpoint-to-cover-member map descends through path components.
  let toGraph : ZerothHomotopy X → G.ConnectedComponent :=
    ZerothHomotopy.lift (fun x ↦ G.connectedComponentMk (member x))
      (fun {_ _} p ↦ SimpleGraph.ConnectedComponent.sound
        (intersectionGraph_reachable_of_joined U hOpen hCover
          (hMember _) (hMember _) ⟨p⟩))
  -- Conversely, chosen basepoints descend through graph components.
  let fromGraph : G.ConnectedComponent → ZerothHomotopy X :=
    SimpleGraph.ConnectedComponent.lift (fun i ↦ ZerothHomotopy.mk (b i))
      (fun _ _ p _ ↦ ZerothHomotopy.sound
        (joined_basepoints_of_intersectionGraph_reachable U hPath b hb p.reachable).somePath)
  refine ⟨{
    toFun := toGraph
    invFun := fromGraph
    left_inv := ?_
    right_inv := ?_ }⟩
  · -- A point and the basepoint of its chosen cover member lie in one path-connected set.
    refine ZerothHomotopy.rec (fun x ↦ ?_)
    simp only [toGraph, fromGraph, ZerothHomotopy.lift_mk,
      SimpleGraph.ConnectedComponent.lift_mk]
    exact ZerothHomotopy.sound
      ((hPath (member x)).joinedIn (b _) (hb _) x (hMember x)).somePath
  · -- A cover member and the member chosen at its basepoint meet at that basepoint.
    refine SimpleGraph.ConnectedComponent.ind (fun i ↦ ?_)
    simp only [fromGraph, toGraph]
    exact SimpleGraph.ConnectedComponent.sound
      (intersectionGraph_reachable_of_joined U hOpen hCover
        (hMember (b i)) (hb i) (Joined.refl _))

end InvarianceOfDomainSupport

end
