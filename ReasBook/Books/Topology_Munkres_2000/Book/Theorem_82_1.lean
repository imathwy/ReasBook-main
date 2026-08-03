module

public import Topology_Munkres_2000.Book.Remark_82_1.Classification
public import Topology_Munkres_2000.Book.Theorem_54_6.Monodromy
public import Topology_Munkres_2000.Book.Definition_82_1.SemilocallySimplyConnected
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Subpath
import all Topology_Munkres_2000.Book.Lemma_55_1.Inclusions
import all Topology_Munkres_2000.Book.Definition_82_1.SemilocallySimplyConnected

public section

universe u

namespace ConnectedCovering

open CategoryTheory Filter TopologicalSpace Topology unitInterval
open scoped Topology

namespace SubgroupPathCover

variable {B : Type u} [TopologicalSpace B] (b₀ : B)
variable (H : Subgroup (FundamentalGroup B b₀))

/-- Helper for Theorem 82.1: reversing a composite path class reverses the factors. -/
private lemma pathClass_symm_trans {x y z : B}
    (a : Path.Homotopic.Quotient x y) (b : Path.Homotopic.Quotient y z) :
    (a.trans b).symm = b.symm.trans a.symm := by
  -- Reduce to the corresponding pointwise identity for concrete paths.
  refine Path.Homotopic.Quotient.ind₂ ?_ a b
  intro p q
  simpa only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm] using
    congrArg Path.Homotopic.Quotient.mk (Path.trans_symm p q)

/-- Helper for Theorem 82.1: reversing a path class twice restores it. -/
private lemma pathClass_symm_symm {x y : B} (a : Path.Homotopic.Quotient x y) :
    a.symm.symm = a := by
  -- Quotient induction reduces to double reversal of a concrete path.
  induction a using Path.Homotopic.Quotient.ind with
  | mk p =>
      simpa only [Path.Homotopic.Quotient.mk_symm] using
        congrArg Path.Homotopic.Quotient.mk (Path.symm_symm p)

/-- Helper for Theorem 82.1: two path classes with common endpoints are related when their
difference loop belongs to `H`. -/
private def pathClassRel {x : B} (a b : Path.Homotopic.Quotient b₀ x) : Prop :=
  FundamentalGroup.fromPath (a.trans b.symm) ∈ H

/-- Helper for Theorem 82.1: the subgroup path-class relation is reflexive. -/
private lemma pathClassRel_refl {x : B} (a : Path.Homotopic.Quotient b₀ x) :
    pathClassRel b₀ H a a := by
  -- Cancelling the path with its reverse leaves the identity loop.
  simpa only [pathClassRel, Path.Homotopic.Quotient.trans_symm,
    FundamentalGroup.one_def] using H.one_mem

/-- Helper for Theorem 82.1: the subgroup path-class relation is symmetric. -/
private lemma pathClassRel_symm {x : B} {a b : Path.Homotopic.Quotient b₀ x}
    (hab : pathClassRel b₀ H a b) : pathClassRel b₀ H b a := by
  -- Reversing the difference loop takes its inverse, which remains in the subgroup.
  change FundamentalGroup.fromPath (a.trans b.symm) ∈ H at hab
  change FundamentalGroup.fromPath (b.trans a.symm) ∈ H
  have hinv : (FundamentalGroup.fromPath (a.trans b.symm))⁻¹ ∈ H := H.inv_mem hab
  rw [FundamentalGroup.inv_def, pathClass_symm_trans,
    pathClass_symm_symm] at hinv
  exact hinv

/-- Helper for Theorem 82.1: the subgroup path-class relation is transitive. -/
private lemma pathClassRel_trans {x : B} {a b c : Path.Homotopic.Quotient b₀ x}
    (hab : pathClassRel b₀ H a b) (hbc : pathClassRel b₀ H b c) :
    pathClassRel b₀ H a c := by
  -- Multiplication concatenates the two difference loops and cancels the middle path.
  change FundamentalGroup.fromPath (a.trans b.symm) ∈ H at hab
  change FundamentalGroup.fromPath (b.trans c.symm) ∈ H at hbc
  change FundamentalGroup.fromPath (a.trans c.symm) ∈ H
  have hmul : FundamentalGroup.fromPath (b.trans c.symm) *
      FundamentalGroup.fromPath (a.trans b.symm) ∈ H := H.mul_mem hbc hab
  rw [FundamentalGroup.mul_def,
    Path.Homotopic.Quotient.trans_assoc, ← Path.Homotopic.Quotient.trans_assoc b.symm,
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans] at hmul
  exact hmul

/-- Helper for Theorem 82.1: the endpoint path classes modulo `H` form a setoid. -/
private def pathClassSetoid (x : B) : Setoid (Path.Homotopic.Quotient b₀ x) :=
  ⟨pathClassRel b₀ H,
    ⟨pathClassRel_refl b₀ H, pathClassRel_symm b₀ H,
      pathClassRel_trans b₀ H⟩⟩

/-- Helper for Theorem 82.1: the fiber of the subgroup path cover over `x`. -/
private abbrev Fiber (x : B) :=
  Quotient (pathClassSetoid b₀ H x)

/-- Helper for Theorem 82.1: the total set of the subgroup path cover. -/
private abbrev Total := Σ x : B, Fiber b₀ H x

/-- Helper for Theorem 82.1: the subgroup path cover projects a class to its endpoint. -/
private def projection : Total b₀ H → B := fun z ↦ z.1

/-- Helper for Theorem 82.1: a based path class determines a point in the fiber over its
endpoint. -/
private def point {x : B} (a : Path.Homotopic.Quotient b₀ x) : Total b₀ H :=
  ⟨x, Quotient.mk (pathClassSetoid b₀ H x) a⟩

/-- Helper for Theorem 82.1: the distinguished point is represented by the constant path
at `b₀`. -/
private def basepoint : Total b₀ H :=
  point b₀ H (Path.Homotopic.Quotient.refl b₀)

/-- Helper for Theorem 82.1: appending a fixed path preserves the subgroup path-class relation. -/
private lemma pathClassRel_trans_right {x y : B}
    (g : Path.Homotopic.Quotient x y) {a b : Path.Homotopic.Quotient b₀ x}
    (hab : pathClassRel b₀ H a b) :
    pathClassRel b₀ H (a.trans g) (b.trans g) := by
  -- Associativity and cancellation reduce the new difference loop to the old one.
  rw [pathClassRel, pathClass_symm_trans,
    Path.Homotopic.Quotient.trans_assoc,
    ← Path.Homotopic.Quotient.trans_assoc g g.symm,
    Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.refl_trans] at ⊢
  exact hab

/-- Helper for Theorem 82.1: append a path class to a point in one fiber. -/
private noncomputable def append {x y : B} (g : Path.Homotopic.Quotient x y) :
    Fiber b₀ H x → Fiber b₀ H y :=
  Quotient.map (fun a ↦ a.trans g)
    (fun _ _ h ↦ pathClassRel_trans_right b₀ H g h)

/-- Helper for Theorem 82.1: appending the constant path does not change a fiber point. -/
private lemma append_refl {x : B} (a : Fiber b₀ H x) :
    append b₀ H (Path.Homotopic.Quotient.refl x) a = a := by
  -- Quotient induction reduces the assertion to the right unit law for paths.
  refine Quotient.inductionOn a ?_
  intro q
  exact congrArg (Quotient.mk (pathClassSetoid b₀ H x))
    (Path.Homotopic.Quotient.trans_refl q)

/-- Helper for Theorem 82.1: successive appends agree with appending the composite path. -/
private lemma append_trans {x y z : B} (g : Path.Homotopic.Quotient x y)
    (k : Path.Homotopic.Quotient y z) (a : Fiber b₀ H x) :
    append b₀ H k (append b₀ H g a) = append b₀ H (g.trans k) a := by
  -- Quotient induction exposes associativity of path-class composition.
  refine Quotient.inductionOn a ?_
  intro q
  exact congrArg (Quotient.mk (pathClassSetoid b₀ H z))
    (Path.Homotopic.Quotient.trans_assoc q g k)

/-- Helper for Theorem 82.1: appending a path and then its reverse restores a fiber point. -/
private lemma append_symm {x y : B} (g : Path.Homotopic.Quotient x y)
    (a : Fiber b₀ H x) :
    append b₀ H g.symm (append b₀ H g a) = a := by
  -- The composite append is the constant path by path cancellation.
  rw [append_trans, Path.Homotopic.Quotient.trans_symm, append_refl]

/-- Helper for Theorem 82.1: reverse append followed by forward append also restores a point. -/
private lemma append_symm_left {x y : B} (g : Path.Homotopic.Quotient x y)
    (a : Fiber b₀ H y) :
    append b₀ H g (append b₀ H g.symm a) = a := by
  -- Apply the preceding cancellation law to the reversed path.
  calc
    append b₀ H g (append b₀ H g.symm a) =
        append b₀ H g.symm.symm (append b₀ H g.symm a) :=
      congrArg (fun k ↦ append b₀ H k (append b₀ H g.symm a))
        (pathClass_symm_symm g).symm
    _ = a := append_symm b₀ H g.symm a

/-- Helper for Theorem 82.1: a represented point projects to the endpoint of its path class. -/
private lemma projection_point {x : B} (a : Path.Homotopic.Quotient b₀ x) :
    projection b₀ H (point b₀ H a) = x := by
  -- The endpoint is stored as the first component of the total-space point.
  rfl

/-- Helper for Theorem 82.1: a loop represents the distinguished point exactly when its
fundamental-group class belongs to `H`. -/
private lemma point_loop_eq_basepoint_iff (a : Path.Homotopic.Quotient b₀ b₀) :
    point b₀ H a = basepoint b₀ H ↔ FundamentalGroup.fromPath a ∈ H := by
  -- Equality in the fiber is precisely the defining subgroup path-class relation.
  unfold basepoint point
  rw [Sigma.mk.inj_iff]
  simp only [heq_iff_eq, true_and]
  rw [Quotient.eq'']
  -- Reversing the constant class is still constant, so the defining relation simplifies.
  have hrefl : (Path.Homotopic.Quotient.refl b₀).symm =
      Path.Homotopic.Quotient.refl b₀ := by
    change Path.Homotopic.Quotient.mk (Path.refl b₀).symm =
      Path.Homotopic.Quotient.mk (Path.refl b₀)
    rw [Path.refl_symm]
  change FundamentalGroup.fromPath
      (a.trans (Path.Homotopic.Quotient.refl b₀).symm) ∈ H ↔
    FundamentalGroup.fromPath a ∈ H
  rw [hrefl, Path.Homotopic.Quotient.trans_refl]

/-- Helper for Theorem 82.1: inclusion through a nested subspace induces the same
fundamental-group map as direct inclusion into the ambient space. -/
private lemma mapOfSubtype_comp_mapOfSubset {A U : Set B} (h : A ⊆ U) (a : A) :
    (FundamentalGroup.mapOfSubtype U ⟨a, h a.property⟩).comp
        (FundamentalGroup.mapOfSubset h a) =
      FundamentalGroup.mapOfSubtype A a := by
  -- Expose both inclusion maps and compare their action on each loop class.
  ext p
  simp only [MonoidHom.comp_apply]
  rw [FundamentalGroup.mapOfSubset_eq_map_inclusion]
  unfold FundamentalGroup.mapOfSubtype
  have innerMap :
      FundamentalGroup.map (ContinuousMap.inclusion h) a p =
        Path.Homotopic.Quotient.map p (ContinuousMap.inclusion h) :=
    FundamentalGroup.map_apply (ContinuousMap.inclusion h) a p
  -- The nested continuous inclusions agree with direct subtype inclusion on path classes.
  have nestedMap :
      Path.Homotopic.Quotient.map
          (Path.Homotopic.Quotient.map p (ContinuousMap.inclusion h))
          (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)) =
        Path.Homotopic.Quotient.map p
          (⟨Subtype.val, continuous_subtype_val⟩ : C(A, B)) := by
    exact (Path.Homotopic.Quotient.map_comp
      (p := p) (f := ContinuousMap.inclusion h)
      (g := (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)))).symm
  have outerToDirect :
      FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B))
          ⟨a, h a.property⟩
            (Path.Homotopic.Quotient.map p (ContinuousMap.inclusion h)) =
        FundamentalGroup.map
          (⟨Subtype.val, continuous_subtype_val⟩ : C(A, B)) a p := by
    rw [FundamentalGroup.map_apply, FundamentalGroup.map_apply]
    exact nestedMap
  exact (congrArg
    (fun q ↦ FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B))
      ⟨a, h a.property⟩ q) innerMap).trans outerToDirect

/-- Helper for Theorem 82.1: every point has an open path-connected neighborhood whose
inclusion induces the trivial fundamental-group homomorphism. -/
private lemma exists_open_pathConnected_mapOfSubtype_eq_one
    [LocallyPathConnectedSpace B] [SemilocallySimplyConnectedSpace B] (x : B) :
    ∃ (U : Set B) (hxU : x ∈ U), IsOpen U ∧ IsPathConnected U ∧
      FundamentalGroup.mapOfSubtype U ⟨x, hxU⟩ = 1 := by
  -- Refine the semilocally simply connected neighborhood by the path-connected basis.
  obtain ⟨V, hV, hmapV⟩ := SemilocallySimplyConnectedSpace.exists_nhds x
  obtain ⟨U, ⟨hUopen, hxU, hUpath⟩, hUV⟩ :=
    (isOpen_isPathConnected_basis x).mem_iff.mp hV
  change U ⊆ V at hUV
  refine ⟨U, hxU, hUopen, hUpath, ?_⟩
  -- The smaller inclusion factors through the original trivial inclusion.
  have hfactor := mapOfSubtype_comp_mapOfSubset (B := B) hUV ⟨x, hxU⟩
  have hcenter : (⟨x, hUV hxU⟩ : V) =
      SemilocallySimplyConnectedSpace.point hV := Subtype.ext rfl
  have hmapV' : FundamentalGroup.mapOfSubtype V ⟨x, hUV hxU⟩ = 1 := by
    rw [hcenter]
    exact hmapV
  rw [hmapV'] at hfactor
  simpa only [MonoidHom.one_comp, id_eq] using hfactor.symm

/-- Helper for Theorem 82.1: a good path-connected neighborhood can be chosen inside a
prescribed open neighborhood. -/
private lemma exists_open_pathConnected_mapOfSubtype_eq_one_subset
    [LocallyPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    {O : Set B} (hO : IsOpen O) {x : B} (hxO : x ∈ O) :
    ∃ (U : Set B) (hxU : x ∈ U), IsOpen U ∧ IsPathConnected U ∧ U ⊆ O ∧
      FundamentalGroup.mapOfSubtype U ⟨x, hxU⟩ = 1 := by
  -- Intersect the semilocally simply connected neighborhood with `O`, then refine it by
  -- the path-connected neighborhood basis.
  obtain ⟨V, hV, hmapV⟩ := SemilocallySimplyConnectedSpace.exists_nhds x
  obtain ⟨U, ⟨hUopen, hxU, hUpath⟩, hUsub⟩ :=
    (isOpen_isPathConnected_basis x).mem_iff.mp
      (inter_mem hV (hO.mem_nhds hxO))
  change U ⊆ V ∩ O at hUsub
  refine ⟨U, hxU, hUopen, hUpath, fun y hy ↦ hUsub hy |>.2, ?_⟩
  -- The inclusion through `V` is trivial, so the smaller direct inclusion is trivial too.
  have hfactor := mapOfSubtype_comp_mapOfSubset (B := B)
    (fun y hy ↦ hUsub hy |>.1) ⟨x, hxU⟩
  have hcenter : (⟨x, (hUsub hxU).1⟩ : V) =
      SemilocallySimplyConnectedSpace.point hV := Subtype.ext rfl
  have hmapV' : FundamentalGroup.mapOfSubtype V ⟨x, (hUsub hxU).1⟩ = 1 := by
    rw [hcenter]
    exact hmapV
  rw [hmapV'] at hfactor
  simpa only [MonoidHom.one_comp, id_eq] using hfactor.symm

/-- Helper for Theorem 82.1: mapping a composite path class maps both factors. -/
private lemma pathClass_map_trans {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x y z : X} (q : Path.Homotopic.Quotient x y)
    (r : Path.Homotopic.Quotient y z) (f : C(X, Y)) :
    (q.trans r).map f = (q.map f).trans (r.map f) := by
  -- Quotient induction reduces functoriality to the pointwise path identity.
  refine Path.Homotopic.Quotient.ind₂ ?_ q r
  intro p s
  simpa only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_map] using
    congrArg Path.Homotopic.Quotient.mk (Path.map_trans p s f.continuous)

/-- Helper for Theorem 82.1: mapping a reversed path class reverses the mapped class. -/
private lemma pathClass_map_symm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x y : X} (q : Path.Homotopic.Quotient x y) (f : C(X, Y)) :
    q.symm.map f = (q.map f).symm := by
  -- Quotient induction reduces compatibility with reversal to concrete paths.
  induction q using Path.Homotopic.Quotient.ind with
  | mk p =>
      simpa only [Path.Homotopic.Quotient.mk_symm,
        Path.Homotopic.Quotient.mk_map] using
        (congrArg Path.Homotopic.Quotient.mk (Path.map_symm p f.continuous)).symm

/-- Helper for Theorem 82.1: paths in a neighborhood with trivial inclusion-induced
fundamental-group map have the same ambient class when their endpoints agree. -/
private lemma pathClass_map_eq_of_mapOfSubtype_eq_one {U : Set B} {x y : B}
    (hx : x ∈ U) (hy : y ∈ U)
    (hmap : FundamentalGroup.mapOfSubtype U ⟨x, hx⟩ = 1)
    (q r : Path.Homotopic.Quotient (⟨x, hx⟩ : U) ⟨y, hy⟩) :
    q.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)) =
      r.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)) := by
  -- Triviality kills the loop obtained by following `q` and returning along `r`.
  have hloop := DFunLike.congr_fun hmap
    (FundamentalGroup.fromPath (q.trans r.symm))
  have hSubtype : FundamentalGroup.mapOfSubtype U ⟨x, hx⟩ =
      FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)) ⟨x, hx⟩ := rfl
  rw [hSubtype, FundamentalGroup.map_apply] at hloop
  simp only [MonoidHom.one_apply, FundamentalGroup.one_def] at hloop
  -- Cancel the common return path in the ambient fundamental groupoid.
  have hcomp :
      (q.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B))).trans
          (r.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B))).symm =
        Path.Homotopic.Quotient.refl x := by
    rw [pathClass_map_trans, pathClass_map_symm] at hloop
    exact hloop
  -- Postcompose the loop equation with `r`; the groupoid cancellation laws close the goal.
  have hcancel := congrArg
    (fun s : Path.Homotopic.Quotient x x ↦
      s.trans (r.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)))) hcomp
  simpa only [Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.trans_refl,
    Path.Homotopic.Quotient.refl_trans] using hcancel

/-- Helper for Theorem 82.1: a path class stays in `U` when it has a representative whose
entire image lies in `U`. -/
private def PathClassIn (U : Set B) {x y : B}
    (q : Path.Homotopic.Quotient x y) : Prop :=
  ∃ p : Path x y, Path.Homotopic.Quotient.mk p = q ∧ ∀ t, p t ∈ U

/-- Helper for Theorem 82.1: the constant path class stays in every set containing its point. -/
private lemma pathClassIn_refl {U : Set B} {x : B} (hx : x ∈ U) :
    PathClassIn U (Path.Homotopic.Quotient.refl x) := by
  -- The concrete constant path supplies the required representative.
  exact ⟨Path.refl x, rfl, fun _ ↦ hx⟩

/-- Helper for Theorem 82.1: concatenating two path classes that stay in `U` again stays in
`U`. -/
private lemma PathClassIn.trans {U : Set B} {x y z : B}
    {q : Path.Homotopic.Quotient x y} {r : Path.Homotopic.Quotient y z}
    (hq : PathClassIn U q) (hr : PathClassIn U r) : PathClassIn U (q.trans r) := by
  -- Concatenate the chosen representatives and use the union formula for their ranges.
  obtain ⟨p, rfl, hp⟩ := hq
  obtain ⟨s, rfl, hs⟩ := hr
  refine ⟨p.trans s, Path.Homotopic.Quotient.mk_trans p s, ?_⟩
  rw [← Set.range_subset_iff, Path.trans_range]
  exact Set.union_subset (Set.range_subset_iff.mpr hp) (Set.range_subset_iff.mpr hs)

/-- Helper for Theorem 82.1: a path class staying in a smaller set stays in every larger set. -/
private lemma PathClassIn.mono {U V : Set B} {x y : B}
    {q : Path.Homotopic.Quotient x y} (hUV : U ⊆ V) (hq : PathClassIn U q) :
    PathClassIn V q := by
  -- Keep the same representative and enlarge its pointwise membership proof.
  obtain ⟨p, hpq, hpU⟩ := hq
  exact ⟨p, hpq, fun t ↦ hUV (hpU t)⟩

/-- Helper for Theorem 82.1: the target of a path class staying in `U` belongs to `U`. -/
private lemma PathClassIn.target_mem {U : Set B} {x y : B}
    {q : Path.Homotopic.Quotient x y} (hq : PathClassIn U q) : y ∈ U := by
  -- Evaluate the chosen representative at its target endpoint.
  obtain ⟨p, hpq, hpU⟩ := hq
  have hend := hpU 1
  rw [p.target] at hend
  exact hend

/-- Helper for Theorem 82.1: path-connectedness supplies a path class staying in the set
between any two of its points. -/
private lemma exists_pathClassIn {U : Set B} (hU : IsPathConnected U)
    {x y : B} (hx : x ∈ U) (hy : y ∈ U) :
    ∃ q : Path.Homotopic.Quotient x y, PathClassIn U q := by
  -- Choose the path furnished by `JoinedIn` and pass to its homotopy class.
  let p := (hU.joinedIn x hx y hy).somePath
  exact ⟨Path.Homotopic.Quotient.mk p, p, rfl,
    fun t ↦ (hU.joinedIn x hx y hy).somePath_mem t⟩

/-- Helper for Theorem 82.1: on a good neighborhood, all path classes staying in that
neighborhood and sharing endpoints are equal. -/
private lemma pathClass_eq_of_mapOfSubtype_eq_one {U : Set B} {x y : B}
    (hx : x ∈ U) (hy : y ∈ U)
    (hmap : FundamentalGroup.mapOfSubtype U ⟨x, hx⟩ = 1)
    {q r : Path.Homotopic.Quotient x y}
    (hq : PathClassIn U q) (hr : PathClassIn U r) : q = r := by
  -- Lift representatives to the subtype `U`, where the preceding triviality lemma applies.
  obtain ⟨p, hpq, hpU⟩ := hq
  obtain ⟨s, hsr, hsU⟩ := hr
  let pU : Path (⟨x, hx⟩ : U) ⟨y, hy⟩ :=
    { toFun := fun t ↦ ⟨p t, hpU t⟩
      continuous_toFun := p.continuous.subtype_mk _
      source' := Subtype.ext p.source
      target' := Subtype.ext p.target }
  let sU : Path (⟨x, hx⟩ : U) ⟨y, hy⟩ :=
    { toFun := fun t ↦ ⟨s t, hsU t⟩
      continuous_toFun := s.continuous.subtype_mk _
      source' := Subtype.ext s.source
      target' := Subtype.ext s.target }
  have hlift (v : Path (⟨x, hx⟩ : U) ⟨y, hy⟩) :
      (Path.Homotopic.Quotient.mk v).map
          (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)) =
        Path.Homotopic.Quotient.mk (v.map continuous_subtype_val) := by
    -- This is the computation rule for mapping a concrete path class.
    exact (Path.Homotopic.Quotient.mk_map v
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B))).symm
  have hpLift : (Path.Homotopic.Quotient.mk pU).map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)) =
      Path.Homotopic.Quotient.mk p := by
    rw [hlift]
    congr 1
  have hsLift : (Path.Homotopic.Quotient.mk sU).map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)) =
      Path.Homotopic.Quotient.mk s := by
    rw [hlift]
    congr 1
  calc
    q = Path.Homotopic.Quotient.mk p := hpq.symm
    _ = (Path.Homotopic.Quotient.mk pU).map
          (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)) := hpLift.symm
    _ = (Path.Homotopic.Quotient.mk sU).map
          (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)) :=
      pathClass_map_eq_of_mapOfSubtype_eq_one hx hy hmap _ _
    _ = Path.Homotopic.Quotient.mk s := hsLift
    _ = r := hsr

/-- Helper for Theorem 82.1: the sheet through a fiber point consists of all points obtained
by appending path classes that stay in `U`. -/
private def sheet (U : Set B) {x : B} (a : Fiber b₀ H x) : Set (Total b₀ H) :=
  {z | ∃ q : Path.Homotopic.Quotient x z.1,
    PathClassIn U q ∧ z.2 = append b₀ H q a}

/-- Helper for Theorem 82.1: a sheet contains its defining fiber point when the center lies
in the underlying neighborhood. -/
private lemma mem_sheet_center {U : Set B} {x : B} (hx : x ∈ U)
    (a : Fiber b₀ H x) : (⟨x, a⟩ : Total b₀ H) ∈ sheet b₀ H U a := by
  -- Use the constant path class and the right-unit law for append.
  refine ⟨Path.Homotopic.Quotient.refl x, pathClassIn_refl hx, ?_⟩
  exact (append_refl b₀ H a).symm

/-- Helper for Theorem 82.1: extending a point of one sheet through a smaller neighborhood
stays in the original sheet. -/
private lemma sheet_through_subset {U W : Set B} {x : B} {a : Fiber b₀ H x}
    {z w : Total b₀ H} (hz : z ∈ sheet b₀ H U a) (hWU : W ⊆ U)
    (hw : w ∈ sheet b₀ H W z.2) : w ∈ sheet b₀ H U a := by
  -- Concatenate the path reaching `z` with the path inside `W` reaching `w`.
  obtain ⟨q, hqU, hzq⟩ := hz
  obtain ⟨r, hrW, hwr⟩ := hw
  refine ⟨q.trans r, hqU.trans (hrW.mono hWU), ?_⟩
  calc
    w.2 = append b₀ H r z.2 := hwr
    _ = append b₀ H r (append b₀ H q a) :=
      congrArg (append b₀ H r) hzq
    _ = append b₀ H (q.trans r) a := append_trans b₀ H q r a

/-- Helper for Theorem 82.1: every point of a sheet projects into its underlying
neighborhood. -/
private lemma projection_mem_of_mem_sheet {U : Set B} {x : B} {a : Fiber b₀ H x}
    {z : Total b₀ H} (hz : z ∈ sheet b₀ H U a) : projection b₀ H z ∈ U := by
  -- Read endpoint membership from the representative witnessing sheet membership.
  obtain ⟨q, ⟨p, hpq, hpU⟩, hzq⟩ := hz
  have hend := hpU 1
  rw [p.target] at hend
  exact hend

/-- Helper for Theorem 82.1: a sheet over a path-connected set projects onto exactly that
set. -/
private lemma projection_image_sheet {U : Set B} {x : B} (hx : x ∈ U)
    (hU : IsPathConnected U) (a : Fiber b₀ H x) :
    projection b₀ H '' sheet b₀ H U a = U := by
  -- Every represented endpoint lies in `U`, and path-connectedness reaches every point of `U`.
  ext y
  constructor
  · rintro ⟨z, ⟨q, ⟨p, hpq, hpU⟩, hzq⟩, rfl⟩
    have hend := hpU 1
    rw [p.target] at hend
    exact hend
  · intro hy
    obtain ⟨q, hqU⟩ := exists_pathClassIn hU hx hy
    refine ⟨⟨y, append b₀ H q a⟩, ?_, rfl⟩
    exact ⟨q, hqU, rfl⟩

/-- Helper for Theorem 82.1: the neighborhoods used as covering charts are open,
path-connected, and have trivial inclusion-induced fundamental group map. -/
@[reducible] private def IsGoodNeighborhood (U : Set B) (x : B) (hx : x ∈ U) : Prop :=
  IsOpen U ∧ IsPathConnected U ∧ FundamentalGroup.mapOfSubtype U ⟨x, hx⟩ = 1

/-- Helper for Theorem 82.1: the basic open sets are sheets over good neighborhoods. -/
private def IsBasicSheet (S : Set (Total b₀ H)) : Prop :=
  ∃ (U : Set B) (x : B) (hx : x ∈ U) (a : Fiber b₀ H x),
    IsGoodNeighborhood U x hx ∧ S = sheet b₀ H U a

/-- Helper for Theorem 82.1: topology generated by the good sheets of the subgroup path
cover. -/
@[reducible] private def subgroupPathCoverTopology : TopologicalSpace (Total b₀ H) :=
  TopologicalSpace.generateFrom {S | IsBasicSheet b₀ H S}

/-- Helper for Theorem 82.1: install the topology generated by good sheets on the total
space. -/
private instance subgroupPathCoverTopologicalSpace : TopologicalSpace (Total b₀ H) :=
  subgroupPathCoverTopology b₀ H

/-- Helper for Theorem 82.1: good sheets form a basis for the subgroup path-cover topology. -/
private lemma sheet_isTopologicalBasis [LocallyPathConnectedSpace B]
    [SemilocallySimplyConnectedSpace B] :
    IsTopologicalBasis {S : Set (Total b₀ H) | IsBasicSheet b₀ H S} := by
  -- Refine two sheets meeting at `z` by a good sheet centered at `z` inside their overlap.
  refine ⟨?_, ?_, ?_⟩
  · rintro S₁ ⟨U, x, hxU, a, ⟨hUopen, hUpath, hUmap⟩, rfl⟩
      S₂ ⟨V, y, hyV, c, ⟨hVopen, hVpath, hVmap⟩, rfl⟩ z ⟨hzU, hzV⟩
    obtain ⟨W, hzW, hWopen, hWpath, hWsub, hWmap⟩ :=
      exists_open_pathConnected_mapOfSubtype_eq_one_subset
        (hUopen.inter hVopen)
        ⟨projection_mem_of_mem_sheet b₀ H hzU,
          projection_mem_of_mem_sheet b₀ H hzV⟩
    refine ⟨sheet b₀ H W z.2, ?_, mem_sheet_center b₀ H hzW z.2, ?_⟩
    · exact ⟨W, z.1, hzW, z.2, ⟨hWopen, hWpath, hWmap⟩, rfl⟩
    · intro w hw
      exact ⟨sheet_through_subset b₀ H hzU (fun t ht ↦ (hWsub ht).1) hw,
        sheet_through_subset b₀ H hzV (fun t ht ↦ (hWsub ht).2) hw⟩
  · -- Every total-space point lies in a good sheet centered at itself.
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨U, hzU, hUopen, hUpath, hUmap⟩ :=
      exists_open_pathConnected_mapOfSubtype_eq_one z.1
    exact Set.mem_sUnion.mpr ⟨sheet b₀ H U z.2,
      ⟨U, z.1, hzU, z.2, ⟨hUopen, hUpath, hUmap⟩, rfl⟩,
      mem_sheet_center b₀ H hzU z.2⟩
  · -- The installed topology is definitionally generated by this family.
    rfl

/-- Helper for Theorem 82.1: every good sheet is open in the generated topology. -/
private lemma isOpen_sheet [LocallyPathConnectedSpace B]
    [SemilocallySimplyConnectedSpace B] {U : Set B} {x : B} {hx : x ∈ U}
    (hU : IsGoodNeighborhood U x hx) (a : Fiber b₀ H x) :
    IsOpen (sheet b₀ H U a) := by
  -- A good sheet is one of the members of the established topological basis.
  exact (sheet_isTopologicalBasis b₀ H).isOpen
    ⟨U, x, hx, a, hU, rfl⟩

/-- Helper for Theorem 82.1: the endpoint projection is continuous for the sheet topology. -/
private lemma continuous_projection [LocallyPathConnectedSpace B]
    [SemilocallySimplyConnectedSpace B] : Continuous (projection b₀ H) := by
  -- Refine the preimage of an arbitrary open set pointwise by good sheets lying over it.
  rw [continuous_def]
  intro O hO
  refine (sheet_isTopologicalBasis b₀ H).isOpen_iff.mpr ?_
  intro z hz
  obtain ⟨U, hzU, hUopen, hUpath, hUsub, hUmap⟩ :=
    exists_open_pathConnected_mapOfSubtype_eq_one_subset hO hz
  refine ⟨sheet b₀ H U z.2, ?_, mem_sheet_center b₀ H hzU z.2, ?_⟩
  · exact ⟨U, z.1, hzU, z.2, ⟨hUopen, hUpath, hUmap⟩, rfl⟩
  · intro w hw
    exact hUsub (projection_mem_of_mem_sheet b₀ H hw)

/-- Helper for Theorem 82.1: the endpoint projection is an open map for the sheet topology. -/
private lemma isOpenMap_projection [LocallyPathConnectedSpace B]
    [SemilocallySimplyConnectedSpace B] : IsOpenMap (projection b₀ H) := by
  -- It suffices to compute the image of each basic sheet, which is its open base set.
  rw [(sheet_isTopologicalBasis b₀ H).isOpenMap_iff]
  intro S hS
  obtain ⟨U, x, hxU, a, ⟨hUopen, hUpath, hUmap⟩, rfl⟩ := hS
  rw [projection_image_sheet b₀ H hxU hUpath a]
  exact hUopen

/-- Helper for Theorem 82.1: projection is injective on a sheet over a good neighborhood. -/
private lemma projection_injectiveOn_sheet {U : Set B} {x : B} {hx : x ∈ U}
    (hU : IsGoodNeighborhood U x hx) (a : Fiber b₀ H x) :
    Set.InjOn (projection b₀ H) (sheet b₀ H U a) := by
  -- Equal projections align endpoints; uniqueness of path classes in `U` aligns fiber values.
  rintro ⟨z, c⟩ hz ⟨y, d⟩ hy hzy
  change z = y at hzy
  subst y
  obtain ⟨q, hqU, hc⟩ := hz
  obtain ⟨r, hrU, hd⟩ := hy
  have hqr := pathClass_eq_of_mapOfSubtype_eq_one hx
    hqU.target_mem hU.2.2 hqU hrU
  have hcd : c = d := calc
    c = append b₀ H q a := hc
    _ = append b₀ H r a := congrArg (fun s ↦ append b₀ H s a) hqr
    _ = d := hd.symm
  exact congrArg (fun e : Fiber b₀ H z ↦ (⟨z, e⟩ : Total b₀ H)) hcd

/-- Helper for Theorem 82.1: projection from a good sheet to its base neighborhood is
bijective. -/
private lemma sheetProjection_bijective {U : Set B} {x : B} {hx : x ∈ U}
    (hU : IsGoodNeighborhood U x hx) (a : Fiber b₀ H x) :
    Function.Bijective
      (fun z : sheet b₀ H U a ↦
        (⟨projection b₀ H z,
          projection_mem_of_mem_sheet b₀ H z.property⟩ : U)) := by
  -- Injectivity is the sheet result above; surjectivity chooses a path inside `U`.
  constructor
  · intro z w hzw
    apply Subtype.ext
    exact projection_injectiveOn_sheet b₀ H hU a z.property w.property
      (congrArg Subtype.val hzw)
  · intro y
    obtain ⟨q, hqU⟩ := exists_pathClassIn hU.2.1 hx y.property
    refine ⟨⟨⟨y, append b₀ H q a⟩, q, hqU, rfl⟩, ?_⟩
    exact Subtype.ext rfl

/-- Helper for Theorem 82.1: the projection equivalence from a good sheet to its base. -/
private noncomputable def sheetProjectionEquiv {U : Set B} {x : B} {hx : x ∈ U}
    (hU : IsGoodNeighborhood U x hx) (a : Fiber b₀ H x) :
    sheet b₀ H U a ≃ U :=
  Equiv.ofBijective
    (fun z : sheet b₀ H U a ↦
      (⟨projection b₀ H z,
        projection_mem_of_mem_sheet b₀ H z.property⟩ : U))
    (sheetProjection_bijective b₀ H hU a)

/-- Helper for Theorem 82.1: the projection equivalence from a good sheet is continuous. -/
private lemma continuous_sheetProjectionEquiv [LocallyPathConnectedSpace B]
    [SemilocallySimplyConnectedSpace B] {U : Set B} {x : B} {hx : x ∈ U}
    (hU : IsGoodNeighborhood U x hx) (a : Fiber b₀ H x) :
    Continuous (sheetProjectionEquiv b₀ H hU a) := by
  -- Restrict the continuous projection and then codomain-restrict it to `U`.
  exact ((continuous_projection b₀ H).comp continuous_subtype_val).subtype_mk _

/-- Helper for Theorem 82.1: the projection equivalence from a good sheet is open. -/
private lemma isOpenMap_sheetProjectionEquiv [LocallyPathConnectedSpace B]
    [SemilocallySimplyConnectedSpace B] {U : Set B} {x : B} {hx : x ∈ U}
    (hU : IsGoodNeighborhood U x hx) (a : Fiber b₀ H x) :
    IsOpenMap (sheetProjectionEquiv b₀ H hU a) := by
  -- Restrict the open projection to the open sheet and codomain-restrict it to `U`.
  have hmaps : Set.MapsTo (projection b₀ H) (sheet b₀ H U a) U :=
    fun z hz ↦ projection_mem_of_mem_sheet b₀ H hz
  exact (isOpenMap_projection b₀ H).mapsToRestrict
    (isOpen_sheet b₀ H hU a) hmaps

/-- Helper for Theorem 82.1: each good sheet is homeomorphic to its base neighborhood by
projection. -/
private noncomputable def sheetHomeomorph [LocallyPathConnectedSpace B]
    [SemilocallySimplyConnectedSpace B] {U : Set B} {x : B} {hx : x ∈ U}
    (hU : IsGoodNeighborhood U x hx) (a : Fiber b₀ H x) :
    sheet b₀ H U a ≃ₜ U :=
  (sheetProjectionEquiv b₀ H hU a).toHomeomorphOfContinuousOpen
    (continuous_sheetProjectionEquiv b₀ H hU a)
    (isOpenMap_sheetProjectionEquiv b₀ H hU a)

/-- Helper for Theorem 82.1: every good sheet is path-connected. -/
private lemma isPathConnected_sheet [LocallyPathConnectedSpace B]
    [SemilocallySimplyConnectedSpace B] {U : Set B} {x : B} {hx : x ∈ U}
    (hU : IsGoodNeighborhood U x hx) (a : Fiber b₀ H x) :
    IsPathConnected (sheet b₀ H U a) := by
  -- Transfer path-connectedness of `U` across the sheet homeomorphism.
  rw [isPathConnected_iff_pathConnectedSpace]
  letI : PathConnectedSpace U := isPathConnected_iff_pathConnectedSpace.mp hU.2.1
  exact (sheetHomeomorph b₀ H hU a).symm.surjective.pathConnectedSpace
    (sheetHomeomorph b₀ H hU a).symm.continuous

/-- Helper for Theorem 82.1: the sheet topology on the total space is locally
path-connected. -/
private lemma locallyPathConnectedSpace [LocallyPathConnectedSpace B]
    [SemilocallySimplyConnectedSpace B] : LocallyPathConnectedSpace (Total b₀ H) := by
  -- Use the good-sheet neighborhood basis and the preceding path-connectedness result.
  refine LocallyPathConnectedSpace.of_bases
    (fun z ↦ (sheet_isTopologicalBasis b₀ H).nhds_hasBasis) ?_
  intro z S hS
  obtain ⟨⟨U, x, hxU, a, hU, rfl⟩, hzS⟩ := hS
  exact isPathConnected_sheet b₀ H hU a

/-- Helper for Theorem 82.1: the endpoint projection is surjective. -/
private lemma projection_surjective [PathConnectedSpace B] :
    Function.Surjective (projection b₀ H) := by
  -- Represent every endpoint by any path from the chosen base point.
  intro y
  let p := PathConnectedSpace.somePath b₀ y
  exact ⟨point b₀ H (Path.Homotopic.Quotient.mk p), projection_point b₀ H _⟩

/-- Helper for Theorem 82.1: choose a path class inside a path-connected neighborhood from
its chart center to a specified point. -/
private noncomputable def chosenPathClass {U : Set B} {x : B} (hx : x ∈ U)
    (hU : IsPathConnected U) (y : U) : Path.Homotopic.Quotient x y :=
  Classical.choose (exists_pathClassIn hU hx y.property)

/-- Helper for Theorem 82.1: the chosen local path class stays in the neighborhood. -/
private lemma chosenPathClass_mem {U : Set B} {x : B} (hx : x ∈ U)
    (hU : IsPathConnected U) (y : U) :
    PathClassIn U (chosenPathClass hx hU y) := by
  -- This is the specification of the selected witness.
  exact Classical.choose_spec (exists_pathClassIn hU hx y.property)

/-- Helper for Theorem 82.1: local product coordinates record the endpoint and transport the
fiber point back to the chart center. -/
private noncomputable def localCoordinate {U : Set B} {x : B} (hx : x ∈ U)
    (hU : IsPathConnected U) :
    projection b₀ H ⁻¹' U → U × WithDiscreteTopology (Fiber b₀ H x) :=
  fun z ↦
    (⟨z.1.1, z.2⟩,
      WithTopology.toTopology ⊥
        (append b₀ H (chosenPathClass hx hU ⟨z.1.1, z.2⟩).symm z.1.2))

/-- Helper for Theorem 82.1: inverse local coordinates append the chosen path to the fiber
coordinate. -/
private noncomputable def localCoordinateInv {U : Set B} {x : B} (hx : x ∈ U)
    (hU : IsPathConnected U) :
    U × WithDiscreteTopology (Fiber b₀ H x) → projection b₀ H ⁻¹' U :=
  fun ya ↦
    ⟨⟨ya.1.1, append b₀ H (chosenPathClass hx hU ya.1)
      (WithTopology.ofTopology ya.2)⟩, ya.1.2⟩

/-- Helper for Theorem 82.1: converting to local coordinates and back fixes a total-space
point. -/
private lemma localCoordinateInv_left {U : Set B} {x : B} (hx : x ∈ U)
    (hU : IsPathConnected U) :
    Function.LeftInverse (localCoordinateInv b₀ H hx hU)
      (localCoordinate b₀ H hx hU) := by
  -- The forward and reverse appends cancel in the fiber.
  rintro ⟨⟨y, c⟩, hy⟩
  unfold localCoordinate localCoordinateInv
  apply Subtype.ext
  have hc := append_symm_left b₀ H (chosenPathClass hx hU ⟨y, hy⟩) c
  exact congrArg (fun d : Fiber b₀ H y ↦ (⟨y, d⟩ : Total b₀ H)) hc

/-- Helper for Theorem 82.1: converting from local coordinates and back fixes the product
coordinate. -/
private lemma localCoordinateInv_right {U : Set B} {x : B} (hx : x ∈ U)
    (hU : IsPathConnected U) :
    Function.RightInverse (localCoordinateInv b₀ H hx hU)
      (localCoordinate b₀ H hx hU) := by
  -- The chosen append followed by its reverse cancels.
  rintro ⟨y, a⟩
  unfold localCoordinate localCoordinateInv
  apply Prod.ext
  · exact Subtype.ext rfl
  · exact congrArg (WithTopology.toTopology (⊥ : TopologicalSpace (Fiber b₀ H x)))
      (append_symm b₀ H (chosenPathClass hx hU y)
        (WithTopology.ofTopology a))

/-- Helper for Theorem 82.1: the local coordinate functions form an equivalence. -/
private noncomputable def localCoordinateEquiv {U : Set B} {x : B} (hx : x ∈ U)
    (hU : IsPathConnected U) :
    projection b₀ H ⁻¹' U ≃ U × WithDiscreteTopology (Fiber b₀ H x) :=
  { toFun := localCoordinate b₀ H hx hU
    invFun := localCoordinateInv b₀ H hx hU
    left_inv := localCoordinateInv_left b₀ H hx hU
    right_inv := localCoordinateInv_right b₀ H hx hU }

/-- Helper for Theorem 82.1: a local fiber coordinate equals `a` exactly on the sheet
indexed by `a`. -/
private lemma localCoordinate_snd_eq_iff_mem_sheet {U : Set B} {x : B} {hx : x ∈ U}
    (hU : IsGoodNeighborhood U x hx) (z : projection b₀ H ⁻¹' U)
    (a : WithDiscreteTopology (Fiber b₀ H x)) :
    (localCoordinate b₀ H hx hU.2.1 z).2 = a ↔
      z.1 ∈ sheet b₀ H U (WithTopology.ofTopology a) := by
  -- Compare every path in `U` with the chosen chart path, then cancel reverse appends.
  let q := chosenPathClass hx hU.2.1 ⟨z.1.1, z.2⟩
  have hqU : PathClassIn U q := chosenPathClass_mem hx hU.2.1 ⟨z.1.1, z.2⟩
  constructor
  · intro hcoord
    refine ⟨q, hqU, ?_⟩
    have hcoord' := congrArg WithTopology.ofTopology hcoord
    change append b₀ H q.symm z.1.2 = WithTopology.ofTopology a at hcoord'
    have happend := congrArg (append b₀ H q) hcoord'
    rw [append_symm_left] at happend
    exact happend
  · rintro ⟨r, hrU, hzr⟩
    have hrq : r = q :=
      pathClass_eq_of_mapOfSubtype_eq_one hx z.2 hU.2.2 hrU hqU
    change WithTopology.toTopology ⊥ (append b₀ H q.symm z.1.2) = a
    rw [hzr, hrq]
    exact congrArg (WithTopology.toTopology (⊥ : TopologicalSpace (Fiber b₀ H x)))
      (append_symm b₀ H q (WithTopology.ofTopology a))

/-- Helper for Theorem 82.1: the local coordinate equivalence is continuous. -/
private lemma continuous_localCoordinate [LocallyPathConnectedSpace B]
    [SemilocallySimplyConnectedSpace B] {U : Set B} {x : B} {hx : x ∈ U}
    (hU : IsGoodNeighborhood U x hx) :
    Continuous (localCoordinate b₀ H hx hU.2.1) := by
  -- The endpoint coordinate is continuous; discrete fiber-coordinate fibers are open sheets.
  apply Continuous.prodMk
  · exact ((continuous_projection b₀ H).comp continuous_subtype_val).subtype_mk _
  · rw [continuous_discrete_rng]
    intro a
    have hfiber :
        (fun z ↦ (localCoordinate b₀ H hx hU.2.1 z).2) ⁻¹' {a} =
          Subtype.val ⁻¹' sheet b₀ H U (WithTopology.ofTopology a) := by
      ext z
      exact localCoordinate_snd_eq_iff_mem_sheet b₀ H hU z a
    change IsOpen
      ((fun z ↦ (localCoordinate b₀ H hx hU.2.1 z).2) ⁻¹' {a})
    rw [hfiber]
    exact (isOpen_sheet b₀ H hU (WithTopology.ofTopology a)).preimage
      continuous_subtype_val

/-- Helper for Theorem 82.1: each fixed discrete-fiber branch of the inverse local
coordinate map is continuous. -/
private lemma continuous_localCoordinateInv_branch [LocallyPathConnectedSpace B]
    [SemilocallySimplyConnectedSpace B] {U : Set B} {x : B} {hx : x ∈ U}
    (hU : IsGoodNeighborhood U x hx)
    (a : WithDiscreteTopology (Fiber b₀ H x)) :
    Continuous (fun y : U ↦ localCoordinateInv b₀ H hx hU.2.1 (y, a)) := by
  -- Compare the explicit branch with the inverse of the corresponding sheet homeomorphism.
  let g : U → projection b₀ H ⁻¹' U := fun y ↦
    ⟨((sheetHomeomorph b₀ H hU (WithTopology.ofTopology a)).symm y).1,
      projection_mem_of_mem_sheet b₀ H
        ((sheetHomeomorph b₀ H hU (WithTopology.ofTopology a)).symm y).2⟩
  have hg : Continuous g :=
    ((continuous_subtype_val.comp
      (sheetHomeomorph b₀ H hU (WithTopology.ofTopology a)).symm.continuous).subtype_mk _)
  apply hg.congr
  intro y
  apply Subtype.ext
  have hinvMem : (localCoordinateInv b₀ H hx hU.2.1 (y, a)).1 ∈
      sheet b₀ H U (WithTopology.ofTopology a) :=
    ⟨chosenPathClass hx hU.2.1 y, chosenPathClass_mem hx hU.2.1 y, rfl⟩
  have hproj : projection b₀ H
      ((sheetHomeomorph b₀ H hU (WithTopology.ofTopology a)).symm y).1 =
      projection b₀ H (localCoordinateInv b₀ H hx hU.2.1 (y, a)).1 := by
    change projection b₀ H
        ((sheetHomeomorph b₀ H hU (WithTopology.ofTopology a)).symm y).1 = y.1
    exact congrArg Subtype.val
      ((sheetHomeomorph b₀ H hU (WithTopology.ofTopology a)).apply_symm_apply y)
  exact projection_injectiveOn_sheet b₀ H hU (WithTopology.ofTopology a)
    ((sheetHomeomorph b₀ H hU (WithTopology.ofTopology a)).symm y).2 hinvMem hproj

/-- Helper for Theorem 82.1: the inverse local coordinate equivalence is continuous. -/
private lemma continuous_localCoordinateInv [LocallyPathConnectedSpace B]
    [SemilocallySimplyConnectedSpace B] {U : Set B} {x : B} {hx : x ∈ U}
    (hU : IsGoodNeighborhood U x hx) :
    Continuous (localCoordinateInv b₀ H hx hU.2.1) := by
  -- Continuity out of a product with discrete right factor is checked branchwise.
  rw [continuous_prod_of_discrete_right]
  intro a
  exact continuous_localCoordinateInv_branch b₀ H hU a

/-- Helper for Theorem 82.1: the preimage of a good neighborhood has the expected product
homeomorphism. -/
private noncomputable def localCoordinateHomeomorph [LocallyPathConnectedSpace B]
    [SemilocallySimplyConnectedSpace B] {U : Set B} {x : B} {hx : x ∈ U}
    (hU : IsGoodNeighborhood U x hx) :
    projection b₀ H ⁻¹' U ≃ₜ U × WithDiscreteTopology (Fiber b₀ H x) :=
  (localCoordinateEquiv b₀ H hx hU.2.1).toHomeomorphOfContinuousOpen
    (continuous_localCoordinate b₀ H hU)
    ((localCoordinateEquiv b₀ H hx hU.2.1).continuous_symm_iff.mp
      (continuous_localCoordinateInv b₀ H hU))

/-- Helper for Theorem 82.1: every base point is evenly covered by a good neighborhood. -/
private lemma projection_isEvenlyCovered [LocallyPathConnectedSpace B]
    [SemilocallySimplyConnectedSpace B] (x : B) :
    IsEvenlyCovered (projection b₀ H) x
      (WithDiscreteTopology (Fiber b₀ H x)) := by
  -- Choose a good neighborhood and use its product coordinate homeomorphism.
  obtain ⟨U, hxU, hUopen, hUpath, hUmap⟩ :=
    exists_open_pathConnected_mapOfSubtype_eq_one x
  let hU : IsGoodNeighborhood U x hxU := ⟨hUopen, hUpath, hUmap⟩
  refine ⟨inferInstance, U, hxU, hUopen,
    hUopen.preimage (continuous_projection b₀ H),
    localCoordinateHomeomorph b₀ H hU, ?_⟩
  -- The first product coordinate is the endpoint projection by construction.
  intro z
  rfl

/-- Helper for Theorem 82.1: the endpoint projection of the subgroup path cover is a
covering map. -/
private lemma projection_isCoveringMap [LocallyPathConnectedSpace B]
    [SemilocallySimplyConnectedSpace B] : IsCoveringMap (projection b₀ H) := by
  -- Convert the explicit temporary discrete fiber into mathlib's canonical actual fiber.
  intro x
  exact (projection_isEvenlyCovered b₀ H x).to_isEvenlyCovered_preimage

/-- Helper for Theorem 82.1: the distinguished point projects to `b₀`. -/
private lemma projection_basepoint : projection b₀ H (basepoint b₀ H) = b₀ := by
  -- The endpoint is the first component of the dependent pair.
  rfl

/-- Helper for Theorem 82.1: the prefix of a path through time `c`, with its source
normalized to the chosen base point. -/
private def prefixPath {x : B} (p : Path b₀ x) (c : I) : Path b₀ (p c) :=
  (p.subpath 0 c).cast p.source.symm rfl

/-- Helper for Theorem 82.1: the point of the subgroup path cover represented by a path
prefix. -/
private def prefixPoint {x : B} (p : Path b₀ x) (c : I) : Total b₀ H :=
  point b₀ H (Path.Homotopic.Quotient.mk (prefixPath b₀ p c))

/-- Helper for Theorem 82.1: heterogeneously equal endpoint path classes represent the
same total-space point after their endpoints are identified. -/
private lemma point_eq_of_pathClass_heq {x y : B}
    (a : Path.Homotopic.Quotient b₀ x)
    (c : Path.Homotopic.Quotient b₀ y) (hxy : x = y) (hac : a ≍ c) :
    point b₀ H a = point b₀ H c := by
  -- Eliminate the endpoint equality first; heterogeneous equality then becomes ordinary
  -- equality in one quotient fiber.
  subst y
  have hac' : a = c := eq_of_heq hac
  subst c
  rfl

/-- Helper for Theorem 82.1: the zero-time prefix is the constant path, with only its target
endpoint transported along the source equation of `p`. -/
private lemma prefixPath_zero {x : B} (p : Path b₀ x) :
    prefixPath b₀ p 0 = (Path.refl b₀).cast rfl p.source := by
  -- Both paths are pointwise constant at `b₀`.
  apply Path.ext
  funext t
  simp [prefixPath, Path.subpath]

/-- Helper for Theorem 82.1: the one-time prefix is the original path, with only its target
endpoint transported along the target equation of `p`. -/
private lemma prefixPath_one {x : B} (p : Path b₀ x) :
    prefixPath b₀ p 1 = p.cast rfl p.target := by
  -- The affine reparameterization from zero to one is the identity.
  apply Path.ext
  funext t
  simp [prefixPath, Path.subpath]

/-- Helper for Theorem 82.1: a prefix followed by the subpath from `c` to `d` has the same
path-homotopy class as the prefix ending at `d`. -/
private lemma prefixClass_trans_subpath {x : B} (p : Path b₀ x) (c d : I) :
    (Path.Homotopic.Quotient.mk (prefixPath b₀ p c)).trans
        (Path.Homotopic.Quotient.mk (p.subpath c d)) =
      Path.Homotopic.Quotient.mk (prefixPath b₀ p d) := by
  -- Concatenating adjacent subpaths is homotopic to the full prefix.
  have hB : Path.Homotopic
      ((p.subpath 0 c).trans (p.subpath c d)) (p.subpath 0 d) :=
    ⟨Path.Homotopy.subpathTransSubpath p 0 c d⟩
  -- Cast the common source from `p 0` to `b₀` only after constructing the homotopy.
  have hcast := hB.pathCast p.source.symm rfl
  have hleft :
      ((p.subpath 0 c).trans (p.subpath c d)).cast p.source.symm rfl =
        (prefixPath b₀ p c).trans (p.subpath c d) :=
    Path.cast_trans (p.subpath 0 c) (p.subpath c d) p.source.symm rfl rfl
  rw [hleft] at hcast
  rw [← Path.Homotopic.Quotient.mk_trans]
  exact Quotient.sound hcast

/-- Helper for Theorem 82.1: appending an interval path to a prefix point gives the later
prefix point. -/
private lemma append_prefixPoint {x : B} (p : Path b₀ x) (c d : I) :
    append b₀ H (Path.Homotopic.Quotient.mk (p.subpath c d))
        (prefixPoint b₀ H p c).2 =
      (prefixPoint b₀ H p d).2 := by
  -- Quotient mapping turns append into path-class composition, which is the preceding lemma.
  exact congrArg (Quotient.mk (pathClassSetoid b₀ H (p d)))
    (prefixClass_trans_subpath b₀ p c d)

/-- Helper for Theorem 82.1: the family of points represented by path prefixes is
continuous in the subgroup path-cover topology. -/
private lemma continuous_prefixPoint [LocallyPathConnectedSpace B]
    [SemilocallySimplyConnectedSpace B] {x : B} (p : Path b₀ x) :
    Continuous (prefixPoint b₀ H p) := by
  -- Check continuity on a basic sheet and refine around each time by a path-connected
  -- interval neighborhood that maps into the sheet's base neighborhood.
  letI : LocallyPathConnectedSpace I :=
    (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  rw [(sheet_isTopologicalBasis b₀ H).continuous_iff]
  intro S hS
  obtain ⟨U, y, hyU, a, hU, rfl⟩ := hS
  apply isOpen_iff_mem_nhds.mpr
  intro c hc
  have hpcU : p c ∈ U := projection_mem_of_mem_sheet b₀ H hc
  obtain ⟨V, ⟨hVopen, hcV, hVpath⟩, hVsub⟩ :=
    (isOpen_isPathConnected_basis c).mem_iff.mp
      ((hU.1.preimage p.continuous).mem_nhds hpcU)
  refine mem_of_superset (hVopen.mem_nhds hcV) ?_
  intro d hdV
  let r : Path.Homotopic.Quotient (p c) (p d) :=
    Path.Homotopic.Quotient.mk (p.subpath c d)
  have hrU : PathClassIn U r := by
    -- Path-connected subsets of the ordered interval contain the whole segment between any
    -- two of their points, so this short subpath remains in `V` and hence maps into `U`.
    refine ⟨p.subpath c d, rfl, ?_⟩
    have hsegment : Set.uIcc c d ⊆ V :=
      hVpath.isConnected.isPreconnected.ordConnected.uIcc_subset hcV hdV
    have hidRange : Set.range (Path.id.subpath c d) ⊆ V := by
      rw [Path.range_subpath]
      simpa using hsegment
    intro t
    exact hVsub (hidRange ⟨t, rfl⟩)
  obtain ⟨q, hqU, hcq⟩ := hc
  refine ⟨q.trans r, hqU.trans hrU, ?_⟩
  -- Extend the path reaching the current prefix by the short path inside `U`.
  calc
    (prefixPoint b₀ H p d).2 = append b₀ H r (prefixPoint b₀ H p c).2 :=
      (append_prefixPoint b₀ H p c d).symm
    _ = append b₀ H r (append b₀ H q a) := congrArg (append b₀ H r) hcq
    _ = append b₀ H (q.trans r) a := append_trans b₀ H q r a

/-- Helper for Theorem 82.1: the zero-time prefix point is the distinguished point. -/
private lemma prefixPoint_zero {x : B} (p : Path b₀ x) :
    prefixPoint b₀ H p 0 = basepoint b₀ H := by
  -- Compare the concrete prefix with the transported constant path, then discard the
  -- endpoint transport by heterogeneous path-class equality.
  apply point_eq_of_pathClass_heq b₀ H _ _ p.source
  have hpath := congrArg Path.Homotopic.Quotient.mk (prefixPath_zero b₀ p)
  exact (heq_of_eq hpath).trans
    (Path.Homotopic.Quotient.cast_heq
      (γ := Path.Homotopic.Quotient.refl b₀) rfl p.source)

/-- Helper for Theorem 82.1: the one-time prefix point is represented by the original path. -/
private lemma prefixPoint_one {x : B} (p : Path b₀ x) :
    prefixPoint b₀ H p 1 =
      point b₀ H (Path.Homotopic.Quotient.mk p) := by
  -- Compare the full prefix with the transported original path, then discard the endpoint
  -- transport by heterogeneous path-class equality.
  apply point_eq_of_pathClass_heq b₀ H _ _ p.target
  have hpath := congrArg Path.Homotopic.Quotient.mk (prefixPath_one b₀ p)
  exact (heq_of_eq hpath).trans
    (Path.Homotopic.Quotient.cast_heq
      (γ := Path.Homotopic.Quotient.mk p) rfl p.target)

/-- Helper for Theorem 82.1: the continuous prefix-point family is a path from the
distinguished point to the point represented by `p`. -/
private def prefixLiftPath [LocallyPathConnectedSpace B]
    [SemilocallySimplyConnectedSpace B] {x : B} (p : Path b₀ x) :
    Path (basepoint b₀ H)
      (point b₀ H (Path.Homotopic.Quotient.mk p)) where
  toFun := prefixPoint b₀ H p
  continuous_toFun := continuous_prefixPoint b₀ H p
  source' := prefixPoint_zero b₀ H p
  target' := prefixPoint_one b₀ H p

/-- Helper for Theorem 82.1: projecting the canonical prefix lift recovers the original
base path up to path-homotopy class. -/
private lemma prefixLiftPath_map [LocallyPathConnectedSpace B]
    [SemilocallySimplyConnectedSpace B] {x : B} (p : Path b₀ x) :
    (Path.Homotopic.Quotient.mk (prefixLiftPath b₀ H p)).map
        ⟨projection b₀ H, continuous_projection b₀ H⟩ =
      Path.Homotopic.Quotient.mk p := by
  -- Projection forgets the prefix class and retains its endpoint `p t` pointwise.
  rw [← Path.Homotopic.Quotient.mk_map]
  apply congrArg Path.Homotopic.Quotient.mk
  apply Path.ext
  funext t
  rfl

/-- Helper for Theorem 82.1: every represented base path lifts from the distinguished point
to the point represented by its path class. -/
private lemma pathToPoint [LocallyPathConnectedSpace B]
    [SemilocallySimplyConnectedSpace B] {x : B}
    (q : Path.Homotopic.Quotient b₀ x) :
    ∃ Γ : Path.Homotopic.Quotient (basepoint b₀ H) (point b₀ H q),
      Γ.map ⟨projection b₀ H, continuous_projection b₀ H⟩ = q := by
  -- Choose a concrete representative and use its continuous family of prefix classes.
  induction q using Path.Homotopic.Quotient.ind with
  | mk p =>
      exact ⟨Path.Homotopic.Quotient.mk (prefixLiftPath b₀ H p),
        prefixLiftPath_map b₀ H p⟩

/-- Helper for Theorem 82.1: the distinguished point is joined to every point of the total
space. -/
private lemma joined_basepoint [LocallyPathConnectedSpace B]
    [SemilocallySimplyConnectedSpace B] (z : Total b₀ H) :
    Joined (basepoint b₀ H) z := by
  -- Choose a representative of the quotient fiber point and use its canonical lifted path.
  rcases z with ⟨x, a⟩
  obtain ⟨q, rfl⟩ := Quotient.exists_rep a
  change Joined (basepoint b₀ H) (point b₀ H q)
  obtain ⟨Γ, hΓ⟩ := pathToPoint b₀ H q
  induction Γ using Path.Homotopic.Quotient.ind with
  | mk p => exact ⟨p⟩

/-- Helper for Theorem 82.1: the subgroup path-cover total space is path-connected. -/
private lemma pathConnectedSpace [LocallyPathConnectedSpace B]
    [SemilocallySimplyConnectedSpace B] : PathConnectedSpace (Total b₀ H) := by
  -- Join arbitrary points through the distinguished point.
  refine ⟨⟨basepoint b₀ H⟩, ?_⟩
  intro z w
  exact (joined_basepoint b₀ H z).symm.trans (joined_basepoint b₀ H w)

/-- Helper for Theorem 82.1: casting a path class along reflexive endpoint proofs leaves
the class unchanged. -/
private lemma pathClassCast_self {X : Type*} [TopologicalSpace X] {x y : X}
    (q : Path.Homotopic.Quotient x y) (hx : x = x) (hy : y = y) :
    q.cast hx hy = q := by
  -- Proof irrelevance reduces both endpoint equations to reflexivity.
  rw [Subsingleton.elim hx rfl, Subsingleton.elim hy rfl,
    Path.Homotopic.Quotient.cast_rfl_rfl]

/-- Helper for Theorem 82.1: the subgroup induced by the subgroup path cover is exactly the
prescribed subgroup. -/
private lemma fundamentalGroupMapRange_eq [LocallyPathConnectedSpace B]
    [SemilocallySimplyConnectedSpace B] :
    (projection_isCoveringMap b₀ H).fundamentalGroupMapRange
      (projection_basepoint b₀ H) = H := by
  -- Work directly with the range definition so the selected base point remains the explicit
  -- point of this construction rather than an opaque canonical fiber wrapper.
  ext γ
  change γ ∈ (FundamentalGroup.mapOfEq
      ⟨projection b₀ H, (projection_isCoveringMap b₀ H).continuous⟩
      (projection_basepoint b₀ H)).range ↔ γ ∈ H
  let qγ := FundamentalGroup.toPath γ
  constructor
  · rintro ⟨δ, hδ⟩
    have hmap :
        (FundamentalGroup.toPath δ).map
            ⟨projection b₀ H, (projection_isCoveringMap b₀ H).continuous⟩ = qγ := by
      -- Expand the induced homomorphism and remove its reflexive endpoint casts.
      rw [FundamentalGroup.mapOfEq_apply] at hδ
      exact (pathClassCast_self _ _ _).symm.trans hδ
    let ebase : projection b₀ H ⁻¹' {b₀} :=
      ⟨basepoint b₀ H, projection_basepoint b₀ H⟩
    let epoint : projection b₀ H ⁻¹' {b₀} :=
      ⟨point b₀ H qγ, projection_point b₀ H qγ⟩
    obtain ⟨Γ, hΓ⟩ := pathToPoint b₀ H qγ
    have hloopCast :
        (FundamentalGroup.toPath δ).map
            ⟨projection b₀ H, (projection_isCoveringMap b₀ H).continuous⟩ =
          qγ.cast ebase.2 ebase.2 := by
      exact hmap.trans (pathClassCast_self qγ ebase.2 ebase.2).symm
    have hpointCast :
        Γ.map ⟨projection b₀ H, (projection_isCoveringMap b₀ H).continuous⟩ =
          qγ.cast ebase.2 epoint.2 := by
      exact hΓ.trans (pathClassCast_self qγ ebase.2 epoint.2).symm
    have hloopMono :
        (projection_isCoveringMap b₀ H).monodromy γ ebase = ebase :=
      (projection_isCoveringMap b₀ H).monodromy_eq_of_map_eq
        (FundamentalGroup.toPath δ) hloopCast
    have hpointMono :
        (projection_isCoveringMap b₀ H).monodromy γ ebase = epoint :=
      (projection_isCoveringMap b₀ H).monodromy_eq_of_map_eq Γ hpointCast
    have hpoint : point b₀ H qγ = basepoint b₀ H :=
      congrArg Subtype.val (hpointMono.symm.trans hloopMono)
    have hmem := (point_loop_eq_basepoint_iff b₀ H qγ).mp hpoint
    simpa [qγ] using hmem
  · intro hγH
    have hmem : FundamentalGroup.fromPath qγ ∈ H := by
      simpa [qγ] using hγH
    have hpoint := (point_loop_eq_basepoint_iff b₀ H qγ).mpr hmem
    obtain ⟨Γ, hΓ⟩ := pathToPoint b₀ H qγ
    let δ : Path.Homotopic.Quotient (basepoint b₀ H) (basepoint b₀ H) :=
      Γ.cast rfl hpoint.symm
    refine ⟨FundamentalGroup.fromPath δ, ?_⟩
    -- Mapping the endpoint-adjusted lift gives `qγ`; all remaining casts are reflexive.
    rw [FundamentalGroup.mapOfEq_apply]
    change (δ.map
        ⟨projection b₀ H, (projection_isCoveringMap b₀ H).continuous⟩).cast
          (projection_basepoint b₀ H).symm
          (projection_basepoint b₀ H).symm = qγ
    dsimp only [δ]
    rw [Path.Homotopic.Quotient.map_cast, hΓ,
      Path.Homotopic.Quotient.cast_cast]
    exact pathClassCast_self qγ _ _

end SubgroupPathCover

/-- Theorem 82.1: Every subgroup of the fundamental group of a path-connected, locally
path-connected, semilocally simply connected space is induced by a connected covering at a
chosen point over the base point. -/
theorem exists_fundamentalGroupMapRange_eq {B : Type u} [TopologicalSpace B]
    [PathConnectedSpace B] [LocallyPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    (b₀ : B) (H : Subgroup (FundamentalGroup B b₀)) :
    ∃ (C : ConnectedCovering.{u} B) (e₀ : C.Total) (h₀ : C.proj e₀ = b₀),
      C.isCoveringMap.fundamentalGroupMapRange h₀ = H := by
  -- Install the connectedness properties proved from the canonical prefix-path lifts.
  letI : PathConnectedSpace (SubgroupPathCover.Total b₀ H) :=
    SubgroupPathCover.pathConnectedSpace b₀ H
  letI : LocallyPathConnectedSpace (SubgroupPathCover.Total b₀ H) :=
    SubgroupPathCover.locallyPathConnectedSpace b₀ H
  -- Bundle the subgroup path cover and retain its distinguished point over `b₀`.
  refine ⟨ConnectedCovering.of (SubgroupPathCover.projection b₀ H)
      (SubgroupPathCover.projection_isCoveringMap b₀ H)
      (SubgroupPathCover.projection_surjective b₀ H),
    SubgroupPathCover.basepoint b₀ H,
    SubgroupPathCover.projection_basepoint b₀ H, ?_⟩
  -- Step 7 identifies the induced subgroup through the computed monodromy endpoint.
  exact SubgroupPathCover.fundamentalGroupMapRange_eq b₀ H

/-- Theorem 82.1 implies surjectivity of the classification by conjugacy classes of
fundamental-group subgroups. -/
theorem isClassificationSurjective {B : Type u} [TopologicalSpace B]
    [PathConnectedSpace B] [LocallyPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    (b₀ : B) : IsClassificationSurjective.{u} b₀ := by
  rw [isClassificationSurjective_iff]
  intro subgroupClass
  refine Quotient.inductionOn subgroupClass ?_
  intro H
  obtain ⟨C, e₀, h₀, hH⟩ := exists_fundamentalGroupMapRange_eq b₀ H
  refine ⟨Quotient.mk (equivalentSetoid B) C, ?_⟩
  rw [classification_mk, subgroupClass_mk C b₀ e₀ h₀]
  rw [subgroupClassAt_eq_mkConjClass]
  simpa [IsCoveringMap.fundamentalGroupMapRange, Subgroup.mkConjClass] using
    congrArg Subgroup.mkConjClass hH

end ConnectedCovering
