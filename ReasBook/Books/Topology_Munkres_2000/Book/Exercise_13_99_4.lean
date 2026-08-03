module

public import Topology_Munkres_2000.Book.Definition_82_1.SemilocallySimplyConnected
public import Topology_Munkres_2000.Book.Exercise_13_99_1
public import Topology_Munkres_2000.Book.Exercise_13_99_4.Countable
public import Topology_Munkres_2000.Book.Theorem_51_3
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.Separation.Hausdorff
import all Topology_Munkres_2000.Book.Definition_82_1.SemilocallySimplyConnected
import all Topology_Munkres_2000.Book.Lemma_55_1.Inclusions

public section

universe u

namespace FundamentalGroup

variable {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
  [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] [CompactSpace X]
  [T2Space X]
variable (x₀ : X)

/-- Helper for Exercise 13.99.4: inclusion through a nested subspace induces the
same fundamental-group map as direct inclusion. -/
private lemma mapOfSubtype_comp_mapOfSubset {A U : Set X} (h : A ⊆ U) (a : A) :
    (FundamentalGroup.mapOfSubtype U ⟨a, h a.property⟩).comp
        (FundamentalGroup.mapOfSubset h a) =
      FundamentalGroup.mapOfSubtype A a := by
  -- Expose the canonical inclusions and use functoriality of path-class mapping.
  ext q
  simp only [MonoidHom.comp_apply]
  rw [FundamentalGroup.mapOfSubset_eq_map_inclusion]
  unfold FundamentalGroup.mapOfSubtype
  rw [FundamentalGroup.map_apply]
  exact (Path.Homotopic.Quotient.map_comp
    (p := q) (f := ContinuousMap.inclusion h)
    (g := (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)))).symm

/-- Helper for Exercise 13.99.4: every point has an open path-connected
neighborhood whose inclusion induces the trivial homomorphism. -/
private lemma exists_open_pathConnected_mapOfSubtype_eq_one (x : X) :
    ∃ (U : Set X) (hxU : x ∈ U), IsOpen U ∧ IsPathConnected U ∧
      FundamentalGroup.mapOfSubtype U ⟨x, hxU⟩ = 1 := by
  -- Refine the semilocally simply connected neighborhood by the path-connected basis.
  obtain ⟨V, hV, hmapV⟩ := SemilocallySimplyConnectedSpace.exists_nhds x
  obtain ⟨U, ⟨hUopen, hxU, hUpath⟩, hUV⟩ :=
    (isOpen_isPathConnected_basis x).mem_iff.mp hV
  change U ⊆ V at hUV
  refine ⟨U, hxU, hUopen, hUpath, ?_⟩
  -- Factor the smaller inclusion through the original trivializing neighborhood.
  have hfactor := mapOfSubtype_comp_mapOfSubset hUV ⟨x, hxU⟩
  have hcenter : (⟨x, hUV hxU⟩ : V) =
      SemilocallySimplyConnectedSpace.point hV := Subtype.ext rfl
  have hmapV' : FundamentalGroup.mapOfSubtype V ⟨x, hUV hxU⟩ = 1 := by
    rw [hcenter]
    exact hmapV
  rw [hmapV'] at hfactor
  simpa only [MonoidHom.one_comp, id_eq] using hfactor.symm

/-- Helper for Exercise 13.99.4: mapping a composite path class maps its two
factors separately. -/
private lemma pathClass_map_trans {Y Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] {x y z : Y} (q : Path.Homotopic.Quotient x y)
    (r : Path.Homotopic.Quotient y z) (f : C(Y, Z)) :
    (q.trans r).map f = (q.map f).trans (r.map f) := by
  -- Quotient induction reduces the assertion to the computation rule for paths.
  refine Path.Homotopic.Quotient.ind₂ ?_ q r
  intro p s
  simpa only [Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_map] using
    congrArg Path.Homotopic.Quotient.mk (Path.map_trans p s f.continuous)

/-- Helper for Exercise 13.99.4: mapping a reversed path class reverses its
mapped class. -/
private lemma pathClass_map_symm {Y Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] {x y : Y} (q : Path.Homotopic.Quotient x y)
    (f : C(Y, Z)) : q.symm.map f = (q.map f).symm := by
  -- Quotient induction reduces the assertion to reversal of a mapped path.
  induction q using Path.Homotopic.Quotient.ind with
  | mk p =>
      simpa only [Path.Homotopic.Quotient.mk_symm,
        Path.Homotopic.Quotient.mk_map] using
        (congrArg Path.Homotopic.Quotient.mk
          (Path.map_symm p f.continuous)).symm

/-- Helper for Exercise 13.99.4: reversing a composite path class reverses its
two factors. -/
private lemma pathClass_symm_trans {x y z : X}
    (p : Path.Homotopic.Quotient x y) (q : Path.Homotopic.Quotient y z) :
    (p.trans q).symm = q.symm.trans p.symm := by
  -- Reduce the reversal identity to the corresponding identity for concrete paths.
  refine Path.Homotopic.Quotient.ind₂ ?_ p q
  intro a b
  simpa only [Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm] using
    congrArg Path.Homotopic.Quotient.mk (Path.trans_symm a b)

/-- Helper for Exercise 13.99.4: attaching base paths to homotopic middle paths
produces the same based loop class. -/
private lemma connectorDifference_eq {a b y : X}
    (alpha : Path x₀ a) (p : Path a y) (beta : Path x₀ b)
    (q : Path b y) (r : Path a b)
    (h : Path.Homotopic.Quotient.mk (p.trans q.symm) =
      Path.Homotopic.Quotient.mk r) :
    (Path.Homotopic.Quotient.mk (alpha.trans p)).trans
        (Path.Homotopic.Quotient.mk (beta.trans q)).symm =
      Path.Homotopic.Quotient.mk (alpha.trans (r.trans beta.symm)) := by
  -- Normalize both loops to base path, middle path, and reverse base path.
  calc
    (Path.Homotopic.Quotient.mk (alpha.trans p)).trans
          (Path.Homotopic.Quotient.mk (beta.trans q)).symm =
        (Path.Homotopic.Quotient.mk alpha).trans
          ((Path.Homotopic.Quotient.mk (p.trans q.symm)).trans
            (Path.Homotopic.Quotient.mk beta).symm) := by
      simp only [Path.Homotopic.Quotient.mk_trans,
        Path.Homotopic.Quotient.mk_symm, pathClass_symm_trans,
        Path.Homotopic.Quotient.trans_assoc]
    _ = (Path.Homotopic.Quotient.mk alpha).trans
          ((Path.Homotopic.Quotient.mk r).trans
            (Path.Homotopic.Quotient.mk beta).symm) :=
      congrArg
        (fun middle ↦ (Path.Homotopic.Quotient.mk alpha).trans
          (middle.trans (Path.Homotopic.Quotient.mk beta).symm)) h
    _ = Path.Homotopic.Quotient.mk
          (alpha.trans (r.trans beta.symm)) := by
      rw [Path.Homotopic.Quotient.mk_trans,
        Path.Homotopic.Quotient.mk_trans,
        Path.Homotopic.Quotient.mk_symm]

/-- Helper for Exercise 13.99.4: the range of a concatenation is contained in
any set containing the ranges of both factors. -/
private lemma pathTrans_range_subset {S : Set X} {a b c : X}
    (p : Path a b) (q : Path b c) (hp : Set.range p ⊆ S)
    (hq : Set.range q ⊆ S) : Set.range (p.trans q) ⊆ S := by
  -- The range formula for concatenation reduces the claim to a union bound.
  rw [Path.trans_range]
  exact Set.union_subset hp hq

/-- Helper for Exercise 13.99.4: reversing a path preserves every range
containment. -/
private lemma pathSymm_range_subset {S : Set X} {a b : X}
    (p : Path a b) (hp : Set.range p ⊆ S) : Set.range p.symm ⊆ S := by
  -- Reversal has exactly the same range as the original path.
  rwa [Path.symm_range]

/-- Helper for Exercise 13.99.4: changing only the endpoint types of a path
preserves every range containment. -/
private lemma pathCast_range_subset {S : Set X} {a b a' b' : X}
    (p : Path a b) (ha : a' = a) (hb : b' = b)
    (hp : Set.range p ⊆ S) : Set.range (p.cast ha hb) ⊆ S := by
  -- Endpoint casts leave the underlying function unchanged.
  rintro z ⟨t, rfl⟩
  rw [Path.cast_coe]
  exact hp (Set.mem_range_self t)

/-- Helper for Exercise 13.99.4: inserting a connector and its reverse between
two composable path classes does not change their closed composite. -/
private lemma closedPathClass_paste {a b c : X}
    (A : Path.Homotopic.Quotient x₀ a)
    (P : Path.Homotopic.Quotient a b)
    (G : Path.Homotopic.Quotient x₀ b)
    (E : Path.Homotopic.Quotient b c)
    (B : Path.Homotopic.Quotient x₀ c) :
    A.trans ((P.trans E).trans B.symm) =
      (A.trans (P.trans G.symm)).trans (G.trans (E.trans B.symm)) := by
  -- Reassociate until the inserted connector and its reverse are adjacent.
  rw [Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.trans_assoc]
  apply congrArg (Path.Homotopic.Quotient.trans A)
  rw [Path.Homotopic.Quotient.trans_assoc]
  apply congrArg (Path.Homotopic.Quotient.trans P)
  rw [← Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]

/-- Helper for Exercise 13.99.4: the path class of a finite concatenation
splits into the prefix class followed by its last edge. -/
private lemma pathClass_concat_succ {n : ℕ} (p : Fin (n + 2) → X)
    (F : (i : Fin (n + 1)) → Path (p i.castSucc) (p i.succ)) :
    Path.Homotopic.Quotient.mk (Path.concat p F) =
      (Path.Homotopic.Quotient.mk
        (Path.concat (p ∘ Fin.castSucc) (fun i ↦ F i.castSucc))).trans
      (Path.Homotopic.Quotient.mk (F (Fin.last n))) := by
  -- Apply the last-edge formula before passing it through the path quotient.
  calc
    Path.Homotopic.Quotient.mk (Path.concat p F) =
        Path.Homotopic.Quotient.mk
          ((Path.concat (p ∘ Fin.castSucc) (fun i ↦ F i.castSucc)).trans
            (F (Fin.last n))) :=
      congrArg Path.Homotopic.Quotient.mk (Path.concat_succ p F)
    _ = (Path.Homotopic.Quotient.mk
          (Path.concat (p ∘ Fin.castSucc) (fun i ↦ F i.castSucc))).trans
        (Path.Homotopic.Quotient.mk (F (Fin.last n))) :=
      Path.Homotopic.Quotient.mk_trans _ _

/-- Helper for Exercise 13.99.4: closing a concatenation at its endpoints
splits at the final edge after inserting the intermediate connector. -/
private lemma closedConcatClass_succ {n : ℕ} (p : Fin (n + 2) → X)
    (F : (i : Fin (n + 1)) → Path (p i.castSucc) (p i.succ))
    (alpha : Path x₀ (p 0))
    (gamma : Path x₀ (p ((Fin.last n).castSucc)))
    (beta : Path x₀ (p (Fin.last (n + 1)))) :
    (Path.Homotopic.Quotient.mk alpha).trans
        ((Path.Homotopic.Quotient.mk (Path.concat p F)).trans
          (Path.Homotopic.Quotient.mk beta).symm) =
      ((Path.Homotopic.Quotient.mk alpha).trans
          ((Path.Homotopic.Quotient.mk
            (Path.concat (p ∘ Fin.castSucc) (fun i ↦ F i.castSucc))).trans
            (Path.Homotopic.Quotient.mk gamma).symm)).trans
        ((Path.Homotopic.Quotient.mk gamma).trans
          ((Path.Homotopic.Quotient.mk (F (Fin.last n))).trans
            (Path.Homotopic.Quotient.mk beta).symm)) := by
  -- Rewrite the finite concatenation once, then cancel the inserted connector.
  rw [pathClass_concat_succ]
  exact closedPathClass_paste (X := X) (x₀ := x₀) _ _ _ _ _

/-- Helper for Exercise 13.99.4: if every edge closed by chosen vertex
connectors lies in a subgroup, then the closed finite concatenation lies there. -/
private lemma closedConcat_mem_of_edgeDifferences
    (H : Subgroup (FundamentalGroup X x₀)) {n : ℕ}
    (p : Fin (n + 2) → X)
    (F : (i : Fin (n + 1)) → Path (p i.castSucc) (p i.succ))
    (C : (i : Fin (n + 2)) → Path x₀ (p i))
    (hF : ∀ i,
      (FundamentalGroup.fromPath
        ((Path.Homotopic.Quotient.mk (C i.castSucc)).trans
          ((Path.Homotopic.Quotient.mk (F i)).trans
            (Path.Homotopic.Quotient.mk (C i.succ)).symm))) ∈ H) :
    FundamentalGroup.fromPath
      ((Path.Homotopic.Quotient.mk (C 0)).trans
        ((Path.Homotopic.Quotient.mk (Path.concat p F)).trans
          (Path.Homotopic.Quotient.mk (C (Fin.last (n + 1)))).symm)) ∈ H := by
  induction n with
  | zero =>
      -- A one-edge concatenation has exactly the assumed edge difference.
      have hconcat : Path.Homotopic.Quotient.mk (Path.concat p F) =
          Path.Homotopic.Quotient.mk (F 0) :=
        Path.Homotopic.Quotient.eq.mpr (Path.Homotopic.concat_one p F)
      rw [hconcat]
      exact hF 0
  | succ n ih =>
      -- Assemble the prefix and last-edge differences using the paste identity.
      have hprefix := ih
        (p := p ∘ Fin.castSucc)
        (F := fun i ↦ F i.castSucc)
        (C := fun i ↦ C i.castSucc)
        (fun i ↦ hF i.castSucc)
      have hlast := hF (Fin.last (n + 1))
      have hcombined := H.mul_mem hlast hprefix
      rw [FundamentalGroup.mul_def] at hcombined
      have hpaste := closedConcatClass_succ (X := X) (x₀ := x₀) p F
        (C 0) (C ((Fin.last (n + 1)).castSucc)) (C (Fin.last (n + 2)))
      exact hpaste.symm ▸ hcombined

/-- Helper for Exercise 13.99.4: membership of both endpoint connectors and
their closed middle composite implies membership of the middle loop. -/
private lemma middleLoop_mem_of_closedDifference
    (H : Subgroup (FundamentalGroup X x₀))
    (A P B : Path.Homotopic.Quotient x₀ x₀)
    (hA : FundamentalGroup.fromPath A ∈ H)
    (hB : FundamentalGroup.fromPath B ∈ H)
    (hclosed : FundamentalGroup.fromPath (A.trans (P.trans B.symm)) ∈ H) :
    FundamentalGroup.fromPath P ∈ H := by
  -- Prepend the reverse of the first connector and append the second connector.
  have hwithoutFirst := H.mul_mem hclosed (H.inv_mem hA)
  have hmiddle := H.mul_mem hB hwithoutFirst
  rw [FundamentalGroup.mul_def, FundamentalGroup.inv_def,
    FundamentalGroup.mul_def, ← Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans,
    Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.trans_refl] at hmiddle
  exact hmiddle

/-- Helper for Exercise 13.99.4: a closed connector decomposition gives
membership of the endpoint-cast middle loop. -/
private lemma pathClassCast_mem_of_closedDifference
    (H : Subgroup (FundamentalGroup X x₀)) {a b : X}
    (hsource : a = x₀) (htarget : b = x₀)
    (alpha : Path x₀ a) (P : Path a b) (beta : Path x₀ b)
    (halpha : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (alpha.cast rfl hsource.symm)) ∈ H)
    (hbeta : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (beta.cast rfl htarget.symm)) ∈ H)
    (hclosed : FundamentalGroup.fromPath
      ((Path.Homotopic.Quotient.mk alpha).trans
        ((Path.Homotopic.Quotient.mk P).trans
          (Path.Homotopic.Quotient.mk beta).symm)) ∈ H) :
    FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (P.cast hsource.symm htarget.symm)) ∈ H := by
  -- Once the endpoint equalities are substituted, this is ordinary group cancellation.
  subst a
  subst b
  simp only [Path.Homotopic.Quotient.mk_cast,
    Path.Homotopic.Quotient.cast_rfl_rfl] at halpha hbeta hclosed ⊢
  exact middleLoop_mem_of_closedDifference (X := X) (x₀ := x₀)
    H _ _ _ halpha hbeta hclosed

/-- Helper for Exercise 13.99.4: in a path-connected subspace whose inclusion
is trivial at one point, same-endpoint path classes have equal ambient images. -/
private lemma pathClass_map_eq_of_pathConnected_map_eq_one
    {U : Set X} (hU : IsPathConnected U) (a x y : U)
    (hmap : FundamentalGroup.mapOfSubtype U a = 1)
    (q r : Path.Homotopic.Quotient x y) :
    q.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) =
      r.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) := by
  -- Join the triviality basepoint to the source and close `q` by reversing `r`.
  let s : Path.Homotopic.Quotient a x :=
    Path.Homotopic.Quotient.mk
      (hU.joinedIn a a.property x x.property).joined_subtype.somePath
  let loop : Path.Homotopic.Quotient a a :=
    s.trans (q.trans (r.symm.trans s.symm))
  have hloop := DFunLike.congr_fun hmap (FundamentalGroup.fromPath loop)
  have hSubtype : FundamentalGroup.mapOfSubtype U a =
      FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) a := rfl
  rw [hSubtype, FundamentalGroup.map_apply] at hloop
  simp only [MonoidHom.one_apply, FundamentalGroup.one_def] at hloop
  -- Normalize mapping through the composite and its reversals.
  have hclosed :
      (s.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))).trans
          ((q.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))).trans
            ((r.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))).symm.trans
              (s.map
                (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))).symm)) =
        Path.Homotopic.Quotient.refl (a : X) := by
    dsimp only [loop] at hloop
    rw [pathClass_map_trans, pathClass_map_trans, pathClass_map_trans,
      pathClass_map_symm, pathClass_map_symm] at hloop
    exact hloop
  -- Cancel the auxiliary path and then the common return path.
  have hpost := congrArg
    (fun z : Path.Homotopic.Quotient (a : X) a ↦
      z.trans (s.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)))) hclosed
  have hwithoutReturn :
      (s.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))).trans
          ((q.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))).trans
            (r.map
              (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))).symm) =
        s.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) := by
    simpa only [Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.symm_trans,
      Path.Homotopic.Quotient.trans_refl,
      Path.Homotopic.Quotient.refl_trans] using hpost
  have hpre := congrArg
    (fun z : Path.Homotopic.Quotient (a : X) x ↦
      (s.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))).symm.trans z)
    hwithoutReturn
  have hloopAtSource :
      (q.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))).trans
          (r.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))).symm =
        Path.Homotopic.Quotient.refl
          ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) x) := by
    simpa only [← Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.symm_trans,
      Path.Homotopic.Quotient.refl_trans] using hpre
  have hcancel := congrArg
    (fun z : Path.Homotopic.Quotient
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) x)
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) x) ↦
      z.trans (r.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)))) hloopAtSource
  simpa only [Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.trans_refl,
    Path.Homotopic.Quotient.refl_trans] using hcancel

/-- Helper for Exercise 13.99.4: two paths contained in one path-connected
trivializing subspace have the same ambient homotopy class. -/
private lemma pathClass_eq_of_ranges_subset_of_mapOfSubtype_eq_one
    {U : Set X} (hU : IsPathConnected U) (a : U)
    (hmap : FundamentalGroup.mapOfSubtype U a = 1)
    {x y : X} (p q : Path x y) (hp : Set.range p ⊆ U)
    (hq : Set.range q ⊆ U) :
    Path.Homotopic.Quotient.mk p = Path.Homotopic.Quotient.mk q := by
  -- Lift both paths to the subtype using their range-containment proofs.
  have hx : x ∈ U := by
    rw [← p.source]
    exact hp (Set.mem_range_self 0)
  have hy : y ∈ U := by
    rw [← p.target]
    exact hp (Set.mem_range_self 1)
  let pU : Path (⟨x, hx⟩ : U) ⟨y, hy⟩ :=
    { toFun := fun t ↦ ⟨p t, hp (Set.mem_range_self t)⟩
      continuous_toFun := p.continuous.subtype_mk _
      source' := Subtype.ext p.source
      target' := Subtype.ext p.target }
  let qU : Path (⟨x, hx⟩ : U) ⟨y, hy⟩ :=
    { toFun := fun t ↦ ⟨q t, hq (Set.mem_range_self t)⟩
      continuous_toFun := q.continuous.subtype_mk _
      source' := Subtype.ext q.source
      target' := Subtype.ext q.target }
  have hpLift :
      (Path.Homotopic.Quotient.mk pU).map
          (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) =
        Path.Homotopic.Quotient.mk p := by
    rw [← Path.Homotopic.Quotient.mk_map]
    congr 1
  have hqLift :
      (Path.Homotopic.Quotient.mk qU).map
          (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) =
        Path.Homotopic.Quotient.mk q := by
    rw [← Path.Homotopic.Quotient.mk_map]
    congr 1
  calc
    Path.Homotopic.Quotient.mk p =
        (Path.Homotopic.Quotient.mk pU).map
          (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) := hpLift.symm
    _ = (Path.Homotopic.Quotient.mk qU).map
          (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) :=
      pathClass_map_eq_of_pathConnected_map_eq_one hU a ⟨x, hx⟩ ⟨y, hy⟩
        hmap _ _
    _ = Path.Homotopic.Quotient.mk q := hqLift

/-- Helper for Exercise 13.99.4: compactness supplies a finite path-connected
open cover whose intersecting pairs lie in path-connected trivializing sets. -/
private lemma exists_finiteTrivializingCover :
    ∃ (s : Finset X) (U : s → Set X) (p : (i : s) → U i),
      (∀ i, IsOpen (U i)) ∧ (∀ i, IsPathConnected (U i)) ∧
      (⋃ i, U i) = Set.univ ∧
      ∀ i j, (U i ∩ U j).Nonempty →
        ∃ (A : Set X) (a : A), IsPathConnected A ∧ U i ∪ U j ⊆ A ∧
          FundamentalGroup.mapOfSubtype A a = 1 := by
  classical
  -- Choose the original cover of path-connected trivializing neighborhoods.
  have hlocal : ∀ x : X, ∃ (A : Set X) (hxA : x ∈ A),
      IsOpen A ∧ IsPathConnected A ∧
        FundamentalGroup.mapOfSubtype A ⟨x, hxA⟩ = 1 :=
    exists_open_pathConnected_mapOfSubtype_eq_one
  choose A hxA hAopen hApath hAmap using hlocal
  let coverA : Set (Set X) := Set.range A
  have hcoverAopen : ∀ V ∈ coverA, IsOpen V := by
    rintro V ⟨x, rfl⟩
    exact hAopen x
  have hcoverAcover : ⋃₀ coverA = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_sUnion.mpr ⟨A x, ⟨x, rfl⟩, hxA x⟩
  -- A barycentric refinement controls the union of each intersecting pair.
  obtain ⟨coverB, hcoverB⟩ :=
    exists_barycentricRefinement_of_compact_t2 coverA hcoverAopen hcoverAcover
  have hrefine : ∀ x : X, ∃ (V : Set X), x ∈ V ∧ IsOpen V ∧
      IsPathConnected V ∧ ∃ B ∈ coverB, V ⊆ B := by
    intro x
    have hxCover : x ∈ ⋃₀ coverB :=
      hcoverB.sUnion_eq_univ.symm ▸ Set.mem_univ x
    obtain ⟨B, hBcoverB, hxB⟩ := Set.mem_sUnion.mp hxCover
    obtain ⟨V, ⟨hVopen, hxV, hVpath⟩, hVB⟩ :=
      (isOpen_isPathConnected_basis x).mem_iff.mp
        (hcoverB.isOpen_of_mem hBcoverB |>.mem_nhds hxB)
    exact ⟨V, hxV, hVopen, hVpath, B, hBcoverB, hVB⟩
  choose V hxV hVopen hVpath B hBcoverB hVB using hrefine
  -- Extract a finite subcover and use its centers as the finite index type.
  have hcover : Set.univ ⊆ ⋃ x, V x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hxV x⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V hVopen hcover
  refine ⟨t, fun i ↦ V i, fun i ↦ ⟨i, hxV i⟩,
    fun i ↦ hVopen i, fun i ↦ hVpath i, ?_, ?_⟩
  · -- Rewrite the finite subcover as a union over its subtype.
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Set.mem_iUnion.mpr ⟨⟨y, hyt⟩, hxy⟩
  · -- Barycentricity supplies one original trivializing parent for each overlap.
    intro i j hij
    have hBB : (B i ∩ B j).Nonempty := by
      obtain ⟨x, hxi, hxj⟩ := hij
      exact ⟨x, hVB i hxi, hVB j hxj⟩
    obtain ⟨C, hCA, hBC⟩ :=
      hcoverB.union_subset_of_inter_nonempty (hBcoverB i) (hBcoverB j) hBB
    obtain ⟨z, rfl⟩ := hCA
    exact ⟨A z, ⟨z, hxA z⟩, hApath z,
      (Set.union_subset_union (hVB i) (hVB j)).trans hBC, hAmap z⟩

/-- Exercise 13.99.4 (1). The fundamental group of a compact Hausdorff,
path-connected, locally path-connected, semilocally simply connected space is finitely
generated. -/
instance instFGOfCompact (x₀ : X) : Group.FG (FundamentalGroup X x₀) := by
  classical
  -- Fix the finite cover and the paths used to turn its ordered overlaps into loops.
  obtain ⟨s, U, p, hUopen, hUpath, hcover, hpair⟩ :=
    exists_finiteTrivializingCover (X := X)
  let localPath (i : s) (y : X) (hy : y ∈ U i) : Path (p i : X) y :=
    ((hUpath i).joinedIn (p i) (p i).property y hy).somePath
  have hlocalPathRange (i : s) (y : X) (hy : y ∈ U i) :
      Set.range (localPath i y hy) ⊆ U i := by
    -- The chosen path carries its membership in `U i` at every parameter.
    rintro z ⟨t, rfl⟩
    exact ((hUpath i).joinedIn (p i) (p i).property y hy).somePath_mem t
  let basePath (i : s) : Path x₀ (p i : X) :=
    PathConnectedSpace.somePath x₀ (p i : X)
  let returnPath (i : s) : Path (p i : X) x₀ :=
    if hx : x₀ ∈ U i then localPath i x₀ hx
    else PathConnectedSpace.somePath (p i : X) x₀
  have returnPath_eq_localPath (i : s) (hx : x₀ ∈ U i) :
      returnPath i = localPath i x₀ hx := by
    -- On a cover member containing the basepoint, use its internal return path.
    simp only [returnPath, dif_pos hx]
  have hreturnPathRange (i : s) (hx : x₀ ∈ U i) :
      Set.range (returnPath i) ⊆ U i := by
    rw [returnPath_eq_localPath i hx]
    exact hlocalPathRange i x₀ hx
  let selectPath (i j : s) : Path (p i : X) (p j : X) :=
    if hij : (U i ∩ U j).Nonempty then
      (((hUpath i).union (hUpath j) hij).joinedIn
        (p i) (Set.mem_union_left (U j) (p i).property)
        (p j) (Set.mem_union_right (U i) (p j).property)).somePath
    else PathConnectedSpace.somePath (p i : X) (p j : X)
  have hselectPathRange (i j : s) (hij : (U i ∩ U j).Nonempty) :
      Set.range (selectPath i j) ⊆ U i ∪ U j := by
    -- For an intersecting pair, the selected path is chosen inside its union.
    simp only [selectPath, dif_pos hij]
    rintro z ⟨t, rfl⟩
    exact (((hUpath i).union (hUpath j) hij).joinedIn
      (p i) (Set.mem_union_left (U j) (p i).property)
      (p j) (Set.mem_union_right (U i) (p j).property)).somePath_mem t
  let generator : Sum s (s × s) → FundamentalGroup X x₀ := fun k ↦
    match k with
    | .inl i => FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk ((basePath i).trans (returnPath i)))
    | .inr ij => FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          ((basePath ij.1).trans
            ((selectPath ij.1 ij.2).trans (basePath ij.2).symm)))
  let H : Subgroup (FundamentalGroup X x₀) :=
    Subgroup.closure (Set.range generator)
  have hgenerator (k : Sum s (s × s)) : generator k ∈ H := by
    -- Every displayed loop lies in the subgroup generated by the finite family.
    exact Subgroup.subset_closure (Set.mem_range_self k)
  -- Boundary connectors are among the first summand of the generating family.
  have hboundaryConnector (i : s) (y : X) (hy : y ∈ U i)
      (hbase : y = x₀) :
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          (((basePath i).trans (localPath i y hy)).cast rfl hbase.symm)) ∈ H := by
    have hii : (U i ∩ U i).Nonempty :=
      ⟨p i, (p i).property, (p i).property⟩
    obtain ⟨A, a, hApath, hUiA, hAmap⟩ := hpair i i hii
    have hlocalCast :
        Set.range ((localPath i y hy).cast rfl hbase.symm) ⊆ A :=
      (pathCast_range_subset (localPath i y hy) rfl hbase.symm
        (hlocalPathRange i y hy)).trans
        (fun z hz ↦ hUiA (Or.inl hz))
    have hreturn : Set.range (returnPath i) ⊆ A :=
      (hreturnPathRange i (hbase ▸ hy)).trans
        (fun z hz ↦ hUiA (Or.inl hz))
    have htail := pathClass_eq_of_ranges_subset_of_mapOfSubtype_eq_one
      hApath a hAmap ((localPath i y hy).cast rfl hbase.symm)
        (returnPath i) hlocalCast hreturn
    have hloop :
        Path.Homotopic.Quotient.mk
            (((basePath i).trans (localPath i y hy)).cast rfl hbase.symm) =
          Path.Homotopic.Quotient.mk
            ((basePath i).trans (returnPath i)) := by
      rw [Path.cast_trans (basePath i) (localPath i y hy)
          rfl rfl hbase.symm,
        Path.cast_rfl_rfl, Path.Homotopic.Quotient.mk_trans,
        Path.Homotopic.Quotient.mk_trans]
      exact congrArg (Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.mk (basePath i))) htail
    rw [hloop]
    simpa only [generator] using hgenerator (Sum.inl i)
  -- It remains to prove that the finite family generates every represented loop.
  refine Group.fg_iff.mpr ⟨Set.range generator, ?_, Set.finite_range generator⟩
  change H = ⊤
  apply top_unique
  intro g _
  obtain ⟨f, rfl⟩ :=
    Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath g)
  let c : s → Set unitInterval := fun i ↦ f ⁻¹' U i
  have hcOpen : ∀ i, IsOpen (c i) := by
    -- Pulling the finite open cover back along the loop preserves openness.
    intro i
    exact (hUopen i).preimage f.continuous
  have hcCover : Set.univ ⊆ ⋃ i, c i := by
    -- The pulled-back family covers the unit interval because `U` covers `X`.
    intro t _
    have hft : f t ∈ ⋃ i, U i := hcover.symm ▸ Set.mem_univ (f t)
    obtain ⟨i, hfti⟩ := Set.mem_iUnion.mp hft
    exact Set.mem_iUnion.mpr ⟨i, hfti⟩
  obtain ⟨t, ht0, htmono, ⟨m, hm⟩, htSubordinate⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hcOpen hcCover
  have hmpositive : 0 < m := by
    -- A cutoff equal to zero would identify the distinct endpoints of the interval.
    by_contra hmnot
    have hmzero : m = 0 := Nat.eq_zero_of_not_pos hmnot
    subst m
    have htone : t 0 = 1 := hm 0 le_rfl
    rw [ht0] at htone
    exact zero_ne_one htone
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpositive)
  let a : Fin (n + 2) → unitInterval := fun i ↦ t i
  have haStart : a 0 = 0 := ht0
  have haEnd : a (Fin.last (n + 1)) = 1 := hm (n + 1) le_rfl
  choose side hside using fun i : Fin (n + 1) ↦ htSubordinate i
  have hsubpath : ∀ i,
      Set.range (f.subpath (a i.castSucc) (a i.succ)) ⊆ U (side i) := by
    -- Monotonicity identifies each subpath range with its subordinate interval.
    intro i
    have hstep : a i.castSucc ≤ a i.succ := htmono (Nat.le_succ i)
    rw [Path.range_subpath_of_le f _ _ hstep]
    rintro z ⟨r, hr, rfl⟩
    exact hside i hr
  let vertexSide : Fin (n + 2) → s :=
    Fin.lastCases (side (Fin.last n)) side
  have hvertex : ∀ k, f (a k) ∈ U (vertexSide k) := by
    -- Each vertex uses the side of the following edge, except the final vertex.
    intro k
    refine Fin.lastCases ?_ (fun i ↦ ?_) k
    · simp only [vertexSide, Fin.lastCases_last]
      have hmem := hsubpath (Fin.last n)
        (Set.mem_range_self (1 : unitInterval))
      rw [(f.subpath (a (Fin.last n).castSucc)
        (a (Fin.last n).succ)).target] at hmem
      simpa only [Fin.succ_last] using hmem
    · simp only [vertexSide, Fin.lastCases_castSucc]
      have hmem := hsubpath i
        (Set.mem_range_self (0 : unitInterval))
      rw [(f.subpath (a i.castSucc) (a i.succ)).source] at hmem
      exact hmem
  let connector (k : Fin (n + 2)) : Path x₀ (f (a k)) :=
    (basePath (vertexSide k)).trans
      (localPath (vertexSide k) (f (a k)) (hvertex k))
  have hedge : ∀ i : Fin (n + 1),
      FundamentalGroup.fromPath
        ((Path.Homotopic.Quotient.mk (connector i.castSucc)).trans
          ((Path.Homotopic.Quotient.mk
            (f.subpath (a i.castSucc) (a i.succ))).trans
            (Path.Homotopic.Quotient.mk (connector i.succ)).symm)) ∈ H := by
    -- Close one edge with its two vertex connectors and compare its middle path
    -- with the selected path for the corresponding ordered pair of cover members.
    intro i
    let left : s := vertexSide i.castSucc
    let right : s := vertexSide i.succ
    have hleft : left = side i := by
      simp only [left, vertexSide, Fin.lastCases_castSucc]
    have hrightLeft : f (a i.succ) ∈ U left := by
      have hmem := hsubpath i (Set.mem_range_self (1 : unitInterval))
      rw [(f.subpath (a i.castSucc) (a i.succ)).target] at hmem
      rw [hleft]
      exact hmem
    have hoverlap : (U left ∩ U right).Nonempty :=
      ⟨f (a i.succ), hrightLeft, hvertex i.succ⟩
    obtain ⟨A, center, hApath, hUnionA, hAmap⟩ :=
      hpair left right hoverlap
    let leftTail : Path (p left : X) (f (a i.succ)) :=
      (localPath left (f (a i.castSucc)) (hvertex i.castSucc)).trans
        (f.subpath (a i.castSucc) (a i.succ))
    let rightTail : Path (p right : X) (f (a i.succ)) :=
      localPath right (f (a i.succ)) (hvertex i.succ)
    have hleftTail : Set.range leftTail ⊆ A := by
      apply pathTrans_range_subset
      · exact (hlocalPathRange left (f (a i.castSucc))
          (hvertex i.castSucc)).trans (fun z hz ↦ hUnionA (Or.inl hz))
      · exact (hsubpath i).trans
          (fun z hz ↦ hUnionA (Or.inl (hleft.symm ▸ hz)))
    have hrightTail : Set.range rightTail.symm ⊆ A :=
      pathSymm_range_subset rightTail
        ((hlocalPathRange right (f (a i.succ))
          (hvertex i.succ)).trans (fun z hz ↦ hUnionA (Or.inr hz)))
    have hmiddleRange : Set.range (leftTail.trans rightTail.symm) ⊆ A :=
      pathTrans_range_subset leftTail rightTail.symm hleftTail hrightTail
    have hselectRange : Set.range (selectPath left right) ⊆ A :=
      (hselectPathRange left right hoverlap).trans hUnionA
    have hmiddle := pathClass_eq_of_ranges_subset_of_mapOfSubtype_eq_one
      hApath center hAmap (leftTail.trans rightTail.symm)
        (selectPath left right) hmiddleRange hselectRange
    have hconnector := connectorDifference_eq (x₀ := x₀)
      (basePath left) leftTail (basePath right) rightTail
        (selectPath left right) hmiddle
    have hclosed :
        (Path.Homotopic.Quotient.mk (connector i.castSucc)).trans
            ((Path.Homotopic.Quotient.mk
              (f.subpath (a i.castSucc) (a i.succ))).trans
              (Path.Homotopic.Quotient.mk (connector i.succ)).symm) =
          Path.Homotopic.Quotient.mk
            ((basePath left).trans
              ((selectPath left right).trans (basePath right).symm)) := by
      simpa only [connector, leftTail, rightTail,
        Path.Homotopic.Quotient.mk_trans,
        Path.Homotopic.Quotient.trans_assoc] using hconnector
    rw [hclosed]
    simpa only [generator] using hgenerator (Sum.inr (left, right))
  have hclosed := closedConcat_mem_of_edgeDifferences (X := X) (x₀ := x₀) H
    (p := f ∘ a)
    (F := fun i ↦ f.subpath (a i.castSucc) (a i.succ))
    (C := connector) hedge
  have hsource : (f ∘ a) 0 = x₀ :=
    (congrArg f haStart).trans f.source
  have htarget : (f ∘ a) (Fin.last (n + 1)) = x₀ :=
    (congrArg f haEnd).trans f.target
  have hfirst : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk
        ((connector 0).cast rfl hsource.symm)) ∈ H := by
    -- The first connector is the boundary generator for its cover member.
    simpa only [connector, Function.comp_apply] using
      hboundaryConnector (vertexSide 0) (f (a 0)) (hvertex 0) hsource
  have hlast : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk
        ((connector (Fin.last (n + 1))).cast rfl htarget.symm)) ∈ H := by
    -- The last connector is likewise a boundary generator.
    simpa only [connector, Function.comp_apply] using
      hboundaryConnector (vertexSide (Fin.last (n + 1)))
        (f (a (Fin.last (n + 1)))) (hvertex (Fin.last (n + 1))) htarget
  have hconcat := pathClassCast_mem_of_closedDifference (X := X) (x₀ := x₀)
    H hsource htarget
    (connector 0)
    (Path.concat (f ∘ a) (fun i ↦ f.subpath (a i.castSucc) (a i.succ)))
    (connector (Fin.last (n + 1))) hfirst hlast hclosed
  have hclass := pathClass_eq_concatSubpaths f a haStart haEnd
  -- The subdivision theorem identifies the endpoint-cast concatenation with `f`.
  change FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk f) ∈ H
  have hclassGroup := congrArg
    (fun q : Path.Homotopic.Quotient x₀ x₀ ↦ FundamentalGroup.fromPath q)
    hclass
  exact hclassGroup.symm ▸ hconcat

/- Exercise 13.99.4 (2). Hence the fundamental group is countable. -/
#synth Countable (FundamentalGroup X x₀)

end FundamentalGroup

end
