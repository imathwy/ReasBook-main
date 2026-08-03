module

public import Topology_Munkres_2000.Book.Definition_82_1.SemilocallySimplyConnected
public import Topology_Munkres_2000.Book.Exercise_13_99_1
public import Topology_Munkres_2000.Book.Theorem_51_3
public import Mathlib.SetTheory.Cardinal.Free
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.Separation.Regular
import all Topology_Munkres_2000.Book.Definition_82_1.SemilocallySimplyConnected
import all Topology_Munkres_2000.Book.Lemma_55_1.Inclusions

public section

universe u

namespace FundamentalGroup

open TopologicalSpace

/-- Helper for Theorem 13.99.1: inclusion through a nested subspace induces the
same fundamental-group map as direct inclusion. -/
private lemma mapOfSubtype_comp_mapOfSubset {X : Type u} [TopologicalSpace X]
    {A U : Set X} (h : A ⊆ U) (a : A) :
    (FundamentalGroup.mapOfSubtype U ⟨a, h a.property⟩).comp
        (FundamentalGroup.mapOfSubset h a) =
      FundamentalGroup.mapOfSubtype A a := by
  -- Expose the canonical inclusion maps, then use functoriality of path-class mapping.
  ext q
  simp only [MonoidHom.comp_apply]
  rw [FundamentalGroup.mapOfSubset_eq_map_inclusion]
  unfold FundamentalGroup.mapOfSubtype
  rw [FundamentalGroup.map_apply]
  exact (Path.Homotopic.Quotient.map_comp
    (p := q) (f := ContinuousMap.inclusion h)
    (g := (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)))).symm

/-- Helper for Theorem 13.99.1: every point has an open path-connected
neighborhood whose inclusion induces the trivial homomorphism. -/
private lemma exists_open_pathConnected_mapOfSubtype_eq_one
    {X : Type u} [TopologicalSpace X] [LocallyPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (x : X) :
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

/-- Helper for Theorem 13.99.1: mapping a composite path class maps its two
factors separately. -/
private lemma pathClass_map_trans {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {x y z : X} (q : Path.Homotopic.Quotient x y)
    (r : Path.Homotopic.Quotient y z) (f : C(X, Y)) :
    (q.trans r).map f = (q.map f).trans (r.map f) := by
  -- Quotient induction reduces the assertion to the computation rule for concrete paths.
  refine Path.Homotopic.Quotient.ind₂ ?_ q r
  intro p s
  simpa only [Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_map] using
    congrArg Path.Homotopic.Quotient.mk (Path.map_trans p s f.continuous)

/-- Helper for Theorem 13.99.1: mapping a reversed path class reverses the
mapped class. -/
private lemma pathClass_map_symm {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {x y : X} (q : Path.Homotopic.Quotient x y)
    (f : C(X, Y)) : q.symm.map f = (q.map f).symm := by
  -- Quotient induction reduces the assertion to reversal of a mapped concrete path.
  induction q using Path.Homotopic.Quotient.ind with
  | mk p =>
      simpa only [Path.Homotopic.Quotient.mk_symm,
        Path.Homotopic.Quotient.mk_map] using
        (congrArg Path.Homotopic.Quotient.mk
          (Path.map_symm p f.continuous)).symm

/-- Helper for Theorem 13.99.1: in a path-connected subspace whose inclusion
is trivial at one point, any two same-endpoint path classes have equal ambient images. -/
private lemma pathClass_map_eq_of_pathConnected_map_eq_one
    {X : Type u} [TopologicalSpace X] {U : Set X} (hU : IsPathConnected U)
    (a x y : U) (hmap : FundamentalGroup.mapOfSubtype U a = 1)
    (q r : Path.Homotopic.Quotient x y) :
    q.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) =
      r.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) := by
  -- Join the triviality basepoint to the source and close `q` with the reverse of `r`.
  letI : PathConnectedSpace U := isPathConnected_iff_pathConnectedSpace.mp hU
  let s : Path.Homotopic.Quotient a x :=
    Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath a x)
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
  -- Cancel the auxiliary path on both sides, followed by the common return path.
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

/-- Helper for Theorem 13.99.1: two paths contained in one path-connected
trivializing subspace have the same ambient homotopy class. -/
private lemma pathClass_eq_of_range_subset_trivializing
    {X : Type u} [TopologicalSpace X] {U : Set X} (hU : IsPathConnected U)
    (a : U) (hmap : FundamentalGroup.mapOfSubtype U a = 1)
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

/-- Helper for Theorem 13.99.1: there is a countable path-connected basis such
that two intersecting members lie in one path-connected trivializing subspace. -/
private lemma exists_countable_pathConnected_trivializingBasis
    {X : Type u} [TopologicalSpace X] [LocallyPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] [T3Space X]
    [SecondCountableTopology X] :
    ∃ ℬ : Set (Set X), ℬ.Countable ∧ IsTopologicalBasis ℬ ∧
      (∀ B ∈ ℬ, IsPathConnected B) ∧
      ∀ B ∈ ℬ, ∀ C ∈ ℬ, (B ∩ C).Nonempty →
        ∃ (A : Set X), IsPathConnected A ∧ B ∪ C ⊆ A ∧
          ∃ a : A, FundamentalGroup.mapOfSubtype A a = 1 := by
  classical
  -- Choose one good neighborhood around every point and package them as an open cover.
  have hlocal : ∀ x : X, ∃ (U : Set X) (hxU : x ∈ U),
      IsOpen U ∧ IsPathConnected U ∧
        FundamentalGroup.mapOfSubtype U ⟨x, hxU⟩ = 1 :=
    exists_open_pathConnected_mapOfSubtype_eq_one
  choose U hxU hUopen hUpath hUmap using hlocal
  let 𝒜 : Set (Set X) := Set.range U
  have h𝒜open : ∀ A ∈ 𝒜, IsOpen A := by
    rintro A ⟨x, rfl⟩
    exact hUopen x
  have h𝒜cover : ⋃₀ 𝒜 = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_sUnion.mpr ⟨U x, ⟨x, rfl⟩, hxU x⟩
  -- A barycentric refinement makes every intersecting pair subordinate to one good member.
  obtain ⟨𝒞, h𝒞⟩ :=
    exists_barycentricRefinement_of_metrizable 𝒜 h𝒜open h𝒜cover
  let 𝒟 : Set (Set X) :=
    {D | IsOpen D ∧ IsPathConnected D ∧ ∃ C ∈ 𝒞, D ⊆ C}
  have h𝒟basis : IsTopologicalBasis 𝒟 := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · intro D hD
      exact hD.1
    · intro x O hxO hOopen
      have hxCover : x ∈ ⋃₀ 𝒞 := h𝒞.sUnion_eq_univ.symm ▸ Set.mem_univ x
      obtain ⟨C, hC𝒞, hxC⟩ := Set.mem_sUnion.mp hxCover
      have hCopen := h𝒞.isOpen_of_mem hC𝒞
      obtain ⟨D, ⟨hDopen, hxD, hDpath⟩, hDsub⟩ :=
        (isOpen_isPathConnected_basis x).mem_iff.mp
          ((hCopen.inter hOopen).mem_nhds ⟨hxC, hxO⟩)
      change D ⊆ C ∩ O at hDsub
      exact ⟨D, ⟨hDopen, hDpath, C, hC𝒞, fun y hy ↦ (hDsub hy).1⟩,
        hxD, fun y hy ↦ (hDsub hy).2⟩
  -- Extract a countable subbasis and inherit the barycentric overlap property.
  obtain ⟨ℬ, hℬ𝒟, hℬcount, hℬbasis⟩ := h𝒟basis.exists_countable
  refine ⟨ℬ, hℬcount, hℬbasis, ?_, ?_⟩
  · intro B hB
    exact (hℬ𝒟 hB).2.1
  · intro B hB C hC hBC
    obtain ⟨R, hR𝒞, hBR⟩ := (hℬ𝒟 hB).2.2
    obtain ⟨S, hS𝒞, hCS⟩ := (hℬ𝒟 hC).2.2
    have hRS : (R ∩ S).Nonempty := by
      obtain ⟨x, hxB, hxC⟩ := hBC
      exact ⟨x, hBR hxB, hCS hxC⟩
    obtain ⟨A, hA𝒜, hRSA⟩ :=
      h𝒞.union_subset_of_inter_nonempty hR𝒞 hS𝒞 hRS
    obtain ⟨z, rfl⟩ := hA𝒜
    exact ⟨U z, hUpath z,
      (Set.union_subset_union hBR hCS).trans hRSA,
      ⟨⟨z, hxU z⟩, hUmap z⟩⟩

/-- Helper for Theorem 13.99.1: the class of a finite concatenation splits off
its final edge. -/
private lemma pathClass_concat_last {X : Type u} [TopologicalSpace X]
    {n : ℕ} (p : Fin (n + 2) → X)
    (F : (i : Fin (n + 1)) → Path (p i.castSucc) (p i.succ)) :
    Path.Homotopic.Quotient.mk (Path.concat p F) =
      (Path.Homotopic.Quotient.mk
        (Path.concat (p ∘ Fin.castSucc) (fun i ↦ F i.castSucc))).trans
      (Path.Homotopic.Quotient.mk (F (Fin.last n))) := by
  -- Pass the defining last-edge decomposition through the path quotient.
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

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Theorem 13.99.1: cellwise path-class equations telescope across
a finite chain of paths. -/
private lemma pathClass_concat_eq_of_cell {X : Type u} [TopologicalSpace X]
    {n : ℕ} (p q : Fin (n + 1) → X)
    (F : (i : Fin n) → Path (p i.castSucc) (p i.succ))
    (G : (i : Fin n) → Path (q i.castSucc) (q i.succ))
    (α : (i : Fin (n + 1)) → Path (p i) (q i))
    (hcell : ∀ i,
      (Path.Homotopic.Quotient.mk (F i)).trans
          (Path.Homotopic.Quotient.mk (α i.succ)) =
        (Path.Homotopic.Quotient.mk (α i.castSucc)).trans
          (Path.Homotopic.Quotient.mk (G i))) :
    (Path.Homotopic.Quotient.mk (Path.concat p F)).trans
        (Path.Homotopic.Quotient.mk (α (Fin.last n))) =
      (Path.Homotopic.Quotient.mk (α 0)).trans
        (Path.Homotopic.Quotient.mk (Path.concat q G)) := by
  induction n with
  | zero =>
      -- With no cells, both concatenations and the sole connector are constant.
      simp only [Path.concat_zero,
        Path.Homotopic.Quotient.mk_refl,
        Path.Homotopic.Quotient.refl_trans,
        Path.Homotopic.Quotient.trans_refl]
      have hzero : Fin.last 0 = 0 := Fin.eq_zero _
      cases hzero
      rfl
  | succ n ih =>
      -- Telescope the prefix, replace the last cell, and reassociate once.
      have hprefix := ih
        (p := p ∘ Fin.castSucc) (q := q ∘ Fin.castSucc)
        (F := fun i ↦ F i.castSucc) (G := fun i ↦ G i.castSucc)
        (α := fun i ↦ α i.castSucc) (fun i ↦ hcell i.castSucc)
      calc
        (Path.Homotopic.Quotient.mk (Path.concat p F)).trans
            (Path.Homotopic.Quotient.mk (α (Fin.last (n + 1)))) =
          ((Path.Homotopic.Quotient.mk
              (Path.concat (p ∘ Fin.castSucc) (fun i ↦ F i.castSucc))).trans
            (Path.Homotopic.Quotient.mk (F (Fin.last n)))).trans
            (Path.Homotopic.Quotient.mk (α (Fin.last n).succ)) :=
          congrArg (fun z ↦ z.trans
            (Path.Homotopic.Quotient.mk (α (Fin.last n).succ)))
            (pathClass_concat_last p F)
        _ = (Path.Homotopic.Quotient.mk
              (Path.concat (p ∘ Fin.castSucc) (fun i ↦ F i.castSucc))).trans
            ((Path.Homotopic.Quotient.mk (F (Fin.last n))).trans
              (Path.Homotopic.Quotient.mk (α (Fin.last n).succ))) :=
          Path.Homotopic.Quotient.trans_assoc _ _ _
        _ = (Path.Homotopic.Quotient.mk
              (Path.concat (p ∘ Fin.castSucc) (fun i ↦ F i.castSucc))).trans
            ((Path.Homotopic.Quotient.mk (α (Fin.last n).castSucc)).trans
              (Path.Homotopic.Quotient.mk (G (Fin.last n)))) :=
          congrArg _ (hcell (Fin.last n))
        _ = ((Path.Homotopic.Quotient.mk
              (Path.concat (p ∘ Fin.castSucc) (fun i ↦ F i.castSucc))).trans
            (Path.Homotopic.Quotient.mk (α (Fin.last n).castSucc))).trans
              (Path.Homotopic.Quotient.mk (G (Fin.last n))) :=
          (Path.Homotopic.Quotient.trans_assoc _ _ _).symm
        _ = ((Path.Homotopic.Quotient.mk (α 0)).trans
              (Path.Homotopic.Quotient.mk
                (Path.concat (q ∘ Fin.castSucc) (fun i ↦ G i.castSucc)))).trans
              (Path.Homotopic.Quotient.mk (G (Fin.last n))) :=
          congrArg (fun z ↦ z.trans
            (Path.Homotopic.Quotient.mk (G (Fin.last n)))) hprefix
        _ = (Path.Homotopic.Quotient.mk (α 0)).trans
            ((Path.Homotopic.Quotient.mk
              (Path.concat (q ∘ Fin.castSucc) (fun i ↦ G i.castSucc))).trans
              (Path.Homotopic.Quotient.mk (G (Fin.last n)))) :=
          Path.Homotopic.Quotient.trans_assoc _ _ _
        _ = (Path.Homotopic.Quotient.mk (α 0)).trans
            (Path.Homotopic.Quotient.mk (Path.concat q G)) :=
          congrArg (Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.mk (α 0)))
            (pathClass_concat_last q G).symm

/-- Helper for Theorem 13.99.1: casting the endpoints of a composite path class
is the composite of the correspondingly cast factors. -/
private lemma pathClass_cast_trans {X : Type u} [TopologicalSpace X]
    {a b c a' b' c' : X} (q : Path.Homotopic.Quotient a b)
    (r : Path.Homotopic.Quotient b c) (ha : a' = a) (hb : b' = b)
    (hc : c' = c) :
    (q.trans r).cast ha hc = (q.cast ha hb).trans (r.cast hb hc) := by
  -- Once the endpoint equalities are eliminated, both sides are definitionally identical.
  subst a'
  subst b'
  subst c'
  simp only [Path.Homotopic.Quotient.cast_rfl_rfl]

/-- Helper for Theorem 13.99.1: inserting a connector and its reverse between
two composable path classes factors the resulting closed class. -/
private lemma closedPathClass_paste {X : Type u} [TopologicalSpace X]
    {x₀ a b c : X}
    (A : Path.Homotopic.Quotient x₀ a)
    (P : Path.Homotopic.Quotient a b)
    (G : Path.Homotopic.Quotient x₀ b)
    (E : Path.Homotopic.Quotient b c)
    (B : Path.Homotopic.Quotient x₀ c) :
    A.trans ((P.trans E).trans B.symm) =
      (A.trans (P.trans G.symm)).trans (G.trans (E.trans B.symm)) := by
  -- Reassociate until the inserted inverse connector cancels in the middle.
  rw [Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.trans_assoc]
  apply congrArg (Path.Homotopic.Quotient.trans A)
  rw [Path.Homotopic.Quotient.trans_assoc]
  apply congrArg (Path.Homotopic.Quotient.trans P)
  rw [← Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Theorem 13.99.1: if every connector-closed edge of a finite path
chain belongs to a subgroup, then the connector-closed concatenation does too. -/
private lemma closedConcat_mem_of_edges {X : Type u} [TopologicalSpace X]
    {x₀ : X} (H : Subgroup (FundamentalGroup X x₀)) {n : ℕ}
    (p : Fin (n + 1) → X)
    (F : (i : Fin n) → Path (p i.castSucc) (p i.succ))
    (c : (i : Fin (n + 1)) → Path x₀ (p i))
    (hedge : ∀ i,
      ((Path.Homotopic.Quotient.mk (c i.castSucc)).trans
        ((Path.Homotopic.Quotient.mk (F i)).trans
          (Path.Homotopic.Quotient.mk (c i.succ)).symm) :
        FundamentalGroup X x₀) ∈ H) :
    ((Path.Homotopic.Quotient.mk (c 0)).trans
      ((Path.Homotopic.Quotient.mk (Path.concat p F)).trans
        (Path.Homotopic.Quotient.mk (c (Fin.last n))).symm) :
      FundamentalGroup X x₀) ∈ H := by
  induction n with
  | zero =>
      -- The empty concatenation closes a connector by its own reverse.
      simp only [Path.concat_zero, Path.Homotopic.Quotient.mk_refl,
        Path.Homotopic.Quotient.refl_trans]
      have hcLast : c (Fin.last 0) = c 0 := rfl
      rw [hcLast, Path.Homotopic.Quotient.trans_symm,
        ← FundamentalGroup.one_def]
      exact H.one_mem
  | succ n ih =>
      -- Factor off the last closed edge and use subgroup multiplication.
      have hprefix := ih
        (p := p ∘ Fin.castSucc) (F := fun i ↦ F i.castSucc)
        (c := fun i ↦ c i.castSucc) (fun i ↦ hedge i.castSucc)
      have hlast := hedge (Fin.last n)
      have hsplit := closedPathClass_paste
        (Path.Homotopic.Quotient.mk (c 0))
        (Path.Homotopic.Quotient.mk
          (Path.concat (p ∘ Fin.castSucc) (fun i ↦ F i.castSucc)))
        (Path.Homotopic.Quotient.mk (c (Fin.last n).castSucc))
        (Path.Homotopic.Quotient.mk (F (Fin.last n)))
        (Path.Homotopic.Quotient.mk (c (Fin.last (n + 1))))
      have hproduct := H.mul_mem hlast hprefix
      rw [FundamentalGroup.mul_def] at hproduct
      rw [pathClass_concat_last, hsplit]
      exact hproduct

/-- Helper for Theorem 13.99.1: membership of a connector-closed path, together
with membership of its two endpoint connectors, implies membership of the middle loop. -/
private lemma middle_mem_of_closedConcat {X : Type u} [TopologicalSpace X]
    {x₀ a b : X} (H : Subgroup (FundamentalGroup X x₀))
    (ha : a = x₀) (hb : b = x₀) (α : Path x₀ a) (P : Path a b)
    (β : Path x₀ b)
    (hα : (Path.Homotopic.Quotient.mk (α.cast rfl ha.symm) :
      FundamentalGroup X x₀) ∈ H)
    (hβ : (Path.Homotopic.Quotient.mk (β.cast rfl hb.symm) :
      FundamentalGroup X x₀) ∈ H)
    (hclosed : ((Path.Homotopic.Quotient.mk α).trans
      ((Path.Homotopic.Quotient.mk P).trans
        (Path.Homotopic.Quotient.mk β).symm) :
      FundamentalGroup X x₀) ∈ H) :
    (Path.Homotopic.Quotient.mk (P.cast ha.symm hb.symm) :
      FundamentalGroup X x₀) ∈ H := by
  -- Replace the endpoint types by the basepoint before carrying out group cancellation.
  subst a
  subst b
  simp only [Path.Homotopic.Quotient.mk_cast,
    Path.Homotopic.Quotient.cast_rfl_rfl] at hα hβ hclosed ⊢
  have happended := H.mul_mem hβ hclosed
  rw [FundamentalGroup.mul_def] at happended
  simp only [Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.trans_refl] at happended
  have hcancelled := H.mul_mem happended (H.inv_mem hα)
  rw [FundamentalGroup.mul_def, FundamentalGroup.inv_def,
    ← Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans] at hcancelled
  exact hcancelled

/-- Helper for Theorem 13.99.1: the subgroup generated by a countable set in a
group is countable. -/
private lemma Subgroup.countable_closure {G : Type*} [Group G] (s : Set G)
    (hs : s.Countable) : Countable (Subgroup.closure s) := by
  -- Realize the closure as the range of the free group on the subtype of generators.
  letI : Countable s := hs.to_subtype
  rw [FreeGroup.closure_eq_range]
  exact Function.Surjective.countable
    (MonoidHom.rangeRestrict_surjective
      (FreeGroup.lift ((↑) : s → G)))

/-- Theorem 13.99.1. The fundamental group of a path-connected, locally path-connected,
semilocally simply connected, regular space with a countable basis is countable. Here
Munkres's regularity is represented by `T3Space`, and a countable basis by
`SecondCountableTopology`. -/
instance instCountableOfSemilocallySimplyConnected {X : Type u} [TopologicalSpace X]
    [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] [T3Space X]
    [SecondCountableTopology X] (x₀ : X) : Countable (FundamentalGroup X x₀) := by
  classical
  -- Fix the countable barycentric basis that controls all local path comparisons.
  obtain ⟨ℬ, hℬcount, hℬbasis, hℬpath, hℬoverlap⟩ :=
    exists_countable_pathConnected_trivializingBasis (X := X)
  let I := ℬ
  letI : Countable I := hℬcount.to_subtype
  have hInonempty : Nonempty I := by
    have hxcover : x₀ ∈ ⋃₀ ℬ := hℬbasis.sUnion_eq.symm ▸ Set.mem_univ x₀
    obtain ⟨B, hBℬ, hxB⟩ := Set.mem_sUnion.mp hxcover
    exact ⟨⟨B, hBℬ⟩⟩
  let i₀ : I := Classical.choice hInonempty
  have hpoint : ∀ i : I, ∃ x : X, x ∈ (i : Set X) := by
    intro i
    exact (hℬpath i i.property).nonempty
  choose p hp using hpoint
  let y₀ : X := p i₀
  let c : (i : I) → Path y₀ (p i) := fun i ↦
    PathConnectedSpace.somePath y₀ (p i)
  -- Choose one select path for every intersecting ordered pair of basis members.
  let E := {e : I × I // ((e.1 : Set X) ∩ (e.2 : Set X)).Nonempty}
  letI : Countable E := inferInstance
  have hedgePath : ∀ e : E, ∃ g : Path (p e.1.1) (p e.1.2),
      Set.range g ⊆ (e.1.1 : Set X) ∪ (e.1.2 : Set X) := by
    intro e
    have hunion := (hℬpath e.1.1 e.1.1.property).union
      (hℬpath e.1.2 e.1.2.property) e.property
    have hjoined := hunion.joinedIn (p e.1.1) (Or.inl (hp e.1.1))
      (p e.1.2) (Or.inr (hp e.1.2))
    refine ⟨hjoined.somePath, ?_⟩
    rintro x ⟨t, rfl⟩
    exact hjoined.somePath_mem t
  choose g hg using hedgePath
  let edgeClass : E → FundamentalGroup X y₀ := fun e ↦
    Path.Homotopic.Quotient.mk
      ((c e.1.1).trans ((g e).trans (c e.1.2).symm))
  let baseClass : FundamentalGroup X y₀ :=
    Path.Homotopic.Quotient.mk (c i₀)
  let S : Set (FundamentalGroup X y₀) :=
    Set.range edgeClass ∪ {baseClass}
  have hScount : S.Countable :=
    Set.countable_range edgeClass |>.union (Set.countable_singleton baseClass)
  let H : Subgroup (FundamentalGroup X y₀) := Subgroup.closure S
  -- The selected edge loops generate: subdivide an arbitrary represented loop.
  have hHtop : H = ⊤ := by
    apply top_unique
    intro q _
    obtain ⟨f, rfl⟩ :=
      Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath q)
    let d : I → Set unitInterval := fun i ↦ f ⁻¹' (i : Set X)
    have hdOpen : ∀ i, IsOpen (d i) := by
      intro i
      exact (hℬbasis.isOpen i.property).preimage f.continuous
    have hdCover : Set.univ ⊆ ⋃ i, d i := by
      intro s _
      have hfs : f s ∈ ⋃₀ ℬ := hℬbasis.sUnion_eq.symm ▸ Set.mem_univ (f s)
      obtain ⟨B, hBℬ, hfsB⟩ := Set.mem_sUnion.mp hfs
      exact Set.mem_iUnion.mpr ⟨⟨B, hBℬ⟩, hfsB⟩
    obtain ⟨t, ht0, htmono, ⟨m, hm⟩, htSubordinate⟩ :=
      exists_monotone_Icc_subset_open_cover_unitInterval hdOpen hdCover
    choose side hside using htSubordinate
    let a : Fin (m + 2) → unitInterval := fun i ↦ t i
    let B : Fin (m + 1) → I := Fin.lastCases i₀ (fun i ↦ side i)
    let C : Fin (m + 2) → I := Fin.cons i₀ B
    let F : (i : Fin (m + 1)) →
        Path (f (a i.castSucc)) (f (a i.succ)) := fun i ↦
      f.subpath (a i.castSucc) (a i.succ)
    have haStart : a 0 = 0 := ht0
    have haEnd : a (Fin.last (m + 1)) = 1 := hm (m + 1) (Nat.le_succ m)
    -- Every subpath lies in its assigned basis member; the last one is constant in `i₀`.
    have hF : ∀ i, Set.range (F i) ⊆ (B i : Set X) := by
      intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · have hleft : a (Fin.last m).castSucc = 1 := hm m le_rfl
        have hright : a (Fin.last m).succ = 1 := hm (m + 1) (Nat.le_succ m)
        rw [show B (Fin.last m) = i₀ by simp only [B, Fin.lastCases_last]]
        dsimp only [F]
        rw [hleft, hright, Path.subpath_self, Path.refl_range]
        exact Set.singleton_subset_iff.mpr (f.target.symm ▸ hp i₀)
      · have hstep : a j.castSucc.castSucc ≤ a j.castSucc.succ := by
          exact htmono (Nat.le_succ j)
        rw [show B j.castSucc = side j by
          simp only [B, Fin.lastCases_castSucc]]
        dsimp only [F]
        rw [Path.range_subpath_of_le f _ _ hstep]
        rintro z ⟨s, hs, rfl⟩
        exact hside j hs
    -- At each subdivision vertex, record the previous basis member used by the source proof.
    have hvertex : ∀ j, f (a j) ∈ (C j : Set X) := by
      intro j
      refine Fin.cases ?_ (fun i ↦ ?_) j
      · rw [show C 0 = i₀ by simp only [C, Fin.cons_zero], haStart, f.source]
        exact hp i₀
      · rw [show C i.succ = B i by simp only [C, Fin.cons_succ]]
        exact hF i (Path.target_mem_range (F i))
    have hinter : ∀ i : Fin (m + 1),
        ((C i.castSucc : Set X) ∩ (C i.succ : Set X)).Nonempty := by
      intro i
      refine ⟨f (a i.castSucc), hvertex i.castSucc, ?_⟩
      rw [show C i.succ = B i by simp only [C, Fin.cons_succ]]
      exact hF i (Path.source_mem_range (F i))
    let e : Fin (m + 1) → E := fun i ↦
      ⟨(C i.castSucc, C i.succ), hinter i⟩
    let G : (i : Fin (m + 1)) →
        Path (p (C i.castSucc)) (p (C i.succ)) := fun i ↦ g (e i)
    -- Join each subdivision vertex to the selected point of its preceding basis member.
    have hconnector : ∀ j, ∃ α : Path (f (a j)) (p (C j)),
        Set.range α ⊆ (C j : Set X) := by
      intro j
      have hjoined := (hℬpath (C j) (C j).property).joinedIn
        (f (a j)) (hvertex j) (p (C j)) (hp (C j))
      refine ⟨hjoined.somePath, ?_⟩
      rintro x ⟨t, rfl⟩
      exact hjoined.somePath_mem t
    choose α hα using hconnector
    -- Each source cell equation holds inside one common trivializing parent.
    have hcell : ∀ i,
        (Path.Homotopic.Quotient.mk (F i)).trans
            (Path.Homotopic.Quotient.mk (α i.succ)) =
          (Path.Homotopic.Quotient.mk (α i.castSucc)).trans
            (Path.Homotopic.Quotient.mk (G i)) := by
      intro i
      obtain ⟨A, hApath, hCA, z, hz⟩ :=
        hℬoverlap (C i.castSucc) (C i.castSucc).property
          (C i.succ) (C i.succ).property (hinter i)
      have hleft : Set.range ((F i).trans (α i.succ)) ⊆ A := by
        rw [Path.trans_range]
        apply Set.union_subset
        · exact (hF i).trans (fun x hx ↦ hCA (Or.inr hx))
        · exact (hα i.succ).trans (fun x hx ↦ hCA (Or.inr hx))
      have hright : Set.range ((α i.castSucc).trans (G i)) ⊆ A := by
        rw [Path.trans_range]
        apply Set.union_subset
        · exact (hα i.castSucc).trans (fun x hx ↦ hCA (Or.inl hx))
        · exact (hg (e i)).trans hCA
      have hpaths := pathClass_eq_of_range_subset_trivializing
        hApath z hz ((F i).trans (α i.succ))
          ((α i.castSucc).trans (G i)) hleft hright
      simpa only [Path.Homotopic.Quotient.mk_trans] using hpaths
    -- Telescope the cell equations, then transport only the two outer endpoints.
    have htele := pathClass_concat_eq_of_cell
      (p := fun j ↦ f (a j)) (q := fun j ↦ p (C j))
      F G α hcell
    have hpStart : f (a 0) = y₀ :=
      (congrArg f haStart).trans f.source
    have hpEnd : f (a (Fin.last (m + 1))) = y₀ :=
      (congrArg f haEnd).trans f.target
    have hCStart : C 0 = i₀ := by
      simp only [C, Fin.cons_zero]
    have hCEnd : C (Fin.last (m + 1)) = i₀ := by
      simp only [C, Fin.cons_last, B, Fin.lastCases_last]
    have hqStart : p (C 0) = y₀ := by
      rw [hCStart]
    have hqEnd : p (C (Fin.last (m + 1))) = y₀ := by
      rw [hCEnd]
    let qF : FundamentalGroup X y₀ :=
      (Path.Homotopic.Quotient.mk (Path.concat (fun j ↦ f (a j)) F)).cast
        hpStart.symm hpEnd.symm
    let qG : FundamentalGroup X y₀ :=
      (Path.Homotopic.Quotient.mk (Path.concat (fun j ↦ p (C j)) G)).cast
        hqStart.symm hqEnd.symm
    let αStart : FundamentalGroup X y₀ :=
      (Path.Homotopic.Quotient.mk (α 0)).cast hpStart.symm hqStart.symm
    let αEnd : FundamentalGroup X y₀ :=
      (Path.Homotopic.Quotient.mk (α (Fin.last (m + 1)))).cast
        hpEnd.symm hqEnd.symm
    have hteleCast := congrArg
      (fun z : Path.Homotopic.Quotient (f (a 0))
          (p (C (Fin.last (m + 1)))) ↦
        z.cast hpStart.symm hqEnd.symm) htele
    have hteleLoop : qF.trans αEnd = αStart.trans qG := by
      dsimp only [qF, qG, αStart, αEnd]
      rw [pathClass_cast_trans, pathClass_cast_trans] at hteleCast
      exact hteleCast
    -- The two endpoint connectors are null because both remain in `i₀`.
    obtain ⟨A₀, hA₀path, hi₀A₀, z₀, hz₀⟩ :=
      hℬoverlap i₀ i₀.property i₀ i₀.property
        ⟨p i₀, hp i₀, hp i₀⟩
    have hαStartRange : Set.range ((α 0).cast hpStart.symm hqStart.symm) ⊆ A₀ := by
      rintro x ⟨s, rfl⟩
      rw [Path.cast_coe]
      exact hi₀A₀ (Or.inl (hCStart ▸ hα 0 (Set.mem_range_self s)))
    have hαEndRange :
        Set.range ((α (Fin.last (m + 1))).cast hpEnd.symm hqEnd.symm) ⊆ A₀ := by
      rintro x ⟨s, rfl⟩
      rw [Path.cast_coe]
      exact hi₀A₀ (Or.inl (hCEnd ▸
        hα (Fin.last (m + 1)) (Set.mem_range_self s)))
    have hreflRange : Set.range (Path.refl y₀) ⊆ A₀ := by
      rw [Path.refl_range]
      exact Set.singleton_subset_iff.mpr (hi₀A₀ (Or.inl (hp i₀)))
    have hαStartOne : αStart = Path.Homotopic.Quotient.refl y₀ := by
      dsimp only [αStart]
      rw [← Path.Homotopic.Quotient.mk_cast]
      exact pathClass_eq_of_range_subset_trivializing hA₀path z₀ hz₀
        ((α 0).cast hpStart.symm hqStart.symm) (Path.refl y₀)
          hαStartRange hreflRange
    have hαEndOne : αEnd = Path.Homotopic.Quotient.refl y₀ := by
      dsimp only [αEnd]
      rw [← Path.Homotopic.Quotient.mk_cast]
      exact pathClass_eq_of_range_subset_trivializing hA₀path z₀ hz₀
        ((α (Fin.last (m + 1))).cast hpEnd.symm hqEnd.symm)
          (Path.refl y₀) hαEndRange hreflRange
    have hFG : qF = qG := by
      rw [hαEndOne, hαStartOne,
        Path.Homotopic.Quotient.trans_refl,
        Path.Homotopic.Quotient.refl_trans] at hteleLoop
      exact hteleLoop
    -- Close every selected edge by the fixed reference paths and generate the whole chain.
    have hedgeMem : ∀ i,
        ((Path.Homotopic.Quotient.mk (c (C i.castSucc))).trans
          ((Path.Homotopic.Quotient.mk (G i)).trans
            (Path.Homotopic.Quotient.mk (c (C i.succ))).symm) :
          FundamentalGroup X y₀) ∈ H := by
      intro i
      have hgenerator : edgeClass (e i) ∈ S :=
        Or.inl ⟨e i, rfl⟩
      have hclosure : edgeClass (e i) ∈ H := by
        exact Subgroup.subset_closure hgenerator
      have hedgeEq :
          ((Path.Homotopic.Quotient.mk (c (C i.castSucc))).trans
            ((Path.Homotopic.Quotient.mk (G i)).trans
              (Path.Homotopic.Quotient.mk (c (C i.succ))).symm) :
            FundamentalGroup X y₀) = edgeClass (e i) := by
        dsimp only [edgeClass, G, e]
        rfl
      rw [hedgeEq]
      exact hclosure
    have hclosed := closedConcat_mem_of_edges H
      (p := fun j ↦ p (C j)) G (fun j ↦ c (C j)) hedgeMem
    have hbase : baseClass ∈ H :=
      Subgroup.subset_closure (Or.inr (Set.mem_singleton baseClass))
    have hcStart :
        (Path.Homotopic.Quotient.mk
          ((c (C 0)).cast rfl hqStart.symm) : FundamentalGroup X y₀) ∈ H := by
      have hcStartPath : (c (C 0)).cast rfl hqStart.symm = c i₀ := by
        ext s
        rw [Path.cast_coe, hCStart]
      rw [hcStartPath]
      exact hbase
    have hcEnd :
        (Path.Homotopic.Quotient.mk
          ((c (C (Fin.last (m + 1)))).cast rfl hqEnd.symm) :
          FundamentalGroup X y₀) ∈ H := by
      have hcEndPath :
          (c (C (Fin.last (m + 1)))).cast rfl hqEnd.symm = c i₀ := by
        ext s
        rw [Path.cast_coe, hCEnd]
      rw [hcEndPath]
      exact hbase
    have hqGmem : qG ∈ H := by
      have hmiddle := middle_mem_of_closedConcat H hqStart hqEnd
        (c (C 0)) (Path.concat (fun j ↦ p (C j)) G)
          (c (C (Fin.last (m + 1)))) hcStart hcEnd hclosed
      exact hmiddle
    -- The subdivision class is the original loop class, so the arbitrary element lies in `H`.
    have hfSubdivision := pathClass_eq_concatSubpaths f a haStart haEnd
    have hfqF : (Path.Homotopic.Quotient.mk f : FundamentalGroup X y₀) = qF := by
      calc
        (Path.Homotopic.Quotient.mk f : FundamentalGroup X y₀) =
            Path.Homotopic.Quotient.mk
              ((Path.concat (f ∘ a)
                (fun i ↦ f.subpath (a i.castSucc) (a i.succ))).cast
                  ((congrArg f haStart).trans f.source).symm
                  ((congrArg f haEnd).trans f.target).symm) := hfSubdivision
        _ = qF := by
          dsimp only [qF, F]
          rfl
    rw [hfqF, hFG]
    exact hqGmem
  -- A countable generating alphabet gives a countable closure, hence a countable group at `y₀`.
  have hHcount : Countable H := Subgroup.countable_closure S hScount
  letI : Countable H := hHcount
  have hcoeSurjective : Function.Surjective ((↑) : H → FundamentalGroup X y₀) := by
    intro q
    refine ⟨⟨q, ?_⟩, rfl⟩
    rw [hHtop]
    exact Subgroup.mem_top q
  have hy₀Count : Countable (FundamentalGroup X y₀) :=
    Function.Surjective.countable hcoeSurjective
  -- Finally transfer countability along basepoint independence in the path-connected space.
  letI : Countable (FundamentalGroup X y₀) := hy₀Count
  exact Function.Surjective.countable
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected y₀ x₀).surjective

end FundamentalGroup

end
