import Mathlib
import Mathlib.Tactic.Recall
import Mathlib.Topology.Connected.LocPathConnected

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_1_1 (from Chap03) -/
universe u

variable {X : Type u} [TopologicalSpace X]

/- Definition 3.1.1: a space is locally path connected when the canonical predicate
`LocPathConnectedSpace X` holds, equivalently when each point has arbitrarily small neighborhoods
whose points can be joined to the basepoint by paths staying inside a prescribed neighborhood. -/
recall LocPathConnectedSpace (X : Type u) [TopologicalSpace X] : Prop

/-- Local path connectedness means that every neighborhood of a point contains a smaller
neighborhood whose points can be joined to the basepoint by a path staying in the original
neighborhood; this witness neighborhood is therefore automatically contained in the original
neighborhood. -/
-- Proof sketch: use the path-connected neighborhood basis from `LocPathConnectedSpace` and the
-- fact that any two points in a path-connected subset are joined by a path inside that subset;
-- conversely, apply the neighborhood criterion to build a basis of path-connected neighborhoods.
theorem locPathConnectedSpace_iff_has_smaller_joinedIn_neighborhoods :
    LocPathConnectedSpace X ↔
      ∀ x : X, ∀ U : Set X, U ∈ nhds x →
        ∃ V : Set X, V ∈ nhds x ∧ ∀ ⦃y : X⦄, y ∈ V → JoinedIn U x y := by
  constructor
  · intro hX x U hU
    letI : LocPathConnectedSpace X := hX
    exact ⟨pathComponentIn U x, pathComponentIn_mem_nhds hU, fun _ hy ↦ hy⟩
  · intro h
    rw [locPathConnectedSpace_iff_pathComponentIn_mem_nhds]
    intro x u hu hxu
    rcases h x u (hu.mem_nhds hxu) with ⟨V, hV, hJoined⟩
    exact Filter.mem_of_superset hV fun _ hy ↦ hJoined hy

/-! ### Lemma_3_1_2 (from Chap03) -/
universe u

open TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/-- Lemma 3.1.2: a space is locally path connected exactly when its topology admits a basis
consisting of open path-connected sets. -/
-- Proof sketch: if `X` is locally path connected, use the open path-connected neighborhood basis
-- at each point and `IsTopologicalBasis.of_hasBasis_nhds`; conversely, a topological basis of open
-- path-connected sets yields a neighborhood basis of path-connected neighborhoods via
-- `IsTopologicalBasis.nhds_hasBasis`, giving `LocPathConnectedSpace X`.
theorem locPathConnectedSpace_iff_isTopologicalBasis_isOpen_isPathConnected :
    LocPathConnectedSpace X ↔
      IsTopologicalBasis {s : Set X | IsOpen s ∧ IsPathConnected s} where
  mp h := by
    letI : LocPathConnectedSpace X := h
    exact .of_hasBasis_nhds fun x ↦
      (isOpen_isPathConnected_basis x).congr
        (by simp [and_assoc, and_comm])
        (fun _ _ ↦ rfl)
  mpr h :=
    LocPathConnectedSpace.of_bases (fun x ↦ h.nhds_hasBasis) fun _ _ hs ↦ hs.1.2

/-! ### Lemma_3_1_3 (from Chap03) -/
/- Lemma 3.1.3: every connected locally path-connected space is path connected, via the
canonical theorem `PathConnectedSpace.of_locPathConnectedSpace`. -/
recall PathConnectedSpace.of_locPathConnectedSpace

/-! ### Assumption_3_1_4 (from Chap03) -/
universe u

/- Assumption 3.1.4: the ambient spaces in Chapter 3 are assumed connected and locally path
connected unless explicitly stated otherwise, so the canonical ambient hypotheses are
`ConnectedSpace X` and `LocPathConnectedSpace X`. -/
recall ConnectedSpace (X : Type u) [TopologicalSpace X] : Prop

/- Assumption 3.1.4 also uses the standard local path-connectedness hypothesis. -/
recall LocPathConnectedSpace (X : Type u) [TopologicalSpace X] : Prop

/-! ### Definition_3_1_5 (from Chap03) -/
universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- A point of the base has a path-connected evenly covered neighborhood when the map is evenly
covered in the sense of `IsEvenlyCovered`, and the chosen evenly covered neighborhood can be taken
to be path-connected. -/
def IsPathConnectedEvenlyCovered (p : E → B) (b : B) : Prop :=
  DiscreteTopology (p ⁻¹' {b}) ∧
    ∃ V : Set B, b ∈ V ∧ IsOpen V ∧ IsPathConnected V ∧ IsOpen (p ⁻¹' V) ∧
      ∃ H : p ⁻¹' V ≃ₜ V × (p ⁻¹' {b}), ∀ e, (H e).1.1 = p e

namespace IsPathConnectedEvenlyCovered

variable {p : E → B} {b : B}

/-- Forgetting path connectedness turns a path-connected evenly covered neighborhood into an
ordinary evenly covered neighborhood. -/
theorem isEvenlyCovered (hb : IsPathConnectedEvenlyCovered p b) :
    IsEvenlyCovered p b (p ⁻¹' {b}) := by
  rcases hb with ⟨hdiscrete, V, hbV, hVOpen, _hVPathConnected, hpVOpen, H, hH⟩
  exact ⟨hdiscrete, V, hbV, hVOpen, hpVOpen, H, hH⟩

end IsPathConnectedEvenlyCovered

/-- Definition 3.1.5: a covering map is a surjective map such that every point of the base has a
path-connected evenly covered neighborhood. -/
def IsPathConnectedCoveringMap (p : E → B) : Prop :=
  Function.Surjective p ∧ ∀ b : B, IsPathConnectedEvenlyCovered p b

namespace IsPathConnectedCoveringMap

variable {p : E → B}

/-- A path-connected covering map is surjective. -/
theorem surjective (hp : IsPathConnectedCoveringMap p) : Function.Surjective p := hp.1

/-- A path-connected covering map is a covering map in the sense of `IsCoveringMap`. -/
theorem isCoveringMap (hp : IsPathConnectedCoveringMap p) : IsCoveringMap p := by
  intro b
  exact (hp.2 b).isEvenlyCovered

end IsPathConnectedCoveringMap

namespace IsCoveringMap

variable {p : E → B} [LocPathConnectedSpace B]

/-- In a locally path-connected base, a surjective covering map has path-connected evenly covered
neighborhoods, so it is a covering map in the sense of Definition 3.1.5. -/
theorem isPathConnectedCoveringMap (hp : IsCoveringMap p)
    (hsurj : Function.Surjective p) : IsPathConnectedCoveringMap p := by
  refine ⟨hsurj, fun b ↦ ?_⟩
  have hpb := hp b
  have hbFiber : Nonempty (p ⁻¹' ({b} : Set B)) := by
    rcases hsurj b with ⟨e, rfl⟩
    exact ⟨⟨e, rfl⟩⟩
  let t : Bundle.Trivialization (p ⁻¹' ({b} : Set B)) p := hpb.toTrivialization
  have hbBase : b ∈ t.baseSet := hpb.mem_toTrivialization_baseSet
  let V : Set B := pathComponentIn t.baseSet b
  have hVBase : V ⊆ t.baseSet := pathComponentIn_subset
  have hbV : b ∈ V := mem_pathComponentIn_self hbBase
  have hVOpen : IsOpen V := t.open_baseSet.pathComponentIn b
  have hVPath : IsPathConnected V := isPathConnected_pathComponentIn hbBase
  let tV : Bundle.Trivialization (p ⁻¹' ({b} : Set B)) p := t.restrOpen V hVOpen
  refine ⟨hpb.discreteTopology_fiber, V, hbV, hVOpen, hVPath, ?_, ?_, ?_⟩
  · simpa using hVOpen.preimage hp.continuous
  · exact tV.preimageHomeomorph fun y hy ↦ ⟨hVBase hy, hy⟩
  · intro e
    simp [Bundle.Trivialization.preimageHomeomorph_apply, tV, V]

end IsCoveringMap

/-! ### Definition_3_1_6 (from Chap03) -/
universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- Definition 3.1.6: for a cover `p : E → B`, the space `E` is the total space, `B` is the base
space, the set-theoretic fiber over `b` is `p ⁻¹' {b}`, and a set `V ⊆ B` is a fundamental
neighborhood of `b` when it is a path-connected evenly covered neighborhood for `p`. -/
def IsFundamentalNeighborhood (p : E → B) (b : B) (V : Set B) : Prop :=
  DiscreteTopology (p ⁻¹' {b}) ∧
    b ∈ V ∧ IsOpen V ∧ IsPathConnected V ∧ IsOpen (p ⁻¹' V) ∧
    ∃ H : p ⁻¹' V ≃ₜ V × (p ⁻¹' {b}), ∀ e, (H e).1.1 = p e

namespace IsFundamentalNeighborhood

variable {p : E → B} {b : B} {V : Set B}

/-- A fundamental neighborhood supplies the chosen witness for
`IsPathConnectedEvenlyCovered p b`. -/
theorem isPathConnectedEvenlyCovered (hV : IsFundamentalNeighborhood p b V) :
    IsPathConnectedEvenlyCovered p b := by
  rcases hV with ⟨hdiscrete, hbV, hVOpen, hVPathConnected, hpVOpen, H, hH⟩
  exact ⟨hdiscrete, V, hbV, hVOpen, hVPathConnected, hpVOpen, H, hH⟩

/-- A fundamental neighborhood is, in particular, an evenly covered neighborhood with fiber
`p ⁻¹' {b}`. -/
theorem isEvenlyCovered (hV : IsFundamentalNeighborhood p b V) :
    IsEvenlyCovered p b (p ⁻¹' {b}) :=
  hV.isPathConnectedEvenlyCovered.isEvenlyCovered

/-- A point has a path-connected evenly covered neighborhood exactly when it admits some
fundamental neighborhood. -/
theorem exists_iff : IsPathConnectedEvenlyCovered p b ↔ ∃ V, IsFundamentalNeighborhood p b V := by
  constructor
  · rintro ⟨hdiscrete, V, hbV, hVOpen, hVPathConnected, hpVOpen, H, hH⟩
    exact ⟨V, hdiscrete, hbV, hVOpen, hVPathConnected, hpVOpen, H, hH⟩
  · rintro ⟨V, hV⟩
    exact hV.isPathConnectedEvenlyCovered

end IsFundamentalNeighborhood

/-! ### Example_3_1_7 (from Chap03) -/
noncomputable section

open scoped TopCat

universe u v u₁ v₁ u₂ v₂

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {E₁ : Type u₁} {B₁ : Type v₁} {E₂ : Type u₂} {B₂ : Type v₂}
variable [TopologicalSpace E₁] [TopologicalSpace B₁] [TopologicalSpace E₂] [TopologicalSpace B₂]

namespace IsEvenlyCovered

/-- The product of two evenly covered neighborhoods is evenly covered for the product map. -/
theorem prodMap {p : E₁ → B₁} {q : E₂ → B₂} {b₁ : B₁} {b₂ : B₂}
    (hp : IsEvenlyCovered p b₁ (p ⁻¹' ({b₁} : Set B₁)))
    (hq : IsEvenlyCovered q b₂ (q ⁻¹' ({b₂} : Set B₂))) :
    IsEvenlyCovered (Prod.map p q) (b₁, b₂)
      (Prod.map p q ⁻¹' ({(b₁, b₂)} : Set (B₁ × B₂))) := by
  rcases hp with ⟨hpdisc, U₁, hb₁U₁, hU₁, hpU₁, H₁, hH₁⟩
  rcases hq with ⟨hqdisc, U₂, hb₂U₂, hU₂, hqU₂, H₂, hH₂⟩
  have hpre :
      Prod.map p q ⁻¹' (U₁ ×ˢ U₂) = (p ⁻¹' U₁) ×ˢ (q ⁻¹' U₂) := by
    ext x
    simp [Prod.map]
  have hfiber :
      Prod.map p q ⁻¹' ({(b₁, b₂)} : Set (B₁ × B₂)) =
        (p ⁻¹' ({b₁} : Set B₁)) ×ˢ (q ⁻¹' ({b₂} : Set B₂)) := by
    ext x
    simp [Prod.map]
  let hFiber :
      ((p ⁻¹' ({b₁} : Set B₁)) × (q ⁻¹' ({b₂} : Set B₂))) ≃ₜ
        (Prod.map p q ⁻¹' ({(b₁, b₂)} : Set (B₁ × B₂))) :=
    (Homeomorph.Set.prod (p ⁻¹' ({b₁} : Set B₁)) (q ⁻¹' ({b₂} : Set B₂))).symm.trans
      (Homeomorph.setCongr hfiber.symm)
  have hdisc : DiscreteTopology (Prod.map p q ⁻¹' ({(b₁, b₂)} : Set (B₁ × B₂))) := by
    letI : DiscreteTopology (p ⁻¹' ({b₁} : Set B₁)) := hpdisc
    letI : DiscreteTopology (q ⁻¹' ({b₂} : Set B₂)) := hqdisc
    letI : DiscreteTopology
        ((p ⁻¹' ({b₁} : Set B₁)) × (q ⁻¹' ({b₂} : Set B₂))) := inferInstance
    exact hFiber.discreteTopology
  let H :
      ↑(Prod.map p q ⁻¹' (U₁ ×ˢ U₂)) ≃ₜ
        ↑(U₁ ×ˢ U₂) × (Prod.map p q ⁻¹' ({(b₁, b₂)} : Set (B₁ × B₂))) :=
    (Homeomorph.setCongr hpre).trans <|
      (Homeomorph.Set.prod (p ⁻¹' U₁) (q ⁻¹' U₂)).trans <|
        (H₁.prodCongr H₂).trans <|
          (Homeomorph.prodProdProdComm U₁ (p ⁻¹' ({b₁} : Set B₁)) U₂
            (q ⁻¹' ({b₂} : Set B₂))).trans <|
            Homeomorph.prodCongr
              (Homeomorph.Set.prod U₁ U₂).symm
              hFiber
  refine ⟨hdisc, U₁ ×ˢ U₂, ⟨hb₁U₁, hb₂U₂⟩, hU₁.prod hU₂, ?_, H, ?_⟩
  · simpa [Prod.map] using hpU₁.prod hqU₂
  · intro x
    have hx₁ : p x.1.1 ∈ U₁ := by
      simpa [Prod.map] using x.2.1
    have hx₂ : q x.1.2 ∈ U₂ := by
      simpa [Prod.map] using x.2.2
    ext
    · simpa [H, Prod.map] using hH₁ ⟨x.1.1, hx₁⟩
    · simpa [H, Prod.map] using hH₂ ⟨x.1.2, hx₂⟩

end IsEvenlyCovered

namespace IsPathConnectedEvenlyCovered

/-- Path-connected evenly covered neighborhoods are stable under products. -/
theorem prodMap {p : E₁ → B₁} {q : E₂ → B₂} {b₁ : B₁} {b₂ : B₂}
    (hp : IsPathConnectedEvenlyCovered p b₁)
    (hq : IsPathConnectedEvenlyCovered q b₂) :
    IsPathConnectedEvenlyCovered (Prod.map p q) (b₁, b₂) := by
  rcases hp with ⟨hpdisc, U₁, hb₁U₁, hU₁, hU₁Path, hpU₁, H₁, hH₁⟩
  rcases hq with ⟨hqdisc, U₂, hb₂U₂, hU₂, hU₂Path, hqU₂, H₂, hH₂⟩
  have hUProd : IsPathConnected (U₁ ×ˢ U₂) := by
    rw [isPathConnected_iff]
    refine ⟨hU₁Path.nonempty.prod hU₂Path.nonempty, ?_⟩
    intro x hx y hy
    let hx₁ := (isPathConnected_iff.mp hU₁Path).2 x.1 hx.1 y.1 hy.1
    let hx₂ := (isPathConnected_iff.mp hU₂Path).2 x.2 hx.2 y.2 hy.2
    exact ⟨hx₁.somePath.prod hx₂.somePath, fun t ↦ ⟨hx₁.somePath_mem t, hx₂.somePath_mem t⟩⟩
  have hpre :
      Prod.map p q ⁻¹' (U₁ ×ˢ U₂) = (p ⁻¹' U₁) ×ˢ (q ⁻¹' U₂) := by
    ext x
    simp [Prod.map]
  have hfiber :
      Prod.map p q ⁻¹' ({(b₁, b₂)} : Set (B₁ × B₂)) =
        (p ⁻¹' ({b₁} : Set B₁)) ×ˢ (q ⁻¹' ({b₂} : Set B₂)) := by
    ext x
    simp [Prod.map]
  let hFiber :
      ((p ⁻¹' ({b₁} : Set B₁)) × (q ⁻¹' ({b₂} : Set B₂))) ≃ₜ
        (Prod.map p q ⁻¹' ({(b₁, b₂)} : Set (B₁ × B₂))) :=
    (Homeomorph.Set.prod (p ⁻¹' ({b₁} : Set B₁)) (q ⁻¹' ({b₂} : Set B₂))).symm.trans
      (Homeomorph.setCongr hfiber.symm)
  have hdisc : DiscreteTopology (Prod.map p q ⁻¹' ({(b₁, b₂)} : Set (B₁ × B₂))) := by
    letI : DiscreteTopology (p ⁻¹' ({b₁} : Set B₁)) := hpdisc
    letI : DiscreteTopology (q ⁻¹' ({b₂} : Set B₂)) := hqdisc
    letI : DiscreteTopology
        ((p ⁻¹' ({b₁} : Set B₁)) × (q ⁻¹' ({b₂} : Set B₂))) := inferInstance
    exact hFiber.discreteTopology
  refine ⟨hdisc, U₁ ×ˢ U₂, ⟨hb₁U₁, hb₂U₂⟩, hU₁.prod hU₂, hUProd, ?_, ?_, ?_⟩
  · simpa [Prod.map] using hpU₁.prod hqU₂
  · exact
      (Homeomorph.setCongr hpre).trans <|
        (Homeomorph.Set.prod (p ⁻¹' U₁) (q ⁻¹' U₂)).trans <|
          (H₁.prodCongr H₂).trans <|
            (Homeomorph.prodProdProdComm U₁ (p ⁻¹' ({b₁} : Set B₁)) U₂
              (q ⁻¹' ({b₂} : Set B₂))).trans <|
              Homeomorph.prodCongr
                (Homeomorph.Set.prod U₁ U₂).symm
                hFiber
  · intro x
    have hx₁ : p x.1.1 ∈ U₁ := by
      simpa [Prod.map] using x.2.1
    have hx₂ : q x.1.2 ∈ U₂ := by
      simpa [Prod.map] using x.2.2
    ext
    · simpa [Prod.map] using hH₁ ⟨x.1.1, hx₁⟩
    · simpa [Prod.map] using hH₂ ⟨x.1.2, hx₂⟩

end IsPathConnectedEvenlyCovered

namespace Homeomorph

/-- Example 3.1.7 (1): every homeomorphism is a covering map. -/
-- Proof sketch: a homeomorphism identifies the source with the target, so every point has an open
-- neighborhood over which the map is trivial with singleton fiber.
theorem isCoveringMap (h : X ≃ₜ Y) : IsCoveringMap h := by
  have hf : Continuous (fun x : X ↦ ((h x, ()) : Y × Unit)) := by
    simpa using
      h.continuous.prodMk (continuous_const : Continuous fun _ : X ↦ (() : Unit))
  have hg : Continuous (fun yp : Y × Unit ↦ h.symm yp.1) := by
    fun_prop
  let t : Bundle.Trivialization Unit h := by
    refine
      { toFun := fun x ↦ (h x, ())
        invFun := fun yp : Y × Unit ↦ h.symm yp.1
        source := (_root_.Set.univ : Set X)
        target := (_root_.Set.univ : Set Y) ×ˢ (_root_.Set.univ : Set Unit)
        map_source' := ?_
        map_target' := ?_
        left_inv' := ?_
        right_inv' := ?_
        open_source := isOpen_univ
        open_target := isOpen_univ.prod isOpen_univ
        continuousOn_toFun := Continuous.continuousOn hf
        continuousOn_invFun := Continuous.continuousOn hg
        baseSet := (_root_.Set.univ : Set Y)
        open_baseSet := isOpen_univ
        source_eq := rfl
        target_eq := rfl
        proj_toFun := by intro x hx; rfl }
    · intro x hx
      simp [Set.mem_univ]
    · intro yp hyp
      simp [Set.mem_univ]
    · intro x hx
      simp
    · rintro ⟨y, u⟩ hyp
      cases u
      simp
  exact IsCoveringMap.mk h (fun _ ↦ Unit) (fun _ ↦ t) fun _ ↦ by simp [t]

/-- Example 3.1.7 (1), source-facing form: on a locally path-connected target, every
homeomorphism is a covering map in the sense of Definition 3.1.5. -/
theorem isPathConnectedCoveringMap [LocPathConnectedSpace Y] (h : X ≃ₜ Y) :
    IsPathConnectedCoveringMap h :=
  h.isCoveringMap.isPathConnectedCoveringMap h.surjective

end Homeomorph

namespace IsCoveringMap

/-- Example 3.1.7 (2): the product of two covering maps is again a covering map. -/
-- Proof sketch: take evenly covered neighborhoods for the two factors and use the product of the
-- corresponding local trivializations to trivialize the product map.
theorem prodMap {p : E₁ → B₁} {q : E₂ → B₂}
    (hp : IsCoveringMap p) (hq : IsCoveringMap q) :
    IsCoveringMap (Prod.map p q) := by
  rintro ⟨b₁, b₂⟩
  simpa using (hp b₁).prodMap (hq b₂)

end IsCoveringMap

namespace IsPathConnectedCoveringMap

/-- Example 3.1.7 (2), source-facing form: the product of two path-connected covering maps is
again a path-connected covering map. -/
theorem prodMap {p : E₁ → B₁} {q : E₂ → B₂}
    (hp : IsPathConnectedCoveringMap p) (hq : IsPathConnectedCoveringMap q) :
    IsPathConnectedCoveringMap (Prod.map p q) := by
  refine ⟨?_, fun b ↦ ?_⟩
  · simpa using hp.surjective.prodMap hq.surjective
  · rcases b with ⟨b₁, b₂⟩
    simpa using (hp.2 b₁).prodMap (hq.2 b₂)

end IsPathConnectedCoveringMap

/- Example 3.1.7 (3): the map `x ↦ e^{2πix}` from `ℝ` to `S¹`, represented by
`Real.fourierChar`, is a covering map. -/
recall real_fourierChar_isCoveringMap : IsCoveringMap Real.fourierChar

namespace Circle

private instance : LocPathConnectedSpace Circle := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 1)) Circle := inferInstance
  let _ : LocPathConnectedSpace (EuclideanSpace ℝ (Fin 1)) := inferInstance
  exact ChartedSpace.locPathConnectedSpace (EuclideanSpace ℝ (Fin 1)) Circle

end Circle

/- The map `x ↦ e^{2πix}` from `ℝ` to `S¹`, represented by `Real.fourierChar`, is a
path-connected covering map in the sense of Definition 3.1.5. -/
theorem real_fourierChar_isPathConnectedCoveringMap :
    IsPathConnectedCoveringMap Real.fourierChar := by
  have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by
    positivity
  have hsurjExp : Function.Surjective Circle.exp := by
    intro z
    rcases Circle.surjOn_exp_neg_pi_pi (by simp : z ∈ (Set.univ : Set Circle)) with ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  have hsurj : Function.Surjective Real.fourierChar := by
    simpa [Real.fourierChar_apply', Function.comp_def, smul_eq_mul] using
      hsurjExp.comp (Homeomorph.smulOfNeZero (2 * Real.pi) h2pi).surjective
  exact real_fourierChar_isCoveringMap.isPathConnectedCoveringMap hsurj

namespace Circle

/-- Example 3.1.7 (4): for `n ≠ 0`, the power map `z ↦ z ^ n` on `S¹` is a covering map. -/
-- Proof sketch: `Circle.isQuotientCoveringMap_npow n` gives the stronger quotient-covering
-- statement, and `IsQuotientCoveringMap.isCoveringMap` forgets the quotient-action data.
theorem isCoveringMap_npow (n : ℕ) (hn : n ≠ 0) :
    IsCoveringMap ((· ^ n) : Circle → Circle) := by
  letI : NeZero n := ⟨hn⟩
  exact (isQuotientCoveringMap_npow n).isCoveringMap

/-- Example 3.1.7 (4), source-facing form: for `n ≠ 0`, the power map `z ↦ z ^ n` on `S¹` is a
path-connected covering map in the sense of Definition 3.1.5. -/
theorem isPathConnectedCoveringMap_npow (n : ℕ) (hn : n ≠ 0) :
    IsPathConnectedCoveringMap ((· ^ n) : Circle → Circle) := by
  letI : NeZero n := ⟨hn⟩
  exact
      (isCoveringMap_npow n hn).isPathConnectedCoveringMap
      (isQuotientCoveringMap_npow n).surjective

end Circle

/-- Helper for Example 3.1.7: the internal subtype model of `S^n` as the unit sphere in
`ℝ^(n+1)`. -/
private abbrev SphereModel (n : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- Helper for Example 3.1.7: the textbook sphere `𝕊 n` is the `ULift` of the concrete sphere
model. -/
private abbrev sphereModelHomeomorph (n : ℕ) : 𝕊 n ≃ₜ SphereModel n := Homeomorph.ulift

/-- Helper for Example 3.1.7: the sphere model is Hausdorff. -/
private instance sphere_t2Space (n : ℕ) : T2Space (𝕊 n) :=
  (sphereModelHomeomorph n).symm.t2Space

/-- Helper for Example 3.1.7: the sphere model is locally compact. -/
private instance sphere_locallyCompactSpace (n : ℕ) : LocallyCompactSpace (𝕊 n) :=
  (sphereModelHomeomorph n).isOpenEmbedding.locallyCompactSpace

/-- Helper for Example 3.1.7: the antipodal map on `𝕊 n`. -/
private def sphereAntipode (n : ℕ) (x : 𝕊 n) : 𝕊 n :=
  ULift.up (-x.down)

/-- The antipodal map gives the canonical negation on `S^n`. -/
instance (n : ℕ) : Neg (𝕊 n) where
  neg := sphereAntipode n

/-- Helper for Example 3.1.7: points on the concrete unit sphere are nonzero. -/
private theorem sphereModel_ne_zero (n : ℕ) (x : SphereModel n) :
    x.1 ≠ (0 : EuclideanSpace ℝ (Fin (n + 1))) := by
  -- Read the subtype condition as the norm-one equation in the ambient Euclidean space.
  intro hx
  have hxnorm : ‖x.1‖ = 1 := by
    simpa [SphereModel, Metric.mem_sphere, dist_eq_norm] using x.2
  simp [hx] at hxnorm

/-- Helper for Example 3.1.7: the antipodal map has no fixed points on `S^n`. -/
private theorem sphereAntipode_ne_self (n : ℕ) (x : 𝕊 n) :
    sphereAntipode n x ≠ x := by
  -- Route correction: avoid the broken later owner and prove freeness of the antipodal action
  -- directly from the concrete sphere model.
  intro hx
  have hx' : -(x.down.1) = x.down.1 := by
    simpa [sphereAntipode] using
      congrArg (fun y : 𝕊 n ↦ y.down.1) hx
  have hsum : x.down.1 + x.down.1 = (0 : EuclideanSpace ℝ (Fin (n + 1))) := by
    calc
      x.down.1 + x.down.1 = -x.down.1 + x.down.1 := by
        simpa using congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦ z + x.down.1) hx'.symm
      _ = 0 := by simp
  have htwo : (2 : ℝ) • x.down.1 = (0 : EuclideanSpace ℝ (Fin (n + 1))) := by
    simpa [two_smul] using hsum
  have hx0 : x.down.1 = (0 : EuclideanSpace ℝ (Fin (n + 1))) :=
    (smul_eq_zero.mp htwo).resolve_left two_ne_zero
  exact sphereModel_ne_zero n x.down hx0

/-- The antipodal involution has no fixed points on `S^n`. -/
theorem sphere_neg_ne_self (n : ℕ) (x : 𝕊 n) : (-x : 𝕊 n) ≠ x :=
  sphereAntipode_ne_self n x

/-- Helper for Example 3.1.7: the antipodal map is an involution. -/
private theorem sphereAntipode_involutive (n : ℕ) (x : 𝕊 n) :
    sphereAntipode n (sphereAntipode n x) = x := by
  -- Unfold the `ULift` model of the sphere and compute.
  apply ULift.ext
  apply Subtype.ext
  simp [sphereAntipode]

/-- Helper for Example 3.1.7: the two-element symmetry group generated by the antipodal map. -/
private inductive AntipodalSymmetry where
  | one
  | neg
deriving DecidableEq, Fintype

/-- Helper for Example 3.1.7: `AntipodalSymmetry` has an identity element. -/
private instance : One AntipodalSymmetry := ⟨AntipodalSymmetry.one⟩

/-- Helper for Example 3.1.7: multiplying antipodal symmetries composes them. -/
private instance : Mul AntipodalSymmetry where
  mul g h :=
    match g, h with
    | .one, h => h
    | .neg, .one => .neg
    | .neg, .neg => .one

/-- Helper for Example 3.1.7: each antipodal symmetry is its own inverse. -/
private instance : Inv AntipodalSymmetry where
  inv g := g

/-- Helper for Example 3.1.7: the antipodal symmetries form a group. -/
private instance : Group AntipodalSymmetry where
  one_mul g := by cases g <;> rfl
  mul_one g := by cases g <;> rfl
  mul_assoc g h k := by cases g <;> cases h <;> cases k <;> rfl
  inv_mul_cancel g := by cases g <;> rfl

/-- Helper for Example 3.1.7: the antipodal symmetry group acts on `S^n`. -/
private def sphereAntipodalSMul (n : ℕ) (g : AntipodalSymmetry) (x : 𝕊 n) : 𝕊 n :=
  match g with
  | .one => x
  | .neg => sphereAntipode n x

/-- Helper for Example 3.1.7: `AntipodalSymmetry` acts on `S^n`. -/
private instance sphereAntipodalSMulInst (n : ℕ) : SMul AntipodalSymmetry (𝕊 n) where
  smul := sphereAntipodalSMul n

/-- Helper for Example 3.1.7: the antipodal symmetry action is a group action. -/
private instance sphereAntipodalMulAction (n : ℕ) : MulAction AntipodalSymmetry (𝕊 n) where
  one_smul x := by
    rfl
  mul_smul g h x := by
    -- There are only four group-element cases, and the nontrivial one uses involutivity.
    change sphereAntipodalSMul n (g * h) x =
      sphereAntipodalSMul n g (sphereAntipodalSMul n h x)
    cases g <;> cases h <;> simp [sphereAntipodalSMul, sphereAntipode_involutive]

/-- Helper for Example 3.1.7: each antipodal symmetry acts continuously on `S^n`. -/
private instance sphereAntipodalContinuousConstSMul (n : ℕ) :
    ContinuousConstSMul AntipodalSymmetry (𝕊 n) where
  continuous_const_smul g := by
    -- The only nontrivial action map is the continuous antipodal map.
    cases g
    · simpa [sphereAntipodalSMul] using
        (continuous_id : Continuous fun x : 𝕊 n ↦ x)
    · simpa [sphereAntipodalSMul, sphereAntipode] using
        (continuous_uliftUp.comp (continuous_neg.comp continuous_uliftDown) :
          Continuous fun x : 𝕊 n ↦ ULift.up (-x.down))

/-- Helper for Example 3.1.7: the antipodal action is free, hence cancellative. -/
private instance sphereAntipodalIsCancelSMul (n : ℕ) :
    IsCancelSMul AntipodalSymmetry (𝕊 n) where
  right_cancel' g h x hgh := by
    -- The only potentially nontrivial equalities would force a fixed point of the antipode.
    change sphereAntipodalSMul n g x = sphereAntipodalSMul n h x at hgh
    cases g <;> cases h
    · rfl
    · exfalso
      exact sphereAntipode_ne_self n x (by simpa [sphereAntipodalSMul] using hgh.symm)
    · exfalso
      exact sphereAntipode_ne_self n x (by simpa [sphereAntipodalSMul] using hgh)
    · rfl

/-- Helper for Example 3.1.7: quotient equality is exactly equality up to the antipodal map. -/
private theorem sphere_eq_or_neg_eq_iff_orbitRel (n : ℕ) {x y : 𝕊 n} :
    x = y ∨ x = -y ↔ MulAction.orbitRel AntipodalSymmetry (𝕊 n) x y := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · intro hxy
    rcases hxy with rfl | hxy
    · exact ⟨1, by simp⟩
    · exact ⟨AntipodalSymmetry.neg, by simpa [sphereAntipodalSMul] using hxy.symm⟩
  · rintro ⟨g, hg⟩
    cases g
    · exact Or.inl (by simpa using hg.symm)
    · exact Or.inr (by simpa [sphereAntipodalSMul] using hg.symm)

/-- Helper for Example 3.1.7: the quotient of `S^n` by the antipodal action, used as a model of
`RP^n`. -/
abbrev RealProjectiveSpace (n : ℕ) := MulAction.orbitRel.Quotient AntipodalSymmetry (𝕊 n)

/-- Helper for Example 3.1.7: the canonical quotient map from `S^n` to `RP^n`. -/
def sphereToRealProjectiveSpace (n : ℕ) : 𝕊 n → RealProjectiveSpace n :=
  Quotient.mk''

@[simp] theorem sphereToRealProjectiveSpace_eq_iff (n : ℕ) {x y : 𝕊 n} :
    sphereToRealProjectiveSpace n x = sphereToRealProjectiveSpace n y ↔ x = y ∨ x = -y := by
  change Quotient.mk'' x = (Quotient.mk'' y : MulAction.orbitRel.Quotient AntipodalSymmetry (𝕊 n)) ↔
    x = y ∨ x = -y
  rw [Quotient.eq'']
  exact (sphere_eq_or_neg_eq_iff_orbitRel n).symm

/- Example 3.1.7 (5): the antipodal quotient map `S^n → RP^n` is a covering map. -/
-- Proof sketch: express `RP^n` as the orbit quotient by the free antipodal action and apply the
-- general quotient-covering theorem for properly discontinuous actions.
theorem sphereToRealProjectiveSpace_isCoveringMap (n : ℕ) :
    IsCoveringMap (sphereToRealProjectiveSpace n) := by
  -- The quotient criterion applies once the sphere carries the free antipodal action data above.
  simpa [RealProjectiveSpace, sphereToRealProjectiveSpace] using
    ((isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
      (G := AntipodalSymmetry) (E := 𝕊 n)).isCoveringMap)

/-! ### Lemma_3_1_8 (from Chap03) -/
universe u v w

variable {E : Type u} {A : Type v} {B : Type w}
variable [TopologicalSpace E] [TopologicalSpace A] [TopologicalSpace B]

/-- The projection from a connected component of the pullback of `p` along `f` to the base `A`. -/
def pullbackComponentProj (p : E → B) (f : C(A, B))
    (D : ConnectedComponents (Function.Pullback p f)) :
    { x : Function.Pullback p f // ConnectedComponents.mk x = D } → A :=
  fun x ↦ Function.Pullback.snd x.1

/-- Helper for Lemma 3.1.8: the pullback projection to the base is continuous. -/
-- This is the ambient continuity fact used to build evenly covered neighborhoods for the
-- pullback projection.
private theorem continuous_pullback_snd {p : E → B} (f : C(A, B)) :
    Continuous (fun x : Function.Pullback p f ↦ x.1.2) := by
  fun_prop

/-- Helper for Lemma 3.1.8: an evenly covered neighborhood for `p` pulls back to an evenly covered
neighborhood for the pullback projection. -/
-- The homeomorphism over the pulled-back neighborhood is obtained by keeping the `A`-coordinate
-- and using the original trivialization on the `E`-coordinate.
theorem pullbackSnd_isEvenlyCovered {p : E → B} (f : C(A, B)) (a : A)
    (I := p ⁻¹' ({f a} : Set B)) [DiscreteTopology I] {V : Set B}
    (haV : f a ∈ V) (hV : IsOpen V) (H : p ⁻¹' V ≃ₜ V × I)
    (hH : ∀ e, (H e).1.1 = p e) :
    IsEvenlyCovered (fun x : Function.Pullback p f ↦ x.1.2) a I := by
  have hU : IsOpen (f ⁻¹' V) := hV.preimage f.continuous
  have hqU : IsOpen ((fun x : Function.Pullback p f ↦ x.1.2) ⁻¹' (f ⁻¹' V)) := by
    simpa using hU.preimage (continuous_pullback_snd f)
  let toFun :
      ((fun x : Function.Pullback p f ↦ x.1.2) ⁻¹' (f ⁻¹' V)) →
        (f ⁻¹' V) × I :=
    fun x ↦
      let hxV : p x.1.1.1 ∈ V := by
        have hxU : f x.1.1.2 ∈ V := x.2
        simpa [x.1.2] using hxU
      (⟨x.1.1.2, x.2⟩, (H ⟨x.1.1.1, hxV⟩).2)
  let invBase : (f ⁻¹' V) × I → Function.Pullback p f :=
    fun y ↦
      let z : p ⁻¹' V := H.symm (⟨f y.1.1, y.1.2⟩, y.2)
      let hz : p z.1 = f y.1.1 := by
        have hzH : H z = (⟨f y.1.1, y.1.2⟩, y.2) := H.apply_symm_apply _
        simpa [hzH] using (hH z).symm
      ⟨(z.1, y.1.1), hz⟩
  have hInvMem :
      ∀ y : (f ⁻¹' V) × I,
        invBase y ∈ (fun x : Function.Pullback p f ↦ x.1.2) ⁻¹' (f ⁻¹' V) := by
    intro y
    simp [invBase]
  let invFun :
      (f ⁻¹' V) × I →
        ((fun x : Function.Pullback p f ↦ x.1.2) ⁻¹' (f ⁻¹' V)) :=
    fun y ↦ ⟨invBase y, hInvMem y⟩
  have hLeft : Function.LeftInverse invFun toFun := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    let z : p ⁻¹' V := by
      have hxV : p x.1.1.1 ∈ V := by
        have hxU : f x.1.1.2 ∈ V := x.2
        simpa [x.1.2] using hxU
      exact ⟨x.1.1.1, hxV⟩
    have hzfst : (⟨f x.1.1.2, x.2⟩ : V) = (H z).1 := by
      apply Subtype.ext
      simpa [z, hH z] using x.1.2.symm
    have hzsymm : H.symm (⟨f x.1.1.2, x.2⟩, (H z).2) = z := by
      have hpair : (⟨f x.1.1.2, x.2⟩, (H z).2) = H z := Prod.ext hzfst rfl
      simp [hpair, z]
    ext <;> simp [toFun, invFun, invBase, z, hzsymm]
  have hRight : Function.RightInverse invFun toFun := by
    intro y
    simp [toFun, invFun, invBase]
  let e :
      ((fun x : Function.Pullback p f ↦ x.1.2) ⁻¹' (f ⁻¹' V)) ≃ₜ
        (f ⁻¹' V) × I :=
    { toFun := toFun
      invFun := invFun
      left_inv := hLeft
      right_inv := hRight
      continuous_toFun := by
        dsimp [toFun]
        fun_prop
      continuous_invFun := by
        refine Continuous.subtype_mk ?_ hInvMem
        dsimp [invBase]
        fun_prop }
  refine ⟨inferInstance, f ⁻¹' V, haV, hU, hqU, e, ?_⟩
  intro x
  rfl

/-- Helper for Lemma 3.1.8: the projection from the full pullback to `A` is surjective. -/
-- Surjectivity is immediate because `p` is surjective and the pullback condition only asks for a
-- point of the fiber of `p` over `f a`.
theorem pullbackSnd_surjective {p : E → B} (hp : IsPathConnectedCoveringMap p) (f : C(A, B)) :
    Function.Surjective (fun x : Function.Pullback p f ↦ x.1.2) := by
  intro a
  rcases hp.surjective (f a) with ⟨e, he⟩
  exact ⟨⟨(e, a), he⟩, rfl⟩

/-- Helper for Lemma 3.1.8: the projection from the full pullback to `A` is a covering map. -/
-- Each evenly covered neighborhood for `p` over `f a` pulls back to an evenly covered
-- neighborhood for the pullback projection over `a`, and then the fiber is identified with the
-- actual pullback fiber over `a`.
theorem pullbackSnd_isCoveringMap {p : E → B} (hp : IsPathConnectedCoveringMap p)
    (f : C(A, B)) : IsCoveringMap (fun x : Function.Pullback p f ↦ x.1.2) := by
  intro a
  rcases hp.2 (f a) with ⟨_hdisc, V, haV, hV, _hVPath, _hpV, H, hH⟩
  let toFiber :
      ((fun x : Function.Pullback p f ↦ x.1.2) ⁻¹' ({a} : Set A)) →
        (p ⁻¹' ({f a} : Set B)) :=
    fun x ↦
      let hxa : x.1.1.2 = a := Set.mem_singleton_iff.mp x.2
      ⟨x.1.1.1, by simpa [hxa] using x.1.2⟩
  let fromFiberBase : (p ⁻¹' ({f a} : Set B)) → Function.Pullback p f :=
    fun y ↦
      let hy : p y.1 = f a := Set.mem_singleton_iff.mp y.2
      ⟨(y.1, a), hy⟩
  have hFromFiberMem :
      ∀ y : p ⁻¹' ({f a} : Set B),
        fromFiberBase y ∈ (fun x : Function.Pullback p f ↦ x.1.2) ⁻¹' ({a} : Set A) := by
    intro y
    simp [fromFiberBase]
  let fromFiber :
      (p ⁻¹' ({f a} : Set B)) →
        ((fun x : Function.Pullback p f ↦ x.1.2) ⁻¹' ({a} : Set A)) :=
    fun y ↦ ⟨fromFiberBase y, hFromFiberMem y⟩
  have hLeftFiber : Function.LeftInverse fromFiber toFiber := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    have hxa : x.1.1.2 = a := Set.mem_singleton_iff.mp x.2
    ext <;> simp [toFiber, fromFiber, fromFiberBase, hxa]
  have hRightFiber : Function.RightInverse fromFiber toFiber := by
    intro y
    apply Subtype.ext
    simp [toFiber, fromFiber, fromFiberBase]
  let hFiber :
      ((fun x : Function.Pullback p f ↦ x.1.2) ⁻¹' ({a} : Set A)) ≃ₜ
        (p ⁻¹' ({f a} : Set B)) :=
    { toFun := toFiber
      invFun := fromFiber
      left_inv := hLeftFiber
      right_inv := hRightFiber
      continuous_toFun := by
        dsimp [toFiber]
        fun_prop
      continuous_invFun := by
        refine Continuous.subtype_mk ?_ hFromFiberMem
        dsimp [fromFiberBase]
        fun_prop }
  exact (pullbackSnd_isEvenlyCovered (f := f) (a := a) (I := p ⁻¹' ({f a} : Set B))
      haV hV H hH).of_fiber_homeomorph
    hFiber.symm

/-- Helper for Lemma 3.1.8: the full pullback projection is a path-connected covering map. -/
-- Once the pullback projection is known to be a covering map, Example 3.1.7 upgrades it to the
-- path-connected covering-map notion because the base `A` is locally path connected.
theorem pullbackSnd_isPathConnectedCoveringMap [LocPathConnectedSpace A]
    {p : E → B} (hp : IsPathConnectedCoveringMap p) (f : C(A, B)) :
    IsPathConnectedCoveringMap (fun x : Function.Pullback p f ↦ x.1.2) :=
  (pullbackSnd_isCoveringMap hp f).isPathConnectedCoveringMap (pullbackSnd_surjective hp f)

/-- Helper for Lemma 3.1.8: the connected-component label is constant along one local sheet. -/
-- A local sheet is the image of a path-connected open set under a continuous section, so its image
-- in `ConnectedComponents X` is forced to be constant.
theorem component_constant_on_sheet {X : Type*} [TopologicalSpace X] {q : X → A} {U : Set A}
    {I : Type*} [TopologicalSpace I] (hUPath : IsPathConnected U) (H : q ⁻¹' U ≃ₜ U × I)
    (i : I) (u₀ u : U) :
    ConnectedComponents.mk ((H.symm (u₀, i)).1) = ConnectedComponents.mk ((H.symm (u, i)).1) := by
  let c : C(U, ConnectedComponents X) :=
    ⟨fun u ↦ ConnectedComponents.mk ((H.symm (u, i)).1), by
      refine ConnectedComponents.continuous_coe.comp ?_
      have hpair : Continuous fun u : U ↦ (u, i) := by
        fun_prop
      exact continuous_subtype_val.comp (H.symm.continuous.comp hpair)⟩
  have hConnected : IsConnected U := hUPath.isConnected
  letI : ConnectedSpace U := (isConnected_iff_connectedSpace).mp hConnected
  have hsubset := c.continuous.image_connectedComponent_subset u₀
  have hu : c u ∈ c '' connectedComponent u₀ := by
    rw [PreconnectedSpace.connectedComponent_eq_univ u₀]
    exact ⟨u, by simp, rfl⟩
  have hmem : c u ∈ connectedComponent (c u₀) := hsubset hu
  have hEq : c u = c u₀ := by
    simpa [c, connectedComponent_eq_singleton (c u₀)] using hmem
  exact hEq.symm

/-- Helper for Lemma 3.1.8: belonging to the chosen connected component is constant along a single
local sheet, so it can be checked at the basepoint of the trivialization. -/
-- This rewrites the component predicate on `U × (q ⁻¹' {a})` into one depending only on the
-- sheet index.
theorem sheet_component_iff_at_basepoint {X : Type*} [TopologicalSpace X] {q : X → A}
    {U : Set A} {a : A} (D : ConnectedComponents X) (haU : a ∈ U)
    (hUPath : IsPathConnected U) (H : q ⁻¹' U ≃ₜ U × (q ⁻¹' ({a} : Set A)))
    (u : U) (i : q ⁻¹' ({a} : Set A)) :
    ConnectedComponents.mk ((H.symm (u, i)).1) = D ↔
      ConnectedComponents.mk ((H.symm (⟨a, haU⟩, i)).1) = D := by
  -- The component label does not change as we move in the same local sheet.
  have hsheet :
      ConnectedComponents.mk ((H.symm (⟨a, haU⟩, i)).1) =
        ConnectedComponents.mk ((H.symm (u, i)).1) :=
    component_constant_on_sheet hUPath H i ⟨a, haU⟩ u
  simpa [hsheet]

/-- Helper for Lemma 3.1.8: restricting a local trivialization of the full pullback to one
connected component yields a product trivialization over that component. -/
-- The only extra bookkeeping is that the allowed sheets are exactly the ones whose basepoint lies
-- in the chosen connected component.
theorem component_restricted_preimage_homeomorph {X : Type*} [TopologicalSpace X] {q : X → A}
    {U : Set A} {a : A} (D : ConnectedComponents X) (haU : a ∈ U)
    (hUPath : IsPathConnected U) (H : q ⁻¹' U ≃ₜ U × (q ⁻¹' ({a} : Set A)))
    (hH : ∀ x, (H x).1.1 = q x) :
    ∃ h :
        { x : { y : X // ConnectedComponents.mk y = D } // q x.1 ∈ U } ≃ₜ
          U × { i : q ⁻¹' ({a} : Set A) //
            ConnectedComponents.mk ((H.symm (⟨a, haU⟩, i)).1) = D },
      ∀ x, (h x).1.1 = q x.1 := by
  let e₀ :
      { x : { y : X // ConnectedComponents.mk y = D } // q x.1 ∈ U } ≃ₜ
        { x : q ⁻¹' U // ConnectedComponents.mk x.1 = D } :=
    { toFun := fun x ↦ ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      invFun := fun x ↦ ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      left_inv := by
        intro x
        cases x
        rfl
      right_inv := by
        intro x
        cases x
        rfl
      continuous_toFun := by
        fun_prop
      continuous_invFun := by
        fun_prop }
  let e₁ :
      { x : q ⁻¹' U // ConnectedComponents.mk x.1 = D } ≃ₜ
        { y : U × (q ⁻¹' ({a} : Set A)) //
          ConnectedComponents.mk ((H.symm y).1) = D } :=
    H.subtype fun x => by
      simp
  let e₂ :
      { y : U × (q ⁻¹' ({a} : Set A)) //
          ConnectedComponents.mk ((H.symm y).1) = D } ≃ₜ
        U × { i : q ⁻¹' ({a} : Set A) //
          ConnectedComponents.mk ((H.symm (⟨a, haU⟩, i)).1) = D } :=
    { toFun := fun y ↦
        ⟨y.1.1, ⟨y.1.2,
          (sheet_component_iff_at_basepoint (D := D) haU hUPath H y.1.1 y.1.2).mp y.2⟩⟩
      invFun := fun y ↦
        ⟨(y.1, y.2.1),
          (sheet_component_iff_at_basepoint (D := D) haU hUPath H y.1 y.2.1).mpr y.2.2⟩
      left_inv := by
        intro y
        cases y
        rfl
      right_inv := by
        intro y
        cases y
        rfl
      continuous_toFun := by
        fun_prop
      continuous_invFun := by
        fun_prop }
  -- First reassociate the nested subtype, then restrict `H`, then rewrite the predicate so it
  -- depends only on the sheet index.
  refine ⟨e₀.trans (e₁.trans e₂), ?_⟩
  intro x
  simpa [e₀, e₁, e₂] using hH ⟨x.1.1, x.2⟩

/-- Helper for Lemma 3.1.8: the allowed sheet indices in the restricted trivialization are
homeomorphic to the actual fiber of the component projection over the basepoint. -/
-- Evaluating a chosen sheet at the basepoint gives the desired fiber point, and the inverse reads
-- off the sheet index from the ambient trivialization.
theorem sheet_index_homeomorph_component_fiber {X : Type*} [TopologicalSpace X] {q : X → A}
    {U : Set A} {a : A} (D : ConnectedComponents X) (haU : a ∈ U)
    (hUPath : IsPathConnected U) (H : q ⁻¹' U ≃ₜ U × (q ⁻¹' ({a} : Set A)))
    (hH : ∀ x, (H x).1.1 = q x) :
    Nonempty (
      { i : q ⁻¹' ({a} : Set A) //
          ConnectedComponents.mk ((H.symm (⟨a, haU⟩, i)).1) = D } ≃ₜ
        { x : { y : X // ConnectedComponents.mk y = D } // q x.1 ∈ ({a} : Set A) }) := by
  let toFun :
      { i : q ⁻¹' ({a} : Set A) //
          ConnectedComponents.mk ((H.symm (⟨a, haU⟩, i)).1) = D } →
        { x : { y : X // ConnectedComponents.mk y = D } // q x.1 ∈ ({a} : Set A) } :=
    fun i ↦
      let x : X := (H.symm (⟨a, haU⟩, i.1)).1
      have hxD : ConnectedComponents.mk x = D := i.2
      have hqa : q x ∈ ({a} : Set A) := by
        have hqa' : ((H (H.symm (⟨a, haU⟩, i.1)))).1.1 = a := by
          simpa using congrArg (fun y : U × (q ⁻¹' ({a} : Set A)) => y.1.1)
            (H.apply_symm_apply (⟨a, haU⟩, i.1))
        simpa [x] using (hH (H.symm (⟨a, haU⟩, i.1))).symm.trans hqa'
      ⟨⟨x, hxD⟩, hqa⟩
  let invFun :
      { x : { y : X // ConnectedComponents.mk y = D } // q x.1 ∈ ({a} : Set A) } →
        { i : q ⁻¹' ({a} : Set A) //
          ConnectedComponents.mk ((H.symm (⟨a, haU⟩, i)).1) = D } :=
    fun x ↦
      let hxa : q x.1.1 = a := Set.mem_singleton_iff.mp x.2
      let hxU : q x.1.1 ∈ U := by
        simpa [hxa] using haU
      let i : q ⁻¹' ({a} : Set A) := (H ⟨x.1.1, hxU⟩).2
      have hxSheet :
          ConnectedComponents.mk ((H.symm ((H ⟨x.1.1, hxU⟩).1, i)).1) = D := by
        have hxBack : H.symm ((H ⟨x.1.1, hxU⟩).1, i) = ⟨x.1.1, hxU⟩ := by
          simp [i]
        simpa [hxBack] using x.1.2
      ⟨i,
        (sheet_component_iff_at_basepoint (D := D) haU hUPath H (H ⟨x.1.1, hxU⟩).1 i).mp
          hxSheet⟩
  have hLeft : Function.LeftInverse invFun toFun := by
    intro i
    apply Subtype.ext
    have hsecond :
        (H ⟨(H.symm (⟨a, haU⟩, i.1)).1, by
          have hqa' : ((H (H.symm (⟨a, haU⟩, i.1)))).1.1 = a := by
            simpa using congrArg (fun y : U × (q ⁻¹' ({a} : Set A)) => y.1.1)
              (H.apply_symm_apply (⟨a, haU⟩, i.1))
          simpa using (hH (H.symm (⟨a, haU⟩, i.1))).symm.trans hqa'⟩).2 = i.1 := by
      simpa using congrArg Prod.snd (H.apply_symm_apply (⟨a, haU⟩, i.1))
    simpa [toFun, invFun, hsecond]
  have hRight : Function.RightInverse invFun toFun := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    let hxa : q x.1.1 = a := Set.mem_singleton_iff.mp x.2
    let hxU : q x.1.1 ∈ U := by
      simpa [hxa] using haU
    let i : q ⁻¹' ({a} : Set A) := (H ⟨x.1.1, hxU⟩).2
    have hfst : (H ⟨x.1.1, hxU⟩).1 = ⟨a, haU⟩ := by
      apply Subtype.ext
      simpa [hxa] using hH ⟨x.1.1, hxU⟩
    have hxBack :
        H.symm (⟨a, haU⟩, i) = ⟨x.1.1, hxU⟩ := by
      rw [← hfst]
      simp [i]
    simpa [toFun, invFun, hxa, hxU, i, hxBack]
  -- The two maps are continuous because they are assembled from `H` and subtype projections.
  refine ⟨{
      toFun := toFun
      invFun := invFun
      left_inv := hLeft
      right_inv := hRight
      continuous_toFun := by
        have hpair : Continuous fun i :
            { i : q ⁻¹' ({a} : Set A) //
              ConnectedComponents.mk ((H.symm (⟨a, haU⟩, i)).1) = D } =>
            ((⟨a, haU⟩, i.1) : U × (q ⁻¹' ({a} : Set A))) := by
          fun_prop
        have hBase :
            Continuous fun i :
                { i : q ⁻¹' ({a} : Set A) //
                  ConnectedComponents.mk ((H.symm (⟨a, haU⟩, i)).1) = D } =>
              (H.symm (⟨a, haU⟩, i.1)).1 := by
          simpa using continuous_subtype_val.comp (H.symm.continuous.comp hpair)
        have hSub :
            Continuous fun i :
                { i : q ⁻¹' ({a} : Set A) //
                  ConnectedComponents.mk ((H.symm (⟨a, haU⟩, i)).1) = D } =>
              (⟨(H.symm (⟨a, haU⟩, i.1)).1, i.2⟩ :
                { y : X // ConnectedComponents.mk y = D }) := by
          exact Continuous.subtype_mk hBase (fun i ↦ i.2)
        exact Continuous.subtype_mk hSub fun i ↦ by
          have hqa' : ((H (H.symm (⟨a, haU⟩, i.1)))).1.1 = a := by
            simp
          simpa [toFun] using (hH (H.symm (⟨a, haU⟩, i.1))).symm.trans hqa'
      continuous_invFun := by
        have hxU :
            ∀ x : { x : { y : X // ConnectedComponents.mk y = D } // q x.1 ∈ ({a} : Set A) },
              q x.1.1 ∈ U := by
          intro x
          have hxa : q x.1.1 = a := Set.mem_singleton_iff.mp x.2
          simpa [hxa] using haU
        have hBase :
            Continuous fun x :
                { x : { y : X // ConnectedComponents.mk y = D } // q x.1 ∈ ({a} : Set A) } =>
              x.1.1 := by
          exact continuous_subtype_val.comp continuous_subtype_val
        have hLift :
            Continuous fun x :
                { x : { y : X // ConnectedComponents.mk y = D } // q x.1 ∈ ({a} : Set A) } =>
              (⟨x.1.1, hxU x⟩ : q ⁻¹' U) := by
          exact Continuous.subtype_mk hBase hxU
        have hSecond :
            Continuous fun x :
                { x : { y : X // ConnectedComponents.mk y = D } // q x.1 ∈ ({a} : Set A) } =>
              (H ⟨x.1.1, hxU x⟩).2 := by
          have hComp : Continuous fun x :
              { x : { y : X // ConnectedComponents.mk y = D } // q x.1 ∈ ({a} : Set A) } =>
              H ⟨x.1.1, hxU x⟩ := H.continuous.comp hLift
          exact continuous_snd.comp hComp
        exact Continuous.subtype_mk hSecond fun x ↦ by
          let hxa : q x.1.1 = a := Set.mem_singleton_iff.mp x.2
          let hxU : q x.1.1 ∈ U := by
            simpa [hxa] using haU
          let i : q ⁻¹' ({a} : Set A) := (H ⟨x.1.1, hxU⟩).2
          have hxSheet :
              ConnectedComponents.mk ((H.symm ((H ⟨x.1.1, hxU⟩).1, i)).1) = D := by
            have hxBack : H.symm ((H ⟨x.1.1, hxU⟩).1, i) = ⟨x.1.1, hxU⟩ := by
              simp [i]
            simpa [hxBack] using x.1.2
          simpa [invFun, hxa, hxU, i] using
            (sheet_component_iff_at_basepoint (D := D) haU hUPath H (H ⟨x.1.1, hxU⟩).1 i).mp
              hxSheet }⟩

/-- Lemma 3.1.8: if `D` is a connected component of the pullback of a cover `p : E → B` along a
continuous map `f : A → B`, then the projection `D → A` is again a cover. -/
-- Proof sketch: pull back the path-connected evenly covered neighborhoods supplied by `hp` along
-- `f`, obtaining a covering projection from the full pullback to `A`. Then restrict that
-- projection to the connected component `D`; in the connected locally path-connected base `A`, the
-- image of `D` is clopen, hence all of `A`, and the restricted projection is again a
-- path-connected covering map.
theorem pullbackComponentProj_isPathConnectedCoveringMap [ConnectedSpace A]
    [LocPathConnectedSpace A]
    {p : E → B} (hp : IsPathConnectedCoveringMap p) (f : C(A, B))
    (D : ConnectedComponents (Function.Pullback p f)) :
    IsPathConnectedCoveringMap (pullbackComponentProj p f D) := by
  let q : Function.Pullback p f → A := fun x ↦ x.1.2
  let s : Set A := Set.range (pullbackComponentProj p f D)
  have hq : IsPathConnectedCoveringMap q := pullbackSnd_isPathConnectedCoveringMap hp f
  have hsClopen : IsClopen s := by
    have hsComplOpen : IsOpen sᶜ := by
      rw [isOpen_iff_mem_nhds]
      intro a ha
      rcases hq.2 a with ⟨_hdisc, U, haU, hU, hUPath, _hqU, H, hH⟩
      refine mem_nhds_iff.mpr ⟨U, ?_, hU, haU⟩
      intro b hbU hbRange
      rcases hbRange with ⟨x, rfl⟩
      have hxU : x.1 ∈ q ⁻¹' U := by
        simpa [pullbackComponentProj, q] using hbU
      let i := (H ⟨x.1, hxU⟩).2
      have hsheet :
          ConnectedComponents.mk ((H.symm (⟨a, haU⟩, i)).1) =
            ConnectedComponents.mk ((H.symm ((H ⟨x.1, hxU⟩).1, i)).1) :=
        component_constant_on_sheet hUPath H i ⟨a, haU⟩ (H ⟨x.1, hxU⟩).1
      have hxD :
          ConnectedComponents.mk ((H.symm ((H ⟨x.1, hxU⟩).1, i)).1) = D := by
        have hxBack : H.symm ((H ⟨x.1, hxU⟩).1, i) = ⟨x.1, hxU⟩ := by
          simp [i]
        simpa [hxBack] using x.2
      have haRange : a ∈ s := by
        refine ⟨⟨(H.symm (⟨a, haU⟩, i)).1, ?_⟩, ?_⟩
        · exact hsheet.trans hxD
        · have hfst :
              (H (H.symm (⟨a, haU⟩, i))).1 = ⟨a, haU⟩ := by
            simpa using congrArg Prod.fst (H.apply_symm_apply (⟨a, haU⟩, i))
          have hqa : q ((H.symm (⟨a, haU⟩, i)).1) = a := by
            have hqa' : ((H (H.symm (⟨a, haU⟩, i)))).1.1 = a := by
              simpa using congrArg (fun y : U × (q ⁻¹' ({a} : Set A)) => y.1.1)
                (H.apply_symm_apply (⟨a, haU⟩, i))
            simpa [q] using (hH (H.symm (⟨a, haU⟩, i))).symm.trans hqa'
          simpa [s, pullbackComponentProj, q] using hqa
      exact ha haRange
    have hsOpen : IsOpen s := by
      rw [isOpen_iff_mem_nhds]
      intro a ha
      rcases ha with ⟨x, rfl⟩
      rcases hq.2 (pullbackComponentProj p f D x) with ⟨_hdisc, U, haU, hU, hUPath, _hqU, H, hH⟩
      refine mem_nhds_iff.mpr ⟨U, ?_, hU, haU⟩
      intro b hbU
      let i := (H ⟨x.1, by simpa [pullbackComponentProj, q] using haU⟩).2
      have hsheet :
          ConnectedComponents.mk ((H.symm (⟨b, hbU⟩, i)).1) =
            ConnectedComponents.mk ((H.symm ((H ⟨x.1, by simpa [pullbackComponentProj, q] using haU⟩).1,
              i)).1) :=
        component_constant_on_sheet hUPath H i ⟨b, hbU⟩
          (H ⟨x.1, by simpa [pullbackComponentProj, q] using haU⟩).1
      have hxD :
          ConnectedComponents.mk
              ((H.symm ((H ⟨x.1, by simpa [pullbackComponentProj, q] using haU⟩).1, i)).1) = D := by
        have hxBack :
            H.symm ((H ⟨x.1, by simpa [pullbackComponentProj, q] using haU⟩).1, i) =
              ⟨x.1, by simpa [pullbackComponentProj, q] using haU⟩ := by
          simp [i]
        simpa [hxBack] using x.2
      refine ⟨⟨(H.symm (⟨b, hbU⟩, i)).1, hsheet.trans hxD⟩, ?_⟩
      have hfst :
          (H (H.symm (⟨b, hbU⟩, i))).1 = ⟨b, hbU⟩ := by
        simpa using congrArg Prod.fst (H.apply_symm_apply (⟨b, hbU⟩, i))
      have hqb : q ((H.symm (⟨b, hbU⟩, i)).1) = b := by
        have hqb' : ((H (H.symm (⟨b, hbU⟩, i)))).1.1 = b := by
          simpa using congrArg (fun y : U × (q ⁻¹' ({pullbackComponentProj p f D x} : Set A)) =>
            y.1.1) (H.apply_symm_apply (⟨b, hbU⟩, i))
        simpa [q] using (hH (H.symm (⟨b, hbU⟩, i))).symm.trans hqb'
      simpa [s, pullbackComponentProj, q] using hqb
    exact ⟨isOpen_compl_iff.mp hsComplOpen, hsOpen⟩
  have hsNonempty : s.Nonempty := by
    rcases ConnectedComponents.surjective_coe D with ⟨x, hxD⟩
    refine ⟨pullbackComponentProj p f D ⟨x, hxD⟩, ?_⟩
    exact ⟨⟨x, hxD⟩, rfl⟩
  have hsUniv : s = Set.univ := hsClopen.eq_univ hsNonempty
  have hsurj : Function.Surjective (pullbackComponentProj p f D) := by
    intro a
    have ha : a ∈ s := by simpa [hsUniv]
    simpa [s] using ha
  have hcov : IsCoveringMap (pullbackComponentProj p f D) := by
    intro a
    rcases hq.2 a with ⟨_hdisc, U, haU, hU, hUPath, _hqU, H, hH⟩
    let T :=
      { i : q ⁻¹' ({a} : Set A) //
        ConnectedComponents.mk ((H.symm (⟨a, haU⟩, i)).1) = D }
    rcases component_restricted_preimage_homeomorph (D := D) haU hUPath H hH with
      ⟨Hcomp, hHcomp⟩
    classical
    let hFiber :=
      Classical.choice (sheet_index_homeomorph_component_fiber (D := D) haU hUPath H hH)
    -- The local model is the restricted trivialization of the full pullback over `U`.
    have hEvenlyCoveredT : IsEvenlyCovered (pullbackComponentProj p f D) a T := by
      refine ⟨inferInstance, U, haU, hU, ?_, ?_, ?_⟩
      · have hproj : Continuous (pullbackComponentProj p f D) := by
          simpa [pullbackComponentProj, q] using
            (continuous_pullback_snd f).comp continuous_subtype_val
        simpa using hU.preimage hproj
      · simpa [T, pullbackComponentProj, q] using Hcomp
      · intro x
        simpa [pullbackComponentProj, q, T] using hHcomp x
    -- The restricted sheet index set is homeomorphic to the actual fiber over `a`.
    have hFiber' :
        T ≃ₜ (pullbackComponentProj p f D ⁻¹' ({a} : Set A)) := by
      simpa [T, pullbackComponentProj, q] using hFiber
    exact hEvenlyCoveredT.of_fiber_homeomorph hFiber'
  exact hcov.isPathConnectedCoveringMap hsurj

/-- The projection from a connected component of the pullback of a cover is a covering map in the
mathlib sense. -/
-- Proof sketch: apply `IsPathConnectedCoveringMap.isCoveringMap` to
-- `pullbackComponentProj_isPathConnectedCoveringMap`.
theorem pullbackComponentProj_isCoveringMap [ConnectedSpace A] [LocPathConnectedSpace A]
    {p : E → B} (hp : IsPathConnectedCoveringMap p) (f : C(A, B))
    (D : ConnectedComponents (Function.Pullback p f)) :
    IsCoveringMap (pullbackComponentProj p f D) := by
  -- Once the component projection is known to be path-connected covering, the ordinary covering
  -- map statement is just the forgetful direction from Definition 3.1.5.
  exact (pullbackComponentProj_isPathConnectedCoveringMap hp f D).isCoveringMap
