module

public import Topology_Munkres_2000.Book.Lemma_55_1.Inclusions
public import Topology_Munkres_2000.Book.Theorem_51_3
import all Topology_Munkres_2000.Book.Lemma_55_1.Inclusions

public section

universe u

/-- Helper for Theorem 59.1: a path whose range lies in `S` lifts continuously to `S`. -/
private lemma continuous_loopRangeLift {X : Type u} [TopologicalSpace X]
    {S : Set X} {x₀ : X} (γ : Path x₀ x₀) (hγ : Set.range γ ⊆ S) :
    Continuous (fun t ↦ (⟨γ t, hγ (Set.mem_range_self t)⟩ : S)) := by
  -- Continuity into a subtype follows from continuity of the underlying loop.
  exact γ.continuous.subtype_mk _

/-- Helper for Theorem 59.1: the lifted loop has the prescribed source. -/
private lemma loopRangeLift_source {X : Type u} [TopologicalSpace X]
    {S : Set X} {x₀ : X} (hx₀ : x₀ ∈ S) (γ : Path x₀ x₀)
    (hγ : Set.range γ ⊆ S) :
    (⟨γ 0, hγ (Set.mem_range_self 0)⟩ : S) = ⟨x₀, hx₀⟩ := by
  -- Subtype extensionality reduces the endpoint claim to the source equation of `γ`.
  exact Subtype.ext γ.source

/-- Helper for Theorem 59.1: the lifted loop has the prescribed target. -/
private lemma loopRangeLift_target {X : Type u} [TopologicalSpace X]
    {S : Set X} {x₀ : X} (hx₀ : x₀ ∈ S) (γ : Path x₀ x₀)
    (hγ : Set.range γ ⊆ S) :
    (⟨γ 1, hγ (Set.mem_range_self 1)⟩ : S) = ⟨x₀, hx₀⟩ := by
  -- Subtype extensionality reduces the endpoint claim to the target equation of `γ`.
  exact Subtype.ext γ.target

/-- Helper for Theorem 59.1: a loop with range in `S`, regarded as a loop in `S`. -/
private def loopRangeLift {X : Type u} [TopologicalSpace X]
    {S : Set X} {x₀ : X} (hx₀ : x₀ ∈ S) (γ : Path x₀ x₀)
    (hγ : Set.range γ ⊆ S) : Path (⟨x₀, hx₀⟩ : S) ⟨x₀, hx₀⟩ :=
  { toFun := fun t ↦ ⟨γ t, hγ (Set.mem_range_self t)⟩
    continuous_toFun := continuous_loopRangeLift γ hγ
    source' := loopRangeLift_source hx₀ γ hγ
    target' := loopRangeLift_target hx₀ γ hγ }

/-- Helper for Theorem 59.1: forgetting the subtype from `loopRangeLift` recovers the loop. -/
private lemma loopRangeLift_map_subtypeVal {X : Type u} [TopologicalSpace X]
    {S : Set X} {x₀ : X} (hx₀ : x₀ ∈ S) (γ : Path x₀ x₀)
    (hγ : Set.range γ ⊆ S) :
    (loopRangeLift hx₀ γ hγ).map continuous_subtype_val = γ := by
  -- Both paths have the same value at every parameter.
  ext t
  rfl

/-- Helper for Theorem 59.1: `mapOfSubtype` is the map induced by subtype coercion. -/
private lemma mapOfSubtype_eq_map_subtypeVal {X : Type u} [TopologicalSpace X]
    (S : Set X) (x₀ : S) :
    FundamentalGroup.mapOfSubtype S x₀ =
      FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(S, X)) x₀ := by
  -- This is the defining continuous map of the inclusion-induced homomorphism.
  rfl

/-- Helper for Theorem 59.1: a loop contained in `S` represents an element in the
range of the inclusion-induced map from `S`. -/
private lemma loopClassMemMapOfSubtypeRange {X : Type u} [TopologicalSpace X]
    {S : Set X} {x₀ : X} (hx₀ : x₀ ∈ S) (γ : Path x₀ x₀)
    (hγ : Set.range γ ⊆ S) :
    (Path.Homotopic.Quotient.mk γ : FundamentalGroup X x₀) ∈
      MonoidHom.range (FundamentalGroup.mapOfSubtype S ⟨x₀, hx₀⟩) := by
  -- Use the subtype-valued lift as a concrete preimage of the ambient loop class.
  refine ⟨Path.Homotopic.Quotient.mk (loopRangeLift hx₀ γ hγ), ?_⟩
  rw [mapOfSubtype_eq_map_subtypeVal, FundamentalGroup.map_apply,
    ← Path.Homotopic.Quotient.mk_map,
    loopRangeLift_map_subtypeVal]

/-- Helper for Theorem 59.1: concatenating two paths contained in `S` remains in `S`. -/
private lemma pathTrans_range_subset {X : Type u} [TopologicalSpace X]
    {S : Set X} {a b c : X} (γ : Path a b) (δ : Path b c)
    (hγ : Set.range γ ⊆ S) (hδ : Set.range δ ⊆ S) :
    Set.range (γ.trans δ) ⊆ S := by
  -- The range of a concatenation is the union of the two ranges.
  rw [Path.trans_range]
  exact Set.union_subset hγ hδ

/-- Helper for Theorem 59.1: reversing a path preserves every range containment. -/
private lemma pathSymm_range_subset {X : Type u} [TopologicalSpace X]
    {S : Set X} {a b : X} (γ : Path a b) (hγ : Set.range γ ⊆ S) :
    Set.range γ.symm ⊆ S := by
  -- Path reversal does not alter the range.
  rwa [Path.symm_range]

/-- Helper for Theorem 59.1: changing only the endpoint types of a path preserves
its range containment. -/
private lemma pathCast_range_subset {X : Type u} [TopologicalSpace X]
    {S : Set X} {a b a' b' : X} (γ : Path a b)
    (ha : a' = a) (hb : b' = b) (hγ : Set.range γ ⊆ S) :
    Set.range (γ.cast ha hb) ⊆ S := by
  -- Endpoint casts leave the underlying function unchanged.
  rintro z ⟨t, rfl⟩
  rw [Path.cast_coe]
  exact hγ (Set.mem_range_self t)

/-- Helper for Theorem 59.1: the intersection of a Boolean pair is contained in either member. -/
private lemma boolIntersection_subset {X : Type u} (W : Bool → Set X) (side : Bool) :
    W false ∩ W true ⊆ W side := by
  -- There are only the two cover members.
  cases side
  · exact Set.inter_subset_left
  · exact Set.inter_subset_right

/-- Helper for Theorem 59.1: the canonical path in the intersection, viewed in `X`. -/
private noncomputable def intersectionConnector {X : Type u} [TopologicalSpace X]
    (W : Bool → Set X) (x₀ : X) (hx₀ : x₀ ∈ W false ∩ W true)
    [PathConnectedSpace (W false ∩ W true : Set X)]
    (y : X) (hy : y ∈ W false ∩ W true) : Path x₀ y :=
  (PathConnectedSpace.somePath
    (⟨x₀, hx₀⟩ : ↥(W false ∩ W true)) ⟨y, hy⟩).map continuous_subtype_val

/-- Helper for Theorem 59.1: `intersectionConnector` stays in the intersection. -/
private lemma intersectionConnector_range_subset {X : Type u} [TopologicalSpace X]
    (W : Bool → Set X) (x₀ : X) (hx₀ : x₀ ∈ W false ∩ W true)
    [PathConnectedSpace (W false ∩ W true : Set X)]
    (y : X) (hy : y ∈ W false ∩ W true) :
    Set.range (intersectionConnector W x₀ hx₀ y hy) ⊆ W false ∩ W true := by
  -- Every value of the subtype-valued path carries its intersection membership.
  rintro z ⟨t, rfl⟩
  exact (PathConnectedSpace.somePath
    (⟨x₀, hx₀⟩ : ↥(W false ∩ W true)) ⟨y, hy⟩ t).property

/-- Helper for Theorem 59.1: the quotient class of a one-edge concatenation is the edge class. -/
private lemma pathClass_concat_one {X : Type u} [TopologicalSpace X]
    (p : Fin 2 → X) (F : (i : Fin 1) → Path (p i.castSucc) (p i.succ)) :
    Path.Homotopic.Quotient.mk (Path.concat p F) =
      Path.Homotopic.Quotient.mk (F 0) := by
  -- Use the canonical homotopy between a one-term concatenation and its sole path.
  exact Path.Homotopic.Quotient.eq.mpr (Path.Homotopic.concat_one p F)

/-- Helper for Theorem 59.1: going backward along a path class and then forward again,
between a connector class and its reverse, yields the identity. -/
private lemma reverseEdgeClosedClass_eq_refl {X : Type u} [TopologicalSpace X]
    {x₀ a b : X} (β : Path.Homotopic.Quotient x₀ b)
    (F : Path.Homotopic.Quotient a b) :
    (β.trans F.symm).trans (F.trans β.symm) =
      Path.Homotopic.Quotient.refl x₀ := by
  -- Associate the quotient composite and cancel first the edge, then the connector.
  rw [← Path.Homotopic.Quotient.trans_assoc
      (β.trans F.symm) F β.symm,
    Path.Homotopic.Quotient.trans_assoc
      β F.symm F,
    Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.trans_refl,
    Path.Homotopic.Quotient.trans_symm]

/-- Helper for Theorem 59.1: path classes turn the last-step decomposition of
`Path.concat` into quotient composition. -/
private lemma pathClass_concat_succ {X : Type u} [TopologicalSpace X]
    {n : ℕ} (p : Fin (n + 2) → X)
    (F : (i : Fin (n + 1)) → Path (p i.castSucc) (p i.succ)) :
    Path.Homotopic.Quotient.mk (Path.concat p F) =
      (Path.Homotopic.Quotient.mk
        (Path.concat (p ∘ Fin.castSucc) (fun i ↦ F i.castSucc))).trans
      (Path.Homotopic.Quotient.mk (F (Fin.last n))) := by
  -- Apply the defining last-edge equation before passing the equality through the quotient.
  calc
    Path.Homotopic.Quotient.mk (Path.concat p F) =
        Path.Homotopic.Quotient.mk
          ((Path.concat (p ∘ Fin.castSucc) (fun i ↦ F i.castSucc)).trans
            (F (Fin.last n))) :=
      congrArg Path.Homotopic.Quotient.mk (Path.concat_succ p F)
    _ = (Path.Homotopic.Quotient.mk
          (Path.concat (p ∘ Fin.castSucc) (fun i ↦ F i.castSucc))).trans
        (Path.Homotopic.Quotient.mk (F (Fin.last n))) := by
      exact Path.Homotopic.Quotient.mk_trans _ _

/-- Helper for Theorem 59.1: inserting a connector and its reverse between two
composable path classes does not change their closed composite. -/
private lemma closedPathClass_paste {X : Type u} [TopologicalSpace X]
    {x₀ a b c : X}
    (A : Path.Homotopic.Quotient x₀ a)
    (P : Path.Homotopic.Quotient a b)
    (G : Path.Homotopic.Quotient x₀ b)
    (E : Path.Homotopic.Quotient b c)
    (B : Path.Homotopic.Quotient x₀ c) :
    A.trans ((P.trans E).trans B.symm) =
      (A.trans (P.trans G.symm)).trans (G.trans (E.trans B.symm)) := by
  -- Reassociate until the adjacent inverse connector cancels.
  rw [Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.trans_assoc]
  apply congrArg (Path.Homotopic.Quotient.trans A)
  rw [Path.Homotopic.Quotient.trans_assoc]
  apply congrArg (Path.Homotopic.Quotient.trans P)
  rw [← Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]

/-- Helper for Theorem 59.1: the closed class of a concatenation split at its last edge
is the composite of the two corresponding closed classes. -/
private lemma closedConcatClass_succ {X : Type u} [TopologicalSpace X]
    {x₀ : X} {n : ℕ} (p : Fin (n + 2) → X)
    (F : (i : Fin (n + 1)) → Path (p i.castSucc) (p i.succ))
    (α : Path x₀ (p 0))
    (γ : Path x₀ (p ((Fin.last n).castSucc)))
    (β : Path x₀ (p (Fin.last (n + 1)))) :
    (Path.Homotopic.Quotient.mk α).trans
        ((Path.Homotopic.Quotient.mk (Path.concat p F)).trans
          (Path.Homotopic.Quotient.mk β).symm) =
      ((Path.Homotopic.Quotient.mk α).trans
          ((Path.Homotopic.Quotient.mk
            (Path.concat (p ∘ Fin.castSucc) (fun i ↦ F i.castSucc))).trans
            (Path.Homotopic.Quotient.mk γ).symm)).trans
        ((Path.Homotopic.Quotient.mk γ).trans
          ((Path.Homotopic.Quotient.mk (F (Fin.last n))).trans
            (Path.Homotopic.Quotient.mk β).symm)) := by
  -- Rewrite the finite concatenation once, then apply the abstract cancellation square.
  rw [pathClass_concat_succ]
  exact closedPathClass_paste _ _ _ _ _

/-- Helper for Theorem 59.1: a nonempty two-set-labeled path chain admits a connector
at its first vertex whose closed concatenation belongs to any subgroup containing all
single-side loops. -/
private lemma existsStartConnector_closedConcatMem {X : Type u} [TopologicalSpace X]
    (W : Bool → Set X) (x₀ : X) (hx₀ : x₀ ∈ W false ∩ W true)
    [PathConnectedSpace (W false ∩ W true : Set X)]
    (H : Subgroup (FundamentalGroup X x₀))
    (hloop : ∀ side (γ : Path x₀ x₀), Set.range γ ⊆ W side →
      (Path.Homotopic.Quotient.mk γ : FundamentalGroup X x₀) ∈ H)
    (n : ℕ) (p : Fin (n + 2) → X)
    (F : (i : Fin (n + 1)) → Path (p i.castSucc) (p i.succ))
    (side : Fin (n + 1) → Bool)
    (hF : ∀ i, Set.range (F i) ⊆ W (side i))
    (β : Path x₀ (p (Fin.last (n + 1))))
    (hβ : Set.range β ⊆ W (side (Fin.last n))) :
    ∃ α : Path x₀ (p 0), Set.range α ⊆ W (side 0) ∧
      ((Path.Homotopic.Quotient.mk α).trans
        ((Path.Homotopic.Quotient.mk (Path.concat p F)).trans
          (Path.Homotopic.Quotient.mk β).symm) : FundamentalGroup X x₀) ∈ H := by
  induction n with
  | zero =>
      -- With one edge, pull the final connector backward across that edge.
      let α : Path x₀ (p 0) := β.trans (F 0).symm
      have hα : Set.range α ⊆ W (side 0) := by
        exact pathTrans_range_subset β (F 0).symm hβ
          (pathSymm_range_subset (F 0) (hF 0))
      refine ⟨α, hα, ?_⟩
      have hconcat := pathClass_concat_one p F
      rw [hconcat]
      have hαclass :
          Path.Homotopic.Quotient.mk α =
            (Path.Homotopic.Quotient.mk β).trans
              (Path.Homotopic.Quotient.mk (F 0)).symm := by
        dsimp only [α]
        rw [Path.Homotopic.Quotient.mk_trans]
        exact congrArg
          (Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk β))
          (Path.Homotopic.Quotient.mk_symm (F 0))
      have hnull :
          (Path.Homotopic.Quotient.mk α).trans
              ((Path.Homotopic.Quotient.mk (F 0)).trans
                (Path.Homotopic.Quotient.mk β).symm) =
            (1 : FundamentalGroup X x₀) := by
        calc
          (Path.Homotopic.Quotient.mk α).trans
                ((Path.Homotopic.Quotient.mk (F 0)).trans
                  (Path.Homotopic.Quotient.mk β).symm) =
              ((Path.Homotopic.Quotient.mk β).trans
                  (Path.Homotopic.Quotient.mk (F 0)).symm).trans
                ((Path.Homotopic.Quotient.mk (F 0)).trans
                  (Path.Homotopic.Quotient.mk β).symm) :=
            congrArg (fun q ↦ q.trans
              ((Path.Homotopic.Quotient.mk (F 0)).trans
                (Path.Homotopic.Quotient.mk β).symm)) hαclass
          _ = Path.Homotopic.Quotient.refl x₀ :=
            reverseEdgeClosedClass_eq_refl _ _
          _ = (1 : FundamentalGroup X x₀) := FundamentalGroup.one_def.symm
      exact hnull.symm ▸ H.one_mem
  | succ n ih =>
      -- At the last vertex of the prefix, either extend backward in one side or reset
      -- the connector inside the intersection when the side label changes.
      have hconnect :
          ∃ γ : Path x₀ (p ((Fin.last (n + 1)).castSucc)),
            Set.range γ ⊆ W (side ((Fin.last n).castSucc)) ∧
            Set.range γ ⊆ W (side (Fin.last (n + 1))) := by
        by_cases hside :
            side ((Fin.last n).castSucc) = side (Fin.last (n + 1))
        · let γ : Path x₀ (p ((Fin.last (n + 1)).castSucc)) :=
            β.trans (F (Fin.last (n + 1))).symm
          have hγlast : Set.range γ ⊆ W (side (Fin.last (n + 1))) := by
            exact pathTrans_range_subset β (F (Fin.last (n + 1))).symm hβ
              (pathSymm_range_subset (F (Fin.last (n + 1)))
                (hF (Fin.last (n + 1))))
          refine ⟨γ, ?_, hγlast⟩
          rw [hside]
          exact hγlast
        · have hshared :
              p ((Fin.last (n + 1)).castSucc) ∈ W false ∩ W true := by
            have hprevious :
                p ((Fin.last (n + 1)).castSucc) ∈
                  W (side ((Fin.last n).castSucc)) := by
              have hindex :
                  (Fin.last n).castSucc.succ =
                    (Fin.last (n + 1)).castSucc := by
                apply Fin.ext
                rfl
              rw [← hindex]
              exact hF ((Fin.last n).castSucc)
                (Path.target_mem_range (F ((Fin.last n).castSucc)))
            have hlast :
                p ((Fin.last (n + 1)).castSucc) ∈
                  W (side (Fin.last (n + 1))) :=
              hF (Fin.last (n + 1))
                (Path.source_mem_range (F (Fin.last (n + 1))))
            cases hpreviousSide : side ((Fin.last n).castSucc)
            · have hlastSide : side (Fin.last (n + 1)) = true := by
                cases hlastValue : side (Fin.last (n + 1))
                · exact False.elim (hside (hpreviousSide.trans hlastValue.symm))
                · rfl
              exact ⟨hpreviousSide ▸ hprevious, hlastSide ▸ hlast⟩
            · have hlastSide : side (Fin.last (n + 1)) = false := by
                cases hlastValue : side (Fin.last (n + 1))
                · rfl
                · exact False.elim (hside (hpreviousSide.trans hlastValue.symm))
              exact ⟨hlastSide ▸ hlast, hpreviousSide ▸ hprevious⟩
          let γ := intersectionConnector W x₀ hx₀
            (p ((Fin.last (n + 1)).castSucc)) hshared
          have hγintersection : Set.range γ ⊆ W false ∩ W true :=
            intersectionConnector_range_subset W x₀ hx₀
              (p ((Fin.last (n + 1)).castSucc)) hshared
          exact ⟨γ,
            hγintersection.trans (boolIntersection_subset W _),
            hγintersection.trans (boolIntersection_subset W _)⟩
      obtain ⟨γ, hγprevious, hγlast⟩ := hconnect
      -- Apply the induction hypothesis to the prefix, using the new shared connector.
      obtain ⟨α, hα, hprefix⟩ := ih
        (p := p ∘ Fin.castSucc)
        (F := fun i ↦ F i.castSucc)
        (side := fun i ↦ side i.castSucc)
        (fun i ↦ hF i.castSucc) γ hγprevious
      refine ⟨α, ?_, ?_⟩
      · have hzero :
            (0 : Fin (n + 1)).castSucc = (0 : Fin (n + 2)) := by
          apply Fin.ext
          rfl
        rw [← hzero]
        exact hα
      · have htailRange :
            Set.range ((F (Fin.last (n + 1))).trans β.symm) ⊆
              W (side (Fin.last (n + 1))) :=
          pathTrans_range_subset (F (Fin.last (n + 1))) β.symm
            (hF (Fin.last (n + 1))) (pathSymm_range_subset β hβ)
        have hclosedRange :
            Set.range (γ.trans ((F (Fin.last (n + 1))).trans β.symm)) ⊆
              W (side (Fin.last (n + 1))) :=
          pathTrans_range_subset γ _ hγlast htailRange
        have hlast := hloop (side (Fin.last (n + 1)))
          (γ.trans ((F (Fin.last (n + 1))).trans β.symm)) hclosedRange
        have hlastClass :
            ((Path.Homotopic.Quotient.mk γ).trans
              ((Path.Homotopic.Quotient.mk (F (Fin.last (n + 1)))).trans
                (Path.Homotopic.Quotient.mk β).symm) :
              FundamentalGroup X x₀) ∈ H := by
          have hinner :
              Path.Homotopic.Quotient.mk
                  ((F (Fin.last (n + 1))).trans β.symm) =
                (Path.Homotopic.Quotient.mk (F (Fin.last (n + 1)))).trans
                  (Path.Homotopic.Quotient.mk β).symm := by
            rw [Path.Homotopic.Quotient.mk_trans]
            exact congrArg
              (Path.Homotopic.Quotient.trans
                (Path.Homotopic.Quotient.mk (F (Fin.last (n + 1)))))
              (Path.Homotopic.Quotient.mk_symm β)
          have houter :
              Path.Homotopic.Quotient.mk
                  (γ.trans ((F (Fin.last (n + 1))).trans β.symm)) =
                (Path.Homotopic.Quotient.mk γ).trans
                  ((Path.Homotopic.Quotient.mk (F (Fin.last (n + 1)))).trans
                    (Path.Homotopic.Quotient.mk β).symm) := by
            rw [Path.Homotopic.Quotient.mk_trans, hinner]
          exact houter ▸ hlast
        have hcombined := H.mul_mem hlastClass hprefix
        rw [FundamentalGroup.mul_def] at hcombined
        have hpaste := closedConcatClass_succ p F α γ β
        exact hpaste.symm ▸ hcombined

/-- Helper for Theorem 59.1: reversing the constant path class fixes it. -/
private lemma quotientRefl_symm {X : Type u} [TopologicalSpace X] (x : X) :
    (Path.Homotopic.Quotient.refl x).symm =
      Path.Homotopic.Quotient.refl x := by
  -- Represent the constant class by its constant path and use reversal of that path.
  rw [← Path.Homotopic.Quotient.mk_refl,
    ← Path.Homotopic.Quotient.mk_symm, Path.refl_symm]

/-- Helper for Theorem 59.1: if closing a path by an initial connector gives an
element of `H`, and that connector itself lies in `H`, then the endpoint-cast path lies in `H`. -/
private lemma pathClassCast_mem_of_closedConcat {X : Type u} [TopologicalSpace X]
    {x₀ a b : X} (H : Subgroup (FundamentalGroup X x₀))
    (hsource : a = x₀) (htarget : b = x₀)
    (α : Path x₀ a) (C : Path a b)
    (hα : (Path.Homotopic.Quotient.mk
      (α.cast rfl hsource.symm) : FundamentalGroup X x₀) ∈ H)
    (hclosed : ((Path.Homotopic.Quotient.mk α).trans
      ((Path.Homotopic.Quotient.mk C).trans
        (Path.Homotopic.Quotient.mk
          ((Path.refl x₀).cast rfl htarget)).symm) :
      FundamentalGroup X x₀) ∈ H) :
    (Path.Homotopic.Quotient.mk
      (C.cast hsource.symm htarget.symm) : FundamentalGroup X x₀) ∈ H := by
  -- Replace the endpoints by the basepoint, then cancel the initial connector in the group.
  subst a
  subst b
  simp only [Path.Homotopic.Quotient.mk_cast,
    Path.Homotopic.Quotient.cast_rfl_rfl] at hα hclosed ⊢
  rw [Path.Homotopic.Quotient.mk_refl, quotientRefl_symm,
    Path.Homotopic.Quotient.trans_refl] at hclosed
  have hcombined := H.mul_mem hclosed (H.inv_mem hα)
  rw [FundamentalGroup.mul_def, FundamentalGroup.inv_def,
    ← Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans] at hcombined
  exact hcombined

/-- Helper for Theorem 59.1: a loop subordinate to a finite subdivision by `U` and `V`
belongs to the subgroup generated by the two inclusion-induced ranges. -/
private lemma loopClassMemSupRangesOfSubdivision {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace (U ∩ V : Set X)]
    (f : Path x₀ x₀) (n : ℕ) (a : Fin (n + 2) → unitInterval)
    (hstart : a 0 = 0) (hend : a (Fin.last (n + 1)) = 1)
    (side : Fin (n + 1) → Bool)
    (hsubpath : ∀ i, Set.range (f.subpath (a i.castSucc) (a i.succ)) ⊆
      if side i then V else U) :
    (Path.Homotopic.Quotient.mk f : FundamentalGroup X x₀) ∈
      MonoidHom.range (FundamentalGroup.mapOfSubtype U ⟨x₀, hx₀.1⟩) ⊔
        MonoidHom.range (FundamentalGroup.mapOfSubtype V ⟨x₀, hx₀.2⟩) := by
  -- Package the two cover members as a Boolean family and name the generated subgroup.
  let W : Bool → Set X := fun
    | false => U
    | true => V
  letI : PathConnectedSpace (W false ∩ W true : Set X) := by
    simpa only [W] using
      (inferInstance : PathConnectedSpace (U ∩ V : Set X))
  let H : Subgroup (FundamentalGroup X x₀) :=
    MonoidHom.range (FundamentalGroup.mapOfSubtype U ⟨x₀, hx₀.1⟩) ⊔
      MonoidHom.range (FundamentalGroup.mapOfSubtype V ⟨x₀, hx₀.2⟩)
  have hxW : x₀ ∈ W false ∩ W true := by
    exact hx₀
  have hsingleSide : ∀ choice (γ : Path x₀ x₀), Set.range γ ⊆ W choice →
      (Path.Homotopic.Quotient.mk γ : FundamentalGroup X x₀) ∈ H := by
    intro choice γ hγ
    cases choice
    · have hrange := loopClassMemMapOfSubtypeRange hx₀.1 γ hγ
      exact (show MonoidHom.range
        (FundamentalGroup.mapOfSubtype U ⟨x₀, hx₀.1⟩) ≤ H from le_sup_left) hrange
    · have hrange := loopClassMemMapOfSubtypeRange hx₀.2 γ hγ
      exact (show MonoidHom.range
        (FundamentalGroup.mapOfSubtype V ⟨x₀, hx₀.2⟩) ≤ H from le_sup_right) hrange
  -- The endpoint equations identify the first and last subdivision vertices with `x₀`.
  have hsource : (f ∘ a) 0 = x₀ :=
    (congrArg f hstart).trans f.source
  have htarget : (f ∘ a) (Fin.last (n + 1)) = x₀ :=
    (congrArg f hend).trans f.target
  let β : Path x₀ ((f ∘ a) (Fin.last (n + 1))) :=
    (Path.refl x₀).cast rfl htarget
  have hxLastSide : x₀ ∈ W (side (Fin.last n)) :=
    boolIntersection_subset W _ hxW
  have hreflRange : Set.range (Path.refl x₀) ⊆ W (side (Fin.last n)) := by
    rw [Path.refl_range]
    exact Set.singleton_subset_iff.mpr hxLastSide
  have hβ : Set.range β ⊆ W (side (Fin.last n)) :=
    pathCast_range_subset (Path.refl x₀) rfl htarget hreflRange
  have hF : ∀ i, Set.range (f.subpath (a i.castSucc) (a i.succ)) ⊆
      W (side i) := by
    -- Normalize the source statement's Boolean conditional to the named cover family.
    intro i
    cases hchoice : side i
    · simpa only [hchoice, W, Bool.false_eq_true, if_false] using hsubpath i
    · simpa only [hchoice, W, Bool.true_eq, if_true] using hsubpath i
  -- The backward connector induction closes the subdivided path inside `H`.
  obtain ⟨α, hα, hclosed⟩ := existsStartConnector_closedConcatMem
    W x₀ hxW H hsingleSide n (f ∘ a)
      (fun i ↦ f.subpath (a i.castSucc) (a i.succ)) side
      hF β hβ
  have hαcast : Set.range (α.cast rfl hsource.symm) ⊆ W (side 0) :=
    pathCast_range_subset α rfl hsource.symm hα
  have hαmem :
      (Path.Homotopic.Quotient.mk (α.cast rfl hsource.symm) :
        FundamentalGroup X x₀) ∈ H :=
    hsingleSide (side 0) (α.cast rfl hsource.symm) hαcast
  dsimp only [β] at hclosed
  have hconcatMem := pathClassCast_mem_of_closedConcat H hsource htarget α
    (Path.concat (f ∘ a) (fun i ↦ f.subpath (a i.castSucc) (a i.succ)))
    hαmem hclosed
  -- Theorem 51.3 identifies the endpoint-cast concatenation with the original loop class.
  have hclass := pathClass_eq_concatSubpaths f a hstart hend
  have hclassGroup :
      (Path.Homotopic.Quotient.mk f : FundamentalGroup X x₀) =
        (Path.Homotopic.Quotient.mk
          ((Path.concat (f ∘ a)
            (fun i ↦ f.subpath (a i.castSucc) (a i.succ))).cast
              hsource.symm htarget.symm) : FundamentalGroup X x₀) :=
    hclass
  have hgoal :
      (Path.Homotopic.Quotient.mk f : FundamentalGroup X x₀) ∈ H :=
    hclassGroup.symm ▸ hconcatMem
  exact hgoal

/-- Theorem 59.1: If `X = U ∪ V`, where `U` and `V` are open and `U ∩ V` is path
connected with basepoint `x₀`, then the images of the inclusion-induced homomorphisms
from the fundamental groups of `U` and `V` generate the fundamental group of `X`. -/
theorem fundamentalGroupMap_range_sup_range_eq_top {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace (U ∩ V : Set X)] :
    MonoidHom.range (FundamentalGroup.mapOfSubtype U ⟨x₀, hx₀.1⟩) ⊔
      MonoidHom.range (FundamentalGroup.mapOfSubtype V ⟨x₀, hx₀.2⟩) = ⊤ := by
  -- It suffices to place an arbitrary represented loop in the generated subgroup.
  apply top_unique
  intro g _
  obtain ⟨f, rfl⟩ :=
    Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath g)
  classical
  -- Pull the two open cover members back along the loop.
  let c : Bool → Set unitInterval := fun
    | false => f ⁻¹' U
    | true => f ⁻¹' V
  have hcOpen : ∀ choice, IsOpen (c choice) := by
    intro choice
    cases choice
    · exact hU.preimage f.continuous
    · exact hV.preimage f.continuous
  have hcCover : Set.univ ⊆ ⋃ choice, c choice := by
    intro s _
    have hfs : f s ∈ U ∪ V := by
      rw [hcover]
      exact Set.mem_univ (f s)
    cases hfs with
    | inl hfsU =>
        apply Set.mem_iUnion.mpr
        exact ⟨false, hfsU⟩
    | inr hfsV =>
        apply Set.mem_iUnion.mpr
        exact ⟨true, hfsV⟩
  -- Compactness of the unit interval supplies a monotone finite subdivision.
  obtain ⟨t, ht0, htmono, ⟨m, hm⟩, htSubordinate⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hcOpen hcCover
  have hmpositive : 0 < m := by
    by_contra hmnot
    have hmzero : m = 0 := Nat.eq_zero_of_not_pos hmnot
    subst m
    have htone : t 0 = 1 := hm 0 le_rfl
    rw [ht0] at htone
    exact zero_ne_one htone
  obtain ⟨n, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpositive)
  let a : Fin (n + 2) → unitInterval := fun i ↦ t i
  have haStart : a 0 = 0 := ht0
  have haEnd : a (Fin.last (n + 1)) = 1 := by
    exact hm (n + 1) le_rfl
  choose side hside using fun i : Fin (n + 1) ↦ htSubordinate i
  have hsubpath : ∀ i, Set.range (f.subpath (a i.castSucc) (a i.succ)) ⊆
      if side i then V else U := by
    intro i
    have hstep : a i.castSucc ≤ a i.succ := by
      exact htmono (Nat.le_succ i)
    rw [Path.range_subpath_of_le f _ _ hstep]
    rintro z ⟨s, hs, rfl⟩
    have hsCover : s ∈ c (side i) := by
      apply hside i
      exact hs
    cases hchoice : side i
    · simpa only [c, hchoice, Bool.false_eq_true, if_false,
        Set.mem_preimage] using hsCover
    · simpa only [c, hchoice, Bool.true_eq, if_true,
        Set.mem_preimage] using hsCover
  -- The subdivision lemma converts those local range containments into generation.
  exact loopClassMemSupRangesOfSubdivision U V x₀ hx₀ f n a
    haStart haEnd side hsubpath
