import stacks_project.Chap10.Lemma_10_127_5

open scoped TensorProduct

universe u v w

noncomputable section

namespace Lemma10_168_4TailZeroFamilyDescent

section

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
variable (A : I → Type u) [∀ i, CommRing (A i)]
variable (f : ∀ i j, i ≤ j → A i →+* A j)
variable [DirectedSystem A (fun i j hij ↦ f i j hij)]
variable {i₀ : I}
variable {C₀ : Type w} [CommRing C₀] [Algebra (A i₀) C₀]

local notation "A∞" => Ring.DirectLimit A (fun i j hij ↦ f i j hij)

/-- Helper for Lemma 10.168.4: the ambient direct limit carries the canonical `A₀`-algebra
structure from the distinguished stage `i₀`. -/
noncomputable local instance directLimitStageAlgebra : Algebra (A i₀) A∞ :=
  (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra

/-- Helper for Lemma 10.168.4: the cofinal tail above `i₀` is inhabited by the base stage
itself. -/
local instance tail_nonempty : Nonempty (Set.Ici i₀) :=
  ⟨⟨i₀, le_rfl⟩⟩

/-- Helper for Lemma 10.168.4: every stage in the tail above `i₀` inherits the canonical
`A i₀`-algebra structure from the transition map out of `i₀`. -/
noncomputable local instance tail_stageAlgebra (j : Set.Ici i₀) : Algebra (A i₀) (A j.1) :=
  (f i₀ j.1 j.2).toAlgebra

/-- Helper for Lemma 10.168.4: a chosen upper bound lies above both a given stage and the base
stage `i₀`. -/
noncomputable def tail_upper_bound (i : I) : I :=
  (exists_ge_ge i i₀).choose

/-- Helper for Lemma 10.168.4: the chosen upper bound lies above the original stage. -/
theorem le_tail_upper_bound_left (i : I) :
    i ≤ tail_upper_bound (i₀ := i₀) i :=
  (exists_ge_ge i i₀).choose_spec.1

/-- Helper for Lemma 10.168.4: the chosen upper bound lies in the tail above `i₀`. -/
theorem le_tail_upper_bound_right (i : I) :
    i₀ ≤ tail_upper_bound (i₀ := i₀) i :=
  (exists_ge_ge i i₀).choose_spec.2

/-- Helper for Lemma 10.168.4: every stage of the directed system maps canonically into the direct
limit of the cofinal tail above `i₀`. -/
noncomputable def full_stage_to_tail_directLimit (i : I) :
    A i →+* Ring.DirectLimit (fun j : Set.Ici i₀ ↦ A j.1) (fun j k hij ↦ f j.1 k.1 hij) :=
  let j : Set.Ici i₀ :=
    ⟨tail_upper_bound (i₀ := i₀) i, le_tail_upper_bound_right (i₀ := i₀) i⟩
  (Ring.DirectLimit.of (fun j : Set.Ici i₀ ↦ A j.1) (fun j k hij ↦ f j.1 k.1 hij) j).comp
    (f i j.1 (le_tail_upper_bound_left (i₀ := i₀) i))

/-- Helper for Lemma 10.168.4: the stage maps into the tail direct limit are compatible with the
original transition maps. -/
theorem full_stage_to_tail_directLimit_compatible {i j : I} (hij : i ≤ j) (x : A i) :
    full_stage_to_tail_directLimit (A := A) (f := f) (i₀ := i₀) j (f i j hij x) =
      full_stage_to_tail_directLimit (A := A) (f := f) (i₀ := i₀) i x := by
  letI : IsDirectedOrder (Set.Ici i₀) := by
    constructor
    intro a b
    obtain ⟨k, hak, hbk⟩ := exists_ge_ge a.1 b.1
    exact ⟨⟨k, le_trans a.2 hak⟩, hak, hbk⟩
  let ji : Set.Ici i₀ :=
    ⟨tail_upper_bound (i₀ := i₀) i, le_tail_upper_bound_right (i₀ := i₀) i⟩
  let jj : Set.Ici i₀ :=
    ⟨tail_upper_bound (i₀ := i₀) j, le_tail_upper_bound_right (i₀ := i₀) j⟩
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge ji jj
  -- Proof comment: move both representatives to a common tail stage and then use the original
  -- directed-system compatibility.
  calc
    full_stage_to_tail_directLimit (A := A) (f := f) (i₀ := i₀) j (f i j hij x) =
      Ring.DirectLimit.of (fun j : Set.Ici i₀ ↦ A j.1) (fun j k hij ↦ f j.1 k.1 hij) k
        (f jj.1 k.1 hjk
          (f j jj.1 (le_tail_upper_bound_left (i₀ := i₀) j) (f i j hij x))) := by
            simp [full_stage_to_tail_directLimit, jj, RingHom.comp_apply]
            symm
            exact Ring.DirectLimit.of_f hjk _
    _ =
      Ring.DirectLimit.of (fun j : Set.Ici i₀ ↦ A j.1) (fun j k hij ↦ f j.1 k.1 hij) k
        (f ji.1 k.1 hik (f i ji.1 (le_tail_upper_bound_left (i₀ := i₀) i) x)) := by
          congr 1
          calc
            f jj.1 k.1 hjk (f j jj.1 (le_tail_upper_bound_left (i₀ := i₀) j)
                (f i j hij x)) =
              f j k.1 (le_trans (le_tail_upper_bound_left (i₀ := i₀) j) hjk)
                (f i j hij x) := by
                  exact DirectedSystem.map_map'
                    (f := fun i j hij ↦ f i j hij)
                    (le_tail_upper_bound_left (i₀ := i₀) j) hjk (f i j hij x)
            _ =
              f i k.1
                (le_trans hij (le_trans (le_tail_upper_bound_left (i₀ := i₀) j) hjk)) x := by
                    exact DirectedSystem.map_map'
                      (f := fun i j hij ↦ f i j hij)
                      hij
                      (le_trans (le_tail_upper_bound_left (i₀ := i₀) j) hjk)
                      x
            _ =
              f ji.1 k.1 hik (f i ji.1 (le_tail_upper_bound_left (i₀ := i₀) i) x) := by
                symm
                exact DirectedSystem.map_map'
                  (f := fun i j hij ↦ f i j hij)
                  (le_tail_upper_bound_left (i₀ := i₀) i) hik x
    _ = full_stage_to_tail_directLimit (A := A) (f := f) (i₀ := i₀) i x := by
      simp [full_stage_to_tail_directLimit, ji, RingHom.comp_apply]
      exact Ring.DirectLimit.of_f hik _

/-- Helper for Lemma 10.168.4: the full direct limit maps canonically to the direct limit of the
tail above `i₀`. -/
noncomputable def full_directLimit_to_tail :
    A∞ →+* Ring.DirectLimit (fun j : Set.Ici i₀ ↦ A j.1) (fun j k hij ↦ f j.1 k.1 hij) :=
  Ring.DirectLimit.lift A (fun i j hij ↦ f i j hij)
    (Ring.DirectLimit (fun j : Set.Ici i₀ ↦ A j.1) (fun j k hij ↦ f j.1 k.1 hij))
    (fun i ↦ full_stage_to_tail_directLimit (A := A) (f := f) (i₀ := i₀) i)
    (fun i j hij x ↦
      full_stage_to_tail_directLimit_compatible (A := A) (f := f) (i₀ := i₀) hij x)

/-- Helper for Lemma 10.168.4: forgetting that a stage lies in the tail gives the compatibility
required to map the tail direct limit back to the original direct limit. -/
theorem tail_directLimit_to_full_compatible {j k : Set.Ici i₀} (hjk : j ≤ k) (x : A j.1) :
    Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) k.1 (f j.1 k.1 hjk x) =
      Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) j.1 x :=
  Ring.DirectLimit.of_f (G := A) (f := fun i j hij ↦ f i j hij) hjk x

/-- Helper for Lemma 10.168.4: the tail direct limit maps canonically back to the original direct
limit. -/
noncomputable def tail_directLimit_to_full :
    Ring.DirectLimit (fun j : Set.Ici i₀ ↦ A j.1) (fun j k hij ↦ f j.1 k.1 hij) →+* A∞ :=
  Ring.DirectLimit.lift
    (fun j : Set.Ici i₀ ↦ A j.1)
    (fun j k hij ↦ f j.1 k.1 hij)
    A∞
    (fun j ↦ Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) j.1)
    (fun j k hjk x ↦ tail_directLimit_to_full_compatible (A := A) (f := f) (i₀ := i₀) hjk x)

/-- Helper for Lemma 10.168.4: passing from the full direct limit to the tail and back is the
identity. -/
theorem tail_directLimit_to_full_comp_full_directLimit_to_tail :
    (tail_directLimit_to_full (A := A) (f := f) (i₀ := i₀)).comp
        (full_directLimit_to_tail (A := A) (f := f) (i₀ := i₀)) =
      RingHom.id _ := by
  apply Ring.DirectLimit.hom_ext
  intro i
  ext x
  -- Proof comment: enlarge to the chosen tail stage and then use the direct-limit relation.
  simp [full_directLimit_to_tail, full_stage_to_tail_directLimit, tail_directLimit_to_full,
    RingHom.comp_apply]

/-- Helper for Lemma 10.168.4: passing from the tail direct limit to the full direct limit and
back is the identity. -/
theorem full_directLimit_to_tail_comp_tail_directLimit_to_full :
    (full_directLimit_to_tail (A := A) (f := f) (i₀ := i₀)).comp
        (tail_directLimit_to_full (A := A) (f := f) (i₀ := i₀)) =
      RingHom.id _ := by
  apply Ring.DirectLimit.hom_ext
  intro j
  ext x
  -- Proof comment: a tail stage already lies above `i₀`, so forgetting and reindexing changes
  -- nothing in the direct limit.
  simp [full_directLimit_to_tail, full_stage_to_tail_directLimit, tail_directLimit_to_full,
    RingHom.comp_apply]

/-- Helper for Lemma 10.168.4: the direct limit of the tail above `i₀` is canonically isomorphic
to the original direct limit. -/
noncomputable def tail_directLimitIso {B : Type*} [CommRing B]
    (colimitIso : A∞ ≃+* B) :
    Ring.DirectLimit (fun j : Set.Ici i₀ ↦ A j.1) (fun j k hij ↦ f j.1 k.1 hij) ≃+* B :=
  (RingEquiv.ofRingHom
      (tail_directLimit_to_full (A := A) (f := f) (i₀ := i₀))
      (full_directLimit_to_tail (A := A) (f := f) (i₀ := i₀))
      (tail_directLimit_to_full_comp_full_directLimit_to_tail (A := A) (f := f) (i₀ := i₀))
      (full_directLimit_to_tail_comp_tail_directLimit_to_full (A := A) (f := f) (i₀ := i₀))).trans
    colimitIso

/-- Helper for Lemma 10.168.4: the tail above the base stage remains directed. -/
theorem tail_index_isDirected :
    IsDirectedOrder (Set.Ici i₀) := by
  constructor
  intro i j
  -- Proof comment: directedness of the ambient preorder gives a common upper bound in the tail.
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.1 j.1
  exact ⟨⟨k, le_trans i.2 hik⟩, hik, hjk⟩

/-- Helper for Lemma 10.168.4: the canonical map from a tail stage to the ambient direct limit
respects the induced `A₀`-algebra structure. -/
theorem tail_stage_to_direct_limit_algHom_commutes
    (j : Set.Ici i₀) (a : A i₀) :
    Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) j.1 ((f i₀ j.1 j.2) a) =
      algebraMap (A i₀) A∞ a := by
  -- Proof comment: this is just the direct-limit relation from the distinguished base stage.
  change Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) j.1 ((f i₀ j.1 j.2) a) =
    Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀ a
  simpa using
    (Ring.DirectLimit.of_f (G := A) (f := fun i j hij ↦ f i j hij) j.2 a).symm

/-- Helper for Lemma 10.168.4: the tail transition maps remain compatible with the chosen base
stage `i₀`. -/
theorem tail_stage_transition_commutes
    {j k : Set.Ici i₀} (hjk : j ≤ k) (a : A i₀) :
    f j.1 k.1 hjk ((f i₀ j.1 j.2) a) = (f i₀ k.1 (le_trans j.2 hjk)) a := by
  -- Proof comment: this is the ambient directed-system composition law specialized to the tail.
  simpa using (DirectedSystem.map_map (f := fun i j hij ↦ f i j hij) j.2 hjk a)

/-- Helper for Lemma 10.168.4: the canonical map from a tail stage to the ambient direct limit is
an algebra homomorphism over `A₀`. -/
noncomputable abbrev tail_stage_to_direct_limit_algHom
    (j : Set.Ici i₀) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    A j.1 →ₐ[A i₀] A∞ :=
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  { toRingHom := Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) j.1
    commutes' := tail_stage_to_direct_limit_algHom_commutes (A := A) (f := f) (i₀ := i₀) j }

/-- Helper for Lemma 10.168.4: the transition map between two tail stages is an algebra map over
`A₀`. -/
noncomputable abbrev tail_transition_algHom
    {j k : Set.Ici i₀} (hjk : j ≤ k) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
    A j.1 →ₐ[A i₀] A k.1 :=
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
  { toRingHom := f j.1 k.1 hjk
    commutes' := tail_stage_transition_commutes (A := A) (f := f) (i₀ := i₀) hjk }

/-- Helper for Lemma 10.168.4: the cofinal tail above `i₀` inherits the directed-order instance
needed by tensor-descent lemmas. -/
local instance tail_isDirectedOrder : IsDirectedOrder (Set.Ici i₀) :=
  tail_index_isDirected (i₀ := i₀)

/-- Helper for Lemma 10.168.4: the tail system reindexes the original directed system over
`Set.Ici i₀`. -/
abbrev tail_ring_family (j : Set.Ici i₀) : Type u :=
  A j.1

/-- Helper for Lemma 10.168.4: the reindexed tail system carries the induced family of
`A i₀`-algebra structures needed by tensor-descent lemmas. -/
noncomputable local instance tail_ring_familyAlgebra (j : Set.Ici i₀) :
    Algebra (A i₀) (tail_ring_family (A := A) (i₀ := i₀) j) :=
  tail_stageAlgebra (A := A) (f := f) (i₀ := i₀) j

/-- Helper for Lemma 10.168.4: the reindexed tail system carries the induced family of
`A i₀`-algebra structures needed by tensor-descent lemmas. -/
noncomputable local instance tail_ring_family_algebra_family :
    ∀ j : Set.Ici i₀, Algebra (A i₀) (tail_ring_family (A := A) (i₀ := i₀) j) :=
  fun j ↦ tail_ring_familyAlgebra (A := A) (f := f) (i₀ := i₀) j

/-- Helper for Lemma 10.168.4: the tail transition maps are the original transition maps on the
underlying stages. -/
abbrev tail_ring_transition (j k : Set.Ici i₀) (hjk : j ≤ k) :
    tail_ring_family (A := A) (i₀ := i₀) j →+*
      tail_ring_family (A := A) (i₀ := i₀) k :=
  f j.1 k.1 hjk

/-- Helper for Lemma 10.168.4: the tail transition algebra maps packaged as a reusable family. -/
abbrev tail_transition_family (j k : Set.Ici i₀) (hjk : j ≤ k) :
    letI : Algebra (A i₀) (tail_ring_family (A := A) (i₀ := i₀) j) :=
      tail_ring_familyAlgebra (A := A) (f := f) (i₀ := i₀) j
    letI : Algebra (A i₀) (tail_ring_family (A := A) (i₀ := i₀) k) :=
      tail_ring_familyAlgebra (A := A) (f := f) (i₀ := i₀) k
    tail_ring_family (A := A) (i₀ := i₀) j →ₐ[A i₀]
      tail_ring_family (A := A) (i₀ := i₀) k :=
  letI : Algebra (A i₀) (tail_ring_family (A := A) (i₀ := i₀) j) :=
    tail_ring_familyAlgebra (A := A) (f := f) (i₀ := i₀) j
  letI : Algebra (A i₀) (tail_ring_family (A := A) (i₀ := i₀) k) :=
    tail_ring_familyAlgebra (A := A) (f := f) (i₀ := i₀) k
  tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk

/-- Helper for Lemma 10.168.4: the tail transition maps form a directed system of rings. -/
local instance tail_directedSystem :
    DirectedSystem (tail_ring_family (A := A) (i₀ := i₀))
      (fun j k hjk ↦ tail_ring_transition (A := A) (f := f) (i₀ := i₀) j k hjk) where
  map_self := by
    intro j x
    exact DirectedSystem.map_self (f := fun i j hij ↦ f i j hij) x
  map_map := by
    intro k j i hij hjk x
    exact DirectedSystem.map_map (f := fun i j hij ↦ f i j hij) hij hjk x

/-- Helper for Lemma 10.168.4: the tail transition algebra maps also provide the exact ring-hom
family required by the owner tensor-descent API. -/
local instance tail_transition_family_directedSystem :
    letI : ∀ j : Set.Ici i₀, Algebra (A i₀) (tail_ring_family (A := A) (i₀ := i₀) j) :=
      tail_ring_family_algebra_family (A := A) (f := f) (i₀ := i₀)
    DirectedSystem (tail_ring_family (A := A) (i₀ := i₀))
      (fun j k hjk ↦
        ((tail_transition_family (A := A) (f := f) (i₀ := i₀) j k hjk :
          tail_ring_family (A := A) (i₀ := i₀) j →ₐ[A i₀]
            tail_ring_family (A := A) (i₀ := i₀) k) :
          tail_ring_family (A := A) (i₀ := i₀) j →+*
            tail_ring_family (A := A) (i₀ := i₀) k)) :=
  letI : ∀ j : Set.Ici i₀, Algebra (A i₀) (tail_ring_family (A := A) (i₀ := i₀) j) :=
    tail_ring_family_algebra_family (A := A) (f := f) (i₀ := i₀)
  tail_directedSystem (A := A) (f := f) (i₀ := i₀)

/-- Helper for Lemma 10.168.4: the tail transition algebra maps also form a directed system when
viewed as a family of functions. -/
local instance tail_transition_directedSystem :
    DirectedSystem (tail_ring_family (A := A) (i₀ := i₀))
      (fun j k hjk ↦
        (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk :
          tail_ring_family (A := A) (i₀ := i₀) j →
            tail_ring_family (A := A) (i₀ := i₀) k)) where
  map_self := by
    intro j x
    exact DirectedSystem.map_self (f := fun i j hij ↦ f i j hij) x
  map_map := by
    intro k j i hij hjk x
    exact DirectedSystem.map_map (f := fun i j hij ↦ f i j hij) hij hjk x

/-- Helper for Lemma 10.168.4: the direct limit of the tail above `i₀` carries the canonical
`A i₀`-algebra structure coming from the base tail stage. -/
noncomputable local instance tail_directLimit_algebra :
    Algebra (A i₀)
      (Ring.DirectLimit
        (tail_ring_family (A := A) (i₀ := i₀))
        (fun j k hjk ↦
          (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j.1 →+* A k.1))) :=
  (Ring.DirectLimit.of
    (tail_ring_family (A := A) (i₀ := i₀))
    (fun j k hjk ↦
      (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j.1 →+* A k.1))
    ⟨i₀, le_rfl⟩).toAlgebra

/-- Helper for Lemma 10.168.4: the direct limit of the tail above `i₀` canonically identifies
with the original direct limit as an `A i₀`-algebra. -/
noncomputable def tail_directLimitAlgEquivToFull :
    Ring.DirectLimit
        (tail_ring_family (A := A) (i₀ := i₀))
        (fun j k hjk ↦ tail_ring_transition (A := A) (f := f) (i₀ := i₀) j k hjk)
        ≃ₐ[A i₀] A∞ where
  __ := tail_directLimitIso (A := A) (f := f) (i₀ := i₀) (B := A∞) (RingEquiv.refl A∞)
  commutes' a := by
    -- Proof comment: both algebra maps are represented by the distinguished base tail stage
    -- `⟨i₀, le_rfl⟩`.
    change
      tail_directLimitIso (A := A) (f := f) (i₀ := i₀) (B := A∞) (RingEquiv.refl A∞)
          (Ring.DirectLimit.of
            (tail_ring_family (A := A) (i₀ := i₀))
            (fun j k hjk ↦ tail_ring_transition (A := A) (f := f) (i₀ := i₀) j k hjk)
            ⟨i₀, le_rfl⟩ a) =
        Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀ a
    rfl

/-- Helper for Lemma 10.168.4: the tail/full colimit equivalence sends a tail stage class to the
corresponding class in the original direct limit. -/
theorem tail_directLimitAlgEquivToFull_of (j : Set.Ici i₀) (x : A j.1) :
    tail_directLimitAlgEquivToFull (A := A) (f := f) (i₀ := i₀)
        (Ring.DirectLimit.of
          (tail_ring_family (A := A) (i₀ := i₀))
          (fun j' k' hjk ↦ tail_ring_transition (A := A) (f := f) (i₀ := i₀) j' k' hjk)
          j x) =
      Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) j.1 x := by
  -- Proof comment: `tail_directLimit_to_full` simply forgets that the chosen stage lies in the
  -- tail.
  rfl

/-- Helper for Lemma 10.168.4: the canonical map from a tail stage into the tail direct limit is
compatible with the `A i₀`-algebra structure induced from the base stage. -/
theorem tail_stage_to_tail_direct_limit_algHom_commutes
    (j : Set.Ici i₀) (a : A i₀) :
    Ring.DirectLimit.of
        (tail_ring_family (A := A) (i₀ := i₀))
        (fun j' k' hjk ↦ tail_ring_transition (A := A) (f := f) (i₀ := i₀) j' k' hjk)
        j ((f i₀ j.1 j.2) a) =
      algebraMap (A i₀)
        (Ring.DirectLimit
          (tail_ring_family (A := A) (i₀ := i₀))
          (fun j' k' hjk ↦ tail_ring_transition (A := A) (f := f) (i₀ := i₀) j' k' hjk)) a := by
  change
    Ring.DirectLimit.of
        (tail_ring_family (A := A) (i₀ := i₀))
        (fun j' k' hjk ↦ tail_ring_transition (A := A) (f := f) (i₀ := i₀) j' k' hjk)
        j ((f i₀ j.1 j.2) a) =
      Ring.DirectLimit.of
        (tail_ring_family (A := A) (i₀ := i₀))
        (fun j' k' hjk ↦ tail_ring_transition (A := A) (f := f) (i₀ := i₀) j' k' hjk)
        ⟨i₀, le_rfl⟩ a
  exact
    Ring.DirectLimit.of_f
      (G := tail_ring_family (A := A) (i₀ := i₀))
      (f := fun j' k' hjk ↦ tail_ring_transition (A := A) (f := f) (i₀ := i₀) j' k' hjk)
      (i := ⟨i₀, le_rfl⟩) (j := j) (hij := j.2) (x := a)

/-- Helper for Lemma 10.168.4: the canonical map from a tail stage to the tail direct limit is an
algebra homomorphism over the distinguished base stage. -/
noncomputable abbrev tail_stage_to_tail_direct_limit_algHom
    (j : Set.Ici i₀) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    A j.1 →ₐ[A i₀]
      Ring.DirectLimit
        (tail_ring_family (A := A) (i₀ := i₀))
        (fun j' k' hjk ↦ tail_ring_transition (A := A) (f := f) (i₀ := i₀) j' k' hjk) :=
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  { toRingHom :=
      Ring.DirectLimit.of
        (tail_ring_family (A := A) (i₀ := i₀))
        (fun j' k' hjk ↦ tail_ring_transition (A := A) (f := f) (i₀ := i₀) j' k' hjk)
        j
    commutes' :=
      tail_stage_to_tail_direct_limit_algHom_commutes (A := A) (f := f) (i₀ := i₀) j }

/-- Helper for Lemma 10.168.4: the canonical tensor map from a tail stage to the tail direct
limit, written using the same ring-transition presentation as `tail_directLimitAlgEquivToFull`. -/
noncomputable abbrev tail_stageTensorMap
    {X : Type*} [CommRing X] [Algebra (A i₀) X] (j : Set.Ici i₀) :
    letI : ∀ j' : Set.Ici i₀, Algebra (A i₀) (tail_ring_family (A := A) (i₀ := i₀) j') :=
      tail_ring_family_algebra_family (A := A) (f := f) (i₀ := i₀)
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    A j.1 ⊗[A i₀] X →ₗ[A i₀]
      ((Ring.DirectLimit
          (tail_ring_family (A := A) (i₀ := i₀))
          (fun j' k' hjk ↦ tail_ring_transition (A := A) (f := f) (i₀ := i₀) j' k' hjk))
        ⊗[A i₀] X) :=
  letI : ∀ j' : Set.Ici i₀, Algebra (A i₀) (tail_ring_family (A := A) (i₀ := i₀) j') :=
    tail_ring_family_algebra_family (A := A) (f := f) (i₀ := i₀)
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  LinearMap.rTensor X
    ((tail_stage_to_tail_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j).toLinearMap)

/-- Helper for Lemma 10.168.4: composing the canonical map from a tail stage into the tail direct
limit with the tail/full colimit equivalence recovers the literal stage map into the ambient
direct limit. -/
theorem tail_directLimitAlgEquivToFull_comp_tail_stage_to_tail_direct_limit_algHom
    (j : Set.Ici i₀) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    (tail_directLimitAlgEquivToFull (A := A) (f := f) (i₀ := i₀)).toAlgHom.comp
        (tail_stage_to_tail_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j) =
      tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j := by
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  -- Proof comment: both algebra maps send `x : A j.1` to the same direct-limit class represented
  -- by `x` at the stage `j`.
  apply AlgHom.ext
  intro x
  exact tail_directLimitAlgEquivToFull_of (A := A) (f := f) (i₀ := i₀) j x

/-- Helper for Lemma 10.168.4: the generic `stageTensorMap` on the tail system matches the
explicit tensor map into the original direct limit after transporting along the tail/full colimit
equivalence. -/
theorem tail_stageTensorMap_to_full
    {X : Type*} [CommRing X] [Algebra (A i₀) X]
    (j : Set.Ici i₀)
    (z :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      A j.1 ⊗[A i₀] X) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    letI : ∀ j' : Set.Ici i₀, Algebra (A i₀) (tail_ring_family (A := A) (i₀ := i₀) j') :=
      tail_ring_family_algebra_family (A := A) (f := f) (i₀ := i₀)
    (Algebra.TensorProduct.congr
      (tail_directLimitAlgEquivToFull (A := A) (f := f) (i₀ := i₀))
      (AlgEquiv.refl : X ≃ₐ[A i₀] X))
      (tail_stageTensorMap (A := A) (f := f) (i₀ := i₀) j z) =
      (Algebra.TensorProduct.map
        (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
        (AlgHom.id (A i₀) X)) z := by
  letI : ∀ j' : Set.Ici i₀, Algebra (A i₀) (tail_ring_family (A := A) (i₀ := i₀) j') :=
    tail_ring_family_algebra_family (A := A) (f := f) (i₀ := i₀)
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  let e := tail_directLimitAlgEquivToFull (A := A) (f := f) (i₀ := i₀)
  let g := tail_stage_to_tail_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j
  let h := tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j
  -- Route correction: identify the transported tensor map by functoriality of
  -- `Algebra.TensorProduct.map` instead of normalizing tensors elementwise.
  calc
    (Algebra.TensorProduct.congr e (AlgEquiv.refl : X ≃ₐ[A i₀] X))
        (tail_stageTensorMap (A := A) (f := f) (i₀ := i₀) j z) =
      (Algebra.TensorProduct.map e.toAlgHom (AlgHom.id (A i₀) X))
        ((Algebra.TensorProduct.map g (AlgHom.id (A i₀) X)) z) := by
          -- Proof comment: rewrite both tensor maps through the corresponding algebra-hom maps.
          change
            (Algebra.TensorProduct.congr e (AlgEquiv.refl : X ≃ₐ[A i₀] X))
              (((Algebra.TensorProduct.map g (AlgHom.id (A i₀) X)).toLinearMap) z) =
              (Algebra.TensorProduct.map e.toAlgHom (AlgHom.id (A i₀) X))
                ((Algebra.TensorProduct.map g (AlgHom.id (A i₀) X)) z)
          rw [Algebra.TensorProduct.congr_apply]
          rfl
    _ =
      (Algebra.TensorProduct.map (e.toAlgHom.comp g) (AlgHom.id (A i₀) X)) z := by
          -- Proof comment: tensoring commutes with composition on each factor.
          simpa [AlgHom.comp_id] using
            (congrArg
              (fun ψ :
                A j.1 ⊗[A i₀] X →ₐ[A i₀] A∞ ⊗[A i₀] X ↦ ψ z)
              (Algebra.TensorProduct.map_comp
                e.toAlgHom g (AlgHom.id (A i₀) X) (AlgHom.id (A i₀) X))).symm
    _ =
      (Algebra.TensorProduct.map h (AlgHom.id (A i₀) X)) z := by
          -- Proof comment: the composed coefficient map is exactly the ambient stage map.
          simpa [e, g, h] using
            congrArg
              (fun ψ : A j.1 →ₐ[A i₀] A∞ ↦
                (Algebra.TensorProduct.map ψ (AlgHom.id (A i₀) X)) z)
              (tail_directLimitAlgEquivToFull_comp_tail_stage_to_tail_direct_limit_algHom
                (A := A) (f := f) (i₀ := i₀) j)

/-- Helper for Lemma 10.168.4: an ambient zero equation for a tail-stage tensor forces the
explicit tail tensor map to agree with its value at zero. -/
theorem tail_stageTensorMap_eq_zero
    (j : Set.Ici i₀)
    (z :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      A j.1 ⊗[A i₀] C₀)
    (hz :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      (Algebra.TensorProduct.map
        (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
        (AlgHom.id (A i₀) C₀)) z = 0) :
    letI : ∀ j' : Set.Ici i₀, Algebra (A i₀) (tail_ring_family (A := A) (i₀ := i₀) j') :=
      tail_ring_family_algebra_family (A := A) (f := f) (i₀ := i₀)
    tail_stageTensorMap (A := A) (f := f) (i₀ := i₀) j z =
      tail_stageTensorMap (A := A) (f := f) (i₀ := i₀) j 0 := by
  letI : ∀ j' : Set.Ici i₀, Algebra (A i₀) (tail_ring_family (A := A) (i₀ := i₀) j') :=
    tail_ring_family_algebra_family (A := A) (f := f) (i₀ := i₀)
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  let e := tail_directLimitAlgEquivToFull (A := A) (f := f) (i₀ := i₀)
  -- Proof comment: transport both sides to the ambient direct-limit tensor product, where the
  -- assumed vanishing identifies the image of `z` with the image of `0`.
  apply (Algebra.TensorProduct.congr e (AlgEquiv.refl : C₀ ≃ₐ[A i₀] C₀)).injective
  calc
    (Algebra.TensorProduct.congr e (AlgEquiv.refl : C₀ ≃ₐ[A i₀] C₀))
        (tail_stageTensorMap (A := A) (f := f) (i₀ := i₀) j z) =
      (Algebra.TensorProduct.map
        (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
        (AlgHom.id (A i₀) C₀)) z := by
          simpa using
            (tail_stageTensorMap_to_full
              (A := A) (f := f) (i₀ := i₀) (X := C₀) j z)
    _ = 0 := hz
    _ =
      (Algebra.TensorProduct.map
        (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
        (AlgHom.id (A i₀) C₀)) (0 : A j.1 ⊗[A i₀] C₀) := by
          simp
    _ =
      (Algebra.TensorProduct.congr e (AlgEquiv.refl : C₀ ≃ₐ[A i₀] C₀))
        (tail_stageTensorMap (A := A) (f := f) (i₀ := i₀) j 0) := by
          symm
          simpa using
            (tail_stageTensorMap_to_full
              (A := A) (f := f) (i₀ := i₀) (X := C₀) j
              (0 : A j.1 ⊗[A i₀] C₀))

/-- Helper for Lemma 10.168.4: the explicit tail-stage tensor map sends the zero tensor to zero. -/
theorem tail_stageTensorMap_zero
    (j : Set.Ici i₀)
    :
    letI : ∀ j' : Set.Ici i₀, Algebra (A i₀) (tail_ring_family (A := A) (i₀ := i₀) j') :=
      tail_ring_family_algebra_family (A := A) (f := f) (i₀ := i₀)
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    tail_stageTensorMap (A := A) (f := f) (i₀ := i₀) j (0 : A j.1 ⊗[A i₀] C₀) = 0 := by
  letI : ∀ j' : Set.Ici i₀, Algebra (A i₀) (tail_ring_family (A := A) (i₀ := i₀) j') :=
    tail_ring_family_algebra_family (A := A) (f := f) (i₀ := i₀)
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  -- Proof comment: the explicit tail tensor map is linear, so it sends zero to zero.
  simp [tail_stageTensorMap]

/-- Helper for Lemma 10.168.4: coercing a tail transition algebra map to a ring hom recovers the
literal tail transition map. -/
theorem tail_transition_algHom_toRingHom_eq_tail_ring_transition
    {j k : Set.Ici i₀} (hjk : j ≤ k) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
    ((tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk :
      A j.1 →ₐ[A i₀] A k.1) :
      A j.1 →+* A k.1) =
      tail_ring_transition (A := A) (f := f) (i₀ := i₀) j k hjk := rfl

/-- Helper for Lemma 10.168.4: the explicit tail-stage coefficient map agrees with the generic
coefficient map used by the owner theorem's `stageTensorMap`. -/
theorem tail_stage_to_tail_direct_limit_linearMap_eq
    (j : Set.Ici i₀) :
    let tailLimit :=
      Ring.DirectLimit
        (tail_ring_family (A := A) (i₀ := i₀))
        (fun j' k' hjk ↦ tail_ring_transition (A := A) (f := f) (i₀ := i₀) j' k' hjk)
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    letI : Algebra (A j.1) tailLimit :=
      (tail_stage_to_tail_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j).toRingHom.toAlgebra
    ((tail_stage_to_tail_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j).toLinearMap :
      A j.1 →ₗ[A i₀] tailLimit) =
      (Algebra.linearMap (A j.1) tailLimit).restrictScalars (A i₀) := by
  let tailLimit :=
    Ring.DirectLimit
      (tail_ring_family (A := A) (i₀ := i₀))
      (fun j' k' hjk ↦ tail_ring_transition (A := A) (f := f) (i₀ := i₀) j' k' hjk)
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  letI : Algebra (A j.1) tailLimit :=
    (tail_stage_to_tail_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j).toRingHom.toAlgebra
  -- Proof comment: both linear maps come from the same canonical ring homomorphism from the tail
  -- stage into the tail direct limit.
  exact LinearMap.ext fun a ↦ rfl

/-- Helper for Lemma 10.168.4: an ambient zero equation forces the explicit tail-stage tensor map
itself to vanish. -/
theorem tail_stageTensorMap_vanishes
    (j : Set.Ici i₀)
    (z :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      A j.1 ⊗[A i₀] C₀)
    (hz :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      (Algebra.TensorProduct.map
        (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
        (AlgHom.id (A i₀) C₀)) z = 0) :
    letI : ∀ j' : Set.Ici i₀, Algebra (A i₀) (tail_ring_family (A := A) (i₀ := i₀) j') :=
      tail_ring_family_algebra_family (A := A) (f := f) (i₀ := i₀)
    tail_stageTensorMap (A := A) (f := f) (i₀ := i₀) j z = 0 := by
  letI : ∀ j' : Set.Ici i₀, Algebra (A i₀) (tail_ring_family (A := A) (i₀ := i₀) j') :=
    tail_ring_family_algebra_family (A := A) (f := f) (i₀ := i₀)
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  -- Proof comment: first identify the explicit tail-stage tensor map with its value on zero, then
  -- collapse that value by linearity.
  calc
    tail_stageTensorMap (A := A) (f := f) (i₀ := i₀) j z =
      tail_stageTensorMap (A := A) (f := f) (i₀ := i₀) j 0 :=
        tail_stageTensorMap_eq_zero (A := A) (f := f) (i₀ := i₀) (C₀ := C₀) j z hz
    _ = 0 := tail_stageTensorMap_zero (A := A) (f := f) (i₀ := i₀) (C₀ := C₀) j

/-- Helper for Lemma 10.168.4: a single tail-stage tensor that vanishes over the ambient direct
limit already vanishes after passing to some later tail stage. -/
theorem tail_tensor_eventually_zero
    (j : Set.Ici i₀)
    (z :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      A j.1 ⊗[A i₀] C₀)
    (hz :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      (Algebra.TensorProduct.map
        (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
        (AlgHom.id (A i₀) C₀)) z = 0) :
    letI : ∀ j' : Set.Ici i₀, Algebra (A i₀) (tail_ring_family (A := A) (i₀ := i₀) j') :=
      tail_ring_family_algebra_family (A := A) (f := f) (i₀ := i₀)
    ∃ k : Set.Ici i₀, ∃ hjk : j ≤ k,
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
    LinearMap.rTensor C₀
      ((tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk).toLinearMap) z = 0 := by
  letI : ∀ j' : Set.Ici i₀, Algebra (A i₀) (tail_ring_family (A := A) (i₀ := i₀) j') :=
    tail_ring_family_algebra_family (A := A) (f := f) (i₀ := i₀)
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  let tailLimit :=
    Ring.DirectLimit
      (tail_ring_family (A := A) (i₀ := i₀))
      (fun j' k' hjk ↦ tail_ring_transition (A := A) (f := f) (i₀ := i₀) j' k' hjk)
  letI : Algebra (A j.1) tailLimit :=
    (tail_stage_to_tail_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j).toRingHom.toAlgebra
  have hz_tail :
      _root_.stageTensorMap
          (A := A i₀)
          (R := tail_ring_family (A := A) (i₀ := i₀))
          (f := fun j' k' hjk ↦
            tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
          (X := C₀) j z =
        _root_.stageTensorMap
          (A := A i₀)
          (R := tail_ring_family (A := A) (i₀ := i₀))
          (f := fun j' k' hjk ↦
            tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
          (X := C₀) j 0 := by
    have hz_map :
        _root_.stageTensorMap
            (A := A i₀)
            (R := tail_ring_family (A := A) (i₀ := i₀))
            (f := fun j' k' hjk ↦
              tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
            (X := C₀) j z =
          tail_stageTensorMap (A := A) (f := f) (i₀ := i₀) (X := C₀) j z := by
      let ownerTailLimit :=
        Ring.DirectLimit
          (tail_ring_family (A := A) (i₀ := i₀))
          (fun j' k' hjk ↦
            ((tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk :
              A j'.1 →ₐ[A i₀] A k'.1) :
              A j'.1 →+* A k'.1))
      have hcod : ownerTailLimit = tailLimit := rfl
      cases hcod
      -- Proof comment: both tensor maps are induced by the same coefficient linear map from the
      -- chosen tail stage into the tail direct limit.
      unfold _root_.stageTensorMap tail_stageTensorMap
      simpa using
        congrArg
          (fun ψ :
            A j.1 ⊗[A i₀] C₀ →ₗ[A i₀] tailLimit ⊗[A i₀] C₀ ↦ ψ z)
          (congrArg (LinearMap.rTensor C₀)
            (tail_stage_to_tail_direct_limit_linearMap_eq (A := A) (f := f) (i₀ := i₀) j))
    have hzero_map :
        _root_.stageTensorMap
            (A := A i₀)
            (R := tail_ring_family (A := A) (i₀ := i₀))
            (f := fun j' k' hjk ↦
              tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
            (X := C₀) j 0 =
          tail_stageTensorMap (A := A) (f := f) (i₀ := i₀) (X := C₀) j 0 := by
      let ownerTailLimit :=
        Ring.DirectLimit
          (tail_ring_family (A := A) (i₀ := i₀))
          (fun j' k' hjk ↦
            ((tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk :
              A j'.1 →ₐ[A i₀] A k'.1) :
              A j'.1 →+* A k'.1))
      have hcod : ownerTailLimit = tailLimit := rfl
      cases hcod
      unfold _root_.stageTensorMap tail_stageTensorMap
      simpa using
        congrArg
          (fun ψ :
            A j.1 ⊗[A i₀] C₀ →ₗ[A i₀] tailLimit ⊗[A i₀] C₀ ↦ ψ 0)
          (congrArg (LinearMap.rTensor C₀)
            (tail_stage_to_tail_direct_limit_linearMap_eq (A := A) (f := f) (i₀ := i₀) j))
    calc
      _root_.stageTensorMap
          (A := A i₀)
          (R := tail_ring_family (A := A) (i₀ := i₀))
          (f := fun j' k' hjk ↦
            tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
          (X := C₀) j z =
        tail_stageTensorMap (A := A) (f := f) (i₀ := i₀) (X := C₀) j z := by
          exact hz_map
      _ =
        tail_stageTensorMap (A := A) (f := f) (i₀ := i₀) (X := C₀) j 0 :=
          tail_stageTensorMap_eq_zero (A := A) (f := f) (i₀ := i₀) (C₀ := C₀) j z hz
      _ =
        _root_.stageTensorMap
          (A := A i₀)
          (R := tail_ring_family (A := A) (i₀ := i₀))
          (f := fun j' k' hjk ↦
            tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
          (X := C₀) j 0 := by
            symm
            exact hzero_map
  -- Proof comment: apply the generic eventual-equality lemma to the tail system with the zero
  -- tensor as the comparison point.
  rcases _root_.tensor_eventually_eq
      (A := A i₀)
      (I := Set.Ici i₀)
      (R := tail_ring_family (A := A) (i₀ := i₀))
      (f := fun j' k' hjk ↦ tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
      C₀ hz_tail with ⟨k, hjk, hk⟩
  refine ⟨k, hjk, ?_⟩
  simpa using hk

/-- Helper for Lemma 10.168.4: once a tail-stage tensor becomes zero at one later stage, it stays
zero after every further enlargement of the stage. -/
theorem tail_zero_persists_to_later_stage
    {j j₁ k : Set.Ici i₀} (hjj₁ : j ≤ j₁) (hj₁k : j₁ ≤ k)
    (z :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      A j.1 ⊗[A i₀] C₀)
    (hz :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      letI : Algebra (A i₀) (A j₁.1) := (f i₀ j₁.1 j₁.2).toAlgebra
      LinearMap.rTensor C₀
        ((tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjj₁).toLinearMap) z = 0) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
    LinearMap.rTensor C₀
      ((tail_transition_algHom (A := A) (f := f) (i₀ := i₀) (le_trans hjj₁ hj₁k)).toLinearMap)
      z = 0 := by
  letI : ∀ j' : Set.Ici i₀, Algebra (A i₀) (tail_ring_family (A := A) (i₀ := i₀) j') :=
    tail_ring_family_algebra_family (A := A) (f := f) (i₀ := i₀)
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  letI : Algebra (A i₀) (A j₁.1) := (f i₀ j₁.1 j₁.2).toAlgebra
  letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
  letI :
      DirectedSystem (tail_ring_family (A := A) (i₀ := i₀))
        (fun j' k' hjk ↦
          ((tail_transition_family (A := A) (f := f) (i₀ := i₀) j' k' hjk :
            tail_ring_family (A := A) (i₀ := i₀) j' →ₐ[A i₀]
              tail_ring_family (A := A) (i₀ := i₀) k') :
            tail_ring_family (A := A) (i₀ := i₀) j' →+*
              tail_ring_family (A := A) (i₀ := i₀) k')) :=
    tail_transition_family_directedSystem (A := A) (f := f) (i₀ := i₀)
  -- Proof comment: apply the later transition map to the vanished tensor, then rewrite the
  -- composite transition by functoriality of `LinearMap.rTensor`.
  calc
    LinearMap.rTensor C₀
        ((tail_transition_algHom (A := A) (f := f) (i₀ := i₀) (le_trans hjj₁ hj₁k)).toLinearMap)
        z =
      LinearMap.rTensor C₀
        ((tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hj₁k).toLinearMap)
        (LinearMap.rTensor C₀
          ((tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjj₁).toLinearMap) z) := by
            symm
            simpa using
              (rTensor_transition_apply
                (A := A i₀)
                (R := tail_ring_family (A := A) (i₀ := i₀))
                (f := fun j' k' hjk ↦
                  tail_transition_family (A := A) (f := f) (i₀ := i₀) j' k' hjk)
                C₀ hjj₁ hj₁k z)
    _ =
      LinearMap.rTensor C₀
        ((tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hj₁k).toLinearMap) 0 := by
          rw [hz]
    _ = 0 := by simp

/-- Helper for Lemma 10.168.4: package the tail zero-family descent step in a small namespace so
the target file can reuse the source-faithful generator-defect argument without elaborating the
raw tail-system `stageTensorMap` there. -/
theorem tensor_equalities_descend_zero_family
    (s : Finset C₀) (j : Set.Ici i₀)
    (z :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      C₀ → A j.1 ⊗[A i₀] C₀)
    (hz :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      ∀ x ∈ s,
        (Algebra.TensorProduct.map
          (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
          (AlgHom.id (A i₀) C₀)) (z x) = 0) :
    letI : ∀ j' : Set.Ici i₀, Algebra (A i₀) (tail_ring_family (A := A) (i₀ := i₀) j') :=
      tail_ring_family_algebra_family (A := A) (f := f) (i₀ := i₀)
    ∃ k : Set.Ici i₀, ∃ hjk : j ≤ k,
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
      ∀ x ∈ s,
        LinearMap.rTensor C₀
          ((tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk).toLinearMap) (z x) = 0 := by
  classical
  letI : ∀ j' : Set.Ici i₀, Algebra (A i₀) (tail_ring_family (A := A) (i₀ := i₀) j') :=
    tail_ring_family_algebra_family (A := A) (f := f) (i₀ := i₀)
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  induction s using Finset.induction_on generalizing j with
  | empty =>
      -- Proof comment: with no defects to kill, the current tail stage already works.
      refine ⟨j, le_rfl, ?_⟩
      intro x hx
      exact False.elim (Finset.notMem_empty x hx)
  | @insert a s ha hs =>
      have hza :
          (Algebra.TensorProduct.map
            (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
            (AlgHom.id (A i₀) C₀)) (z a) = 0 :=
        hz a (Finset.mem_insert_self a s)
      have hzs :
          ∀ x ∈ s,
            (Algebra.TensorProduct.map
              (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
              (AlgHom.id (A i₀) C₀)) (z x) = 0 := by
        intro x hx
        exact hz x (Finset.mem_insert_of_mem hx)
      rcases tail_tensor_eventually_zero
          (A := A) (f := f) (i₀ := i₀) (C₀ := C₀) j (z a) hza with ⟨j₁, hjj₁, hj₁⟩
      rcases hs j z hzs with ⟨j₂, hjj₂, hj₂⟩
      rcases exists_ge_ge j₁ j₂ with ⟨k, hj₁k, hj₂k⟩
      let hjk : j ≤ k := le_trans hjj₁ hj₁k
      have hnew :
          LinearMap.rTensor C₀
            ((tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk).toLinearMap) (z a) = 0 :=
        tail_zero_persists_to_later_stage
          (A := A) (f := f) (i₀ := i₀) (C₀ := C₀) hjj₁ hj₁k (z a) hj₁
      refine ⟨k, hjk, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · -- Proof comment: enlarge the single descended zero for the new defect to the common
        -- upper tail stage.
        simpa using hnew
      · -- Proof comment: enlarge the recursive common-stage vanishing for the older defects to
        -- the same upper tail stage, then identify the two proofs of `j ≤ k`.
        have hkx :=
          tail_zero_persists_to_later_stage
            (A := A) (f := f) (i₀ := i₀) (C₀ := C₀) hjj₂ hj₂k (z x) (hj₂ x hx)
        have hproof : le_trans hjj₂ hj₂k = hjk := Subsingleton.elim _ _
        simpa [hjk, hproof] using hkx

end

end Lemma10_168_4TailZeroFamilyDescent
