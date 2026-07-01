import Mathlib
import stacks_project.Chap10.Lemma_10_127_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

noncomputable section

section

/-
Domain sampling:
* Primary domain: descent of algebra maps along filtered/direct-ring colimits via tensor-product
  base change.
* Relevant owner declarations inspected:
  - `Algebra.TensorProduct.map`
  - `Ring.DirectLimit.of`
  - `finite_type_surjectivity_descends` from `Lemma_10_127_7`
  - `DirectedFiniteTypeHomApproximation.stageBaseChange` from `Lemma_10_127_14`
* Best owner abstraction:
  - `source-facing`: the directed-ring-colimit descent theorem below
  - `core/canonical`: tensor-product base change via `Algebra.TensorProduct.map` together with
    the direct-limit ring `Ring.DirectLimit`
  - `bridge/view`: the chosen directed-system presentation of that filtered-colimit situation
* Primitive vs. derived:
  - primitive data: the directed system `A`, transition maps `f`, the distinguished stage `i₀`,
    and the algebra map `φ₀`
  - derived API: the stagewise and direct-limit base-change maps expressed directly by
    `Algebra.TensorProduct.map`
-/

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
variable (A : I → Type u) [∀ i, CommRing (A i)]
variable (f : ∀ i j, i ≤ j → A i →+* A j)
variable [DirectedSystem A (fun i j hij ↦ f i j hij)]
variable {i₀ : I}
variable {B₀ C₀ : Type w} [CommRing B₀] [CommRing C₀]
variable [Algebra (A i₀) B₀] [Algebra (A i₀) C₀]
local notation "A∞" => Ring.DirectLimit A (fun i j hij ↦ f i j hij)

/-- Helper for Lemma 10.168.4: if finitely many algebra generators of `C₀` already have
preimages under the stagewise tensor-base-change map, then that tensor map is surjective. -/
lemma tensor_map_surjective_of_generator_preimages
    {R' : Type u} [CommRing R'] [Algebra (A i₀) R']
    (u : B₀ →ₐ[A i₀] C₀)
    (s : Finset C₀)
    (hs :
      letI : Algebra B₀ C₀ := u.toRingHom.toAlgebra
      Algebra.adjoin B₀ (s : Set C₀) = ⊤)
    (hpre :
      ∀ x ∈ s, ∃ b : B₀ ⊗[A i₀] R',
        (Algebra.TensorProduct.map u (AlgHom.id (A i₀) R')) b = x ⊗ₜ[A i₀] (1 : R')) :
    Function.Surjective (Algebra.TensorProduct.map u (AlgHom.id (A i₀) R')) := by
  letI : Algebra B₀ C₀ := u.toRingHom.toAlgebra
  let S := B₀ ⊗[A i₀] R'
  let T := S ⊗[B₀] C₀
  letI : Algebra S T := Algebra.TensorProduct.leftAlgebra
  let α : S →ₐ[S] T := Algebra.ofId S T
  let e :=
    (Algebra.TensorProduct.comm (R := B₀) (A := S) (B := C₀)).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange
        (R := A i₀) (S := B₀) (T := C₀) (A := C₀) (B := R')).toRingEquiv
  let ψ := Algebra.TensorProduct.map u (AlgHom.id (A i₀) R')
  have he : e.toRingHom.comp α.toRingHom = ψ.toRingHom := by
    -- Proof comment: the literal base change along `B₀ → B₀ ⊗[A₀] R'` matches the tensor map
    -- in the statement after the standard `comm` and `cancelBaseChange` transport.
    apply RingHom.ext
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp [α, ψ]
    · intro b a
      change
        (Algebra.TensorProduct.cancelBaseChange
          (R := A i₀) (S := B₀) (T := C₀) (A := C₀) (B := R'))
          ((Algebra.TensorProduct.comm (R := B₀) (A := S) (B := C₀))
            ((((b ⊗ₜ[A i₀] a) : S) ⊗ₜ[B₀] (1 : C₀)))) =
          u b ⊗ₜ[A i₀] a
      simp [S, Algebra.smul_def]
      simpa using
        (show (algebraMap B₀ C₀) b ⊗ₜ[A i₀] a = u b ⊗ₜ[A i₀] a from rfl)
    · intro z₁ z₂ hz₁ hz₂
      rw [RingHom.map_add, RingHom.map_add, hz₁, hz₂]
  have hincludeRight (x : C₀) :
      e (Algebra.TensorProduct.includeRight (R := B₀) (A := S) (B := C₀) x) =
        x ⊗ₜ[A i₀] (1 : R') := by
    -- Proof comment: the transport sends the right tensor generator `1 ⊗ x` to the target pure
    -- tensor `x ⊗ 1`.
    change
      (Algebra.TensorProduct.cancelBaseChange
        (R := A i₀) (S := B₀) (T := C₀) (A := C₀) (B := R'))
        ((Algebra.TensorProduct.comm (R := B₀) (A := S) (B := C₀))
          (((1 : S) ⊗ₜ[B₀] x))) =
        x ⊗ₜ[A i₀] (1 : R')
    rw [Algebra.TensorProduct.comm_tmul]
    change
      (Algebra.TensorProduct.cancelBaseChange
        (R := A i₀) (S := B₀) (T := C₀) (A := C₀) (B := R'))
        (x ⊗ₜ[B₀] (((1 : B₀) ⊗ₜ[A i₀] (1 : R')) : S)) =
        x ⊗ₜ[A i₀] (1 : R')
    simpa [S, Algebra.smul_def] using
      (Algebra.TensorProduct.cancelBaseChange_tmul
        (R := A i₀) (S := B₀) (T := C₀) (A := C₀) (B := R')
        x (1 : B₀) (1 : R'))
  have hgen :
      Algebra.adjoin S (((1 : S) ⊗ₜ[B₀] ·) '' (s : Set C₀)) = ⊤ := by
    -- Proof comment: the same finite generating set still generates after base change.
    simpa [S] using
      Algebra.TensorProduct.adjoin_one_tmul_image_eq_top (A := S) (s := (s : Set C₀)) hs
  have hmem :
      ∀ x ∈ s,
        Algebra.TensorProduct.includeRight (R := B₀) (A := S) (B := C₀) x ∈ α.range := by
    -- Proof comment: each chosen generator lies in the literal base-change image because the
    -- prescribed tensor preimage maps to `x ⊗ 1`.
    intro x hx
    rcases hpre x hx with ⟨b, hb⟩
    refine (AlgHom.mem_range α).2 ⟨b, ?_⟩
    apply e.injective
    calc
      e (α b) = ψ b := by
        simpa [α] using congrArg (fun g : S →+* (C₀ ⊗[A i₀] R') ↦ g b) he
      _ = x ⊗ₜ[A i₀] (1 : R') := hb
      _ = e (Algebra.TensorProduct.includeRight (R := B₀) (A := S) (B := C₀) x) :=
        (hincludeRight x).symm
  have hrange : α.range = ⊤ := by
    -- Proof comment: the range is an `S`-subalgebra containing the transported generators, so it
    -- must be the whole tensor product.
    apply top_unique
    rw [← hgen]
    exact Algebra.adjoin_le_iff.mpr fun y hy ↦ by
      rcases hy with ⟨x, hx, rfl⟩
      simpa [S] using hmem x hx
  have hαsurj : Function.Surjective α := (AlgHom.range_eq_top α).mp hrange
  intro z
  obtain ⟨t, rfl⟩ := e.surjective z
  obtain ⟨b, hb⟩ := hαsurj t
  refine ⟨b, ?_⟩
  calc
    ψ b = e (α b) := by
      symm
      simpa [α] using congrArg (fun g : S →+* (C₀ ⊗[A i₀] R') ↦ g b) he
    _ = e t := by rw [hb]

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
            simpa [full_stage_to_tail_directLimit, jj, RingHom.comp_apply] using
              (Ring.DirectLimit.of_f
                (G := fun j : Set.Ici i₀ ↦ A j.1)
                (f := fun j k hij ↦ f j.1 k.1 hij)
                (i := jj) (j := k) (hij := hjk)
                (x := f j jj.1 (le_tail_upper_bound_left (i₀ := i₀) j) (f i j hij x))).symm
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
      simpa [full_stage_to_tail_directLimit, ji, RingHom.comp_apply] using
        (Ring.DirectLimit.of_f
          (G := fun j : Set.Ici i₀ ↦ A j.1)
          (f := fun j k hij ↦ f j.1 k.1 hij)
          (i := ji) (j := k) (hij := hik)
          (x := f i ji.1 (le_tail_upper_bound_left (i₀ := i₀) i) x))

/-- Helper for Lemma 10.168.4: the full direct limit maps canonically to the direct limit of the
tail above `i₀`. -/
noncomputable def full_directLimit_to_tail :
    A∞ →+* Ring.DirectLimit (fun j : Set.Ici i₀ ↦ A j.1) (fun j k hij ↦ f j.1 k.1 hij) :=
  Ring.DirectLimit.lift A (fun i j hij ↦ f i j hij)
    (Ring.DirectLimit (fun j : Set.Ici i₀ ↦ A j.1) (fun j k hij ↦ f j.1 k.1 hij))
    (fun i ↦ full_stage_to_tail_directLimit (A := A) (f := f) (i₀ := i₀) i)
    (fun _ _ hij x ↦
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
    (fun _ _ hjk x ↦ tail_directLimit_to_full_compatible (A := A) (f := f) (i₀ := i₀) hjk x)

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

/-- Helper for Lemma 10.168.4: transporting a tensor to a later tail stage does not change its
image in the ambient direct-limit tensor product. -/
theorem tail_tensor_map_transition
    {X : Type*} [CommRing X] [Algebra (A i₀) X]
    {j k : Set.Ici i₀} (hjk : j ≤ k)
    (z :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      A j.1 ⊗[A i₀] X) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
    let τjk : (A j.1 ⊗[A i₀] X) →ₐ[A i₀] (A k.1 ⊗[A i₀] X) :=
      Algebra.TensorProduct.map
        (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
        (AlgHom.id (A i₀) X)
    let κj : (A j.1 ⊗[A i₀] X) →ₐ[A i₀] (A∞ ⊗[A i₀] X) :=
      Algebra.TensorProduct.map
        (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
        (AlgHom.id (A i₀) X)
    let κk : (A k.1 ⊗[A i₀] X) →ₐ[A i₀] (A∞ ⊗[A i₀] X) :=
      Algebra.TensorProduct.map
        (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) k)
        (AlgHom.id (A i₀) X)
    κk (τjk z) = κj z := by
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
  let τjk : (A j.1 ⊗[A i₀] X) →ₐ[A i₀] (A k.1 ⊗[A i₀] X) :=
    Algebra.TensorProduct.map
      (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
      (AlgHom.id (A i₀) X)
  let κj : (A j.1 ⊗[A i₀] X) →ₐ[A i₀] (A∞ ⊗[A i₀] X) :=
    Algebra.TensorProduct.map
      (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
      (AlgHom.id (A i₀) X)
  let κk : (A k.1 ⊗[A i₀] X) →ₐ[A i₀] (A∞ ⊗[A i₀] X) :=
    Algebra.TensorProduct.map
      (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) k)
      (AlgHom.id (A i₀) X)
  -- Proof comment: on pure tensors this is exactly `Ring.DirectLimit.of_f`, and tensor induction
  -- extends the compatibility to all tensors.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro r x
    change
      Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) k.1 (f j.1 k.1 hjk r) ⊗ₜ[A i₀] x =
        Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) j.1 r ⊗ₜ[A i₀] x
    exact congrArg (fun s : A∞ ↦ s ⊗ₜ[A i₀] x)
      (Ring.DirectLimit.of_f (G := A) (f := fun i j hij ↦ f i j hij) hjk r)
  · intro z₁ z₂ hz₁ hz₂
    simp [hz₁, hz₂]

/-- Helper for Lemma 10.168.4: every element of the ambient direct limit already comes from some
stage lying in the tail above `i₀`. -/
theorem directLimit_exists_tail_repr (z : A∞) :
    ∃ (j : Set.Ici i₀) (x : A j.1),
      Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) j.1 x = z := by
  letI : Nonempty I := ⟨i₀⟩
  rcases Ring.DirectLimit.exists_of (G := A) (f := fun i j hij ↦ f i j hij) z with ⟨i, x, rfl⟩
  let j : Set.Ici i₀ :=
    ⟨tail_upper_bound i, le_tail_upper_bound_right i⟩
  refine ⟨j, f i j.1 (le_tail_upper_bound_left i) x, ?_⟩
  -- Proof comment: enlarging a stage representative to a later tail stage does not change its
  -- image in the direct limit.
  exact Ring.DirectLimit.of_f (G := A) (f := fun i j hij ↦ f i j hij)
    (le_tail_upper_bound_left i) x

/-- Helper for Lemma 10.168.4: every tensor over the ambient direct-limit ring already comes from
some tensor over one tail stage above `i₀`. -/
theorem directLimit_tensor_exists_tail_repr
    {X : Type*} [CommRing X] [Algebra (A i₀) X]
    (z : A∞ ⊗[A i₀] X) :
    ∃ j : Set.Ici i₀,
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      ∃ zj : A j.1 ⊗[A i₀] X,
      (Algebra.TensorProduct.map
        (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
        (AlgHom.id (A i₀) X)) zj = z := by
  -- Proof comment: descend a pure tensor by descending its direct-limit coefficient to one tail
  -- stage, then merge two stagewise lifts by moving both to a common upper bound in the tail.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · refine ⟨⟨i₀, le_rfl⟩, 0, ?_⟩
    simp
  · intro r x
    obtain ⟨j, rj, hrj⟩ := directLimit_exists_tail_repr (A := A) (f := f) (i₀ := i₀) r
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    refine ⟨j, rj ⊗ₜ[A i₀] x, ?_⟩
    change Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) j.1 rj ⊗ₜ[A i₀] x = r ⊗ₜ[A i₀] x
    exact congrArg (fun s : A∞ ↦ s ⊗ₜ[A i₀] x) hrj
  · intro z₁ z₂ hz₁ hz₂
    obtain ⟨j₁, zj₁, hzj₁⟩ := hz₁
    obtain ⟨j₂, zj₂, hzj₂⟩ := hz₂
    obtain ⟨k, hj₁k, hj₂k⟩ := exists_ge_ge j₁.1 j₂.1
    let j : Set.Ici i₀ := ⟨k, le_trans j₁.2 hj₁k⟩
    letI : Algebra (A i₀) (A j₁.1) := (f i₀ j₁.1 j₁.2).toAlgebra
    letI : Algebra (A i₀) (A j₂.1) := (f i₀ j₂.1 j₂.2).toAlgebra
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    let τ₁ :
        (A j₁.1 ⊗[A i₀] X) →ₐ[A i₀] (A j.1 ⊗[A i₀] X) :=
      Algebra.TensorProduct.map
        (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hj₁k)
        (AlgHom.id (A i₀) X)
    let τ₂ :
        (A j₂.1 ⊗[A i₀] X) →ₐ[A i₀] (A j.1 ⊗[A i₀] X) :=
      Algebra.TensorProduct.map
        (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hj₂k)
        (AlgHom.id (A i₀) X)
    refine ⟨j, τ₁ zj₁ + τ₂ zj₂, ?_⟩
    calc
      (Algebra.TensorProduct.map
          (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
          (AlgHom.id (A i₀) X)) (τ₁ zj₁ + τ₂ zj₂)
          =
        (Algebra.TensorProduct.map
          (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
          (AlgHom.id (A i₀) X)) (τ₁ zj₁) +
          (Algebra.TensorProduct.map
            (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
            (AlgHom.id (A i₀) X)) (τ₂ zj₂) := by
              simp
      _ =
        (Algebra.TensorProduct.map
          (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j₁)
          (AlgHom.id (A i₀) X)) zj₁ +
          (Algebra.TensorProduct.map
            (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j₂)
            (AlgHom.id (A i₀) X)) zj₂ := by
              rw [tail_tensor_map_transition (A := A) (f := f) (i₀ := i₀) hj₁k zj₁]
              rw [tail_tensor_map_transition (A := A) (f := f) (i₀ := i₀) hj₂k zj₂]
      _ = z₁ + z₂ := by rw [hzj₁, hzj₂]

/-- Helper for Lemma 10.168.4: finitely many tensors over the ambient direct-limit ring admit
simultaneous lifts to one common tail stage above `i₀`. -/
theorem tail_tensor_lifts_from_stage_on_finset
    {α : Type*}
    {X : Type*} [CommRing X] [Algebra (A i₀) X]
    (s : Finset α) (z : α → A∞ ⊗[A i₀] X) :
    ∃ j : Set.Ici i₀,
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      ∃ zj : α → A j.1 ⊗[A i₀] X,
      ∀ a ∈ s,
        (Algebra.TensorProduct.map
          (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
          (AlgHom.id (A i₀) X)) (zj a) = z a := by
  classical
  refine Finset.induction_on s ?_ ?_
  · refine ⟨⟨i₀, le_rfl⟩, fun _ ↦ 0, ?_⟩
    intro a ha
    exact False.elim (Finset.notMem_empty a ha)
  · intro a s ha hs
    obtain ⟨j₁, zj₁, hzj₁⟩ :=
      directLimit_tensor_exists_tail_repr (A := A) (f := f) (i₀ := i₀) (z a)
    obtain ⟨j₂, zj₂, hzj₂⟩ := hs
    obtain ⟨k, hj₁k, hj₂k⟩ := exists_ge_ge j₁.1 j₂.1
    let j : Set.Ici i₀ := ⟨k, le_trans j₁.2 hj₁k⟩
    letI : Algebra (A i₀) (A j₁.1) := (f i₀ j₁.1 j₁.2).toAlgebra
    letI : Algebra (A i₀) (A j₂.1) := (f i₀ j₂.1 j₂.2).toAlgebra
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    let τ₁ :
        (A j₁.1 ⊗[A i₀] X) →ₐ[A i₀] (A j.1 ⊗[A i₀] X) :=
      Algebra.TensorProduct.map
        (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hj₁k)
        (AlgHom.id (A i₀) X)
    let τ₂ :
        (A j₂.1 ⊗[A i₀] X) →ₐ[A i₀] (A j.1 ⊗[A i₀] X) :=
      Algebra.TensorProduct.map
        (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hj₂k)
        (AlgHom.id (A i₀) X)
    refine ⟨j, fun b ↦ if hba : b = a then τ₁ zj₁ else τ₂ (zj₂ b), ?_⟩
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb'
    ·
      have hif :
          (fun b_1 ↦ if hba : b_1 = b then τ₁ zj₁ else τ₂ (zj₂ b_1)) b = τ₁ zj₁ := by
        simp
      rw [hif]
      calc
        (Algebra.TensorProduct.map
            (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
            (AlgHom.id (A i₀) X)) (τ₁ zj₁)
            =
          (Algebra.TensorProduct.map
            (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j₁)
            (AlgHom.id (A i₀) X)) zj₁ := by
              rw [tail_tensor_map_transition (A := A) (f := f) (i₀ := i₀) hj₁k zj₁]
        _ = z b := hzj₁
    · have hba : b ≠ a := by
        intro hba
        apply ha
        simpa [hba] using hb'
      simp only [dif_neg hba]
      calc
        (Algebra.TensorProduct.map
            (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
            (AlgHom.id (A i₀) X)) (τ₂ (zj₂ b))
            =
          (Algebra.TensorProduct.map
            (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j₂)
            (AlgHom.id (A i₀) X)) (zj₂ b) := by
              rw [tail_tensor_map_transition (A := A) (f := f) (i₀ := i₀) hj₂k (zj₂ b)]
        _ = z b := hzj₂ b hb'

/-- Helper for Lemma 10.168.4: the cofinal tail above `i₀` inherits the directed-order instance
needed by the imported finite-family tensor-descent theorem. -/
local instance tail_isDirectedOrder : IsDirectedOrder (Set.Ici i₀) :=
  tail_index_isDirected (i₀ := i₀)

/-- Helper for Lemma 10.168.4: the tail system reindexes the original directed system over
`Set.Ici i₀`. -/
abbrev tail_ring_family (j : Set.Ici i₀) : Type u :=
  A j.1

/-- Helper for Lemma 10.168.4: the reindexed tail family inherits the canonical `A i₀`-algebra
structure from the corresponding tail stage. -/
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
  (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j.1 →+* A k.1)

/-- Helper for Lemma 10.168.4: the tail transition maps form a directed system of rings. -/
local instance tail_directedSystem :
    DirectedSystem (tail_ring_family (A := A) (i₀ := i₀))
      (fun j k hjk ↦
        (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j.1 →+* A k.1)) where
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

/-- Helper for Lemma 10.168.4: the owner theorem's tail-system specialization uses the standard
arbitrary-stage `A i₀`-algebra structure on the tail direct limit. -/
@[reducible]
noncomputable def owner_tail_directLimitAlgebra :
    Algebra (A i₀)
      (Ring.DirectLimit
        (tail_ring_family (A := A) (i₀ := i₀))
        (fun j k hjk ↦
          (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j.1 →+* A k.1))) :=
  let j : Set.Ici i₀ := Classical.arbitrary (Set.Ici i₀)
  letI : Algebra (A i₀) (A j.1) := tail_ring_familyAlgebra (A := A) (f := f) (i₀ := i₀) j
  ((Ring.DirectLimit.of
      (tail_ring_family (A := A) (i₀ := i₀))
      (fun j' k' hjk ↦
        (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j'.1 →+* A k'.1))
      j).comp
    (algebraMap (A i₀) (A j.1))).toAlgebra

/-- Helper for Lemma 10.168.4: the owner theorem's arbitrary-stage algebra map to the tail direct
limit agrees with the canonical one coming from the base tail stage `⟨i₀, le_rfl⟩`. -/
theorem owner_tail_directLimit_algebraMap_eq (a : A i₀) :
    let tailLimit :=
      Ring.DirectLimit
        (tail_ring_family (A := A) (i₀ := i₀))
        (fun j k hjk ↦
          (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j.1 →+* A k.1))
    letI : Algebra (A i₀) tailLimit := owner_tail_directLimitAlgebra (A := A) (f := f) (i₀ := i₀)
    algebraMap (A i₀) tailLimit a =
      Ring.DirectLimit.of
        (tail_ring_family (A := A) (i₀ := i₀))
        (fun j k hjk ↦
          (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j.1 →+* A k.1))
        ⟨i₀, le_rfl⟩ a := by
  classical
  let tailLimit :=
    Ring.DirectLimit
      (tail_ring_family (A := A) (i₀ := i₀))
      (fun j k hjk ↦
        (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j.1 →+* A k.1))
  let j : Set.Ici i₀ := Classical.arbitrary (Set.Ici i₀)
  letI : Algebra (A i₀) tailLimit := owner_tail_directLimitAlgebra (A := A) (f := f) (i₀ := i₀)
  obtain ⟨k, hjk, h0k⟩ := exists_ge_ge j ⟨i₀, le_rfl⟩
  change
    Ring.DirectLimit.of
        (tail_ring_family (A := A) (i₀ := i₀))
        (fun j' k' hjk ↦
          (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j'.1 →+* A k'.1))
        j ((f i₀ j.1 j.2) a) =
      Ring.DirectLimit.of
        (tail_ring_family (A := A) (i₀ := i₀))
        (fun j' k' hjk ↦
          (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j'.1 →+* A k'.1))
        ⟨i₀, le_rfl⟩ a
  calc
    Ring.DirectLimit.of
        (tail_ring_family (A := A) (i₀ := i₀))
        (fun j' k' hjk ↦
          (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j'.1 →+* A k'.1))
        j ((f i₀ j.1 j.2) a) =
      Ring.DirectLimit.of
        (tail_ring_family (A := A) (i₀ := i₀))
        (fun j' k' hjk ↦
          (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j'.1 →+* A k'.1))
        k (f j.1 k.1 hjk ((f i₀ j.1 j.2) a)) := by
          symm
          exact Ring.DirectLimit.of_f
            (G := tail_ring_family (A := A) (i₀ := i₀))
            (f := fun j' k' hjk ↦
              (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j'.1 →+* A k'.1))
            (i := j) (j := k) (hij := hjk) (x := (f i₀ j.1 j.2) a)
    _ =
      Ring.DirectLimit.of
        (tail_ring_family (A := A) (i₀ := i₀))
        (fun j' k' hjk ↦
          (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j'.1 →+* A k'.1))
        k (f i₀ k.1 (le_trans j.2 hjk) a) := by
          rw [tail_stage_transition_commutes (A := A) (f := f) (i₀ := i₀) hjk]
    _ =
      Ring.DirectLimit.of
        (tail_ring_family (A := A) (i₀ := i₀))
        (fun j' k' hjk ↦
          (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j'.1 →+* A k'.1))
        k (f i₀ k.1 h0k a) := by
          have hproof : le_trans j.2 hjk = h0k := Subsingleton.elim _ _
          cases hproof
          rfl
    _ =
      Ring.DirectLimit.of
        (tail_ring_family (A := A) (i₀ := i₀))
        (fun j' k' hjk ↦
          (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j'.1 →+* A k'.1))
        ⟨i₀, le_rfl⟩ a := by
          exact Ring.DirectLimit.of_f
            (G := tail_ring_family (A := A) (i₀ := i₀))
            (f := fun j' k' hjk ↦
              (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j'.1 →+* A k'.1))
            (i := ⟨i₀, le_rfl⟩) (j := k) (hij := h0k) (x := a)

/-- Helper for Lemma 10.168.4: the direct limit of the tail above `i₀` canonically identifies
with the original direct limit as an `A i₀`-algebra. -/
noncomputable def tail_directLimitAlgEquivToFull :
    Ring.DirectLimit
        (tail_ring_family (A := A) (i₀ := i₀))
        (fun j k hjk ↦
          (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j.1 →+* A k.1))
        ≃ₐ[A i₀] A∞ where
  __ := tail_directLimitIso (A := A) (f := f) (i₀ := i₀) (B := A∞) (RingEquiv.refl A∞)
  commutes' a := by
    -- Proof comment: both algebra maps are represented by the distinguished base tail stage
    -- `⟨i₀, le_rfl⟩`.
    change
      tail_directLimitIso (A := A) (f := f) (i₀ := i₀) (B := A∞) (RingEquiv.refl A∞)
          (Ring.DirectLimit.of
            (tail_ring_family (A := A) (i₀ := i₀))
            (fun j k hjk ↦
              (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j.1 →+* A k.1))
            ⟨i₀, le_rfl⟩ a) =
        Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀ a
    rfl

/-- Helper for Lemma 10.168.4: transporting the owner theorem's tail direct-limit algebra
structure to the ambient direct limit gives the same tail/full equivalence. -/
noncomputable def owner_tail_directLimitAlgEquivToFull :
    let tailLimit :=
      Ring.DirectLimit
        (tail_ring_family (A := A) (i₀ := i₀))
        (fun j k hjk ↦
          (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j.1 →+* A k.1))
    letI : Algebra (A i₀) tailLimit := owner_tail_directLimitAlgebra (A := A) (f := f) (i₀ := i₀)
    tailLimit ≃ₐ[A i₀] A∞ :=
  let tailLimit :=
    Ring.DirectLimit
      (tail_ring_family (A := A) (i₀ := i₀))
      (fun j k hjk ↦
        (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j.1 →+* A k.1))
  letI : Algebra (A i₀) tailLimit := owner_tail_directLimitAlgebra (A := A) (f := f) (i₀ := i₀)
  { __ := tail_directLimitIso (A := A) (f := f) (i₀ := i₀) (B := A∞) (RingEquiv.refl A∞)
    commutes' := fun a ↦ by
      rw [owner_tail_directLimit_algebraMap_eq (A := A) (f := f) (i₀ := i₀)]
      rfl }

/-- Helper for Lemma 10.168.4: the transported owner-style tail/full equivalence still sends a
tail stage class to the corresponding ambient direct-limit class. -/
theorem owner_tail_directLimitAlgEquivToFull_of (j : Set.Ici i₀) (x : A j.1) :
    let tailLimit :=
      Ring.DirectLimit
        (tail_ring_family (A := A) (i₀ := i₀))
        (fun j' k' hjk ↦
          (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j'.1 →+* A k'.1))
    letI : Algebra (A i₀) tailLimit := owner_tail_directLimitAlgebra (A := A) (f := f) (i₀ := i₀)
    owner_tail_directLimitAlgEquivToFull (A := A) (f := f) (i₀ := i₀)
        (Ring.DirectLimit.of
          (tail_ring_family (A := A) (i₀ := i₀))
          (fun j' k' hjk ↦
            (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j'.1 →+* A k'.1))
          j x) =
      Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) j.1 x := by
  rfl

/-- Helper for Lemma 10.168.4: the tail/full colimit equivalence sends a tail stage class to the
corresponding class in the original direct limit. -/
theorem tail_directLimitAlgEquivToFull_of (j : Set.Ici i₀) (x : A j.1) :
    tail_directLimitAlgEquivToFull (A := A) (f := f) (i₀ := i₀)
        (Ring.DirectLimit.of
          (tail_ring_family (A := A) (i₀ := i₀))
          (fun j' k' hjk ↦
            (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j'.1 →+* A k'.1))
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
        (fun j' k' hjk ↦
          (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j'.1 →+* A k'.1))
        j ((f i₀ j.1 j.2) a) =
      algebraMap (A i₀)
        (Ring.DirectLimit
          (tail_ring_family (A := A) (i₀ := i₀))
          (fun j' k' hjk ↦
            (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j'.1 →+* A k'.1))) a := by
  change
    Ring.DirectLimit.of
        (tail_ring_family (A := A) (i₀ := i₀))
        (fun j' k' hjk ↦
          (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j'.1 →+* A k'.1))
        j ((f i₀ j.1 j.2) a) =
      Ring.DirectLimit.of
        (tail_ring_family (A := A) (i₀ := i₀))
        (fun j' k' hjk ↦
          (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j'.1 →+* A k'.1))
        ⟨i₀, le_rfl⟩ a
  simpa using
    (Ring.DirectLimit.of_f
      (G := tail_ring_family (A := A) (i₀ := i₀))
      (f := fun j' k' hjk ↦
        (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j'.1 →+* A k'.1))
      (i := ⟨i₀, le_rfl⟩) (j := j) (hij := j.2) (x := a))

/-- Helper for Lemma 10.168.4: the canonical map from a tail stage to the tail direct limit is an
algebra homomorphism over the distinguished base stage. -/
noncomputable abbrev tail_stage_to_tail_direct_limit_algHom
    (j : Set.Ici i₀) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    A j.1 →ₐ[A i₀]
      Ring.DirectLimit
        (tail_ring_family (A := A) (i₀ := i₀))
        (fun j' k' hjk ↦
          (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j'.1 →+* A k'.1)) :=
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  { toRingHom :=
      Ring.DirectLimit.of
        (tail_ring_family (A := A) (i₀ := i₀))
        (fun j' k' hjk ↦
          (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j'.1 →+* A k'.1))
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
          (fun j' k' hjk ↦
            (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j'.1 →+* A k'.1)))
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
  -- Proof comment: both linear maps are induced by the same canonical ring homomorphism from the
  -- chosen tail stage into the tail direct limit.
  exact LinearMap.ext fun a ↦ rfl

/-- Helper for Lemma 10.168.4: transporting the owner `stageTensorMap` for the tail system along
the tail/full direct-limit equivalence recovers the explicit tensor map into the ambient direct
limit. -/
theorem owner_stageTensorMap_to_full
    (j : Set.Ici i₀)
    (z :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      A j.1 ⊗[A i₀] C₀) :
    letI : ∀ j' : Set.Ici i₀, Algebra (A i₀) (tail_ring_family (A := A) (i₀ := i₀) j') :=
      tail_ring_family_algebra_family (A := A) (f := f) (i₀ := i₀)
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    let tailLimit :=
      Ring.DirectLimit
        (tail_ring_family (A := A) (i₀ := i₀))
        (fun j' k' hjk ↦
          (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j'.1 →+* A k'.1))
    letI : Algebra (A i₀) tailLimit := owner_tail_directLimitAlgebra (A := A) (f := f) (i₀ := i₀)
    (Algebra.TensorProduct.congr
      (owner_tail_directLimitAlgEquivToFull (A := A) (f := f) (i₀ := i₀))
      (AlgEquiv.refl : C₀ ≃ₐ[A i₀] C₀))
      (_root_.stageTensorMap
        (A := A i₀)
        (R := tail_ring_family (A := A) (i₀ := i₀))
        (f := fun _ _ hjk ↦
          tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
        (X := C₀) j z) =
      (Algebra.TensorProduct.map
        (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
        (AlgHom.id (A i₀) C₀)) z := by
  letI : ∀ j' : Set.Ici i₀, Algebra (A i₀) (tail_ring_family (A := A) (i₀ := i₀) j') :=
    tail_ring_family_algebra_family (A := A) (f := f) (i₀ := i₀)
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  let tailLimit :=
    Ring.DirectLimit
      (tail_ring_family (A := A) (i₀ := i₀))
      (fun j' k' hjk ↦
        (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j'.1 →+* A k'.1))
  letI : Algebra (A i₀) tailLimit := owner_tail_directLimitAlgebra (A := A) (f := f) (i₀ := i₀)
  let e := owner_tail_directLimitAlgEquivToFull (A := A) (f := f) (i₀ := i₀)
  -- Proof comment: on pure tensors the owner `stageTensorMap` uses the canonical stage class in
  -- the tail direct limit, and the tail/full equivalence sends that class to the ambient one.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simpa using (Algebra.TensorProduct.congr e (AlgEquiv.refl : C₀ ≃ₐ[A i₀] C₀)).map_zero
  · intro r x
    simpa [e, _root_.stageTensorMap] using
      congrArg (fun s : A∞ ↦ s ⊗ₜ[A i₀] x)
        (owner_tail_directLimitAlgEquivToFull_of (A := A) (f := f) (i₀ := i₀) j r)
  · intro z₁ z₂ hz₁ hz₂
    calc
      (Algebra.TensorProduct.congr e (AlgEquiv.refl : C₀ ≃ₐ[A i₀] C₀))
          ((_root_.stageTensorMap
            (A := A i₀)
            (R := tail_ring_family (A := A) (i₀ := i₀))
            (f := fun j' k' hjk ↦
              tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
            (X := C₀) j) (z₁ + z₂)) =
        (Algebra.TensorProduct.congr e (AlgEquiv.refl : C₀ ≃ₐ[A i₀] C₀))
          (((_root_.stageTensorMap
            (A := A i₀)
            (R := tail_ring_family (A := A) (i₀ := i₀))
            (f := fun j' k' hjk ↦
              tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
            (X := C₀) j) z₁) +
            ((_root_.stageTensorMap
              (A := A i₀)
              (R := tail_ring_family (A := A) (i₀ := i₀))
              (f := fun j' k' hjk ↦
                tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
              (X := C₀) j) z₂)) := by
            exact congrArg
              (Algebra.TensorProduct.congr e (AlgEquiv.refl : C₀ ≃ₐ[A i₀] C₀))
              ((_root_.stageTensorMap
                (A := A i₀)
                (R := tail_ring_family (A := A) (i₀ := i₀))
                (f := fun j' k' hjk ↦
                  tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
                (X := C₀) j).map_add z₁ z₂)
      _ =
        (Algebra.TensorProduct.congr e (AlgEquiv.refl : C₀ ≃ₐ[A i₀] C₀))
            ((_root_.stageTensorMap
              (A := A i₀)
              (R := tail_ring_family (A := A) (i₀ := i₀))
              (f := fun j' k' hjk ↦
                tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
              (X := C₀) j) z₁) +
          (Algebra.TensorProduct.congr e (AlgEquiv.refl : C₀ ≃ₐ[A i₀] C₀))
            ((_root_.stageTensorMap
              (A := A i₀)
              (R := tail_ring_family (A := A) (i₀ := i₀))
              (f := fun j' k' hjk ↦
                tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
              (X := C₀) j) z₂) := by
            simpa using
              (Algebra.TensorProduct.congr e (AlgEquiv.refl : C₀ ≃ₐ[A i₀] C₀)).map_add
                ((_root_.stageTensorMap
                  (A := A i₀)
                  (R := tail_ring_family (A := A) (i₀ := i₀))
                  (f := fun j' k' hjk ↦
                    tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
                  (X := C₀) j) z₁)
                ((_root_.stageTensorMap
                  (A := A i₀)
                  (R := tail_ring_family (A := A) (i₀ := i₀))
                  (f := fun j' k' hjk ↦
                    tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
                  (X := C₀) j) z₂)
      _ =
        (Algebra.TensorProduct.map
          (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
          (AlgHom.id (A i₀) C₀)) z₁ +
          (Algebra.TensorProduct.map
            (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
            (AlgHom.id (A i₀) C₀)) z₂ := by
              rw [hz₁, hz₂]
      _ =
        (Algebra.TensorProduct.map
          (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
          (AlgHom.id (A i₀) C₀)) (z₁ + z₂) := by
              symm
              exact (Algebra.TensorProduct.map
                (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
                (AlgHom.id (A i₀) C₀)).map_add z₁ z₂

/-- Helper for Lemma 10.168.4: an ambient vanishing equation yields the owner-surface equality
needed to invoke finite-family tensor descent on the tail system. -/
theorem owner_stageTensorMap_eq_zero_of_ambient_zero
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
    _root_.stageTensorMap
        (A := A i₀)
        (R := tail_ring_family (A := A) (i₀ := i₀))
        (f := fun _ _ hjk ↦
          tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
        (X := C₀) j z =
    _root_.stageTensorMap
        (A := A i₀)
        (R := tail_ring_family (A := A) (i₀ := i₀))
        (f := fun _ _ hjk ↦
          tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
        (X := C₀) j 0 := by
  letI : ∀ j' : Set.Ici i₀, Algebra (A i₀) (tail_ring_family (A := A) (i₀ := i₀) j') :=
    tail_ring_family_algebra_family (A := A) (f := f) (i₀ := i₀)
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  let tailLimit :=
    Ring.DirectLimit
      (tail_ring_family (A := A) (i₀ := i₀))
      (fun j' k' hjk ↦
        (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j'.1 →+* A k'.1))
  letI : Algebra (A i₀) tailLimit := owner_tail_directLimitAlgebra (A := A) (f := f) (i₀ := i₀)
  let e := owner_tail_directLimitAlgEquivToFull (A := A) (f := f) (i₀ := i₀)
  -- Proof comment: transport the owner `stageTensorMap` to the ambient direct-limit tensor
  -- product, where the assumed vanishing identifies the two images immediately.
  apply (Algebra.TensorProduct.congr e (AlgEquiv.refl : C₀ ≃ₐ[A i₀] C₀)).injective
  calc
    (Algebra.TensorProduct.congr e (AlgEquiv.refl : C₀ ≃ₐ[A i₀] C₀))
        (_root_.stageTensorMap
          (A := A i₀)
          (R := tail_ring_family (A := A) (i₀ := i₀))
          (f := fun j' k' hjk ↦
            tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
          (X := C₀) j z) =
      (Algebra.TensorProduct.map
        (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
        (AlgHom.id (A i₀) C₀)) z := by
          simpa [e] using owner_stageTensorMap_to_full
            (A := A) (f := f) (i₀ := i₀) j z
    _ =
      0 := hz
    _ =
      (Algebra.TensorProduct.map
        (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
        (AlgHom.id (A i₀) C₀)) (0 : A j.1 ⊗[A i₀] C₀) := by
          simp
    _ =
      (Algebra.TensorProduct.congr e (AlgEquiv.refl : C₀ ≃ₐ[A i₀] C₀))
        (_root_.stageTensorMap
          (A := A i₀)
          (R := tail_ring_family (A := A) (i₀ := i₀))
          (f := fun j' k' hjk ↦
            tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
          (X := C₀) j 0) := by
          symm
          simpa [e] using owner_stageTensorMap_to_full
            (A := A) (f := f) (i₀ := i₀) j (0 : A j.1 ⊗[A i₀] C₀)

/-- Helper for Lemma 10.168.4: finitely many equalities that hold after tensoring to the ambient
direct limit already hold after enlarging to one tail stage. -/
theorem tail_exists_common_stage_tensor_zero_family
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
  letI : ∀ j' : Set.Ici i₀, Algebra (A i₀) (tail_ring_family (A := A) (i₀ := i₀) j') :=
    tail_ring_family_algebra_family (A := A) (f := f) (i₀ := i₀)
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  have hz_tail :
      ∀ x ∈ s,
        _root_.stageTensorMap
            (A := A i₀)
            (R := tail_ring_family (A := A) (i₀ := i₀))
            (f := fun j' k' hjk ↦
              tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
            (X := C₀) j (z x) =
          _root_.stageTensorMap
            (A := A i₀)
            (R := tail_ring_family (A := A) (i₀ := i₀))
            (f := fun j' k' hjk ↦
              tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
            (X := C₀) j 0 := by
    intro x hx
    exact owner_stageTensorMap_eq_zero_of_ambient_zero
      (A := A) (f := f) (i₀ := i₀) (C₀ := C₀) j (z x) (hz x hx)
  -- Route correction: descend the whole finite zero family directly on the reindexed tail system,
  -- using `y := 0` so the conclusion simplifies to literal vanishing at one later tail stage.
  classical
  simpa using
    (_root_.tensor_equalities_descend_on_finset
      (A := A i₀)
      (I := Set.Ici i₀)
      (R := tail_ring_family (A := A) (i₀ := i₀))
      (f := fun j' k' hjk ↦ tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
      (X := C₀) (s := s) (i := j) z (fun _ ↦ 0) hz_tail)

/-- Helper for Lemma 10.168.4: swapping tensor factors commutes with base change along `φ₀`. -/
theorem tensor_comm_baseChange_naturality
    {R' : Type*} [CommRing R'] [Algebra (A i₀) R']
    (z : B₀ ⊗[A i₀] R') :
    (Algebra.TensorProduct.comm (R := A i₀) (A := C₀) (B := R'))
        ((Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) R')) z) =
      (Algebra.TensorProduct.map (AlgHom.id (A i₀) R') φ₀)
        ((Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := R')) z) := by
  -- Proof comment: both composites send a pure tensor `b ⊗ r` to the same swapped tensor
  -- `r ⊗ φ₀ b`, so tensor induction closes the naturality statement.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro b r
    simp [Algebra.TensorProduct.comm_tmul]
  · intro z₁ z₂ hz₁ hz₂
    simp [hz₁, hz₂]

/-- Helper for Lemma 10.168.4: applying base change on the right tensor factor commutes with
moving the left tensor factor forward along a tail transition. -/
theorem tail_transition_baseChange_naturality
    {X Y : Type*} [CommRing X] [CommRing Y]
    [Algebra (A i₀) X] [Algebra (A i₀) Y]
    {j k : Set.Ici i₀} (hjk : j ≤ k) (u : X →ₐ[A i₀] Y)
    (z :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      A j.1 ⊗[A i₀] X) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
    LinearMap.rTensor Y
        ((tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk).toLinearMap)
        ((Algebra.TensorProduct.map (AlgHom.id (A i₀) (A j.1)) u) z) =
      (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A k.1)) u)
        (LinearMap.rTensor X
          ((tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk).toLinearMap) z) := by
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
  -- Proof comment: on a pure tensor `r ⊗ x`, both sides compute to `f_{jk}(r) ⊗ u(x)`;
  -- tensor induction then extends the equality to arbitrary tensors.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro r x
    simp
  · intro z₁ z₂ hz₁ hz₂
    simp [hz₁, hz₂]

/-- Helper for Lemma 10.168.4: applying base change on the right tensor factor commutes with the
canonical map from a tail stage to the ambient direct limit. -/
theorem tail_stage_baseChange_naturality
    {X Y : Type*} [CommRing X] [CommRing Y]
    [Algebra (A i₀) X] [Algebra (A i₀) Y]
    (j : Set.Ici i₀) (u : X →ₐ[A i₀] Y)
    (z :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      A j.1 ⊗[A i₀] X) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    (Algebra.TensorProduct.map
        (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
        (AlgHom.id (A i₀) Y))
        ((Algebra.TensorProduct.map (AlgHom.id (A i₀) (A j.1)) u) z) =
      (Algebra.TensorProduct.map (AlgHom.id (A i₀) A∞) u)
        ((Algebra.TensorProduct.map
          (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
          (AlgHom.id (A i₀) X)) z) := by
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  -- Proof comment: on a pure tensor `r ⊗ x`, both sides send it to the same tensor
  -- `(of j r) ⊗ u(x)` in the ambient direct-limit tensor product.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro r x
    simp
  · intro z₁ z₂ hz₁ hz₂
    simp [hz₁, hz₂]

-- Proof sketch: apply the filtered-colimit descent statement for surjectivity from
-- the direct-limit presentation `Ring.DirectLimit A f`. Finite type of `C₀` over `B₀` is encoded
-- as `φ₀.FiniteType`, so finitely many generators admit preimages after base change to the direct
-- limit; directedness lets one realize those preimages simultaneously at a single stage.
/-- Lemma 10.168.4: for a directed colimit `A = colim_i A_i`, if `φ₀ : B₀ → C₀` is a map of
`A₀`-algebras whose base change to the colimit ring is surjective and `C₀` is of finite type over
`B₀`, then the base change of `φ₀` to some later stage `Aᵢ` is already surjective. -/
theorem finite_type_surjectivity_descends_along_directed_ring_colimit
    (φ₀ : B₀ →ₐ[A i₀] C₀)
    (hsurj :
      letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
      Function.Surjective (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)))
    (hfinite : φ₀.FiniteType) :
    ∃ (i : I) (hi : i₀ ≤ i),
      letI : Algebra (A i₀) (A i) := (f i₀ i hi).toAlgebra
      Function.Surjective (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A i))) :=
  by
    classical
    letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
    have hC₀FiniteType : Algebra.FiniteType B₀ C₀ := by
      simpa [AlgHom.FiniteType, RingHom.FiniteType] using hfinite
    obtain ⟨s, hs⟩ := hC₀FiniteType.out
    have hpreInf :
        ∀ x ∈ s, ∃ b : B₀ ⊗[A i₀] A∞,
          (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)) b =
            x ⊗ₜ[A i₀] (1 : A∞) := by
      intro x hx
      exact hsurj (x ⊗ₜ[A i₀] (1 : A∞))
    let bInf : C₀ → B₀ ⊗[A i₀] A∞ :=
      fun x ↦ if hx : x ∈ s then Classical.choose (hpreInf x hx) else 0
    let zInf : C₀ → A∞ ⊗[A i₀] B₀ :=
      fun x ↦ (Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := A∞)) (bInf x)
    obtain ⟨j, zj, hzj⟩ :=
      tail_tensor_lifts_from_stage_on_finset
        (A := A) (f := f) (i₀ := i₀) (X := B₀) s zInf
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    let δ : C₀ → A j.1 ⊗[A i₀] C₀ :=
      fun x ↦
        (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A j.1)) φ₀) (zj x) -
          (1 : A j.1) ⊗ₜ[A i₀] x
    have hδzero :
        ∀ x ∈ s,
          (Algebra.TensorProduct.map
            (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
            (AlgHom.id (A i₀) C₀)) (δ x) = 0 := by
      intro x hx
      have hbInf :
          (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)) (bInf x) =
            x ⊗ₜ[A i₀] (1 : A∞) := by
        simpa [bInf, hx] using Classical.choose_spec (hpreInf x hx)
      -- Proof comment: the defect compares the chosen tail lift with the desired generator tensor,
      -- and both become equal after mapping to the ambient direct-limit tensor product.
      calc
        (Algebra.TensorProduct.map
            (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
            (AlgHom.id (A i₀) C₀)) (δ x)
            =
          (Algebra.TensorProduct.map (AlgHom.id (A i₀) A∞) φ₀)
              ((Algebra.TensorProduct.map
                (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
                (AlgHom.id (A i₀) B₀)) (zj x)) -
            ((1 : A∞) ⊗ₜ[A i₀] x) := by
              simp [δ, tail_stage_baseChange_naturality (A := A) (f := f) (i₀ := i₀)
                (j := j) (u := φ₀) (z := zj x)]
        _ =
          (Algebra.TensorProduct.map (AlgHom.id (A i₀) A∞) φ₀) (zInf x) -
            ((1 : A∞) ⊗ₜ[A i₀] x) := by
              rw [hzj x hx]
        _ =
          (Algebra.TensorProduct.comm (R := A i₀) (A := C₀) (B := A∞))
              ((Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)) (bInf x)) -
            ((1 : A∞) ⊗ₜ[A i₀] x) := by
              simpa [zInf] using
                (congrArg
                  (fun t : A∞ ⊗[A i₀] C₀ ↦ t - ((1 : A∞) ⊗ₜ[A i₀] x))
                  ((tensor_comm_baseChange_naturality
                    (A := A) (i₀ := i₀) (B₀ := B₀) (C₀ := C₀)
                    (φ₀ := φ₀) (R' := A∞) (z := bInf x)).symm))
        _ =
          (Algebra.TensorProduct.comm (R := A i₀) (A := C₀) (B := A∞))
              (x ⊗ₜ[A i₀] (1 : A∞)) -
            ((1 : A∞) ⊗ₜ[A i₀] x) := by
              rw [hbInf]
        _ = 0 := by
              simp [Algebra.TensorProduct.comm_tmul]
    obtain ⟨k, hjk, hdesc⟩ :=
      tail_exists_common_stage_tensor_zero_family
        (A := A) (f := f) (i₀ := i₀) (C₀ := C₀) s j δ hδzero
    letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
    let bk : C₀ → A k.1 ⊗[A i₀] B₀ :=
      fun x ↦
        LinearMap.rTensor B₀
          ((tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk).toLinearMap) (zj x)
    have hpreK :
        ∀ x ∈ s, ∃ b : B₀ ⊗[A i₀] A k.1,
          (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A k.1))) b =
            x ⊗ₜ[A i₀] (1 : A k.1) := by
      intro x hx
      have hk_eq :
          (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A k.1)) φ₀) (bk x) =
            (1 : A k.1) ⊗ₜ[A i₀] x := by
        have hk_sub :
            (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A k.1)) φ₀) (bk x) -
              ((1 : A k.1) ⊗ₜ[A i₀] x) = 0 := by
          -- Proof comment: the descended defect equation rewrites to the claimed generator
          -- equality after commuting base change with the tail transition.
          simpa [δ, bk, tail_transition_baseChange_naturality (A := A) (f := f) (i₀ := i₀)
            (hjk := hjk) (u := φ₀) (z := zj x)] using hdesc x hx
        exact sub_eq_zero.mp hk_sub
      let b : B₀ ⊗[A i₀] A k.1 :=
        (Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := A k.1)).symm (bk x)
      refine ⟨b, ?_⟩
      apply (Algebra.TensorProduct.comm (R := A i₀) (A := C₀) (B := A k.1)).injective
      -- Proof comment: commute the stagewise generator preimage back to the source-oriented tensor
      -- product used by the surjectivity criterion.
      calc
        (Algebra.TensorProduct.comm (R := A i₀) (A := C₀) (B := A k.1))
            ((Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A k.1))) b) =
          (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A k.1)) φ₀)
            ((Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := A k.1)) b) := by
              exact tensor_comm_baseChange_naturality
                (A := A) (i₀ := i₀) (B₀ := B₀) (C₀ := C₀)
                (φ₀ := φ₀) (R' := A k.1) (z := b)
        _ = (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A k.1)) φ₀) (bk x) := by
              simp [b, bk]
        _ = (1 : A k.1) ⊗ₜ[A i₀] x := hk_eq
        _ = (Algebra.TensorProduct.comm (R := A i₀) (A := C₀) (B := A k.1))
              (x ⊗ₜ[A i₀] (1 : A k.1)) := by
                simp [Algebra.TensorProduct.comm_tmul]
    refine ⟨k.1, k.2, ?_⟩
    -- Proof comment: once the chosen finite generators have stagewise preimages, the standard
    -- generator criterion makes the stage tensor map surjective.
    exact tensor_map_surjective_of_generator_preimages
      (A := A) (i₀ := i₀) (B₀ := B₀) (C₀ := C₀) (R' := A k.1)
      (u := φ₀) (s := s) (hs := hs) (hpre := hpreK)

end
