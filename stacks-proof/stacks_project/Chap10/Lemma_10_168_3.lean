import stacks_project.Chap10.Lemma_10_127_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Polynomial

universe u v w

section

/-
Domain sampling:
* Primary domain: finite-type and finite descent for algebra-map base change along directed ring
  colimits.
* Relevant owner declarations inspected:
  - `Algebra.TensorProduct.map`
  - `Ring.DirectLimit.of`
  - `finite_type_surjectivity_descends` from `Lemma_10_127_7`
  - `DirectedFiniteTypeHomApproximation.stageBaseChangeMap` from `Lemma_10_127_14`
* Best owner abstraction:
  - `source-facing`: the finite and finite-type descent statements below
  - `core/canonical`: base change along a stage map or the direct-limit map, expressed by
    `Algebra.TensorProduct.map`
  - `bridge/view`: the chosen directed-system presentation of the colimit
* Primitive vs. derived:
  - primitive data: the directed system, the distinguished stage `i0`, and the algebra map `φ₀`
  - derived API: the stagewise and direct-limit tensor-product base-change maps
-/

variable {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
variable (G : ι → Type v) [∀ i, CommRing (G i)]
variable (f : ∀ i j, i ≤ j → G i →+* G j)
variable [DirectedSystem G fun i j hij ↦ f i j hij]
variable (i0 : ι)
variable {B₀ : Type w} [CommRing B₀] [Algebra (G i0) B₀]
variable {C₀ : Type w} [CommRing C₀] [Algebra (G i0) C₀]
variable (φ₀ : B₀ →ₐ[G i0] C₀)

local notation "G∞" => Ring.DirectLimit G (fun i j hij ↦ f i j hij)
local notation "ρ" => (fun i j hij ↦ f i j hij)

/-- Helper for Lemma 10.168.3: the tail above `i0` is inhabited by the base stage itself. -/
local instance tail_nonempty : Nonempty (Set.Ici i0) :=
  ⟨⟨i0, le_rfl⟩⟩

/-- Helper for Lemma 10.168.3: every stage above `i0` inherits the canonical `G i0`-algebra
structure from the transition map out of `i0`. -/
noncomputable local instance tail_stageAlgebra (j : Set.Ici i0) : Algebra (G i0) (G j.1) :=
  (f i0 j.1 j.2).toAlgebra

/-- Helper for Lemma 10.168.3: the ring direct limit carries the canonical `G i0`-algebra
structure coming from the distinguished stage `i0`. -/
noncomputable local instance directLimitStageAlgebra : Algebra (G i0) G∞ :=
  (Ring.DirectLimit.of G (fun i j hij ↦ f i j hij) i0).toAlgebra

/-- The stagewise base-changed map is of finite type whenever `φ₀` is of finite type. -/
-- Proof sketch: Finite type is stable under base change, applied to the base change of `φ₀`
-- along `G i0 → G i`.
theorem stage_base_change_hom_finiteType (hφ₀ : φ₀.FiniteType) {i : ι} (hi : i0 ≤ i) :
    letI : Algebra (G i0) (G i) := (f i0 i hi).toAlgebra
    (Algebra.TensorProduct.map φ₀ (AlgHom.id (G i0) (G i))).FiniteType := by
  letI : Algebra (G i0) (G i) := (f i0 i hi).toAlgebra
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  let S := B₀ ⊗[G i0] G i
  let e :=
    (Algebra.TensorProduct.comm (R := B₀) (A := S) (B := C₀)).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange
        (R := G i0) (S := B₀) (T := C₀) (A := C₀) (B := G i)).toRingEquiv
  let fbase : S →+* (S ⊗[B₀] C₀) :=
    (Algebra.TensorProduct.includeLeft : S →ₐ[B₀] (S ⊗[B₀] C₀)).toRingHom
  -- We first prove finite type for the literal base change along `B₀ → B₀ ⊗[G i0] G i`.
  have hbaseAlg : Algebra.FiniteType S (S ⊗[B₀] C₀) := by
    -- The finite-type input on `φ₀` is exactly the finite-type algebra structure on `C₀` over
    -- `B₀`, so we can invoke the standard base-change instance explicitly.
    letI : Algebra.FiniteType B₀ C₀ := by
      simpa [AlgHom.FiniteType, RingHom.FiniteType] using hφ₀
    exact Algebra.FiniteType.baseChange (R := B₀) (A := C₀) (B := S)
  have hfbase : @RingHom.FiniteType S (S ⊗[B₀] C₀) inferInstance inferInstance fbase := by
    -- We now package the base-change algebra as the corresponding finite-type ring map.
    unfold fbase
    exact RingHom.finiteType_algebraMap.mpr hbaseAlg
  have he :
      e.toRingHom.comp fbase =
        (Algebra.TensorProduct.map φ₀ (AlgHom.id (G i0) (G i))).toRingHom := by
    -- The transport `comm` followed by `cancelBaseChange` rewrites the literal base change into
    -- the tensor map appearing in the statement.
    ext b
    · -- On the `B₀`-generator, the composite sends `b ⊗ 1` to `φ₀ b ⊗ 1`.
      change
        (Algebra.TensorProduct.cancelBaseChange
          (R := G i0) (S := B₀) (T := C₀) (A := C₀) (B := G i))
          ((Algebra.TensorProduct.comm (R := B₀) (A := S) (B := C₀))
            ((((b ⊗ₜ[G i0] (1 : G i)) : S) ⊗ₜ[B₀] (1 : C₀)))) =
          φ₀ b ⊗ₜ[G i0] (1 : G i)
      simp [S, Algebra.smul_def]
      simpa using
        (show (algebraMap B₀ C₀) b ⊗ₜ[G i0] (1 : G i) = φ₀ b ⊗ₜ[G i0] (1 : G i) from rfl)
    · -- On the `G i`-generator, the composite fixes `1 ⊗ b`.
      simpa [e, fbase, S] using
        (show
          ((e.toRingHom.comp fbase).comp Algebra.TensorProduct.includeRight.toRingHom) b =
            ((Algebra.TensorProduct.map φ₀ (AlgHom.id (G i0) (G i))).comp
              Algebra.TensorProduct.includeRight.toRingHom) b from rfl)
  have hcomp : (e.toRingHom.comp fbase).FiniteType :=
    RingHom.finiteType_respectsIso.1 _ e hfbase
  -- After rewriting the transported base-change map, this is exactly the desired statement.
  rw [AlgHom.FiniteType]
  rw [← he]
  exact hcomp

/-- The colimit base-changed map is of finite type whenever `φ₀` is of finite type. -/
-- Proof sketch: Finite type is stable under base change, applied to the canonical map
-- `G i0 → Ring.DirectLimit G f`.
theorem direct_limit_base_change_hom_finiteType (hφ₀ : φ₀.FiniteType) :
    letI : Algebra (G i0) G∞ := (Ring.DirectLimit.of G (fun i j hij ↦ f i j hij) i0).toAlgebra
    (Algebra.TensorProduct.map φ₀ (AlgHom.id (G i0) G∞)).FiniteType := by
  letI : Algebra (G i0) G∞ := (Ring.DirectLimit.of G (fun i j hij ↦ f i j hij) i0).toAlgebra
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  let S := B₀ ⊗[G i0] G∞
  let e :=
    (Algebra.TensorProduct.comm (R := B₀) (A := S) (B := C₀)).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange
        (R := G i0) (S := B₀) (T := C₀) (A := C₀) (B := G∞)).toRingEquiv
  let fbase : S →+* (S ⊗[B₀] C₀) :=
    (Algebra.TensorProduct.includeLeft : S →ₐ[B₀] (S ⊗[B₀] C₀)).toRingHom
  -- As in the stagewise case, finite type survives the literal base change along `B₀ → S`.
  have hbaseAlg : Algebra.FiniteType S (S ⊗[B₀] C₀) := by
    letI : Algebra.FiniteType B₀ C₀ := by
      simpa [AlgHom.FiniteType, RingHom.FiniteType] using hφ₀
    exact Algebra.FiniteType.baseChange (R := B₀) (A := C₀) (B := S)
  have hfbase : @RingHom.FiniteType S (S ⊗[B₀] C₀) inferInstance inferInstance fbase := by
    -- Package the base-changed algebra as the corresponding finite-type ring map.
    unfold fbase
    exact RingHom.finiteType_algebraMap.mpr hbaseAlg
  have he :
      e.toRingHom.comp fbase =
        (Algebra.TensorProduct.map φ₀ (AlgHom.id (G i0) G∞)).toRingHom := by
    -- The same `comm` plus `cancelBaseChange` transport rewrites the literal base change into the
    -- tensor map over the direct-limit ring.
    ext b
    ·
      change
        (Algebra.TensorProduct.cancelBaseChange
          (R := G i0) (S := B₀) (T := C₀) (A := C₀) (B := G∞))
          ((Algebra.TensorProduct.comm (R := B₀) (A := S) (B := C₀))
            ((((b ⊗ₜ[G i0] (1 : G∞)) : S) ⊗ₜ[B₀] (1 : C₀)))) =
          φ₀ b ⊗ₜ[G i0] (1 : G∞)
      simp [S, Algebra.smul_def]
      simpa using
        (show (algebraMap B₀ C₀) b ⊗ₜ[G i0] (1 : G∞) = φ₀ b ⊗ₜ[G i0] (1 : G∞) from rfl)
    ·
      simpa [e, fbase, S] using
        (show
          ((e.toRingHom.comp fbase).comp Algebra.TensorProduct.includeRight.toRingHom) b =
            ((Algebra.TensorProduct.map φ₀ (AlgHom.id (G i0) G∞)).comp
              Algebra.TensorProduct.includeRight.toRingHom) b from rfl)
  have hcomp : (e.toRingHom.comp fbase).FiniteType :=
    RingHom.finiteType_respectsIso.1 _ e hfbase
  -- After rewriting the transported base-change map, this is exactly the desired map.
  rw [AlgHom.FiniteType]
  rw [← he]
  exact hcomp

/-- Helper for Lemma 10.168.3: a chosen upper bound lies above both a given stage and the base
stage `i0`. -/
noncomputable def tail_upper_bound (i : ι) : ι :=
  (exists_ge_ge i i0).choose

/-- Helper for Lemma 10.168.3: the chosen upper bound lies above the original stage. -/
theorem le_tail_upper_bound_left (i : ι) :
    i ≤ tail_upper_bound (i0 := i0) i :=
  (exists_ge_ge i i0).choose_spec.1

/-- Helper for Lemma 10.168.3: the chosen upper bound lies in the tail above `i0`. -/
theorem le_tail_upper_bound_right (i : ι) :
    i0 ≤ tail_upper_bound (i0 := i0) i :=
  (exists_ge_ge i i0).choose_spec.2

/-- Helper for Lemma 10.168.3: every stage of the original directed system maps canonically into
the direct limit of the tail above `i0`. -/
noncomputable def full_stage_to_tail_directLimit (i : ι) :
    G i →+* Ring.DirectLimit (fun j : Set.Ici i0 ↦ G j.1) (fun j k hij ↦ f j.1 k.1 hij) :=
  let j : Set.Ici i0 := ⟨tail_upper_bound (i0 := i0) i, le_tail_upper_bound_right (i0 := i0) i⟩
  (Ring.DirectLimit.of (fun j : Set.Ici i0 ↦ G j.1) (fun j k hij ↦ f j.1 k.1 hij) j).comp
    (f i j.1 (le_tail_upper_bound_left (i0 := i0) i))

/-- Helper for Lemma 10.168.3: the canonical maps from the original stages into the tail direct
limit are compatible with the original transition maps. -/
theorem full_stage_to_tail_directLimit_compatible {i j : ι} (hij : i ≤ j) (x : G i) :
    full_stage_to_tail_directLimit (G := G) (f := f) (i0 := i0) j (f i j hij x) =
      full_stage_to_tail_directLimit (G := G) (f := f) (i0 := i0) i x := by
  letI : IsDirectedOrder (Set.Ici i0) := by
    constructor
    intro a b
    obtain ⟨k, hak, hbk⟩ := exists_ge_ge a.1 b.1
    exact ⟨⟨k, le_trans a.2 hak⟩, hak, hbk⟩
  let ji : Set.Ici i0 :=
    ⟨tail_upper_bound (i0 := i0) i, le_tail_upper_bound_right (i0 := i0) i⟩
  let jj : Set.Ici i0 :=
    ⟨tail_upper_bound (i0 := i0) j, le_tail_upper_bound_right (i0 := i0) j⟩
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge ji jj
  -- Proof comment: move both representatives to a common tail stage, then compare them using the
  -- original directed-system relation.
  calc
    full_stage_to_tail_directLimit (G := G) (f := f) (i0 := i0) j (f i j hij x)
        =
      Ring.DirectLimit.of (fun j : Set.Ici i0 ↦ G j.1) (fun j k hij ↦ f j.1 k.1 hij) k
        (f jj.1 k.1 hjk
          (f j jj.1 (le_tail_upper_bound_left (i0 := i0) j) (f i j hij x))) := by
            simp [full_stage_to_tail_directLimit, jj, RingHom.comp_apply]
            symm
            exact Ring.DirectLimit.of_f hjk _
    _ =
      Ring.DirectLimit.of (fun j : Set.Ici i0 ↦ G j.1) (fun j k hij ↦ f j.1 k.1 hij) k
        (f ji.1 k.1 hik (f i ji.1 (le_tail_upper_bound_left (i0 := i0) i) x)) := by
          congr 1
          calc
            f jj.1 k.1 hjk (f j jj.1 (le_tail_upper_bound_left (i0 := i0) j) (f i j hij x))
                = f j k.1 (le_trans (le_tail_upper_bound_left (i0 := i0) j) hjk)
                    (f i j hij x) := by
                    exact DirectedSystem.map_map' (f := fun i j hij ↦ f i j hij)
                      (le_tail_upper_bound_left (i0 := i0) j) hjk (f i j hij x)
            _ = f i k.1 (le_trans hij (le_trans (le_tail_upper_bound_left (i0 := i0) j) hjk)) x := by
                  exact DirectedSystem.map_map' (f := fun i j hij ↦ f i j hij)
                    hij (le_trans (le_tail_upper_bound_left (i0 := i0) j) hjk) x
            _ = f ji.1 k.1 hik (f i ji.1 (le_tail_upper_bound_left (i0 := i0) i) x) := by
                  symm
                  exact DirectedSystem.map_map' (f := fun i j hij ↦ f i j hij)
                    (le_tail_upper_bound_left (i0 := i0) i) hik x
    _ = full_stage_to_tail_directLimit (G := G) (f := f) (i0 := i0) i x := by
          simp [full_stage_to_tail_directLimit, ji, RingHom.comp_apply]
          exact Ring.DirectLimit.of_f hik _

/-- Helper for Lemma 10.168.3: the full direct limit maps canonically to the direct limit of the
tail above `i0`. -/
noncomputable def full_directLimit_to_tail :
    Ring.DirectLimit G (fun i j hij ↦ f i j hij) →+*
      Ring.DirectLimit (fun j : Set.Ici i0 ↦ G j.1) (fun j k hij ↦ f j.1 k.1 hij) :=
  Ring.DirectLimit.lift G (fun i j hij ↦ f i j hij)
    (Ring.DirectLimit (fun j : Set.Ici i0 ↦ G j.1) (fun j k hij ↦ f j.1 k.1 hij))
    (fun i ↦ full_stage_to_tail_directLimit (G := G) (f := f) (i0 := i0) i)
    (fun i j hij x ↦ full_stage_to_tail_directLimit_compatible (G := G) (f := f) (i0 := i0) hij x)

/-- Helper for Lemma 10.168.3: the tail direct limit maps canonically back to the original full
direct limit by forgetting that the stages lie in the tail. -/
noncomputable def tail_directLimit_to_full :
    Ring.DirectLimit (fun j : Set.Ici i0 ↦ G j.1) (fun j k hij ↦ f j.1 k.1 hij) →+*
      Ring.DirectLimit G (fun i j hij ↦ f i j hij) :=
  Ring.DirectLimit.lift
    (fun j : Set.Ici i0 ↦ G j.1)
    (fun j k hij ↦ f j.1 k.1 hij)
    (Ring.DirectLimit G (fun i j hij ↦ f i j hij))
    (fun j ↦ Ring.DirectLimit.of G (fun i j hij ↦ f i j hij) j.1)
    (fun j k hjk x ↦ by
      -- Proof comment: the tail transition is the original transition on the underlying stages.
      exact Ring.DirectLimit.of_f
        (G := G)
        (f := fun i j hij ↦ f i j hij) hjk x)

/-- Helper for Lemma 10.168.3: passing from the full direct limit to the tail and back is the
identity on the full direct limit. -/
theorem tail_directLimit_to_full_comp_full_directLimit_to_tail :
    (tail_directLimit_to_full (G := G) (f := f) (i0 := i0)).comp
        (full_directLimit_to_tail (G := G) (f := f) (i0 := i0)) =
      RingHom.id _ := by
  apply Ring.DirectLimit.hom_ext
  intro i
  ext x
  -- Proof comment: enlarge to the chosen tail stage and then use the direct-limit relation to
  -- come back to the original stage.
  simp [full_directLimit_to_tail, full_stage_to_tail_directLimit, tail_directLimit_to_full,
    RingHom.comp_apply]

/-- Helper for Lemma 10.168.3: passing from the tail direct limit to the full direct limit and
back is the identity on the tail direct limit. -/
theorem full_directLimit_to_tail_comp_tail_directLimit_to_full :
    (full_directLimit_to_tail (G := G) (f := f) (i0 := i0)).comp
        (tail_directLimit_to_full (G := G) (f := f) (i0 := i0)) =
      RingHom.id _ := by
  apply Ring.DirectLimit.hom_ext
  intro j
  ext x
  -- Proof comment: a tail stage already lies above `i0`, so the chosen upper tail stage
  -- represents the same class as the original one.
  simp [full_directLimit_to_tail, full_stage_to_tail_directLimit, tail_directLimit_to_full,
    RingHom.comp_apply]

/-- Helper for Lemma 10.168.3: the direct limit of the tail above `i0` is canonically isomorphic
to the original direct limit. -/
noncomputable def tail_directLimitIso {B : Type*} [CommRing B]
    (colimitIso : Ring.DirectLimit G (fun i j hij ↦ f i j hij) ≃+* B) :
    Ring.DirectLimit (fun j : Set.Ici i0 ↦ G j.1) (fun j k hij ↦ f j.1 k.1 hij) ≃+* B :=
  (RingEquiv.ofRingHom
      (tail_directLimit_to_full (G := G) (f := f) (i0 := i0))
      (full_directLimit_to_tail (G := G) (f := f) (i0 := i0))
      (tail_directLimit_to_full_comp_full_directLimit_to_tail (G := G) (f := f) (i0 := i0))
      (full_directLimit_to_tail_comp_tail_directLimit_to_full (G := G) (f := f) (i0 := i0))).trans
    colimitIso

/-- Helper for Lemma 10.168.3: transition maps above `i0` commute with the induced
`G i0`-algebra structures. -/
theorem stage_transition_commutes {i j : ι} (hi : i0 ≤ i) (hij : i ≤ j) (a : G i0) :
    f i j hij ((f i0 i hi) a) = (f i0 j (le_trans hi hij)) a := by
  -- Proof comment: both routes are the same directed-system transition out of the base stage.
  simpa using (DirectedSystem.map_map (f := fun i j hij ↦ f i j hij) hi hij a)

/-- Helper for Lemma 10.168.3: the tail above the distinguished stage `i0` is still directed. -/
theorem tail_index_isDirected :
    IsDirectedOrder (Set.Ici i0) := by
  constructor
  intro i j
  -- Directedness of the ambient preorder gives a common upper bound in the tail.
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.1 j.1
  exact ⟨⟨k, le_trans i.2 hik⟩, hik, hjk⟩

/-- Helper for Lemma 10.168.3: the canonical map from a stage above `i0` to the ring direct limit
respects the induced `G i0`-algebra structures. -/
theorem stage_to_direct_limit_commutes (j : Set.Ici i0) (a : G i0) :
    Ring.DirectLimit.of G (fun i j hij ↦ f i j hij) j.1 ((f i0 j.1 j.2) a) =
      Ring.DirectLimit.of G (fun i j hij ↦ f i j hij) i0 a := by
  -- Proof comment: this is exactly the defining relation of the direct limit.
  simpa using
    (Ring.DirectLimit.of_f (G := G) (f := fun i j hij ↦ f i j hij) j.2 a).symm

/-- Helper for Lemma 10.168.3: if a finite set of generators of `C₀` becomes integral in the
literal stage base change `(B₀ ⊗[G i0] G i) ⊗[B₀] C₀`, then the stage base-change map
`B₀ ⊗[G i0] G i → C₀ ⊗[G i0] G i` is integral. -/
theorem stage_base_change_hom_isIntegral_of_generator_integral
    {i : ι} (hi : i0 ≤ i) (s : Finset C₀)
    (hs :
      letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
      Algebra.adjoin B₀ (s : Set C₀) = ⊤)
    (hint :
      letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
      letI : Algebra (G i0) (G i) := (f i0 i hi).toAlgebra
      let S := B₀ ⊗[G i0] G i
      ∀ x ∈ s,
        IsIntegral S
          ((Algebra.TensorProduct.includeRight : C₀ →ₐ[B₀] S ⊗[B₀] C₀) x)) :
    letI : Algebra (G i0) (G i) := (f i0 i hi).toAlgebra
    (Algebra.TensorProduct.map φ₀ (AlgHom.id (G i0) (G i))).IsIntegral := by
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  letI : Algebra (G i0) (G i) := (f i0 i hi).toAlgebra
  let S := B₀ ⊗[G i0] G i
  let e :=
    (Algebra.TensorProduct.comm (R := B₀) (A := S) (B := C₀)).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange
        (R := G i0) (S := B₀) (T := C₀) (A := C₀) (B := G i)).toRingEquiv
  let fbase : S →+* (S ⊗[B₀] C₀) :=
    (Algebra.TensorProduct.includeLeft : S →ₐ[B₀] (S ⊗[B₀] C₀)).toRingHom
  have htop : Algebra.adjoin S (((1 : S) ⊗ₜ[B₀] ·) '' (s : Set C₀)) = ⊤ := by
    -- The same finite generating set still generates after literal base change.
    simpa [S] using
      Algebra.TensorProduct.adjoin_one_tmul_image_eq_top (A := S) (s := (s : Set C₀)) hs
  have hIntegralTop : Algebra.IsIntegral S (Algebra.adjoin S (((1 : S) ⊗ₜ[B₀] ·) '' (s : Set C₀))) := by
    -- Integrality on generators extends to the adjoined subalgebra.
    refine Algebra.IsIntegral.adjoin ?_
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    simpa [S] using hint x hx
  have hIntegralTop' : Algebra.IsIntegral S (⊤ : Subalgebra S (S ⊗[B₀] C₀)) := by
    rw [← htop]
    exact hIntegralTop
  have hIntegralAll : Algebra.IsIntegral S (S ⊗[B₀] C₀) := by
    -- Passing from the top subalgebra back to the ambient ring removes the final coercion layer.
    exact (Subalgebra.topEquiv (R := S) (A := S ⊗[B₀] C₀)).isIntegral_iff.mp hIntegralTop'
  have hfbase : fbase.IsIntegral := by
    -- Since the tensor generators adjoin to the whole target, the literal base change is integral.
    change RingHom.IsIntegral (algebraMap S (S ⊗[B₀] C₀))
    rw [algebraMap_isIntegral_iff]
    exact hIntegralAll
  have he :
      e.toRingHom.comp fbase =
        (Algebra.TensorProduct.map φ₀ (AlgHom.id (G i0) (G i))).toRingHom := by
    -- The standard `comm` plus `cancelBaseChange` transport identifies the two base-change maps.
    ext b
    ·
      change
        (Algebra.TensorProduct.cancelBaseChange
          (R := G i0) (S := B₀) (T := C₀) (A := C₀) (B := G i))
          ((Algebra.TensorProduct.comm (R := B₀) (A := S) (B := C₀))
            ((((b ⊗ₜ[G i0] (1 : G i)) : S) ⊗ₜ[B₀] (1 : C₀)))) =
          φ₀ b ⊗ₜ[G i0] (1 : G i)
      simp [S, Algebra.smul_def]
      simpa using
        (show (algebraMap B₀ C₀) b ⊗ₜ[G i0] (1 : G i) = φ₀ b ⊗ₜ[G i0] (1 : G i) from rfl)
    ·
      simpa [e, fbase, S] using
        (show
          ((e.toRingHom.comp fbase).comp Algebra.TensorProduct.includeRight.toRingHom) b =
            ((Algebra.TensorProduct.map φ₀ (AlgHom.id (G i0) (G i))).comp
              Algebra.TensorProduct.includeRight.toRingHom) b from rfl)
  have hcomp : (e.toRingHom.comp fbase).IsIntegral :=
    RingHom.isIntegral_respectsIso.1 _ e hfbase
  -- Rewriting back along the comparison isomorphism yields the desired stagewise integrality.
  have htarget : ((Algebra.TensorProduct.map φ₀ (AlgHom.id (G i0) (G i))).toRingHom).IsIntegral := by
    rw [← he]
    exact hcomp
  simpa using htarget

/-- Helper for Lemma 10.168.3: the literal tail stage-to-limit base-change map carries the
evaluation of a stage polynomial at `includeRight x` to the evaluation of the mapped polynomial at
the direct-limit tensor generator. -/
theorem literal_stage_to_limit_tensor_aeval
    {j : Set.Ici i0} (x : C₀)
    (qj :
      letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
      Polynomial (B₀ ⊗[G i0] G j.1)) :
    letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
    letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
    letI : Algebra (G i0) G∞ := (Ring.DirectLimit.of G (fun i j hij ↦ f i j hij) i0).toAlgebra
    let Sinf : Type _ := B₀ ⊗[G i0] G∞
    let gj_to_inf : G j.1 →ₐ[G i0] G∞ :=
      { toRingHom := Ring.DirectLimit.of G (fun i j hij ↦ f i j hij) j.1
        commutes' := by
          intro r
          exact Ring.DirectLimit.of_f (G := G) (f := fun i j hij ↦ f i j hij) j.2 r }
    let σj : (B₀ ⊗[G i0] G j.1) →ₐ[B₀] Sinf :=
      { toRingHom := (Algebra.TensorProduct.map (AlgHom.id (G i0) B₀) gj_to_inf).toRingHom
        commutes' := by
          intro b
          change (Algebra.TensorProduct.map (AlgHom.id (G i0) B₀) gj_to_inf) (b ⊗ₜ[G i0] (1 : G j.1)) =
            b ⊗ₜ[G i0] (1 : G∞)
          simp [gj_to_inf] }
    let τj : (B₀ ⊗[G i0] G j.1) ⊗[B₀] C₀ →ₐ[B₀] Sinf ⊗[B₀] C₀ :=
      Algebra.TensorProduct.map σj (AlgHom.id B₀ C₀)
    τj (Polynomial.aeval (Algebra.TensorProduct.includeRight x) qj) =
      Polynomial.aeval (Algebra.TensorProduct.includeRight x) (Polynomial.map σj.toRingHom qj) := by
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
  letI : Algebra (G i0) G∞ := (Ring.DirectLimit.of G (fun i j hij ↦ f i j hij) i0).toAlgebra
  let Sinf : Type _ := B₀ ⊗[G i0] G∞
  let gj_to_inf : G j.1 →ₐ[G i0] G∞ :=
    { toRingHom := Ring.DirectLimit.of G (fun i j hij ↦ f i j hij) j.1
      commutes' := by
        intro r
        exact Ring.DirectLimit.of_f (G := G) (f := fun i j hij ↦ f i j hij) j.2 r }
  let σj : (B₀ ⊗[G i0] G j.1) →ₐ[B₀] Sinf :=
    { toRingHom := (Algebra.TensorProduct.map (AlgHom.id (G i0) B₀) gj_to_inf).toRingHom
      commutes' := by
        intro b
        change (Algebra.TensorProduct.map (AlgHom.id (G i0) B₀) gj_to_inf) (b ⊗ₜ[G i0] (1 : G j.1)) =
          b ⊗ₜ[G i0] (1 : G∞)
        simp [gj_to_inf] }
  let τj : (B₀ ⊗[G i0] G j.1) ⊗[B₀] C₀ →ₐ[B₀] Sinf ⊗[B₀] C₀ :=
    Algebra.TensorProduct.map σj (AlgHom.id B₀ C₀)
  -- The left tensor factor is mapped by `σj`, so this is the coefficient compatibility needed for
  -- `Polynomial.map_aeval_eq_aeval_map`.
  have hcomm :
      (algebraMap Sinf (Sinf ⊗[B₀] C₀)).comp σj.toRingHom =
        τj.toRingHom.comp (algebraMap (B₀ ⊗[G i0] G j.1) ((B₀ ⊗[G i0] G j.1) ⊗[B₀] C₀)) := rfl
  -- The base-change map fixes the right tensor generator, since it is the identity on `C₀`.
  have hright :
      τj.comp (Algebra.TensorProduct.includeRight : C₀ →ₐ[B₀] (B₀ ⊗[G i0] G j.1) ⊗[B₀] C₀) =
        (Algebra.TensorProduct.includeRight : C₀ →ₐ[B₀] Sinf ⊗[B₀] C₀) := by
    simpa [τj] using Algebra.TensorProduct.map_comp_includeRight σj (AlgHom.id B₀ C₀)
  calc
    τj (Polynomial.aeval (Algebra.TensorProduct.includeRight x) qj)
        = Polynomial.aeval (τj (Algebra.TensorProduct.includeRight x))
            (Polynomial.map σj.toRingHom qj) := by
            simpa using Polynomial.map_aeval_eq_aeval_map hcomm qj
              (Algebra.TensorProduct.includeRight x)
    _ = Polynomial.aeval (Algebra.TensorProduct.includeRight x) (Polynomial.map σj.toRingHom qj) := by
          rw [show τj (Algebra.TensorProduct.includeRight x) =
              Algebra.TensorProduct.includeRight x by
                simpa using congrArg (fun h : C₀ →ₐ[B₀] Sinf ⊗[B₀] C₀ => h x) hright]

/-- Helper for Lemma 10.168.3: the tail transition maps remain compatible with the chosen base
stage map out of `i0`. -/
theorem tail_stage_transition_commutes
    {j k : Set.Ici i0} (hjk : j ≤ k) (a : G i0) :
    f j.1 k.1 hjk ((f i0 j.1 j.2) a) = (f i0 k.1 (le_trans j.2 hjk)) a := by
  -- Proof comment: this is the ambient directed-system composition law specialized to the tail.
  simpa using (DirectedSystem.map_map (f := fun i j hij ↦ f i j hij) j.2 hjk a)

/-- Helper for Lemma 10.168.3: the canonical map from a tail stage to the ambient direct limit is
an algebra homomorphism over the distinguished base stage `i0`. -/
theorem tail_stage_to_direct_limit_algHom_commutes
    (j : Set.Ici i0) (a : G i0) :
    Ring.DirectLimit.of G (fun i j hij ↦ f i j hij) j.1 ((f i0 j.1 j.2) a) =
      algebraMap (G i0) G∞ a := by
  -- Proof comment: this is the stage-to-direct-limit compatibility already proved above, repackaged
  -- in the form needed to build an algebra homomorphism.
  change Ring.DirectLimit.of G (fun i j hij ↦ f i j hij) j.1 ((f i0 j.1 j.2) a) =
    Ring.DirectLimit.of G (fun i j hij ↦ f i j hij) i0 a
  exact stage_to_direct_limit_commutes (G := G) (f := f) (i0 := i0) j a

/-- Helper for Lemma 10.168.3: every element of the ambient direct limit already comes from some
stage lying in the tail above `i0`. -/
theorem directLimit_exists_tail_repr (z : G∞) :
    ∃ (j : Set.Ici i0) (x : G j.1),
      Ring.DirectLimit.of G (fun i j hij ↦ f i j hij) j.1 x = z := by
  rcases Ring.DirectLimit.exists_of (G := G) (f := fun i j hij ↦ f i j hij) z with ⟨i, x, rfl⟩
  let j : Set.Ici i0 := ⟨tail_upper_bound (i0 := i0) i, le_tail_upper_bound_right (i0 := i0) i⟩
  refine ⟨j, f i j.1 (le_tail_upper_bound_left (i0 := i0) i) x, ?_⟩
  -- Proof comment: enlarging a stage representative to a later tail stage does not change its
  -- image in the direct limit.
  exact Ring.DirectLimit.of_f (G := G) (f := fun i j hij ↦ f i j hij)
    (le_tail_upper_bound_left (i0 := i0) i) x

/-- Helper for Lemma 10.168.3: a finite family of ambient direct-limit elements admits
representatives in one common tail stage above `i0`. -/
theorem directLimit_exists_common_tail_repr_finset
    (s : Finset G∞) :
    ∃ (j : Set.Ici i0),
      ∀ z ∈ s, ∃ x : G j.1,
        Ring.DirectLimit.of G (fun i j hij ↦ f i j hij) j.1 x = z := by
  classical
  refine Finset.induction_on s ?_ ?_
  · refine ⟨⟨i0, le_rfl⟩, ?_⟩
    intro z hz
    exact False.elim (Finset.notMem_empty z hz)
  · intro a s ha hs
    obtain ⟨j₁, x₁, hx₁⟩ := directLimit_exists_tail_repr (G := G) (f := f) (i0 := i0) a
    obtain ⟨j₂, hs₂⟩ := hs
    obtain ⟨k, hj₁k, hj₂k⟩ := exists_ge_ge j₁.1 j₂.1
    let j : Set.Ici i0 := ⟨k, le_trans j₁.2 hj₁k⟩
    refine ⟨j, ?_⟩
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · refine ⟨f j₁.1 j.1 hj₁k x₁, ?_⟩
      exact (Ring.DirectLimit.of_f (G := G) (f := fun i j hij ↦ f i j hij) hj₁k x₁).trans hx₁
    · obtain ⟨x, hx⟩ := hs₂ z hz
      refine ⟨f j₂.1 j.1 hj₂k x, ?_⟩
      exact (Ring.DirectLimit.of_f (G := G) (f := fun i j hij ↦ f i j hij) hj₂k x).trans hx

/-- Helper for Lemma 10.168.3: tensoring an algebra map on the left factor with the identity on
`B₀` agrees with the corresponding `rTensor` map. -/
theorem tensor_map_eq_rTensor_B0
    {R' S' : Type*} [CommRing R'] [CommRing S']
    [Algebra (G i0) R'] [Algebra (G i0) S']
    (g : R' →ₐ[G i0] S') (z : R' ⊗[G i0] B₀) :
    (Algebra.TensorProduct.map g (AlgHom.id (G i0) B₀)) z =
      LinearMap.rTensor B₀ g.toLinearMap z := by
  -- Proof comment: both maps send a pure tensor `r ⊗ b` to `g r ⊗ b`, so tensor induction closes.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro r b
    simp [LinearMap.rTensor_tmul]
  · intro z₁ z₂ hz₁ hz₂
    simp [hz₁, hz₂]

/-- Helper for Lemma 10.168.3: tensoring an algebra map on the left factor with the identity on
`C₀` agrees with the corresponding `rTensor` map. -/
theorem tensor_map_eq_rTensor_C0
    {R' S' : Type*} [CommRing R'] [CommRing S']
    [Algebra (G i0) R'] [Algebra (G i0) S']
    (g : R' →ₐ[G i0] S') (z : R' ⊗[G i0] C₀) :
    (Algebra.TensorProduct.map g (AlgHom.id (G i0) C₀)) z =
      LinearMap.rTensor C₀ g.toLinearMap z := by
  -- Proof comment: as above, the two maps agree on pure tensors and hence on the whole tensor
  -- product.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro r c
    simp [LinearMap.rTensor_tmul]
  · intro z₁ z₂ hz₁ hz₂
    simp [hz₁, hz₂]

/-- Helper for Lemma 10.168.3: after swapping the coefficient tensor to the `G`-on-the-left
orientation, polynomial evaluation commutes with changing the stage ring on that left factor. -/
theorem comm_tensor_aeval
    {R' S' : Type*} [CommRing R'] [CommRing S']
    [Algebra (G i0) R'] [Algebra (G i0) S']
    (g : R' →ₐ[G i0] S') (x : C₀) (q : Polynomial (R' ⊗[G i0] B₀)) :
    letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
    let κB : (R' ⊗[G i0] B₀) →ₐ[G i0] (S' ⊗[G i0] B₀) :=
      Algebra.TensorProduct.map g (AlgHom.id (G i0) B₀)
    let κC : (R' ⊗[G i0] C₀) →ₐ[G i0] (S' ⊗[G i0] C₀) :=
      Algebra.TensorProduct.map g (AlgHom.id (G i0) C₀)
    let θR : (R' ⊗[G i0] B₀) →ₐ[G i0] (R' ⊗[G i0] C₀) :=
      Algebra.TensorProduct.map (AlgHom.id (G i0) R') φ₀
    let θS : (S' ⊗[G i0] B₀) →ₐ[G i0] (S' ⊗[G i0] C₀) :=
      Algebra.TensorProduct.map (AlgHom.id (G i0) S') φ₀
    letI : Algebra (R' ⊗[G i0] B₀) (R' ⊗[G i0] C₀) := θR.toRingHom.toAlgebra
    letI : Algebra (S' ⊗[G i0] B₀) (S' ⊗[G i0] C₀) := θS.toRingHom.toAlgebra
    κC (Polynomial.aeval ((1 : R') ⊗ₜ[G i0] x) q) =
      Polynomial.aeval ((1 : S') ⊗ₜ[G i0] x) (Polynomial.map κB.toRingHom q) := by
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  let κB : (R' ⊗[G i0] B₀) →ₐ[G i0] (S' ⊗[G i0] B₀) :=
    Algebra.TensorProduct.map g (AlgHom.id (G i0) B₀)
  let κC : (R' ⊗[G i0] C₀) →ₐ[G i0] (S' ⊗[G i0] C₀) :=
    Algebra.TensorProduct.map g (AlgHom.id (G i0) C₀)
  let θR : (R' ⊗[G i0] B₀) →ₐ[G i0] (R' ⊗[G i0] C₀) :=
    Algebra.TensorProduct.map (AlgHom.id (G i0) R') φ₀
  let θS : (S' ⊗[G i0] B₀) →ₐ[G i0] (S' ⊗[G i0] C₀) :=
    Algebra.TensorProduct.map (AlgHom.id (G i0) S') φ₀
  letI : Algebra (R' ⊗[G i0] B₀) (R' ⊗[G i0] C₀) := θR.toRingHom.toAlgebra
  letI : Algebra (S' ⊗[G i0] B₀) (S' ⊗[G i0] C₀) := θS.toRingHom.toAlgebra
  -- Proof comment: `Polynomial.map_aeval_eq_aeval_map` applies once the coefficient maps commute,
  -- and the tensor map fixes the element `1 ⊗ x`.
  have hcomm :
      θS.toRingHom.comp κB.toRingHom =
        κC.toRingHom.comp θR.toRingHom := by
    ext r b <;> simp [θR, θS, κB, κC]
  have hxmap : κC ((1 : R') ⊗ₜ[G i0] x) = (1 : S') ⊗ₜ[G i0] x := by
    simp [κC]
  calc
    κC (Polynomial.aeval ((1 : R') ⊗ₜ[G i0] x) q)
        = Polynomial.aeval (κC ((1 : R') ⊗ₜ[G i0] x)) (Polynomial.map κB.toRingHom q) := by
            simpa [θR, θS] using
              Polynomial.map_aeval_eq_aeval_map hcomm q (((1 : R') ⊗ₜ[G i0] x))
    _ = Polynomial.aeval ((1 : S') ⊗ₜ[G i0] x) (Polynomial.map κB.toRingHom q) := by
          rw [hxmap]

/-- Helper for Lemma 10.168.3: the canonical map from a tail stage to the ambient direct limit is
an algebra homomorphism over the distinguished base stage `i0`. -/
noncomputable abbrev tail_stage_to_direct_limit_algHom
    (j : Set.Ici i0) :
    letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
    G j.1 →ₐ[G i0] G∞ :=
  letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
  { toRingHom := Ring.DirectLimit.of G (fun i j hij ↦ f i j hij) j.1
    commutes' := tail_stage_to_direct_limit_algHom_commutes (G := G) (f := f) (i0 := i0) j }

/-- Helper for Lemma 10.168.3: the transition map between two tail stages is an algebra map over
`G i0`. -/
noncomputable abbrev tail_transition_algHom
    {j k : Set.Ici i0} (hjk : j ≤ k) :
    letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
    letI : Algebra (G i0) (G k.1) := (f i0 k.1 k.2).toAlgebra
    G j.1 →ₐ[G i0] G k.1 :=
  letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
  letI : Algebra (G i0) (G k.1) := (f i0 k.1 k.2).toAlgebra
  { toRingHom := f j.1 k.1 hjk
    commutes' := tail_stage_transition_commutes (G := G) (f := f) (i0 := i0) hjk }

/-- Helper for Lemma 10.168.3: the transition map between two tail stages as a
`G i0`-linear map. -/
noncomputable abbrev tail_transition_linearMap
    {j k : Set.Ici i0} (hjk : j ≤ k) :
    letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
    letI : Algebra (G i0) (G k.1) := (f i0 k.1 k.2).toAlgebra
    G j.1 →ₗ[G i0] G k.1 :=
  letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
  letI : Algebra (G i0) (G k.1) := (f i0 k.1 k.2).toAlgebra
  (tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk).toLinearMap

/-- Helper for Lemma 10.168.3: transporting a tensor to a later tail stage does not change its
image in the ambient direct-limit tensor product. -/
theorem tail_tensor_map_transition
    {X : Type*} [CommRing X] [Algebra (G i0) X]
    {j k : Set.Ici i0} (hjk : j ≤ k)
    (z :
      letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
      G j.1 ⊗[G i0] X) :
    letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
    letI : Algebra (G i0) (G k.1) := (f i0 k.1 k.2).toAlgebra
    let τjk : (G j.1 ⊗[G i0] X) →ₐ[G i0] (G k.1 ⊗[G i0] X) :=
      Algebra.TensorProduct.map
        (tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk)
        (AlgHom.id (G i0) X)
    let κj : (G j.1 ⊗[G i0] X) →ₐ[G i0] (G∞ ⊗[G i0] X) :=
      Algebra.TensorProduct.map
        (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j)
        (AlgHom.id (G i0) X)
    let κk : (G k.1 ⊗[G i0] X) →ₐ[G i0] (G∞ ⊗[G i0] X) :=
      Algebra.TensorProduct.map
        (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) k)
        (AlgHom.id (G i0) X)
    κk (τjk z) = κj z := by
  letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
  letI : Algebra (G i0) (G k.1) := (f i0 k.1 k.2).toAlgebra
  let τjk : (G j.1 ⊗[G i0] X) →ₐ[G i0] (G k.1 ⊗[G i0] X) :=
    Algebra.TensorProduct.map
      (tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk)
      (AlgHom.id (G i0) X)
  let κj : (G j.1 ⊗[G i0] X) →ₐ[G i0] (G∞ ⊗[G i0] X) :=
    Algebra.TensorProduct.map
      (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j)
      (AlgHom.id (G i0) X)
  let κk : (G k.1 ⊗[G i0] X) →ₐ[G i0] (G∞ ⊗[G i0] X) :=
    Algebra.TensorProduct.map
      (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) k)
      (AlgHom.id (G i0) X)
  -- Proof comment: on pure tensors this is exactly `Ring.DirectLimit.of_f`, and tensor induction
  -- extends the compatibility to all tensors.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp [τjk, κj, κk]
  · intro r x
    change
      Ring.DirectLimit.of G (fun i j hij ↦ f i j hij) k.1 (f j.1 k.1 hjk r) ⊗ₜ[G i0] x =
        Ring.DirectLimit.of G (fun i j hij ↦ f i j hij) j.1 r ⊗ₜ[G i0] x
    exact congrArg (fun s : G∞ ↦ s ⊗ₜ[G i0] x)
      (Ring.DirectLimit.of_f (G := G) (f := fun i j hij ↦ f i j hij) hjk r)
  · intro z₁ z₂ hz₁ hz₂
    simp [τjk, κj, κk, hz₁, hz₂]

/-- Helper for Lemma 10.168.3: every tensor over the ambient direct-limit ring already comes from
some tensor over one tail stage above `i0`. -/
theorem directLimit_tensor_exists_tail_repr
    {X : Type*} [CommRing X] [Algebra (G i0) X]
    (z : G∞ ⊗[G i0] X) :
    ∃ j : Set.Ici i0,
      letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
      ∃ zj : G j.1 ⊗[G i0] X,
      (Algebra.TensorProduct.map
        (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j)
        (AlgHom.id (G i0) X)) zj = z := by
  -- Proof comment: descend a pure tensor by descending its direct-limit coefficient to one tail
  -- stage, then merge two stagewise lifts by moving both to a common upper bound in the tail.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · refine ⟨⟨i0, le_rfl⟩, 0, ?_⟩
    simp
  · intro r x
    obtain ⟨j, rj, hrj⟩ := directLimit_exists_tail_repr (G := G) (f := f) (i0 := i0) r
    letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
    refine ⟨j, rj ⊗ₜ[G i0] x, ?_⟩
    change Ring.DirectLimit.of G (fun i j hij ↦ f i j hij) j.1 rj ⊗ₜ[G i0] x = r ⊗ₜ[G i0] x
    exact congrArg (fun s : G∞ ↦ s ⊗ₜ[G i0] x) hrj
  · intro z₁ z₂ hz₁ hz₂
    obtain ⟨j₁, zj₁, hzj₁⟩ := hz₁
    obtain ⟨j₂, zj₂, hzj₂⟩ := hz₂
    obtain ⟨k, hj₁k, hj₂k⟩ := exists_ge_ge j₁.1 j₂.1
    let j : Set.Ici i0 := ⟨k, le_trans j₁.2 hj₁k⟩
    letI : Algebra (G i0) (G j₁.1) := (f i0 j₁.1 j₁.2).toAlgebra
    letI : Algebra (G i0) (G j₂.1) := (f i0 j₂.1 j₂.2).toAlgebra
    letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
    let τ₁ :
        (G j₁.1 ⊗[G i0] X) →ₐ[G i0] (G j.1 ⊗[G i0] X) :=
      Algebra.TensorProduct.map
        (tail_transition_algHom (G := G) (f := f) (i0 := i0) hj₁k)
        (AlgHom.id (G i0) X)
    let τ₂ :
        (G j₂.1 ⊗[G i0] X) →ₐ[G i0] (G j.1 ⊗[G i0] X) :=
      Algebra.TensorProduct.map
        (tail_transition_algHom (G := G) (f := f) (i0 := i0) hj₂k)
        (AlgHom.id (G i0) X)
    refine ⟨j, τ₁ zj₁ + τ₂ zj₂, ?_⟩
    calc
      (Algebra.TensorProduct.map
          (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j)
          (AlgHom.id (G i0) X)) (τ₁ zj₁ + τ₂ zj₂)
          =
        (Algebra.TensorProduct.map
          (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j)
          (AlgHom.id (G i0) X)) (τ₁ zj₁) +
          (Algebra.TensorProduct.map
            (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j)
            (AlgHom.id (G i0) X)) (τ₂ zj₂) := by
              simp
      _ =
        (Algebra.TensorProduct.map
          (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j₁)
          (AlgHom.id (G i0) X)) zj₁ +
          (Algebra.TensorProduct.map
            (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j₂)
            (AlgHom.id (G i0) X)) zj₂ := by
              rw [tail_tensor_map_transition (G := G) (f := f) (i0 := i0) hj₁k zj₁]
              rw [tail_tensor_map_transition (G := G) (f := f) (i0 := i0) hj₂k zj₂]
      _ = z₁ + z₂ := by rw [hzj₁, hzj₂]

/-- Helper for Lemma 10.168.3: finitely many tensors over the ambient direct-limit ring admit
simultaneous lifts to one common tail stage above `i0`. -/
theorem tail_tensor_lifts_from_stage_on_finset
    {α : Type*} [DecidableEq α]
    {X : Type*} [CommRing X] [Algebra (G i0) X]
    (s : Finset α) (z : α → G∞ ⊗[G i0] X) :
    ∃ j : Set.Ici i0,
      letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
      ∃ zj : α → G j.1 ⊗[G i0] X,
      ∀ a ∈ s,
        (Algebra.TensorProduct.map
          (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j)
          (AlgHom.id (G i0) X)) (zj a) = z a := by
  classical
  refine Finset.induction_on s ?_ ?_
  · refine ⟨⟨i0, le_rfl⟩, fun _ ↦ 0, ?_⟩
    intro a ha
    exact False.elim (Finset.notMem_empty a ha)
  · intro a s ha hs
    obtain ⟨j₁, zj₁, hzj₁⟩ :=
      directLimit_tensor_exists_tail_repr (G := G) (f := f) (i0 := i0) (z a)
    obtain ⟨j₂, zj₂, hzj₂⟩ := hs
    obtain ⟨k, hj₁k, hj₂k⟩ := exists_ge_ge j₁.1 j₂.1
    let j : Set.Ici i0 := ⟨k, le_trans j₁.2 hj₁k⟩
    letI : Algebra (G i0) (G j₁.1) := (f i0 j₁.1 j₁.2).toAlgebra
    letI : Algebra (G i0) (G j₂.1) := (f i0 j₂.1 j₂.2).toAlgebra
    letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
    let τ₁ :
        (G j₁.1 ⊗[G i0] X) →ₐ[G i0] (G j.1 ⊗[G i0] X) :=
      Algebra.TensorProduct.map
        (tail_transition_algHom (G := G) (f := f) (i0 := i0) hj₁k)
        (AlgHom.id (G i0) X)
    let τ₂ :
        (G j₂.1 ⊗[G i0] X) →ₐ[G i0] (G j.1 ⊗[G i0] X) :=
      Algebra.TensorProduct.map
        (tail_transition_algHom (G := G) (f := f) (i0 := i0) hj₂k)
        (AlgHom.id (G i0) X)
    refine ⟨j, fun b ↦ if hba : b = a then τ₁ zj₁ else τ₂ (zj₂ b), ?_⟩
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb'
    · simp only [dif_pos rfl]
      calc
        (Algebra.TensorProduct.map
            (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j)
            (AlgHom.id (G i0) X)) (τ₁ zj₁)
            =
          (Algebra.TensorProduct.map
            (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j₁)
            (AlgHom.id (G i0) X)) zj₁ := by
              rw [tail_tensor_map_transition (G := G) (f := f) (i0 := i0) hj₁k zj₁]
        _ = z b := hzj₁
    · have hba : b ≠ a := by
        intro hba
        apply ha
        simpa [hba] using hb'
      simp only [dif_neg hba]
      calc
        (Algebra.TensorProduct.map
            (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j)
            (AlgHom.id (G i0) X)) (τ₂ (zj₂ b))
            =
          (Algebra.TensorProduct.map
            (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j₂)
            (AlgHom.id (G i0) X)) (zj₂ b) := by
              rw [tail_tensor_map_transition (G := G) (f := f) (i0 := i0) hj₂k (zj₂ b)]
        _ = z b := hzj₂ b hb'

/-- Helper for Lemma 10.168.3: a monic polynomial over `G∞ ⊗[G i0] B₀` already comes from one
tail stage above `i0`. -/
theorem tail_exists_stage_monic_comm_polynomial
    (P : Polynomial (G∞ ⊗[G i0] B₀)) (hP : P.Monic) :
    ∃ j : Set.Ici i0,
      letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
      ∃ Q : Polynomial (G j.1 ⊗[G i0] B₀),
      Q.Monic ∧
        let gj_to_inf : G j.1 →ₐ[G i0] G∞ :=
          { toRingHom := Ring.DirectLimit.of G (fun i j hij ↦ f i j hij) j.1
            commutes' := by
              intro a
              exact Ring.DirectLimit.of_f (G := G) (f := fun i j hij ↦ f i j hij) j.2 a }
        let κj : (G j.1 ⊗[G i0] B₀) →ₐ[G i0] (G∞ ⊗[G i0] B₀) :=
          Algebra.TensorProduct.map gj_to_inf (AlgHom.id (G i0) B₀)
        Polynomial.map κj.toRingHom Q = P := by
  classical
  let coeffs : Finset (G∞ ⊗[G i0] B₀) := P.support.image P.coeff
  -- Proof comment: only finitely many coefficients are nonzero, so we first descend exactly those
  -- coefficients to one common tail stage.
  obtain ⟨j, zj, hzj⟩ :=
    tail_tensor_lifts_from_stage_on_finset
      (G := G) (f := f) (i0 := i0) (X := B₀) coeffs (fun z ↦ z)
  letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
  let κj : (G j.1 ⊗[G i0] B₀) →ₐ[G i0] (G∞ ⊗[G i0] B₀) :=
    Algebra.TensorProduct.map
      (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j)
      (AlgHom.id (G i0) B₀)
  have hlifts : P ∈ Polynomial.lifts κj.toRingHom := by
    -- Proof comment: on-support coefficients use the descended lifts, while off-support
    -- coefficients lift by `0`.
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases hn : n ∈ P.support
    · refine ⟨zj (P.coeff n), ?_⟩
      exact hzj (P.coeff n) (Finset.mem_image.mpr ⟨n, hn, rfl⟩)
    · refine ⟨0, ?_⟩
      rw [map_zero, Polynomial.notMem_support_iff.mp hn]
  -- Proof comment: the polynomial-lifts API reconstructs a monic stage polynomial with the same
  -- image in the ambient tensor ring.
  obtain ⟨Q, hQmap, _, hQmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hP
  refine ⟨j, Q, hQmonic, ?_⟩
  simpa [κj, tail_stage_to_direct_limit_algHom] using hQmap

/-- Helper for Lemma 10.168.3: finitely many monic polynomials over the ambient direct-limit
tensor ring descend simultaneously to one common tail stage above `i0`. -/
theorem tail_exists_common_stage_monic_comm_relations
    (s : Finset C₀) (P : C₀ → Polynomial (G∞ ⊗[G i0] B₀))
    (hP : ∀ x ∈ s, (P x).Monic) :
    ∃ j : Set.Ici i0,
      letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
      ∃ Q : C₀ → Polynomial (G j.1 ⊗[G i0] B₀),
        (∀ x ∈ s, (Q x).Monic) ∧
          ∀ x ∈ s,
            Polynomial.map
              ((Algebra.TensorProduct.map
                (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j)
                (AlgHom.id (G i0) B₀)).toRingHom) (Q x) = P x := by
  classical
  revert P
  refine Finset.induction_on s ?_ ?_
  · intro P hP
    refine ⟨⟨i0, le_rfl⟩, fun _ ↦ 0, ?_⟩
    constructor
    · intro x hx
      exact False.elim (Finset.notMem_empty x hx)
    · intro x hx
      exact False.elim (Finset.notMem_empty x hx)
  · intro a s ha hs P hP
    -- Proof comment: descend the new monic polynomial for `a`, descend the old family on `s`,
    -- and then move both stagewise families to one common upper tail stage.
    obtain ⟨j₁, Q₁, hQ₁Monic, hQ₁Map⟩ :=
      tail_exists_stage_monic_comm_polynomial
        (G := G) (f := f) (i0 := i0) (B₀ := B₀) (P a) (hP a (Finset.mem_insert_self a s))
    letI : Algebra (G i0) (G j₁.1) := (f i0 j₁.1 j₁.2).toAlgebra
    have hQ₁Map' :
        Polynomial.map
            ((Algebra.TensorProduct.map
              (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j₁)
              (AlgHom.id (G i0) B₀)).toRingHom) Q₁ =
          P a := by
      -- Proof comment: the one-polynomial descent lemma uses the same stage-to-limit map, only
      -- written with local `let`s.
      simpa [tail_stage_to_direct_limit_algHom] using hQ₁Map
    obtain ⟨j₂, Q₂, hQ₂Monic, hQ₂Map⟩ :=
      hs P (fun x hx ↦ hP x (Finset.mem_insert_of_mem hx))
    letI : Algebra (G i0) (G j₂.1) := (f i0 j₂.1 j₂.2).toAlgebra
    obtain ⟨k, hj₁k, hj₂k⟩ := exists_ge_ge j₁.1 j₂.1
    let j : Set.Ici i0 := ⟨k, le_trans j₁.2 hj₁k⟩
    letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
    let τ₁ :
        (G j₁.1 ⊗[G i0] B₀) →ₐ[G i0] (G j.1 ⊗[G i0] B₀) :=
      Algebra.TensorProduct.map
        (tail_transition_algHom (G := G) (f := f) (i0 := i0) hj₁k)
        (AlgHom.id (G i0) B₀)
    let τ₂ :
        (G j₂.1 ⊗[G i0] B₀) →ₐ[G i0] (G j.1 ⊗[G i0] B₀) :=
      Algebra.TensorProduct.map
        (tail_transition_algHom (G := G) (f := f) (i0 := i0) hj₂k)
        (AlgHom.id (G i0) B₀)
    let κ :
        (G j.1 ⊗[G i0] B₀) →ₐ[G i0] (G∞ ⊗[G i0] B₀) :=
      Algebra.TensorProduct.map
        (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j)
        (AlgHom.id (G i0) B₀)
    let κ₁ :
        (G j₁.1 ⊗[G i0] B₀) →ₐ[G i0] (G∞ ⊗[G i0] B₀) :=
      Algebra.TensorProduct.map
        (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j₁)
        (AlgHom.id (G i0) B₀)
    let κ₂ :
        (G j₂.1 ⊗[G i0] B₀) →ₐ[G i0] (G∞ ⊗[G i0] B₀) :=
      Algebra.TensorProduct.map
        (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j₂)
        (AlgHom.id (G i0) B₀)
    have hκτ₁ : κ.toRingHom.comp τ₁.toRingHom = κ₁.toRingHom := by
      -- Proof comment: both composites agree on pure tensors, where the claim is the direct-limit
      -- relation `Ring.DirectLimit.of_f` on the left tensor factor.
      ext r b <;> simp [κ, κ₁, τ₁, tail_stage_to_direct_limit_algHom, tail_transition_algHom]
    have hκτ₂ : κ.toRingHom.comp τ₂.toRingHom = κ₂.toRingHom := by
      -- Proof comment: this is the same compatibility for the second descended polynomial family.
      ext r b <;> simp [κ, κ₂, τ₂, tail_stage_to_direct_limit_algHom, tail_transition_algHom]
    refine ⟨j, fun x ↦ if hxa : x = a then Polynomial.map τ₁.toRingHom Q₁
      else Polynomial.map τ₂.toRingHom (Q₂ x), ?_⟩
    constructor
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · -- Proof comment: the polynomial for the new generator stays monic after moving to `j`.
        simp only [dif_pos rfl]
        simpa [τ₁] using hQ₁Monic.map τ₁.toRingHom
      · have hxa : x ≠ a := by
          intro hxa
          apply ha
          simpa [hxa] using hx
        -- Proof comment: old monic relations remain monic after the stage transition.
        simp only [dif_neg hxa]
        simpa [τ₂] using (hQ₂Monic x hx).map τ₂.toRingHom
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · -- Proof comment: map the descended polynomial from `j₁` through the common upper stage.
        simp only [dif_pos rfl]
        calc
          Polynomial.map κ.toRingHom (Polynomial.map τ₁.toRingHom Q₁)
              = Polynomial.map (κ.toRingHom.comp τ₁.toRingHom) Q₁ := by
                  rw [Polynomial.map_map]
          _ = Polynomial.map κ₁.toRingHom Q₁ := by rw [hκτ₁]
          _ = P x := hQ₁Map'
      · have hxa : x ≠ a := by
          intro hxa
          apply ha
          simpa [hxa] using hx
        -- Proof comment: the old family keeps the same ambient image after passing through `j`.
        simp only [dif_neg hxa]
        calc
          Polynomial.map κ.toRingHom (Polynomial.map τ₂.toRingHom (Q₂ x))
              = Polynomial.map (κ.toRingHom.comp τ₂.toRingHom) (Q₂ x) := by
                  rw [Polynomial.map_map]
          _ = Polynomial.map κ₂.toRingHom (Q₂ x) := by rw [hκτ₂]
          _ = P x := hQ₂Map x hx

/-- Helper for Lemma 10.168.3: the cofinal tail above `i0` inherits the directed-order instance
needed by the imported finite-family tensor-descent theorem. -/
local instance tail_isDirectedOrder : IsDirectedOrder (Set.Ici i0) :=
  tail_index_isDirected (i0 := i0)

/-- Helper for Lemma 10.168.3: the tail system reindexes the original directed system over
`Set.Ici i0`. -/
abbrev tail_ring_family (j : Set.Ici i0) : Type v :=
  G j.1

/-- Helper for Lemma 10.168.3: each reindexed tail stage is a commutative ring. -/
local instance tail_ring_family_commRing (j : Set.Ici i0) :
    CommRing (tail_ring_family (G := G) (i0 := i0) j) :=
  inferInstance

/-- Helper for Lemma 10.168.3: each reindexed tail stage carries the induced `G i0`-algebra
structure. -/
noncomputable local instance tail_ring_family_algebra (j : Set.Ici i0) :
    Algebra (G i0) (tail_ring_family (G := G) (i0 := i0) j) :=
  tail_stageAlgebra (G := G) (f := f) (i0 := i0) j

/-- Helper for Lemma 10.168.3: the reindexed tail system carries the induced family of
`G i0`-algebra structures needed by tensor-descent lemmas. -/
noncomputable local instance tail_ring_family_algebra_family :
    ∀ j : Set.Ici i0, Algebra (G i0) (tail_ring_family (G := G) (i0 := i0) j) :=
  fun j ↦ tail_ring_family_algebra (G := G) (f := f) (i0 := i0) j

/-- Helper for Lemma 10.168.3: the tail transition maps are the original transition maps on the
underlying stages. -/
abbrev tail_ring_transition (j k : Set.Ici i0) (hjk : j ≤ k) :
    tail_ring_family (G := G) (i0 := i0) j →+*
      tail_ring_family (G := G) (i0 := i0) k :=
  f j.1 k.1 hjk

/-- Helper for Lemma 10.168.3: the tail transition algebra maps packaged as a reusable family. -/
noncomputable abbrev tail_transition_family (j k : Set.Ici i0) (hjk : j ≤ k) :
    letI : Algebra (G i0) (tail_ring_family (G := G) (i0 := i0) j) :=
      tail_ring_family_algebra (G := G) (f := f) (i0 := i0) j
    letI : Algebra (G i0) (tail_ring_family (G := G) (i0 := i0) k) :=
      tail_ring_family_algebra (G := G) (f := f) (i0 := i0) k
    tail_ring_family (G := G) (i0 := i0) j →ₐ[G i0]
      tail_ring_family (G := G) (i0 := i0) k :=
  tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk

/-- Helper for Lemma 10.168.3: the tail transition maps form a directed system of rings. -/
local instance tail_directedSystem :
    DirectedSystem (tail_ring_family (G := G) (i0 := i0))
      (fun j k hjk ↦ tail_ring_transition (G := G) (f := f) (i0 := i0) j k hjk) where
  map_self := by
    intro j x
    exact DirectedSystem.map_self (f := fun i j hij ↦ f i j hij) x
  map_map := by
    intro k j i hij hjk x
    exact DirectedSystem.map_map (f := fun i j hij ↦ f i j hij) hij hjk x

/-- Helper for Lemma 10.168.3: the tail transition algebra maps also form a directed system when
viewed as a family of functions. -/
local instance tail_transition_directedSystem :
    DirectedSystem (tail_ring_family (G := G) (i0 := i0))
      (fun j k hjk ↦
        (tail_transition_family (G := G) (f := f) (i0 := i0) j k hjk :
          tail_ring_family (G := G) (i0 := i0) j →
            tail_ring_family (G := G) (i0 := i0) k)) where
  map_self := by
    intro j x
    exact DirectedSystem.map_self (f := fun i j hij ↦ f i j hij) x
  map_map := by
    intro k j i hij hjk x
    exact DirectedSystem.map_map (f := fun i j hij ↦ f i j hij) hij hjk x

/-- Helper for Lemma 10.168.3: the tail transition algebra maps form a directed system after
coercing to ring homomorphisms. -/
local instance tail_transition_algHom_directedSystem :
    DirectedSystem (tail_ring_family (G := G) (i0 := i0))
      (fun j k hjk ↦
        (tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk : G j.1 →+* G k.1)) where
  map_self := by
    intro j x
    exact DirectedSystem.map_self (f := fun i j hij ↦ f i j hij) x
  map_map := by
    intro k j i hij hjk x
    exact DirectedSystem.map_map (f := fun i j hij ↦ f i j hij) hij hjk x

/-- Helper for Lemma 10.168.3: the direct limit of the tail above `i0` carries the canonical
`G i0`-algebra structure coming from the base tail stage. -/
noncomputable local instance tail_directLimit_algebra :
    Algebra (G i0)
      (Ring.DirectLimit
        (tail_ring_family (G := G) (i0 := i0))
        (fun j k hjk ↦ tail_ring_transition (G := G) (f := f) (i0 := i0) j k hjk)) :=
  (Ring.DirectLimit.of
    (tail_ring_family (G := G) (i0 := i0))
    (fun j k hjk ↦ tail_ring_transition (G := G) (f := f) (i0 := i0) j k hjk)
    ⟨i0, le_rfl⟩).toAlgebra

/-- Helper for Lemma 10.168.3: the tail direct limit built from the algebra-map presentation also
carries the canonical `G i0`-algebra structure from the base tail stage. -/
noncomputable local instance tail_transition_algHom_directLimit_algebra :
    Algebra (G i0)
      (Ring.DirectLimit
        (tail_ring_family (G := G) (i0 := i0))
        (fun j k hjk ↦
          (tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk : G j.1 →+* G k.1))) :=
  (Ring.DirectLimit.of
    (tail_ring_family (G := G) (i0 := i0))
    (fun j k hjk ↦
      (tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk : G j.1 →+* G k.1))
    ⟨i0, le_rfl⟩).toAlgebra

/-- Helper for Lemma 10.168.3: the owner theorem's tail-system specialization uses the standard
arbitrary-stage `G i0`-algebra structure on the tail direct limit. -/
@[reducible]
noncomputable def owner_tail_directLimitAlgebra :
    Algebra (G i0)
      (Ring.DirectLimit
        (tail_ring_family (G := G) (i0 := i0))
        (fun j k hjk ↦
          (tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk : G j.1 →+* G k.1))) :=
  let j : Set.Ici i0 := Classical.arbitrary (Set.Ici i0)
  letI : Algebra (G i0) (G j.1) := tail_ring_family_algebra (G := G) (f := f) (i0 := i0) j
  ((Ring.DirectLimit.of
      (tail_ring_family (G := G) (i0 := i0))
      (fun j' k' hjk ↦
        (tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk : G j'.1 →+* G k'.1))
      j).comp
    (algebraMap (G i0) (G j.1))).toAlgebra

/-- Helper for Lemma 10.168.3: the owner theorem's arbitrary-stage algebra map to the tail direct
limit agrees with the canonical one coming from the base tail stage `⟨i0, le_rfl⟩`. -/
theorem owner_tail_directLimit_algebraMap_eq (a : G i0) :
    let tailLimit :=
      Ring.DirectLimit
        (tail_ring_family (G := G) (i0 := i0))
        (fun j k hjk ↦
          (tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk : G j.1 →+* G k.1))
    letI : Algebra (G i0) tailLimit := owner_tail_directLimitAlgebra (G := G) (f := f) (i0 := i0)
    algebraMap (G i0) tailLimit a =
      Ring.DirectLimit.of
        (tail_ring_family (G := G) (i0 := i0))
        (fun j k hjk ↦
          (tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk : G j.1 →+* G k.1))
        ⟨i0, le_rfl⟩ a := by
  classical
  let tailLimit :=
    Ring.DirectLimit
      (tail_ring_family (G := G) (i0 := i0))
      (fun j k hjk ↦
        (tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk : G j.1 →+* G k.1))
  let j : Set.Ici i0 := Classical.arbitrary (Set.Ici i0)
  letI : Algebra (G i0) tailLimit := owner_tail_directLimitAlgebra (G := G) (f := f) (i0 := i0)
  obtain ⟨k, hjk, h0k⟩ := exists_ge_ge j ⟨i0, le_rfl⟩
  change
    Ring.DirectLimit.of
        (tail_ring_family (G := G) (i0 := i0))
        (fun j' k' hjk ↦
          (tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk : G j'.1 →+* G k'.1))
        j ((f i0 j.1 j.2) a) =
      Ring.DirectLimit.of
        (tail_ring_family (G := G) (i0 := i0))
        (fun j' k' hjk ↦
          (tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk : G j'.1 →+* G k'.1))
        ⟨i0, le_rfl⟩ a
  calc
    Ring.DirectLimit.of
        (tail_ring_family (G := G) (i0 := i0))
        (fun j' k' hjk ↦
          (tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk : G j'.1 →+* G k'.1))
        j ((f i0 j.1 j.2) a) =
      Ring.DirectLimit.of
        (tail_ring_family (G := G) (i0 := i0))
        (fun j' k' hjk ↦
          (tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk : G j'.1 →+* G k'.1))
        k (f j.1 k.1 hjk ((f i0 j.1 j.2) a)) := by
          symm
          exact Ring.DirectLimit.of_f
            (G := tail_ring_family (G := G) (i0 := i0))
            (f := fun j' k' hjk ↦
              (tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk : G j'.1 →+* G k'.1))
            (i := j) (j := k) (hij := hjk) (x := (f i0 j.1 j.2) a)
    _ =
      Ring.DirectLimit.of
        (tail_ring_family (G := G) (i0 := i0))
        (fun j' k' hjk ↦
          (tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk : G j'.1 →+* G k'.1))
        k (f i0 k.1 (le_trans j.2 hjk) a) := by
          rw [tail_stage_transition_commutes (G := G) (f := f) (i0 := i0) hjk]
    _ =
      Ring.DirectLimit.of
        (tail_ring_family (G := G) (i0 := i0))
        (fun j' k' hjk ↦
          (tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk : G j'.1 →+* G k'.1))
        k (f i0 k.1 h0k a) := by
          have hproof : le_trans j.2 hjk = h0k := Subsingleton.elim _ _
          cases hproof
          rfl
    _ =
      Ring.DirectLimit.of
        (tail_ring_family (G := G) (i0 := i0))
        (fun j' k' hjk ↦
          (tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk : G j'.1 →+* G k'.1))
        ⟨i0, le_rfl⟩ a := by
          exact Ring.DirectLimit.of_f
            (G := tail_ring_family (G := G) (i0 := i0))
            (f := fun j' k' hjk ↦
              (tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk : G j'.1 →+* G k'.1))
            (i := ⟨i0, le_rfl⟩) (j := k) (hij := h0k) (x := a)

/-- Helper for Lemma 10.168.3: the direct limit of the tail above `i0` identifies with the
original direct limit as a `G i0`-algebra. -/
noncomputable def tail_directLimitAlgEquivToFull :
    Ring.DirectLimit
        (tail_ring_family (G := G) (i0 := i0))
        (fun j k hjk ↦ tail_ring_transition (G := G) (f := f) (i0 := i0) j k hjk) ≃ₐ[G i0] G∞ where
  __ := tail_directLimitIso (G := G) (f := f) (i0 := i0) (B := G∞) (RingEquiv.refl G∞)
  commutes' a := by
    -- Proof comment: both algebra maps are represented by the distinguished base stage `i0`.
    change
      tail_directLimitIso (G := G) (f := f) (i0 := i0) (B := G∞) (RingEquiv.refl G∞)
          (Ring.DirectLimit.of
            (tail_ring_family (G := G) (i0 := i0))
            (fun j k hjk ↦ tail_ring_transition (G := G) (f := f) (i0 := i0) j k hjk)
            ⟨i0, le_rfl⟩ a) =
        Ring.DirectLimit.of G (fun i j hij ↦ f i j hij) i0 a
    simp [tail_directLimitIso, tail_directLimit_to_full]

/-- Helper for Lemma 10.168.3: the tail/full colimit equivalence sends a tail stage class to the
corresponding class in the original direct limit. -/
theorem tail_directLimitAlgEquivToFull_of (j : Set.Ici i0) (x : G j.1) :
    tail_directLimitAlgEquivToFull (G := G) (f := f) (i0 := i0)
        (Ring.DirectLimit.of
          (tail_ring_family (G := G) (i0 := i0))
          (fun j' k' hjk ↦ tail_ring_transition (G := G) (f := f) (i0 := i0) j' k' hjk)
          j x) =
      Ring.DirectLimit.of G (fun i j hij ↦ f i j hij) j.1 x := by
  -- Proof comment: `tail_directLimit_to_full` simply forgets that the chosen stage lies in the
  -- tail.
  simp [tail_directLimitAlgEquivToFull, tail_directLimitIso, tail_directLimit_to_full]

/-- Helper for Lemma 10.168.3: transporting the owner theorem's tail direct-limit algebra
structure to the ambient direct limit gives the same tail/full equivalence. -/
noncomputable def owner_tail_directLimitAlgEquivToFull :
    let tailLimit :=
      Ring.DirectLimit
        (tail_ring_family (G := G) (i0 := i0))
        (fun j k hjk ↦
          (tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk : G j.1 →+* G k.1))
    letI : Algebra (G i0) tailLimit := owner_tail_directLimitAlgebra (G := G) (f := f) (i0 := i0)
    tailLimit ≃ₐ[G i0] G∞ :=
  let tailLimit :=
    Ring.DirectLimit
      (tail_ring_family (G := G) (i0 := i0))
      (fun j k hjk ↦
        (tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk : G j.1 →+* G k.1))
  letI : Algebra (G i0) tailLimit := owner_tail_directLimitAlgebra (G := G) (f := f) (i0 := i0)
  { __ := tail_directLimitIso (G := G) (f := f) (i0 := i0) (B := G∞) (RingEquiv.refl G∞)
    commutes' := fun a ↦ by
      rw [owner_tail_directLimit_algebraMap_eq (G := G) (f := f) (i0 := i0)]
      rfl }

/-- Helper for Lemma 10.168.3: the transported owner-style tail/full equivalence still sends a
tail stage class to the corresponding ambient direct-limit class. -/
theorem owner_tail_directLimitAlgEquivToFull_of (j : Set.Ici i0) (x : G j.1) :
    let tailLimit :=
      Ring.DirectLimit
        (tail_ring_family (G := G) (i0 := i0))
        (fun j' k' hjk ↦
          (tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk : G j'.1 →+* G k'.1))
    letI : Algebra (G i0) tailLimit := owner_tail_directLimitAlgebra (G := G) (f := f) (i0 := i0)
    owner_tail_directLimitAlgEquivToFull (G := G) (f := f) (i0 := i0)
        (Ring.DirectLimit.of
          (tail_ring_family (G := G) (i0 := i0))
          (fun j' k' hjk ↦
            (tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk : G j'.1 →+* G k'.1))
          j x) =
      Ring.DirectLimit.of G (fun i j hij ↦ f i j hij) j.1 x := by
  rfl

/-- Helper for Lemma 10.168.3: the canonical map from a tail stage into the tail direct limit is
compatible with the `G i0`-algebra structure induced from the base stage. -/
theorem tail_stage_to_tail_direct_limit_algHom_commutes
    (j : Set.Ici i0) (a : G i0) :
    Ring.DirectLimit.of
        (tail_ring_family (G := G) (i0 := i0))
        (fun j' k' hjk ↦ tail_ring_transition (G := G) (f := f) (i0 := i0) j' k' hjk)
        j ((f i0 j.1 j.2) a) =
      algebraMap (G i0)
        (Ring.DirectLimit
          (tail_ring_family (G := G) (i0 := i0))
          (fun j' k' hjk ↦ tail_ring_transition (G := G) (f := f) (i0 := i0) j' k' hjk)) a := by
  -- Proof comment: the tail direct-limit `algebraMap` is represented by the base tail stage
  -- `⟨i0, le_rfl⟩`, so the compatibility reduces to the direct-limit relation `of_f`.
  change
    Ring.DirectLimit.of
        (tail_ring_family (G := G) (i0 := i0))
        (fun j' k' hjk ↦ tail_ring_transition (G := G) (f := f) (i0 := i0) j' k' hjk)
        j ((f i0 j.1 j.2) a) =
      Ring.DirectLimit.of
        (tail_ring_family (G := G) (i0 := i0))
        (fun j' k' hjk ↦ tail_ring_transition (G := G) (f := f) (i0 := i0) j' k' hjk)
        ⟨i0, le_rfl⟩ a
  simpa [tail_ring_transition] using
    (Ring.DirectLimit.of_f
      (G := tail_ring_family (G := G) (i0 := i0))
      (f := fun j' k' hjk ↦ tail_ring_transition (G := G) (f := f) (i0 := i0) j' k' hjk)
      (i := ⟨i0, le_rfl⟩) (j := j) (hij := j.2) (x := a))

/-- Helper for Lemma 10.168.3: the canonical map from a tail stage to the tail direct limit is an
algebra homomorphism over the distinguished base stage. -/
noncomputable abbrev tail_stage_to_tail_direct_limit_algHom
    (j : Set.Ici i0) :
    letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
    G j.1 →ₐ[G i0]
      Ring.DirectLimit
        (tail_ring_family (G := G) (i0 := i0))
        (fun j' k' hjk ↦ tail_ring_transition (G := G) (f := f) (i0 := i0) j' k' hjk) :=
  letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
  { toRingHom :=
      Ring.DirectLimit.of
        (tail_ring_family (G := G) (i0 := i0))
        (fun j' k' hjk ↦ tail_ring_transition (G := G) (f := f) (i0 := i0) j' k' hjk)
        j
    commutes' :=
      tail_stage_to_tail_direct_limit_algHom_commutes (G := G) (f := f) (i0 := i0) j }

/-- Helper for Lemma 10.168.3: the canonical tensor map from a tail stage to the tail direct
limit, written using the same ring-transition presentation as `tail_directLimitAlgEquivToFull`. -/
noncomputable abbrev tail_stageTensorMap
    {X : Type*} [CommRing X] [Algebra (G i0) X] (j : Set.Ici i0) :
    letI : ∀ j' : Set.Ici i0, Algebra (G i0) (tail_ring_family (G := G) (i0 := i0) j') :=
      tail_ring_family_algebra_family (G := G) (f := f) (i0 := i0)
    letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
    G j.1 ⊗[G i0] X →ₗ[G i0]
      ((Ring.DirectLimit
          (tail_ring_family (G := G) (i0 := i0))
        (fun j' k' hjk ↦ tail_ring_transition (G := G) (f := f) (i0 := i0) j' k' hjk))
        ⊗[G i0] X) :=
  letI : ∀ j' : Set.Ici i0, Algebra (G i0) (tail_ring_family (G := G) (i0 := i0) j') :=
    tail_ring_family_algebra_family (G := G) (f := f) (i0 := i0)
  letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
  LinearMap.rTensor X
    ((tail_stage_to_tail_direct_limit_algHom (G := G) (f := f) (i0 := i0) j).toLinearMap)

/-- Helper for Lemma 10.168.3: composing the canonical map from a tail stage into the tail direct
limit with the tail/full colimit equivalence recovers the literal stage map into the ambient
direct limit. -/
theorem tail_directLimitAlgEquivToFull_comp_tail_stage_to_tail_direct_limit_algHom
    (j : Set.Ici i0) :
    letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
    (tail_directLimitAlgEquivToFull (G := G) (f := f) (i0 := i0)).toAlgHom.comp
        (tail_stage_to_tail_direct_limit_algHom (G := G) (f := f) (i0 := i0) j) =
      tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j := by
  letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
  -- Proof comment: both algebra maps send `x : G j.1` to the same direct-limit class represented
  -- by `x` at the stage `j`.
  apply DFunLike.ext
  intro x
  exact tail_directLimitAlgEquivToFull_of (G := G) (f := f) (i0 := i0) j x

/-- Helper for Lemma 10.168.3: the generic `stageTensorMap` on the tail system matches the
explicit tensor map into the original direct limit after transporting along the tail/full colimit
equivalence. -/
theorem tail_stageTensorMap_to_full
    {X : Type*} [CommRing X] [Algebra (G i0) X]
    (j : Set.Ici i0)
    (z :
      letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
      G j.1 ⊗[G i0] X) :
    letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
    letI : ∀ j' : Set.Ici i0, Algebra (G i0) (tail_ring_family (G := G) (i0 := i0) j') :=
      tail_ring_family_algebra_family (G := G) (f := f) (i0 := i0)
    (Algebra.TensorProduct.congr
      (tail_directLimitAlgEquivToFull (G := G) (f := f) (i0 := i0))
      (AlgEquiv.refl : X ≃ₐ[G i0] X))
      (tail_stageTensorMap (G := G) (f := f) (i0 := i0) j z) =
      (Algebra.TensorProduct.map
        (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j)
        (AlgHom.id (G i0) X)) z := by
  -- Route correction: instead of normalizing transported tensors elementwise, first rewrite the
  -- coefficient map through the colimit equivalence and then tensor that map.
  letI : ∀ j' : Set.Ici i0, Algebra (G i0) (tail_ring_family (G := G) (i0 := i0) j') :=
    tail_ring_family_algebra_family (G := G) (f := f) (i0 := i0)
  letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp [tail_stageTensorMap]
  · intro a x
    -- Proof comment: on pure tensors, the transported map is the tensor product of the composed
    -- coefficient map identified in the preceding helper lemma.
    change
      (tail_directLimitAlgEquivToFull (G := G) (f := f) (i0 := i0)
        (Ring.DirectLimit.of
          (tail_ring_family (G := G) (i0 := i0))
          (fun j' k' hjk ↦ tail_ring_transition (G := G) (f := f) (i0 := i0) j' k' hjk)
          j a)) ⊗ₜ[G i0] x =
        Ring.DirectLimit.of G (fun i j hij ↦ f i j hij) j.1 a ⊗ₜ[G i0] x
    exact congrArg (fun r : G∞ ↦ r ⊗ₜ[G i0] x)
      (tail_directLimitAlgEquivToFull_of (G := G) (f := f) (i0 := i0) j a)
  · intro z₁ z₂ hz₁ hz₂
    -- Proof comment: both sides are `G i0`-linear, so additivity finishes the tensor induction.
    calc
      (Algebra.TensorProduct.congr
          (tail_directLimitAlgEquivToFull (G := G) (f := f) (i0 := i0))
          (AlgEquiv.refl : X ≃ₐ[G i0] X))
          (tail_stageTensorMap (G := G) (f := f) (i0 := i0) j (z₁ + z₂))
          =
        (Algebra.TensorProduct.congr
            (tail_directLimitAlgEquivToFull (G := G) (f := f) (i0 := i0))
            (AlgEquiv.refl : X ≃ₐ[G i0] X))
            (tail_stageTensorMap (G := G) (f := f) (i0 := i0) j z₁) +
          (Algebra.TensorProduct.congr
            (tail_directLimitAlgEquivToFull (G := G) (f := f) (i0 := i0))
            (AlgEquiv.refl : X ≃ₐ[G i0] X))
            (tail_stageTensorMap (G := G) (f := f) (i0 := i0) j z₂) := by
              simp [tail_stageTensorMap]
      _ =
        (Algebra.TensorProduct.map
          (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j)
          (AlgHom.id (G i0) X)) z₁ +
          (Algebra.TensorProduct.map
            (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j)
            (AlgHom.id (G i0) X)) z₂ := by
              rw [hz₁, hz₂]
      _ =
        (Algebra.TensorProduct.map
          (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j)
          (AlgHom.id (G i0) X)) (z₁ + z₂) := by
              simp

/-- Helper for Lemma 10.168.3: an ambient zero equation for a tail-stage tensor forces the
explicit tail tensor map to agree with its value at zero. -/
theorem tail_stageTensorMap_eq_zero
    (j : Set.Ici i0)
    (z :
      letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
      G j.1 ⊗[G i0] C₀)
    (hz :
      letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
      (Algebra.TensorProduct.map
        (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j)
        (AlgHom.id (G i0) C₀)) z = 0) :
    letI : ∀ j' : Set.Ici i0, Algebra (G i0) (tail_ring_family (G := G) (i0 := i0) j') :=
      tail_ring_family_algebra_family (G := G) (f := f) (i0 := i0)
    tail_stageTensorMap (G := G) (f := f) (i0 := i0) j z =
      tail_stageTensorMap (G := G) (f := f) (i0 := i0) j 0 := by
  letI : ∀ j' : Set.Ici i0, Algebra (G i0) (tail_ring_family (G := G) (i0 := i0) j') :=
    tail_ring_family_algebra_family (G := G) (f := f) (i0 := i0)
  letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
  let e := tail_directLimitAlgEquivToFull (G := G) (f := f) (i0 := i0)
  -- Proof comment: transport both sides to the ambient direct-limit tensor product, where the
  -- assumed vanishing identifies the image of `z` with the image of `0`.
  apply (Algebra.TensorProduct.congr e (AlgEquiv.refl : C₀ ≃ₐ[G i0] C₀)).injective
  calc
    (Algebra.TensorProduct.congr e (AlgEquiv.refl : C₀ ≃ₐ[G i0] C₀))
        (tail_stageTensorMap (G := G) (f := f) (i0 := i0) j z) =
      (Algebra.TensorProduct.map
        (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j)
        (AlgHom.id (G i0) C₀)) z := by
          simpa using
            (tail_stageTensorMap_to_full
              (G := G) (f := f) (i0 := i0) (X := C₀) j z)
    _ = 0 := hz
    _ =
      (Algebra.TensorProduct.map
        (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j)
        (AlgHom.id (G i0) C₀)) (0 : G j.1 ⊗[G i0] C₀) := by
          simp
    _ =
      (Algebra.TensorProduct.congr e (AlgEquiv.refl : C₀ ≃ₐ[G i0] C₀))
        (tail_stageTensorMap (G := G) (f := f) (i0 := i0) j 0) := by
          symm
          simpa using
            (tail_stageTensorMap_to_full
              (G := G) (f := f) (i0 := i0) (X := C₀) j
              (0 : G j.1 ⊗[G i0] C₀))

/-- Helper for Lemma 10.168.3: the explicit tail-stage coefficient map agrees with the generic
coefficient map used by the owner theorem's `stageTensorMap`. -/
theorem tail_stage_to_tail_direct_limit_isScalarTower
    (j : Set.Ici i0) :
    let tailLimit :=
      Ring.DirectLimit
        (tail_ring_family (G := G) (i0 := i0))
        (fun j' k' hjk ↦ tail_ring_transition (G := G) (f := f) (i0 := i0) j' k' hjk)
    letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
    letI : Algebra (G j.1) tailLimit :=
      (Ring.DirectLimit.of
        (tail_ring_family (G := G) (i0 := i0))
        (fun j' k' hjk ↦ tail_ring_transition (G := G) (f := f) (i0 := i0) j' k' hjk)
        j).toAlgebra
    IsScalarTower (G i0) (G j.1) tailLimit := by
  let tailLimit :=
    Ring.DirectLimit
      (tail_ring_family (G := G) (i0 := i0))
      (fun j' k' hjk ↦ tail_ring_transition (G := G) (f := f) (i0 := i0) j' k' hjk)
  letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
  letI : Algebra (G j.1) tailLimit :=
    (Ring.DirectLimit.of
      (tail_ring_family (G := G) (i0 := i0))
      (fun j' k' hjk ↦ tail_ring_transition (G := G) (f := f) (i0 := i0) j' k' hjk)
      j).toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun a ↦ by
    symm
    simpa [tail_ring_transition] using
      (tail_stage_to_tail_direct_limit_algHom_commutes
        (G := G) (f := f) (i0 := i0) j a)

/-- Helper for Lemma 10.168.3: the explicit tail-stage coefficient map agrees with the generic
coefficient map used by the owner theorem's `stageTensorMap`. -/
theorem tail_stage_to_tail_direct_limit_linearMap_eq
    (j : Set.Ici i0) :
    let tailLimit :=
      Ring.DirectLimit
        (tail_ring_family (G := G) (i0 := i0))
        (fun j' k' hjk ↦ tail_ring_transition (G := G) (f := f) (i0 := i0) j' k' hjk)
    letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
    letI : Algebra (G j.1) tailLimit :=
      (Ring.DirectLimit.of
        (tail_ring_family (G := G) (i0 := i0))
        (fun j' k' hjk ↦ tail_ring_transition (G := G) (f := f) (i0 := i0) j' k' hjk)
        j).toAlgebra
    letI : IsScalarTower (G i0) (G j.1) tailLimit :=
      tail_stage_to_tail_direct_limit_isScalarTower (G := G) (f := f) (i0 := i0) j
    ((tail_stage_to_tail_direct_limit_algHom (G := G) (f := f) (i0 := i0) j).toLinearMap :
      G j.1 →ₗ[G i0] tailLimit) =
      (Algebra.linearMap (G j.1) tailLimit).restrictScalars (G i0) := by
  let tailLimit :=
    Ring.DirectLimit
      (tail_ring_family (G := G) (i0 := i0))
      (fun j' k' hjk ↦ tail_ring_transition (G := G) (f := f) (i0 := i0) j' k' hjk)
  letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
  letI : Algebra (G j.1) tailLimit :=
    (Ring.DirectLimit.of
      (tail_ring_family (G := G) (i0 := i0))
      (fun j' k' hjk ↦ tail_ring_transition (G := G) (f := f) (i0 := i0) j' k' hjk)
      j).toAlgebra
  letI : IsScalarTower (G i0) (G j.1) tailLimit :=
    tail_stage_to_tail_direct_limit_isScalarTower (G := G) (f := f) (i0 := i0) j
  -- Proof comment: both linear maps are induced by the same canonical ring homomorphism from the
  -- chosen tail stage into the tail direct limit.
  apply LinearMap.ext
  intro a
  rfl

/-- Helper for Lemma 10.168.3: transporting the owner `stageTensorMap` for the tail system along
the tail/full direct-limit equivalence recovers the explicit tensor map into the ambient direct
limit. -/
theorem owner_stageTensorMap_to_full
    (j : Set.Ici i0)
    (z :
      letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
      G j.1 ⊗[G i0] C₀) :
    letI : ∀ j' : Set.Ici i0, Algebra (G i0) (tail_ring_family (G := G) (i0 := i0) j') :=
      tail_ring_family_algebra_family (G := G) (f := f) (i0 := i0)
    letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
    let tailLimit :=
      Ring.DirectLimit
        (tail_ring_family (G := G) (i0 := i0))
        (fun j' k' hjk ↦
          (tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk : G j'.1 →+* G k'.1))
    letI : Algebra (G i0) tailLimit := owner_tail_directLimitAlgebra (G := G) (f := f) (i0 := i0)
    (Algebra.TensorProduct.congr
      (owner_tail_directLimitAlgEquivToFull (G := G) (f := f) (i0 := i0))
      (AlgEquiv.refl : C₀ ≃ₐ[G i0] C₀))
      (_root_.stageTensorMap
        (A := G i0)
        (R := tail_ring_family (G := G) (i0 := i0))
        (f := fun _ _ hjk ↦
          tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk)
        (X := C₀) j z) =
      (Algebra.TensorProduct.map
        (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j)
        (AlgHom.id (G i0) C₀)) z := by
  letI : ∀ j' : Set.Ici i0, Algebra (G i0) (tail_ring_family (G := G) (i0 := i0) j') :=
    tail_ring_family_algebra_family (G := G) (f := f) (i0 := i0)
  letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
  let tailLimit :=
    Ring.DirectLimit
      (tail_ring_family (G := G) (i0 := i0))
      (fun j' k' hjk ↦
        (tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk : G j'.1 →+* G k'.1))
  letI : Algebra (G i0) tailLimit := owner_tail_directLimitAlgebra (G := G) (f := f) (i0 := i0)
  let e := owner_tail_directLimitAlgEquivToFull (G := G) (f := f) (i0 := i0)
  -- Proof comment: on pure tensors the owner `stageTensorMap` uses the canonical stage class in
  -- the tail direct limit, and the tail/full equivalence sends that class to the ambient one.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simpa using (Algebra.TensorProduct.congr e (AlgEquiv.refl : C₀ ≃ₐ[G i0] C₀)).map_zero
  · intro r x
    simpa [e, _root_.stageTensorMap] using
      congrArg (fun s : G∞ ↦ s ⊗ₜ[G i0] x)
        (owner_tail_directLimitAlgEquivToFull_of (G := G) (f := f) (i0 := i0) j r)
  · intro z₁ z₂ hz₁ hz₂
    calc
      (Algebra.TensorProduct.congr e (AlgEquiv.refl : C₀ ≃ₐ[G i0] C₀))
          ((_root_.stageTensorMap
            (A := G i0)
            (R := tail_ring_family (G := G) (i0 := i0))
            (f := fun j' k' hjk ↦
              tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk)
            (X := C₀) j) (z₁ + z₂)) =
        (Algebra.TensorProduct.congr e (AlgEquiv.refl : C₀ ≃ₐ[G i0] C₀))
          (((_root_.stageTensorMap
            (A := G i0)
            (R := tail_ring_family (G := G) (i0 := i0))
            (f := fun j' k' hjk ↦
              tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk)
            (X := C₀) j) z₁) +
            ((_root_.stageTensorMap
              (A := G i0)
              (R := tail_ring_family (G := G) (i0 := i0))
              (f := fun j' k' hjk ↦
                tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk)
              (X := C₀) j) z₂)) := by
            exact congrArg
              (Algebra.TensorProduct.congr e (AlgEquiv.refl : C₀ ≃ₐ[G i0] C₀))
              ((_root_.stageTensorMap
                (A := G i0)
                (R := tail_ring_family (G := G) (i0 := i0))
                (f := fun j' k' hjk ↦
                  tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk)
                (X := C₀) j).map_add z₁ z₂)
      _ =
        (Algebra.TensorProduct.congr e (AlgEquiv.refl : C₀ ≃ₐ[G i0] C₀))
            ((_root_.stageTensorMap
              (A := G i0)
              (R := tail_ring_family (G := G) (i0 := i0))
              (f := fun j' k' hjk ↦
                tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk)
              (X := C₀) j) z₁) +
          (Algebra.TensorProduct.congr e (AlgEquiv.refl : C₀ ≃ₐ[G i0] C₀))
            ((_root_.stageTensorMap
              (A := G i0)
              (R := tail_ring_family (G := G) (i0 := i0))
              (f := fun j' k' hjk ↦
                tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk)
              (X := C₀) j) z₂) := by
            simpa using
              (Algebra.TensorProduct.congr e (AlgEquiv.refl : C₀ ≃ₐ[G i0] C₀)).map_add
                ((_root_.stageTensorMap
                  (A := G i0)
                  (R := tail_ring_family (G := G) (i0 := i0))
                  (f := fun j' k' hjk ↦
                    tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk)
                  (X := C₀) j) z₁)
                ((_root_.stageTensorMap
                  (A := G i0)
                  (R := tail_ring_family (G := G) (i0 := i0))
                  (f := fun j' k' hjk ↦
                    tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk)
                  (X := C₀) j) z₂)
      _ =
        (Algebra.TensorProduct.map
          (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j)
          (AlgHom.id (G i0) C₀)) z₁ +
          (Algebra.TensorProduct.map
            (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j)
            (AlgHom.id (G i0) C₀)) z₂ := by
              rw [hz₁, hz₂]
      _ =
        (Algebra.TensorProduct.map
          (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j)
          (AlgHom.id (G i0) C₀)) (z₁ + z₂) := by
              symm
              exact (Algebra.TensorProduct.map
                (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j)
                (AlgHom.id (G i0) C₀)).map_add z₁ z₂

/-- Helper for Lemma 10.168.3: an ambient vanishing equation yields the owner-surface equality
needed to invoke finite-family tensor descent on the tail system. -/
theorem owner_stageTensorMap_eq_zero_of_ambient_zero
    (j : Set.Ici i0)
    (z :
      letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
      G j.1 ⊗[G i0] C₀)
    (hz :
      letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
      (Algebra.TensorProduct.map
        (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j)
        (AlgHom.id (G i0) C₀)) z = 0) :
    letI : ∀ j' : Set.Ici i0, Algebra (G i0) (tail_ring_family (G := G) (i0 := i0) j') :=
      tail_ring_family_algebra_family (G := G) (f := f) (i0 := i0)
    _root_.stageTensorMap
        (A := G i0)
        (R := tail_ring_family (G := G) (i0 := i0))
        (f := fun _ _ hjk ↦
          tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk)
        (X := C₀) j z =
    _root_.stageTensorMap
        (A := G i0)
        (R := tail_ring_family (G := G) (i0 := i0))
        (f := fun _ _ hjk ↦
          tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk)
        (X := C₀) j 0 := by
  letI : ∀ j' : Set.Ici i0, Algebra (G i0) (tail_ring_family (G := G) (i0 := i0) j') :=
    tail_ring_family_algebra_family (G := G) (f := f) (i0 := i0)
  letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
  let tailLimit :=
    Ring.DirectLimit
      (tail_ring_family (G := G) (i0 := i0))
      (fun j' k' hjk ↦
        (tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk : G j'.1 →+* G k'.1))
  letI : Algebra (G i0) tailLimit := owner_tail_directLimitAlgebra (G := G) (f := f) (i0 := i0)
  let e := owner_tail_directLimitAlgEquivToFull (G := G) (f := f) (i0 := i0)
  -- Proof comment: transport the owner `stageTensorMap` to the ambient direct-limit tensor
  -- product, where the assumed vanishing identifies the two images immediately.
  apply (Algebra.TensorProduct.congr e (AlgEquiv.refl : C₀ ≃ₐ[G i0] C₀)).injective
  calc
    (Algebra.TensorProduct.congr e (AlgEquiv.refl : C₀ ≃ₐ[G i0] C₀))
        (_root_.stageTensorMap
          (A := G i0)
          (R := tail_ring_family (G := G) (i0 := i0))
          (f := fun j' k' hjk ↦
            tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk)
          (X := C₀) j z) =
      (Algebra.TensorProduct.map
        (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j)
        (AlgHom.id (G i0) C₀)) z := by
          simpa [e] using owner_stageTensorMap_to_full
            (G := G) (f := f) (i0 := i0) (C₀ := C₀) j z
    _ = 0 := hz
    _ =
      (Algebra.TensorProduct.map
        (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j)
        (AlgHom.id (G i0) C₀)) (0 : G j.1 ⊗[G i0] C₀) := by
          simp
    _ =
      (Algebra.TensorProduct.congr e (AlgEquiv.refl : C₀ ≃ₐ[G i0] C₀))
        (_root_.stageTensorMap
          (A := G i0)
          (R := tail_ring_family (G := G) (i0 := i0))
          (f := fun j' k' hjk ↦
            tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk)
          (X := C₀) j 0) := by
          symm
          simpa [e] using owner_stageTensorMap_to_full
            (G := G) (f := f) (i0 := i0) (C₀ := C₀) j (0 : G j.1 ⊗[G i0] C₀)

/-- Helper for Lemma 10.168.3: a comm-oriented monic relation at one stage makes the literal
generator in the usual stage base change integral. -/
theorem stage_generator_isIntegral_of_comm_monic_relation
    {j : Set.Ici i0} :
    letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
    ∀ (x : C₀) (Q : Polynomial (G j.1 ⊗[G i0] B₀)),
      Q.Monic →
      let θj : (G j.1 ⊗[G i0] B₀) →ₐ[G i0] (G j.1 ⊗[G i0] C₀) :=
        Algebra.TensorProduct.map (AlgHom.id (G i0) (G j.1)) φ₀
      letI : Algebra (G j.1 ⊗[G i0] B₀) (G j.1 ⊗[G i0] C₀) := θj.toRingHom.toAlgebra
      Polynomial.aeval (((1 : G j.1) ⊗ₜ[G i0] x) : G j.1 ⊗[G i0] C₀) Q = 0 →
      letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
      let S : Type _ := B₀ ⊗[G i0] G j.1
      IsIntegral S
        ((Algebra.TensorProduct.includeRight : C₀ →ₐ[B₀] (S ⊗[B₀] C₀)) x) := by
  letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
  intro x Q hQ
  dsimp
  intro hroot
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  let S : Type _ := B₀ ⊗[G i0] G j.1
  let coeffComm : S ≃+* (G j.1 ⊗[G i0] B₀) :=
    (Algebra.TensorProduct.comm (R := G i0) (A := B₀) (B := G j.1)).toRingEquiv
  let literalToComm : (S ⊗[B₀] C₀) ≃+* (C₀ ⊗[G i0] G j.1) :=
      (Algebra.TensorProduct.comm (R := B₀) (A := S) (B := C₀)).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange
        (R := G i0) (S := B₀) (T := C₀) (A := C₀) (B := G j.1)).toRingEquiv
  let targetComm : (C₀ ⊗[G i0] G j.1) ≃+* (G j.1 ⊗[G i0] C₀) :=
    ((Algebra.TensorProduct.comm (R := G i0) (A := G j.1) (B := C₀)).symm).toRingEquiv
  let e : (S ⊗[B₀] C₀) ≃+* (G j.1 ⊗[G i0] C₀) :=
    literalToComm.trans targetComm
  let θj : (G j.1 ⊗[G i0] B₀) →ₐ[G i0] (G j.1 ⊗[G i0] C₀) :=
    Algebra.TensorProduct.map (AlgHom.id (G i0) (G j.1)) φ₀
  letI : Algebra (G j.1 ⊗[G i0] B₀) (G j.1 ⊗[G i0] C₀) := θj.toRingHom.toAlgebra
  let Q' : Polynomial S := Polynomial.map coeffComm.symm.toRingHom Q
  have hQ' : Q'.Monic := by
    -- Proof comment: the coefficient transport is a ring equivalence, so it preserves monicity.
    simpa [Q'] using hQ.map coeffComm.symm.toRingHom
  have hcomm :
      θj.toRingHom.comp coeffComm.toRingHom =
        e.toRingHom.comp (algebraMap S (S ⊗[B₀] C₀)) := by
    -- Proof comment: both routes send the left `B₀`-generator to `1 ⊗ φ₀(b)` and the right
    -- `G j.1`-generator to `g ⊗ 1`.
    ext b
    ·
      change
        (Algebra.TensorProduct.map (AlgHom.id (G i0) (G j.1)) φ₀)
            ((Algebra.TensorProduct.comm (R := G i0) (A := B₀) (B := G j.1))
              (b ⊗ₜ[G i0] (1 : G j.1))) =
          e (((b ⊗ₜ[G i0] (1 : G j.1)) : S) ⊗ₜ[B₀] (1 : C₀))
      calc
        (Algebra.TensorProduct.map (AlgHom.id (G i0) (G j.1)) φ₀)
            ((Algebra.TensorProduct.comm (R := G i0) (A := B₀) (B := G j.1))
              (b ⊗ₜ[G i0] (1 : G j.1)))
            = ((1 : G j.1) ⊗ₜ[G i0] φ₀ b : G j.1 ⊗[G i0] C₀) := by
                simp
        _ = targetComm ((algebraMap B₀ C₀ b) ⊗ₜ[G i0] (1 : G j.1)) := by
              rfl
        _ = e (((b ⊗ₜ[G i0] (1 : G j.1)) : S) ⊗ₜ[B₀] (1 : C₀)) := by
              simp [e, literalToComm, S, Algebra.smul_def]
    ·
      change
        (Algebra.TensorProduct.map (AlgHom.id (G i0) (G j.1)) φ₀)
            ((Algebra.TensorProduct.comm (R := G i0) (A := B₀) (B := G j.1))
              ((1 : B₀) ⊗ₜ[G i0] b)) =
          e ((((1 : B₀) ⊗ₜ[G i0] b : S) ⊗ₜ[B₀] (1 : C₀)))
      calc
        (Algebra.TensorProduct.map (AlgHom.id (G i0) (G j.1)) φ₀)
            ((Algebra.TensorProduct.comm (R := G i0) (A := B₀) (B := G j.1))
              ((1 : B₀) ⊗ₜ[G i0] b))
            = (b ⊗ₜ[G i0] (1 : C₀) : G j.1 ⊗[G i0] C₀) := by
                simp
        _ = targetComm ((1 : C₀) ⊗ₜ[G i0] b) := by
              rfl
        _ = e ((((1 : B₀) ⊗ₜ[G i0] b : S) ⊗ₜ[B₀] (1 : C₀))) := by
              simp [e, literalToComm, S, Algebra.smul_def]
  have hincludeRight :
      e (Algebra.TensorProduct.includeRight (R := B₀) (A := S) (B := C₀) x) =
        ((1 : G j.1) ⊗ₜ[G i0] x : G j.1 ⊗[G i0] C₀) := by
    -- Proof comment: under the standard `comm` plus `cancelBaseChange` transport, the literal
    -- right tensor generator becomes the comm-oriented tensor generator `1 ⊗ x`.
    change
      targetComm
        ((Algebra.TensorProduct.cancelBaseChange
          (R := G i0) (S := B₀) (T := C₀) (A := C₀) (B := G j.1))
          ((Algebra.TensorProduct.comm (R := B₀) (A := S) (B := C₀))
            (((1 : S) ⊗ₜ[B₀] x)))) =
        ((1 : G j.1) ⊗ₜ[G i0] x : G j.1 ⊗[G i0] C₀)
    rw [Algebra.TensorProduct.comm_tmul]
    change
      targetComm
        ((Algebra.TensorProduct.cancelBaseChange
          (R := G i0) (S := B₀) (T := C₀) (A := C₀) (B := G j.1))
          (x ⊗ₜ[B₀] (((1 : B₀) ⊗ₜ[G i0] (1 : G j.1)) : S))) =
        ((1 : G j.1) ⊗ₜ[G i0] x : G j.1 ⊗[G i0] C₀)
    calc
      targetComm
          ((Algebra.TensorProduct.cancelBaseChange
            (R := G i0) (S := B₀) (T := C₀) (A := C₀) (B := G j.1))
            (x ⊗ₜ[B₀] (((1 : B₀) ⊗ₜ[G i0] (1 : G j.1)) : S)))
          =
        targetComm (x ⊗ₜ[G i0] (1 : G j.1)) := by
            simpa [S, Algebra.smul_def] using
              (Algebra.TensorProduct.cancelBaseChange_tmul
                (R := G i0) (S := B₀) (T := C₀) (A := C₀) (B := G j.1)
                x (1 : B₀) (1 : G j.1))
      _ = ((1 : G j.1) ⊗ₜ[G i0] x : G j.1 ⊗[G i0] C₀) := by
            rfl
  have hroot' :
      Polynomial.aeval
          (Algebra.TensorProduct.includeRight (R := B₀) (A := S) (B := C₀) x) Q' = 0 := by
    -- Proof comment: map the literal evaluation through `e`; it becomes the given comm-oriented
    -- evaluation of `Q`, so injectivity of the equivalence returns the desired zero relation.
    apply e.injective
    calc
      e (Polynomial.aeval
          (Algebra.TensorProduct.includeRight (R := B₀) (A := S) (B := C₀) x) Q')
          =
        Polynomial.aeval
          (e (Algebra.TensorProduct.includeRight (R := B₀) (A := S) (B := C₀) x))
          (Polynomial.map coeffComm.toRingHom Q') := by
            simpa using
              Polynomial.map_aeval_eq_aeval_map hcomm Q'
                (Algebra.TensorProduct.includeRight (R := B₀) (A := S) (B := C₀) x)
      _ =
        Polynomial.aeval
          (((1 : G j.1) ⊗ₜ[G i0] x) : G j.1 ⊗[G i0] C₀)
          (Polynomial.map coeffComm.toRingHom Q') := by
            rw [hincludeRight]
      _ = Polynomial.aeval (((1 : G j.1) ⊗ₜ[G i0] x) : G j.1 ⊗[G i0] C₀) Q := by
            have hQmap : Polynomial.map coeffComm.toRingHom Q' = Q := by
              simpa [Q'] using
                (Polynomial.map_map coeffComm.symm.toRingHom coeffComm.toRingHom Q)
            rw [hQmap]
      _ = 0 := hroot
      _ = e 0 := by simp
  exact ⟨Q', hQ', hroot'⟩

/-- Helper for Lemma 10.168.3: moving a stage relation forward along a tail transition preserves
the vanishing of its comm-oriented polynomial evaluation. -/
theorem tail_transition_preserves_comm_aeval_zero
    {j k : Set.Ici i0} (hjk : j ≤ k) (x : C₀) :
    letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
    ∀ Q : Polynomial (G j.1 ⊗[G i0] B₀),
      (let θj : (G j.1 ⊗[G i0] B₀) →ₐ[G i0] (G j.1 ⊗[G i0] C₀) :=
          Algebra.TensorProduct.map (AlgHom.id (G i0) (G j.1)) φ₀
       letI : Algebra (G j.1 ⊗[G i0] B₀) (G j.1 ⊗[G i0] C₀) := θj.toRingHom.toAlgebra
       Polynomial.aeval (((1 : G j.1) ⊗ₜ[G i0] x) : G j.1 ⊗[G i0] C₀) Q = 0) →
      (letI : Algebra (G i0) (G k.1) := (f i0 k.1 k.2).toAlgebra
       let θk : (G k.1 ⊗[G i0] B₀) →ₐ[G i0] (G k.1 ⊗[G i0] C₀) :=
          Algebra.TensorProduct.map (AlgHom.id (G i0) (G k.1)) φ₀
       letI : Algebra (G k.1 ⊗[G i0] B₀) (G k.1 ⊗[G i0] C₀) := θk.toRingHom.toAlgebra
       Polynomial.aeval (((1 : G k.1) ⊗ₜ[G i0] x) : G k.1 ⊗[G i0] C₀)
        (Polynomial.map
          ((Algebra.TensorProduct.map
            (tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk)
            (AlgHom.id (G i0) B₀)).toRingHom) Q) = 0) := by
  letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
  intro Q hQ
  letI : Algebra (G i0) (G k.1) := (f i0 k.1 k.2).toAlgebra
  let θj : (G j.1 ⊗[G i0] B₀) →ₐ[G i0] (G j.1 ⊗[G i0] C₀) :=
    Algebra.TensorProduct.map (AlgHom.id (G i0) (G j.1)) φ₀
  let θk : (G k.1 ⊗[G i0] B₀) →ₐ[G i0] (G k.1 ⊗[G i0] C₀) :=
    Algebra.TensorProduct.map (AlgHom.id (G i0) (G k.1)) φ₀
  letI : Algebra (G j.1 ⊗[G i0] B₀) (G j.1 ⊗[G i0] C₀) := θj.toRingHom.toAlgebra
  letI : Algebra (G k.1 ⊗[G i0] B₀) (G k.1 ⊗[G i0] C₀) := θk.toRingHom.toAlgebra
  -- Proof comment: `comm_tensor_aeval` is the source-faithful bridge showing that changing the
  -- left stage ring commutes with evaluating the same generator relation.
  calc
    Polynomial.aeval (((1 : G k.1) ⊗ₜ[G i0] x) : G k.1 ⊗[G i0] C₀)
        (Polynomial.map
          ((Algebra.TensorProduct.map
            (tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk)
            (AlgHom.id (G i0) B₀)).toRingHom) Q)
        =
      (Algebra.TensorProduct.map
        (tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk)
        (AlgHom.id (G i0) C₀))
        (Polynomial.aeval (((1 : G j.1) ⊗ₜ[G i0] x) : G j.1 ⊗[G i0] C₀) Q) := by
          symm
          simpa [θj, θk] using
            (comm_tensor_aeval
              (φ₀ := φ₀) (R' := G j.1) (S' := G k.1)
              (g := tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk)
              (x := x) (q := Q))
    _ = 0 := by
          rw [hQ]
          simp

/-- Helper for Lemma 10.168.3: the comm-oriented direct-limit base-change map. -/
noncomputable abbrev direct_limit_commBaseChangeAlgHom :
    (G∞ ⊗[G i0] B₀) →ₐ[G i0] (G∞ ⊗[G i0] C₀) :=
  Algebra.TensorProduct.map (AlgHom.id (G i0) G∞) φ₀

/-- Helper for Lemma 10.168.3: the target of the comm-oriented direct-limit base change carries
the induced algebra structure from `B₀`. -/
noncomputable abbrev direct_limit_commBaseChangeAlgebra :
    Algebra (G∞ ⊗[G i0] B₀) (G∞ ⊗[G i0] C₀) :=
  (direct_limit_commBaseChangeAlgHom
    (G := G) (f := f) (i0 := i0) (B₀ := B₀) (C₀ := C₀) (φ₀ := φ₀)).toRingHom.toAlgebra

/-- Helper for Lemma 10.168.3: an integral relation for a literal tensor generator
`x ⊗ 1` over `B₀ ⊗[G i0] R'` transports across tensor commutativity to a comm-oriented monic
relation for `1 ⊗ x` over `R' ⊗[G i0] B₀`. -/
theorem literal_tensor_generator_exists_comm_monic_relation
    {R' : Type*} [CommRing R'] [Algebra (G i0) R']
    (x : C₀)
    (hx :
      let θlit : (B₀ ⊗[G i0] R') →ₐ[G i0] (C₀ ⊗[G i0] R') :=
        Algebra.TensorProduct.map φ₀ (AlgHom.id (G i0) R')
      letI : Algebra (B₀ ⊗[G i0] R') (C₀ ⊗[G i0] R') := θlit.toRingHom.toAlgebra
      IsIntegral (B₀ ⊗[G i0] R') ((x ⊗ₜ[G i0] (1 : R')) : C₀ ⊗[G i0] R')) :
    ∃ Q : Polynomial (R' ⊗[G i0] B₀), Q.Monic ∧
      (let θcomm : (R' ⊗[G i0] B₀) →ₐ[G i0] (R' ⊗[G i0] C₀) :=
        Algebra.TensorProduct.map (AlgHom.id (G i0) R') φ₀
       letI : Algebra (R' ⊗[G i0] B₀) (R' ⊗[G i0] C₀) := θcomm.toRingHom.toAlgebra
       Polynomial.aeval (((1 : R') ⊗ₜ[G i0] x) : R' ⊗[G i0] C₀) Q = 0) := by
  let θlit : (B₀ ⊗[G i0] R') →ₐ[G i0] (C₀ ⊗[G i0] R') :=
    Algebra.TensorProduct.map φ₀ (AlgHom.id (G i0) R')
  letI : Algebra (B₀ ⊗[G i0] R') (C₀ ⊗[G i0] R') := θlit.toRingHom.toAlgebra
  rcases hx with ⟨P, hPmonic, hProot⟩
  let coeffComm : (B₀ ⊗[G i0] R') ≃+* (R' ⊗[G i0] B₀) :=
    (Algebra.TensorProduct.comm (R := G i0) (A := B₀) (B := R')).toRingEquiv
  let targetComm : (C₀ ⊗[G i0] R') ≃+* (R' ⊗[G i0] C₀) :=
    (Algebra.TensorProduct.comm (R := G i0) (A := C₀) (B := R')).toRingEquiv
  let θcomm : (R' ⊗[G i0] B₀) →ₐ[G i0] (R' ⊗[G i0] C₀) :=
    Algebra.TensorProduct.map (AlgHom.id (G i0) R') φ₀
  letI : Algebra (R' ⊗[G i0] B₀) (R' ⊗[G i0] C₀) := θcomm.toRingHom.toAlgebra
  let Q : Polynomial (R' ⊗[G i0] B₀) := Polynomial.map coeffComm.toRingHom P
  have hQmonic : Q.Monic := by
    -- Proof comment: transporting coefficients across a ring equivalence preserves monicity.
    simpa [Q] using hPmonic.map coeffComm.toRingHom
  have hcomm :
      θcomm.toRingHom.comp coeffComm.toRingHom =
        targetComm.toRingHom.comp θlit.toRingHom := by
    -- Proof comment: both routes are the same tensor base-change map, only written in the
    -- literal and comm-oriented tensor conventions.
    ext b
    ·
      change
        (Algebra.TensorProduct.map (AlgHom.id (G i0) R') φ₀)
            ((Algebra.TensorProduct.comm (R := G i0) (A := B₀) (B := R'))
              (b ⊗ₜ[G i0] (1 : R'))) =
          (Algebra.TensorProduct.comm (R := G i0) (A := C₀) (B := R'))
            ((Algebra.TensorProduct.map φ₀ (AlgHom.id (G i0) R'))
              (b ⊗ₜ[G i0] (1 : R')))
      simp
    ·
      change
        (Algebra.TensorProduct.map (AlgHom.id (G i0) R') φ₀)
            ((Algebra.TensorProduct.comm (R := G i0) (A := B₀) (B := R'))
              ((1 : B₀) ⊗ₜ[G i0] b)) =
          (Algebra.TensorProduct.comm (R := G i0) (A := C₀) (B := R'))
            ((Algebra.TensorProduct.map φ₀ (AlgHom.id (G i0) R'))
              ((1 : B₀) ⊗ₜ[G i0] b))
      simp
  have hroot' :
      Polynomial.aeval (((1 : R') ⊗ₜ[G i0] x) : R' ⊗[G i0] C₀) Q = 0 := by
    -- Proof comment: apply the commutativity equivalence to the literal root relation and rewrite
    -- the transported evaluation as evaluation of the transported polynomial.
    calc
      Polynomial.aeval (((1 : R') ⊗ₜ[G i0] x) : R' ⊗[G i0] C₀) Q
          =
        targetComm
          (Polynomial.aeval (((x ⊗ₜ[G i0] (1 : R')) : C₀ ⊗[G i0] R')) P) := by
            symm
            simpa [Q, θlit, θcomm, coeffComm, targetComm] using
              Polynomial.map_aeval_eq_aeval_map hcomm P
                (((x ⊗ₜ[G i0] (1 : R')) : C₀ ⊗[G i0] R'))
      _ = 0 := by
            simpa using congrArg targetComm hProot
  exact ⟨Q, hQmonic, hroot'⟩

/-- Helper for Lemma 10.168.3: an integral relation for a generator over the literal direct-limit
base change transports to a comm-oriented monic polynomial relation over `G∞ ⊗[G i0] B₀`. -/
theorem direct_limit_generator_exists_comm_monic_relation
    (x : C₀)
    (hx :
      let θInf : (B₀ ⊗[G i0] G∞) →ₐ[G i0] (C₀ ⊗[G i0] G∞) :=
        Algebra.TensorProduct.map φ₀ (AlgHom.id (G i0) G∞)
      letI : Algebra (B₀ ⊗[G i0] G∞) (C₀ ⊗[G i0] G∞) := θInf.toRingHom.toAlgebra
      IsIntegral (B₀ ⊗[G i0] G∞) ((x ⊗ₜ[G i0] (1 : G∞)) : C₀ ⊗[G i0] G∞)) :
    ∃ Q : Polynomial (G∞ ⊗[G i0] B₀), Q.Monic ∧
      (letI : Algebra (G∞ ⊗[G i0] B₀) (G∞ ⊗[G i0] C₀) :=
        direct_limit_commBaseChangeAlgebra
          (G := G) (f := f) (i0 := i0) (B₀ := B₀) (C₀ := C₀) (φ₀ := φ₀)
      Polynomial.aeval (((1 : G∞) ⊗ₜ[G i0] x) : G∞ ⊗[G i0] C₀) Q = 0) := by
  -- Proof comment: this is the generic literal-to-comm transport specialized to the direct-limit
  -- coefficient ring.
  simpa [direct_limit_commBaseChangeAlgebra, direct_limit_commBaseChangeAlgHom] using
    (literal_tensor_generator_exists_comm_monic_relation
      (G := G) (i0 := i0) (B₀ := B₀) (C₀ := C₀) (φ₀ := φ₀)
      (R' := G∞) x hx)

/-- Lemma 10.168.3: if the base change of `φ₀` to the directed colimit ring is finite and `φ₀`
is of finite type, then after passing to some stage `i ≥ i0` the corresponding base-changed map
is already finite. -/
-- Proof sketch: Choose finitely many generators of `C₀` over `B₀`. The finiteness of the colimit
-- base change gives monic relations for their images over the direct limit. Descend the finitely
-- many coefficients and relations to some stage using directedness, then conclude that the stage
-- base change is finite.
theorem exists_ge_finite_stage_base_change_hom_of_direct_limit_finite
    (hfinite :
      letI : Algebra (G i0) G∞ := (Ring.DirectLimit.of G (fun i j hij ↦ f i j hij) i0).toAlgebra
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (G i0) G∞)).Finite)
    (hφ₀ : φ₀.FiniteType) :
    ∃ (i : ι) (hi : i0 ≤ i),
      letI : Algebra (G i0) (G i) := (f i0 i hi).toAlgebra
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (G i0) (G i))).Finite := by
  classical
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  have hC₀FiniteType : Algebra.FiniteType B₀ C₀ := by
    simpa [AlgHom.FiniteType, RingHom.FiniteType] using hφ₀
  obtain ⟨s, hs⟩ := hC₀FiniteType.out
  have hliteralIntegral :
      ∀ x ∈ s,
        let θInf : (B₀ ⊗[G i0] G∞) →ₐ[G i0] (C₀ ⊗[G i0] G∞) :=
          Algebra.TensorProduct.map φ₀ (AlgHom.id (G i0) G∞)
        letI : Algebra (B₀ ⊗[G i0] G∞) (C₀ ⊗[G i0] G∞) := θInf.toRingHom.toAlgebra
        IsIntegral (B₀ ⊗[G i0] G∞) ((x ⊗ₜ[G i0] (1 : G∞)) : C₀ ⊗[G i0] G∞) := by
    intro x hx
    let θInf : (B₀ ⊗[G i0] G∞) →ₐ[G i0] (C₀ ⊗[G i0] G∞) :=
      Algebra.TensorProduct.map φ₀ (AlgHom.id (G i0) G∞)
    letI : Algebra (B₀ ⊗[G i0] G∞) (C₀ ⊗[G i0] G∞) := θInf.toRingHom.toAlgebra
    have hθInfFinite : θInf.toRingHom.Finite := by
      simpa [θInf, AlgHom.Finite] using hfinite
    -- Proof comment: finiteness of the direct-limit base change makes every target element,
    -- hence every chosen generator tensor, integral over the source.
    exact (RingHom.Finite.to_isIntegral hθInfFinite)
      (((x ⊗ₜ[G i0] (1 : G∞)) : C₀ ⊗[G i0] G∞))
  have hdirectRelations :
      ∀ x ∈ s,
        ∃ Q : Polynomial (G∞ ⊗[G i0] B₀), Q.Monic ∧
          (letI : Algebra (G∞ ⊗[G i0] B₀) (G∞ ⊗[G i0] C₀) :=
            direct_limit_commBaseChangeAlgebra
              (G := G) (f := f) (i0 := i0) (B₀ := B₀) (C₀ := C₀) (φ₀ := φ₀)
           Polynomial.aeval (((1 : G∞) ⊗ₜ[G i0] x) : G∞ ⊗[G i0] C₀) Q = 0) := by
    intro x hx
    exact direct_limit_generator_exists_comm_monic_relation
      (G := G) (f := f) (i0 := i0) (B₀ := B₀) (C₀ := C₀) (φ₀ := φ₀)
      x (hliteralIntegral x hx)
  let P : C₀ → Polynomial (G∞ ⊗[G i0] B₀) :=
    fun x ↦ if hx : x ∈ s then Classical.choose (hdirectRelations x hx) else 1
  have hPmonic : ∀ x ∈ s, (P x).Monic := by
    intro x hx
    simp only [P, dif_pos hx]
    exact (Classical.choose_spec (hdirectRelations x hx)).1
  have hProot :
      ∀ x ∈ s,
        letI : Algebra (G∞ ⊗[G i0] B₀) (G∞ ⊗[G i0] C₀) :=
          direct_limit_commBaseChangeAlgebra
            (G := G) (f := f) (i0 := i0) (B₀ := B₀) (C₀ := C₀) (φ₀ := φ₀)
        Polynomial.aeval (((1 : G∞) ⊗ₜ[G i0] x) : G∞ ⊗[G i0] C₀) (P x) = 0 := by
    intro x hx
    simpa only [P, dif_pos hx] using (Classical.choose_spec (hdirectRelations x hx)).2
  set_option maxHeartbeats 5000000 in
  have hdesc :
      ∃ j : Set.Ici i0,
        letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
        ∃ Q : C₀ → Polynomial (G j.1 ⊗[G i0] B₀),
          (∀ x ∈ s, (Q x).Monic) ∧
            ∀ x ∈ s,
              let θj : (G j.1 ⊗[G i0] B₀) →ₐ[G i0] (G j.1 ⊗[G i0] C₀) :=
                Algebra.TensorProduct.map (AlgHom.id (G i0) (G j.1)) φ₀
              letI : Algebra (G j.1 ⊗[G i0] B₀) (G j.1 ⊗[G i0] C₀) := θj.toRingHom.toAlgebra
              Polynomial.aeval (((1 : G j.1) ⊗ₜ[G i0] x) : G j.1 ⊗[G i0] C₀) (Q x) = 0 := by
    -- Proof comment: first descend the finitely many coefficient polynomials, then descend the
    -- finitely many resulting vanishing relations to one later stage.
    rcases
      tail_exists_common_stage_monic_comm_relations
        (G := G) (f := f) (i0 := i0) (B₀ := B₀) (C₀ := C₀) s P hPmonic with
      ⟨j, Q, hQmonic, hQmap⟩
    letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
    let θj : (G j.1 ⊗[G i0] B₀) →ₐ[G i0] (G j.1 ⊗[G i0] C₀) :=
      Algebra.TensorProduct.map (AlgHom.id (G i0) (G j.1)) φ₀
    letI : Algebra (G j.1 ⊗[G i0] B₀) (G j.1 ⊗[G i0] C₀) := θj.toRingHom.toAlgebra
    letI : Algebra (G∞ ⊗[G i0] B₀) (G∞ ⊗[G i0] C₀) :=
      direct_limit_commBaseChangeAlgebra
        (G := G) (f := f) (i0 := i0) (B₀ := B₀) (C₀ := C₀) (φ₀ := φ₀)
    let z : C₀ → G j.1 ⊗[G i0] C₀ :=
      fun x ↦ Polynomial.aeval (((1 : G j.1) ⊗ₜ[G i0] x) : G j.1 ⊗[G i0] C₀) (Q x)
    have hz :
        ∀ x ∈ s,
          (Algebra.TensorProduct.map
            (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j)
            (AlgHom.id (G i0) C₀)) (z x) = 0 := by
      intro x hx
      calc
        (Algebra.TensorProduct.map
            (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j)
            (AlgHom.id (G i0) C₀)) (z x)
            =
          Polynomial.aeval (((1 : G∞) ⊗ₜ[G i0] x) : G∞ ⊗[G i0] C₀)
            (Polynomial.map
              ((Algebra.TensorProduct.map
                (tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j)
                (AlgHom.id (G i0) B₀)).toRingHom) (Q x)) := by
                simpa [z, θj, direct_limit_commBaseChangeAlgHom, direct_limit_commBaseChangeAlgebra]
                  using
                    (comm_tensor_aeval
                      (φ₀ := φ₀) (R' := G j.1) (S' := G∞)
                      (g := tail_stage_to_direct_limit_algHom (G := G) (f := f) (i0 := i0) j)
                      (x := x) (q := Q x))
        _ = Polynomial.aeval (((1 : G∞) ⊗ₜ[G i0] x) : G∞ ⊗[G i0] C₀) (P x) := by
              rw [hQmap x hx]
        _ = 0 := hProot x hx
    letI : ∀ j' : Set.Ici i0, Algebra (G i0) (tail_ring_family (G := G) (i0 := i0) j') :=
      tail_ring_family_algebra_family (G := G) (f := f) (i0 := i0)
    letI : Algebra (G i0)
        (Ring.DirectLimit
          (tail_ring_family (G := G) (i0 := i0))
          (fun j' k' hjk ↦
            ((tail_transition_family (G := G) (f := f) (i0 := i0) j' k' hjk :
              tail_ring_family (G := G) (i0 := i0) j' →+*
                tail_ring_family (G := G) (i0 := i0) k')))) :=
      (Ring.DirectLimit.of
        (tail_ring_family (G := G) (i0 := i0))
        (fun j' k' hjk ↦
          ((tail_transition_family (G := G) (f := f) (i0 := i0) j' k' hjk :
            tail_ring_family (G := G) (i0 := i0) j' →+*
              tail_ring_family (G := G) (i0 := i0) k')))
        ⟨i0, le_rfl⟩).toAlgebra
    have hz_tail :
        ∀ x ∈ s,
          _root_.stageTensorMap
              (A := G i0)
              (R := tail_ring_family (G := G) (i0 := i0))
              (f := tail_transition_family (G := G) (f := f) (i0 := i0))
              (X := C₀) j (z x) =
          _root_.stageTensorMap
              (A := G i0)
              (R := tail_ring_family (G := G) (i0 := i0))
              (f := tail_transition_family (G := G) (f := f) (i0 := i0))
              (X := C₀) j 0 := by
      intro x hx
      -- Proof comment: the new owner-style transport lemma converts the ambient vanishing `hz`
      -- directly into the owner-surface equality required by finite-family tensor descent.
      simpa [tail_transition_family] using
        (owner_stageTensorMap_eq_zero_of_ambient_zero
          (G := G) (f := f) (i0 := i0) (C₀ := C₀) j (z x) (hz x hx))
    obtain ⟨k, hjk, hzero⟩ :=
      (_root_.tensor_equalities_descend_on_finset
        (A := G i0)
        (I := Set.Ici i0)
        (R := tail_ring_family (G := G) (i0 := i0))
        (f := tail_transition_family (G := G) (f := f) (i0 := i0))
        (X := C₀) (s := s) (i := j) z (fun _ ↦ 0) hz_tail)
    letI : Algebra (G i0) (G k.1) := (f i0 k.1 k.2).toAlgebra
    let τB :
        (G j.1 ⊗[G i0] B₀) →ₐ[G i0] (G k.1 ⊗[G i0] B₀) :=
      Algebra.TensorProduct.map
        (tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk)
        (AlgHom.id (G i0) B₀)
    let τC :
        (G j.1 ⊗[G i0] C₀) →ₐ[G i0] (G k.1 ⊗[G i0] C₀) :=
      Algebra.TensorProduct.map
        (tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk)
        (AlgHom.id (G i0) C₀)
    refine ⟨k, fun x ↦ Polynomial.map τB.toRingHom (Q x), ?_⟩
    constructor
    · intro x hx
      simpa [τB] using (hQmonic x hx).map τB.toRingHom
    · intro x hx
      let θk : (G k.1 ⊗[G i0] B₀) →ₐ[G i0] (G k.1 ⊗[G i0] C₀) :=
        Algebra.TensorProduct.map (AlgHom.id (G i0) (G k.1)) φ₀
      letI : Algebra (G k.1 ⊗[G i0] B₀) (G k.1 ⊗[G i0] C₀) := θk.toRingHom.toAlgebra
      have hz' : τC (z x) = 0 := by
        simpa
          [tail_transition_family, tail_transition_algHom, z, τC, tensor_map_eq_rTensor_C0,
            tail_transition_linearMap, tail_ring_transition] using
          hzero x hx
      calc
        Polynomial.aeval (((1 : G k.1) ⊗ₜ[G i0] x) : G k.1 ⊗[G i0] C₀)
            (Polynomial.map τB.toRingHom (Q x))
            =
          τC (Polynomial.aeval (((1 : G j.1) ⊗ₜ[G i0] x) : G j.1 ⊗[G i0] C₀) (Q x)) := by
              symm
              simpa [τB, τC, θk] using
                (comm_tensor_aeval
                  (φ₀ := φ₀) (R' := G j.1) (S' := G k.1)
                  (g := tail_transition_algHom (G := G) (f := f) (i0 := i0) hjk)
                  (x := x) (q := Q x))
        _ = 0 := hz'
  rcases hdesc with ⟨j, Q, hQmonic, hQroot⟩
  letI : Algebra (G i0) (G j.1) := (f i0 j.1 j.2).toAlgebra
  have hstageGeneratorIntegral :
      let S : Type _ := B₀ ⊗[G i0] G j.1
      ∀ x ∈ s,
        IsIntegral S
          ((Algebra.TensorProduct.includeRight : C₀ →ₐ[B₀] (S ⊗[B₀] C₀)) x) := by
    dsimp
    intro c hc
    -- Proof comment: each descended comm-oriented polynomial relation gives integrality of the
    -- corresponding literal tensor generator at stage `j`.
    exact stage_generator_isIntegral_of_comm_monic_relation
      (G := G) (f := f) (i0 := i0) (φ₀ := φ₀)
      (j := j) c (Q c) (hQmonic c hc) (hQroot c hc)
  have hstageIntegral :
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (G i0) (G j.1))).IsIntegral := by
    -- Proof comment: integrality on the finite generating set extends to integrality of the whole
    -- stage base change.
    exact stage_base_change_hom_isIntegral_of_generator_integral
      (G := G) (f := f) (i0 := i0) (B₀ := B₀) (C₀ := C₀) (φ₀ := φ₀)
      (i := j.1) j.2 s hs hstageGeneratorIntegral
  have hstageFiniteType :
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (G i0) (G j.1))).FiniteType :=
    stage_base_change_hom_finiteType
      (G := G) (f := f) (i0 := i0) (B₀ := B₀) (C₀ := C₀) (φ₀ := φ₀) hφ₀ j.2
  refine ⟨j.1, j.2, ?_⟩
  rw [AlgHom.Finite]
  -- Proof comment: the descended stage map is both integral and of finite type, hence finite.
  exact RingHom.Finite.of_isIntegral_of_finiteType hstageIntegral
    (by simpa [AlgHom.FiniteType] using hstageFiniteType)

end
