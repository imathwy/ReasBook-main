import stacks_proof.stacks_project.Chap10.Lemma_10_127_17.RawTail

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Helper for Lemma 10.127.17: the ambient `Rᵢ₀`-algebra structure on `R` coming from the source
direct limit. -/
noncomputable abbrev raw_tail_limitAlgebra
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ) :
    Algebra (A₀.RStage i₀) R :=
  (Ring.DirectLimit.toLimitHom A₀.RStage (fun a b h ↦ A₀.RMap a b h) A₀.colimitSource i₀).toAlgebra

/-- Helper for Lemma 10.127.17: the common tensor product `P₀ ⊗[Rᵢ₀] R` used by the raw tail. -/
abbrev raw_tail_limitTensor
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀] : Type u :=
  let _ : Algebra (A₀.RStage i₀) R := raw_tail_limitAlgebra A₀ i₀
  P₀ ⊗[A₀.RStage i₀] R

/-- Helper for Lemma 10.127.17: compose the raw tail stage map to `P₀ ⊗[Rᵢ₀] R` with the chosen
identification of that tensor product with `S`. -/
noncomputable abbrev range_tail_sigma
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra R S] (e : raw_tail_limitTensor A₀ i₀ P₀ ≃ₐ[R] S) (j : Set.Ici i₀) :
    raw_tail_stage A₀ i₀ P₀ j →+* S := by
  letI : Algebra (A₀.RStage i₀) R := raw_tail_limitAlgebra A₀ i₀
  exact e.toRingEquiv.toRingHom.comp (raw_tail_stageToTensor A₀ i₀ P₀ j)

/-- Helper for Lemma 10.127.17: the maps `σ j` on the raw tensor tail are compatible with the raw
transition maps. -/
theorem range_tail_sigma_compatible
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra R S] (e : raw_tail_limitTensor A₀ i₀ P₀ ≃ₐ[R] S)
    {j k : Set.Ici i₀} (hjk : j ≤ k) :
    range_tail_sigma A₀ i₀ P₀ e j =
      (range_tail_sigma A₀ i₀ P₀ e k).comp (raw_tail_map A₀ i₀ P₀ j k hjk) := by
  letI : Algebra (A₀.RStage i₀) R := raw_tail_limitAlgebra A₀ i₀
  -- Proof comment: `σ j` is obtained by postcomposing the raw tail map to `P₀ ⊗[Rᵢ₀] R` with
  -- the fixed identification `e`, so compatibility is inherited directly from the raw tail.
  simpa [range_tail_sigma, RingHom.comp_assoc] using
    congrArg (fun g : raw_tail_stage A₀ i₀ P₀ j →+* raw_tail_limitTensor A₀ i₀ P₀ ↦
      e.toRingEquiv.toRingHom.comp g)
      (raw_tail_stageToTensor_compatible A₀ i₀ P₀ hjk)

/-- Helper for Lemma 10.127.17: the image subrings of the compatible maps `σ j` form an
increasing family inside `S`. -/
theorem range_tail_targetStage_mono
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra R S] (e : raw_tail_limitTensor A₀ i₀ P₀ ≃ₐ[R] S)
    {j k : Set.Ici i₀} (hjk : j ≤ k) :
    (range_tail_sigma A₀ i₀ P₀ e j).range ≤ (range_tail_sigma A₀ i₀ P₀ e k).range := by
  rintro x ⟨y, rfl⟩
  refine ⟨raw_tail_map A₀ i₀ P₀ j k hjk y, ?_⟩
  -- Proof comment: move the chosen raw stage representative forward along the raw transition and
  -- then rewrite by the compatibility of the maps `σ`.
  simpa [RingHom.comp_apply] using
    (congrArg (fun g : raw_tail_stage A₀ i₀ P₀ j →+* S ↦ g y)
      (range_tail_sigma_compatible A₀ i₀ P₀ e hjk)).symm

/-- Helper for Lemma 10.127.17: the transition map between the image stages is the ambient
subring inclusion in `S`. -/
noncomputable abbrev range_tail_targetMap
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra R S] (e : raw_tail_limitTensor A₀ i₀ P₀ ≃ₐ[R] S)
    {j k : Set.Ici i₀} (hjk : j ≤ k) :
    (range_tail_sigma A₀ i₀ P₀ e j).range →+* (range_tail_sigma A₀ i₀ P₀ e k).range :=
  Subring.inclusion (range_tail_targetStage_mono A₀ i₀ P₀ e hjk)

/-- Helper for Lemma 10.127.17: the image-stage transition maps form a directed system because
they are literal subtype inclusions. -/
instance range_tail_targetDirectedSystem
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra R S] (e : raw_tail_limitTensor A₀ i₀ P₀ ≃ₐ[R] S) :
    DirectedSystem
      (fun j : Set.Ici i₀ ↦ (range_tail_sigma A₀ i₀ P₀ e j).range)
      (fun _ _ h ↦ range_tail_targetMap A₀ i₀ P₀ e h) where
  map_self := by
    intro j x
    rfl
  map_map := by
    intro i j k hij hjk x
    rfl

/-- Helper for Lemma 10.127.17: the source-stage map into the image stage is obtained by first
forming the raw tensor stage and then restricting `σ j` to its image. -/
noncomputable abbrev range_tail_stageMap
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra R S] (e : raw_tail_limitTensor A₀ i₀ P₀ ≃ₐ[R] S)
    (j : Set.Ici i₀) :
    A₀.RStage j.1 →+* (range_tail_sigma A₀ i₀ P₀ e j).range :=
  ((range_tail_sigma A₀ i₀ P₀ e j).rangeRestrict).comp (raw_tail_stageMap A₀ i₀ P₀ j)

/-- Helper for Lemma 10.127.17: the source-stage maps commute with the image-stage transitions. -/
theorem range_tail_stageMap_comm
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra R S] (e : raw_tail_limitTensor A₀ i₀ P₀ ≃ₐ[R] S)
    {j k : Set.Ici i₀} (hjk : j ≤ k) :
    (range_tail_stageMap A₀ i₀ P₀ e k).comp (A₀.RMap j.1 k.1 hjk) =
      (range_tail_targetMap A₀ i₀ P₀ e hjk).comp (range_tail_stageMap A₀ i₀ P₀ e j) := by
  apply RingHom.ext
  intro x
  apply Subtype.ext
  -- Proof comment: after forgetting that both sides land in image subrings, the equality reduces
  -- to the raw stage-map compatibility followed by the compatibility of the maps `σ`.
  change range_tail_sigma A₀ i₀ P₀ e k ((raw_tail_stageMap A₀ i₀ P₀ k) ((A₀.RMap j.1 k.1 hjk) x)) =
    range_tail_sigma A₀ i₀ P₀ e j ((raw_tail_stageMap A₀ i₀ P₀ j) x)
  rw [show (raw_tail_stageMap A₀ i₀ P₀ k) ((A₀.RMap j.1 k.1 hjk) x) =
      raw_tail_map A₀ i₀ P₀ j k hjk ((raw_tail_stageMap A₀ i₀ P₀ j) x) by
        exact congrArg (fun g : A₀.RStage j.1 →+* raw_tail_stage A₀ i₀ P₀ k ↦ g x)
          (raw_tail_stageMap_comm A₀ i₀ P₀ hjk)]
  simpa [RingHom.comp_apply] using
    congrArg (fun g : raw_tail_stage A₀ i₀ P₀ j →+* S ↦
      g ((raw_tail_stageMap A₀ i₀ P₀ j) x))
      (range_tail_sigma_compatible A₀ i₀ P₀ e hjk).symm

/-- Helper for Lemma 10.127.17: after composing with the canonical raw stage map, `σ j` agrees
with the ambient `R`-algebra map on `S` evaluated at the ambient source-stage element. -/
theorem range_tail_sigma_stageMap_eq
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra R S] (e : raw_tail_limitTensor A₀ i₀ P₀ ≃ₐ[R] S)
    (j : Set.Ici i₀) (x : A₀.RStage j.1) :
    range_tail_sigma A₀ i₀ P₀ e j ((raw_tail_stageMap A₀ i₀ P₀ j) x) =
      algebraMap R S ((Ring.DirectLimit.toLimitHom A₀.RStage (fun a b h ↦ A₀.RMap a b h)
        A₀.colimitSource j.1) x) := by
  letI : Algebra (A₀.RStage i₀) R := raw_tail_limitAlgebra A₀ i₀
  -- Proof comment: the raw stage map is the right-factor tensor inclusion, so after applying the
  -- tensor-stage map we land in the image of the ambient source element under `R → P₀ ⊗[Rᵢ₀] R`.
  have hraw :
      raw_tail_stageToTensor A₀ i₀ P₀ j ((raw_tail_stageMap A₀ i₀ P₀ j) x) =
        algebraMap R (raw_tail_limitTensor A₀ i₀ P₀)
          ((Ring.DirectLimit.toLimitHom A₀.RStage (fun a b h ↦ A₀.RMap a b h)
            A₀.colimitSource j.1) x) := by
    rfl
  calc
    range_tail_sigma A₀ i₀ P₀ e j ((raw_tail_stageMap A₀ i₀ P₀ j) x) =
        e.toRingEquiv.toRingHom
          (raw_tail_stageToTensor A₀ i₀ P₀ j ((raw_tail_stageMap A₀ i₀ P₀ j) x)) := by
      rfl
    _ = e.toRingEquiv.toRingHom
          (algebraMap R (raw_tail_limitTensor A₀ i₀ P₀)
            ((Ring.DirectLimit.toLimitHom A₀.RStage (fun a b h ↦ A₀.RMap a b h)
              A₀.colimitSource j.1) x)) := by
      rw [hraw]
    _ = algebraMap R S ((Ring.DirectLimit.toLimitHom A₀.RStage (fun a b h ↦ A₀.RMap a b h)
          A₀.colimitSource j.1) x) := by
      simpa using
        e.commutes ((Ring.DirectLimit.toLimitHom A₀.RStage (fun a b h ↦ A₀.RMap a b h)
          A₀.colimitSource j.1) x)

/-- Helper for Lemma 10.127.17: every element of `S` already lies in the image of some tail stage
map `σ j`. This is the cover needed to identify the direct limit of the image stages with `S`. -/
theorem range_tail_target_cover
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra R S] (e : raw_tail_limitTensor A₀ i₀ P₀ ≃ₐ[R] S)
    (s : S) :
    ∃ j : Set.Ici i₀, s ∈ (range_tail_sigma A₀ i₀ P₀ e j).range := by
  letI : Algebra (A₀.RStage i₀) R := raw_tail_limitAlgebra A₀ i₀
  obtain ⟨t, rfl⟩ := e.surjective s
  obtain ⟨z, rfl⟩ := (raw_tail_directLimit_equiv A₀ i₀ P₀).surjective t
  rcases Ring.DirectLimit.exists_of z with ⟨j, x, rfl⟩
  refine ⟨j, ⟨x, ?_⟩⟩
  -- Proof comment: represent the chosen direct-limit element by a single raw stage and then read
  -- off its image in `S` through the direct-limit equivalence.
  simpa [range_tail_sigma, RingHom.comp_apply] using
    congrArg e.toRingEquiv.toRingHom (raw_tail_directLimit_equiv_of A₀ i₀ P₀ j x)

/-- Helper for Lemma 10.127.17: the ambient inclusion of an image stage into `S`. -/
noncomputable abbrev range_tail_targetToAmbient
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra R S] (e : raw_tail_limitTensor A₀ i₀ P₀ ≃ₐ[R] S)
    (j : Set.Ici i₀) :
    (range_tail_sigma A₀ i₀ P₀ e j).range →+* S :=
  ((range_tail_sigma A₀ i₀ P₀ e j).range).subtype

/-- Helper for Lemma 10.127.17: the direct limit of the image stages maps to `S` by the ambient
subtype inclusions. -/
noncomputable def range_tail_targetColimitToAmbient
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra R S] (e : raw_tail_limitTensor A₀ i₀ P₀ ≃ₐ[R] S) :
    Ring.DirectLimit
        (fun j : Set.Ici i₀ ↦ (range_tail_sigma A₀ i₀ P₀ e j).range)
        (fun _ _ h ↦ range_tail_targetMap A₀ i₀ P₀ e h) →+* S :=
  Ring.DirectLimit.lift
    (fun j : Set.Ici i₀ ↦ (range_tail_sigma A₀ i₀ P₀ e j).range)
    (fun j k h ↦ range_tail_targetMap A₀ i₀ P₀ e h)
    S
    (fun j ↦ range_tail_targetToAmbient A₀ i₀ P₀ e j)
    (fun j k hjk x ↦ by
      -- Proof comment: the image-stage transition maps are subtype inclusions, so the ambient
      -- value in `S` is definitionally unchanged.
      rfl)

/-- Helper for Lemma 10.127.17: the direct limit of the image stages is `S`. Injectivity comes
from stagewise subtype inclusions, and surjectivity comes from the raw-tail cover. -/
theorem range_tail_targetColimitToAmbient_bijective
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra R S] (e : raw_tail_limitTensor A₀ i₀ P₀ ≃ₐ[R] S) :
    Function.Bijective (range_tail_targetColimitToAmbient A₀ i₀ P₀ e) := by
  -- Proof comment: apply the same direct-limit criterion used in Lemma `10.127.14`, with the
  -- image stages of the maps `σ j` in place of the finitely generated subalgebras.
  simpa [range_tail_targetColimitToAmbient, range_tail_targetToAmbient] using
    (Ring.DirectLimit.lift_bijective_of_stagewise_injective_cover
      (A := fun j : Set.Ici i₀ ↦ (range_tail_sigma A₀ i₀ P₀ e j).range)
      (map := fun j k h ↦ range_tail_targetMap A₀ i₀ P₀ e h)
      (B := S)
      (g := fun j ↦ range_tail_targetToAmbient A₀ i₀ P₀ e j)
      (hg := fun j k hjk x ↦ rfl)
      (hinj := fun _ ↦ by
        intro x y hxy
        exact Subtype.ext hxy)
      (hcover := fun s ↦ by
        rcases range_tail_target_cover A₀ i₀ P₀ e s with ⟨j, hs⟩
        exact ⟨j, ⟨s, hs⟩, rfl⟩))

/-- Helper for Lemma 10.127.17: the image-stage direct limit identifies with `S`. -/
noncomputable def range_tail_targetColimitIso
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra R S] (e : raw_tail_limitTensor A₀ i₀ P₀ ≃ₐ[R] S) :
    Ring.DirectLimit
        (fun j : Set.Ici i₀ ↦ (range_tail_sigma A₀ i₀ P₀ e j).range)
        (fun _ _ h ↦ range_tail_targetMap A₀ i₀ P₀ e h) ≃+* S :=
  RingEquiv.ofBijective
    (range_tail_targetColimitToAmbient A₀ i₀ P₀ e)
    (range_tail_targetColimitToAmbient_bijective A₀ i₀ P₀ e)

/-- Helper for Lemma 10.127.17: before replacing the target direct limit by `S`, the induced map
from the source tail colimit to the image-stage colimit already agrees with the ambient
`R`-algebra map on each canonical source-stage generator. -/
theorem range_tail_colimit_comm_toAmbient_on_generator
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra R S] (e : raw_tail_limitTensor A₀ i₀ P₀ ≃ₐ[R] S)
    (j : Set.Ici i₀) (x : A₀.RStage j.1) :
    ((range_tail_targetColimitToAmbient A₀ i₀ P₀ e).comp
        (Ring.DirectLimit.map
          (range_tail_stageMap A₀ i₀ P₀ e)
          (fun _ _ h ↦ range_tail_stageMap_comm A₀ i₀ P₀ e h)))
      (Ring.DirectLimit.of
        (fun j : Set.Ici i₀ ↦ A₀.RStage j.1)
        (fun a b h ↦ A₀.RMap a.1 b.1 h)
        j x) =
      (((algebraMap R S).comp
          (tail_directLimitIso A₀.RStage (fun a b h ↦ A₀.RMap a b h) i₀
            A₀.colimitSource).toRingHom)
        (Ring.DirectLimit.of
          (fun j : Set.Ici i₀ ↦ A₀.RStage j.1)
          (fun a b h ↦ A₀.RMap a.1 b.1 h)
          j x)) := by
  -- Proof comment: evaluate both direct-limit maps on the same tail-stage generator, then rewrite
  -- the source-colimit side through the tail colimit identification and finish with the stagewise
  -- ambient formula for `σ j`.
  rw [RingHom.comp_apply, Ring.DirectLimit.map_apply_of, range_tail_targetColimitToAmbient,
    Ring.DirectLimit.lift_of, RingHom.comp_apply]
  have htail :
      (tail_directLimitIso A₀.RStage (fun a b h ↦ A₀.RMap a b h) i₀
          A₀.colimitSource).toRingHom
        (Ring.DirectLimit.of
          (fun j : Set.Ici i₀ ↦ A₀.RStage j.1)
          (fun a b h ↦ A₀.RMap a.1 b.1 h)
          j x) =
        Ring.DirectLimit.toLimitHom A₀.RStage (fun a b h ↦ A₀.RMap a b h)
          A₀.colimitSource j.1 x := by
    simpa [tail_directLimitIso, tail_directLimit_to_full_of, Ring.DirectLimit.toLimitHom]
  simpa [range_tail_targetToAmbient, range_tail_stageMap, RingHom.comp_apply, htail] using
    (range_tail_sigma_stageMap_eq A₀ i₀ P₀ e j x)

/-- Helper for Lemma 10.127.17: before replacing the target direct limit by `S`, the induced map
from the source tail colimit to the image-stage colimit already agrees with the ambient
`R`-algebra map on `S`. -/
theorem range_tail_colimit_comm_toAmbient
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra R S] (e : raw_tail_limitTensor A₀ i₀ P₀ ≃ₐ[R] S) :
    (range_tail_targetColimitToAmbient A₀ i₀ P₀ e).comp
        (Ring.DirectLimit.map
          (range_tail_stageMap A₀ i₀ P₀ e)
          (fun _ _ h ↦ range_tail_stageMap_comm A₀ i₀ P₀ e h)) =
      (algebraMap R S).comp
        (tail_directLimitIso A₀.RStage (fun a b h ↦ A₀.RMap a b h) i₀
          A₀.colimitSource).toRingHom := by
  -- Proof comment: direct-limit ring maps agree once they agree on each tail-stage generator.
  apply Ring.DirectLimit.hom_ext
  intro j
  ext x
  exact range_tail_colimit_comm_toAmbient_on_generator A₀ i₀ P₀ e j x

/-- Helper for Lemma 10.127.17: package the range stages of the compatible maps `σ j` as a
directed finite-type approximation of `f`. This finishes the source-faithful owner construction
and leaves only the base-change bijectivity comparison. -/
noncomputable def range_tail_target_approximation
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra.FinitePresentation (A₀.RStage i₀) P₀]
    [Algebra R S] (e : raw_tail_limitTensor A₀ i₀ P₀ ≃ₐ[R] S) :
    DirectedFiniteTypeHomApproximation.{u, v, u} (algebraMap R S) :=
  { Λ := Set.Ici i₀
    instPreorder := inferInstance
    instNonempty := inferInstance
    instDirectedOrder := raw_tail_isDirectedOrder A₀ i₀
    RStage := fun j ↦ A₀.RStage j.1
    SStage := fun j ↦ (range_tail_sigma A₀ i₀ P₀ e j).range
    instCommRingRStage := fun j ↦ inferInstance
    instCommRingSStage := fun j ↦ inferInstance
    RMap := fun j k h ↦ A₀.RMap j.1 k.1 h
    SMap := fun j k h ↦ range_tail_targetMap A₀ i₀ P₀ e h
    instDirectedSystemRStage := inferInstance
    instDirectedSystemSStage := range_tail_targetDirectedSystem A₀ i₀ P₀ e
    stageMap := range_tail_stageMap A₀ i₀ P₀ e
    comm := fun {j k} h ↦ range_tail_stageMap_comm A₀ i₀ P₀ e h
    source_finiteType := fun j ↦ A₀.source_finiteType j.1
    target_finiteType := fun j ↦ by
      letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.RMap i₀ j.1 j.2).toAlgebra
      exact descended_tail_range_stage_finiteType A₀ i₀ (P₀ := P₀) j
        (range_tail_sigma A₀ i₀ P₀ e j)
    colimitSource := tail_directLimitIso A₀.RStage (fun a b h ↦ A₀.RMap a b h) i₀
      A₀.colimitSource
    colimitTarget := range_tail_targetColimitIso A₀ i₀ P₀ e
    colimit_comm := by
      -- Proof comment: after identifying the target direct limit with `S` through the ambient
      -- subtype inclusions, the colimit square is exactly the stagewise formula proved above.
      simpa [range_tail_targetColimitIso, RingHom.algebraMap_toAlgebra] using
        range_tail_colimit_comm_toAmbient A₀ i₀ P₀ e }

/-- Helper for Lemma 10.127.17: the range restriction of `σ j` is an algebra homomorphism over the
stage ring `Rⱼ`. -/
theorem range_tail_sigma_rangeRestrict_commutes
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra R S] (e : raw_tail_limitTensor A₀ i₀ P₀ ≃ₐ[R] S)
    (j : Set.Ici i₀) (r : A₀.RStage j.1) :
    let _ : Algebra (A₀.RStage j.1) ((range_tail_sigma A₀ i₀ P₀ e j).range) :=
      (((range_tail_sigma A₀ i₀ P₀ e j).rangeRestrict).comp (raw_tail_stageMap A₀ i₀ P₀ j)).toAlgebra
    (range_tail_sigma A₀ i₀ P₀ e j).rangeRestrict
        (algebraMap (A₀.RStage j.1) (raw_tail_stage A₀ i₀ P₀ j) r) =
      algebraMap (A₀.RStage j.1) ((range_tail_sigma A₀ i₀ P₀ e j).range) r := by
  rfl

/-- Helper for Lemma 10.127.17: the raw stage map `σ j` restricted to its image is the canonical
algebra map into the range stage. -/
noncomputable def range_tail_sigma_rangeRestrictAlgHom
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra R S] (e : raw_tail_limitTensor A₀ i₀ P₀ ≃ₐ[R] S)
    (j : Set.Ici i₀) :
    let _ : Algebra (A₀.RStage j.1) ((range_tail_sigma A₀ i₀ P₀ e j).range) :=
      (((range_tail_sigma A₀ i₀ P₀ e j).rangeRestrict).comp (raw_tail_stageMap A₀ i₀ P₀ j)).toAlgebra
    raw_tail_stage A₀ i₀ P₀ j →ₐ[A₀.RStage j.1] (range_tail_sigma A₀ i₀ P₀ e j).range :=
  let _ : Algebra (A₀.RStage j.1) ((range_tail_sigma A₀ i₀ P₀ e j).range) :=
    (((range_tail_sigma A₀ i₀ P₀ e j).rangeRestrict).comp (raw_tail_stageMap A₀ i₀ P₀ j)).toAlgebra
  { toRingHom := (range_tail_sigma A₀ i₀ P₀ e j).rangeRestrict
    commutes' := range_tail_sigma_rangeRestrict_commutes A₀ i₀ P₀ e j }

/-- Helper for Lemma 10.127.17: on pure tensors, the range-stage owner base-change map agrees with
the raw-tail owner base-change map after restricting to the later image stage. -/
theorem range_tail_stageBaseChange_compares_to_raw_tail_stageBaseChange_tmul
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra.FinitePresentation (A₀.RStage i₀) P₀]
    [Algebra R S] (e : raw_tail_limitTensor A₀ i₀ P₀ ≃ₐ[R] S)
    {j k : Set.Ici i₀} (hjk : j ≤ k) (x : raw_tail_stage A₀ i₀ P₀ j) (y : A₀.RStage k.1) :
    let _ : Algebra (A₀.RStage j.1) (raw_tail_stage A₀ i₀ P₀ j) :=
      (raw_tail_stageMap A₀ i₀ P₀ j).toAlgebra
    let _ : Module (A₀.RStage j.1) (raw_tail_stage A₀ i₀ P₀ j) := Algebra.toModule
    let _ : Algebra (A₀.RStage j.1) (A₀.RStage k.1) := (A₀.RMap j.1 k.1 hjk).toAlgebra
    let _ : Module (A₀.RStage j.1) (A₀.RStage k.1) := Algebra.toModule
    let _ : Algebra (A₀.RStage j.1) ((range_tail_sigma A₀ i₀ P₀ e j).range) :=
      (((range_tail_sigma A₀ i₀ P₀ e j).rangeRestrict).comp (raw_tail_stageMap A₀ i₀ P₀ j)).toAlgebra
    let A := range_tail_target_approximation A₀ i₀ P₀ e
    let beta_jk :=
      tensorMapLeft_mixed
        (R := A₀.RStage j.1) (A := raw_tail_stage A₀ i₀ P₀ j) (B := A₀.RStage k.1)
        (C := (range_tail_sigma A₀ i₀ P₀ e j).range)
        (range_tail_sigma_rangeRestrictAlgHom A₀ i₀ P₀ e j)
    A.stageBaseChangeMap hjk (beta_jk (x ⊗ₜ[A₀.RStage j.1] y)) =
      (((range_tail_sigma A₀ i₀ P₀ e k).rangeRestrict).comp
        ((rawTensorCancel A₀.RStage (fun a b h ↦ A₀.RMap a b h) P₀
          j.2 k.2 hjk
          (RingHom.ext <| DirectedSystem.map_map (f := fun a b h ↦ A₀.RMap a b h) j.2 hjk)).toRingHom))
        (x ⊗ₜ[A₀.RStage j.1] y) := by
  let _ : Algebra (A₀.RStage j.1) (raw_tail_stage A₀ i₀ P₀ j) :=
    (raw_tail_stageMap A₀ i₀ P₀ j).toAlgebra
  let _ : Module (A₀.RStage j.1) (raw_tail_stage A₀ i₀ P₀ j) := Algebra.toModule
  let _ : Algebra (A₀.RStage j.1) (A₀.RStage k.1) := (A₀.RMap j.1 k.1 hjk).toAlgebra
  let _ : Module (A₀.RStage j.1) (A₀.RStage k.1) := Algebra.toModule
  let _ : Algebra (A₀.RStage j.1) ((range_tail_sigma A₀ i₀ P₀ e j).range) :=
    (((range_tail_sigma A₀ i₀ P₀ e j).rangeRestrict).comp (raw_tail_stageMap A₀ i₀ P₀ j)).toAlgebra
  let A := range_tail_target_approximation A₀ i₀ P₀ e
  let _ : Algebra (A.RStage j) (raw_tail_stage A₀ i₀ P₀ j) := (raw_tail_stageMap A₀ i₀ P₀ j).toAlgebra
  let _ : Module (A.RStage j) (raw_tail_stage A₀ i₀ P₀ j) := Algebra.toModule
  let beta_jk :=
    tensorMapLeft_mixed
      (R := A₀.RStage j.1) (A := raw_tail_stage A₀ i₀ P₀ j) (B := A₀.RStage k.1)
      (C := (range_tail_sigma A₀ i₀ P₀ e j).range)
      (range_tail_sigma_rangeRestrictAlgHom A₀ i₀ P₀ e j)
  let rawCancel_jk :=
    (rawTensorCancel A₀.RStage (fun a b h ↦ A₀.RMap a b h) P₀
      j.2 k.2 hjk
      (RingHom.ext <| DirectedSystem.map_map (f := fun a b h ↦ A₀.RMap a b h) j.2 hjk)).toRingHom
  have howner :
      A.stageBaseChangeMap hjk (beta_jk (x ⊗ₜ[A₀.RStage j.1] y)) =
        range_tail_targetMap A₀ i₀ P₀ e hjk
            ((range_tail_sigma_rangeRestrictAlgHom A₀ i₀ P₀ e j) x) *
          range_tail_stageMap A₀ i₀ P₀ e k y := by
    -- Proof comment: the owner-side map is already normalized on pure tensors by the generic
    -- stage-base-change formula for tensoring an explicit left algebra map.
    simpa [A, beta_jk] using
      (DirectedFiniteTypeHomApproximation.stageBaseChangeMap_tensorBridge_tensorMapLeft_tmul_pointwise_mixed
        A hjk ((A.stageMap j).toAlgebra) rfl
        (range_tail_sigma_rangeRestrictAlgHom A₀ i₀ P₀ e j)
        (range_tail_targetMap A₀ i₀ P₀ e hjk)
        (range_tail_stageMap A₀ i₀ P₀ e k)
        (fun z ↦ rfl) (fun r ↦ rfl) x y)
  have hraw :
      rawCancel_jk (x ⊗ₜ[A₀.RStage j.1] y) =
        raw_tail_map A₀ i₀ P₀ j k hjk x * raw_tail_stageMap A₀ i₀ P₀ k y := by
    -- Proof comment: rewrite the raw side by the explicit tensor-cancellation equivalence.
    simpa [rawCancel_jk] using
      (rawTensorCancel_tmul_right
        (RStage := A₀.RStage) (map := fun a b h ↦ A₀.RMap a b h)
        (P₀ := P₀) (hij := j.2) (hik := k.2) (hjk := hjk)
        (RingHom.ext <| DirectedSystem.map_map (f := fun a b h ↦ A₀.RMap a b h) j.2 hjk)
        x y)
  have hraw_apply :
      ((rawTensorCancel A₀.RStage (fun a b h ↦ A₀.RMap a b h) P₀
          j.2 k.2 hjk
          (RingHom.ext <| DirectedSystem.map_map (f := fun a b h ↦ A₀.RMap a b h) j.2 hjk)).toRingHom)
        (x ⊗ₜ[A₀.RStage j.1] y) =
      raw_tail_map A₀ i₀ P₀ j k hjk x * raw_tail_stageMap A₀ i₀ P₀ k y := by
    simpa [rawCancel_jk] using hraw
  -- Proof comment: both sides land in the later image stage, so it suffices to compare the
  -- underlying elements in `S` using compatibility of the maps `σ`.
  apply Subtype.ext
  rw [howner, RingHom.comp_apply]
  change
    range_tail_sigma A₀ i₀ P₀ e j x *
        range_tail_sigma A₀ i₀ P₀ e k (raw_tail_stageMap A₀ i₀ P₀ k y) =
      range_tail_sigma A₀ i₀ P₀ e k
        (((rawTensorCancel A₀.RStage (fun a b h ↦ A₀.RMap a b h) P₀
            j.2 k.2 hjk
            (RingHom.ext <| DirectedSystem.map_map (f := fun a b h ↦ A₀.RMap a b h) j.2 hjk)).toRingHom)
          (x ⊗ₜ[A₀.RStage j.1] y))
  rw [hraw_apply]
  rw [range_tail_sigma_compatible A₀ i₀ P₀ e hjk]
  simp only [RingHom.comp_apply, map_mul]

/-- Helper for Lemma 10.127.17: the owner-level comparison square between the range-stage system
and the raw-tail system holds as an equality of ring homomorphisms. -/
theorem range_tail_stageBaseChange_compares_to_raw_tail_stageBaseChange
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra.FinitePresentation (A₀.RStage i₀) P₀]
    [Algebra R S] (e : raw_tail_limitTensor A₀ i₀ P₀ ≃ₐ[R] S)
    {j k : Set.Ici i₀} (hjk : j ≤ k) :
    let _ : Algebra (A₀.RStage j.1) (raw_tail_stage A₀ i₀ P₀ j) :=
      (raw_tail_stageMap A₀ i₀ P₀ j).toAlgebra
    let _ : Module (A₀.RStage j.1) (raw_tail_stage A₀ i₀ P₀ j) := Algebra.toModule
    let _ : Algebra (A₀.RStage j.1) (A₀.RStage k.1) := (A₀.RMap j.1 k.1 hjk).toAlgebra
    let _ : Module (A₀.RStage j.1) (A₀.RStage k.1) := Algebra.toModule
    let _ : Algebra (A₀.RStage j.1) ((range_tail_sigma A₀ i₀ P₀ e j).range) :=
      (((range_tail_sigma A₀ i₀ P₀ e j).rangeRestrict).comp (raw_tail_stageMap A₀ i₀ P₀ j)).toAlgebra
    let A := range_tail_target_approximation A₀ i₀ P₀ e
    let beta_jk :=
      tensorMapLeft_mixed
        (R := A₀.RStage j.1) (A := raw_tail_stage A₀ i₀ P₀ j) (B := A₀.RStage k.1)
        (C := (range_tail_sigma A₀ i₀ P₀ e j).range)
        (range_tail_sigma_rangeRestrictAlgHom A₀ i₀ P₀ e j)
    (A.stageBaseChangeMap hjk).comp beta_jk =
      ((range_tail_sigma A₀ i₀ P₀ e k).rangeRestrict).comp
        ((rawTensorCancel A₀.RStage (fun a b h ↦ A₀.RMap a b h) P₀
          j.2 k.2 hjk
          (RingHom.ext <| DirectedSystem.map_map (f := fun a b h ↦ A₀.RMap a b h) j.2 hjk)).toRingHom) := by
  let _ : Algebra (A₀.RStage j.1) (raw_tail_stage A₀ i₀ P₀ j) :=
    (raw_tail_stageMap A₀ i₀ P₀ j).toAlgebra
  let _ : Module (A₀.RStage j.1) (raw_tail_stage A₀ i₀ P₀ j) := Algebra.toModule
  let _ : Algebra (A₀.RStage j.1) (A₀.RStage k.1) := (A₀.RMap j.1 k.1 hjk).toAlgebra
  let _ : Module (A₀.RStage j.1) (A₀.RStage k.1) := Algebra.toModule
  let _ : Algebra (A₀.RStage j.1) ((range_tail_sigma A₀ i₀ P₀ e j).range) :=
    (((range_tail_sigma A₀ i₀ P₀ e j).rangeRestrict).comp (raw_tail_stageMap A₀ i₀ P₀ j)).toAlgebra
  let A := range_tail_target_approximation A₀ i₀ P₀ e
  let _ : Algebra (A.RStage j) (raw_tail_stage A₀ i₀ P₀ j) := (raw_tail_stageMap A₀ i₀ P₀ j).toAlgebra
  let _ : Module (A.RStage j) (raw_tail_stage A₀ i₀ P₀ j) := Algebra.toModule
  let beta_jk :=
    tensorMapLeft_mixed
      (R := A₀.RStage j.1) (A := raw_tail_stage A₀ i₀ P₀ j) (B := A₀.RStage k.1)
      (C := (range_tail_sigma A₀ i₀ P₀ e j).range)
      (range_tail_sigma_rangeRestrictAlgHom A₀ i₀ P₀ e j)
  let rawCancel_jk :=
    (rawTensorCancel A₀.RStage (fun a b h ↦ A₀.RMap a b h) P₀
      j.2 k.2 hjk
      (RingHom.ext <| DirectedSystem.map_map (f := fun a b h ↦ A₀.RMap a b h) j.2 hjk)).toRingHom
  -- Proof comment: both ring homomorphisms out of the tensor product are determined by their
  -- values on pure tensors, so the pointwise comparison upgrades by tensor induction.
  apply ringHom_eq_of_tmul
  intro x y
  simpa [A, beta_jk] using
    range_tail_stageBaseChange_compares_to_raw_tail_stageBaseChange_tmul
      A₀ i₀ P₀ e hjk x y

/-- Helper for Lemma 10.127.17: after restricting the raw-tail base-change map to the later image
stage, the resulting comparison map is still surjective. -/
theorem range_tail_raw_tail_stageBaseChange_surjective
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra.FinitePresentation (A₀.RStage i₀) P₀]
    [Algebra R S] (e : raw_tail_limitTensor A₀ i₀ P₀ ≃ₐ[R] S)
    {j k : Set.Ici i₀} (hjk : j ≤ k) :
    Function.Surjective
      (((range_tail_sigma A₀ i₀ P₀ e k).rangeRestrict).comp
        ((raw_tail_approximation A₀ i₀ P₀).stageBaseChangeMap hjk)) := by
  have hraw_surj :
      Function.Surjective ((raw_tail_approximation A₀ i₀ P₀).stageBaseChangeMap hjk) := by
    -- Proof comment: the raw-tail base-change map is the tensor-cancellation isomorphism.
    simpa [raw_tail_stageBaseChange_eq_rawTensorCancel A₀ i₀ P₀ j k hjk] using
      (rawTensorCancel A₀.RStage (fun a b h ↦ A₀.RMap a b h) P₀
        j.2 k.2 hjk
        (RingHom.ext <| DirectedSystem.map_map (f := fun a b h ↦ A₀.RMap a b h) j.2 hjk)).surjective
  intro z
  obtain ⟨w, rfl⟩ := (range_tail_sigma A₀ i₀ P₀ e k).rangeRestrict_surjective z
  obtain ⟨t, rfl⟩ := hraw_surj w
  refine ⟨t, ?_⟩
  rfl
