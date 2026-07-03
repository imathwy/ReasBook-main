import stacks_project.Chap10.Definition_10_54_1
import stacks_project.Chap10.Lemma_10_106_8
import stacks_project.Chap10.Lemma_10_127_8
import stacks_project.Chap10.Lemma_10_127_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w uR uS

section

variable {R : Type uR} {S : Type uS} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]

/-
Domain sampling:
* Primary domain: directed approximation systems for local homomorphisms of local rings in
  commutative algebra.
* Owner declarations inspected in this domain:
  - `DirectedLocalHomApproximation`
  - `DirectedLocalHomApproximation.targetStageBaseChange`
  - `DirectedLocalHomApproximation.stageBaseChangeMap`
  - `RingHom.EssFinitePresentation`
* Best owner abstraction: `DirectedLocalHomApproximation f` is the source-facing approximation
  object; “the transition base-change maps are localizations at prime ideals” is derived
  transition behavior of that owner, not new primitive data from `Lemma_10_127_10`.
* Primitive vs. derived: the directed system, stage rings, local maps, and colimit identifications
  are primitive owner data from `Lemma_10_127_10`; prime-localization transition behavior is a
  property of those canonical base-change maps.
-/

namespace DirectedLocalHomApproximation

/-- A transition in a directed local approximation presents the later target stage as a
localization at a prime ideal of the corresponding base-change ring. -/
def TransitionIsLocalizationAtPrime {f : R →+* S} (A : DirectedLocalHomApproximation f)
    {i j : A.Λ} (h : i ≤ j) : Prop :=
  ∃ q : Ideal (A.targetStageBaseChange h),
    ∃ _ : q.IsPrime, q.primeCompl.IsLocalizationMap (A.stageBaseChangeMap h)

/-- Every transition in a directed local approximation is a localization at a prime ideal. -/
def HasPrimeLocalizationTransitions {f : R →+* S} (A : DirectedLocalHomApproximation f) : Prop :=
  ∀ {i j : A.Λ} (h : i ≤ j), A.TransitionIsLocalizationAtPrime h

/-- A directed local approximation has a transition whose canonical base-change map is not a
localization at a prime ideal. -/
def HasFailingPrimeLocalizationTransition {f : R →+* S} (A : DirectedLocalHomApproximation f) :
    Prop :=
  ∃ (i j : A.Λ) (h : i ≤ j), ¬ A.TransitionIsLocalizationAtPrime h

end DirectedLocalHomApproximation

variable (f : R →+* S) [IsLocalHom f]

/-- Helper for Lemma 10.127.11: localizing a ring at a submonoid and then localizing the result at
the complement of its maximal ideal is the same as localizing the source at the pulled-back prime.
-/
theorem local_isLocalization_at_comap_maximalIdeal
    {P : Type v} {T : Type w} [CommRing P] [CommRing T] [Algebra P T]
    (M : Submonoid P) [IsLocalization M T] [IsLocalRing T] :
    let q : Ideal P := Ideal.comap (algebraMap P T) (IsLocalRing.maximalIdeal T)
    q.IsPrime ∧ q.primeCompl.IsLocalizationMap (algebraMap P T) := by
  let q : Ideal P := Ideal.comap (algebraMap P T) (IsLocalRing.maximalIdeal T)
  have hq_prime : q.IsPrime := by
    -- The pullback of the maximal ideal along the localization map is prime.
    simpa [q] using Ideal.comap_isPrime (algebraMap P T) (IsLocalRing.maximalIdeal T)
  letI : q.IsPrime := hq_prime
  have h_units : (IsLocalRing.maximalIdeal T).primeCompl ≤ IsUnit.submonoid T := by
    intro x hx
    -- In a local ring, every element outside the maximal ideal is a unit.
    simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Ideal.mem_primeCompl_iff,
      Classical.not_not] using hx
  letI : IsLocalization (IsLocalRing.maximalIdeal T).primeCompl T := IsLocalization.self h_units
  have hloc :
      IsLocalization (((IsLocalRing.maximalIdeal T).primeCompl).comap (algebraMap P T)) T := by
    -- Re-localize at the complement of the maximal ideal and collapse the second localization.
    exact IsLocalization.localization_localization_isLocalization_of_has_all_units
      (M := M) (N := (IsLocalRing.maximalIdeal T).primeCompl) (T := T) fun x hx ↦ by
        -- Units in a local ring lie outside the maximal ideal.
        simpa [Ideal.mem_primeCompl_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
          Classical.not_not] using hx
  have hprime_compl :
      ((IsLocalRing.maximalIdeal T).primeCompl).comap (algebraMap P T) = q.primeCompl := by
    -- The pulled-back complement is the complement of the pulled-back prime ideal.
    ext x
    simp [q, Ideal.mem_primeCompl_iff]
  have hq_localization : IsLocalization q.primeCompl T := by
    simpa [hprime_compl] using hloc
  -- Convert the prime-localization instance back to the explicit localization-map predicate.
  exact ⟨hq_prime, (isLocalization_iff_isLocalizationMap
    (M := q.primeCompl) (S := T)).mp hq_localization⟩

/-- Helper for Lemma 10.127.11: a cofinal tail of a directed preorder is directed. -/
theorem tail_index_isDirected {ι : Type v} [Preorder ι] [IsDirectedOrder ι] (i₀ : ι) :
    IsDirectedOrder (Set.Ici i₀) := by
  choose ub hub_left hub_right using exists_ge_ge (α := ι)
  have hdir : DirectedOn (· ≤ ·) (Set.Ici i₀) := by
    intro a ha b hb
    refine ⟨ub a b, le_trans ha (hub_left a b), hub_left a b, hub_right a b⟩
  rw [directedOn_iff_directed] at hdir
  rwa [IsDirectedOrder, ← directed_id_iff]

/-- Helper for Lemma 10.127.11: restricting a directed ring system to a tail still gives a
directed system of transition maps. -/
instance tail_directedSystem {ι : Type v} [Preorder ι]
    (G : ι → Type w) [∀ i, CommRing (G i)]
    (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ f i j h)] (i₀ : ι) :
    DirectedSystem (fun j : Set.Ici i₀ ↦ G j.1) (fun j k h ↦ f j.1 k.1 h) where
  map_self := by
    intro j x
    simpa using DirectedSystem.map_self (f := fun i j h ↦ f i j h) x
  map_map := by
    intro i j k hij hjk x
    simpa using DirectedSystem.map_map (f := fun i j h ↦ f i j h) hij hjk x

/-- Helper for Lemma 10.127.11: choose an upper bound of a stage and the distinguished tail base
stage. -/
noncomputable def tail_upper_bound {ι : Type v} [Preorder ι] [IsDirectedOrder ι]
    (i₀ i : ι) : ι :=
  (exists_ge_ge i i₀).choose

/-- Helper for Lemma 10.127.11: the chosen tail upper bound lies above the original stage. -/
theorem le_tail_upper_bound_left {ι : Type v} [Preorder ι] [IsDirectedOrder ι]
    (i₀ i : ι) :
    i ≤ tail_upper_bound i₀ i :=
  (exists_ge_ge i i₀).choose_spec.1

/-- Helper for Lemma 10.127.11: the chosen tail upper bound lies in the tail above the
distinguished base stage. -/
theorem le_tail_upper_bound_right {ι : Type v} [Preorder ι] [IsDirectedOrder ι]
    (i₀ i : ι) :
    i₀ ≤ tail_upper_bound i₀ i :=
  (exists_ge_ge i i₀).choose_spec.2

/-- Helper for Lemma 10.127.11: every stage of the original directed system maps canonically into
the direct limit of the tail above `i₀`. -/
noncomputable def tail_stage_to_directLimit {ι : Type v} [Preorder ι] [Nonempty ι]
    [IsDirectedOrder ι] (G : ι → Type w) [∀ i, CommRing (G i)]
    (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ f i j h)] (i₀ : ι) (i : ι) :
    G i →+*
      Ring.DirectLimit (fun j : Set.Ici i₀ ↦ G j.1) (fun j k h ↦ f j.1 k.1 h) :=
  let j : Set.Ici i₀ := ⟨tail_upper_bound i₀ i, le_tail_upper_bound_right i₀ i⟩
  (Ring.DirectLimit.of (fun j : Set.Ici i₀ ↦ G j.1) (fun j k h ↦ f j.1 k.1 h) j).comp
    (f i j.1 (le_tail_upper_bound_left i₀ i))

/-- Helper for Lemma 10.127.11: the canonical maps from the original stages into the tail direct
limit are compatible with the original transition maps. -/
theorem tail_stage_to_directLimit_compatible {ι : Type v} [Preorder ι] [Nonempty ι]
    [IsDirectedOrder ι] (G : ι → Type w) [∀ i, CommRing (G i)]
    (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ f i j h)] (i₀ : ι) {i j : ι} (hij : i ≤ j) (x : G i) :
    tail_stage_to_directLimit G f i₀ j (f i j hij x) =
      tail_stage_to_directLimit G f i₀ i x := by
  letI : IsDirectedOrder (Set.Ici i₀) := tail_index_isDirected i₀
  let ji : Set.Ici i₀ := ⟨tail_upper_bound i₀ i, le_tail_upper_bound_right i₀ i⟩
  let jj : Set.Ici i₀ := ⟨tail_upper_bound i₀ j, le_tail_upper_bound_right i₀ j⟩
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge ji jj
  -- Proof comment: move both chosen representatives to one common tail stage and compare them
  -- there using the original directed-system relation.
  calc
    tail_stage_to_directLimit G f i₀ j (f i j hij x) =
      Ring.DirectLimit.of (fun j : Set.Ici i₀ ↦ G j.1) (fun j k h ↦ f j.1 k.1 h) k
        (f jj.1 k.1 hjk
          (f j jj.1 (le_tail_upper_bound_left i₀ j) (f i j hij x))) := by
            simp only [tail_stage_to_directLimit, jj, RingHom.comp_apply]
            symm
            exact Ring.DirectLimit.of_f hjk _
    _ =
      Ring.DirectLimit.of (fun j : Set.Ici i₀ ↦ G j.1) (fun j k h ↦ f j.1 k.1 h) k
        (f ji.1 k.1 hik (f i ji.1 (le_tail_upper_bound_left i₀ i) x)) := by
          congr 1
          calc
            f jj.1 k.1 hjk (f j jj.1 (le_tail_upper_bound_left i₀ j) (f i j hij x)) =
                f j k.1 (le_trans (le_tail_upper_bound_left i₀ j) hjk) (f i j hij x) := by
                  exact DirectedSystem.map_map' (f := fun i j h ↦ f i j h)
                    (le_tail_upper_bound_left i₀ j) hjk (f i j hij x)
            _ = f i k.1 (le_trans hij (le_trans (le_tail_upper_bound_left i₀ j) hjk)) x := by
                  exact DirectedSystem.map_map' (f := fun i j h ↦ f i j h)
                    hij (le_trans (le_tail_upper_bound_left i₀ j) hjk) x
            _ = f ji.1 k.1 hik (f i ji.1 (le_tail_upper_bound_left i₀ i) x) := by
                  symm
                  exact DirectedSystem.map_map' (f := fun i j h ↦ f i j h)
                    (le_tail_upper_bound_left i₀ i) hik x
    _ = tail_stage_to_directLimit G f i₀ i x := by
          simp only [tail_stage_to_directLimit, ji, RingHom.comp_apply]
          exact Ring.DirectLimit.of_f hik _

/-- Helper for Lemma 10.127.11: the full direct limit maps canonically to the direct limit of the
tail above `i₀`. -/
noncomputable def full_directLimit_to_tail {ι : Type v} [Preorder ι] [Nonempty ι]
    [IsDirectedOrder ι] (G : ι → Type w) [∀ i, CommRing (G i)]
    (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ f i j h)] (i₀ : ι) :
    Ring.DirectLimit G (fun i j h ↦ f i j h) →+*
      Ring.DirectLimit (fun j : Set.Ici i₀ ↦ G j.1) (fun j k h ↦ f j.1 k.1 h) :=
  Ring.DirectLimit.lift G (fun i j h ↦ f i j h)
    (Ring.DirectLimit (fun j : Set.Ici i₀ ↦ G j.1) (fun j k h ↦ f j.1 k.1 h))
    (fun i ↦ tail_stage_to_directLimit G f i₀ i)
    (fun _ _ hij x ↦ tail_stage_to_directLimit_compatible G f i₀ hij x)

/-- Helper for Lemma 10.127.11: the tail direct limit maps canonically back to the original full
direct limit by forgetting that the stages lie in the tail. -/
noncomputable def tail_directLimit_to_full {ι : Type v} [Preorder ι] [Nonempty ι]
    [IsDirectedOrder ι] (G : ι → Type w) [∀ i, CommRing (G i)]
    (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ f i j h)] (i₀ : ι) :
    Ring.DirectLimit (fun j : Set.Ici i₀ ↦ G j.1) (fun j k h ↦ f j.1 k.1 h) →+*
      Ring.DirectLimit G (fun i j h ↦ f i j h) :=
  Ring.DirectLimit.lift
    (fun j : Set.Ici i₀ ↦ G j.1)
    (fun j k h ↦ f j.1 k.1 h)
    (Ring.DirectLimit G (fun i j h ↦ f i j h))
    (fun j ↦ Ring.DirectLimit.of G (fun i j h ↦ f i j h) j.1)
    (fun j k hjk x ↦ by
      -- Proof comment: the tail transition is just the original transition on the underlying
      -- stages, so the full direct-limit relation applies directly.
      simpa using
        (Ring.DirectLimit.of_f
          (G := fun j : Set.Ici i₀ ↦ G j.1)
          (f := fun j k h ↦ f j.1 k.1 h)
          hjk x))

/-- Helper for Lemma 10.127.11: passing from the full direct limit to the tail and back is the
identity on the full direct limit. -/
theorem tail_directLimit_to_full_comp_full_directLimit_to_tail {ι : Type v}
    [Preorder ι] [Nonempty ι] [IsDirectedOrder ι] (G : ι → Type w)
    [∀ i, CommRing (G i)] (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ f i j h)] (i₀ : ι) :
    (tail_directLimit_to_full G f i₀).comp (full_directLimit_to_tail G f i₀) = RingHom.id _ := by
  apply Ring.DirectLimit.hom_ext
  intro i
  ext x
  -- Proof comment: the composite lands in the chosen upper tail stage and then uses the
  -- direct-limit relation to return to the original stage.
  simpa [full_directLimit_to_tail, tail_stage_to_directLimit, tail_directLimit_to_full,
    RingHom.comp_apply] using
    (Ring.DirectLimit.of_f
      (f := fun i j h ↦ f i j h)
      (le_tail_upper_bound_left i₀ i) x)

/-- Helper for Lemma 10.127.11: passing from the tail direct limit to the full direct limit and
back is the identity on the tail direct limit. -/
theorem full_directLimit_to_tail_comp_tail_directLimit_to_full {ι : Type v}
    [Preorder ι] [Nonempty ι] [IsDirectedOrder ι] (G : ι → Type w)
    [∀ i, CommRing (G i)] (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ f i j h)] (i₀ : ι) :
    (full_directLimit_to_tail G f i₀).comp (tail_directLimit_to_full G f i₀) = RingHom.id _ := by
  apply Ring.DirectLimit.hom_ext
  intro j
  ext x
  -- Proof comment: a tail stage already lies above `i₀`, so the chosen upper-bound stage
  -- represents the same direct-limit element as the original tail stage.
  simpa [full_directLimit_to_tail, tail_stage_to_directLimit, tail_directLimit_to_full,
    RingHom.comp_apply] using
    (Ring.DirectLimit.of_f
      (G := fun j : Set.Ici i₀ ↦ G j.1)
      (f := fun j k h ↦ f j.1 k.1 h)
      (le_tail_upper_bound_left i₀ j.1) x)

/-- Helper for Lemma 10.127.11: the tail-to-full direct-limit comparison restricts to the
canonical inclusion on each tail-stage generator. -/
@[simp] theorem tail_directLimit_to_full_of {ι : Type v}
    [Preorder ι] [Nonempty ι] [IsDirectedOrder ι] (G : ι → Type w)
    [∀ i, CommRing (G i)] (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ f i j h)] (i₀ : ι) (j : Set.Ici i₀) (x : G j.1) :
    tail_directLimit_to_full G f i₀
        (Ring.DirectLimit.of (fun j : Set.Ici i₀ ↦ G j.1) (fun j k h ↦ f j.1 k.1 h) j x) =
      Ring.DirectLimit.of G (fun i j h ↦ f i j h) j.1 x := by
  -- Proof comment: this is the defining lift property of the tail comparison on a generator.
  simp [tail_directLimit_to_full, Ring.DirectLimit.lift_of]

/-- Helper for Lemma 10.127.11: the direct limit of a directed system is canonically isomorphic to
the direct limit of any tail above a fixed stage. -/
noncomputable def tail_directLimitIso {ι : Type v} [Preorder ι] [Nonempty ι]
    [IsDirectedOrder ι] {B : Type*} [CommRing B] (G : ι → Type w) [∀ i, CommRing (G i)]
    (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ f i j h)] (i₀ : ι)
    (colimitIso : Ring.DirectLimit G (fun i j h ↦ f i j h) ≃+* B) :
    Ring.DirectLimit (fun j : Set.Ici i₀ ↦ G j.1) (fun j k h ↦ f j.1 k.1 h) ≃+* B :=
  (RingEquiv.ofRingHom
      (tail_directLimit_to_full G f i₀)
      (full_directLimit_to_tail G f i₀)
      (tail_directLimit_to_full_comp_full_directLimit_to_tail G f i₀)
      (full_directLimit_to_tail_comp_tail_directLimit_to_full G f i₀)).trans colimitIso

/-- Helper for Lemma 10.127.11: the inverse tail-colimit equivalence sends a full stage
generator back to the same generator viewed in the tail. -/
theorem tail_directLimitIso_symm_toLimitHom {ι : Type v} [Preorder ι] [Nonempty ι]
    [IsDirectedOrder ι] {B : Type*} [CommRing B] (G : ι → Type w) [∀ i, CommRing (G i)]
    (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ f i j h)] (i₀ : ι)
    (colimitIso : Ring.DirectLimit G (fun i j h ↦ f i j h) ≃+* B)
    (j : Set.Ici i₀) (x : G j.1) :
    (tail_directLimitIso G f i₀ colimitIso).symm
        (colimitIso (Ring.DirectLimit.of G (fun i j h ↦ f i j h) j.1 x)) =
      Ring.DirectLimit.of (fun j : Set.Ici i₀ ↦ G j.1)
        (fun j k h ↦ f j.1 k.1 h) j x := by
  apply (tail_directLimitIso G f i₀ colimitIso).injective
  rw [RingEquiv.apply_symm_apply]
  simp [tail_directLimitIso, tail_directLimit_to_full_of]

/-- Helper for Lemma 10.127.11: if a comparison map from a stage algebra to a local target is
local after precomposing with the source algebra map, then the pulled-back prime lies over the
maximal ideal of the local source stage. -/
theorem comap_comap_maximalIdeal_of_local_comparison
    {A : Type v} {B : Type w} {T : Type u} [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B] [CommRing T] [IsLocalRing T]
    (σ : B →+* T) [IsLocalHom (σ.comp (algebraMap A B))] :
    Ideal.comap (algebraMap A B) (Ideal.comap σ (IsLocalRing.maximalIdeal T)) =
      IsLocalRing.maximalIdeal A := by
  -- Rewrite the pulled-back prime as the maximal-ideal pullback along the composite local map.
  simpa [Ideal.comap_comap] using
    (IsLocalRing.maximalIdeal_comap (σ.comp (algebraMap A B)))

/-- Helper for Lemma 10.127.11: if a prime of a stage algebra lies over the maximal ideal of the
local source stage, then the induced map to the prime localization is local. -/
theorem atPrime_algebraMap_isLocalHom_of_comap_maximalIdeal
    {A : Type v} {B : Type w} [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
    (q : Ideal B) [q.IsPrime]
    (hcomap : Ideal.comap (algebraMap A B) q = IsLocalRing.maximalIdeal A) :
    IsLocalHom (algebraMap A (Localization.AtPrime q)) := by
  -- Use the maximal-ideal pullback criterion for local ring homomorphisms.
  have hmax :
      Ideal.comap (algebraMap A (Localization.AtPrime q))
        (IsLocalRing.maximalIdeal (Localization.AtPrime q)) = IsLocalRing.maximalIdeal A := by
    change
      Ideal.comap
          ((algebraMap B (Localization.AtPrime q)).comp (algebraMap A B))
          (IsLocalRing.maximalIdeal (Localization.AtPrime q)) =
        IsLocalRing.maximalIdeal A
    rw [← Ideal.comap_comap (algebraMap A B) (algebraMap B (Localization.AtPrime q))]
    simpa [Localization.AtPrime.comap_maximalIdeal] using hcomap
  exact ((IsLocalRing.local_hom_TFAE
    (algebraMap A (Localization.AtPrime q))).out 4 0).mp hmax

/-- Helper for Lemma 10.127.11: the canonical map from the later source stage into the
localization of the descended tensor stage is the composite through the tensor-product stage. -/
noncomputable def descended_tensor_localizationMap
    {R₀ : Type v} {Rj : Type w} {P₀ : Type u} [CommRing R₀] [CommRing Rj] [CommRing P₀]
    [Algebra R₀ Rj] [Algebra R₀ P₀]
    (qj : Ideal (P₀ ⊗[R₀] Rj)) [qj.IsPrime] :
    Rj →+* Localization.AtPrime qj :=
  let Pj : Type _ := P₀ ⊗[R₀] Rj
  let _ : Algebra Rj Pj := Algebra.TensorProduct.rightAlgebra
  ((algebraMap Pj (Localization.AtPrime qj)).comp (algebraMap Rj Pj))

/-- Helper for Lemma 10.127.11: localizing a finitely presented base change at a prime keeps the
resulting stage map essentially of finite type over the later source stage. -/
theorem localized_baseChange_essFiniteType
    {R₀ : Type v} {Rj : Type w} {P₀ : Type u} [CommRing R₀] [CommRing Rj] [CommRing P₀]
    [Algebra R₀ Rj] [Algebra R₀ P₀] [Algebra.FinitePresentation R₀ P₀]
    (qj : Ideal (P₀ ⊗[R₀] Rj)) [qj.IsPrime] :
    (algebraMap Rj (Localization.AtPrime qj)).EssFiniteType := by
  have hcomm : (Rj ⊗[R₀] P₀) ≃ₐ[Rj] (P₀ ⊗[R₀] Rj) :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm R₀ Rj P₀).toRingEquiv)
      (fun x ↦ by
        change (Algebra.TensorProduct.comm R₀ Rj P₀) (x ⊗ₜ[R₀] (1 : P₀)) = (1 : P₀) ⊗ₜ[R₀] x
        rw [Algebra.TensorProduct.comm_tmul])
  have hbase : Algebra.FinitePresentation Rj (P₀ ⊗[R₀] Rj) :=
    Algebra.FinitePresentation.equiv hcomm
  letI : Algebra.FinitePresentation Rj (P₀ ⊗[R₀] Rj) := hbase
  have hess :
      Algebra.EssFinitePresentation Rj (Localization.AtPrime qj) :=
    Algebra.EssFinitePresentation.of_isLocalization
      (R := Rj) (S := Localization.AtPrime qj) (P := P₀ ⊗[R₀] Rj) qj.primeCompl
  -- Proof comment: the descended tensor algebra is finitely presented over `Rj`, and prime
  -- localization upgrades that presentation to an essentially finitely presented stage map.
  rw [RingHom.essFiniteType_algebraMap]
  exact Algebra.EssFinitePresentation.toEssFiniteType
    (R := Rj) (S := Localization.AtPrime qj) hess

/-- Helper for Lemma 10.127.11: once a descended stage algebra maps locally to the final target,
pulling back the maximal ideal and localizing at that prime produces exactly the local,
essentially-finite-type stage required by the source proof. -/
theorem localized_descended_stage_of_local_comparison
    {R₀ : Type v} {Rj : Type w} {P₀ : Type u} {T : Type*}
    [CommRing R₀] [CommRing Rj] [IsLocalRing Rj] [CommRing P₀] [CommRing T] [IsLocalRing T]
    [Algebra R₀ Rj] [Algebra R₀ P₀] [Algebra.FinitePresentation R₀ P₀]
    (σ : (P₀ ⊗[R₀] Rj) →+* T) [IsLocalHom (σ.comp (algebraMap Rj (P₀ ⊗[R₀] Rj)))] :
    let q : Ideal (P₀ ⊗[R₀] Rj) := Ideal.comap σ (IsLocalRing.maximalIdeal T)
    IsLocalHom (algebraMap Rj (Localization.AtPrime q)) ∧
      (algebraMap Rj (Localization.AtPrime q)).EssFiniteType := by
  let q : Ideal (P₀ ⊗[R₀] Rj) := Ideal.comap σ (IsLocalRing.maximalIdeal T)
  have hq_prime : q.IsPrime := by
    -- The contracted maximal ideal of the local target is prime.
    simpa [q] using Ideal.comap_isPrime σ (IsLocalRing.maximalIdeal T)
  letI : q.IsPrime := hq_prime
  have hcomap :
      Ideal.comap (algebraMap Rj (P₀ ⊗[R₀] Rj)) q = IsLocalRing.maximalIdeal Rj := by
    -- The comparison is local after precomposing with the stage map, so the pulled-back prime
    -- lies over the maximal ideal of `Rj`.
    simpa [q] using
      comap_comap_maximalIdeal_of_local_comparison
        (A := Rj) (B := P₀ ⊗[R₀] Rj) (T := T) σ
  constructor
  · -- The localization at a prime above the maximal ideal is again a local map from `Rj`.
    exact atPrime_algebraMap_isLocalHom_of_comap_maximalIdeal
      (A := Rj) (B := P₀ ⊗[R₀] Rj) q hcomap
  · -- Essential finite type comes from finite-presentation base change followed by localization.
    exact localized_baseChange_essFiniteType (R₀ := R₀) (Rj := Rj) (P₀ := P₀) q

omit [IsLocalRing R] in
/-- Helper for Lemma 10.127.11: in an approximation of `RingHom.id R`, the source-stage map to the
limit ring obtained by passing through the matching target stage agrees with the canonical source
direct-limit comparison map. -/
theorem id_source_stage_to_limit_eq_targetStageToLimitHom_comp_stageMap
    (A : DirectedLocalHomApproximation (RingHom.id R)) (i : A.Λ) :
    (A.targetStageToLimitHom i).comp (A.stageMap i) =
      Ring.DirectLimit.toLimitHom A.RStage (fun i j h ↦ A.map i j h) A.colimitIso i := by
  ext x
  -- Evaluate the owner-level colimit comparison on the stage element `x`.
  have hcolimit := congrArg
    (fun g : Ring.DirectLimit A.RStage (fun i j h ↦ A.map i j h) →+* R =>
      g (Ring.DirectLimit.of A.RStage (fun i j h ↦ A.map i j h) i x))
    A.colimit_comm
  -- The induced direct-limit map sends the source-stage generator to the matching target-stage
  -- generator, so the colimit square specializes to the desired stage comparison.
  simpa [DirectedLocalHomApproximation.targetStageToLimitHom, Ring.DirectLimit.toLimitHom,
    RingHom.comp_apply, Ring.DirectLimit.map_apply_of] using
    hcolimit

namespace Ring.DirectLimit

/-- Helper for Lemma 10.127.11: once a directed system of local rings is identified with a chosen
local limit ring, the induced map from any stage to that chosen limit ring is still local. -/
theorem toLimitHom_isLocalHom
    {Λ : Type v} [Preorder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    (RStage : Λ → Type w) [∀ i, CommRing (RStage i)]
    (map : ∀ i j, i ≤ j → RStage i →+* RStage j)
    [DirectedSystem RStage (fun i j h ↦ map i j h)]
    [∀ i, IsLocalRing (RStage i)] [∀ i j h, IsLocalHom (map i j h)]
    (colimitIso : Ring.DirectLimit RStage (fun i j h ↦ map i j h) ≃+* R) (i : Λ) :
    IsLocalHom
      (colimitIso.toRingHom.comp (Ring.DirectLimit.of RStage (fun i j h ↦ map i j h) i)) := by
  letI : IsLocalHom colimitIso.toRingHom :=
    Function.Surjective.isLocalHom _ colimitIso.surjective
  -- Proof comment: the stage map into the direct limit is already local, and a ring equivalence
  -- to the chosen limit ring preserves locality under composition.
  exact RingHom.isLocalHom_comp _ _

/-- Helper for Lemma 10.127.11: if every stage of a directed system maps locally to a fixed local
target ring in a compatible way, then the induced map from the direct limit is local. -/
theorem lift_isLocalHom
    {Λ : Type v} [Preorder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    (RStage : Λ → Type w) [∀ i, CommRing (RStage i)]
    (map : ∀ i j, i ≤ j → RStage i →+* RStage j)
    [DirectedSystem RStage (fun i j h ↦ map i j h)]
    [∀ i, IsLocalRing (RStage i)] [∀ i j h, IsLocalHom (map i j h)]
    {T : Type*} [CommRing T] [IsLocalRing T]
    (φ : (i : Λ) → RStage i →+* T)
    (hφ : ∀ i j (hij : i ≤ j), φ i = (φ j).comp (map i j hij))
    [∀ i, IsLocalHom (φ i)] :
    IsLocalHom
      (Ring.DirectLimit.lift RStage (fun i j h ↦ map i j h) T φ
        (fun i j hij x ↦ by
          simpa [RingHom.comp_apply] using
            (congrArg (fun g : RStage i →+* T => g x) (hφ i j hij)).symm)) := by
  refine ((IsLocalRing.local_hom_TFAE _).out 3 0).mp ?_
  intro z hz
  rcases Ring.DirectLimit.exists_of z with ⟨i, x, rfl⟩
  rw [Ideal.mem_comap, Ring.DirectLimit.lift_of]
  by_contra hx
  rw [IsLocalRing.notMem_maximalIdeal] at hx
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hz
  -- Proof comment: if the lifted image of a stage generator is a unit in `T`, locality of `φ i`
  -- makes the stage element a unit already, hence its direct-limit class is a unit as well.
  exact hz <|
    (Ring.DirectLimit.of RStage (fun i j h ↦ map i j h) i).isUnit_map <|
      (isUnit_map_iff (φ i) x).mp hx

end Ring.DirectLimit

namespace DirectedLocalHomApproximation

omit [IsLocalRing R] [IsLocalRing S] in
/-- Helper for Lemma 10.127.11: the owner base-change map multiplies the target transition and
the later stage map on pure tensors, for any directed local approximation. -/
theorem stageBaseChangeMap_tmul' {f' : R →+* S} (A' : DirectedLocalHomApproximation f')
    {i j : A'.Λ} (h : i ≤ j) :
    let _ : Algebra (A'.RStage i) (A'.SStage i) := (A'.stageMap i).toAlgebra
    let _ : Algebra (A'.RStage i) (A'.RStage j) := (A'.map i j h).toAlgebra
    ∀ (s : A'.SStage i) (r : A'.RStage j),
      A'.stageBaseChangeMap h (s ⊗ₜ[A'.RStage i] r) =
        A'.targetMap i j h s * A'.stageMap j r := by
  intro _ _ s r
  -- Proof comment: unfold the base-change map, evaluate the product map on the pure tensor, and
  -- close the algebra-hom coercions definitionally.
  simp [DirectedLocalHomApproximation.stageBaseChangeMap,
    Algebra.TensorProduct.productMap_apply_tmul]
  rfl

end DirectedLocalHomApproximation

/-- Helper for Lemma 10.127.11: the localization of a local ring at its maximal ideal collapses
back to the ring itself. -/
noncomputable def maxLocalizationCollapse (T : Type*) [CommRing T] [IsLocalRing T] :
    Localization.AtPrime (IsLocalRing.maximalIdeal T) ≃ₐ[T] T :=
  (IsLocalization.atUnits T (IsLocalRing.maximalIdeal T).primeCompl
    (fun x hx ↦ by
      have hunit : IsUnit x := by
        by_contra h
        exact hx ((IsLocalRing.mem_maximalIdeal x).mpr (mem_nonunits_iff.mpr h))
      exact hunit)).symm

/-- Helper for Lemma 10.127.11: the collapse equivalence restricts to the identity on the original
local ring. -/
@[simp] theorem maxLocalizationCollapse_algebraMap (T : Type*) [CommRing T] [IsLocalRing T]
    (t : T) :
    maxLocalizationCollapse T
        (algebraMap T (Localization.AtPrime (IsLocalRing.maximalIdeal T)) t) = t := by
  rw [maxLocalizationCollapse]
  exact (AlgEquiv.symm_apply_eq _).mpr rfl

/-- Helper for Lemma 10.127.11: if two stage comparisons to the final local target differ only by
precomposition with a transition map, then the pulled-back maximal ideals differ by the same
comap. -/
theorem comap_contracted_maximalIdeal_eq_of_comp
    {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    (τ : A →+* B) (σA : A →+* S) (σB : B →+* S) (hcomp : σA = σB.comp τ) :
    Ideal.comap τ (Ideal.comap σB (IsLocalRing.maximalIdeal S)) =
      Ideal.comap σA (IsLocalRing.maximalIdeal S) := by
  -- Rewrite the stage comparison through the given factorization and collapse the iterated comap.
  rw [hcomp, Ideal.comap_comap]

/-- Helper for Lemma 10.127.11: if a directed family of stage maps to a fixed local target is
compatible with the transition maps, then the induced prime localizations at the contracted
maximal ideals form a directed system. -/
theorem localized_contracted_maximalIdeal_directedSystem
    {Λ : Type v} [Preorder Λ] [Nonempty Λ]
    (G : Λ → Type w) [∀ i, CommRing (G i)]
    (map : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ map i j h)]
    (σ : (i : Λ) → G i →+* S)
    (hσ : ∀ i j (hij : i ≤ j), σ i = (σ j).comp (map i j hij)) :
    let q : (i : Λ) → Ideal (G i) := fun i ↦ Ideal.comap (σ i) (IsLocalRing.maximalIdeal S)
    DirectedSystem (fun i ↦ Localization.AtPrime (q i))
      (fun i j hij ↦
        Localization.localRingHom (q i) (q j) (map i j hij)
          ((comap_contracted_maximalIdeal_eq_of_comp
            (S := S) (τ := map i j hij) (σA := σ i) (σB := σ j) (hσ i j hij)).symm)) := by
  classical
  let q : (i : Λ) → Ideal (G i) := fun i ↦ Ideal.comap (σ i) (IsLocalRing.maximalIdeal S)
  let ρ :
      ∀ i j, i ≤ j → Localization.AtPrime (q i) →+* Localization.AtPrime (q j) :=
    fun i j hij ↦
      Localization.localRingHom (q i) (q j) (map i j hij)
        ((comap_contracted_maximalIdeal_eq_of_comp
          (S := S) (τ := map i j hij) (σA := σ i) (σB := σ j) (hσ i j hij)).symm)
  change DirectedSystem (fun i ↦ Localization.AtPrime (q i)) fun i j hij ↦ ρ i j hij
  refine
    { map_self := ?_
      map_map := ?_ }
  · intro i x
    have hmap_id : map i i le_rfl = RingHom.id _ := by
      ext y
      simpa using DirectedSystem.map_self (f := fun i j h ↦ map i j h) y
    have hρ_id : ρ i i le_rfl = RingHom.id _ := by
      -- Proof comment: after rewriting the transition at a fixed stage to the identity, the
      -- induced localization map is the canonical identity map.
      simpa [ρ, q, hmap_id] using (Localization.localRingHom_id (I := q i))
    simpa [hρ_id]
  · intro k j i hij hjk x
    have hmap_comp :
        map i k (le_trans hij hjk) = (map j k hjk).comp (map i j hij) := by
      ext y
      simpa [RingHom.comp_apply] using
        (DirectedSystem.map_map (f := fun i j h ↦ map i j h) hij hjk y).symm
    have hρ_comp :
        ρ i k (le_trans hij hjk) = (ρ j k hjk).comp (ρ i j hij) := by
      -- Proof comment: the localization transitions compose exactly because the raw transition
      -- maps compose and the contracted maximal ideals match by compatibility of the `σ i`.
      simpa [ρ, q, hmap_comp] using
        (Localization.localRingHom_comp
          (I := q i)
          (J := q j)
          (K := q k)
          (f := map i j hij)
          ((comap_contracted_maximalIdeal_eq_of_comp
            (S := S) (τ := map i j hij) (σA := σ i) (σB := σ j) (hσ i j hij)).symm)
          (g := map j k hjk)
          ((comap_contracted_maximalIdeal_eq_of_comp
            (S := S) (τ := map j k hjk) (σA := σ j) (σB := σ k) (hσ j k hjk)).symm))
    simpa [RingHom.comp_apply] using
      (congrArg (fun g : Localization.AtPrime (q i) →+* Localization.AtPrime (q k) => g x)
        hρ_comp).symm

/-- Helper for Lemma 10.127.11: compatible stage maps to a fixed local target induce compatible
maps from the corresponding prime localizations cut out by the target maximal ideal. -/
theorem localized_stage_maps_to_ambient_compatible
    {Λ : Type v} [Preorder Λ]
    (G : Λ → Type w) [∀ i, CommRing (G i)]
    (map : ∀ i j, i ≤ j → G i →+* G j)
    (σ : (i : Λ) → G i →+* S)
    (hσ : ∀ i j (hij : i ≤ j), σ i = (σ j).comp (map i j hij)) :
    let q : (i : Λ) → Ideal (G i) := fun i ↦ Ideal.comap (σ i) (IsLocalRing.maximalIdeal S)
    let ρ :
        ∀ i j, i ≤ j → Localization.AtPrime (q i) →+* Localization.AtPrime (q j) :=
      fun i j hij ↦
        Localization.localRingHom (q i) (q j) (map i j hij)
          ((comap_contracted_maximalIdeal_eq_of_comp
            (S := S) (τ := map i j hij) (σA := σ i) (σB := σ j) (hσ i j hij)).symm)
    let φ : (i : Λ) → Localization.AtPrime (q i) →+* S :=
      fun i ↦ (maxLocalizationCollapse S :
          Localization.AtPrime (IsLocalRing.maximalIdeal S) →+* S).comp
        (Localization.localRingHom (q i) (IsLocalRing.maximalIdeal S) (σ i) rfl)
    ∀ i j (hij : i ≤ j), φ i = (φ j).comp (ρ i j hij) := by
  dsimp
  intro i j hij
  -- Proof comment: compatibility on the raw stages passes to the prime localizations by the
  -- composition formula for `Localization.localRingHom`, and the collapse factor is shared.
  have hcomp :
      Localization.localRingHom (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S))
          (IsLocalRing.maximalIdeal S) (σ i) rfl =
        (Localization.localRingHom (Ideal.comap (σ j) (IsLocalRing.maximalIdeal S))
            (IsLocalRing.maximalIdeal S) (σ j) rfl).comp
          (Localization.localRingHom
            (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S))
            (Ideal.comap (σ j) (IsLocalRing.maximalIdeal S))
            (map i j hij)
            ((comap_contracted_maximalIdeal_eq_of_comp
              (S := S) (τ := map i j hij) (σA := σ i) (σB := σ j) (hσ i j hij)).symm)) := by
    apply Localization.localRingHom_unique
    intro x
    have hx : σ j (map i j hij x) = σ i x :=
      (congrArg (fun g : G i →+* S => g x) (hσ i j hij)).symm
    simp [RingHom.comp_apply, Localization.localRingHom_to_map, hx]
  rw [hcomp, RingHom.comp_assoc]

/-- Helper for Lemma 10.127.11: the compatible localized stage maps to `S` lift to a map from the
direct limit of the localized system. -/
noncomputable def tail_target_colimit_to_ambient
    {Λ : Type v} [Preorder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    (G : Λ → Type w) [∀ i, CommRing (G i)]
    (map : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ map i j h)]
    (σ : (i : Λ) → G i →+* S)
    (hσ : ∀ i j (hij : i ≤ j), σ i = (σ j).comp (map i j hij)) :
    let q : (i : Λ) → Ideal (G i) := fun i ↦ Ideal.comap (σ i) (IsLocalRing.maximalIdeal S)
    let ρ :
        ∀ i j, i ≤ j → Localization.AtPrime (q i) →+* Localization.AtPrime (q j) :=
      fun i j hij ↦
        Localization.localRingHom (q i) (q j) (map i j hij)
          ((comap_contracted_maximalIdeal_eq_of_comp
            (S := S) (τ := map i j hij) (σA := σ i) (σB := σ j) (hσ i j hij)).symm)
    Ring.DirectLimit (fun i ↦ Localization.AtPrime (q i)) (fun i j h ↦ ρ i j h) →+* S :=
  let q : (i : Λ) → Ideal (G i) := fun i ↦ Ideal.comap (σ i) (IsLocalRing.maximalIdeal S)
  let ρ :
      ∀ i j, i ≤ j → Localization.AtPrime (q i) →+* Localization.AtPrime (q j) :=
    fun i j hij ↦
      Localization.localRingHom (q i) (q j) (map i j hij)
        ((comap_contracted_maximalIdeal_eq_of_comp
          (S := S) (τ := map i j hij) (σA := σ i) (σB := σ j) (hσ i j hij)).symm)
  let φ : (i : Λ) → Localization.AtPrime (q i) →+* S :=
    fun i ↦ (maxLocalizationCollapse S :
        Localization.AtPrime (IsLocalRing.maximalIdeal S) →+* S).comp
      (Localization.localRingHom (q i) (IsLocalRing.maximalIdeal S) (σ i) rfl)
  -- Proof comment: the stagewise localized comparison maps are compatible, so the universal
  -- property of the direct limit assembles them into a single ambient comparison.
  Ring.DirectLimit.lift
    (fun i ↦ Localization.AtPrime (q i))
    (fun i j h ↦ ρ i j h)
    S
    φ
    (fun i j hij x ↦ by
      have h := congrArg (fun g : Localization.AtPrime (q i) →+* S => g x)
        (localized_stage_maps_to_ambient_compatible
          (S := S) (G := G) (map := map) (σ := σ) (hσ := hσ) i j hij)
      simpa [φ, ρ, q, RingHom.comp_apply] using h.symm)

/-- Helper for Lemma 10.127.11: the lifted ambient comparison map agrees with the given localized
stage map on each direct-limit generator. -/
@[simp] theorem tail_target_colimit_to_ambient_of
    {Λ : Type v} [Preorder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    (G : Λ → Type w) [∀ i, CommRing (G i)]
    (map : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ map i j h)]
    (σ : (i : Λ) → G i →+* S)
    (hσ : ∀ i j (hij : i ≤ j), σ i = (σ j).comp (map i j hij))
    (i : Λ) (x : Localization.AtPrime (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S))) :
    tail_target_colimit_to_ambient (S := S) G map σ hσ
        (Ring.DirectLimit.of
          (fun i ↦ Localization.AtPrime (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S)))
          (fun i j hij ↦
            Localization.localRingHom
              (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S))
              (Ideal.comap (σ j) (IsLocalRing.maximalIdeal S))
              (map i j hij)
              ((comap_contracted_maximalIdeal_eq_of_comp
                (S := S) (τ := map i j hij) (σA := σ i) (σB := σ j) (hσ i j hij)).symm))
          i x) =
      (maxLocalizationCollapse S :
          Localization.AtPrime (IsLocalRing.maximalIdeal S) →+* S)
        (Localization.localRingHom
          (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S))
          (IsLocalRing.maximalIdeal S)
          (σ i)
          rfl
          x) := by
  -- Proof comment: this is the defining property of the direct-limit lift on a stage generator.
  simp [tail_target_colimit_to_ambient]

omit [IsLocalRing R] in
/-- Helper for Lemma 10.127.11: the tensor-product comparison maps from a descended stage algebra
to the colimit ring are compatible with the tail transition maps. -/
theorem tensorProduct_map_to_limit_comp
    {Λ : Type v} [Preorder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    (RStage : Λ → Type w) [∀ i, CommRing (RStage i)]
    (map : ∀ i j, i ≤ j → RStage i →+* RStage j)
    [DirectedSystem RStage (fun i j h ↦ map i j h)]
    (_colimitIso : Ring.DirectLimit RStage (fun i j h ↦ map i j h) ≃+* R)
    {i₀ : Λ} {Bj : Type*} {Bk : Type*} {T : Type*}
    [CommRing Bj] [CommRing Bk] [CommRing T]
    [Algebra (RStage i₀) Bj] [Algebra (RStage i₀) Bk] [Algebra (RStage i₀) T]
    (P₀ : Type u) [CommRing P₀] [Algebra (RStage i₀) P₀]
    (τ : Bj →ₐ[RStage i₀] Bk) (σj : Bj →ₐ[RStage i₀] T) (σk : Bk →ₐ[RStage i₀] T)
    (hcomp : σj = σk.comp τ) :
    let τtensor : P₀ ⊗[RStage i₀] Bj →ₐ[P₀] P₀ ⊗[RStage i₀] Bk :=
      Algebra.TensorProduct.map (AlgHom.id P₀ P₀) τ
    let σjtensor : P₀ ⊗[RStage i₀] Bj →ₐ[P₀] P₀ ⊗[RStage i₀] T :=
      Algebra.TensorProduct.map (AlgHom.id P₀ P₀) σj
    let σktensor : P₀ ⊗[RStage i₀] Bk →ₐ[P₀] P₀ ⊗[RStage i₀] T :=
      Algebra.TensorProduct.map (AlgHom.id P₀ P₀) σk
    σjtensor = σktensor.comp τtensor := by
  -- Proof comment: tensoring with the identity on the descended algebra preserves composition on
  -- the right factor, so the tensor comparison inherits the same compatibility relation.
  subst hcomp
  simpa using
    Algebra.TensorProduct.map_comp (AlgHom.id P₀ P₀) (AlgHom.id P₀ P₀) σk τ

/-- Helper for Lemma 10.127.11: a map into the minimal stage of a tail system extends along the
canonical direct-limit inclusion to a map into the tail direct limit. -/
noncomputable def tail_targetDirectLimit_of_minimal_stage
    {Λ : Type v} [Preorder Λ] (i₀ : Λ)
    {P₀ : Type u} [CommRing P₀]
    (Sj : Set.Ici i₀ → Type w) [∀ j, CommRing (Sj j)]
    (ρ : ∀ (j k : Set.Ici i₀), j ≤ k → Sj j →+* Sj k)
    [DirectedSystem Sj (fun j k h ↦ ρ j k h)]
    [Nonempty (Set.Ici i₀)]
    (φ₀ : P₀ →+* Sj ⟨i₀, le_rfl⟩) :
    P₀ →+* Ring.DirectLimit Sj (fun j k h ↦ ρ j k h) :=
  let j0 : Set.Ici i₀ := ⟨i₀, le_rfl⟩
  -- The only work is to pass from the chosen minimal stage map to the universal direct-limit map.
  (Ring.DirectLimit.of Sj (fun j k h ↦ ρ j k h) j0).comp φ₀

/-- Helper for Lemma 10.127.11: composing a tail direct-limit lift with the canonical inclusion of
the minimal stage recovers the chosen minimal-stage comparison map. -/
theorem lift_comp_tail_targetDirectLimit_of_minimal_stage
    {Λ : Type v} [Preorder Λ] (i₀ : Λ)
    {P₀ : Type u} [CommRing P₀]
    (Sj : Set.Ici i₀ → Type w) [∀ j, CommRing (Sj j)]
    (ρ : ∀ (j k : Set.Ici i₀), j ≤ k → Sj j →+* Sj k)
    [DirectedSystem Sj (fun j k h ↦ ρ j k h)]
    [Nonempty (Set.Ici i₀)]
    {T : Type*} [CommRing T]
    (φ₀ : P₀ →+* Sj ⟨i₀, le_rfl⟩)
    (φ : (j : Set.Ici i₀) → Sj j →+* T)
    (hφ : ∀ j k (hjk : j ≤ k), φ j = (φ k).comp (ρ j k hjk)) :
    (Ring.DirectLimit.lift Sj (fun j k h ↦ ρ j k h) T φ
        (fun j k hjk x ↦ by
          simpa [RingHom.comp_apply] using
            (congrArg (fun g : Sj j →+* T => g x) (hφ j k hjk)).symm)).comp
        (tail_targetDirectLimit_of_minimal_stage (i₀ := i₀) (Sj := Sj) ρ φ₀) =
      (φ ⟨i₀, le_rfl⟩).comp φ₀ := by
  ext x
  -- Proof comment: the tail map lands in the distinguished minimal stage, so the direct-limit
  -- lift immediately evaluates back to the chosen stage comparison.
  simp [tail_targetDirectLimit_of_minimal_stage, RingHom.comp_apply, Ring.DirectLimit.lift_of]

/-- Helper for Lemma 10.127.11: if `q ≤ m`, then localizing `A` at `m` and pushing `q` forward
produces a prime whose contraction is again `q`. -/
theorem localization_atPrime_map_under
    {A : Type v} [CommRing A] {q m : Ideal A} [q.IsPrime] [m.IsPrime] (hqm : q ≤ m) :
    (Ideal.map (algebraMap A (Localization.AtPrime m)) q).under A = q := by
  -- This is the standard contraction formula for primes under localization at `m`.
  simpa using
    (Ideal.under_map_of_isLocalizationAtPrime
      (S := Localization.AtPrime m) (q := m) hqm :
        (Ideal.map (algebraMap A (Localization.AtPrime m)) q).under A = q)

/-- Helper for Lemma 10.127.11: if `q ≤ m`, then the image of `q` in `A_m` is still prime. -/
theorem localization_atPrime_map_isPrime
    {A : Type v} [CommRing A] {q m : Ideal A} [q.IsPrime] [m.IsPrime] (hqm : q ≤ m) :
    (Ideal.map (algebraMap A (Localization.AtPrime m)) q).IsPrime := by
  -- Localization preserves primeness for primes lying under the localization prime.
  simpa using
    (Ideal.isPrime_map_of_isLocalizationAtPrime
      (S := Localization.AtPrime m) (q := m) hqm :
        (Ideal.map (algebraMap A (Localization.AtPrime m)) q).IsPrime)

/-- Helper for Lemma 10.127.11: localizing `A_m` further at the image of `q ≤ m` recovers
`A_q`. -/
noncomputable def localization_atPrime_map_algEquiv
    {A : Type v} [CommRing A] {q m q' : Ideal A} [q.IsPrime] [m.IsPrime] [q'.IsPrime]
    (hq' :
      q' = Ideal.comap (algebraMap A (Localization m.primeCompl))
        (Ideal.map (algebraMap A (Localization.AtPrime m)) q))
    [(Ideal.map (algebraMap A (Localization.AtPrime m)) q).IsPrime] :
    Localization.AtPrime (Ideal.map (algebraMap A (Localization.AtPrime m)) q) ≃ₐ[A]
      Localization.AtPrime q' := by
  subst q'
  -- Collapse the iterated localization by the canonical localization-of-localization equivalence.
  exact
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      m.primeCompl
      (Ideal.map (algebraMap A (Localization.AtPrime m)) q)).symm

/-- Helper for Lemma 10.127.11: the inverse of the two-step localization equivalence is the
canonical local map from `A_q` to the further localization of `A_m`. -/
theorem localization_atPrime_map_algEquiv_symm_toRingHom
    {A : Type v} [CommRing A] {q m : Ideal A} [q.IsPrime] [m.IsPrime] (hqm : q ≤ m) :
    let p_m : Ideal (Localization.AtPrime m) := Ideal.map (algebraMap A (Localization.AtPrime m)) q
    letI : p_m.IsPrime := localization_atPrime_map_isPrime (A := A) hqm
    let eLoc : Localization.AtPrime p_m ≃ₐ[A] Localization.AtPrime q :=
      localization_atPrime_map_algEquiv (A := A) (q := q) (m := m) (q' := q)
        (localization_atPrime_map_under (A := A) hqm).symm
    eLoc.symm.toRingHom =
      Localization.localRingHom q p_m (algebraMap A (Localization.AtPrime m))
        (localization_atPrime_map_under (A := A) hqm).symm := by
  let p_m : Ideal (Localization.AtPrime m) := Ideal.map (algebraMap A (Localization.AtPrime m)) q
  letI : p_m.IsPrime := localization_atPrime_map_isPrime (A := A) hqm
  let eLoc : Localization.AtPrime p_m ≃ₐ[A] Localization.AtPrime q :=
    localization_atPrime_map_algEquiv (A := A) (q := q) (m := m) (q' := q)
      (localization_atPrime_map_under (A := A) hqm).symm
  change eLoc.symm.toRingHom =
      Localization.localRingHom q p_m (algebraMap A (Localization.AtPrime m))
        (localization_atPrime_map_under (A := A) hqm).symm
  -- Equality out of `A_q` is determined by the images of elements of the original ring `A`.
  symm
  apply Localization.localRingHom_unique
  intro x
  calc
    eLoc.symm (algebraMap A (Localization.AtPrime q) x) =
        algebraMap A (Localization.AtPrime p_m) x := eLoc.symm.commutes x
    _ =
        algebraMap (Localization.AtPrime m) (Localization.AtPrime p_m)
          (algebraMap A (Localization.AtPrime m) x) := rfl

/-- Helper for Lemma 10.127.11: after localizing a local ring `T` at its maximal ideal and then
collapsing that localization back to `T`, a generator coming from a prime localization stage
returns to its original image in `T`. -/
theorem max_localization_collapse_comp_localRingHom_to_map
    {A : Type v} {T : Type w} [CommRing A] [CommRing T] [IsLocalRing T]
    (σ : A →+* T) (q : Ideal A) [q.IsPrime]
    [IsLocalization (IsLocalRing.maximalIdeal T).primeCompl T]
    (e : Localization.AtPrime (IsLocalRing.maximalIdeal T) ≃ₐ[T] T)
    (hq : Ideal.comap σ (IsLocalRing.maximalIdeal T) = q)
    (x : A) :
    (e.toRingHom.comp
      (Localization.localRingHom q (IsLocalRing.maximalIdeal T) σ hq.symm))
        (algebraMap A (Localization.AtPrime q) x) = σ x := by
  -- Proof comment: the local ring hom sends the localization generator to the corresponding
  -- element of `T_(m_T)`, and the algebra equivalence `e` then cancels that final localization.
  simp [Localization.localRingHom_to_map]

end

section SameUniverse

variable {R S : Type u} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
variable (f : R →+* S) [IsLocalHom f]

omit [IsLocalRing R] in
/-- Helper for Lemma 10.127.11: every polynomial over the colimit ring descends to a polynomial
over some stage of the directed system. -/
theorem mvPolynomial_descends
    {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    (RStage : Λ → Type u) [∀ i, CommRing (RStage i)]
    (map : ∀ i j, i ≤ j → RStage i →+* RStage j)
    [DirectedSystem RStage (fun i j h ↦ map i j h)]
    (colimitIso : Ring.DirectLimit RStage (fun i j h ↦ map i j h) ≃+* R)
    {n : ℕ} (g : MvPolynomial (Fin n) R) :
    ∃ (i : Λ) (g₀ : MvPolynomial (Fin n) (RStage i)),
      MvPolynomial.map
        (Ring.DirectLimit.toLimitHom RStage (fun i j h ↦ map i j h) colimitIso i) g₀ = g := by
  classical
  induction g using MvPolynomial.induction_on with
  | C r =>
    -- Proof comment: a constant descends because the colimit identification is surjective and
    -- every direct-limit element comes from a stage.
    obtain ⟨z, hz⟩ := colimitIso.surjective r
    obtain ⟨i, x, hx⟩ := Ring.DirectLimit.exists_of z
    refine ⟨i, MvPolynomial.C x, ?_⟩
    rw [MvPolynomial.map_C]
    rw [show Ring.DirectLimit.toLimitHom RStage (fun i j h ↦ map i j h) colimitIso i x =
      colimitIso (Ring.DirectLimit.of RStage (fun i j h ↦ ⇑(map i j h)) i x) from rfl]
    rw [hx, hz]
  | add p q hp hq =>
    -- Proof comment: sums descend to a common upper stage by directedness.
    obtain ⟨i, p₀, hp₀⟩ := hp
    obtain ⟨j, q₀, hq₀⟩ := hq
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    refine ⟨k, MvPolynomial.map (map i k hik) p₀ + MvPolynomial.map (map j k hjk) q₀, ?_⟩
    rw [map_add, MvPolynomial.map_map, MvPolynomial.map_map,
      Ring.DirectLimit.toLimitHom_comp_map, Ring.DirectLimit.toLimitHom_comp_map, hp₀, hq₀]
  | mul_X p k hp =>
    -- Proof comment: multiplying by a variable stays at the same stage.
    obtain ⟨i, p₀, hp₀⟩ := hp
    refine ⟨i, p₀ * MvPolynomial.X k, ?_⟩
    rw [map_mul, MvPolynomial.map_X, hp₀]

omit [IsLocalRing R] in
/-- Helper for Lemma 10.127.11: a finitely presented algebra over the colimit ring descends to a
finitely presented algebra over some stage, up to base change. -/
theorem finitelyPresented_algebra_descends
    {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    (RStage : Λ → Type u) [∀ i, CommRing (RStage i)]
    (map : ∀ i j, i ≤ j → RStage i →+* RStage j)
    [DirectedSystem RStage (fun i j h ↦ map i j h)]
    (colimitIso : Ring.DirectLimit RStage (fun i j h ↦ map i j h) ≃+* R)
    (P : Type u) [CommRing P] [Algebra R P] [Algebra.FinitePresentation R P] :
    ∃ (i₀ : Λ) (P₀ : Type u) (_ : CommRing P₀) (_ : Algebra (RStage i₀) P₀)
      (_ : Algebra.FinitePresentation (RStage i₀) P₀),
      letI : Algebra (RStage i₀) R :=
        (Ring.DirectLimit.toLimitHom RStage (fun i j h ↦ map i j h) colimitIso i₀).toAlgebra
      letI : Algebra R (P₀ ⊗[RStage i₀] R) := Algebra.TensorProduct.rightAlgebra
      Nonempty (P₀ ⊗[RStage i₀] R ≃ₐ[R] P) := by
  classical
  obtain ⟨n, φ, hφsurj, hφker⟩ := ‹Algebra.FinitePresentation R P›.out
  obtain ⟨s, hs⟩ := hφker
  choose stage poly hpoly using fun g : MvPolynomial (Fin n) R ↦
    mvPolynomial_descends RStage map colimitIso g
  obtain ⟨i₀, hi₀⟩ := (s.image stage).exists_le
  letI : Algebra (RStage i₀) R :=
    (Ring.DirectLimit.toLimitHom RStage (fun i j h ↦ map i j h) colimitIso i₀).toAlgebra
  -- Proof comment: push every descended relation polynomial up to the common stage `i₀`.
  let liftP : (g : MvPolynomial (Fin n) R) → g ∈ s → MvPolynomial (Fin n) (RStage i₀) :=
    fun g hg ↦
      MvPolynomial.map (map (stage g) i₀ (hi₀ _ (Finset.mem_image_of_mem stage hg))) (poly g)
  let s₀ : Finset (MvPolynomial (Fin n) (RStage i₀)) :=
    s.attach.image fun g ↦ liftP g.1 g.2
  have hlift : ∀ (g) (hg : g ∈ s),
      MvPolynomial.map (algebraMap (RStage i₀) R) (liftP g hg) = g := by
    intro g hg
    change MvPolynomial.map (algebraMap (RStage i₀) R)
        (MvPolynomial.map (map (stage g) i₀ (hi₀ _ (Finset.mem_image_of_mem stage hg)))
          (poly g)) = g
    rw [MvPolynomial.map_map, RingHom.algebraMap_toAlgebra,
      Ring.DirectLimit.toLimitHom_comp_map, hpoly]
  -- Proof comment: the lifted generators present exactly the kernel after base change.
  have himg :
      Ideal.map (MvPolynomial.map (algebraMap (RStage i₀) R) :
          MvPolynomial (Fin n) (RStage i₀) →+* MvPolynomial (Fin n) R)
        (Ideal.span (↑s₀ : Set (MvPolynomial (Fin n) (RStage i₀)))) =
        RingHom.ker φ.toRingHom := by
    rw [Ideal.map_span, ← hs]
    congr 1
    ext g
    simp only [s₀, Set.mem_image, Finset.coe_image, Finset.mem_coe,
      Finset.mem_attach, true_and, Subtype.exists]
    constructor
    · rintro ⟨-, ⟨g', hg', rfl⟩, rfl⟩
      simpa [hlift g' hg'] using hg'
    · intro hg
      exact ⟨liftP g hg, ⟨g, hg, rfl⟩, hlift g hg⟩
  let P₀ : Type u := (MvPolynomial (Fin n) (RStage i₀)) ⧸
    (Ideal.span (↑s₀ : Set (MvPolynomial (Fin n) (RStage i₀))))
  refine ⟨i₀, P₀, inferInstance, inferInstance,
    Algebra.FinitePresentation.quotient ⟨s₀, rfl⟩, ⟨?_⟩⟩
  -- Proof comment: commute the tensor factors, exchange the quotient with the base change, and
  -- identify the extended relation ideal with the kernel of the chosen presentation.
  refine AlgEquiv.trans
    (AlgEquiv.ofRingEquiv
      (f := (Algebra.TensorProduct.comm (RStage i₀)
        (MvPolynomial (Fin n) (RStage i₀) ⧸
          Ideal.span (↑s₀ : Set (MvPolynomial (Fin n) (RStage i₀)))) R).toRingEquiv)
      (fun x ↦ by
        change (Algebra.TensorProduct.comm (RStage i₀)
            (MvPolynomial (Fin n) (RStage i₀) ⧸
              Ideal.span (↑s₀ : Set (MvPolynomial (Fin n) (RStage i₀)))) R)
            ((1 : MvPolynomial (Fin n) (RStage i₀) ⧸
              Ideal.span (↑s₀ : Set (MvPolynomial (Fin n) (RStage i₀)))) ⊗ₜ[RStage i₀] x) =
          x ⊗ₜ[RStage i₀] (1 : MvPolynomial (Fin n) (RStage i₀) ⧸
            Ideal.span (↑s₀ : Set (MvPolynomial (Fin n) (RStage i₀))))
        rw [Algebra.TensorProduct.comm_tmul])) ?_
  letI : IsScalarTower (RStage i₀) R R := IsScalarTower.right
  let e₂ : R ⊗[RStage i₀]
      ((MvPolynomial (Fin n) (RStage i₀)) ⧸
        (Ideal.span (↑s₀ : Set (MvPolynomial (Fin n) (RStage i₀))))) ≃ₐ[R]
      (R ⊗[RStage i₀] MvPolynomial (Fin n) (RStage i₀)) ⧸
        Ideal.map (Algebra.TensorProduct.includeRight :
            MvPolynomial (Fin n) (RStage i₀) →ₐ[RStage i₀]
              R ⊗[RStage i₀] MvPolynomial (Fin n) (RStage i₀))
          (Ideal.span (↑s₀ : Set (MvPolynomial (Fin n) (RStage i₀)))) :=
    Algebra.TensorProduct.tensorQuotientEquiv
      (R := RStage i₀) (S := R) (A := R) (T := MvPolynomial (Fin n) (RStage i₀))
      (I := Ideal.span (↑s₀ : Set (MvPolynomial (Fin n) (RStage i₀))))
  refine AlgEquiv.trans e₂ ?_
  have hcomp :
      ((MvPolynomial.algebraTensorAlgEquiv (RStage i₀) R :
          R ⊗[RStage i₀] MvPolynomial (Fin n) (RStage i₀) ≃ₐ[R] MvPolynomial (Fin n) R) :
            R ⊗[RStage i₀] MvPolynomial (Fin n) (RStage i₀) →+* MvPolynomial (Fin n) R).comp
          (Algebra.TensorProduct.includeRight :
            MvPolynomial (Fin n) (RStage i₀) →ₐ[RStage i₀]
              R ⊗[RStage i₀] MvPolynomial (Fin n) (RStage i₀)) =
        (MvPolynomial.map (algebraMap (RStage i₀) R) :
          MvPolynomial (Fin n) (RStage i₀) →+* MvPolynomial (Fin n) R) := by
    ext p
    · simp [MvPolynomial.algebraTensorAlgEquiv_tmul]
    · simp [MvPolynomial.algebraTensorAlgEquiv_tmul]
  refine AlgEquiv.trans
    (Ideal.quotientEquivAlg
      (I := Ideal.map (Algebra.TensorProduct.includeRight :
          MvPolynomial (Fin n) (RStage i₀) →ₐ[RStage i₀]
            R ⊗[RStage i₀] MvPolynomial (Fin n) (RStage i₀))
        (Ideal.span (↑s₀ : Set (MvPolynomial (Fin n) (RStage i₀)))))
      (J := RingHom.ker φ.toRingHom)
      (MvPolynomial.algebraTensorAlgEquiv (RStage i₀) R)
      (by
        rw [← himg]
        simp only [Ideal.map_span, ← Set.image_comp]
        refine congrArg Ideal.span (Set.image_congr fun p _ ↦ ?_)
        exact (congrArg
          (fun h : MvPolynomial (Fin n) (RStage i₀) →+* MvPolynomial (Fin n) R => h p)
          hcomp).symm)) ?_
  exact Ideal.quotientKerAlgEquivOfSurjective hφsurj

/-- Helper for Lemma 10.127.11: an essentially finitely presented local map can be rewritten as a
finitely presented model localized at the prime cut out by the maximal ideal of the local target.
-/
theorem exists_local_finitePresentation_model
    (hf : f.EssFinitePresentation) :
    ∃ (P : Type u) (_ : CommRing P) (g : R →+* P) (_ : g.FinitePresentation)
      (q : Ideal P) (_ : q.IsPrime) (_ : Algebra P S),
      q.primeCompl.IsLocalizationMap (algebraMap P S) ∧
        f = (algebraMap P S).comp g ∧
        Ideal.comap g q = IsLocalRing.maximalIdeal R := by
  obtain ⟨P, _, g, hg, M, _, hloc, hfg⟩ :=
    (RingHom.essFinitePresentation_iff_exists_finitePresentation (f := f)).mp hf
  let q : Ideal P := Ideal.comap (algebraMap P S) (IsLocalRing.maximalIdeal S)
  have hq :
      q.IsPrime ∧ q.primeCompl.IsLocalizationMap (algebraMap P S) := by
    -- Replace the original localization witness by the local prime localization at the contracted
    -- maximal ideal of `S`.
    simpa [q] using
      (local_isLocalization_at_comap_maximalIdeal (P := P) (T := S) (M := M))
  refine ⟨P, inferInstance, g, hg, q, hq.1, inferInstance, hq.2, hfg, ?_⟩
  -- Proof comment: pulling back the maximal ideal along the factored local map recovers the
  -- maximal ideal of `R`.
  simpa [q, hfg, Ideal.comap_comap] using IsLocalRing.maximalIdeal_comap f

/-- Helper for Lemma 10.127.11: after choosing the local finite-presentation model of `S`, the
finitely presented algebra part descends to a stage of an approximation of `RingHom.id R`. -/
theorem exists_descended_local_finitePresentation_model
    (hf : f.EssFinitePresentation) :
    ∃ (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R))
      (_ : ∀ i j (h : i ≤ j), IsLocalHom (A₀.map i j h))
      (_ : ∀ i, IsLocalHom
        (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i))
      (P : Type u) (_ : CommRing P) (g : R →+* P) (_ : g.FinitePresentation)
      (q : Ideal P) (_ : q.IsPrime) (_ : Algebra P S),
      q.primeCompl.IsLocalizationMap (algebraMap P S) ∧
        f = (algebraMap P S).comp g ∧
        Ideal.comap g q = IsLocalRing.maximalIdeal R ∧
        ∃ (i₀ : A₀.Λ) (P₀ : Type u) (_ : CommRing P₀)
          (_ : Algebra (A₀.RStage i₀) P₀) (_ : Algebra.FinitePresentation (A₀.RStage i₀) P₀),
          letI : Algebra R P := g.toAlgebra
          letI : Algebra (A₀.RStage i₀) R :=
            (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso
              i₀).toAlgebra
          letI : Algebra R (P₀ ⊗[A₀.RStage i₀] R) := Algebra.TensorProduct.rightAlgebra
          Nonempty (P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P) := by
  have hid : (RingHom.id R).EssFiniteType := by
    -- The identity map is essentially finitely presented, hence essentially of finite type.
    rw [← Algebra.algebraMap_self (R := R), RingHom.essFiniteType_algebraMap]
    infer_instance
  obtain ⟨A₀, _, hA₀map, hA₀lim⟩ :=
    exists_directed_local_essFiniteType_approximation_isLocalHom (f := RingHom.id R) hid
  obtain ⟨P, _, g, hg, q, hq, _, hlocq, hfg, hqR⟩ :=
    exists_local_finitePresentation_model (f := f) hf
  letI : Algebra R P := g.toAlgebra
  have hPfp : Algebra.FinitePresentation R P := by
    -- Reinterpret finite presentation of the ring map as finite presentation of the corresponding
    -- `R`-algebra.
    rw [← RingHom.finitePresentation_algebraMap]
    exact hg
  obtain ⟨i₀, P₀, _, _, _, e⟩ :=
    finitelyPresented_algebra_descends (R := R) A₀.RStage (fun i j h ↦ A₀.map i j h)
      A₀.colimitIso P
  exact ⟨A₀, hA₀map, hA₀lim, P, inferInstance, g, hg, q, hq, inferInstance, hlocq, hfg, hqR,
    i₀, P₀, inferInstance, inferInstance, inferInstance, e⟩

omit [IsLocalRing R] [IsLocalRing S] in
/-- Helper for Lemma 10.127.11: if the base-change domain of a transition is identified with a
prime localization and the transported owner map is the canonical localization map, then that
transition is a localization at a prime ideal. -/
theorem transitionIsLocalizationAtPrime_of_domain_equiv
    {f : R →+* S} (A : DirectedLocalHomApproximation f) {i j : A.Λ} (h : i ≤ j)
    {T : Type*} [CommRing T] (e : A.targetStageBaseChange h ≃+* T)
    (p : Ideal T) [p.IsPrime]
    (hmap :
      p.primeCompl.IsLocalizationMap ((A.stageBaseChangeMap h).comp e.symm.toRingHom)) :
    A.TransitionIsLocalizationAtPrime h := by
  let q : Ideal (A.targetStageBaseChange h) := Ideal.comap e.toRingHom p
  have hq_prime : q.IsPrime := by
    -- The transported prime is prime because ring equivalences preserve contraction of primes.
    simpa [q] using Ideal.comap_isPrime e.toRingHom p
  letI : q.IsPrime := hq_prime
  letI : Algebra T (A.SStage j) := ((A.stageBaseChangeMap h).comp e.symm.toRingHom).toAlgebra
  have hlocT : IsLocalization p.primeCompl (A.SStage j) := by
    -- Reinterpret the explicit localization-map witness as the corresponding typeclass instance.
    exact (isLocalization_iff_isLocalizationMap
      (M := p.primeCompl) (S := A.SStage j)).mpr hmap
  letI : Algebra (A.targetStageBaseChange h) (A.SStage j) := (A.stageBaseChangeMap h).toAlgebra
  have halg : ∀ z : A.targetStageBaseChange h,
      algebraMap (A.targetStageBaseChange h) (A.SStage j) z =
        algebraMap T (A.SStage j) (e z) := by
    intro z
    change A.stageBaseChangeMap h z = (A.stageBaseChangeMap h) (e.symm (e z))
    rw [RingEquiv.symm_apply_apply]
  haveI hlocT' : IsLocalization p.primeCompl (A.SStage j) := hlocT
  have hloc :
      IsLocalization q.primeCompl (A.SStage j) := by
    -- Transport the localization structure across the source ring equivalence `e`, field by
    -- field.
    refine ⟨fun y ↦ ?_, fun z ↦ ?_, fun {x y} hxy ↦ ?_⟩
    · rw [halg]
      have hey : e (y : A.targetStageBaseChange h) ∈ p.primeCompl := fun hmem ↦
        y.2 (Ideal.mem_comap.mpr hmem)
      exact IsLocalization.map_units (M := p.primeCompl) (A.SStage j) ⟨_, hey⟩
    · obtain ⟨⟨x, s⟩, hx⟩ := IsLocalization.surj (M := p.primeCompl) (S := A.SStage j) z
      refine ⟨⟨e.symm x, ⟨e.symm (s : T), fun hmem ↦ ?_⟩⟩, ?_⟩
      · have h1 : (s : T) ∈ p := by
          have h2 := Ideal.mem_comap.mp hmem
          rwa [show e.toRingHom (e.symm (s : T)) = (s : T) from e.apply_symm_apply (s : T)] at h2
        exact s.2 h1
      · rw [halg, halg, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
        exact hx
    · rw [halg, halg] at hxy
      obtain ⟨c, hc⟩ :=
        IsLocalization.exists_of_eq (M := p.primeCompl) (S := A.SStage j) hxy
      refine ⟨⟨e.symm (c : T), fun hmem ↦ ?_⟩, ?_⟩
      · have h1 : (c : T) ∈ p := by
          have h2 := Ideal.mem_comap.mp hmem
          rwa [show e.toRingHom (e.symm (c : T)) = (c : T) from e.apply_symm_apply (c : T)] at h2
        exact c.2 h1
      · have h3 := congrArg e.symm hc
        simpa [map_mul, RingEquiv.symm_apply_apply] using h3
  exact ⟨q, hq_prime,
    (isLocalization_iff_isLocalizationMap
      (M := q.primeCompl) (S := A.SStage j)).mp hloc⟩

-- Proof sketch: choose an essentially finitely presented local presentation of `S` over `R`,
-- write `R` as a directed colimit of local rings essentially of finite type over `ℤ`, descend the
-- finitely many generators and relations of the presentation to a sufficiently large stage, and
-- localize at the inverse images of the chosen prime.
/-- Helper for Lemma 10.127.11: localizing the left factor of a base change at a prime presents
the localized tensor product as a localization of the raw tensor product. -/
theorem tensorLocalization_of_atPrime
    {Λ : Type u} [Preorder Λ]
    (RStage : Λ → Type u) [∀ i, CommRing (RStage i)]
    (map : ∀ i j, i ≤ j → RStage i →+* RStage j)
    (P₀ : Type u) [CommRing P₀] {i₀ j k : Λ} (hij : i₀ ≤ j) (hjk : j ≤ k)
    [Algebra (RStage i₀) P₀]
    (q : Ideal (letI : Algebra (RStage i₀) (RStage j) := (map i₀ j hij).toAlgebra
      P₀ ⊗[RStage i₀] RStage j)) (hq : q.IsPrime) :
    let _ : Algebra (RStage i₀) (RStage j) := (map i₀ j hij).toAlgebra
    let _ : Algebra (RStage j) (RStage k) := (map j k hjk).toAlgebra
    let _ : q.IsPrime := hq
    let _ : Algebra ((P₀ ⊗[RStage i₀] RStage j) ⊗[RStage j] RStage k)
        (Localization.AtPrime q ⊗[RStage j] RStage k) :=
      (Algebra.TensorProduct.map
        (Algebra.ofId (P₀ ⊗[RStage i₀] RStage j) (Localization.AtPrime q))
        (AlgHom.id (RStage j) (RStage k))).toAlgebra
    let _ : Module ((P₀ ⊗[RStage i₀] RStage j) ⊗[RStage j] RStage k)
        (Localization.AtPrime q ⊗[RStage j] RStage k) := Algebra.toModule
    IsLocalization
      (Algebra.algebraMapSubmonoid ((P₀ ⊗[RStage i₀] RStage j) ⊗[RStage j] RStage k)
        q.primeCompl)
      (Localization.AtPrime q ⊗[RStage j] RStage k) := by
  intro _ _ _ _ _
  exact (Algebra.isLocalization_iff_isPushout q.primeCompl _).mpr
    (Algebra.IsPushout.tensorProduct_tensorProduct (RStage j) (RStage k)
      (P₀ ⊗[RStage i₀] RStage j) (Localization.AtPrime q)
      (by ext x; simp [RingHom.algebraMap_toAlgebra])).symm

/-- If `T₁` is a localization of `T₀` at `M₀`, and the composite `g ∘ α` presents the local ring
`U` as the localization of `T₀` at a prime `qk'` containing no element of `M₀`, then `g` presents
`U` as a localization of `T₁` at a prime. -/
theorem isLocalizationMap_of_localization_tower
    {T₀ T₁ U : Type u} [CommRing T₀] [CommRing T₁] [CommRing U] [IsLocalRing U]
    (α : T₀ →+* T₁) (g : T₁ →+* U) (M₀ : Submonoid T₀)
    (qk' : Ideal T₀) (hqk'_prime : qk'.IsPrime)
    (hM₀ : M₀ ≤ qk'.primeCompl)
    (hT₁ : @IsLocalization T₀ _ M₀ T₁ _ α.toAlgebra)
    (hU : @IsLocalization.AtPrime T₀ _ U _ (g.comp α).toAlgebra qk' hqk'_prime) :
    ∃ q : Ideal T₁, ∃ _ : q.IsPrime, q.primeCompl.IsLocalizationMap g := by
  letI : Algebra T₀ T₁ := α.toAlgebra
  letI : Algebra T₀ U := (g.comp α).toAlgebra
  letI : Algebra T₁ U := g.toAlgebra
  haveI : IsScalarTower T₀ T₁ U := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsLocalization M₀ T₁ := hT₁
  haveI : IsLocalization qk'.primeCompl U := hU
  have hαmap : (algebraMap T₀ T₁) = α := RingHom.algebraMap_toAlgebra _
  have hgmap : (algebraMap T₁ U) = g := RingHom.algebraMap_toAlgebra _
  have hgα : (algebraMap T₀ U) = g.comp α := RingHom.algebraMap_toAlgebra _
  have hcomapT₀ : Ideal.comap (algebraMap T₀ U) (IsLocalRing.maximalIdeal U) = qk' :=
    IsLocalization.AtPrime.comap_maximalIdeal U qk'
  let q : Ideal T₁ := Ideal.comap g (IsLocalRing.maximalIdeal U)
  have hq_prime : q.IsPrime := Ideal.comap_isPrime g (IsLocalRing.maximalIdeal U)
  refine ⟨q, hq_prime, ?_⟩
  -- It suffices to provide the `IsLocalization` instance at `q.primeCompl`.
  suffices hloc : IsLocalization q.primeCompl U by
    have := (isLocalization_iff_isLocalizationMap q.primeCompl U).mp hloc
    rwa [hgmap] at this
  -- `U` is a localization of `T₁` at the image of `qk'.primeCompl`.
  have hlocSub : IsLocalization (Submonoid.map α qk'.primeCompl) U := by
    have h := IsLocalization.isLocalization_of_submonoid_le T₁ U M₀ qk'.primeCompl hM₀
    rwa [hαmap] at h
  -- Upgrade the localization to all of `q.primeCompl`.
  refine IsLocalization.isLocalization_of_is_exists_mul_mem U
    (Submonoid.map α qk'.primeCompl) q.primeCompl ?_ ?_
  · -- The image of `qk'.primeCompl` lands in `q.primeCompl`.
    rintro x ⟨y, hy, rfl⟩
    have hy' : (y : T₀) ∉ qk' := hy
    change α y ∉ q
    intro hmem
    apply hy'
    rw [← hcomapT₀, Ideal.mem_comap, hgα, RingHom.comp_apply]
    exact hmem
  · -- Every element of `q.primeCompl` is reachable up to an `M₀`-denominator.
    rintro ⟨x, hx⟩
    have hx' : x ∉ q := hx
    obtain ⟨⟨a, s⟩, he⟩ := IsLocalization.surj M₀ x
    rw [hαmap] at he
    -- `g x` is a unit because `x ∉ q`.
    have hxunit : IsUnit (g x) :=
      IsLocalRing.notMem_maximalIdeal.mp (fun hc => hx' hc)
    -- `g (α s)` is a unit because `s ∉ qk'`.
    have hsunit : IsUnit (g (α (s : T₀))) := by
      refine IsLocalRing.notMem_maximalIdeal.mp (fun hc => ?_)
      have hsmem : (s : T₀) ∉ qk' := hM₀ s.2
      apply hsmem
      rw [← hcomapT₀, Ideal.mem_comap, hgα, RingHom.comp_apply]
      exact hc
    refine ⟨α (s : T₀), a, ?_, ?_⟩
    · -- `a ∉ qk'`, since `g (α a) = g x * g (α s)` is a unit.
      change (a : T₀) ∉ qk'
      intro hmem
      have haunit : IsUnit (g (α a)) := by
        have heq : g (α a) = g x * g (α (s : T₀)) := by
          rw [← map_mul]; exact congrArg g he.symm
        rw [heq]; exact hxunit.mul hsunit
      have hain : (algebraMap T₀ U) a ∈ IsLocalRing.maximalIdeal U := by
        rw [← hcomapT₀, Ideal.mem_comap] at hmem; exact hmem
      rw [hgα, RingHom.comp_apply] at hain
      exact (IsLocalRing.notMem_maximalIdeal.mpr haunit) hain
    · -- `α s * x = α a`.
      rw [mul_comm]; exact he.symm

/-- Helper for Lemma 10.127.11: the iterated base change of a descended algebra along the
directed system collapses to a single base change. -/
noncomputable def rawTensorCancel
    {Λ : Type u} [Preorder Λ]
    (RStage : Λ → Type u) [∀ i, CommRing (RStage i)]
    (map : ∀ i j, i ≤ j → RStage i →+* RStage j)
    (P₀ : Type u) [CommRing P₀] {i₀ j k : Λ} (hij : i₀ ≤ j) (hik : i₀ ≤ k) (hjk : j ≤ k)
    [Algebra (RStage i₀) P₀]
    (hcomp : (map j k hjk).comp (map i₀ j hij) = map i₀ k hik) :
    letI : Algebra (RStage i₀) (RStage j) := (map i₀ j hij).toAlgebra
    letI : Algebra (RStage i₀) (RStage k) := (map i₀ k hik).toAlgebra
    letI : Algebra (RStage j) (RStage k) := (map j k hjk).toAlgebra
    (P₀ ⊗[RStage i₀] RStage j) ⊗[RStage j] RStage k ≃+* P₀ ⊗[RStage i₀] RStage k :=
  letI : Algebra (RStage i₀) (RStage j) := (map i₀ j hij).toAlgebra
  letI : Algebra (RStage i₀) (RStage k) := (map i₀ k hik).toAlgebra
  letI : Algebra (RStage j) (RStage k) := (map j k hjk).toAlgebra
  letI : IsScalarTower (RStage i₀) (RStage j) (RStage k) :=
    IsScalarTower.of_algebraMap_eq' hcomp.symm
  -- Proof comment: commute the outer factors, commute the inner factors, cancel the middle base
  -- change, and commute back.
  ((Algebra.TensorProduct.comm (RStage j) (P₀ ⊗[RStage i₀] RStage j) (RStage k)).toRingEquiv).trans
    (((Algebra.TensorProduct.congr (AlgEquiv.refl (R := RStage j) (A₁ := RStage k))
      (AlgEquiv.ofRingEquiv
        (f := (Algebra.TensorProduct.comm (RStage i₀) P₀ (RStage j)).toRingEquiv)
        (fun x ↦ by
          change (Algebra.TensorProduct.comm (RStage i₀) P₀ (RStage j))
              ((1 : P₀) ⊗ₜ[RStage i₀] x) = x ⊗ₜ[RStage i₀] (1 : P₀)
          rw [Algebra.TensorProduct.comm_tmul]))).toRingEquiv).trans
      (((Algebra.TensorProduct.cancelBaseChange (RStage i₀) (RStage j) (RStage j) (RStage k)
        P₀).toRingEquiv).trans
        ((Algebra.TensorProduct.comm (RStage i₀) (RStage k) P₀).toRingEquiv)))

/-- Helper for Lemma 10.127.11: the collapse of the iterated base change sends a pure tensor to
the expected single base-change tensor. -/
theorem rawTensorCancel_tmul
    {Λ : Type u} [Preorder Λ]
    (RStage : Λ → Type u) [∀ i, CommRing (RStage i)]
    (map : ∀ i j, i ≤ j → RStage i →+* RStage j)
    (P₀ : Type u) [CommRing P₀] {i₀ j k : Λ} (hij : i₀ ≤ j) (hik : i₀ ≤ k) (hjk : j ≤ k)
    [Algebra (RStage i₀) P₀]
    (hcomp : (map j k hjk).comp (map i₀ j hij) = map i₀ k hik) :
    letI : Algebra (RStage i₀) (RStage j) := (map i₀ j hij).toAlgebra
    letI : Algebra (RStage i₀) (RStage k) := (map i₀ k hik).toAlgebra
    letI : Algebra (RStage j) (RStage k) := (map j k hjk).toAlgebra
    ∀ (p : P₀) (r : RStage j) (r' : RStage k),
      rawTensorCancel RStage map P₀ hij hik hjk hcomp
          ((p ⊗ₜ[RStage i₀] r) ⊗ₜ[RStage j] r') =
        p ⊗ₜ[RStage i₀] (map j k hjk r * r') := by
  intro p r r'
  -- Proof comment: chase the pure tensor through the four equivalences of the collapse.
  simp [rawTensorCancel, Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.congr,
    Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.cancelBaseChange_tmul,
    Algebra.smul_def, RingHom.algebraMap_toAlgebra]

/-- Helper for Lemma 10.127.11: the raw tensor cancellation sends an arbitrary left tensor
factor tensored with a later-stage element to the transitioned left factor multiplied by the
right-factor generator. -/
theorem rawTensorCancel_tmul_right
    {Λ : Type u} [Preorder Λ]
    (RStage : Λ → Type u) [∀ i, CommRing (RStage i)]
    (map : ∀ i j, i ≤ j → RStage i →+* RStage j)
    (P₀ : Type u) [CommRing P₀] {i₀ j k : Λ} (hij : i₀ ≤ j) (hik : i₀ ≤ k)
    (hjk : j ≤ k) [Algebra (RStage i₀) P₀]
    (hcomp : (map j k hjk).comp (map i₀ j hij) = map i₀ k hik) :
    letI : Algebra (RStage i₀) (RStage j) := (map i₀ j hij).toAlgebra
    letI : Algebra (RStage i₀) (RStage k) := (map i₀ k hik).toAlgebra
    letI : Algebra (RStage j) (RStage k) := (map j k hjk).toAlgebra
    ∀ (x : P₀ ⊗[RStage i₀] RStage j) (r' : RStage k),
      rawTensorCancel RStage map P₀ hij hik hjk hcomp (x ⊗ₜ[RStage j] r') =
        (Algebra.TensorProduct.map (AlgHom.id P₀ P₀)
          { toRingHom := map j k hjk
            commutes' := fun r ↦ by
              change (map j k hjk) ((map i₀ j hij) r) = (map i₀ k hik) r
              exact congrArg (fun g : RStage i₀ →+* RStage k => g r) hcomp } :
          P₀ ⊗[RStage i₀] RStage j →ₐ[P₀] P₀ ⊗[RStage i₀] RStage k) x *
          ((1 : P₀) ⊗ₜ[RStage i₀] r') := by
  letI : Algebra (RStage i₀) (RStage j) := (map i₀ j hij).toAlgebra
  letI : Algebra (RStage i₀) (RStage k) := (map i₀ k hik).toAlgebra
  letI : Algebra (RStage j) (RStage k) := (map j k hjk).toAlgebra
  intro x r'
  -- Proof comment: reduce the arbitrary left factor to pure tensors, where the defining
  -- computation `rawTensorCancel_tmul` applies directly.
  induction x using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul p r =>
      rw [rawTensorCancel_tmul]
      simp [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy =>
      calc
        rawTensorCancel RStage map P₀ hij hik hjk hcomp ((x + y) ⊗ₜ[RStage j] r') =
            rawTensorCancel RStage map P₀ hij hik hjk hcomp (x ⊗ₜ[RStage j] r') +
              rawTensorCancel RStage map P₀ hij hik hjk hcomp (y ⊗ₜ[RStage j] r') := by
              rw [TensorProduct.add_tmul, map_add]
        _ = (Algebra.TensorProduct.map (AlgHom.id P₀ P₀)
                { toRingHom := map j k hjk
                  commutes' := fun r ↦ by
                    change (map j k hjk) ((map i₀ j hij) r) = (map i₀ k hik) r
                    exact congrArg (fun g : RStage i₀ →+* RStage k => g r) hcomp } :
                P₀ ⊗[RStage i₀] RStage j →ₐ[P₀] P₀ ⊗[RStage i₀] RStage k) x *
                ((1 : P₀) ⊗ₜ[RStage i₀] r') +
              (Algebra.TensorProduct.map (AlgHom.id P₀ P₀)
                { toRingHom := map j k hjk
                  commutes' := fun r ↦ by
                    change (map j k hjk) ((map i₀ j hij) r) = (map i₀ k hik) r
                    exact congrArg (fun g : RStage i₀ →+* RStage k => g r) hcomp } :
                P₀ ⊗[RStage i₀] RStage j →ₐ[P₀] P₀ ⊗[RStage i₀] RStage k) y *
                ((1 : P₀) ⊗ₜ[RStage i₀] r') := by
              rw [hx, hy]
        _ = (Algebra.TensorProduct.map (AlgHom.id P₀ P₀)
                { toRingHom := map j k hjk
                  commutes' := fun r ↦ by
                    change (map j k hjk) ((map i₀ j hij) r) = (map i₀ k hik) r
                    exact congrArg (fun g : RStage i₀ →+* RStage k => g r) hcomp } :
                P₀ ⊗[RStage i₀] RStage j →ₐ[P₀] P₀ ⊗[RStage i₀] RStage k) (x + y) *
                ((1 : P₀) ⊗ₜ[RStage i₀] r') := by
              rw [map_add, add_mul]

/-- Helper for Lemma 10.127.11: the raw tensor cancellation restricts to the raw transition map
on the canonical copy of the earlier raw tensor stage. -/
theorem rawTensorCancel_algebraMap
    {Λ : Type u} [Preorder Λ]
    (RStage : Λ → Type u) [∀ i, CommRing (RStage i)]
    (map : ∀ i j, i ≤ j → RStage i →+* RStage j)
    (P₀ : Type u) [CommRing P₀] {i₀ j k : Λ} (hij : i₀ ≤ j) (hik : i₀ ≤ k)
    (hjk : j ≤ k) [Algebra (RStage i₀) P₀]
    (hcomp : (map j k hjk).comp (map i₀ j hij) = map i₀ k hik)
    (x : letI : Algebra (RStage i₀) (RStage j) := (map i₀ j hij).toAlgebra
      P₀ ⊗[RStage i₀] RStage j) :
    letI : Algebra (RStage i₀) (RStage j) := (map i₀ j hij).toAlgebra
    letI : Algebra (RStage i₀) (RStage k) := (map i₀ k hik).toAlgebra
    letI : Algebra (RStage j) (RStage k) := (map j k hjk).toAlgebra
    rawTensorCancel RStage map P₀ hij hik hjk hcomp
        (algebraMap (P₀ ⊗[RStage i₀] RStage j)
          ((P₀ ⊗[RStage i₀] RStage j) ⊗[RStage j] RStage k) x) =
      (Algebra.TensorProduct.map (AlgHom.id P₀ P₀)
        { toRingHom := map j k hjk
          commutes' := fun r ↦ by
            change (map j k hjk) ((map i₀ j hij) r) = (map i₀ k hik) r
            exact congrArg (fun g : RStage i₀ →+* RStage k => g r) hcomp } :
        P₀ ⊗[RStage i₀] RStage j →ₐ[P₀] P₀ ⊗[RStage i₀] RStage k) x := by
  letI : Algebra (RStage i₀) (RStage j) := (map i₀ j hij).toAlgebra
  letI : Algebra (RStage i₀) (RStage k) := (map i₀ k hik).toAlgebra
  letI : Algebra (RStage j) (RStage k) := (map j k hjk).toAlgebra
  -- Proof comment: specialize the right-tensor formula to the unit of the later source stage.
  rw [show algebraMap (P₀ ⊗[RStage i₀] RStage j)
      ((P₀ ⊗[RStage i₀] RStage j) ⊗[RStage j] RStage k) x =
        x ⊗ₜ[RStage j] (1 : RStage k) from rfl]
  rw [rawTensorCancel_tmul_right]
  rw [← Algebra.TensorProduct.one_def, mul_one]

/-- Helper for Lemma 10.127.11: a prime localization remains a prime localization after
precomposing the source ring with a ring equivalence. -/
theorem isLocalization_atPrime_of_ringEquiv_source
    {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
    (e : A ≃+* B) (q : Ideal B) [q.IsPrime]
    [Algebra B T] [IsLocalization.AtPrime T q] :
    let qA : Ideal A := Ideal.comap e.toRingHom q
    letI : qA.IsPrime := Ideal.comap_isPrime e.toRingHom q
    letI : Algebra A T := ((algebraMap B T).comp e.toRingHom).toAlgebra
    IsLocalization.AtPrime T qA := by
  let qA : Ideal A := Ideal.comap e.toRingHom q
  letI : qA.IsPrime := Ideal.comap_isPrime e.toRingHom q
  letI : Algebra A T := ((algebraMap B T).comp e.toRingHom).toAlgebra
  change IsLocalization qA.primeCompl T
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · -- Units inverted for `q` remain units after pulling the prime back along the equivalence.
    intro y
    change IsUnit (algebraMap B T (e (y : A)))
    exact IsLocalization.map_units T
      (⟨e (y : A), fun hmem ↦ y.2 (Ideal.mem_comap.mpr hmem)⟩ : q.primeCompl)
  · -- A fraction over `B` is rewritten as the corresponding fraction over `A` using `e.symm`.
    intro z
    obtain ⟨⟨b, s⟩, hz⟩ := IsLocalization.surj q.primeCompl z
    refine ⟨⟨e.symm b, ⟨e.symm (s : B), ?_⟩⟩, ?_⟩
    · intro hmem
      exact s.2 <| by
        have hs := Ideal.mem_comap.mp hmem
        simpa using hs
    · simpa [RingHom.algebraMap_toAlgebra] using hz
  · -- Equality after localization over `A` is transported to `B`, cleared there, and transported
    -- back through the equivalence.
    intro x y hxy
    have hxyB : algebraMap B T (e x) = algebraMap B T (e y) := by
      simpa [RingHom.algebraMap_toAlgebra] using hxy
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists q.primeCompl T).mp hxyB
    refine ⟨⟨e.symm (c : B), ?_⟩, ?_⟩
    · intro hmem
      exact c.2 <| by
        have hcq := Ideal.mem_comap.mp hmem
        simpa using hcq
    · exact e.injective <| by
        simpa using hc

/-- Helper for Lemma 10.127.11: a prime localization remains a prime localization after
precomposing the source ring with a ring equivalence and replacing the algebra map by an equal
ring homomorphism. -/
theorem isLocalization_atPrime_of_ringEquiv_source_map
    {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
    (e : A ≃+* B) (q : Ideal B) [q.IsPrime]
    [Algebra B T] [IsLocalization.AtPrime T q]
    (φ : A →+* T) (hφ : φ = (algebraMap B T).comp e.toRingHom) :
    let qA : Ideal A := Ideal.comap e.toRingHom q
    letI : qA.IsPrime := Ideal.comap_isPrime e.toRingHom q
    letI : Algebra A T := φ.toAlgebra
    IsLocalization.AtPrime T qA := by
  cases hφ
  exact isLocalization_atPrime_of_ringEquiv_source e q

/-- L1: assemble a ring map out of a base-change algebra `P ≅ P₀ ⊗ R` from compatible factor maps. -/
noncomputable def descentPsi
    {R₀ P₀ R' P' C : Type u} [CommRing R₀] [CommRing P₀] [CommRing R'] [CommRing P'] [CommRing C]
    [Algebra R₀ P₀] [Algebra R₀ R'] [Algebra R₀ C] [Algebra R' P']
    (e : P₀ ⊗[R₀] R' ≃ₐ[R'] P') (fP₀ : P₀ →ₐ[R₀] C) (fR : R' →ₐ[R₀] C) : P' →+* C :=
  (Algebra.TensorProduct.productMap fP₀ fR).toRingHom.comp e.symm.toRingHom

theorem descentPsi_apply
    {R₀ P₀ R' P' C : Type u} [CommRing R₀] [CommRing P₀] [CommRing R'] [CommRing P'] [CommRing C]
    [Algebra R₀ P₀] [Algebra R₀ R'] [Algebra R₀ C] [Algebra R' P']
    (e : P₀ ⊗[R₀] R' ≃ₐ[R'] P') (fP₀ : P₀ →ₐ[R₀] C) (fR : R' →ₐ[R₀] C) (p : P₀) (r : R') :
    descentPsi e fP₀ fR (e (p ⊗ₜ[R₀] r)) = fP₀ p * fR r := by
  change (Algebra.TensorProduct.productMap fP₀ fR) (e.symm (e (p ⊗ₜ[R₀] r))) = fP₀ p * fR r
  rw [e.symm_apply_apply, Algebra.TensorProduct.productMap_apply_tmul]

/-- L3: the forward comparison `F` undoes `descentPsi`, given how it acts on the two factors. -/
theorem descentPsi_comp_eq
    {R₀ P₀ R' P' C T : Type u} [CommRing R₀] [CommRing P₀] [CommRing R'] [CommRing P'] [CommRing C]
    [CommRing T] [Algebra R₀ P₀] [Algebra R₀ R'] [Algebra R₀ C] [Algebra R' P'] [Algebra P' T]
    (e : P₀ ⊗[R₀] R' ≃ₐ[R'] P') (fP₀ : P₀ →ₐ[R₀] C) (fR : R' →ₐ[R₀] C) (F : C →+* T)
    (hp0 : ∀ p, F (fP₀ p) = algebraMap P' T (e (p ⊗ₜ[R₀] 1)))
    (hsrc : ∀ r, F (fR r) = algebraMap P' T (e ((1 : P₀) ⊗ₜ[R₀] r))) :
    F.comp (descentPsi e fP₀ fR) = algebraMap P' T := by
  have key : ∀ x : P₀ ⊗[R₀] R',
      F (descentPsi e fP₀ fR (e x)) = algebraMap P' T (e x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul p r =>
      rw [descentPsi_apply, map_mul, hp0, hsrc, ← map_mul, ← map_mul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    | add a b ha hb => simp only [map_add, ha, hb]
  refine RingHom.ext fun p ↦ ?_
  obtain ⟨x, rfl⟩ := e.surjective p
  exact key x

/-- L4: `descentPsi` sends the base-change image of a raw stage element to its localized image. -/
theorem descentPsi_factB
    {R₀ P₀ R' P' C Rj : Type u} [CommRing R₀] [CommRing P₀] [CommRing R'] [CommRing P'] [CommRing C]
    [CommRing Rj] [Algebra R₀ P₀] [Algebra R₀ R'] [Algebra R₀ C] [Algebra R' P'] [Algebra R₀ Rj]
    (e : P₀ ⊗[R₀] R' ≃ₐ[R'] P') (fP₀ : P₀ →ₐ[R₀] C) (fR : R' →ₐ[R₀] C)
    (mapRj : Rj →+* R') (toStage : (P₀ ⊗[R₀] Rj) →+* C) (baseCh : (P₀ ⊗[R₀] Rj) →+* P')
    (hbaseCh : ∀ p w, baseCh (p ⊗ₜ[R₀] w) = e (p ⊗ₜ[R₀] mapRj w))
    (hp0Stage : ∀ p, toStage (p ⊗ₜ[R₀] 1) = fP₀ p)
    (hsrcStage : ∀ w, toStage ((1 : P₀) ⊗ₜ[R₀] w) = fR (mapRj w))
    (x : P₀ ⊗[R₀] Rj) :
    descentPsi e fP₀ fR (baseCh x) = toStage x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p w =>
    have hts : toStage (p ⊗ₜ[R₀] w) = fP₀ p * fR (mapRj w) := by
      rw [show (p ⊗ₜ[R₀] w : P₀ ⊗[R₀] Rj) = (p ⊗ₜ[R₀] 1) * ((1 : P₀) ⊗ₜ[R₀] w) from by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul],
        map_mul, hp0Stage, hsrcStage]
    rw [hbaseCh, descentPsi_apply, hts]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- L2: the canonical comparison from the colimit of localized stages reflects units. -/
theorem tailTargetColimit_isLocalHom
    {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    (G : Λ → Type u) [∀ i, CommRing (G i)]
    (map : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ map i j h)]
    (σ : (i : Λ) → G i →+* S)
    (hσ : ∀ i j (hij : i ≤ j), σ i = (σ j).comp (map i j hij)) :
    IsLocalHom (tail_target_colimit_to_ambient (S := S) G map σ hσ) := by
  let q : (i : Λ) → Ideal (G i) := fun i ↦ Ideal.comap (σ i) (IsLocalRing.maximalIdeal S)
  let ρ : ∀ i j, i ≤ j → Localization.AtPrime (q i) →+* Localization.AtPrime (q j) :=
    fun i j hij ↦
      Localization.localRingHom (q i) (q j) (map i j hij)
        ((comap_contracted_maximalIdeal_eq_of_comp
          (S := S) (τ := map i j hij) (σA := σ i) (σB := σ j) (hσ i j hij)).symm)
  let φ : (i : Λ) → Localization.AtPrime (q i) →+* S :=
    fun i ↦ (maxLocalizationCollapse S :
        Localization.AtPrime (IsLocalRing.maximalIdeal S) →+* S).comp
      (Localization.localRingHom (q i) (IsLocalRing.maximalIdeal S) (σ i) rfl)
  haveI hDS : DirectedSystem (fun i ↦ Localization.AtPrime (q i)) (fun i j h ↦ ρ i j h) :=
    localized_contracted_maximalIdeal_directedSystem (S := S) G map σ hσ
  haveI : ∀ i j h, IsLocalHom (ρ i j h) := fun i j h ↦ Localization.isLocalHom_localRingHom _ _ _ _
  haveI hcollapse : IsLocalHom
      (maxLocalizationCollapse S : Localization.AtPrime (IsLocalRing.maximalIdeal S) →+* S) :=
    Function.Surjective.isLocalHom _ (maxLocalizationCollapse S).surjective
  haveI : ∀ i, IsLocalHom (φ i) := fun i ↦ by
    haveI : IsLocalHom (Localization.localRingHom (q i) (IsLocalRing.maximalIdeal S) (σ i) rfl) :=
      Localization.isLocalHom_localRingHom _ _ _ _
    exact RingHom.isLocalHom_comp _ _
  have hφcompat : ∀ i j (hij : i ≤ j), φ i = (φ j).comp (ρ i j hij) :=
    localized_stage_maps_to_ambient_compatible (S := S) G map σ hσ
  exact Ring.DirectLimit.lift_isLocalHom (fun i ↦ Localization.AtPrime (q i)) ρ φ hφcompat

/-- L5: assemble the colimit/ambient ring equivalence from an inverse comparison `ψ`. -/
theorem tailTargetColimitEquiv
    {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    (G : Λ → Type u) [∀ i, CommRing (G i)]
    (map : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ map i j h)]
    (σ : (i : Λ) → G i →+* S)
    (hσ : ∀ i j (hij : i ≤ j), σ i = (σ j).comp (map i j hij))
    {P : Type u} [CommRing P] [Algebra P S]
    (q : Ideal P) [q.IsPrime] [IsLocalization q.primeCompl S]
    (pComp : (i : Λ) → G i →+* P)
    (hpComp : ∀ i, (algebraMap P S).comp (pComp i) = σ i)
    (ψ : P →+* Ring.DirectLimit
        (fun i ↦ Localization.AtPrime (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S)))
        (fun i j h ↦ Localization.localRingHom _ _ (map i j h)
          ((comap_contracted_maximalIdeal_eq_of_comp
            (S := S) (τ := map i j h) (σA := σ i) (σB := σ j) (hσ i j h)).symm)))
    (hψ : (tail_target_colimit_to_ambient (S := S) G map σ hσ).comp ψ = algebraMap P S)
    (hfactB : ∀ (i : Λ) (w : G i),
        ψ (pComp i w) = Ring.DirectLimit.of
          (fun i ↦ Localization.AtPrime (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S)))
          (fun i j h ↦ Localization.localRingHom _ _ (map i j h)
            ((comap_contracted_maximalIdeal_eq_of_comp
              (S := S) (τ := map i j h) (σA := σ i) (σB := σ j) (hσ i j h)).symm))
          i (algebraMap (G i)
              (Localization.AtPrime (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S))) w)) :
    ∃ eTail : Ring.DirectLimit
        (fun i ↦ Localization.AtPrime (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S)))
        (fun i j h ↦ Localization.localRingHom _ _ (map i j h)
          ((comap_contracted_maximalIdeal_eq_of_comp
            (S := S) (τ := map i j h) (σA := σ i) (σB := σ j) (hσ i j h)).symm)) ≃+* S,
      eTail.toRingHom = tail_target_colimit_to_ambient (S := S) G map σ hσ := by
  haveI hDS := localized_contracted_maximalIdeal_directedSystem (S := S) G map σ hσ
  have hlocal : IsLocalHom (tail_target_colimit_to_ambient (S := S) G map σ hσ) :=
    tailTargetColimit_isLocalHom G map σ hσ
  have hunits : ∀ y : q.primeCompl, IsUnit (ψ (y : P)) := by
    intro y
    apply hlocal.1
    rw [show (tail_target_colimit_to_ambient (S := S) G map σ hσ) (ψ (y : P))
        = algebraMap P S (y : P) from congrArg (fun h : P →+* S => h (y : P)) hψ]
    exact IsLocalization.map_units S y
  let invMap : S →+* Ring.DirectLimit
      (fun i ↦ Localization.AtPrime (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S)))
      (fun i j h ↦ Localization.localRingHom _ _ (map i j h)
        ((comap_contracted_maximalIdeal_eq_of_comp
          (S := S) (τ := map i j h) (σA := σ i) (σB := σ j) (hσ i j h)).symm)) :=
    IsLocalization.lift (M := q.primeCompl) hunits
  have hforward : (tail_target_colimit_to_ambient (S := S) G map σ hσ).comp invMap
      = RingHom.id S := by
    apply IsLocalization.ringHom_ext q.primeCompl
    refine RingHom.ext fun x ↦ ?_
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [show invMap (algebraMap P S x) = ψ x from IsLocalization.lift_eq hunits x]
    exact congrArg (fun h : P →+* S => h x) hψ
  have hbackward : invMap.comp (tail_target_colimit_to_ambient (S := S) G map σ hσ)
      = RingHom.id _ := by
    apply Ring.DirectLimit.hom_ext
    intro i
    apply IsLocalization.ringHom_ext
      (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S)).primeCompl
    refine RingHom.ext fun w ↦ ?_
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [tail_target_colimit_to_ambient_of (S := S) G map σ hσ, Localization.localRingHom_to_map]
    simp only [RingHom.coe_coe, maxLocalizationCollapse_algebraMap]
    rw [show σ i w = algebraMap P S (pComp i w) from
      (congrArg (fun h : G i →+* S => h w) (hpComp i)).symm]
    rw [IsLocalization.lift_eq hunits (pComp i w)]
    exact hfactB i w
  exact ⟨RingEquiv.ofRingHom (tail_target_colimit_to_ambient (S := S) G map σ hσ) invMap
    hforward hbackward, rfl⟩

/-- Helper for Lemma 10.127.11: two equal `R`-algebra structures on the left tensor factor give a
ring isomorphism of the resulting base-change rings. (Used to bridge the record's
`(stageMap).toAlgebra` view with the canonical localization algebra, which are equal as instances
but not definitionally so.) -/
def tensorRingEquivOfAlgEq {R Sj Rk : Type u}
    [CommRing R] [CommRing Sj] [CommRing Rk] [Algebra R Rk]
    (alg1 alg2 : Algebra R Sj) (halg : alg1 = alg2) :
    (letI := alg1; (Sj ⊗[R] Rk)) ≃+* (letI := alg2; (Sj ⊗[R] Rk)) := by
  subst halg
  exact RingEquiv.refl _

/-- The bridge of `tensorRingEquivOfAlgEq` is the identity on pure tensors. -/
theorem tensorRingEquivOfAlgEq_symm_tmul {R Sj Rk : Type u}
    [CommRing R] [CommRing Sj] [CommRing Rk] [Algebra R Rk]
    (alg1 alg2 : Algebra R Sj) (halg : alg1 = alg2) (x : Sj) (y : Rk) :
    (tensorRingEquivOfAlgEq alg1 alg2 halg).symm (letI := alg2; (x ⊗ₜ[R] y)) =
      (letI := alg1; (x ⊗ₜ[R] y)) := by
  subst halg; rfl

/-- The reverse bridge of `tensorRingEquivOfAlgEq` as a named ring hom. Keeping this bridge
outside the large transition proof avoids re-synthesizing the tensor-product semiring instances
from the expanded owner record. -/
noncomputable def tensorRingHomOfAlgEqSymm {R Sj Rk : Type u}
    [CommRing R] [CommRing Sj] [CommRing Rk] [Algebra R Rk]
    (alg1 alg2 : Algebra R Sj) (halg : alg1 = alg2) :
    (letI := alg2; Sj ⊗[R] Rk) →+* (letI := alg1; Sj ⊗[R] Rk) :=
  (tensorRingEquivOfAlgEq alg1 alg2 halg).symm.toRingHom

/-- The named reverse bridge is the identity on pure tensors after the algebra-instance
identification. -/
theorem tensorRingHomOfAlgEqSymm_tmul {R Sj Rk : Type u}
    [CommRing R] [CommRing Sj] [CommRing Rk] [Algebra R Rk]
    (alg1 alg2 : Algebra R Sj) (halg : alg1 = alg2) (x : Sj) (y : Rk) :
    tensorRingHomOfAlgEqSymm alg1 alg2 halg (letI := alg2; (x ⊗ₜ[R] y)) =
      (letI := alg1; (x ⊗ₜ[R] y)) := by
  subst halg; rfl

/-- The owner base-change map after the algebra-instance bridge has the expected pure-tensor
formula. This packages the expensive bridge normalization away from the large transition proof. -/
theorem stageBaseChangeMap_tensorBridge_tmul
    {R' S' : Type u} [CommRing R'] [CommRing S'] {f' : R' →+* S'}
    (A' : DirectedLocalHomApproximation.{u, u, u} f') {i j : A'.Λ} (h : i ≤ j)
    (algStage : Algebra (A'.RStage i) (A'.SStage i))
    (hinst : (A'.stageMap i).toAlgebra = algStage)
    (x : A'.SStage i) (y : A'.RStage j) :
    letI : Algebra (A'.RStage i) (A'.RStage j) := (A'.map i j h).toAlgebra
    ((A'.stageBaseChangeMap h).comp
        (tensorRingHomOfAlgEqSymm (R := A'.RStage i) (Sj := A'.SStage i)
          (Rk := A'.RStage j) ((A'.stageMap i).toAlgebra) algStage hinst))
      (letI : Algebra (A'.RStage i) (A'.SStage i) := algStage
       x ⊗ₜ[A'.RStage i] y) =
    A'.targetMap i j h x * A'.stageMap j y := by
  letI : Algebra (A'.RStage i) (A'.RStage j) := (A'.map i j h).toAlgebra
  dsimp [tensorRingHomOfAlgEqSymm]
  rw [tensorRingEquivOfAlgEq_symm_tmul]
  exact DirectedLocalHomApproximation.stageBaseChangeMap_tmul' A' h x y

/-- The tensor map induced by the structural map `A → C` on the left factor and the identity on
the right factor, named so transition proofs do not repeatedly synthesize the same map. -/
noncomputable def tensorMapOfIdId {R A B C : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra A C] [IsScalarTower R A C] :
    A ⊗[R] B →+* C ⊗[R] B :=
  (Algebra.TensorProduct.map (Algebra.ofId A C) (AlgHom.id R B)).toRingHom

/-- The named tensor map sends a pure tensor to the structural image on the left and the same
right factor. -/
theorem tensorMapOfIdId_tmul {R A B C : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra A C] [IsScalarTower R A C]
    (x : A) (y : B) :
    tensorMapOfIdId (R := R) (A := A) (B := B) (C := C) (x ⊗ₜ[R] y) =
      (algebraMap A C x) ⊗ₜ[R] y := by
  change (Algebra.TensorProduct.map (Algebra.ofId A C) (AlgHom.id R B)) (x ⊗ₜ[R] y) =
    (algebraMap A C x) ⊗ₜ[R] y
  rw [Algebra.TensorProduct.map_tmul]
  rfl

/-- Tensor on the left by an explicit algebra hom and on the right by the identity, named so
transition proofs do not repeatedly synthesize the same map. -/
noncomputable def tensorMapLeft {R A B C : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] (φ : A →ₐ[R] C) :
    A ⊗[R] B →+* C ⊗[R] B :=
  (Algebra.TensorProduct.map φ (AlgHom.id R B)).toRingHom

/-- The explicit left tensor map sends a pure tensor to the image on the left and the same right
factor. -/
theorem tensorMapLeft_tmul {R A B C : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] (φ : A →ₐ[R] C)
    (x : A) (y : B) :
    tensorMapLeft (R := R) (A := A) (B := B) (C := C) φ (x ⊗ₜ[R] y) = φ x ⊗ₜ[R] y := by
  change (Algebra.TensorProduct.map φ (AlgHom.id R B)) (x ⊗ₜ[R] y) = φ x ⊗ₜ[R] y
  rw [Algebra.TensorProduct.map_tmul]
  rfl

/-- The owner base-change map after both explicit tensor normalizations has the expected
pure-tensor formula. -/
theorem stageBaseChangeMap_tensorBridge_tensorMapLeft_tmul
    {R' S' T : Type u} [CommRing R'] [CommRing S'] [CommRing T] {f' : R' →+* S'}
    (A' : DirectedLocalHomApproximation.{u, u, u} f') {i j : A'.Λ} (h : i ≤ j)
    [Algebra (A'.RStage i) T]
    (algStage : Algebra (A'.RStage i) (A'.SStage i))
    (hinst : (A'.stageMap i).toAlgebra = algStage)
    (φ : T →ₐ[A'.RStage i] A'.SStage i) (x : T) (y : A'.RStage j) :
    letI : Algebra (A'.RStage i) (A'.RStage j) := (A'.map i j h).toAlgebra
    letI : Algebra (A'.RStage i) (A'.SStage i) := algStage
    ((A'.stageBaseChangeMap h).comp
        (tensorRingHomOfAlgEqSymm (R := A'.RStage i) (Sj := A'.SStage i)
          (Rk := A'.RStage j) ((A'.stageMap i).toAlgebra) algStage hinst))
      (tensorMapLeft (R := A'.RStage i) (A := T) (B := A'.RStage j)
        (C := A'.SStage i) φ (x ⊗ₜ[A'.RStage i] y)) =
    A'.targetMap i j h (φ x) * A'.stageMap j y := by
  letI : Algebra (A'.RStage i) (A'.RStage j) := (A'.map i j h).toAlgebra
  letI : Algebra (A'.RStage i) (A'.SStage i) := algStage
  rw [tensorMapLeft_tmul]
  exact stageBaseChangeMap_tensorBridge_tmul A' h algStage hinst (φ x) y

/-- Helper for Lemma 10.127.11: at the minimal tail stage, the base element embedded
through the left tensor factor agrees with the same base element in the right tensor factor. -/
theorem tensor_minimalStage_base_comm
    {R₀ P₀ Sj C : Type u} [CommRing R₀] [CommRing P₀] [CommRing Sj] [CommRing C]
    [Algebra R₀ P₀] [Algebra R₀ R₀] [Algebra (P₀ ⊗[R₀] R₀) Sj]
    (targetOf : Sj →+* C) (hself : ∀ r : R₀, algebraMap R₀ R₀ r = r) (r : R₀) :
    targetOf ((algebraMap (P₀ ⊗[R₀] R₀) Sj)
        ((algebraMap P₀ (P₀ ⊗[R₀] R₀)) (algebraMap R₀ P₀ r))) =
      targetOf ((algebraMap (P₀ ⊗[R₀] R₀) Sj) ((1 : P₀) ⊗ₜ[R₀] r)) := by
  congr 1
  congr 1
  calc (algebraMap P₀ (P₀ ⊗[R₀] R₀)) (algebraMap R₀ P₀ r)
      = (algebraMap R₀ P₀ r) ⊗ₜ[R₀] (1 : R₀) := rfl
    _ = (1 : P₀) ⊗ₜ[R₀] r := by
        rw [← Algebra.TensorProduct.algebraMap_apply r,
          Algebra.TensorProduct.algebraMap_apply' r, hself r]

/-- Helper for Lemma 10.127.11: a ring map `P₀ → B` compatible with a base map
`R₀ → B` gives an `R₀`-algebra map after postcomposition. -/
noncomputable def algHomOfCompBase
    {R₀ P₀ B C : Type u} [CommRing R₀] [CommRing P₀] [CommRing B] [CommRing C]
    [Algebra R₀ P₀] (target : B →+* C) (stage : R₀ →+* B) (pmap : P₀ →+* B)
    (hbase : ∀ r : R₀, pmap (algebraMap R₀ P₀ r) = stage r) :
    letI : Algebra R₀ C := (target.comp stage).toAlgebra
    P₀ →ₐ[R₀] C := by
  letI : Algebra R₀ C := (target.comp stage).toAlgebra
  exact
    { toRingHom := target.comp pmap
      commutes' := fun r ↦ by
        change target (pmap (algebraMap R₀ P₀ r)) = target (stage r)
        rw [hbase r] }

/-- Helper for Lemma 10.127.11: the canonical localized target stage attached to a raw
tail stage and its comparison map to `S`. -/
abbrev localizedTailStage
    {Λ : Type u}
    (G : Λ → Type u) [∀ i, CommRing (G i)]
    (σ : (i : Λ) → G i →+* S) (i : Λ) : Type u :=
  Localization.AtPrime (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S))

/-- Helper for Lemma 10.127.11: the canonical transition map between localized target tail
stages. -/
noncomputable abbrev localizedTailMap
    {Λ : Type u} [Preorder Λ]
    (G : Λ → Type u) [∀ i, CommRing (G i)]
    (map : ∀ i j, i ≤ j → G i →+* G j)
    (σ : (i : Λ) → G i →+* S)
    (hσ : ∀ i j (hij : i ≤ j), σ i = (σ j).comp (map i j hij))
    (i j : Λ) (hij : i ≤ j) : localizedTailStage (S := S) G σ i →+*
      localizedTailStage (S := S) G σ j :=
  Localization.localRingHom
    (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S))
    (Ideal.comap (σ j) (IsLocalRing.maximalIdeal S))
    (map i j hij)
    ((comap_contracted_maximalIdeal_eq_of_comp
      (S := S) (τ := map i j hij) (σA := σ i) (σB := σ j) (hσ i j hij)).symm)

/-- Helper for Lemma 10.127.11: the direct limit of the tail of localized stages. -/
abbrev localizedTailLimit
    {Λ : Type u} [Preorder Λ]
    (G : Λ → Type u) [∀ i, CommRing (G i)]
    (map : ∀ i j, i ≤ j → G i →+* G j)
    (σ : (i : Λ) → G i →+* S)
    (hσ : ∀ i j (hij : i ≤ j), σ i = (σ j).comp (map i j hij)) : Type u :=
  Ring.DirectLimit (localizedTailStage (S := S) G σ)
    (fun i j hij ↦ localizedTailMap (S := S) G map σ hσ i j hij)

/-- Helper for Lemma 10.127.11: the canonical inclusion of a localized tail stage into the
localized tail direct limit. -/
noncomputable abbrev localizedTailOf
    {Λ : Type u} [Preorder Λ]
    (G : Λ → Type u) [∀ i, CommRing (G i)]
    (map : ∀ i j, i ≤ j → G i →+* G j)
    (σ : (i : Λ) → G i →+* S)
    (hσ : ∀ i j (hij : i ≤ j), σ i = (σ j).comp (map i j hij))
    (i : Λ) : Localization.AtPrime (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S)) →+*
      localizedTailLimit (S := S) G map σ hσ :=
  Ring.DirectLimit.of (localizedTailStage (S := S) G σ)
    (fun i j hij ↦ localizedTailMap (S := S) G map σ hσ i j hij) i

/-- Helper for Lemma 10.127.11: assemble the localized tail colimit equivalence from the descended
presentation comparison data. -/
theorem localizedTailColimitData_of_descended_comparisons
    {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    (G : Λ → Type u) [∀ i, CommRing (G i)]
    (map : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ map i j h)]
    (σ : (i : Λ) → G i →+* S)
    (hσ : ∀ i j (hij : i ≤ j), σ i = (σ j).comp (map i j hij))
    {R₀ P₀ P : Type u} [CommRing R₀] [CommRing P₀] [CommRing P]
    [Algebra R₀ P₀] [Algebra R₀ R] [Algebra R P] [Algebra P S]
    [Algebra R₀ (localizedTailLimit (S := S) G map σ hσ)]
    (e : P₀ ⊗[R₀] R ≃ₐ[R] P) (q : Ideal P) [q.IsPrime]
    (hlocq : q.primeCompl.IsLocalizationMap (algebraMap P S))
    (p0Alg : P₀ →ₐ[R₀] localizedTailLimit (S := S) G map σ hσ)
    (srcAlg : R →ₐ[R₀] localizedTailLimit (S := S) G map σ hσ)
    (pComp : (i : Λ) → G i →+* P)
    (hpComp : ∀ i, (algebraMap P S).comp (pComp i) = σ i)
    (hp0 : ∀ p,
      tail_target_colimit_to_ambient (S := S) G map σ hσ (p0Alg p) =
        algebraMap P S (e (p ⊗ₜ[R₀] (1 : R))))
    (hsrc : ∀ r,
      tail_target_colimit_to_ambient (S := S) G map σ hσ (srcAlg r) =
        algebraMap P S (e ((1 : P₀) ⊗ₜ[R₀] r)))
    (hfactB : ∀ i w,
      descentPsi e p0Alg srcAlg (pComp i w) =
        localizedTailOf (S := S) G map σ hσ i
          (algebraMap (G i)
            (Localization.AtPrime (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S))) w)) :
    ∃ eTail : localizedTailLimit (S := S) G map σ hσ ≃+* S,
      eTail.toRingHom = tail_target_colimit_to_ambient (S := S) G map σ hσ := by
  haveI : IsLocalization q.primeCompl S :=
    (isLocalization_iff_isLocalizationMap q.primeCompl S).mpr hlocq
  refine tailTargetColimitEquiv G map σ hσ q pComp hpComp
    (descentPsi e p0Alg srcAlg) ?_ ?_
  · exact descentPsi_comp_eq e p0Alg srcAlg
      (tail_target_colimit_to_ambient (S := S) G map σ hσ) hp0 hsrc
  · intro i w
    exact hfactB i w


/-- Helper for Lemma 10.127.11: the raw descended tensor stage over a tail index. -/
abbrev descendedTailRawStage
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R))
    (i₀ : A₀.Λ) (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    (j : Set.Ici i₀) : Type u :=
  letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
  P₀ ⊗[A₀.RStage i₀] A₀.RStage j.1

/-- Helper for Lemma 10.127.11: the raw tensor transition map on descended tail stages. -/
noncomputable abbrev descendedTailRawMap
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R))
    (i₀ : A₀.Λ) (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    (j k : Set.Ici i₀) (hjk : j ≤ k) :
    descendedTailRawStage A₀ i₀ P₀ j →+* descendedTailRawStage A₀ i₀ P₀ k :=
  letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
  letI : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.map i₀ k.1 k.2).toAlgebra
  (Algebra.TensorProduct.map (AlgHom.id P₀ P₀)
    { toRingHom := A₀.map j.1 k.1 hjk
      commutes' := fun x ↦
        DirectedSystem.map_map (f := fun i j h ↦ A₀.map i j h) j.2 hjk x } :
    _ →+* _)

/-- Helper for Lemma 10.127.11: the raw tensor cancellation formula specialized to the
canonical descended tail stages. Naming this specialization keeps later transition proofs from
expanding the iterated tensor-cancellation equivalence in a large owner-record context. -/
theorem descendedTailRawTensorCancel_tmul_right
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R))
    (i₀ : A₀.Λ) (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    (j k : Set.Ici i₀) (hjk : j ≤ k)
    (hcomp : (A₀.map j.1 k.1 hjk).comp (A₀.map i₀ j.1 j.2) = A₀.map i₀ k.1 k.2)
    (x : descendedTailRawStage A₀ i₀ P₀ j) (r' : A₀.RStage k.1) :
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
    letI : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.map i₀ k.1 k.2).toAlgebra
    letI : Algebra (A₀.RStage j.1) (A₀.RStage k.1) := (A₀.map j.1 k.1 hjk).toAlgebra
    rawTensorCancel A₀.RStage (fun a b h ↦ A₀.map a b h) P₀
        j.2 k.2 hjk hcomp (x ⊗ₜ[A₀.RStage j.1] r') =
      descendedTailRawMap A₀ i₀ P₀ j k hjk x *
        ((1 : P₀) ⊗ₜ[A₀.RStage i₀] r') := by
  letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
  letI : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.map i₀ k.1 k.2).toAlgebra
  letI : Algebra (A₀.RStage j.1) (A₀.RStage k.1) := (A₀.map j.1 k.1 hjk).toAlgebra
  exact rawTensorCancel_tmul_right (RStage := A₀.RStage)
    (map := fun a b h ↦ A₀.map a b h) (P₀ := P₀)
    (i₀ := i₀) (j := j.1) (k := k.1) j.2 k.2 hjk hcomp x r'

/-- Helper for Lemma 10.127.11: the raw tensor cancellation restricts to the canonical
transition map on the canonical copy of an earlier descended tail stage. -/
theorem descendedTailRawTensorCancel_algebraMap
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R))
    (i₀ : A₀.Λ) (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    (j k : Set.Ici i₀) (hjk : j ≤ k)
    (hcomp : (A₀.map j.1 k.1 hjk).comp (A₀.map i₀ j.1 j.2) = A₀.map i₀ k.1 k.2)
    (x : descendedTailRawStage A₀ i₀ P₀ j) :
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
    letI : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.map i₀ k.1 k.2).toAlgebra
    letI : Algebra (A₀.RStage j.1) (A₀.RStage k.1) := (A₀.map j.1 k.1 hjk).toAlgebra
    (rawTensorCancel A₀.RStage (fun a b h ↦ A₀.map a b h) P₀
        j.2 k.2 hjk hcomp).toRingHom
      (algebraMap (descendedTailRawStage A₀ i₀ P₀ j)
        ((descendedTailRawStage A₀ i₀ P₀ j) ⊗[A₀.RStage j.1] A₀.RStage k.1) x) =
      descendedTailRawMap A₀ i₀ P₀ j k hjk x := by
  letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
  letI : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.map i₀ k.1 k.2).toAlgebra
  letI : Algebra (A₀.RStage j.1) (A₀.RStage k.1) := (A₀.map j.1 k.1 hjk).toAlgebra
  exact rawTensorCancel_algebraMap (RStage := A₀.RStage)
    (map := fun a b h ↦ A₀.map a b h) (P₀ := P₀)
    (i₀ := i₀) (j := j.1) (k := k.1) j.2 k.2 hjk hcomp x

/-- Helper for Lemma 10.127.11: denominators from an earlier contracted prime remain
denominators after raw tensor cancellation to a later stage. This is the `M₀ ≤ qk'.primeCompl`
input for the localization tower. -/
theorem descendedTail_algebraMapSubmonoid_le_cancel_comap_primeCompl
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R))
    (i₀ : A₀.Λ) (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    (σ : (j : Set.Ici i₀) → descendedTailRawStage A₀ i₀ P₀ j →+* S)
    (j k : Set.Ici i₀) (hjk : j ≤ k)
    (hcomp : (A₀.map j.1 k.1 hjk).comp (A₀.map i₀ j.1 j.2) = A₀.map i₀ k.1 k.2)
    (hσ_comap : Ideal.comap (descendedTailRawMap A₀ i₀ P₀ j k hjk)
        (Ideal.comap (σ k) (IsLocalRing.maximalIdeal S)) =
      Ideal.comap (σ j) (IsLocalRing.maximalIdeal S)) :
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
    letI : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.map i₀ k.1 k.2).toAlgebra
    letI : Algebra (A₀.RStage j.1) (A₀.RStage k.1) := (A₀.map j.1 k.1 hjk).toAlgebra
    Algebra.algebraMapSubmonoid
        ((descendedTailRawStage A₀ i₀ P₀ j) ⊗[A₀.RStage j.1] A₀.RStage k.1)
        (Ideal.comap (σ j) (IsLocalRing.maximalIdeal S)).primeCompl ≤
      (Ideal.comap
        (rawTensorCancel A₀.RStage (fun a b h ↦ A₀.map a b h) P₀
          j.2 k.2 hjk hcomp).toRingHom
        (Ideal.comap (σ k) (IsLocalRing.maximalIdeal S))).primeCompl := by
  letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
  letI : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.map i₀ k.1 k.2).toAlgebra
  letI : Algebra (A₀.RStage j.1) (A₀.RStage k.1) := (A₀.map j.1 k.1 hjk).toAlgebra
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩
  intro hmem
  have hcancel :
      (rawTensorCancel A₀.RStage (fun a b h ↦ A₀.map a b h) P₀
          j.2 k.2 hjk hcomp).toRingHom
        (algebraMap (descendedTailRawStage A₀ i₀ P₀ j)
          ((descendedTailRawStage A₀ i₀ P₀ j) ⊗[A₀.RStage j.1] A₀.RStage k.1) x) =
        descendedTailRawMap A₀ i₀ P₀ j k hjk x := by
    exact descendedTailRawTensorCancel_algebraMap A₀ i₀ P₀ j k hjk hcomp x
  have hraw : descendedTailRawMap A₀ i₀ P₀ j k hjk x ∈
      Ideal.comap (σ k) (IsLocalRing.maximalIdeal S) := by
    have hmem' := Ideal.mem_comap.mp hmem
    rwa [hcancel] at hmem'
  have hxmem : x ∈ Ideal.comap (σ j) (IsLocalRing.maximalIdeal S) := by
    rw [← hσ_comap]
    exact Ideal.mem_comap.mpr hraw
  exact hx hxmem

/-- Helper for Lemma 10.127.11: the canonical source-to-limit scalar tower on a tail stage,
allowing the bottom algebra instance to be supplied as a theorem parameter. -/
theorem tail_toLimit_isScalarTower_of_base_eq
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R))
    (i₀ : A₀.Λ) [Algebra (A₀.RStage i₀) R]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (j : Set.Ici i₀) :
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
    letI : Algebra (A₀.RStage j.1) R :=
      (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h)
        A₀.colimitIso j.1).toAlgebra
    IsScalarTower (A₀.RStage i₀) (A₀.RStage j.1) R := by
  letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
  letI : Algebra (A₀.RStage j.1) R :=
    (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h)
      A₀.colimitIso j.1).toAlgebra
  exact IsScalarTower.of_algebraMap_eq' (by
    ext x
    change algebraMap (A₀.RStage i₀) R x =
      Ring.DirectLimit.toLimitHom A₀.RStage
        (fun i j h ↦ A₀.map i j h) A₀.colimitIso j.1 ((A₀.map i₀ j.1 j.2) x)
    rw [hRalg]
    simp [Ring.DirectLimit.toLimitHom, Ring.DirectLimit.of_f])

/-- Helper for Lemma 10.127.11: the comparison from a raw tail stage to the descended
presentation over the colimit source. -/
noncomputable abbrev descendedTailPComp
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R))
    {P : Type u} [CommRing P] [Algebra R P]
    (i₀ : A₀.Λ) (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra (A₀.RStage i₀) R]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (j : Set.Ici i₀) : descendedTailRawStage A₀ i₀ P₀ j →+* P :=
  letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
  letI : Algebra (A₀.RStage j.1) R :=
    (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h)
      A₀.colimitIso j.1).toAlgebra
  letI : IsScalarTower (A₀.RStage i₀) (A₀.RStage j.1) R :=
    tail_toLimit_isScalarTower_of_base_eq A₀ i₀ hRalg j
  e.toRingHom.comp
    (Algebra.TensorProduct.map (AlgHom.id P₀ P₀)
      (IsScalarTower.toAlgHom (A₀.RStage i₀) (A₀.RStage j.1) R) :
      _ →+* _)

/-- Helper for Lemma 10.127.11: the comparison from a raw tail stage to the final local target. -/
noncomputable abbrev descendedTailSigma
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R))
    {P : Type u} [CommRing P] [Algebra R P] [Algebra P S]
    (i₀ : A₀.Λ) (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra (A₀.RStage i₀) R]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (j : Set.Ici i₀) : descendedTailRawStage A₀ i₀ P₀ j →+* S :=
  (algebraMap P S).comp (descendedTailPComp A₀ i₀ P₀ hRalg e j)

/-- Helper for Lemma 10.127.11: the canonical localized target stage of the descended tail
system. -/
abbrev descendedTailSStage
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R))
    {P : Type u} [CommRing P] [Algebra R P] [Algebra P S]
    (i₀ : A₀.Λ) (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra (A₀.RStage i₀) R]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P) (j : Set.Ici i₀) : Type u :=
  localizedTailStage (S := S) (descendedTailRawStage A₀ i₀ P₀)
    (descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e) j

/-- Helper for Lemma 10.127.11: the canonical localized target transition of the descended tail
system. -/
noncomputable abbrev descendedTailTargetMap
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R))
    {P : Type u} [CommRing P] [Algebra R P] [Algebra P S]
    (i₀ : A₀.Λ) (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra (A₀.RStage i₀) R]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (hσ_raw_comp : ∀ (j k : Set.Ici i₀) (hjk : j ≤ k),
      descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e j =
        (descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e k).comp
          (descendedTailRawMap A₀ i₀ P₀ j k hjk))
    (j k : Set.Ici i₀) (hjk : j ≤ k) :
    descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j →+*
      descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e k :=
  localizedTailMap (S := S) (descendedTailRawStage A₀ i₀ P₀)
    (descendedTailRawMap A₀ i₀ P₀)
    (descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e) hσ_raw_comp j k hjk

/-- Helper for Lemma 10.127.11: the canonical localized target transition sends a raw-stage
generator to the localization of its raw tensor transition. -/
theorem descendedTailTargetMap_algebraMap
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R))
    {P : Type u} [CommRing P] [Algebra R P] [Algebra P S]
    (i₀ : A₀.Λ) (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra (A₀.RStage i₀) R]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (hσ_raw_comp : ∀ (j k : Set.Ici i₀) (hjk : j ≤ k),
      descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e j =
        (descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e k).comp
          (descendedTailRawMap A₀ i₀ P₀ j k hjk))
    (j k : Set.Ici i₀) (hjk : j ≤ k)
    (x : descendedTailRawStage A₀ i₀ P₀ j) :
    descendedTailTargetMap (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k hjk
        (algebraMap (descendedTailRawStage A₀ i₀ P₀ j)
          (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j) x) =
      algebraMap (descendedTailRawStage A₀ i₀ P₀ k)
        (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e k)
        (descendedTailRawMap A₀ i₀ P₀ j k hjk x) := by
  let qTail : (j : Set.Ici i₀) → Ideal (descendedTailRawStage A₀ i₀ P₀ j) := fun j ↦
    Ideal.comap (descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e j)
      (IsLocalRing.maximalIdeal S)
  change Localization.localRingHom (qTail j) (qTail k)
        (descendedTailRawMap A₀ i₀ P₀ j k hjk)
        ((comap_contracted_maximalIdeal_eq_of_comp
          (S := S) (τ := descendedTailRawMap A₀ i₀ P₀ j k hjk)
          (σA := descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e j)
          (σB := descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e k)
          (hσ_raw_comp j k hjk)).symm)
        (algebraMap (descendedTailRawStage A₀ i₀ P₀ j)
          (Localization.AtPrime (qTail j)) x) =
      algebraMap (descendedTailRawStage A₀ i₀ P₀ k)
        (Localization.AtPrime (qTail k)) (descendedTailRawMap A₀ i₀ P₀ j k hjk x)
  exact Localization.localRingHom_to_map (I := qTail j) (J := qTail k)
    (f := descendedTailRawMap A₀ i₀ P₀ j k hjk)
    ((comap_contracted_maximalIdeal_eq_of_comp
      (S := S) (τ := descendedTailRawMap A₀ i₀ P₀ j k hjk)
      (σA := descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e j)
      (σB := descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e k)
      (hσ_raw_comp j k hjk)).symm) x

/-- Helper for Lemma 10.127.11: after passing to localized tail target stages, the
localized transition on a raw generator multiplied by a source-stage generator agrees with the
raw tensor cancellation map followed by the later localization. This packages the generator
calculation used to compare the owner base-change map with the explicit localization tower. -/
theorem descendedTailTargetMap_stageMap_mul_eq_cancel
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R))
    {P : Type u} [CommRing P] [Algebra R P] [Algebra P S]
    (i₀ : A₀.Λ) (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra (A₀.RStage i₀) R]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (hσ_raw_comp : ∀ (j k : Set.Ici i₀) (hjk : j ≤ k),
      descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e j =
        (descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e k).comp
          (descendedTailRawMap A₀ i₀ P₀ j k hjk))
    (stageMapTail : (j : Set.Ici i₀) → A₀.RStage j.1 →+*
      descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j)
    (hstageMapTail_apply : ∀ (j : Set.Ici i₀) (x : A₀.RStage j.1),
      stageMapTail j x =
        algebraMap (descendedTailRawStage A₀ i₀ P₀ j)
          (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j)
          ((algebraMap (A₀.RStage j.1) (descendedTailRawStage A₀ i₀ P₀ j)) x))
    (j k : Set.Ici i₀) (hjk : j ≤ k)
    (hcomp : (A₀.map j.1 k.1 hjk).comp (A₀.map i₀ j.1 j.2) = A₀.map i₀ k.1 k.2)
    (x : descendedTailRawStage A₀ i₀ P₀ j) (r' : A₀.RStage k.1) :
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
    letI : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.map i₀ k.1 k.2).toAlgebra
    letI : Algebra (A₀.RStage j.1) (A₀.RStage k.1) := (A₀.map j.1 k.1 hjk).toAlgebra
    descendedTailTargetMap (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k hjk
        (algebraMap (descendedTailRawStage A₀ i₀ P₀ j)
          (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j) x) *
      stageMapTail k r' =
    algebraMap (descendedTailRawStage A₀ i₀ P₀ k)
      (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e k)
      (rawTensorCancel A₀.RStage (fun a b h ↦ A₀.map a b h) P₀
        j.2 k.2 hjk hcomp (x ⊗ₜ[A₀.RStage j.1] r')) := by
  letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
  letI : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.map i₀ k.1 k.2).toAlgebra
  letI : Algebra (A₀.RStage j.1) (A₀.RStage k.1) := (A₀.map j.1 k.1 hjk).toAlgebra
  calc
    descendedTailTargetMap (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k hjk
          (algebraMap (descendedTailRawStage A₀ i₀ P₀ j)
            (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j) x) *
        stageMapTail k r' =
      algebraMap (descendedTailRawStage A₀ i₀ P₀ k)
          (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e k)
          (descendedTailRawMap A₀ i₀ P₀ j k hjk x) *
        algebraMap (descendedTailRawStage A₀ i₀ P₀ k)
          (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e k)
          ((1 : P₀) ⊗ₜ[A₀.RStage i₀] r') := by
        rw [descendedTailTargetMap_algebraMap (S := S) A₀ i₀ P₀ hRalg e
          hσ_raw_comp j k hjk x]
        rw [hstageMapTail_apply k r']
        rfl
    _ = algebraMap (descendedTailRawStage A₀ i₀ P₀ k)
          (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e k)
          (descendedTailRawMap A₀ i₀ P₀ j k hjk x *
            ((1 : P₀) ⊗ₜ[A₀.RStage i₀] r')) := by
        rw [map_mul]
    _ = algebraMap (descendedTailRawStage A₀ i₀ P₀ k)
          (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e k)
          (rawTensorCancel A₀.RStage (fun a b h ↦ A₀.map a b h) P₀
            j.2 k.2 hjk hcomp (x ⊗ₜ[A₀.RStage j.1] r')) := by
        rw [descendedTailRawTensorCancel_tmul_right A₀ i₀ P₀ j k hjk hcomp x r']

/-- Helper for Lemma 10.127.11: the target direct limit attached to the descended localized tail. -/
abbrev descendedTailLimit
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R))
    {P : Type u} [CommRing P] [Algebra R P] [Algebra P S]
    (i₀ : A₀.Λ) (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra (A₀.RStage i₀) R]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (hσ_raw_comp : ∀ (j k : Set.Ici i₀) (hjk : j ≤ k),
      descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e j =
        (descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e k).comp
          (descendedTailRawMap A₀ i₀ P₀ j k hjk)) : Type u :=
  Ring.DirectLimit (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e)
    (fun j k h ↦ descendedTailTargetMap (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k h)

/-- Helper for Lemma 10.127.11: the canonical map from a descended localized tail stage to its
 target direct limit. -/
noncomputable abbrev descendedTailOf
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R))
    {P : Type u} [CommRing P] [Algebra R P] [Algebra P S]
    (i₀ : A₀.Λ) (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra (A₀.RStage i₀) R]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (hσ_raw_comp : ∀ (j k : Set.Ici i₀) (hjk : j ≤ k),
      descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e j =
        (descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e k).comp
          (descendedTailRawMap A₀ i₀ P₀ j k hjk))
    (j : Set.Ici i₀) : descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j →+*
      descendedTailLimit (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp :=
  Ring.DirectLimit.of (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e)
    (fun j k h ↦ descendedTailTargetMap (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k h) j

/-- Helper for Lemma 10.127.11: the inverse comparison built from the descended presentation sends
raw tail-stage elements to their localized direct-limit generators. -/
theorem descendedTail_descentPsi_factB
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R))
    {P : Type u} [CommRing P] [Algebra R P] [Algebra P S]
    (i₀ : A₀.Λ) (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra (A₀.RStage i₀) R]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (hσ_raw_comp : ∀ (j k : Set.Ici i₀) (hjk : j ≤ k),
      descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e j =
        (descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e k).comp
          (descendedTailRawMap A₀ i₀ P₀ j k hjk))
    [DirectedSystem (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e)
      (fun j k h ↦ descendedTailTargetMap (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k h)]
    [Algebra (A₀.RStage i₀) (descendedTailLimit (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp)]
    (stageMapTail : (j : Set.Ici i₀) → A₀.RStage j.1 →+*
      descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j)
    (hstageMapTail_apply : ∀ (j : Set.Ici i₀) (x : A₀.RStage j.1),
      stageMapTail j x =
        algebraMap (descendedTailRawStage A₀ i₀ P₀ j)
          (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j)
          ((algebraMap (A₀.RStage j.1) (descendedTailRawStage A₀ i₀ P₀ j)) x))
    (sourceToTargetDirectLimit : R →+*
      descendedTailLimit (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp)
    (hSourceStage : ∀ (i : Set.Ici i₀) (x : A₀.RStage i.1),
      sourceToTargetDirectLimit
        (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h)
          A₀.colimitIso i.1 x) =
      descendedTailOf (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp i (stageMapTail i x))
    (p0Alg : P₀ →ₐ[A₀.RStage i₀]
      descendedTailLimit (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp)
    (srcAlg : R →ₐ[A₀.RStage i₀]
      descendedTailLimit (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp)
    (hp0Alg : ∀ p : P₀,
      p0Alg p =
        descendedTailOf (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp ⟨i₀, le_rfl⟩
          (algebraMap (descendedTailRawStage A₀ i₀ P₀ ⟨i₀, le_rfl⟩)
            (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e ⟨i₀, le_rfl⟩)
            ((algebraMap P₀ (descendedTailRawStage A₀ i₀ P₀ ⟨i₀, le_rfl⟩)) p)))
    (hsrcAlg : ∀ r : R, srcAlg r = sourceToTargetDirectLimit r)
    (i : Set.Ici i₀) (w : descendedTailRawStage A₀ i₀ P₀ i) :
    descentPsi e p0Alg srcAlg (descendedTailPComp A₀ i₀ P₀ hRalg e i w) =
      descendedTailOf (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp i
        (algebraMap (descendedTailRawStage A₀ i₀ P₀ i)
          (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e i) w) := by
  let j0 : Set.Ici i₀ := ⟨i₀, le_rfl⟩
  letI : Algebra (A₀.RStage i₀) (A₀.RStage i.1) := (A₀.map i₀ i.1 i.2).toAlgebra
  letI : Algebra (A₀.RStage i.1) R :=
    (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h)
      A₀.colimitIso i.1).toAlgebra
  letI : IsScalarTower (A₀.RStage i₀) (A₀.RStage i.1) R :=
    tail_toLimit_isScalarTower_of_base_eq A₀ i₀ hRalg i
  refine descentPsi_factB e p0Alg srcAlg (algebraMap (A₀.RStage i.1) R)
    ((descendedTailOf (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp i).comp
      (algebraMap (descendedTailRawStage A₀ i₀ P₀ i)
        (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e i)))
    (descendedTailPComp A₀ i₀ P₀ hRalg e i) ?_ ?_ ?_ w
  · intro p ww
    change e.toRingHom (Algebra.TensorProduct.map (AlgHom.id P₀ P₀)
        (IsScalarTower.toAlgHom (A₀.RStage i₀) (A₀.RStage i.1) R)
        (p ⊗ₜ[A₀.RStage i₀] ww)) =
      e (p ⊗ₜ[A₀.RStage i₀] (algebraMap (A₀.RStage i.1) R) ww)
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  · intro p
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j0.1) := (A₀.map i₀ j0.1 j0.2).toAlgebra
    have hj0i : j0 ≤ i := i.2
    change descendedTailOf (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp i
        (algebraMap (descendedTailRawStage A₀ i₀ P₀ i)
          (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e i)
          (p ⊗ₜ[A₀.RStage i₀] (1 : A₀.RStage i.1))) = p0Alg p
    have key : descendedTailOf (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp i
          (descendedTailTargetMap (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j0 i hj0i
            (algebraMap (descendedTailRawStage A₀ i₀ P₀ j0)
              (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j0)
              ((algebraMap P₀ (descendedTailRawStage A₀ i₀ P₀ j0)) p))) =
        descendedTailOf (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j0
          (algebraMap (descendedTailRawStage A₀ i₀ P₀ j0)
            (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j0)
            ((algebraMap P₀ (descendedTailRawStage A₀ i₀ P₀ j0)) p)) := by
      exact Ring.DirectLimit.of_f hj0i
        (algebraMap (descendedTailRawStage A₀ i₀ P₀ j0)
          (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j0)
          ((algebraMap P₀ (descendedTailRawStage A₀ i₀ P₀ j0)) p))
    rw [hp0Alg p, ← key]
    apply congrArg (descendedTailOf (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp i)
    symm
    calc
      descendedTailTargetMap (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j0 i hj0i
          (algebraMap (descendedTailRawStage A₀ i₀ P₀ j0)
            (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j0)
            ((algebraMap P₀ (descendedTailRawStage A₀ i₀ P₀ j0)) p))
          = algebraMap (descendedTailRawStage A₀ i₀ P₀ i)
              (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e i)
              (descendedTailRawMap A₀ i₀ P₀ j0 i hj0i
                ((algebraMap P₀ (descendedTailRawStage A₀ i₀ P₀ j0)) p)) :=
            descendedTailTargetMap_algebraMap (S := S) A₀ i₀ P₀ hRalg e
              hσ_raw_comp j0 i hj0i ((algebraMap P₀ (descendedTailRawStage A₀ i₀ P₀ j0)) p)
      _ = algebraMap (descendedTailRawStage A₀ i₀ P₀ i)
              (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e i)
              (p ⊗ₜ[A₀.RStage i₀] (1 : A₀.RStage i.1)) := by
            congr 1
            dsimp [descendedTailRawMap]
            change (Algebra.TensorProduct.map (AlgHom.id P₀ P₀)
                { toRingHom := A₀.map j0.1 i.1 hj0i
                  commutes' := fun x ↦
                    DirectedSystem.map_map (f := fun i j h ↦ A₀.map i j h) j0.2 hj0i x } :
                _ →+* _) ((algebraMap P₀ (descendedTailRawStage A₀ i₀ P₀ j0)) p) =
              p ⊗ₜ[A₀.RStage i₀] (1 : A₀.RStage i.1)
            rw [show (algebraMap P₀ (descendedTailRawStage A₀ i₀ P₀ j0)) p =
                (p ⊗ₜ[A₀.RStage i₀] (1 : A₀.RStage j0.1) :
                  descendedTailRawStage A₀ i₀ P₀ j0) from rfl]
            simpa using
              (Algebra.TensorProduct.map_tmul (AlgHom.id P₀ P₀)
                { toRingHom := A₀.map j0.1 i.1 hj0i
                  commutes' := fun x ↦
                    DirectedSystem.map_map (f := fun i j h ↦ A₀.map i j h) j0.2 hj0i x }
                p (1 : A₀.RStage j0.1))
  · intro ww
    change descendedTailOf (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp i
        (algebraMap (descendedTailRawStage A₀ i₀ P₀ i)
          (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e i)
          ((1 : P₀) ⊗ₜ[A₀.RStage i₀] ww)) =
      srcAlg (algebraMap (A₀.RStage i.1) R ww)
    calc
      descendedTailOf (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp i
          (algebraMap (descendedTailRawStage A₀ i₀ P₀ i)
            (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e i)
            ((1 : P₀) ⊗ₜ[A₀.RStage i₀] ww))
          = descendedTailOf (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp i
              (stageMapTail i ww) := by
            rw [hstageMapTail_apply i ww]
            rfl
      _ = sourceToTargetDirectLimit
            (Ring.DirectLimit.toLimitHom A₀.RStage
              (fun i j h ↦ A₀.map i j h) A₀.colimitIso i.1 ww) := by
            exact (hSourceStage i ww).symm
      _ = sourceToTargetDirectLimit (algebraMap (A₀.RStage i.1) R ww) := rfl
      _ = srcAlg (algebraMap (A₀.RStage i.1) R ww) := by
            rw [hsrcAlg]

/-- Helper for Lemma 10.127.11: the canonical source-to-target direct-limit map induced by
stage maps on a tail. -/
noncomputable abbrev sourceToTargetDirectLimitOf
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (SStage : Set.Ici i₀ → Type u) [∀ j, CommRing (SStage j)]
    (targetMap : ∀ j k : Set.Ici i₀, j ≤ k → SStage j →+* SStage k)
    [DirectedSystem SStage (fun j k h ↦ targetMap j k h)]
    (stageMapTail : (j : Set.Ici i₀) → A₀.RStage j.1 →+* SStage j)
    (hcommTail : ∀ {j k : Set.Ici i₀} (hjk : j ≤ k),
      (stageMapTail k).comp (A₀.map j.1 k.1 hjk) =
        (targetMap j k hjk).comp (stageMapTail j)) :
    R →+* Ring.DirectLimit SStage (fun j k h ↦ targetMap j k h) :=
  (Ring.DirectLimit.map stageMapTail (fun _ _ h ↦ hcommTail h)).comp
    (tail_directLimitIso A₀.RStage (fun i j h ↦ A₀.map i j h) i₀ A₀.colimitIso).symm.toRingHom

/-- Helper for Lemma 10.127.11: the source-to-target direct-limit map sends a source stage
generator to the corresponding target stage generator. -/
theorem sourceToTargetDirectLimit_stage_of
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (SStage : Set.Ici i₀ → Type u) [∀ j, CommRing (SStage j)]
    (targetMap : ∀ j k : Set.Ici i₀, j ≤ k → SStage j →+* SStage k)
    [DirectedSystem SStage (fun j k h ↦ targetMap j k h)]
    (stageMapTail : (j : Set.Ici i₀) → A₀.RStage j.1 →+* SStage j)
    (hcommTail : ∀ {j k : Set.Ici i₀} (hjk : j ≤ k),
      (stageMapTail k).comp (A₀.map j.1 k.1 hjk) =
        (targetMap j k hjk).comp (stageMapTail j))
    (i : Set.Ici i₀) (x : A₀.RStage i.1) :
    sourceToTargetDirectLimitOf A₀ i₀ SStage targetMap stageMapTail
      (fun {j} {k} hjk ↦ hcommTail hjk)
      (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h)
        A₀.colimitIso i.1 x) =
    Ring.DirectLimit.of SStage (fun j k h ↦ targetMap j k h) i (stageMapTail i x) := by
  change (Ring.DirectLimit.map stageMapTail (fun _ _ h ↦ hcommTail h))
      ((tail_directLimitIso A₀.RStage (fun i j h ↦ A₀.map i j h) i₀ A₀.colimitIso).symm
        (A₀.colimitIso
          (Ring.DirectLimit.of A₀.RStage (fun i j h ↦ A₀.map i j h) i.1 x))) =
    Ring.DirectLimit.of SStage (fun j k h ↦ targetMap j k h) i (stageMapTail i x)
  rw [tail_directLimitIso_symm_toLimitHom, Ring.DirectLimit.map_apply_of]

/-- Helper for Lemma 10.127.11: construct the target-colimit equivalence for the canonical
localized descended tail system. -/
theorem descendedTailTargetColimitData
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R))
    {P : Type u} [CommRing P] [Algebra R P] (g : R →+* P) [Algebra P S]
    (q : Ideal P) [q.IsPrime]
    (hlocq : q.primeCompl.IsLocalizationMap (algebraMap P S))
    (hfg : f = (algebraMap P S).comp g)
    (i₀ : A₀.Λ) (P₀ : Type u) [CommRing P₀]
    [Algebra (A₀.RStage i₀) P₀] [Algebra (A₀.RStage i₀) R]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (hPalg : algebraMap R P = g)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (hσ_raw_comp : ∀ (j k : Set.Ici i₀) (hjk : j ≤ k),
      descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e j =
        (descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e k).comp
          (descendedTailRawMap A₀ i₀ P₀ j k hjk))
    [IsDirectedOrder (Set.Ici i₀)]
    [DirectedSystem (descendedTailRawStage A₀ i₀ P₀)
      (fun j k h ↦ descendedTailRawMap A₀ i₀ P₀ j k h)]
    [DirectedSystem (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e)
      (fun j k h ↦ descendedTailTargetMap (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k h)]
    (stageMapTail : (j : Set.Ici i₀) → A₀.RStage j.1 →+*
      descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j)
    (hstageMapTail_apply : ∀ (j : Set.Ici i₀) (x : A₀.RStage j.1),
      stageMapTail j x =
        algebraMap (descendedTailRawStage A₀ i₀ P₀ j)
          (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j)
          ((algebraMap (A₀.RStage j.1) (descendedTailRawStage A₀ i₀ P₀ j)) x))
    (hcommTail : ∀ {j k : Set.Ici i₀} (hjk : j ≤ k),
      (stageMapTail k).comp (A₀.map j.1 k.1 hjk) =
        (descendedTailTargetMap (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k hjk).comp
          (stageMapTail j))
    (hSourceStage : ∀ (i : Set.Ici i₀) (x : A₀.RStage i.1),
      sourceToTargetDirectLimitOf A₀ i₀
        (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e)
        (descendedTailTargetMap (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp)
        stageMapTail (fun {j} {k} hjk ↦ hcommTail hjk)
        (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h)
          A₀.colimitIso i.1 x) =
      descendedTailOf (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp i (stageMapTail i x))
    (htargetColimitToAmbient_comm :
      (tail_target_colimit_to_ambient (S := S)
          (descendedTailRawStage A₀ i₀ P₀) (descendedTailRawMap A₀ i₀ P₀)
          (descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e) hσ_raw_comp).comp
          (Ring.DirectLimit.map stageMapTail (fun _ _ h ↦ hcommTail h)) =
        f.comp (tail_directLimitIso A₀.RStage (fun i j h ↦ A₀.map i j h)
          i₀ A₀.colimitIso).toRingHom) :
    ∃ eTail : descendedTailLimit (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp ≃+* S,
      eTail.toRingHom = tail_target_colimit_to_ambient (S := S)
        (descendedTailRawStage A₀ i₀ P₀) (descendedTailRawMap A₀ i₀ P₀)
        (descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e) hσ_raw_comp := by
  let tail : Type u := Set.Ici i₀
  letI : IsDirectedOrder tail := inferInstance
  let j0 : tail := ⟨i₀, le_rfl⟩
  let rawStage : tail → Type u := descendedTailRawStage A₀ i₀ P₀
  let rawMap : ∀ j k : tail, j ≤ k → rawStage j →+* rawStage k := fun j k h ↦
    descendedTailRawMap A₀ i₀ P₀ j k h
  let σ : (j : tail) → rawStage j →+* S := fun j ↦
    descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e j
  let SStage : tail → Type u := descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e
  let targetMap : ∀ j k : tail, j ≤ k → SStage j →+* SStage k := fun j k h ↦
    descendedTailTargetMap (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k h
  letI : DirectedSystem rawStage (fun j k h ↦ rawMap j k h) := inferInstance
  letI : DirectedSystem SStage (fun j k h ↦ targetMap j k h) := inferInstance
  let targetLimit : Type u := descendedTailLimit (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp
  let targetOf : (j : tail) → SStage j →+* targetLimit := fun j ↦
    descendedTailOf (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j
  let targetColimitToAmbient : targetLimit →+* S :=
    tail_target_colimit_to_ambient (S := S) rawStage rawMap σ hσ_raw_comp
  let minimalStageMap : P₀ →+* SStage j0 :=
    (algebraMap (rawStage j0) (SStage j0)).comp (algebraMap P₀ (rawStage j0))
  let p0ToTargetDirectLimit : P₀ →+* targetLimit :=
    tail_targetDirectLimit_of_minimal_stage (i₀ := i₀) (Sj := SStage)
      (fun j k h ↦ targetMap j k h) minimalStageMap
  have htargetColimitToAmbient_p0 :
      targetColimitToAmbient.comp p0ToTargetDirectLimit =
        ((algebraMap P S).comp e.toRingHom).comp
          (algebraMap P₀ (P₀ ⊗[A₀.RStage i₀] R)) := by
    ext x
    change
      (tail_target_colimit_to_ambient (S := S) rawStage rawMap σ hσ_raw_comp)
          (Ring.DirectLimit.of SStage (fun j k h ↦ targetMap j k h) j0
            (minimalStageMap x)) =
        (algebraMap P S) (e (algebraMap P₀ (P₀ ⊗[A₀.RStage i₀] R) x))
    refine (tail_target_colimit_to_ambient_of (S := S) (G := rawStage) (map := rawMap)
      (σ := σ) (hσ := hσ_raw_comp) j0 (minimalStageMap x)).trans ?_
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j0.1) := (A₀.map i₀ j0.1 j0.2).toAlgebra
    rw [show minimalStageMap x =
      algebraMap (rawStage j0) (SStage j0) ((algebraMap P₀ (rawStage j0)) x) from rfl]
    rw [Localization.localRingHom_to_map]
    simp only [σ, RingHom.comp_apply]
    have h1 : (algebraMap P₀ (rawStage j0)) x =
        (x ⊗ₜ[A₀.RStage i₀] (1 : A₀.RStage j0.1) : rawStage j0) := rfl
    rw [h1]
    simp only [RingHom.coe_coe, maxLocalizationCollapse_algebraMap]
    exact congrArg (fun y : P₀ ⊗[A₀.RStage i₀] R => (algebraMap P S) (e y)) (by
      rw [Algebra.TensorProduct.map_tmul, map_one]
      rfl)
  let sourceToTargetDirectLimit : R →+* targetLimit :=
    sourceToTargetDirectLimitOf A₀ i₀ SStage targetMap stageMapTail
      (fun {j} {k} hjk ↦ hcommTail hjk)
  letI algColim : Algebra (A₀.RStage i₀) targetLimit :=
    ((targetOf j0).comp (stageMapTail j0)).toAlgebra
  let p0Alg : P₀ →ₐ[A₀.RStage i₀] targetLimit :=
    algHomOfCompBase (target := targetOf j0) (stage := stageMapTail j0)
      (pmap := minimalStageMap) (fun r ↦ by
        letI : Algebra (A₀.RStage i₀) (A₀.RStage j0.1) := (A₀.map i₀ j0.1 j0.2).toAlgebra
        rw [hstageMapTail_apply j0 r]
        change (algebraMap (rawStage j0) (SStage j0))
            ((algebraMap P₀ (rawStage j0)) (algebraMap (A₀.RStage i₀) P₀ r)) =
          (algebraMap (rawStage j0) (SStage j0)) ((1 : P₀) ⊗ₜ[A₀.RStage i₀] r)
        exact tensor_minimalStage_base_comm (targetOf := RingHom.id (SStage j0))
          (hself := fun r ↦ by
            change (A₀.map i₀ j0.1 j0.2) r = r
            exact DirectedSystem.map_self (f := fun i j h ↦ A₀.map i j h) r) r)
  let srcAlg : R →ₐ[A₀.RStage i₀] targetLimit :=
    { sourceToTargetDirectLimit with
      commutes' := fun r ↦ by
        change ((Ring.DirectLimit.map stageMapTail (fun _ _ h ↦ hcommTail h)).comp
            (tail_directLimitIso A₀.RStage (fun i j h ↦ A₀.map i j h) i₀ A₀.colimitIso).symm.toRingHom)
            (algebraMap (A₀.RStage i₀) R r) =
          (targetOf j0) (stageMapTail j0 r)
        have hsrcfull : (tail_directLimitIso A₀.RStage (fun i j h ↦ A₀.map i j h)
              i₀ A₀.colimitIso).symm (algebraMap (A₀.RStage i₀) R r) =
            Ring.DirectLimit.of (fun j : tail ↦ A₀.RStage j.1)
              (fun j k h ↦ A₀.map j.1 k.1 h) j0 r := by
          apply (tail_directLimitIso A₀.RStage (fun i j h ↦ A₀.map i j h)
            i₀ A₀.colimitIso).injective
          rw [RingEquiv.apply_symm_apply]
          show algebraMap (A₀.RStage i₀) R r =
            (tail_directLimitIso A₀.RStage (fun i j h ↦ A₀.map i j h)
              i₀ A₀.colimitIso) (Ring.DirectLimit.of (fun j : tail ↦ A₀.RStage j.1)
                (fun j k h ↦ A₀.map j.1 k.1 h) j0 r)
          simp only [tail_directLimitIso, RingEquiv.trans_apply, RingEquiv.ofRingHom_apply]
          exact congrArg (fun h : A₀.RStage i₀ →+* R => h r) hRalg
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
          hsrcfull]
        rfl }
  let pComp : (i : tail) → rawStage i →+* P := fun i ↦
    descendedTailPComp A₀ i₀ P₀ hRalg e i
  have htargetColimitToAmbient_source :
      targetColimitToAmbient.comp sourceToTargetDirectLimit = f := by
    ext x
    change
      targetColimitToAmbient
          ((Ring.DirectLimit.map stageMapTail (fun _ _ h ↦ hcommTail h))
            ((tail_directLimitIso A₀.RStage (fun i j h ↦ A₀.map i j h)
              i₀ A₀.colimitIso).symm x)) =
        f x
    have h := congrArg
      (fun g : Ring.DirectLimit (fun j : tail ↦ A₀.RStage j.1)
          (fun j k h ↦ A₀.map j.1 k.1 h) →+* S =>
        g ((tail_directLimitIso A₀.RStage (fun i j h ↦ A₀.map i j h)
          i₀ A₀.colimitIso).symm x))
      htargetColimitToAmbient_comm
    simp only [RingHom.comp_apply] at h
    rw [h]
    simp
  refine localizedTailColimitData_of_descended_comparisons
    (G := rawStage) (map := rawMap) (σ := σ) (hσ := hσ_raw_comp)
    (e := e) (q := q) hlocq p0Alg srcAlg pComp ?_ ?_ ?_ ?_
  · intro i
    rfl
  · intro p
    have := congrArg (fun h : P₀ →+* S => h p) htargetColimitToAmbient_p0
    simp only [RingHom.comp_apply] at this
    exact this
  · intro r
    have hsrc0 := congrArg (fun h : R →+* S => h r) htargetColimitToAmbient_source
    simp only [RingHom.comp_apply] at hsrc0
    change (tail_target_colimit_to_ambient (S := S) rawStage rawMap σ hσ_raw_comp) (srcAlg r)
        = algebraMap P S (e ((1 : P₀) ⊗ₜ[A₀.RStage i₀] r))
    rw [show srcAlg r = sourceToTargetDirectLimit r from rfl, hsrc0]
    have he : e ((1 : P₀) ⊗ₜ[A₀.RStage i₀] r) = g r := by
      have hc := e.commutes r
      rwa [show algebraMap R (P₀ ⊗[A₀.RStage i₀] R) r = (1 : P₀) ⊗ₜ[A₀.RStage i₀] r from rfl,
        congrArg (fun h : R →+* P => h r) hPalg] at hc
    rw [he]
    exact congrArg (fun h : R →+* S => h r) hfg
  · intro i w
    exact descendedTail_descentPsi_factB (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp
      stageMapTail hstageMapTail_apply sourceToTargetDirectLimit hSourceStage
      p0Alg srcAlg (fun p ↦ rfl) (fun r ↦ rfl) i w

end SameUniverse
