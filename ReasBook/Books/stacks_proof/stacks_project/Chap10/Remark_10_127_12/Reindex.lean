import stacks_proof.stacks_project.Chap10.Lemma_10_127_10
import stacks_proof.stacks_project.Chap10.Lemma_10_127_11
import Mathlib.RingTheory.DualNumber

universe u v w w₀

section

open DirectedLocalHomApproximation
open scoped DualNumber TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Helper for Remark 10.127.12: reindexing a `Type`-indexed directed ring system along
`ULift.down` preserves
the directed-system identities. -/
private instance ulift_isDirectedOrder {ι : Type} [Preorder ι] [IsDirectedOrder ι] :
    IsDirectedOrder (ULift.{w} ι) := by
  refine ⟨?_⟩
  intro i j
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.down j.down
  exact ⟨ULift.up k, hik, hjk⟩

/-- Helper for Remark 10.127.12: reindexing a `Type`-indexed directed ring system along
`ULift.down` preserves
the directed-system identities. -/
private instance ulift_directedSystem {ι : Type} [Preorder ι]
    (G : ι → Type u) [∀ i, CommRing (G i)]
    (φ : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ φ i j h)] :
    DirectedSystem (fun i : ULift.{w} ι ↦ G i.down) (fun i j h ↦ φ i.down j.down h) where
  map_self := by
    intro i x
    simpa using DirectedSystem.map_self (f := fun i j h ↦ φ i j h) x
  map_map := by
    intro i j k hij hjk x
    simpa using DirectedSystem.map_map (f := fun i j h ↦ φ i j h) hij hjk x

/-- Helper for Remark 10.127.12: the direct limit of a `ULift`-reindexed `Type`-indexed system
maps to the
original direct limit by forgetting the lifted index. -/
private noncomputable def directLimit_uliftToOriginal {ι : Type} [Preorder ι]
    (G : ι → Type u) [∀ i, CommRing (G i)]
    (φ : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ φ i j h)] :
    Ring.DirectLimit (fun i : ULift.{w} ι ↦ G i.down) (fun i j h ↦ φ i.down j.down h) →+*
      Ring.DirectLimit G (fun i j h ↦ φ i j h) :=
  Ring.DirectLimit.lift
    (fun i : ULift.{w} ι ↦ G i.down) (fun i j h ↦ φ i.down j.down h)
    (Ring.DirectLimit G (fun i j h ↦ φ i j h))
    (fun i ↦ Ring.DirectLimit.of G (fun i j h ↦ φ i j h) i.down)
    (by
      intro i j hij x
      simpa using (Ring.DirectLimit.of_f hij x))

/-- Helper for Remark 10.127.12: the previous map sends each lifted stage generator to the
corresponding generator in the original direct limit. -/
@[simp] private theorem directLimit_uliftToOriginal_of {ι : Type} [Preorder ι]
    (G : ι → Type u) [∀ i, CommRing (G i)]
    (φ : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ φ i j h)]
    (i : ULift.{w} ι) (x : G i.down) :
    directLimit_uliftToOriginal (G := G) (φ := φ)
        (Ring.DirectLimit.of (fun j : ULift.{w} ι ↦ G j.down) (fun j k h ↦ φ j.down k.down h)
          i x) =
      Ring.DirectLimit.of G (fun j k h ↦ φ j k h) i.down x := by
  -- Proof comment: this is the defining formula for the universal direct-limit lift.
  simpa [directLimit_uliftToOriginal] using
    (Ring.DirectLimit.lift_of
      (G := fun j : ULift.{w} ι ↦ G j.down)
      (f := fun j k h ↦ φ j.down k.down h)
      (P := Ring.DirectLimit G (fun j k h ↦ φ j k h))
      (g := fun j ↦ Ring.DirectLimit.of G (fun j k h ↦ φ j k h) j.down)
      (Hg := by intro i j hij y; rfl)
      i x)

/-- Helper for Remark 10.127.12: the original direct limit maps back to the `ULift`-reindexed
direct limit by inserting `ULift.up` on indices. -/
private noncomputable def directLimit_originalToUlift {ι : Type} [Preorder ι]
    (G : ι → Type u) [∀ i, CommRing (G i)]
    (φ : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ φ i j h)] :
    Ring.DirectLimit G (fun i j h ↦ φ i j h) →+*
      Ring.DirectLimit (fun i : ULift.{w} ι ↦ G i.down) (fun i j h ↦ φ i.down j.down h) :=
  Ring.DirectLimit.lift
    G (fun i j h ↦ φ i j h)
    (Ring.DirectLimit (fun i : ULift.{w} ι ↦ G i.down) (fun i j h ↦ φ i.down j.down h))
    (fun i ↦ Ring.DirectLimit.of (fun j : ULift.{w} ι ↦ G j.down) (fun j k h ↦ φ j.down k.down h)
      (ULift.up i))
    (by
      intro i j hij x
      simpa using (Ring.DirectLimit.of_f hij x))

/-- Helper for Remark 10.127.12: the map back to the lifted direct limit sends each original stage
generator to the corresponding lifted generator. -/
@[simp] private theorem directLimit_originalToUlift_of {ι : Type} [Preorder ι]
    (G : ι → Type u) [∀ i, CommRing (G i)]
    (φ : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ φ i j h)]
    (i : ι) (x : G i) :
    directLimit_originalToUlift (G := G) (φ := φ)
        (Ring.DirectLimit.of G (fun j k h ↦ φ j k h) i x) =
      Ring.DirectLimit.of (fun j : ULift.{w} ι ↦ G j.down) (fun j k h ↦ φ j.down k.down h)
        (ULift.up i) x := by
  -- Proof comment: this is again the defining `lift_of` formula.
  simpa [directLimit_originalToUlift] using
    (Ring.DirectLimit.lift_of
      (G := G)
      (f := fun j k h ↦ φ j k h)
      (P := Ring.DirectLimit (fun j : ULift.{w} ι ↦ G j.down) (fun j k h ↦ φ j.down k.down h))
      (g := fun i ↦
        Ring.DirectLimit.of (fun j : ULift.{w} ι ↦ G j.down) (fun j k h ↦ φ j.down k.down h)
          (ULift.up i))
      (Hg := by intro i j hij y; rfl)
      i x)

/-- Helper for Remark 10.127.12: reindexing a `Type`-indexed directed ring system along `ULift`
does not change
its direct limit. -/
private noncomputable def directLimit_uliftRingEquiv {ι : Type} [Preorder ι]
    (G : ι → Type u) [∀ i, CommRing (G i)]
    (φ : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ φ i j h)] :
    Ring.DirectLimit (fun i : ULift.{w} ι ↦ G i.down) (fun i j h ↦ φ i.down j.down h) ≃+*
      Ring.DirectLimit G (fun i j h ↦ φ i j h) :=
  RingEquiv.ofRingHom
    (directLimit_uliftToOriginal (G := G) (φ := φ))
    (directLimit_originalToUlift (G := G) (φ := φ))
    (by
      -- Proof comment: on every original stage generator, forgetting and then restoring the
      -- lifted index is definitionally the identity.
      apply Ring.DirectLimit.hom_ext
      intro i
      ext x
      simp [directLimit_uliftToOriginal, directLimit_originalToUlift])
    (by
      -- Proof comment: the same argument works on the lifted-index presentation.
      apply Ring.DirectLimit.hom_ext
      intro i
      ext x
      simp [directLimit_uliftToOriginal, directLimit_originalToUlift])

/-- Helper for Remark 10.127.12: the direct-limit equivalence sends a lifted generator to the
corresponding original generator. -/
@[simp] private theorem directLimit_uliftRingEquiv_of {ι : Type} [Preorder ι]
    (G : ι → Type u) [∀ i, CommRing (G i)]
    (φ : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ φ i j h)]
    (i : ULift.{w} ι) (x : G i.down) :
    directLimit_uliftRingEquiv (G := G) (φ := φ)
        (Ring.DirectLimit.of (fun j : ULift.{w} ι ↦ G j.down) (fun j k h ↦ φ j.down k.down h)
          i x) =
      Ring.DirectLimit.of G (fun j k h ↦ φ j k h) i.down x := by
  -- Proof comment: the forward map of the equivalence is the named forgetting morphism.
  exact directLimit_uliftToOriginal_of (G := G) (φ := φ) i x

namespace DirectedLocalHomApproximation

/-- Helper for Remark 10.127.12: the `ULift`-reindexed approximation inherits the original
colimit compatibility statement on each stage generator. -/
private theorem reindex_ulift_colimit_comm {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] {f : R →+* S}
    (A : DirectedLocalHomApproximation.{u, v, 0} f) :
    ((directLimit_uliftRingEquiv (G := A.SStage) (φ := A.targetMap)).trans A.targetColimit).toRingHom.comp
        (Ring.DirectLimit.map (fun i : ULift.{w} A.Λ ↦ A.stageMap i.down)
          (fun _ _ h ↦ A.comm h)) =
      f.comp
        ((directLimit_uliftRingEquiv (G := A.RStage) (φ := A.map)).trans A.colimitIso).toRingHom := by
  -- Proof comment: compare both ring homomorphisms on a lifted stage generator, collapse the two
  -- `ULift` direct-limit presentations back to the original ones, and then invoke the original
  -- colimit square of `A`.
  apply Ring.DirectLimit.hom_ext
  intro i
  ext x
  have hA :=
    congrArg
      (fun g : Ring.DirectLimit A.RStage (fun j k h ↦ A.map j k h) →+* S =>
        g (Ring.DirectLimit.of A.RStage (fun j k h ↦ A.map j k h) i.down x))
      A.colimit_comm
  simpa [RingHom.comp_apply] using hA

/-- Helper for Remark 10.127.12: reindex a directed local approximation along `ULift` so the
index type lands in the ambient universe `w`. -/
noncomputable def reindex_ulift {R : Type u} {S : Type v}
    [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] {f : R →+* S}
    (A : DirectedLocalHomApproximation.{u, v, 0} f) :
    DirectedLocalHomApproximation.{u, v, w} f :=
  { Λ := ULift.{w} A.Λ
    instPreorder := inferInstance
    instNonempty := inferInstance
    instDirectedOrder := inferInstance
    RStage := fun i ↦ A.RStage i.down
    instCommRingRStage := fun i ↦ A.instCommRingRStage i.down
    map := fun i j h ↦ A.map i.down j.down h
    instDirectedSystemRStage := ulift_directedSystem A.RStage A.map
    colimitIso := (directLimit_uliftRingEquiv (G := A.RStage) (φ := A.map)).trans A.colimitIso
    instIsLocalRingRStage := fun i ↦ A.instIsLocalRingRStage i.down
    SStage := fun i ↦ A.SStage i.down
    instCommRingSStage := fun i ↦ A.instCommRingSStage i.down
    instIsLocalRingSStage := fun i ↦ A.instIsLocalRingSStage i.down
    stageMap := fun i ↦ A.stageMap i.down
    stageMap_isLocalHom := fun i ↦ A.stageMap_isLocalHom i.down
    targetMap := fun i j h ↦ A.targetMap i.down j.down h
    instDirectedSystemTarget := ulift_directedSystem A.SStage A.targetMap
    comm := fun {_ _} h ↦ A.comm h
    targetColimit :=
      (directLimit_uliftRingEquiv (G := A.SStage) (φ := A.targetMap)).trans A.targetColimit
    colimit_comm := reindex_ulift_colimit_comm A
    source_essFiniteType := fun i ↦ A.source_essFiniteType i.down
    target_essFiniteType := fun i ↦ A.target_essFiniteType i.down }

end DirectedLocalHomApproximation

end
