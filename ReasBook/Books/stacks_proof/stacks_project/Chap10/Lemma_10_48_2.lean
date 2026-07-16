import Mathlib
import stacks_proof.stacks_project.Chap09.Lemma_9_6_9
import stacks_proof.stacks_project.Chap10.Definition_10_47_4
import stacks_proof.stacks_project.Chap10.Lemma_10_21_4
import stacks_proof.stacks_project.Chap10.Lemma_10_47_5
import stacks_proof.stacks_project.Chap10.Lemma_10_48_2.Index
import stacks_proof.stacks_project.Chap10.Lemma_10_48_6
import stacks_proof.stacks_project.Chap10.Definition_10_48_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct
open AlgebraicGeometry CommRingCat
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Algebra

universe u

section

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R]

/-- Helper for Lemma 10.48.2: a connected prime spectrum is nonempty, so the ring is
nontrivial. -/
private theorem nontrivial_of_connected_primeSpectrum {A : Type u} [CommRing A]
    (hA : ConnectedSpace (PrimeSpectrum A)) : Nontrivial A := by
  -- Proof comment: connected spaces are nonempty, and `Spec(A)` is nonempty exactly when `A` is
  -- nontrivial.
  letI : ConnectedSpace (PrimeSpectrum A) := hA
  exact PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance

/-- Helper for Lemma 10.48.2: connectedness transports across a homeomorphism. -/
private theorem connectedSpace_of_homeomorph {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) [ConnectedSpace X] : ConnectedSpace Y :=
  e.surjective.connectedSpace e.continuous

/-- Helper for Lemma 10.48.2: connectedness of prime spectra descends along injective ring maps
by transporting triviality of idempotents. -/
private theorem connectedSpace_primeSpectrum_of_injective {A B : Type u} [CommRing A]
    [CommRing B] (f : A →+* B) (hf : Function.Injective f) :
    ConnectedSpace (PrimeSpectrum B) → ConnectedSpace (PrimeSpectrum A) := by
  intro hB
  -- Proof comment: connectedness is equivalent to triviality of idempotents, and injectivity lets
  -- us pull that triviality back from `B` to `A`.
  letI : Nontrivial B := nontrivial_of_connected_primeSpectrum hB
  letI : Nontrivial A := RingHom.domain_nontrivial f
  refine (primeSpectrum_connectedSpace_iff_idempotents_trivial (R := A)).2 ?_
  intro e he
  have htrivB :
      ∀ b : B, IsIdempotentElem b → b = 0 ∨ b = 1 :=
    (primeSpectrum_connectedSpace_iff_idempotents_trivial (R := B)).1 hB
  rcases htrivB (f e) (he.map f) with hzero | hone
  · left
    exact hf <| by simpa using hzero
  · right
    exact hf <| by simpa using hone

/-- Helper for Lemma 10.48.2: every tensor in `R ⊗[k] SeparableClosure k` already comes from a
finite separable intermediate field of `SeparableClosure k / k`. -/
private theorem exists_finite_separable_stage_ringTensor_separableClosure
    (x : R ⊗[k] SeparableClosure k) :
    ∃ (L : IntermediateField k (SeparableClosure k)) (_ : FiniteDimensional k L)
      (_ : Algebra.IsSeparable k L) (xL : R ⊗[k] L),
      Algebra.TensorProduct.map (AlgHom.id k R) L.val xL = x := by
  -- Route correction: descend a single tensor element directly to an intermediate-field stage
  -- inside `SeparableClosure k`, avoiding the unstable finitely-generated-subalgebra promotion.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · -- Proof comment: the zero tensor already lives over the bottom intermediate field.
    refine ⟨⊥, inferInstance, inferInstance, 0, ?_⟩
    simp
  · intro r a
    let L : IntermediateField k (SeparableClosure k) :=
      IntermediateField.adjoin k ({a} : Set (SeparableClosure k))
    have ha_sep : IsSeparable k a :=
      Algebra.IsSeparable.isSeparable (F := k) (K := SeparableClosure k) (x := a)
    have hLfd : FiniteDimensional k L := by
      apply IntermediateField.finiteDimensional_adjoin
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact ha_sep.isIntegral
    have hLsep : Algebra.IsSeparable k L := by
      rw [IntermediateField.isSeparable_adjoin_iff_isSeparable]
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact ha_sep
    let aL : L := ⟨a, IntermediateField.subset_adjoin k ({a} : Set (SeparableClosure k)) (by simp)⟩
    refine ⟨L, hLfd, hLsep, r ⊗ₜ[k] aL, ?_⟩
    simp [L, aL]
  · intro x y hx hy
    rcases hx with ⟨Lx, hLx_fd, hLx_sep, xL, hxL⟩
    rcases hy with ⟨Ly, hLy_fd, hLy_sep, yL, hyL⟩
    let L : IntermediateField k (SeparableClosure k) := Lx ⊔ Ly
    let ix : Lx →ₐ[k] L := IntermediateField.inclusion le_sup_left
    let iy : Ly →ₐ[k] L := IntermediateField.inclusion le_sup_right
    let xL' : R ⊗[k] L := Algebra.TensorProduct.map (AlgHom.id k R) ix xL
    let yL' : R ⊗[k] L := Algebra.TensorProduct.map (AlgHom.id k R) iy yL
    refine ⟨L, inferInstance, inferInstance, xL' + yL', ?_⟩
    -- Proof comment: enlarge both stage witnesses to the common finite separable compositum.
    have hxL' :
        Algebra.TensorProduct.map (AlgHom.id k R) L.val xL' = x := by
      have hcomp :
          Algebra.TensorProduct.map (AlgHom.id k R) (L.val.comp ix) xL =
            Algebra.TensorProduct.map (AlgHom.id k R) L.val
              ((Algebra.TensorProduct.map (AlgHom.id k R) ix) xL) := by
        simpa using congrArg
          (fun ψ : R ⊗[k] Lx →ₐ[k] R ⊗[k] SeparableClosure k => ψ xL)
          (Algebra.TensorProduct.map_comp (AlgHom.id k R) (AlgHom.id k R) L.val ix)
      calc
        Algebra.TensorProduct.map (AlgHom.id k R) L.val xL'
            = Algebra.TensorProduct.map (AlgHom.id k R) (L.val.comp ix) xL := by
                simpa [xL'] using hcomp.symm
        _ = Algebra.TensorProduct.map (AlgHom.id k R) Lx.val xL := by
              rfl
        _ = x := hxL
    have hyL' :
        Algebra.TensorProduct.map (AlgHom.id k R) L.val yL' = y := by
      have hcomp :
          Algebra.TensorProduct.map (AlgHom.id k R) (L.val.comp iy) yL =
            Algebra.TensorProduct.map (AlgHom.id k R) L.val
              ((Algebra.TensorProduct.map (AlgHom.id k R) iy) yL) := by
        simpa using congrArg
          (fun ψ : R ⊗[k] Ly →ₐ[k] R ⊗[k] SeparableClosure k => ψ yL)
          (Algebra.TensorProduct.map_comp (AlgHom.id k R) (AlgHom.id k R) L.val iy)
      calc
        Algebra.TensorProduct.map (AlgHom.id k R) L.val yL'
            = Algebra.TensorProduct.map (AlgHom.id k R) (L.val.comp iy) yL := by
                simpa [yL'] using hcomp.symm
        _ = Algebra.TensorProduct.map (AlgHom.id k R) Ly.val yL := by
              rfl
        _ = y := hyL
    simp [xL', yL', hxL', hyL']

/-- Helper for Lemma 10.48.2: tensoring a connected algebra with a geometrically connected
algebra over a field preserves connectedness of prime spectra. -/
private theorem connectedSpace_primeSpectrum_tensorProduct_of_geometricallyConnected_right
    {L A S : Type u} [Field L] [CommRing A] [Algebra L A] [CommRing S] [Algebra L S]
    (hA : ConnectedSpace (PrimeSpectrum A))
    (hS : geometrically (ConnectedSpace ·) (Spec.map (ofHom (algebraMap L S)))) :
    ConnectedSpace (PrimeSpectrum (A ⊗[L] S)) := by
  -- Route correction: use the idempotent bijection from Lemma `10.48.6` directly, rather than
  -- importing the later packaged statement `Lemma_10_48_1`.
  letI : Nontrivial A := nontrivial_of_connected_primeSpectrum hA
  rw [geometricallyConnected_iff_connectedSpace_primeSpectrum_baseChange] at hS
  have hSL : ConnectedSpace (PrimeSpectrum (S ⊗[L] L)) := hS L
  let eS : S ⊗[L] L ≃ₐ[S] S := Algebra.TensorProduct.rid L S S
  letI : Nontrivial (S ⊗[L] L) := nontrivial_of_connected_primeSpectrum hSL
  letI : Nontrivial S := eS.injective.nontrivial
  letI : Nontrivial (A ⊗[L] S) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left
      (R := L) (A := A) (B := S) (algebraMap L S).injective
  have htrivA :
      ∀ a : A, IsIdempotentElem a → a = 0 ∨ a = 1 :=
    (primeSpectrum_connectedSpace_iff_idempotents_trivial (R := A)).1 hA
  have hbij :
      Function.Bijective
        (fun e : {a : A // IsIdempotentElem a} ↦
          (⟨includeLeft e.1, e.2.map (includeLeft : A →ₐ[L] A ⊗[L] S)⟩ :
            {x : A ⊗[L] S // IsIdempotentElem x})) :=
    (Lemma_10_48_6 (k := L) (R := A) (S := S)
      (by
        rw [geometricallyConnected_iff_connectedSpace_primeSpectrum_baseChange]
        intro K _ _
        exact hS K)).1
  refine (primeSpectrum_connectedSpace_iff_idempotents_trivial (R := A ⊗[L] S)).2 ?_
  intro e he
  rcases hbij.surjective ⟨e, he⟩ with ⟨a, ha⟩
  rcases htrivA a.1 a.2 with hzero | hone
  · left
    apply congrArg Subtype.val at ha
    simpa [hzero] using ha.symm
  · right
    apply congrArg Subtype.val at ha
    simpa [hone] using ha.symm

/-- Helper for Lemma 10.48.2: if every finite separable base change is connected, then the base
change to the separable closure is connected. -/
private theorem connectedSpace_primeSpectrum_separableClosure_of_finiteSeparable
    (h :
      ∀ (K : Type u) [Field K] [Algebra k K]
        [FiniteDimensional k K] [Algebra.IsSeparable k K],
        ConnectedSpace (PrimeSpectrum (R ⊗[k] K))) :
    ConnectedSpace (PrimeSpectrum (R ⊗[k] SeparableClosure k)) := by
  -- Route correction: descend a hypothetical nontrivial idempotent only to one finite separable
  -- intermediate field stage, then contradict connectedness there.
  by_contra hSep
  have hk : ConnectedSpace (PrimeSpectrum (R ⊗[k] k)) := h k
  letI : Nontrivial (R ⊗[k] k) := nontrivial_of_connected_primeSpectrum hk
  let eBase : R ⊗[k] k ≃ₐ[R] R := Algebra.TensorProduct.rid k R R
  letI : Nontrivial R := eBase.injective.nontrivial
  letI : Nontrivial (R ⊗[k] SeparableClosure k) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left
      (R := k) (A := R) (B := SeparableClosure k) (algebraMap k (SeparableClosure k)).injective
  have hexists :
      ∃ e : R ⊗[k] SeparableClosure k, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
    by_contra hno
    apply hSep
    refine (primeSpectrum_connectedSpace_iff_idempotents_trivial
      (R := R ⊗[k] SeparableClosure k)).2 ?_
    intro e he
    by_cases hzero : e = 0
    · exact Or.inl hzero
    · right
      by_contra hone
      exact hno ⟨e, he, hzero, hone⟩
  obtain ⟨e, he, he_zero, he_one⟩ := hexists
  obtain ⟨L, hLfd, hLsep, eL, heL_map⟩ :=
    exists_finite_separable_stage_ringTensor_separableClosure (k := k) (R := R) e
  let stageMap : R ⊗[k] L →ₐ[k] R ⊗[k] SeparableClosure k :=
    Algebra.TensorProduct.map (AlgHom.id k R) L.val
  have hstage_inj : Function.Injective stageMap := by
    -- Proof comment: tensoring the injective field inclusion `L ↪ SeparableClosure k` preserves
    -- injectivity because both tensor factors are flat over the base field.
    simpa [stageMap] using TensorProduct.map_injective_of_flat_flat
      (AlgHom.id k R).toLinearMap L.val.toLinearMap Function.injective_id L.val.injective
  have heL : IsIdempotentElem eL := by
    -- Proof comment: the descended element is idempotent because its image is the given
    -- idempotent upstairs and the stage map is injective.
    exact hstage_inj <| by
      calc
        stageMap (eL * eL) = stageMap eL * stageMap eL := by rw [map_mul]
        _ = stageMap eL * e := by rw [heL_map]
        _ = e * e := by rw [heL_map]
        _ = e := he.eq
        _ = stageMap eL := by rw [heL_map]
  have heL_zero : eL ≠ 0 := by
    intro hzero
    apply he_zero
    rw [← heL_map, hzero, map_zero]
  have heL_one : eL ≠ 1 := by
    intro hone
    apply he_one
    rw [← heL_map, hone, map_one]
  have hL : ConnectedSpace (PrimeSpectrum (R ⊗[k] L)) := h L
  letI : Nontrivial (R ⊗[k] L) := nontrivial_of_connected_primeSpectrum hL
  have htrivL :
      ∀ x : R ⊗[k] L, IsIdempotentElem x → x = 0 ∨ x = 1 :=
    (primeSpectrum_connectedSpace_iff_idempotents_trivial (R := R ⊗[k] L)).1 hL
  rcases htrivL eL heL with hzero | hone
  · exact heL_zero hzero
  · exact heL_one hone

/-- Helper for Lemma 10.48.2: a field over a separably closed base field is geometrically
connected. -/
private theorem geometricallyConnected_of_field_over_isSepClosed
    {L Ω : Type u} [Field L] [IsSepClosed L] [Field Ω] [Algebra L Ω] :
    geometrically (ConnectedSpace ·) (Spec.map (ofHom (algebraMap L Ω))) := by
  have hGeomIrred :
      GeometricallyIrreducible (Spec.map (ofHom (algebraMap L Ω))) := by
    -- Proof comment: over a separably closed field, a field algebra has irreducible spectrum, so
    -- Lemma `10.47.5` upgrades that to geometric irreducibility.
    refine (Lemma_10_47_5 (k := L) (R := Ω)).2 ?_
    infer_instance
  rw [geometricallyConnected_iff_connectedSpace_primeSpectrum_baseChange]
  intro K _ _
  -- Proof comment: every field-valued base change stays irreducible by geometric irreducibility,
  -- hence connected.
  rw [geometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_baseChange] at hGeomIrred
  letI : IrreducibleSpace (PrimeSpectrum (Ω ⊗[L] K)) := hGeomIrred K
  infer_instance

/-- Helper for Lemma 10.48.2: connectedness after base change to the separable closure implies
connectedness after every field extension. -/
private theorem connectedSpace_primeSpectrum_baseChange_of_separableClosure
    (hSep : ConnectedSpace (PrimeSpectrum (R ⊗[k] SeparableClosure k))) :
    ∀ (K : Type u) [Field K] [Algebra k K], ConnectedSpace (PrimeSpectrum (R ⊗[k] K)) := by
  intro K _ _
  obtain ⟨Ω, _, _, iK, iSep, hiK, _⟩ :=
    exists_common_field_extension (k := k) (E := K) (F := SeparableClosure k)
  letI : Algebra (SeparableClosure k) Ω := iSep.toAlgebra
  letI : IsScalarTower k (SeparableClosure k) Ω := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro x
    exact (iSep.commutes x).symm
  let baseChangeMap : R ⊗[k] K →ₐ[k] R ⊗[k] Ω :=
    Algebra.TensorProduct.map (AlgHom.id k R) iK
  have hbaseChangeMap_injective : Function.Injective baseChangeMap := by
    -- Proof comment: tensoring the injective field map `K ↪ Ω` with the identity on `R` preserves
    -- injectivity because both tensor factors are flat over the base field `k`.
    simpa [baseChangeMap] using TensorProduct.map_injective_of_flat_flat
      (AlgHom.id k R).toLinearMap iK.toLinearMap Function.injective_id hiK
  have hΩ_geom :
      geometrically (ConnectedSpace ·)
        (Spec.map (ofHom (algebraMap (SeparableClosure k) Ω))) :=
    geometricallyConnected_of_field_over_isSepClosed
      (L := SeparableClosure k) (Ω := Ω)
  have hIter :
      ConnectedSpace
        (PrimeSpectrum ((R ⊗[k] SeparableClosure k) ⊗[SeparableClosure k] Ω)) := by
    -- Proof comment: once the right factor `Ω` is geometrically connected over the separable
    -- closure, the tensor-product connectedness lemma applies directly to the source base change.
    exact connectedSpace_primeSpectrum_tensorProduct_of_geometricallyConnected_right
      (L := SeparableClosure k) (A := R ⊗[k] SeparableClosure k) (S := Ω) hSep hΩ_geom
  let eCompare :
      ((R ⊗[k] SeparableClosure k) ⊗[SeparableClosure k] Ω) ≃+* R ⊗[k] Ω :=
    baseChange_separableClosure_tensor_equiv (k := k) (R := R) (Ω := Ω)
  have hΩ :
      ConnectedSpace (PrimeSpectrum (R ⊗[k] Ω)) := by
    -- Proof comment: transport connectedness across the named iterated-base-change comparison,
    -- instead of re-elaborating the whole tensor equivalence chain inline.
    letI :
        ConnectedSpace
          (PrimeSpectrum ((R ⊗[k] SeparableClosure k) ⊗[SeparableClosure k] Ω)) := hIter
    exact connectedSpace_of_homeomorph (PrimeSpectrum.homeomorphOfRingEquiv eCompare)
  -- Proof comment: connectedness finally descends from the common overfield tensor product along
  -- the injective base-change map `R ⊗[k] K → R ⊗[k] Ω`.
  exact connectedSpace_primeSpectrum_of_injective
    baseChangeMap.toRingHom hbaseChangeMap_injective hΩ

-- Proof sketch: the forward implication is immediate. For the converse, pass to
-- `SeparableClosure k`, use the idempotent criterion for connectedness together with the
-- finite-separable-stage detection of idempotents after tensor product, and then compare an
-- arbitrary base change with a common overfield containing both it and `SeparableClosure k`.
/-- Source-facing companion to Lemma 10.48.2: it suffices to test connectedness of
`Spec (R ⊗[k] K)` on finite separable field extensions `K / k`. -/
theorem connectedSpace_primeSpectrum_baseChange_iff_finiteSeparable_baseChange :
    (∀ (K : Type u) [Field K] [Algebra k K], ConnectedSpace (PrimeSpectrum (R ⊗[k] K))) ↔
      ∀ (K : Type u) [Field K] [Algebra k K]
        [FiniteDimensional k K] [Algebra.IsSeparable k K],
        ConnectedSpace (PrimeSpectrum (R ⊗[k] K)) := by
  constructor
  · intro h K _ _ _ _
    -- Proof comment: finite separable extensions are a special case of arbitrary extensions.
    exact h K
  · intro h
    -- Proof comment: first pass to `SeparableClosure k`, then descend from a common overfield for
    -- an arbitrary extension and the separable closure.
    have hSep :
        ConnectedSpace (PrimeSpectrum (R ⊗[k] SeparableClosure k)) :=
      connectedSpace_primeSpectrum_separableClosure_of_finiteSeparable (k := k) (R := R) h
    exact connectedSpace_primeSpectrum_baseChange_of_separableClosure (k := k) (R := R) hSep

/-- Lemma 10.48.2 (Tag 037S): a `k`-algebra is geometrically connected iff it remains connected
after every finite separable base change. -/
@[stacks 037S]
theorem Lemma_10_48_2 :
    geometrically (ConnectedSpace ·) (Spec.map (ofHom (algebraMap k R))) ↔
      ∀ (K : Type u) [Field K] [Algebra k K]
        [FiniteDimensional k K] [Algebra.IsSeparable k K],
        ConnectedSpace (PrimeSpectrum (R ⊗[k] K)) := by
  rw [geometricallyConnected_iff_connectedSpace_primeSpectrum_baseChange]
  exact connectedSpace_primeSpectrum_baseChange_iff_finiteSeparable_baseChange

end

end Algebra
