import Mathlib
import StacksProject_2024.Chap10.Lemma_10_20_1_Nakayama_s_lemma
import StacksProject_2024.Chap10.Lemma_10_39_10
import StacksProject_2024.Chap10.Lemma_10_77_5
import StacksProject_2024.Chap10.Lemma_10_99_1

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open TensorProduct.AlgebraTensorModule
open scoped TensorProduct
open IsLocalRing

universe u v w x

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S]
variable [IsLocalRing R] [IsLocalRing S]
variable [IsNoetherianRing S]
variable [Algebra R S] [IsLocalHom (algebraMap R S)]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Finite S M]

local notation "𝔪S" => Ideal.map (algebraMap R S) (maximalIdeal R)
local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S
local notation "ClosedFiberModule" => ClosedFiber ⊗[S] M

/- Domain sampling pass:
* primary domain: local commutative algebra of finite modules over flat local homomorphisms and
  their closed fibers;
* sampled owner declarations:
  - `Ideal.Fiber`, the canonical closed-fiber ring owner `κ(maximalIdeal R) ⊗[R] S`;
  - `TensorProduct.quotTensorEquivQuotSMul`, the quotient model for reduction modulo an ideal;
  - `injective_of_mod_maximalIdeal_injective`, the injectivity criterion from Lemma `10.99.1`;
  - `surjective_of_quotientMap_surjective_of_le_ring_jacobson`, the Nakayama-surjectivity lemma;
  - `algebraMap_flat_of_flat_of_faithfullyFlat`, the faithful-flat descent statement for
    algebra-map flatness.

Source/core/bridge triage:
* source-facing: the two textbook statements about freeness of `M` and flatness of `R → S`;
* core/canonical: the closed-fiber ring `ClosedFiber` and its fiber module `ClosedFiber ⊗[S] M`;
* bridge/view: the quotient presentation
  `M ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M))`.
-/

/-- Helper for Lemma 10.99.4: the closed fiber is canonically the quotient `S / 𝔪S`. -/
noncomputable def closedFiber_quotient_equiv :
    (S ⧸ 𝔪S) ≃ₐ[S] ClosedFiber :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (maximalIdeal R)).trans <|
    (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
      (.ofBijective _
        (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R)))).trans <|
      Algebra.TensorProduct.commRight R S ((maximalIdeal R).ResidueField)

omit [IsLocalRing S] [IsNoetherianRing S] [IsLocalHom (algebraMap R S)] in
/-- Helper for Lemma 10.99.4: under the quotient description of the closed fiber, the class of
`s : S` maps to its canonical image in the tensor fiber. -/
@[simp] lemma closedFiber_quotient_equiv_mk (s : S) :
    closedFiber_quotient_equiv (R := R) (S := S) (Ideal.Quotient.mk 𝔪S s) =
      algebraMap S ClosedFiber s := by
  -- Unfold the quotient-to-fiber comparison and evaluate it on the quotient class of `s`.
  simp [closedFiber_quotient_equiv, Algebra.TensorProduct.right_algebraMap_apply]

omit [IsLocalRing S] [IsNoetherianRing S] [IsLocalHom (algebraMap R S)] in
/-- Helper for Lemma 10.99.4: the inverse quotient-to-fiber comparison sends the image of `s : S`
back to its quotient class. -/
@[simp] lemma closedFiber_quotient_equiv_symm_algebraMap (s : S) :
    (closedFiber_quotient_equiv (R := R) (S := S)).symm (algebraMap S ClosedFiber s) =
      Ideal.Quotient.mk 𝔪S s := by
  -- Proof comment: this is just the inverse form of the representative computation above.
  simpa using
    (closedFiber_quotient_equiv_mk (R := R) (S := S) s)

omit [IsLocalRing S] [IsNoetherianRing S] [IsLocalHom (algebraMap R S)] in
/-- Helper for Lemma 10.99.4: the algebra map `S → ClosedFiber` is surjective because the closed
fiber is the quotient `S / 𝔪S`. -/
lemma closedFiber_algebraMap_surjective :
    Function.Surjective (algebraMap S ClosedFiber) := by
  -- Every fiber element comes from a quotient class, and every quotient class has a lift in `S`.
  intro x
  obtain ⟨y, rfl⟩ := (closedFiber_quotient_equiv (R := R) (S := S)).surjective x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨s, (closedFiber_quotient_equiv_mk (R := R) (S := S) s).symm⟩

/-- Helper for Lemma 10.99.4: quotienting the free module `ι →₀ S` by `𝔪S` identifies with
coefficientwise reduction modulo `𝔪S`. -/
noncomputable def finsupp_quotient_equiv (ι : Type*) :
    ((ι →₀ S) ⧸ (𝔪S • (⊤ : Submodule S (ι →₀ S)))) ≃ₗ[S]
      ι →₀ (S ⧸ 𝔪S) :=
  (Submodule.quotEquivOfEq
      (𝔪S • (⊤ : Submodule S (ι →₀ S)))
      (LinearMap.ker (finsupp_quotientMapLinear (R := S) (I := 𝔪S) ι))
      (finsupp_quotientMap_ker_eq_ideal_smul_top (R := S) (I := 𝔪S) (ι := ι)).symm).trans <|
    (finsupp_quotientMapLinear (R := S) (I := 𝔪S) ι).quotKerEquivOfSurjective
      (finsupp_quotientMap_surjective (R := S) (I := 𝔪S) ι)

omit [IsLocalRing S] [IsNoetherianRing S] [IsLocalHom (algebraMap R S)] in
/-- Helper for Lemma 10.99.4: the quotient of the free module maps to the coefficientwise reduced
vector on representatives. -/
@[simp] lemma finsupp_quotient_equiv_apply_mk (ι : Type*) (l : ι →₀ S) :
    finsupp_quotient_equiv (R := R) (S := S) ι (Submodule.Quotient.mk l) =
      finsupp_quotientMapLinear (R := S) (I := 𝔪S) ι l := by
  -- The quotient equivalence is built from the kernel identification followed by the first
  -- isomorphism theorem for the coefficientwise quotient map.
  simp [finsupp_quotient_equiv]

omit [IsLocalRing S] [IsNoetherianRing S] [IsLocalHom (algebraMap R S)] in
/-- Helper for Lemma 10.99.4: the inverse quotient equivalence sends the coefficientwise reduced
vector back to the quotient class of the original finitely supported family. -/
@[simp] lemma finsupp_quotient_equiv_symm_apply_quotientMap (ι : Type*) (l : ι →₀ S) :
    (finsupp_quotient_equiv (R := R) (S := S) ι).symm
      (finsupp_quotientMapLinear (R := S) (I := 𝔪S) ι l) =
        Submodule.Quotient.mk l := by
  -- Proof comment: rewrite the target through the forward representative formula and cancel the
  -- quotient equivalence with its inverse.
  rw [← finsupp_quotient_equiv_apply_mk (R := R) (S := S) (ι := ι) l]
  exact (finsupp_quotient_equiv (R := R) (S := S) ι).symm_apply_apply _

/-- Helper for Lemma 10.99.4: quotienting an `S`-module by `𝔪S` agrees with quotienting its
underlying `R`-module by `maximalIdeal R`. -/
noncomputable def map_maximalIdeal_quotient_equiv
    (N : Type*) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    (N ⧸ (𝔪S • (⊤ : Submodule S N))) ≃ₗ[R]
      N ⧸ (maximalIdeal R • (⊤ : Submodule R N)) :=
  (Submodule.Quotient.restrictScalarsEquiv R (𝔪S • (⊤ : Submodule S N))).trans <|
    quotient_source_over_mapped_ideal_equiv (R := R) (S := S) (N := N) (maximalIdeal R)

omit [IsLocalRing S] [IsNoetherianRing S] [IsLocalHom (algebraMap R S)] in
/-- Helper for Lemma 10.99.4: the quotient comparison above fixes representatives. -/
@[simp] lemma map_maximalIdeal_quotient_equiv_apply_mk
    (N : Type*) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (x : N) :
    map_maximalIdeal_quotient_equiv (R := R) (S := S) N (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := by
  -- Both quotient comparisons are definitionally the identity on representatives.
  change
    quotient_source_over_mapped_ideal_equiv (R := R) (S := S) (N := N) (maximalIdeal R)
      ((Submodule.Quotient.restrictScalarsEquiv R (𝔪S • (⊤ : Submodule S N)))
        (Submodule.Quotient.mk x)) =
      Submodule.Quotient.mk x
  rw [Submodule.Quotient.restrictScalarsEquiv_mk]
  simpa using
    quotient_source_over_mapped_ideal_equiv_apply_mk
      (R := R) (S := S) (N := N) (maximalIdeal R) x

/-- Helper for Lemma 10.99.4: the quotient model of the closed-fiber module is the quotient
`M / 𝔪S M`, viewed as a `ClosedFiber`-module via the quotient-ring identification. -/
noncomputable def closed_fiber_module_quotient_equiv :
    letI : Algebra ClosedFiber (S ⧸ 𝔪S) :=
      (closedFiber_quotient_equiv (R := R) (S := S)).symm.toAlgHom.toAlgebra
    letI : Module ClosedFiber (M ⧸ (𝔪S • (⊤ : Submodule S M))) :=
      Module.compHom (M ⧸ (𝔪S • (⊤ : Submodule S M))) (algebraMap ClosedFiber (S ⧸ 𝔪S))
    ClosedFiberModule ≃ₗ[ClosedFiber] (M ⧸ (𝔪S • (⊤ : Submodule S M))) :=
  let Abar : Type v := S ⧸ 𝔪S
  let _ : Algebra ClosedFiber Abar :=
    (closedFiber_quotient_equiv (R := R) (S := S)).symm.toAlgHom.toAlgebra
  let _ : Module ClosedFiber (M ⧸ (𝔪S • (⊤ : Submodule S M))) :=
    Module.compHom (M ⧸ (𝔪S • (⊤ : Submodule S M))) (algebraMap ClosedFiber Abar)
  let _ : IsScalarTower S ClosedFiber (M ⧸ (𝔪S • (⊤ : Submodule S M))) :=
    -- Proof comment: the `ClosedFiber`-action on the quotient is induced from the quotient-ring
    -- owner `S ⧸ 𝔪S`, so restricting along `S → ClosedFiber` recovers the original `S`-action.
    IsScalarTower.of_algebraMap_smul (R := S) (A := ClosedFiber)
      (M := M ⧸ (𝔪S • (⊤ : Submodule S M))) <|
        fun s x ↦ by
          calc
            (algebraMap ClosedFiber Abar (algebraMap S ClosedFiber s)) • x =
                ((Ideal.Quotient.mk 𝔪S s : Abar) • x) := by
                  change
                    ((closedFiber_quotient_equiv (R := R) (S := S)).symm
                      (algebraMap S ClosedFiber s)) • x =
                        ((Ideal.Quotient.mk 𝔪S s : Abar) • x)
                  simpa using
                    congrArg (fun t : Abar => t • x)
                      (closedFiber_quotient_equiv_symm_algebraMap (R := R) (S := S) s)
            _ = s • x := by
              rw [← ideal_scalar_action_eq_quotient_scalar_action
                (R := S) (I := 𝔪S) (N := M ⧸ (𝔪S • (⊤ : Submodule S M))) s x]
  let eChange : ClosedFiberModule ≃ₗ[S] (Abar ⊗[S] M) :=
    -- Proof comment: first rewrite the left tensor factor `ClosedFiber` as the quotient ring
    -- `S ⧸ 𝔪S`, keeping the source module `M` fixed.
    TensorProduct.congr
      ((closedFiber_quotient_equiv (R := R) (S := S)).symm.toLinearEquiv)
      (LinearEquiv.refl S M)
  let eQuot : (Abar ⊗[S] M) ≃ₗ[Abar] (M ⧸ (𝔪S • (⊤ : Submodule S M))) :=
    -- Proof comment: over the quotient owner, the tensor/quotient comparison is the canonical
    -- `quotTensorEquivQuotSMul` equivalence.
    (TensorProduct.quotTensorEquivQuotSMul M 𝔪S).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  -- Route correction: the earlier version tried to build a custom ClosedFiber-linear owner change.
  -- The stable route is to compose the quotient-owner rewrite with the standard tensor/quotient
  -- equivalence and only then upgrade scalars along the surjective map `S → ClosedFiber`.
  (eChange.trans (LinearEquiv.restrictScalars S eQuot)).extendScalarsOfSurjective
    (closedFiber_algebraMap_surjective (R := R) (S := S))

omit [IsLocalRing S] [IsNoetherianRing S] [IsLocalHom (algebraMap R S)]
  [Module R M] [IsScalarTower R S M] [Module.Finite S M] in
/-- Helper for Lemma 10.99.4: after identifying the `𝔪S`-quotient of the free source with
coefficientwise reduction, the reduced cover is the basis linear-combination map. -/
lemma linearCombination_reduce_mod_eq_basis_cover
    {ι : Type*}
    (b : Module.Basis ι (S ⧸ 𝔪S) (M ⧸ (𝔪S • (⊤ : Submodule S M))))
    (x : ι → M)
    (hx : ∀ i, (Submodule.Quotient.mk (x i) : M ⧸ (𝔪S • (⊤ : Submodule S M))) = b i) :
    let u : (ι →₀ S) →ₗ[S] M := Finsupp.linearCombination S x
    (u.quotientMapByIdeal 𝔪S).comp
        (finsupp_quotient_equiv (R := R) (S := S) ι).symm.toLinearMap =
      (Finsupp.linearCombination (S ⧸ 𝔪S) b).restrictScalars S := by
  -- Route correction: instead of fighting the quotient equivalence abstractly, evaluate on
  -- coefficientwise quotient representatives and rewrite both sides to the same quotient sum.
  dsimp
  let qM : M →ₗ[S] M ⧸ (𝔪S • (⊤ : Submodule S M)) :=
    Submodule.mkQ (𝔪S • (⊤ : Submodule S M))
  let vbar : ι → M ⧸ (𝔪S • (⊤ : Submodule S M)) :=
    fun i => qM (x i)
  let lcQ : (ι →₀ (S ⧸ 𝔪S)) →ₗ[S ⧸ 𝔪S] M ⧸ (𝔪S • (⊤ : Submodule S M)) :=
    Finsupp.linearCombination (S ⧸ 𝔪S) vbar
  apply LinearMap.ext
  intro z
  obtain ⟨l, rfl⟩ := finsupp_quotientMap_surjective (R := S) (I := 𝔪S) ι z
  -- Proof comment: after replacing the inverse quotient equivalence by the quotient class of `l`,
  -- both sides become the same linear combination in the quotient module.
  have hmk :
      (finsupp_quotient_equiv (R := R) (S := S) ι).symm
        (finsupp_quotientMapLinear (R := S) (I := 𝔪S) ι l) =
          Submodule.Quotient.mk l := by
    simpa using
      finsupp_quotient_equiv_symm_apply_quotientMap (R := R) (S := S) (ι := ι) l
  calc
    ((Finsupp.linearCombination S x).quotientMapByIdeal 𝔪S)
        ((finsupp_quotient_equiv (R := R) (S := S) ι).symm
          (finsupp_quotientMapLinear (R := S) (I := 𝔪S) ι l)) =
        (Submodule.Quotient.mk (Finsupp.linearCombination S x l) :
          M ⧸ (𝔪S • (⊤ : Submodule S M))) := by
      rw [hmk]
      simp [LinearMap.quotientMapByIdeal]
    _ = ((Finsupp.linearCombination (S ⧸ 𝔪S) b).restrictScalars S)
          (finsupp_quotientMapLinear (R := S) (I := 𝔪S) ι l) := by
      have hreduce :
          (Submodule.Quotient.mk (Finsupp.linearCombination S x l) :
            M ⧸ (𝔪S • (⊤ : Submodule S M))) =
              (lcQ.restrictScalars S)
                (finsupp_quotientMapLinear (R := S) (I := 𝔪S) ι l) := by
        calc
          (Submodule.Quotient.mk (Finsupp.linearCombination S x l) :
              M ⧸ (𝔪S • (⊤ : Submodule S M))) =
                Finsupp.linearCombination S
                  vbar l := by
            simpa using
              (Finsupp.apply_linearCombination
                (R := S)
                (f := qM)
                (v := x) l)
          _ = (lcQ.restrictScalars S)
                (finsupp_quotientMapLinear (R := S) (I := 𝔪S) ι l) := by
            change _ = ((Finsupp.linearCombination (S ⧸ 𝔪S) vbar).restrictScalars S)
              (finsupp_quotientMapLinear (R := S) (I := 𝔪S) ι l)
            change _ = (finsupp_quotientMapLinear (R := S) (I := 𝔪S) ι l).sum
              (fun i a => a • vbar i)
            rw [Finsupp.linearCombination_apply]
            calc
              l.sum (fun i a => a • vbar i) =
                  l.sum (fun i a => (Ideal.Quotient.mk 𝔪S a : S ⧸ 𝔪S) • vbar i) := by
                refine Finsupp.sum_congr ?_
                intro i hi
                exact ideal_scalar_action_eq_quotient_scalar_action
                  (R := S) (I := 𝔪S)
                  (N := M ⧸ (𝔪S • (⊤ : Submodule S M))) (l i) (vbar i)
              _ = (finsupp_quotientMapLinear (R := S) (I := 𝔪S) ι l).sum
                    (fun i a => a • vbar i) := by
                simpa [finsupp_quotientMapLinear] using
                  (Finsupp.sum_mapRange_index (g := l) (h := fun i a => a • vbar i)
                    (fun i => by simp)).symm
          -- Proof comment: now substitute the chosen lifts `x i` back by the quotient basis `b i`.
      simpa [qM, vbar, lcQ, hx] using hreduce

omit [IsLocalRing S] [IsNoetherianRing S] [IsLocalHom (algebraMap R S)]
  [Module R M] [IsScalarTower R S M] [Module.Finite S M] in
/-- Helper for Lemma 10.99.4: if the chosen lifts map to a basis of the quotient module, then the
reduced free cover is bijective. -/
lemma quotient_cover_bijective_of_basis_lifts
    {ι : Type*}
    (b : Module.Basis ι (S ⧸ 𝔪S) (M ⧸ (𝔪S • (⊤ : Submodule S M))))
    (x : ι → M)
    (hx : ∀ i, (Submodule.Quotient.mk (x i) : M ⧸ (𝔪S • (⊤ : Submodule S M))) = b i) :
    let u : (ι →₀ S) →ₗ[S] M := Finsupp.linearCombination S x
    Function.Bijective (u.quotientMapByIdeal 𝔪S) := by
  dsimp
  let e := finsupp_quotient_equiv (R := R) (S := S) ι
  have hcover :
      (LinearMap.quotientMapByIdeal (Finsupp.linearCombination S x) 𝔪S).comp e.symm.toLinearMap =
        (Finsupp.linearCombination (S ⧸ 𝔪S) b).restrictScalars S :=
    linearCombination_reduce_mod_eq_basis_cover (R := R) (S := S) (M := M) b x hx
  have hbasis_linear :
      (Finsupp.linearCombination (S ⧸ 𝔪S) b).restrictScalars S =
        (LinearEquiv.restrictScalars S b.repr.symm).toLinearMap := by
    -- Proof comment: a basis identifies `linearCombination` with the inverse coordinate map.
    ext l
    simp [b.repr_symm_apply]
  have hcover_bij :
      Function.Bijective
        (((LinearMap.quotientMapByIdeal (Finsupp.linearCombination S x) 𝔪S).comp
          e.symm.toLinearMap)) := by
    -- Proof comment: the composite is just the basis coordinate isomorphism written as
    -- `linearCombination`.
    rw [hcover, hbasis_linear]
    exact (LinearEquiv.restrictScalars S b.repr.symm).bijective
  refine ⟨?_, ?_⟩
  · intro a b hab
    -- Proof comment: compare the images of `e a` and `e b` under the bijective composite.
    apply e.injective
    apply hcover_bij.1
    simpa using hab
  · intro y
    obtain ⟨z, hz⟩ := hcover_bij.2 y
    refine ⟨e.symm z, ?_⟩
    simpa using hz

omit [IsLocalRing S] [IsNoetherianRing S] [IsLocalHom (algebraMap R S)] [Module.Finite S M] in
/-- Helper for Lemma 10.99.4: passing from the `𝔪S`-quotient to the `maximalIdeal R`-quotient
commutes with the free cover. -/
lemma quotient_cover_compare
    {ι : Type*} (x : ι → M) :
    let u : (ι →₀ S) →ₗ[S] M := Finsupp.linearCombination S x
    let eSource := map_maximalIdeal_quotient_equiv (R := R) (S := S) (ι →₀ S)
    let eTarget := map_maximalIdeal_quotient_equiv (R := R) (S := S) M
    eTarget.toLinearMap.comp ((u.quotientMapByIdeal 𝔪S).restrictScalars R) =
      ((u.restrictScalars R).quotientMapByIdeal (maximalIdeal R)).comp eSource.toLinearMap := by
  -- Both routes send the class of a source element to the same class of its image in `M`.
  dsimp
  apply LinearMap.ext
  intro z
  obtain ⟨l, rfl⟩ := Submodule.mkQ_surjective (𝔪S • (⊤ : Submodule S (ι →₀ S))) z
  simp [map_maximalIdeal_quotient_equiv_apply_mk]

/-- Helper for Lemma 10.99.4: a basis of the closed fiber module transports to a basis of the
quotient module `M / 𝔪S M`. -/
noncomputable def quotient_basis_of_closedFiber_basis
    {ι : Type*} (bCF : Module.Basis ι ClosedFiber ClosedFiberModule) :
    Module.Basis ι (S ⧸ 𝔪S) (M ⧸ (𝔪S • (⊤ : Submodule S M))) :=
  let _ : Algebra ClosedFiber (S ⧸ 𝔪S) :=
    (closedFiber_quotient_equiv (R := R) (S := S)).symm.toAlgHom.toAlgebra
  let _ : Module ClosedFiber (M ⧸ (𝔪S • (⊤ : Submodule S M))) :=
    Module.compHom (M ⧸ (𝔪S • (⊤ : Submodule S M)))
      (algebraMap ClosedFiber (S ⧸ 𝔪S))
  let bQCF : Module.Basis ι ClosedFiber (M ⧸ (𝔪S • (⊤ : Submodule S M))) :=
    bCF.map (closed_fiber_module_quotient_equiv (R := R) (S := S) (M := M))
  -- Proof comment: the `ClosedFiber`-action on the quotient was defined via `Module.compHom`
  -- along `ClosedFiber ≃ S ⧸ 𝔪S`, so changing coefficients only unwraps that action.
  bQCF.mapCoeffs (closedFiber_quotient_equiv (R := R) (S := S)).symm fun c x ↦ by
    change ((closedFiber_quotient_equiv (R := R) (S := S)).symm c : S ⧸ 𝔪S) • x =
      (algebraMap ClosedFiber (S ⧸ 𝔪S) c) • x
    rfl

omit [Module.Finite S M] in
/-- Helper for Lemma 10.99.4: if chosen lifts map to a quotient basis, then the induced free cover
is injective. -/
lemma free_cover_injective_of_basis_lifts
    {ι : Type x} [Finite ι] [Module.Flat R M]
    (b : Module.Basis ι (S ⧸ 𝔪S) (M ⧸ (𝔪S • (⊤ : Submodule S M))))
    (x : ι → M)
    (hx : ∀ i, (Submodule.Quotient.mk (x i) : M ⧸ (𝔪S • (⊤ : Submodule S M))) = b i) :
    let u : (ι →₀ S) →ₗ[S] M := Finsupp.linearCombination S x
    Function.Injective u := by
  dsimp
  let u : (ι →₀ S) →ₗ[S] M := Finsupp.linearCombination S x
  have hquot_inj : Function.Injective (u.quotientMapByIdeal 𝔪S) :=
    (quotient_cover_bijective_of_basis_lifts (R := R) (S := S) (M := M) b x hx).1
  let eSource := map_maximalIdeal_quotient_equiv (R := R) (S := S) (ι →₀ S)
  let eTarget := map_maximalIdeal_quotient_equiv (R := R) (S := S) M
  have hmod :
      Function.Injective ((u.restrictScalars R).quotientMapByIdeal (maximalIdeal R)) := by
    -- Proof comment: the quotient comparison transports injectivity from the `𝔪S`-model to the
    -- `maximalIdeal R`-model through quotient equivalences.
    have hcompare :
        ((u.restrictScalars R).quotientMapByIdeal (maximalIdeal R)).comp eSource.toLinearMap =
          eTarget.toLinearMap.comp ((u.quotientMapByIdeal 𝔪S).restrictScalars R) := by
      simpa [u, eSource, eTarget] using
        (quotient_cover_compare (R := R) (S := S) (M := M) (x := x)).symm
    exact injective_of_ladder_linearEquiv (R := R) hcompare hquot_inj
  let uLift :
      ULift.{max x v w} (ι →₀ S) →ₗ[R] ULift.{max x v w} M :=
    (ULift.moduleEquiv (R := R) (M := M)).symm.toLinearMap.comp
      ((u.restrictScalars R).comp
        (ULift.moduleEquiv (R := R) (M := ι →₀ S)).toLinearMap)
  let eSourceLift :
      ((ULift.{max x v w} (ι →₀ S)) ⧸
        (maximalIdeal R • (⊤ : Submodule R (ULift.{max x v w} (ι →₀ S))))) ≃ₗ[R]
        ((ι →₀ S) ⧸ (maximalIdeal R • (⊤ : Submodule R (ι →₀ S)))) :=
    Submodule.Quotient.equiv
      (maximalIdeal R • (⊤ : Submodule R (ULift.{max x v w} (ι →₀ S))))
      (maximalIdeal R • (⊤ : Submodule R (ι →₀ S)))
      (ULift.moduleEquiv (R := R) (M := ι →₀ S))
      (by simpa [Submodule.map_smul''])
  let eTargetLift :
      ((ULift.{max x v w} M) ⧸ (maximalIdeal R • (⊤ : Submodule R (ULift.{max x v w} M)))) ≃ₗ[R]
        (M ⧸ (maximalIdeal R • (⊤ : Submodule R M))) :=
    Submodule.Quotient.equiv
      (maximalIdeal R • (⊤ : Submodule R (ULift.{max x v w} M)))
      (maximalIdeal R • (⊤ : Submodule R M))
      (ULift.moduleEquiv (R := R) (M := M))
      (by simpa [Submodule.map_smul''])
  have hcompareLift :
      ((u.restrictScalars R).quotientMapByIdeal (maximalIdeal R)).comp eSourceLift.toLinearMap =
        eTargetLift.toLinearMap.comp (uLift.quotientMapByIdeal (maximalIdeal R)) := by
    -- Proof comment: quotienting commutes with the `ULift.moduleEquiv` identifications.
    apply LinearMap.ext
    intro z
    obtain ⟨l, rfl⟩ := Submodule.mkQ_surjective
      (maximalIdeal R • (⊤ : Submodule R (ULift.{max x v w} (ι →₀ S)))) z
    simp [uLift, eSourceLift, eTargetLift]
  have hcompareLift' :
      (uLift.quotientMapByIdeal (maximalIdeal R)).comp eSourceLift.symm.toLinearMap =
        eTargetLift.symm.toLinearMap.comp ((u.restrictScalars R).quotientMapByIdeal (maximalIdeal R)) := by
    apply LinearMap.ext
    intro z
    have hz := LinearMap.congr_fun hcompareLift (eSourceLift.symm z)
    simpa [LinearMap.comp_apply] using
      (congrArg eTargetLift.symm.toLinearMap hz).symm
  have hmodLift :
      Function.Injective (uLift.quotientMapByIdeal (maximalIdeal R)) := by
    exact injective_of_ladder_linearEquiv (R := R) hcompareLift' hmod
  letI : Module.Flat R (ULift.{max x v w} M) := by infer_instance
  have huLift_inj : Function.Injective uLift := by
    -- Proof comment: Lemma `10.99.1` applies after the universe lift because source and target
    -- now live in a common owner universe.
    exact
      injective_of_mod_maximalIdeal_injective
        (R := R) (S := S)
        (M := ULift.{max x v w} M)
        (N := ULift.{max x v w} (ι →₀ S)) uLift hmodLift
  -- Proof comment: transport the resulting injectivity back down along `ULift.moduleEquiv`.
  intro a b hab
  have : uLift (ULift.up a) = uLift (ULift.up b) := by
    simpa [uLift, hab]
  simpa using huLift_inj this

omit [IsNoetherianRing S] [Module R M] [IsScalarTower R S M] in
/-- Helper for Lemma 10.99.4: if chosen lifts map to a quotient basis, then the induced free cover
is surjective. -/
lemma free_cover_surjective_of_basis_lifts
    {ι : Type*}
    (b : Module.Basis ι (S ⧸ 𝔪S) (M ⧸ (𝔪S • (⊤ : Submodule S M))))
    (x : ι → M)
    (hx : ∀ i, (Submodule.Quotient.mk (x i) : M ⧸ (𝔪S • (⊤ : Submodule S M))) = b i) :
    let u : (ι →₀ S) →ₗ[S] M := Finsupp.linearCombination S x
    Function.Surjective u := by
  dsimp
  let u : (ι →₀ S) →ₗ[S] M := Finsupp.linearCombination S x
  have hquot_surj : Function.Surjective (u.quotientMapByIdeal 𝔪S) :=
    (quotient_cover_bijective_of_basis_lifts (R := R) (S := S) (M := M) b x hx).2
  have h𝔪S_jac : 𝔪S ≤ Ring.jacobson S := by
    simpa [IsLocalRing.ringJacobson_eq_maximalIdeal] using
      (IsLocalRing.map_maximalIdeal_le (algebraMap R S))
  -- Proof comment: this is the Nakayama step from the source proof, applied to the free cover.
  exact
    surjective_of_quotientMap_surjective_of_le_ring_jacobson
      (I := 𝔪S) u hquot_surj h𝔪S_jac

/-- Helper for Lemma 10.99.4: the restricted-scalars `R`-module on `M` is definitionally the same
as the ambient `R`-module used in the local-flatness hypotheses. -/
noncomputable def restrictScalars_linearEquiv :
    RestrictScalars R S M ≃ₗ[R] M :=
  -- Proof comment: `RestrictScalars` only changes which scalar structure Lean remembers; the
  -- underlying additive group and `R`-action are unchanged.
  { toAddEquiv := RestrictScalars.addEquiv R S M
    map_smul' := by
      intro a m
      simpa using RestrictScalars.addEquiv_map_smul (R := R) (S := S) (M := M) a m }

-- Proof sketch: choose lifts in `M` of a basis of the closed fiber module
-- `ClosedFiberModule = ClosedFiber ⊗[S] M`, equivalently
-- `M ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M))`, yielding an
-- `S`-linear map `S^n → M`. The induced map on the closed fiber is bijective because the chosen
-- images form a basis there, so Lemma 10.99.1 gives injectivity upstairs. Nakayama's lemma gives
-- surjectivity, and hence `M` is free over `S`.
/-- Lemma 10.99.4 (1): if the closed fiber module `ClosedFiber ⊗[S] M`, equivalently
`M ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M))`, is free over the closed
fiber ring `ClosedFiber = (maximalIdeal R).Fiber S` and `M` is flat over `R`, then `M` is free
over `S`. -/
@[stacks 00MH]
theorem free_of_flat_of_free_closedFiber [Module.Flat R M] [Module.Free ClosedFiber ClosedFiberModule] :
    Module.Free S M := by
  classical
  letI : Nontrivial (S ⧸ 𝔪S) :=
    Ideal.Quotient.nontrivial_iff.mpr (IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S)).ne
  letI : Nontrivial ClosedFiber :=
    (closedFiber_quotient_equiv (R := R) (S := S)).symm.toRingEquiv.toEquiv.nontrivial
  let ι := Module.Free.ChooseBasisIndex ClosedFiber ClosedFiberModule
  let bCF : Module.Basis ι ClosedFiber ClosedFiberModule :=
    Module.Free.chooseBasis ClosedFiber ClosedFiberModule
  letI : Finite ι := Module.Finite.finite_basis bCF
  letI : Module.Finite S (ι →₀ S) := by infer_instance
  let bQ : Module.Basis ι (S ⧸ 𝔪S) (M ⧸ (𝔪S • (⊤ : Submodule S M))) :=
    quotient_basis_of_closedFiber_basis (R := R) (S := S) (M := M) bCF
  let x : ι → M := fun i ↦
    Classical.choose (Submodule.mkQ_surjective (𝔪S • (⊤ : Submodule S M)) (bQ i))
  have hx : ∀ i, (Submodule.Quotient.mk (x i) : M ⧸ (𝔪S • (⊤ : Submodule S M))) = bQ i := by
    intro i
    exact Classical.choose_spec
      (Submodule.mkQ_surjective (𝔪S • (⊤ : Submodule S M)) (bQ i))
  let u : (ι →₀ S) →ₗ[S] M := Finsupp.linearCombination S x
  -- Proof comment: the chosen lifts give the textbook free cover `u : S^{⊕ι} → M`.
  have hu_inj : Function.Injective u := by
    simpa [u] using
      free_cover_injective_of_basis_lifts (R := R) (S := S) (M := M) bQ x hx
  have hu_surj : Function.Surjective u := by
    simpa [u] using
      free_cover_surjective_of_basis_lifts (R := R) (S := S) (M := M) bQ x hx
  -- Proof comment: once the free cover is bijective, transport the standard free structure on the
  -- source `ι →₀ S` across the resulting linear equivalence.
  exact Module.Free.of_equiv' inferInstance (LinearEquiv.ofBijective u ⟨hu_inj, hu_surj⟩)

-- Proof sketch: part (1) makes `M` into a free `S`-module. Because `M` is nontrivial, a nonzero
-- free `S`-module is faithfully flat over `S`; then apply Lemma 10.39.10 to descend the given
-- `R`-flatness of `M` to flatness of the algebra map `R → S`.
/-- Lemma 10.99.4 (2): if the closed fiber module `ClosedFiber ⊗[S] M`, equivalently
`M ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M))`, is free over the closed
fiber ring `ClosedFiber = (maximalIdeal R).Fiber S`, `M` is flat over `R`, and `M` is nonzero,
then the local homomorphism `R → S` is flat. -/
@[stacks 00MH]
theorem algebraMap_flat_of_nontrivial_flat_module_of_free_closedFiber
    [Nontrivial M] [Module.Flat R M] [Module.Free ClosedFiber ClosedFiberModule] :
    (algebraMap R S).Flat := by
  letI : Module.Free S M :=
    free_of_flat_of_free_closedFiber (R := R) (S := S) (M := M)
  letI : Module.FaithfullyFlat S M := by infer_instance
  letI : Module.Flat R (RestrictScalars R S M) := by
    -- Proof comment: the restricted-scalars `R`-module is exactly the given flat module `M`.
    exact Module.Flat.of_linearEquiv (restrictScalars_linearEquiv (R := R) (S := S) (M := M))
  -- Proof comment: with `M` free and nontrivial over `S`, faithful flatness is automatic, so
  -- Lemma `10.39.10` descends the given `R`-flatness of `M` to flatness of `R → S`.
  exact algebraMap_flat_of_flat_of_faithfullyFlat (R := R) (S := S) (M := M)

end
