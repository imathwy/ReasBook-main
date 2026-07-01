import Mathlib
import stacks_project.Chap10.Lemma_10_39_9
import stacks_project.Chap10.Lemma_10_39_18

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w x y

section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {R : Type u} {S : Type v} {R' : Type w} {S' : Type x}
variable [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
variable [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S']
variable (W : Submonoid (S ⊗[R] R'))
variable [Algebra (S ⊗[R] R') S']
variable [IsScalarTower S (S ⊗[R] R') S'] [IsScalarTower R' (S ⊗[R] R') S']
variable [IsLocalization W S']

variable {M : Type y} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/- Domain triage:
- primary domain: commutative algebra of flatness under base change, localization, and descent;
- source-facing layer: the four Stacks implications comparing flatness of `M` with flatness of the
  textbook base-changed module `S' ⊗[S] M`;
- core/canonical owner: `Module.Flat`, `Module.FaithfullyFlat`, `Module.Flat.trans`,
  `Module.Flat.of_isLocalizedModule`, `IsLocalization.flat`, and
  `Module.FaithfullyFlat.of_flat_of_isLocalHom`;
- bridge/view: the identification of `S' ⊗[S] M` with the localization of the canonical
  base-change over `S ⊗[R] R'`.

The public items stay source-facing. The refinement only trims redundant ambient hypotheses:
parts `(1)` and `(3)` need only base change plus localization, while parts `(2)` and `(4)` add
exactly the local-hom hypotheses needed for faithful-flat descent along `S → S'`.
-/

/-- Helper for Lemma 10.100.1: the public tensor module `S' ⊗[S] M` is the localization of the
canonical base-change module `(S ⊗[R] R') ⊗[S] M` at `W`. -/
noncomputable def tensor_localizedModule_equiv :
    S' ⊗[S] M ≃ₗ[R'] LocalizedModule W ((S ⊗[R] R') ⊗[S] M) := by
  let e :
      S' ⊗[S ⊗[R] R'] ((S ⊗[R] R') ⊗[S] M) ≃ₗ[S ⊗[R] R'] S' ⊗[S] M :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange S (S ⊗[R] R') S' S' M).restrictScalars
      (S ⊗[R] R')
  let f :
      ((S ⊗[R] R') ⊗[S] M) →ₗ[S ⊗[R] R'] S' ⊗[S] M :=
    e.toLinearMap.comp (TensorProduct.mk (S ⊗[R] R') S' ((S ⊗[R] R') ⊗[S] M) 1)
  letI : IsLocalizedModule W f := by
    letI :
        IsLocalizedModule W
          (TensorProduct.mk (S ⊗[R] R') S' ((S ⊗[R] R') ⊗[S] M) 1) :=
      inferInstance
    exact IsLocalizedModule.of_linearEquiv (S := W)
      (f := TensorProduct.mk (S ⊗[R] R') S' ((S ⊗[R] R') ⊗[S] M) 1) e
  -- This is the source identity `M' = W⁻¹((S ⊗[R] R') ⊗[S] M)` packaged as a reusable equivalence.
  exact
    (IsLocalizedModule.linearEquiv W f
      (LocalizedModule.mkLinearMap W ((S ⊗[R] R') ⊗[S] M))).restrictScalars R'

/-- Helper for Lemma 10.100.1: an `R`-module linearly equivalent to a localization of an
`R`-flat `A`-module is flat over `R`. -/
theorem flat_of_linearEquiv_localizedModule
    {R₀ : Type*} [CommRing R₀] {A : Type*} [CommRing A] [Algebra R₀ A] {T : Submonoid A}
    {N : Type*} [AddCommGroup N] [Module R₀ N] [Module A N] [IsScalarTower R₀ A N]
    {N' : Type*} [AddCommGroup N'] [Module R₀ N']
    (e : N' ≃ₗ[R₀] LocalizedModule T N) (hN : Module.Flat R₀ N) : Module.Flat R₀ N' := by
  letI : Module.Flat R₀ (LocalizedModule T N) :=
    flat_localizedModule_of_flat (R := R₀) (A := A) (M := N) T hN
  exact Module.Flat.of_linearEquiv e

/-- Helper for Lemma 10.100.1: the localized tensor-product ring `S'` is linearly equivalent,
after restricting scalars to `S`, to the canonical localization of `S ⊗[R] R'` at `W`. -/
noncomputable def localized_ring_linearEquiv :
    S' ≃ₗ[S] LocalizedModule W (S ⊗[R] R') :=
  (IsLocalizedModule.linearEquiv W (Algebra.linearMap (S ⊗[R] R') S')
    (LocalizedModule.mkLinearMap W (S ⊗[R] R'))).restrictScalars S

include W

-- Proof sketch: first base change the `R`-flat `S`-module `M` along `R → R'` to obtain an
-- `R'`-flat module over `S ⊗[R] R'`; then identify `S' ⊗[S] M` with the localization of that
-- base change along the localization map `(S ⊗[R] R') → S'`, and use that localization preserves
-- flatness.
/-- Lemma 10.100.1 (1): if `M` is flat over `R`, then after forming
`M' = S' ⊗[S] M`, the module `M'` is flat over `R'`, provided `S'` is a localization of
`S ⊗[R] R'`. -/
-- TODO: follow the source route `R' ⊗[R] M` flat over `R'` -> `(S ⊗[R] R') ⊗[S] M` flat over
-- `R'` -> localize along `W` and transport the resulting `R'`-flatness to `S' ⊗[S] M`.
theorem flat_tensorProduct_of_flat_of_isLocalization_tensorProduct
    (hM : Module.Flat R M) : Module.Flat R' (S' ⊗[S] M) := by
  let eBase :
      ((S ⊗[R] R') ⊗[S] M) ≃ₗ[R'] R' ⊗[R] M :=
    Algebra.IsPushout.cancelBaseChange R R' S (S ⊗[R] R') M
  have hBaseChange : Module.Flat R' ((S ⊗[R] R') ⊗[S] M) := by
    -- First perform the textbook base change `M ⊗[R] R'`.
    letI : Module.Flat R M := hM
    have hTensor : Module.Flat R' (R' ⊗[R] M) :=
      Module.Flat.baseChange (R := R) (S := R') (M := M)
    -- Then rewrite it into the pushout model over `S ⊗[R] R'`.
    letI : Module.Flat R' (R' ⊗[R] M) := hTensor
    exact Module.Flat.of_linearEquiv eBase
  -- Transport the localized flatness back to the public tensor-product model.
  exact flat_of_linearEquiv_localizedModule
    (e := tensor_localizedModule_equiv (R := R) (S := S) (R' := R') (S' := S') (W := W) (M := M))
    hBaseChange

/-- Helper for Lemma 10.100.1: if `R → R'` is flat, then `S → S'` is flat by base changing to
`S ⊗[R] R'` and then localizing at `W`. -/
theorem flat_target_over_source_of_flat_baseChange
    (hR' : Module.Flat R R') : Module.Flat S S' := by
  let _ : Algebra R' S' := inferInstance
  let _ : IsScalarTower R' (S ⊗[R] R') S' := inferInstance
  have hTensor : Module.Flat S (S ⊗[R] R') := by
    -- The reflected source route first base changes the flat `R`-module `R'` along `R → S`.
    letI : Module.Flat R R' := hR'
    exact Module.Flat.baseChange (R := R) (S := S) (M := R')
  let e := localized_ring_linearEquiv (R := R) (S := S) (R' := R') (S' := S') (W := W)
  exact flat_of_linearEquiv_localizedModule (R₀ := S) (e := e) hTensor

-- Proof sketch: use part (1) with `M := S` to show that `S → S'` is flat when `R → R'` is flat;
-- because `S → S'` is also a local homomorphism of local rings, it is faithfully flat. Then apply
-- faithfully flat descent for flatness along `S → S'` to descend flatness of `S' ⊗[S] M` back to
-- flatness of `M` over `R`.
/-- Lemma 10.100.1 (2): if `M' = S' ⊗[S] M` is flat over `R'` and `R'` is flat over `R`, then
`M` is flat over `R`. -/
-- TODO: follow the source route via faithfully flat descent for injectivity: first obtain
-- faithful flatness of `S → S'`, then reflect injectivity of `I.subtype.lTensor M` from the
-- tensorized map over `S'`, identified with the corresponding `R'`-flat map on `S' ⊗[S] M`.
theorem flat_of_flat_tensorProduct_of_isLocalization_tensorProduct
    [IsLocalRing S] [IsLocalRing S'] [IsLocalHom (algebraMap S S')]
    (hM' : Module.Flat R' (S' ⊗[S] M)) (hR' : Module.Flat R R') :
    Module.Flat R M := by
  have hSS' : Module.Flat S S' :=
    flat_target_over_source_of_flat_baseChange (R := R) (S := S) (R' := R') (S' := S') (W := W)
      hR'
  letI : Module.Flat S S' := hSS'
  letI : Module.FaithfullyFlat S S' := Module.FaithfullyFlat.of_flat_of_isLocalHom
  letI : Algebra R S' := RingHom.toAlgebra ((algebraMap S S').comp (algebraMap R S))
  letI : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq fun r ↦ rfl
  letI : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq fun r ↦ by
    have hleft :
        (algebraMap R S') r =
          (algebraMap (S ⊗[R] R') S')
            ((Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] R') ((algebraMap R S) r)) := by
      exact
        (congrArg (fun h : R →+* S' ↦ h r) (IsScalarTower.algebraMap_eq R S S')).trans
          (congrArg (fun h : S →+* S' ↦ h ((algebraMap R S) r))
            (IsScalarTower.algebraMap_eq S (S ⊗[R] R') S'))
    have hbase :
        (algebraMap (S ⊗[R] R') S')
            ((Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] R') ((algebraMap R S) r)) =
          (algebraMap (S ⊗[R] R') S')
            ((Algebra.TensorProduct.includeRight : R' →ₐ[R] S ⊗[R] R') ((algebraMap R R') r)) := by
      simpa using
        congrArg
          (fun h : R →+* S ⊗[R] R' ↦ h r)
          (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := R) (A := S) (B := R'))
    have hright :
        (algebraMap R' S') ((algebraMap R R') r) =
          (algebraMap (S ⊗[R] R') S')
            ((Algebra.TensorProduct.includeRight : R' →ₐ[R] S ⊗[R] R') ((algebraMap R R') r)) := by
      exact congrArg (fun h : R' →+* S' ↦ h ((algebraMap R R') r))
        (IsScalarTower.algebraMap_eq R' (S ⊗[R] R') S')
    exact hleft.trans (hbase.trans hright.symm)
  have hM'_over_R : Module.Flat R (S' ⊗[S] M) := by
    -- The upper-right module is already flat over `R'`, and flatness composes along `R → R'`.
    letI : Module.Flat R R' := hR'
    letI : Module.Flat R' (S' ⊗[S] M) := hM'
    letI : IsScalarTower R R' (S' ⊗[S] M) := IsScalarTower.of_algebraMap_smul fun r x ↦ by
      have hleft :
          (algebraMap R' S' ((algebraMap R R') r)) • x = ((algebraMap R R') r) • x := by
        simpa using IsScalarTower.algebraMap_smul (R := R') (A := S') ((algebraMap R R') r) x
      have hmid :
          (algebraMap R' S' ((algebraMap R R') r)) • x = (algebraMap R S') r • x := by
        rw [IsScalarTower.algebraMap_eq R R' S']
        rfl
      have hright : (algebraMap R S') r • x = r • x := by
        simpa using IsScalarTower.algebraMap_smul (R := R) (A := S') r x
      exact hleft.symm.trans (hmid.trans hright)
    exact Module.Flat.trans (R := R) (S := R') (M := S' ⊗[S] M)
  -- Route correction: rather than redoing the associativity ladder here, invoke the earlier
  -- faithfully flat base-change descent lemma for `R`-flatness along `S → S'`.
  exact (flat_iff_flat_baseChange_of_faithfullyFlat (R := R) (S := S) (S' := S') (M := M)).mpr
    hM'_over_R

-- Proof sketch: specialize part (1) to the `S`-module `M := S`; then `S' ⊗[S] S` identifies with
-- `S'`, so flatness of `S` over `R` ascends to flatness of `S'` over `R'`.
/-- Lemma 10.100.1 (3): if `S` is flat over `R`, then `S'` is flat over `R'`. -/
theorem flat_target_of_flat_source_of_isLocalization_tensorProduct
    (hS : Module.Flat R S) : Module.Flat R' S' := by
  -- Specialize part `(1)` to the source algebra itself.
  have hTensor : Module.Flat R' (S' ⊗[S] S) :=
    flat_tensorProduct_of_flat_of_isLocalization_tensorProduct
      (S' := S') (W := W) (M := S) hS
  -- The canonical right-unitor identifies `S' ⊗[S] S` with `S'`.
  let e : S' ≃ₗ[R'] S' ⊗[S] S :=
    (TensorProduct.AlgebraTensorModule.rid S S' S').symm.restrictScalars R'
  letI : Module.Flat R' (S' ⊗[S] S) := hTensor
  exact Module.Flat.of_linearEquiv e

-- Proof sketch: specialize part (2) to the `S`-module `M := S`; then `S' ⊗[S] S` is canonically
-- `S'`, so flatness of `R' → S'` together with flatness of `R → R'` descends to flatness of
-- `R → S`.
/-- Lemma 10.100.1 (4): if `R' → S'` is flat and `R → R'` is flat, then `S` is flat over `R`.
-/
theorem flat_source_of_flat_target_of_isLocalization_tensorProduct
    [IsLocalRing S] [IsLocalRing S'] [IsLocalHom (algebraMap S S')]
    (hS' : Module.Flat R' S') (hR' : Module.Flat R R') : Module.Flat R S := by
  -- Transport the flat target module to the tensor-product model needed by part `(2)`.
  let e : (S' ⊗[S] S) ≃ₗ[R'] S' :=
    (TensorProduct.AlgebraTensorModule.rid S S' S').restrictScalars R'
  have hTensor : Module.Flat R' (S' ⊗[S] S) :=
    letI : Module.Flat R' S' := hS'
    Module.Flat.of_linearEquiv e
  -- Specializing part `(2)` to `M := S` descends flatness back to the source.
  exact flat_of_flat_tensorProduct_of_isLocalization_tensorProduct
    (S' := S') (W := W) (M := S) hTensor hR'

end
