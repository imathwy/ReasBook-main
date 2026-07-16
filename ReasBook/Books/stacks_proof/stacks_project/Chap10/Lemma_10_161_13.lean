import Mathlib
import stacks_proof.stacks_project.Chap09.Lemma_9_12_8
import stacks_proof.stacks_project.Chap10.Lemma_10_37_12
import stacks_proof.stacks_project.Chap10.Lemma_10_37_14
import stacks_proof.stacks_project.Chap10.Lemma_10_42_4
import stacks_proof.stacks_project.Chap10.Lemma_10_161_7
import stacks_proof.stacks_project.Chap10.Lemma_10_161_11
import stacks_proof.stacks_project.Chap10.Lemma_10_161_12

-- Declarations for this item will be appended below by the statement pipeline.

open scoped RatFunc

universe u

section

/-
Domain triage:
* primary domain: commutative algebra of the `N-1` and `N-2` conditions under polynomial
  extension;
* sampled owner/bridge declarations:
  - `IsN1Ring` and `IsN2Ring`, the source-facing owner classes from `Definition 10.161.1`;
  - `isNormalRing_polynomial`, the canonical polynomial normality theorem from `Lemma 10.37.14`;
  - `isN1Ring_iff_isN2Ring_of_noetherian_of_fractionRing_charZero`, the characteristic-zero
    bridge from `Lemma 10.161.11`;
  - `isN2Ring_iff_integralClosure_finite_for_finite_purelyInseparable_extensions`, the
    positive-characteristic bridge from `Lemma 10.161.12`.
* layer triage:
  - `source-facing`: the two polynomial stability theorems below;
  - `core/canonical`: the owner classes `IsN1Ring` and `IsN2Ring`;
  - `bridge/view`: polynomial normality and the characteristic-zero/positive-characteristic
    comparison theorems listed above, together with finite-extension descent from `Lemma 10.161.7`.

Primitive data are only the Noetherian domain `R` and the owner hypotheses `IsN1Ring R` or
`IsN2Ring R`. Normality of the normalization, polynomial normality, and the characteristic-case
reductions are derived API, so they should stay in the proof layer rather than being repackaged as
new public data in this file.
-/

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]

/-- Helper for Lemma 10.161.13: a finite coefficient extension `R ⊂ S` induces a finite
polynomial coefficient map `R[X] → S[X]`. -/
lemma polynomial_mapRingHom_finite_of_moduleFinite
    {S : Type u} [CommRing S] [Algebra R S] [Module.Finite R S] :
    (Polynomial.mapRingHom (algebraMap R S)).Finite := by
  let f : Polynomial R →+* Polynomial S := Polynomial.mapRingHom (algebraMap R S)
  letI : Algebra (Polynomial R) (Polynomial S) := f.toAlgebra
  change Module.Finite (Polynomial R) (Polynomial S)
  rw [Module.finite_def, Submodule.fg_iff_exists_fin_generating_family]
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := R) (M := S)
  refine ⟨n, fun i ↦ Polynomial.C (g i), ?_⟩
  apply top_le_iff.mp
  intro p hp
  clear hp
  -- Every polynomial is built from monomials, so it suffices to control one coefficient at a time.
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      -- The span is closed under addition, so the induction hypotheses combine directly.
      exact Submodule.add_mem _ hp hq
  | monomial k a =>
      have ha : a ∈ Submodule.span R (Set.range g) := by
        simpa [hg] using (show a ∈ (⊤ : Submodule R S) from trivial)
      have hC :
          Polynomial.C a ∈
            Submodule.span (Polynomial R) (Set.range fun i : Fin n ↦ Polynomial.C (g i)) := by
        -- Expand the coefficient `a` in the chosen finite `R`-spanning family and then apply `C`.
        rcases (Submodule.mem_span_range_iff_exists_fun R).1 ha with ⟨c, hc⟩
        refine (Submodule.mem_span_range_iff_exists_fun (Polynomial R)).2 ?_
        refine ⟨fun i ↦ Polynomial.C (c i), ?_⟩
        simpa [Algebra.smul_def, hc] using congrArg (Polynomial.C : S → Polynomial S) hc
      have hmono :
          (Polynomial.X ^ k : Polynomial R) • Polynomial.C a ∈
            Submodule.span (Polynomial R) (Set.range fun i : Fin n ↦ Polynomial.C (g i)) :=
        Submodule.smul_mem _ (Polynomial.X ^ k) hC
      -- Multiplying the constant polynomial `C a` by `X^k` recovers the monomial `a * X^k`.
      simpa [Algebra.smul_def, Polynomial.X_pow_mul_C, Polynomial.C_mul_X_pow_eq_monomial] using
        hmono

/-- Helper for Lemma 10.161.13: substituting `X ^ q` for `X` gives a finite polynomial
endomorphism. -/
lemma qth_power_variable_map_finite
    {A : Type u} [CommRing A] [Nontrivial A] {q : ℕ} (hq : 0 < q) :
    (Polynomial.eval₂RingHom Polynomial.C (Polynomial.X ^ q : Polynomial A)).Finite := by
  let f : Polynomial A →ₐ[A] Polynomial A := Polynomial.aeval (Polynomial.X ^ q : Polynomial A)
  letI : Algebra (Polynomial A) (Polynomial A) := f.toRingHom.toAlgebra
  have hroot :
      IsIntegral (Polynomial A) (Polynomial.X : Polynomial A) := by
    -- The target generator `X` satisfies the monic relation `T^q - X` over the source ring.
    refine ⟨Polynomial.X ^ q - Polynomial.C Polynomial.X, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub_C Polynomial.X (Nat.ne_of_gt hq)
    · change
        Polynomial.eval₂ (algebraMap (Polynomial A) (Polynomial A)) Polynomial.X
          (Polynomial.X ^ q - Polynomial.C Polynomial.X) = 0
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
      have hX : algebraMap (Polynomial A) (Polynomial A) Polynomial.X = Polynomial.X ^ q := by
        change f Polynomial.X = Polynomial.X ^ q
        simp [f, Polynomial.aeval_X]
      simpa [hX]
  have hadjoin :
      Algebra.adjoin (Polynomial A) ({Polynomial.X} : Set (Polynomial A)) = ⊤ := by
    -- Every target polynomial already lies in the algebra generated by the single element `X`.
    apply Algebra.eq_top_iff.2
    intro p
    refine Polynomial.induction_on' p ?_ ?_
    · intro p₁ p₂ hp₁ hp₂
      exact Subalgebra.add_mem _ hp₁ hp₂
    · intro n a
      have hC :
          Polynomial.C a ∈ Algebra.adjoin (Polynomial A) ({Polynomial.X} : Set (Polynomial A)) := by
        have hCa :
            algebraMap (Polynomial A) (Polynomial A) (Polynomial.C a) = Polynomial.C a := by
          change f (Polynomial.C a) = Polynomial.C a
          exact f.commutes a
        have hbase :
            algebraMap (Polynomial A) (Polynomial A) (Polynomial.C a) ∈
              Algebra.adjoin (Polynomial A) ({Polynomial.X} : Set (Polynomial A)) :=
          (Algebra.adjoin (Polynomial A) ({Polynomial.X} : Set (Polynomial A))).algebraMap_mem
            (Polynomial.C a)
        exact hCa ▸ hbase
      have hX :
          Polynomial.X ∈ Algebra.adjoin (Polynomial A) ({Polynomial.X} : Set (Polynomial A)) :=
        Algebra.subset_adjoin (by simp)
      simpa [Polynomial.C_mul_X_pow_eq_monomial] using
        Subalgebra.mul_mem _ hC (Subalgebra.pow_mem _ hX n)
  have hfinite_top : Module.Finite (Polynomial A) (Polynomial A) := by
    -- Once `X` is integral over the source image, the whole target is finite over the adjoin.
    letI :
        Module.Finite (Polynomial A)
          (Algebra.adjoin (Polynomial A) ({Polynomial.X} : Set (Polynomial A))) :=
      Algebra.finite_adjoin_simple_of_isIntegral hroot
    letI :
        Module.Finite (Polynomial A) (⊤ : Subalgebra (Polynomial A) (Polynomial A)) :=
      Module.Finite.equiv
        (Subalgebra.equivOfEq _ _ hadjoin).toLinearEquiv
    exact Module.Finite.equiv
      (Subalgebra.topEquiv : (⊤ : Subalgebra (Polynomial A) (Polynomial A)) ≃ₐ[Polynomial A]
        Polynomial A).toLinearEquiv
  simpa [f, Polynomial.aeval_def, AlgHom.Finite, RingHom.Finite] using hfinite_top

/-- Helper for Lemma 10.161.13: after a finite coefficient extension `R ⊂ S`, the twisted
polynomial map sending `X` to `X ^ q` is still finite. -/
lemma twisted_polynomial_map_finite
    {S : Type u} [CommRing S] [Nontrivial S] [Algebra R S] [Module.Finite R S]
    {q : ℕ} (hq : 0 < q) :
    (Polynomial.eval₂RingHom (Polynomial.C.comp (algebraMap R S))
      (Polynomial.X ^ q : Polynomial S)).Finite := by
  let coeffMap : Polynomial R →+* Polynomial S := Polynomial.mapRingHom (algebraMap R S)
  have hcoeff :
      @RingHom.Finite (Polynomial R) (Polynomial S) inferInstance inferInstance coeffMap := by
    -- The coefficient extension is already finite on polynomial rings.
    simpa [coeffMap] using
      (polynomial_mapRingHom_finite_of_moduleFinite (R := R) (S := S))
  have hsub :
      @RingHom.Finite (Polynomial S) (Polynomial S) inferInstance inferInstance
        ((Polynomial.aeval (R := S) (A := Polynomial S) (Polynomial.X ^ q : Polynomial S)).toRingHom) := by
    -- The source proof's `X ↦ X^q` substitution is finite by the previous helper.
    simpa [AlgHom.Finite, RingHom.Finite] using
      (qth_power_variable_map_finite (A := S) hq)
  have hcomp :
      (Polynomial.aeval (R := S) (A := Polynomial S)
        (Polynomial.X ^ q : Polynomial S)).toRingHom.comp coeffMap =
        Polynomial.eval₂RingHom (Polynomial.C.comp (algebraMap R S))
          (Polynomial.X ^ q : Polynomial S) := by
    -- Both ring maps agree on coefficients and on the variable `X`.
    ext a <;> simp [coeffMap, Polynomial.aeval_def]
  -- Compose the finite coefficient map with the finite `X ↦ X^q` substitution.
  rw [← hcomp]
  exact RingHom.Finite.comp hsub hcoeff

/-- Helper for Lemma 10.161.13: the twisted coefficient/variable map makes `S[X]` a finite
`R[X]`-module. -/
lemma twisted_polynomial_moduleFinite
    {S : Type u} [CommRing S] [Nontrivial S] [Algebra R S] [Module.Finite R S]
    {q : ℕ} (hq : 0 < q) :
    let f : Polynomial R →+* Polynomial S :=
      Polynomial.eval₂RingHom (Polynomial.C.comp (algebraMap R S))
        (Polynomial.X ^ q : Polynomial S)
    let _ : Algebra (Polynomial R) (Polynomial S) := f.toAlgebra
    Module.Finite (Polynomial R) (Polynomial S) := by
  let f : Polynomial R →+* Polynomial S :=
    Polynomial.eval₂RingHom (Polynomial.C.comp (algebraMap R S))
      (Polynomial.X ^ q : Polynomial S)
  letI : Algebra (Polynomial R) (Polynomial S) := f.toAlgebra
  letI : Module (Polynomial R) (Polynomial S) := RingHom.toModule f
  -- Reuse the finite twisted-map package so later proofs can work directly with module finiteness.
  letI : Module.Finite (Polynomial R) (Polynomial S) := by
    simpa [f, RingHom.Finite] using
      (twisted_polynomial_map_finite (R := R) (S := S) hq)
  infer_instance

/-- Helper for Lemma 10.161.13: if `S` is integrally closed and finite over `R`, then the twisted
polynomial ring `S[X]` is the integral closure of `R[X]` in its own fraction field. -/
lemma twisted_polynomial_isIntegralClosure
    {S : Type u} [CommRing S] [Nontrivial S] [IsDomain S]
    [Algebra R S] [Module.Finite R S] [IsIntegrallyClosed S]
    {q : ℕ} (hq : 0 < q) :
    let f : Polynomial R →+* Polynomial S :=
      Polynomial.eval₂RingHom (Polynomial.C.comp (algebraMap R S))
        (Polynomial.X ^ q : Polynomial S)
    let _ : Algebra (Polynomial R) (FractionRing (Polynomial S)) :=
      (RingHom.comp (algebraMap (Polynomial S) (FractionRing (Polynomial S))) f).toAlgebra
    @IsIntegralClosure (Polynomial S) (Polynomial R) (FractionRing (Polynomial S))
      _ _ _ inferInstance inferInstance := by
  let f : Polynomial R →+* Polynomial S :=
    Polynomial.eval₂RingHom (Polynomial.C.comp (algebraMap R S))
      (Polynomial.X ^ q : Polynomial S)
  letI : Algebra (Polynomial R) (Polynomial S) := f.toAlgebra
  letI : Module (Polynomial R) (Polynomial S) := RingHom.toModule f
  have hfinite : f.Finite := by
    -- The source `X ↦ X^q` normalization step is finite once coefficients are finite.
    simpa [f] using
      (twisted_polynomial_map_finite (R := R) (S := S) hq)
  letI : Algebra.IsIntegral (Polynomial R) (Polynomial S) := ⟨fun x ↦ hfinite.to_isIntegral x⟩
  letI : Algebra (Polynomial R) (FractionRing (Polynomial S)) :=
    (RingHom.comp (algebraMap (Polynomial S) (FractionRing (Polynomial S))) f).toAlgebra
  letI : SMul (Polynomial R) (FractionRing (Polynomial S)) :=
    (show Algebra (Polynomial R) (FractionRing (Polynomial S)) from inferInstance).toSMul
  letI : IsScalarTower (Polynomial R) (Polynomial S) (FractionRing (Polynomial S)) := by
    -- The fraction-field algebra is exactly the composite of the twisted map with localization.
    refine IsScalarTower.of_algebraMap_eq
      (R := Polynomial R) (S := Polynomial S) (A := FractionRing (Polynomial S)) ?_
    intro x
    rfl
  -- Polynomial rings over integrally closed domains are integrally closed, so the generic
  -- `of_isIntegrallyClosed` packaging turns the twisted integral map into an integral closure.
  exact IsIntegralClosure.of_isIntegrallyClosed
    (R := Polynomial S) (S := Polynomial R) (K := FractionRing (Polynomial S))

/-- Helper for Lemma 10.161.13: localizing the coefficient-extension map
`R[X] → Frac(R)[X]` identifies `Frac(R[X])` with a subfield of `Frac(R)(X)`. -/
noncomputable def fractionRing_polynomial_to_ratFunc_transport :
    FractionRing (Polynomial R) →+* RatFunc (FractionRing R) :=
  IsFractionRing.map
    (K := FractionRing (Polynomial R))
    (L := RatFunc (FractionRing R))
    (j := Polynomial.mapRingHom (algebraMap R (FractionRing R)))
    (Polynomial.map_injective _ (IsFractionRing.injective R (FractionRing R)))

/-- Helper for Lemma 10.161.13: on polynomial numerators, the fraction-ring transport is just the
localized coefficient map. -/
lemma fractionRing_polynomial_to_ratFunc_transport_algebraMap
    (p : Polynomial R) :
    fractionRing_polynomial_to_ratFunc_transport (R := R)
      (algebraMap (Polynomial R) (FractionRing (Polynomial R)) p) =
        algebraMap (Polynomial (FractionRing R)) (RatFunc (FractionRing R))
          (p.map (algebraMap R (FractionRing R))) := by
  -- Unfold the localization map once so the claim reduces to the defining `IsLocalization.map_eq`.
  delta fractionRing_polynomial_to_ratFunc_transport IsFractionRing.map
  simpa [Polynomial.mapRingHom] using
    (show
      algebraMap (Polynomial (FractionRing R)) (RatFunc (FractionRing R))
          ((Polynomial.mapRingHom (algebraMap R (FractionRing R))) p) =
        algebraMap (Polynomial (FractionRing R)) (RatFunc (FractionRing R))
          ((Polynomial.mapRingHom (algebraMap R (FractionRing R))) p) by
      simpa only [IsLocalization.map_eq, RingHom.comp_apply])

/-- Helper for Lemma 10.161.13: the localized transport sends the polynomial variable to the
standard rational-function variable. -/
lemma fractionRing_polynomial_to_ratFunc_transport_X :
    fractionRing_polynomial_to_ratFunc_transport (R := R)
      (algebraMap (Polynomial R) (FractionRing (Polynomial R)) Polynomial.X) =
        RatFunc.X := by
  -- Apply the general polynomial transport formula to `X` and simplify the resulting map.
  rw [fractionRing_polynomial_to_ratFunc_transport_algebraMap (R := R) Polynomial.X]
  simp

/-- Helper for Lemma 10.161.13: the coefficient field `Frac(S)` maps into
`Frac(S[X])` through the constant-polynomial inclusion. -/
noncomputable def fractionRing_to_polynomial_fractionRing_coeffLift
    {S : Type u} [CommRing S] [IsDomain S]
    {K' : Type u} [Field K'] [Algebra S K'] [IsFractionRing S K'] :
    K' →+* FractionRing (Polynomial S) :=
  IsFractionRing.lift
    (K := K') (L := FractionRing (Polynomial S))
    (g := algebraMap S (FractionRing (Polynomial S)))
    (FaithfulSMul.algebraMap_injective S (FractionRing (Polynomial S)))

/-- Helper for Lemma 10.161.13: localizing the coefficient map `S[X] → Frac(S)[X]` embeds
`Frac(S[X])` into the rational-function field over `Frac(S)`. -/
noncomputable def polynomial_fractionRing_to_ratFunc_transport
    {S : Type u} [CommRing S] [IsDomain S]
    {K' : Type u} [Field K'] [Algebra S K'] [IsFractionRing S K'] :
    FractionRing (Polynomial S) →+* RatFunc K' :=
  IsFractionRing.map
    (K := FractionRing (Polynomial S))
    (L := RatFunc K')
    (j := Polynomial.mapRingHom (algebraMap S K'))
    (Polynomial.map_injective _ (IsFractionRing.injective S K'))

/-- Helper for Lemma 10.161.13: on polynomial numerators, the localization map from
`Frac(S[X])` to `Frac(S)(X)` is the obvious coefficient extension. -/
lemma polynomial_fractionRing_to_ratFunc_transport_algebraMap
    {S : Type u} [CommRing S] [IsDomain S]
    {K' : Type u} [Field K'] [Algebra S K'] [IsFractionRing S K']
    (p : Polynomial S) :
    polynomial_fractionRing_to_ratFunc_transport (S := S) (K' := K')
      (algebraMap (Polynomial S) (FractionRing (Polynomial S)) p) =
        algebraMap (Polynomial K') (RatFunc K') (p.map (algebraMap S K')) := by
  -- As above, the fraction-ring map is determined by its action on the polynomial numerator.
  delta polynomial_fractionRing_to_ratFunc_transport IsFractionRing.map
  simpa [Polynomial.mapRingHom] using
    (show
      algebraMap (Polynomial K') (RatFunc K')
          ((Polynomial.mapRingHom (algebraMap S K')) p) =
        algebraMap (Polynomial K') (RatFunc K')
          ((Polynomial.mapRingHom (algebraMap S K')) p) by
      simpa only [IsLocalization.map_eq, RingHom.comp_apply])

/-- Helper for Lemma 10.161.13: the coefficient lift `Frac(S) → Frac(S[X])` becomes the usual
constant-function inclusion after transport to `Frac(S)(X)`. -/
lemma polynomial_fractionRing_to_ratFunc_transport_coeffLift
    {S : Type u} [CommRing S] [IsDomain S]
    {K' : Type u} [Field K'] [Algebra S K'] [IsFractionRing S K']
    (a : K') :
    polynomial_fractionRing_to_ratFunc_transport (S := S) (K' := K')
      (fractionRing_to_polynomial_fractionRing_coeffLift (S := S) (K' := K') a) =
        algebraMap K' (RatFunc K') a := by
  -- Compare the two maps out of `Frac(S)` on the dense subring `S`.
  have hmaps :
      (polynomial_fractionRing_to_ratFunc_transport (S := S) (K' := K')).comp
          (fractionRing_to_polynomial_fractionRing_coeffLift (S := S) (K' := K')) =
        algebraMap K' (RatFunc K') := by
    apply IsFractionRing.ringHom_ext (A := S)
    intro s
    have hcoefflift :
        fractionRing_to_polynomial_fractionRing_coeffLift (S := S) (K' := K')
            ((algebraMap S K') s) =
          algebraMap S (FractionRing (Polynomial S)) s := by
      simpa [fractionRing_to_polynomial_fractionRing_coeffLift] using
        (IsFractionRing.lift_algebraMap
          (A := S) (K := K') (L := FractionRing (Polynomial S))
          (g := algebraMap S (FractionRing (Polynomial S)))
          (hg := FaithfulSMul.algebraMap_injective S (FractionRing (Polynomial S))) s)
    rw [RingHom.comp_apply, hcoefflift]
    have hconst :
        algebraMap S (FractionRing (Polynomial S)) s =
          algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C s) := by
      simpa using
        congrArg
          (fun g : S →+* FractionRing (Polynomial S) => g s)
          (IsScalarTower.algebraMap_eq S (Polynomial S) (FractionRing (Polynomial S)))
    rw [hconst]
    rw [polynomial_fractionRing_to_ratFunc_transport_algebraMap (S := S) (K' := K')
      (Polynomial.C s)]
    simp
  exact congrArg (fun f : K' →+* RatFunc K' => f a) hmaps

/-- Helper for Lemma 10.161.13: the localization map from `Frac(S[X])` to `Frac(S)(X)` preserves
the polynomial variable. -/
lemma polynomial_fractionRing_to_ratFunc_transport_X
    {S : Type u} [CommRing S] [IsDomain S]
    {K' : Type u} [Field K'] [Algebra S K'] [IsFractionRing S K'] :
    polynomial_fractionRing_to_ratFunc_transport (S := S) (K' := K')
      (algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X) =
        RatFunc.X := by
  -- This is the `X`-specialization of the previous algebra-map formula.
  rw [polynomial_fractionRing_to_ratFunc_transport_algebraMap
    (S := S) (K' := K') Polynomial.X]
  simp

/-- Helper for Lemma 10.161.13: evaluating `K'[X]` at the polynomial variable inside
`Frac(S[X])`, with coefficients lifted from `Frac(S)`, is injective. -/
lemma polynomial_fractionRing_eval₂_injective
    {S : Type u} [CommRing S] [IsDomain S]
    {K' : Type u} [Field K'] [Algebra S K'] [IsFractionRing S K'] :
    Function.Injective
      (Polynomial.eval₂RingHom
        (fractionRing_to_polynomial_fractionRing_coeffLift (S := S) (K' := K'))
        (algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X)) := by
  let σ : FractionRing (Polynomial S) →+* RatFunc K' :=
    polynomial_fractionRing_to_ratFunc_transport (S := S) (K' := K')
  have hcoeff :
      ∀ a : K',
        σ (fractionRing_to_polynomial_fractionRing_coeffLift (S := S) (K' := K') a) =
          algebraMap K' (RatFunc K') a := by
    intro a
    exact polynomial_fractionRing_to_ratFunc_transport_coeffLift
      (S := S) (K' := K') a
  have hcomp :
      σ.comp
          (Polynomial.eval₂RingHom
            (fractionRing_to_polynomial_fractionRing_coeffLift (S := S) (K' := K'))
            (algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X)) =
        algebraMap (Polynomial K') (RatFunc K') := by
    apply Polynomial.ringHom_ext
    · intro a
      -- On constants, the composition is exactly the coefficient inclusion.
      simp [hcoeff]
    · -- The polynomial variable is preserved by the comparison map.
      simpa using polynomial_fractionRing_to_ratFunc_transport_X (S := S) (K' := K')
  intro p q hpq
  -- Cancel the comparison map to `RatFunc K'`, where polynomial algebra maps are injective.
  have hmap :
      (σ.comp
          (Polynomial.eval₂RingHom
            (fractionRing_to_polynomial_fractionRing_coeffLift (S := S) (K' := K'))
            (algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X))) p =
        (σ.comp
          (Polynomial.eval₂RingHom
            (fractionRing_to_polynomial_fractionRing_coeffLift (S := S) (K' := K'))
            (algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X))) q := by
    exact congrArg (fun z ↦ σ z) hpq
  rw [hcomp] at hmap
  exact (RatFunc.algebraMap_injective (K := K')) hmap

/-- Helper for Lemma 10.161.13: the rational-function field over `Frac(S)` maps into
`Frac(S[X])` by lifting coefficients through the fraction-field structure and sending `X` to the
polynomial variable. -/
noncomputable def ratfunc_to_twisted_polynomial_fractionRing_transport
    {S : Type u} [CommRing S] [IsDomain S]
    {K' : Type u} [Field K'] [Algebra S K'] [IsFractionRing S K'] :
    K'⟮X⟯ →+* FractionRing (Polynomial S) :=
  RatFunc.liftRingHom
    (Polynomial.eval₂RingHom
      (fractionRing_to_polynomial_fractionRing_coeffLift (S := S) (K' := K'))
      (algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (polynomial_fractionRing_eval₂_injective (S := S) (K' := K')))

/-- Helper for Lemma 10.161.13: on polynomial numerators, the transport
`Frac(S)(X) → Frac(S[X])` is the obvious evaluation map with lifted coefficients and
`X` sent to the polynomial variable. -/
lemma ratfunc_to_twisted_polynomial_fractionRing_transport_algebraMap
    {S : Type u} [CommRing S] [IsDomain S]
    {K' : Type u} [Field K'] [Algebra S K'] [IsFractionRing S K']
    (p : Polynomial K') :
    ratfunc_to_twisted_polynomial_fractionRing_transport (S := S) (K' := K')
      (algebraMap (Polynomial K') K'⟮X⟯ p) =
        Polynomial.eval₂
          (fractionRing_to_polynomial_fractionRing_coeffLift (S := S) (K' := K'))
          (algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X) p := by
  let φ : Polynomial K' →+* FractionRing (Polynomial S) :=
    Polynomial.eval₂RingHom
      (fractionRing_to_polynomial_fractionRing_coeffLift (S := S) (K' := K'))
      (algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X)
  -- The lifted rational-function map agrees with its defining polynomial map on numerators.
  change RatFunc.liftRingHom φ
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (polynomial_fractionRing_eval₂_injective (S := S) (K' := K')))
      (algebraMap (Polynomial K') K'⟮X⟯ p) = φ p
  simpa using RatFunc.liftRingHom_algebraMap φ
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (polynomial_fractionRing_eval₂_injective (S := S) (K' := K'))) p

/-- Helper for Lemma 10.161.13: the transport `Frac(S)(X) → Frac(S[X])` preserves coefficients. -/
lemma ratfunc_to_twisted_polynomial_fractionRing_transport_coeff
    {S : Type u} [CommRing S] [IsDomain S]
    {K' : Type u} [Field K'] [Algebra S K'] [IsFractionRing S K']
    (a : K') :
    ratfunc_to_twisted_polynomial_fractionRing_transport (S := S) (K' := K')
      (algebraMap K' K'⟮X⟯ a) =
        fractionRing_to_polynomial_fractionRing_coeffLift (S := S) (K' := K') a := by
  -- Rewrite the constant rational function as the image of the constant polynomial `C a`.
  change
    ratfunc_to_twisted_polynomial_fractionRing_transport (S := S) (K' := K') (RatFunc.C a) =
      fractionRing_to_polynomial_fractionRing_coeffLift (S := S) (K' := K') a
  rw [← RatFunc.algebraMap_C]
  simpa using
    ratfunc_to_twisted_polynomial_fractionRing_transport_algebraMap
      (S := S) (K' := K') (Polynomial.C a)

/-- Helper for Lemma 10.161.13: the transport `Frac(S)(X) → Frac(S[X])` sends the rational
function variable to the polynomial variable. -/
lemma ratfunc_to_twisted_polynomial_fractionRing_transport_X
    {S : Type u} [CommRing S] [IsDomain S]
    {K' : Type u} [Field K'] [Algebra S K'] [IsFractionRing S K'] :
    ratfunc_to_twisted_polynomial_fractionRing_transport (S := S) (K' := K') RatFunc.X =
      algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X := by
  -- Specialize the numerator formula to the variable polynomial `X`.
  rw [← RatFunc.algebraMap_X]
  simpa using
    ratfunc_to_twisted_polynomial_fractionRing_transport_algebraMap
      (S := S) (K' := K') Polynomial.X

/-- Helper for Lemma 10.161.13: the twisted polynomial map `R[X] → S[X]` sending `X` to `X^q`
is injective for every positive exponent `q`. -/
lemma twisted_polynomial_map_injective
    {S : Type u} [CommRing S] [IsDomain S] [Algebra R S]
    (hRS : Function.Injective (algebraMap R S)) {q : ℕ} (hq : 0 < q) :
    Function.Injective
      (Polynomial.eval₂RingHom (Polynomial.C.comp (algebraMap R S))
        (Polynomial.X ^ q : Polynomial S)) := by
  intro p₁ p₂ hp
  have hp₁ :
      Polynomial.expand S q (p₁.map (algebraMap R S)) =
        Polynomial.eval₂ (Polynomial.C.comp (algebraMap R S))
          (Polynomial.X ^ q : Polynomial S) p₁ := by
    calc
      Polynomial.expand S q (p₁.map (algebraMap R S)) =
          Polynomial.eval₂ Polynomial.C (Polynomial.X ^ q : Polynomial S)
            (p₁.map (algebraMap R S)) := by
        simp [Polynomial.coe_expand]
      _ = Polynomial.eval₂ (Polynomial.C.comp (algebraMap R S))
            (Polynomial.X ^ q : Polynomial S) p₁ := by
        simpa using
          (Polynomial.eval₂_map (p := p₁) (f := algebraMap R S) (g := Polynomial.C)
            (x := (Polynomial.X ^ q : Polynomial S)))
  have hp₂ :
      Polynomial.expand S q (p₂.map (algebraMap R S)) =
        Polynomial.eval₂ (Polynomial.C.comp (algebraMap R S))
          (Polynomial.X ^ q : Polynomial S) p₂ := by
    calc
      Polynomial.expand S q (p₂.map (algebraMap R S)) =
          Polynomial.eval₂ Polynomial.C (Polynomial.X ^ q : Polynomial S)
            (p₂.map (algebraMap R S)) := by
        simp [Polynomial.coe_expand]
      _ = Polynomial.eval₂ (Polynomial.C.comp (algebraMap R S))
            (Polynomial.X ^ q : Polynomial S) p₂ := by
        simpa using
          (Polynomial.eval₂_map (p := p₂) (f := algebraMap R S) (g := Polynomial.C)
            (x := (Polynomial.X ^ q : Polynomial S)))
  have hcomp :
      Polynomial.expand S q (p₁.map (algebraMap R S)) =
        Polynomial.expand S q (p₂.map (algebraMap R S)) := by
    -- Both sides are the same twisted coefficient-extension map written via `Polynomial.expand`.
    calc
      Polynomial.expand S q (p₁.map (algebraMap R S)) =
          Polynomial.eval₂ (Polynomial.C.comp (algebraMap R S))
            (Polynomial.X ^ q : Polynomial S) p₁ := hp₁
      _ = Polynomial.eval₂ (Polynomial.C.comp (algebraMap R S))
            (Polynomial.X ^ q : Polynomial S) p₂ := by
        simpa using hp
      _ = Polynomial.expand S q (p₂.map (algebraMap R S)) := hp₂.symm
  have hmap :
      p₁.map (algebraMap R S) = p₂.map (algebraMap R S) :=
    (Polynomial.expand_inj (R := S) hq).1 hcomp
  exact Polynomial.map_injective (algebraMap R S) hRS hmap

/-- Helper for Lemma 10.161.13: if a rational-function base-change map sends coefficients by the
field extension `K → K'` and sends `X` to `X^q`, then after transporting to `Frac(S[X])` it
agrees on `K[X]` with the twisted polynomial map sending coefficients through `K'` and
`X` to `X^q`. -/
lemma qpow_ratfunc_transport_on_fraction_field_polynomials
    {K' : Type u} [Field K'] [Algebra (FractionRing R) K']
    {S : Type u} [CommRing S] [IsDomain S] [Algebra S K'] [IsFractionRing S K']
    {q : ℕ}
    (σqRat : RatFunc (FractionRing R) →+* RatFunc K')
    (hcoeff :
      ∀ a : FractionRing R,
        σqRat (algebraMap (FractionRing R) (RatFunc (FractionRing R)) a) =
          algebraMap K' (RatFunc K') (algebraMap (FractionRing R) K' a))
    (hX : σqRat RatFunc.X = RatFunc.X ^ q) :
    (ratfunc_to_twisted_polynomial_fractionRing_transport (S := S) (K' := K')).comp
        (σqRat.comp (algebraMap (Polynomial (FractionRing R))
          (RatFunc (FractionRing R)))) =
      Polynomial.eval₂RingHom
        ((fractionRing_to_polynomial_fractionRing_coeffLift (S := S) (K' := K')).comp
          (algebraMap (FractionRing R) K'))
        (algebraMap (Polynomial S) (FractionRing (Polynomial S))
          (Polynomial.X ^ q : Polynomial S)) := by
  apply Polynomial.ringHom_ext
  · intro a
    -- Constants are transported only through the coefficient field extension.
    have hcoeff' :
        σqRat (RatFunc.C a) =
          algebraMap K' K'⟮X⟯ (algebraMap (FractionRing R) K' a) := by
      change σqRat ((algebraMap (FractionRing R) (RatFunc (FractionRing R))) a) =
        algebraMap K' K'⟮X⟯ (algebraMap (FractionRing R) K' a)
      exact hcoeff a
    calc
      ratfunc_to_twisted_polynomial_fractionRing_transport (S := S) (K' := K')
          (σqRat (RatFunc.C a)) =
        ratfunc_to_twisted_polynomial_fractionRing_transport (S := S) (K' := K')
          (algebraMap K' K'⟮X⟯ (algebraMap (FractionRing R) K' a)) := by
        rw [hcoeff']
      _ =
        fractionRing_to_polynomial_fractionRing_coeffLift (S := S) (K' := K')
          (algebraMap (FractionRing R) K' a) := by
        exact ratfunc_to_twisted_polynomial_fractionRing_transport_coeff
          (S := S) (K' := K') (algebraMap (FractionRing R) K' a)
      _ =
        (Polynomial.eval₂RingHom
          ((fractionRing_to_polynomial_fractionRing_coeffLift (S := S) (K' := K')).comp
            (algebraMap (FractionRing R) K'))
          (algebraMap (Polynomial S) (FractionRing (Polynomial S))
            (Polynomial.X ^ q : Polynomial S))) (Polynomial.C a) := by
        change
          fractionRing_to_polynomial_fractionRing_coeffLift (S := S) (K' := K')
            (algebraMap (FractionRing R) K' a) =
            Polynomial.eval₂
              ((fractionRing_to_polynomial_fractionRing_coeffLift (S := S) (K' := K')).comp
                (algebraMap (FractionRing R) K'))
              (algebraMap (Polynomial S) (FractionRing (Polynomial S))
                (Polynomial.X ^ q : Polynomial S))
              (Polynomial.C a)
        simp [RingHom.comp_apply]
  · -- The rational-function variable becomes the polynomial variable raised to the chosen power.
    calc
      ratfunc_to_twisted_polynomial_fractionRing_transport (S := S) (K' := K')
          (σqRat RatFunc.X) =
        ratfunc_to_twisted_polynomial_fractionRing_transport (S := S) (K' := K')
          (RatFunc.X ^ q) := by
        rw [hX]
      _ =
        (ratfunc_to_twisted_polynomial_fractionRing_transport (S := S) (K' := K')
          RatFunc.X) ^ q := by
        rw [map_pow]
      _ =
        (algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X) ^ q := by
        rw [ratfunc_to_twisted_polynomial_fractionRing_transport_X (S := S) (K' := K')]
      _ =
        algebraMap (Polynomial S) (FractionRing (Polynomial S))
          (Polynomial.X ^ q : Polynomial S) := by
        rw [map_pow]
      _ =
        (Polynomial.eval₂RingHom
          ((fractionRing_to_polynomial_fractionRing_coeffLift (S := S) (K' := K')).comp
            (algebraMap (FractionRing R) K'))
          (algebraMap (Polynomial S) (FractionRing (Polynomial S))
            (Polynomial.X ^ q : Polynomial S))) Polynomial.X := by
        change
          algebraMap (Polynomial S) (FractionRing (Polynomial S))
            (Polynomial.X ^ q : Polynomial S) =
            Polynomial.eval₂
              ((fractionRing_to_polynomial_fractionRing_coeffLift (S := S) (K' := K')).comp
                (algebraMap (FractionRing R) K'))
              (algebraMap (Polynomial S) (FractionRing (Polynomial S))
                (Polynomial.X ^ q : Polynomial S))
              Polynomial.X
        rw [Polynomial.eval₂_X]

/-- Helper for Lemma 10.161.13: localizing the twisted polynomial map
`R[X] → S[X]`, with `X ↦ X^q`, gives a canonical map
`Frac(R[X]) → Frac(S[X])`. -/
noncomputable def twisted_polynomial_fractionRing_localization
    {S : Type u} [CommRing S] [IsDomain S] [Algebra R S]
    {q : ℕ} (hq : 0 < q) (hRS : Function.Injective (algebraMap R S)) :
    FractionRing (Polynomial R) →+* FractionRing (Polynomial S) :=
  IsFractionRing.map
    (K := FractionRing (Polynomial R))
    (L := FractionRing (Polynomial S))
    (j := Polynomial.eval₂RingHom (Polynomial.C.comp (algebraMap R S))
      (Polynomial.X ^ q : Polynomial S))
    (twisted_polynomial_map_injective (R := R) (S := S) hRS hq)

/-- Helper for Lemma 10.161.13: on polynomial numerators, the localized twisted map is the
localization of the polynomial map itself. -/
lemma twisted_polynomial_fractionRing_localization_algebraMap
    {S : Type u} [CommRing S] [IsDomain S] [Algebra R S]
    {q : ℕ} (hq : 0 < q) (hRS : Function.Injective (algebraMap R S))
    (p : Polynomial R) :
    twisted_polynomial_fractionRing_localization (R := R) (S := S) hq hRS
      (algebraMap (Polynomial R) (FractionRing (Polynomial R)) p) =
        algebraMap (Polynomial S) (FractionRing (Polynomial S))
          ((Polynomial.eval₂RingHom (Polynomial.C.comp (algebraMap R S))
            (Polynomial.X ^ q : Polynomial S)) p) := by
  -- Unfold the localization map once so the claim reduces to `IsLocalization.map_eq`.
  delta twisted_polynomial_fractionRing_localization IsFractionRing.map
  simpa using
    (show
      algebraMap (Polynomial S) (FractionRing (Polynomial S))
          ((Polynomial.eval₂RingHom (Polynomial.C.comp (algebraMap R S))
            (Polynomial.X ^ q : Polynomial S)) p) =
        algebraMap (Polynomial S) (FractionRing (Polynomial S))
          ((Polynomial.eval₂RingHom (Polynomial.C.comp (algebraMap R S))
            (Polynomial.X ^ q : Polynomial S)) p) by
      simpa only [IsLocalization.map_eq, RingHom.comp_apply])

/-- Helper for Lemma 10.161.13: if the coefficient lift `Frac(S) → Frac(S[X])` is fed a scalar
coming from `R`, the result is the obvious constant polynomial with coefficient in `S`. -/
lemma fractionRing_to_polynomial_fractionRing_coeffLift_base
    {S : Type u} [CommRing S] [IsDomain S] [Algebra R S]
    {K' : Type u} [Field K'] [Algebra (FractionRing R) K'] [Algebra R K']
    [Algebra S K'] [IsFractionRing S K']
    [IsScalarTower R S K'] [IsScalarTower R (FractionRing R) K']
    (r : R) :
    fractionRing_to_polynomial_fractionRing_coeffLift (S := S) (K' := K')
      (algebraMap (FractionRing R) K' (algebraMap R (FractionRing R) r)) =
        algebraMap (Polynomial S) (FractionRing (Polynomial S))
          (Polynomial.C (algebraMap R S r)) := by
  have hscalar :
      algebraMap (FractionRing R) K' (algebraMap R (FractionRing R) r) =
        algebraMap S K' (algebraMap R S r) := by
    have hleft :
        algebraMap (FractionRing R) K' (algebraMap R (FractionRing R) r) =
          algebraMap R K' r := by
      simpa using
        congrArg (fun g : R →+* K' => g r)
          (IsScalarTower.algebraMap_eq R (FractionRing R) K').symm
    have hright :
        algebraMap S K' (algebraMap R S r) = algebraMap R K' r := by
      simpa using
        congrArg (fun g : R →+* K' => g r) (IsScalarTower.algebraMap_eq R S K').symm
    exact hleft.trans hright.symm
  have hcoeff :
      fractionRing_to_polynomial_fractionRing_coeffLift (S := S) (K' := K')
        (algebraMap S K' (algebraMap R S r)) =
          algebraMap S (FractionRing (Polynomial S)) (algebraMap R S r) := by
    simpa [fractionRing_to_polynomial_fractionRing_coeffLift] using
      (IsFractionRing.lift_algebraMap
        (A := S) (K := K') (L := FractionRing (Polynomial S))
        (g := algebraMap S (FractionRing (Polynomial S)))
        (hg := FaithfulSMul.algebraMap_injective S (FractionRing (Polynomial S)))
        (algebraMap R S r))
  rw [hscalar, hcoeff]
  -- Convert the scalar inclusion into the constant-polynomial inclusion.
  simpa using
    congrArg
      (fun g : S →+* FractionRing (Polynomial S) => g (algebraMap R S r))
      (IsScalarTower.algebraMap_eq S (Polynomial S) (FractionRing (Polynomial S)))

/-- Helper for Lemma 10.161.13: after transporting `Frac(R[X])` to `RatFunc(Frac(R))`, any
base-change map sending coefficients by `Frac(R) → K'` and `X` to `X^q` agrees with the
localized twisted polynomial map `Frac(R[X]) → Frac(S[X])`. -/
lemma qpow_ratfunc_transport_eq_twisted_polynomial_localization
    {K' : Type u} [Field K'] [Algebra (FractionRing R) K'] [Algebra R K']
    [IsScalarTower R (FractionRing R) K']
    {S : Type u} [CommRing S] [IsDomain S] [Algebra R S] [Algebra S K']
    [IsFractionRing S K'] [IsScalarTower R S K']
    {q : ℕ} (hq : 0 < q)
    (σqRat : RatFunc (FractionRing R) →+* RatFunc K')
    (hcoeff :
      ∀ a : FractionRing R,
        σqRat (algebraMap (FractionRing R) (RatFunc (FractionRing R)) a) =
          algebraMap K' (RatFunc K') (algebraMap (FractionRing R) K' a))
    (hX : σqRat RatFunc.X = RatFunc.X ^ q) :
    ((ratfunc_to_twisted_polynomial_fractionRing_transport (S := S) (K' := K')).comp σqRat).comp
        (fractionRing_polynomial_to_ratFunc_transport (R := R)) =
      twisted_polynomial_fractionRing_localization (R := R) (S := S) hq
        (algebraMap_injective_of_field_isFractionRing R S (FractionRing R) K') := by
  let hRS : Function.Injective (algebraMap R S) :=
    algebraMap_injective_of_field_isFractionRing R S (FractionRing R) K'
  have hcoeff_comp :
      (((fractionRing_to_polynomial_fractionRing_coeffLift (S := S) (K' := K')).comp
        (algebraMap (FractionRing R) K')).comp (algebraMap R (FractionRing R))) =
        ((algebraMap (Polynomial S) (FractionRing (Polynomial S))).comp
          (Polynomial.C.comp (algebraMap R S))) := by
    apply RingHom.ext
    intro r
    -- On base coefficients, both sides are the same constant-polynomial inclusion.
    simpa [RingHom.comp_apply] using
      fractionRing_to_polynomial_fractionRing_coeffLift_base
        (R := R) (S := S) (K' := K') r
  apply IsFractionRing.ringHom_ext (A := Polynomial R)
  intro p
  have hpoly_transport :
      ((ratfunc_to_twisted_polynomial_fractionRing_transport (S := S) (K' := K')).comp
          (σqRat.comp
            (algebraMap (Polynomial (FractionRing R)) (RatFunc (FractionRing R)))))
        (p.map (algebraMap R (FractionRing R))) =
        Polynomial.eval₂
          ((fractionRing_to_polynomial_fractionRing_coeffLift (S := S) (K' := K')).comp
            (algebraMap (FractionRing R) K'))
          (algebraMap (Polynomial S) (FractionRing (Polynomial S))
            (Polynomial.X ^ q : Polynomial S))
          (p.map (algebraMap R (FractionRing R))) := by
    exact congrArg
      (fun f : Polynomial (FractionRing R) →+* FractionRing (Polynomial S) =>
        f (p.map (algebraMap R (FractionRing R))))
      (qpow_ratfunc_transport_on_fraction_field_polynomials
        (R := R) (S := S) (K' := K') σqRat hcoeff hX)
  -- Compare the two fraction-ring maps on polynomial numerators, where both descriptions are
  -- explicit.
  calc
    (((ratfunc_to_twisted_polynomial_fractionRing_transport (S := S) (K' := K')).comp σqRat).comp
        (fractionRing_polynomial_to_ratFunc_transport (R := R)))
        (algebraMap (Polynomial R) (FractionRing (Polynomial R)) p) =
      ((ratfunc_to_twisted_polynomial_fractionRing_transport (S := S) (K' := K')).comp
          (σqRat.comp
            (algebraMap (Polynomial (FractionRing R)) (RatFunc (FractionRing R)))))
        (p.map (algebraMap R (FractionRing R))) := by
      rw [RingHom.comp_apply,
        fractionRing_polynomial_to_ratFunc_transport_algebraMap (R := R) p]
      rfl
    _ =
      Polynomial.eval₂
        ((fractionRing_to_polynomial_fractionRing_coeffLift (S := S) (K' := K')).comp
          (algebraMap (FractionRing R) K'))
        (algebraMap (Polynomial S) (FractionRing (Polynomial S))
          (Polynomial.X ^ q : Polynomial S))
        (p.map (algebraMap R (FractionRing R))) := hpoly_transport
    _ =
      Polynomial.eval₂
        (((algebraMap (Polynomial S) (FractionRing (Polynomial S))).comp
          (Polynomial.C.comp (algebraMap R S))))
        (algebraMap (Polynomial S) (FractionRing (Polynomial S))
          (Polynomial.X ^ q : Polynomial S))
        p := by
      rw [map_pow]
      have hmap_eval :
          Polynomial.eval₂
            ((fractionRing_to_polynomial_fractionRing_coeffLift (S := S) (K' := K')).comp
              (algebraMap (FractionRing R) K'))
            ((algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X) ^ q)
            (p.map (algebraMap R (FractionRing R))) =
            Polynomial.eval₂
              ((((fractionRing_to_polynomial_fractionRing_coeffLift (S := S) (K' := K')).comp
                (algebraMap (FractionRing R) K')).comp (algebraMap R (FractionRing R))))
              ((algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X) ^ q)
              p := by
        simpa using
          (Polynomial.eval₂_map
            (p := p) (f := algebraMap R (FractionRing R))
            (g := ((fractionRing_to_polynomial_fractionRing_coeffLift
              (S := S) (K' := K')).comp (algebraMap (FractionRing R) K')))
            (x := (algebraMap (Polynomial S) (FractionRing (Polynomial S))
              Polynomial.X) ^ q))
      rw [hmap_eval, hcoeff_comp]
    _ =
      algebraMap (Polynomial S) (FractionRing (Polynomial S))
        ((Polynomial.eval₂RingHom (Polynomial.C.comp (algebraMap R S))
          (Polynomial.X ^ q : Polynomial S)) p) := by
      rw [← Polynomial.eval₂_map]
      rw [Polynomial.eval₂_at_apply]
      rw [Polynomial.eval_map]
      rfl
    _ =
      twisted_polynomial_fractionRing_localization (R := R) (S := S) hq hRS
        (algebraMap (Polynomial R) (FractionRing (Polynomial R)) p) := by
      rw [twisted_polynomial_fractionRing_localization_algebraMap
        (R := R) (S := S) hq hRS p]

/-- Helper for Lemma 10.161.13: the twisted normalization package already yields finite
integral closure over `R[X]` inside `Frac(S[X])`. -/
lemma twisted_polynomial_fractionRing_integralClosure_finite
    {S : Type u} [CommRing S] [Nontrivial S] [IsDomain S]
    [Algebra R S] [Module.Finite R S] [IsIntegrallyClosed S]
    {q : ℕ} (hq : 0 < q) :
    let f : Polynomial R →+* Polynomial S :=
      Polynomial.eval₂RingHom (Polynomial.C.comp (algebraMap R S))
        (Polynomial.X ^ q : Polynomial S)
    let _ : Algebra (Polynomial R) (FractionRing (Polynomial S)) :=
      (RingHom.comp (algebraMap (Polynomial S) (FractionRing (Polynomial S))) f).toAlgebra
    Module.Finite (Polynomial R)
      (integralClosure (Polynomial R) (FractionRing (Polynomial S))) := by
  let f : Polynomial R →+* Polynomial S :=
    Polynomial.eval₂RingHom (Polynomial.C.comp (algebraMap R S))
      (Polynomial.X ^ q : Polynomial S)
  letI : Algebra (Polynomial R) (Polynomial S) := f.toAlgebra
  letI : Module (Polynomial R) (Polynomial S) := RingHom.toModule f
  letI : Algebra (Polynomial R) (FractionRing (Polynomial S)) :=
    (RingHom.comp (algebraMap (Polynomial S) (FractionRing (Polynomial S))) f).toAlgebra
  letI : SMul (Polynomial R) (FractionRing (Polynomial S)) :=
    (show Algebra (Polynomial R) (FractionRing (Polynomial S)) from inferInstance).toSMul
  letI : IsScalarTower (Polynomial R) (Polynomial S) (FractionRing (Polynomial S)) := by
    -- The chosen algebra on the fraction field is the composite of the twisted coefficient map
    -- with localization from `S[X]`.
    refine IsScalarTower.of_algebraMap_eq ?_
    intro p
    rfl
  letI :
      IsIntegralClosure (Polynomial S) (Polynomial R) (FractionRing (Polynomial S)) :=
    twisted_polynomial_isIntegralClosure (R := R) (S := S) hq
  letI : Module.Finite (Polynomial R) (Polynomial S) :=
    twisted_polynomial_moduleFinite (R := R) (S := S) hq
  let e :
      integralClosure (Polynomial R) (FractionRing (Polynomial S)) ≃ₐ[Polynomial R]
        Polynomial S :=
    IsIntegralClosure.equiv
      (Polynomial R)
      (integralClosure (Polynomial R) (FractionRing (Polynomial S)))
      (FractionRing (Polynomial S))
      (Polynomial S)
  -- Transport finite generation across the canonical equivalence with the twisted polynomial ring.
  exact Module.Finite.equiv e.toLinearEquiv.symm

/-- Helper for Lemma 10.161.13: a Noetherian normal domain is `N-1`. -/
lemma isN1Ring_of_isNormalRing_noetherian
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsNormalRing A] :
    IsN1Ring A := by
  letI : IsIntegrallyClosed A := isIntegrallyClosed_of_isNormalRing (R := A)
  let e : integralClosure A (FractionRing A) ≃ₐ[A] A :=
    -- An integrally closed domain identifies its integral closure in the fraction field with the
    -- original ring itself.
    (Subalgebra.equivOfEq _ _ (IsIntegrallyClosed.integralClosure_eq_bot
      (R := A) (K := FractionRing A))).trans
        (Algebra.botEquivOfInjective (R := A) (A := FractionRing A)
          (IsFractionRing.injective A (FractionRing A)))
  refine IsN1Ring.mk ?_
  -- Transport the obvious finite `A`-module structure on `A` across the normalization equivalence.
  exact Module.Finite.equiv e.toLinearEquiv.symm

-- Proof sketch: let `R'` be the integral closure of `R` in `FractionRing R`. The `N-1`
-- hypothesis makes `R'` finite over `R`, hence `R'[X]` finite over `R[X]`. Since `R'` is normal,
-- the canonical theorem `isNormalRing_polynomial` makes `R'[X]` normal. Then
-- `isN1Ring_of_finite_extension` descends the `N-1` property from `R'[X]` to `R[X]`.
/-- Lemma 10.161.13 (1): if `R` is a Noetherian domain and `R` is `N-1`, then the polynomial ring
`R[X]` is `N-1`. -/
@[stacks 032O]
theorem isN1Ring_polynomial
    [IsN1Ring R] :
    IsN1Ring (Polynomial R) := by
  let S := integralClosure R (FractionRing R)
  letI : Module.Finite R S := inferInstance
  letI : IsFractionRing S (FractionRing R) :=
    integralClosure.isFractionRing_of_finite_extension
      (A := R) (K := FractionRing R) (L := FractionRing R)
  letI : IsIntegrallyClosed S :=
    integralClosure.isIntegrallyClosedOfFiniteExtension
      (R := R) (K := FractionRing R) (L := FractionRing R)
  letI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  let f : Polynomial R →+* Polynomial S := Polynomial.mapRingHom (algebraMap R S)
  have hRS : Function.Injective (algebraMap R S) := by
    -- The normalization sits inside the common fraction field, so coefficient equality can be
    -- checked after coercing into `FractionRing R`.
    intro x y hxy
    apply IsFractionRing.injective R (FractionRing R)
    simpa [S] using congrArg (fun z : S => (z : FractionRing R)) hxy
  have hf : Function.Injective f := by
    -- Injectivity of the coefficient map lifts directly to the polynomial map.
    exact Polynomial.map_injective (algebraMap R S) hRS
  have hfinite : @RingHom.Finite (Polynomial R) (Polynomial S) inferInstance inferInstance f := by
    -- The normalization coefficients are finite over `R`, so the induced polynomial map is finite.
    simpa [f, S] using
      (polynomial_mapRingHom_finite_of_moduleFinite (R := R)
        (S := integralClosure R (FractionRing R)))
  letI : Algebra (Polynomial R) (Polynomial S) := f.toAlgebra
  letI : Module.Finite (Polynomial R) (Polynomial S) := hfinite
  have hSN1 : IsN1Ring (Polynomial S) := by
    -- The normalization coefficients are normal, hence the polynomial ring over them is normal,
    -- and Noetherianity upgrades that normality to the `N-1` property.
    letI : IsNormalRing S := inferInstance
    letI : IsNormalRing (Polynomial S) := isNormalRing_polynomial
    exact isN1Ring_of_isNormalRing_noetherian
  -- Descend `N-1` along the finite injective polynomial coefficient extension.
  exact isN1Ring_of_finite_extension (R := Polynomial R) (S := Polynomial S) hf

/-- Helper for Lemma 10.161.13: a finite purely inseparable field extension admits a finite
generating family whose members all have the same `p^e`-power in the base field. -/
lemma generating_finset_with_common_qpow_mem_base
    {Kx : Type*} {L : Type*} [Field Kx] [Field L] [Algebra Kx L]
    {p : ℕ} [Fact p.Prime] [CharP Kx p] [FiniteDimensional Kx L] [IsPurelyInseparable Kx L] :
    ∃ (s : Finset L) (e : ℕ),
      IntermediateField.adjoin Kx (↑s : Set L) = ⊤ ∧
        ∀ a ∈ s, ∃ b : Kx, a ^ (p ^ e) = algebraMap Kx L b := by
  classical
  letI : Algebra.EssFiniteType Kx L := inferInstance
  obtain ⟨s, hs_top⟩ := IntermediateField.fg_top Kx L
  have hpow :
      ∀ a : {a // a ∈ s}, ∃ n : ℕ, ∃ b : Kx,
        (a.1 : L) ^ (p ^ n) = algebraMap Kx L b := by
    intro a
    -- Pure inseparability sends each chosen generator into the base after some `p^n`-power.
    obtain ⟨n, hn⟩ := IsPurelyInseparable.pow_mem Kx p a.1
    rcases hn with ⟨b, hb⟩
    exact ⟨n, b, hb.symm⟩
  choose n b hb using hpow
  let e : ℕ := s.attach.sup n
  refine ⟨s, e, hs_top, ?_⟩
  intro a ha
  let a' : {a // a ∈ s} := ⟨a, ha⟩
  have hle : n a' ≤ e := by
    -- The chosen exponent `e` dominates all individual generator exponents.
    exact Finset.le_sup (s := s.attach) (f := n) (by simp [a'])
  refine ⟨b a' ^ (p ^ (e - n a')), ?_⟩
  -- Raise the individual `p^(n a')`-relation to the remaining power so everything lands in the
  -- base with the same exponent `p^e`.
  calc
    a ^ (p ^ e) = a ^ (p ^ (n a' + (e - n a'))) := by
      rw [Nat.add_sub_of_le hle]
    _ = a ^ (p ^ n a' * p ^ (e - n a')) := by
      rw [pow_add]
    _ = (a ^ (p ^ n a')) ^ (p ^ (e - n a')) := by
      rw [pow_mul]
    _ = (algebraMap Kx L (b a')) ^ (p ^ (e - n a')) := by
      rw [hb a']
    _ = algebraMap Kx L (b a' ^ (p ^ (e - n a'))) := by
      rw [map_pow]

/-- Helper for Lemma 10.161.13: one finite purely inseparable coefficient extension makes a finite
family of base-field scalars into `p`th powers. -/
lemma scalar_family_pth_roots_after_finite_coefficient_extension
    {K : Type u} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p] (C : Finset K) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K'),
      FiniteDimensional K K' ∧
        IsPurelyInseparable K K' ∧
          ∀ a ∈ C, ∃ b : K', b ^ p = algebraMap K K' a := by
  -- Reuse the earlier Frobenius-root package instead of rebuilding the coefficient extension here.
  obtain ⟨K', _, _, hfd, hpi, hroots⟩ :=
    exists_finite_purelyInseparable_extension_with_pth_roots
      (k := K) (p := p) C
  exact ⟨K', inferInstance, inferInstance, hfd, hpi, hroots⟩

/-- Helper for Lemma 10.161.13: iterating the one-step coefficient extension makes a finite
family of scalars into common `p^e`th powers. -/
lemma scalar_family_qpow_roots_after_finite_coefficient_extension
    {K : Type u} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p] (C : Finset K) :
    ∀ e : ℕ,
      ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K'),
        FiniteDimensional K K' ∧
          IsPurelyInseparable K K' ∧
            ∀ a ∈ C, ∃ b : K', b ^ (p ^ e) = algebraMap K K' a := by
  classical
  intro e
  induction e with
  | zero =>
      refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
      intro a ha
      -- In the zero-step case the identity extension already gives the required witness.
      exact ⟨algebraMap K K a, by simp⟩
  | succ e ih =>
      obtain ⟨K₁, _, _, hfd₁, hpi₁, hroots₁⟩ := ih
      letI : CharP K₁ p := charP_of_injective_algebraMap (algebraMap K K₁).injective p
      let chosenRoot : K → K₁ := fun a ↦
        if ha : a ∈ C then Classical.choose (hroots₁ a ha) else 0
      let C₁ : Finset K₁ := C.image chosenRoot
      obtain ⟨K₂, _, _, hfd₂, hpi₂, hroots₂⟩ :=
        scalar_family_pth_roots_after_finite_coefficient_extension
          (K := K₁) (p := p) C₁
      letI : Algebra K K₂ :=
        (RingHom.comp (algebraMap K₁ K₂) (algebraMap K K₁)).toAlgebra
      letI : IsScalarTower K K₁ K₂ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
      have hfd : FiniteDimensional K K₂ := by
        letI : FiniteDimensional K K₁ := hfd₁
        letI : FiniteDimensional K₁ K₂ := hfd₂
        exact FiniteDimensional.trans K K₁ K₂
      have hpi : IsPurelyInseparable K K₂ := by
        letI : IsPurelyInseparable K K₁ := hpi₁
        letI : IsPurelyInseparable K₁ K₂ := hpi₂
        exact IsPurelyInseparable.trans K K₁ K₂
      refine ⟨K₂, inferInstance, inferInstance, hfd, hpi, ?_⟩
      intro a ha
      have hchosen_mem : chosenRoot a ∈ C₁ := by
        exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
      obtain ⟨c, hc⟩ := hroots₂ (chosenRoot a) hchosen_mem
      refine ⟨c, ?_⟩
      have hchosen_pow : chosenRoot a ^ (p ^ e) = algebraMap K K₁ a := by
        -- The first-stage extension was chosen so that every scalar in `C` already has a
        -- `p^e`th root upstairs in `K₁`.
        simp only [chosenRoot, ha, dite_true]
        exact Classical.choose_spec (hroots₁ a ha)
      -- Raising the second-stage `p`th root to the remaining exponent gives the desired `p^(e+1)`
      -- relation over the original base field.
      calc
        c ^ (p ^ Nat.succ e) = c ^ (p * p ^ e) := by
          rw [pow_succ']
        _ = (c ^ p) ^ (p ^ e) := by
          rw [pow_mul]
        _ = (algebraMap K₁ K₂ (chosenRoot a)) ^ (p ^ e) := by
          rw [hc]
        _ = algebraMap K₁ K₂ (chosenRoot a ^ (p ^ e)) := by
          rw [map_pow]
        _ = algebraMap K K₂ a := by
          rw [hchosen_pow]
          simpa using
            congrArg (fun g : K →+* K₂ => g a) (IsScalarTower.algebraMap_eq K K₁ K₂)

/-- Helper for Lemma 10.161.13: the unique variable of `Fin 1` identifies the one-variable
multivariate polynomial owner with the `PUnit` owner used by `MvPolynomial.pUnitAlgEquiv`. -/
noncomputable abbrev fin_one_punit_equiv : Fin 1 ≃ PUnit :=
  Equiv.equivPUnit (Fin 1)

/-- Helper for Lemma 10.161.13: the one-variable multivariate polynomial ring over `K` is the
usual polynomial ring over `K`. -/
noncomputable abbrev one_variable_mvPolynomial_algEquiv
    {K : Type u} [Field K] :
    MvPolynomial (Fin 1) K ≃ₐ[K] Polynomial K :=
  (MvPolynomial.renameEquiv K fin_one_punit_equiv).trans (MvPolynomial.pUnitAlgEquiv.{u, 0} K)

/-- Helper for Lemma 10.161.13: the fraction field of the one-variable multivariate polynomial
ring over `K` identifies with the rational function field `K(X)`. -/
noncomputable abbrev one_variable_ratFunc_algEquiv
    {K : Type u} [Field K] :
    FractionRing (MvPolynomial (Fin 1) K) ≃ₐ[K] K⟮X⟯ :=
  IsFractionRing.algEquivOfAlgEquiv (one_variable_mvPolynomial_algEquiv (K := K))

/-- Helper for Lemma 10.161.13: after one finite purely inseparable coefficient extension, a
finite family of rational functions becomes `p`th powers under the source Frobenius-style
base-change map. -/
lemma ratfunc_family_pth_roots_after_finite_coefficient_extension
    {K : Type u} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p] (B : Finset K⟮X⟯) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K'),
      FiniteDimensional K K' ∧
        IsPurelyInseparable K K' ∧
          ∃ σpRat : K⟮X⟯ →+* K'⟮X⟯,
            (∀ a : K,
              σpRat (algebraMap K K⟮X⟯ a) =
                algebraMap K' K'⟮X⟯ (algebraMap K K' a)) ∧
              σpRat RatFunc.X = RatFunc.X ^ p ∧
                ∀ b ∈ B, ∃ w : K'⟮X⟯, σpRat b = w ^ p := by
  classical
  let zMv : K⟮X⟯ → FractionRing (MvPolynomial (Fin 1) K) :=
    fun z ↦ (one_variable_ratFunc_algEquiv (K := K)).symm z
  let numDen : K⟮X⟯ → MvPolynomial (Fin 1) K × MvPolynomial (Fin 1) K :=
    fun z ↦
      Classical.choose
        (exists_fraction_ring_numerator_denominator
          (k := K) (r := 1) (z := zMv z))
  have hnumDen :
      ∀ z : K⟮X⟯,
        (numDen z).2 ≠ 0 ∧
          algebraMap (MvPolynomial (Fin 1) K) (FractionRing (MvPolynomial (Fin 1) K))
              (numDen z).1 /
            algebraMap (MvPolynomial (Fin 1) K) (FractionRing (MvPolynomial (Fin 1) K))
              (numDen z).2 =
              zMv z := by
    intro z
    -- For each rational function, record one fixed numerator/denominator presentation upstairs.
    exact
      Classical.choose_spec
        (exists_fraction_ring_numerator_denominator
          (k := K) (r := 1) (z := zMv z))
  let coeffFinset : MvPolynomial (Fin 1) K → Finset K := fun f ↦ f.support.image f.coeff
  let C : Finset K :=
    B.attach.biUnion fun z ↦ coeffFinset (numDen z.1).1 ∪ coeffFinset (numDen z.1).2
  obtain ⟨K', _, _, hfd, hpi, hroots⟩ :=
    scalar_family_pth_roots_after_finite_coefficient_extension
      (K := K) (p := p) C
  letI : CharP K' p := charP_of_injective_algebraMap (algebraMap K K').injective p
  let σpRat : K⟮X⟯ →+* K'⟮X⟯ :=
    ((one_variable_ratFunc_algEquiv (K := K')).toRingHom).comp
      ((ratFunc_frobenius_baseChangeHom (k := K) (k' := K') (r := 1) (p := p)).comp
        (one_variable_ratFunc_algEquiv (K := K)).symm.toRingHom)
  refine ⟨K', inferInstance, inferInstance, hfd, hpi, σpRat, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a
    have hsymm_const :
        (one_variable_ratFunc_algEquiv (K := K)).symm (algebraMap K K⟮X⟯ a) =
          algebraMap (MvPolynomial (Fin 1) K) (FractionRing (MvPolynomial (Fin 1) K))
            (MvPolynomial.C a) := by
      -- Transport the constant rational function back to the one-variable multivariate owner.
      change (one_variable_ratFunc_algEquiv (K := K)).symm (RatFunc.C a) =
        algebraMap (MvPolynomial (Fin 1) K) (FractionRing (MvPolynomial (Fin 1) K))
          (MvPolynomial.C a)
      simpa [one_variable_ratFunc_algEquiv, one_variable_mvPolynomial_algEquiv,
        fin_one_punit_equiv] using
        (IsFractionRing.algEquivOfAlgEquiv_algebraMap
          (h := (one_variable_mvPolynomial_algEquiv (K := K)).symm)
          (a := Polynomial.C a))
    have hforward_const :
        (one_variable_ratFunc_algEquiv (K := K'))
            (algebraMap (MvPolynomial (Fin 1) K') (FractionRing (MvPolynomial (Fin 1) K'))
              (MvPolynomial.C (algebraMap K K' a))) =
          algebraMap K' K'⟮X⟯ (algebraMap K K' a) := by
      -- The forward equivalence sends the constant multivariate polynomial back to the constant
      -- rational function.
      change
        (one_variable_ratFunc_algEquiv (K := K'))
            (algebraMap (MvPolynomial (Fin 1) K') (FractionRing (MvPolynomial (Fin 1) K'))
              (MvPolynomial.C (algebraMap K K' a))) =
          RatFunc.C (algebraMap K K' a)
      simpa [one_variable_ratFunc_algEquiv, one_variable_mvPolynomial_algEquiv,
        fin_one_punit_equiv] using
        (IsFractionRing.algEquivOfAlgEquiv_algebraMap
          (h := one_variable_mvPolynomial_algEquiv (K := K'))
          (a := MvPolynomial.C (algebraMap K K' a)))
    -- The explicit Frobenius-style base change preserves constants via coefficient extension.
    calc
      σpRat (algebraMap K K⟮X⟯ a) =
          (one_variable_ratFunc_algEquiv (K := K'))
            (ratFunc_frobenius_baseChangeHom (k := K) (k' := K') (r := 1) (p := p)
              ((one_variable_ratFunc_algEquiv (K := K)).symm
                (algebraMap K K⟮X⟯ a))) := by
        rfl
      _ =
          (one_variable_ratFunc_algEquiv (K := K'))
            (ratFunc_frobenius_baseChangeHom (k := K) (k' := K') (r := 1) (p := p)
              (algebraMap (MvPolynomial (Fin 1) K) (FractionRing (MvPolynomial (Fin 1) K))
                (MvPolynomial.C a))) := by
        rw [hsymm_const]
      _ =
          (one_variable_ratFunc_algEquiv (K := K'))
            (algebraMap (MvPolynomial (Fin 1) K') (FractionRing (MvPolynomial (Fin 1) K'))
              (MvPolynomial.C (algebraMap K K' a))) := by
        delta ratFunc_frobenius_baseChangeHom IsFractionRing.map
        simp [MvPolynomial.map_C]
      _ = algebraMap K' K'⟮X⟯ (algebraMap K K' a) := hforward_const
  · have hsymm_X :
        (one_variable_ratFunc_algEquiv (K := K)).symm RatFunc.X =
          algebraMap (MvPolynomial (Fin 1) K) (FractionRing (MvPolynomial (Fin 1) K))
            (MvPolynomial.X 0) := by
      -- The inverse transport sends the rational-function variable to the unique multivariate
      -- variable.
      rw [← RatFunc.algebraMap_X]
      simpa [one_variable_ratFunc_algEquiv, one_variable_mvPolynomial_algEquiv,
        fin_one_punit_equiv] using
        (IsFractionRing.algEquivOfAlgEquiv_algebraMap
          (h := (one_variable_mvPolynomial_algEquiv (K := K)).symm)
          (a := Polynomial.X))
    have hforward_Xpow :
        (one_variable_ratFunc_algEquiv (K := K'))
            (algebraMap (MvPolynomial (Fin 1) K') (FractionRing (MvPolynomial (Fin 1) K'))
              ((MvPolynomial.X 0) ^ p)) =
          RatFunc.X ^ p := by
      -- After transporting forward, the unique multivariate variable again becomes `RatFunc.X`.
      calc
        (one_variable_ratFunc_algEquiv (K := K'))
            (algebraMap (MvPolynomial (Fin 1) K') (FractionRing (MvPolynomial (Fin 1) K'))
              ((MvPolynomial.X 0) ^ p)) =
            algebraMap (Polynomial K') K'⟮X⟯
              ((one_variable_mvPolynomial_algEquiv (K := K')) ((MvPolynomial.X 0) ^ p)) := by
          simpa [one_variable_ratFunc_algEquiv] using
            (IsFractionRing.algEquivOfAlgEquiv_algebraMap
              (h := one_variable_mvPolynomial_algEquiv (K := K'))
              (a := (MvPolynomial.X 0) ^ p))
        _ = algebraMap (Polynomial K') K'⟮X⟯ (Polynomial.X ^ p : Polynomial K') := by
          congr 1
          simp [one_variable_mvPolynomial_algEquiv, fin_one_punit_equiv]
        _ = RatFunc.X ^ p := by
          rw [← RatFunc.algebraMap_X, map_pow]
    -- The explicit Frobenius-style base change sends the variable to its `p`th power.
    calc
      σpRat RatFunc.X =
          (one_variable_ratFunc_algEquiv (K := K'))
            (ratFunc_frobenius_baseChangeHom (k := K) (k' := K') (r := 1) (p := p)
              ((one_variable_ratFunc_algEquiv (K := K)).symm RatFunc.X)) := by
        rfl
      _ =
          (one_variable_ratFunc_algEquiv (K := K'))
            (ratFunc_frobenius_baseChangeHom (k := K) (k' := K') (r := 1) (p := p)
              (algebraMap (MvPolynomial (Fin 1) K) (FractionRing (MvPolynomial (Fin 1) K))
                (MvPolynomial.X 0))) := by
        rw [hsymm_X]
      _ =
          (one_variable_ratFunc_algEquiv (K := K'))
            (algebraMap (MvPolynomial (Fin 1) K') (FractionRing (MvPolynomial (Fin 1) K'))
              ((MvPolynomial.X 0) ^ p)) := by
        delta ratFunc_frobenius_baseChangeHom IsFractionRing.map
        simp [MvPolynomial.expand_X]
      _ = RatFunc.X ^ p := hforward_Xpow
  · intro b hb
    have hnum :
        ∀ d ∈ (numDen b).1.support, ∃ c : K', c ^ p = algebraMap K K' ((numDen b).1.coeff d) := by
      intro d hd
      have hmem_num : (numDen b).1.coeff d ∈ C := by
        -- The numerator coefficients were inserted into the single finite scalar set `C`.
        refine Finset.mem_biUnion.mpr ?_
        refine ⟨⟨b, hb⟩, by simp, ?_⟩
        exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_image.mpr ⟨d, hd, rfl⟩
      exact hroots _ hmem_num
    have hden :
        ∀ d ∈ (numDen b).2.support, ∃ c : K', c ^ p = algebraMap K K' ((numDen b).2.coeff d) := by
      intro d hd
      have hmem_den : (numDen b).2.coeff d ∈ C := by
        -- The denominator coefficients lie in the same finite scalar set.
        refine Finset.mem_biUnion.mpr ?_
        refine ⟨⟨b, hb⟩, by simp, ?_⟩
        exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_image.mpr ⟨d, hd, rfl⟩
      exact hroots _ hmem_den
    obtain ⟨w, hw⟩ :=
      ratFunc_image_is_pth_power_of_repr_coeff_roots
        (k := K) (k' := K') (r := 1) (p := p)
        (z := zMv b) (a := (numDen b).1) (b := (numDen b).2)
        (hnumDen b).1 (hnumDen b).2 hnum hden
    refine ⟨(one_variable_ratFunc_algEquiv (K := K')) w, ?_⟩
    -- Transport the `p`th-power witness back from the `Fin 1` owner to the `RatFunc` owner.
    calc
      σpRat b =
          (one_variable_ratFunc_algEquiv (K := K'))
            (ratFunc_frobenius_baseChangeHom (k := K) (k' := K') (r := 1) (p := p) (zMv b)) := by
        rfl
      _ = (one_variable_ratFunc_algEquiv (K := K')) (w ^ p) := by
        rw [hw]
      _ = ((one_variable_ratFunc_algEquiv (K := K')) w) ^ p := by
        simp

/-- Helper for Lemma 10.161.13: iterating the one-step rational-function base change produces a
common `p^e`-power presentation after one finite purely inseparable coefficient extension. -/
lemma ratfunc_family_qpow_roots_after_finite_coefficient_extension
    {K : Type u} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p] (B : Finset K⟮X⟯) :
    ∀ e : ℕ,
      ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K'),
        FiniteDimensional K K' ∧
          IsPurelyInseparable K K' ∧
            ∃ σqRat : K⟮X⟯ →+* K'⟮X⟯,
              (∀ a : K,
                σqRat (algebraMap K K⟮X⟯ a) =
                  algebraMap K' K'⟮X⟯ (algebraMap K K' a)) ∧
                σqRat RatFunc.X = RatFunc.X ^ (p ^ e) ∧
                  ∀ b ∈ B, ∃ w : K'⟮X⟯, σqRat b = w ^ (p ^ e) := by
  classical
  intro e
  induction e with
  | zero =>
      refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, RingHom.id _, ?_⟩
      refine ⟨?_, ?_, ?_⟩
      · intro a
        -- At exponent `p^0 = 1`, the identity map preserves coefficients exactly.
        simp
      · -- The identity map also keeps the rational-function variable fixed.
        simp
      · intro b hb
        -- With exponent `p^0 = 1`, every element is already its own witness.
        exact ⟨b, by simp⟩
  | succ e ih =>
      obtain ⟨K₁, _, _, hfd₁, hpi₁, σ₁, hcoeff₁, hX₁, hroots₁⟩ := ih
      letI : CharP K₁ p := charP_of_injective_algebraMap (algebraMap K K₁).injective p
      let chosenRoot : K⟮X⟯ → K₁⟮X⟯ := fun b ↦
        if hb : b ∈ B then Classical.choose (hroots₁ b hb) else 0
      let B₁ : Finset K₁⟮X⟯ := B.image chosenRoot
      obtain ⟨K₂, _, _, hfd₂, hpi₂, σ₂, hcoeff₂, hX₂, hroots₂⟩ :=
        ratfunc_family_pth_roots_after_finite_coefficient_extension
          (K := K₁) (p := p) B₁
      letI : Algebra K K₂ :=
        (RingHom.comp (algebraMap K₁ K₂) (algebraMap K K₁)).toAlgebra
      letI : IsScalarTower K K₁ K₂ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
      have hfd : FiniteDimensional K K₂ := by
        letI : FiniteDimensional K K₁ := hfd₁
        letI : FiniteDimensional K₁ K₂ := hfd₂
        exact FiniteDimensional.trans K K₁ K₂
      have hpi : IsPurelyInseparable K K₂ := by
        letI : IsPurelyInseparable K K₁ := hpi₁
        letI : IsPurelyInseparable K₁ K₂ := hpi₂
        exact IsPurelyInseparable.trans K K₁ K₂
      let σqRat : K⟮X⟯ →+* K₂⟮X⟯ := σ₂.comp σ₁
      refine ⟨K₂, inferInstance, inferInstance, hfd, hpi, σqRat, ?_⟩
      refine ⟨?_, ?_, ?_⟩
      · intro a
        -- The iterated base change still sends coefficients through the composite field
        -- extension `K → K₁ → K₂`.
        calc
          σqRat (algebraMap K K⟮X⟯ a) = σ₂ (σ₁ (algebraMap K K⟮X⟯ a)) := by
            rfl
          _ = σ₂ (algebraMap K₁ K₁⟮X⟯ (algebraMap K K₁ a)) := by
            rw [hcoeff₁ a]
          _ = algebraMap K₂ K₂⟮X⟯ (algebraMap K₁ K₂ (algebraMap K K₁ a)) := by
            rw [hcoeff₂ (algebraMap K K₁ a)]
          _ = algebraMap K₂ K₂⟮X⟯ (algebraMap K K₂ a) := by
            have hcomp :
                algebraMap K₁ K₂ (algebraMap K K₁ a) = algebraMap K K₂ a := by
              simpa using
                congrArg (fun g : K →+* K₂ => g a) (IsScalarTower.algebraMap_eq K K₁ K₂)
            rw [hcomp]
      · -- The iterated Frobenius-style base change sends `RatFunc.X` to `RatFunc.X^(p^(e+1))`.
        calc
          σqRat RatFunc.X = σ₂ (σ₁ RatFunc.X) := by
            rfl
          _ = σ₂ (RatFunc.X ^ (p ^ e)) := by
            rw [hX₁]
          _ = (σ₂ RatFunc.X) ^ (p ^ e) := by
            rw [map_pow]
          _ = (RatFunc.X ^ p) ^ (p ^ e) := by
            rw [hX₂]
          _ = RatFunc.X ^ (p * p ^ e) := by
            rw [pow_mul]
          _ = RatFunc.X ^ (p ^ Nat.succ e) := by
            rw [pow_succ']
      · intro b hb
        have hchosen_mem : chosenRoot b ∈ B₁ := by
          exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
        obtain ⟨c, hc⟩ := hroots₂ (chosenRoot b) hchosen_mem
        have hchosen_pow : σ₁ b = chosenRoot b ^ (p ^ e) := by
          -- The induction hypothesis provides the first-stage common `p^e`-power witness.
          simp only [chosenRoot, hb, dite_true]
          exact Classical.choose_spec (hroots₁ b hb)
        refine ⟨c, ?_⟩
        -- Compose the first-stage `p^e` witness with the second-stage `p`th-root witness.
        calc
          σqRat b = σ₂ (σ₁ b) := by
            rfl
          _ = σ₂ (chosenRoot b ^ (p ^ e)) := by
            rw [hchosen_pow]
          _ = (σ₂ (chosenRoot b)) ^ (p ^ e) := by
            rw [map_pow]
          _ = (c ^ p) ^ (p ^ e) := by
            rw [hc]
          _ = c ^ (p * p ^ e) := by
            rw [pow_mul]
          _ = c ^ (p ^ Nat.succ e) := by
            rw [pow_succ']

/-- Helper for Lemma 10.161.13: a chosen root of the minimal polynomial of `a` over `M`
determines an `M`-algebra map from the simple extension `M⟮a⟯`. -/
lemma adjoin_simple_algHom_of_aeval_eq_zero
    {M : Type*} {L : Type*} {E : Type*}
    [Field M] [Field L] [Field E] [Algebra M L] [Algebra M E]
    {a : L} {w : E}
    (ha : IsIntegral M a)
    (hw : Polynomial.aeval w (minpoly M a) = 0) :
    ∃ φ : ↥(IntermediateField.adjoin M ({a} : Set L)) →ₐ[M] E,
      φ (IntermediateField.AdjoinSimple.gen M a) = w := by
  let root : {x // x ∈ (minpoly M a).aroots E} := by
    refine ⟨w, ?_⟩
    -- Package the chosen root as an element of the `aroots` set of the minimal polynomial.
    rw [Polynomial.mem_aroots]
    exact ⟨minpoly.ne_zero ha, hw⟩
  refine ⟨
    (IntermediateField.algHomAdjoinIntegralEquiv
      (F := M) (K := E) (α := a) ha).symm root,
    ?_⟩
  -- The canonical inverse of `algHomAdjoinIntegralEquiv` sends the adjoin generator to the
  -- chosen root.
  simpa [root] using
    (IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen
      (F := M) (K := E) (α := a) (h := ha) root)

/-- Helper for Lemma 10.161.13: if the minimal polynomial of `a` is `X^(q^n) - C b`, then any
element satisfying the same `q^n`-power relation yields an `M`-algebra map out of `M⟮a⟯`. -/
lemma adjoin_simple_algHom_of_minpoly_eq_X_pow_sub_C
    {M : Type*} {L : Type*} {E : Type*}
    [Field M] [Field L] [Field E] [Algebra M L] [Algebra M E]
    {a : L} {w : E} {q n : ℕ} {b : M}
    (hq : 0 < q)
    (hmin : minpoly M a = Polynomial.X ^ (q ^ n) - Polynomial.C b)
    (hw : w ^ (q ^ n) = algebraMap M E b) :
    ∃ φ : ↥(IntermediateField.adjoin M ({a} : Set L)) →ₐ[M] E,
      φ (IntermediateField.AdjoinSimple.gen M a) = w := by
  have ha : IsIntegral M a := by
    -- Since `minpoly M a` is visibly nonzero, the defining characterization of `minpoly`
    -- forces `a` to be integral over `M`.
    apply (minpoly.ne_zero_iff (A := M) (B := L) (x := a)).1
    rw [hmin]
    exact Polynomial.X_pow_sub_C_ne_zero (pow_pos hq n) b
  -- The displayed power relation is exactly the evaluation of the transported minimal polynomial
  -- at `w`, so the previous root-to-map helper applies.
  refine adjoin_simple_algHom_of_aeval_eq_zero (M := M) (a := a) (w := w) ha ?_
  rw [hmin, Polynomial.aeval_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C, hw, sub_self]

/-- Helper for Lemma 10.161.13: in exponential characteristic `p`, the map `z ↦ z^(p^n)` is
injective on reduced rings. -/
lemma qpow_injective
    {A : Type*} [CommRing A] [IsReduced A] {p n : ℕ} [ExpChar A p] :
    Function.Injective (fun z : A ↦ z ^ (p ^ n)) := by
  intro x y hxy
  -- Repackage the equality as an equality after iterated Frobenius and use reducedness.
  exact ((frobenius_inj A p).iterate n) (by simpa [iterate_frobenius] using hxy)

/-- Helper for Lemma 10.161.13: purely inseparable extensions stay purely inseparable after
enlarging the base to an intermediate field. -/
lemma isPurelyInseparable_over_intermediate
    {Kx : Type*} {L : Type*} [Field Kx] [Field L] [Algebra Kx L]
    {p : ℕ} [Fact p.Prime] [CharP Kx p] [IsPurelyInseparable Kx L]
    (M : IntermediateField Kx L) :
    IsPurelyInseparable M L := by
  rw [isPurelyInseparable_iff_pow_mem M p]
  intro x
  -- A `p^n`-power already landing in `Kx` certainly lands in every intermediate field above `Kx`.
  obtain ⟨n, hn⟩ := IsPurelyInseparable.pow_mem Kx p x
  rcases hn with ⟨c, hc⟩
  refine ⟨n, ⟨algebraMap Kx M c, ?_⟩⟩
  change algebraMap Kx L c = x ^ (p ^ n)
  exact hc

/-- Helper for Lemma 10.161.13: if the minimal polynomial of `x` over an intermediate field is
`X^(p^n) - C b` and `x^(p^e)` already comes from the original base, then necessarily `n ≤ e`. -/
lemma minpoly_exponent_le_common_exponent
    {Kx : Type*} {L : Type*} [Field Kx] [Field L] [Algebra Kx L]
    {M : IntermediateField Kx L}
    {p e n : ℕ} [Fact p.Prime] [CharP Kx p]
    {x : L} {b : M} {c : Kx}
    (hmin : minpoly M x = Polynomial.X ^ (p ^ n) - Polynomial.C b)
    (hxq : x ^ (p ^ e) = algebraMap Kx L c) :
    n ≤ e := by
  have hpprime : Nat.Prime p := Fact.out
  have hp0 : p ≠ 0 := Nat.ne_of_gt hpprime.pos
  have hroot :
      Polynomial.aeval x (Polynomial.X ^ (p ^ e) - Polynomial.C (algebraMap Kx M c)) = 0 := by
    -- The common `p^e`-power relation makes `x` a root of the larger base polynomial.
    rw [Polynomial.aeval_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C]
    rw [hxq, IsScalarTower.algebraMap_eq Kx M L]
    change algebraMap M L (algebraMap Kx M c) - algebraMap M L (algebraMap Kx M c) = 0
    exact sub_self _
  have hdvd :
      minpoly M x ∣ Polynomial.X ^ (p ^ e) - Polynomial.C (algebraMap Kx M c) :=
    minpoly.dvd M x hroot
  have hdeg :
      (minpoly M x).natDegree ≤
        (Polynomial.X ^ (p ^ e) - Polynomial.C (algebraMap Kx M c)).natDegree :=
    Polynomial.natDegree_le_of_dvd hdvd
      (Polynomial.X_pow_sub_C_ne_zero (pow_pos hpprime.pos e) _)
  have hpow_le : p ^ n ≤ p ^ e := by
    -- Compare degrees of the minimal polynomial with the explicit polynomial annihilating `x`.
    simpa [hmin, Polynomial.natDegree_sub_C, Polynomial.natDegree_X_pow] using hdeg
  by_contra hne
  exact (not_lt_of_ge hpow_le) <|
    (Nat.pow_lt_pow_iff_right hpprime.one_lt).2 (lt_of_not_ge hne)

/-- Helper for Lemma 10.161.13: once the minimal-polynomial exponent `n` is known to satisfy
`n ≤ e`, the coefficient of `X^(p^n) - C b` has the same residual `p^(e-n)`-power as the common
base scalar. -/
lemma minpoly_coefficient_qpow_eq_base_scalar
    {Kx : Type*} {L : Type*} [Field Kx] [Field L] [Algebra Kx L]
    {M : IntermediateField Kx L}
    {p e n : ℕ} [Fact p.Prime] [CharP Kx p]
    {x : L} {b : M} {c : Kx}
    (hmin : minpoly M x = Polynomial.X ^ (p ^ n) - Polynomial.C b)
    (hxq : x ^ (p ^ e) = algebraMap Kx L c)
    (hne : n ≤ e) :
    b ^ (p ^ (e - n)) = algebraMap Kx M c := by
  have hxpn : x ^ (p ^ n) = algebraMap M L b := by
    -- Evaluating the minimal polynomial at `x` recovers the defining `p^n`-power relation.
    have hroot : Polynomial.aeval x (minpoly M x) = 0 := minpoly.aeval M x
    rw [hmin, Polynomial.aeval_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C] at hroot
    exact sub_eq_zero.mp hroot
  apply (algebraMap M L).injective
  -- Raise the `p^n`-power relation to the remaining `p^(e-n)` and compare with the common base
  -- scalar relation.
  calc
    algebraMap M L (b ^ (p ^ (e - n))) = (algebraMap M L b) ^ (p ^ (e - n)) := by
      rw [map_pow]
    _ = (x ^ (p ^ n)) ^ (p ^ (e - n)) := by
      rw [hxpn]
    _ = x ^ (p ^ n * p ^ (e - n)) := by
      rw [pow_mul]
    _ = x ^ (p ^ e) := by
      rw [← pow_add, Nat.add_sub_of_le hne]
    _ = algebraMap Kx L c := hxq
    _ = algebraMap M L (algebraMap Kx M c) := by
      rw [IsScalarTower.algebraMap_eq Kx M L]
      rfl

/-- Helper for Lemma 10.161.13: after matching the common `p^e`-power relation with the
minimal-polynomial coefficient, the chosen target root has the correct `p^n`-power to define the
simple-adjoin map. -/
lemma common_qpow_root_matches_minpoly_coefficient
    {Kx : Type*} {L : Type*} {E : Type*}
    [Field Kx] [Field L] [Field E] [Algebra Kx L] [Algebra Kx E]
    {M : IntermediateField Kx L}
    {ψ : M →ₐ[Kx] E}
    {p e n : ℕ} [Fact p.Prime] [CharP Kx p]
    {x : L} {u : E} {b : M} {c : Kx}
    (hmin : minpoly M x = Polynomial.X ^ (p ^ n) - Polynomial.C b)
    (hxq : x ^ (p ^ e) = algebraMap Kx L c)
    (hu : u ^ (p ^ e) = algebraMap Kx E c)
    (hne : n ≤ e) :
    u ^ (p ^ n) = ψ b := by
  letI : Algebra M E := ψ.toAlgebra
  letI : IsScalarTower Kx M E := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro a
    exact (ψ.commutes a).symm
  letI : CharP E p := charP_of_injective_algebraMap (algebraMap Kx E).injective p
  have hbpow :
      b ^ (p ^ (e - n)) = algebraMap Kx M c :=
    minpoly_coefficient_qpow_eq_base_scalar
      (Kx := Kx) (L := L) (M := M) (p := p) (e := e) (n := n) hmin hxq hne
  have hcompare :
      (u ^ (p ^ n)) ^ (p ^ (e - n)) = (ψ b) ^ (p ^ (e - n)) := by
    -- Both candidate images have the same remaining `p^(e-n)`-power, so Frobenius injectivity
    -- identifies them.
    calc
      (u ^ (p ^ n)) ^ (p ^ (e - n)) = u ^ (p ^ n * p ^ (e - n)) := by
        rw [pow_mul]
      _ = u ^ (p ^ e) := by
        rw [← pow_add, Nat.add_sub_of_le hne]
      _ = algebraMap Kx E c := hu
      _ = ψ (algebraMap Kx M c) := by
        exact (ψ.commutes c).symm
      _ = ψ (b ^ (p ^ (e - n))) := by
        rw [hbpow]
      _ = (ψ b) ^ (p ^ (e - n)) := by
        rw [map_pow]
  exact (qpow_injective (A := E) (p := p) (n := e - n)) hcompare

/-- Helper for Lemma 10.161.13: a chosen element `u` with the same common `p^e`-power as `x`
extends an existing `Kx`-algebra map across the simple adjunction `M⟮x⟯`. -/
lemma extend_algHom_adjoin_singleton_of_qpow_image_eq
    {Kx : Type*} {L : Type*} {E : Type*}
    [Field Kx] [Field L] [Field E] [Algebra Kx L] [Algebra Kx E]
    {M : IntermediateField Kx L}
    {ψ : M →ₐ[Kx] E}
    {p e : ℕ} [Fact p.Prime] [CharP Kx p] [IsPurelyInseparable Kx L]
    {x : L} {u : E} {c : Kx}
    (hxq : x ^ (p ^ e) = algebraMap Kx L c)
    (hu : u ^ (p ^ e) = algebraMap Kx E c) :
    ∃ φ : ↥((IntermediateField.adjoin M ({x} : Set L)).restrictScalars Kx) →ₐ[Kx] E,
      φ (IntermediateField.AdjoinSimple.gen M x) = u := by
  letI : IsPurelyInseparable M L :=
    isPurelyInseparable_over_intermediate (Kx := Kx) (L := L) (p := p) M
  obtain ⟨n, b, hmin⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C M p x
  have hne :
      n ≤ e :=
    minpoly_exponent_le_common_exponent
      (Kx := Kx) (L := L) (M := M) (p := p) (e := e) (n := n) hmin hxq
  letI : Algebra M E := ψ.toAlgebra
  letI : IsScalarTower Kx M E := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro a
    exact (ψ.commutes a).symm
  have hu' : u ^ (p ^ n) = algebraMap M E b := by
    -- The common `p^e`-power witness now matches the minimal-polynomial coefficient over `M`.
    simpa using
      (common_qpow_root_matches_minpoly_coefficient
        (Kx := Kx) (L := L) (E := E) (M := M) (ψ := ψ)
        (p := p) (e := e) (n := n) hmin hxq hu hne)
  obtain ⟨φ, hφ⟩ :=
    adjoin_simple_algHom_of_minpoly_eq_X_pow_sub_C
      (M := M) (L := L) (E := E) (a := x) (w := u) (q := p) (n := n) (b := b)
      (hq := Nat.Prime.pos (Fact.out : Nat.Prime p)) hmin hu'
  -- Restrict scalars back to `Kx` to obtain the one-step extension used in the finite-adjoin
  -- induction.
  refine ⟨φ.restrictScalars Kx, ?_⟩
  simpa using hφ

/-- Helper for Lemma 10.161.13: a finite generating family with one common `p^e`-power relation
can be reindexed by `Fin n` without changing the generated top field. -/
lemma generator_tuple_with_common_qpow
    {Kx : Type*} {L : Type*} [Field Kx] [Field L] [Algebra Kx L]
    {p e : ℕ}
    (s : Finset L)
    (hs_top : IntermediateField.adjoin Kx (↑s : Set L) = ⊤)
    (hs_pow : ∀ a ∈ s, ∃ c : Kx, a ^ (p ^ e) = algebraMap Kx L c) :
    ∃ (n : ℕ) (α : Fin n → L) (c : Fin n → Kx),
      Situation_9_12_7.stage Kx α (Fin.last n) = ⊤ ∧
        ∀ i, α i ^ (p ^ e) = algebraMap Kx L (c i) := by
  classical
  let ι := {a // a ∈ s}
  let eι : ι ≃ Fin s.card := Finset.equivFin s
  have hs_pow' : ∀ a : ι, ∃ c : Kx, (a : L) ^ (p ^ e) = algebraMap Kx L c := by
    intro a
    exact hs_pow a a.2
  choose coeff hcoeff using hs_pow'
  refine ⟨s.card, fun i ↦ (eι.symm i : L), fun i ↦ coeff (eι.symm i), ?_, ?_⟩
  · have hrange :
        Set.range (fun i : Fin s.card ↦ ((eι.symm i : ι) : L)) = (↑s : Set L) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact (eι.symm i).2
      · intro hx
        refine ⟨eι ⟨x, hx⟩, ?_⟩
        simp
    -- At the last stage, the Chapter 9 tower adjoins exactly the full image of the tuple.
    have hstage_range :
        Situation_9_12_7.stage Kx (fun i : Fin s.card ↦ ((eι.symm i : ι) : L)) (Fin.last s.card) =
          IntermediateField.adjoin Kx
            (Set.range fun i : Fin s.card ↦ ((eι.symm i : ι) : L)) := by
      unfold Situation_9_12_7.stage
      congr
      ext x
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i, i.2, rfl⟩
    calc
      Situation_9_12_7.stage Kx (fun i : Fin s.card ↦ ((eι.symm i : ι) : L)) (Fin.last s.card) =
          IntermediateField.adjoin Kx
            (Set.range fun i : Fin s.card ↦ ((eι.symm i : ι) : L)) := hstage_range
      _ = IntermediateField.adjoin Kx (↑s : Set L) := by
        rw [hrange]
      _ = ⊤ := hs_top
  · intro i
    -- The tuple coordinates inherit the common `p^e`-power relation from the original finite set.
    simpa using hcoeff (eι.symm i)

/-- Helper for Lemma 10.161.13: if `x` and `u` have the same common `p^e`-power over `Kx`, then
`u` is a root of the minimal polynomial of `x` transported along any intermediate-stage
embedding. -/
lemma qpow_image_is_root_of_mapped_minpoly
    {Kx : Type*} {L : Type*} {E : Type*}
    [Field Kx] [Field L] [Field E] [Algebra Kx L] [Algebra Kx E]
    {M : IntermediateField Kx L}
    {ψ : M →ₐ[Kx] E}
    {p e : ℕ} [Fact p.Prime] [CharP Kx p] [IsPurelyInseparable Kx L]
    {x : L} {u : E} {c : Kx} :
    x ^ (p ^ e) = algebraMap Kx L c →
      u ^ (p ^ e) = algebraMap Kx E c →
        ((minpoly M x).map ψ.toRingHom).IsRoot u := by
  intro hxq hu
  letI : IsPurelyInseparable M L :=
    isPurelyInseparable_over_intermediate (Kx := Kx) (L := L) (p := p) M
  obtain ⟨n, b, hmin⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C M p x
  have hne :
      n ≤ e :=
    minpoly_exponent_le_common_exponent
      (Kx := Kx) (L := L) (M := M) (p := p) (e := e) (n := n) hmin hxq
  have hu' :
      u ^ (p ^ n) = ψ b := by
    -- Match the chosen target root with the coefficient determined by the minimal polynomial.
    simpa using
      (common_qpow_root_matches_minpoly_coefficient
        (Kx := Kx) (L := L) (E := E) (M := M) (ψ := ψ)
        (p := p) (e := e) (n := n) hmin hxq hu hne)
  -- After rewriting the minimal polynomial to its purely inseparable shape, the root check is
  -- the displayed `p^n`-power equality.
  rw [hmin]
  simpa [Polynomial.IsRoot, hu'] using
    (show (Polynomial.X ^ (p ^ n) - Polynomial.C (ψ b)).eval u = 0 by
      rw [Polynomial.eval_sub, Polynomial.eval_X_pow, Polynomial.eval_C, hu', sub_self])

/-- Helper for Lemma 10.161.13: matching common `p^e`-power data on a generator tuple produces
the Chapter 9 successive-root tuple needed for the global stage embedding. -/
lemma successive_root_tuple_of_common_qpow_data
    {Kx : Type*} {L : Type*} {E : Type*}
    [Field Kx] [Field L] [Field E] [Algebra Kx L] [Algebra Kx E]
    [FiniteDimensional Kx L]
    {p e : ℕ} [Fact p.Prime] [CharP Kx p] [IsPurelyInseparable Kx L]
    {n : ℕ} (α : Fin n → L) (u : Fin n → E) (c : Fin n → Kx)
    (hαq : ∀ i, α i ^ (p ^ e) = algebraMap Kx L (c i))
    (huq : ∀ i, u i ^ (p ^ e) = algebraMap Kx E (c i)) :
    Situation_9_12_7.IsSuccessiveRootTuple Kx α u := by
  have hprefix :
      ∀ m : ℕ, ∀ hm : m ≤ n,
        Situation_9_12_7.IsSuccessiveRootTupleUpTo Kx α
          ⟨m, Nat.lt_succ_of_le hm⟩ u := by
    intro m
    induction m with
    | zero =>
        intro hm
        -- The stage-zero clause is tautological in the recursive Chapter 9 package.
        simpa using
          Situation_9_12_7.isSuccessiveRootTupleUpTo_zero (F := Kx) (α := α) u
    | succ m ihm =>
        intro hm
        let i : Fin n := ⟨m, Nat.lt_of_succ_le hm⟩
        have hprev :
            Situation_9_12_7.IsSuccessiveRootTupleUpTo Kx α i.castSucc u :=
          ihm (Nat.le_of_succ_le hm)
        refine (Situation_9_12_7.isSuccessiveRootTupleUpTo_succ_iff
          (F := Kx) (α := α) i u).2 ?_
        refine ⟨hprev, ?_⟩
        intro hβ
        -- The stage root condition is exactly the transported minimal-polynomial root statement.
        exact qpow_image_is_root_of_mapped_minpoly
          (Kx := Kx) (L := L) (E := E)
          (M := Situation_9_12_7.stage Kx α i.castSucc)
          (ψ := Situation_9_12_7.stageEmbedding Kx α i.castSucc u hβ)
          (p := p) (e := e) (x := α i) (u := u i) (c := c i)
          (hαq i) (huq i)
  -- The final stage `Fin.last n` is the full successive-root predicate.
  simpa [Situation_9_12_7.IsSuccessiveRootTuple] using hprefix n le_rfl

/-- Helper for Lemma 10.161.13: once a finite purely inseparable extension `L / Frac(R[X])`
embeds over `Frac(R[X])` into an ambient field `Frac(S[X])` whose normalization over `R[X]` is
already known to be finite, finiteness descends to the integral closure of `R[X]` in `L`. -/
lemma finite_integralClosure_of_cover_into_twisted_polynomial_fractionRing
    {S : Type u} [CommRing S] [IsDomain S]
    {L : Type u} [Field L]
    [Algebra (Polynomial R) L] [Algebra (FractionRing (Polynomial R)) L]
    [IsScalarTower (Polynomial R) (FractionRing (Polynomial R)) L]
    [Algebra (Polynomial R) (FractionRing (Polynomial S))]
    [Algebra (FractionRing (Polynomial R)) (FractionRing (Polynomial S))]
    [IsScalarTower (Polynomial R) (FractionRing (Polynomial R))
      (FractionRing (Polynomial S))]
    (φ : L →ₐ[FractionRing (Polynomial R)] FractionRing (Polynomial S))
    (hfinite_target :
      Module.Finite (Polynomial R)
        (integralClosure (Polynomial R) (FractionRing (Polynomial S)))) :
    Module.Finite (Polynomial R) (integralClosure (Polynomial R) L) := by
  let φR : L →ₐ[Polynomial R] FractionRing (Polynomial S) :=
    φ.restrictScalars (Polynomial R)
  -- Restrict scalars along `R[X] → Frac(R[X])` and then apply the standard finite-normalization
  -- descent lemma to the chosen ambient cover.
  exact
    finite_of_integralClosure_map_to_larger_base
      (R := Polynomial R) (S := Polynomial R) φR φR.injective hfinite_target

/-- Helper for Lemma 10.161.13: freezing the twisted localization package on `Frac(S[X])`
turns the ambient normalization finiteness theorem into a transport-stable statement. -/
lemma twisted_polynomial_fractionRing_integralClosure_finite_explicit
    {S : Type u} [CommRing S] [Nontrivial S] [IsDomain S]
    [Algebra R S] [Module.Finite R S] [IsIntegrallyClosed S]
    {q : ℕ} (hq : 0 < q) (hRS : Function.Injective (algebraMap R S)) :
    let σpoly : FractionRing (Polynomial R) →+* FractionRing (Polynomial S) :=
      twisted_polynomial_fractionRing_localization (R := R) (S := S) hq hRS
    let fσ : Polynomial R →+* FractionRing (Polynomial S) :=
      RingHom.comp σpoly
        (algebraMap (Polynomial R) (FractionRing (Polynomial R)))
    let _ : Algebra (FractionRing (Polynomial R)) (FractionRing (Polynomial S)) := σpoly.toAlgebra
    let _ : Algebra (Polynomial R) (FractionRing (Polynomial S)) := fσ.toAlgebra
    let _ : IsScalarTower (Polynomial R) (FractionRing (Polynomial R))
        (FractionRing (Polynomial S)) :=
      IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
    Module.Finite (Polynomial R)
      (integralClosure (Polynomial R) (FractionRing (Polynomial S))) := by
  let σpoly : FractionRing (Polynomial R) →+* FractionRing (Polynomial S) :=
    twisted_polynomial_fractionRing_localization (R := R) (S := S) hq hRS
  let fσ : Polynomial R →+* FractionRing (Polynomial S) :=
    RingHom.comp σpoly
      (algebraMap (Polynomial R) (FractionRing (Polynomial R)))
  letI : Algebra (FractionRing (Polynomial R)) (FractionRing (Polynomial S)) := σpoly.toAlgebra
  letI : Algebra (Polynomial R) (FractionRing (Polynomial S)) := fσ.toAlgebra
  letI : IsScalarTower (Polynomial R) (FractionRing (Polynomial R))
      (FractionRing (Polynomial S)) :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let feval : Polynomial R →+* FractionRing (Polynomial S) :=
    RingHom.comp (algebraMap (Polynomial S) (FractionRing (Polynomial S)))
      (Polynomial.eval₂RingHom (Polynomial.C.comp (algebraMap R S))
        (Polynomial.X ^ q : Polynomial S))
  have hfeq : feval = fσ := by
    -- On every polynomial numerator, the localized twisted map is exactly the polynomial
    -- evaluation map followed by localization.
    apply RingHom.ext
    intro p
    simpa [feval, fσ] using
      (twisted_polynomial_fractionRing_localization_algebraMap
        (R := R) (S := S) hq hRS p).symm
  have hfinite_eval :
      let _ : Algebra (Polynomial R) (FractionRing (Polynomial S)) := feval.toAlgebra
      Module.Finite (Polynomial R)
        (integralClosure (Polynomial R) (FractionRing (Polynomial S))) := by
    -- The ambient finiteness theorem is stated for the evaluation-form polynomial algebra.
    simpa [feval] using
      (twisted_polynomial_fractionRing_integralClosure_finite
        (R := R) (S := S) (q := q) hq)
  -- Identify the localization-form algebra package with the evaluation-form package once and then
  -- reuse the theorem proved under the latter.
  have hAlg : feval.toAlgebra = fσ.toAlgebra := by
    simpa using congrArg RingHom.toAlgebra hfeq
  let P :
      Algebra (Polynomial R) (FractionRing (Polynomial S)) → Prop :=
    fun alg =>
      Module.Finite (Polynomial R)
        (@integralClosure (Polynomial R) (FractionRing (Polynomial S))
          Polynomial.commRing OreLocalization.instCommRing alg)
  have hfinite_eval' : P feval.toAlgebra := hfinite_eval
  exact Eq.ndrec hfinite_eval' hAlg

-- Proof sketch: reduce first to the case where `R` is normal using the finite-extension descent
-- lemma `isN2Ring_of_finite_extension`. In characteristic zero, combine
-- `isN1Ring_polynomial` with Lemma `10.161.11`. In characteristic `p > 0`, use Lemma `10.161.12`
-- to reduce to finite purely inseparable extensions and identify the relevant integral closure
-- with a polynomial ring `R'[X^(1/q)]` over a finite integral extension `R' / R`, which is finite
-- over `R[X]`.
/-- Lemma 10.161.13 (2): if `R` is a Noetherian domain and `R` is `N-2`, then the polynomial ring
`R[X]` is `N-2`. -/
@[stacks 032O]
theorem isN2Ring_polynomial
    [IsN2Ring R] :
    IsN2Ring (Polynomial R) := by
  by_cases hchar0 : ringChar (FractionRing R) = 0
  · haveI : CharZero (FractionRing R) :=
      (CharP.ringChar_zero_iff_CharZero (R := FractionRing R)).1 hchar0
    haveI : CharZero R := by
      refine charZero_of_inj_zero ?_
      intro n hn
      apply CharZero.cast_injective (R := FractionRing R)
      simpa using congrArg (algebraMap R (FractionRing R)) hn
    haveI : CharZero (Polynomial R) := inferInstance
    haveI : CharZero (FractionRing (Polynomial R)) :=
      IsFractionRing.charZero_of_isFractionRing (Polynomial R)
    have hN1 : IsN1Ring (Polynomial R) := isN1Ring_polynomial (R := R)
    -- In characteristic zero, the polynomial case is exactly Lemma 10.161.11 once part (1) is known.
    exact
      (isN1Ring_iff_isN2Ring_of_noetherian_of_fractionRing_charZero
        (R := Polynomial R)).1 hN1
  · let p := ringChar (FractionRing R)
    classical
    have hp0 : p ≠ 0 := hchar0
    haveI : CharP (FractionRing R) p := ringChar.of_eq (R := FractionRing R) rfl
    haveI : NeZero p := ⟨hp0⟩
    haveI : Fact p.Prime := CharP.char_is_prime_of_pos (FractionRing R) p
    have hp_cast_zero : (p : R) = 0 := by
      apply IsFractionRing.injective R (FractionRing R)
      simpa using (CharP.cast_eq_zero (FractionRing R) p)
    haveI : CharP R p :=
      (CharP.charP_iff_prime_eq_zero (R := R) (p := p) (Fact.out)).2 hp_cast_zero
    haveI : CharP (Polynomial R) p := inferInstance
    haveI : CharP (FractionRing (Polynomial R)) p :=
      IsFractionRing.charP_of_isFractionRing (Polynomial R) p
    refine
      (isN2Ring_iff_integralClosure_finite_for_finite_purelyInseparable_extensions
        (R := Polynomial R)).2 ?_
    intro L _ _ _ _ _ _
    obtain ⟨s, e, hs_top, hs_pow⟩ :=
      generating_finset_with_common_qpow_mem_base
        (Kx := FractionRing (Polynomial R)) (L := L) (p := p)
    obtain ⟨n, α, c, hα_top, hαq⟩ :=
      generator_tuple_with_common_qpow
        (Kx := FractionRing (Polynomial R)) (L := L) (p := p) (e := e) s hs_top hs_pow
    let B : Finset (RatFunc (FractionRing R)) :=
      Finset.univ.image fun i : Fin n ↦
        fractionRing_polynomial_to_ratFunc_transport (R := R) (c i)
    obtain ⟨K', _, _, hfdK', hpiK', σqRat, hcoeffRat, hXRat, hrootsRat⟩ :=
      ratfunc_family_qpow_roots_after_finite_coefficient_extension
        (K := FractionRing R) (p := p) B e
    letI : Algebra R K' :=
      (RingHom.comp (algebraMap (FractionRing R) K') (algebraMap R (FractionRing R))).toAlgebra
    letI : IsScalarTower R (FractionRing R) K' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let S := integralClosure R K'
    letI : Module.Finite R S := by
      letI : FiniteDimensional (FractionRing R) K' := hfdK'
      exact IsN2Ring.integralClosure_finite_of_finiteDimensional (R := R) K'
    letI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
    letI : IsFractionRing S K' :=
      integralClosure.isFractionRing_of_finite_extension
        (A := R) (K := FractionRing R) (L := K')
    letI : IsIntegrallyClosed S :=
      integralClosure.isIntegrallyClosedOfFiniteExtension
        (R := R) (K := FractionRing R) (L := K')
    let hRS : Function.Injective (algebraMap R S) :=
      algebraMap_injective_of_field_isFractionRing R S (FractionRing R) K'
    let E := FractionRing (Polynomial S)
    let hq : 0 < p ^ e := pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) e
    let σpoly :
        FractionRing (Polynomial R) →+* E :=
      twisted_polynomial_fractionRing_localization (R := R) (S := S) hq hRS
    let algKxPolyFrac :
        Algebra (FractionRing (Polynomial R)) (FractionRing (Polynomial S)) := by
      simpa [E] using (σpoly.toAlgebra :
        Algebra (FractionRing (Polynomial R)) E)
    letI : Algebra (FractionRing (Polynomial R)) (FractionRing (Polynomial S)) := algKxPolyFrac
    letI : SMul (FractionRing (Polynomial R)) (FractionRing (Polynomial S)) :=
      algKxPolyFrac.toSMul
    let algPolyFrac :
        Algebra (Polynomial R) (FractionRing (Polynomial S)) :=
      (RingHom.comp (show FractionRing (Polynomial R) →+* FractionRing (Polynomial S) by
          simpa [E] using σpoly)
        (algebraMap (Polynomial R) (FractionRing (Polynomial R)))).toAlgebra
    letI : Algebra (Polynomial R) (FractionRing (Polynomial S)) := algPolyFrac
    letI : SMul (Polynomial R) (FractionRing (Polynomial S)) := algPolyFrac.toSMul
    letI : IsScalarTower (Polynomial R) (FractionRing (Polynomial R)) (FractionRing (Polynomial S)) := by
      refine IsScalarTower.of_algebraMap_eq ?_
      intro x
      rfl
    have htransport :
        ((ratfunc_to_twisted_polynomial_fractionRing_transport (S := S) (K' := K')).comp σqRat).comp
            (fractionRing_polynomial_to_ratFunc_transport (R := R)) =
          σpoly := by
      -- This is the packaged identification of the rational-function Frobenius transport with the
      -- twisted localization on `Frac(R[X])`.
      exact qpow_ratfunc_transport_eq_twisted_polynomial_localization
        (R := R) (K' := K') (S := S) hq σqRat hcoeffRat hXRat
    have hroot_mem :
        ∀ i : Fin n,
          fractionRing_polynomial_to_ratFunc_transport (R := R) (c i) ∈ B := by
      intro i
      simpa [B] using
        (Finset.mem_image.mpr
          ⟨i, Finset.mem_univ i, rfl⟩ :
            fractionRing_polynomial_to_ratFunc_transport (R := R) (c i) ∈
              Finset.image
                (fun i : Fin n ↦ fractionRing_polynomial_to_ratFunc_transport (R := R) (c i))
                Finset.univ)
    have hroot_witness :
        ∀ i : Fin n, ∃ w : RatFunc K',
          σqRat (fractionRing_polynomial_to_ratFunc_transport (R := R) (c i)) =
            w ^ (p ^ e) := by
      intro i
      exact hrootsRat _ (hroot_mem i)
    choose w hw using hroot_witness
    let u : Fin n → E := fun i ↦
      ratfunc_to_twisted_polynomial_fractionRing_transport (S := S) (K' := K') (w i)
    have huq :
        ∀ i : Fin n,
          u i ^ (p ^ e) = algebraMap (FractionRing (Polynomial R)) E (c i) := by
      intro i
      -- Transport the chosen rational-function `p^e`th root to the twisted polynomial fraction
      -- field and rewrite via the comparison map.
      calc
        u i ^ (p ^ e) =
            ratfunc_to_twisted_polynomial_fractionRing_transport (S := S) (K' := K')
              (w i ^ (p ^ e)) := by
          rw [show u i =
              ratfunc_to_twisted_polynomial_fractionRing_transport (S := S) (K' := K') (w i) by
              rfl]
          rw [map_pow]
        _ =
            ratfunc_to_twisted_polynomial_fractionRing_transport (S := S) (K' := K')
              (σqRat (fractionRing_polynomial_to_ratFunc_transport (R := R) (c i))) := by
          rw [hw i]
        _ =
            (((ratfunc_to_twisted_polynomial_fractionRing_transport (S := S) (K' := K')).comp σqRat).comp
              (fractionRing_polynomial_to_ratFunc_transport (R := R))) (c i) := by
          rfl
        _ = σpoly (c i) := by
          rw [htransport]
        _ = algebraMap (FractionRing (Polynomial R)) E (c i) := by
          rfl
    have hsucc :
        Situation_9_12_7.IsSuccessiveRootTuple (FractionRing (Polynomial R)) α u := by
      -- The Chapter 9 recursive root conditions are exactly the common `p^e`-power relations for
      -- the source tuple and its transported target tuple.
      exact successive_root_tuple_of_common_qpow_data
        (Kx := FractionRing (Polynomial R)) (L := L) (E := E)
        (p := p) (e := e) α u c hαq huq
    have hsurj :=
      (embeddingTuple_bijective
        (F := FractionRing (Polynomial R)) (K := L) (L := E) α hα_top).2
    obtain ⟨φ, _⟩ := hsurj ⟨u, hsucc⟩
    let φ' : L →ₐ[FractionRing (Polynomial R)] FractionRing (Polynomial S) := by
      simpa [E] using φ
    have hfinite_target :=
      twisted_polynomial_fractionRing_integralClosure_finite_explicit
        (R := R) (S := S) (q := p ^ e) hq hRS
    -- Route correction: keep the source-faithful cover `φ'` and feed the explicit ambient
    -- finiteness package directly into the existing integral-closure descent helper.
    exact finite_integralClosure_of_cover_into_twisted_polynomial_fractionRing
      (R := R) (S := S) (L := L) φ' hfinite_target

end
