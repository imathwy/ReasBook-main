import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_97_1 (from Chap10) -/
open CategoryTheory

noncomputable section

universe u

-- Domain-style sampling for Lemma 10.97.1:
-- * primary domain: adic-completion exactness for short exact sequences of finite modules over a
--   Noetherian ring, together with the tensor-product description of completion.
-- * sampled owner declarations in this domain:
--   `AdicCompletion.map_injective`,
--   `AdicCompletion.map_exact`,
--   `AdicCompletion.map_surjective`,
--   `CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact`,
--   `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`.
-- * best owner abstractions: the short-complex owner `S : ShortComplex (ModuleCat R)` with
--   `hS : S.ShortExact`, the induced completed short complex `completionShortComplex I S`, and the
--   tensor comparison equivalence
--   `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`.
-- * primitive data: the short complex owner and the finite middle-term hypothesis for part `(2)`,
--   together with the module input for the tensor-comparison owner in part `(3)`.
-- * derived API: the restricted-scalars `ModuleCat R` form in part `(2)` is only a bridge;
--   parts `(1)` and `(3)` are direct owner recalls.

section injective

variable {R : Type u} [CommRing R] (I : Ideal R) [IsNoetherianRing R]
variable {K N : Type u} [AddCommGroup K] [Module R K] [AddCommGroup N] [Module R N]
variable [Module.Finite R N]

/- Lemma 10.97.1 (1): completion preserves injectivity for maps into a finite module over a
Noetherian ring. This is exactly the canonical theorem `AdicCompletion.map_injective`. -/
recall AdicCompletion.map_injective

end injective

section shortExact

variable {R : Type u} [CommRing R] (I : Ideal R) [IsNoetherianRing R]

namespace CategoryTheory.ShortComplex

variable {S : ShortComplex (ModuleCat.{u} R)}
variable [Module.Finite R S.X₂]

-- Domain-style sampling for Lemma 10.97.1 (2):
-- * primary domain: short exact sequences of modules and exactness of adic completion.
-- * sampled owner declarations:
--   `CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact`,
--   `ModuleCat.shortComplex_shortExact`,
--   `AdicCompletion.map_exact`,
--   `AdicCompletion.map_injective`.
-- * best owner abstraction: a short complex `S : ShortComplex (ModuleCat R)` with
--   `hS : S.ShortExact`, and the induced completed short complex `completionShortComplex I S`.
-- * primitive data: the owner short complex and the finite middle-term hypothesis
--   `[Module.Finite R S.X₂]`.
-- * derived API: the restricted-scalars `ModuleCat R` presentation is only a bridge.

/-- The short complex of completed modules attached to `S`. -/
abbrev completionShortComplex (S : ShortComplex (ModuleCat.{u} R)) :
    ShortComplex (ModuleCat.{u} (AdicCompletion I R)) :=
  ShortComplex.moduleCatMk
    (AdicCompletion.map I S.f.hom)
    (AdicCompletion.map I S.g.hom)
    (by
      have hzero : S.g.hom ∘ₗ S.f.hom = 0 := by
        ext x
        exact S.zero_apply x
      rw [AdicCompletion.map_comp, hzero, AdicCompletion.map_zero])

-- Proof sketch: convert the short exact owner hypothesis `hS` into injectivity, exactness, and
-- surjectivity of the underlying linear maps, then apply the owner theorems
-- `AdicCompletion.map_injective`, `AdicCompletion.map_exact`, and `AdicCompletion.map_surjective`
-- to the two structure maps of `S`.
/-- Lemma 10.97.1 (2): over a Noetherian ring, if `S` is a short exact sequence of `R`-modules and
its middle term is finite, then the completed sequence `completionShortComplex I S` is short exact
over `AdicCompletion I R`. -/
theorem completionShortComplex_shortExact (hS : S.ShortExact) :
    (completionShortComplex I S).ShortExact := by
  let f : S.X₁ →ₗ[R] S.X₂ := S.f.hom
  let g : S.X₂ →ₗ[R] S.X₃ := S.g.hom
  have hf : Function.Injective f := by
    simpa using hS.moduleCat_injective_f
  have hfg : Function.Exact f g := by
    simpa using (ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact
  have hg : Function.Surjective g := by
    simpa using hS.moduleCat_surjective_g
  refine ModuleCat.shortComplex_shortExact (completionShortComplex I S) ?_ ?_ ?_
  · simpa [completionShortComplex] using
      (show Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g) from
        AdicCompletion.map_exact hf hfg hg)
  · simpa [completionShortComplex] using
      (AdicCompletion.map_injective I hf)
  · simpa [completionShortComplex] using
      (AdicCompletion.map_surjective I hg)

/-- Companion bridge: after restricting scalars along `R → AdicCompletion I R`, the completed
short complex is still short exact as a short complex in `ModuleCat R`. -/
theorem completionShortComplex_restrictScalars_shortExact (hS : S.ShortExact) :
    (ShortComplex.moduleCatMk
      ((AdicCompletion.map I S.f.hom).restrictScalars R)
      ((AdicCompletion.map I S.g.hom).restrictScalars R)
      (by
        have hzero :
            AdicCompletion.map I S.g.hom ∘ₗ AdicCompletion.map I S.f.hom = 0 := by
          rw [AdicCompletion.map_comp]
          have hzero : S.g.hom ∘ₗ S.f.hom = 0 := by
            ext x
            exact S.zero_apply x
          rw [hzero, AdicCompletion.map_zero]
        simpa using congrArg
          (fun φ : AdicCompletion I S.X₁ →ₗ[AdicCompletion I R] AdicCompletion I S.X₃ ↦
            φ.restrictScalars R)
          hzero)).ShortExact := by
  let T : ShortComplex (ModuleCat (AdicCompletion I R)) := completionShortComplex I S
  have hT : T.ShortExact := completionShortComplex_shortExact I hS
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · simpa using (ShortExact.moduleCat_exact_iff_function_exact T).1 hT.exact
  · simpa using hT.moduleCat_injective_f
  · simpa using hT.moduleCat_surjective_g

end CategoryTheory.ShortComplex

end shortExact

section tensorProduct

variable {R : Type u} [CommRing R] (I : Ideal R) [IsNoetherianRing R]
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]

/- Lemma 10.97.1 (3): for a finite module over a Noetherian ring, its `I`-adic completion is
canonically identified with the completed ring tensored with the module. This is exactly the
canonical equivalence `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`. -/
recall AdicCompletion.ofTensorProductEquivOfFiniteNoetherian

end tensorProduct

/-! ### Lemma_10_97_2 (from Chap10) -/
universe u v

section flatness

variable {R : Type u} [CommRing R] (I : Ideal R) [IsNoetherianRing R]

-- The owner-level canonical fact is the instance
-- `AdicCompletion.flat_of_isNoetherian : Module.Flat R (AdicCompletion I R)`.
-- The textbook ring-hom statement is its standard bridge through
-- `RingHom.flat_algebraMap_iff`.
/-- Lemma 10.97.2 (1): if `R` is Noetherian, then the canonical ring map from `R` to its `I`-adic
completion is flat. -/
theorem adicCompletion_algebraMap_flat :
    (algebraMap R (AdicCompletion I R)).Flat := by
  rw [RingHom.flat_algebraMap_iff]
  infer_instance

end flatness

section exactness

variable {R : Type u} [CommRing R] {I : Ideal R} [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type v} [AddCommGroup N] [Module R N]
variable {P : Type v} [AddCommGroup P] [Module R P]
variable [Module.Finite R N]
variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}
variable (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)

/- Lemma 10.97.2 (2): for finitely generated modules over a Noetherian ring, applying `I`-adic
completion to an exact pair of linear maps remains exact. This is exactly the canonical theorem
`AdicCompletion.map_exact`. -/
recall AdicCompletion.map_exact

end exactness

/-! ### Lemma_10_97_3 (from Chap10) -/
universe u

open IsLocalRing PrimeSpectrum

section

variable {R : Type u} [CommRing R] (I : Ideal R) [IsNoetherianRing R]

-- Proof sketch: use the owner criterion `faithfullyFlat_iff_closedPoints_subset_range` together
-- with Lemma `10.97.2` for flatness. If `I ≤ Ring.jacobson R`, then every closed point of
-- `Spec R` contains `I`, so it comes from `Spec (R ⧸ I)` via the quotient-spectrum homeomorphism
-- from Lemma `10.17.7`; composing with the surjective map `AdicCompletion I R → R ⧸ I` gives a
-- lift to `Spec (AdicCompletion I R)`.
/-- Lemma 10.97.3: if `I` is contained in the Jacobson radical of a Noetherian ring `R`, then the
canonical map from `R` to its `I`-adic completion is faithfully flat. -/
theorem adicCompletion_algebraMap_faithfullyFlat_of_le_jacobson
    (hI : I ≤ Ring.jacobson R) :
    RingHom.FaithfullyFlat (algebraMap R (AdicCompletion I R)) := by
  rw [faithfullyFlat_iff_closedPoints_subset_range _ (adicCompletion_algebraMap_flat I)]
  intro x hx
  have hxmax : x.asIdeal.IsMaximal := by
    exact (isClosed_singleton_iff_isMaximal x).mp (by simpa [closedPoints] using hx)
  let _ : x.asIdeal.IsMaximal := hxmax
  have hxI : I ≤ x.asIdeal := hI.trans (Ring.jacobson_le_of_isMaximal x.asIdeal)
  let x' : PrimeSpectrum (R ⧸ I) :=
    (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus I).symm ⟨x, by simpa using hxI⟩
  refine ⟨PrimeSpectrum.comap (AdicCompletion.evalOneₐ I).toRingHom x', ?_⟩
  rw [← PrimeSpectrum.comap_comp_apply]
  change PrimeSpectrum.comap
      ((AdicCompletion.evalOneₐ I).toRingHom.comp (algebraMap R (AdicCompletion I R))) x' = x
  have hx'' : ((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus I) x').1 = x := by
    exact congrArg Subtype.val
      ((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus I).apply_symm_apply
        ⟨x, by simpa using hxI⟩)
  have hx' :
      PrimeSpectrum.comap (Ideal.Quotient.mk I) x' = x := by
    simpa using hx''
  rw [show (AdicCompletion.evalOneₐ I).toRingHom.comp (algebraMap R (AdicCompletion I R)) =
      Ideal.Quotient.mk I by
        ext r
        simp]
  exact hx'

-- Proof sketch: apply the previous theorem to `I = maximalIdeal R`. In a local ring the maximal
-- ideal is contained in the Jacobson radical, by `maximalIdeal_le_jacobson`.
/-- For a Noetherian local ring, the canonical map to its maximal-ideal adic completion is
faithfully flat. This is the completion `\varprojlim_n R / (maximalIdeal R)^n` from the textbook
statement. -/
theorem maximalIdeal_adicCompletion_algebraMap_faithfullyFlat
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    RingHom.FaithfullyFlat (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
  adicCompletion_algebraMap_faithfullyFlat_of_le_jacobson (maximalIdeal R)
    (by
      simpa [Ideal.jacobson_bot] using
        (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R)))

end

/-! ### Lemma_10_97_4 (from Chap10) -/
noncomputable section

universe u v

section

open AdicCompletion

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (I : Ideal R)
variable (M : Type v) [AddCommGroup M] [Module R M]

-- Proof sketch: apply the finitely generated ideal case from `Lemma_10_96_3` using
-- `I.fg_of_isNoetherianRing`. The first clause is `AdicCompletion.isAdicComplete`, and the second
-- follows by identifying both the image of `AdicCompletion.ofPowSMul I M n` and
-- `I ^ n • ⊤` with the kernel of `AdicCompletion.eval I M n`.
/-- Lemma 10.97.4: over a Noetherian ring, the `I`-adic completion of `M` is `I`-adically
complete, and for every `n` the canonical map from the completion of `I ^ n M` to the completion
of `M` has image exactly `I ^ n M^`. -/
theorem adicCompletion_isAdicComplete_and_completed_pow_smul_range_eq_pow_smul :
    IsAdicComplete I (AdicCompletion I M) ∧
      ∀ n : ℕ,
        (ofPowSMul I M n).range.restrictScalars R =
          I ^ n • (⊤ : Submodule R (AdicCompletion I M)) := by
  constructor
  · exact isAdicComplete I.fg_of_isNoetherianRing
  intro n
  calc
    (ofPowSMul I M n).range.restrictScalars R = (eval I M n).ker :=
      restrictScalars_range_ofPowSMul_eq_ker_eval I
    _ = I ^ n • (⊤ : Submodule R (AdicCompletion I M)) := by
      symm
      exact pow_smul_top_eq_ker_eval I.fg_of_isNoetherianRing

/-- The quotient of the completed module by `I ^ n` times the completed module is canonically
identified with the quotient `M / I ^ n M`. -/
abbrev adicCompletionQuotientPowLinearEquiv (n : ℕ) :
    ((AdicCompletion I M) ⧸ (I ^ n • (⊤ : Submodule R (AdicCompletion I M)))) ≃ₗ[R]
      M ⧸ (I ^ n • (⊤ : Submodule R M)) :=
  (Submodule.quotEquivOfEq _ _
      (pow_smul_top_eq_ker_eval I.fg_of_isNoetherianRing)).trans
    ((eval I M n).quotKerEquivOfSurjective (eval_surjective I M n))

end

/-! ### Lemma_10_97_5 (from Chap10) -/
universe u

section

variable {R : Type u} [CommRing R]
variable (I : Ideal R)

-- Domain-style sampling:
-- * primary domain: adic completions of commutative rings, with Noetherianity and adic
--   completeness for the extended ideal on the completion.
-- * layer: `source-facing`; the theorem keeps the textbook criterion while reusing the canonical
--   owner ring `AdicCompletion I R` and the owner predicate `IsAdicComplete`.
-- * sampled declarations:
--   `AdicCompletion.isAdicComplete`,
--   `IsAdicComplete.map_algebraMap_iff`,
--   `AdicCompletion.evalOneₐ`,
--   `isNoetherianRing_iff_ideal_fg`.
-- * owner abstraction: `AdicCompletion I R`; the extended ideal
--   `I.map (algebraMap R (AdicCompletion I R))` is derived from that owner, not extra primitive
--   data.
-- * primitive data: the ideal `I`, the quotient hypothesis `[IsNoetherianRing (R ⧸ I)]`, and the
--   finite-generation input `hI`.
-- * derived API: Noetherianity of the completion ring and completeness for the extended ideal.
--
-- Proof sketch: use finite generation of `I` to obtain `I`-adic completeness of
-- `AdicCompletion I R`, then transport it to the extended ideal via
-- `IsAdicComplete.map_algebraMap_iff`. For noetherianity, combine the quotient identification
-- `(AdicCompletion I R) ⧸ I.map (algebraMap R (AdicCompletion I R)) ≃+* R ⧸ I`
-- with finite generation of the extended ideal and the standard criterion that a ring is
-- noetherian when a finitely generated ideal has noetherian quotient.
/-- Helper for Lemma 10.97.5: after restricting scalars to `R`, the kernel of the algebra-valued
stage-one evaluation map agrees with the kernel of the underlying linear evaluation map. -/
lemma ker_evalOneₐ_restrictScalars_eq_ker_eval :
    (((RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom : Ideal (AdicCompletion I R)) :
        Submodule (AdicCompletion I R) (AdicCompletion I R)).restrictScalars R) =
      (AdicCompletion.eval I R 1).ker := by
  have hle₁ : I ^ 1 ≤ I ^ 1 • (⊤ : Submodule R R) := by
    simpa [pow_one, Ideal.smul_eq_mul] using le_of_eq (Ideal.mul_top I).symm
  have hle₂ : I ^ 1 • (⊤ : Submodule R R) ≤ I ^ 1 := by
    simpa [pow_one, Ideal.smul_eq_mul] using le_of_eq (Ideal.mul_top I)
  -- Compare the two kernels by transporting vanishing across the quotient identifications.
  ext x
  rw [Submodule.restrictScalars_mem, RingHom.mem_ker, LinearMap.mem_ker]
  constructor
  · intro hx
    have hfactor :
        Ideal.Quotient.factor (show I ^ 1 ≤ I by simp) ((AdicCompletion.evalₐ I 1) x) = 0 := by
      calc
        Ideal.Quotient.factor (show I ^ 1 ≤ I by simp) ((AdicCompletion.evalₐ I 1) x) =
            (AdicCompletion.evalOneₐ I) x := AdicCompletion.factorₐ_evalₐ_one (I := I) x
        _ = 0 := hx
    have hx' : (AdicCompletion.evalₐ I 1) x = 0 := by
      have hf :
          Function.Injective
            (Ideal.Quotient.factor (show I ^ 1 ≤ I by simp) : R ⧸ I ^ 1 →+* R ⧸ I) := by
        let e : (R ⧸ I ^ 1) ≃+* (R ⧸ I) := (Ideal.quotientEquivAlgOfEq R (by simp)).toRingEquiv
        simpa [e, pow_one] using e.injective
      apply hf
      simpa using hfactor
    calc
      (AdicCompletion.eval I R 1) x =
          Ideal.Quotient.factor hle₁ ((AdicCompletion.evalₐ I 1) x) := by
            symm
            exact AdicCompletion.factor_evalₐ_eq_eval (I := I) (n := 1) x hle₁
      _ = 0 := by simpa [hx']
  · intro hx
    have hx' : (AdicCompletion.evalₐ I 1) x = 0 := by
      calc
        (AdicCompletion.evalₐ I 1) x =
            Submodule.factor hle₂ ((AdicCompletion.eval I R 1) x) := by
              symm
              exact AdicCompletion.factor_eval_eq_evalₐ (I := I) (n := 1) x hle₂
        _ = 0 := by simpa [hx]
    calc
      (AdicCompletion.evalOneₐ I) x =
          Ideal.Quotient.factor (show I ^ 1 ≤ I by simp) ((AdicCompletion.evalₐ I 1) x) := by
            symm
            exact AdicCompletion.factorₐ_evalₐ_one (I := I) x
      _ = 0 := by simpa [hx']

/-- Helper for Lemma 10.97.5: the extended ideal on the completion is the kernel of the canonical
map to `R ⧸ I`. -/
lemma completion_ideal_eq_ker_evalOneA (hI : I.FG) :
    Ideal.map (algebraMap R (AdicCompletion I R)) I =
      RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom := by
  -- Reduce the ideal equality to the module-side kernel formula for adic completions.
  apply Submodule.restrictScalars_injective R (AdicCompletion I R) (AdicCompletion I R)
  calc
    (((Ideal.map (algebraMap R (AdicCompletion I R)) I : Ideal (AdicCompletion I R)) :
        Submodule (AdicCompletion I R) (AdicCompletion I R)).restrictScalars R) =
        I • (⊤ : Submodule R (AdicCompletion I R)) := by
          simpa [Ideal.smul_top_eq_map]
    _ = (AdicCompletion.eval I R 1).ker := by
      -- Finite generation identifies the first adic-step kernel with `I • ⊤`.
      simpa using (AdicCompletion.pow_smul_top_eq_ker_eval (I := I) (M := R) (n := 1) hI)
    _ =
        (((RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom : Ideal (AdicCompletion I R)) :
          Submodule (AdicCompletion I R) (AdicCompletion I R)).restrictScalars R) := by
      -- The algebra-valued and linear stage-one evaluations have the same restricted kernel.
      symm
      exact ker_evalOneₐ_restrictScalars_eq_ker_eval (I := I)

variable [IsNoetherianRing (R ⧸ I)]

/-- Helper for Lemma 10.97.5: the quotient of the completion by the extended ideal is Noetherian
because it is canonically identified with `R ⧸ I`. -/
lemma completion_quotient_isNoetherianRing (hI : I.FG) :
    IsNoetherianRing ((AdicCompletion I R) ⧸ Ideal.map (algebraMap R (AdicCompletion I R)) I) := by
  let e :
      ((AdicCompletion I R) ⧸ RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom) ≃+* (R ⧸ I) :=
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := AdicCompletion.evalOneₐ I) (AdicCompletion.evalOneₐ_surjective I)).toRingEquiv
  have hquot :
      IsNoetherianRing
        ((AdicCompletion I R) ⧸ RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom) :=
    isNoetherianRing_of_ringEquiv (R ⧸ I) e.symm
  -- Rewrite the kernel quotient using the first-stage kernel description above.
  rw [completion_ideal_eq_ker_evalOneA (I := I) hI]
  exact hquot

/-- Helper for Lemma 10.97.5: in a `K`-adically complete ring, an ideal is finitely generated as
soon as its quotient modulo `K` is a finite module over `S ⧸ K`. -/
lemma ideal_fg_of_finite_quotient_of_isAdicComplete
    {S : Type u} [CommRing S] (K : Ideal S) [IsAdicComplete K S] (J : Ideal S)
    [Module.Finite (S ⧸ K) (J ⧸ K • (⊤ : Submodule S J))] :
    J.FG := by
  -- Restrict Hausdorffness from the complete ambient ring to the ideal viewed as a submodule.
  letI : IsHausdorff K J := isHausdorff_submodule (I := K) (M := S) J
  letI : Module.Finite S J :=
    moduleFinite_of_finite_quotient_of_isHausdorff (I := K) (R := S) (M := J)
  -- Convert finiteness of the ideal as an `S`-module back to finite generation of the ideal.
  have hfgTop : (⊤ : Submodule S J).FG := Module.Finite.fg_top (R := S) (M := J)
  have hfgMap : (Submodule.map J.subtype (⊤ : Submodule S J)).FG :=
    Submodule.FG.map J.subtype hfgTop
  simpa [Submodule.map_top, Submodule.range_subtype] using hfgMap

/-- Helper for Lemma 10.97.5: once an ideal `J` is finitely generated, its quotient `J / KJ` is a
finite module over the quotient ring `S ⧸ K`. -/
lemma ideal_quotient_finite_of_fg
    {S : Type u} [CommRing S] (K J : Ideal S) (hJ : J.FG) :
    Module.Finite (S ⧸ K) (J ⧸ K • (⊤ : Submodule S J)) := by
  -- First view `J` itself as a finite `S`-module via its finite generating set.
  letI : Module.Finite S J := (Module.Finite.iff_fg (N := J)).2 hJ
  -- Quotients of finite modules are finite over the same ring.
  letI : Module.Finite S (J ⧸ K • (⊤ : Submodule S J)) := inferInstance
  -- Then descend scalars along the quotient map `S → S ⧸ K`.
  exact Module.Finite.of_restrictScalars_finite S (S ⧸ K)
    (J ⧸ K • (⊤ : Submodule S J))

/-- Helper for Lemma 10.97.5: the image of an ideal in the quotient `S ⧸ K` is finitely generated
because it is an ideal of a Noetherian ring. -/
lemma ideal_map_quotient_fg
    {S : Type u} [CommRing S] (K J : Ideal S) [IsNoetherianRing (S ⧸ K)] :
    (Ideal.map (Ideal.Quotient.mk K) J).FG := by
  -- The quotient ring is Noetherian, so every ideal inside it is finitely generated.
  exact Ideal.FG.of_isNoetherianRing (Ideal.map (Ideal.Quotient.mk K) J)

/-- Helper for Lemma 10.97.5: quotienting `J` by the intersection `J ∩ K` identifies with the
image ideal of `J` inside `S ⧸ K`. -/
noncomputable def ideal_quotient_inf_equiv_map_quotient
    {S : Type u} [CommRing S] (K J : Ideal S) :
    (J ⧸ (J ⊓ K).submoduleOf J) ≃ₗ[S]
      (((Ideal.map (Ideal.Quotient.mk K) J : Ideal (S ⧸ K)) :
        Submodule (S ⧸ K) (S ⧸ K)).restrictScalars S) := by
  let q : J →ₗ[S] (S ⧸ K) :=
    { toFun := fun x ↦ Ideal.Quotient.mk K x.1
      map_add' := fun x y ↦ rfl
      map_smul' := fun a x ↦ rfl }
  have hker : LinearMap.ker q = (J ⊓ K).submoduleOf J := by
    -- The restricted quotient map kills exactly those elements of `J` that already lie in `K`.
    ext x
    constructor
    · intro hx
      rw [LinearMap.mem_ker] at hx
      change (x : S) ∈ J ⊓ K
      exact ⟨x.2, Ideal.Quotient.eq_zero_iff_mem.mp hx⟩
    · intro hx
      change (x : S) ∈ J ⊓ K at hx
      rw [LinearMap.mem_ker]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hx.2
  have hrange :
      LinearMap.range q =
        (((Ideal.map (Ideal.Quotient.mk K) J : Ideal (S ⧸ K)) :
          Submodule (S ⧸ K) (S ⧸ K)).restrictScalars S) := by
    -- The range is precisely the ideal generated by the quotient images of elements of `J`.
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact Ideal.mem_map_of_mem (Ideal.Quotient.mk K) x.2
    · intro hy
      rcases
          (Ideal.mem_map_iff_of_surjective
            (f := Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective).1 hy with
        ⟨x, hxJ, rfl⟩
      exact ⟨⟨x, hxJ⟩, rfl⟩
  -- Apply the first isomorphism theorem and then rewrite the kernel and range into ideal language.
  exact
    (Submodule.quotEquivOfEq (LinearMap.ker q) ((J ⊓ K).submoduleOf J) hker).symm.trans
      (q.quotKerEquivRange.trans
        (LinearEquiv.ofEq _ _ hrange))

/-- Helper for Lemma 10.97.5: the naive quotient-image route makes `J / (J ∩ K)` finite over `S`,
because that quotient is the image ideal of `J` in the Noetherian ring `S ⧸ K`. -/
lemma ideal_quotient_inf_finite_of_noetherian_quotient
    {S : Type u} [CommRing S] (K J : Ideal S) [IsNoetherianRing (S ⧸ K)] :
    Module.Finite S (J ⧸ (J ⊓ K).submoduleOf J) := by
  have hfgImage : (Ideal.map (Ideal.Quotient.mk K) J).FG := ideal_map_quotient_fg K J
  have hfgImageS :
      ((((Ideal.map (Ideal.Quotient.mk K) J : Ideal (S ⧸ K)) :
          Submodule (S ⧸ K) (S ⧸ K)).restrictScalars S)).FG := by
    -- Finite generation over the quotient ring remains finite generation after restricting
    -- scalars along the surjective quotient map `S → S ⧸ K`.
    exact
      Submodule.FG.restrictScalars_of_surjective
        (R := S) (A := S ⧸ K) (M := S ⧸ K)
        (S := ((Ideal.map (Ideal.Quotient.mk K) J : Ideal (S ⧸ K)) :
          Submodule (S ⧸ K) (S ⧸ K)))
        hfgImage Ideal.Quotient.mk_surjective
  letI :
      Module.Finite S
        ((((Ideal.map (Ideal.Quotient.mk K) J : Ideal (S ⧸ K)) :
            Submodule (S ⧸ K) (S ⧸ K)).restrictScalars S)) :=
    (Module.Finite.iff_fg
      (N := (((Ideal.map (Ideal.Quotient.mk K) J : Ideal (S ⧸ K)) :
        Submodule (S ⧸ K) (S ⧸ K)).restrictScalars S))).2 hfgImageS
  -- Transport finite generation across the quotient-by-intersection equivalence.
  exact Module.Finite.equiv (ideal_quotient_inf_equiv_map_quotient K J).symm

/-- Helper for Lemma 10.97.5: pulling the quotient image of `J` back along `S → S ⧸ K` recovers
`J ⊔ K`, so the naive quotient-image route controls `J / (J ∩ K)` rather than `J / KJ`. -/
lemma comap_ideal_map_quotient_eq_sup
    {S : Type u} [CommRing S] (K J : Ideal S) :
    Ideal.comap (Ideal.Quotient.mk K) (Ideal.map (Ideal.Quotient.mk K) J) = J ⊔ K := by
  -- This is the standard pullback calculation for the quotient map by `K`.
  simpa [sup_comm] using (Ideal.comap_map_quotientMk K J)

/-- Helper for Lemma 10.97.5: an element of the `n`-th `K`-adic stage gives a degree-`n`
monomial in the quotient-Rees presentation of the associated graded ring. -/
private theorem ideal_associated_graded_stage_monomial_mem
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage K S n) :
    Polynomial.monomial n (x : S) ∈ reesAlgebra K := by
  -- The stage condition is exactly the coefficient condition for a Rees monomial.
  apply reesAlgebra.monomial_mem.mpr
  simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
    using x.2

/-- Helper for Lemma 10.97.5: the degree-`n` class of a stage element in the quotient-Rees model
of `gr_K(S)`. -/
private noncomputable def idealAssociatedGradedStageClass
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ) :
    RingTheory.Sequence.idealAssociatedGradedStage K S n → idealAssociatedGradedRing K :=
  fun x ↦
    Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K)
      ⟨Polynomial.monomial n (x : S), ideal_associated_graded_stage_monomial_mem K n x⟩

/-- Helper for Lemma 10.97.5: use the canonical quotient-ring structure on the quotient-Rees
model of the associated graded ring, avoiding slower instance search through local wrappers. -/
noncomputable local instance idealAssociatedGradedRing_commRing
    {S : Type u} [CommRing S] (K : Ideal S) :
    CommRing (idealAssociatedGradedRing K) :=
  Ideal.Quotient.commRing (Ideal.map (algebraMap S (reesAlgebra K)) K)

/-- Helper for Lemma 10.97.5: use the canonical quotient algebra structure over `S ⧸ K` on the
quotient-Rees model of the associated graded ring. -/
noncomputable local instance idealAssociatedGradedRing_algebraQuotient
    {S : Type u} [CommRing S] (K : Ideal S) :
    Algebra (S ⧸ K) (idealAssociatedGradedRing K) :=
  Ideal.Quotient.algebraQuotientMapQuotient

/-- Helper for Lemma 10.97.5: an element of `K` gives the textbook degree-one class in
`gr_K(S)`. -/
private noncomputable def idealAssociatedGradedDegreeOne
    {S : Type u} [CommRing S] (K : Ideal S) (x : K) :
    idealAssociatedGradedRing K :=
  idealAssociatedGradedStageClass K 1
    ⟨x, by
      -- Repackage `x ∈ K` as membership in the first stage `K^1`.
      simpa [RingTheory.Sequence.idealAssociatedGradedStage, pow_one, Ideal.smul_eq_mul,
        Ideal.mul_top] using x.2⟩

/-- Helper for Lemma 10.97.5: the degree-`n` monomial representative of a stage element belongs
to the degree-`n` part of the Rees algebra. -/
private theorem ideal_associated_graded_stage_mem_grade
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage K S n) :
    (⟨Polynomial.monomial n (x : S), ideal_associated_graded_stage_monomial_mem K n x⟩ :
      reesAlgebra K) ∈ reesAlgebraGrade K n := by
  -- The chosen monomial already has the canonical degree-`n` shape defining `reesAlgebraGrade`.
  refine ⟨⟨(x : S), ?_⟩, rfl⟩
  simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
    using x.2

/-- Helper for Lemma 10.97.5: the stage class map lands in the degree-`n` owner piece of the
associated graded ring. -/
private theorem idealAssociatedGradedStageClass_mem_grade
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage K S n) :
    idealAssociatedGradedStageClass K n x ∈ idealAssociatedGradedRingGrade K n := by
  -- The owner-grade witness is exactly the degree-`n` monomial representative used to define the
  -- stage class.
  refine ⟨⟨Polynomial.monomial n (x : S), ideal_associated_graded_stage_monomial_mem K n x⟩,
    ideal_associated_graded_stage_mem_grade K n x, rfl⟩

/-- Helper for Lemma 10.97.5: the monomial stage construction is linear before passing to the
associated graded quotient. -/
private noncomputable def idealAssociatedGradedStageToReesLinear
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ) :
    RingTheory.Sequence.idealAssociatedGradedStage K S n →ₗ[S] reesAlgebra K :=
  LinearMap.codRestrict ((reesAlgebra K).toSubmodule)
    ((Polynomial.monomial n).comp (show
      RingTheory.Sequence.idealAssociatedGradedStage K S n →ₗ[S] S from
        (RingTheory.Sequence.idealAssociatedGradedStage K S n).subtype))
    (fun x ↦ ideal_associated_graded_stage_monomial_mem K n x)

/-- Helper for Lemma 10.97.5: the linear stage map to the owner ring lands in the degree-`n`
owner subtype. -/
private noncomputable def idealAssociatedGradedStageClassLinear
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ) :
    RingTheory.Sequence.idealAssociatedGradedStage K S n →ₗ[S] idealAssociatedGradedRingGrade K n :=
  LinearMap.codRestrict (idealAssociatedGradedRingGrade K n)
    (((Ideal.Quotient.mkₐ S (Ideal.map (algebraMap S (reesAlgebra K)) K)).toLinearMap).comp
      (idealAssociatedGradedStageToReesLinear K n))
    (fun x ↦ by
      simpa [idealAssociatedGradedStageToReesLinear, idealAssociatedGradedStageClass,
        LinearMap.comp_apply] using idealAssociatedGradedStageClass_mem_grade K n x)

/-- Helper for Lemma 10.97.5: the linear stage-to-grade map agrees with the stage-class map after
forgetting the grade subtype. -/
private theorem idealAssociatedGradedStageClassLinear_apply
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage K S n) :
    ((idealAssociatedGradedStageClassLinear K n x :
      idealAssociatedGradedRingGrade K n) : idealAssociatedGradedRing K) =
      idealAssociatedGradedStageClass K n x := by
  -- Compare both definitions on the common Rees representative before passing to the quotient.
  change
    Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K)
        ((idealAssociatedGradedStageToReesLinear K n) x) =
      Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K)
        ⟨Polynomial.monomial n (x : S), ideal_associated_graded_stage_monomial_mem K n x⟩
  congr 1

/-- Helper for Lemma 10.97.5: every element of the degree-`n` owner piece is represented by a
stage element in `K ^ n`. -/
private theorem idealAssociatedGradedStageClassLinear_surjective
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ) :
    Function.Surjective (idealAssociatedGradedStageClassLinear K n) := by
  intro x
  rcases x.2 with ⟨y, hy, hxy⟩
  rcases hy with ⟨a, rfl⟩
  refine ⟨⟨a.1, ?_⟩, ?_⟩
  · -- A homogeneous Rees generator in degree `n` is exactly an element of `K ^ n`.
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
      using a.2
  · -- The representative is already the canonical monomial image of that stage element.
    exact Subtype.ext <| by
      simpa [idealAssociatedGradedStageClassLinear, idealAssociatedGradedStageToReesLinear] using hxy

/-- Helper for Lemma 10.97.5: a finitely generated ideal can be reindexed by a finite `Fin`
family of generators. -/
private theorem exists_fin_generating_family_of_ideal
    {S : Type u} [CommRing S] (K : Ideal S) (hK : K.FG) :
    ∃ t : ℕ, ∃ g : Fin t → K, Ideal.span (Set.range fun i ↦ ((g i : K) : S)) = K := by
  classical
  let s : Finset S := (Submodule.FG.finite_generators hK).toFinset
  have hs_generators : (s : Set S) = K.generators := by
    exact (Submodule.FG.finite_generators hK).coe_toFinset
  have hmem_generators : K.generators ⊆ K := Submodule.FG.generators_mem (p := K)
  let g : Fin s.card → K := fun i ↦
    ⟨((Finset.equivFin s).symm i : S), by
      have hi : (((Finset.equivFin s).symm i : s) : S) ∈ (s : Set S) := ((Finset.equivFin s).symm i).2
      rw [hs_generators] at hi
      exact hmem_generators hi⟩
  have hrange : Set.range (fun i ↦ ((g i : K) : S)) = (s : Set S) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ((Finset.equivFin s).symm i).2
    · intro hx
      refine ⟨(Finset.equivFin s) ⟨x, hx⟩, ?_⟩
      simpa [g] using congrArg Subtype.val ((Finset.equivFin s).symm_apply_apply ⟨x, hx⟩)
  refine ⟨s.card, g, ?_⟩
  calc
    Ideal.span (Set.range fun i ↦ ((g i : K) : S)) = Ideal.span (s : Set S) := by rw [hrange]
    _ = K := by simpa [hs_generators] using K.span_generators

/-- Helper for Lemma 10.97.5: once generators `g` of `K` are fixed, the source proof identifies
`K ^ n` with the span of the degree-`n` monomial weights in those generators. -/
private lemma ideal_pow_eq_span_monomial_weight_of_generators
    {S : Type u} [CommRing S] (K : Ideal S) {t : ℕ} (g : Fin t → K)
    (hgspan : Ideal.span (Set.range fun i ↦ ((g i : K) : S)) = K) (n : ℕ) :
    K ^ n =
      Ideal.span ((fun e : Fin t →₀ ℕ =>
        ∏ i : Fin t, ((g i : K) : S) ^ e i) '' {e | e.degree = n}) := by
  -- Rewrite the power of `K` through the chosen generators before invoking the standard
  -- `Finsupp`-product description of powers of a span.
  calc
    K ^ n = (Ideal.span (Set.range fun i ↦ ((g i : K) : S))) ^ n := by rw [hgspan]
    _ = Ideal.span ((fun e : Fin t →₀ ℕ => ∏ i : Fin t, ((g i : K) : S) ^ e i) '' {e | e.degree = n}) := by
      rw [Ideal.span, Submodule.span_pow, ← Set.image_univ,
        Finsupp.image_pow_eq_finsuppProd_image]
      simp

/-- Helper for Lemma 10.97.5: every monomial weight in the chosen generators lies in the matching
power of `K`. -/
private lemma monomial_weight_mem_ideal_pow_of_generators
    {S : Type u} [CommRing S] (K : Ideal S) {t : ℕ} (g : Fin t → K)
    (hgspan : Ideal.span (Set.range fun i ↦ ((g i : K) : S)) = K)
    (e : Fin t →₀ ℕ) :
    (∏ i : Fin t, ((g i : K) : S) ^ e i) ∈ K ^ e.degree := by
  -- Place the chosen monomial in the span description of `K ^ e.degree`.
  rw [ideal_pow_eq_span_monomial_weight_of_generators K g hgspan e.degree]
  exact Ideal.subset_span ⟨e, by simp⟩

/-- Helper for Lemma 10.97.5: after choosing generators of `K`, the source polynomial algebra
maps to `gr_K(S)` by sending `X i` to the degree-one class of the `i`-th generator. -/
private noncomputable def associated_graded_presentation
    {S : Type u} [CommRing S] (K : Ideal S) {t : ℕ} (g : Fin t → K) :
    MvPolynomial (Fin t) (S ⧸ K) →ₐ[S ⧸ K] idealAssociatedGradedRing K :=
  MvPolynomial.aeval fun i ↦ idealAssociatedGradedDegreeOne K (g i)

/-- Helper for Lemma 10.97.5: the presentation map sends each polynomial variable to the chosen
degree-one generator class in the associated graded ring. -/
private lemma associated_graded_presentation_X
    {S : Type u} [CommRing S] (K : Ideal S) {t : ℕ} (g : Fin t → K) (i : Fin t) :
    associated_graded_presentation K g (MvPolynomial.X i) =
      idealAssociatedGradedDegreeOne K (g i) := by
  -- The evaluation map is defined precisely to realize the source presentation on variables.
  simp [associated_graded_presentation]

/-- Helper for Lemma 10.97.5: once the source polynomial presentation
`(S ⧸ K)[T_1, ..., T_t] ↠ gr_K(S)` is constructed, Noetherianity of the associated graded ring
follows formally by surjectivity. -/
private lemma associated_graded_isNoetherian_of_surjective_mvPolynomial
    {S : Type u} [CommRing S] (K : Ideal S) [IsNoetherianRing (S ⧸ K)]
    {t : ℕ}
    (φ : MvPolynomial (Fin t) (S ⧸ K) →ₐ[S ⧸ K] idealAssociatedGradedRing K)
    (hφ : Function.Surjective φ) :
    IsNoetherianRing (idealAssociatedGradedRing K) := by
  -- The source polynomial algebra is Noetherian over the Noetherian coefficient ring `S ⧸ K`.
  letI : IsNoetherianRing (MvPolynomial (Fin t) (S ⧸ K)) := inferInstance
  -- Surjective maps preserve Noetherianity, so the remaining work is exactly the source
  -- presentation by degree-one generators of `K`.
  exact isNoetherianRing_of_surjective _ _ φ.toRingHom hφ

/-- Helper for Lemma 10.97.5: taking the `n`-th coefficient sends the denominator ideal of the
quotient-Rees presentation into `K^(n + 1)`. -/
private theorem rees_algebra_coeff_mem_pow_succ_of_mem_denominator
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ)
    {y : reesAlgebra K}
    (hy : y ∈ Ideal.map (algebraMap S (reesAlgebra K)) K) :
    y.1.coeff n ∈ K ^ (n + 1) := by
  have hy' : y ∈ K • (⊤ : Submodule S (reesAlgebra K)) := by
    -- Rewrite the denominator ideal as the stage-one scalar multiple.
    simpa [Ideal.smul_top_eq_map] using hy
  -- Check the coefficient condition first on generators, then extend by additivity.
  refine Submodule.smul_induction_on hy' ?_ ?_
  · intro r hr z hz
    have hzcoeff : z.1.coeff n ∈ K ^ n := z.2 n
    change (r • z.1).coeff n ∈ K ^ (n + 1)
    simpa [Polynomial.coeff_smul, smul_eq_mul, pow_succ', Ideal.mul_comm] using
      Ideal.mul_mem_mul hr hzcoeff
  · intro x y hx hy
    simpa [Polynomial.coeff_add] using Ideal.add_mem (K ^ (n + 1)) hx hy

/-- Helper for Lemma 10.97.5: if a degree-`n` coefficient already lies in `K^(n + 1)`, then the
corresponding monomial is in the denominator ideal of the quotient-Rees presentation. -/
private theorem monomial_mem_denominator_of_mem_pow_succ
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ) {a : S}
    (ha : a ∈ K ^ (n + 1)) :
    (⟨Polynomial.monomial n a,
        reesAlgebra.monomial_mem.mpr
          ((Ideal.pow_le_pow_right (Nat.le_succ n)) ha)⟩ :
      reesAlgebra K) ∈ Ideal.map (algebraMap S (reesAlgebra K)) K := by
  have hsmul :
      (⟨Polynomial.monomial n a,
          reesAlgebra.monomial_mem.mpr
            ((Ideal.pow_le_pow_right (Nat.le_succ n)) ha)⟩ :
        reesAlgebra K) ∈ K • (⊤ : Submodule S (reesAlgebra K)) := by
    let x : reesAlgebra K :=
      ⟨Polynomial.monomial n a,
        reesAlgebra.monomial_mem.mpr
          ((Ideal.pow_le_pow_right (Nat.le_succ n)) ha)⟩
    let φ : S →ₗ[S] Polynomial S := Polynomial.monomial n
    have ha' : a ∈ K • (K ^ n : Submodule S S) := by
      -- This is the source identity `K * K^n = K^(n+1)`.
      simpa [Ideal.smul_eq_mul, pow_succ, Ideal.mul_comm] using ha
    let RK : Submodule S (Polynomial S) := Subalgebra.toSubmodule (reesAlgebra K)
    have hmap0 :
        (Submodule.map φ (K ^ n : Submodule S S) : Submodule S (Polynomial S)) ≤ RK := by
      intro p hp
      rcases hp with ⟨b, hb, rfl⟩
      exact reesAlgebra.monomial_mem.mpr hb
    have hmap :
        (Submodule.map φ (K • (K ^ n : Submodule S S)) : Submodule S (Polynomial S)) ≤
          (K • RK : Submodule S (Polynomial S)) := by
      rw [Submodule.map_smul'']
      refine Submodule.smul_le.mpr ?_
      intro r hr p hp
      exact Submodule.smul_mem_smul hr (hmap0 hp)
    have hambient : (x : Polynomial S) ∈ K • RK := by
      have hxmap : φ a ∈ Submodule.map φ (K • (K ^ n : Submodule S S)) := by
        exact Submodule.mem_map_of_mem ha'
      exact hmap <| by simpa [φ, x] using hxmap
    exact (Submodule.mem_smul_top_iff (I := K) (N := RK) (x := x)).2 hambient
  simpa [Ideal.smul_top_eq_map] using hsmul

/-- Helper for Lemma 10.97.5: the degree-`n` class of a stage element is zero exactly when the
coefficient lies one step deeper in the `K`-adic filtration. -/
private theorem associated_graded_stage_class_zero_iff
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage K S n) :
    idealAssociatedGradedStageClass K n x = 0 ↔
      (x : S) ∈ RingTheory.Sequence.idealAssociatedGradedStage K S (n + 1) := by
  constructor
  · intro hx
    change
      Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K)
          ⟨Polynomial.monomial n (x : S), ideal_associated_graded_stage_monomial_mem K n x⟩ = 0
      at hx
    rw [Ideal.Quotient.eq_zero_iff_mem] at hx
    -- A vanishing class means the monomial representative falls in the denominator ideal.
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
      using rees_algebra_coeff_mem_pow_succ_of_mem_denominator K n hx
  · intro hx
    change
      Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K)
          ⟨Polynomial.monomial n (x : S), ideal_associated_graded_stage_monomial_mem K n x⟩ = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have hx' : (x : S) ∈ K ^ (n + 1) := by
      -- Re-express the next stage as the pure power ideal `K^(n+1)`.
      simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
        using hx
    simpa using monomial_mem_denominator_of_mem_pow_succ K n hx'

/-- Helper for Lemma 10.97.5: the kernel of the stage-to-grade map is the next filtration step. -/
private theorem idealAssociatedGradedStageClassLinear_ker_eq
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ) :
    LinearMap.ker (idealAssociatedGradedStageClassLinear K n) =
      (RingTheory.Sequence.idealAssociatedGradedStage K S (n + 1)).submoduleOf
        (RingTheory.Sequence.idealAssociatedGradedStage K S n) := by
  ext x
  constructor
  · intro hx
    have hx' :
        (((idealAssociatedGradedStageClassLinear K n x : idealAssociatedGradedRingGrade K n) :
            idealAssociatedGradedRing K)) = 0 := by
      exact congrArg (fun z : idealAssociatedGradedRingGrade K n ↦ (z : idealAssociatedGradedRing K)) hx
    -- Forgetting the grade subtype reduces kernel membership to vanishing of the stage class.
    change idealAssociatedGradedStageClass K n x = 0 at hx'
    exact (associated_graded_stage_class_zero_iff K n x).1 hx'
  · intro hx
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    -- The previously proved zero criterion identifies the next stage with the kernel.
    change idealAssociatedGradedStageClass K n x = 0
    exact (associated_graded_stage_class_zero_iff K n x).2 hx

/-- Helper for Lemma 10.97.5: the degree-`n` owner piece is canonically equivalent to the
textbook quotient `K^n / K^(n + 1)`. -/
private noncomputable def idealAssociatedGradedRingGrade_equiv_piece
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ) :
    idealAssociatedGradedRingGrade K n ≃ₗ[S] RingTheory.Sequence.idealAssociatedGradedPiece K S n :=
  ((idealAssociatedGradedStageClassLinear K n).quotKerEquivOfSurjective
      (idealAssociatedGradedStageClassLinear_surjective K n)).symm.trans
    (Submodule.quotEquivOfEq _ _
      (idealAssociatedGradedStageClassLinear_ker_eq K n))

/-- Helper for Lemma 10.97.5: reducing a stage representative modulo `K^(n + 1)` lands in the
image of `K ^ n` in the quotient ring `S / K^(n + 1)`. -/
private theorem idealAssociatedGradedStageToPowQuotient_mem
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage K S n) :
    Ideal.Quotient.mk (K ^ (n + 1)) (x : S) ∈
      Ideal.map (Ideal.Quotient.mk (K ^ (n + 1))) (K ^ n) := by
  -- Forgetting the stage subtype recovers a literal element of `K ^ n`.
  exact Ideal.mem_map_of_mem _ <|
    by
      simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
        using x.2

/-- Helper for Lemma 10.97.5: the `n`-th stage maps linearly into the image of `K ^ n`
inside `S / K^(n + 1)`. -/
private noncomputable def idealAssociatedGradedStageToPowQuotientLinear
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ) :
    RingTheory.Sequence.idealAssociatedGradedStage K S n →ₗ[S]
      Ideal.map (Ideal.Quotient.mk (K ^ (n + 1))) (K ^ n) :=
  { toFun := fun x ↦ ⟨Ideal.Quotient.mk (K ^ (n + 1)) (x : S),
      idealAssociatedGradedStageToPowQuotient_mem K n x⟩
    map_add' := fun x y ↦ by
      apply Subtype.ext
      rfl
    map_smul' := fun r x ↦ by
      apply Subtype.ext
      rfl }

/-- Helper for Lemma 10.97.5: the codomain-restricted stage-to-quotient map evaluates to the
obvious quotient class modulo `K^(n + 1)`. -/
private theorem idealAssociatedGradedStageToPowQuotientLinear_apply
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage K S n) :
    ((idealAssociatedGradedStageToPowQuotientLinear K n x :
      Ideal.map (Ideal.Quotient.mk (K ^ (n + 1))) (K ^ n)) : S ⧸ K ^ (n + 1)) =
      Ideal.Quotient.mk (K ^ (n + 1)) (x : S) := by
  -- The codomain restriction keeps the same quotient representative.
  rfl

/-- Helper for Lemma 10.97.5: every class in the image of `K ^ n` inside `S / K^(n + 1)` is
represented by an element of the `n`-th stage. -/
private theorem idealAssociatedGradedStageToPowQuotientLinear_surjective
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ) :
    Function.Surjective (idealAssociatedGradedStageToPowQuotientLinear K n) := by
  intro y
  rcases y with ⟨y, hy⟩
  rcases
      (Ideal.mem_map_iff_of_surjective
        (Ideal.Quotient.mk (K ^ (n + 1))) Ideal.Quotient.mk_surjective).mp hy with
    ⟨a, ha, rfl⟩
  refine ⟨⟨a, ?_⟩, ?_⟩
  · -- The witness in `K ^ n` is exactly an element of the `n`-th filtration stage.
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
      using ha
  · -- The codomain representative is built from the same quotient class.
    apply Subtype.ext
    rfl

/-- Helper for Lemma 10.97.5: the kernel of the stage-to-quotient map is the next filtration
stage. -/
private theorem idealAssociatedGradedStageToPowQuotientLinear_ker_eq
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ) :
    LinearMap.ker (idealAssociatedGradedStageToPowQuotientLinear K n) =
      (RingTheory.Sequence.idealAssociatedGradedStage K S (n + 1)).submoduleOf
        (RingTheory.Sequence.idealAssociatedGradedStage K S n) := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker] at hx
    have hx' : Ideal.Quotient.mk (K ^ (n + 1)) (x : S) = 0 := by
      exact congrArg Subtype.val hx
    rw [Ideal.Quotient.eq_zero_iff_mem] at hx'
    -- Vanishing in the quotient means the representative lies one step deeper in the filtration.
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top] using hx'
  · intro hx
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    -- Membership in the next stage is exactly the quotient-zero criterion.
    exact Ideal.Quotient.eq_zero_iff_mem.mpr <|
      by
        simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
          using hx

/-- Helper for Lemma 10.97.5: the quotient `K^n / K^(n + 1)` identifies with the image of `K ^ n`
inside `S / K^(n + 1)`. -/
private noncomputable def idealAssociatedGradedPiece_equiv_map_pow
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ) :
    RingTheory.Sequence.idealAssociatedGradedPiece K S n ≃ₗ[S]
      Ideal.map (Ideal.Quotient.mk (K ^ (n + 1))) (K ^ n) :=
  (Submodule.quotEquivOfEq _ _
      (idealAssociatedGradedStageToPowQuotientLinear_ker_eq K n).symm).trans
    ((idealAssociatedGradedStageToPowQuotientLinear K n).quotKerEquivOfSurjective
      (idealAssociatedGradedStageToPowQuotientLinear_surjective K n))

/-- Helper for Lemma 10.97.5: the piece-to-quotient identification sends the stage class of `x`
to the quotient class of `x` modulo `K^(n + 1)`. -/
private theorem idealAssociatedGradedPiece_equiv_map_pow_apply_stage
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage K S n) :
    idealAssociatedGradedPiece_equiv_map_pow K n
      (Submodule.Quotient.mk x) =
        idealAssociatedGradedStageToPowQuotientLinear K n x := by
  -- Both quotient equivalences act trivially on the stage representative `x`.
  simp [idealAssociatedGradedPiece_equiv_map_pow]

/-- Helper for Lemma 10.97.5: the owner degree-`n` piece is canonically equivalent to the image
of `K ^ n` inside `S / K^(n + 1)`. -/
private noncomputable def idealAssociatedGradedRingGrade_equiv_map_pow
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ) :
    idealAssociatedGradedRingGrade K n ≃
      Ideal.map (Ideal.Quotient.mk (K ^ (n + 1))) (K ^ n) :=
  (idealAssociatedGradedRingGrade_equiv_piece K n).toEquiv.trans
    (idealAssociatedGradedPiece_equiv_map_pow K n).toEquiv

/-- Helper for Lemma 10.97.5: on a stage representative, the owner-grade equivalence agrees with
the obvious quotient class modulo `K^(n + 1)`. -/
private theorem idealAssociatedGradedRingGrade_equiv_map_pow_apply_stage
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage K S n) :
    idealAssociatedGradedRingGrade_equiv_map_pow K n
      (idealAssociatedGradedStageClassLinear K n x) =
        idealAssociatedGradedStageToPowQuotientLinear K n x := by
  -- First identify the owner grade with `K^n / K^(n + 1)`, then with the quotient image.
  simpa [idealAssociatedGradedRingGrade_equiv_map_pow, idealAssociatedGradedRingGrade_equiv_piece]
    using idealAssociatedGradedPiece_equiv_map_pow_apply_stage (S := S) K n x

/-- Helper for Lemma 10.97.5: the `n`-th coefficient of a Rees element lies in the `n`-th
associated-graded stage. -/
private theorem coeff_mem_idealAssociatedGradedStage
    {S : Type u} [CommRing S] (K : Ideal S) (y : reesAlgebra K) (n : ℕ) :
    y.1.coeff n ∈ RingTheory.Sequence.idealAssociatedGradedStage K S n := by
  -- The defining coefficient condition for the Rees algebra is exactly stage membership.
  simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
    using y.2 n

/-- Helper for Lemma 10.97.5: the unit of `S` belongs to the degree-zero stage of the
`K`-adic filtration. -/
private theorem one_mem_idealAssociatedGradedStage_zero
    {S : Type u} [CommRing S] (K : Ideal S) :
    (1 : S) ∈ RingTheory.Sequence.idealAssociatedGradedStage K S 0 := by
  -- Degree zero is the whole ring, so the unit is available as the multiplicative base case.
  simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top] using
    (show (1 : S) ∈ (⊤ : Ideal S) by simp)

/-- Helper for Lemma 10.97.5: a chosen generator of `K` raised to the `n`-th power belongs to the
`n`-th stage of the `K`-adic filtration. -/
private theorem generator_pow_mem_idealAssociatedGradedStage
    {S : Type u} [CommRing S] (K : Ideal S) {t : ℕ} (g : Fin t → K) (i : Fin t) (n : ℕ) :
    (((g i : K) : S) ^ n) ∈ RingTheory.Sequence.idealAssociatedGradedStage K S n := by
  -- A generator of `K` contributes one copy of `K` at each multiplication step.
  have hpow : (((g i : K) : S) ^ n) ∈ K ^ n := Ideal.pow_mem_pow (g i).2 n
  simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top] using
    hpow

/-- Helper for Lemma 10.97.5: multiplying representatives from stages `m` and `n` lands in the
stage `m + n`. -/
private theorem ideal_associated_graded_stage_mul_mem
    {S : Type u} [CommRing S] (K : Ideal S) {m n : ℕ}
    (x : RingTheory.Sequence.idealAssociatedGradedStage K S m)
    (y : RingTheory.Sequence.idealAssociatedGradedStage K S n) :
    ((x : S) * (y : S)) ∈ RingTheory.Sequence.idealAssociatedGradedStage K S (m + n) := by
  -- The filtration is multiplicative because `K ^ m * K ^ n = K ^ (m + n)`.
  have hx : (x : S) ∈ K ^ m := by
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
      using x.2
  have hy : (y : S) ∈ K ^ n := by
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
      using y.2
  have hxy : (x : S) * (y : S) ∈ K ^ m * K ^ n := Ideal.mul_mem_mul hx hy
  simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top,
    pow_add] using hxy

/-- Helper for Lemma 10.97.5: the product in the associated graded ring is induced by
multiplication of stage representatives. -/
private theorem idealAssociatedGradedStageClass_mul
    {S : Type u} [CommRing S] (K : Ideal S) {m n : ℕ}
    (x : RingTheory.Sequence.idealAssociatedGradedStage K S m)
    (y : RingTheory.Sequence.idealAssociatedGradedStage K S n) :
    idealAssociatedGradedStageClass K (m + n)
        ⟨(x : S) * (y : S), ideal_associated_graded_stage_mul_mem K x y⟩ =
      idealAssociatedGradedStageClass K m x * idealAssociatedGradedStageClass K n y := by
  -- Compare both sides on the canonical quotient-Rees monomial representatives.
  change
    Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K)
        (⟨Polynomial.monomial (m + n) ((x : S) * (y : S)), _⟩ : reesAlgebra K) =
      Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K)
        ((⟨Polynomial.monomial m (x : S), _⟩ : reesAlgebra K) *
          (⟨Polynomial.monomial n (y : S), _⟩ : reesAlgebra K))
  congr 1
  apply Subtype.ext
  simp [Polynomial.monomial_mul_monomial, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Lemma 10.97.5: the degree-`n` class of a single generator power is the `n`-th
power of the corresponding degree-one class. -/
private theorem associated_graded_stage_class_generator_pow_eq
    {S : Type u} [CommRing S] (K : Ideal S) {t : ℕ} (g : Fin t → K) (i : Fin t) (n : ℕ) :
    idealAssociatedGradedStageClass K n
        ⟨((g i : K) : S) ^ n, generator_pow_mem_idealAssociatedGradedStage K g i n⟩ =
      idealAssociatedGradedDegreeOne K (g i) ^ n := by
  letI : Monoid (idealAssociatedGradedRing K) := inferInstance
  induction n with
  | zero =>
      -- Compare the degree-zero representative with the unit of the quotient-Rees ring.
      change
        (Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K)
          (⟨Polynomial.monomial 0 (((g i : K) : S) ^ 0),
              ideal_associated_graded_stage_monomial_mem K 0
                ⟨((g i : K) : S) ^ 0, generator_pow_mem_idealAssociatedGradedStage K g i 0⟩⟩ :
            reesAlgebra K) : idealAssociatedGradedRing K) =
          Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K) (1 : reesAlgebra K)
      congr 1
      apply Subtype.ext
      simp
  | succ n ih =>
      -- Multiply the degree-`n` class by the degree-one class of the same generator.
      let xn : RingTheory.Sequence.idealAssociatedGradedStage K S n :=
        ⟨((g i : K) : S) ^ n, generator_pow_mem_idealAssociatedGradedStage K g i n⟩
      let x1 : RingTheory.Sequence.idealAssociatedGradedStage K S 1 :=
        ⟨((g i : K) : S) ^ 1, generator_pow_mem_idealAssociatedGradedStage K g i 1⟩
      have hmul :
          idealAssociatedGradedStageClass K (n + 1)
              ⟨((g i : K) : S) ^ (n + 1), generator_pow_mem_idealAssociatedGradedStage K g i (n + 1)⟩ =
            idealAssociatedGradedStageClass K n xn * idealAssociatedGradedDegreeOne K (g i) := by
        -- The source multiplication rule on stages matches multiplication in the quotient.
        simpa [xn, x1, idealAssociatedGradedDegreeOne, pow_succ, pow_one] using
          idealAssociatedGradedStageClass_mul (S := S) K xn x1
      calc
        idealAssociatedGradedStageClass K (n + 1)
            ⟨((g i : K) : S) ^ (n + 1), generator_pow_mem_idealAssociatedGradedStage K g i (n + 1)⟩ =
          idealAssociatedGradedStageClass K n xn * idealAssociatedGradedDegreeOne K (g i) := hmul
        _ = idealAssociatedGradedDegreeOne K (g i) ^ n * idealAssociatedGradedDegreeOne K (g i) := by
            rw [ih]
        _ = idealAssociatedGradedDegreeOne K (g i) ^ (n + 1) := by
            rw [pow_succ]

/-- Helper for Lemma 10.97.5: the monomial weight attached to `e` lies in the stage of degree
`e.degree`. -/
private theorem monomial_weight_mem_idealAssociatedGradedStage_of_generators
    {S : Type u} [CommRing S] (K : Ideal S) {t : ℕ} (g : Fin t → K)
    (hgspan : Ideal.span (Set.range fun i ↦ ((g i : K) : S)) = K) (e : Fin t →₀ ℕ) :
    (∏ i : Fin t, ((g i : K) : S) ^ e i) ∈ RingTheory.Sequence.idealAssociatedGradedStage K S
      e.degree := by
  -- The monomial-weight description of `K ^ e.degree` gives the required stage membership.
  simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top] using
    monomial_weight_mem_ideal_pow_of_generators K g hgspan e

/-- Helper for Lemma 10.97.5: a finite product of ordinary monomials in one variable collapses to
one monomial whose degree and coefficient are the corresponding finite sums and products. -/
private theorem polynomial_finset_prod_monomial_eq_monomial_sum
    {S : Type u} [CommRing S] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (d : ι → ℕ) (a : ι → S) :
    (∏ i ∈ s, Polynomial.monomial (d i) (a i)) =
      Polynomial.monomial (s.sum d) (s.prod a) := by
  induction s using Finset.induction_on with
  | empty =>
      -- The empty product is the degree-zero monomial with coefficient `1`.
      simp
  | @insert i s hi hs =>
      -- One more factor combines with the inductive monomial by `monomial_mul_monomial`.
      simp [hi, hs, Polynomial.monomial_mul_monomial, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Lemma 10.97.5: the degree-`e.degree` class of the monomial weight attached to `e`
is the product of the degree-one classes of the chosen generators. -/
private theorem associated_graded_stage_class_monomial_weight_eq
    {S : Type u} [CommRing S] (K : Ideal S) {t : ℕ} (g : Fin t → K)
    (hgspan : Ideal.span (Set.range fun i ↦ ((g i : K) : S)) = K) (e : Fin t →₀ ℕ) :
    idealAssociatedGradedStageClass K e.degree
        ⟨∏ i : Fin t, ((g i : K) : S) ^ e i,
          monomial_weight_mem_idealAssociatedGradedStage_of_generators K g hgspan e⟩ =
      ∏ i : Fin t, idealAssociatedGradedDegreeOne K (g i) ^ e i := by
  -- TODO: expand the monomial weight as a product of generator powers inside the quotient-Rees
  -- presentation, then rewrite each factor with
  -- `associated_graded_stage_class_generator_pow_eq`.
  sorry

/-- Helper for Lemma 10.97.5: any `S`-linear combination of degree-`n` generator monomials
belongs to the degree-`n` stage. -/
private theorem span_monomial_weight_mem_idealAssociatedGradedStage_of_generators
    {S : Type u} [CommRing S] (K : Ideal S) {t : ℕ} (g : Fin t → K)
    (hgspan : Ideal.span (Set.range fun i ↦ ((g i : K) : S)) = K) (n : ℕ) {x : S}
    (hx : x ∈ Ideal.span ((fun e : Fin t →₀ ℕ =>
      ∏ i : Fin t, ((g i : K) : S) ^ e i) '' {e | e.degree = n})) :
    x ∈ RingTheory.Sequence.idealAssociatedGradedStage K S n := by
  -- Reinterpret the span description of `K ^ n` back as stage membership.
  have hxK : x ∈ K ^ n := by
    rw [ideal_pow_eq_span_monomial_weight_of_generators K g hgspan n]
    exact hx
  simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top] using
    hxK

/-- Helper for Lemma 10.97.5: every stage class lies in the subalgebra generated by the degree-one
classes of a fixed finite generating family of `K`. -/
private theorem associated_graded_stage_class_mem_adjoin_degree_one
    {S : Type u} [CommRing S] (K : Ideal S) {t : ℕ} (g : Fin t → K)
    (hgspan : Ideal.span (Set.range fun i ↦ ((g i : K) : S)) = K)
    (n : ℕ) (x : RingTheory.Sequence.idealAssociatedGradedStage K S n) :
    idealAssociatedGradedStageClass K n x ∈
      Algebra.adjoin (S ⧸ K) (Set.range fun i : Fin t ↦ idealAssociatedGradedDegreeOne K (g i)) := by
  -- TODO: rewrite `(x : S)` by the monomial-span description of `K ^ n`, then use a span
  -- induction whose generators are handled by
  -- `associated_graded_stage_class_monomial_weight_eq`.
  sorry

/-- Helper for Lemma 10.97.5: every quotient-Rees class is the sum of the stage classes of its
support coefficients. -/
private theorem idealAssociatedGradedClass_eq_sum_stage_classes
    {S : Type u} [CommRing S] (K : Ideal S) (y : reesAlgebra K) :
    (Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K) y :
      idealAssociatedGradedRing K) =
        ∑ n ∈ y.1.support,
          idealAssociatedGradedStageClass K n
            ⟨y.1.coeff n, coeff_mem_idealAssociatedGradedStage K y n⟩ := by
  -- TODO: apply the quotient map to `Polynomial.sum_monomial_eq y.1` termwise, using the imported
  -- quotient-ring structure instead of the duplicate local instance path that previously caused
  -- elaboration drift here.
  sorry

/-- Helper for Lemma 10.97.5: the degree-one classes of a finite generating family of `K`
generate the whole associated graded ring over `S ⧸ K`. -/
private theorem associated_graded_degree_one_adjoin_eq_top
    {S : Type u} [CommRing S] (K : Ideal S) {t : ℕ} (g : Fin t → K)
    (hgspan : Ideal.span (Set.range fun i ↦ ((g i : K) : S)) = K) :
    Algebra.adjoin (S ⧸ K) (Set.range fun i : Fin t ↦ idealAssociatedGradedDegreeOne K (g i)) = ⊤ := by
  -- TODO: combine `idealAssociatedGradedClass_eq_sum_stage_classes` with
  -- `associated_graded_stage_class_mem_adjoin_degree_one` and then perform quotient induction.
  sorry

/-- Helper for Lemma 10.97.5: if the degree-one classes adjoin to all of `gr_K(S)`, then the
source polynomial presentation is surjective. -/
private theorem associated_graded_presentation_surjective
    {S : Type u} [CommRing S] (K : Ideal S) {t : ℕ} (g : Fin t → K)
    (hadjoin :
      Algebra.adjoin (S ⧸ K) (Set.range fun i : Fin t ↦ idealAssociatedGradedDegreeOne K (g i)) = ⊤) :
    Function.Surjective (associated_graded_presentation K g) := by
  -- Convert the adjoin statement into the exact range statement for `MvPolynomial.aeval`.
  have hrange :
      (associated_graded_presentation K g).range =
        Algebra.adjoin (S ⧸ K) (Set.range fun i : Fin t ↦ idealAssociatedGradedDegreeOne K (g i)) := by
    simpa [associated_graded_presentation] using
      (Algebra.adjoin_range_eq_range_aeval (R := S ⧸ K)
        (f := fun i : Fin t ↦ idealAssociatedGradedDegreeOne K (g i))).symm
  -- The range is all of `gr_K(S)`, so the presentation is surjective.
  exact (AlgHom.range_eq_top (associated_graded_presentation K g)).1 <| by
    rw [hrange]
    simpa using hadjoin

/-- Helper for Lemma 10.97.5: once the associated graded ring is generated by finitely many
degree-one classes over `S ⧸ K`, it is Noetherian. -/
private theorem associated_graded_isNoetherian_of_degree_one_adjoin_eq_top
    {S : Type u} [CommRing S] (K : Ideal S) [IsNoetherianRing (S ⧸ K)] {t : ℕ} (g : Fin t → K)
    (hadjoin :
      Algebra.adjoin (S ⧸ K) (Set.range fun i : Fin t ↦ idealAssociatedGradedDegreeOne K (g i)) = ⊤) :
    IsNoetherianRing (idealAssociatedGradedRing K) := by
  -- Use the source-faithful polynomial presentation rather than rebuilding a separate finite-type
  -- instance layer.
  exact associated_graded_isNoetherian_of_surjective_mvPolynomial K
    (associated_graded_presentation K g)
    (associated_graded_presentation_surjective K g hadjoin)

/-- Helper for Lemma 10.97.5: in a complete ring with finitely generated ideal and Noetherian
quotient, every ideal should be finitely generated. -/
private lemma ideal_fg_of_complete_fg_ideal_noetherian_quotient
    {S : Type u} [CommRing S] (K : Ideal S) [IsAdicComplete K S]
    (hKfg : K.FG) (hquot : IsNoetherianRing (S ⧸ K)) (J : Ideal S) :
    J.FG := by
  -- Route correction: the source proof must run through the associated graded kernel
  -- `⊕ (J ∩ K^n)/(J ∩ K^(n + 1))`, not through the false shortcut `J / KJ`.
  have himagefg : (Ideal.map (Ideal.Quotient.mk K) J).FG :=
    ideal_map_quotient_fg K J
  have hquotInfFinite : Module.Finite S (J ⧸ (J ⊓ K).submoduleOf J) :=
    ideal_quotient_inf_finite_of_noetherian_quotient K J
  have hpullback :
      Ideal.comap (Ideal.Quotient.mk K) (Ideal.map (Ideal.Quotient.mk K) J) = J ⊔ K :=
    comap_ideal_map_quotient_eq_sup K J
  have hzero_bridge :
      ∀ n (x : RingTheory.Sequence.idealAssociatedGradedStage K S n),
        idealAssociatedGradedStageClass K n x = 0 ↔
          (x : S) ∈ RingTheory.Sequence.idealAssociatedGradedStage K S (n + 1) := by
    intro n x
    exact associated_graded_stage_class_zero_iff K n x
  have hgr_noeth_of_presentation :
      ∀ {t : ℕ} (φ : MvPolynomial (Fin t) (S ⧸ K) →ₐ[S ⧸ K] idealAssociatedGradedRing K),
        Function.Surjective φ → IsNoetherianRing (idealAssociatedGradedRing K) := by
    intro t φ hφ
    -- This isolates the remaining source-faithful task to constructing the polynomial presentation
    -- from a finite set of generators of `K`.
    exact associated_graded_isNoetherian_of_surjective_mvPolynomial K φ hφ
  obtain ⟨t, g, hgspan⟩ := exists_fin_generating_family_of_ideal K hKfg
  let φ : MvPolynomial (Fin t) (S ⧸ K) →ₐ[S ⧸ K] idealAssociatedGradedRing K :=
    associated_graded_presentation K g
  have hgr_noeth_of_degree_one_adjoin :
      Algebra.adjoin (S ⧸ K) (Set.range fun i : Fin t ↦ idealAssociatedGradedDegreeOne K (g i)) = ⊤ →
        IsNoetherianRing (idealAssociatedGradedRing K) := by
    intro hadjoin
    -- The adjoin-to-finite-type bridge isolates the remaining work to proving the source
    -- degree-one generation statement for `gr_K(S)`.
    exact associated_graded_isNoetherian_of_degree_one_adjoin_eq_top K g hadjoin
  have hφX :
      ∀ i : Fin t, φ (MvPolynomial.X i) = idealAssociatedGradedDegreeOne K (g i) := by
    intro i
    simpa [φ] using associated_graded_presentation_X K g i
  have hdegreeOne_range :
      ∀ i : Fin t, idealAssociatedGradedDegreeOne K (g i) ∈ Set.range φ := by
    intro i
    refine ⟨MvPolynomial.X i, ?_⟩
    simpa using hφX i
  have hpow_span :
      ∀ n,
        K ^ n =
          Ideal.span ((fun e : Fin t →₀ ℕ =>
            ∏ i : Fin t, ((g i : K) : S) ^ e i) '' {e | e.degree = n}) := by
    intro n
    -- This is the source monomial expansion of `K ^ n` attached to the fixed generators `g`.
    exact ideal_pow_eq_span_monomial_weight_of_generators K g hgspan n
  have hmonomial_mem_pow :
      ∀ e : Fin t →₀ ℕ, (∏ i : Fin t, ((g i : K) : S) ^ e i) ∈ K ^ e.degree := by
    intro e
    -- Each source monomial weight really is a degree-`e.degree` element of the `K`-adic
    -- filtration.
    exact monomial_weight_mem_ideal_pow_of_generators K g hgspan e
  have hdegreeOneAdjoin :
      Algebra.adjoin (S ⧸ K) (Set.range fun i : Fin t ↦ idealAssociatedGradedDegreeOne K (g i)) =
        ⊤ := by
    -- The fixed degree-one classes generate every homogeneous stage class, hence the whole
    -- associated graded ring.
    exact associated_graded_degree_one_adjoin_eq_top K g hgspan
  have hgrNoeth : IsNoetherianRing (idealAssociatedGradedRing K) :=
    hgr_noeth_of_degree_one_adjoin hdegreeOneAdjoin
  -- These closed facts now match the source setup more closely. The naive quotient-image route
  -- only controls `J / (J ∩ K)`, while `hzero_bridge` supplies the owner/piece zero criterion
  -- needed for the real source route on `⊕ (J ∩ K^n)/(J ∩ K^(n + 1))`. The new bridge
  -- `hgr_noeth_of_presentation` and the new adjoin bridge
  -- `hgr_noeth_of_degree_one_adjoin` now isolate the graded Noetherian step to two equivalent
  -- source-faithful frontiers: either prove the literal surjective presentation
  -- `(S ⧸ K)[T_1, ..., T_t] ↠ gr_K(S)`, or prove directly that the degree-one classes of the
  -- chosen generators adjoin to all of `gr_K(S)`. The closed monomial-span data `hpow_span` and
  -- `hmonomial_mem_pow`, together with `hdegreeOne_range`, are exactly the verified prefix needed
  -- for that generation step.
  -- TODO: complete that degree-one generation argument, then feed the resulting
  -- `IsNoetherianRing (idealAssociatedGradedRing K)` into the source kernel/correction tail.
  -- After that, use `hzero_bridge` to extract finitely many kernel generators of the
  -- quotient-induced associated graded map from classes represented by elements of `J ∩ K^d`,
  -- and finally run the one-step correction plus completeness limit argument.
  sorry

omit [IsNoetherianRing (R ⧸ I)] in
/-- Helper for Lemma 10.97.5: the completion is complete for the adic topology of the extended
ideal. -/
lemma completion_ideal_isAdicComplete (hI : I.FG) :
    IsAdicComplete (I.map (algebraMap R (AdicCompletion I R))) (AdicCompletion I R) := by
  -- Transport the owner completeness theorem across the standard map-ideal equivalence.
  have hmap :
      IsAdicComplete (I.map (algebraMap R (AdicCompletion I R))) (AdicCompletion I R) ↔
        IsAdicComplete I (AdicCompletion I R) :=
    IsAdicComplete.map_algebraMap_iff I (AdicCompletion I R)
  exact hmap.2 (AdicCompletion.isAdicComplete hI)

/-- Lemma 10.97.5: if `R ⧸ I` is Noetherian and `I` is finitely generated, then the `I`-adic
completion `AdicCompletion I R` is a Noetherian ring and is complete for the adic topology defined
by the extended ideal `I.map (algebraMap R (AdicCompletion I R))`. -/
lemma adicCompletion_isNoetherian_and_isAdicComplete
    (hI : I.FG) :
    IsNoetherianRing (AdicCompletion I R) ∧
      IsAdicComplete (I.map (algebraMap R (AdicCompletion I R))) (AdicCompletion I R) := by
  constructor
  ·
    -- Route correction: the tempting quotient-image route `J / KJ ≃ J.map (Ideal.Quotient.mk K)`
    -- is false in general because the kernel of `J → S ⧸ K` is `J ⊓ K`, not `KJ`.
    refine (isNoetherianRing_iff_ideal_fg (AdicCompletion I R)).2 ?_
    intro J
    let K : Ideal (AdicCompletion I R) := I.map (algebraMap R (AdicCompletion I R))
    have hcompleteK : IsAdicComplete K (AdicCompletion I R) := by
      simpa [K] using completion_ideal_isAdicComplete (I := I) hI
    letI : IsAdicComplete K (AdicCompletion I R) := hcompleteK
    have hquot :
        IsNoetherianRing ((AdicCompletion I R) ⧸ K) := by
      simpa [K] using completion_quotient_isNoetherianRing (I := I) hI
    have hKfg : K.FG := by
      simpa [K] using Ideal.FG.map hI (algebraMap R (AdicCompletion I R))
    -- The theorem-specific work is now reduced to the complete-ring frontier above.
    exact @ideal_fg_of_complete_fg_ideal_noetherian_quotient
      (AdicCompletion I R) _ K hcompleteK hKfg hquot J
  ·
    exact completion_ideal_isAdicComplete (I := I) hI

end

/-! ### Lemma_10_97_6 (from Chap10) -/
universe u

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (I : Ideal R)

-- Domain-style sampling:
-- * primary domain: adic completions of commutative Noetherian rings.
-- * layer: `bridge/view`; this item is the textbook specialization of the owner theorem from
--   `Lemma_10_97_5`.
-- * sampled declarations:
--   `adicCompletion_isNoetherian_and_isAdicComplete`,
--   `I.fg_of_isNoetherianRing`,
--   the quotient instance `[IsNoetherianRing (R ⧸ I)]`.
-- * owner abstraction: the completion ring `AdicCompletion I R`; completeness for the extended
--   ideal is derived API and is discarded here because the source item asks only for
--   Noetherianity.
-- * primitive data: the ring `R`, the ideal `I`, and the ambient Noetherian hypothesis on `R`.
--
-- Proof sketch: since `R` is Noetherian, the ideal `I` is finitely generated and the quotient
-- `R ⧸ I` is Noetherian. Apply the standard noetherianity criterion for `AdicCompletion I R`
-- from the previous lemma to conclude that the completion is Noetherian.
/-- Lemma 10.97.6: if `R` is a Noetherian ring, then its `I`-adic completion
`AdicCompletion I R` is Noetherian. -/
lemma adicCompletion_isNoetherianRing :
    IsNoetherianRing (AdicCompletion I R) :=
  (adicCompletion_isNoetherian_and_isAdicComplete I I.fg_of_isNoetherianRing).1

end
