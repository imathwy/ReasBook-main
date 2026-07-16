import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import stacks_proof.stacks_project.Chap15.Lemma_15_89_3
import stacks_proof.stacks_project.Chap15.Lemma_15_89_4
import stacks_proof.stacks_project.Chap15.Lemma_15_89_9
import stacks_proof.stacks_project.Chap15.Lemma_15_90_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open ModuleCat
open scoped IdealPowerTorsion
open scoped TensorProduct

noncomputable section

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Domain-style sampling:
- primary domain: base change for ideal-power torsion in module categories, with the source-facing
  torsion submodules written as `M[I^∞]` and
  `(S ⊗[R] M)[(I.map (algebraMap R S))^∞]`, carried by the owner `Ideal.primaryComponent`
  and the ambient owner functor `ModuleCat.extendScalars`;
- inspected same-domain owners:
  `Ideal.primaryComponent`,
  `Ideal.primaryComponent.map`,
  `Module.IsIdealPowerTorsion`,
  `ModuleCat.extendScalars`,
  `TensorProduct.mk`,
  `idealPowerTorsionRestrictedBaseChange`;
- best owner abstraction: the canonical tensor base-change unit together with the source-facing
  primary-component submodules and the induced restricted base-change map on them, viewed as the
  elementwise shadow of the canonical torsion base-change functor obtained by
  `idealPowerTorsionRestrictedBaseChange`;
- primitive data: the ideal `I`, the module `M`, and the canonical tensor base-change unit;
- derived API: the induced restricted linear map on primary components and its bijectivity under
  the flatness and quotient hypotheses.

Source/core/bridge triage:
- `source-facing`: the comparison of the `I^∞`-torsion submodule of `M` with the `(IS)^∞`-torsion
  submodule after base change;
- `core/canonical`: `ModuleCat.extendScalars (algebraMap R S)` and the canonical linear map
  `TensorProduct.mk R S M 1`;
- `bridge/view`: `idealPowerTorsionRestrictedBaseChange (algebraMap R S) I` and the restricted
  map on `Ideal.primaryComponent` cut out by `tensorBaseChangeUnitPrimaryComponent`.
-/

/- The canonical unit map `M → S ⊗[R] M` is `TensorProduct.mk R S M 1`; this is the
mathlib-facing model of the textbook map `M → M \otimes_R S`. -/
-- Proof sketch: if `x` is killed by a power `I^n`, then every pure tensor `1 ⊗ x` is killed by
-- the corresponding power of `IS`; by additivity, the same holds for the image of any element of
-- the `I`-primary component.
private theorem tensorBaseChangeUnitPrimaryComponent_mem
    (I : Ideal R) (M : Type w) [AddCommGroup M] [Module R M]
    (x : M[I^∞]) :
    TensorProduct.mk R S M 1 x ∈
      ((S ⊗[R] M)[(I.map (algebraMap R S))^∞] : Submodule S (S ⊗[R] M)) :=
  by
    -- Proof comment: unpack the source `I^∞`-torsion witness for `x`, then repeat the tensor-side
    -- span-induction argument from the general base-change torsion lemma on the pure tensor
    -- `1 ⊗ x`.
    rw [Ideal.primaryComponent_mem]
    obtain ⟨n, hx⟩ := (Ideal.primaryComponent_mem M I (x : M)).1 x.2
    refine ⟨n, ?_⟩
    rw [Submodule.mem_torsionBySet_iff] at hx ⊢
    intro b
    have hb : (b : S) ∈ Ideal.span (algebraMap R S '' (↑(I ^ n) : Set R)) := by
      have hb' : (b : S) ∈ Ideal.map (algebraMap R S) (I ^ n) := by
        simpa [Ideal.map_pow] using b.2
      simpa [Ideal.map_span] using hb'
    refine Submodule.span_induction
      (p := fun z _ ↦ z • (TensorProduct.mk R S M 1 x : S ⊗[R] M) = 0)
      ?_ ?_ ?_ ?_ hb
    · intro y hy
      rcases hy with ⟨a, ha, rfl⟩
      calc
        (algebraMap R S a : S) • (TensorProduct.mk R S M 1 x : S ⊗[R] M) =
            ((a • (1 : S)) ⊗ₜ[R] (x : M)) := by
              rfl
        _ = (1 : S) ⊗ₜ[R] (a • (x : M)) := by
              rw [TensorProduct.smul_tmul]
        _ = 0 := by
              simp [hx ⟨a, ha⟩]
    · simp
    · intro y z hy hz hy' hz'
      rw [add_smul, hy', hz']
      simp
    · intro c y hy hy'
      simpa [smul_smul] using congrArg (fun t : S ⊗[R] M ↦ c • t) hy'

/-- The canonical tensor base-change map restricted to the `I^∞`-torsion submodule `M[I^∞]`. -/
def tensorBaseChangeUnitPrimaryComponent
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R)
    (M : Type w) [AddCommGroup M] [Module R M] :
    (M[I^∞] : Submodule R M) →ₗ[R]
      (((S ⊗[R] M)[(I.map (algebraMap R S))^∞] :
          Submodule S (S ⊗[R] M)).restrictScalars R) :=
  ((TensorProduct.mk R S M 1).domRestrict (M[I^∞] : Submodule R M)).codRestrict
    ((((S ⊗[R] M)[(I.map (algebraMap R S))^∞] :
        Submodule S (S ⊗[R] M)).restrictScalars R))
    (tensorBaseChangeUnitPrimaryComponent_mem I M)

variable (I : Ideal R) (hflat : (algebraMap R S).Flat) (hI : I.FG)
variable (hquot :
  Function.Bijective
    (Ideal.quotientMap
      (I.map (algebraMap R S))
      (algebraMap R S)
      Ideal.le_comap_map))

/-- Helper for Lemma 15.90.3: the flat quotient hypothesis upgrades to faithfulness of the
restricted base-change functor on `I`-power torsion modules. -/
private theorem idealPowerTorsionRestrictedBaseChange_faithful :
    (idealPowerTorsionRestrictedBaseChange (algebraMap R S) I).Faithful := by
  -- Proof comment: extract clause `(4)` from the TFAE of Lemma `15.90.1` using the quotient-map
  -- bijectivity witness as the faithfully flat quotient condition.
  let hTFAE :=
    flat_quotientFaithfullyFlat_tfae_baseChangeFaithfulOnIdealTorsionModules
      (algebraMap R S) I
  have h₀ :
      (algebraMap R S).Flat ∧
        (quotientMapModIdeal (algebraMap R S) I).FaithfullyFlat := by
    exact ⟨hflat, RingHom.FaithfullyFlat.of_bijective hquot⟩
  exact (hTFAE.out 0 3).mp h₀ |>.2

/-- Helper for Lemma 15.90.3: `(IS)^∞`-power torsion remains `I^∞`-power torsion after
restricting scalars along `R → S`. -/
theorem restrictScalars_isIdealPowerTorsion_of_mapped_idealPowerTorsion
    {N : ModuleCat S}
    (hN : Module.IsIdealPowerTorsion (I.map (algebraMap R S)) N) :
    Module.IsIdealPowerTorsion I ((ModuleCat.restrictScalars (algebraMap R S)).obj N) := by
  -- Proof comment: the same positive exponent works after restriction because every coefficient
  -- from `I^n` maps into `(IS)^n`.
  rw [Module.isIdealPowerTorsion_iff] at hN ⊢
  intro x
  obtain ⟨n, hn⟩ := hN x
  refine ⟨n, fun a ↦ ?_⟩
  let aS : ↥((I.map (algebraMap R S)) ^ (n : ℕ)) :=
    ⟨algebraMap R S a, by
      have ha' : algebraMap R S (a : R) ∈ Ideal.map (algebraMap R S) (I ^ (n : ℕ)) := by
        exact Ideal.mem_map_of_mem (algebraMap R S) a.2
      simpa [Ideal.map_pow] using ha'⟩
  simpa [aS] using hn aS

/-- Helper for Lemma 15.90.3: maps out of an `I`-power torsion module factor uniquely through the
`I^∞`-torsion submodule of the target. -/
theorem hom_to_primaryComponent_bijective_of_idealPowerTorsion_left
    {M N : ModuleCat R}
    (hM : Module.IsIdealPowerTorsion I M) :
    Function.Bijective
      (fun f : M ⟶ ModuleCat.of R (N[I^∞]) ↦
        f ≫ ModuleCat.ofHom (Submodule.subtype (N[I^∞] : Submodule R N))) := by
  constructor
  · intro f g hfg
    -- Proof comment: the subtype inclusion is pointwise injective, so equality after inclusion
    -- already forces equality of the lifted maps.
    ext x
    apply Subtype.ext
    exact congrArg (fun k : M ⟶ N ↦ k x) hfg
  · intro g
    rw [Module.isIdealPowerTorsion_iff] at hM
    -- Proof comment: cod-restrict `g` by showing every value lands in the primary component of
    -- the target using the torsion witness on the source element.
    refine ⟨ModuleCat.ofHom <|
      LinearMap.codRestrict (N[I^∞] : Submodule R N) g.hom (fun x ↦ ?_), ?_⟩
    · rw [Ideal.primaryComponent_mem]
      obtain ⟨n, hn⟩ := hM x
      refine ⟨(n : ℕ), ?_⟩
      rw [Submodule.mem_torsionBySet_iff]
      intro a
      have hx : (a : R) • x = 0 := hn a
      simpa using congrArg g.hom hx
    · ext x
      rfl

-- Proof sketch: apply the formal glueing hypotheses of Lemmas `15.90.1` and `15.90.2` to reduce
-- to modules with no residual `I`-torsion after quotienting by `I^∞`-torsion. Flatness preserves
-- the injectivity criterion from Lemma `15.89.4`, which shows that no new `(IS)^∞`-torsion
-- appears after tensoring the quotient, so the induced map on primary components is bijective.
/-- Lemma 15.90.3 (1): if `R → S` is flat, `I` is finitely generated, and `R ⧸ I → S ⧸ IS` is
bijective, then for every `R`-module `M` the canonical map `M → S ⊗[R] M` induces a bijection
from `M[I^∞]` onto `((S ⊗[R] M)[(I.map (algebraMap R S))^∞] : Submodule S (S ⊗[R] M))`. -/
@[stacks 05EC]
theorem tensorBaseChangeUnitPrimaryComponent_bijective
    (M : Type w) [AddCommGroup M] [Module R M] :
    Function.Bijective (tensorBaseChangeUnitPrimaryComponent S I M) := by
  -- TODO: follow the quotient-by-`M[I^∞]` route from the source proof, using
  -- `powerTorsion_quotient_primaryComponent_eq_bot`, `ideal_power_torsion_bot_tfae_of_span_eq`,
  -- and flatness to show that base change creates no new torsion in the quotient.
  sorry

-- Proof sketch: if `N` is `I`-power torsion, combine Lemma `15.90.2` with the tensor-Hom
-- adjunction to identify the displayed map with the canonical Hom bijection over `R ⧸ I`. If `M`
-- is `I`-power torsion, any morphism out of `M` factors through the `I^∞`-torsion submodule of
-- the target, and part `(1)` transports that reduction through base change.
/-- Lemma 15.90.3 (2): under the same hypotheses, extension of scalars induces a bijection
`Hom_R(M, N) → Hom_S(S ⊗[R] M, S ⊗[R] N)` whenever either `M` or `N` is `I`-power torsion. -/
@[stacks 05EC]
theorem extendScalars_hom_bijective_of_idealPowerTorsion_left_or_right
    {M N : ModuleCat R}
    (hMN :
      Module.IsIdealPowerTorsion I M ∨
        Module.IsIdealPowerTorsion I N) :
    Function.Bijective
      (fun f : M ⟶ N ↦ (extendScalars (algebraMap R S)).map f) := by
  -- TODO: the right-torsion case should be reduced to the tensor-unit isomorphism for torsion
  -- codomains, and the left-torsion case then factors through the target primary component using
  -- `hom_to_primaryComponent_bijective_of_idealPowerTorsion_left` and part `(1)`.
  sorry

-- Proof sketch: part `(2)` gives full faithfulness of the restricted extension-of-scalars
-- functor on the torsion full subcategories. For essential surjectivity, an `IS`-power torsion
-- `S`-module is unchanged by extension of scalars along `R → S`, so every object of the target
-- lies in the essential image.
/-- Lemma 15.90.3 (3): under the same hypotheses, extension of scalars defines an equivalence
between the full subcategory of `I`-power torsion `R`-modules and the full subcategory of
`IS`-power torsion `S`-modules. -/
@[stacks 05EC]
theorem idealPowerTorsionRestrictedBaseChange_isEquivalence
    :
    Functor.IsEquivalence
      (idealPowerTorsionRestrictedBaseChange (algebraMap R S) I) := by
  -- TODO: combine part `(2)` for full faithfulness with the source-proof essential-surjectivity
  -- argument, using `restrictScalars_isIdealPowerTorsion_of_mapped_idealPowerTorsion` and part
  -- `(1)` specialized to the restricted-scalar source object.
  sorry

end
