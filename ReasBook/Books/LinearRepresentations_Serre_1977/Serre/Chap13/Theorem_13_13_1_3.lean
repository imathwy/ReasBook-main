import Mathlib
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.RealizableOver
import LinearRepresentations_Serre_1977.Serre.Chap12.Corollary_12_12_4_2
import LinearRepresentations_Serre_1977.Serre.Chap12.Lemma_12_12_1_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open Representation
open scoped Representation

section

variable {G : Type u} [Group G] [Finite G]
variable {K : Type v} [Field K] [CharZero K]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ K]

local instance instFintypeG : Fintype G := Fintype.ofFinite G
local instance instNeZeroExponent : NeZero (Monoid.exponent G) :=
  Monoid.neZero_exponent_of_finite

/- Source/core/bridge triage:
- `source-facing`: Serre's rational-character criterion over a cyclotomic realization of `ℚ(m)`,
  together with its rational-valued specialization.
- `core/canonical`: the Chapter `12` owner
  `Representation.classFunction_mem_characterRingOverFieldScalarExtension_map_iff_galoisCompatible`,
  its invariant-form corollary
  `Representation.classFunction_mem_characterRingOverFieldScalarExtension_iff_
    gammaSubgroup_invariant`, and the canonical cyclotomic `(ZMod m)ˣ`-action on values.
- `bridge/view`: the reusable source notation `Γ_ℚ(G) = (ZMod (exp G))ˣ`.

This file keeps the source-facing specializations because they are less restrictive than the
Chapter `12` number-field statement, but it reuses the upstream owner action instead of rebuilding
it locally. -/

-- Sampled domain declarations:
-- * `Representation.classFunction_mem_characterRingOverFieldScalarExtension_map_
--     iff_galoisCompatible`
-- * `Representation.classFunction_mem_characterRingOverFieldScalarExtension_iff_
--     gammaSubgroup_invariant`
-- * `Representation.gammaSubgroup`, with the notations `Γ[K](G)` and `Γ_ℚ(G)`
-- * `gammaRat_conjugate_iff_conjugate_zpowers`
--
-- Primitive data:
-- * a `K`-valued or `ℚ`-valued class function on `G`
-- * the canonical `Γ_ℚ(G)` power action on `G` and cyclotomic action on values
--
-- Derived API:
-- * membership in `ℚ ⊗ R_ℚ(G)` and its cyclotomic realization inside `G → K`
-- * the `Γ_ℚ`-power-invariance criterion obtained by specializing the Chapter `12` owner to the
--   bottom field.

-- Proof sketch: combine the cyclotomic Galois description from Theorem `13-13.1-1` with the
-- general Galois-power criterion for rationalized character rings from Chapter `12`, specialized
-- to the exponent `m = Monoid.exponent G`; over a cyclotomic realization of `ℚ(m)`, this is
-- exactly Serre's condition `σ_t(f) = Ψ^t(f)`.
/-- Helper for Theorem 13-13.1-3: extending rational characters from `ℚ` to the bottom field of
`K` keeps them inside Serre's character ring. -/
private theorem bot_symm_mem_characterRingOverField_of_mem
    {χ : G → ℚ} (hχ : χ ∈ R[ℚ](G)) :
    (fun s ↦ (IntermediateField.botEquiv ℚ K).symm (χ s)) ∈
      R[↥(⊥ : IntermediateField ℚ K)](G) := by
  -- Transport each irreducible generator by scalar extension, then close under the adjoin rules.
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hχ
  · intro ψ hψ
    rcases hψ with ⟨ρ, _, _, rfl⟩
    let ρL : Rep.{max u v} ↥(⊥ : IntermediateField ℚ K) G :=
      Rep.of (Representation.scalarExtension (k := ↥(⊥ : IntermediateField ℚ K)) ρ.ρ)
    have hρL : ρL.ρ.character ∈ R[↥(⊥ : IntermediateField ℚ K)](G) := by
      exact Representation.rep_character_mem_characterRingOverField
        (K := ↥(⊥ : IntermediateField ℚ K)) (G := G) ρL
    have hchar :
        ρL.ρ.character =
          fun s ↦ (IntermediateField.botEquiv ℚ K).symm (ρ.ρ.character s) := by
      -- Scalar extension along `ℚ → ↥⊥` applies that coefficient map pointwise to characters.
      ext s
      have hs : ρL.ρ.character s = (IntermediateField.botEquiv ℚ K).symm (ρ.ρ.character s) := by
        change (LinearMap.trace ↥(⊥ : IntermediateField ℚ K)
            (TensorProduct ℚ ↥(⊥ : IntermediateField ℚ K) ↑ρ))
          ((Representation.scalarExtension (k := ↥(⊥ : IntermediateField ℚ K)) ρ.ρ) s) =
            algebraMap ℚ ↥(⊥ : IntermediateField ℚ K) ((LinearMap.trace ℚ ↑ρ) (ρ.ρ s))
        exact LinearMap.trace_baseChange (ρ.ρ s) ↥(⊥ : IntermediateField ℚ K)
      exact congrArg (fun x : ↥(⊥ : IntermediateField ℚ K) => (x : K)) hs
    simpa [ρL, hchar] using hρL
  · intro n
    -- Integer-valued constant functions are preserved by the bottom-field embedding.
    have hconst :
        (fun s : G ↦ (IntermediateField.botEquiv ℚ K).symm ((algebraMap ℤ (G → ℚ)) n s)) =
          algebraMap ℤ (G → ↥(⊥ : IntermediateField ℚ K)) n := by
      ext s
      simp [Pi.algebraMap_apply]
    rw [hconst]
    exact (R[↥(⊥ : IntermediateField ℚ K)](G)).algebraMap_mem n
  · intro f g _ _ hf hg
    -- The character ring is closed under addition.
    simpa [Pi.add_apply] using (R[↥(⊥ : IntermediateField ℚ K)](G)).add_mem hf hg
  · intro f g _ _ hf hg
    -- The character ring is closed under multiplication.
    simpa [Pi.mul_apply] using (R[↥(⊥ : IntermediateField ℚ K)](G)).mul_mem hf hg

/-- Helper for Theorem 13-13.1-3: transporting a bottom-valued character through `botEquiv`
lands in the literal rational character ring `R[ℚ](G)`. -/
private theorem bot_equiv_mem_characterRingOverField_of_mem
    {χ : G → ↥(⊥ : IntermediateField ℚ K)}
    (hχ : χ ∈ R[↥(⊥ : IntermediateField ℚ K)](G)) :
    (fun s ↦ IntermediateField.botEquiv ℚ K (χ s)) ∈ R[ℚ](G) := by
  let χQ : G → ℚ := fun s ↦ IntermediateField.botEquiv ℚ K (χ s)
  have hχQ_over :
      χQ ∈ overlineCharacterRingInExtension
        (K := ℚ) (L := ↥(⊥ : IntermediateField ℚ K)) (G := G) := by
    -- The coefficientwise image of `χQ` in the bottom field is exactly the original `χ`.
    rw [mem_overlineCharacterRingInExtension_iff
      (K := ℚ) (L := ↥(⊥ : IntermediateField ℚ K)) (G := G) χQ]
    have himage :
        ((IsScalarTower.toAlgHom ℤ ℚ ↥(⊥ : IntermediateField ℚ K)).compLeft G) χQ = χ := by
      ext s
      have hs : algebraMap ℚ K (χQ s) = (χ s : K) := by
        change algebraMap ℚ K (IntermediateField.botEquiv ℚ K (χ s)) =
          algebraMap ↥(⊥ : IntermediateField ℚ K) K (χ s)
        rw [IsScalarTower.algebraMap_apply ℚ ↥(⊥ : IntermediateField ℚ K) K
          (IntermediateField.botEquiv ℚ K (χ s))]
        rw [show algebraMap ℚ ↥(⊥ : IntermediateField ℚ K)
          (IntermediateField.botEquiv ℚ K (χ s)) = χ s by
          exact (IntermediateField.botEquiv ℚ K).symm_apply_apply (χ s)]
      simpa [χQ] using hs
    convert hχ using 1
  have hsmul : ((Module.finrank ℚ ↥(⊥ : IntermediateField ℚ K) : ℤ) • χQ) ∈ R[ℚ](G) :=
    Representation.extensionDegree_smul_mem_characterRingOverField
      (K := ℚ) (L := ↥(⊥ : IntermediateField ℚ K)) (G := G) ⟨χQ, hχQ_over⟩
  have hfinrank : Module.finrank ℚ ↥(⊥ : IntermediateField ℚ K) = 1 := by
    -- The bottom intermediate field is canonically isomorphic to `ℚ`.
    simpa using (IntermediateField.botEquiv ℚ K).toLinearEquiv.finrank_eq
  simpa [χQ, hfinrank] using hsmul

/-- Helper for Theorem 13-13.1-3: scalar extension from the bottom field to `K` agrees with
scalar extension from `ℚ` after transporting coefficients through `botEquiv`. -/
private theorem bot_equiv_classFunctionScalarExtension
    (g : G → ↥(⊥ : IntermediateField ℚ K)) :
    classFunctionScalarExtension G ↥(⊥ : IntermediateField ℚ K) K g =
      classFunctionScalarExtension G ℚ K
        (fun s ↦ IntermediateField.botEquiv ℚ K (g s)) := by
  -- Both scalar extensions evaluate to the same `K`-valued function pointwise.
  ext s
  change algebraMap ↥(⊥ : IntermediateField ℚ K) K (g s) =
    algebraMap ℚ K (IntermediateField.botEquiv ℚ K (g s))
  calc
    algebraMap ↥(⊥ : IntermediateField ℚ K) K (g s) =
        algebraMap ↥(⊥ : IntermediateField ℚ K) K
          ((IntermediateField.botEquiv ℚ K).symm (IntermediateField.botEquiv ℚ K (g s))) := by
            rw [(IntermediateField.botEquiv ℚ K).symm_apply_apply]
    _ = algebraMap ↥(⊥ : IntermediateField ℚ K) K
          (algebraMap ℚ ↥(⊥ : IntermediateField ℚ K)
            (IntermediateField.botEquiv ℚ K (g s))) := by
          rfl
    _ = algebraMap ℚ K (IntermediateField.botEquiv ℚ K (g s)) := by
          exact (IsScalarTower.algebraMap_apply ℚ ↥(⊥ : IntermediateField ℚ K) K
            (IntermediateField.botEquiv ℚ K (g s))).symm

/-- Helper for Theorem 13-13.1-3: the source owner `ℚ ⊗ R_{↥⊥}(G)` is transported to
`ℚ ⊗ R_ℚ(G)` by the pointwise bottom-field equivalence. -/
private theorem bot_equiv_mem_characterRingOverFieldScalarExtension_iff
    (g : G → ↥(⊥ : IntermediateField ℚ K)) :
    g ∈ ℚ⊗R[↥(⊥ : IntermediateField ℚ K)](G) ↔
      (fun s ↦ IntermediateField.botEquiv ℚ K (g s)) ∈ ℚ⊗R[ℚ](G) := by
  let e : (G → ↥(⊥ : IntermediateField ℚ K)) →ₗ[ℚ] G → ℚ :=
    ((IntermediateField.botEquiv ℚ K).toLinearEquiv.compLeft G)
  have hmap :
      Submodule.map e (ℚ⊗R[↥(⊥ : IntermediateField ℚ K)](G)) = ℚ⊗R[ℚ](G) := by
    -- Route correction: transport the source owner first, before comparing the two maps into `K`.
    change Submodule.map e
        (Submodule.span ℚ
          (((R[↥(⊥ : IntermediateField ℚ K)](G)).toSubmodule :
            Submodule ℤ (G → ↥(⊥ : IntermediateField ℚ K))) :
              Set (G → ↥(⊥ : IntermediateField ℚ K)))) =
      Submodule.span ℚ
        (((R[ℚ](G)).toSubmodule : Submodule ℤ (G → ℚ)) : Set (G → ℚ))
    rw [Submodule.map_span]
    congr 1
    ext χ
    constructor
    · rintro ⟨ψ, hψ, rfl⟩
      exact bot_equiv_mem_characterRingOverField_of_mem (G := G) (K := K) (by simpa using hψ)
    · intro hχ
      refine ⟨fun s ↦ (IntermediateField.botEquiv ℚ K).symm (χ s), ?_, ?_⟩
      · exact bot_symm_mem_characterRingOverField_of_mem (G := G) (K := K) hχ
      · ext s
        simp [e, IntermediateField.botEquiv_symm]
  constructor
  · intro hg
    have hem : e g ∈ Submodule.map e (ℚ⊗R[↥(⊥ : IntermediateField ℚ K)](G)) :=
      Submodule.mem_map.mpr ⟨g, hg, rfl⟩
    rw [hmap] at hem
    simpa [e] using hem
  · intro hg
    have hem : e g ∈ Submodule.map e (ℚ⊗R[↥(⊥ : IntermediateField ℚ K)](G)) := by
      rw [hmap]
      simpa [e] using hg
    rcases Submodule.mem_map.mp hem with ⟨g', hg', hg'eq⟩
    have hgg' : g' = g := by
      ext s
      exact congrArg (fun x : ↥(⊥ : IntermediateField ℚ K) => (x : K)) <|
        (IntermediateField.botEquiv ℚ K).injective (congrFun hg'eq s)
    simpa [hgg'] using hg'

/-- Helper for Theorem 13-13.1-3: transport the Chapter `12` bottom-field scalar-extension owner
to the literal rational field `ℚ`. -/
private theorem bot_field_scalar_extension_transport
    (f : G → K) :
    f ∈ (ℚ⊗R[↥(⊥ : IntermediateField ℚ K)](G)).map
          (classFunctionScalarExtension G ↥(⊥ : IntermediateField ℚ K) K) ↔
      f ∈ (ℚ⊗R[ℚ](G)).map (classFunctionScalarExtension G ℚ K) := by
  constructor
  · intro hf
    rcases Submodule.mem_map.mp hf with ⟨g, hg, rfl⟩
    -- First transport the source owner, then rewrite the scalar-extension map into `K`.
    refine Submodule.mem_map.mpr ?_
    refine ⟨fun s ↦ IntermediateField.botEquiv ℚ K (g s), ?_, ?_⟩
    · exact (bot_equiv_mem_characterRingOverFieldScalarExtension_iff (G := G) (K := K) g).1 hg
    · simpa using (bot_equiv_classFunctionScalarExtension (G := G) (K := K) g).symm
  · intro hf
    rcases Submodule.mem_map.mp hf with ⟨g, hg, rfl⟩
    -- Use the inverse transport on coefficients to build a bottom-field witness.
    refine Submodule.mem_map.mpr ?_
    refine ⟨fun s ↦ (IntermediateField.botEquiv ℚ K).symm (g s), ?_, ?_⟩
    · have hpre :
        (fun s ↦ IntermediateField.botEquiv ℚ K
          ((IntermediateField.botEquiv ℚ K).symm (g s))) ∈
            ℚ⊗R[ℚ](G) := by
            simpa using hg
      exact (bot_equiv_mem_characterRingOverFieldScalarExtension_iff (G := G) (K := K)
        (fun s ↦ (IntermediateField.botEquiv ℚ K).symm (g s))).2 hpre
    · ext s
      change algebraMap ↥(⊥ : IntermediateField ℚ K) K
        ((IntermediateField.botEquiv ℚ K).symm (g s)) = algebraMap ℚ K (g s)
      rw [IntermediateField.botEquiv_symm]
      rfl

/-- Theorem 13-13.1-3 (1): for a `K`-valued class function on `G`, where `K` is a cyclotomic
extension realizing the source field `ℚ(m)` with `m = Monoid.exponent G`, membership in Serre's
rational character ring `ℚ ⊗ R(G)`, realized inside `G → K` as the `ℚ`-span (equivalently the
bottom-field span) of the ordinary `K`-valued characters of `G`, is equivalent to the compatibility
condition `σ_t(f) = Ψ^t(f)` for every `t ∈ (ℤ / mℤ)ˣ`, written using the canonical cyclotomic
Galois action of `Γ_ℚ` on `K`. -/
theorem cyclotomic_valued_classFunction_mem_rational_character_ring_iff_galois_compatible
    (f : G → K) (hf : _root_.IsClassFunction f) :
    f ∈ Submodule.span (⊥ : IntermediateField ℚ K) ((R[K](G) : Set (G → K))) ↔
      ∀ s (t : Γ_ℚ(G)),
        t • f s = f (s ^ t) := by
  haveI : NumberField K := IsCyclotomicExtension.numberField {Monoid.exponent G} ℚ K
  let φ : classFunctionSubmodule K G := ⟨f, (mem_classFunctionSubmodule_iff K _).2 hf⟩
  have hGammaBot : Γ[(⊥ : IntermediateField ℚ K)](G) = ⊤ := by
    -- Over the bottom field `ℚ`, the cyclotomic Galois subgroup is the full unit group.
    unfold Representation.gammaSubgroup
    letI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {Monoid.exponent G} ℚ K
    have hfixingSubgroupBot : (⊥ : IntermediateField ℚ K).fixingSubgroup = ⊤ :=
      IsGaloisGroup.fixingSubgroup_bot (G := Gal(K / ℚ)) (K := ℚ) (L := K)
    rw [hfixingSubgroupBot]
    simp
  have howner :
      f ∈ Submodule.span (⊥ : IntermediateField ℚ K) ((R[K](G) : Set (G → K))) ↔
        ∀ s (t : Γ[(⊥ : IntermediateField ℚ K)](G)), t • f s = f (s ^ t) := by
    -- Bundle `f` as a class function and specialize the Chapter `12` owner theorem to `⊥`.
    simpa [φ] using
      (Representation.classFunction_mem_characterRingOverFieldScalarExtension_map_iff_galoisCompatible
        (G := G) (L := K) (K := (⊥ : IntermediateField ℚ K)) φ)
  calc
    f ∈ Submodule.span (⊥ : IntermediateField ℚ K) ((R[K](G) : Set (G → K))) ↔
        ∀ s (t : Γ[(⊥ : IntermediateField ℚ K)](G)), t • f s = f (s ^ t) := howner
    _ ↔ ∀ s (t : Γ_ℚ(G)), t • f s = f (s ^ t) := by
      -- Replace the bottom-field subgroup by the full unit group, which is `Γ_ℚ(G)`.
      constructor
      · intro h s t
        let tBot : Γ[(⊥ : IntermediateField ℚ K)](G) := ⟨t, by simpa [hGammaBot]⟩
        simpa [tBot, Representation.pow_subgroup_eq_pow_nat, Representation.pow_unit_eq_pow_nat]
          using h s tBot
      · intro h s t
        simpa [Representation.pow_subgroup_eq_pow_nat, Representation.pow_unit_eq_pow_nat]
          using h s (t : Γ_ℚ(G))

-- Proof sketch: specialize part (1) to the rational field, where the Galois action on values is
-- trivial; equivalently, this is the rational-field case of the Chapter `12` criterion for
-- `ℚ ⊗ R_ℚ(G)`, with the source condition "values in `ℚ`" encoded by the codomain of `f`.
/-- Helper for Theorem 13-13.1-3: the `Γ_ℚ(G)`-action fixes rational scalars embedded in `K`. -/
private theorem gammaRat_smul_algebraMap_rat
    (q : ℚ) (t : Γ_ℚ(G)) :
    t • (algebraMap ℚ K q) = algebraMap ℚ K q := by
  haveI : NumberField K := IsCyclotomicExtension.numberField {Monoid.exponent G} ℚ K
  -- The cyclotomic action is through `ℚ`-algebra automorphisms, so it fixes the image of `ℚ`.
  change
      (IsCyclotomicExtension.Rat.galEquivZMod (Monoid.exponent G) K).symm t
        (algebraMap ℚ K q) =
    _
  simpa using
    AlgEquiv.commutes
      ((IsCyclotomicExtension.Rat.galEquivZMod (Monoid.exponent G) K).symm t) q

/-- Helper for Theorem 13-13.1-3: extending a rational-valued class function to `K` does not
change whether it comes from `ℚ ⊗ R_ℚ(G)`. -/
private theorem rational_scalar_extension_mem_map_iff
    (f : G → ℚ) :
    classFunctionScalarExtension G ℚ K f ∈
      (ℚ⊗R[ℚ](G)).map (classFunctionScalarExtension G ℚ K) ↔
      f ∈ ℚ⊗R[ℚ](G) := by
  constructor
  · intro hf
    -- Compare the two preimages using injectivity of `algebraMap ℚ K`.
    rcases Submodule.mem_map.mp hf with ⟨g, hg, hg_eq⟩
    have hgf : g = f := by
      ext s
      apply (algebraMap ℚ K).injective
      simpa [Representation.classFunctionScalarExtension] using congrFun hg_eq s
    simpa [hgf] using hg
  · intro hf
    -- The forward map witnesses membership immediately.
    exact Submodule.mem_map.mpr ⟨f, hf, rfl⟩

/-- Helper for Theorem 13-13.1-3: when the structure map `ℚ → K` is surjective (as it is for the
bottom field `↥⊥`), spanning `R[K](G)` over `K` and over `ℚ` produces the same submodule, so
membership in either scalar extension is the same condition. -/
private theorem mem_characterRingOverFieldAlgebraScalarExtension_self_iff_rat
    {F : Type*} [Field F] [CharZero F] [Algebra ℚ F]
    (hsurj : Function.Surjective (algebraMap ℚ F)) (f : G → F) :
    f ∈ F⊗R[F](G) ↔ f ∈ ℚ⊗R[F](G) := by
  unfold Representation.characterRingOverFieldAlgebraScalarExtension
  constructor
  · intro hf
    induction hf using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
        obtain ⟨q, rfl⟩ := hsurj a
        rw [algebraMap_smul]
        exact Submodule.smul_mem _ q hx
  · intro hf
    induction hf using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
        rw [← algebraMap_smul F a x]
        exact Submodule.smul_mem _ _ hx

/-- Helper for Theorem 13-13.1-3: the structure map `ℚ → ↥⊥` into the bottom intermediate field
is surjective. -/
private theorem algebraMap_rat_bot_surjective
    {F : Type*} [Field F] [CharZero F] :
    Function.Surjective (algebraMap ℚ ↥(⊥ : IntermediateField ℚ F)) := by
  intro x
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp x.2
  exact ⟨q, by ext; exact hq⟩

/-- Theorem 13-13.1-3 (2): a rational-valued class function belongs to Serre's
`ℚ ⊗ R_ℚ(G)` exactly when it is fixed by every power operation `Ψ^t` with
`t ∈ (ℤ / mℤ)ˣ`, where `m = Monoid.exponent G`; the source requirement that `f` have values in
`ℚ` is represented here by taking `f : G → ℚ`. -/
theorem rational_valued_classFunction_mem_rational_character_ring_iff_power_invariant
    (f : G → ℚ) (hf : _root_.IsClassFunction f) :
    f ∈ ℚ⊗R[ℚ](G) ↔
      ∀ s (t : Γ_ℚ(G)),
        f s = f (s ^ t) := by
  let Lexp := CyclotomicField (Monoid.exponent G) ℚ
  letI : Field Lexp := inferInstance
  letI : CharZero Lexp := inferInstance
  letI : NumberField Lexp := inferInstance
  letI : IsCyclotomicExtension {Monoid.exponent G} ℚ Lexp :=
    CyclotomicField.isCyclotomicExtension (n := Monoid.exponent G) (K := ℚ)
  let fBot : G → ↥(⊥ : IntermediateField ℚ Lexp) :=
    fun s ↦ (IntermediateField.botEquiv ℚ Lexp).symm (f s)
  have hfBotClass : _root_.IsClassFunction fBot := by
    -- Composing with the bottom-field equivalence preserves the class-function condition.
    exact hf.comp ((IntermediateField.botEquiv ℚ Lexp).symm : ℚ → ↥(⊥ : IntermediateField ℚ Lexp))
  let φBot : classFunctionSubmodule (⊥ : IntermediateField ℚ Lexp) G :=
    ⟨fBot, (mem_classFunctionSubmodule_iff _ _).2 hfBotClass⟩
  have hGammaBot : Γ[(⊥ : IntermediateField ℚ Lexp)](G) = ⊤ := by
    -- Over the bottom field `ℚ`, the cyclotomic Galois subgroup is the full unit group.
    unfold Representation.gammaSubgroup
    letI : IsGalois ℚ Lexp := IsCyclotomicExtension.isGalois {Monoid.exponent G} ℚ Lexp
    have hfixingSubgroupBot : (⊥ : IntermediateField ℚ Lexp).fixingSubgroup = ⊤ :=
      IsGaloisGroup.fixingSubgroup_bot (G := Gal(Lexp / ℚ)) (K := ℚ) (L := Lexp)
    rw [hfixingSubgroupBot]
    simp
  have howner :
      fBot ∈ ℚ⊗R[↥(⊥ : IntermediateField ℚ Lexp)](G) ↔
        ∀ s (t : Γ[(⊥ : IntermediateField ℚ Lexp)](G)), fBot s = fBot (s ^ t) := by
    -- Apply the Chapter 12 invariant criterion over the bottom intermediate field; the owner gives
    -- membership in the `↥⊥`-span, which coincides with the `ℚ`-span because `ℚ → ↥⊥` is onto.
    rw [← mem_characterRingOverFieldAlgebraScalarExtension_self_iff_rat
      (G := G) (F := ↥(⊥ : IntermediateField ℚ Lexp)) algebraMap_rat_bot_surjective fBot]
    simpa [φBot] using
      (Representation.classFunction_mem_characterRingOverFieldScalarExtension_iff_gammaSubgroup_invariant
        (G := G) (L := Lexp) (K := (⊥ : IntermediateField ℚ Lexp))
        φBot)
  calc
    f ∈ ℚ⊗R[ℚ](G) ↔
        fBot ∈ ℚ⊗R[↥(⊥ : IntermediateField ℚ Lexp)](G) := by
          simpa [fBot] using
            (bot_equiv_mem_characterRingOverFieldScalarExtension_iff
              (G := G) (K := Lexp) fBot).symm
    _ ↔ ∀ s (t : Γ[(⊥ : IntermediateField ℚ Lexp)](G)), fBot s = fBot (s ^ t) := howner
    _ ↔ ∀ s (t : Γ_ℚ(G)), f s = f (s ^ t) := by
      constructor
      · intro h s t
        let tBot : Γ[(⊥ : IntermediateField ℚ Lexp)](G) := ⟨t, by simp [hGammaBot]⟩
        simpa [fBot, tBot, pow_subgroup_eq_pow_nat, pow_unit_eq_pow_nat] using
          congrArg (IntermediateField.botEquiv ℚ Lexp) (h s tBot)
      · intro h s t
        apply (IntermediateField.botEquiv ℚ Lexp).injective
        simpa [fBot, pow_subgroup_eq_pow_nat, pow_unit_eq_pow_nat] using h s (t : Γ_ℚ(G))

end
