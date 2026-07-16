import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_96_1
import stacks_proof.stacks_project.Chap10.Lemma_10_96_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open AdicCompletion Submodule

variable {R : Type u} [CommRing R]
variable {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]
variable [IsAdicComplete I R]
variable [Module.Finite (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))]

-- Domain-style sampling:
-- * source-facing layer: the Stacks criterion that finite generation of `M / IM` plus
--   `⋂ n, I ^ n M = 0` over an `I`-adically complete ring forces `M` itself to be finite.
-- * core/canonical owner: `IsHausdorff I M` for the separatedness hypothesis.
-- * sampled upstream declarations:
--   `IsAdicComplete`,
--   `IsHausdorff`,
--   `IsHausdorff.iInf_pow_smul`,
--   `isAdicComplete_of_finite_of_iInf_pow_smul_eq_bot`.
-- * primitive data: the ring-completeness hypothesis and the finite quotient module
--   `M ⧸ I • ⊤`.
-- * derived API: the equality `⨅ n, I ^ n • ⊤ = ⊥` is the source-facing formulation of the
--   canonical separatedness owner `IsHausdorff I M`.

-- Proof sketch: choose finitely many lifts in `M` of generators of `M / IM`, and let `M'` be the
-- submodule they generate. Lemma `10.96.1` gives a surjection `(M')^∧ → M^∧`, while
-- Lemma `10.96.11` makes `M'` complete because it is finite and inherits
-- `⋂ n, I^n M' = 0`. Thus `M' → M^∧` is surjective. Since the kernel of `M → M^∧` is
-- `⋂ n, I^n M = 0`, the inclusion `M' → M` is surjective, so `M` is finitely generated.
omit [IsAdicComplete I R] [Module.Finite (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))] in
/-- Helper for Lemma 10.96.12: the intersection condition `⋂ n, I ^ n M = 0` is exactly the
Hausdorffness condition needed by the completion API. -/
lemma isHausdorff_of_iInf_pow_smul_eq_bot
    (hM : (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M) : Submodule R M) = ⊥) :
    IsHausdorff I M := by
  -- Repackage the source-facing intersection hypothesis into the owner-facing Hausdorff API.
  refine ⟨fun x hx ↦ ?_⟩
  have hx' : x ∈ (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M) : Submodule R M) := by
    simpa [SModEq.zero] using hx
  simpa [hM] using hx'

omit [IsAdicComplete I R] [Module.Finite (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))] in
/-- Helper for Lemma 10.96.12: a submodule of a Hausdorff module is Hausdorff for the induced
`I`-adic topology. -/
lemma isHausdorff_submodule [IsHausdorff I M] (N : Submodule R M) :
    IsHausdorff I N := by
  -- View a compatible system in `N` inside `M`, where Hausdorffness is already available.
  have hhausM : IsHausdorff I M := inferInstance
  refine ⟨fun x hx ↦ ?_⟩
  apply Subtype.ext
  apply hhausM.haus x.1
  intro n
  rw [SModEq.zero]
  have hx_mem : x ∈ I ^ n • (⊤ : Submodule R N) := by
    simpa [SModEq.zero] using hx n
  have hx_map : x.1 ∈ Submodule.map N.subtype (I ^ n • (⊤ : Submodule R N)) := by
    exact ⟨x, hx_mem, rfl⟩
  have hx_in_submodule : x.1 ∈ I ^ n • N := by
    simpa [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype] using hx_map
  exact (smul_mono le_rfl (show N ≤ (⊤ : Submodule R M) from le_top)) hx_in_submodule

omit [IsAdicComplete I R] [Module.Finite (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))] in
/-- Helper for Lemma 10.96.12: if a finite family of lifts maps to generators of `M / IM`, then
the span of those lifts maps onto all of `M / IM`. -/
lemma map_mkQ_span_eq_top_of_lifts {n : ℕ} {x : Fin n → M}
    {xbar : Fin n → M ⧸ I • (⊤ : Submodule R M)}
    (hx : ∀ i, Submodule.mkQ (I • (⊤ : Submodule R M)) (x i) = xbar i)
    (hspan : Submodule.span R (Set.range xbar) = ⊤) :
    Submodule.map (Submodule.mkQ (I • (⊤ : Submodule R M)))
      (Submodule.span R (Set.range x)) = ⊤ := by
  -- Push the span through the quotient map and identify the image set with the chosen generators.
  have himage :
      (Submodule.mkQ (I • (⊤ : Submodule R M))) '' Set.range x = Set.range xbar := by
    ext y
    constructor
    · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hx i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨x i, ⟨i, rfl⟩, hx i⟩
  rw [Submodule.map_span, himage, hspan]

omit [IsAdicComplete I R] [Module.Finite (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))] in
/-- Helper for Lemma 10.96.12: if the quotient map sends a submodule onto all of `M / IM`, then
the composite of the subtype map with the quotient map is surjective. -/
lemma surjective_mkQ_comp_subtype_of_map_eq_top {N : Submodule R M}
    (hN : Submodule.map (Submodule.mkQ (I • (⊤ : Submodule R M))) N = ⊤) :
    Function.Surjective (Submodule.mkQ (I • (⊤ : Submodule R M)) ∘ₗ N.subtype) := by
  -- Translate the submodule-image equality into the usual `range = ⊤` criterion for surjectivity.
  rw [← LinearMap.range_eq_top]
  simpa [LinearMap.range_comp, Submodule.range_subtype] using hN

/-- Lemma 10.96.12: if `R` is `I`-adically complete, `⋂ n, I ^ n M = 0`, and the quotient
`M / IM` is a finite `R / I`-module, then `M` is a finite `R`-module. -/
@[stacks 031D]
theorem moduleFinite_of_finite_quotient_of_iInf_pow_smul_eq_bot
    (hM : (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M) : Submodule R M) = ⊥) :
    Module.Finite R M := by
  -- First convert the source hypothesis to the canonical separatedness API for `M`.
  letI : IsHausdorff I M := isHausdorff_of_iInf_pow_smul_eq_bot (I := I) hM
  let Q : Type v := M ⧸ I • (⊤ : Submodule R M)
  -- Restrict scalars along `R → R / I` so the finite quotient has an `R`-generating family.
  have hfgQ : (⊤ : Submodule R Q).FG := by
    have hfgQ' : (⊤ : Submodule (R ⧸ I) Q).FG :=
      Module.Finite.fg_top (R := R ⧸ I) (M := Q)
    simpa [Q] using
      (Submodule.FG.restrictScalars_of_surjective
        (R := R) (A := R ⧸ I) (M := Q) (S := (⊤ : Submodule (R ⧸ I) Q))
        hfgQ' Ideal.Quotient.mk_surjective)
  -- Choose finitely many quotient generators and lift them back to `M`.
  obtain ⟨n, xbar, hspanbar⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfgQ
  choose x hx using fun i : Fin n ↦
    Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) (xbar i)
  let N : Submodule R M := Submodule.span R (Set.range x)
  have hfiniteN : Module.Finite R N := by
    -- The lift-span is finite because it is generated by finitely many elements.
    simpa [N] using Module.Finite.span_of_finite R (Set.finite_range x)
  have hmapN :
      Submodule.map (Submodule.mkQ (I • (⊤ : Submodule R M))) N = ⊤ := by
    -- The chosen lifts still generate after quotienting by `I`.
    simpa [N] using map_mkQ_span_eq_top_of_lifts (I := I) hx hspanbar
  have hsurjQ :
      Function.Surjective (Submodule.mkQ (I • (⊤ : Submodule R M)) ∘ₗ N.subtype) :=
    surjective_mkQ_comp_subtype_of_map_eq_top (I := I) hmapN
  have hhausN : IsHausdorff I N := isHausdorff_submodule (I := I) N
  have hNbot : (⨅ n : ℕ, I ^ n • (⊤ : Submodule R N) : Submodule R N) = ⊥ :=
    IsHausdorff.iInf_pow_smul hhausN
  letI : Module.Finite R N := hfiniteN
  have hcompleteN : IsAdicComplete I N := by
    -- Lemma `10.96.11` makes the finite Hausdorff span complete.
    exact isAdicComplete_of_finite_of_iInf_pow_smul_eq_bot (I := I) (M := N) hNbot
  letI : IsAdicComplete I N := hcompleteN
  have hsurjN : Function.Surjective N.subtype := by
    -- Lemma `10.96.1` upgrades surjectivity modulo `I` to surjectivity of the inclusion itself.
    exact surjective_of_mkQ_comp_surjective (I := I) (f := N.subtype) hsurjQ
  -- A finite submodule surjecting onto `M` exhibits `M` as finite.
  exact Module.Finite.of_surjective N.subtype hsurjN

/-- Canonical owner-facing form of Lemma `10.96.12`, using `IsHausdorff I M` for the separatedness
hypothesis instead of the explicit intersection formula. -/
theorem moduleFinite_of_finite_quotient_of_isHausdorff [IsHausdorff I M] :
    Module.Finite R M := by
  have hM : (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M) : Submodule R M) = ⊥ :=
    IsHausdorff.iInf_pow_smul inferInstance
  simpa using moduleFinite_of_finite_quotient_of_iInf_pow_smul_eq_bot hM

end
