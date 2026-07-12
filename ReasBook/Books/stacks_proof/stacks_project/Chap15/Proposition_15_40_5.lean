import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap10.Lemma_10_112_8
import StacksProject_2024.Chap10.Lemma_10_166_5
import StacksProject_2024.Chap15.Definition_15_37_3
import StacksProject_2024.Chap15.Lemma_15_38_2
import StacksProject_2024.Chap15.Lemma_15_40_3

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open IsLocalRing
open scoped TensorProduct

universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
variable [IsLocalHom (algebraMap A B)]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal A) B
local notation "𝔪ClosedFiber" => Ideal.map (algebraMap B ClosedFiber) (maximalIdeal B)

namespace Proposition_15_40_5

/-- Helper for Proposition 15.40.5: the maximal-ideal residue field of a local ring agrees with
its ordinary residue field. -/
noncomputable abbrev maximalIdeal_residueField_equiv
    (R : Type*) [CommRing R] [IsLocalRing R] :
    (maximalIdeal R).ResidueField ≃+* ResidueField R :=
  (RingEquiv.ofBijective
    (algebraMap (ResidueField R) (maximalIdeal R).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))).symm

/-- Helper for Proposition 15.40.5: precomposing an adically formally smooth map with a ring
equivalence of discrete source rings preserves adic formal smoothness. -/
theorem formally_smooth_for_adic_of_domain_ringEquiv
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    (e : R ≃+* S) (f : S →+* T) {J : Ideal T}
    (hf : RingHom.formally_smooth_for_adic f J) :
    RingHom.formally_smooth_for_adic (f.comp e.toRingHom) J := by
  -- Proof comment: move the lifting problem across the inverse ring equivalence on the discrete
  -- source, solve it over `S`, and then evaluate the resulting lift back on `R`.
  rw [RingHom.formally_smooth_for_adic_iff] at hf ⊢
  letI : TopologicalSpace R := ⊥
  letI : DiscreteTopology R := ⟨rfl⟩
  letI : TopologicalSpace S := ⊥
  letI : DiscreteTopology S := ⟨rfl⟩
  letI : TopologicalSpace T := Ideal.adicTopology J
  refine
    { toContinuous := hf.toContinuous.comp continuous_of_discreteTopology
      lift_condition := ?_ }
  intro C _ _ _ L _ hL g hg g0 hg0 hcomm
  let g0S : S →+* C := g0.comp e.symm.toRingHom
  have hg0S : Continuous g0S := hg0.comp continuous_of_discreteTopology
  have hcommS : (Ideal.Quotient.mk L).comp g0S = g.comp f := by
    -- Proof comment: rewrite the square after transporting the source variable through `e.symm`.
    ext s
    simpa [g0S, RingHom.comp_assoc] using DFunLike.congr_fun hcomm (e.symm s)
  obtain ⟨φ, hφcont, hφquot, hφbase⟩ :=
    RingHom.FormallySmoothTopologically.exists_lift hf L hL g hg g0S hg0S hcommS
  refine ⟨φ, hφcont, hφquot, ?_⟩
  -- Proof comment: the lift over `S` induces the desired lift over `R` by evaluation on `e r`.
  ext r
  simpa [g0S, RingHom.comp_assoc] using DFunLike.congr_fun hφbase (e r)

omit [IsNoetherianRing A] [IsNoetherianRing B] in
/-- Helper for Proposition 15.40.5: the closed fiber of a local homomorphism between local rings
is again a local ring. -/
theorem closedFiber_isLocalRing_aux :
    IsLocalRing ClosedFiber := by
  let e :
      ClosedFiber ≃ₐ[A] B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A) :=
    closedFiberQuotAlgEquiv
  letI : IsLocalRing (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) := by
    -- Proof comment: the quotient by the image of the source maximal ideal is nontrivial and
    -- receives a surjective map from the local ring `B`, so it is local.
    have hmap : Ideal.map (algebraMap A B) (maximalIdeal A) < (⊤ : Ideal B) :=
      IsLocalRing.map_maximalIdeal_lt_top (algebraMap A B)
    have : Nontrivial (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) :=
      Ideal.Quotient.nontrivial_iff.2 hmap.ne
    exact IsLocalRing.of_surjective'
      (Ideal.Quotient.mk (Ideal.map (algebraMap A B) (maximalIdeal A)))
      Ideal.Quotient.mk_surjective
  exact e.toRingEquiv.symm.isLocalRing

/-- Helper for Proposition 15.40.5: the quotient presentation of the closed fiber agrees with the
canonical `B`-algebra map into the tensor-product model. -/
private theorem closedFiber_quotient_comp_eq_algebraMap :
    ((closedFiberQuotAlgEquiv (R := A) (S := B)).symm.toRingHom).comp
        (Ideal.Quotient.mk (Ideal.map (algebraMap A B) (maximalIdeal A))) =
      algebraMap B ClosedFiber := by
  -- Proof comment: the source proof uses the quotient presentation `B / m_A B`; here we isolate
  -- the exact comparison with the tensor-product owner `ClosedFiber`.
  ext b
  -- Proof comment: after rewriting the owner-side `B`-algebra map as the tensor `includeRight`
  -- branch, the closed-fiber quotient equivalence sends the class of `b` to the pure tensor
  -- `1 ⊗ₜ b` by its defining quotient/tensor comparison.
  change
    ((closedFiberQuotAlgEquiv (R := A) (S := B)).symm
      ((Ideal.Quotient.mk (Ideal.map (algebraMap A B) (maximalIdeal A))) b)) =
      (Algebra.TensorProduct.includeRight : B →ₐ[A] ClosedFiber) b
  simp [closedFiberQuotAlgEquiv]

omit [IsLocalRing B] [IsNoetherianRing A] [IsLocalHom (algebraMap A B)] in
/-- Helper for Proposition 15.40.5: the closed fiber is Noetherian via its quotient
presentation. -/
theorem closedFiber_isNoetherianRing_aux :
    IsNoetherianRing ClosedFiber :=
  isNoetherianRing_of_ringEquiv
    (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A))
    (closedFiberQuotAlgEquiv (R := A) (S := B)).toRingEquiv.symm

/-- Helper for Proposition 15.40.5: the canonical map from the target ring onto the closed fiber
is surjective. -/
private theorem closedFiber_algebraMap_surjective :
    Function.Surjective (algebraMap B ClosedFiber) := by
  intro x
  obtain ⟨b, hb⟩ :=
    Ideal.Quotient.mk_surjective
      ((closedFiberQuotAlgEquiv (R := A) (S := B)) x)
  refine ⟨b, ?_⟩
  have hcomp :
      ((closedFiberQuotAlgEquiv (R := A) (S := B)).symm
        ((Ideal.Quotient.mk (Ideal.map (algebraMap A B) (maximalIdeal A))) b)) =
        (algebraMap B ClosedFiber) b := by
    simpa using
      congrArg (fun f : B →+* ClosedFiber ↦ f b)
        (closedFiber_quotient_comp_eq_algebraMap (A := A) (B := B))
  have hx :
      ((closedFiberQuotAlgEquiv (R := A) (S := B)).symm
        ((Ideal.Quotient.mk (Ideal.map (algebraMap A B) (maximalIdeal A))) b)) = x := by
    simpa using congrArg (closedFiberQuotAlgEquiv (R := A) (S := B)).symm hb
  exact hcomp.symm.trans hx

/-- Helper for Proposition 15.40.5: the image of the maximal ideal of `B` in the closed fiber is
the maximal ideal of the closed fiber. -/
theorem closedFiber_map_maximalIdeal_eq_maximalIdeal
    [IsLocalRing ClosedFiber] :
    𝔪ClosedFiber = maximalIdeal ClosedFiber := by
  -- Proof comment: once `B → ClosedFiber` is recognized as a surjection onto a local ring, the
  -- maximal ideal of the target is exactly the image of the maximal ideal of `B`.
  exact IsLocalRing.map_maximalIdeal_of_surjective
    (algebraMap B ClosedFiber) (closedFiber_algebraMap_surjective (A := A) (B := B))

/-- Helper for Proposition 15.40.5: adic formal smoothness of the source map forces flatness and
base-changes to adic formal smoothness of the closed-fiber map. -/
theorem closedFiber_formallySmooth_of_source_formallySmooth
    (hfs : (algebraMap A B).formally_smooth_for_adic (maximalIdeal B)) :
    (algebraMap A B).Flat ∧
      RingHom.formally_smooth_for_adic (algebraMap (ResidueField A) ClosedFiber) 𝔪ClosedFiber := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: Lemma `15.40.3` already isolates flatness from source adic formal smoothness.
    simpa using
      RingHom.flat_of_formallySmooth_for_maximalIdeal_adic
        (A := A) (B := B) (f := algebraMap A B) hfs
  · have hbase :
        RingHom.formally_smooth_for_adic
          (Algebra.TensorProduct.includeLeftRingHom :
            (maximalIdeal A).ResidueField →+* ClosedFiber)
          𝔪ClosedFiber := by
        -- Proof comment: this is exactly the source-proof base change along `A → κ(A)`.
        simpa using
          RingHom.formally_smooth_for_adic_baseChange
            (R := A) (S := B) (R' := (maximalIdeal A).ResidueField)
            (𝔫 := maximalIdeal B) hfs
    -- Proof comment: transport the source ring from the ideal residue field to the ordinary
    -- residue field of the local ring `A`.
    simpa using
      formally_smooth_for_adic_of_domain_ringEquiv
        ((maximalIdeal_residueField_equiv A).symm)
        (Algebra.TensorProduct.includeLeftRingHom :
          (maximalIdeal A).ResidueField →+* ClosedFiber) hbase

end Proposition_15_40_5

/-- Helper for Proposition 15.40.5: the closed fiber criterion `(geometrically regular) ↔
formally smooth for the maximal-ideal-adic topology` is the field-valued Theorem `15.40.1`. -/
lemma closedFiber_geometricallyRegular_iff_formally_smooth :
    Algebra.IsGeometricallyRegular (ResidueField A) ClosedFiber ↔
      RingHom.formally_smooth_for_adic (algebraMap (ResidueField A) ClosedFiber) 𝔪ClosedFiber := by
  -- Route correction: the intended proof runs through Theorem `15.40.1`, but the current
  -- workspace cannot import that theorem because its prerequisite `Lemma_15_38_5` does not
  -- compile. Keep the precise bridge statement here so the theorem skeleton below is stable.
  -- TODO: once `Theorem_15_40_1` is importable, prove this by the characteristic split from the
  -- source proof, using the characteristic-zero helper above and the positive-characteristic TFAE.
  sorry

/-- Helper for Proposition 15.40.5: adic formal smoothness of the source map already implies
flatness by Lemma `15.40.3`. -/
lemma source_formally_smooth_implies_flat
    (hfs : (algebraMap A B).formally_smooth_for_adic (maximalIdeal B)) :
    (algebraMap A B).Flat := by
  -- Proof comment: this is exactly the flatness descent statement already isolated in
  -- Lemma `15.40.3`.
  simpa using
    RingHom.flat_of_formallySmooth_for_maximalIdeal_adic
      (A := A) (B := B) (f := algebraMap A B) hfs

/-- Helper for Proposition 15.40.5: adic formal smoothness of the source map forces flatness and
survives after base change to the closed fiber. -/
lemma source_formally_smooth_implies_flat_and_closedFiber_formally_smooth
    (hfs : (algebraMap A B).formally_smooth_for_adic (maximalIdeal B)) :
    (algebraMap A B).Flat ∧
      RingHom.formally_smooth_for_adic (algebraMap (ResidueField A) ClosedFiber) 𝔪ClosedFiber := by
  -- Proof comment: delegate the source-proof base-change step to the theorem-local transport
  -- helper so the target file no longer re-elaborates the quotient/fiber bridge.
  simpa using
    Proposition_15_40_5.closedFiber_formallySmooth_of_source_formallySmooth
      (A := A) (B := B) hfs

/-- Helper for Proposition 15.40.5: formal smoothness of the closed-fiber structure map makes the
closed fiber a regular local ring. -/
lemma closedFiber_regularLocal_of_formally_smooth
    (hfs :
      RingHom.formally_smooth_for_adic (algebraMap (ResidueField A) ClosedFiber) 𝔪ClosedFiber) :
    IsRegularLocalRing ClosedFiber := by
  letI : IsLocalRing ClosedFiber :=
    Proposition_15_40_5.closedFiber_isLocalRing_aux (A := A) (B := B)
  letI : IsNoetherianRing ClosedFiber :=
    Proposition_15_40_5.closedFiber_isNoetherianRing_aux (A := A) (B := B)
  -- Proof comment: rewrite the adic ideal on the closed fiber to its actual maximal ideal, then
  -- apply the regular-local criterion from Lemma `15.38.2`.
  have hfs_max :
      RingHom.formally_smooth_for_adic
        (algebraMap (ResidueField A) ClosedFiber) (maximalIdeal ClosedFiber) := by
    simpa [Proposition_15_40_5.closedFiber_map_maximalIdeal_eq_maximalIdeal (A := A) (B := B)]
      using hfs
  exact
    isRegularLocalRing_of_formallySmooth_for_maximalIdeal_adic
      (k := ResidueField A) (A := ClosedFiber) hfs_max

/-- Helper for Proposition 15.40.5: the hard direction `(flat + formally smooth closed fiber) →
formal smoothness` is the complete-local presentation argument from the source proof. -/
lemma formally_smooth_of_flat_and_closedFiber_formally_smooth
    (hflat : (algebraMap A B).Flat)
    (hfsFiber :
      RingHom.formally_smooth_for_adic (algebraMap (ResidueField A) ClosedFiber) 𝔪ClosedFiber) :
    (algebraMap A B).formally_smooth_for_adic (maximalIdeal B) := by
  -- Route correction: the missing step is not a local rewrite but the full source-faithful
  -- complete-local presentation argument via Lemmas `15.39.x`, exactly as planned by Agent C.
  let _ := hflat
  let _ := hfsFiber
  -- TODO: reduce to complete local rings via `RingHom.formally_smooth_for_adic_tfae_completion_invariance`,
  -- choose the `15.39.3` presentation, kill the special-fiber kernel by `10.106.4`, identify
  -- `S ⊗[R] A ≃ B`, and finish with the derivation-correction argument from Theorem `15.40.1`.
  sorry

/- Domain-style sampling for Proposition 15.40.5:
- primary domain: local commutative algebra of Noetherian local ring maps and their closed fibers;
- sampled owner declarations:
  `Ideal.Fiber`,
  `Algebra.IsGeometricallyRegular`,
  `RingHom.formally_smooth_for_adic`,
  `RingHom.Flat`;
- best owner abstraction: the special fiber is canonically owned by
  `ClosedFiber = Ideal.Fiber (maximalIdeal A) B`, while the tensor product presentation
  `ResidueField A ⊗[A] B` is only a bridge view;
- primitive data: the local map `A → B`, its flatness, the closed fiber `ClosedFiber`, and the
  adic ideal `𝔪ClosedFiber = Ideal.map (algebraMap B ClosedFiber) (maximalIdeal B)`;
- derived API: geometric regularity and adic formal smoothness of `ClosedFiber`.

Source/core/bridge triage:
- `source-facing`: the three-way equivalence in Proposition 15.40.5;
- `core/canonical`: `Ideal.Fiber`, `Algebra.IsGeometricallyRegular`,
  `RingHom.formally_smooth_for_adic`, and `RingHom.Flat`;
- `bridge/view`: the tensor-product presentation `ResidueField A ⊗[A] B` of `ClosedFiber`.
-/
-- Proof sketch: `(1) ↔ (2)` is Theorem `15.40.1` applied to the special fiber `κ(A) ⊗[A] B`.
-- The implication `(3) → (2)` combines flatness from Lemma `15.40.3` with base change of adic
-- formal smoothness along `A → κ(A)` from Lemma `15.37.8`. For `(2) → (3)`, pass to completions,
-- choose Cohen presentations as in Lemma `15.39.3`, identify the completed base change with `B`,
-- and then run the same derivation-splitting argument as in the proof of Theorem `15.40.1`.
/-- Proposition 15.40.5: for a local homomorphism `A → B` of Noetherian local rings with special
fiber `ClosedFiber = Ideal.Fiber (maximalIdeal A) B`, canonically presented by `κ(A) ⊗[A] B`,
the following are equivalent: `A → B` is flat and `ClosedFiber` is geometrically regular over
`κ(A)`; `A → B` is flat and `κ(A) → ClosedFiber` is formally smooth for the adic topology defined
by `𝔪ClosedFiber = Ideal.map (algebraMap B ClosedFiber) (maximalIdeal B)`; and `A → B` is
formally smooth for the `maximalIdeal B`-adic topology. -/
@[stacks 07NQ]
theorem flat_geometricallyRegularSpecialFiber_formallySmooth_tfae :
    List.TFAE [
      (algebraMap A B).Flat ∧ Algebra.IsGeometricallyRegular (ResidueField A) ClosedFiber,
      (algebraMap A B).Flat ∧
        RingHom.formally_smooth_for_adic (algebraMap (ResidueField A) ClosedFiber) 𝔪ClosedFiber,
      (algebraMap A B).formally_smooth_for_adic (maximalIdeal B)
    ] := by
  -- Proof comment: separate the theorem into the closed-fiber equivalence, the easy base-change
  -- implication from source formal smoothness, and the remaining complete-local presentation step.
  tfae_have 1 ↔ 2 := by
    constructor
    · intro h1
      rcases h1 with ⟨hflat, hgeom⟩
      exact ⟨hflat, closedFiber_geometricallyRegular_iff_formally_smooth.mp hgeom⟩
    · intro h2
      rcases h2 with ⟨hflat, hfsFiber⟩
      exact ⟨hflat, closedFiber_geometricallyRegular_iff_formally_smooth.mpr hfsFiber⟩
  tfae_have 3 → 2 := by
    intro h3
    exact source_formally_smooth_implies_flat_and_closedFiber_formally_smooth
      (A := A) (B := B) h3
  tfae_have 2 → 3 := by
    intro h2
    rcases h2 with ⟨hflat, hfsFiber⟩
    exact formally_smooth_of_flat_and_closedFiber_formally_smooth
      (A := A) (B := B) hflat hfsFiber
  tfae_finish

end
