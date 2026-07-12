import Mathlib
import StacksProject_2024.Chap10.Definition_10_153_1
import StacksProject_2024.Chap10.Lemma_10_153_4
import StacksProject_2024.Chap10.Lemma_10_154_8

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-
Domain-style sampling for Lemma 15.105.23:
- primary domain: local commutative algebra of integral extensions of henselian and strictly
  henselian local rings, together with the induced residue-field extension;
- sampled owner declarations:
  `HenselianLocalRing`,
  `StrictHenselianLocalRing`,
  `finite_local_henselianLocalRing`,
  `algebraMap_isLocalHom_of_finite_local`,
  `IsLocalHom (algebraMap A B)`,
  `IsLocalRing.ResidueField.algebraOfIsIntegral`,
  `Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed`,
  `Algebra.IsAlgebraic.isSepClosed`;
- best owner abstraction: the integral-domain transfer statements here are `source-facing`, while
  the local/integral and residue-field-purely-inseparable steps are `bridge/view` results that
  should expose the canonical owner classes above rather than source-specific packages;
- primitive data: the integral `A`-algebra structure on the domain `B`;
- derived API: the henselian local structure on `B`, the locality of `A → B`, and the resulting
  purely inseparable residue-field extension.

Source/core/bridge triage:
- `source-facing`:
  `henselianLocalRing_of_henselianLocalRing_of_integral_domain`,
  `strictHenselianLocalRing_of_strictHenselianLocalRing_of_integral_domain`;
- `core/canonical`: `HenselianLocalRing`, `StrictHenselianLocalRing`, `IsLocalHom`,
  `finite_local_henselianLocalRing`, `algebraMap_isLocalHom_of_finite_local`,
  `IsPurelyInseparable`;
- `bridge/view`: the canonical residue-field algebraicity instance for local integral maps and the
  canonical bridge theorems
  `algebraMap_isLocalHom_of_isLocalRing_of_integral` and
  `residueField_isPurelyInseparable_of_isSepClosed_of_localHom_of_integral`, which expose the
  induced residue-field extension through the local-map interface and feed the source-facing
  corollaries below.
 -/

section LocalIntegralBridge

variable [IsLocalRing A] [IsLocalRing B] [Algebra.IsIntegral A B]

/-- An integral algebra map between local rings is a local ring homomorphism. -/
theorem algebraMap_isLocalHom_of_isLocalRing_of_integral :
    IsLocalHom (algebraMap A B) := by
  -- Contracting the maximal ideal of the local target stays maximal under integrality.
  have hcomap : Ideal.comap (algebraMap A B) (maximalIdeal B) = maximalIdeal A := by
    exact IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal B))
  -- The local-hom TFAE packages the inclusion of maximal ideals as the desired unit-reflection.
  have hle : maximalIdeal A ≤ Ideal.comap (algebraMap A B) (maximalIdeal B) := by
    simpa [hcomap]
  let l : List Prop :=
    [ IsLocalHom (algebraMap A B)
    , ⇑(algebraMap A B) '' ↑(maximalIdeal A) ⊆ ↑(maximalIdeal B)
    , Ideal.map (algebraMap A B) (maximalIdeal A) ≤ maximalIdeal B
    , maximalIdeal A ≤ Ideal.comap (algebraMap A B) (maximalIdeal B)
    , Ideal.comap (algebraMap A B) (maximalIdeal B) = maximalIdeal A
    ]
  have hl : l.TFAE := by
    simpa [l] using (IsLocalRing.local_hom_TFAE (f := algebraMap A B))
  have hiff :
      (maximalIdeal A ≤ Ideal.comap (algebraMap A B) (maximalIdeal B)) ↔
        IsLocalHom (algebraMap A B) := by
    exact List.TFAE.out hl 3 0 (by simp [l]) (by simp [l])
  exact hiff.mp hle

end LocalIntegralBridge

section ResidueFieldIntegrality

variable [IsLocalRing B] [Algebra.IsIntegral A B]

/-- Helper for Lemma 15.105.23: the target residue field stays integral over the source ring of
an integral extension. -/
lemma residueField_isIntegral_over_base_of_integral :
    Algebra.IsIntegral A (ResidueField B) := by
  -- The canonical quotient-to-residue-field map makes `κ(B)` integral over `B`.
  let _ : Algebra.IsIntegral B (ResidueField B) := inferInstance
  -- Then integrality descends along the tower `A → B → κ(B)`.
  exact Algebra.IsIntegral.trans B

end ResidueFieldIntegrality

section ResidueFieldBridge

variable [IsLocalRing A]
variable [IsLocalRing B] [IsLocalHom (algebraMap A B)] [Algebra.IsIntegral A B]

/-- Helper for Lemma 15.105.23: an integral local map induces an integral extension on residue
fields. -/
lemma residueField_isIntegral_over_baseResidueField_of_localHom_of_integral :
    Algebra.IsIntegral (ResidueField A) (ResidueField B) := by
  let ρ : ResidueField A →+* ResidueField B :=
    IsLocalRing.ResidueField.map (algebraMap A B)
  -- The composite `A → κ(A) → κ(B)` is the usual map `A → κ(B)`, so tower integrality descends
  -- from `A → κ(B)` to `κ(A) → κ(B)`.
  have hcomp : (ρ.comp (IsLocalRing.residue A)).IsIntegral := by
    have hbase : (algebraMap A (ResidueField B)).IsIntegral := by
      exact
        algebraMap_isIntegral_iff.mpr
          (residueField_isIntegral_over_base_of_integral (A := A) (B := B))
    simpa [ρ, RingHom.comp_assoc, IsLocalRing.ResidueField.map_residue] using hbase
  have hρ : ρ.IsIntegral :=
    RingHom.IsIntegral.tower_top (IsLocalRing.residue A) ρ hcomp
  exact algebraMap_isIntegral_iff.mp (by simpa [ρ] using hρ)

variable [IsSepClosed (ResidueField A)]

/-- The residue-field extension induced by an integral local homomorphism from a local ring with
separably closed residue field is purely inseparable. -/
theorem residueField_isPurelyInseparable_of_isSepClosed_of_localHom_of_integral :
    IsPurelyInseparable (ResidueField A) (ResidueField B) := by
  let _ : Algebra.IsIntegral (ResidueField A) (ResidueField B) :=
    residueField_isIntegral_over_baseResidueField_of_localHom_of_integral (A := A) (B := B)
  let _ : Algebra.IsAlgebraic (ResidueField A) (ResidueField B) := by
    rw [Algebra.isAlgebraic_iff_isIntegral]
    infer_instance
  -- Once the residue-field extension is algebraic, separable closure of `κ(A)` upgrades it to
  -- pure inseparability.
  exact
    Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed
      (F := ResidueField A) (E := ResidueField B)

end ResidueFieldBridge

section Henselian

variable [HenselianLocalRing A]

/-- Helper for Lemma 15.105.23: the finite `A`-subalgebra of `B` generated by a finset of
elements. -/
abbrev adjoin_stage (s : Finset B) : Subalgebra A B :=
  Algebra.adjoin A (s : Set B)

/-- Helper for Lemma 15.105.23: the carrier type of a finite adjoin stage. -/
abbrev adjoin_stage_type (s : Finset B) : Type v :=
  ↥(adjoin_stage (A := A) (B := B) s)

/-- Helper for Lemma 15.105.23: enlarging the finite set of generators enlarges the corresponding
adjoin stage. -/
lemma adjoin_stage_mono {s t : Finset B} (h : s ≤ t) :
    adjoin_stage (A := A) (B := B) s ≤ adjoin_stage (A := A) (B := B) t := by
  -- Monotonicity of `Algebra.adjoin` turns inclusion of generating sets into inclusion of stages.
  exact Algebra.adjoin_mono (show (s : Set B) ⊆ t from h)

/-- Helper for Lemma 15.105.23: the canonical inclusion between two finite adjoin stages. -/
abbrev adjoin_stage_map {s t : Finset B} (h : s ≤ t) :
    adjoin_stage_type (A := A) (B := B) s →ₐ[A] adjoin_stage_type (A := A) (B := B) t :=
  Subalgebra.inclusion (adjoin_stage_mono (A := A) (B := B) h)

/-- Helper for Lemma 15.105.23: the ring-hom version of the canonical inclusion between finite
adjoin stages. -/
abbrev adjoin_stage_ringHom {s t : Finset B} (h : s ≤ t) :
    adjoin_stage_type (A := A) (B := B) s →+* adjoin_stage_type (A := A) (B := B) t :=
  (adjoin_stage_map (A := A) (B := B) (s := s) (t := t) h).toRingHom

/-- Helper for Lemma 15.105.23: the directed-system transition maps between finite adjoin
stages. -/
abbrev adjoin_stage_transition {s t : Finset B} (h : s ≤ t) :
    adjoin_stage_type (A := A) (B := B) s →+* adjoin_stage_type (A := A) (B := B) t :=
  adjoin_stage_ringHom (A := A) (B := B) (s := s) (t := t) h

/-- Helper for Lemma 15.105.23: the direct limit of the finite adjoin stages. -/
abbrev adjoin_stage_colimit : Type v :=
  Ring.DirectLimit (adjoin_stage_type (A := A) (B := B))
    (fun s t h ↦ adjoin_stage_transition (A := A) (B := B) h)

/-- Helper for Lemma 15.105.23: the transition map for a fixed finite adjoin stage acts as the
identity on underlying elements. -/
lemma adjoin_stage_ringHom_id_apply (s : Finset B)
    (x : adjoin_stage_type (A := A) (B := B) s) :
    adjoin_stage_transition (A := A) (B := B) (s := s) (t := s) le_rfl x = x := by
  -- Both sides are the same subtype element because the inclusion map preserves the underlying
  -- element of `B`.
  rfl

/-- Helper for Lemma 15.105.23: the finite adjoin stages form a directed system under inclusion. -/
instance adjoin_stage_directedSystem :
    DirectedSystem (adjoin_stage_type (A := A) (B := B))
      (fun s t h ↦ adjoin_stage_transition (A := A) (B := B) h) :=
  -- TODO: prove the directed-system laws at the carrier level to avoid the deterministic kernel
  -- timeout caused by elaborating the inclusion maps through `Subalgebra.inclusion`.
  sorry

/-- Helper for Lemma 15.105.23: every finite adjoin stage is finite over the henselian base. -/
lemma adjoin_stage_moduleFinite [Algebra.IsIntegral A B] (s : Finset B) :
    Module.Finite A (adjoin_stage_type (A := A) (B := B) s) := by
  -- Each chosen generator is integral over `A`, so the finite adjoin is a finite `A`-algebra.
  exact
    Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet
      (fun x _ ↦ Algebra.IsIntegral.isIntegral x)

/-- Helper for Lemma 15.105.23: once a larger finite adjoin stage is local, the transition map
from any smaller stage is a local homomorphism. -/
lemma adjoin_stage_isLocalHom_of_le [Algebra.IsIntegral A B] (s t : Finset B) (h : s ≤ t)
    [IsLocalRing (adjoin_stage_type (A := A) (B := B) t)] :
    IsLocalHom (adjoin_stage_map (A := A) (B := B) h).toRingHom := by
  -- View the larger stage as an algebra over the smaller one via the inclusion map.
  letI : Algebra (adjoin_stage_type (A := A) (B := B) s)
      (adjoin_stage_type (A := A) (B := B) t) :=
    (adjoin_stage_map (A := A) (B := B) h).toAlgebra
  -- Finite generation over `A` restricts to finite generation over the smaller stage.
  let _ : Module.Finite A (adjoin_stage_type (A := A) (B := B) t) :=
    adjoin_stage_moduleFinite (A := A) (B := B) t
  let _ : Module.Finite (adjoin_stage_type (A := A) (B := B) s)
      (adjoin_stage_type (A := A) (B := B) t) :=
    Module.Finite.of_restrictScalars_finite A
      (adjoin_stage_type (A := A) (B := B) s)
      (adjoin_stage_type (A := A) (B := B) t)
  -- Lemma `10.153.4 (3)` then upgrades finite-over-local to a local homomorphism.
  simpa [adjoin_stage_map] using
    (algebraMap_isLocalHom_of_finite_local
      (R := adjoin_stage_type (A := A) (B := B) s)
      (S := adjoin_stage_type (A := A) (B := B) t))

/-- Helper for Lemma 15.105.23: a finite product of local rings is local once the total product is
a domain. -/
lemma pi_isLocalRing_of_isDomain {ι : Type*} [Fintype ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsLocalRing (R i)] [IsDomain ((i : ι) → R i)] :
    IsLocalRing ((i : ι) → R i) := by
  classical
  -- The ambient domain must contain at least one nontrivial factor.
  have h_exists_nontrivial : ∃ i, Nontrivial (R i) := by
    by_contra hnone
    have hsub : Subsingleton ((i : ι) → R i) := by
      refine ⟨?_⟩
      intro x y
      funext i
      have hsub_i : Subsingleton (R i) := by
        exact not_nontrivial_iff_subsingleton.mp (by
          intro hi
          exact hnone ⟨i, hi⟩)
      exact Subsingleton.elim _ _
    exact (not_nontrivial_iff_subsingleton.mpr hsub) inferInstance
  obtain ⟨i0, hi0⟩ := h_exists_nontrivial
  let _ : Nontrivial (R i0) := hi0
  -- Distinct nontrivial coordinates would produce zero divisors via `Pi.single`, so every other
  -- factor must collapse to a subsingleton ring.
  have hsub_factor : ∀ j : ι, j ≠ i0 → Subsingleton (R j) := by
    intro j hj
    have hnot_nontrivial : ¬ Nontrivial (R j) := by
      intro hj_nontrivial
      let _ : Nontrivial (R j) := hj_nontrivial
      have hmul :
          (Pi.single i0 (1 : R i0) : (i : ι) → R i) * Pi.single j (1 : R j) = 0 := by
        ext k
        by_cases hki : k = i0
        · subst hki
          simp [hj]
        · by_cases hkj : k = j
          · subst hkj
            simp [hki]
          · simp [hki, hkj]
      rcases mul_eq_zero.mp hmul with hleft | hright
      · have h10 : (1 : R i0) = 0 := by
          simpa [Pi.single_apply] using congrArg (fun f ↦ f i0) hleft
        exact one_ne_zero h10
      · have h10 : (1 : R j) = 0 := by
          simpa [Pi.single_apply, hj] using congrArg (fun f ↦ f j) hright
        exact one_ne_zero h10
    exact not_nontrivial_iff_subsingleton.mp hnot_nontrivial
  refine IsLocalRing.of_is_unit_or_is_unit_of_add_one ?_
  intro a b hab
  -- Evaluate the local-ring criterion at the unique nontrivial factor and rebuild a unit in the
  -- whole product, using subsingleton factors away from `i0`.
  have hi0_sum : a i0 + b i0 = 1 := by
    simpa using congrArg (fun f ↦ f i0) hab
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hi0_sum with ha0 | hb0
  · left
    exact Pi.isUnit_iff.mpr fun j ↦ by
      by_cases hj : j = i0
      · rcases hj with rfl
        simpa using ha0
      · let _ : Subsingleton (R j) := hsub_factor j hj
        simpa using isUnit_of_subsingleton (a j)
  · right
    exact Pi.isUnit_iff.mpr fun j ↦ by
      by_cases hj : j = i0
      · rcases hj with rfl
        simpa using hb0
      · let _ : Subsingleton (R j) := hsub_factor j hj
        simpa using isUnit_of_subsingleton (b j)

/-- Helper for Lemma 15.105.23: a finite domain algebra over a henselian local ring is local. -/
lemma isLocalRing_of_moduleFinite_of_henselianLocalRing_of_isDomain
    {S : Type v} [CommRing S] [Algebra A S] [Module.Finite A S] [IsDomain S] :
    IsLocalRing S := by
  -- Route correction: the source decomposition gives local henselian factors, so we transport the
  -- ambient domain structure to the total product instead of forcing each factor to be a domain.
  obtain ⟨ι, instFintype, A', instAComm, instAAlg, instAHenselian, instAFinite, ⟨e⟩⟩ :=
    exists_pi_algEquiv_henselianLocalRing_of_finite (R := A) (S := S)
  letI : Fintype ι := instFintype
  letI : ∀ i, CommRing (A' i) := instAComm
  letI : ∀ i, Algebra A (A' i) := instAAlg
  letI : ∀ i, HenselianLocalRing (A' i) := instAHenselian
  letI : ∀ i, Module.Finite A (A' i) := instAFinite
  letI : ∀ i, IsLocalRing (A' i) := fun i ↦ inferInstance
  let _ : IsDomain ((i : ι) → A' i) := Function.Injective.isDomain e.symm e.symm.injective
  let _ : IsLocalRing ((i : ι) → A' i) := pi_isLocalRing_of_isDomain (R := A')
  -- The decomposition equivalence identifies `S` with the local total product.
  exact e.symm.toRingEquiv.isLocalRing

/-- Helper for Lemma 15.105.23: each finite adjoin stage inside the ambient domain is henselian
local. -/
lemma adjoin_stage_henselianLocalRing [Algebra.IsIntegral A B] [IsDomain B] (s : Finset B) :
    HenselianLocalRing (adjoin_stage_type (A := A) (B := B) s) := by
  let _ : Module.Finite A (adjoin_stage_type (A := A) (B := B) s) :=
    adjoin_stage_moduleFinite (A := A) (B := B) s
  let _ : IsDomain (adjoin_stage_type (A := A) (B := B) s) :=
    Subalgebra.isDomain (adjoin_stage (A := A) (B := B) s)
  let _ : IsLocalRing (adjoin_stage_type (A := A) (B := B) s) :=
    isLocalRing_of_moduleFinite_of_henselianLocalRing_of_isDomain (A := A)
  -- After proving the stage is local, the finite henselian owner applies directly.
  exact finite_local_henselianLocalRing (R := A) (S := adjoin_stage_type (A := A) (B := B) s)

/-- Helper for Lemma 15.105.23: every element of `B` belongs to the finite adjoin stage generated
by its singleton. -/
lemma self_mem_adjoin_stage_singleton (b : B) :
    b ∈ adjoin_stage (A := A) (B := B) ({b} : Finset B) := by
  -- The singleton generator is contained in the adjoin by the defining universal property.
  exact Algebra.subset_adjoin (by simp)

/-- Helper for Lemma 15.105.23: the canonical inclusion of a finite adjoin stage into `B`. -/
abbrev adjoin_stage_subtype (s : Finset B) :
    adjoin_stage_type (A := A) (B := B) s →+* B :=
  (adjoin_stage (A := A) (B := B) s).val

/-- Helper for Lemma 15.105.23: the larger-stage inclusion into `B` composed with the transition
map is the original smaller-stage inclusion. -/
lemma adjoin_stage_subtype_comp_transition {s t : Finset B} (h : s ≤ t) :
    (adjoin_stage_subtype (A := A) (B := B) t).comp
        (adjoin_stage_transition (A := A) (B := B) (s := s) (t := t) h) =
      adjoin_stage_subtype (A := A) (B := B) s := by
  -- TODO: prove this by extensionality on subtype elements once the inclusion-composition normal
  -- form for `Subalgebra.inclusion` has been stabilized.
  sorry

/-- Helper for Lemma 15.105.23: the canonical map from the direct limit of the finite adjoin
stages to `B`. -/
noncomputable def adjoin_stage_directLimit_toRing :
    adjoin_stage_colimit (A := A) (B := B) →+* B :=
  -- TODO: define the colimit map using `Ring.DirectLimit.lift` once the directed-system instance
  -- and the stage-inclusion compatibility lemma above elaborate without timeout.
  sorry

/-- Helper for Lemma 15.105.23: the direct-limit comparison map evaluates a stage representative
to its underlying element in `B`. -/
lemma adjoin_stage_directLimit_toRing_of (s : Finset B)
    (x : adjoin_stage_type (A := A) (B := B) s) :
    adjoin_stage_directLimit_toRing (A := A) (B := B)
        (Ring.DirectLimit.of
          (adjoin_stage_type (A := A) (B := B))
          (fun s t h ↦ adjoin_stage_transition (A := A) (B := B) h)
          s x) =
      (x : B) :=
  -- TODO: once `adjoin_stage_directLimit_toRing` is defined, this is the `lift_of` computation
  -- rule for the stage representative `x`.
  sorry

/-- Helper for Lemma 15.105.23: `B` is the filtered colimit of its finite adjoin stages. -/
noncomputable def adjoin_stage_directLimit_equiv :
    adjoin_stage_colimit (A := A) (B := B) ≃+* B :=
  -- TODO: prove bijectivity of `adjoin_stage_directLimit_toRing` by singleton-stage surjectivity
  -- and a direct-limit kernel argument, then package it with `RingEquiv.ofBijective`.
  sorry

/-- Helper for Lemma 15.105.23: ring equivalences preserve henselian local rings. -/
lemma henselianLocalRing_of_equiv {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) [HenselianLocalRing R] :
    HenselianLocalRing S :=
  by
    letI : IsLocalRing S := e.isLocalRing
    have hR := ((HenselianLocalRing.TFAE R).out 0 2).mp
      (show HenselianLocalRing R from inferInstance)
    -- Transport clause `(3)` of the henselian TFAE across the ring equivalence.
    refine ((HenselianLocalRing.TFAE S).out 2 0).mp ?_
    intro K _ φ hφ f hf a₀ hroot hderiv
    let g : Polynomial R := f.map (e.symm : S →+* R)
    have hcomp : ((φ.comp (e : R →+* S)).comp (e.symm : S →+* R)) = φ := by
      -- The equivalence and its inverse cancel inside the composite ring hom.
      ext x
      simp
    have hφe : Function.Surjective (φ.comp (e : R →+* S)) := by
      -- Precomposing a surjective map with an equivalence stays surjective.
      intro y
      obtain ⟨x, rfl⟩ := hφ y
      exact ⟨e.symm x, by simp⟩
    have hg_monic : g.Monic := hf.map (e.symm : S →+* R)
    have hg_root : g.eval₂ (φ.comp (e : R →+* S)) a₀ = 0 := by
      -- Evaluating the pulled-back polynomial agrees with evaluating the original polynomial.
      rw [show g = f.map (e.symm : S →+* R) by rfl, Polynomial.eval₂_map, hcomp]
      exact hroot
    have hg_deriv : g.derivative.eval₂ (φ.comp (e : R →+* S)) a₀ = f.derivative.eval₂ φ a₀ := by
      -- The same compatibility holds after taking derivatives.
      rw [show g = f.map (e.symm : S →+* R) by rfl, Polynomial.derivative_map,
        Polynomial.eval₂_map, hcomp]
    have hg_simple : g.derivative.eval₂ (φ.comp (e : R →+* S)) a₀ ≠ 0 := by
      -- Nonvanishing is preserved by the derivative rewrite above.
      simpa [hg_deriv] using hderiv
    obtain ⟨a, ha_root, ha_map⟩ := hR (φ.comp (e : R →+* S)) hφe g hg_monic a₀ hg_root hg_simple
    refine ⟨e a, ?_, ?_⟩
    · -- Apply `e.symm` to reduce the root equation in `S` to the one already proved in `R`.
      have ha_eval₂ : Polynomial.eval₂ (e.symm : S →+* R) a f = 0 := by
        simpa [g, Polynomial.IsRoot, Polynomial.eval_map] using ha_root
      exact
        Polynomial.isRoot_of_eval₂_map_eq_zero
          (p := f) (f := (e.symm : S →+* R)) e.symm.injective
          (by simpa using ha_eval₂)
    · -- The field-valued point condition is the pushed-forward equality from the source clause.
      simpa using ha_map

-- Proof sketch: write `B` as a filtered colimit of finite `A`-subalgebras and apply the finite
-- henselian case to each stage. Since `B` is a domain, each finite local factor is forced to be
-- unique, and Lemma `10.154.8` upgrades the filtered colimit to a henselian local ring.
/-- Lemma 15.105.23 (1): if `A → B` is an integral ring map, `A` is henselian local, and `B` is a
domain, then `B` is a henselian local ring. -/
@[stacks 092X]
theorem henselianLocalRing_of_henselianLocalRing_of_integral_domain
    (A : Type u) [CommRing A] [Algebra A B] [HenselianLocalRing A] [Algebra.IsIntegral A B]
    [IsDomain B] : HenselianLocalRing B := by
  -- Route correction: we now follow the source proof literally by proving each finite adjoin
  -- stage is henselian local, then transporting the filtered-colimit henselian structure to `B`.
  let _ : ∀ s : Finset B, HenselianLocalRing (adjoin_stage_type (A := A) (B := B) s) := fun s ↦
    adjoin_stage_henselianLocalRing (A := A) (B := B) s
  let _ :
      ∀ s t (h : s ≤ t),
        IsLocalHom ((adjoin_stage_map (A := A) (B := B) (s := s) (t := t) h).toRingHom) :=
    fun s t h ↦ adjoin_stage_isLocalHom_of_le (A := A) (B := B) s t h
  let e := adjoin_stage_directLimit_equiv (A := A) (B := B)
  let _ :
      HenselianLocalRing
        (Ring.DirectLimit (adjoin_stage_type (A := A) (B := B))
          (fun s t h ↦
            adjoin_stage_transition (A := A) (B := B) (s := s) (t := t) h)) :=
    inferInstance
  -- The filtered-colimit henselian structure transfers to `B` through the comparison equivalence.
  exact henselianLocalRing_of_equiv e

/-- Lemma 15.105.23 (2): if `A → B` is an integral ring map, `A` is henselian local, and `B` is a
domain, then `A → B` is a local homomorphism. -/
@[stacks 092X]
theorem algebraMap_isLocalHom_of_henselianLocalRing_of_integral_domain [Algebra.IsIntegral A B]
    [IsDomain B] : IsLocalHom (algebraMap A B) := by
  let _ : HenselianLocalRing B :=
    henselianLocalRing_of_henselianLocalRing_of_integral_domain A
  exact algebraMap_isLocalHom_of_isLocalRing_of_integral

end Henselian

section StrictHenselian

variable [StrictHenselianLocalRing A]

/-- Lemma 15.105.23 (4): for an integral local homomorphism from a strictly henselian local ring,
the induced residue-field extension is purely inseparable. -/
@[stacks 092X]
theorem residueField_isPurelyInseparable_of_strictHenselianLocalRing_of_localHom_of_integral
    [IsLocalRing B] [IsLocalHom (algebraMap A B)] [Algebra.IsIntegral A B] :
    IsPurelyInseparable (ResidueField A) (ResidueField B) := by
  exact residueField_isPurelyInseparable_of_isSepClosed_of_localHom_of_integral

-- Proof sketch: once clause (1) gives that `B` is henselian local and clause (2) gives that
-- `A → B` is local, clause (4) upgrades the induced residue-field extension to a purely
-- inseparable extension. We then reuse the canonical algebraic-extension owner to conclude that
-- `ResidueField B` is separably closed.
/-- Lemma 15.105.23 (3): if `A` is strictly henselian in addition to the integral-domain
hypotheses, then `B` is strictly henselian. -/
@[stacks 092X]
theorem strictHenselianLocalRing_of_strictHenselianLocalRing_of_integral_domain
    (A : Type u) [CommRing A] [Algebra A B] [StrictHenselianLocalRing A] [Algebra.IsIntegral A B]
    [IsDomain B] :
    StrictHenselianLocalRing B := by
  let _ : HenselianLocalRing B :=
    henselianLocalRing_of_henselianLocalRing_of_integral_domain A
  let _ : IsLocalHom (algebraMap A B) :=
    algebraMap_isLocalHom_of_isLocalRing_of_integral
  let hPure : IsPurelyInseparable (ResidueField A) (ResidueField B) :=
    residueField_isPurelyInseparable_of_isSepClosed_of_localHom_of_integral
  let _ : Algebra.IsAlgebraic (ResidueField A) (ResidueField B) :=
    hPure.isAlgebraic
  let _ : IsSepClosed (ResidueField B) :=
    Algebra.IsAlgebraic.isSepClosed (F := ResidueField A) (E := ResidueField B)
  exact
    { toHenselianLocalRing := inferInstance
      toIsSepClosed := inferInstance }

end StrictHenselian

section IntegralClosure

variable {L : Type v} [Field L] [Algebra A L]

/-- The integral closure of a henselian local ring in a field is henselian local. -/
instance integralClosure_henselianLocalRing [HenselianLocalRing A] :
    HenselianLocalRing (integralClosure A L) := by
  let _ : Algebra.IsIntegral A (integralClosure A L) := IsIntegralClosure.isIntegral_algebra A L
  exact
    (henselianLocalRing_of_henselianLocalRing_of_integral_domain A :
      HenselianLocalRing (integralClosure A L))

/-- The integral closure of a strictly henselian local ring in a field is strictly henselian. -/
instance integralClosure_strictHenselianLocalRing [StrictHenselianLocalRing A] :
    StrictHenselianLocalRing (integralClosure A L) := by
  let _ : Algebra.IsIntegral A (integralClosure A L) := IsIntegralClosure.isIntegral_algebra A L
  exact
    (strictHenselianLocalRing_of_strictHenselianLocalRing_of_integral_domain A :
      StrictHenselianLocalRing (integralClosure A L))

end IntegralClosure

end
