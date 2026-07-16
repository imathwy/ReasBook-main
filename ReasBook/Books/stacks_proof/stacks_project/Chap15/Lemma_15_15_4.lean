import Mathlib
import Mathlib.Tactic.TFAE
import stacks_proof.stacks_project.Chap10.Lemma_10_5_3
import stacks_proof.stacks_project.Chap10.Definition_10_82_1
import stacks_proof.stacks_project.Chap10.Lemma_10_82_4
import stacks_proof.stacks_project.Chap10.Lemma_10_82_7
import stacks_proof.stacks_project.Chap10.Lemma_10_82_13
import stacks_proof.stacks_project.Chap15.Lemma_15_15_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x y

section

variable {R : Type u} [CommRing R]

open CategoryTheory
open Module

/-- Helper for Lemma 15.15.4: the canonical quotient sequence for a submodule is a complex. -/
lemma subtype_mkQ_comp_zero
    {M : Type v} [AddCommGroup M] [Module R M] (N : Submodule R M) :
    N.mkQ.comp N.subtype = 0 := by
  -- The canonical quotient sequence is exact, so its composite is zero.
  exact (LinearMap.exact_subtype_mkQ N).linearMap_comp_eq_zero

/-- Helper for Lemma 15.15.4: the range of an injective map from a finite projective module is
again finite projective. -/
lemma range_finite_projective_of_injective
    {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
    {M : Type w} [AddCommGroup M] [Module R M]
    (u : N →ₗ[R] M) (hu : Function.Injective u) :
    Module.Finite R u.range ∧ Module.Projective R u.range := by
  let e : N ≃ₗ[R] u.range := LinearEquiv.ofInjective u hu
  constructor
  · -- Transport finiteness across the canonical equivalence with the source.
    exact Module.Finite.equiv e
  · -- Projectivity is likewise invariant under linear equivalence.
    exact Module.Projective.of_equiv e

namespace LinearMap

/-- Helper for Lemma 15.15.4: the projective universal-injectivity criterion from Lemma `15.15.3`
specialized to the common universe used by the TFAE statement. -/
lemma universallyInjective_iff_injective_of_projective_of_proper_fg_ideal_annihilator_ne_bot_common_universe
    {N : Type (max u v w)} [AddCommGroup N] [Module R N] [Module.Projective R N]
    {M : Type (max u v w)} [AddCommGroup M] [Module R M] [Module.Projective R M]
    (hP : ∀ {I : Ideal R}, I.FG → I ≠ ⊤ → I.annihilator ≠ (⊥ : Ideal R))
    (u : N →ₗ[R] M) :
    UniversallyInjective.{u, max (max u v) w, max (max u v) w, u} u ↔ Function.Injective u := by
  -- Reuse Lemma `15.15.3` and normalize only the common-universe indices of the TFAE.
  simpa [max_assoc, max_left_comm, max_comm] using
    (LinearMap.universallyInjective_iff_injective_of_projective_of_proper_fg_ideal_annihilator_ne_bot
      (R := R) (N := N) (M := M) hP u)

end LinearMap

namespace Submodule

/-- Helper for Lemma 15.15.4: if both a submodule and its quotient are projective, then the
submodule is complemented. -/
lemma isComplemented_of_projective_quotient
    {M : Type v} [AddCommGroup M] [Module R M]
    (N : Submodule R M) [Module.Projective R N] [Module.Projective R (M ⧸ N)] :
    IsComplemented N := by
  -- Projectivity of the quotient supplies a section of the quotient map.
  obtain ⟨s, hs⟩ :=
    Module.projective_lifting_property N.mkQ (LinearMap.id : (M ⧸ N) →ₗ[R] (M ⧸ N))
      N.mkQ_surjective
  -- Exactness of the quotient sequence converts that section into a retraction of the inclusion.
  obtain ⟨p, hp⟩ :=
    ((Function.Exact.split_tfae (LinearMap.exact_subtype_mkQ N) Subtype.val_injective
      N.mkQ_surjective).out 0 1 rfl rfl).mp ⟨s, hs⟩
  have hp_proj : ∀ x : N, p x = x := by
    intro x
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hp x
  -- A projection onto `N` yields the complementary kernel.
  exact ⟨LinearMap.ker p, LinearMap.isCompl_of_proj hp_proj⟩

end Submodule

/-- Helper for Lemma 15.15.4: a complemented range of an injective map `R → R^n` yields a
splitting retraction. -/
lemma split_of_isComplemented_range_of_injective
    {N : Type v} [AddCommGroup N] [Module R N]
    {M : Type w} [AddCommGroup M] [Module R M]
    (u : N →ₗ[R] M) (hu : Function.Injective u)
    (hcompl : IsComplemented u.range) :
    ∃ v : M →ₗ[R] N, v.comp u = LinearMap.id := by
  rcases hcompl with ⟨q, hq⟩
  let e : N ≃ₗ[R] u.range := LinearEquiv.ofInjective u hu
  let proj : M →ₗ[R] u.range := u.range.linearProjOfIsCompl q hq
  -- Project onto the complemented range and transport back along the injective-range equivalence.
  refine ⟨e.symm.toLinearMap.comp proj, ?_⟩
  refine LinearMap.ext ?_
  intro x
  have hcomp := LinearMap.congr_fun (u.range.linearProjOfIsCompl_comp_subtype hq) (e x)
  -- On elements already in the range, the projection is the identity.
  change e.symm (proj (u x)) = x
  simpa [e, proj] using congrArg e.symm hcomp

/-- Helper for Lemma 15.15.4: a complemented range of an injective map `R → R^n` yields a
splitting retraction. -/
lemma split_of_isComplemented_range
    {n : ℕ} (u : R →ₗ[R] (Fin n → R)) (hu : Function.Injective u)
    (hcompl : IsComplemented u.range) :
    ∃ v : (Fin n → R) →ₗ[R] R, v.comp u = LinearMap.id := by
  -- Reuse the general complemented-range splitting criterion at this finite free target.
  exact split_of_isComplemented_range_of_injective (R := R) u hu hcompl

/-- Helper for Lemma 15.15.4: a linear map from `R^n` to `R` is determined by its values on the
standard basis vectors. -/
lemma fin_linearMap_eq_piEquiv_basis_values
    {n : ℕ} (g : (Fin n → R) →ₗ[R] R) :
    g = Module.piEquiv (Fin n) R R (fun i ↦ g ((Pi.single i (1 : R)) : Fin n → R)) := by
  refine LinearMap.ext ?_
  intro w
  have hw : w = ∑ i, w i • (Pi.single i (1 : R) : Fin n → R) := by
    -- Expand a vector in `R^n` against the standard basis.
    ext i
    simp [Pi.single_apply]
  calc
    g w = g (∑ i, w i • (Pi.single i (1 : R) : Fin n → R)) := by
      conv_lhs => rw [hw]
    _ = ∑ i, w i • g ((Pi.single i (1 : R)) : Fin n → R) := by
      simp [map_sum]
    _ = (Module.piEquiv (Fin n) R R (fun i ↦ g ((Pi.single i (1 : R)) : Fin n → R))) w := by
      -- `Module.piEquiv` records the same basis-value reconstruction formula.
      symm
      simpa using
        (Module.piEquiv_apply_apply (Fin n) R R
          (fun i ↦ g ((Pi.single i (1 : R)) : Fin n → R)) w)

/-- Helper for Lemma 15.15.4: if the target is flat, universal injectivity can be reindexed to a
different tensor-factor universe via the finitely generated-ideal criterion. -/
lemma universallyInjective_change_tensor_universe_of_flat
    {N : Type v} [AddCommGroup N] [Module R N]
    {M : Type w} [AddCommGroup M] [Module R M] [Module.Flat R M]
    (u : N →ₗ[R] M)
    (hu : LinearMap.UniversallyInjective.{u, v, w, x} u) :
    LinearMap.UniversallyInjective.{u, v, w, y} u := by
  -- Reindex universal injectivity through the quotient-map criterion of Lemma `10.82.13`.
  refine (LinearMap.universallyInjective_iff_injective_mod_finite_ideal u).2 ?_
  intro I hI
  -- The source-universe hypothesis already controls every finitely generated ideal quotient.
  exact (LinearMap.universallyInjective_iff_injective_mod_finite_ideal u).1 hu I hI

/-- Helper for Lemma 15.15.4: a linear equivalence is universally injective in every tensor
universe because its tensor extension is itself a linear equivalence. -/
lemma universallyInjective_of_linearEquiv
    {M : Type v} [AddCommGroup M] [Module R M]
    {M' : Type w} [AddCommGroup M'] [Module R M']
    (e : M ≃ₗ[R] M') :
    LinearMap.UniversallyInjective.{u, v, w, x} e.toLinearMap := by
  -- Tensoring a linear equivalence with any module remains injective.
  intro Q _ _
  simpa using (LinearEquiv.rTensor Q e).injective

/-- Helper for Lemma 15.15.4: the quotient row `u.range ↪ M → M ⧸ u.range` is short exact in
`ModuleCat`. -/
lemma shortExact_range_subtype_mkQ
    {N : Type v} [AddCommGroup N] [Module R N]
    {M : Type w} [AddCommGroup M] [Module R M]
    (u : N →ₗ[R] M) :
    let S : ShortComplex (ModuleCat.{w} R) :=
      ShortComplex.mk (ModuleCat.ofHom u.range.subtype) (ModuleCat.ofHom u.range.mkQ)
        (by
          ext x
          simp)
    S.ShortExact := by
  -- Package the standard exact sequence `0 → range(u) → M → M / range(u) → 0` once and for all.
  dsimp
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · simpa using LinearMap.exact_subtype_mkQ u.range
  · exact Submodule.injective_subtype u.range
  · simpa using Submodule.mkQ_surjective u.range

/-- Helper for Lemma 15.15.4: package the quotient row `0 → range(u) → M → M / range(u) → 0`
into a short complex whose objects all live in the common universe `max u w`. -/
abbrev range_quotient_shortComplex_ulift
    {N : Type v} [AddCommGroup N] [Module R N]
    {M : Type w} [AddCommGroup M] [Module R M]
    (u : N →ₗ[R] M) :
    ShortComplex (ModuleCat.{max u w} R) :=
  ShortComplex.moduleCatMk
    ((((ULift.moduleEquiv : ULift.{max u w, w} M ≃ₗ[R] M).symm.toLinearMap :
        M →ₗ[R] ULift.{max u w, w} M).comp
      (u.range.subtype.comp ((ULift.moduleEquiv : ULift.{max u w, w} u.range ≃ₗ[R] u.range).toLinearMap :
        ULift.{max u w, w} u.range →ₗ[R] u.range))))
    ((((ULift.moduleEquiv : ULift.{max u w, w} (M ⧸ u.range) ≃ₗ[R] M ⧸ u.range).symm.toLinearMap :
        (M ⧸ u.range) →ₗ[R] ULift.{max u w, w} (M ⧸ u.range)).comp
      (u.range.mkQ.comp ((ULift.moduleEquiv : ULift.{max u w, w} M ≃ₗ[R] M).toLinearMap :
        ULift.{max u w, w} M →ₗ[R] M))))
    <| by
      -- The composite is still zero after conjugating both maps by the chosen ULift equivalences.
      refine LinearMap.ext ?_
      intro x
      apply ULift.ext
      simpa using
        congr_fun (LinearMap.exact_subtype_mkQ u.range).linearMap_comp_eq_zero (ULift.down x)

/-- Helper for Lemma 15.15.4: the ULift-packaged quotient row is short exact. -/
lemma range_quotient_shortComplex_ulift_shortExact
    {N : Type v} [AddCommGroup N] [Module R N]
    {M : Type w} [AddCommGroup M] [Module R M]
    (u : N →ₗ[R] M) :
    (range_quotient_shortComplex_ulift (R := R) u).ShortExact := by
  -- Re-express exactness on the ULift row by descending to the usual `subtype`/`mkQ` row.
  have hExact :
      (range_quotient_shortComplex_ulift (R := R) u).Exact := by
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (range_quotient_shortComplex_ulift (R := R) u)]
    intro y
    constructor
    · intro hy
      have hyUp : ULift.up (u.range.mkQ y.down) = 0 := by
        simpa [range_quotient_shortComplex_ulift] using hy
      have hyDown : u.range.mkQ y.down = 0 := by
        simpa using congrArg ULift.down hyUp
      obtain ⟨x, hx⟩ := (LinearMap.exact_subtype_mkQ u.range y.down).1 hyDown
      -- Lift the standard exact witness back to the chosen common universe.
      refine ⟨⟨x⟩, ?_⟩
      change ULift.up (u.range.subtype x) = y
      apply ULift.ext
      simpa using hx
    · rintro ⟨x, rfl⟩
      -- The composite stays zero after conjugating both maps by `ULift.moduleEquiv`.
      change ULift.up (u.range.mkQ (u.range.subtype x.down)) = 0
      apply ULift.ext
      simpa using
        congr_fun (LinearMap.exact_subtype_mkQ u.range).linearMap_comp_eq_zero x.down
  -- The first map remains mono because `subtype` is injective.
  have hMono : Mono (range_quotient_shortComplex_ulift (R := R) u).f := by
    rw [ModuleCat.mono_iff_injective]
    intro x y hxy
    change ULift.up (u.range.subtype x.down) = ULift.up (u.range.subtype y.down) at hxy
    apply ULift.ext
    apply Submodule.injective_subtype u.range
    simpa using congrArg ULift.down hxy
  -- The second map remains epi because `mkQ` is surjective.
  have hEpi : Epi (range_quotient_shortComplex_ulift (R := R) u).g := by
    rw [ModuleCat.epi_iff_surjective]
    intro z
    obtain ⟨y, hy⟩ := u.range.mkQ_surjective z.down
    refine ⟨⟨y⟩, ?_⟩
    change ULift.up (u.range.mkQ y) = z
    apply ULift.ext
    simpa using hy
  exact ShortComplex.ShortExact.mk' hExact hMono hEpi

/-- Helper for Lemma 15.15.4: the ULift-packaged quotient row is universally exact as soon as the
range inclusion is universally injective. -/
lemma range_quotient_shortComplex_ulift_f_universallyInjective
    {N : Type v} [AddCommGroup N] [Module R N]
    {M : Type w} [AddCommGroup M] [Module R M] [Module.Flat R M]
    (u : N →ₗ[R] M)
    (hur : LinearMap.UniversallyInjective.{u, w, w, u} u.range.subtype) :
    LinearMap.UniversallyInjective.{u, max u w, max u w, max u w}
      (range_quotient_shortComplex_ulift (R := R) u).f.hom := by
  let eRange : ULift.{max u w, w} u.range ≃ₗ[R] u.range := ULift.moduleEquiv
  let eM : ULift.{max u w, w} M ≃ₗ[R] M := ULift.moduleEquiv
  -- Reindex the source universal-injectivity statement to the tensor universe used by the ULift row.
  have hSubtype :
      LinearMap.UniversallyInjective.{u, w, w, max u w} u.range.subtype :=
    universallyInjective_change_tensor_universe_of_flat
      (R := R) (u := u.range.subtype) hur
  -- The ULift conjugations are linear equivalences, hence universally injective.
  have hRange :
      LinearMap.UniversallyInjective.{u, max u w, w, max u w} eRange.toLinearMap :=
    universallyInjective_of_linearEquiv (R := R) eRange
  have hLiftedSubtype :
      LinearMap.UniversallyInjective.{u, max u w, w, max u w}
        (u.range.subtype.comp eRange.toLinearMap) :=
    LinearMap.universallyInjective_comp hSubtype hRange
  have hM :
      LinearMap.UniversallyInjective.{u, w, max u w, max u w} eM.symm.toLinearMap :=
    universallyInjective_of_linearEquiv (R := R) eM.symm
  -- Compose the reindexed range inclusion with the explicit ULift conjugations.
  simpa [range_quotient_shortComplex_ulift, eRange, eM, LinearMap.comp_assoc] using
    (LinearMap.universallyInjective_comp hM hLiftedSubtype)

/-- Helper for Lemma 15.15.4: a splitting of the ULift-packaged quotient row descends to a
section of the ordinary quotient map `u.range.mkQ`. -/
lemma descend_mkQ_section_of_range_quotient_shortComplex_ulift_splitting
    {N : Type v} [AddCommGroup N] [Module R N]
    {M : Type w} [AddCommGroup M] [Module R M]
    (u : N →ₗ[R] M)
    (spl : (range_quotient_shortComplex_ulift (R := R) u).Splitting) :
    ∃ σ : (M ⧸ u.range) →ₗ[R] M, u.range.mkQ.comp σ = LinearMap.id := by
  let eM : ULift.{max u w, w} M ≃ₗ[R] M := ULift.moduleEquiv
  let eQ : ULift.{max u w, w} (M ⧸ u.range) ≃ₗ[R] M ⧸ u.range := ULift.moduleEquiv
  let σ : (M ⧸ u.range) →ₗ[R] M :=
    eM.toLinearMap.comp (spl.s.hom.comp eQ.symm.toLinearMap)
  refine ⟨σ, LinearMap.ext ?_⟩
  intro x
  -- Rewrite the categorical section identity `spl.s ≫ g = 𝟙` in terms of the concrete quotient map.
  have hsHom :
      (range_quotient_shortComplex_ulift (R := R) u).g.hom.comp spl.s.hom = LinearMap.id := by
    simpa using congrArg ModuleCat.Hom.hom spl.s_g
  have hs :
      ((range_quotient_shortComplex_ulift (R := R) u).g.hom.comp spl.s.hom) (ULift.up x) =
        ULift.up x := by
    simpa using LinearMap.congr_fun hsHom (ULift.up x)
  have hs' : u.range.mkQ (σ x) = x := by
    simpa [range_quotient_shortComplex_ulift, σ, eM, eQ, LinearMap.comp_assoc] using
      congrArg ULift.down hs
  simpa [σ, LinearMap.comp_apply] using hs'

/-- Helper for Lemma 15.15.4: the ULift-packaged quotient row is universally exact as soon as the
range inclusion is universally injective. -/
lemma range_quotient_shortComplex_ulift_universallyExact
    {N : Type v} [AddCommGroup N] [Module R N]
    {M : Type w} [AddCommGroup M] [Module R M] [Module.Flat R M]
    (u : N →ₗ[R] M)
    (hur : LinearMap.UniversallyInjective.{u, w, w, u} u.range.subtype) :
    (range_quotient_shortComplex_ulift (R := R) u).UniversallyExact := by
  -- Package the owner row as universally exact by combining short exactness with the conjugated
  -- first-map universal injectivity.
  refine ⟨range_quotient_shortComplex_ulift_shortExact (R := R) u, ?_⟩
  exact range_quotient_shortComplex_ulift_f_universallyInjective (R := R) u hur

/-- Helper for Lemma 15.15.4: from universal exactness of the ULift quotient row, one obtains a
finitely presented flat quotient module. -/
lemma finitePresentation_and_flat_quotient_of_universallyInjective_range_subtype
    {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
    {M : Type w} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (u : N →ₗ[R] M) (hu : Function.Injective u)
    (hur : LinearMap.UniversallyInjective.{u, w, w, u} u.range.subtype) :
    Module.FinitePresentation R (M ⧸ u.range) ∧ Module.Flat R (M ⧸ u.range) := by
  letI : Module.Flat R M := Module.Flat.of_projective (R := R) (M := M)
  letI : Module.Flat R (ULift.{max u w, w} M) :=
    Module.Flat.of_linearEquiv
      (ULift.moduleEquiv : ULift.{max u w, w} M ≃ₗ[R] M)
  have hrange : Module.Finite R u.range ∧ Module.Projective R u.range :=
    range_finite_projective_of_injective (R := R) u hu
  letI : Module.Finite R u.range := hrange.1
  have hfgRangeTop : (⊤ : Submodule R u.range).FG := Module.Finite.fg_top
  have hfgRange : u.range.FG := (Submodule.fg_top u.range).mp hfgRangeTop
  have hfinitePresentation :
      Module.FinitePresentation R (M ⧸ u.range) := by
    letI : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
    -- The quotient map has finitely generated kernel because the range is a finite module.
    exact Module.finitePresentation_of_surjective u.range.mkQ u.range.mkQ_surjective <| by
      simpa [Submodule.ker_mkQ] using hfgRange
  have huniversallyExact :
      (range_quotient_shortComplex_ulift (R := R) u).UniversallyExact :=
    range_quotient_shortComplex_ulift_universallyExact (R := R) u hur
  have hflatMiddle :
      Module.Flat R ↑(range_quotient_shortComplex_ulift (R := R) u).X₂ := by
    change Module.Flat R (ULift.{max u w, w} M)
    infer_instance
  letI : Module.Flat R ↑(range_quotient_shortComplex_ulift (R := R) u).X₂ := hflatMiddle
  have hflatUp :
      Module.Flat R (ULift.{max u w, w} (M ⧸ u.range)) :=
    UniversallyExact.flat_X₃ huniversallyExact
  have hflat :
      Module.Flat R (M ⧸ u.range) :=
    Module.Flat.of_linearEquiv
      ((ULift.moduleEquiv :
        ULift.{max u w, w} (M ⧸ u.range) ≃ₗ[R] (M ⧸ u.range)).symm)
  exact ⟨hfinitePresentation, hflat⟩

/-- Helper for Lemma 15.15.4: from universal exactness of the ULift quotient row, one obtains a
section of the quotient map `u.range.mkQ`. -/
lemma exists_section_mkQ_of_range_subtype_universallyInjective_ulift
    {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
    {M : Type w} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (u : N →ₗ[R] M) (hu : Function.Injective u)
    (hur : LinearMap.UniversallyInjective.{u, w, w, u} u.range.subtype) :
    ∃ σ : (M ⧸ u.range) →ₗ[R] M, u.range.mkQ.comp σ = LinearMap.id := by
  have hquot :
      Module.FinitePresentation R (M ⧸ u.range) ∧ Module.Flat R (M ⧸ u.range) :=
    finitePresentation_and_flat_quotient_of_universallyInjective_range_subtype
      (R := R) (u := u) hu hur
  letI : Module.FinitePresentation R (M ⧸ u.range) := hquot.1
  letI : Module.Flat R (M ⧸ u.range) := hquot.2
  letI : Module.Projective R (M ⧸ u.range) := Module.Flat.projective_of_finitePresentation
  -- Once the quotient is projective, its defining surjection admits a section.
  exact Module.projective_lifting_property
    u.range.mkQ (LinearMap.id : (M ⧸ u.range) →ₗ[R] (M ⧸ u.range))
    u.range.mkQ_surjective

/-- Helper for Lemma 15.15.4: universal injectivity of the canonical range inclusion forces the
quotient by that range to be finite projective. -/
lemma projective_quotient_of_universallyInjective_range_subtype
    {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
    {M : Type w} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (u : N →ₗ[R] M) (hu : Function.Injective u)
    (hur : LinearMap.UniversallyInjective.{u, w, w, u} u.range.subtype) :
    Module.Finite R (M ⧸ u.range) ∧ Module.Projective R (M ⧸ u.range) := by
  have hquot :
      Module.FinitePresentation R (M ⧸ u.range) ∧ Module.Flat R (M ⧸ u.range) :=
    finitePresentation_and_flat_quotient_of_universallyInjective_range_subtype
      (R := R) (u := u) hu hur
  have hfinite : Module.Finite R (M ⧸ u.range) :=
    Module.Finite.of_surjective u.range.mkQ u.range.mkQ_surjective
  letI : Module.FinitePresentation R (M ⧸ u.range) := hquot.1
  letI : Module.Flat R (M ⧸ u.range) := hquot.2
  have hprojective : Module.Projective R (M ⧸ u.range) := Module.Flat.projective_of_finitePresentation
  exact ⟨hfinite, hprojective⟩

/-- Helper for Lemma 15.15.4: property `(P)` gives the exact public clause `(2)` after fixing the
carrier universes once and reindexing only the tensor-factor universe. -/
lemma proper_fg_ideal_annihilator_ne_bot_clause2_exact_bridge
    (hP : ∀ {I : Ideal R}, I.FG → I ≠ ⊤ → I.annihilator ≠ (⊥ : Ideal R)) :
    ∀ {N : Type (max u v w)} [AddCommGroup N] [Module R N] [Module.Projective R N]
      {M : Type (max u v w)} [AddCommGroup M] [Module R M] [Module.Projective R M]
      (u : N →ₗ[R] M), Function.Injective u →
        LinearMap.UniversallyInjective.{u, max u v w, max u v w, u} u := by
  intro N _ _ _ M _ _ _ u hu
  letI : Module.Flat R M := Module.Flat.of_projective (R := R) (M := M)
  have hiff :
      LinearMap.UniversallyInjective.{u, max u v w, max u v w, u} u ↔ Function.Injective u := by
    -- Pin the carrier universes on Lemma `15.15.3` before reading off the forward implication.
    simpa [max_assoc, max_left_comm, max_comm] using
      (LinearMap.universallyInjective_iff_injective_of_projective_of_proper_fg_ideal_annihilator_ne_bot.{u, max u v w, max u v w}
        (R := R) (N := N) (M := M) hP u)
  -- Reindex the tensor-factor universe from the owner theorem back to the explicit target clause.
  exact universallyInjective_change_tensor_universe_of_flat (R := R) (u := u) (hiff.2 hu)

/-- Helper for Lemma 15.15.4: clause `(2)` applied to the canonical range inclusion gives the
universally injective map needed for the quotient-projectivity step in `(2) → (3)`. -/
lemma universallyInjective_range_subtype_of_clause2
    (h2 :
      ∀ {N : Type (max u v w)} [AddCommGroup N] [Module R N] [Module.Projective R N]
        {M : Type (max u v w)} [AddCommGroup M] [Module R M] [Module.Projective R M]
        (u : N →ₗ[R] M), Function.Injective u →
          LinearMap.UniversallyInjective.{u, max u v w, max u v w, u} u) :
    ∀ {N : Type (max u v w)} [AddCommGroup N] [Module R N] [Module.Finite R N]
      [Module.Projective R N] {M : Type (max u v w)} [AddCommGroup M] [Module R M]
      [Module.Finite R M] [Module.Projective R M] (u : N →ₗ[R] M), Function.Injective u →
        LinearMap.UniversallyInjective.{u, max u v w, max u v w, u} u.range.subtype := by
  intro N _ _ _ _ M _ _ _ _ u hu
  have hrange : Module.Finite R u.range ∧ Module.Projective R u.range :=
    range_finite_projective_of_injective (R := R) u hu
  letI : Module.Projective R u.range := hrange.2
  letI : Module.Flat R M := Module.Flat.of_projective (R := R) (M := M)
  -- Apply clause `(2)` directly to the canonical range inclusion.
  exact
    universallyInjective_change_tensor_universe_of_flat
      (R := R) (u := u.range.subtype) (h2 u.range.subtype (Submodule.injective_subtype u.range))

/-- Helper for Lemma 15.15.4: the public clause `(2)` is equivalent to the exact owner clause with
the tensor-factor universe frozen once and for all. -/
lemma injective_projective_maps_universallyInjective_public_clause2_iff_exact_owner :
    (∀ {N : Type (max u v w)} [AddCommGroup N] [Module R N] [Module.Projective R N]
        {M : Type (max u v w)} [AddCommGroup M] [Module R M] [Module.Projective R M]
        (u : N →ₗ[R] M), Function.Injective u → u.UniversallyInjective) ↔
      (∀ {N : Type (max u v w)} [AddCommGroup N] [Module R N] [Module.Projective R N]
        {M : Type (max u v w)} [AddCommGroup M] [Module R M] [Module.Projective R M]
        (u : N →ₗ[R] M), Function.Injective u →
          LinearMap.UniversallyInjective.{u, max u v w, max u v w, u} u) := by
  constructor
  · intro h N _ _ _ M _ _ _ u hu
    letI : Module.Flat R M := Module.Flat.of_projective (R := R) (M := M)
    -- Freeze the tensor universe by reindexing the public universal-injectivity statement.
    exact universallyInjective_change_tensor_universe_of_flat (R := R) (u := u) (h u hu)
  · intro h N _ _ _ M _ _ _ u hu
    letI : Module.Flat R M := Module.Flat.of_projective (R := R) (M := M)
    -- The same reindexing moves the owner clause back to the public raw clause.
    exact universallyInjective_change_tensor_universe_of_flat (R := R) (u := u) (h u hu)

/-- Helper for Lemma 15.15.4: a splitting of the generator map forces the chosen generators to
span the unit ideal. -/
lemma span_eq_top_of_split_generator_map
    {n : ℕ} {u : R →ₗ[R] (Fin n → R)} (a : Fin n → R)
    (hu : ∀ r i, u r i = r * a i)
    (v : (Fin n → R) →ₗ[R] R) (hv : v.comp u = LinearMap.id) :
    Ideal.span (Set.range a) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have hv_apply : v (u 1) = 1 := by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hv (1 : R)
  have huv :
      v (u 1) = ∑ i, (u 1 i) * v ((Pi.single i (1 : R)) : Fin n → R) := by
    have hu_decomp : u 1 = ∑ i, (u 1 i) • (Pi.single i (1 : R) : Fin n → R) := by
      ext i
      simp [Pi.single_apply]
    calc
      v (u 1) = v (∑ i, (u 1 i) • (Pi.single i (1 : R) : Fin n → R)) := by
        simpa using congrArg v hu_decomp
      _ = ∑ i, (u 1 i) * v ((Pi.single i (1 : R)) : Fin n → R) := by
        simp [map_sum, smul_eq_mul]
  have hsum_mem :
      ∑ i, (u 1 i) * v ((Pi.single i (1 : R)) : Fin n → R) ∈ Ideal.span (Set.range a) := by
    refine Submodule.sum_mem _ ?_
    intro i
    have hai : a i ∈ Ideal.span (Set.range a) := Ideal.subset_span (Set.mem_range_self i)
    have hsmul : v ((Pi.single i (1 : R)) : Fin n → R) • a i ∈ Ideal.span (Set.range a) := by
      exact Submodule.smul_mem (Ideal.span (Set.range a)) _ hai
    have hu1 : u 1 i = a i := by
      simpa using hu 1 i
    simpa [hu1, smul_eq_mul, mul_comm] using hsmul
  have hmem : v (u 1) ∈ Ideal.span (Set.range a) := by
    rw [huv]
    exact hsum_mem
  simpa [hv_apply] using hmem

/-- Helper for Lemma 15.15.4: an element killing each chosen generator lies in the annihilator of
their span. -/
lemma kernel_element_mem_annihilator_of_generator_map
    {n : ℕ} (a : Fin n → R) {x : R}
    (hxkill : ∀ i, x * a i = 0) :
    x ∈ (Ideal.span (Set.range a)).annihilator := by
  rw [Submodule.mem_annihilator]
  intro y hy
  -- Check the annihilator condition first on the chosen generators, then extend by span
  -- induction.
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
  · intro z hz
    rcases hz with ⟨i, rfl⟩
    exact hxkill i
  · simp
  · intro y z _ _ hy hz
    have hy' : x * y = 0 := by
      simpa [smul_eq_mul] using hy
    have hz' : x * z = 0 := by
      simpa [smul_eq_mul] using hz
    simp [smul_eq_mul, mul_add, hy', hz']
  · intro c y _ hy
    have hy' : x * y = 0 := by
      simpa [smul_eq_mul] using hy
    simp [smul_eq_mul, mul_left_comm x c y, hy']

/-- Helper for Lemma 15.15.4: if every injective map `R → R^n` splits, then every proper finitely
generated ideal has nonzero annihilator. -/
lemma annihilator_ne_bot_of_split_injective_maps_to_fin
    (hsplit :
      ∀ n : ℕ, ∀ u : R →ₗ[R] (Fin n → R), Function.Injective u →
        ∃ v : (Fin n → R) →ₗ[R] R, v.comp u = LinearMap.id)
    {I : Ideal R} (hIfg : I.FG) (hIproper : I ≠ ⊤) :
    I.annihilator ≠ (⊥ : Ideal R) := by
  classical
  obtain ⟨s, hs⟩ := hIfg
  let a : Fin s.card → R := fun i ↦ (s.equivFin.symm i : R)
  have ha_span : Ideal.span (Set.range a) = I := by
    -- Rewrite the chosen finite generating set as a `Fin`-indexed family.
    rw [← hs]
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (s.equivFin.symm i).2
    · intro hx
      exact ⟨s.equivFin ⟨x, hx⟩, by simp [a]⟩
  let u : R →ₗ[R] (Fin s.card → R) :=
    { toFun := fun r i ↦ r * a i
      map_add' := by
        intro r t
        ext i
        simp [add_mul]
      map_smul' := by
        intro c r
        ext i
        simp [mul_assoc] }
  by_cases hu : Function.Injective u
  · obtain ⟨v, hv⟩ := hsplit s.card u hu
    have htop : Ideal.span (Set.range a) = ⊤ :=
      span_eq_top_of_split_generator_map (R := R) a (fun r i ↦ rfl) v hv
    exfalso
    exact hIproper <| by simpa [ha_span] using htop
  · have hne : ∃ r t : R, r ≠ t ∧ u r = u t := by
      by_contra hne
      apply hu
      intro r t hrt_eq
      by_contra hrt
      exact hne ⟨r, t, hrt, hrt_eq⟩
    rcases hne with ⟨r, t, hrt, hrt_eq⟩
    let x : R := r - t
    have hx_ne_zero : x ≠ 0 := by
      exact sub_ne_zero.mpr hrt
    have hxkill : ∀ i, x * a i = 0 := by
      intro i
      have hcoord := congrFun hrt_eq i
      change u r i = u t i at hcoord
      simpa [x, u, sub_mul] using sub_eq_zero.mpr hcoord
    have hx_ann_span : x ∈ (Ideal.span (Set.range a)).annihilator :=
      kernel_element_mem_annihilator_of_generator_map (R := R) a hxkill
    have hx_ann : x ∈ I.annihilator := by
      simpa [ha_span] using hx_ann_span
    intro hbot
    have hx_zero : x = 0 := by
      have hx_mem_bot : x ∈ (⊥ : Ideal R) := by
        simpa [hbot] using hx_ann
      simpa using hx_mem_bot
    exact hx_ne_zero hx_zero

namespace List

/-- Helper for Lemma 15.15.4: replace the second clause of a five-term `TFAE` by an equivalent
proposition while preserving the cyclic proof route. -/
lemma tfae_replace_second_of_iff {A B B' C D E : Prop}
    (hBB' : B ↔ B') (hT : List.TFAE [A, B', C, D, E]) :
    List.TFAE [A, B, C, D, E] := by
  -- Rebuild the same five-cycle after transporting only the second clause across `hBB'`.
  refine List.tfae_of_cycle ?_ ?_
  · -- The chain `A → B → C → D → E` is inherited from the owner chain after transporting `B`.
    simpa using
      And.intro
        (fun hA ↦ hBB'.mpr ((hT.out 0 1 (by simp) (by simp)).1 hA))
        (And.intro
          (fun hB ↦ (hT.out 1 2 (by simp) (by simp)).1 (hBB'.1 hB))
          (And.intro
            ((hT.out 2 3 (by simp) (by simp)).1)
            ((hT.out 3 4 (by simp) (by simp)).1)))
  · exact (hT.out 4 0 (by simp) (by simp)).1

end List

-- Proof sketch: `(1) → (2)` is Lemma `15.15.3`. The equivalence of `(3)` and `(4)` is the
-- standard splitting criterion for short exact sequences with finite projective end terms, where
-- clause `(4)` is phrased via the canonical owner property `IsComplemented` on submodules, and
-- `(2) → (3)` follows from the universal-exactness splitting criterion of Lemma `10.82.4`
-- applied to `0 → N → M → coker u → 0`. Clause `(5)` is the special case of `(4)` for
-- submodules of finite free modules of rank `n`, while `(5) → (1)` is proved by applying a
-- splitting obstruction to the map `R → Rⁿ` determined by generators of a proper finitely
-- generated ideal and extracting a nonzero annihilator element from its kernel.
/-- Helper for Lemma 15.15.4: the source-faithful five-cycle with clause `(2)` frozen in the exact
owner tensor-universe form. -/
theorem proper_fg_ideal_annihilator_ne_bot_tfae_fixed_tensor_clause2 :
    List.TFAE
      [ (∀ {I : Ideal R}, I.FG → I ≠ ⊤ → I.annihilator ≠ (⊥ : Ideal R)),
        (∀ {N : Type (max u v w)} [AddCommGroup N] [Module R N] [Module.Projective R N]
            {M : Type (max u v w)} [AddCommGroup M] [Module R M] [Module.Projective R M]
            (u : N →ₗ[R] M), Function.Injective u →
              LinearMap.UniversallyInjective.{u, max u v w, max u v w, u} u),
        (∀ {N : Type (max u v w)} [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
            {M : Type (max u v w)} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
            (u : N →ₗ[R] M), Function.Injective u →
              Module.Finite R (M ⧸ u.range) ∧ Module.Projective R (M ⧸ u.range)),
        (∀ {M : Type (max u v w)} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
            (N : Submodule R M) [Module.Finite R N] [Module.Projective R N],
            IsComplemented N),
        (∀ n : ℕ, ∀ u : R →ₗ[R] (Fin n → R), Function.Injective u →
            ∃ v : (Fin n → R) →ₗ[R] R, v.comp u = LinearMap.id) ] := by
  -- Route correction: prove the textbook cycle once for the frozen owner clause, then transport
  -- the public raw clause only after `List.TFAE` has been built.
  tfae_have 1 → 2 := by
    intro hP N _ _ _ M _ _ _ u hu
    have hiff :
        LinearMap.UniversallyInjective.{u, max u v w, max u v w, u} u ↔
          Function.Injective u := by
      -- Clause `(1)` is exactly the owner criterion from Lemma `15.15.3`.
      simpa [max_assoc, max_left_comm, max_comm] using
        (LinearMap.universallyInjective_iff_injective_of_projective_of_proper_fg_ideal_annihilator_ne_bot
          (R := R) (N := N) (M := M) hP u)
    exact hiff.2 hu
  tfae_have 2 → 3 := by
    intro h2 N _ _ _ _ M _ _ _ _ u hu
    -- Apply clause `(2)` to the canonical range inclusion, then read off projectivity of the
    -- quotient by that range.
    have hrange : Module.Finite R u.range ∧ Module.Projective R u.range :=
      range_finite_projective_of_injective (R := R) u hu
    letI : Module.Projective R u.range := hrange.2
    have hur :
        LinearMap.UniversallyInjective.{u, max u v w, max u v w, u} u.range.subtype :=
      h2 u.range.subtype (Submodule.injective_subtype u.range)
    exact
      projective_quotient_of_universallyInjective_range_subtype
        (R := R) (u := u) hu hur
  tfae_have 3 → 4 := by
    intro h3 M _ _ _ _ N _ _
    -- Clause `(3)` applied to the inclusion `N ↪ M` makes the quotient projective, so `N`
    -- admits a complementary summand.
    have hprojectiveQuotient : Module.Projective R (M ⧸ N) := by
      have hprojectiveRange : Module.Projective R (M ⧸ N.subtype.range) :=
        (h3 N.subtype (Submodule.injective_subtype N)).2
      letI : Module.Projective R (M ⧸ N.subtype.range) := hprojectiveRange
      exact Module.Projective.of_equiv
        (Submodule.quotEquivOfEq N.subtype.range N (Submodule.range_subtype N))
    letI : Module.Projective R (M ⧸ N) := hprojectiveQuotient
    exact Submodule.isComplemented_of_projective_quotient (R := R) N
  tfae_have 4 → 5 := by
    intro h4 n u hu
    let eR : ULift.{max u v w, u} R ≃ₗ[R] R := ULift.moduleEquiv
    let eM : ULift.{max u v w, u} (Fin n → R) ≃ₗ[R] (Fin n → R) := ULift.moduleEquiv
    let uLift : ULift.{max u v w, u} R →ₗ[R] ULift.{max u v w, u} (Fin n → R) :=
      eM.symm.toLinearMap.comp (u.comp eR.toLinearMap)
    have huLift : Function.Injective uLift :=
      eM.symm.injective.comp (hu.comp eR.injective)
    letI : Module.Finite R (ULift.{max u v w, u} R) := Module.Finite.equiv eR.symm
    letI : Module.Projective R (ULift.{max u v w, u} R) := Module.Projective.of_equiv eR.symm
    letI : Module.Finite R (ULift.{max u v w, u} (Fin n → R)) := Module.Finite.equiv eM.symm
    letI : Module.Projective R (ULift.{max u v w, u} (Fin n → R)) :=
      Module.Projective.of_equiv eM.symm
    have hrange :
        Module.Finite R uLift.range ∧ Module.Projective R uLift.range :=
      range_finite_projective_of_injective (R := R) uLift huLift
    letI : Module.Finite R uLift.range := hrange.1
    letI : Module.Projective R uLift.range := hrange.2
    have hcompl : IsComplemented uLift.range := h4 uLift.range
    obtain ⟨vLift, hvLift⟩ :=
      split_of_isComplemented_range_of_injective (R := R) uLift huLift hcompl
    let v : (Fin n → R) →ₗ[R] R := eR.toLinearMap.comp (vLift.comp eM.symm.toLinearMap)
    refine ⟨v, LinearMap.ext ?_⟩
    intro x
    -- Descend the splitting of the ULifted map back to the original `R → R^n`.
    simpa [v, uLift, eR, eM, LinearMap.comp_assoc] using
      congrArg ULift.down (LinearMap.congr_fun hvLift (ULift.up x))
  tfae_have 5 → 1 := by
    intro h5 I hIfg hIproper
    -- A non-split generator map would contradict clause `(5)`, producing a nonzero annihilator.
    exact annihilator_ne_bot_of_split_injective_maps_to_fin (R := R) h5 hIfg hIproper
  tfae_finish

/-- Lemma 15.15.4: for a commutative ring `R`, the following are equivalent: every proper finitely
generated ideal of `R` has nonzero annihilator, every injective map of projective `R`-modules is
universally injective, the cokernel of an injective map of finite projective `R`-modules is finite
projective, every finite projective submodule of a finite projective `R`-module is a direct
summand, and every injective map `R → R^{⊕ n}` is split. -/
@[stacks 05GQ]
theorem proper_fg_ideal_annihilator_ne_bot_tfae :
    List.TFAE
      [ (∀ {I : Ideal R}, I.FG → I ≠ ⊤ → I.annihilator ≠ (⊥ : Ideal R)),
        (∀ {N : Type (max u v w)} [AddCommGroup N] [Module R N] [Module.Projective R N]
            {M : Type (max u v w)} [AddCommGroup M] [Module R M] [Module.Projective R M]
            (u : N →ₗ[R] M), Function.Injective u → u.UniversallyInjective),
        (∀ {N : Type (max u v w)} [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
            {M : Type (max u v w)} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
            (u : N →ₗ[R] M), Function.Injective u →
              Module.Finite R (M ⧸ u.range) ∧ Module.Projective R (M ⧸ u.range)),
        (∀ {M : Type (max u v w)} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
            (N : Submodule R M) [Module.Finite R N] [Module.Projective R N],
            IsComplemented N),
        (∀ n : ℕ, ∀ u : R →ₗ[R] (Fin n → R), Function.Injective u →
            ∃ v : (Fin n → R) →ₗ[R] R, v.comp u = LinearMap.id) ] := by
  -- Route correction: keep the source proof on the frozen owner clause and transport the raw
  -- public clause only once at the `List.TFAE` level.
  -- Route correction: keep the source proof on the frozen owner clause and transport the raw
  -- public clause only once at the `List.TFAE` level.
  tfae_have 1 → 2 := by
    intro hP N _ _ _ M _ _ _ u hu
    letI : Module.Flat R M := Module.Flat.of_projective (R := R) (M := M)
    have hiff :
        LinearMap.UniversallyInjective.{u, max u v w, max u v w, u} u ↔
          Function.Injective u := by
      -- Read off the frozen owner criterion and reindex only the tensor universe.
      simpa [max_assoc, max_left_comm, max_comm] using
        (LinearMap.universallyInjective_iff_injective_of_projective_of_proper_fg_ideal_annihilator_ne_bot
          (R := R) (N := N) (M := M) hP u)
    exact universallyInjective_change_tensor_universe_of_flat (R := R) (u := u) (hiff.2 hu)
  tfae_have 2 → 3 := by
    intro h2 N _ _ _ _ M _ _ _ _ u hu
    have hrange : Module.Finite R u.range ∧ Module.Projective R u.range :=
      range_finite_projective_of_injective (R := R) u hu
    letI : Module.Projective R u.range := hrange.2
    letI : Module.Flat R M := Module.Flat.of_projective (R := R) (M := M)
    have hur :
        LinearMap.UniversallyInjective.{u, max u v w, max u v w, u} u.range.subtype :=
      universallyInjective_change_tensor_universe_of_flat
        (R := R) (u := u.range.subtype)
        (h2 u.range.subtype (Submodule.injective_subtype u.range))
    exact
      projective_quotient_of_universallyInjective_range_subtype
        (R := R) (u := u) hu hur
  tfae_have 3 → 4 := by
    intro h3 M _ _ _ _ N _ _
    -- Clause `(3)` applied to the inclusion `N ↪ M` makes the quotient projective, so `N`
    -- admits a complementary summand.
    have hprojectiveQuotient : Module.Projective R (M ⧸ N) := by
      have hprojectiveRange : Module.Projective R (M ⧸ N.subtype.range) :=
        (h3 N.subtype (Submodule.injective_subtype N)).2
      letI : Module.Projective R (M ⧸ N.subtype.range) := hprojectiveRange
      exact Module.Projective.of_equiv
        (Submodule.quotEquivOfEq N.subtype.range N (Submodule.range_subtype N))
    letI : Module.Projective R (M ⧸ N) := hprojectiveQuotient
    exact Submodule.isComplemented_of_projective_quotient (R := R) N
  tfae_have 4 → 5 := by
    intro h4 n u hu
    let eR : ULift.{max u v w, u} R ≃ₗ[R] R := ULift.moduleEquiv
    let eM : ULift.{max u v w, u} (Fin n → R) ≃ₗ[R] (Fin n → R) := ULift.moduleEquiv
    let uLift : ULift.{max u v w, u} R →ₗ[R] ULift.{max u v w, u} (Fin n → R) :=
      eM.symm.toLinearMap.comp (u.comp eR.toLinearMap)
    have huLift : Function.Injective uLift :=
      eM.symm.injective.comp (hu.comp eR.injective)
    letI : Module.Finite R (ULift.{max u v w, u} R) := Module.Finite.equiv eR.symm
    letI : Module.Projective R (ULift.{max u v w, u} R) := Module.Projective.of_equiv eR.symm
    letI : Module.Finite R (ULift.{max u v w, u} (Fin n → R)) := Module.Finite.equiv eM.symm
    letI : Module.Projective R (ULift.{max u v w, u} (Fin n → R)) :=
      Module.Projective.of_equiv eM.symm
    have hrange :
        Module.Finite R uLift.range ∧ Module.Projective R uLift.range :=
      range_finite_projective_of_injective (R := R) uLift huLift
    letI : Module.Finite R uLift.range := hrange.1
    letI : Module.Projective R uLift.range := hrange.2
    have hcompl : IsComplemented uLift.range := h4 uLift.range
    obtain ⟨vLift, hvLift⟩ :=
      split_of_isComplemented_range_of_injective (R := R) uLift huLift hcompl
    let v : (Fin n → R) →ₗ[R] R := eR.toLinearMap.comp (vLift.comp eM.symm.toLinearMap)
    refine ⟨v, LinearMap.ext ?_⟩
    intro x
    -- Descend the splitting of the ULifted map back to the original `R → R^n`.
    simpa [v, uLift, eR, eM, LinearMap.comp_assoc] using
      congrArg ULift.down (LinearMap.congr_fun hvLift (ULift.up x))
  tfae_have 5 → 1 := by
    intro h5 I hIfg hIproper
    -- A non-split generator map would contradict clause `(5)`, producing a nonzero annihilator.
    exact annihilator_ne_bot_of_split_injective_maps_to_fin (R := R) h5 hIfg hIproper
  tfae_finish

/-- Clause `(1) ↔ (2)` of Lemma `15.15.4`: over a commutative ring `R`, every proper finitely
generated ideal has nonzero annihilator if and only if every injective map of projective
`R`-modules is universally injective. -/
theorem proper_fg_ideal_annihilator_ne_bot_iff_injective_projective_maps_universallyInjective :
    (∀ {I : Ideal R}, I.FG → I ≠ ⊤ → I.annihilator ≠ (⊥ : Ideal R)) ↔
      (∀ {N : Type (max u v w)} [AddCommGroup N] [Module R N] [Module.Projective R N]
          {M : Type (max u v w)} [AddCommGroup M] [Module R M] [Module.Projective R M]
          (u : N →ₗ[R] M), Function.Injective u → u.UniversallyInjective) := by
  -- Route correction: extract clause `(1) ↔ (2_owner)` from the frozen theorem, then compose with
  -- the owner-to-public equivalence for clause `(2)`.
  constructor
  · intro hP N _ _ _ M _ _ _ u hu
    letI : Module.Flat R M := Module.Flat.of_projective (R := R) (M := M)
    have hiff :
        LinearMap.UniversallyInjective.{u, max u v w, max u v w, u} u ↔
          Function.Injective u := by
      simpa [max_assoc, max_left_comm, max_comm] using
        (LinearMap.universallyInjective_iff_injective_of_projective_of_proper_fg_ideal_annihilator_ne_bot
          (R := R) (N := N) (M := M) hP u)
    exact universallyInjective_change_tensor_universe_of_flat (R := R) (u := u) (hiff.2 hu)
  · intro h2 I hIfg hIproper
    have hsplit :
        ∀ n : ℕ, ∀ u : R →ₗ[R] (Fin n → R), Function.Injective u →
          ∃ v : (Fin n → R) →ₗ[R] R, v.comp u = LinearMap.id := by
      intro n u hu
      let eR : ULift.{max u v w, u} R ≃ₗ[R] R := ULift.moduleEquiv
      let eM : ULift.{max u v w, u} (Fin n → R) ≃ₗ[R] (Fin n → R) := ULift.moduleEquiv
      let uLift : ULift.{max u v w, u} R →ₗ[R] ULift.{max u v w, u} (Fin n → R) :=
        eM.symm.toLinearMap.comp (u.comp eR.toLinearMap)
      have huLift : Function.Injective uLift :=
        eM.symm.injective.comp (hu.comp eR.injective)
      letI : Module.Finite R (ULift.{max u v w, u} R) := Module.Finite.equiv eR.symm
      letI : Module.Projective R (ULift.{max u v w, u} R) := Module.Projective.of_equiv eR.symm
      letI : Module.Finite R (ULift.{max u v w, u} (Fin n → R)) := Module.Finite.equiv eM.symm
      letI : Module.Projective R (ULift.{max u v w, u} (Fin n → R)) :=
        Module.Projective.of_equiv eM.symm
      have hrange :
          Module.Finite R uLift.range ∧ Module.Projective R uLift.range :=
        range_finite_projective_of_injective (R := R) uLift huLift
      letI : Module.Finite R uLift.range := hrange.1
      letI : Module.Projective R uLift.range := hrange.2
      letI : Module.Flat R (ULift.{max u v w, u} (Fin n → R)) :=
        Module.Flat.of_projective (R := R) (M := ULift.{max u v w, u} (Fin n → R))
      have hur :
          LinearMap.UniversallyInjective.{u, max u v w, max u v w, u} uLift.range.subtype :=
        universallyInjective_change_tensor_universe_of_flat
          (R := R) (u := uLift.range.subtype)
          (h2 uLift.range.subtype (Submodule.injective_subtype uLift.range))
      have hquot :
          Module.Finite R (ULift.{max u v w, u} (Fin n → R) ⧸ uLift.range) ∧
            Module.Projective R (ULift.{max u v w, u} (Fin n → R) ⧸ uLift.range) :=
        projective_quotient_of_universallyInjective_range_subtype
          (R := R) (u := uLift) huLift hur
      letI : Module.Projective R (ULift.{max u v w, u} (Fin n → R) ⧸ uLift.range) := hquot.2
      have hcompl : IsComplemented uLift.range :=
        Submodule.isComplemented_of_projective_quotient (R := R) uLift.range
      obtain ⟨vLift, hvLift⟩ :=
        split_of_isComplemented_range_of_injective (R := R) uLift huLift hcompl
      let v : (Fin n → R) →ₗ[R] R := eR.toLinearMap.comp (vLift.comp eM.symm.toLinearMap)
      refine ⟨v, LinearMap.ext ?_⟩
      intro x
      simpa [v, uLift, eR, eM, LinearMap.comp_assoc] using
        congrArg ULift.down (LinearMap.congr_fun hvLift (ULift.up x))
    exact annihilator_ne_bot_of_split_injective_maps_to_fin (R := R) hsplit hIfg hIproper

end
