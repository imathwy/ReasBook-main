import Mathlib
import StacksProject_2024.Chap10.Lemma_10_39_12
import StacksProject_2024.Chap10.Lemma_10_5_3
import StacksProject_2024.Chap10.Lemma_10_78_6
import StacksProject_2024.Chap15.Lemma_15_91_4
import StacksProject_2024.Chap15.Lemma_15_91_18

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

noncomputable section

universe u w

section

variable {R : Type u} [CommRing R]
variable {R' : Type u} [CommRing R'] [Algebra R R']
variable {M : Type w} [AddCommMonoid M] [Module R M]
local notation "Away" => LocalizedModule.Away

/-- Helper for Lemma 15.91.19: localizing submodules is monotone, with the module allowed to live
in an arbitrary universe. -/
lemma localized_submodule_mono_general
    (S : Submonoid R) {Q : Type w} [AddCommMonoid Q] [Module R Q]
    {P Q' : Submodule R Q} (hPQ : P ≤ Q') :
    P.localized S ≤ Q'.localized S := by
  intro x hx
  -- Reuse the same numerator and denominator witness after enlarging the source submodule.
  change x ∈ Submodule.localized₀ S (LocalizedModule.mkLinearMap S Q) Q'
  change x ∈ Submodule.localized₀ S (LocalizedModule.mkLinearMap S Q) P at hx
  rcases hx with ⟨m, hm, s, rfl⟩
  exact ⟨m, hPQ hm, s, rfl⟩

/-- Helper for Lemma 15.91.19: finite generation of the tensor base change is already witnessed by
some finitely generated submodule of the original module, in arbitrary module universe. -/
lemma exists_fg_submodule_baseChange_eq_top_of_moduleFinite_general
    {Q : Type w} [AddCommMonoid Q] [Module R Q]
    (hfinite : Module.Finite R' (R' ⊗[R] Q)) :
    ∃ P : Submodule R Q, P.FG ∧ P.baseChange R' = ⊤ := by
  classical
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R' (R' ⊗[R] Q)
  have hdecomp :
      ∀ i : Fin n, ∃ k : ℕ, ∃ a : Fin k → R', ∃ m : Fin k → Q,
        π (Pi.basisFun R' (Fin n) i) = ∑ j, a j ⊗ₜ[R] m j := by
    intro i
    obtain ⟨k, a, m, hm⟩ := TensorProduct.exists_sum_tmul_eq (π (Pi.basisFun R' (Fin n) i))
    exact ⟨k, a, m, hm⟩
  choose k a m hm using hdecomp
  let v : (Σ i : Fin n, Fin (k i)) → Q := fun ij ↦ m ij.1 ij.2
  let P : Submodule R Q := Submodule.span R (Set.range v)
  refine ⟨P, Submodule.fg_span (Set.finite_range v), ?_⟩
  apply top_unique
  intro z hz
  rcases hπ z with ⟨y, rfl⟩
  have hy : y = ∑ i, Pi.single i (y i) := by
    ext i
    simp
  -- Expand the tensor element along the standard basis of the chosen finite free cover.
  rw [hy, map_sum]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  have hsingle : Pi.single i (y i) = y i • Pi.basisFun R' (Fin n) i := by
    ext j
    by_cases h : j = i
    · subst h
      simp [Pi.basisFun]
    · simp [Pi.basisFun, h]
  rw [hsingle, LinearMap.map_smul]
  apply Submodule.smul_mem
  rw [hm i]
  refine Submodule.sum_mem _ fun j _ ↦ ?_
  rw [Submodule.baseChange_eq_span]
  have hmP : m i j ∈ P := by
    exact Submodule.subset_span ⟨⟨i, j⟩, rfl⟩
  have hgen :
      (1 : R') ⊗ₜ[R] m i j ∈
        Submodule.span R' ((fun x ↦ (1 : R') ⊗ₜ[R] x) '' (P : Set Q)) := by
    exact Submodule.subset_span ⟨m i j, hmP, rfl⟩
  have hsmul :
      a i j • ((1 : R') ⊗ₜ[R] m i j) ∈
        Submodule.span R' ((fun x ↦ (1 : R') ⊗ₜ[R] x) '' (P : Set Q)) :=
    Submodule.smul_mem _ _ hgen
  -- Each summand is a scalar multiple of a denominator-`1` tensor coming from `P`.
  simpa [TensorProduct.smul_tmul', one_smul] using hsmul

/-- Helper for Lemma 15.91.19: finite generation after localizing away from `f` is already
witnessed by a finitely generated submodule of the original module, in arbitrary module universe. -/
lemma exists_fg_submodule_localized_eq_top_of_moduleFinite_general
    (f : R) {Q : Type w} [AddCommMonoid Q] [Module R Q]
    (hfinite : Module.Finite (Localization.Away f) (Away f Q)) :
    ∃ P : Submodule R Q, P.FG ∧ Submodule.localized (p := Submonoid.powers f) P = ⊤ := by
  classical
  let S : Submonoid R := Submonoid.powers f
  let mkQ : Q →ₗ[R] Away f Q := LocalizedModule.mkLinearMap S Q
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' (Localization.Away f) (Away f Q)
  have hrepr :
      ∀ i : Fin n, ∃ q : Q, ∃ s : S,
        IsLocalizedModule.mk' mkQ q s = π (Pi.basisFun (Localization.Away f) (Fin n) i) := by
    intro i
    rcases IsLocalizedModule.mk'_surjective S mkQ
        (π (Pi.basisFun (Localization.Away f) (Fin n) i)) with ⟨⟨q, s⟩, hs⟩
    exact ⟨q, s, hs⟩
  choose q s hs using hrepr
  let P : Submodule R Q := Submodule.span R (Set.range q)
  refine ⟨P, Submodule.fg_span (Set.finite_range q), ?_⟩
  apply top_unique
  intro z hz
  rcases hπ z with ⟨y, rfl⟩
  have hy : y = ∑ i, Pi.single i (y i) := by
    ext i
    simp
  -- Expand a localized vector along the standard basis of the chosen finite free cover.
  rw [hy, map_sum]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  have hsingle :
      Pi.single i (y i) = y i • Pi.basisFun (Localization.Away f) (Fin n) i := by
    ext j
    by_cases h : j = i
    · subst h
      simp [Pi.basisFun]
    · simp [Pi.basisFun, h]
  rw [hsingle, LinearMap.map_smul]
  apply Submodule.smul_mem
  -- Each basis generator already lies in the localized copy of the span of its chosen numerator.
  exact ⟨q i, Submodule.subset_span ⟨i, rfl⟩, s i, hs i⟩

/-- Helper for Lemma 15.91.19: if a submodule becomes all of the tensor base change, then the
tensor base change of the quotient is trivial, in arbitrary module universe. -/
lemma tensor_quotient_subsingleton_of_baseChange_eq_top_general
    {Q : Type w} [AddCommGroup Q] [Module R Q]
    (P : Submodule R Q) (hP : P.baseChange R' = ⊤) :
    Subsingleton (R' ⊗[R] (Q ⧸ P)) := by
  let ψ : R' ⊗[R] P →ₗ[R'] R' ⊗[R] Q := P.subtype.baseChange R'
  let φ : R' ⊗[R] Q →ₗ[R'] R' ⊗[R] (Q ⧸ P) := P.mkQ.baseChange R'
  have hψsurj : Function.Surjective ψ := by
    -- The equality `P.baseChange R' = ⊤` is exactly surjectivity of the tensorized subtype map.
    rw [← LinearMap.range_eq_top]
    simpa [ψ, Submodule.baseChange] using hP
  have hExact : Function.Exact ψ φ := by
    -- Right exactness of tensor product transports the standard quotient sequence.
    simpa [ψ, φ, LinearMap.baseChange_eq_ltensor] using
      (lTensor_exact R' (LinearMap.exact_subtype_mkQ P) P.mkQ_surjective)
  have hsurj : Function.Surjective φ := by
    -- Tensoring preserves surjectivity of the quotient map.
    simpa [φ, LinearMap.baseChange_eq_ltensor] using
      (LinearMap.lTensor_surjective R' P.mkQ_surjective)
  refine (subsingleton_iff_forall_eq 0).2 fun z ↦ ?_
  rcases hsurj z with ⟨y, rfl⟩
  rcases hψsurj y with ⟨x, hx⟩
  -- Every quotient tensor is already in the image of the tensorized submodule, hence vanishes.
  exact (hExact y).2 ⟨x, hx⟩

/-- Helper for Lemma 15.91.19: if a submodule becomes all of the localization away from `f`, then
the localization of the quotient is trivial, in arbitrary module universe. -/
lemma localized_quotient_subsingleton_of_localized_eq_top_general
    (f : R) {Q : Type w} [AddCommGroup Q] [Module R Q]
    (P : Submodule R Q)
    (hlocalized : Submodule.localized (p := Submonoid.powers f) P = ⊤) :
    Subsingleton (Away f (Q ⧸ P)) := by
  let e :
      (Away f Q ⧸ Submodule.localized (p := Submonoid.powers f) P) ≃ₗ[
        Localization.Away f] Away f (Q ⧸ P) :=
    localizedQuotientEquiv (Submonoid.powers f) P
  have hquot :
      Subsingleton (Away f Q ⧸ Submodule.localized (p := Submonoid.powers f) P) := by
    -- Quotienting by `⊤` makes the localized quotient trivial.
    rw [hlocalized]
    infer_instance
  letI :
      Subsingleton (Away f Q ⧸ Submodule.localized (p := Submonoid.powers f) P) := hquot
  exact e.symm.toEquiv.subsingleton

/-- Helper for Lemma 15.91.19: finite generation descends from the tensor branch and the
localization branch without requiring the module to live in the same universe as `R`. -/
lemma moduleFinite_iff_finite_tensor_and_localizedAway_of_quotientMapBijective_universe
    (f : R)
    (hquot : ∀ n : ℕ+, Function.Bijective
      (principalPowerIdealImageQuotientMap (algebraMap R R') f n)) :
    Module.Finite R M ↔
      Module.Finite R' (R' ⊗[R] M) ∧
        Module.Finite (Localization.Away f) (Away f M) := by
  sorry

/-- Helper for Lemma 15.91.19: tensoring the kernel sequence with `R'` keeps it short exact
because the cokernel `M` is flat. This makes the tensorized kernel finite once the tensorized
cokernel is finitely presented. -/
lemma finite_tensor_kernel_of_surjective_free_cover
    [AddCommGroup M]
    {n : ℕ} (π : (Fin n → R) →ₗ[R] M) (hπ : Function.Surjective π)
    (hflat : Module.Flat R M)
    (hfiniteProjective : Module.FiniteProjective R' (R' ⊗[R] M)) :
    Module.Finite R' (R' ⊗[R] LinearMap.ker π) := by
  sorry

/-- Helper for Lemma 15.91.19: tensoring the kernel sequence with `R_f` keeps it short exact
because the cokernel `M` is flat. This makes the localized kernel finite once the localized
cokernel is finitely presented. -/
lemma finite_localizedAway_kernel_of_surjective_free_cover
    [AddCommGroup M]
    (f : R)
    {n : ℕ} (π : (Fin n → R) →ₗ[R] M) (hπ : Function.Surjective π)
    (hflat : Module.Flat R M)
    (hfiniteProjective : Module.FiniteProjective (Localization.Away f) (Away f M)) :
    Module.Finite (Localization.Away f) (Away f (LinearMap.ker π)) := by
  sorry

/-- Helper for Lemma 15.91.19: a surjective finite free cover with finite kernel is a finite
presentation. -/
lemma finitePresentation_of_surjective_free_cover_of_finite_kernel
    [AddCommGroup M]
    {n : ℕ} (π : (Fin n → R) →ₗ[R] M) (hπ : Function.Surjective π)
    (hker : Module.Finite R (LinearMap.ker π)) :
    Module.FinitePresentation R M := by
  sorry

/-- Helper for Lemma 15.91.19: finite projectivity localizes away from `f`. -/
lemma finiteProjective_localizedAway_of_finiteProjective
    (f : R)
    (hfiniteProjective : Module.FiniteProjective R M) :
    Module.FiniteProjective (Localization.Away f) (Away f M) := by
  rcases hfiniteProjective with ⟨hfinite, hprojective⟩
  letI : Module.Finite R M := hfinite
  letI : Module.Projective R M := hprojective
  have hfiniteTensor :
      Module.Finite (Localization.Away f) ((Localization.Away f) ⊗[R] M) := by
    -- Finite generation survives localization.
    exact Module.Finite.base_change (R := R) (A := Localization.Away f) (M := M)
  have hprojectiveTensor :
      Module.Projective (Localization.Away f) ((Localization.Away f) ⊗[R] M) := by
    -- Projectivity also survives base change.
    exact Module.Projective.tensorProduct
  letI :
      Module.Finite (Localization.Away f) ((Localization.Away f) ⊗[R] M) :=
    hfiniteTensor
  letI :
      Module.Projective (Localization.Away f) ((Localization.Away f) ⊗[R] M) :=
    hprojectiveTensor
  -- Transport the tensor-side statement to the canonical localized module.
  exact
    ⟨Module.Finite.equiv (LocalizedModule.equivTensorProduct (Submonoid.powers f) M).symm,
      Module.Projective.of_equiv
        (LocalizedModule.equivTensorProduct (Submonoid.powers f) M).symm⟩

/- Domain-style sampling:
* primary domain: Beauville-Laszlo descent for finite projective modules over commutative rings.
* sampled owner declarations:
  `IsBeauvilleLaszloGlueingPairAlong`,
  `Module.FiniteProjective`,
  `flat_iff_flat_tensor_and_localizedAway_of_beauvilleLaszloGlueingPair`,
  `moduleFinite_iff_finite_tensor_and_localizedAway_of_quotientMapBijective`.
* owner abstraction: the source-facing Beauville-Laszlo descent statement should use the chapter
  owner predicate `Module.FiniteProjective`, while the glueing hypothesis is still owned by
  `IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f`.
* primitive data: the rings `R`, `R'`, the algebra map `R → R'`, the element `f`, and the
  module `M`.
* derived API: the finite-projective comparisons for the canonical base change `R' ⊗[R] M` and
  localization `Away f M`.
*
* Source/core/bridge triage:
  `source-facing`: the Beauville-Laszlo finite-projective criterion below;
  `core/canonical`: `IsBeauvilleLaszloGlueingPairAlong` and `Module.FiniteProjective`;
  `bridge/view`: the canonical base-change module `R' ⊗[R] M` and localization `Away f M`.
-/

-- Proof sketch: for the forward implication, finite projective modules remain finite projective
-- after scalar extension to `R'` and localization away from `f`. For the converse, use Lemma
-- `15.91.18` to descend flatness from `R' ⊗[R] M` and `M_f`, use Lemma `15.91.4` to descend
-- finite generation, and then package the result in the canonical owner predicate
-- `Module.FiniteProjective`.
/-- Lemma 15.91.19: for a Beauville-Laszlo glueing pair `(R → R', f)`, an `R`-module `M` is
finite projective if and only if its base change `R' ⊗[R] M` is finite and projective over `R'`
and its localization `LocalizedModule.Away f M` is finite and projective over
`Localization.Away f`. -/
lemma finiteProjective_iff_tensor_and_localizedAway_finiteProjective_of_beauvilleLaszloGlueingPair
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    Module.FiniteProjective R M ↔
      Module.FiniteProjective R' (R' ⊗[R] M) ∧
        Module.FiniteProjective (Localization.Away f) (Away f M) := by
  constructor
  · intro hfiniteProjective
    rcases hfiniteProjective with ⟨hfinite, hprojective⟩
    letI : Module.Finite R M := hfinite
    letI : Module.Projective R M := hprojective
    constructor
    · -- Finite projective modules remain finite projective after base change to `R'`.
      exact
        ⟨Module.Finite.base_change (R := R) (A := R') (M := M),
          Module.Projective.tensorProduct⟩
    · -- Localization is the other source branch in the Beauville-Laszlo criterion.
      exact finiteProjective_localizedAway_of_finiteProjective
        (R := R) (M := M) f ⟨hfinite, hprojective⟩
  · rintro ⟨hfiniteProjectiveTensor, hfiniteProjectiveAway⟩
    letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
    have hflatTensor : Module.Flat R' (R' ⊗[R] M) := by
      -- Projective modules are flat on the tensor branch.
      letI : Module.Projective R' (R' ⊗[R] M) := hfiniteProjectiveTensor.2
      exact Module.Flat.of_projective
    have hflatAway : Module.Flat (Localization.Away f) (Away f M) := by
      -- The same holds for the localization branch.
      letI : Module.Projective (Localization.Away f) (Away f M) := hfiniteProjectiveAway.2
      exact Module.Flat.of_projective
    have hflat : Module.Flat R M := by
      -- Lemma `15.91.18` descends flatness from the two comparison modules.
      exact
        (flat_iff_flat_tensor_and_localizedAway_of_beauvilleLaszloGlueingPair
          (R := R) (R' := R') (M := M) f hpair).2
          ⟨hflatTensor, hflatAway⟩
    have hfinite : Module.Finite R M := by
      -- Use the local universe-polymorphic finite-descent bridge.
      exact
        (moduleFinite_iff_finite_tensor_and_localizedAway_of_quotientMapBijective_universe
          (R := R) (R' := R') (M := M) f hpair.quotientMapBijective).2
          ⟨hfiniteProjectiveTensor.1, hfiniteProjectiveAway.1⟩
    letI : Module.Flat R M := hflat
    letI : Module.Finite R M := hfinite
    -- Route correction: follow the source proof by choosing a finite free cover, proving the
    -- tensor and localized kernels are finite, and then descending finiteness of the kernel.
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
    have hkerTensor :
        Module.Finite R' (R' ⊗[R] LinearMap.ker π) := by
      -- Follow the source proof: control the tensorized kernel of a finite free cover.
      exact finite_tensor_kernel_of_surjective_free_cover
        (R := R) (R' := R') (M := M) π hπ hflat hfiniteProjectiveTensor
    have hkerAway :
        Module.Finite (Localization.Away f) (Away f (LinearMap.ker π)) := by
      -- The localized kernel is handled by the same exact-sequence argument.
      exact finite_localizedAway_kernel_of_surjective_free_cover
        (R := R) (M := M) f π hπ hflat hfiniteProjectiveAway
    have hker : Module.Finite R (LinearMap.ker π) := by
      -- Apply the same finite-descent bridge to the kernel of the chosen free cover.
      exact
        (moduleFinite_iff_finite_tensor_and_localizedAway_of_quotientMapBijective_universe
          (R := R) (R' := R') (M := LinearMap.ker π) f hpair.quotientMapBijective).2
          ⟨hkerTensor, hkerAway⟩
    have hfinitePresentation : Module.FinitePresentation R M := by
      -- Finite generation of the kernel upgrades the chosen free cover to a finite presentation.
      exact finitePresentation_of_surjective_free_cover_of_finite_kernel
        (R := R) (M := M) π hπ hker
    letI : Module.FinitePresentation R M := hfinitePresentation
    letI : Module.Flat R M := hflat
    -- A finitely presented flat module is projective, so the source module is finite projective.
    exact ⟨hfinite, Module.Flat.projective_of_finitePresentation (R := R) (M := M)⟩

end
