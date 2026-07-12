import Mathlib
import StacksProject_2024.Chap15.Lemma_15_91_1
import StacksProject_2024.Chap15.Lemma_15_91_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u

section

variable {R : Type u} [CommRing R]
variable {R' : Type u} [CommRing R'] [Algebra R R']
variable {M : Type u} [AddCommMonoid M] [Module R M]

local notation "Away" => LocalizedModule.Away

/- Domain-style sampling:
- primary domain: finite-generation descent for modules in the Beauville-Laszlo completion and
  localization setting;
- sampled owner declarations:
  `principalPowerIdealImageQuotientMap`,
  `tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective`,
  `LocalizedModule.equivTensorProduct`,
  `adicCompletion_quotientMap_bijective`;
- best owner abstraction: the finite-generation criterion naturally lives on the pair of canonical
  base-change objects `R' ⊗[R] M` and `Away f M`; the completion case is a source-faithful
  specialization through `principalAdicCompletion`;
- primitive data: the algebra map `R → R'`, the element `f : R`, the `R`-module `M`, and the
  principal-power quotient bijectivity hypothesis;
- derived API: the completion specialization;
- triage:
  - `source-facing`: the finite-generation descent criterion;
  - `core/canonical`: the owner objects `R' ⊗[R] M`, `Away f M`, and the chapter owner
    `principalPowerIdealImageQuotientMap`;
  - `bridge/view`: the specialization to `principalAdicCompletion f`.
-/

-- Proof sketch: the forward implication is preserved by extension of scalars and localization. For
-- the converse, choose a surjection from a finite free `R`-module onto `M` whose image generates
-- both `R' ⊗[R] M` and `M_f`; its cokernel becomes zero after tensoring with `R'` and after
-- localizing away from `f`, so Lemma `15.91.2` forces that cokernel to vanish, proving that `M`
-- is finitely generated over `R`.
-- Lemma 15.91.4 itself is proved below after the file-local descent helpers.
/-- Helper for Lemma 15.91.4: localizing submodules is monotone. -/
lemma localized_submodule_mono
    (S : Submonoid R) {P Q : Submodule R M} (hPQ : P ≤ Q) :
    P.localized S ≤ Q.localized S := by
  intro x hx
  -- Reuse the same numerator and denominator witness after enlarging the source submodule.
  change x ∈ Submodule.localized₀ S (LocalizedModule.mkLinearMap S M) Q
  change x ∈ Submodule.localized₀ S (LocalizedModule.mkLinearMap S M) P at hx
  rcases hx with ⟨m, hm, s, rfl⟩
  exact ⟨m, hPQ hm, s, rfl⟩

/-- Helper for Lemma 15.91.4: finite generation of the tensor base change comes from a finitely
generated submodule of `M` whose base change is already the whole tensor product. -/
lemma exists_fg_submodule_baseChange_eq_top_of_moduleFinite
    (hfinite : Module.Finite R' (R' ⊗[R] M)) :
    ∃ P : Submodule R M, P.FG ∧ P.baseChange R' = ⊤ := by
  classical
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R' (R' ⊗[R] M)
  have hdecomp :
      ∀ i : Fin n, ∃ k : ℕ, ∃ a : Fin k → R', ∃ m : Fin k → M,
        π (Pi.basisFun R' (Fin n) i) = ∑ j, a j ⊗ₜ[R] m j := by
    intro i
    obtain ⟨k, a, m, hm⟩ := TensorProduct.exists_sum_tmul_eq (π (Pi.basisFun R' (Fin n) i))
    exact ⟨k, a, m, hm⟩
  choose k a m hm using hdecomp
  let v : (Σ i : Fin n, Fin (k i)) → M := fun ij ↦ m ij.1 ij.2
  let P : Submodule R M := Submodule.span R (Set.range v)
  refine ⟨P, Submodule.fg_span (Set.finite_range v), ?_⟩
  apply top_unique
  intro z hz
  rcases hπ z with ⟨y, rfl⟩
  have hy : y = ∑ i, Pi.single i (y i) := by
    ext i
    simp
  -- Expand a tensor element along the standard basis of the finite free source.
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
        Submodule.span R' ((fun x ↦ (1 : R') ⊗ₜ[R] x) '' (P : Set M)) := by
    exact Submodule.subset_span ⟨m i j, hmP, rfl⟩
  -- Each summand is a scalar multiple of a denominator-`1` tensor coming from `P`.
  have hsmul :
      a i j • ((1 : R') ⊗ₜ[R] m i j) ∈
        Submodule.span R' ((fun x ↦ (1 : R') ⊗ₜ[R] x) '' (P : Set M)) :=
    Submodule.smul_mem _ _ hgen
  simpa [TensorProduct.smul_tmul', one_smul] using hsmul

/-- Helper for Lemma 15.91.4: finite generation after localizing away from `f` comes from a
finitely generated submodule of `M` whose localization is already the whole localized module. -/
lemma exists_fg_submodule_localized_eq_top_of_moduleFinite
    (f : R)
    (hfinite : Module.Finite (Localization.Away f) (Away f M)) :
    ∃ P : Submodule R M, P.FG ∧ Submodule.localized (p := Submonoid.powers f) P = ⊤ := by
  classical
  let S : Submonoid R := Submonoid.powers f
  let mkM : M →ₗ[R] Away f M := LocalizedModule.mkLinearMap S M
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' (Localization.Away f) (Away f M)
  have hrepr :
      ∀ i : Fin n, ∃ m : M, ∃ s : S,
        IsLocalizedModule.mk' mkM m s = π (Pi.basisFun (Localization.Away f) (Fin n) i) := by
    intro i
    rcases IsLocalizedModule.mk'_surjective S mkM
        (π (Pi.basisFun (Localization.Away f) (Fin n) i)) with ⟨⟨m, s⟩, hs⟩
    exact ⟨m, s, hs⟩
  choose m s hs using hrepr
  let P : Submodule R M := Submodule.span R (Set.range m)
  refine ⟨P, Submodule.fg_span (Set.finite_range m), ?_⟩
  apply top_unique
  intro z hz
  rcases hπ z with ⟨y, rfl⟩
  have hy : y = ∑ i, Pi.single i (y i) := by
    ext i
    simp
  -- Expand a localized vector along the standard basis of the finite free source.
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
  exact ⟨m i, Submodule.subset_span ⟨i, rfl⟩, s i, hs i⟩

/-- Helper for Lemma 15.91.4: once the tensor-base-changed submodule is all of `R' ⊗[R] M`, the
tensor base change of the quotient vanishes. -/
lemma tensor_quotient_subsingleton_of_baseChange_eq_top
    {Q : Type u} [AddCommGroup Q] [Module R Q]
    (P : Submodule R Q) (hP : P.baseChange R' = ⊤) :
    Subsingleton (R' ⊗[R] (Q ⧸ P)) := by
  let ψ : R' ⊗[R] P →ₗ[R'] R' ⊗[R] Q := P.subtype.baseChange R'
  let φ : R' ⊗[R] Q →ₗ[R'] R' ⊗[R] (Q ⧸ P) := P.mkQ.baseChange R'
  have hψsurj : Function.Surjective ψ := by
    -- `P.baseChange R' = ⊤` is exactly surjectivity of the tensorized subtype inclusion.
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
  -- Every element of the quotient tensor product is the image of something already coming from
  -- the tensorized copy of `P`, so it must be zero by exactness.
  refine (subsingleton_iff_forall_eq 0).2 fun z ↦ ?_
  rcases hsurj z with ⟨y, rfl⟩
  rcases hψsurj y with ⟨x, hx⟩
  exact (hExact y).2 ⟨x, hx⟩

/-- Helper for Lemma 15.91.4: once the localized copy of a submodule is all of `Away f M`, the
localization of the quotient vanishes. -/
lemma localized_quotient_subsingleton_of_localized_eq_top
    {Q : Type u} [AddCommGroup Q] [Module R Q]
    (f : R) (P : Submodule R Q)
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

/-- Helper for Lemma 15.91.4: if both the tensor base change and the localization away from `f`
of an `R`-module are subsingleton, then the module itself is subsingleton. -/
lemma subsingleton_of_tensor_and_localizedAway_subsingleton_of_quotientMapBijective
    (f : R)
    (hquot : ∀ n : ℕ+, Function.Bijective
      (principalPowerIdealImageQuotientMap (algebraMap R R') f n))
    {Q : Type u} [AddCommMonoid Q] [Module R Q]
    (htensor : Subsingleton (R' ⊗[R] Q))
    (hlocal : Subsingleton (Away f Q)) :
    Subsingleton Q := by
  classical
  letI : AddCommGroup Q := Module.addCommMonoidToAddCommGroup R
  by_contra hQ
  letI : Nontrivial Q := not_subsingleton_iff_nontrivial.mp hQ
  have hleft : Subsingleton (Q ⊗[R] R') := by
    -- Commute the tensor factors so the subsingleton hypothesis matches the right-ordered tensor.
    exact (TensorProduct.comm R R' Q).symm.toEquiv.subsingleton
  have hright : Subsingleton (Q ⊗[R] Localization.Away f) := by
    let e : Q ⊗[R] Localization.Away f ≃ₗ[R] Away f Q :=
      (TensorProduct.comm R Q (Localization.Away f)).trans
        ((LocalizedModule.equivTensorProduct (Submonoid.powers f) Q).symm.restrictScalars R)
    exact e.toEquiv.subsingleton
  letI : Subsingleton (Q ⊗[R] R') := hleft
  letI : Subsingleton (Q ⊗[R] Localization.Away f) := hright
  have hprod :
      Subsingleton (Q ⊗[R] (R' × Localization.Away f)) := by
    -- Tensoring with a product ring splits as the product of the two tensor factors.
    exact (TensorProduct.prodRight R R Q R' (Localization.Away f)).toEquiv.subsingleton
  have hnontrivial :
      Nontrivial (Q ⊗[R] (R' × Localization.Away f)) :=
    tensorProduct_prod_localizationAway_nontrivial_of_quotientMapBijective
      (R := R) (R' := R') (M := Q) f hquot
  exact (not_nontrivial_iff_subsingleton.mpr hprod) hnontrivial

/-- Lemma 15.91.4: if the quotient maps `R / (f)^n → R' / (f)^n R'` are bijective for all
positive integers `n`, then an `R`-module `M` is finitely generated if and only if both its base
change `R' ⊗[R] M` and its localization `Away f M` are finitely generated over
`R'` and `Localization.Away f`, respectively. -/
theorem moduleFinite_iff_finite_tensor_and_localizedAway_of_quotientMapBijective
    (f : R)
    (hquot : ∀ n : ℕ+, Function.Bijective
      (principalPowerIdealImageQuotientMap (algebraMap R R') f n)) :
    Module.Finite R M ↔
      Module.Finite R' (R' ⊗[R] M) ∧
        Module.Finite (Localization.Away f) (Away f M) := by
  constructor
  · intro hfinite
    letI : Module.Finite R M := hfinite
    constructor
    · -- Finite generation survives extension of scalars.
      infer_instance
    · letI : Module.Finite (Localization.Away f) ((Localization.Away f) ⊗[R] M) := inferInstance
      -- Transport the localized tensor product back to the canonical localized module.
      exact Module.Finite.equiv (LocalizedModule.equivTensorProduct (Submonoid.powers f) M).symm
  · rintro ⟨hfiniteTensor, hfiniteLocalization⟩
    letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
    obtain ⟨P₁, hP₁fg, hP₁top⟩ :=
      exists_fg_submodule_baseChange_eq_top_of_moduleFinite
        (R := R) (R' := R') (M := M) hfiniteTensor
    obtain ⟨P₂, hP₂fg, hP₂top⟩ :=
      exists_fg_submodule_localized_eq_top_of_moduleFinite
        (R := R) (M := M) f hfiniteLocalization
    let N : Submodule R M := P₁ ⊔ P₂
    have hNfg : N.FG := Submodule.FG.sup hP₁fg hP₂fg
    letI : Module.Finite R N := Module.Finite.of_fg hNfg
    have hNtensor : N.baseChange R' = ⊤ := by
      apply top_unique
      calc
        (⊤ : Submodule R' (R' ⊗[R] M)) = P₁.baseChange R' := hP₁top.symm
        _ ≤ N.baseChange R' := by
          rw [Submodule.baseChange_eq_span, Submodule.baseChange_eq_span]
          exact Submodule.span_mono fun z hz ↦ by
            rcases hz with ⟨m, hm, rfl⟩
            have hmN : m ∈ N := (show P₁ ≤ N by exact le_sup_left) hm
            exact ⟨m, hmN, rfl⟩
    have hNlocalized : Submodule.localized (p := Submonoid.powers f) N = ⊤ := by
      apply top_unique
      calc
        (⊤ : Submodule (Localization.Away f) (Away f M)) =
            Submodule.localized (p := Submonoid.powers f) P₂ := hP₂top.symm
        _ ≤ Submodule.localized (p := Submonoid.powers f) N :=
          localized_submodule_mono (R := R) (M := M) (Submonoid.powers f) le_sup_right
    have htensorQuot :
        Subsingleton (R' ⊗[R] (M ⧸ N)) :=
      tensor_quotient_subsingleton_of_baseChange_eq_top
        (R := R) (R' := R') (Q := M) N hNtensor
    have hlocalizedQuot :
        Subsingleton (Away f (M ⧸ N)) :=
      localized_quotient_subsingleton_of_localized_eq_top
        (R := R) (Q := M) f N hNlocalized
    have hquotSub :
        Subsingleton (M ⧸ N) :=
      subsingleton_of_tensor_and_localizedAway_subsingleton_of_quotientMapBijective
        (R := R) (R' := R') (f := f) hquot htensorQuot hlocalizedQuot
    have hNtop : N = ⊤ := (Submodule.Quotient.subsingleton_iff).mp hquotSub
    have hsurj : Function.Surjective N.subtype := by
      intro x
      refine ⟨⟨x, ?_⟩, rfl⟩
      simpa [N, hNtop]
    -- The finite submodule `N` already equals `M`, so finite generation descends to `M`.
    exact Module.Finite.of_surjective N.subtype hsurj

-- Proof sketch: apply
-- `moduleFinite_iff_finite_tensor_and_localizedAway_of_quotientMapBijective` with
-- `R' = principalAdicCompletion f`, and use Lemma `15.91.1` to supply the
-- required quotient-map bijectivity for the `(f)`-adic completion.
/-- The completion-localization Beauville-Laszlo criterion for finite generation, in owner form. -/
theorem moduleFinite_of_finite_completion_and_localizedAway
    (f : R)
    (hfiniteCompletion :
      Module.Finite
        (principalAdicCompletion f)
        (principalAdicCompletion f ⊗[R] M))
    (hfiniteLocalization :
      Module.Finite (Localization.Away f) (Away f M)) :
    Module.Finite R M := by
  -- Specialize the main descent criterion to the principal adic completion.
  exact
    (moduleFinite_iff_finite_tensor_and_localizedAway_of_quotientMapBijective
      (R := R) (R' := principalAdicCompletion f) (M := M) f
      (fun n ↦ principalAdicCompletion_quotientMap_bijective (R := R) f n)).2
      ⟨hfiniteCompletion, hfiniteLocalization⟩

end
