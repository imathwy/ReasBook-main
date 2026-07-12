import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Support
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace RingTheory.Sequence

/-
Domain triage:
* primary domain: regular sequences on localized modules over commutative rings;
* sampled owner API: `RingTheory.Sequence.IsRegular`,
  `RingTheory.Sequence.IsRegular.isQuasiRegular`,
  `RingTheory.Sequence.IsQuasiRegular.exists_away_of_atPrime`,
  `Module.mem_support_iff`;
* core/canonical owner: `RingTheory.Sequence.IsRegular M rs`;
* layer split: regularity of the successive quotients is primitive owner data, while spreading
  regularity from `M_𝔭` to some principal neighborhood `M_g` is derived bridge API.
-/

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.68.6: a finite product of elements outside a prime ideal stays outside that
prime ideal. -/
lemma finset_prod_notMem_prime (p : Ideal R) [p.IsPrime] {n : ℕ} (g : Fin n → R)
    (hg : ∀ i, g i ∉ p) : (∏ i, g i) ∉ p := by
  simpa using p.primeCompl.prod_mem fun i _ ↦ hg i

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.68.6: if each stage module becomes zero after inverting one factor, then it
also becomes zero after inverting the whole product. -/
lemma subsingleton_localizedModule_away_of_product {n : ℕ} {N : Fin n → Type*}
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)] (g : Fin n → R)
    (hsub : ∀ i, Subsingleton (LocalizedModule (.powers (g i)) (N i))) :
    ∀ i, Subsingleton (LocalizedModule (.powers (∏ j, g j)) (N i)) := by
  intro i
  -- Clear the local denominator for one stage, then observe that the total product contains it.
  rw [LocalizedModule.subsingleton_iff]
  intro m
  obtain ⟨r, hr, hm⟩ := (LocalizedModule.subsingleton_iff.mp (hsub i)) m
  rcases hr with ⟨n, rfl⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem g (Finset.mem_univ i)
  refine ⟨(∏ j, g j) ^ n, ⟨n, rfl⟩, ?_⟩
  calc
    (∏ j, g j) ^ n • m = ((g i * c) ^ n) • m := by simp [hc]
    _ = (c ^ n) • ((g i) ^ n • m) := by
      simp [mul_pow, smul_smul, mul_comm]
    _ = 0 := by simp [hm]

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Lemma 10.68.6: a support point cannot disappear after inverting an element outside
that prime. -/
lemma nontrivial_away_of_mem_support {p : PrimeSpectrum R} (hp : p ∈ Module.support R M)
    {g : R} (hg : g ∉ p.asIdeal) : Nontrivial (LocalizedModule.Away g M) := by
  -- If the away localization were zero, its support would lie in `V(g)`, contradicting `g ∉ p`.
  by_contra htriv
  have hsub : Subsingleton (LocalizedModule.Away g M) := not_nontrivial_iff_subsingleton.mp htriv
  have hsupp : Module.support R M ⊆ PrimeSpectrum.zeroLocus ({g} : Set R) :=
    (LocalizedModule.subsingleton_iff_support_subset (M := M) (f := g)).mp hsub
  exact hg (hsupp hp (by simp))

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.68.6: localizing the multiplication map by `x` is multiplication by the
localized image of `x`. -/
lemma localizedModule_map_lsmul {S : Submonoid R} {Q : Type*}
    [AddCommGroup Q] [Module R Q] (x : R) :
    LocalizedModule.map S (LinearMap.lsmul R Q x) =
      LinearMap.lsmul (Localization S) (LocalizedModule S Q) (algebraMap R (Localization S) x) := by
  -- Check both maps on localized generators; there the multiplication formulas are explicit.
  ext y
  obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S (LocalizedModule.mkLinearMap S Q) y
  simp only [Function.uncurry_apply_pair]
  rw [← IsLocalizedModule.mk_eq_mk' (S := S) (M := Q) s m]
  -- After rewriting to `LocalizedModule.mk`, both sides are the same scalar-multiplication formula.
  simpa [LinearMap.lsmul_apply] using (LocalizedModule.smul'_mk (S := S) x s m).symm

-- Proof sketch: for each stage of the sequence, take the kernel of multiplication by the next
-- element on the corresponding quotient of `M`. These kernels are finite `R`-modules because `R`
-- is Noetherian and `M` is finite, and the hypothesis says their localizations at `p` vanish.
-- Clear denominators for finitely many generators of all these kernels at once to obtain
-- `g ∉ p` such that every localized kernel over `R_g` is zero, which is exactly regularity over
-- `R_g`.
/-- Lemma 10.68.6: if `R` is Noetherian, `M` is a finite `R`-module, and the image of a sequence
`xs` in `R_𝔭` is regular on `M_𝔭`, then after inverting one element outside `p` the image of `xs`
is already regular on `M_g`. -/
@[stacks 061L]
theorem IsRegular.exists_away_of_atPrime (p : Ideal R) [p.IsPrime] {xs : List R}
    (hxs : IsRegular (LocalizedModule.AtPrime p M)
      (xs.map (algebraMap R (Localization.AtPrime p)))) :
    ∃ g : R, g ∉ p ∧
      IsRegular (LocalizedModule.Away g M)
        (xs.map (algebraMap R (Localization.Away g))) := by
  classical
  let stageQuotient : Fin xs.length → Type v := fun i ↦
    M ⧸ (Ideal.ofList (xs.take i) • ⊤ : Submodule R M)
  let stageKernelSubmodule : ∀ i : Fin xs.length, Submodule R (stageQuotient i) := fun i ↦
    LinearMap.ker (LinearMap.lsmul R (stageQuotient i) xs[i])
  let stageKernel : Fin xs.length → Type v := fun i ↦
    stageKernelSubmodule i
  -- Reuse one quotient-localization equivalence for both stage quotients and the full quotient.
  have hquotientEquiv :
      ∀ (S : Submonoid R) (ys : List R),
        LocalizedModule S (M ⧸ (Ideal.ofList ys • ⊤ : Submodule R M)) ≃ₗ[Localization S]
          ((LocalizedModule S M) ⧸
            (Ideal.ofList (ys.map (algebraMap R (Localization S))) • ⊤ :
              Submodule (Localization S) (LocalizedModule S M))) := by
    intro S ys
    have hlocalized :
        ((Ideal.ofList ys • ⊤ : Submodule R M)).localized S =
          (Ideal.ofList (ys.map (algebraMap R (Localization S))) • ⊤ :
            Submodule (Localization S) (LocalizedModule S M)) := by
      rw [Submodule.localized, Submodule.localized'_smul, Ideal.localized'_eq_map,
        Submodule.localized'_top, Ideal.map_ofList]
    exact (localizedQuotientEquiv S (Ideal.ofList ys • ⊤ : Submodule R M)).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ hlocalized
  -- Package the canonical comparison between a localized stage quotient and the corresponding
  -- quotient of the localized module once, so later regularity clauses can be transported cleanly.
  have hstageQuotientEquiv :
      ∀ (S : Submonoid R) (i : Fin xs.length),
        LocalizedModule S (stageQuotient i) ≃ₗ[Localization S]
          ((LocalizedModule S M) ⧸
            (Ideal.ofList ((xs.take i).map (algebraMap R (Localization S))) • ⊤ :
              Submodule (Localization S) (LocalizedModule S M))) := by
    intro S i
    simpa [stageQuotient] using hquotientEquiv S (xs.take i)
  -- Convert localized vanishing of the `i`-th stage kernel into regularity of `x_i` on the
  -- localized `i`-th stage quotient, and conversely.
  have hstageKernel_subsingleton_iff :
      ∀ (S : Submonoid R) (i : Fin xs.length),
        Subsingleton (LocalizedModule S (stageKernel i)) ↔
          IsSMulRegular
            (((LocalizedModule S M) ⧸
              (Ideal.ofList ((xs.take i).map (algebraMap R (Localization S))) • ⊤ :
                Submodule (Localization S) (LocalizedModule S M))))
            (algebraMap R (Localization S) xs[i]) := by
    intro S i
    -- Route correction: identify the localized stage kernel as a localized submodule first, then
    -- rewrite its ambient endomorphism to the canonical localized `lsmul`.
    have hrestrictMap :
        (LocalizedModule.map S (LinearMap.lsmul R (stageQuotient i) xs[i])).restrictScalars R =
          IsLocalizedModule.map S
            (LocalizedModule.mkLinearMap S (stageQuotient i))
            (LocalizedModule.mkLinearMap S (stageQuotient i))
            (LinearMap.lsmul R (stageQuotient i) xs[i]) := by
      -- For canonical localized modules, the comparison isomorphisms in `restrictScalars_map_eq`
      -- are identities, so no extra transport remains.
      simpa [IsLocalizedModule.iso_localizedModule_eq_refl] using
        (LocalizedModule.restrictScalars_map_eq (S := S)
          (g₁ := LocalizedModule.mkLinearMap S (stageQuotient i))
          (g₂ := LocalizedModule.mkLinearMap S (stageQuotient i))
          (l := LinearMap.lsmul R (stageQuotient i) xs[i]))
    have hlocalizedMap :
        ((IsLocalizedModule.map S
            (LocalizedModule.mkLinearMap S (stageQuotient i))
            (LocalizedModule.mkLinearMap S (stageQuotient i))
            (LinearMap.lsmul R (stageQuotient i) xs[i])).extendScalarsOfIsLocalization
              S (Localization S)) =
          LocalizedModule.map S (LinearMap.lsmul R (stageQuotient i) xs[i]) := by
      -- Extending scalars of an already localized linear map recovers the localized-module map.
      rw [← hrestrictMap]
      simp
    have hlocalizedKernel :
        (stageKernelSubmodule i).localized S =
          LinearMap.ker (LocalizedModule.map S (LinearMap.lsmul R (stageQuotient i) xs[i])) := by
      -- Localization commutes with kernels, and here the localized kernel sits inside the
      -- localized stage quotient.
      calc
        (stageKernelSubmodule i).localized S =
            LinearMap.ker
              ((IsLocalizedModule.map S
                  (LocalizedModule.mkLinearMap S (stageQuotient i))
                  (LocalizedModule.mkLinearMap S (stageQuotient i))
                  (LinearMap.lsmul R (stageQuotient i) xs[i])).extendScalarsOfIsLocalization
                    S (Localization S)) := by
          simpa [stageKernelSubmodule, Submodule.localized] using
            (LinearMap.localized'_ker_eq_ker_localizedMap (S := Localization S)
              (p := S)
              (f := LocalizedModule.mkLinearMap S (stageQuotient i))
              (f' := LocalizedModule.mkLinearMap S (stageQuotient i))
              (g := LinearMap.lsmul R (stageQuotient i) xs[i]))
        _ = LinearMap.ker (LocalizedModule.map S (LinearMap.lsmul R (stageQuotient i) xs[i])) := by
          rw [hlocalizedMap]
    have hlocalizedStageKernel :
        Subsingleton (LocalizedModule S (stageKernel i)) ↔
          IsSMulRegular (LocalizedModule S (stageQuotient i))
            (algebraMap R (Localization S) xs[i]) := by
      -- Vanishing of the localized stage kernel is exactly injectivity of localized multiplication.
      rw [← ((stageKernelSubmodule i).localizedEquiv S).toEquiv.subsingleton_congr,
        Submodule.subsingleton_iff_eq_bot, hlocalizedKernel, localizedModule_map_lsmul,
        isSMulRegular_iff_ker_lsmul_eq_bot]
    -- Finally, transport regularity from the localized stage quotient to the canonical quotient
    -- presentation used in the regular-sequence predicate.
    exact hlocalizedStageKernel.trans <|
      (hstageQuotientEquiv S i).isSMulRegular_congr (algebraMap R (Localization S) xs[i])
  have hweakAtPrimeRaw :
      ∀ i : Fin (xs.map (algebraMap R (Localization.AtPrime p))).length,
        IsSMulRegular
          ((LocalizedModule.AtPrime p M) ⧸
            (Ideal.ofList
                ((xs.map (algebraMap R (Localization.AtPrime p))).take i) • ⊤ :
              Submodule (Localization.AtPrime p) (LocalizedModule.AtPrime p M)))
          ((xs.map (algebraMap R (Localization.AtPrime p)))[i]) :=
    (isWeaklyRegular_iff_Fin (M := LocalizedModule.AtPrime p M)
      (xs.map (algebraMap R (Localization.AtPrime p)))).mp hxs.toIsWeaklyRegular
  have hweakAtPrime :
      ∀ i : Fin xs.length,
        IsSMulRegular
          ((LocalizedModule.AtPrime p M) ⧸
            (Ideal.ofList
                ((xs.map (algebraMap R (Localization.AtPrime p))).take i) • ⊤ :
              Submodule (Localization.AtPrime p) (LocalizedModule.AtPrime p M)))
          ((xs.map (algebraMap R (Localization.AtPrime p)))[i]) := by
    intro i
    simpa using hweakAtPrimeRaw ⟨i.1, by simpa using i.2⟩
  have hstage_atPrime :
      ∀ i : Fin xs.length, Subsingleton (LocalizedModule p.primeCompl (stageKernel i)) := by
    intro i
    -- Apply the stage-kernel criterion at `p`; the regularity clause of `hxs` kills the kernel.
    exact (hstageKernel_subsingleton_iff p.primeCompl i).mpr <| by
      rw [List.map_take]
      simpa [LocalizedModule.AtPrime, Localization.AtPrime] using hweakAtPrime i
  -- After each stage kernel vanishes at `p`, choose one denominator clearing that stage.
  obtain ⟨gStage, hgStage, hsubStage⟩ :
      ∃ gStage : Fin xs.length → R,
        (∀ i, gStage i ∉ p) ∧
          (∀ i, Subsingleton (LocalizedModule (.powers (gStage i)) (stageKernel i))) := by
    choose gStage hgStage hsubStage using fun i : Fin xs.length ↦ by
      let _ : Subsingleton (LocalizedModule p.primeCompl (stageKernel i)) := hstage_atPrime i
      exact LocalizedModule.exists_subsingleton_away (M := stageKernel i) p
    exact ⟨gStage, hgStage, hsubStage⟩
  let g : R := ∏ i, gStage i
  have hg : g ∉ p := finset_prod_notMem_prime p gStage hgStage
  have hsubProduct :
      ∀ i : Fin xs.length, Subsingleton (LocalizedModule (.powers g) (stageKernel i)) :=
    subsingleton_localizedModule_away_of_product gStage hsubStage
  have hregularAway :
      IsRegular (LocalizedModule.Away g M)
        (xs.map (algebraMap R (Localization.Away g))) := by
    have hweakAway :
        IsWeaklyRegular (LocalizedModule.Away g M)
          (xs.map (algebraMap R (Localization.Away g))) := by
      -- Each away-localized stage kernel is zero by construction, so every stage remains regular.
      rw [isWeaklyRegular_iff_Fin]
      intro i
      let j : Fin xs.length := ⟨i.1, by simpa using i.2⟩
      rw [← List.map_take]
      simpa [LocalizedModule.Away, Localization.Away, j] using
        (hstageKernel_subsingleton_iff (.powers g) j).mp (hsubProduct j)
    let finalQuotient : Type v := M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)
    have hfinalAtPrimeEquiv :
        LocalizedModule.AtPrime p finalQuotient ≃ₗ[Localization.AtPrime p]
          ((LocalizedModule.AtPrime p M) ⧸
            (Ideal.ofList (xs.map (algebraMap R (Localization.AtPrime p))) • ⊤ :
              Submodule (Localization.AtPrime p) (LocalizedModule.AtPrime p M))) := by
      -- The full quotient localizes to the quotient of the localized module by the full list ideal.
      simpa [finalQuotient] using hquotientEquiv p.primeCompl xs
    have hpSupport :
        (⟨p, inferInstance⟩ : PrimeSpectrum R) ∈ Module.support R finalQuotient := by
      -- The final quotient is nontrivial after localizing at `p` because `hxs` is regular there.
      rw [Module.mem_support_iff]
      let _ :
          Nontrivial (((LocalizedModule.AtPrime p M) ⧸
            (Ideal.ofList (xs.map (algebraMap R (Localization.AtPrime p))) • ⊤ :
              Submodule (Localization.AtPrime p) (LocalizedModule.AtPrime p M)))) :=
        Submodule.Quotient.nontrivial_iff.mpr <| by
          simpa [ne_comm] using hxs.top_ne_smul
      exact hfinalAtPrimeEquiv.nontrivial
    have hfinalAwayNontrivial :
        Nontrivial (LocalizedModule.Away g finalQuotient) :=
      nontrivial_away_of_mem_support (M := finalQuotient) hpSupport hg
    have hfinalAwayEquiv :
        LocalizedModule.Away g finalQuotient ≃ₗ[Localization.Away g]
          ((LocalizedModule.Away g M) ⧸
            (Ideal.ofList (xs.map (algebraMap R (Localization.Away g))) • ⊤ :
              Submodule (Localization.Away g) (LocalizedModule.Away g M))) := by
      -- The same quotient-localization comparison identifies the away localization of the final
      -- quotient with the final quotient of the away-localized module.
      simpa [finalQuotient] using hquotientEquiv (.powers g) xs
    have htop_ne_smul :
        (⊤ : Submodule (Localization.Away g) (LocalizedModule.Away g M)) ≠
          (Ideal.ofList (xs.map (algebraMap R (Localization.Away g))) • ⊤ :
            Submodule (Localization.Away g) (LocalizedModule.Away g M)) := by
      -- Transport nontriviality of the away-localized final quotient back to the quotient
      -- presentation that appears in `IsRegular`.
      let _ : Nontrivial (LocalizedModule.Away g finalQuotient) := hfinalAwayNontrivial
      have hquotNontrivial :
          Nontrivial (((LocalizedModule.Away g M) ⧸
            (Ideal.ofList (xs.map (algebraMap R (Localization.Away g))) • ⊤ :
              Submodule (Localization.Away g) (LocalizedModule.Away g M)))) :=
        hfinalAwayEquiv.symm.nontrivial
      have hneq :
          (Ideal.ofList (xs.map (algebraMap R (Localization.Away g))) • ⊤ :
            Submodule (Localization.Away g) (LocalizedModule.Away g M)) ≠ ⊤ :=
        (Submodule.Quotient.nontrivial_iff
          (p := (Ideal.ofList (xs.map (algebraMap R (Localization.Away g))) • ⊤ :
            Submodule (Localization.Away g) (LocalizedModule.Away g M)))).mp hquotNontrivial
      intro htop
      exact hneq htop.symm
    exact ⟨hweakAway, htop_ne_smul⟩
  exact ⟨g, hg, hregularAway⟩

end

end RingTheory.Sequence
