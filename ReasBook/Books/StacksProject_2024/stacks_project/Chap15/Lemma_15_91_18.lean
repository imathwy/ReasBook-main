import Mathlib
import StacksProject_2024.Chap10.Lemma_10_39_12
import StacksProject_2024.Chap15.Lemma_15_91_4
import StacksProject_2024.Chap15.Lemma_15_91_6
import StacksProject_2024.Chap15.Remark_15_91_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open CategoryTheory MonoidalCategory

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
variable {R' : Type u} [CommRing R'] [Algebra R R']
variable {M : Type u} [AddCommMonoid M] [Module R M]
local notation "Away" => LocalizedModule.Away

/- Domain-style sampling:
* primary domain: Beauville-Laszlo glueing pairs and flatness descent for a single localization.
* sampled owner declarations:
  `IsBeauvilleLaszloGlueingPairAlong`,
  `Module.Flat`,
  `beauvilleLaszloModuleCechSequence`,
  `beauvilleLaszloModuleCechH0Map_surjective`.
* owner abstraction: the ambient owner is the glueing-pair predicate
  `IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f`; the module property itself is the
  canonical owner predicate `Module.Flat`, not a packaged Beauville-Laszlo flatness wrapper.
* primitive data: the rings `R`, `R'`, the map `algebraMap R R'`, the element `f`, and the
  `R`-module `M`.
* derived API: the two comparison flatness conditions on the canonical base-change module
  `R' ⊗[R] M` and the canonical localization `Away f M`.
*
* Source/core/bridge triage:
  `source-facing`: the Beauville-Laszlo flatness criterion for a single module;
  `core/canonical`: `IsBeauvilleLaszloGlueingPairAlong` and `Module.Flat`;
  `bridge/view`: the base-change module `R' ⊗[R] M` and the localization `Away f M`.
-/

-- Proof sketch: one implication is preserved by base change and localization. For the converse,
-- replace `M` by the glueable module `H⁰(Can(M))` from Remark `15.91.17`, use the Beauville-Laszlo
-- short exact sequence to compare `M` with that replacement, and then prove flatness by the Tor
-- criterion using the exact Čech sequence of the glueing pair.
/-- Helper for Lemma 15.91.18: flatness of an `R`-module descends to its localization away from
`f`. -/
lemma flat_localizedAway_of_flat
    (f : R) (hflat : Module.Flat R M) :
    Module.Flat (Localization.Away f) (Away f M) := by
  let _ : Module.Flat R M := hflat
  have htensor :
      Module.Flat (Localization.Away f) ((Localization.Away f) ⊗[R] M) := by
    -- Base change to `R_f` gives the tensor-product model of the localized module.
    simpa using
      (Module.Flat.baseChange (R := R) (S := Localization.Away f) (M := M))
  let _ : Module.Flat (Localization.Away f) ((Localization.Away f) ⊗[R] M) := htensor
  -- Transport the tensor-side flatness across the standard localization/tensor equivalence.
  exact
    Module.Flat.of_linearEquiv
      (LocalizedModule.equivTensorProduct (Submonoid.powers f) M)

section ProofHelpers

variable {G : Type u} [AddCommGroup G] [Module R G]

/-- Helper for Lemma 15.91.18: after passing through `moduleCatCyclesIso.hom`, the public map to
cycles agrees with the concrete kernel-level map `moduleCatToCycles`. -/
lemma moduleCatCyclesIso_hom_toCycles_local
    (S : CategoryTheory.ShortComplex (ModuleCat R)) (b : S.X₁) :
    S.moduleCatCyclesIso.hom (S.toCycles.hom b) = S.moduleCatToCycles b := by
  -- Compare the two cycle representatives through their ambient values in `S.X₂`.
  apply Subtype.ext
  change S.iCycles.hom (S.toCycles.hom b) = (S.moduleCatToCycles b).1
  have hto :
      S.iCycles.hom (S.toCycles.hom b) = S.f.hom b := by
    -- The defining relation `toCycles ≫ iCycles = f` identifies the ambient values.
    exact
      LinearMap.congr_fun
        (ModuleCat.hom_ext_iff.mp (CategoryTheory.ShortComplex.toCycles_i S))
        b
  simpa [CategoryTheory.ShortComplex.moduleCatToCycles] using hto

/-- Helper for Lemma 15.91.18: tensoring a bijective linear map along a scalar extension keeps the
base-changed map bijective. -/
lemma baseChange_bijective_of_bijective_local
    {A : Type u} [CommRing A] [Algebra R A]
    {N P : Type u} [AddCommMonoid N] [AddCommMonoid P] [Module R N] [Module R P]
    (φ : N →ₗ[R] P) (hφ : Function.Bijective φ) :
    Function.Bijective (LinearMap.baseChange A φ) := by
  let e : N ≃ₗ[R] P := LinearEquiv.ofBijective φ hφ
  let ψ : P →ₗ[R] N := e.symm.toLinearMap
  have hleft : ψ ∘ₗ φ = LinearMap.id := by
    -- The inverse from the linear equivalence is a left inverse to `φ`.
    ext x
    change e.symm (e x) = x
    exact e.symm_apply_apply x
  have hright : φ ∘ₗ ψ = LinearMap.id := by
    -- The same inverse is also a right inverse to `φ`.
    ext x
    change e (e.symm x) = x
    exact e.apply_symm_apply x
  have hbaseLeft :
      (LinearMap.baseChange A ψ) ∘ₗ (LinearMap.baseChange A φ) = LinearMap.id := by
    -- Base change preserves the left-inverse identity.
    calc
      (LinearMap.baseChange A ψ) ∘ₗ (LinearMap.baseChange A φ) =
          LinearMap.baseChange A (ψ ∘ₗ φ) := by
            rw [← LinearMap.baseChange_comp]
      _ = LinearMap.baseChange A (LinearMap.id : N →ₗ[R] N) := by
            simpa [hleft]
      _ = LinearMap.id := by
            simpa using (LinearMap.baseChange_id (R := R) (A := A) (M := N))
  have hbaseRight :
      (LinearMap.baseChange A φ) ∘ₗ (LinearMap.baseChange A ψ) = LinearMap.id := by
    -- Base change preserves the right-inverse identity.
    calc
      (LinearMap.baseChange A φ) ∘ₗ (LinearMap.baseChange A ψ) =
          LinearMap.baseChange A (φ ∘ₗ ψ) := by
            rw [← LinearMap.baseChange_comp]
      _ = LinearMap.baseChange A (LinearMap.id : P →ₗ[R] P) := by
            simpa [hright]
      _ = LinearMap.id := by
            simpa using (LinearMap.baseChange_id (R := R) (A := A) (M := P))
  constructor
  · -- A left inverse after base change makes the tensorized map injective.
    exact Function.LeftInverse.injective (f := LinearMap.baseChange A φ) <| by
      intro x
      exact LinearMap.congr_fun hbaseLeft x
  · -- A right inverse after base change makes the tensorized map surjective.
    exact Function.RightInverse.surjective (f := LinearMap.baseChange A φ) <| by
      intro x
      exact LinearMap.congr_fun hbaseRight x

/-- Helper for Lemma 15.91.18: the public map `toCycles.hom` is surjective for the canonical
`H⁰(Cech)` replacement. -/
lemma cech_replacement_toCycles_surjective
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    Function.Surjective (beauvilleLaszloModuleCechSequence R' G f).toCycles.hom := by
  let S := beauvilleLaszloModuleCechSequence R' G f
  intro z
  obtain ⟨x, hx⟩ :=
    beauvilleLaszloModuleCechH0Map_surjective
      (R := R) (R' := R') (M := G) (f := f) hpair (S.moduleCatCyclesIso.hom z)
  refine ⟨x, ?_⟩
  apply (ModuleCat.mono_iff_injective S.moduleCatCyclesIso.hom).1 inferInstance
  exact (moduleCatCyclesIso_hom_toCycles_local S x).trans hx

/-- Helper for Lemma 15.91.18: the public kernel row
`0 → ker(toCycles.hom) → G → H⁰(Cech(G)) → 0` is short exact. -/
lemma cech_replacement_shortExact_row
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    (CategoryTheory.ShortComplex.moduleCatMk
      (LinearMap.ker (beauvilleLaszloModuleCechSequence R' G f).toCycles.hom).subtype
      (beauvilleLaszloModuleCechSequence R' G f).toCycles.hom
      (by
        ext x
        exact x.2)).ShortExact := by
  let S := beauvilleLaszloModuleCechSequence R' G f
  refine CategoryTheory.ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · -- The public replacement row is the standard kernel-subtype exact sequence.
    rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    simpa using LinearMap.exact_subtype_ker_map S.toCycles.hom
  · -- The kernel subtype map is injective, hence mono.
    exact (ModuleCat.mono_iff_injective _).2 fun x y h ↦ Subtype.ext h
  · -- Surjectivity comes from the Beauville-Laszlo `H⁰(Cech)` replacement map.
    exact (ModuleCat.epi_iff_surjective _).2 <|
      cech_replacement_toCycles_surjective
        (R := R) (R' := R') (G := G) f hpair

/-- Helper for Lemma 15.91.18: in a short exact row, injectivity of the right map forces the left
term to vanish. -/
lemma subsingleton_of_shortExact_of_injective_right
    {S : CategoryTheory.ShortComplex (ModuleCat R)}
    (hS : S.ShortExact)
    (hg : Function.Injective S.g.hom) :
    Subsingleton S.X₁ := by
  have hExact :
      LinearMap.range S.f.hom = LinearMap.ker S.g.hom :=
    (LinearMap.exact_iff.mp
      ((CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1
        hS.exact)).symm
  have hker : LinearMap.ker S.g.hom = ⊥ := LinearMap.ker_eq_bot.2 hg
  refine (subsingleton_iff_forall_eq 0).2 fun x ↦ ?_
  apply hS.moduleCat_injective_f
  have hxRange : S.f.hom x ∈ LinearMap.range S.f.hom := ⟨x, rfl⟩
  rw [hExact, hker, Submodule.mem_bot] at hxRange
  simpa using hxRange

/-- Helper for Lemma 15.91.18: after tensoring with `R'`, the public `toCycles` map is bijective. -/
lemma cech_replacement_toCycles_baseChange_bijective
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    Function.Bijective
      ((beauvilleLaszloModuleCechSequence R' G f).toCycles.hom.baseChange R') := by
  let S := beauvilleLaszloModuleCechSequence R' G f
  have hcomp :
      S.moduleCatCyclesIso.hom.hom.comp S.toCycles.hom = S.moduleCatToCycles := by
    ext x
    exact moduleCatCyclesIso_hom_toCycles_local S x
  have hcyclesBaseBij :
      Function.Bijective ((S.moduleCatCyclesIso.hom.hom).baseChange R') :=
    baseChange_bijective_of_bijective_local
      (R := R) (A := R') S.moduleCatCyclesIso.hom.hom
      ⟨(ModuleCat.mono_iff_injective S.moduleCatCyclesIso.hom).1 inferInstance,
        (ModuleCat.epi_iff_surjective S.moduleCatCyclesIso.hom).1 inferInstance⟩
  have hmoduleBaseBij :
      Function.Bijective ((S.moduleCatToCycles).baseChange R') :=
    beauvilleLaszloModuleCechH0Map_baseChange_bijective
      (R := R) (R' := R') (M := G) (f := f) hpair
  have hcompBase :
      ((S.moduleCatCyclesIso.hom.hom).baseChange R').comp
          ((S.toCycles.hom).baseChange R') =
        (S.moduleCatToCycles).baseChange R' := by
    calc
      ((S.moduleCatCyclesIso.hom.hom).baseChange R').comp
          ((S.toCycles.hom).baseChange R') =
        (S.moduleCatCyclesIso.hom.hom.comp S.toCycles.hom).baseChange R' := by
          rw [← LinearMap.baseChange_comp]
      _ = (S.moduleCatToCycles).baseChange R' := by
          exact congrArg (LinearMap.baseChange R') hcomp
  constructor
  · -- Injectivity is checked after composing with the base-changed cycles isomorphism.
    intro x y hxy
    exact hmoduleBaseBij.1 <| by
      have hxcomp :
          ((S.moduleCatCyclesIso.hom.hom).baseChange R')
              (((S.toCycles.hom).baseChange R') x) =
            (S.moduleCatToCycles).baseChange R' x := by
        simpa [LinearMap.comp_apply] using congrArg (fun ψ ↦ ψ x) hcompBase
      have hycomp :
          ((S.moduleCatCyclesIso.hom.hom).baseChange R')
              (((S.toCycles.hom).baseChange R') y) =
            (S.moduleCatToCycles).baseChange R' y := by
        simpa [LinearMap.comp_apply] using congrArg (fun ψ ↦ ψ y) hcompBase
      exact hxcomp.symm.trans <| (congrArg ((S.moduleCatCyclesIso.hom.hom).baseChange R') hxy).trans hycomp
  · -- Surjectivity lifts through the same comparison square.
    intro z
    obtain ⟨y, hy⟩ :=
      hmoduleBaseBij.2 (((S.moduleCatCyclesIso.hom.hom).baseChange R') z)
    refine ⟨y, ?_⟩
    exact hcyclesBaseBij.1 <| by
      have hycomp :
          ((S.moduleCatCyclesIso.hom.hom).baseChange R')
              (((S.toCycles.hom).baseChange R') y) =
            (S.moduleCatToCycles).baseChange R' y := by
        simpa [LinearMap.comp_apply] using congrArg (fun ψ ↦ ψ y) hcompBase
      exact hycomp.trans hy

/-- Helper for Lemma 15.91.18: after localizing away from `f`, the public `toCycles` map is
bijective. -/
lemma cech_replacement_toCycles_localizedAway_bijective
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    Function.Bijective
      (LocalizedModule.map
        (Submonoid.powers f)
        (beauvilleLaszloModuleCechSequence R' G f).toCycles.hom) := by
  -- Route correction: the remaining interface problem is to rewrite the localized public
  -- `toCycles` map through `moduleCatCyclesIso.hom` and the imported localized bijection on
  -- `moduleCatToCycles`. This is the exact localized comparison needed in the source proof.
  -- TODO for Lemma 15.91.18: localize the identity from `moduleCatCyclesIso_hom_toCycles_local`,
  -- compare the resulting composition with `beauvilleLaszloModuleCechH0Map_localizedAway_bijective`,
  -- and then read off injectivity and surjectivity of the localized public `toCycles` map.
  sorry

/-- Helper for Lemma 15.91.18: the canonical `H⁰(Cech)` replacement inherits the two branch
flatness hypotheses from `M`. -/
lemma cech_cycles_branch_flatness
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f)
    (hflatTensor : Module.Flat R' (R' ⊗[R] G))
    (hflatAway : Module.Flat (Localization.Away f) (Away f G)) :
    Module.Flat R' (R' ⊗[R] (beauvilleLaszloModuleCechSequence R' G f).cycles) ∧
      Module.Flat (Localization.Away f)
        (Away f (beauvilleLaszloModuleCechSequence R' G f).cycles) := by
  let S := beauvilleLaszloModuleCechSequence R' G f
  have hbaseBij :
      Function.Bijective ((S.moduleCatToCycles).baseChange R') :=
    beauvilleLaszloModuleCechH0Map_baseChange_bijective
      (R := R) (R' := R') (M := G) (f := f) hpair
  have hcyclesBaseBij :
      Function.Bijective ((S.moduleCatCyclesIso.hom.hom).baseChange R') :=
    baseChange_bijective_of_bijective_local
      (R := R) (A := R') S.moduleCatCyclesIso.hom.hom
      ⟨(ModuleCat.mono_iff_injective S.moduleCatCyclesIso.hom).1 inferInstance,
        (ModuleCat.epi_iff_surjective S.moduleCatCyclesIso.hom).1 inferInstance⟩
  have hlocalizedBij :
      Function.Bijective
        (LocalizedModule.map (Submonoid.powers f) S.moduleCatToCycles) :=
    beauvilleLaszloModuleCechH0Map_localizedAway_bijective
      (R := R) (R' := R') (M := G) (f := f) hpair
  have hcyclesLocalizedBij :
      Function.Bijective
        (LocalizedModule.map (Submonoid.powers f) S.moduleCatCyclesIso.hom.hom) := by
    constructor
    · -- Localizing an injective linear equivalence stays injective.
      exact
        LocalizedModule.map_injective
          (Submonoid.powers f)
          S.moduleCatCyclesIso.hom.hom
          ((ModuleCat.mono_iff_injective S.moduleCatCyclesIso.hom).1 inferInstance)
    · -- Localizing a surjective linear equivalence stays surjective.
      exact
        LocalizedModule.map_surjective
          (Submonoid.powers f)
          S.moduleCatCyclesIso.hom.hom
          ((ModuleCat.epi_iff_surjective S.moduleCatCyclesIso.hom).1 inferInstance)
  constructor
  · let eKernel :
        (R' ⊗[R] G) ≃ₗ[R'] (R' ⊗[R] LinearMap.ker S.g.hom) :=
        LinearEquiv.ofBijective ((S.moduleCatToCycles).baseChange R') hbaseBij
    let eCycles :
        (R' ⊗[R] S.cycles) ≃ₗ[R'] (R' ⊗[R] LinearMap.ker S.g.hom) :=
        LinearEquiv.ofBijective ((S.moduleCatCyclesIso.hom.hom).baseChange R') hcyclesBaseBij
    -- Transport flatness from the branch-flat source module across the two comparison
    -- equivalences to the public `cycles` replacement.
    exact Module.Flat.of_linearEquiv (eCycles.trans eKernel.symm)
  · let eKernel :
        Away f G ≃ₗ[Localization.Away f] Away f (LinearMap.ker S.g.hom) :=
        LinearEquiv.ofBijective
          (LocalizedModule.map (Submonoid.powers f) S.moduleCatToCycles)
          hlocalizedBij
    let eCycles :
        Away f S.cycles ≃ₗ[Localization.Away f] Away f (LinearMap.ker S.g.hom) :=
        LinearEquiv.ofBijective
          (LocalizedModule.map (Submonoid.powers f) S.moduleCatCyclesIso.hom.hom)
          hcyclesLocalizedBij
    -- The same comparison on the localized branch identifies `Away f S.cycles` with `Away f G`.
    exact Module.Flat.of_linearEquiv (eCycles.trans eKernel.symm)

/-- Helper for Lemma 15.91.18: if the canonical `H⁰(Cech)` replacement is flat, then the original
module is flat. -/
lemma flat_of_flat_cech_cycles_replacement
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f)
    (hflat :
      Module.Flat R ((beauvilleLaszloModuleCechSequence R' G f).cycles)) :
    Module.Flat R G := by
  let S := beauvilleLaszloModuleCechSequence R' G f
  let T : CategoryTheory.ShortComplex (ModuleCat R) :=
    CategoryTheory.ShortComplex.moduleCatMk
      (LinearMap.ker S.toCycles.hom).subtype
      S.toCycles.hom
      (by
        ext x
        exact x.2)
  have hT :
      T.ShortExact :=
    cech_replacement_shortExact_row
      (R := R) (R' := R') f hpair
  have hbaseShort :
      (T.map (tensorLeft (ModuleCat.of R R'))).ShortExact := by
    have hflatCoker : Module.Flat R T.X₃ := by
      simpa [T] using hflat
    let _ : Module.Flat R T.X₃ := hflatCoker
    -- Tensor the public kernel row with `R'` to keep exactness on the base-change branch.
    exact CategoryTheory.ShortComplex.ShortExact.tensorLeft_of_flat_cokernel hT (ModuleCat.of R R')
  have hbaseKerSub :
      Subsingleton (R' ⊗[R] LinearMap.ker S.toCycles.hom) := by
    -- Since the tensorized right map is bijective, exactness forces the tensorized kernel to be
    -- trivial.
    have hsub :
        Subsingleton (T.map (tensorLeft (ModuleCat.of R R'))).X₁ :=
      subsingleton_of_shortExact_of_injective_right
        (R := R)
        hbaseShort
        (by
          simpa [T, LinearMap.baseChange_eq_ltensor] using
            (cech_replacement_toCycles_baseChange_bijective
              (R := R) (R' := R') (G := G) f hpair).1)
    simpa [T] using hsub
  -- Route correction: the remaining source-faithful step is now only the localized kernel kill.
  -- One needs the localized public-map bijectivity from
  -- `cech_replacement_toCycles_localizedAway_bijective`, then the canonical localization-of-kernel
  -- identification to show `Away f (ker S.toCycles.hom)` is subsingleton, and finally Lemma
  -- `15.91.4` to force `ker S.toCycles.hom = 0`.
  -- TODO for Lemma 15.91.18: after the localized kernel is shown trivial, conclude that
  -- `S.toCycles.hom` is a linear equivalence and transport flatness from `S.cycles` back to `G`.
  sorry

/-- Helper for Lemma 15.91.18: in the glueable case, flatness on the `R'` and `R_f` branches
forces flatness over `R`. -/
lemma flat_of_glueable_of_branch_flatness
    (f : R)
    (hshort :
      (beauvilleLaszloModuleCechSequence R'
        ((beauvilleLaszloModuleCechSequence R' G f).cycles)
        f).ShortExact)
    (hflatTensor :
      Module.Flat R'
        (R' ⊗[R] (beauvilleLaszloModuleCechSequence R' G f).cycles))
    (hflatAway :
      Module.Flat (Localization.Away f)
        (Away f (beauvilleLaszloModuleCechSequence R' G f).cycles)) :
    Module.Flat R ((beauvilleLaszloModuleCechSequence R' G f).cycles) := by
  -- Route correction: once the replacement module is glueable, the remaining step is the source
  -- Tor argument on the short exact Beauville-Laszlo Cech row for that replacement.
  -- TODO for Lemma 15.91.18: prove `Tor₁^R(H⁰(Cech(M)), N) = 0` for every `N` by combining the
  -- ring Čech six-term Tor sequence with the branch-flatness hypotheses and then invoke the Tor
  -- flatness criterion.
  sorry

end ProofHelpers

/-- Lemma 15.91.18: for a Beauville-Laszlo glueing pair `(R → R', f)`, an `R`-module `M` is flat
if and only if its base change is flat over `R'` and its localization `LocalizedModule.Away f M`
is flat over `Localization.Away f`. In mathlib-facing form, the base change of the textbook module
`M ⊗_R R'` is written as `R' ⊗[R] M`. -/
lemma flat_iff_flat_tensor_and_localizedAway_of_beauvilleLaszloGlueingPair
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    Module.Flat R M ↔
      Module.Flat R' (R' ⊗[R] M) ∧
        Module.Flat (Localization.Away f) (Away f M) := by
  constructor
  · intro hflat
    constructor
    · let _ : Module.Flat R M := hflat
      -- Base change preserves flatness on the `R'` branch.
      simpa using (Module.Flat.baseChange (R := R) (S := R') (M := M))
    · -- The localization branch is the standard away-localization of a flat module.
      exact flat_localizedAway_of_flat (R := R) (M := M) f hflat
  · rintro ⟨hflatTensor, hflatAway⟩
    letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
    have hcycles :
        Module.Flat R' (R' ⊗[R] (beauvilleLaszloModuleCechSequence R' M f).cycles) ∧
          Module.Flat (Localization.Away f)
            (Away f (beauvilleLaszloModuleCechSequence R' M f).cycles) :=
      cech_cycles_branch_flatness
        (R := R) (R' := R') (G := M) f hpair hflatTensor hflatAway
    have hflatCycles :
        Module.Flat R ((beauvilleLaszloModuleCechSequence R' M f).cycles) := by
      -- First prove flatness for the canonical glueable replacement from Remark `15.91.17`.
      exact
        flat_of_glueable_of_branch_flatness
          (R := R) (R' := R') (G := M) f
          (beauvilleLaszloModuleCechH0_shortExact
            (R := R) (R' := R') (M := M) (f := f) hpair)
          hcycles.1
          hcycles.2
    -- Then compare the original module with that replacement.
    exact
      flat_of_flat_cech_cycles_replacement
        (R := R) (R' := R') (G := M) f hpair hflatCycles

end
