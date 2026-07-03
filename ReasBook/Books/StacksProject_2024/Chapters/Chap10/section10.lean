import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_10_1 (from Chap10) -/
universe uR u1 u2 u3 u4 u5

open Function LinearMap

/-
Lemma 10.10.1 lies in the module-theoretic exactness/Hom domain.

Layering for this file:
* `source-facing`: the two iff criteria expressing exactness of `M₁ ⟶ M₂ ⟶ M₃ ⟶ 0`
  and `0 ⟶ M₁ ⟶ M₂ ⟶ M₃` via the induced `Hom` sequences;
* `core/canonical`: the sampled owner declarations
  `LinearMap.exact_lcomp_of_exact_of_surjective`,
  `LinearMap.lcomp_injective_of_surjective`,
  `LinearMap.exact_of_comp_eq_zero_of_ker_le_range`,
  `Function.Exact.linearEquivOfSurjective`;
* `bridge/view`: the private helper lemmas below adapt those owner-level exactness patterns to the
  `R`-linear Hom spaces appearing in the source statement, still over an arbitrary ring `R`.
-/

variable {R : Type uR} [Ring R]
variable {M1 : Type u1} {M2 : Type u2} {M3 : Type u3}
variable [AddCommGroup M1] [AddCommGroup M2] [AddCommGroup M3]
variable [Module R M1] [Module R M2] [Module R M3]

private theorem exact_lcomp_hom_into_of_exact_of_surjective
    {N : Type u4} [AddCommGroup N] [Module R N]
    {f : M1 →ₗ[R] M2} {g : M2 →ₗ[R] M3}
    (hfg : Exact f g) (hg : Surjective g) :
    Exact (lcomp ℤ N g) (lcomp ℤ N f) := by
  rw [Exact]
  intro φ
  constructor
  · intro hφ
    refine ⟨((range f).liftQ φ (range_le_ker_iff.mpr hφ)).comp
        (hfg.linearEquivOfSurjective hg).symm.toLinearMap, ?_⟩
    ext x
    simp [Exact.linearEquivOfSurjective_symm_apply]
  · rintro ⟨ψ, rfl⟩
    ext x
    simp [lcomp_apply', hfg.linearMap_comp_eq_zero, LinearMap.comp_assoc]

private theorem exact_compRight_hom_from_of_injective_of_exact
    {N : Type u5} [AddCommGroup N] [Module R N]
    {f : M1 →ₗ[R] M2} {g : M2 →ₗ[R] M3}
    (hf : Injective f) (hfg : Exact f g) :
    let F : (N →ₗ[R] M1) →ₗ[ℤ] N →ₗ[R] M2 := compRight ℤ f
    let G : (N →ₗ[R] M2) →ₗ[ℤ] N →ₗ[R] M3 := compRight ℤ g
    Exact F G := by
  let fker : M1 →ₗ[R] ker g :=
    f.codRestrict (ker g) fun x ↦ by
      simpa [mem_ker] using hfg.apply_apply_eq_zero x
  have hfker : Bijective fker := by
    constructor
    · intro x y hxy
      exact hf (Subtype.ext_iff.mp hxy)
    · intro x
      obtain ⟨y, hy⟩ := (hfg x.1).mp x.2
      exact ⟨y, Subtype.ext hy⟩
  let e : M1 ≃ₗ[R] ker g := LinearEquiv.ofBijective fker hfker
  rw [Exact]
  intro φ
  constructor
  · intro hφ
    let φ' : N →ₗ[R] ker g :=
      φ.codRestrict (ker g) fun x ↦ by
        simpa [comp_apply, mem_ker] using LinearMap.congr_fun hφ x
    refine ⟨e.symm ∘ₗ φ', ?_⟩
    ext x
    exact congrArg Subtype.val (e.apply_symm_apply (φ' x))
  · rintro ⟨ψ, rfl⟩
    ext x
    exact hfg.apply_apply_eq_zero (ψ x)

/-- Lemma 10.10.1 (1): the sequence `M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` is exact if and only if for every
`R`-module `N` the induced sequence `0 ⟶ Hom_R(M₃, N) ⟶ Hom_R(M₂, N) ⟶ Hom_R(M₁, N)` is exact. -/
-- Proof sketch: the forward direction combines injectivity of precomposition by a surjection with
-- the standard left exactness of `Hom_R(-, N)`. For the converse, test the induced Hom-sequences
-- against `N = M₃` to get `g ∘ f = 0`, and against the quotient `M₂ / range(f)` to recover
-- `ker(g) ≤ range(f)`.
theorem exact_iff_exact_hom_into
    (f : M1 →ₗ[R] M2) (g : M2 →ₗ[R] M3) :
    (Exact f g ∧ Surjective g) ↔
      ∀ (N : Type (max u2 u3 u4)) [AddCommGroup N] [Module R N],
        Injective (lcomp ℤ N g) ∧ Exact (lcomp ℤ N g) (lcomp ℤ N f) := by
  constructor
  · rintro ⟨hfg, hg⟩ N _ _
    exact ⟨lcomp_injective_of_surjective g hg, exact_lcomp_hom_into_of_exact_of_surjective hfg hg⟩
  · intro h
    refine ⟨?_, ?_⟩
    · let eu : ULift.{max u2 u3 u4} M3 ≃ₗ[R] M3 := ULift.moduleEquiv
      let u : M3 →ₗ[R] ULift.{max u2 u3 u4} M3 := eu.symm.toLinearMap
      let q0 : M2 →ₗ[R] M2 ⧸ range f := Submodule.mkQ _
      let eq : ULift.{max u2 u3 u4} (M2 ⧸ range f) ≃ₗ[R] M2 ⧸ range f := ULift.moduleEquiv
      let q : M2 →ₗ[R] ULift.{max u2 u3 u4} (M2 ⧸ range f) := eq.symm ∘ₗ q0
      have hexact : Exact
          (lcomp ℤ (ULift.{max u2 u3 u4} (M2 ⧸ range f)) g)
          (lcomp ℤ (ULift.{max u2 u3 u4} (M2 ⧸ range f)) f) := by
        simpa using (h (ULift.{max u2 u3 u4} (M2 ⧸ range f))).2
      refine exact_of_comp_eq_zero_of_ker_le_range ?_ ?_
      · have hu : u.comp g ∈ Set.range (fun φ : M3 →ₗ[R] ULift.{max u2 u3 u4} M3 ↦
          φ.comp g) :=
          ⟨u, by ext x; rfl⟩
        have hzero : (u.comp g).comp f = 0 :=
          (h (ULift.{max u2 u3 u4} M3)).2 (u.comp g) |>.2 hu
        ext x
        exact eu.symm.injective <| by
          simpa [u, LinearMap.comp_assoc] using LinearMap.congr_fun hzero x
      · intro x hx
        have hx0 : g x = 0 := by
          simpa [LinearMap.mem_ker] using hx
        have hqf : q.comp f = 0 := by
          ext y
          simp [q, q0, eq]
        obtain ⟨φ, hφ⟩ := (hexact q).1 hqf
        have hqx : q x = 0 := by
          rw [← LinearMap.congr_fun hφ x]
          simp [hx0]
        have : q0 x = 0 := by
          exact eq.symm.injective <| by simpa [q, q0] using hqx
        simpa [q0] using (Submodule.Quotient.eq (range f)).mp this
    · let qg0 : M3 →ₗ[R] M3 ⧸ range g := Submodule.mkQ _
      let eg : ULift.{max u2 u3 u4} (M3 ⧸ range g) ≃ₗ[R] M3 ⧸ range g := ULift.moduleEquiv
      let qg : M3 →ₗ[R] ULift.{max u2 u3 u4} (M3 ⧸ range g) :=
        eg.symm ∘ₗ qg0
      have hqg : qg = 0 := by
        apply (h (ULift.{max u2 u3 u4} (M3 ⧸ range g))).1
        apply LinearMap.ext
        intro x
        exact eg.injective <| by simp [qg, qg0]
      have htop : range g = ⊤ := by
        rw [eq_top_iff]
        intro y hy
        have hqy : qg y = 0 := by
          simp [hqg]
        have : qg0 y = 0 := by
          exact eg.symm.injective <| by simpa [qg, qg0] using hqy
        simpa [qg0] using (Submodule.Quotient.eq (range g)).mp this
      exact range_eq_top.mp htop

/-- Lemma 10.10.1 (2): the sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃` is exact if and only if for every
`R`-module `N` the induced sequence `0 ⟶ Hom_R(N, M₁) ⟶ Hom_R(N, M₂) ⟶ Hom_R(N, M₃)` is exact. -/
-- Proof sketch: the forward direction is pointwise exactness after postcomposition. Conversely,
-- test at `N = M₁` to get `g ∘ f = 0`, and test at `N = ker(g)` to show every element of `ker(g)`
-- comes from `M₁`.
theorem exact_iff_exact_hom_from
    (f : M1 →ₗ[R] M2) (g : M2 →ₗ[R] M3) :
    (Injective f ∧ Exact f g) ↔
      ∀ (N : Type (max u1 u2 u5)) [AddCommGroup N] [Module R N],
        let F : (N →ₗ[R] M1) →ₗ[ℤ] N →ₗ[R] M2 := compRight ℤ f
        let G : (N →ₗ[R] M2) →ₗ[ℤ] N →ₗ[R] M3 := compRight ℤ g
        Injective F ∧ Exact F G := by
  constructor
  · rintro ⟨hf, hfg⟩ N _ _
    dsimp
    refine ⟨?_, ?_⟩
    · simpa using hf.injective_linearMapComp_left
    · exact exact_compRight_hom_from_of_injective_of_exact hf hfg
  · intro h
    refine ⟨?_, ?_⟩
    · let i0 : ker f →ₗ[R] M1 := (ker f).subtype
      let ei : ULift.{max u1 u2 u5} (ker f) ≃ₗ[R] ker f := ULift.moduleEquiv
      let i : ULift.{max u1 u2 u5} (ker f) →ₗ[R] M1 := i0.comp ei.toLinearMap
      have hi : i = 0 := by
        apply (h (ULift.{max u1 u2 u5} (ker f))).1
        ext x
        simp [i, i0]
      intro x y hxy
      have hz : x - y = 0 := by
        have : i (ULift.up ⟨x - y, by simp [mem_ker, map_sub, hxy]⟩) = 0 := by
          simp [hi, i, i0]
        simpa [ei, i, i0] using this
      exact sub_eq_zero.mp hz
    let ed : ULift.{max u1 u2 u5} M1 ≃ₗ[R] M1 := ULift.moduleEquiv
    let d : ULift.{max u1 u2 u5} M1 →ₗ[R] M1 := ed.toLinearMap
    let i0 : ker g →ₗ[R] M2 := (ker g).subtype
    let ei : ULift.{max u1 u2 u5} (ker g) ≃ₗ[R] ker g := ULift.moduleEquiv
    let i : ULift.{max u1 u2 u5} (ker g) →ₗ[R] M2 := i0.comp ei.toLinearMap
    refine exact_of_comp_eq_zero_of_ker_le_range ?_ ?_
    · have hf' : f.comp d ∈ Set.range (fun φ : ULift.{max u1 u2 u5} M1 →ₗ[R] M1 ↦
        f.comp φ) :=
        ⟨d, by ext x; rfl⟩
      have hzero : g.comp (f.comp d) = 0 :=
        (h (ULift.{max u1 u2 u5} M1)).2 (f.comp d) |>.2 hf'
      ext x
      simpa [d, ed, LinearMap.comp_assoc] using
        LinearMap.congr_fun hzero (ULift.up x)
    · intro x hx
      have hexact : Exact
          ((compRight ℤ f :
            (ULift.{max u1 u2 u5} (ker g) →ₗ[R] M1) →ₗ[ℤ]
              ULift.{max u1 u2 u5} (ker g) →ₗ[R] M2))
          ((compRight ℤ g :
            (ULift.{max u1 u2 u5} (ker g) →ₗ[R] M2) →ₗ[ℤ]
              ULift.{max u1 u2 u5} (ker g) →ₗ[R] M3)) := by
        simpa using (h (ULift.{max u1 u2 u5} (ker g))).2
      have hi : g.comp i = 0 := by
        ext y
        simp [i, i0]
      obtain ⟨φ, hφ⟩ := (hexact i).1 hi
      refine ⟨φ (ULift.up ⟨x, hx⟩), ?_⟩
      have hx' : f (φ (ULift.up ⟨x, hx⟩)) = ((⟨x, hx⟩ : ker g) : M2) := by
        simpa [ei, i, i0] using LinearMap.congr_fun hφ (ULift.up ⟨x, hx⟩)
      exact hx'

/-! ### Lemma_10_10_2 (from Chap10) -/
universe u v w

section

variable {R : Type u} [CommRing R]
variable {M : Type v} {N : Type w}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

/-
Lemma 10.10.2 is `source-facing` but bridge-shaped in the localization/Hom domain. The primitive
owner abstractions are `Module.FinitePresentation.linearEquivMapExtendScalars` for localizing
`Hom_R(M, N)` with `M` finitely presented and `LinearMap.extendScalarsOfIsLocalizationEquiv` for
forgetting no-longer-essential `Localization S`-linearity on already localized modules. The
textbook clauses are the `Localization S`-linear and away-localization specializations of those
owners. -/

/- Owner recall for clauses `(3)` and `(1)`: localizing `Hom_R(M, N)` commutes with `Hom` out of a
finitely presented module. -/
recall Module.FinitePresentation.linearEquivMapExtendScalars

section

variable [Module.FinitePresentation R M]

variable (S : Submonoid R)

/- Lemma 10.10.2 (3): for a finitely presented `R`-module `M` and any multiplicative subset
`S ⊆ R`, the localization of `Hom_R(M, N)` is canonically identified with the module of
`Localization S`-linear maps `S⁻¹M → S⁻¹N`. This is the `Localization S`-linear upgrade of the
owner comparison `Module.FinitePresentation.linearEquivMapExtendScalars`. -/
#check
  (LinearEquiv.extendScalarsOfIsLocalization S (Localization S)
      (Module.FinitePresentation.linearEquivMapExtendScalars S) :
    LocalizedModule S (M →ₗ[R] N) ≃ₗ[Localization S]
      (LocalizedModule S M →ₗ[Localization S] LocalizedModule S N))

/- Lemma 10.10.2 (1): for `f ∈ R`, the localization of `Hom_R(M, N)` away from `f` is the away
specialization of the previous `Localization S`-linear comparison. -/
variable (f : R)

#check
  (LinearEquiv.extendScalarsOfIsLocalization (Submonoid.powers f) (Localization.Away f)
      (Module.FinitePresentation.linearEquivMapExtendScalars (Submonoid.powers f)) :
    LocalizedModule.Away f (M →ₗ[R] N) ≃ₗ[Localization.Away f]
      (LocalizedModule.Away f M →ₗ[Localization.Away f] LocalizedModule.Away f N))

end

/- Owner recall for clauses `(4)` and `(2)`: once source and target already carry the localized
module structure, `R`-linear maps and `Localization S`-linear maps are canonically equivalent. -/
recall LinearMap.extendScalarsOfIsLocalizationEquiv

/- Lemma 10.10.2 (4): `Localization S`-linear maps between localized modules are canonically the
same as `R`-linear maps between those localized modules. This is the inverse orientation of
`LinearMap.extendScalarsOfIsLocalizationEquiv`. -/
variable (S : Submonoid R)

#check
  ((LinearMap.extendScalarsOfIsLocalizationEquiv S (Localization S)).symm :
    (LocalizedModule S M →ₗ[Localization S] LocalizedModule S N) ≃ₗ[Localization S]
      (LocalizedModule S M →ₗ[R] LocalizedModule S N))

/- Lemma 10.10.2 (2): for `f ∈ R`, `R_f`-linear maps `M_f → N_f` are canonically the same as
`R`-linear maps `M_f → N_f`. This is the away-localization specialization of the previous
canonical equivalence. -/
variable (f : R)

#check
  ((LinearMap.extendScalarsOfIsLocalizationEquiv (Submonoid.powers f) (Localization.Away f)).symm :
    (LocalizedModule.Away f M →ₗ[Localization.Away f] LocalizedModule.Away f N) ≃ₗ[Localization.Away f]
      (LocalizedModule.Away f M →ₗ[R] LocalizedModule.Away f N))

end
