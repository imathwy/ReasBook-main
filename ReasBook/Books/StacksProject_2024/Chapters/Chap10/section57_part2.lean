import Mathlib
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.Data.Finset.Card
import Mathlib.Order.Preorder.Finite
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_57_5 (from Chap10) -/
open AlgebraicGeometry ProjectiveSpectrum LocalizedModule HomogeneousLocalization
open scoped DirectSum

universe u v w

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M]
variable (𝒜 : ℕ → Submodule R S) (ℳ : ℕ → Submodule R M)
variable [GradedAlgebra 𝒜] [SetLike.GradedSMul 𝒜 ℳ]

attribute [local instance] RingHomInvPair.of_ringEquiv

/- Domain triage: this file lies in graded commutative algebra on `Proj`.
The ring-side owner abstraction is `Proj.isLocalization_atPrime`, and the module-side objects are
the degree-zero submodules cut out inside ordinary localizations. The source-facing content here is
the bridge from the basic-open localization `M_(f)` to the intrinsic localization `M_(x)`, not a
new ambient owner for projective localizations. -/

/- Lemma 10.57.5, ring half: for `x ∈ D₊(f)` with `f` homogeneous of positive degree, the ring
`S_(x)` is the localization of `S_(f)` at the corresponding prime of `Spec(S_(f))`. This is the
canonical mathlib theorem `Proj.isLocalization_atPrime`. -/
recall Proj.isLocalization_atPrime

private def atPrimeDegreeZeroPartSet (I : Ideal S) [I.IsPrime] :
    Set (LocalizedModule I.primeCompl M) :=
  { z | ∃ i, ∃ m : ℳ i, ∃ s : 𝒜 i, ∃ hs : (s : S) ∉ I,
      z = LocalizedModule.mk (m : M) ⟨(s : S), hs⟩ }

omit [SetLike.GradedSMul 𝒜 ℳ] in
private theorem atPrimeDegreeZeroPartSet_zero_mem (I : Ideal S) [I.IsPrime] :
    0 ∈ atPrimeDegreeZeroPartSet 𝒜 ℳ I := by
  refine ⟨0, 0, 1, ?_, ?_⟩
  · simpa [Ideal.ne_top_iff_one] using (Ideal.IsPrime.ne_top (show I.IsPrime from inferInstance))
  simp

private theorem atPrimeDegreeZeroPartSet_add_mem (I : Ideal S) [I.IsPrime]
    {x y : LocalizedModule I.primeCompl M}
    (hx : x ∈ atPrimeDegreeZeroPartSet 𝒜 ℳ I)
    (hy : y ∈ atPrimeDegreeZeroPartSet 𝒜 ℳ I) :
    x + y ∈ atPrimeDegreeZeroPartSet 𝒜 ℳ I := by
  rcases hx with ⟨i, m, s, hsI, rfl⟩
  rcases hy with ⟨j, m', t, htI, rfl⟩
  refine ⟨i + j, ⟨(t : S) • (m : M) + (s : S) • (m' : M), ?_⟩,
    ⟨(s : S) * t, SetLike.mul_mem_graded s.2 t.2⟩, I.primeCompl.mul_mem hsI htI, ?_⟩
  · refine add_mem ?_ ?_
    · simpa [Nat.add_comm] using SetLike.GradedSMul.smul_mem t.2 m.2
    · simpa using SetLike.GradedSMul.smul_mem s.2 m'.2
  · rw [LocalizedModule.mk_add_mk]
    change LocalizedModule.mk ((t : S) • (m : M) + (s : S) • (m' : M))
        (⟨(s : S), hsI⟩ * ⟨(t : S), htI⟩) =
      LocalizedModule.mk ((t : S) • (m : M) + (s : S) • (m' : M))
        ⟨(s : S) * t, I.primeCompl.mul_mem hsI htI⟩
    rfl

private noncomputable instance atPrimeLocalizedModuleModule (I : Ideal S) [I.IsPrime] :
    Module (HomogeneousLocalization.AtPrime 𝒜 I) (LocalizedModule I.primeCompl M) :=
  Module.compHom (LocalizedModule I.primeCompl M)
    (algebraMap (HomogeneousLocalization.AtPrime 𝒜 I) (Localization I.primeCompl))

private theorem atPrimeDegreeZeroPartSet_smul_mem (I : Ideal S) [I.IsPrime]
    (z : HomogeneousLocalization.AtPrime 𝒜 I) {x : LocalizedModule I.primeCompl M}
    (hx : x ∈ atPrimeDegreeZeroPartSet 𝒜 ℳ I) :
    z • x ∈ atPrimeDegreeZeroPartSet 𝒜 ℳ I := by
  rcases hx with ⟨i, m, s, hsI, rfl⟩
  obtain ⟨⟨j, a, b, hbI⟩, rfl⟩ := HomogeneousLocalization.mk_surjective z
  refine ⟨j + i, ⟨(a : S) • (m : M), ?_⟩, ⟨(b : S) * s, SetLike.mul_mem_graded b.2 s.2⟩,
    I.primeCompl.mul_mem hbI hsI, ?_⟩
  · simpa using SetLike.GradedSMul.smul_mem a.2 m.2
  · change (algebraMap (HomogeneousLocalization.AtPrime 𝒜 I) (Localization I.primeCompl)
        (HomogeneousLocalization.mk ⟨j, a, b, hbI⟩)) •
        LocalizedModule.mk (m : M) ⟨(s : S), hsI⟩ =
      LocalizedModule.mk ((a : S) • (m : M)) ⟨(b : S) * s, I.primeCompl.mul_mem hbI hsI⟩
    rw [HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.val_mk,
      LocalizedModule.mk_smul_mk]
    rfl

/-- The intrinsic homogeneous localization `M_(x)` of a graded module `M` at a homogeneous prime
ideal `I`, realized as the degree-zero part of the ordinary localization `M_I`. -/
noncomputable def atPrimeDegreeZeroPart (I : Ideal S) [I.IsPrime] :
    Submodule (HomogeneousLocalization.AtPrime 𝒜 I) (LocalizedModule I.primeCompl M) :=
  { carrier := atPrimeDegreeZeroPartSet 𝒜 ℳ I
    zero_mem' := atPrimeDegreeZeroPartSet_zero_mem 𝒜 ℳ I
    add_mem' := atPrimeDegreeZeroPartSet_add_mem 𝒜 ℳ I
    smul_mem' := atPrimeDegreeZeroPartSet_smul_mem 𝒜 ℳ I }

private noncomputable instance awayAtPrimeAlgebra {d : ℕ} (f : 𝒜 d)
    (x : Proj.basicOpen 𝒜 (f : S)) :
    Algebra (Away 𝒜 (f : S))
      (HomogeneousLocalization.AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal) :=
  (mapId 𝒜 (Submonoid.powers_le.mpr x.2)).toAlgebra

private noncomputable instance awayAtPrimeLocalizedModuleModule {d : ℕ} (f : 𝒜 d)
    (x : Proj.basicOpen 𝒜 (f : S)) :
    Module (Away 𝒜 (f : S))
      (LocalizedModule x.1.asHomogeneousIdeal.toIdeal.primeCompl M) :=
  Module.compHom (LocalizedModule x.1.asHomogeneousIdeal.toIdeal.primeCompl M)
    (algebraMap (Away 𝒜 (f : S))
      (HomogeneousLocalization.AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal))

private instance awayAtPrimeLocalizedModuleIsScalarTower {d : ℕ} (f : 𝒜 d)
    (x : Proj.basicOpen 𝒜 (f : S)) :
    IsScalarTower (Away 𝒜 (f : S))
      (HomogeneousLocalization.AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal)
      (LocalizedModule x.1.asHomogeneousIdeal.toIdeal.primeCompl M) where
  smul_assoc r s m := by
    change (algebraMap (Away 𝒜 (f : S))
        (HomogeneousLocalization.AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal) r * s) • m =
      algebraMap (Away 𝒜 (f : S))
        (HomogeneousLocalization.AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal) r • s • m
    rw [mul_smul]

/-- The explicit comparison map on the ambient localizations `M[f⁻¹] → M_I`, where
`I = x.asHomogeneousIdeal.toIdeal`. This is the `bridge/view` map obtained from the inclusion of
submonoids `powers f ⊆ Iᶜ`. -/
private noncomputable def awayAtPrimeLinearMap {d : ℕ} (f : 𝒜 d)
    (x : Proj.basicOpen 𝒜 (f : S)) :
    LocalizedModule.Away (f : S) M →ₗ[Away 𝒜 (f : S)]
      LocalizedModule x.1.asHomogeneousIdeal.toIdeal.primeCompl M :=
  let I := x.1.asHomogeneousIdeal.toIdeal
  let P := I.primeCompl
  let l :
      LocalizedModule.Away (f : S) M →ₗ[S] LocalizedModule P M :=
    LocalizedModule.liftOfLE (Submonoid.powers (f : S)) P (Submonoid.powers_le.mpr x.2)
  { toFun := l
    map_add' := l.map_add
    map_smul' := by
      intro z y
      obtain ⟨k, a, ha, rfl⟩ := Away.mk_surjective 𝒜 f.2 z
      induction y using LocalizedModule.induction_on with
      | _ m s =>
          change l ((algebraMap (Away 𝒜 (f : S)) (Localization.Away (f : S))
              (Away.mk 𝒜 f.2 k a ha)) • LocalizedModule.mk m s) =
            (algebraMap (Away 𝒜 (f : S))
              (HomogeneousLocalization.AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal)
              (Away.mk 𝒜 f.2 k a ha)) • l (LocalizedModule.mk m s)
          rw [HomogeneousLocalization.algebraMap_apply, Away.val_mk, LocalizedModule.mk_smul_mk]
          have hsI : (s : S) ∈ P := by
            rcases s.2 with ⟨n, hn⟩
            simpa [P, hn] using (show (f : S) ^ n ∈ P from Submonoid.pow_mem P x.2 n)
          have hkI : (f : S) ^ k ∈ P := by
            exact Submonoid.pow_mem P x.2 k
          let fkI : P := ⟨(f : S) ^ k, hkI⟩
          let sI : P := ⟨(s : S), hsI⟩
          let t : P := fkI * sI
          have ht :
              (⟨↑(⟨(f : S) ^ k, by exact ⟨k, rfl⟩⟩ * s),
                mul_mem hkI hsI⟩ : P) = t := by
            ext
            simp [t, fkI, sI]
          have hleft :
              l (LocalizedModule.mk ((a : S) • m) (⟨(f : S) ^ k, by exact ⟨k, rfl⟩⟩ * s)) =
                IsLocalizedModule.mk'
                  (LocalizedModule.mkLinearMap P M) ((a : S) • m) t := by
            simpa [t] using
              (show l (LocalizedModule.mk ((a : S) • m) (⟨(f : S) ^ k, by exact ⟨k, rfl⟩⟩ * s)) =
                  IsLocalizedModule.mk'
                    (LocalizedModule.mkLinearMap P M) ((a : S) • m)
                    (⟨↑(⟨(f : S) ^ k, by exact ⟨k, rfl⟩⟩ * s), mul_mem hkI hsI⟩ : P) by
                simp only [l, IsLocalizedModule.mk_eq_mk', IsLocalizedModule.liftOfLE_mk', ht])
          have hright :
              (algebraMap (Away 𝒜 (f : S))
                  (HomogeneousLocalization.AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal)
                  (Away.mk 𝒜 f.2 k a ha)) • l (LocalizedModule.mk m s) =
                IsLocalizedModule.mk'
                  (LocalizedModule.mkLinearMap P M) ((a : S) • m) t := by
            rw [show l (LocalizedModule.mk m s) =
                IsLocalizedModule.mk'
                  (LocalizedModule.mkLinearMap P M) m sI by
                  simp only [l, IsLocalizedModule.mk_eq_mk', IsLocalizedModule.liftOfLE_mk', sI]]
            change
              (HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr x.2)
                  (Away.mk 𝒜 f.2 k a ha)) •
                IsLocalizedModule.mk' (LocalizedModule.mkLinearMap P M) m sI =
              IsLocalizedModule.mk' (LocalizedModule.mkLinearMap P M) ((a : S) • m) t
            rw [show HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr x.2)
                (Away.mk 𝒜 f.2 k a ha) =
                  HomogeneousLocalization.mk
                    ⟨k * d, ⟨a, ha⟩,
                      ⟨(f : S) ^ k,
                        by simpa [nsmul_eq_mul] using SetLike.pow_mem_graded k f.2⟩,
                      hkI⟩ by
                  rfl]
            change
              (algebraMap (HomogeneousLocalization.AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal)
                  (Localization P)
                  (HomogeneousLocalization.mk
                    ⟨k * d, ⟨a, ha⟩,
                      ⟨(f : S) ^ k,
                        by simpa [nsmul_eq_mul] using SetLike.pow_mem_graded k f.2⟩,
                      hkI⟩)) •
                IsLocalizedModule.mk' (LocalizedModule.mkLinearMap P M) m sI =
              IsLocalizedModule.mk' (LocalizedModule.mkLinearMap P M) ((a : S) • m) t
            rw [HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.val_mk,
              Localization.mk_eq_mk']
            change
              IsLocalization.mk' (Localization P) (a : S) fkI •
                IsLocalizedModule.mk' (LocalizedModule.mkLinearMap P M) m sI =
              IsLocalizedModule.mk' (LocalizedModule.mkLinearMap P M) ((a : S) • m) (fkI * sI)
            simpa [t] using
              (IsLocalizedModule.mk'_smul_mk'
                (Localization P) (LocalizedModule.mkLinearMap P M) (a : S) m fkI sI)
          exact hleft.trans hright.symm }

private theorem awayAtPrimeLinearMap_mem_atPrimeDegreeZeroPart {d : ℕ} (f : 𝒜 d)
    (x : Proj.basicOpen 𝒜 (f : S)) {z : LocalizedModule.Away (f : S) M}
    (hz : z ∈ awayDegreeZeroPart 𝒜 ℳ f) :
    awayAtPrimeLinearMap 𝒜 f x z ∈ atPrimeDegreeZeroPart 𝒜 ℳ x.1.asHomogeneousIdeal.toIdeal := by
  let I := x.1.asHomogeneousIdeal.toIdeal
  let P := I.primeCompl
  rcases (mem_awayDegreeZeroPart_iff 𝒜 ℳ f).1 hz with ⟨n, m, rfl⟩
  refine ⟨n * d, m, ⟨(f : S) ^ n, by simpa [nsmul_eq_mul] using SetLike.pow_mem_graded n f.2⟩,
    (show (f : S) ^ n ∈ P from Submonoid.pow_mem P x.2 n), ?_⟩
  dsimp [awayAtPrimeLinearMap]
  simp only [IsLocalizedModule.mk_eq_mk',
    IsLocalizedModule.liftOfLE_mk']

/-- The explicit source-facing comparison map `M_(f) → M_(x)` in Lemma 10.57.5, obtained by
restricting the ambient localization map `M[f⁻¹] → M_I` to degree-zero parts. This is the
`bridge/view` layer; the owner statement is that this map is localization at the prime of
`Spec(S_(f))`. -/
noncomputable def awayDegreeZeroPartToAtPrimeDegreeZeroPart {d : ℕ} (f : 𝒜 d)
    (x : Proj.basicOpen 𝒜 (f : S)) :
    awayDegreeZeroPart 𝒜 ℳ f →ₗ[Away 𝒜 (f : S)]
      (atPrimeDegreeZeroPart 𝒜 ℳ x.1.asHomogeneousIdeal.toIdeal).restrictScalars
        (Away 𝒜 (f : S)) :=
  ((awayAtPrimeLinearMap 𝒜 f x).domRestrict (awayDegreeZeroPart 𝒜 ℳ f)).codRestrict
    ((atPrimeDegreeZeroPart 𝒜 ℳ x.1.asHomogeneousIdeal.toIdeal).restrictScalars
      (Away 𝒜 (f : S))) fun z ↦ awayAtPrimeLinearMap_mem_atPrimeDegreeZeroPart 𝒜 ℳ f x z.2

/-- Helper for Lemma 10.57.5: a homogeneous element whose numerator avoids the homogeneous prime
behind `x` yields the powered denominator `s^deg(f) / f^i` in the corresponding prime complement of
`Spec(S_(f))`. -/
private theorem away_mk_mem_base_prime_compl {d i : ℕ} (f : 𝒜 d)
    (x : Proj.basicOpen 𝒜 (f : S)) (s : 𝒜 i)
    (hs : (s : S) ∉ x.1.asHomogeneousIdeal.toIdeal) :
    Away.mk 𝒜 f.2 i ((s : S) ^ d)
      (by
        simpa [nsmul_eq_mul, Nat.mul_comm] using SetLike.pow_mem_graded d s.2) ∈
      (((Proj.toSpec 𝒜 (f : S)).base x).asIdeal.primeCompl) := by
  -- Rewrite membership in the prime complement through the ring-side `Proj.toSpec` criterion.
  refine (Proj.mk_mem_toSpec_base_apply (𝒜 := 𝒜) (x := x)
    ⟨i * d, ⟨(s : S) ^ d, by
        simpa [nsmul_eq_mul, Nat.mul_comm] using SetLike.pow_mem_graded d s.2⟩,
      ⟨(f : S) ^ i, by
      simpa [nsmul_eq_mul] using SetLike.pow_mem_graded i f.2⟩, ⟨_, rfl⟩⟩).not.mpr ?_
  exact x.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hs d

/-- Helper for Lemma 10.57.5: any scalar outside the homogeneous prime behind `x` has a
homogeneous component that also lies outside that prime. -/
private theorem exists_homogeneous_component_not_mem {d : ℕ} (f : 𝒜 d)
    (x : Proj.basicOpen 𝒜 (f : S)) {c : S}
    (hc : c ∉ x.1.asHomogeneousIdeal.toIdeal) :
    ∃ i : ℕ, ((DirectSum.decompose 𝒜 c i : 𝒜 i) : S) ∉ x.1.asHomogeneousIdeal.toIdeal := by
  -- The homogeneous ideal membership criterion reduces non-membership to one escaping component.
  exact not_forall.mp
    ((Ideal.IsHomogeneous.mem_iff (𝒜 := 𝒜)
      (I := x.1.asHomogeneousIdeal.toIdeal)
      x.1.asHomogeneousIdeal.isHomogeneous).not.mp hc)

/-- Helper for Lemma 10.57.5: on a standard homogeneous fraction `m / f^n`, the comparison map
to the prime localization is the obvious ambient localization map. -/
private theorem awayDegreeZeroPartToAtPrimeDegreeZeroPart_val_mk {d n : ℕ} (f : 𝒜 d)
    (x : Proj.basicOpen 𝒜 (f : S)) {m : M} (hm : m ∈ ℳ (n * d)) :
    (((awayDegreeZeroPartToAtPrimeDegreeZeroPart 𝒜 ℳ f x)
      ⟨LocalizedModule.mk m ⟨(f : S) ^ n, by exact ⟨n, rfl⟩⟩,
        awayDegreeZeroPart_mk_mem (𝒜 := 𝒜) (ℳ := ℳ) f hm⟩).1 :
      LocalizedModule x.1.asHomogeneousIdeal.toIdeal.primeCompl M) =
        LocalizedModule.mk m
          ⟨(f : S) ^ n,
            x.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem
              (show (f : S) ∈ x.1.asHomogeneousIdeal.toIdeal.primeCompl from x.2) n⟩ := by
  -- Unfold the restricted map and simplify the ambient localization morphism on this generator.
  dsimp [awayDegreeZeroPartToAtPrimeDegreeZeroPart, awayAtPrimeLinearMap]
  simp only [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.liftOfLE_mk']

/-- Helper for Lemma 10.57.5: equality of two standard generators after comparison can be cleared
by a denominator outside the homogeneous prime in the ambient localization. -/
private theorem exists_prime_compl_smul_eq_of_comparison_eq {d a b : ℕ} (f : 𝒜 d)
    (x : Proj.basicOpen 𝒜 (f : S))
    {m₁ : ℳ (a * d)} {m₂ : ℳ (b * d)}
    (h :
      awayDegreeZeroPartToAtPrimeDegreeZeroPart 𝒜 ℳ f x
          ⟨LocalizedModule.mk (m₁ : M) ⟨(f : S) ^ a, by exact ⟨a, rfl⟩⟩,
            awayDegreeZeroPart_mk_mem (𝒜 := 𝒜) (ℳ := ℳ) f m₁.2⟩ =
        awayDegreeZeroPartToAtPrimeDegreeZeroPart 𝒜 ℳ f x
          ⟨LocalizedModule.mk (m₂ : M) ⟨(f : S) ^ b, by exact ⟨b, rfl⟩⟩,
            awayDegreeZeroPart_mk_mem (𝒜 := 𝒜) (ℳ := ℳ) f m₂.2⟩) :
    ∃ c : x.1.asHomogeneousIdeal.toIdeal.primeCompl,
      c • ((f : S) ^ b • (m₁ : M)) = c • ((f : S) ^ a • (m₂ : M)) := by
  -- Forget the subtype and use the standard equality criterion in the ambient localized module.
  apply_fun Subtype.val at h
  rw [awayDegreeZeroPartToAtPrimeDegreeZeroPart_val_mk (𝒜 := 𝒜) (ℳ := ℳ) (f := f) (x := x) m₁.2,
    awayDegreeZeroPartToAtPrimeDegreeZeroPart_val_mk (𝒜 := 𝒜) (ℳ := ℳ) (f := f) (x := x) m₂.2] at h
  simpa [Submonoid.smul_def, smul_smul, mul_assoc] using LocalizedModule.mk_eq.mp h

/-- Helper for Lemma 10.57.5: every element of `M_(x)` becomes the image of an element of `M_(f)`
after multiplying by a denominator from the corresponding prime complement of `Spec(S_(f))`. -/
private theorem atPrimeDegreeZeroPart_exists_smul_eq_image {d : ℕ} (f : 𝒜 d)
    (hd : 0 < d) (x : Proj.basicOpen 𝒜 (f : S))
    (z : (atPrimeDegreeZeroPart 𝒜 ℳ x.1.asHomogeneousIdeal.toIdeal).restrictScalars
      (Away 𝒜 (f : S))) :
    ∃ y : awayDegreeZeroPart 𝒜 ℳ f,
      ∃ u : (((Proj.toSpec 𝒜 (f : S)).base x).asIdeal.primeCompl),
        u • z = awayDegreeZeroPartToAtPrimeDegreeZeroPart 𝒜 ℳ f x y := by
  rcases z with ⟨z, ⟨i, m, s, hs, rfl⟩⟩
  rcases Nat.exists_eq_succ_of_ne_zero hd.ne' with ⟨k, rfl⟩
  let I := x.1.asHomogeneousIdeal.toIdeal
  let P := I.primeCompl
  let sI : P := ⟨(s : S), hs⟩
  let fi : Submonoid.powers (f : S) := ⟨(f : S) ^ i, ⟨i, rfl⟩⟩
  let fiP : P := ⟨(f : S) ^ i, Submonoid.pow_mem P x.2 i⟩
  have hs_pow_mem : ((s : S) ^ (k + 1)) ∈ 𝒜 (i * (k + 1)) := by
    simpa [nsmul_eq_mul, Nat.mul_comm] using SetLike.pow_mem_graded (k + 1) s.2
  have hsmul_mem : ((s : S) ^ k • (m : M)) ∈ ℳ (i * (k + 1)) := by
    -- The inverse formula keeps the numerator homogeneous of degree `deg(s) * deg(f)`.
    have hsmul := SetLike.GradedSMul.smul_mem
      (SetLike.pow_mem_graded k s.2) m.2
    have hsmul' : ((s : S) ^ k • (m : M)) ∈ ℳ (i + i * k) := by
      simpa [nsmul_eq_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
        add_comm, add_left_comm, add_assoc] using hsmul
    have hdeg : i + i * k = i * (k + 1) := by
      rw [Nat.mul_succ, Nat.add_comm]
    exact hdeg ▸ hsmul'
  let y : awayDegreeZeroPart 𝒜 ℳ f :=
    ⟨LocalizedModule.mk (((s : S) ^ k) • (m : M)) fi,
      awayDegreeZeroPart_mk_mem (𝒜 := 𝒜) (ℳ := ℳ) (f := f) hsmul_mem⟩
  let u : (((Proj.toSpec 𝒜 (f : S)).base x).asIdeal.primeCompl) :=
    ⟨Away.mk 𝒜 f.2 i ((s : S) ^ (k + 1)) hs_pow_mem,
      away_mk_mem_base_prime_compl (𝒜 := 𝒜) (f := f) (x := x) s hs⟩
  refine ⟨y, u, ?_⟩
  apply Subtype.ext
  change
    (algebraMap (Away 𝒜 (f : S))
        (HomogeneousLocalization.AtPrime 𝒜 I) (u : Away 𝒜 (f : S))) •
      LocalizedModule.mk (m : M) sI =
    awayAtPrimeLinearMap 𝒜 f x (y : LocalizedModule.Away (f : S) M)
  dsimp [u, y, fi, fiP, sI]
  -- Rewrite both sides as standard fractions in the ambient localization `M_I`.
  change
    (HomogeneousLocalization.mapId (𝒜 := 𝒜) (P := Submonoid.powers (f : S)) (Q := P)
        (Submonoid.powers_le.mpr x.2)
        (Away.mk 𝒜 f.2 i ((s : S) ^ (k + 1)) hs_pow_mem)).val •
      LocalizedModule.mk (m : M) sI =
    awayAtPrimeLinearMap 𝒜 f x
      (LocalizedModule.mk (((s : S) ^ k) • (m : M))
        (⟨(f : S) ^ i, ⟨i, rfl⟩⟩ : Submonoid.powers (f : S)))
  rw [show HomogeneousLocalization.mapId (𝒜 := 𝒜) (P := Submonoid.powers (f : S)) (Q := P)
      (Submonoid.powers_le.mpr x.2)
      (Away.mk 𝒜 f.2 i ((s : S) ^ (k + 1)) hs_pow_mem) =
        HomogeneousLocalization.mk
          ⟨i * (k + 1), ⟨(s : S) ^ (k + 1), hs_pow_mem⟩,
            ⟨(f : S) ^ i, by simpa [nsmul_eq_mul] using SetLike.pow_mem_graded i f.2⟩,
            fiP.2⟩ by
      rfl]
  rw [HomogeneousLocalization.val_mk, Localization.mk_eq_mk']
  rw [show LocalizedModule.mk (m : M) sI =
      IsLocalizedModule.mk' (LocalizedModule.mkLinearMap P M) (m : M) sI by
      rw [IsLocalizedModule.mk_eq_mk']]
  rw [show IsLocalization.mk' (Localization P) ((s : S) ^ (k + 1)) fiP •
      IsLocalizedModule.mk' (LocalizedModule.mkLinearMap P M) (m : M) sI =
        IsLocalizedModule.mk' (LocalizedModule.mkLinearMap P M)
          (((s : S) ^ (k + 1)) • (m : M)) (fiP * sI) by
      simpa using
        (IsLocalizedModule.mk'_smul_mk' (A := Localization P)
          (f := LocalizedModule.mkLinearMap P M) ((s : S) ^ (k + 1)) (m : M) fiP sI)]
  dsimp [awayAtPrimeLinearMap]
  simp only [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.liftOfLE_mk']
  -- Clear the common denominator `f^i`; the remaining identity is the source-textbook formula.
  apply (IsLocalizedModule.mk'_eq_mk'_iff (f := LocalizedModule.mkLinearMap P M)
    (((s : S) ^ (k + 1)) • (m : M)) (((s : S) ^ k) • (m : M)) (fiP * sI) fiP).2
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, smul_smul]
  congr 1
  dsimp [sI, fiP]
  rw [pow_succ, mul_assoc]
  rw [mul_comm (s : S) ((s : S) ^ k)]

/-- Helper for Lemma 10.57.5: denominators from the corresponding prime complement of `Spec(S_(f))`
act invertibly on `M_(x)` because `M_(x)` is a module over the localized ring `S_(x)`. -/
private theorem awayDegreeZeroPartToAtPrimeDegreeZeroPart_map_units {d : ℕ} (f : 𝒜 d)
    (hd : 0 < d) (x : Proj.basicOpen 𝒜 (f : S))
    (u : (((Proj.toSpec 𝒜 (f : S)).base x).asIdeal.primeCompl)) :
    IsUnit (algebraMap (Away 𝒜 (f : S))
      (Module.End (Away 𝒜 (f : S))
        ((atPrimeDegreeZeroPart 𝒜 ℳ x.1.asHomogeneousIdeal.toIdeal).restrictScalars
          (Away 𝒜 (f : S)))) u) := by
  let A := HomogeneousLocalization.AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal
  let N := (atPrimeDegreeZeroPart 𝒜 ℳ x.1.asHomogeneousIdeal.toIdeal).restrictScalars
    (Away 𝒜 (f : S))
  letI : IsLocalization (((Proj.toSpec 𝒜 (f : S)).base x).asIdeal.primeCompl) A :=
    Proj.isLocalization_atPrime 𝒜 (f : S) x f.2 hd
  letI : IsLocalizedModule (((Proj.toSpec 𝒜 (f : S)).base x).asIdeal.primeCompl)
      (.id : N →ₗ[Away 𝒜 (f : S)] N) :=
    isLocalizedModule_id (M := N)
      (R := Away 𝒜 (f : S)) (R' := A)
      (((Proj.toSpec 𝒜 (f : S)).base x).asIdeal.primeCompl)
  -- Reuse the identity localization of the codomain module over the localized ring.
  exact IsLocalizedModule.map_units (.id : N →ₗ[Away 𝒜 (f : S)] N) u

/-- Helper for Lemma 10.57.5: equality after applying the comparison map is killed by a
denominator from the corresponding prime complement of `Spec(S_(f))`. -/
private theorem awayDegreeZeroPart_exists_smul_eq_of_map_eq {d : ℕ} (f : 𝒜 d)
    (hd : 0 < d) (x : Proj.basicOpen 𝒜 (f : S))
    {y₁ y₂ : awayDegreeZeroPart 𝒜 ℳ f}
    (h : awayDegreeZeroPartToAtPrimeDegreeZeroPart 𝒜 ℳ f x y₁ =
      awayDegreeZeroPartToAtPrimeDegreeZeroPart 𝒜 ℳ f x y₂) :
    ∃ u : (((Proj.toSpec 𝒜 (f : S)).base x).asIdeal.primeCompl), u • y₁ = u • y₂ := by
  -- Route correction: the direct denominator-clearing proof reaches the equality
  -- `c • (f^b • m₁) = c • (f^a • m₂)` with `c ∉ I`, but turning that into a homogeneous
  -- denominator `s ∉ I` that still kills the same difference appears to require more module-side
  -- grading API than `SetLike.GradedSMul 𝒜 ℳ` currently supplies.
  -- TODO: either prove the ambient localization owner theorem for `awayAtPrimeLinearMap` and
  -- reuse `IsLocalizedModule.exists_of_eq`, or add a dependency-closed lemma that upgrades an
  -- arbitrary scalar killer `c ∉ I` to a homogeneous killer for equal-degree homogeneous vectors.
  sorry

/-- Lemma 10.57.5, module half in owner form: for `x ∈ D₊(f)`, the comparison map
`M_(f) → M_(x)` is localization at the corresponding prime of `Spec(S_(f))`. The linear
equivalence between the localized source and `M_(x)` is then derived from
`IsLocalizedModule.linearEquiv`; it is no longer a chosen primitive. -/
theorem awayDegreeZeroPartToAtPrimeDegreeZeroPart_isLocalizedModule {d : ℕ} (f : 𝒜 d)
    (hd : 0 < d) (x : Proj.basicOpen 𝒜 (f : S)) :
    IsLocalizedModule (((Proj.toSpec 𝒜 (f : S)).base x).asIdeal.primeCompl)
      (awayDegreeZeroPartToAtPrimeDegreeZeroPart 𝒜 ℳ f x) := by
  refine ⟨awayDegreeZeroPartToAtPrimeDegreeZeroPart_map_units (𝒜 := 𝒜) (ℳ := ℳ) f hd x,
    ?_, ?_⟩
  · intro z
    -- The source proof gives the surjectivity witness explicitly by clearing the denominator in
    -- a chosen homogeneous representative of `z`.
    rcases atPrimeDegreeZeroPart_exists_smul_eq_image (𝒜 := 𝒜) (ℳ := ℳ) f hd x z with
      ⟨y, u, hu⟩
    exact ⟨⟨y, u⟩, hu⟩
  · intro y₁ y₂ h
    -- Route correction: delegate the final denominator-clearing step to the dedicated helper so
    -- the main theorem matches the source-faithful localization skeleton.
    exact awayDegreeZeroPart_exists_smul_eq_of_map_eq (𝒜 := 𝒜) (ℳ := ℳ) (f := f) hd x h

end

/-! ### Lemma_10_57_6 (from Chap10) -/
universe u v

open HomogeneousIdeal

section

variable {A : Type u} {σ : Type v}
variable [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/- Domain triage:
* source-facing: a homogeneous ideal inside the irrelevant ideal contains a positive-degree
  homogeneous element avoiding finitely many homogeneous prime ideals.
* core/canonical owner: `ProjectiveSpectrum 𝒜`.
* bridge/view: the private theorem works at the owner level, and the public theorem upgrades a
  finite family of homogeneous prime ideals to points of `Proj` by deriving relevance from
  `I ≤ 𝒜₊` and `¬ I ≤ p i`.
-/

/-- Helper for Lemma 10.57.6: the finite product of homogeneous ideals is homogeneous. -/
private lemma family_product_isHomogeneous {ι : Type*}
    (p : ι → HomogeneousIdeal 𝒜) (s : Finset ι) :
    (s.prod fun i ↦ (p i).toIdeal).IsHomogeneous 𝒜 := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      -- The empty product is `⊤`, which is homogeneous.
      simpa using (Ideal.IsHomogeneous.top (𝒜 := 𝒜))
  | @cons i s hi hs =>
      -- Insert one factor and use closure of homogeneous ideals under multiplication.
      simpa [Finset.prod_insert hi] using
        Ideal.IsHomogeneous.mul (𝒜 := 𝒜) (p i).isHomogeneous hs

/-- Helper for Lemma 10.57.6: the product ideal associated to a finite family of homogeneous
prime ideals. -/
private def familyProduct {ι : Type*} [DecidableEq ι]
    (p : ι → HomogeneousIdeal 𝒜) (s : Finset ι) : HomogeneousIdeal 𝒜 :=
  ⟨s.prod fun i ↦ (p i).toIdeal, family_product_isHomogeneous 𝒜 p s⟩

/-- Helper for Lemma 10.57.6: inserting a new factor multiplies the family product by that factor.
-/
private lemma familyProduct_insert {ι : Type*} [DecidableEq ι]
    (p : ι → HomogeneousIdeal 𝒜) {i : ι} {s : Finset ι} (hi : i ∉ s) :
    familyProduct 𝒜 p (insert i s) = p i * familyProduct 𝒜 p s := by
  -- Both sides have the same underlying ideal product.
  apply HomogeneousIdeal.ext
  simp [familyProduct, hi, Finset.prod_insert, HomogeneousIdeal.toIdeal_mul]

/-- Helper for Lemma 10.57.6: the family product is contained in each factor that appears in the
finite family. -/
private lemma familyProduct_le_of_mem {ι : Type*} [DecidableEq ι]
    (p : ι → HomogeneousIdeal 𝒜) {s : Finset ι} {i : ι} (hi : i ∈ s) :
    familyProduct 𝒜 p s ≤ p i := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      cases hi
  | @cons j s hj hs =>
      simp only [Finset.mem_cons] at hi
      have hcons : familyProduct 𝒜 p (Finset.cons j s hj) = p j * familyProduct 𝒜 p s := by
        simpa [Finset.cons_eq_insert] using (familyProduct_insert 𝒜 p hj)
      rw [hcons]
      rcases hi with rfl | hi
      · -- The factor indexed by `j` contains the whole product.
        change (p i).toIdeal * (familyProduct 𝒜 p s).toIdeal ≤ (p i).toIdeal
        simpa [HomogeneousIdeal.toIdeal_mul] using
          (Ideal.mul_le_right : (p i).toIdeal * (familyProduct 𝒜 p s).toIdeal ≤ (p i).toIdeal)
      · -- Otherwise the product is first contained in the tail product, then in the target factor.
        exact le_trans
          (by
            change (p j).toIdeal * (familyProduct 𝒜 p s).toIdeal ≤
                (familyProduct 𝒜 p s).toIdeal
            simpa [HomogeneousIdeal.toIdeal_mul] using
              (Ideal.mul_le_left :
                (p j).toIdeal * (familyProduct 𝒜 p s).toIdeal ≤
                  (familyProduct 𝒜 p s).toIdeal))
          (hs hi)

/-- Helper for Lemma 10.57.6: if a prime homogeneous ideal contains the product of a finite family,
then it contains one of the factors. -/
private lemma family_product_not_le_of_forall_factor_not_le {ι : Type*} [DecidableEq ι]
    (p : ι → HomogeneousIdeal 𝒜) (s : Finset ι) (q : HomogeneousIdeal 𝒜)
    (hq : q.toIdeal.IsPrime) (havoid : ∀ i ∈ s, ¬ p i ≤ q) :
    ¬ familyProduct 𝒜 p s ≤ q := by
  intro hle
  -- Prime containment of a finite product forces containment of one factor.
  rcases (Ideal.IsPrime.prod_le (s := s) (f := fun i ↦ (p i).toIdeal) hq).1
      (by simpa [familyProduct] using (show (familyProduct 𝒜 p s).toIdeal ≤ q.toIdeal from hle)) with
    ⟨i, hi, hip⟩
  exact havoid i hi hip

/-- Helper for Lemma 10.57.6: a homogeneous ideal not contained in a homogeneous prime contains a
positive-degree homogeneous element outside that prime once it lies in the irrelevant ideal. -/
private lemma exists_pos_degree_mem_and_not_mem_of_not_le_prime
    (I P : HomogeneousIdeal 𝒜) (hI_irrelevant : I ≤ 𝒜₊) (havoid : ¬ I ≤ P) :
    ∃ x ∈ I, ∃ d > 0, x ∈ 𝒜 d ∧ x ∉ P := by
  classical
  by_cases hex : ∃ z, z ∈ I ∧ z ∉ P
  · obtain ⟨z, hzI, hzP⟩ := hex
    have hzI_decomp : ∀ d, (DirectSum.decompose 𝒜 z d : A) ∈ I :=
      (Ideal.IsHomogeneous.mem_iff (𝒜 := 𝒜) I.isHomogeneous).1 hzI
    have hnotall : ¬ ∀ d, (DirectSum.decompose 𝒜 z d : A) ∈ P := by
      intro hall
      exact hzP <| (Ideal.IsHomogeneous.mem_iff (𝒜 := 𝒜) P.isHomogeneous).2 hall
    obtain ⟨d, hdP⟩ := not_forall.mp hnotall
    let x : A := DirectSum.decompose 𝒜 z d
    have hxI : x ∈ I := hzI_decomp d
    have hxd : x ∈ 𝒜 d := SetLike.coe_mem _
    have hxP : x ∉ P := hdP
    have hx0 : x ≠ 0 := fun hx ↦ hxP (hx ▸ P.zero_mem)
    -- The irrelevant-ideal hypothesis rules out degree `0` for a nonzero homogeneous witness.
    have hdpos : 0 < d := by
      by_contra hd
      have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
      have hxirr0 : GradedRing.proj 𝒜 0 x = 0 := by
        simpa [HomogeneousIdeal.mem_irrelevant_iff] using hI_irrelevant hxI
      have hproj0 : GradedRing.proj 𝒜 0 x = x := by
        simpa [GradedRing.proj_apply, hd0] using
          (DirectSum.decompose_of_mem_same 𝒜 (hd0 ▸ hxd))
      exact hx0 <| by
        rw [← hproj0, hxirr0]
    exact ⟨x, hxI, d, hdpos, hxd, hxP⟩
  · exfalso
    apply havoid
    intro z hzI
    by_contra hzP
    exact hex ⟨z, hzI, hzP⟩

/-- Helper for Lemma 10.57.6: two powers of homogeneous elements with swapped exponents have the
same degree, so their sum is homogeneous. -/
private lemma pow_swap_add_mem_mul_degree {x y : A} {dx dy : ℕ}
    (hx : x ∈ 𝒜 dx) (hy : y ∈ 𝒜 dy) :
    x ^ dy + y ^ dx ∈ 𝒜 (dx * dy) := by
  -- Each summand lands in degree `dx * dy`, so the sum stays in that degree.
  have hxpow : x ^ dy ∈ 𝒜 (dx * dy) := by
    simpa [nsmul_eq_mul, Nat.mul_comm] using SetLike.pow_mem_graded dy hx
  have hypow : y ^ dx ∈ 𝒜 (dx * dy) := by
    simpa [nsmul_eq_mul] using SetLike.pow_mem_graded dx hy
  exact add_mem hxpow hypow

/-- Helper for Lemma 10.57.6: finite homogeneous-prime avoidance for an arbitrary finite index set.
-/
private theorem exists_pos_degree_mem_avoid_homogeneous_primes_finset
    {ι : Type*} (s : Finset ι) (I : HomogeneousIdeal 𝒜)
    (p : ι → HomogeneousIdeal 𝒜) (hprime : ∀ i ∈ s, (p i).toIdeal.IsPrime)
    (hI_irrelevant : I ≤ 𝒜₊) (havoid : ∀ i ∈ s, ¬ I ≤ p i) :
    ∃ x ∈ I, ∃ d > 0, x ∈ 𝒜 d ∧ ∀ i ∈ s, x ∉ p i := by
  classical
  -- Route correction: prove the positive-degree theorem directly by finite-set induction; the
  -- owner-level `Proj` statement will then be derived from it by multiplying with `𝒜₊`.
  revert hprime havoid
  refine s.strongInductionOn ?_
  intro s ih hprime havoid
  by_cases hs : s.Nonempty
  · obtain ⟨i₀, hi₀, hmin⟩ := s.exists_minimalFor p hs
    let t := s.erase i₀
    by_cases ht : t.Nonempty
    · have htss : t ⊂ s := by
        simpa [t] using Finset.erase_ssubset hi₀
      have hprime_t : ∀ i ∈ t, (p i).toIdeal.IsPrime := by
        intro i hi
        exact hprime i (by simpa [t] using Finset.mem_of_mem_erase hi)
      have havoid_t : ∀ i ∈ t, ¬ I ≤ p i := by
        intro i hi
        exact havoid i (by simpa [t] using Finset.mem_of_mem_erase hi)
      obtain ⟨x, hxI, dx, hdxpos, hxd, hxavoid_t⟩ :=
        ih t htss hprime_t havoid_t
      by_cases hxPi₀ : x ∈ p i₀
      · have hfactor_avoid : ∀ i ∈ t, ¬ p i ≤ p i₀ := by
          intro i hi hle
          have hi_s : i ∈ s := by
            simpa [t] using Finset.mem_of_mem_erase hi
          have hi₀le : p i₀ ≤ p i := hmin hi_s hle
          exact hxavoid_t i hi (hi₀le hxPi₀)
        have hfamily_not_le : ¬ familyProduct 𝒜 p t ≤ p i₀ :=
          family_product_not_le_of_forall_factor_not_le 𝒜 p t (p i₀) (hprime i₀ hi₀) hfactor_avoid
        have hprod_le_I : I * familyProduct 𝒜 p t ≤ I := by
          change I.toIdeal * (familyProduct 𝒜 p t).toIdeal ≤ I.toIdeal
          simpa [HomogeneousIdeal.toIdeal_mul] using
            (Ideal.mul_le_right : I.toIdeal * (familyProduct 𝒜 p t).toIdeal ≤ I.toIdeal)
        have hprod_irrelevant : I * familyProduct 𝒜 p t ≤ 𝒜₊ := hprod_le_I.trans hI_irrelevant
        have hprod_not_le : ¬ I * familyProduct 𝒜 p t ≤ p i₀ := by
          intro hle
          rcases (Ideal.IsPrime.mul_le (P := (p i₀).toIdeal) (hprime i₀ hi₀)).1
              (by simpa [HomogeneousIdeal.toIdeal_mul] using
                (show (I * familyProduct 𝒜 p t).toIdeal ≤ (p i₀).toIdeal from hle)) with
            hIle | hFle
          · exact havoid i₀ hi₀ hIle
          · exact hfamily_not_le hFle
        obtain ⟨y, hyProd, dy, hdypos, hyd, hyPi₀⟩ :=
          exists_pos_degree_mem_and_not_mem_of_not_le_prime 𝒜
            (I * familyProduct 𝒜 p t) (p i₀) hprod_irrelevant hprod_not_le
        have hyI : y ∈ I := hprod_le_I hyProd
        have hxPowI : x ^ dy ∈ I := I.toIdeal.pow_mem_of_mem hxI dy hdypos
        have hyPowI : y ^ dx ∈ I := I.toIdeal.pow_mem_of_mem hyI dx hdxpos
        have hzI : x ^ dy + y ^ dx ∈ I := I.add_mem hxPowI hyPowI
        have hzPi₀ : x ^ dy + y ^ dx ∉ p i₀ := by
          intro hzmem
          have hxPowPi₀ : x ^ dy ∈ p i₀ := (p i₀).toIdeal.pow_mem_of_mem hxPi₀ dy hdypos
          have hyPowPi₀ : y ^ dx ∈ p i₀ := by
            have : x ^ dy + y ^ dx - x ^ dy ∈ p i₀ := (p i₀).toIdeal.sub_mem hzmem hxPowPi₀
            simpa [add_comm, add_left_comm, add_assoc] using this
          exact hyPi₀ <| ((hprime i₀ hi₀).pow_mem_iff_mem dx hdxpos).1 hyPowPi₀
        have hzavoid_t : ∀ i ∈ t, x ^ dy + y ^ dx ∉ p i := by
          intro i hi hzmem
          have hyFamily : y ∈ familyProduct 𝒜 p t := by
            have hprod_le_family : (I * familyProduct 𝒜 p t).toIdeal ≤ (familyProduct 𝒜 p t).toIdeal := by
              simpa [HomogeneousIdeal.toIdeal_mul] using
                (Ideal.mul_le_left :
                  I.toIdeal * (familyProduct 𝒜 p t).toIdeal ≤ (familyProduct 𝒜 p t).toIdeal)
            exact hprod_le_family hyProd
          have hyPi : y ∈ p i := familyProduct_le_of_mem 𝒜 p hi hyFamily
          have hyPowPi : y ^ dx ∈ p i := (p i).toIdeal.pow_mem_of_mem hyPi dx hdxpos
          have hxPowPi : x ^ dy ∈ p i := by
            have : x ^ dy + y ^ dx - y ^ dx ∈ p i := (p i).toIdeal.sub_mem hzmem hyPowPi
            simpa [add_comm, add_left_comm, add_assoc] using this
          exact hxavoid_t i hi <| ((hprime_t i hi).pow_mem_iff_mem dy hdypos).1 hxPowPi
        exact ⟨x ^ dy + y ^ dx, hzI, dx * dy, Nat.mul_pos hdxpos hdypos,
          pow_swap_add_mem_mul_degree 𝒜 hxd hyd, by
            intro i hi
            by_cases hii₀ : i = i₀
            · simpa [hii₀] using hzPi₀
            · have hit : i ∈ t := by
                simpa [t, hii₀] using hi
              exact hzavoid_t i hit⟩
      · exact ⟨x, hxI, dx, hdxpos, hxd, by
          intro i hi
          by_cases hii₀ : i = i₀
          · simpa [hii₀] using hxPi₀
          · have hit : i ∈ t := by
              simpa [t, hii₀] using hi
            exact hxavoid_t i hit⟩
    · have ht0 : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
      obtain ⟨x, hxI, d, hdpos, hxd, hxPi₀⟩ :=
        exists_pos_degree_mem_and_not_mem_of_not_le_prime 𝒜
          I (p i₀) hI_irrelevant (havoid i₀ hi₀)
      exact ⟨x, hxI, d, hdpos, hxd, by
        intro i hi
        have hii₀ : i = i₀ := by
          by_contra hii₀
          have : i ∈ t := by
            simpa [t, hii₀] using hi
          simpa [ht0] using this
        simpa [hii₀] using hxPi₀⟩
  · -- For the empty family, the zero element is a vacuous witness of positive degree.
    refine ⟨0, I.zero_mem, 1, zero_lt_one, ?_, ?_⟩
    · simpa using (show (0 : A) ∈ 𝒜 1 from ZeroMemClass.coe_zero)
    · intro i hi
      have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      have : False := by
        simpa [hs0] using hi
      exact this.elim

/-- Lemma 10.57.6: if a homogeneous ideal `I` is contained in the irrelevant ideal and is not
contained in any of finitely many homogeneous prime ideals, then `I` contains a homogeneous element
of positive degree that avoids all of those prime ideals. -/
theorem exists_pos_degree_mem_avoid_homogeneous_primes
    {r : ℕ} (I : HomogeneousIdeal 𝒜) (p : Fin r → HomogeneousIdeal 𝒜)
    (hprime : ∀ i, (p i).toIdeal.IsPrime) (hI_irrelevant : I ≤ 𝒜₊) (havoid : ∀ i, ¬ I ≤ p i) :
    ∃ x ∈ I, ∃ d > 0, x ∈ 𝒜 d ∧ ∀ i, x ∉ p i := by
  -- Specialize the finite-set theorem to `Finset.univ`.
  simpa using exists_pos_degree_mem_avoid_homogeneous_primes_finset 𝒜
    (Finset.univ : Finset (Fin r)) I p (fun i _ ↦ hprime i) hI_irrelevant (fun i _ ↦ havoid i)

/-- Internal owner-level bridge: a homogeneous ideal contains a homogeneous element avoiding
finitely many relevant homogeneous primes as soon as it is not contained in any of them. -/
private theorem exists_isHomogeneousElem_mem_and_avoid
    {r : ℕ} (I : HomogeneousIdeal 𝒜) (p : Fin r → ProjectiveSpectrum 𝒜)
    (havoid : ∀ i, ¬ I ≤ (p i).asHomogeneousIdeal) :
    ∃ x ∈ I, SetLike.IsHomogeneousElem 𝒜 x ∧ ∀ i, x ∉ (p i).asHomogeneousIdeal := by
  -- Multiply by the irrelevant ideal to force positive degree, then forget the degree afterwards.
  have hprod_le_I : I * 𝒜₊ ≤ I := by
    change I.toIdeal * (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal ≤ I.toIdeal
    simpa [HomogeneousIdeal.toIdeal_mul] using
      (Ideal.mul_le_right : I.toIdeal * (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal ≤ I.toIdeal)
  have hprod_irrelevant : I * 𝒜₊ ≤ 𝒜₊ := by
    change I.toIdeal * (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal ≤
        (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal
    simpa [HomogeneousIdeal.toIdeal_mul] using
      (Ideal.mul_le_left : I.toIdeal * (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal ≤
        (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal)
  have hprod_avoid : ∀ i, ¬ I * 𝒜₊ ≤ (p i).asHomogeneousIdeal := by
    intro i hle
    rcases (Ideal.IsPrime.mul_le (P := (p i).asHomogeneousIdeal.toIdeal) (p i).isPrime).1
        (by simpa [HomogeneousIdeal.toIdeal_mul] using
          (show (I * 𝒜₊).toIdeal ≤ (p i).asHomogeneousIdeal.toIdeal from hle)) with
      hIle | hIrr
    · exact havoid i hIle
    · exact (p i).not_irrelevant_le hIrr
  obtain ⟨x, hxProd, d, hdpos, hxd, hxavoid⟩ :=
    exists_pos_degree_mem_avoid_homogeneous_primes 𝒜 (I * 𝒜₊)
      (fun i ↦ (p i).asHomogeneousIdeal) (fun i ↦ (p i).isPrime) hprod_irrelevant hprod_avoid
  exact ⟨x, hprod_le_I hxProd, ⟨d, hxd⟩, hxavoid⟩

end

/-! ### Lemma_10_57_7 (from Chap10) -/
universe u v

section

variable {A : Type u} {σ : Type v}
variable [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/- Lemma 10.57.7 (Stacks, Tag `00JT`): in an `ℕ`-graded commutative ring, the homogeneous ideal
generated by the homogeneous elements of a prime ideal is again prime. This is exactly the
canonical theorem `Ideal.IsPrime.homogeneousCore`. -/
recall Ideal.IsPrime.homogeneousCore

end

/-! ### Lemma_10_57_8 (from Chap10) -/
universe u v

section

open Ideal

variable {S : Type u} {σ : Type v}
variable [CommRing S] [SetLike σ S] [AddSubmonoidClass σ S]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Lemma 10.57.8 (2) (Stacks, Tag `00JU`): if `I` is a homogeneous ideal of an `ℕ`-graded
commutative ring `S`, then every minimal prime ideal over `I` is homogeneous. -/
-- Proof sketch: for a minimal prime `𝔭` over `I`, the canonical theorem
-- `Ideal.IsPrime.homogeneousCore` shows that `(𝔭.homogeneousCore 𝒜).toIdeal` is again prime.
-- Since `I` is homogeneous and `I ≤ 𝔭`, we have
-- `I ≤ (𝔭.homogeneousCore 𝒜).toIdeal ≤ 𝔭`. Minimality of `𝔭` among primes over `I` forces equality,
-- so `𝔭` equals its homogeneous core and is therefore homogeneous.
theorem isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous
    {I 𝔭 : Ideal S} (hI : I.IsHomogeneous 𝒜) (h𝔭 : 𝔭 ∈ I.minimalPrimes) :
    𝔭.IsHomogeneous 𝒜 := by
  have hIcore : I ≤ (𝔭.homogeneousCore 𝒜).toIdeal := by
    rw [← hI.toIdeal_homogeneousCore_eq_self]
    exact homogeneousCore_mono 𝒜 h𝔭.1.2
  have h𝔭core : 𝔭 ≤ (𝔭.homogeneousCore 𝒜).toIdeal :=
    h𝔭.2 ⟨h𝔭.1.1.homogeneousCore, hIcore⟩ (toIdeal_homogeneousCore_le 𝒜 𝔭)
  exact (IsHomogeneous.iff_eq 𝒜 𝔭).2 <| le_antisymm (toIdeal_homogeneousCore_le 𝒜 𝔭) h𝔭core

/-- Lemma 10.57.8 (1) (Stacks, Tag `00JU`): every minimal prime of an `ℕ`-graded commutative ring
is homogeneous. -/
theorem isHomogeneous_of_mem_minimalPrimes {𝔭 : Ideal S} (h𝔭 : 𝔭 ∈ minimalPrimes S) :
    𝔭.IsHomogeneous 𝒜 := by
  simpa [minimalPrimes] using
    isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous 𝒜 (IsHomogeneous.bot 𝒜) h𝔭

end
