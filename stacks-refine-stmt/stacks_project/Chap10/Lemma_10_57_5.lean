import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.Tactic.Recall
import stacks_project.Chap10.Lemma_10_57_9

-- Declarations for this item will be appended below by the statement pipeline.

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

/-- Lemma 10.57.5, module half in owner form: for `x ∈ D₊(f)`, the comparison map
`M_(f) → M_(x)` is localization at the corresponding prime of `Spec(S_(f))`. The linear
equivalence between the localized source and `M_(x)` is then derived from
`IsLocalizedModule.linearEquiv`; it is no longer a chosen primitive. -/
theorem awayDegreeZeroPartToAtPrimeDegreeZeroPart_isLocalizedModule {d : ℕ} (f : 𝒜 d)
    (hd : 0 < d) (x : Proj.basicOpen 𝒜 (f : S)) :
    IsLocalizedModule (((Proj.toSpec 𝒜 (f : S)).base x).asIdeal.primeCompl)
      (awayDegreeZeroPartToAtPrimeDegreeZeroPart 𝒜 ℳ f x) := by
  sorry

end
