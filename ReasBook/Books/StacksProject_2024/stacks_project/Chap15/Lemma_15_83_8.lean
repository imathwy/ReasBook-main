import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap15.Lemma_15_82_10
import StacksProject_2024.Chap15.Lemma_15_82_13
import StacksProject_2024.Chap15.Lemma_15_82_15
import StacksProject_2024.Chap15.Lemma_15_83_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} {B : Type u} {A : Type u}
variable [CommRing R] [CommRing B] [CommRing A]
variable [Algebra R B] [Algebra B A] [Algebra R A] [IsScalarTower R B A]
variable [Module.Flat R B] [Algebra.FinitePresentation R B]
variable [Module.Flat R A] [Algebra.FinitePresentation R A]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModB" => DerivedCategory (ModuleCat B)

/-- Helper for Lemma 15.83.8: after identifying `MvPolynomial (Fin 0) B` with `B`, surjectivity
of `B → A` turns relative `m`-pseudo-coherence over `B` into ordinary `m`-pseudo-coherence of the
restricted derived object. -/
private theorem isMPseudoCoherentRelativeTo_base_iff_restrictScalars_of_surjective
    (K : DModA) (m : ℤ) (hφ : Function.Surjective (algebraMap B A)) :
    by
      letI : Algebra.FiniteType B A := Algebra.FiniteType.of_surjective (algebraMap B A) hφ
      exact
        K.IsMPseudoCoherentRelativeTo B m ↔
          (((ModuleCat.restrictScalars (algebraMap B A)).mapDerivedCategory.obj K)).IsMPseudoCoherent m := by
  letI : Algebra.FiniteType B A := Algebra.FiniteType.of_surjective (algebraMap B A) hφ
  let KB : DModB := ((ModuleCat.restrictScalars (algebraMap B A)).mapDerivedCategory.obj K)
  let e : MvPolynomial (Fin 0) B ≃ₐ[B] B :=
    RingHom.IsLocalCompleteIntersection.empty_polynomial_algEquiv B
  let α₀ : MvPolynomial (Fin 0) B →ₐ[B] A := (Algebra.ofId B A).comp e.toAlgHom
  have hα₀ : Function.Surjective α₀ := by
    intro a
    rcases hφ a with ⟨b, rfl⟩
    refine ⟨e.symm b, ?_⟩
    simp [α₀]
  have hrestricted_regular :
      ((ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of B B)).IsPseudoCoherent := by
    -- Restricting the regular `B`-module along the empty polynomial equivalence keeps the free
    -- rank-one module.
    simpa using restrictScalars_regularModule_isPseudoCoherent_of_ringEquiv e.toRingEquiv
  have hchange :
      KB.IsMPseudoCoherent m ↔
        (((ModuleCat.restrictScalars e.toRingHom).mapDerivedCategory.obj KB)).IsMPseudoCoherent
          m := by
    -- Absolute pseudo-coherence is invariant under restricting scalars along a ring equivalence.
    simpa using isMPseudoCoherent_iff_restrictScalars_local e.toRingHom KB m hrestricted_regular
  constructor
  · intro hK
    -- Evaluate the relative condition on the empty polynomial presentation of `A` over `B`.
    have hα :
        (((ModuleCat.restrictScalars α₀.toRingHom).mapDerivedCategory.obj K)).IsMPseudoCoherent m :=
      hK 0 α₀ hα₀
    exact hchange.mpr (by simpa [KB, α₀, e] using hα)
  · intro hKB
    -- Route correction: use the source-faithful empty presentation over the surjective base map
    -- instead of trying to force absolute pseudo-coherence through `15.65.11`.
    refine
      (derived_isMPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation
        (R := B) (A := A) K m).2 ?_
    refine ⟨0, α₀, hα₀, ?_⟩
    exact hchange.mp (by simpa [KB, α₀, e] using hKB)

/-- Helper for Lemma 15.83.8: the same empty-presentation argument identifies relative
pseudo-coherence over `B` with pseudo-coherence of the restricted derived object. -/
private theorem isPseudoCoherentRelativeTo_base_iff_restrictScalars_of_surjective
    (K : DModA) (hφ : Function.Surjective (algebraMap B A)) :
    by
      letI : Algebra.FiniteType B A := Algebra.FiniteType.of_surjective (algebraMap B A) hφ
      exact
        K.IsPseudoCoherentRelativeTo B ↔
          (((ModuleCat.restrictScalars (algebraMap B A)).mapDerivedCategory.obj K)).IsPseudoCoherent := by
  letI : Algebra.FiniteType B A := Algebra.FiniteType.of_surjective (algebraMap B A) hφ
  rw [DerivedCategory.IsPseudoCoherentRelativeTo, isPseudoCoherent_iff_forall_isMPseudoCoherent]
  constructor
  · intro hK m
    exact (isMPseudoCoherentRelativeTo_base_iff_restrictScalars_of_surjective K m hφ).1 (hK m)
  · intro hK m
    exact (isMPseudoCoherentRelativeTo_base_iff_restrictScalars_of_surjective K m hφ).2 (hK m)

/-- Helper for Lemma 15.83.8: under a pseudo-coherent ring map `R → S`, relative
`m`-pseudo-coherence over `R` agrees with ordinary `m`-pseudo-coherence in `D(S)`. -/
private theorem isMPseudoCoherentRelativeTo_iff_isMPseudoCoherent_of_pseudoCoherentRingMap
    {S : Type u} [CommRing S] [Algebra R S]
    [(algebraMap R S).IsPseudoCoherentRingMap]
    (K : DerivedCategory (ModuleCat S)) (m : ℤ) :
    K.IsMPseudoCoherentRelativeTo R m ↔ K.IsMPseudoCoherent m := by
  constructor
  · intro hK
    rcases
      Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType R S)
      with ⟨n, α, hα⟩
    have hrestricted :
        ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K).IsMPseudoCoherent m :=
      hK n α hα
    exact
      (isMPseudoCoherent_iff_restrictScalars_local α.toRingHom K m
        (regularModule_restrictScalars_isPseudoCoherent_of_relative
          (show (ModuleCat.of S S).IsPseudoCoherentRelativeTo R from inferInstance) α hα)).2
        hrestricted
  · intro hK n α hα
    exact
      (isMPseudoCoherent_iff_restrictScalars_local α.toRingHom K m
        (regularModule_restrictScalars_isPseudoCoherent_of_relative
          (show (ModuleCat.of S S).IsPseudoCoherentRelativeTo R from inferInstance) α hα)).1
        hK

/-- Helper for Lemma 15.83.8: under a pseudo-coherent ring map `R → S`, relative
pseudo-coherence over `R` agrees with ordinary pseudo-coherence in `D(S)`. -/
private theorem isPseudoCoherentRelativeTo_iff_isPseudoCoherent_of_pseudoCoherentRingMap
    {S : Type u} [CommRing S] [Algebra R S]
    [(algebraMap R S).IsPseudoCoherentRingMap]
    (K : DerivedCategory (ModuleCat S)) :
    K.IsPseudoCoherentRelativeTo R ↔ K.IsPseudoCoherent := by
  rw [DerivedCategory.IsPseudoCoherentRelativeTo, isPseudoCoherent_iff_forall_isMPseudoCoherent]
  constructor
  · intro hK m
    exact
      (isMPseudoCoherentRelativeTo_iff_isMPseudoCoherent_of_pseudoCoherentRingMap
        (R := R) (S := S) K m).1 (hK m)
  · intro hK m
    exact
      (isMPseudoCoherentRelativeTo_iff_isMPseudoCoherent_of_pseudoCoherentRingMap
        (R := R) (S := S) K m).2 (hK m)

-- Proof sketch: use flat finite presentation to regard `R → B` and `R → A` as perfect, hence
-- pseudo-coherent, ring maps. Then center the five-way comparison at relative pseudo-coherence
-- over `R`: Lemma `15.83.7` gives clauses `(1)` and `(5)`, Lemma `15.82.15` gives clause `(3)`,
-- and the surjective empty-presentation helper above rewrites clause `(4)` through relative
-- pseudo-coherence over `B`.
/-- Lemma 15.83.8: let `R → B → A` be ring maps with `B → A` surjective and with `R → B` and
`R → A` flat and of finite presentation. For `K ∈ D(A)`, the following are equivalent:
`K` is pseudo-coherent, `K` is pseudo-coherent relative to `R`, `K` is pseudo-coherent relative
to `A`, its restriction of scalars to `D(B)` is pseudo-coherent, and that restriction is
pseudo-coherent relative to `R`. -/
theorem isPseudoCoherent_tfae_of_surjective_of_flat_of_finitePresentation
    (K : DModA) (hφ : Function.Surjective (algebraMap B A)) :
    List.TFAE [
      K.IsPseudoCoherent,
      K.IsPseudoCoherentRelativeTo R,
      K.IsPseudoCoherentRelativeTo A,
      (((ModuleCat.restrictScalars (algebraMap B A)).mapDerivedCategory.obj K)).IsPseudoCoherent,
      (((ModuleCat.restrictScalars (algebraMap B A)).mapDerivedCategory.obj K)).IsPseudoCoherentRelativeTo R
    ] := by
  letI : Algebra.FiniteType B A := Algebra.FiniteType.of_surjective (algebraMap B A) hφ
  let KB : DModB := ((ModuleCat.restrictScalars (algebraMap B A)).mapDerivedCategory.obj K)
  have hArel : (ModuleCat.of A A).IsPseudoCoherentRelativeTo R := by
    exact (inferInstance : (algebraMap R A).IsPerfectRingMap).toIsPseudoCoherentRingMap.isPseudoCoherentRelativeTo
  have hBrel : (ModuleCat.of B B).IsPseudoCoherentRelativeTo R := by
    exact (inferInstance : (algebraMap R B).IsPerfectRingMap).toIsPseudoCoherentRingMap.isPseudoCoherentRelativeTo
  refine List.tfae_of_forall (K.IsPseudoCoherentRelativeTo R) _ ?_
  intro P hP
  simp only [List.mem_cons] at hP
  rcases hP with rfl | hP
  · exact
      (isPseudoCoherentRelativeTo_iff_isPseudoCoherent_of_pseudoCoherentRingMap
        (R := R) (S := A) K).symm
  rcases hP with rfl | hP
  · rfl
  rcases hP with rfl | hP
  · simpa using
      (isPseudoCoherentRelativeTo_iff_of_intermediate_isPseudoCoherentRelativeTo
        (R := R) (A := A) (B := A) K hArel)
  rcases hP with rfl | hP
  · calc
      KB.IsPseudoCoherent ↔ K.IsPseudoCoherentRelativeTo B := by
        exact (isPseudoCoherentRelativeTo_base_iff_restrictScalars_of_surjective K hφ).symm
      _ ↔ K.IsPseudoCoherentRelativeTo R := by
        simpa using
          (isPseudoCoherentRelativeTo_iff_of_intermediate_isPseudoCoherentRelativeTo
            (R := R) (A := B) (B := A) K hBrel)
  · rcases hP with rfl | hP
    · calc
        KB.IsPseudoCoherentRelativeTo R ↔ KB.IsPseudoCoherent := by
          exact
            isPseudoCoherentRelativeTo_iff_isPseudoCoherent_of_pseudoCoherentRingMap
              (R := R) (S := B) KB
        _ ↔ K.IsPseudoCoherentRelativeTo R := by
          calc
            KB.IsPseudoCoherent ↔ K.IsPseudoCoherentRelativeTo B := by
              exact (isPseudoCoherentRelativeTo_base_iff_restrictScalars_of_surjective K hφ).symm
            _ ↔ K.IsPseudoCoherentRelativeTo R := by
              simpa using
                (isPseudoCoherentRelativeTo_iff_of_intermediate_isPseudoCoherentRelativeTo
                  (R := R) (A := B) (B := A) K hBrel)
    · simpa using hP

-- Proof sketch: repeat the same central comparison at relative `m`-pseudo-coherence over `R`,
-- reusing the surjective empty-presentation helper for the restricted object and the `m`-versions
-- of Lemmas `15.83.7` and `15.82.15`.
/-- Under the same hypotheses, the analogous five-way equivalence also holds for
`m`-pseudo-coherence. -/
theorem isMPseudoCoherent_tfae_of_surjective_of_flat_of_finitePresentation
    (K : DModA) (m : ℤ) (hφ : Function.Surjective (algebraMap B A)) :
    List.TFAE [
      K.IsMPseudoCoherent m,
      K.IsMPseudoCoherentRelativeTo R m,
      K.IsMPseudoCoherentRelativeTo A m,
      (((ModuleCat.restrictScalars (algebraMap B A)).mapDerivedCategory.obj K)).IsMPseudoCoherent m,
      (((ModuleCat.restrictScalars (algebraMap B A)).mapDerivedCategory.obj K)).IsMPseudoCoherentRelativeTo R m
    ] := by
  letI : Algebra.FiniteType B A := Algebra.FiniteType.of_surjective (algebraMap B A) hφ
  let KB : DModB := ((ModuleCat.restrictScalars (algebraMap B A)).mapDerivedCategory.obj K)
  have hArel : (ModuleCat.of A A).IsPseudoCoherentRelativeTo R := by
    exact (inferInstance : (algebraMap R A).IsPerfectRingMap).toIsPseudoCoherentRingMap.isPseudoCoherentRelativeTo
  have hBrel : (ModuleCat.of B B).IsPseudoCoherentRelativeTo R := by
    exact (inferInstance : (algebraMap R B).IsPerfectRingMap).toIsPseudoCoherentRingMap.isPseudoCoherentRelativeTo
  refine List.tfae_of_forall (K.IsMPseudoCoherentRelativeTo R m) _ ?_
  intro P hP
  simp only [List.mem_cons] at hP
  rcases hP with rfl | hP
  · exact
      (isMPseudoCoherentRelativeTo_iff_isMPseudoCoherent_of_pseudoCoherentRingMap
        (R := R) (S := A) K m).symm
  rcases hP with rfl | hP
  · rfl
  rcases hP with rfl | hP
  · simpa using
      (isMPseudoCoherentRelativeTo_iff_of_intermediate_isPseudoCoherentRelativeTo
        (R := R) (A := A) (B := A) K m hArel)
  rcases hP with rfl | hP
  · calc
      KB.IsMPseudoCoherent m ↔ K.IsMPseudoCoherentRelativeTo B m := by
        exact (isMPseudoCoherentRelativeTo_base_iff_restrictScalars_of_surjective K m hφ).symm
      _ ↔ K.IsMPseudoCoherentRelativeTo R m := by
        simpa using
          (isMPseudoCoherentRelativeTo_iff_of_intermediate_isPseudoCoherentRelativeTo
            (R := R) (A := B) (B := A) K m hBrel)
  · rcases hP with rfl | hP
    · calc
        KB.IsMPseudoCoherentRelativeTo R m ↔ KB.IsMPseudoCoherent m := by
          exact
            isMPseudoCoherentRelativeTo_iff_isMPseudoCoherent_of_pseudoCoherentRingMap
              (R := R) (S := B) KB m
        _ ↔ K.IsMPseudoCoherentRelativeTo R m := by
          calc
            KB.IsMPseudoCoherent m ↔ K.IsMPseudoCoherentRelativeTo B m := by
              exact (isMPseudoCoherentRelativeTo_base_iff_restrictScalars_of_surjective K m hφ).symm
            _ ↔ K.IsMPseudoCoherentRelativeTo R m := by
              simpa using
                (isMPseudoCoherentRelativeTo_iff_of_intermediate_isPseudoCoherentRelativeTo
                  (R := R) (A := B) (B := A) K m hBrel)
    · simpa using hP

end

end CategoryTheory
