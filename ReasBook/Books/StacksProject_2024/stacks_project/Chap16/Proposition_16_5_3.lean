import Mathlib
import StacksProject_2024.Chap10.Lemma_10_127_1
import StacksProject_2024.Chap10.Lemma_10_127_3
import StacksProject_2024.Chap10.Lemma_10_147_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

namespace Algebra

section

variable {R : Type u} {Λ : Type v}
variable [CommRing R] [CommRing Λ] [Algebra R Λ]
variable [Module.Flat R Λ]

/-- Helper for Proposition 16.5.3: quotienting a flat algebra map by the induced ideal preserves
flatness. -/
private theorem quotientMapFlatOfFlat
    {S : Type*} {T : Type*} [CommRing S] [CommRing T]
    (φ : S →+* T) (I : Ideal S) (hφ : φ.Flat) :
    (Ideal.quotientMap (Ideal.map φ I) φ Ideal.le_comap_map).Flat := by
  let _ : Algebra S T := φ.toAlgebra
  let e : T ⧸ Ideal.map φ I ≃+* ((S ⧸ I) ⊗[S] T) :=
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot T I).toRingEquiv).trans
      (Algebra.TensorProduct.comm S T (S ⧸ I)).toRingEquiv
  -- Proof comment: first base change the flat source map to `S ⧸ I`.
  have hφ_alg : (algebraMap S T).Flat := by
    simpa [RingHom.algebraMap_toAlgebra] using hφ
  have hbaseModule : Module.Flat (S ⧸ I) ((S ⧸ I) ⊗[S] T) := by
    let _ : Module.Flat S T := RingHom.flat_algebraMap_iff.mp hφ_alg
    simpa using (Module.Flat.baseChange (R := S) (S := S ⧸ I) (M := T))
  have hbase : (algebraMap (S ⧸ I) ((S ⧸ I) ⊗[S] T)).Flat := by
    exact RingHom.flat_algebraMap_iff.mpr hbaseModule
  -- Proof comment: then transport flatness across the quotient-tensor ring equivalence.
  have he : e.symm.toRingHom.Flat := RingHom.Flat.of_bijective e.symm.bijective
  have hcomp :
      (e.symm.toRingHom.comp (algebraMap (S ⧸ I) ((S ⧸ I) ⊗[S] T))).Flat :=
    RingHom.Flat.comp hbase he
  have hEq :
      e.symm.toRingHom.comp (algebraMap (S ⧸ I) ((S ⧸ I) ⊗[S] T)) =
        Ideal.quotientMap (Ideal.map φ I) φ Ideal.le_comap_map := by
    apply Ideal.Quotient.ringHom_ext
    rw [Ideal.quotientMap_comp_mk]
    ext x
    change
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot T I).symm
          ((Algebra.TensorProduct.comm S T (S ⧸ I)).symm
            ((Ideal.Quotient.mk I) x ⊗ₜ[S] (1 : T))) =
        (Ideal.Quotient.mk (Ideal.map φ I)) (φ x)
    have hcomm :
        (Algebra.TensorProduct.comm S T (S ⧸ I)).symm
            ((Ideal.Quotient.mk I) x ⊗ₜ[S] (1 : T)) =
          (1 : T) ⊗ₜ[S] (Ideal.Quotient.mk I x) := by
      simpa using
        (Algebra.TensorProduct.comm_symm_tmul (R := S) (a := (1 : T))
          (b := Ideal.Quotient.mk I x))
    rw [hcomm, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul]
    have hs : x • (1 : T) = φ x := by
      change (algebraMap S T x) * 1 = φ x
      simpa [RingHom.algebraMap_toAlgebra]
    simpa [RingHom.algebraMap_toAlgebra, hs]
  rw [← hEq]
  exact hcomp

/-- Helper for Proposition 16.5.3: this local square-zero quotient factorization is the exact
input formerly imported from `Lemma_16_5_1`. -/
private theorem existsSmoothQuotientFactorizationOfSquareZero
    {A : Type w} [CommRing A] [Algebra R A] [FinitePresentation R A]
    (I : Ideal R) (hSq : I ^ 2 = ⊥)
    (hcolim : (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))).IsFilteredColimitOfSmooth)
    (φ : A →ₐ[R] Λ) :
    ∃ (B : Type (max u v w)) (_ : CommRing B) (_ : Algebra R B) (_ : Smooth R B)
      (J : Ideal B) (_ : J ≤ I.map (algebraMap R B)) (_ : J.FG)
      (f : A →ₐ[R] B ⧸ J) (g : B ⧸ J →ₐ[R] Λ),
      g.comp f = φ := by
  -- Route correction: the canonical owner theorem from `Lemma_16_5_1` still fails to import in
  -- this snapshot because of a universe error, so the proposition keeps this theorem-local
  -- placeholder until the owner API is repaired or reproved locally.
  --
  -- TODO: either repair `Algebra.exists_smooth_quotient_factorization_of_square_zero` in its
  -- owner file, or re-establish the reduced finite-presentation bridge and correction algebra
  -- argument here so this factorization can be discharged locally.
  sorry

/-- Helper for Proposition 16.5.3: this local ideal-killing smooth factorization is the exact
input formerly imported from `Lemma_16_5_2`. -/
private theorem existsSmoothFactorizationKillingIdealOfSquareZero
    {B : Type w} [CommRing B] [Algebra R B] [Smooth R B]
    (I : Ideal R) (hSq : I ^ 2 = ⊥)
    (hcolim : (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))).IsFilteredColimitOfSmooth)
    (φ : B →ₐ[R] Λ) (J : Ideal B)
    (hJ : J ≤ I.map (algebraMap R B)) (hJfg : J.FG)
    (hφJ : J ≤ RingHom.ker φ) :
    ∃ (B' : Type (max u v w)) (_ : CommRing B') (_ : Algebra R B') (_ : Smooth R B')
      (α : B →ₐ[R] B') (β : B' →ₐ[R] Λ),
      J ≤ RingHom.ker α ∧ β.comp α = φ := by
  -- Route correction: the canonical owner theorem from `Lemma_16_5_2` depends on the same
  -- broken `Lemma_16_5_1` import chain, so the proposition keeps only this minimal local blocker.
  --
  -- TODO: after the square-zero quotient factorization above is available, follow the finite
  -- generating-family reduction from Lemma `16.5.2` to kill `J` inside another smooth algebra.
  sorry

/-- Helper for Proposition 16.5.3: in the square-zero case, every finitely presented algebra map
to `Λ` factors through a smooth `R`-algebra. -/
lemma finitelyPresentedFactorization_of_squareZero
    {A : Type w} [CommRing A] [Algebra R A] [FinitePresentation R A]
    (I : Ideal R) (hSq : I ^ 2 = ⊥)
    (hquot : (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))).IsFilteredColimitOfSmooth)
    (φ : A →ₐ[R] Λ) :
    ∃ (B' : Type (max u v w)) (_ : CommRing B') (_ : Algebra R B') (_ : Smooth R B')
      (f : A →ₐ[R] B') (g : B' →ₐ[R] Λ),
      g.comp f = φ := by
  -- Proof comment: first factor `φ` through a smooth quotient stage `B ⧸ J`.
  obtain ⟨B, _, _, hBsmooth, J, hJ, hJfg, f, g, hgf⟩ :=
    existsSmoothQuotientFactorizationOfSquareZero
      (A := A) (I := I) (hSq := hSq) (hcolim := hquot) φ
  let _ : Smooth R B := hBsmooth
  let φB : B →ₐ[R] Λ := g.comp (Ideal.Quotient.mkₐ R J)
  have hφJ : J ≤ RingHom.ker φB := by
    intro x hx
    rw [RingHom.mem_ker]
    have hx0 : Ideal.Quotient.mk J x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
    simpa [φB, hx0]
  -- Proof comment: then apply Lemma `16.5.2` to kill `J` inside another smooth algebra.
  obtain ⟨B', _, _, hB'smooth, α, β, hαJ, hβα⟩ :=
    existsSmoothFactorizationKillingIdealOfSquareZero
      (B := B) (I := I) (hSq := hSq) (hcolim := hquot)
      (φ := φB) (J := J) hJ hJfg hφJ
  have hαQuot : ∀ x, x ∈ J → α x = 0 := by
    intro x hx
    simpa [RingHom.mem_ker] using hαJ hx
  let δ : B ⧸ J →ₐ[R] B' :=
    Ideal.Quotient.liftₐ J α hαQuot
  have hδ : δ.comp (Ideal.Quotient.mkₐ R J) = α := by
    simpa [δ] using (Ideal.Quotient.liftₐ_comp (R₁ := R) J α hαQuot)
  have hβδ : β.comp δ = g := by
    apply Ideal.Quotient.algHom_ext
    calc
      (β.comp δ).comp (Ideal.Quotient.mkₐ R J)
          = β.comp (δ.comp (Ideal.Quotient.mkₐ R J)) := by
            rw [AlgHom.comp_assoc]
      _ = β.comp α := by rw [hδ]
      _ = φB := hβα
      _ = g.comp (Ideal.Quotient.mkₐ R J) := rfl
  refine ⟨B', inferInstance, inferInstance, hB'smooth, δ.comp f, β, ?_⟩
  -- Proof comment: descend the map from `B` through `B ⧸ J` and close by associativity.
  calc
    β.comp (δ.comp f) = (β.comp δ).comp f := by rw [AlgHom.comp_assoc]
    _ = g.comp f := by rw [hβδ]
    _ = φ := hgf

/-- Helper for Proposition 16.5.3: the induced target ideal in the double-quotient step agrees
with the direct quotient ideal obtained from the larger source ideal. -/
private theorem quotientStepTargetIdeal_eq
    {S : Type*} {T : Type*} [CommRing S] [CommRing T] [Algebra S T]
    (J K : Ideal S) :
    Ideal.map
        (algebraMap (S ⧸ J) (T ⧸ J.map (algebraMap S T)))
        (Ideal.map (Ideal.Quotient.mk J) K) =
      Ideal.map (Ideal.Quotient.mk (J.map (algebraMap S T))) (K.map (algebraMap S T)) := by
  -- Proof comment: the quotient algebra map is the composite of the original algebra map with
  -- the quotient map, so the double ideal image is exactly `Ideal.map_map`.
  have hcomp :
      (algebraMap (S ⧸ J) (T ⧸ J.map (algebraMap S T))).comp (Ideal.Quotient.mk J) =
        algebraMap S (T ⧸ J.map (algebraMap S T)) := by
    ext x
    rfl
  simpa [Ideal.map_map, hcomp]

/-- Helper for Proposition 16.5.3: the source quotient-of-quotient in the induction step is
canonically identified with the direct quotient by the larger ideal. -/
private theorem quotientStepSourceEquiv
    {S : Type*} [CommRing S] {J K : Ideal S} (hJK : J ≤ K) :
    ((S ⧸ J) ⧸ Ideal.map (Ideal.Quotient.mk J) K) ≃+* (S ⧸ K) := by
  -- Proof comment: this is the standard double-quotient equivalence for nested ideals.
  exact DoubleQuot.quotQuotEquivQuotOfLE (R := S) (I := J) (J := K) hJK

/-- Helper for Proposition 16.5.3: the target quotient-of-quotient in the induction step is
canonically identified with the quotient by the larger extended ideal. -/
private theorem quotientStepTargetEquiv
    {S : Type*} {T : Type*} [CommRing S] [CommRing T] [Algebra S T]
    {J K : Ideal S} (hJK : J ≤ K) :
    ((T ⧸ J.map (algebraMap S T)) ⧸
        Ideal.map (algebraMap (S ⧸ J) (T ⧸ J.map (algebraMap S T)))
          (Ideal.map (Ideal.Quotient.mk J) K)) ≃+*
      (T ⧸ K.map (algebraMap S T)) := by
  let eT₁ :
      ((T ⧸ J.map (algebraMap S T)) ⧸
          Ideal.map (algebraMap (S ⧸ J) (T ⧸ J.map (algebraMap S T)))
            (Ideal.map (Ideal.Quotient.mk J) K)) ≃+*
        ((T ⧸ J.map (algebraMap S T)) ⧸
          Ideal.map (Ideal.Quotient.mk (J.map (algebraMap S T))) (K.map (algebraMap S T))) :=
    Ideal.quotEquivOfEq (quotientStepTargetIdeal_eq (S := S) (T := T) J K)
  let eT₂ :
      ((T ⧸ J.map (algebraMap S T)) ⧸
          Ideal.map (Ideal.Quotient.mk (J.map (algebraMap S T))) (K.map (algebraMap S T))) ≃+*
        (T ⧸ K.map (algebraMap S T)) :=
    DoubleQuot.quotQuotEquivQuotOfLE
      (R := T) (I := J.map (algebraMap S T)) (J := K.map (algebraMap S T))
      (Ideal.map_mono hJK)
  -- Proof comment: first normalize the target ideal, then apply the standard double-quotient
  -- equivalence for the extended ideals.
  exact eT₁.trans eT₂

/-- Helper for Proposition 16.5.3: the induction-step quotient hypothesis is the original PT
hypothesis transported across the standard source and target double-quotient equivalences. -/
private theorem quotientHypothesisOfQuotientStep
    {S : Type*} {T : Type*} [CommRing S] [CommRing T] [Algebra S T]
    {J K : Ideal S} (hJK : J ≤ K)
    (hquotK :
      (algebraMap (S ⧸ K) (T ⧸ K.map (algebraMap S T))).IsFilteredColimitOfSmooth) :
    (algebraMap
        ((S ⧸ J) ⧸ Ideal.map (Ideal.Quotient.mk J) K)
        ((T ⧸ J.map (algebraMap S T)) ⧸
          Ideal.map (algebraMap (S ⧸ J) (T ⧸ J.map (algebraMap S T)))
            (Ideal.map (Ideal.Quotient.mk J) K))).IsFilteredColimitOfSmooth := by
  let eS := quotientStepSourceEquiv (S := S) (J := J) (K := K) hJK
  let eT := quotientStepTargetEquiv (S := S) (T := T) (J := J) (K := K) hJK
  -- Route correction: the remaining blocker is no longer the quotient algebra geometry itself.
  -- The unresolved step is only the final `ULift`-compatible `Arrow.isoMk` packaging needed to
  -- transport `RingHom.IsFilteredColimitOfSmooth` across `eS` and `eT`.
  --
  -- TODO: rewrite the transported source and target arrows in the exact `ULift` normal form used
  -- by `RingHom.IsFilteredColimitOfSmooth`, then apply `CategoryTheory.ObjectProperty.prop_of_iso`
  -- to the resulting arrow isomorphism.
  let _ := eS
  let _ := eT
  let _ := hquotK
  sorry

/-- Helper for Proposition 16.5.3: the square-zero quotient hypothesis already upgrades to PT for
the original flat map. -/
private theorem isFilteredColimitOfSmooth_of_squareZeroQuotient
    {S : Type*} {T : Type*} [CommRing S] [CommRing T] [Algebra S T] [Module.Flat S T]
    (I : Ideal S) (hSq : I ^ 2 = ⊥)
    (hquot : (algebraMap (S ⧸ I) (T ⧸ I.map (algebraMap S T))).IsFilteredColimitOfSmooth) :
    (algebraMap S T).IsFilteredColimitOfSmooth := by
  -- Route correction: the intended `ULift` + `MorphismProperty.ind_iff_exists` proof is now
  -- structurally clear, but its owner helper import chain still fails in `Lemma_16_4_4` because
  -- of typeclass-resolution timeouts. This theorem stays as the remaining owner-level blocker
  -- until that earlier API is repaired or the stage-extraction argument is localized here.
  --
  -- TODO: reintroduce the proof by extracting one finitely presented lifted stage map, descending
  -- it to an `S`-algebra map `A.left →ₐ[S] T`, applying
  -- `finitelyPresentedFactorization_of_squareZero`, and repackaging the resulting smooth
  -- factorization back into the `ULift`-owner criterion.
  sorry

/- Domain-style sampling for PT across nilpotent thickenings:
* primary domain: commutative algebra of filtered colimits of smooth algebras and nilpotent
  thickenings;
* sampled owner declarations:
  `RingHom.IsFilteredColimitOfSmooth`,
  `exists_smooth_quotient_factorization_of_square_zero`,
  `exists_smooth_factorization_killing_ideal_of_square_zero`,
  `IsNilpotent`;
* best owner abstraction: `(algebraMap R Λ).IsFilteredColimitOfSmooth`;
* primitive data: the nilpotent ideal `I`, flatness of `R → Λ`, and the PT hypothesis on the
  quotient map;
* derived API: any chosen filtered diagram presenting PT and the square-zero induction step used
  in the proof.

Source/core/bridge triage:
* `source-facing`: the nilpotent-thickening lifting statement of Proposition `16.5.3`;
* `core/canonical`: `RingHom.IsFilteredColimitOfSmooth`;
* `bridge/view`: the square-zero factorization results from Lemmas `16.5.1` and `16.5.2`.

This item stays source-facing, but its public statement should be phrased directly in the canonical
owner `RingHom.IsFilteredColimitOfSmooth` rather than through any auxiliary presentation data.
-/

-- Proof sketch: choose `n` with `I ^ n = ⊥` and argue by induction on `n`, reducing to the
-- square-zero case. To apply the factorization criterion for filtered colimits of smooth
-- algebras, start from a finitely presented `R`-algebra mapping to `Λ`, use Lemma `16.5.1` to
-- write it as a quotient `B ⧸ J` of a smooth `R`-algebra with `J ⊆ IB` finitely generated, and
-- then apply Lemma `16.5.2` to kill `J` after passing to another smooth `R`-algebra. The map
-- from the finitely presented algebra then factors through a smooth `R`-algebra, which is the
-- desired factorization criterion.
/-- Proposition 16.5.3: let `R → Λ` be a flat ring map and `I ⊂ R` a nilpotent ideal. If
`Λ ⧸ IΛ` is a filtered colimit of smooth `(R ⧸ I)`-algebras, then `Λ` is a filtered colimit of
smooth `R`-algebras. -/
theorem isFilteredColimitOfSmooth_of_nilpotent_quotient
    (I : Ideal R) (hI : IsNilpotent I)
    (hquot : (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))).IsFilteredColimitOfSmooth) :
    (algebraMap R Λ).IsFilteredColimitOfSmooth := by
  let P : ∀ ⦃S : Type _⦄ [CommRing S], Ideal S → Prop :=
    fun {S} _ J =>
      ∀ {T : Type _} [CommRing T] [Algebra S T] [Module.Flat S T],
        (algebraMap (S ⧸ J) (T ⧸ J.map (algebraMap S T))).IsFilteredColimitOfSmooth →
          (algebraMap S T).IsFilteredColimitOfSmooth
  -- Proof comment: apply the standard nilpotent-ideal induction, with the square-zero case as
  -- the base and the double-quotient transport as the induction step.
  exact
    Ideal.IsNilpotent.induction_on (S := R) I hI
      (P := P)
      (fun {S} _ J hJsq {T} _ _ _ ↦
        fun hquotJ ↦
          isFilteredColimitOfSmooth_of_squareZeroQuotient
            (S := S) (T := T) (I := J) hJsq hquotJ)
      (fun {S} _ J K hJK hJ hKquot {T} _ _ _ ↦
        fun hquotK ↦ by
          have hflat : (algebraMap S T).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
          have hquotFlat :
              (algebraMap (S ⧸ J) (T ⧸ J.map (algebraMap S T))).Flat := by
            simpa [RingHom.algebraMap_toAlgebra] using
              quotientMapFlatOfFlat (φ := algebraMap S T) J hflat
          let _ : Module.Flat (S ⧸ J) (T ⧸ J.map (algebraMap S T)) :=
            RingHom.flat_algebraMap_iff.mp hquotFlat
          have hquotJ :
              (algebraMap (S ⧸ J) (T ⧸ J.map (algebraMap S T))).IsFilteredColimitOfSmooth := by
            -- Proof comment: first descend the PT hypothesis from `K` to the quotient by `J`
            -- using the quotient-of-quotient induction step.
            exact
              hKquot
                (T := T ⧸ J.map (algebraMap S T))
                (quotientHypothesisOfQuotientStep
                  (S := S) (T := T) (J := J) (K := K) hJK hquotK)
          -- Proof comment: once the quotient by `J` satisfies PT, invoke the smaller-ideal
          -- induction hypothesis to conclude PT for the original map.
          exact hJ (T := T) hquotJ)
      (T := Λ) hquot

end

end Algebra
