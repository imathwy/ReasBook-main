import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_15_4_Chinese_remainder
import stacks_proof.stacks_project.Chap15.Lemma_15_11_11
import stacks_proof.stacks_project.Chap15.Lemma_15_12_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open RingPairCat

universe u v

noncomputable section

section

variable {A : Type u} [CommRing A]
variable {ι : Type v}
variable [RingPairCat.henselianPairInclusion.IsRightAdjoint]

/-- Helper for Lemma 15.12.8: after isolating the first ideal in a `Fin (n + 1)`-indexed
pairwise comaximal family, the intersection of the remaining ideals is still comaximal with the
first one. -/
lemma isCoprime_iInf_of_pairwise {n : ℕ} (I : Fin (n + 1) → Ideal A)
    (hI : Pairwise fun i j ↦ IsCoprime (I i) (I j)) :
    IsCoprime (⨅ j : Fin n, I j.succ) (I 0) := by
  classical
  -- Proof comment: first prove comaximality with the finite product of the tail ideals by
  -- multiplying the pairwise comaximality witnesses against `I 0`.
  have hprod : IsCoprime (∏ j : Fin n, I j.succ) (I 0) := by
    refine IsCoprime.prod_left ?_
    intro j hj
    exact hI (by simpa using (Fin.succ_ne_zero j))
  -- Proof comment: in a finite pairwise-comaximal family, the tail product equals the tail
  -- intersection, so the previous product statement is exactly the desired intersection statement.
  have htail :
      ∏ j : Fin n, I j.succ = ⨅ j : Fin n, I j.succ := by
    exact chinese_remainder_prod_eq_iInf (I := fun j : Fin n ↦ I j.succ) <| by
      intro i j hij
      exact hI (by simpa using hij)
  rw [← htail]
  exact hprod

section ProductQuotient

variable {R : ι → Type u} [∀ i, CommRing (R i)]

/-- Helper for Lemma 15.12.8: the ideals cutting out one coordinate quotient inside a product ring
are pairwise comaximal. -/
lemma eval_comap_isCoprime (I : ∀ i, Ideal (R i)) {i j : ι} (hij : i ≠ j) :
    IsCoprime
      (Ideal.comap (Pi.evalRingHom R i) (I i))
      (Ideal.comap (Pi.evalRingHom R j) (I j)) := by
  classical
  rw [Ideal.isCoprime_iff_exists]
  let xi : ∀ k, R k := Function.update 1 i 0
  let xj : ∀ k, R k := Function.update 0 i 1
  have hji : j ≠ i := fun h ↦ hij h.symm
  refine ⟨xi, ?_, xj, ?_, ?_⟩
  · -- Proof comment: `xi` vanishes in the `i`-th coordinate, so it lies in the `i`-th comap.
    change xi i ∈ I i
    simp [xi]
  · -- Proof comment: `xj` vanishes away from the `i`-th coordinate, in particular at `j`.
    change xj j ∈ I j
    simp [xj, hji]
  · -- Proof comment: the two witnesses complement each other pointwise to the constant one tuple.
    ext k
    by_cases hk : k = i
    · subst hk
      simp [xi, xj]
    · simp [xi, xj, hk]

/-- Helper for Lemma 15.12.8: the family of coordinate-comap ideals in a product ring is pairwise
comaximal. -/
lemma pairwise_eval_comap_isCoprime (I : ∀ i, Ideal (R i)) :
    Pairwise fun i j ↦
      IsCoprime
        (Ideal.comap (Pi.evalRingHom R i) (I i))
        (Ideal.comap (Pi.evalRingHom R j) (I j)) := by
  intro i j hij
  exact eval_comap_isCoprime (R := R) I hij

/-- Helper for Lemma 15.12.8: intersecting the coordinate-comap ideals in a product ring recovers
the product ideal. -/
lemma iInf_eval_comap_eq_pi (I : ∀ i, Ideal (R i)) :
    (⨅ i, Ideal.comap (Pi.evalRingHom R i) (I i)) = Ideal.pi I := by
  ext x
  simp [Ideal.mem_pi]

/-- Helper for Lemma 15.12.8: the quotient map obtained by evaluating a product ring in one
coordinate and then reducing modulo `I i` is surjective. -/
lemma evalQuotientAlgHom_surjective (I : ∀ i, Ideal (R i)) (i : ι) :
    Function.Surjective
      (((Ideal.Quotient.mk (I i)).toIntAlgHom).comp (Pi.evalRingHom R i).toIntAlgHom) := by
  -- Proof comment: evaluation is surjective, and quotienting is surjective, so the composite is.
  simpa using
    Function.Surjective.comp Ideal.Quotient.mk_surjective (Function.surjective_eval i)

/-- Helper for Lemma 15.12.8: the kernel of the coordinate-evaluation quotient map is exactly the
corresponding coordinate-comap ideal. -/
lemma ker_evalQuotientAlgHom_eq_comap (I : ∀ i, Ideal (R i)) (i : ι) :
    RingHom.ker
        ((((Ideal.Quotient.mk (I i)).toIntAlgHom).comp
            (Pi.evalRingHom R i).toIntAlgHom).toRingHom) =
      Ideal.comap (Pi.evalRingHom R i) (I i) := by
  ext x
  -- Proof comment: vanishing in the quotient means precisely membership in the reduced ideal.
  change
    (((Ideal.Quotient.mk (I i)) ((Pi.evalRingHom R i) x)) = 0) ↔
      (Pi.evalRingHom R i) x ∈ I i
  simpa using (Ideal.Quotient.eq_zero_iff_mem : (Ideal.Quotient.mk (I i)) (x i) = 0 ↔ x i ∈ I i)

/-- Helper for Lemma 15.12.8: quotienting a product ring by a single coordinate-comap ideal is
canonically the same as quotienting that coordinate ring by the corresponding ideal. -/
noncomputable def quotientEvalComapRingEquiv (I : ∀ i, Ideal (R i)) (i : ι) :
    ((∀ j, R j) ⧸ Ideal.comap (Pi.evalRingHom R i) (I i)) ≃+* R i ⧸ I i :=
  (Ideal.quotEquivOfEq (ker_evalQuotientAlgHom_eq_comap (R := R) I i).symm).trans
    ((Ideal.quotientKerAlgEquivOfSurjective
      (f := ((Ideal.Quotient.mk (I i)).toIntAlgHom).comp (Pi.evalRingHom R i).toIntAlgHom)
      (evalQuotientAlgHom_surjective (R := R) I i)).toRingEquiv)

/-- Helper for Lemma 15.12.8: quotienting a product ring by the product ideal is canonically the
same as taking the product of the coordinate quotients. -/
noncomputable def quotientPiRingEquivPiQuotient [Finite ι] (I : ∀ i, Ideal (R i)) :
    ((∀ i, R i) ⧸ Ideal.pi I) ≃+* ∀ i, R i ⧸ I i :=
  (Ideal.quotEquivOfEq (iInf_eval_comap_eq_pi (R := R) I).symm).trans <|
    (Ideal.quotientInfRingEquivPiQuotient
      (fun i ↦ Ideal.comap (Pi.evalRingHom R i) (I i))
      (pairwise_eval_comap_isCoprime (R := R) I)).trans <|
      RingEquiv.piCongrRight fun i ↦
        quotientEvalComapRingEquiv (R := R) I i

end ProductQuotient

/-- Helper for Lemma 15.12.8: the distinguished henselization ideal pulls back along the canonical
map `A → A^h` to the original ideal. -/
lemma henselizationIdeal_le_comap_toHenselization (I : Ideal A) :
    I ≤ Ideal.comap (toHenselization (pairOfIdeal I))
      (henselizationIdeal (pairOfIdeal I)) := by
  -- Proof comment: replace the henselization ideal by the mapped ideal from Lemma `15.12.2`.
  simpa [henselizationIdeal_eq_map (X := pairOfIdeal I)] using
    (Ideal.le_comap_map :
      I ≤ Ideal.comap (toHenselization (pairOfIdeal I))
        (Ideal.map (toHenselization (pairOfIdeal I)) I))

/-- Helper for Lemma 15.12.8: the quotient of a chosen henselization by its distinguished ideal is
canonically identified with the original quotient `A ⧸ I`. -/
lemma henselization_quotientMap_bijective (I : Ideal A) :
    Function.Bijective
      (Ideal.quotientMap
        (henselizationIdeal (pairOfIdeal I))
        (toHenselization (pairOfIdeal I))
        (henselizationIdeal_le_comap_toHenselization (I := I))) := by
  -- Proof comment: this is the `n = 1` case of the quotient comparison from Lemma `15.12.2`.
  convert (quotientPowToHenselization_bijective (X := pairOfIdeal I) 1) using 1
  simp [pow_one]

/-- Helper for Lemma 15.12.8: if one factor ideal maps to `⊤`, then mapping an intersection agrees
with mapping the other factor. -/
lemma map_inf_eq_left_of_map_right_eq_top {B : Type u} [CommRing B] (f : A →+* B)
    (I J : Ideal A) (hJ : Ideal.map f J = ⊤) :
    Ideal.map f (I ⊓ J) = Ideal.map f I := by
  apply le_antisymm
  · -- Proof comment: the intersection is contained in `I`, so its image is as well.
    exact Ideal.map_mono inf_le_left
  · -- Proof comment: once `J` maps to the unit ideal, every generator of `map I` comes from the
    -- product `I * J`, which is contained in `I ⊓ J`.
    calc
      Ideal.map f I = Ideal.map f I * Ideal.map f J := by
        rw [hJ, Ideal.mul_top]
      _ = Ideal.map f (I * J) := by
        rw [Ideal.map_mul]
      _ ≤ Ideal.map f (I ⊓ J) := Ideal.map_mono Ideal.mul_le_inf

/-- Helper for Lemma 15.12.8: in the henselization of `(A, I)`, every ideal comaximal with `I`
maps to the unit ideal. -/
lemma ideal_map_eq_top_of_isCoprime_to_henselization (I J : Ideal A) (hIJ : IsCoprime I J) :
    Ideal.map (toHenselization (pairOfIdeal I)) J = ⊤ := by
  let f : A →+* henselizationRing (pairOfIdeal I) := toHenselization (pairOfIdeal I)
  have hPair :
      HenselianRing (henselizationRing (pairOfIdeal I))
        (henselizationIdeal (pairOfIdeal I)) := by
    change HenselianRing (henselizationPair (pairOfIdeal I)).ring
      (henselizationPair (pairOfIdeal I)).ideal
    exact (henselization (pairOfIdeal I)).property
  let _ :
      HenselianRing (henselizationRing (pairOfIdeal I))
        (henselizationIdeal (pairOfIdeal I)) := hPair
  have hIdealJac :
      henselizationIdeal (pairOfIdeal I) ≤
        Ring.jacobson (henselizationRing (pairOfIdeal I)) := by
    -- Proof comment: a henselian ideal lies in the Jacobson radical by the owner field `jac`.
    simpa [Ideal.jacobson_bot] using
      (show henselizationIdeal (pairOfIdeal I) ≤
          Ideal.jacobson (⊥ : Ideal (henselizationRing (pairOfIdeal I))) from
        HenselianRing.jac)
  have hJac :
      Ideal.map f I ≤ Ring.jacobson (henselizationRing (pairOfIdeal I)) := by
    -- Proof comment: the distinguished henselization ideal is Jacobson, and it is exactly `I A^h`.
    simpa [f, henselizationIdeal_eq_map (X := pairOfIdeal I)] using
      hIdealJac
  have hsup :
      Ideal.map f I ⊔ Ideal.map f J = ⊤ := by
    rw [Ideal.isCoprime_iff_sup_eq] at hIJ
    calc
      Ideal.map f I ⊔ Ideal.map f J = Ideal.map f (I ⊔ J) := by
        rw [← Ideal.map_sup]
      _ = ⊤ := by
        simpa [hIJ, Ideal.map_top]
  have honeSup :
      (1 : henselizationRing (pairOfIdeal I)) ∈ Ideal.map f I ⊔ Ideal.map f J := by
    simpa [Ideal.eq_top_iff_one] using hsup
  rcases (Submodule.mem_sup.mp honeSup) with ⟨x, hx, y, hy, hxy⟩
  have hnegx : -x ∈ Ideal.map f I := by
    simpa using Ideal.neg_mem _ hx
  have hy_eq : y = 1 + -x := by
    calc
      y = y + (x + -x) := by simp
      _ = (x + y) + -x := by ac_rfl
      _ = 1 + -x := by rw [hxy]
  have hyUnit : IsUnit y := by
    -- Proof comment: write `y` as `1 + (-x)` with `x` in the Jacobson ideal `I A^h`.
    have hmemJac :
        -x ∈ Ideal.jacobson (⊥ : Ideal (henselizationRing (pairOfIdeal I))) := by
      simpa [Ideal.jacobson_bot] using hJac hnegx
    have hunit : IsUnit (1 + (-x)) := by
      simpa [add_comm] using (Ideal.mem_jacobson_bot.mp hmemJac) (1 : henselizationRing (pairOfIdeal I))
    simpa [hy_eq] using hunit
  exact Ideal.eq_top_of_isUnit_mem _ hy hyUnit

/-- Helper for Lemma 15.12.8: on the first binary henselization coordinate, the image of
`I₁ ⊓ I₂` is the distinguished henselization ideal. -/
lemma binary_left_intersection_map_eq_henselizationIdeal (I₁ I₂ : Ideal A)
    (h : IsCoprime I₁ I₂) :
    Ideal.map (toHenselization (pairOfIdeal I₁)) (I₁ ⊓ I₂) =
      henselizationIdeal (pairOfIdeal I₁) := by
  -- Proof comment: `I₂` becomes the unit ideal in `A_1^h`, so intersecting with `I₂` does not
  -- change the image of `I₁`.
  calc
    Ideal.map (toHenselization (pairOfIdeal I₁)) (I₁ ⊓ I₂) =
        Ideal.map (toHenselization (pairOfIdeal I₁)) I₁ := by
          exact map_inf_eq_left_of_map_right_eq_top
            (f := toHenselization (pairOfIdeal I₁)) I₁ I₂
            (ideal_map_eq_top_of_isCoprime_to_henselization (I := I₁) (J := I₂) h)
    _ = henselizationIdeal (pairOfIdeal I₁) := by
      simpa [henselizationIdeal_eq_map (X := pairOfIdeal I₁)]

/-- Helper for Lemma 15.12.8: on the second binary henselization coordinate, the image of
`I₁ ⊓ I₂` is the distinguished henselization ideal. -/
lemma binary_right_intersection_map_eq_henselizationIdeal (I₁ I₂ : Ideal A)
    (h : IsCoprime I₁ I₂) :
    Ideal.map (toHenselization (pairOfIdeal I₂)) (I₁ ⊓ I₂) =
      henselizationIdeal (pairOfIdeal I₂) := by
  -- Proof comment: this is the same argument with the roles of `I₁` and `I₂` exchanged.
  calc
    Ideal.map (toHenselization (pairOfIdeal I₂)) (I₁ ⊓ I₂) =
        Ideal.map (toHenselization (pairOfIdeal I₂)) (I₂ ⊓ I₁) := by
          rw [inf_comm]
    _ = Ideal.map (toHenselization (pairOfIdeal I₂)) I₂ := by
          exact map_inf_eq_left_of_map_right_eq_top
            (f := toHenselization (pairOfIdeal I₂)) I₂ I₁
            (ideal_map_eq_top_of_isCoprime_to_henselization (I := I₂) (J := I₁) <| by
              rw [Ideal.isCoprime_iff_sup_eq] at h ⊢
              simpa [sup_comm] using h)
    _ = henselizationIdeal (pairOfIdeal I₂) := by
      simpa [henselizationIdeal_eq_map (X := pairOfIdeal I₂)]

/-- Helper for Lemma 15.12.8: the `Fin 2` family attached to `I₁, I₂` is pairwise comaximal as
soon as `I₁` and `I₂` are. -/
lemma binary_ideal_family_pairwise (I₁ I₂ : Ideal A) (h : IsCoprime I₁ I₂) :
    Pairwise fun i j : Fin 2 ↦
      IsCoprime
        (Fin.cases I₁ (fun _ ↦ I₂) i)
        (Fin.cases I₁ (fun _ ↦ I₂) j) := by
  have hsup : I₁ ⊔ I₂ = ⊤ := by
    rwa [Ideal.isCoprime_iff_sup_eq] at h
  intro i j hij
  -- Proof comment: after case-splitting on `Fin 2`, only the off-diagonal cases survive, and
  -- they are exactly the original comaximality hypothesis or its symmetric form.
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · simpa using h
  · rw [Ideal.isCoprime_iff_sup_eq]
    simpa [sup_comm] using hsup
  · exact (hij rfl).elim

/-- Helper for Lemma 15.12.8: the intersection of the binary `Fin 2` family is `I₁ ⊓ I₂`. -/
lemma binary_ideal_family_iInf (I₁ I₂ : Ideal A) :
    (⨅ i : Fin 2, Fin.cases I₁ (fun _ ↦ I₂) i) = I₁ ⊓ I₂ := by
  ext x
  rw [Ideal.mem_iInf, Ideal.mem_inf]
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · exact hx 0
    · exact hx 1
  · intro hx
    intro i
    fin_cases i
    · exact hx.1
    · exact hx.2

/-- Helper for Lemma 15.12.8: the product henselization pair has the expected special fiber, namely
the product of the quotients `A ⧸ I i`. -/
noncomputable def henselizationPiQuotientEquivPiQuotient [Finite ι] (I : ι → Ideal A) :
    ((∀ i, henselizationRing (pairOfIdeal (I i))) ⧸
        Ideal.pi (fun i ↦ henselizationIdeal (pairOfIdeal (I i)))) ≃+* ∀ i, A ⧸ I i :=
  (quotientPiRingEquivPiQuotient
    (R := fun i ↦ henselizationRing (pairOfIdeal (I i)))
    (I := fun i ↦ henselizationIdeal (pairOfIdeal (I i)))).trans <|
    RingEquiv.piCongrRight fun i ↦
      (RingEquiv.ofBijective
      (Ideal.quotientMap
          (henselizationIdeal (pairOfIdeal (I i)))
          (toHenselization (pairOfIdeal (I i)))
          (henselizationIdeal_le_comap_toHenselization (I := I i)))
        (henselization_quotientMap_bijective (I := I i))).symm

/-- Helper for Lemma 15.12.8: in the binary case, the quotient of the product henselization target
by its distinguished product ideal is canonically the same as `A ⧸ (I₁ ⊓ I₂)`. -/
noncomputable def binary_henselization_target_quotient_equiv (I₁ I₂ : Ideal A)
    (h : IsCoprime I₁ I₂) :
    ((∀ i : Fin 2, henselizationRing (pairOfIdeal (Fin.cases I₁ (fun _ ↦ I₂) i))) ⧸
        Ideal.pi
          (fun i : Fin 2 ↦
            henselizationIdeal (pairOfIdeal (Fin.cases I₁ (fun _ ↦ I₂) i)))) ≃+*
      A ⧸ (I₁ ⊓ I₂) :=
  let J : Fin 2 → Ideal A := fun i ↦ Fin.cases I₁ (fun _ ↦ I₂) i
  -- Proof comment: package the binary Chinese-remainder identification for the source ring and
  -- compose it with the already-proved product special-fiber equivalence for henselizations.
  let hquot :
      A ⧸ (I₁ ⊓ I₂) ≃+*
        ∀ i : Fin 2, A ⧸ J i :=
    (Ideal.quotEquivOfEq (by simpa [J] using (binary_ideal_family_iInf I₁ I₂)).symm).trans
      (Ideal.quotientInfRingEquivPiQuotient J <| by
        simpa [J] using (binary_ideal_family_pairwise I₁ I₂ h))
  show
      (((i : Fin 2) → henselizationRing (pairOfIdeal (J i))) ⧸
          Ideal.pi (fun i : Fin 2 ↦ henselizationIdeal (pairOfIdeal (J i)))) ≃+*
        A ⧸ (I₁ ⊓ I₂)
  simpa [J] using (henselizationPiQuotientEquivPiQuotient (I := J)).trans hquot.symm

/-- Helper for Lemma 15.12.8: the binary product henselization target is henselian for its
distinguished product ideal. -/
lemma binary_product_target_henselian (I₁ I₂ : Ideal A) :
    HenselianRing
      (∀ i : Fin 2, henselizationRing (pairOfIdeal (Fin.cases I₁ (fun _ ↦ I₂) i)))
      (Ideal.pi
        (fun i : Fin 2 ↦
          henselizationIdeal (pairOfIdeal (Fin.cases I₁ (fun _ ↦ I₂) i)))) := by
  let J : Fin 2 → Ideal A := fun i ↦ Fin.cases I₁ (fun _ ↦ I₂) i
  -- Proof comment: each coordinate henselization pair is henselian by construction, so the
  -- product pair is henselian by Lemma `15.11.11`.
  let _ : ∀ i : Fin 2, HenselianRing (henselizationRing (pairOfIdeal (J i)))
      (henselizationIdeal (pairOfIdeal (J i))) := fun i ↦ by
        change HenselianRing (henselizationPair (pairOfIdeal (J i))).ring
          (henselizationPair (pairOfIdeal (J i))).ideal
        exact (henselization (pairOfIdeal (J i))).property
  simpa [J] using
    (inferInstance :
      HenselianRing
        (∀ i : Fin 2, henselizationRing (pairOfIdeal (J i)))
        (Ideal.pi (fun i : Fin 2 ↦ henselizationIdeal (pairOfIdeal (J i)))))

/-- Helper for Lemma 15.12.8: the intersection ideal `(I₁ ⊓ I₂)` maps into the distinguished
product ideal of the binary henselization target. -/
lemma binary_intersection_le_comap_productIdeal (I₁ I₂ : Ideal A) :
    I₁ ⊓ I₂ ≤
      Ideal.comap
        (Pi.ringHom fun i : Fin 2 ↦
          (toHenselization (pairOfIdeal (Fin.cases I₁ (fun _ ↦ I₂) i)) :
            A →+* henselizationRing (pairOfIdeal (Fin.cases I₁ (fun _ ↦ I₂) i))))
        (Ideal.pi
          (fun i : Fin 2 ↦
            henselizationIdeal (pairOfIdeal (Fin.cases I₁ (fun _ ↦ I₂) i)))) := by
  intro x hx
  -- Proof comment: membership in the product ideal is coordinatewise, and each coordinate is the
  -- standard containment of `I₁` or `I₂` into its henselization ideal.
  rw [Ideal.mem_comap, Ideal.mem_pi]
  intro i
  fin_cases i
  · exact henselizationIdeal_le_comap_toHenselization (I := I₁) hx.1
  · exact henselizationIdeal_le_comap_toHenselization (I := I₂) hx.2

namespace RingPairCat

/-- Helper for Lemma 15.12.8: any packaged universal henselian pair over `X` receives the
canonical comparison map from the chosen henselization of `X` on underlying rings. -/
noncomputable def comparisonRingHomOfPairHenselizationData (X : RingPairCat.{u})
    (data : PairHenselizationData X) [henselianPairInclusion.IsRightAdjoint] :
    henselizationRing X →+* (henselianPairInclusion.obj data.obj).ring :=
  RingPairCat.ringHom
    ((((Adjunction.ofIsRightAdjoint henselianPairInclusion).homEquiv X data.obj).symm
      data.unit).hom)

/-- Helper for Lemma 15.12.8: the canonical comparison from the chosen henselization of `X` to
any packaged universal henselian pair over `X` is bijective. -/
lemma comparison_bijective_of_pair_henselization_data (X : RingPairCat.{u})
    (data : PairHenselizationData X) [henselianPairInclusion.IsRightAdjoint] :
    Function.Bijective (comparisonRingHomOfPairHenselizationData X data) := by
  let adj := Adjunction.ofIsRightAdjoint henselianPairInclusion
  let forward : henselization X ⟶ data.obj :=
    (adj.homEquiv X data.obj).symm data.unit
  let backward : data.obj ⟶ henselization X :=
    Classical.choose ((data.universal (henselization X)).surjective (adj.unit.app X))
  have hbackward :
      data.unit ≫ henselianPairInclusion.map backward = adj.unit.app X := by
    exact Classical.choose_spec ((data.universal (henselization X)).surjective (adj.unit.app X))
  have hforward :
      adj.homEquiv X data.obj forward = data.unit := by
    exact Equiv.apply_symm_apply (adj.homEquiv X data.obj) data.unit
  have hforward_unit :
      adj.unit.app X ≫ henselianPairInclusion.map forward = data.unit := by
    calc
      adj.unit.app X ≫ henselianPairInclusion.map forward =
          adj.homEquiv X data.obj forward := by
            symm
            exact adj.homEquiv_unit (X := X) (Y := data.obj) (f := forward)
      _ = data.unit := hforward
  have hbackward_forward :
      backward ≫ forward = 𝟙 data.obj := by
    apply (data.universal data.obj).injective
    calc
      data.unit ≫ henselianPairInclusion.map (backward ≫ forward) =
          (data.unit ≫ henselianPairInclusion.map backward) ≫
            henselianPairInclusion.map forward := by
              simp [Category.assoc]
      _ = adj.unit.app X ≫ henselianPairInclusion.map forward := by
        simpa [hbackward]
      _ = data.unit := hforward_unit
      _ = data.unit ≫ henselianPairInclusion.map (𝟙 data.obj) := by
        simp
  have hforward_backward :
      forward ≫ backward = 𝟙 (henselization X) := by
    apply (adj.homEquiv X (henselization X)).injective
    calc
      adj.homEquiv X (henselization X) (forward ≫ backward) =
          adj.unit.app X ≫ henselianPairInclusion.map (forward ≫ backward) :=
            adj.homEquiv_unit (X := X) (Y := henselization X) (f := forward ≫ backward)
      _ = (adj.unit.app X ≫ henselianPairInclusion.map forward) ≫
            henselianPairInclusion.map backward := by
              simp [Category.assoc]
      _ = data.unit ≫ henselianPairInclusion.map backward := by
        simpa [hforward_unit]
      _ = adj.unit.app X := hbackward
      _ = adj.homEquiv X (henselization X) (𝟙 (henselization X)) := by
        symm
        exact adj.homEquiv_unit (X := X) (Y := henselization X)
          (f := 𝟙 (henselization X))
  refine ⟨?_, ?_⟩
  · intro x y hxy
    -- Proof comment: the chosen backward morphism is a left inverse on underlying rings.
    have hx :
        RingPairCat.ringHom backward.hom
            ((comparisonRingHomOfPairHenselizationData X data) x) = x := by
      have hcomp := congrArg
        (fun k : henselization X ⟶ henselization X ↦ RingPairCat.ringHom k.hom x)
        hforward_backward
      simpa [comparisonRingHomOfPairHenselizationData, forward, RingPairCat.ringHom] using hcomp
    have hy :
        RingPairCat.ringHom backward.hom
            ((comparisonRingHomOfPairHenselizationData X data) y) = y := by
      have hcomp := congrArg
        (fun k : henselization X ⟶ henselization X ↦ RingPairCat.ringHom k.hom y)
        hforward_backward
      simpa [comparisonRingHomOfPairHenselizationData, forward, RingPairCat.ringHom] using hcomp
    calc
      x = RingPairCat.ringHom backward.hom
            ((comparisonRingHomOfPairHenselizationData X data) x) := hx.symm
      _ = RingPairCat.ringHom backward.hom
            ((comparisonRingHomOfPairHenselizationData X data) y) := by rw [hxy]
      _ = y := hy
  · intro y
    -- Proof comment: the same backward morphism is also a right inverse on underlying rings.
    refine ⟨RingPairCat.ringHom backward.hom y, ?_⟩
    have hcomp := congrArg
      (fun k : data.obj ⟶ data.obj ↦ RingPairCat.ringHom k.hom y)
      hbackward_forward
    simpa [comparisonRingHomOfPairHenselizationData, forward, RingPairCat.ringHom] using hcomp

end RingPairCat

/-
Domain-style sampling:
- primary domain: pair henselization in Chapter 15, with owner surface
  `henselizationRing (pairOfIdeal I)` and functoriality via `henselizationRingMap`;
- sampled same-kind declarations:
  `henselizationRing`,
  `toHenselization`,
  `henselizationRingMap`,
  `henselizationRing_existsUnique_algEquiv_of_zeroLocus_eq`;
- best owner abstraction: the canonical chosen henselization owner from `Lemma_15_12_1`, not a
  fresh public parameter for an arbitrary left adjoint to `henselianPairInclusion`;
- primitive data: `henselizationRing (pairOfIdeal I)`;
- derived API: the comparison map from the henselization of an intersection to the product of the
  henselizations of the components, and its bijectivity under pairwise comaximality.

Source/core/bridge triage:
- `source-facing`: `henselizationIntersectionToPi` and its bijectivity theorem;
- `core/canonical`: `henselizationRing`, `pairOfIdeal`, `toHenselization`, and
  `henselizationRingMap`;
- `bridge/view`: the product comparison map assembled from the canonical maps
  `henselizationRingMap (pairOfIdealMap (⨅ j, I j) (I i) (iInf_le I i))`.
-/

/-- The natural comparison map from the henselization ring of the intersection pair to the
product of the henselization rings of the component pairs. -/
def henselizationIntersectionToPi (I : ι → Ideal A) :
    henselizationRing (pairOfIdeal (⨅ j, I j)) →+*
      ∀ i : ι, henselizationRing (pairOfIdeal (I i)) :=
  Pi.ringHom fun i ↦
    henselizationRingMap (pairOfIdealMap (⨅ j, I j) (I i) (iInf_le I i))

-- Proof sketch: argue by induction on the finite index set, reducing to the case of two ideals by
-- grouping all but one ideal into their intersection. For two pairwise comaximal ideals, the
-- Chinese remainder theorem identifies the special fibres, and the universal property of pair
-- henselization upgrades that decomposition to an isomorphism of henselizations.
/-- Lemma 15.12.8: for a finite nonempty family of pairwise comaximal ideals in `A`, the chosen
henselization of the intersection pair `(A, ⋂ i, I i)` has a natural comparison map to the
product of the henselizations of `(A, I i)`, and that map is bijective. -/
@[stacks 0H7Q]
theorem henselizationIntersectionToPi_bijective [Finite ι] [Nonempty ι]
    (I : ι → Ideal A) (hI : Pairwise fun i j ↦ IsCoprime (I i) (I j)) :
    Function.Bijective (henselizationIntersectionToPi I) := by
  classical
  -- Proof comment: the verified frontier now matches the two reusable pieces of the source proof:
  -- the induction bridge `isCoprime_iInf_of_pairwise`, the generic comparison-bijectivity lemma
  -- `RingPairCat.comparison_bijective_of_pair_henselization_data`, the binary henselian target
  -- packaging (`binary_product_target_henselian`, `binary_intersection_le_comap_productIdeal`),
  -- and the binary special-fiber comparison `binary_henselization_target_quotient_equiv`.
  -- Route correction: the remaining blocker is no longer the finite ideal-combinatorics layer.
  -- What is still missing is the source-faithful binary `PairHenselizationData` whose target is
  -- `A₁^h × A₂^h`; once that cofinal/product package is built, the generic comparison lemma above
  -- identifies the binary map as an isomorphism, and the existing finite induction can finish.
  -- TODO: construct the binary `PairHenselizationData`, identify its comparison with
  -- `henselizationIntersectionToPi` for `Fin 2`, then reindex to `Fin n`, split off coordinate
  -- `0`, and close the induction using `isCoprime_iInf_of_pairwise`.
  sorry

end
