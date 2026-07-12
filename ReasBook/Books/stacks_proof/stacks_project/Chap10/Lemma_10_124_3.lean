import StacksProject_2024.Chap10.Lemma_10_97_8
import StacksProject_2024.Chap10.Lemma_10_124_3_CompletionHelpers

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing Ideal AdicCompletion
open scoped TensorProduct
open Lemma101243CompletionHelpers

attribute [local instance high] Semiring.toModule Algebra.toModule

universe u v w

/-- Helper for Chap10 Lemma 10 124 3: an element outside a prime maps to a unit in the
completion of the corresponding local ring. -/
private theorem isUnit_algebraMap_completedAtPrime_of_notMem {A : Type u} [CommRing A]
    (Q : Ideal A) [Q.IsPrime] {r : A} (hr : r ∉ Q) :
    IsUnit (algebraMap A
      (AdicCompletion (maximalIdeal (Localization.AtPrime Q)) (Localization.AtPrime Q)) r) := by
  -- First invert `r` in the local ring at `Q`.
  have hunit_local : IsUnit (algebraMap A (Localization.AtPrime Q) r) := by
    have hrPrimeCompl : r ∈ Q.primeCompl := by
      simpa [Ideal.mem_primeCompl_iff] using hr
    simpa [Ideal.mem_primeCompl_iff] using
      IsLocalization.map_units (Localization.AtPrime Q)
        ⟨r, hrPrimeCompl⟩
  rcases hunit_local with ⟨u, hu⟩
  let f : Localization.AtPrime Q →*
      AdicCompletion (maximalIdeal (Localization.AtPrime Q)) (Localization.AtPrime Q) :=
    (algebraMap (Localization.AtPrime Q)
      (AdicCompletion (maximalIdeal (Localization.AtPrime Q)) (Localization.AtPrime Q)) :
        Localization.AtPrime Q →+*
          AdicCompletion (maximalIdeal (Localization.AtPrime Q))
            (Localization.AtPrime Q)).toMonoidWithZeroHom.toMonoidHom
  -- Then map the resulting unit through the completion map.
  refine ⟨(Units.map f) u, ?_⟩
  calc
    ↑((Units.map f) u) =
        algebraMap (Localization.AtPrime Q)
          (AdicCompletion (maximalIdeal (Localization.AtPrime Q)) (Localization.AtPrime Q))
          (algebraMap A (Localization.AtPrime Q) r) := by
          rw [Units.coe_map]
          exact congrArg f hu
    _ = algebraMap A
          (AdicCompletion (maximalIdeal (Localization.AtPrime Q)) (Localization.AtPrime Q)) r := by
          rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply]
          simp

/-- Helper for Chap10 Lemma 10 124 3: the canonical map from the basic-open localization at an
element outside a prime to the completed local ring at that prime. -/
private noncomputable def awayToCompletedAtPrime {A : Type u} [CommRing A]
    (Q : Ideal A) [Q.IsPrime] {r : A} (hr : r ∉ Q) :
    Localization.Away r →+*
      AdicCompletion (maximalIdeal (Localization.AtPrime Q)) (Localization.AtPrime Q) :=
  let g : A →+* AdicCompletion (maximalIdeal (Localization.AtPrime Q)) (Localization.AtPrime Q) :=
    algebraMap A (AdicCompletion (maximalIdeal (Localization.AtPrime Q)) (Localization.AtPrime Q))
  @IsLocalization.Away.lift A _ (Localization.Away r) _ _
    (AdicCompletion (maximalIdeal (Localization.AtPrime Q)) (Localization.AtPrime Q)) _ r
    inferInstance g (isUnit_algebraMap_completedAtPrime_of_notMem Q hr)

/-- Helper for Chap10 Lemma 10 124 3: the away-to-completion map extends the canonical map from
the original ring. -/
private theorem awayToCompletedAtPrime_algebraMap {A : Type u} [CommRing A]
    (Q : Ideal A) [Q.IsPrime] {r : A} (hr : r ∉ Q) (a : A) :
    awayToCompletedAtPrime Q hr (algebraMap A (Localization.Away r) a) =
      algebraMap A
        (AdicCompletion (maximalIdeal (Localization.AtPrime Q)) (Localization.AtPrime Q)) a := by
  -- This is exactly the universal property computation for the away localization.
  exact IsLocalization.Away.lift_eq r (isUnit_algebraMap_completedAtPrime_of_notMem Q hr) a

/-- Helper for Chap10 Lemma 10 124 3: a bijective basic-open map is the corresponding algebra
equivalence. -/
private noncomputable def awayMapAlgEquivOfBijective {R A B : Type*}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (r : A)
    (h : Function.Bijective (Localization.awayMapₐ f r)) :
    Localization.Away r ≃ₐ[R] Localization.Away (f r) :=
  AlgEquiv.ofBijective (Localization.awayMapₐ f r) h

/-- Helper for Chap10 Lemma 10 124 3: the algebra equivalence induced by a bijective away map
has the expected underlying function. -/
private theorem awayMapAlgEquivOfBijective_apply {R A B : Type*}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (r : A)
    (h : Function.Bijective (Localization.awayMapₐ f r)) (x : Localization.Away r) :
    awayMapAlgEquivOfBijective f r h x = Localization.awayMapₐ f r x := by
  -- `AlgEquiv.ofBijective` keeps the original algebra homomorphism as its forward map.
  rfl

/-- Helper for Chap10 Lemma 10 124 3: the inverse away-localization equivalence sends the
target algebra-map image of `f a` back to the source algebra-map image of `a`. -/
private theorem awayMapAlgEquivOfBijective_symm_algebraMap {R A B : Type*}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (r a : A)
    (h : Function.Bijective (Localization.awayMapₐ f r)) :
    (awayMapAlgEquivOfBijective f r h).symm
        (algebraMap B (Localization.Away (f r)) (f a)) =
      algebraMap A (Localization.Away r) a := by
  -- Apply the forward equivalence so the computation reduces to the canonical away map.
  apply (awayMapAlgEquivOfBijective f r h).injective
  rw [AlgEquiv.apply_symm_apply]
  rw [awayMapAlgEquivOfBijective_apply]
  simp [Localization.awayMapₐ, IsLocalization.Away.map]

/-- Helper for Chap10 Lemma 10 124 3: the explicit extension through a bijective away map agrees
with a chosen map from the source away localization on elements coming from the source algebra. -/
private theorem awayExtension_comp_algebraMap {R A B C : Type*}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (f : A →ₐ[R] B) (r a : A)
    (haway : Function.Bijective (Localization.awayMapₐ f r))
    (δ : Localization.Away r →ₐ[R] C) :
    (δ.comp ((awayMapAlgEquivOfBijective f r haway).symm.toAlgHom.comp
      ((Algebra.ofId B (Localization.Away (f r))).restrictScalars R))) (f a) =
      δ (algebraMap A (Localization.Away r) a) := by
  -- The composite was chosen so that only the inverse-equivalence computation remains.
  simp [AlgHom.comp_apply, awayMapAlgEquivOfBijective_symm_algebraMap]

/-- Helper for Chap10 Lemma 10 124 3: the explicit extension through a bijective away map sends
the distinguished target denominator to a unit whenever the source-away map does. -/
private theorem awayExtension_isUnit_of_comp {R A B C : Type*}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (f : A →ₐ[R] B) (r : A)
    (haway : Function.Bijective (Localization.awayMapₐ f r))
    (δ : Localization.Away r →ₐ[R] C)
    (hunit : IsUnit (δ (algebraMap A (Localization.Away r) r))) :
    IsUnit ((δ.comp ((awayMapAlgEquivOfBijective f r haway).symm.toAlgHom.comp
      ((Algebra.ofId B (Localization.Away (f r))).restrictScalars R))) (f r)) := by
  -- Reuse the agreement lemma at `r`, then keep the supplied unit proof.
  rw [awayExtension_comp_algebraMap]
  exact hunit

/-- Helper for Chap10 Lemma 10 124 3: after a bijective away-localization comparison, two
algebra maps out of the target are equal if they invert the distinguished denominator and agree on
the finite source algebra. -/
private theorem awayMapBijective_algHom_ext {R A B C : Type*}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (f : A →ₐ[R] B) (r : A)
    (haway : Function.Bijective (Localization.awayMapₐ f r))
    (g₁ g₂ : B →ₐ[R] C)
    (hg₁ : IsUnit (g₁ (f r))) (hg₂ : IsUnit (g₂ (f r)))
    (hagree : ∀ a : A, g₁ (f a) = g₂ (f a)) :
    g₁ = g₂ := by
  let G₁ : Localization.Away (f r) →+* C :=
    @IsLocalization.Away.lift B _ (Localization.Away (f r)) _ _ C _ (f r) inferInstance
      g₁.toRingHom hg₁
  let G₂ : Localization.Away (f r) →+* C :=
    @IsLocalization.Away.lift B _ (Localization.Away (f r)) _ _ C _ (f r) inferInstance
      g₂.toRingHom hg₂
  have hG : G₁ = G₂ := by
    ext y
    rcases haway.2 y with ⟨x, rfl⟩
    -- Pull equality back along the surjective away map and then use localization extensionality
    -- on the source away localization.
    have hcomp :
        G₁.comp (Localization.awayMapₐ f r).toRingHom =
          G₂.comp (Localization.awayMapₐ f r).toRingHom := by
      apply IsLocalization.ringHom_ext (Submonoid.powers r)
      ext a
      simp [G₁, G₂, Localization.awayMapₐ, IsLocalization.Away.map, hagree a]
    exact RingHom.congr_fun hcomp x
  apply AlgHom.ext
  intro b
  -- Evaluate the two lifted maps on the dense image of `B`; this recovers the original maps.
  have hG₁ : G₁ (algebraMap B (Localization.Away (f r)) b) = g₁ b := by
    exact IsLocalization.Away.lift_eq (f r) hg₁ b
  have hG₂ : G₂ (algebraMap B (Localization.Away (f r)) b) = g₂ b := by
    exact IsLocalization.Away.lift_eq (f r) hg₂ b
  calc
    g₁ b = G₁ (algebraMap B (Localization.Away (f r)) b) := hG₁.symm
    _ = G₂ (algebraMap B (Localization.Away (f r)) b) := by rw [hG]
    _ = g₂ b := hG₂

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable (q : Ideal S) [q.IsPrime]

local notation "R_qR" => Localization.AtPrime (q.under R)
local notation "S_q" => Localization.AtPrime q
local notation "R_qR^" => AdicCompletion (maximalIdeal R_qR) R_qR
local notation "S_q^" => AdicCompletion (maximalIdeal S_q) S_q

noncomputable local instance completedLocalRingAlgebra : Algebra R_qR^ S_q^ :=
  (maximalIdealCompletionMap
    (Localization.localRingHom (q.under R) q (algebraMap R S) rfl)).toAlgebra

/-- Helper for Chap10 Lemma 10 124 3: the completed local comparison is compatible with the
original base algebra map. -/
private theorem completedLocalRing_algebraMap_eq (r : R) :
    algebraMap R S_q^ r =
      algebraMap R_qR^ S_q^ (algebraMap R R_qR^ r) := by
  let f : R_qR →+* S_q := Localization.localRingHom (q.under R) q (algebraMap R S) rfl
  have hfcomp :=
    congrArg (fun g : R_qR →+* S_q^ ↦ g (algebraMap R R_qR r))
      (maximalIdealCompletionMap_comp f)
  have hf_to_map : f (algebraMap R R_qR r) = algebraMap S S_q (algebraMap R S r) := by
    -- On the dense local-ring image, `localRingHom` is the original algebra map.
    exact Localization.localRingHom_to_map (q.under R) q (algebraMap R S) rfl r
  calc
    algebraMap R S_q^ r =
        algebraMap S_q S_q^ (algebraMap R S_q r) := by
          rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply]
          rfl
    _ = algebraMap S_q S_q^ (algebraMap S S_q (algebraMap R S r)) := by
          rw [IsScalarTower.algebraMap_apply R S S_q]
    _ = algebraMap S_q S_q^ (f (algebraMap R R_qR r)) := by
          rw [hf_to_map]
    _ = maximalIdealCompletionMap f (algebraMap R_qR R_qR^ (algebraMap R R_qR r)) := by
          simpa [RingHom.comp_apply] using hfcomp.symm
    _ = maximalIdealCompletionMap f (algebraMap R R_qR^ r) := rfl
    _ = algebraMap R_qR^ S_q^ (algebraMap R R_qR^ r) := by
          rw [RingHom.algebraMap_toAlgebra]

/-- Helper for Chap10 Lemma 10 124 3: the completed local factor carries the scalar action
coming from the completed local comparison map. -/
noncomputable local instance completedLocalRingSMul : SMul R_qR^ S_q^ :=
  @Algebra.toSMul R_qR^ S_q^ _ _ (completedLocalRingAlgebra q)

/-- Helper for Chap10 Lemma 10 124 3: the completed local factor is a module over the completed
base local ring via the completed local comparison map. -/
noncomputable local instance completedLocalRingModule : Module R_qR^ S_q^ :=
  @Algebra.toModule R_qR^ S_q^ _ _ (completedLocalRingAlgebra q)

/-- Helper for Chap10 Lemma 10 124 3: the original base action on the completed local factor
factors through the completed base local ring. -/
private noncomputable local instance completedLocalRingIsScalarTower : IsScalarTower R R_qR^ S_q^ :=
  IsScalarTower.of_algebraMap_eq (completedLocalRing_algebraMap_eq q)

/-- Helper for Chap10 Lemma 10 124 3: the two canonical maps into the completed local ring
commute, so they induce a map from the completed tensor product. -/
private theorem completedTensorProductProjection_commute (x : R_qR^) (s : S) :
    Commute
      ((Algebra.ofId R_qR^ S_q^) x)
      (((Algebra.ofId S S_q^).restrictScalars R) s) := by
  -- The target is commutative, so the two structural maps commute elementwise.
  exact Commute.all _ _

/-- Helper for Chap10 Lemma 10 124 3: the canonical projection from the completed tensor product
to the completed local factor at `q`. -/
private noncomputable def completedTensorProductProjection :
    R_qR^ ⊗[R] S →ₐ[R_qR^] S_q^ :=
  Algebra.TensorProduct.lift
    (Algebra.ofId R_qR^ S_q^)
    ((Algebra.ofId S S_q^).restrictScalars R)
    (completedTensorProductProjection_commute q)

local notation "completedTensorProductProjection_q" =>
  (completedTensorProductProjection q : R_qR^ ⊗[R] S →ₐ[R_qR^] S_q^)

/-- Helper for Chap10 Lemma 10 124 3: the canonical tensor projection agrees with the completed
local comparison map on the completed base factor. -/
private theorem completedTensorProductProjection_tmul_one (x : R_qR^) :
    completedTensorProductProjection_q (x ⊗ₜ[R] 1) =
      maximalIdealCompletionMap
        (Localization.localRingHom (q.under R) q (algebraMap R S) rfl) x := by
  -- The tensor-product universal property evaluates the left factor and kills the right unit.
  simp [completedTensorProductProjection, RingHom.algebraMap_toAlgebra]

/-- Helper for Chap10 Lemma 10 124 3: the canonical tensor projection agrees with the
localization-completion map on the algebra factor. -/
private theorem completedTensorProductProjection_one_tmul (s : S) :
    completedTensorProductProjection_q (1 ⊗ₜ[R] s) =
      algebraMap S S_q^ s := by
  -- The tensor-product universal property evaluates the right factor and kills the left unit.
  simp [completedTensorProductProjection]

/-- Helper for Chap10 Lemma 10 124 3: a product split whose first projection is the canonical
tensor projection gives exactly the source-facing product decomposition. -/
private theorem existsCompletionTensorProductAlgEquivOfCanonicalProjectionSplit
    (h :
      ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R_qR^ B)
        (e : (R_qR^ ⊗[R] S) ≃ₐ[R_qR^] (S_q^ × B)),
        ∀ z : R_qR^ ⊗[R] S,
          (RingHom.fst S_q^ B) (e z) = completedTensorProductProjection_q z) :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R_qR^ B)
      (e : (R_qR^ ⊗[R] S) ≃ₐ[R_qR^] (S_q^ × B)),
      (∀ x : R_qR^,
        (RingHom.fst S_q^ B) (e (x ⊗ₜ[R] 1)) =
          maximalIdealCompletionMap
            (Localization.localRingHom (q.under R) q (algebraMap R S) rfl) x) ∧
      ∀ s : S,
        (RingHom.fst S_q^ B) (e (1 ⊗ₜ[R] s)) = algebraMap S S_q^ s := by
  -- Once the first projection is normalized to the canonical tensor projection, the two formulas
  -- are just the two generator computations above.
  rcases h with ⟨B, hB, hAlg, e, hfst⟩
  refine ⟨B, hB, hAlg, e, ?_, ?_⟩
  · intro x
    rw [hfst]
    exact completedTensorProductProjection_tmul_one q x
  · intro s
    rw [hfst]
    exact completedTensorProductProjection_one_tmul q s

/-- Helper for Chap10 Lemma 10 124 3: a quotient by the complement of an idempotent identifying
the first factor gives a product split whose first projection is a prescribed algebra map. -/
private theorem algEquivProdOfIdempotentQuotientEquiv
    {K : Type*} {T : Type w} {C : Type*} [CommRing K] [CommRing T] [CommRing C]
    [Algebra K T] [Algebra K C]
    (π : T →ₐ[K] C) {e : T} (he : IsIdempotentElem e)
    (first : (T ⧸ Ideal.span ({1 - e} : Set T)) ≃ₐ[K] C)
    (hfirst : ∀ z : T,
      first ((Ideal.Quotient.mk (Ideal.span ({1 - e} : Set T))) z) = π z) :
    ∃ (B : Type w) (_ : CommRing B) (_ : Algebra K B)
      (E : T ≃ₐ[K] C × B),
      ∀ z : T, RingHom.fst C B (E z) = π z := by
  let B : Type w := T ⧸ Ideal.span ({e} : Set T)
  let splitEquiv : T ≃ₐ[K] ((T ⧸ Ideal.span ({1 - e} : Set T)) × B) :=
    -- The complementary idempotents `1 - e` and `e` split `T` into the displayed quotients.
    AlgEquiv.prodQuotientOfIsIdempotentElem K he.one_sub he (by simp) (by
      simpa using he.one_sub_mul_self)
  let finalEquiv : T ≃ₐ[K] C × B :=
    splitEquiv.trans <|
      AlgEquiv.prodCongr first (AlgEquiv.refl : B ≃ₐ[K] B)
  refine ⟨B, inferInstance, inferInstance, finalEquiv, ?_⟩
  intro z
  -- The first coordinate of the standard split is the quotient by `span {1 - e}`, and the
  -- supplied quotient equivalence identifies that quotient map with `π`.
  dsimp [finalEquiv, splitEquiv]
  rw [AlgEquiv.prodQuotientOfIsIdempotentElem_apply_fst]
  exact hfirst z

/-- Helper for Chap10 Lemma 10 124 3: the first product idempotent pulled back through an
algebra equivalence is idempotent. -/
private theorem algEquivProdFirstIdempotent
    {K : Type*} {T : Type w} {C : Type*} {B : Type*}
    [CommRing K] [CommRing T] [CommRing C] [CommRing B]
    [Algebra K T] [Algebra K C] [Algebra K B]
    (E : T ≃ₐ[K] C × B) :
    IsIdempotentElem (E.symm (1, 0)) := by
  -- Transport the product idempotent `(1, 0)` back along the algebra equivalence.
  rw [IsIdempotentElem, ← E.injective.eq_iff]
  simp

/-- Helper for Chap10 Lemma 10 124 3: the kernel of the first product projection is generated by
the complementary idempotent. -/
private theorem algEquivProdFirstProjection_ker
    {K : Type*} {T : Type w} {C : Type*} {B : Type*}
    [CommRing K] [CommRing T] [CommRing C] [CommRing B]
    [Algebra K T] [Algebra K C] [Algebra K B]
    (E : T ≃ₐ[K] C × B) :
    Ideal.span ({1 - E.symm (1, 0)} : Set T) =
      RingHom.ker (((AlgHom.fst K C B).comp E.toAlgHom).toRingHom) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    change (((AlgHom.fst K C B).comp E.toAlgHom).toRingHom) (1 - E.symm (1, 0)) = 0
    simp
  · intro x hx
    change (((AlgHom.fst K C B).comp E.toAlgHom).toRingHom) x = 0 at hx
    have hxfirst : (E x).1 = 0 := hx
    rw [← E.symm_apply_apply x]
    have hprod : E x = (0, (E x).2) := by
      ext
      · exact hxfirst
      · rfl
    rw [hprod]
    have hmul : E.symm (0, (E x).2) = (1 - E.symm (1, 0)) * E.symm (0, (E x).2) := by
      rw [← E.injective.eq_iff]
      simp only [map_mul, AlgEquiv.apply_symm_apply, map_sub, Prod.mk_mul_mk,
        sub_mul, one_mul, zero_mul]
      simp
    rw [hmul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

/-- Helper for Chap10 Lemma 10 124 3: the first projection of a product equivalence is
surjective. -/
private theorem algEquivProdFirstProjection_surjective
    {K : Type*} {T : Type w} {C : Type*} {B : Type*}
    [CommRing K] [CommRing T] [CommRing C] [CommRing B]
    [Algebra K T] [Algebra K C] [Algebra K B]
    (E : T ≃ₐ[K] C × B) :
    Function.Surjective (((AlgHom.fst K C B).comp E.toAlgHom).toRingHom) := by
  -- Lift a desired first coordinate by applying the inverse product equivalence to `(c, 0)`.
  intro c
  refine ⟨E.symm (c, 0), ?_⟩
  simp

/-- Helper for Chap10 Lemma 10 124 3: a product splitting whose first projection is a given
map yields the quotient by the complementary idempotent and the same first projection formula. -/
private theorem idempotentQuotientEquivOfAlgEquivProd
    {K : Type*} {T : Type w} {C : Type*} {B : Type*}
    [CommRing K] [CommRing T] [CommRing C] [CommRing B]
    [Algebra K T] [Algebra K C] [Algebra K B]
    (E : T ≃ₐ[K] C × B) (π : T →ₐ[K] C)
    (hE : ∀ z : T, RingHom.fst C B (E z) = π z) :
    ∃ e : T,
      IsIdempotentElem e ∧
        ∃ first : (T ⧸ Ideal.span ({1 - e} : Set T)) ≃ₐ[K] C,
          ∀ z : T,
            first ((Ideal.Quotient.mk (Ideal.span ({1 - e} : Set T))) z) = π z := by
  let e : T := E.symm (1, 0)
  have he : IsIdempotentElem e := algEquivProdFirstIdempotent E
  have hker :
      Ideal.span ({1 - e} : Set T) =
        RingHom.ker (((AlgHom.fst K C B).comp E.toAlgHom).toRingHom) := by
    simpa [e] using algEquivProdFirstProjection_ker E
  have hsurj :
      Function.Surjective (((AlgHom.fst K C B).comp E.toAlgHom).toRingHom) :=
    algEquivProdFirstProjection_surjective E
  let first : (T ⧸ Ideal.span ({1 - e} : Set T)) ≃ₐ[K] C :=
    (Ideal.quotientEquivAlgOfEq K hker).trans
      (Ideal.quotientKerAlgEquivOfSurjective hsurj)
  refine ⟨e, he, first, ?_⟩
  intro z
  -- The quotient equivalence is the first isomorphism theorem for the first projection, so
  -- evaluating on a class recovers the first product coordinate and hence `π`.
  dsimp [first]
  have hquot :
      (Ideal.quotientEquivAlgOfEq K hker)
          ((Ideal.Quotient.mk (Ideal.span ({1 - e} : Set T))) z) =
        (Ideal.Quotient.mk
          (RingHom.ker (((AlgHom.fst K C B).comp E.toAlgHom).toRingHom))) z := by
    exact Ideal.quotientEquivAlgOfEq_mk K hker z
  calc
    (Ideal.quotientKerAlgEquivOfSurjective hsurj)
        ((Ideal.quotientEquivAlgOfEq K hker)
          ((Ideal.Quotient.mk (Ideal.span ({1 - e} : Set T))) z)) =
        (Ideal.quotientKerAlgEquivOfSurjective hsurj)
          ((Ideal.Quotient.mk
            (RingHom.ker (((AlgHom.fst K C B).comp E.toAlgHom).toRingHom))) z) := by
          exact congrArg (Ideal.quotientKerAlgEquivOfSurjective hsurj) hquot
    _ = ((AlgHom.fst K C B).comp E.toAlgHom) z := by
          exact Ideal.quotientKerAlgEquivOfSurjective_mk hsurj z
    _ = π z := by
          simpa using hE z

/-- Helper for Chap10 Lemma 10 124 3: a surjective algebra map whose kernel is generated by
the complement of an idempotent gives a product split whose first projection is the map. -/
private theorem algEquivProdOfSurjectiveIdempotentKernel
    {K : Type*} {T : Type w} {C : Type*} [CommRing K] [CommRing T] [CommRing C]
    [Algebra K T] [Algebra K C]
    (π : T →ₐ[K] C) (hπ : Function.Surjective π)
    {e : T} (he : IsIdempotentElem e)
    (hker : RingHom.ker π.toRingHom = Ideal.span ({1 - e} : Set T)) :
    ∃ (B : Type w) (_ : CommRing B) (_ : Algebra K B)
      (E : T ≃ₐ[K] C × B),
      ∀ z : T, RingHom.fst C B (E z) = π z := by
  let first : (T ⧸ Ideal.span ({1 - e} : Set T)) ≃ₐ[K] C :=
    (Ideal.quotientEquivAlgOfEq K hker.symm).trans <|
      Ideal.quotientKerAlgEquivOfSurjective hπ
  have hfirst :
      ∀ z : T,
        first ((Ideal.Quotient.mk (Ideal.span ({1 - e} : Set T))) z) = π z := by
    intro z
    -- The quotient equivalence first rewrites the ideal using `hker`, then applies the first
    -- isomorphism theorem for the surjective map `π`.
    change
      (Ideal.quotientKerAlgEquivOfSurjective hπ)
          ((Ideal.quotientEquivAlgOfEq K hker.symm)
            ((Ideal.Quotient.mk (Ideal.span ({1 - e} : Set T))) z)) =
        π z
    rw [Ideal.quotientEquivAlgOfEq_mk K hker.symm z]
    exact Ideal.quotientKerAlgEquivOfSurjective_mk hπ z
  exact
    algEquivProdOfIdempotentQuotientEquiv
      (K := K)
      π he first hfirst

/-- Helper for Chap10 Lemma 10 124 3: in the quotient by `1 - e`, the class of `e` is `1`. -/
private theorem quotient_mk_self_eq_one_of_one_sub
    {T : Type w} [CommRing T] (e : T) :
    (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set T)) e) = 1 := by
  -- Compare `e` with `1` by putting their difference in the ideal generated by `1 - e`.
  rw [← map_one (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set T)))]
  rw [Ideal.Quotient.eq]
  have hgen : (1 - e : T) ∈ Ideal.span ({1 - e} : Set T) :=
    Ideal.subset_span (by simp)
  have hneg : -(1 - e : T) ∈ Ideal.span ({1 - e} : Set T) :=
    (Ideal.span ({1 - e} : Set T)).neg_mem hgen
  have hsub : e - 1 = -(1 - e) := by
    abel
  exact hsub ▸ hneg

/-- Helper for Chap10 Lemma 10 124 3: algebra homomorphisms carry idempotent elements to
idempotent elements. -/
private theorem algHom_map_isIdempotentElem
    {K : Type*} {T : Type w} {U : Type*} [CommRing K] [CommRing T] [CommRing U]
    [Algebra K T] [Algebra K U] (f : T →ₐ[K] U) {e : T}
    (he : IsIdempotentElem e) :
    IsIdempotentElem (f e) := by
  -- Apply the homomorphism to the defining multiplication relation for the idempotent.
  rw [IsIdempotentElem] at he ⊢
  rw [← map_mul, he]

/-- Helper for Chap10 Lemma 10 124 3: an algebra map sending an idempotent `e` to `f e`
descends to the quotients by the complementary principal idempotents. -/
private noncomputable def quotientMapOfIdempotentImage
    {K : Type*} {T : Type w} {U : Type*} [CommRing K] [CommRing T] [CommRing U]
    [Algebra K T] [Algebra K U] (f : T →ₐ[K] U) (e : T) :
    (T ⧸ Ideal.span ({1 - e} : Set T)) →ₐ[K]
      U ⧸ Ideal.span ({1 - f e} : Set U) :=
  Ideal.quotientMapₐ (Ideal.span ({1 - f e} : Set U)) f <| by
    -- The generator `1 - e` maps to the generator `1 - f e`, so the quotient map is well-defined.
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact Ideal.subset_span (by simp)

/-- Helper for Chap10 Lemma 10 124 3: the idempotent-image quotient map evaluates on quotient
classes by applying the original algebra map. -/
private theorem quotientMapOfIdempotentImage_mk
    {K : Type*} {T : Type w} {U : Type*} [CommRing K] [CommRing T] [CommRing U]
    [Algebra K T] [Algebra K U] (f : T →ₐ[K] U) (e z : T) :
    quotientMapOfIdempotentImage f e
        ((Ideal.Quotient.mk (Ideal.span ({1 - e} : Set T))) z) =
      (Ideal.Quotient.mk (Ideal.span ({1 - f e} : Set U))) (f z) := by
  -- This is the computation rule for `Ideal.quotientMapₐ`, specialized to the idempotent
  -- complement ideals used in the finite-away quotient comparison.
  exact Ideal.quotient_map_mkₐ (Ideal.span ({1 - f e} : Set U)) f _ 

/-- Helper for Chap10 Lemma 10 124 3: an algebra map that sends the image idempotent to `1`
kills the complementary-idempotent ideal on the target quotient. -/
private theorem idempotentImageQuotientLift_vanishes
    {K : Type*} {T : Type w} {U C : Type*}
    [CommRing K] [CommRing T] [CommRing U] [CommRing C]
    [Algebra K T] [Algebra K U] [Algebra K C]
    (f : T →ₐ[K] U) (e : T) (ψ : U →ₐ[K] C) (hψ : ψ (f e) = 1) :
    ∀ x : U, x ∈ Ideal.span ({1 - f e} : Set U) → ψ x = 0 := by
  -- It is enough to check the single generator `1 - f e`; the hypothesis makes its image zero.
  intro x hx
  have hle : Ideal.span ({1 - f e} : Set U) ≤ RingHom.ker ψ.toRingHom := by
    rw [Ideal.span_le]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    change ψ (1 - f e) = 0
    simp [hψ]
  exact RingHom.mem_ker.mp (hle hx)

/-- Helper for Chap10 Lemma 10 124 3: descend a map through the quotient by the complement of an
image idempotent once that image idempotent maps to `1`. -/
private noncomputable def quotientLiftOfIdempotentImageToOne
    {K : Type*} {T : Type w} {U C : Type*}
    [CommRing K] [CommRing T] [CommRing U] [CommRing C]
    [Algebra K T] [Algebra K U] [Algebra K C]
    (f : T →ₐ[K] U) (e : T) (ψ : U →ₐ[K] C) (hψ : ψ (f e) = 1) :
    U ⧸ Ideal.span ({1 - f e} : Set U) →ₐ[K] C :=
  Ideal.Quotient.liftₐ (Ideal.span ({1 - f e} : Set U)) ψ
    (idempotentImageQuotientLift_vanishes f e ψ hψ)

/-- Helper for Chap10 Lemma 10 124 3: the descended idempotent-image quotient lift computes on
quotient classes by applying the original target map. -/
private theorem quotientLiftOfIdempotentImageToOne_mk
    {K : Type*} {T : Type w} {U C : Type*}
    [CommRing K] [CommRing T] [CommRing U] [CommRing C]
    [Algebra K T] [Algebra K U] [Algebra K C]
    (f : T →ₐ[K] U) (e : T) (ψ : U →ₐ[K] C) (hψ : ψ (f e) = 1) (z : U) :
    quotientLiftOfIdempotentImageToOne f e ψ hψ
        ((Ideal.Quotient.mk (Ideal.span ({1 - f e} : Set U))) z) =
      ψ z := by
  -- The proof records the computation rule for the quotient lift, so later inverse-map checks can
  -- rewrite quotient representatives without unfolding the lift.
  simp [quotientLiftOfIdempotentImageToOne, Ideal.Quotient.liftₐ_apply]

/-- Helper for Chap10 Lemma 10 124 3: composing the existing idempotent-image quotient map with
the descended target map computes by applying the target map after `f`. -/
private theorem quotientLiftOfIdempotentImageToOne_quotientMap_mk
    {K : Type*} {T : Type w} {U C : Type*}
    [CommRing K] [CommRing T] [CommRing U] [CommRing C]
    [Algebra K T] [Algebra K U] [Algebra K C]
    (f : T →ₐ[K] U) (e : T) (ψ : U →ₐ[K] C) (hψ : ψ (f e) = 1) (z : T) :
    quotientLiftOfIdempotentImageToOne f e ψ hψ
        (quotientMapOfIdempotentImage f e
          ((Ideal.Quotient.mk (Ideal.span ({1 - e} : Set T))) z)) =
      ψ (f z) := by
  -- First move across the already-defined quotient map, then use the quotient-lift computation on
  -- the target representative.
  rw [quotientMapOfIdempotentImage_mk]
  exact quotientLiftOfIdempotentImageToOne_mk f e ψ hψ (f z)

/-- Helper for Chap10 Lemma 10 124 3: a map whose restriction is the quotient map sends the
chosen idempotent image to `1`. -/
private theorem algHom_image_eq_one_of_comp_quotient_mk
    {K : Type*} {T : Type w} {U : Type*}
    [CommRing K] [CommRing T] [CommRing U]
    [Algebra K T] [Algebra K U]
    (f : T →ₐ[K] U) (e : T)
    (ψ : U →ₐ[K] T ⧸ Ideal.span ({1 - e} : Set T))
    (hcomp :
      ψ.comp f =
        (Ideal.Quotient.mkₐ K (Ideal.span ({1 - e} : Set T)) : T →ₐ[K]
          T ⧸ Ideal.span ({1 - e} : Set T))) :
    ψ (f e) = 1 := by
  -- Evaluate the restriction formula at `e`, then use that `e` is `1` in the quotient.
  calc
    ψ (f e) = (ψ.comp f) e := rfl
    _ = (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set T))) e := by
          exact congrArg (fun g : T →ₐ[K] T ⧸ Ideal.span ({1 - e} : Set T) ↦ g e) hcomp
    _ = 1 := quotient_mk_self_eq_one_of_one_sub e

/-- Helper for Chap10 Lemma 10 124 3: if the target map restricts to the source quotient map,
then the descended lift is a left inverse to the idempotent-image quotient map. -/
private theorem quotientLiftOfIdempotentImageToOne_comp_quotientMap
    {K : Type*} {T : Type w} {U : Type*}
    [CommRing K] [CommRing T] [CommRing U]
    [Algebra K T] [Algebra K U]
    (f : T →ₐ[K] U) (e : T)
    (ψ : U →ₐ[K] T ⧸ Ideal.span ({1 - e} : Set T)) (hψ : ψ (f e) = 1)
    (hcomp :
      ψ.comp f =
        (Ideal.Quotient.mkₐ K (Ideal.span ({1 - e} : Set T)) : T →ₐ[K]
          T ⧸ Ideal.span ({1 - e} : Set T))) :
    (quotientLiftOfIdempotentImageToOne f e ψ hψ).comp
        (quotientMapOfIdempotentImage f e) =
      AlgHom.id K (T ⧸ Ideal.span ({1 - e} : Set T)) := by
  apply AlgHom.ext
  intro x
  -- It is enough to check quotient representatives, where both maps compute by construction.
  refine Quotient.inductionOn' x ?_
  intro z
  change
    ((quotientLiftOfIdempotentImageToOne f e ψ hψ).comp
        (quotientMapOfIdempotentImage f e))
        ((Ideal.Quotient.mk (Ideal.span ({1 - e} : Set T))) z) =
      (AlgHom.id K (T ⧸ Ideal.span ({1 - e} : Set T)))
        ((Ideal.Quotient.mk (Ideal.span ({1 - e} : Set T))) z)
  rw [AlgHom.comp_apply, quotientLiftOfIdempotentImageToOne_quotientMap_mk]
  exact congrArg (fun g : T →ₐ[K] T ⧸ Ideal.span ({1 - e} : Set T) ↦ g z) hcomp

/-- Helper for Chap10 Lemma 10 124 3: once the descended target map is a left inverse to the
idempotent-image quotient map, that quotient map is injective. -/
private theorem quotientMapOfIdempotentImage_injective_of_leftInverse
    {K : Type*} {T : Type w} {U : Type*}
    [CommRing K] [CommRing T] [CommRing U]
    [Algebra K T] [Algebra K U]
    (f : T →ₐ[K] U) (e : T)
    (ψ : U →ₐ[K] T ⧸ Ideal.span ({1 - e} : Set T)) (hψ : ψ (f e) = 1)
    (hcomp :
      ψ.comp f =
        (Ideal.Quotient.mkₐ K (Ideal.span ({1 - e} : Set T)) : T →ₐ[K]
          T ⧸ Ideal.span ({1 - e} : Set T))) :
    Function.Injective (quotientMapOfIdempotentImage f e) := by
  have hleft :
      Function.LeftInverse
        (quotientLiftOfIdempotentImageToOne f e ψ hψ)
        (quotientMapOfIdempotentImage f e) := by
    intro x
    exact DFunLike.congr_fun
      (quotientLiftOfIdempotentImageToOne_comp_quotientMap f e ψ hψ hcomp) x
  -- The explicit quotient lift provides a left inverse, so the quotient map is injective.
  exact Function.LeftInverse.injective hleft

/-- Helper for Chap10 Lemma 10 124 3: a bijective basic-open comparison from a finite
subalgebra induces a bijection on the local rings at the distinguished prime. -/
private theorem subalgebraLocalRingHom_bijective_of_awayMapBijective
    (A : Subalgebra R S) (r : A)
    (hrq : (r : S) ∉ q)
    (haway : Function.Bijective (Localization.awayMap A.val.toRingHom r)) :
    Function.Bijective
      (Localization.localRingHom (Ideal.comap A.val.toRingHom q) q A.val.toRingHom rfl) := by
  let qA : Ideal A := Ideal.comap A.val.toRingHom q
  have hqAprime : qA.IsPrime := Ideal.comap_isPrime A.val.toRingHom q
  letI : qA.IsPrime := hqAprime
  letI : q.LiesOver qA := ⟨rfl⟩
  have hSat :
      A.saturation (q.primeCompl ⊓ A.toSubmonoid) (by
        intro x hx
        exact hx.2) = ⊤ := by
    rw [eq_top_iff]
    intro x _hx
    rw [Subalgebra.mem_saturation_iff]
    rcases Localization.awayMap_surjective_iff.mp haway.2 x with
      ⟨b, m, hb⟩
    have hdenom_notMem : A.val.toRingHom r ^ m ∉ q := by
      by_cases hm : m = 0
      · subst m
        intro hmem
        exact (inferInstance : q.IsPrime).ne_top
          ((Ideal.eq_top_iff_one q).mpr (by simpa using hmem))
      · intro hmem
        have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        have hrmem : A.val.toRingHom r ∈ q :=
          ((inferInstance : q.IsPrime).pow_mem_iff_mem m hmpos).mp hmem
        exact hrq hrmem
    have hmulMem : A.val.toRingHom r ^ m * x ∈ A := by
      rw [← hb]
      exact b.2
    refine ⟨A.val.toRingHom r ^ m,
      ⟨by simpa [Ideal.mem_primeCompl_iff] using hdenom_notMem, by
        simpa using A.pow_mem r.2 m⟩, ?_⟩
    -- The denominator-clearing equality supplied by away-surjectivity puts `x` in the saturation
    -- of `A` by elements outside `q`.
    simpa [Submonoid.smul_def] using hmulMem
  simpa [qA] using
    (Localization.localRingHom_bijective_of_saturated_inf_eq_top
      (R := R) (S := S) (P := q) (s := A) hSat qA)

/-- Helper for Chap10 Lemma 10 124 3: a bijective basic-open comparison upgrades the induced
local-ring homomorphism at the selected prime to a ring equivalence. -/
private noncomputable def subalgebraLocalRingEquivOfAwayMapBijective
    (A : Subalgebra R S) (r : A)
    (hrq : (r : S) ∉ q)
    (haway : Function.Bijective (Localization.awayMap A.val.toRingHom r)) :
    Localization.AtPrime (Ideal.comap A.val.toRingHom q) ≃+* S_q :=
  RingEquiv.ofBijective
    (Localization.localRingHom (Ideal.comap A.val.toRingHom q) q A.val.toRingHom rfl)
    (subalgebraLocalRingHom_bijective_of_awayMapBijective q A r hrq haway)

/-- Helper for Chap10 Lemma 10 124 3: the local-ring equivalence from a bijective basic-open
comparison has the expected forward map. -/
private theorem subalgebraLocalRingEquivOfAwayMapBijective_apply
    (A : Subalgebra R S) (r : A)
    (hrq : (r : S) ∉ q)
    (haway : Function.Bijective (Localization.awayMap A.val.toRingHom r))
    (x : Localization.AtPrime (Ideal.comap A.val.toRingHom q)) :
    subalgebraLocalRingEquivOfAwayMapBijective q A r hrq haway x =
      Localization.localRingHom (Ideal.comap A.val.toRingHom q) q A.val.toRingHom rfl x := by
  -- The equivalence is `RingEquiv.ofBijective`, so its forward function is the original
  -- local-ring homomorphism.
  rfl

omit [q.IsPrime] in
/-- Helper for Chap10 Lemma 10 124 3: the contracted prime
`Ideal.comap A.val.toRingHom q` is a prime of `A` lying over `q.under R`. -/
private theorem subalgebraComapPrime_under_eq
    (A : Subalgebra R S) :
    Ideal.comap (algebraMap R A) (Ideal.comap A.val.toRingHom q) = q.under R := by
  -- Expanding both contractions reduces the identity to functoriality of `Ideal.comap`.
  ext x
  simp [Ideal.under_def, Ideal.comap_comap]

/-- Helper for Chap10 Lemma 10 124 3: the contracted prime
`Ideal.comap A.val.toRingHom q` is a prime of `A` lying over `q.under R`. -/
private theorem subalgebraComapPrime_mem_primesOver
    (A : Subalgebra R S) :
    Ideal.comap A.val.toRingHom q ∈ (q.under R).primesOver A := by
  let qA : Ideal A := Ideal.comap A.val.toRingHom q
  have hqA_over_R : Ideal.comap (algebraMap R A) qA = q.under R := by
    -- This is the contraction identity packaged as a reusable helper for the local-ring algebra.
    simpa [qA] using subalgebraComapPrime_under_eq q A
  haveI : qA.IsPrime := Ideal.comap_isPrime A.val.toRingHom q
  haveI : qA.LiesOver (q.under R) := by
    -- The contracted prime lies over the base prime because contracting further to `R` recovers
    -- `q.under R`.
    constructor
    simpa [Ideal.under_def] using hqA_over_R.symm
  exact ⟨inferInstance, inferInstance⟩

/-- Helper for Chap10 Lemma 10 124 3: package the contracted prime as the distinguished
`primesOver` index used by the finite-side product split. -/
private noncomputable def subalgebraComapPrimePrimesOver
    (A : Subalgebra R S) :
    (q.under R).primesOver A :=
  ⟨Ideal.comap A.val.toRingHom q, subalgebraComapPrime_mem_primesOver q A⟩

/-- Helper for Chap10 Lemma 10 124 3: the localization of the finite subalgebra at the
contracted prime is naturally an `R_qR`-algebra. -/
private noncomputable local instance subalgebraLocalizationAlgebra
    (A : Subalgebra R S) :
    Algebra R_qR (Localization.AtPrime (Ideal.comap A.val.toRingHom q)) :=
  (Localization.localRingHom (q.under R) (Ideal.comap A.val.toRingHom q) (algebraMap R A)
    (subalgebraComapPrime_under_eq q A)).toAlgebra

/-- Helper for Chap10 Lemma 10 124 3: the away-bijective local-ring equivalence carries the
`R_qR`-algebra structure on the finite subalgebra localization to the canonical one on `S_q`. -/
private theorem subalgebraLocalRingEquivOfAwayMapBijective_commutes
    (A : Subalgebra R S) (r : A)
    (hrq : (r : S) ∉ q)
    (haway : Function.Bijective (Localization.awayMap A.val.toRingHom r))
    (x : R_qR) :
    subalgebraLocalRingEquivOfAwayMapBijective q A r hrq haway
        (algebraMap R_qR (Localization.AtPrime (Ideal.comap A.val.toRingHom q)) x) =
      algebraMap R_qR S_q x := by
  let qA : Ideal A := Ideal.comap A.val.toRingHom q
  have hqA_over_R : Ideal.comap (algebraMap R A) qA = q.under R := by
    -- Reuse the contraction identity so the local-ring comparison has the canonical source prime.
    simpa [qA] using subalgebraComapPrime_under_eq q A
  have hcomp :
      algebraMap R_qR S_q =
        (Localization.localRingHom qA q A.val.toRingHom rfl).comp
          (Localization.localRingHom (q.under R) qA (algebraMap R A)
            hqA_over_R) := by
    -- The canonical comparison from `R_(q ∩ R)` to `S_q` factors through the finite subalgebra
    -- localization by the standard composition theorem for `Localization.localRingHom`.
    simpa [qA] using
      (Localization.localRingHom_comp (q.under R) qA q
        (algebraMap R A) hqA_over_R A.val.toRingHom rfl)
  -- Evaluate the composed local-ring homomorphism at `x`; this is exactly the algebra-commuting
  -- condition needed later when upgrading to an algebra equivalence.
  rw [subalgebraLocalRingEquivOfAwayMapBijective_apply]
  simpa [RingHom.comp_apply] using
    congrArg (fun f : R_qR →+* S_q ↦ f x) hcomp.symm

/-- Helper for Chap10 Lemma 10 124 3: the away-bijective local-ring comparison upgrades to an
`R_qR`-algebra equivalence. -/
private noncomputable def subalgebraLocalRingAlgEquivOfAwayMapBijective
    (A : Subalgebra R S) (r : A)
    (hrq : (r : S) ∉ q)
    (haway : Function.Bijective (Localization.awayMap A.val.toRingHom r)) :
    Localization.AtPrime (Ideal.comap A.val.toRingHom q) ≃ₐ[R_qR] S_q :=
  { __ := subalgebraLocalRingEquivOfAwayMapBijective q A r hrq haway
    commutes' := subalgebraLocalRingEquivOfAwayMapBijective_commutes q A r hrq haway }


/-- Helper for Chap10 Lemma 10 124 3: a bijective basic-open comparison induces a ring
equivalence between the completed local ring of the finite model and the completed local ring of
the target. -/
private noncomputable def completedLocalRingRingEquivOfAwayBijectiveAtPrime
    (A : Subalgebra R S) (r : A)
    (hrq : (r : S) ∉ q)
    (haway : Function.Bijective (Localization.awayMap A.val.toRingHom r)) :
    AdicCompletion
        (maximalIdeal (Localization.AtPrime (Ideal.comap A.val.toRingHom q)))
        (Localization.AtPrime (Ideal.comap A.val.toRingHom q)) ≃+* S_q^ :=
  let eLocal := subalgebraLocalRingEquivOfAwayMapBijective q A r hrq haway
  RingEquiv.ofBijective
    (@maximalIdealCompletionMap
      (Localization.AtPrime (Ideal.comap A.val.toRingHom q)) S_q
      _ _ _ _ eLocal.toRingHom
      (ringEquiv_isLocalHom_of_localRings eLocal))
    (maximalIdealCompletionMap_bijective_of_ringEquiv eLocal)

/-- Helper for Chap10 Lemma 10 124 3: the completed local comparison induced by the away-bijective
finite model agrees with the dense local-ring map on elements from the source localization. -/
private theorem completedLocalRingRingEquivOfAwayBijectiveAtPrime_apply_of_localized
    (A : Subalgebra R S) (r : A)
    (hrq : (r : S) ∉ q)
    (haway : Function.Bijective (Localization.awayMap A.val.toRingHom r))
    (y : Localization.AtPrime (Ideal.comap A.val.toRingHom q)) :
    completedLocalRingRingEquivOfAwayBijectiveAtPrime q A r hrq haway
        (algebraMap
          (Localization.AtPrime (Ideal.comap A.val.toRingHom q))
          (AdicCompletion
            (maximalIdeal (Localization.AtPrime (Ideal.comap A.val.toRingHom q)))
            (Localization.AtPrime (Ideal.comap A.val.toRingHom q))) y) =
      algebraMap S_q S_q^
        (subalgebraLocalRingEquivOfAwayMapBijective q A r hrq haway y) := by
  let eLocal := subalgebraLocalRingEquivOfAwayMapBijective q A r hrq haway
  -- The completion comparison is `maximalIdealCompletionMap`, so on dense elements it simply
  -- applies the underlying local-ring equivalence before taking the dense image in the target
  -- completion.
  change
    @maximalIdealCompletionMap
        (Localization.AtPrime (Ideal.comap A.val.toRingHom q)) S_q
        _ _ _ _ eLocal.toRingHom (ringEquiv_isLocalHom_of_localRings eLocal)
        (algebraMap
          (Localization.AtPrime (Ideal.comap A.val.toRingHom q))
          (AdicCompletion
            (maximalIdeal (Localization.AtPrime (Ideal.comap A.val.toRingHom q)))
            (Localization.AtPrime (Ideal.comap A.val.toRingHom q))) y) =
      algebraMap S_q S_q^ (eLocal y)
  letI : IsLocalHom eLocal.toRingHom := ringEquiv_isLocalHom_of_localRings eLocal
  have hcomp :=
    congrArg
      (fun g : Localization.AtPrime (Ideal.comap A.val.toRingHom q) →+* S_q^ ↦ g y)
      (maximalIdealCompletionMap_comp eLocal.toRingHom)
  simpa [RingHom.comp_apply] using hcomp

/-- Helper for Chap10 Lemma 10 124 3: the completed local comparison sends the dense image of a
finite-subalgebra element to the dense image of the same element in `S_q^`. -/
private theorem completedLocalRingRingEquivOfAwayBijectiveAtPrime_apply_algebraMap
    (A : Subalgebra R S) (r a : A)
    (hrq : (r : S) ∉ q)
    (haway : Function.Bijective (Localization.awayMap A.val.toRingHom r)) :
    completedLocalRingRingEquivOfAwayBijectiveAtPrime q A r hrq haway
        (algebraMap
          (Localization.AtPrime (Ideal.comap A.val.toRingHom q))
          (AdicCompletion
            (maximalIdeal (Localization.AtPrime (Ideal.comap A.val.toRingHom q)))
            (Localization.AtPrime (Ideal.comap A.val.toRingHom q)))
          (algebraMap A (Localization.AtPrime (Ideal.comap A.val.toRingHom q)) a)) =
      algebraMap S S_q^ a := by
  -- First move across the completion comparison, then collapse the local-ring map on the dense
  -- subalgebra element to the ordinary localization map into `S_q`.
  rw [completedLocalRingRingEquivOfAwayBijectiveAtPrime_apply_of_localized]
  rw [subalgebraLocalRingEquivOfAwayMapBijective_apply]
  have hmap :
      Localization.localRingHom (Ideal.comap A.val.toRingHom q) q A.val.toRingHom rfl
          (algebraMap A (Localization.AtPrime (Ideal.comap A.val.toRingHom q)) a) =
        algebraMap S S_q a := by
    exact Localization.localRingHom_to_map
      (Ideal.comap A.val.toRingHom q) q A.val.toRingHom rfl a
  rw [hmap]
  simpa using (IsScalarTower.algebraMap_apply S S_q S_q^ a).symm

/-- Helper for Chap10 Lemma 10 124 3: the completed local comparison induced by the away-bijective
finite model respects the completed base local-ring action. -/
private theorem completedLocalRingRingEquivOfAwayBijectiveAtPrime_commutes
    (A : Subalgebra R S) (r : A)
    (hrq : (r : S) ∉ q)
    (haway : Function.Bijective (Localization.awayMap A.val.toRingHom r))
    (x : R_qR) :
    completedLocalRingRingEquivOfAwayBijectiveAtPrime q A r hrq haway
        (algebraMap
          R_qR
          (AdicCompletion
            (maximalIdeal (Localization.AtPrime (Ideal.comap A.val.toRingHom q)))
            (Localization.AtPrime (Ideal.comap A.val.toRingHom q))) x) =
      algebraMap R_qR S_q^ x := by
  -- Rewrite the source dense element through the finite-model localization, then use the local-ring
  -- commutativity statement already proved before passing to completions.
  rw [show algebraMap R_qR
      (AdicCompletion
        (maximalIdeal (Localization.AtPrime (Ideal.comap A.val.toRingHom q)))
        (Localization.AtPrime (Ideal.comap A.val.toRingHom q))) x =
        algebraMap
          (Localization.AtPrime (Ideal.comap A.val.toRingHom q))
          (AdicCompletion
            (maximalIdeal (Localization.AtPrime (Ideal.comap A.val.toRingHom q)))
            (Localization.AtPrime (Ideal.comap A.val.toRingHom q)))
          (algebraMap R_qR (Localization.AtPrime (Ideal.comap A.val.toRingHom q)) x) from
      (IsScalarTower.algebraMap_apply
        R_qR
        (Localization.AtPrime (Ideal.comap A.val.toRingHom q))
        (AdicCompletion
          (maximalIdeal (Localization.AtPrime (Ideal.comap A.val.toRingHom q)))
          (Localization.AtPrime (Ideal.comap A.val.toRingHom q)))
        x).symm]
  rw [completedLocalRingRingEquivOfAwayBijectiveAtPrime_apply_of_localized]
  rw [subalgebraLocalRingEquivOfAwayMapBijective_commutes q A r hrq haway x]
  simpa using (IsScalarTower.algebraMap_apply R_qR S_q S_q^ x).symm

/-- Helper for Chap10 Lemma 10 124 3: the away-bijective completed local-ring comparison upgrades
to an `R_(q ∩ R)`-algebra equivalence. -/
private noncomputable def completedLocalRingAlgEquivOfAwayBijectiveAtPrime
    (A : Subalgebra R S) (r : A)
    (hrq : (r : S) ∉ q)
    (haway : Function.Bijective (Localization.awayMap A.val.toRingHom r)) :
    AdicCompletion
        (maximalIdeal (Localization.AtPrime (Ideal.comap A.val.toRingHom q)))
        (Localization.AtPrime (Ideal.comap A.val.toRingHom q)) ≃ₐ[R_qR] S_q^ :=
  { __ := completedLocalRingRingEquivOfAwayBijectiveAtPrime q A r hrq haway
    commutes' := completedLocalRingRingEquivOfAwayBijectiveAtPrime_commutes q A r hrq haway }

/-- Helper for Chap10 Lemma 10 124 3: comapping a prime along the `ULift` algebra equivalence
preserves primality. -/
private theorem uliftAlgEquivComap_isPrime {A : Type w} [CommRing A] [Algebra R A]
    (Q : Ideal A) [Q.IsPrime] :
    (Q.comap ((ULift.algEquiv : ULift A ≃ₐ[R] A).toRingHom)).IsPrime := by
  -- The bridge prime on `ULift A` is the ordinary comap of the original prime along the
  -- canonical algebra equivalence.
  exact Ideal.comap_isPrime
    ((ULift.algEquiv : ULift A ≃ₐ[R] A).toRingHom) Q

/-- Helper for Chap10 Lemma 10 124 3: comapping a prime-over ideal along the `ULift` algebra
equivalence preserves the lies-over relation. -/
private theorem uliftAlgEquivComap_liesOver {A : Type w} [CommRing A] [Algebra R A]
    (p : Ideal R) (Q : Ideal A) [Q.LiesOver p] :
    (Q.comap ((ULift.algEquiv : ULift A ≃ₐ[R] A).toRingHom)).LiesOver p := by
  -- Since `ULift.algEquiv` is an `R`-algebra equivalence, the base contraction is unchanged.
  exact Ideal.comap_liesOver Q p (ULift.algEquiv : ULift A ≃ₐ[R] A)

/-- Helper for Chap10 Lemma 10 124 3: the prime complement of a comapped ideal on `ULift A`
transports exactly to the original prime complement on `A`. -/
private theorem uliftAlgEquiv_primeCompl_eq {A : Type w} [CommRing A] [Algebra R A]
    (Q : Ideal A) [Q.IsPrime]
    [_hQlift :
      (Ideal.comap
        (show ULift.{u} A →+* A from (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingHom)
        Q).IsPrime] :
    Submonoid.map
        (show ULift.{u} A →* A from (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toMonoidHom)
        (Ideal.primeCompl
          (Ideal.comap
            (show ULift.{u} A →+* A from (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingHom) Q)) =
      Ideal.primeCompl Q := by
  -- The `ULift` algebra equivalence preserves membership in the chosen prime ideal exactly.
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hy
    refine ⟨(ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).symm y, ?_, by simp⟩
    simpa using hy

/-- Helper for Chap10 Lemma 10 124 3: localizing `ULift A` at the comapped prime is canonically
the same local ring as localizing `A` at the original prime. -/
private noncomputable def uliftLocalizationAtPrimeRingEquiv
    {A : Type w} [CommRing A] [Algebra R A] (Q : Ideal A) [Q.IsPrime]
    [_hQlift :
      (Ideal.comap
        (show ULift.{u} A →+* A from (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingHom)
        Q).IsPrime] :
    Localization.AtPrime
        (Ideal.comap
          (show ULift.{u} A →+* A from (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingHom) Q) ≃+*
      Localization.AtPrime Q := by
  -- The localization owner only depends on the prime complement, so transport along the `ULift`
  -- ring equivalence once and reuse the canonical localization comparison.
  exact
    IsLocalization.ringEquivOfRingEquiv
      (Localization.AtPrime
        (Ideal.comap
          (show ULift.{u} A →+* A from (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingHom) Q))
      (Localization.AtPrime Q)
      ((ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingEquiv)
      (uliftAlgEquiv_primeCompl_eq (R := R) Q)

/-- Helper for Chap10 Lemma 10 124 3: after transporting the local ring comparison through
`ULift`, the corresponding maximal-ideal completions are canonically ring equivalent. -/
private noncomputable def uliftLocalizationAtPrimeCompletionRingEquiv
    {A : Type w} [CommRing A] [Algebra R A] (Q : Ideal A) [Q.IsPrime]
    [_hQlift :
      (Ideal.comap
        (show ULift.{u} A →+* A from (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingHom)
        Q).IsPrime] :
    AdicCompletion
        (maximalIdeal
          (Localization.AtPrime
            (Ideal.comap
              (show ULift.{u} A →+* A from (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingHom)
              Q)))
        (Localization.AtPrime
          (Ideal.comap
            (show ULift.{u} A →+* A from (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingHom) Q)) ≃+*
      AdicCompletion (maximalIdeal (Localization.AtPrime Q)) (Localization.AtPrime Q) := by
  let eLocal := uliftLocalizationAtPrimeRingEquiv (R := R) Q
  -- The completion map attached to a local-ring equivalence is bijective, so it upgrades to a
  -- ring equivalence between the two completed local rings.
  exact
    RingEquiv.ofBijective
      (@maximalIdealCompletionMap
        (Localization.AtPrime
          (Ideal.comap
            (show ULift.{u} A →+* A from (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingHom)
            Q))
        (Localization.AtPrime Q)
        _ _ _ _ eLocal.toRingHom
        (ringEquiv_isLocalHom_of_localRings eLocal))
      (maximalIdealCompletionMap_bijective_of_ringEquiv eLocal)

/-- Helper for Chap10 Lemma 10 124 3: the `ULift`-transported completion comparison sends the
dense image of a localized element to the dense image of its transported value. -/
private theorem uliftLocalizationAtPrimeCompletionRingEquiv_apply_algebraMap
    {A : Type w} [CommRing A] [Algebra R A] (Q : Ideal A) [Q.IsPrime]
    [_hQlift :
      (Ideal.comap
        (show ULift.{u} A →+* A from (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingHom)
        Q).IsPrime]
    (y : Localization.AtPrime
      (Ideal.comap
        (show ULift.{u} A →+* A from (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingHom) Q)) :
    uliftLocalizationAtPrimeCompletionRingEquiv (R := R) Q
        (algebraMap
          (Localization.AtPrime
            (Ideal.comap
              (show ULift.{u} A →+* A from (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingHom)
              Q))
          (AdicCompletion
            (maximalIdeal
              (Localization.AtPrime
                (Ideal.comap
                  (show ULift.{u} A →+* A from
                    (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingHom) Q)))
            (Localization.AtPrime
              (Ideal.comap
                (show ULift.{u} A →+* A from
                  (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingHom) Q))) y) =
      algebraMap
        (Localization.AtPrime Q)
        (AdicCompletion (maximalIdeal (Localization.AtPrime Q)) (Localization.AtPrime Q))
        (uliftLocalizationAtPrimeRingEquiv (R := R) Q y) := by
  let eLocal := uliftLocalizationAtPrimeRingEquiv (R := R) Q
  -- The completion comparison is `maximalIdealCompletionMap`, so on dense localized elements it
  -- simply applies the underlying local-ring equivalence before taking the dense image.
  change
    @maximalIdealCompletionMap
        (Localization.AtPrime
          (Ideal.comap
            (show ULift.{u} A →+* A from (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingHom)
            Q))
        (Localization.AtPrime Q)
        _ _ _ _ eLocal.toRingHom (ringEquiv_isLocalHom_of_localRings eLocal)
        (algebraMap
          (Localization.AtPrime
            (Ideal.comap
              (show ULift.{u} A →+* A from (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingHom)
              Q))
          (AdicCompletion
            (maximalIdeal
              (Localization.AtPrime
                (Ideal.comap
                  (show ULift.{u} A →+* A from
                    (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingHom) Q)))
            (Localization.AtPrime
              (Ideal.comap
                (show ULift.{u} A →+* A from
                  (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingHom) Q))) y) =
      algebraMap
        (Localization.AtPrime Q)
        (AdicCompletion (maximalIdeal (Localization.AtPrime Q)) (Localization.AtPrime Q))
        (eLocal y)
  letI : IsLocalHom eLocal.toRingHom := ringEquiv_isLocalHom_of_localRings eLocal
  have hcomp :=
    congrArg
      (fun g :
        Localization.AtPrime
            (Ideal.comap
              (show ULift.{u} A →+* A from (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingHom) Q) →+*
          AdicCompletion (maximalIdeal (Localization.AtPrime Q)) (Localization.AtPrime Q) ↦ g y)
      (maximalIdealCompletionMap_comp eLocal.toRingHom)
  simpa [RingHom.comp_apply] using hcomp

/-- Helper for Chap10 Lemma 10 124 3: the `ULift` localization comparison sends a dense source
generator to the corresponding dense target generator. -/
private theorem uliftLocalizationAtPrimeRingEquiv_apply_algebraMap
    {A : Type w} [CommRing A] [Algebra R A] (Q : Ideal A) [Q.IsPrime]
    [_hQlift :
      (Ideal.comap
        (show ULift.{u} A →+* A from (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingHom)
        Q).IsPrime]
    (a : ULift.{u} A) :
    uliftLocalizationAtPrimeRingEquiv (R := R) Q
        (algebraMap
          (ULift.{u} A)
          (Localization.AtPrime
            (Ideal.comap
              (show ULift.{u} A →+* A from (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingHom)
              Q)) a) =
      algebraMap A (Localization.AtPrime Q)
        ((ULift.algEquiv : ULift.{u} A ≃ₐ[R] A) a) := by
  -- The localization transport is `ringEquivOfRingEquiv`, so on dense generators it simply
  -- applies the underlying `ULift` equivalence before taking the target localization class.
  simpa [uliftLocalizationAtPrimeRingEquiv] using
    (IsLocalization.ringEquivOfRingEquiv_eq
      (S := Localization.AtPrime
        (Ideal.comap
          (show ULift.{u} A →+* A from (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingHom)
          Q))
      (Q := Localization.AtPrime Q)
      (j := (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingEquiv)
      (uliftAlgEquiv_primeCompl_eq (R := R) Q)
      a)

/-- Helper for Chap10 Lemma 10 124 3: the `ULift` localization comparison is the canonical local
ring map induced by the `ULift` algebra equivalence. -/
private theorem uliftLocalizationAtPrimeRingEquiv_apply
    {A : Type w} [CommRing A] [Algebra R A] (Q : Ideal A) [Q.IsPrime]
    [_hQlift :
      (Ideal.comap
        (show ULift.{u} A →+* A from (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingHom)
        Q).IsPrime]
    (y : Localization.AtPrime
      (Ideal.comap
        (show ULift.{u} A →+* A from (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingHom)
        Q)) :
    uliftLocalizationAtPrimeRingEquiv (R := R) Q y =
      Localization.localRingHom
        (Ideal.comap
          (show ULift.{u} A →+* A from (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingHom) Q)
        Q
        (show ULift.{u} A →+* A from (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingHom)
        rfl y := by
  have hmap :
      (uliftLocalizationAtPrimeRingEquiv (R := R) Q).toRingHom =
        Localization.localRingHom
          (Ideal.comap
            (show ULift.{u} A →+* A from
              (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingHom) Q)
          Q
          (show ULift.{u} A →+* A from (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingHom)
          rfl := by
    -- Proof comment: both maps are local-ring maps from the same source localization, so it
    -- suffices to compare them on dense generators coming from `ULift A`.
    apply Localization.localRingHom_unique
      (Ideal.comap
        (show ULift.{u} A →+* A from (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingHom) Q)
      Q
      (show ULift.{u} A →+* A from (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingHom)
      rfl
    intro a
    simpa [RingHom.comp_apply] using
      (uliftLocalizationAtPrimeRingEquiv_apply_algebraMap (R := R) (Q := Q) a)
  exact congrArg
    (fun f :
      Localization.AtPrime
          (Ideal.comap
            (show ULift.{u} A →+* A from
              (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toRingHom) Q) →+*
        Localization.AtPrime Q ↦ f y)
    hmap

/-- Helper for Chap10 Lemma 10 124 3: splitting a `Π`-indexed algebra target at one chosen
coordinate produces a two-factor product decomposition. -/
private noncomputable def algEquivProdOfPiSplitAt
    {K : Type*} {T : Type w} {ι : Type*} {Y : ι → Type*}
    [CommRing K] [CommRing T] [Algebra K T]
    [DecidableEq ι] [∀ i, CommRing (Y i)] [∀ i, Algebra K (Y i)]
    (E : T ≃ₐ[K] ∀ i, Y i) (i0 : ι) :
    T ≃ₐ[K] (Y i0 × ((j : { i : ι // i ≠ i0 }) → Y j.1)) := by
  let eSplit :
      ((i : ι) → Y i) ≃ₐ[K]
        ((j : { i : ι // i = i0 }) → Y j.1) × ((j : { i : ι // i ≠ i0 }) → Y j.1) :=
    { __ := RingEquiv.piEquivPiSubtypeProd (fun i : ι ↦ i = i0) Y
      commutes' := by
        intro k
        ext j <;> rfl }
  letI : Unique { i : ι // i = i0 } :=
    { default := ⟨i0, rfl⟩
      uniq := by
        intro j
        rcases j with ⟨j, hj⟩
        cases hj
        rfl }
  let eFirst : ((j : { i : ι // i = i0 }) → Y j.1) ≃ₐ[K] Y i0 :=
    { __ := RingEquiv.piUnique (fun j : { i : ι // i = i0 } ↦ Y j.1)
      commutes' := by
        intro k
        rfl }
  -- First split the product into the chosen coordinate and its complement, then identify the
  -- singleton-coordinate function space with that chosen factor.
  exact E.trans <| eSplit.trans <|
    AlgEquiv.prodCongr eFirst
      (AlgEquiv.refl : ((j : { i : ι // i ≠ i0 }) → Y j.1) ≃ₐ[K]
        ((j : { i : ι // i ≠ i0 }) → Y j.1))

/-- Helper for Chap10 Lemma 10 124 3: after splitting a `Π`-indexed algebra target at `i0`, the
first projection is evaluation at that chosen coordinate. -/
private theorem algEquivProdOfPiSplitAt_fst
    {K : Type*} {T : Type w} {ι : Type*} {Y : ι → Type*}
    [CommRing K] [CommRing T] [Algebra K T]
    [DecidableEq ι] [∀ i, CommRing (Y i)] [∀ i, Algebra K (Y i)]
    (E : T ≃ₐ[K] ∀ i, Y i) (i0 : ι) (z : T) :
    RingHom.fst (Y i0) (((j : { i : ι // i ≠ i0 }) → Y j.1))
        (algEquivProdOfPiSplitAt E i0 z) =
      E z i0 := by
  -- Unfold the packaged split once; the singleton factor reduces to evaluation at `i0`.
  dsimp [algEquivProdOfPiSplitAt]
  rfl

/-- Helper for Chap10 Lemma 10 124 3: splitting a `Π`-indexed ring target at one chosen
coordinate produces a two-factor product decomposition. -/
private noncomputable def ringEquivProdOfPiSplitAt
    {T : Type w} {ι : Type*} {Y : ι → Type*}
    [CommRing T] [DecidableEq ι] [∀ i, CommRing (Y i)]
    (E : T ≃+* ∀ i, Y i) (i0 : ι) :
    T ≃+* (Y i0 × ((j : { i : ι // i ≠ i0 }) → Y j.1)) := by
  let eSplit :
      ((i : ι) → Y i) ≃+*
        ((j : { i : ι // i = i0 }) → Y j.1) × ((j : { i : ι // i ≠ i0 }) → Y j.1) :=
    RingEquiv.piEquivPiSubtypeProd (fun i : ι ↦ i = i0) Y
  letI : Unique { i : ι // i = i0 } :=
    { default := ⟨i0, rfl⟩
      uniq := by
        intro j
        rcases j with ⟨j, hj⟩
        cases hj
        rfl }
  let eFirst : ((j : { i : ι // i = i0 }) → Y j.1) ≃+* Y i0 :=
    RingEquiv.piUnique (fun j : { i : ι // i = i0 } ↦ Y j.1)
  -- First split off the chosen coordinate, then identify the singleton-coordinate function ring
  -- with that factor.
  exact E.trans <| eSplit.trans <|
    RingEquiv.prodCongr eFirst
      (RingEquiv.refl ((j : { i : ι // i ≠ i0 }) → Y j.1) :
        ((j : { i : ι // i ≠ i0 }) → Y j.1) ≃+*
        ((j : { i : ι // i ≠ i0 }) → Y j.1))

/-- Helper for Chap10 Lemma 10 124 3: after splitting a `Π`-indexed ring target at `i0`, the
first projection is evaluation at that chosen coordinate. -/
private theorem ringEquivProdOfPiSplitAt_fst
    {T : Type w} {ι : Type*} {Y : ι → Type*}
    [CommRing T] [DecidableEq ι] [∀ i, CommRing (Y i)]
    (E : T ≃+* ∀ i, Y i) (i0 : ι) (z : T) :
    RingHom.fst (Y i0) (((j : { i : ι // i ≠ i0 }) → Y j.1))
        (ringEquivProdOfPiSplitAt E i0 z) =
      E z i0 := by
  -- Unfold the packaged split once; the singleton factor reduces to evaluation at `i0`.
  dsimp [ringEquivProdOfPiSplitAt]
  rfl

/-- Helper for Chap10 Lemma 10 124 3: after transporting a product decomposition by `prodCongr`,
the first projection is the transported first projection of the original split. -/
private theorem ringEquivTransProdCongr_fst
    {T : Type*} {A : Type*} {B : Type*} {C : Type*} {D : Type*}
    [CommRing T] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (E : T ≃+* (A × B)) (e₁ : A ≃+* C) (e₂ : B ≃+* D) (z : T) :
    RingHom.fst C D ((E.trans (RingEquiv.prodCongr e₁ e₂)) z) =
      e₁ (RingHom.fst A B (E z)) := by
  -- Unfold the composite product transport once; the first coordinate is exactly `e₁` applied to
  -- the original first coordinate.
  rfl

/-- Helper for Chap10 Lemma 10 124 3: a ring product decomposition upgrades to an algebra product
decomposition once the first projection is known to be the prescribed algebra map. -/
private theorem algEquivOfRingEquivProdOfFirstProjection
    {K : Type*} {T : Type w} {C : Type*} {B : Type*}
    [CommRing K] [CommRing T] [CommRing C] [CommRing B]
    [Algebra K T] [Algebra K C]
    (π : T →ₐ[K] C)
    (E : T ≃+* (C × B))
    (hfst : ∀ z : T, RingHom.fst C B (E z) = π z) :
    ∃ (_ : Algebra K B), Nonempty (T ≃ₐ[K] (C × B)) := by
  let bAlg : K →+* B :=
    ((RingHom.snd C B).comp E.toRingHom).comp (algebraMap K T)
  letI : Algebra K B := bAlg.toAlgebra
  let EAlg : T ≃ₐ[K] (C × B) :=
    AlgEquiv.ofRingEquiv (f := E) <| by
      intro k
      apply Prod.ext
      · -- The first coordinate is prescribed by `π`, so it already uses the canonical `K`-action.
        simpa [RingHom.comp_apply] using hfst (algebraMap K T k)
      · -- The second coordinate is the transported `K`-algebra structure on `B`.
        rfl
  exact ⟨inferInstance, ⟨EAlg⟩⟩

/-- Helper for Chap10 Lemma 10 124 3: the packaged algebra equivalence can be chosen with the
given underlying ring equivalence. -/
private theorem algEquivOfRingEquivProdOfFirstProjectionExplicit
    {K : Type*} {T : Type w} {C : Type*} {B : Type*}
    [CommRing K] [CommRing T] [CommRing C] [CommRing B]
    [Algebra K T] [Algebra K C]
    (π : T →ₐ[K] C)
    (E : T ≃+* (C × B))
    (hfst : ∀ z : T, RingHom.fst C B (E z) = π z) :
    ∃ (_ : Algebra K B) (EA : T ≃ₐ[K] (C × B)),
      EA.toRingEquiv = E := by
  let bAlg : K →+* B :=
    ((RingHom.snd C B).comp E.toRingHom).comp (algebraMap K T)
  letI : Algebra K B := bAlg.toAlgebra
  let EA : T ≃ₐ[K] (C × B) :=
    AlgEquiv.ofRingEquiv (f := E) <| by
      intro k
      apply Prod.ext
      · -- The first coordinate is still the prescribed algebra map `π`.
        simpa [RingHom.comp_apply] using hfst (algebraMap K T k)
      · -- The second coordinate is definitionally the transported `K`-action on `B`.
        rfl
  -- Return the explicit packaged equivalence so downstream proofs can rewrite by its ring part.
  exact ⟨inferInstance, EA, rfl⟩

/-- Helper for Chap10 Lemma 10 124 3: the tensor map induced by the finite subalgebra inclusion
`A ↪ S`. -/
private noncomputable def tensorProductMapOfSubalgebra
    (A : Subalgebra R S) :
    R_qR^ ⊗[R] A →ₐ[R_qR^] R_qR^ ⊗[R] S :=
  Algebra.TensorProduct.map (AlgHom.id R_qR^ R_qR^) A.val

/-- Helper for Chap10 Lemma 10 124 3: the tensor map induced by `A ↪ S` sends a pure tensor to
the corresponding tensor with the same left factor and included right factor. -/
private theorem tensorProductMapOfSubalgebra_tmul
    (A : Subalgebra R S) (x : R_qR^) (a : A) :
    tensorProductMapOfSubalgebra q A (x ⊗ₜ[R] a) =
      x ⊗ₜ[R] (a : S) := by
  -- The tensor map is `Algebra.TensorProduct.map`, so its value on pure tensors is definitional.
  simp [tensorProductMapOfSubalgebra]

/-- Helper for Chap10 Lemma 10 124 3: composing the canonical projection on
`R_qR^ ⊗[R] S` with the tensor map from `A` gives the induced projection on
`R_qR^ ⊗[R] A`. -/
private noncomputable def completedTensorProductProjectionSubalgebra
    (A : Subalgebra R S) :
    R_qR^ ⊗[R] A →ₐ[R_qR^] S_q^ :=
  (completedTensorProductProjection_q).comp (tensorProductMapOfSubalgebra q A)

/-- Helper for Chap10 Lemma 10 124 3: on `x ⊗ₜ[R] 1`, the induced subalgebra projection agrees
with the canonical completed local map from the completed base local ring. -/
private theorem completedTensorProductProjectionSubalgebra_tmul_one
    (A : Subalgebra R S) (x : R_qR^) :
    completedTensorProductProjectionSubalgebra q A (x ⊗ₜ[R] 1) =
      maximalIdealCompletionMap
        (Localization.localRingHom (q.under R) q (algebraMap R S) rfl) x := by
  -- First move the tensor into `R_qR^ ⊗[R] S`, then use the already-normalized generator formula.
  rw [completedTensorProductProjectionSubalgebra]
  rw [AlgHom.comp_apply]
  rw [tensorProductMapOfSubalgebra_tmul]
  exact completedTensorProductProjection_tmul_one q x

/-- Helper for Chap10 Lemma 10 124 3: on `1 ⊗ₜ[R] a`, the induced subalgebra projection is the
image of `a` in the completed local ring of `S`. -/
private theorem completedTensorProductProjectionSubalgebra_one_tmul
    (A : Subalgebra R S) (a : A) :
    completedTensorProductProjectionSubalgebra q A (1 ⊗ₜ[R] a) =
      algebraMap S S_q^ a := by
  -- Reduce to the corresponding generator computation on the ambient tensor product.
  rw [completedTensorProductProjectionSubalgebra]
  rw [AlgHom.comp_apply]
  rw [tensorProductMapOfSubalgebra_tmul]
  exact completedTensorProductProjection_one_tmul q a

/-- Helper for Chap10 Lemma 10 124 3: if `s ∉ q`, then the canonical completed tensor-product
projection sends `1 ⊗ₜ[R] s` to a unit. -/
private theorem completedTensorProductProjection_one_tmul_isUnit
    {s : S} (hs : s ∉ q) :
    IsUnit (completedTensorProductProjection_q (1 ⊗ₜ[R] s)) := by
  -- The generator formula identifies this value with the canonical image of `s` in `S_q^`.
  rw [completedTensorProductProjection_one_tmul]
  exact isUnit_algebraMap_completedAtPrime_of_notMem q hs

/-- Helper for Chap10 Lemma 10 124 3: if `a : A` avoids `q`, then the induced subalgebra
projection sends `1 ⊗ₜ[R] a` to a unit in `S_q^`. -/
private theorem completedTensorProductProjectionSubalgebra_one_tmul_isUnit
    (A : Subalgebra R S) {a : A} (ha : (a : S) ∉ q) :
    IsUnit
      (completedTensorProductProjectionSubalgebra q A (1 ⊗ₜ[R] a)) := by
  -- This is the ambient unit statement applied after identifying the subalgebra tensor generator.
  rw [completedTensorProductProjectionSubalgebra_one_tmul]
  exact isUnit_algebraMap_completedAtPrime_of_notMem q ha

/-- Helper for Chap10 Lemma 10 124 3: the tensor-inclusion sends the distinguished denominator
`1 ⊗ₜ[R] r` to the matching denominator in the ambient tensor product. -/
private theorem tensorProductMapOfSubalgebra_denominator
    (A : Subalgebra R S) (r : A) :
    tensorProductMapOfSubalgebra q A (1 ⊗ₜ[R] r) = 1 ⊗ₜ[R] ((r : S)) := by
  -- This packages the denominator transport separately so later away-localization arguments can
  -- rewrite the distinguished element without unfolding the tensor map again.
  simpa using tensorProductMapOfSubalgebra_tmul q A (1 : R_qR^) r

/-- Helper for Chap10 Lemma 10 124 3: every `R`-algebra can be viewed as an algebra over the
lifted base ring `ULift.{v} R` by restricting scalars along `ULift.ringEquiv`. -/
noncomputable local instance (priority := 100) liftedBaseAlgebra
    {A : Type w} [CommRing A] [Algebra R A] :
    Algebra (ULift.{v} R) A :=
  ULift.algebra' R A

/-- Helper for Chap10 Lemma 10 124 3: every `R`-algebra also carries the corresponding
`ULift.{v} R`-module structure explicitly, so lifted-base tensor products do not have to recover
it through coercions. -/
noncomputable local instance (priority := 100) liftedBaseModule
    {A : Type w} [CommRing A] [Algebra R A] :
    Module (ULift.{v} R) A :=
  inferInstance

/-- Helper for Chap10 Lemma 10 124 3: the lifted-base action on any `R`-algebra factors through
the original `R`-action, giving the expected scalar tower `ULift.{v} R → R → A`. -/
noncomputable local instance liftedBaseIsScalarTower
    {A : Type w} [CommRing A] [Algebra R A] :
    IsScalarTower (ULift.{v} R) R A :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Helper for Chap10 Lemma 10 124 3: if `A` is an `R`-algebra, then `ULift.{u} A` is naturally
an algebra over the lifted base ring `ULift.{v} R`. -/
noncomputable local instance (priority := 100) liftedBaseUliftAlgebra
    {A : Type w} [CommRing A] [Algebra R A] :
    Algebra (ULift.{v} R) (ULift.{u} A) :=
  ULift.algebra' R (ULift.{u} A)

/-- Helper for Chap10 Lemma 10 124 3: the completed base local ring `R_(q ∩ R)^∧` carries the
canonical `ULift.{v} R`-algebra structure. -/
noncomputable local instance liftedBaseCompletedBaseLocalRingAlgebra :
    Algebra (ULift.{v} R) R_qR^ :=
  inferInstance

/-- Helper for Chap10 Lemma 10 124 3: the trivial scalar tower
`ULift.{v} R → ULift.{v} R → R_(q ∩ R)^∧` is available explicitly for the lifted-base tensor
transport. -/
noncomputable local instance liftedBaseCompletedBaseLocalRingSelfTower :
    IsScalarTower (ULift.{v} R) (ULift.{v} R) R_qR^ :=
  inferInstance

/-- Helper for Chap10 Lemma 10 124 3: the tensor product over the lifted base `ULift.{v} R`,
spelled with explicit carrier data to avoid later typeclass ambiguity. -/
private abbrev tensorProductOverUliftBase
    (A : Type w) [CommRing A] [Algebra R A] :=
  R_qR^ ⊗[ULift.{v} R] A

/-- Helper for Chap10 Lemma 10 124 3: the explicit lifted-base tensor product inherits its
canonical commutative ring structure. -/
noncomputable local instance tensorProductOverUliftBaseCommRing
    (A : Type w) [CommRing A] [Algebra R A] :
    CommRing (tensorProductOverUliftBase (R := R) (q := q) A) :=
  by
    let _ : Module (ULift.{v} R) R_qR^ := Algebra.toModule
    let _ : Module (ULift.{v} R) A := Algebra.toModule
    -- Proof comment: after fixing the lifted-base module structures on both tensor factors, the
    -- tensor product carries the standard commutative ring structure from mathlib.
    change CommRing (R_qR^ ⊗[ULift.{v} R] A)
    infer_instance

/-- Helper for Chap10 Lemma 10 124 3: the explicit lifted-base tensor product is naturally an
`R_(q ∩ R)^∧`-algebra through the left tensor factor. -/
noncomputable local instance tensorProductOverUliftBaseAlgebra
    (A : Type w) [CommRing A] [Algebra R A] :
    Algebra R_qR^ (tensorProductOverUliftBase (R := R) (q := q) A) :=
  by
    let _ : Module (ULift.{v} R) R_qR^ := Algebra.toModule
    let _ : Module (ULift.{v} R) A := Algebra.toModule
    -- Proof comment: with the lifted-base modules fixed, this is the standard left-factor algebra
    -- structure on a tensor product.
    change Algebra R_qR^ (R_qR^ ⊗[ULift.{v} R] A)
    infer_instance

/-- Helper for Chap10 Lemma 10 124 3: after replacing the base ring by `ULift.{v} R`, the
right-unit tensor equivalence still agrees with the original `R`-algebra map on the left tensor
factor. -/
private theorem uliftBaseRightTensorRingEquiv_commutes
    {A : Type w} [CommRing A] [Algebra R A] :
    ∀ r : R,
      (((Algebra.TensorProduct.congr
            ((ULift.algEquiv (R := ULift.{v} R) (A := R)).symm)
            (AlgEquiv.refl : A ≃ₐ[ULift.{v} R] A)).trans
          (Algebra.TensorProduct.lid (ULift.{v} R) A)).toRingEquiv)
          (algebraMap R (R ⊗[ULift.{v} R] A) r) =
        algebraMap R A r := by
  intro r
  -- Expand the left tensor generator and simplify through the `ULift` transport and tensor-unit
  -- comparison.
  change
    (Algebra.TensorProduct.lid (ULift.{v} R) A)
        (((ULift.algEquiv (R := ULift.{v} R) (A := R)).symm r) ⊗ₜ[ULift.{v} R] (1 : A)) =
      algebraMap R A r
  rw [Algebra.TensorProduct.lid_tmul]
  simpa [Algebra.smul_def, ULift.algebra']

/-- Helper for Chap10 Lemma 10 124 3: tensoring over the lifted base ring `ULift.{v} R` with
`R` on the left canonically recovers the original `R`-algebra. -/
private noncomputable def uliftBaseRightTensorAlgEquiv
    {A : Type w} [CommRing A] [Algebra R A] :
    R ⊗[ULift.{v} R] A ≃ₐ[R] A :=
  AlgEquiv.ofRingEquiv
    (f := ((Algebra.TensorProduct.congr
        ((ULift.algEquiv (R := ULift.{v} R) (A := R)).symm)
        (AlgEquiv.refl : A ≃ₐ[ULift.{v} R] A)).trans
      (Algebra.TensorProduct.lid (ULift.{v} R) A)).toRingEquiv)
    (uliftBaseRightTensorRingEquiv_commutes (R := R) (A := A))

/-- Helper for Chap10 Lemma 10 124 3: the lifted-base right-unit tensor equivalence sends a pure
tensor `r ⊗ₜ a` to the expected scalar multiple `r • a`. -/
private theorem uliftBaseRightTensorAlgEquiv_tmul
    {A : Type w} [CommRing A] [Algebra R A] (r : R) (a : A) :
    uliftBaseRightTensorAlgEquiv (R := R) (A := A) (r ⊗ₜ[ULift.{v} R] a) = r • a := by
  -- Unfold the composite once; the first step removes the `ULift`, and the second is the usual
  -- tensor-right-unit map.
  change
    (Algebra.TensorProduct.lid (ULift.{v} R) A)
        (((ULift.algEquiv (R := ULift.{v} R) (A := R)).symm r) ⊗ₜ[ULift.{v} R] a) =
      r • a
  rw [Algebra.TensorProduct.lid_tmul]
  simp [Algebra.smul_def, ULift.algebra']

/-- Helper for Chap10 Lemma 10 124 3: the inverse lifted-base right-unit tensor equivalence sends
`a : A` to the pure tensor `1 ⊗ₜ a`. -/
private theorem uliftBaseRightTensorAlgEquiv_symm_apply
    {A : Type w} [CommRing A] [Algebra R A] (a : A) :
    (uliftBaseRightTensorAlgEquiv (R := R) (A := A)).symm a =
      1 ⊗ₜ[ULift.{v} R] a := by
  -- The inverse is the tensor-unit inverse followed by the inverse `ULift` transport on the left
  -- factor, and both steps are explicit on pure tensors.
  change
    (Algebra.TensorProduct.congr
        ((ULift.algEquiv (R := ULift.{v} R) (A := R)).symm)
        (AlgEquiv.refl : A ≃ₐ[ULift.{v} R] A)).symm
      ((Algebra.TensorProduct.lid (ULift.{v} R) A).symm a) =
    1 ⊗ₜ[ULift.{v} R] a
  simp

/-- Helper for Chap10 Lemma 10 124 3: the original tensor product over `R` can be rewritten as a
tensor product over `ULift.{v} R` without changing the left completed local factor. -/
private noncomputable def tensorProductOverUliftBaseAlgEquiv
    {A : Type w} [CommRing A] [Algebra R A] :
    R_qR^ ⊗[R] A ≃ₐ[R_qR^] tensorProductOverUliftBase (R := R) (q := q) A :=
  (Algebra.TensorProduct.congr
      (AlgEquiv.refl : R_qR^ ≃ₐ[R_qR^] R_qR^)
      (uliftBaseRightTensorAlgEquiv (R := R) (A := A)).symm).trans
    (Algebra.TensorProduct.cancelBaseChange
      (R := ULift.{v} R) (S := R) (T := R_qR^) (A := R_qR^) (B := A))

/-- Helper for Chap10 Lemma 10 124 3: rewriting the tensor product over `R` as a tensor product
over `ULift.{v} R` leaves pure tensors unchanged. -/
private theorem tensorProductOverUliftBaseAlgEquiv_tmul
    {A : Type w} [CommRing A] [Algebra R A] (x : R_qR^) (a : A) :
    tensorProductOverUliftBaseAlgEquiv (R := R) (q := q) (A := A) (x ⊗ₜ[R] a) =
      ((x ⊗ₜ[ULift.{v} R] a) : tensorProductOverUliftBase (R := R) (q := q) A) := by
  let _ : Module (ULift.{v} R) R_qR^ := Algebra.toModule
  let _ : Module (ULift.{v} R) A := Algebra.toModule
  -- Expand the inserted middle tensor factor `R ⊗[ULift.{v} R] A`, then cancel the base change.
  change
    (Algebra.TensorProduct.cancelBaseChange
        (ULift.{v} R) R R_qR^ R_qR^ A)
        (x ⊗ₜ[R] (uliftBaseRightTensorAlgEquiv (R := R) (A := A)).symm a) =
      ((x ⊗ₜ[ULift.{v} R] a) : tensorProductOverUliftBase (R := R) (q := q) A)
  rw [uliftBaseRightTensorAlgEquiv_symm_apply]
  simp using
    (Algebra.TensorProduct.cancelBaseChange_tmul
      (R := ULift.{v} R) (S := R) (T := R_qR^) (A := R_qR^) (B := A) x 1 a)

/-- Helper for Chap10 Lemma 10 124 3: package the contracted prime of `A` as the distinguished
`primesOver` index in the lifted same-universe model used to apply Lemma `10.97.8`. -/
private noncomputable def uliftSubalgebraComapPrimePrimesOver
    (A : Subalgebra R S) :
    (⟨Ideal.comap
        (show ULift.{v} R →+* R from (ULift.algEquiv : ULift.{v} R ≃ₐ[ULift.{v} R] R).toRingHom)
        (q.under R),
      uliftAlgEquivComap_isPrime (R := ULift.{v} R) (A := R) (Q := q.under R)⟩ :
      PrimeSpectrum (ULift.{v} R)).asIdeal.primesOver (ULift.{u} A) := by
  let qA : Ideal A := Ideal.comap A.val.toRingHom q
  let qLift : Ideal (ULift.{u} A) := Ideal.comap
    (show ULift.{u} A →+* A from (ULift.algEquiv : ULift.{u} A ≃ₐ[ULift.{v} R] A).toRingHom)
    qA
  haveI : qLift.IsPrime := by
    -- The lifted contracted prime is still prime after transporting it through `ULift.algEquiv`.
    dsimp [qLift]
    exact uliftAlgEquivComap_isPrime (R := ULift.{v} R) (A := A) (Q := qA)
  have hunder :
      Ideal.comap (algebraMap (ULift.{v} R) (ULift.{u} A)) qLift =
        Ideal.comap
          (show ULift.{v} R →+* R from
            (ULift.algEquiv : ULift.{v} R ≃ₐ[ULift.{v} R] R).toRingHom)
          (q.under R) := by
    -- Both contractions reduce to the original base contraction `qA ∩ R = q.under R`.
    ext x
    simp [qLift, qA]
  haveI : qLift.LiesOver
      (Ideal.comap
        (show ULift.{v} R →+* R from (ULift.algEquiv : ULift.{v} R ≃ₐ[ULift.{v} R] R).toRingHom)
        (q.under R)) := by
    -- The lifted contracted prime lies over the lifted base prime by the previous contraction
    -- computation.
    constructor
    simpa using hunder.symm
  exact ⟨qLift, by exact ⟨inferInstance, inferInstance⟩⟩

/-- Helper for Chap10 Lemma 10 124 3: the distinguished lifted prime over `q ∩ A` has the
expected underlying ideal on `ULift.{u} A`. -/
private theorem uliftSubalgebraComapPrimePrimesOver_asIdeal
    (A : Subalgebra R S) :
    (uliftSubalgebraComapPrimePrimesOver (R := R) (q := q) A).1 =
      Ideal.comap
        (show ULift.{u} A →+* A from
          (ULift.algEquiv : ULift.{u} A ≃ₐ[ULift.{v} R] A).toRingHom)
        (Ideal.comap A.val.toRingHom q) :=
  rfl

/-- Helper for Chap10 Lemma 10 124 3: the lifted localization of `R` at `q ∩ R`. -/
private noncomputable abbrev uliftBaseRingEquiv :
    ULift.{v} R ≃+* R :=
  (ULift.algEquiv : ULift.{v} R ≃ₐ[ULift.{v} R] R).toRingEquiv

/-- Helper for Chap10 Lemma 10 124 3: the contracted prime `q ∩ R` transported to
`ULift.{v} R`. -/
private noncomputable abbrev uliftBaseUnderIdeal :
    Ideal (ULift.{v} R) :=
  Ideal.comap (uliftBaseRingEquiv (R := R)).toRingHom (q.under R)

/-- Helper for Chap10 Lemma 10 124 3: the distinguished lifted prime over `q ∩ A` contracts to
the lifted base prime `q ∩ R`. -/
private theorem uliftSubalgebraComapPrime_under_eq
    (A : Subalgebra R S) :
    Ideal.comap
        (algebraMap (ULift.{v} R) (ULift.{u} A))
        ((uliftSubalgebraComapPrimePrimesOver (R := R) (q := q) A).1) =
      uliftBaseUnderIdeal (R := R) (q := q) := by
  -- Proof comment: both contractions reduce to the original base contraction `q ∩ R`, with only
  -- the `ULift` spellings differing.
  ext x
  simp [uliftSubalgebraComapPrimePrimesOver_asIdeal, uliftBaseUnderIdeal, Ideal.comap_comap]

/-- Helper for Chap10 Lemma 10 124 3: the lifted localization of `R` at `q ∩ R`. -/
private abbrev uliftBaseLocalizationAtUnder :
    Type (max u v) :=
  Localization.AtPrime (uliftBaseUnderIdeal (R := R) (q := q))

/-- Helper for Chap10 Lemma 10 124 3: the completion of the lifted base localization at its
maximal ideal. -/
private abbrev uliftBaseCompletedLocalRing :
    Type (max u v) :=
  AdicCompletion
    (maximalIdeal (uliftBaseLocalizationAtUnder (R := R) (q := q)))
    (uliftBaseLocalizationAtUnder (R := R) (q := q))

/-- Helper for Chap10 Lemma 10 124 3: the lifted completed base local ring carries the canonical
`ULift.{v} R`-module structure coming from the scalar tower through the localization. -/
noncomputable local instance uliftBaseCompletedLocalRingAlgebra :
    Algebra (ULift.{v} R) (uliftBaseCompletedLocalRing (R := R) (q := q)) :=
  inferInstance

/-- Helper for Chap10 Lemma 10 124 3: the trivial scalar tower
`ULift.{v} R → ULift.{v} R → uliftBaseCompletedLocalRing` is available explicitly for the
same-universe tensor transport. -/
noncomputable local instance uliftBaseCompletedLocalRingSelfTower :
    IsScalarTower
      (ULift.{v} R) (ULift.{v} R) (uliftBaseCompletedLocalRing (R := R) (q := q)) :=
  inferInstance

/-- Helper for Chap10 Lemma 10 124 3: the lifted completed base local ring carries the canonical
`ULift.{v} R`-module structure coming from the scalar tower through the localization. -/
noncomputable local instance uliftBaseCompletedLocalRingModule :
    Module (ULift.{v} R) (uliftBaseCompletedLocalRing (R := R) (q := q)) :=
  inferInstance

/-- Helper for Chap10 Lemma 10 124 3: `ULift.{u} A` uses the canonical `ULift.{v} R`-module
structure induced by its lifted-base algebra. -/
noncomputable local instance liftedBaseUliftModule
    {A : Type w} [CommRing A] [Algebra R A] :
    Module (ULift.{v} R) (ULift.{u} A) :=
  inferInstance

/-- Helper for Chap10 Lemma 10 124 3: the lifted completed tensor product used for the `07N9`
transport, spelled with the explicit base semiring expected by that equivalence. -/
private abbrev uliftBaseCompletionTensorProduct
    (A : Subalgebra R S) :=
  uliftBaseCompletedLocalRing (R := R) (q := q) ⊗[ULift.{v} R] ULift.{u} A

/-- Helper for Chap10 Lemma 10 124 3: the explicit same-universe completion tensor product
inherits its canonical commutative ring structure. -/
noncomputable local instance uliftBaseCompletionTensorProductCommRing
    (A : Subalgebra R S) :
    CommRing (uliftBaseCompletionTensorProduct (R := R) (q := q) A) :=
  by
    let _ : Module (ULift.{v} R) (uliftBaseCompletedLocalRing (R := R) (q := q)) :=
      Algebra.toModule
    let _ : Module (ULift.{v} R) (ULift.{u} A) := Algebra.toModule
    -- Proof comment: once the lifted completed local ring and lifted subalgebra use their
    -- canonical `ULift`-base modules, the tensor product inherits the usual commutative ring API.
    change CommRing
      (uliftBaseCompletedLocalRing (R := R) (q := q) ⊗[ULift.{v} R] ULift.{u} A)
    infer_instance

/-- Helper for Chap10 Lemma 10 124 3: the same-universe completion tensor product is naturally an
algebra over the lifted completed base local ring via the left tensor factor. -/
noncomputable local instance uliftBaseCompletionTensorProductAlgebra
    (A : Subalgebra R S) :
    Algebra (uliftBaseCompletedLocalRing (R := R) (q := q))
      (uliftBaseCompletionTensorProduct (R := R) (q := q) A) :=
  by
    let _ : Module (ULift.{v} R) (uliftBaseCompletedLocalRing (R := R) (q := q)) :=
      Algebra.toModule
    let _ : Module (ULift.{v} R) (ULift.{u} A) := Algebra.toModule
    -- Proof comment: with those module choices fixed, this is the standard tensor-product algebra
    -- on the left factor.
    change Algebra (uliftBaseCompletedLocalRing (R := R) (q := q))
      (uliftBaseCompletedLocalRing (R := R) (q := q) ⊗[ULift.{v} R] ULift.{u} A)
    infer_instance

/-- Helper for Chap10 Lemma 10 124 3: the contracted prime `q ∩ R` remains prime after
transporting `R` to `ULift.{v} R`. -/
private instance uliftBaseLocalizationAtUnder_isPrime :
    (uliftBaseUnderIdeal (R := R) (q := q)).IsPrime :=
  uliftAlgEquivComap_isPrime (R := ULift.{v} R) (A := R) (Q := q.under R)

/-- Helper for Chap10 Lemma 10 124 3: the contraction `q ∩ R` viewed inside the same-universe
`ULift.{v} R` model used to apply Lemma `10.97.8`. -/
private noncomputable def uliftBaseUnderPrime :
    PrimeSpectrum (ULift.{v} R) :=
  ⟨uliftBaseUnderIdeal (R := R) (q := q), inferInstance⟩

/-- Helper for Chap10 Lemma 10 124 3: the lifted base localization carries the canonical
`AtPrime` localization structure for `uliftBaseUnderIdeal`. -/
private noncomputable instance uliftBaseLocalizationAtUnder_isLocalization :
    IsLocalization
      (uliftBaseUnderIdeal (R := R) (q := q)).primeCompl
      (Localization.AtPrime (uliftBaseUnderIdeal (R := R) (q := q))) := by
  change
    IsLocalization
      (uliftBaseUnderIdeal (R := R) (q := q)).primeCompl
      (Localization (uliftBaseUnderIdeal (R := R) (q := q)).primeCompl)
  exact Localization.isLocalization (M := (uliftBaseUnderIdeal (R := R) (q := q)).primeCompl)

/-- Helper for Chap10 Lemma 10 124 3: the prime complement of `q ∩ R` is preserved by the
specialized `ULift.{v} R ≃ₐ[ULift.{v} R] R` comparison used for the base-completion transport. -/
private theorem uliftBaseAlgEquiv_primeCompl_eq :
    Submonoid.map
        (uliftBaseRingEquiv (R := R)).toMonoidHom
        (uliftBaseUnderIdeal (R := R) (q := q)).primeCompl =
      Ideal.primeCompl (q.under R) := by
  -- The specialized `ULift.{v} R ≃ₐ[ULift.{v} R] R` equivalence preserves membership in
  -- `q ∩ R`, so it also preserves the corresponding prime complement.
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hy
    refine ⟨(ULift.algEquiv (R := ULift.{v} R) (A := R)).symm y, ?_, by simp⟩
    simpa using hy

/-- Helper for Chap10 Lemma 10 124 3: the lifted completed local ring at `q ∩ R` is canonically
identified with the original base localization `R_(q ∩ R)` at the ring level. -/
private noncomputable def uliftBaseLocalizationAtUnderRingEquiv :
    uliftBaseLocalizationAtUnder (R := R) (q := q) ≃+*
      Localization.AtPrime (q.under R) :=
  IsLocalization.ringEquivOfRingEquiv
    (Localization.AtPrime (uliftBaseUnderIdeal (R := R) (q := q)))
    (Localization.AtPrime (q.under R))
    (uliftBaseRingEquiv (R := R))
    (uliftBaseAlgEquiv_primeCompl_eq (R := R) (q := q))

/-- Helper for Chap10 Lemma 10 124 3: the lifted base localization comparison sends a dense
source generator to the corresponding dense target generator. -/
private theorem uliftBaseLocalizationAtUnderRingEquiv_apply_algebraMap
    (x : ULift.{v} R) :
    uliftBaseLocalizationAtUnderRingEquiv (R := R) (q := q)
        (algebraMap
          (ULift.{v} R)
          (uliftBaseLocalizationAtUnder (R := R) (q := q)) x) =
      algebraMap R (Localization.AtPrime (q.under R))
        ((ULift.algEquiv (R := ULift.{v} R) (A := R)) x) := by
  simp [uliftBaseLocalizationAtUnderRingEquiv, uliftBaseLocalizationAtUnder] using
    (IsLocalization.ringEquivOfRingEquiv_eq
      (S := Localization.AtPrime (uliftBaseUnderIdeal (R := R) (q := q)))
      (Q := Localization.AtPrime (q.under R))
      (j := uliftBaseRingEquiv (R := R))
      (uliftBaseAlgEquiv_primeCompl_eq (R := R) (q := q))
      x)

/-- Helper for Chap10 Lemma 10 124 3: the lifted-base localization comparison respects the
canonical map from `R_(q ∩ R)` into the localization of a finite subalgebra at `q ∩ A`. -/
private noncomputable local instance uliftBaseLocalizationAtUnderSubalgebraLocalizationAlgebra
    (A : Subalgebra R S) :
    Algebra (uliftBaseLocalizationAtUnder (R := R) (q := q))
      (Localization.AtPrime (Ideal.comap A.val.toRingHom q)) :=
  (Localization.localRingHom
    (uliftBaseUnderIdeal (R := R) (q := q))
    (Ideal.comap A.val.toRingHom q)
    (algebraMap (ULift.{v} R) A)
    (by
      ext r
      simp [uliftBaseUnderIdeal, Ideal.comap_comap])).toAlgebra

/-- Helper for Chap10 Lemma 10 124 3: the distinguished lifted prime localization is naturally
an algebra over the lifted base localization. -/
private noncomputable local instance uliftBaseLocalizationAtUnderLiftedPrimeAlgebra
    (A : Subalgebra R S) :
    Algebra (uliftBaseLocalizationAtUnder (R := R) (q := q))
      (Localization.AtPrime
        ((uliftSubalgebraComapPrimePrimesOver (R := R) (q := q) A).1)) :=
  (Localization.localRingHom
    (uliftBaseUnderIdeal (R := R) (q := q))
    ((uliftSubalgebraComapPrimePrimesOver (R := R) (q := q) A).1)
    (algebraMap (ULift.{v} R) (ULift.{u} A))
    (uliftSubalgebraComapPrime_under_eq (R := R) (q := q) A)).toAlgebra

/-- Helper for Chap10 Lemma 10 124 3: the lifted-base localization comparison respects the
canonical map from `R_(q ∩ R)` into the localization of a finite subalgebra at `q ∩ A`. -/
private theorem uliftBaseLocalizationAtUnderRingEquiv_commutes_subalgebraLocalization
    (A : Subalgebra R S)
    (x : uliftBaseLocalizationAtUnder (R := R) (q := q)) :
    algebraMap
        (uliftBaseLocalizationAtUnder (R := R) (q := q))
        (Localization.AtPrime (Ideal.comap A.val.toRingHom q))
        x =
      algebraMap
        R_qR
        (Localization.AtPrime (Ideal.comap A.val.toRingHom q))
        (uliftBaseLocalizationAtUnderRingEquiv (R := R) (q := q) x) := by
  have hbase :
      Ideal.comap
          (algebraMap (ULift.{v} R) A)
          (Ideal.comap A.val.toRingHom q) =
        uliftBaseUnderIdeal (R := R) (q := q) := by
    -- Proof comment: contracting `q ∩ A` further to the lifted base ring is the same as the
    -- lifted contraction `q ∩ R`.
    ext r
    simp [uliftBaseUnderIdeal, Ideal.comap_comap]
  have hcomp :
      (algebraMap
          (uliftBaseLocalizationAtUnder (R := R) (q := q))
          (Localization.AtPrime (Ideal.comap A.val.toRingHom q)) :
        uliftBaseLocalizationAtUnder (R := R) (q := q) →+*
          Localization.AtPrime (Ideal.comap A.val.toRingHom q)) =
        (algebraMap
            R_qR
            (Localization.AtPrime (Ideal.comap A.val.toRingHom q))).comp
          (uliftBaseLocalizationAtUnderRingEquiv (R := R) (q := q)).toRingHom := by
    -- Proof comment: both maps are the canonical local-ring map from the lifted base
    -- localization, so it is enough to compare them on the dense image of `ULift.{v} R`.
    apply Localization.localRingHom_unique
      (uliftBaseUnderIdeal (R := R) (q := q))
      (Ideal.comap A.val.toRingHom q)
      (algebraMap (ULift.{v} R) A)
      hbase
    intro r
    have hcomm :
        algebraMap
            (Localization.AtPrime (q.under R))
            (Localization.AtPrime (Ideal.comap A.val.toRingHom q))
            (uliftBaseLocalizationAtUnderRingEquiv (R := R) (q := q)
              (algebraMap
                (ULift.{v} R)
                (uliftBaseLocalizationAtUnder (R := R) (q := q)) r)) =
          algebraMap
            (ULift.{v} R)
            (Localization.AtPrime (Ideal.comap A.val.toRingHom q))
            r := by
      calc
        algebraMap
            (Localization.AtPrime (q.under R))
            (Localization.AtPrime (Ideal.comap A.val.toRingHom q))
            (uliftBaseLocalizationAtUnderRingEquiv (R := R) (q := q)
              (algebraMap
                (ULift.{v} R)
                (uliftBaseLocalizationAtUnder (R := R) (q := q)) r)) =
          algebraMap
            (Localization.AtPrime (q.under R))
            (Localization.AtPrime (Ideal.comap A.val.toRingHom q))
            ((algebraMap R (Localization.AtPrime (q.under R)))
              ((ULift.algEquiv (R := ULift.{v} R) (A := R)) r)) := by
              rw [uliftBaseLocalizationAtUnderRingEquiv_apply_algebraMap (R := R) (q := q)]
        _ =
          ((algebraMap
              (Localization.AtPrime (q.under R))
              (Localization.AtPrime (Ideal.comap A.val.toRingHom q))).comp
            (algebraMap R (Localization.AtPrime (q.under R))))
            ((ULift.algEquiv (R := ULift.{v} R) (A := R)) r) := by
              rfl
        _ =
          algebraMap A (Localization.AtPrime (Ideal.comap A.val.toRingHom q))
            (algebraMap R A ((ULift.algEquiv (R := ULift.{v} R) (A := R)) r)) := by
              simpa [RingHom.comp_apply, subalgebraComapPrime_under_eq q A] using
                (Localization.localRingHom_to_map
                  (q.under R)
                  (Ideal.comap A.val.toRingHom q)
                  (algebraMap R A)
                  (subalgebraComapPrime_under_eq q A)
                  ((ULift.algEquiv (R := ULift.{v} R) (A := R)) r))
        _ =
          algebraMap R (Localization.AtPrime (Ideal.comap A.val.toRingHom q))
            ((ULift.algEquiv (R := ULift.{v} R) (A := R)) r) := by
              rfl
        _ =
          algebraMap
            (ULift.{v} R)
            (Localization.AtPrime (Ideal.comap A.val.toRingHom q))
            r := by
              rfl
    simpa [RingHom.comp_apply] using hcomm
  exact congrArg
    (fun f :
      uliftBaseLocalizationAtUnder (R := R) (q := q) →+*
        Localization.AtPrime (Ideal.comap A.val.toRingHom q) ↦ f x)
    hcomp

/-- Helper for Chap10 Lemma 10 124 3: the lifted completed local ring at `q ∩ R` is canonically
identified with the original completed base local ring `R_(q ∩ R)^∧` at the ring level. -/
private noncomputable def uliftCompletedBaseLocalRingRingEquiv :
    uliftBaseCompletedLocalRing (R := R) (q := q) ≃+* R_qR^ := by
  let eLocal := uliftBaseLocalizationAtUnderRingEquiv (R := R) (q := q)
  exact
    RingEquiv.ofBijective
      (@maximalIdealCompletionMap
        (uliftBaseLocalizationAtUnder (R := R) (q := q))
        (Localization.AtPrime (q.under R))
        _ _ _ _ eLocal.toRingHom
        (ringEquiv_isLocalHom_of_localRings eLocal))
      (maximalIdealCompletionMap_bijective_of_ringEquiv eLocal)

/-- Helper for Chap10 Lemma 10 124 3: the specialized base `ULift` completion comparison sends a
dense localized element to the dense image of its transported value. -/
private theorem uliftCompletedBaseLocalRingRingEquiv_apply_algebraMap
    (y : uliftBaseLocalizationAtUnder (R := R) (q := q)) :
    uliftCompletedBaseLocalRingRingEquiv (R := R) (q := q)
        (algebraMap
          (uliftBaseLocalizationAtUnder (R := R) (q := q))
          (uliftBaseCompletedLocalRing (R := R) (q := q)) y) =
      algebraMap
        (Localization.AtPrime (q.under R))
        R_qR^
        (uliftBaseLocalizationAtUnderRingEquiv (R := R) (q := q) y) := by
  let eLocal := uliftBaseLocalizationAtUnderRingEquiv (R := R) (q := q)
  change
    @maximalIdealCompletionMap
        (uliftBaseLocalizationAtUnder (R := R) (q := q))
        (Localization.AtPrime (q.under R))
        _ _ _ _ eLocal.toRingHom (ringEquiv_isLocalHom_of_localRings eLocal)
        (algebraMap
          (uliftBaseLocalizationAtUnder (R := R) (q := q))
          (uliftBaseCompletedLocalRing (R := R) (q := q)) y) =
      algebraMap
        (Localization.AtPrime (q.under R))
        R_qR^
        (eLocal y)
  letI : IsLocalHom eLocal.toRingHom := ringEquiv_isLocalHom_of_localRings eLocal
  have hcomp :=
    congrArg
      (fun g :
        uliftBaseLocalizationAtUnder (R := R) (q := q) →+* R_qR^ ↦ g y)
      (maximalIdealCompletionMap_comp eLocal.toRingHom)
  simpa [RingHom.comp_apply] using hcomp

/-- Helper for Chap10 Lemma 10 124 3: the specialized base `ULift` completion comparison agrees
with the transported `ULift.{v} R`-algebra structure on `R_(q ∩ R)^∧`. -/
private theorem uliftCompletedBaseLocalRingRingEquiv_commutes
    (x : ULift.{v} R) :
    uliftCompletedBaseLocalRingRingEquiv (R := R) (q := q)
        (algebraMap
          (ULift.{v} R)
          (uliftBaseCompletedLocalRing (R := R) (q := q)) x) =
      algebraMap (ULift.{v} R) R_qR^ x := by
  -- The base completion comparison is the generic `ULift` localization/completion transport
  -- specialized to the contracted prime `q ∩ R`.
  calc
    uliftCompletedBaseLocalRingRingEquiv (R := R) (q := q)
        (algebraMap
          (ULift.{v} R)
          (uliftBaseCompletedLocalRing (R := R) (q := q)) x) =
      algebraMap
        (Localization.AtPrime (q.under R))
        R_qR^
        (uliftBaseLocalizationAtUnderRingEquiv
          (R := R) (q := q)
          (algebraMap
            (ULift.{v} R)
            (uliftBaseLocalizationAtUnder (R := R) (q := q)) x)) := by
          simpa using
            (uliftCompletedBaseLocalRingRingEquiv_apply_algebraMap
              (R := R) (q := q)
              (y := algebraMap
                (ULift.{v} R)
                (uliftBaseLocalizationAtUnder (R := R) (q := q)) x))
    _ = algebraMap
          (Localization.AtPrime (q.under R))
          R_qR^
          (algebraMap R (Localization.AtPrime (q.under R))
            ((ULift.algEquiv (R := ULift.{v} R) (A := R)) x)) := by
          rw [uliftBaseLocalizationAtUnderRingEquiv_apply_algebraMap
            (R := R) (q := q)]
    _ = algebraMap (ULift.{v} R) R_qR^ x := by
          rfl

/-- Helper for Chap10 Lemma 10 124 3: the lifted completed local ring at `q ∩ R` is canonically
identified with the original completed base local ring `R_(q ∩ R)^∧` as a `ULift.{v} R`-algebra.
-/
private noncomputable def uliftCompletedBaseLocalRingAlgEquiv :
    uliftBaseCompletedLocalRing (R := R) (q := q) ≃ₐ[ULift.{v} R] R_qR^ :=
  AlgEquiv.ofRingEquiv
    (f := uliftCompletedBaseLocalRingRingEquiv (R := R) (q := q))
    (uliftCompletedBaseLocalRingRingEquiv_commutes (R := R) (q := q))

/-- Helper for Chap10 Lemma 10 124 3: the inverse base `ULift` completion comparison sends a
dense element of `R_(q ∩ R)^∧` back to the dense image of the corresponding lifted localization
element. -/
private theorem uliftCompletedBaseLocalRingAlgEquiv_symm_apply_algebraMap
    (y : R_qR) :
    (uliftCompletedBaseLocalRingAlgEquiv (R := R) (q := q)).symm
        (algebraMap R_qR R_qR^ y) =
      algebraMap
        (uliftBaseLocalizationAtUnder (R := R) (q := q))
        (uliftBaseCompletedLocalRing (R := R) (q := q))
        ((uliftBaseLocalizationAtUnderRingEquiv (R := R) (q := q)).symm y) := by
  -- Proof comment: apply the forward comparison and use the dense-element formula already proved
  -- for `uliftCompletedBaseLocalRingRingEquiv`.
  apply (uliftCompletedBaseLocalRingAlgEquiv (R := R) (q := q)).injective
  calc
    uliftCompletedBaseLocalRingAlgEquiv (R := R) (q := q)
        ((uliftCompletedBaseLocalRingAlgEquiv (R := R) (q := q)).symm
          (algebraMap R_qR R_qR^ y)) =
      algebraMap R_qR R_qR^ y := by
          exact AlgEquiv.apply_symm_apply _ _
    _ =
      uliftCompletedBaseLocalRingAlgEquiv (R := R) (q := q)
        (algebraMap
          (uliftBaseLocalizationAtUnder (R := R) (q := q))
          (uliftBaseCompletedLocalRing (R := R) (q := q))
          ((uliftBaseLocalizationAtUnderRingEquiv (R := R) (q := q)).symm y)) := by
          simpa using
            (uliftCompletedBaseLocalRingRingEquiv_apply_algebraMap
              (R := R) (q := q)
              (y := (uliftBaseLocalizationAtUnderRingEquiv (R := R) (q := q)).symm y)).symm

/-- Helper for Chap10 Lemma 10 124 3: at every quotient stage, the inverse base `ULift`
completion comparison sends a Cauchy representative to the class of its transported localization
term. -/
private theorem uliftCompletedBaseLocalRingAlgEquiv_symm_evalA_mk
    (n : ℕ) (f : AdicCauchySequence (maximalIdeal R_qR) R_qR) :
    AdicCompletion.evalₐ
        (maximalIdeal (uliftBaseLocalizationAtUnder (R := R) (q := q))) n
        ((uliftCompletedBaseLocalRingAlgEquiv (R := R) (q := q)).symm
          (AdicCompletion.mk (maximalIdeal R_qR) R_qR f)) =
      Ideal.Quotient.mk
        ((maximalIdeal (uliftBaseLocalizationAtUnder (R := R) (q := q))) ^ n)
        ((uliftBaseLocalizationAtUnderRingEquiv (R := R) (q := q)).symm (f.val n)) := by
  let eLocal := uliftBaseLocalizationAtUnderRingEquiv (R := R) (q := q)
  change
    AdicCompletion.evalₐ
        (maximalIdeal (uliftBaseLocalizationAtUnder (R := R) (q := q))) n
        ((uliftCompletedBaseLocalRingRingEquiv (R := R) (q := q)).symm
          (AdicCompletion.mk (maximalIdeal R_qR) R_qR f)) =
      Ideal.Quotient.mk
        ((maximalIdeal (uliftBaseLocalizationAtUnder (R := R) (q := q))) ^ n)
        (eLocal.symm (f.val n))
  -- Proof comment: evaluate the inverse completion equivalence stagewise, then collapse the
  -- inverse quotient transport on the dense class of `f.val n`.
  calc
    AdicCompletion.evalₐ
        (maximalIdeal (uliftBaseLocalizationAtUnder (R := R) (q := q))) n
        ((uliftCompletedBaseLocalRingRingEquiv (R := R) (q := q)).symm
          (AdicCompletion.mk (maximalIdeal R_qR) R_qR f)) =
      (ringEquiv_quotient_maximalIdeal_pow eLocal n).symm
        (AdicCompletion.evalₐ (maximalIdeal R_qR) n
          (AdicCompletion.mk (maximalIdeal R_qR) R_qR f)) := by
            simpa [uliftCompletedBaseLocalRingRingEquiv] using
              (ringEquiv_completion_symm_evalₐ
                (e := eLocal) n (AdicCompletion.mk (maximalIdeal R_qR) R_qR f))
    _ =
      (ringEquiv_quotient_maximalIdeal_pow eLocal n).symm
        (Ideal.Quotient.mk ((maximalIdeal R_qR) ^ n) (f.val n)) := by
          rw [AdicCompletion.evalₐ_mk]
    _ =
      Ideal.Quotient.mk
        ((maximalIdeal (uliftBaseLocalizationAtUnder (R := R) (q := q))) ^ n)
        (eLocal.symm (f.val n)) := by
          exact ringEquiv_quotient_maximalIdeal_pow_symm_mk eLocal n (f.val n)

/-- Helper for Chap10 Lemma 10 124 3: the intermediate tensor transport from
`R_(q ∩ R)^∧ ⊗[ULift.{v} R] A` to the same-universe model
`uliftBaseCompletedLocalRing ⊗[ULift.{v} R] ULift.{u} A`. -/
private noncomputable def finiteSubalgebraPiCompletionTensorCongr
    (A : Subalgebra R S) :
    (R_qR^ ⊗[ULift.{v} R] A) ≃+*
      uliftBaseCompletionTensorProduct (R := R) (q := q) A :=
  by
    let _ : Module (ULift.{v} R) R_qR^ := Algebra.toModule
    let _ : Module (ULift.{v} R) A := Algebra.toModule
    let _ : Module (ULift.{v} R) (uliftBaseCompletedLocalRing (R := R) (q := q)) :=
      Algebra.toModule
    let _ : Module (ULift.{v} R) (ULift.{u} A) := Algebra.toModule
    -- Proof comment: this is the tensor-product congruence induced by transporting both factors to
    -- the same-universe model used by Lemma `10.97.8`.
    exact
      (Algebra.TensorProduct.congr
        (uliftCompletedBaseLocalRingAlgEquiv (R := R) (q := q)).symm
        ((ULift.algEquiv : ULift.{u} A ≃ₐ[ULift.{v} R] A).symm)).toRingEquiv

/-- Helper for Chap10 Lemma 10 124 3: finite generation of the finite subalgebra transports to
the same-universe `ULift` model used to apply Lemma 10.97.8. -/
private theorem moduleFinite_uliftBase_uliftSubalgebra
    (A : Subalgebra R S) (hAfin : Module.Finite R A) :
    Module.Finite (ULift.{v} R) (ULift.{u} A) := by
  -- First regard `A` as finite over the lifted base, then transport along `ULift.algEquiv`.
  letI : Module.Finite (ULift.{v} R) A :=
    Module.Finite.of_restrictScalars_finite R (ULift.{v} R) A
  exact Module.Finite.equiv
    ((ULift.algEquiv : ULift.{u} A ≃ₐ[ULift.{v} R] A).symm.toLinearEquiv)

variable [IsNoetherianRing R] [Algebra.FiniteType R S]

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 3: Noetherianity is preserved by the lifted base ring
`ULift.{v} R`. -/
private instance uliftBase_isNoetherianRing :
    IsNoetherianRing (ULift.{v} R) :=
  isNoetherianRing_of_ringEquiv R
    ((ULift.algEquiv (R := ULift.{v} R) (A := R)).symm.toRingEquiv)

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 3: the same-universe `07N9` product decomposition for the
lifted finite model, isolated as a standalone equivalence so later declarations do not re-run its
elaboration inside longer composite terms. -/
private noncomputable def finiteSubalgebraPiCompletionPiRingEquiv
    (A : Subalgebra R S) [Module.Finite (ULift.{v} R) (ULift.{u} A)] :
    uliftBaseCompletionTensorProduct (R := R) (q := q) A ≃+*
      ∀ q0 : (uliftBaseUnderPrime (R := R) (q := q)).asIdeal.primesOver (ULift.{u} A),
        AdicCompletion (maximalIdeal (Localization.AtPrime q0.1)) (Localization.AtPrime q0.1) := by
  let _ : Module (ULift.{v} R) (uliftBaseCompletedLocalRing (R := R) (q := q)) :=
    Algebra.toModule
  let _ : Module (ULift.{v} R) (ULift.{u} A) := Algebra.toModule
  let _ : CommRing (uliftBaseCompletionTensorProduct (R := R) (q := q) A) :=
    uliftBaseCompletionTensorProductCommRing (R := R) (q := q) A
  -- Route correction: this cached same-universe `07N9` equivalence is the only remaining
  -- imported boundary for the finite-away route below; every downstream declaration is already
  -- written to consume it abstractly without reopening the upstream stage-bijectivity proof.
  -- Proof comment: with the lifted tensor-product structure cached explicitly, the owner `07N9`
  -- equivalence applies directly to the same-universe model.
  simpa [uliftBaseCompletedLocalRing, uliftBaseLocalizationAtUnder,
    uliftBaseUnderPrime, max_comm, max_left_comm, max_assoc] using
    (completion_tensorProductOverBase_ringEquiv_pi_localRingCompletion
      (R := ULift.{v} R) (S := ULift.{u} A) (p := uliftBaseUnderPrime (R := R) (q := q)))

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 3: choose the transported same-universe `Π`-decomposition once
so later coordinate computations do not repeatedly unfold the existential packaging. -/
private noncomputable def finiteSubalgebraPiCompletionRingEquiv
    (A : Subalgebra R S) (hAfin : Module.Finite R A) :
    (R_qR^ ⊗[R] A) ≃+*
      ∀ q0 : (uliftBaseUnderPrime (R := R) (q := q)).asIdeal.primesOver (ULift.{u} A),
        AdicCompletion (maximalIdeal (Localization.AtPrime q0.1)) (Localization.AtPrime q0.1) :=
  by
    let _ : Module.Finite (ULift.{v} R) (ULift.{u} A) :=
      moduleFinite_uliftBase_uliftSubalgebra (R := R) (S := S) A hAfin
    let _ : Module (ULift.{v} R) R_qR^ := Algebra.toModule
    let _ : Module (ULift.{v} R) A := Algebra.toModule
    let _ : CommRing (tensorProductOverUliftBase (R := R) (q := q) A) :=
      tensorProductOverUliftBaseCommRing (R := R) (q := q) A
    -- Proof comment: compose the three cached transports once, so later coordinate computations
    -- only unfold the packaged equivalence instead of rebuilding the tensor infrastructure.
    exact
      (tensorProductOverUliftBaseAlgEquiv (R := R) (q := q) (A := A)).toRingEquiv.trans <|
        (finiteSubalgebraPiCompletionTensorCongr (R := R) (q := q) A).trans <|
          finiteSubalgebraPiCompletionPiRingEquiv (R := R) (q := q) A

omit [Algebra.FiniteType R S] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 124 3: a ring hom out of `R_(q ∩ R)^∧ ⊗[R] A` is determined by its
values on the two tensor generators `x ⊗ 1` and `1 ⊗ a`. -/
private theorem tensorProductRingHom_eq_of_generators
    (A : Subalgebra R S)
    {T : Type*} [CommRing T]
    (f g : R_qR^ ⊗[R] A →+* T)
    (hleft : ∀ x : R_qR^, f (x ⊗ₜ[R] (1 : A)) = g (x ⊗ₜ[R] (1 : A)))
    (hright : ∀ a : A, f ((1 : R_qR^) ⊗ₜ[R] a) = g ((1 : R_qR^) ⊗ₜ[R] a)) :
    f = g := by
  -- Proof comment: tensor-product ring homomorphisms are determined by their two structure maps.
  apply Algebra.TensorProduct.ringHom_ext
  · apply RingHom.ext
    intro x
    -- Proof comment: the left structure map evaluates at the generator `x ⊗ₜ[R] 1`.
    simpa [RingHom.comp_apply] using hleft x
  · apply RingHom.ext
    intro a
    -- Proof comment: the right structure map evaluates at the generator `1 ⊗ₜ[R] a`.
    simpa [RingHom.comp_apply, Algebra.TensorProduct.includeRight_apply] using hright a

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 3: the canonical ring hom `ULift.{u} A → A` fixes the
universe spelling used in the distinguished same-universe prime over `q ∩ A`. -/
private noncomputable def uliftSubalgebraRingHom (A : Subalgebra R S) :
    ULift.{u} A →+* A :=
  (ULift.algEquiv : ULift.{u} A ≃ₐ[ULift.{v} R] A).toRingHom

/-- Helper for Chap10 Lemma 10 124 3: the distinguished `qLift` factor in the lifted `Π`
decomposition is exactly the transported completion at `q ∩ A`, so it can be compared directly
with `S_q^`. -/
private noncomputable def finiteSubalgebraPiCompletionDistinguishedCoordRingEquiv
    (A : Subalgebra R S) (r : A)
    (hrq : (r : S) ∉ q)
    (haway : Function.Bijective (Localization.awayMap A.val.toRingHom r)) :
    AdicCompletion
        (maximalIdeal
          (Localization.AtPrime
            (Ideal.comap
              (uliftSubalgebraRingHom (R := R) (S := S) A)
              (Ideal.comap A.val.toRingHom q))))
        (Localization.AtPrime
          (Ideal.comap
            (uliftSubalgebraRingHom (R := R) (S := S) A)
            (Ideal.comap A.val.toRingHom q))) ≃+*
      S_q^ :=
  -- Proof comment: first remove the `ULift` spelling from the distinguished completion factor,
  -- then transport the resulting completed local ring to `S_q^` via the away-bijective model.
  (uliftLocalizationAtPrimeCompletionRingEquiv
      (R := R) (Q := Ideal.comap A.val.toRingHom q)).trans
    (completedLocalRingRingEquivOfAwayBijectiveAtPrime q A r hrq haway)

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 3: the distinguished `qLift` coordinate of the lifted
`Π`-decomposition, transported back to `S_q^`. -/
private noncomputable def finiteSubalgebraPiCompletionCoordHom
    (A : Subalgebra R S) (r : A) (hAfin : Module.Finite R A)
    (hrq : (r : S) ∉ q)
    (haway : Function.Bijective (Localization.awayMap A.val.toRingHom r)) :
    R_qR^ ⊗[R] A →+* S_q^ :=
  -- Proof comment: evaluate the cached `Π`-decomposition at the distinguished lifted prime and
  -- compose with the transported comparison from that completion factor to `S_q^`.
  (finiteSubalgebraPiCompletionDistinguishedCoordRingEquiv
      (R := R) (q := q) A r hrq haway).toRingHom.comp
    ((Pi.evalRingHom
        (fun q0 : (uliftBaseUnderPrime (R := R) (q := q)).asIdeal.primesOver (ULift.{u} A) ↦
          AdicCompletion (maximalIdeal (Localization.AtPrime q0.1))
            (Localization.AtPrime q0.1))
        (uliftSubalgebraComapPrimePrimesOver (R := R) (q := q) A)).comp
      (finiteSubalgebraPiCompletionRingEquiv (R := R) (q := q) A hAfin).toRingHom)

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 3: stagewise evaluation of the distinguished `qLift`
coordinate on a Cauchy left generator records the same quotient representative as the canonical
base-localization map. -/
private theorem finiteSubalgebraPiCompletionCoord_mk_tmul_one_evalA
    (A : Subalgebra R S) (r : A) (hAfin : Module.Finite R A)
    (hrq : (r : S) ∉ q)
    (haway : Function.Bijective (Localization.awayMap A.val.toRingHom r))
    (n : ℕ) (f : AdicCauchySequence (maximalIdeal R_qR) R_qR) :
    AdicCompletion.evalₐ (maximalIdeal S_q) n
        (finiteSubalgebraPiCompletionCoordHom (R := R) (q := q) A r hAfin hrq haway
          ((AdicCompletion.mk (maximalIdeal R_qR) R_qR f) ⊗ₜ[R] (1 : A))) =
      Ideal.Quotient.mk ((maximalIdeal S_q) ^ n) (algebraMap R_qR S_q (f.val n)) := by
  -- Route correction: the staged tensor proof now reduces to one explicit quotient-stage
  -- normalization for the distinguished `qLift` factor. The proof first computes that raw stage,
  -- then transports the resulting quotient class across the two cached local-ring equivalences.
  let qA : Ideal A := Ideal.comap A.val.toRingHom q
  let qLift : Ideal (ULift.{u} A) :=
    Ideal.comap (uliftSubalgebraRingHom (R := R) (S := S) A) qA
  letI :
      Algebra
        (uliftBaseLocalizationAtUnder (R := R) (q := q))
        (Localization.AtPrime qLift) :=
    uliftBaseLocalizationAtUnderLiftedPrimeAlgebra (R := R) (q := q) A
  let inner :
      AdicCompletion (maximalIdeal (Localization.AtPrime qLift))
        (Localization.AtPrime qLift) :=
    ((Pi.evalRingHom
          (fun q0 :
            (uliftBaseUnderPrime (R := R) (q := q)).asIdeal.primesOver (ULift.{u} A) ↦
              AdicCompletion (maximalIdeal (Localization.AtPrime q0.1))
                (Localization.AtPrime q0.1))
          (uliftSubalgebraComapPrimePrimesOver (R := R) (q := q) A)).comp
        (finiteSubalgebraPiCompletionRingEquiv (R := R) (q := q) A hAfin).toRingHom)
      ((AdicCompletion.mk (maximalIdeal R_qR) R_qR f) ⊗ₜ[R] (1 : A))
  let e1Local := uliftLocalizationAtPrimeRingEquiv (R := R) qA
  let e2Local := subalgebraLocalRingEquivOfAwayMapBijective q A r hrq haway
  have hraw :
      AdicCompletion.evalₐ (maximalIdeal (Localization.AtPrime qLift)) n inner =
        Ideal.Quotient.mk ((maximalIdeal (Localization.AtPrime qLift)) ^ n)
          (algebraMap
            (uliftBaseLocalizationAtUnder (R := R) (q := q))
            (Localization.AtPrime qLift)
            ((uliftBaseLocalizationAtUnderRingEquiv (R := R) (q := q)).symm (f.val n))) := by
    -- Proof comment: the cached tensor and `ULift` transports already normalize the
    -- distinguished `07N9` coordinate at the raw `qLift` stage before any outer completion
    -- equivalence is touched.
    simpa [inner, qA, qLift, finiteSubalgebraPiCompletionRingEquiv,
      finiteSubalgebraPiCompletionTensorCongr, finiteSubalgebraPiCompletionPiRingEquiv,
      tensorProductOverUliftBaseAlgEquiv_tmul, uliftSubalgebraComapPrimePrimesOver_asIdeal,
      RingHom.comp_apply, uliftCompletedBaseLocalRingAlgEquiv_symm_evalA_mk]
  have hloc :
      Localization.localRingHom
          qLift
          qA
          (uliftSubalgebraRingHom (R := R) (S := S) A)
          rfl
          (algebraMap
            (uliftBaseLocalizationAtUnder (R := R) (q := q))
            (Localization.AtPrime qLift)
            ((uliftBaseLocalizationAtUnderRingEquiv (R := R) (q := q)).symm (f.val n))) =
        algebraMap
          (uliftBaseLocalizationAtUnder (R := R) (q := q))
          (Localization.AtPrime qA)
          ((uliftBaseLocalizationAtUnderRingEquiv (R := R) (q := q)).symm (f.val n)) := by
    have hcomp :
        (Localization.localRingHom
            qLift
            qA
            (uliftSubalgebraRingHom (R := R) (S := S) A)
            rfl).comp
            (algebraMap
              (uliftBaseLocalizationAtUnder (R := R) (q := q))
              (Localization.AtPrime qLift)) =
          (algebraMap
            (uliftBaseLocalizationAtUnder (R := R) (q := q))
            (Localization.AtPrime qA)) := by
      -- Proof comment: localizing at the lifted prime over `q ∩ A` is the same as localizing
      -- directly at `q ∩ A` after the lifted base localization.
      simpa [qA, qLift, uliftSubalgebraComapPrime_under_eq (R := R) (q := q) A] using
        (Localization.localRingHom_comp
          (uliftBaseUnderIdeal (R := R) (q := q))
          qLift
          qA
          (algebraMap (ULift.{v} R) (ULift.{u} A))
          (uliftSubalgebraComapPrime_under_eq (R := R) (q := q) A)
          (uliftSubalgebraRingHom (R := R) (S := S) A)
          rfl).symm
    exact congrArg
      (fun g :
        uliftBaseLocalizationAtUnder (R := R) (q := q) →+*
          Localization.AtPrime qA ↦
            g ((uliftBaseLocalizationAtUnderRingEquiv (R := R) (q := q)).symm (f.val n)))
      hcomp
  have htransport :
      (ringEquiv_quotient_maximalIdeal_pow e2Local n)
          ((ringEquiv_quotient_maximalIdeal_pow e1Local n)
            (Ideal.Quotient.mk ((maximalIdeal (Localization.AtPrime qLift)) ^ n)
              (algebraMap
                (uliftBaseLocalizationAtUnder (R := R) (q := q))
                (Localization.AtPrime qLift)
                ((uliftBaseLocalizationAtUnderRingEquiv (R := R) (q := q)).symm
                  (f.val n))))) =
        Ideal.Quotient.mk ((maximalIdeal S_q) ^ n) (algebraMap R_qR S_q (f.val n)) := by
    -- Proof comment: quotient-stage transport first removes the `ULift` spelling and then uses
    -- the away-bijective finite localization comparison to recover the canonical class in `S_q`.
    simp only [ringEquiv_quotient_maximalIdeal_pow, Ideal.quotientMap_mk]
    rw [uliftLocalizationAtPrimeRingEquiv_apply]
    rw [hloc]
    rw [uliftBaseLocalizationAtUnderRingEquiv_commutes_subalgebraLocalization
      (R := R) (q := q) A
      ((uliftBaseLocalizationAtUnderRingEquiv (R := R) (q := q)).symm (f.val n))]
    rw [subalgebraLocalRingEquivOfAwayMapBijective_commutes q A r hrq haway (f.val n)]
  rw [finiteSubalgebraPiCompletionCoordHom, RingHom.comp_apply]
  -- Proof comment: apply the two completion-stage transport formulas and then plug in the raw
  -- `qLift` stage computation and the quotient-stage localization transport.
  calc
    AdicCompletion.evalₐ (maximalIdeal S_q) n
        ((completedLocalRingRingEquivOfAwayBijectiveAtPrime q A r hrq haway)
          ((uliftLocalizationAtPrimeCompletionRingEquiv (R := R) (Q := qA)) inner)) =
      (ringEquiv_quotient_maximalIdeal_pow e2Local n)
        (AdicCompletion.evalₐ (maximalIdeal (Localization.AtPrime qA)) n
          ((uliftLocalizationAtPrimeCompletionRingEquiv (R := R) (Q := qA)) inner)) := by
            simpa [e2Local, completedLocalRingRingEquivOfAwayBijectiveAtPrime] using
              (maximalIdealCompletionMap_evalₐ_of_ringEquiv
                (e := e2Local) n
                ((uliftLocalizationAtPrimeCompletionRingEquiv (R := R) (Q := qA)) inner))
    _ =
      (ringEquiv_quotient_maximalIdeal_pow e2Local n)
        ((ringEquiv_quotient_maximalIdeal_pow e1Local n)
          (AdicCompletion.evalₐ (maximalIdeal (Localization.AtPrime qLift)) n inner)) := by
            congr 1
            simpa [e1Local, uliftLocalizationAtPrimeCompletionRingEquiv] using
              (maximalIdealCompletionMap_evalₐ_of_ringEquiv
                (e := e1Local) n inner)
    _ =
      (ringEquiv_quotient_maximalIdeal_pow e2Local n)
        ((ringEquiv_quotient_maximalIdeal_pow e1Local n)
          (Ideal.Quotient.mk ((maximalIdeal (Localization.AtPrime qLift)) ^ n)
            (algebraMap
              (uliftBaseLocalizationAtUnder (R := R) (q := q))
              (Localization.AtPrime qLift)
              ((uliftBaseLocalizationAtUnderRingEquiv (R := R) (q := q)).symm
                (f.val n))))) := by
            rw [hraw]
    _ = Ideal.Quotient.mk ((maximalIdeal S_q) ^ n) (algebraMap R_qR S_q (f.val n)) := by
          exact htransport

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 3: the distinguished `qLift` coordinate on a left tensor
generator agrees first with the canonical completion map from `R_(q ∩ R)^∧`. -/
private theorem finiteSubalgebraPiCompletionCoord_tmul_one_baseMap
    (A : Subalgebra R S) (r : A) (hAfin : Module.Finite R A)
    (hrq : (r : S) ∉ q)
    (haway : Function.Bijective (Localization.awayMap A.val.toRingHom r))
    (x : R_qR^) :
    finiteSubalgebraPiCompletionCoordHom (R := R) (q := q) A r hAfin hrq haway
        (x ⊗ₜ[R] (1 : A)) =
      maximalIdealCompletionMap
        (Localization.localRingHom (q.under R) q (algebraMap R S) rfl) x := by
  let P : R_qR^ → Prop := fun z ↦
    finiteSubalgebraPiCompletionCoordHom (R := R) (q := q) A r hAfin hrq haway
        (z ⊗ₜ[R] (1 : A)) =
      maximalIdealCompletionMap
        (Localization.localRingHom (q.under R) q (algebraMap R S) rfl) z
  change P x
  -- Proof comment: once the stagewise quotient representative is identified on Cauchy sequences,
  -- the two completion elements are equal by `AdicCompletion.ext_evalₐ`.
  refine AdicCompletion.induction_on (I := maximalIdeal R_qR) (M := R_qR) x ?_
  intro f
  apply AdicCompletion.ext_evalₐ
  intro n
  calc
    AdicCompletion.evalₐ (maximalIdeal S_q) n
        (finiteSubalgebraPiCompletionCoordHom (R := R) (q := q) A r hAfin hrq haway
          ((AdicCompletion.mk (maximalIdeal R_qR) R_qR f) ⊗ₜ[R] (1 : A))) =
      Ideal.Quotient.mk ((maximalIdeal S_q) ^ n) (algebraMap R_qR S_q (f.val n)) := by
        exact
          finiteSubalgebraPiCompletionCoord_mk_tmul_one_evalA
            (R := R) (q := q) A r hAfin hrq haway n f
    _ =
      AdicCompletion.evalₐ (maximalIdeal S_q) n
        (maximalIdealCompletionMap
          (Localization.localRingHom (q.under R) q (algebraMap R S) rfl)
          (AdicCompletion.mk (maximalIdeal R_qR) R_qR f)) := by
        symm
        exact
          maximalIdealCompletionMap_evalₐ_mk
            (Localization.localRingHom (q.under R) q (algebraMap R S) rfl) n f

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 3: the distinguished `qLift` coordinate of the lifted
`Π`-decomposition agrees with the canonical tensor-product projection on the left generator
`x ⊗ₜ[R] 1`. -/
private theorem finiteSubalgebraPiCompletionCoord_tmul_one
    (A : Subalgebra R S) (r : A) (hAfin : Module.Finite R A)
    (hrq : (r : S) ∉ q)
    (haway : Function.Bijective (Localization.awayMap A.val.toRingHom r))
    (x : R_qR^) :
    finiteSubalgebraPiCompletionCoordHom (R := R) (q := q) A r hAfin hrq haway
        (x ⊗ₜ[R] (1 : A)) =
      completedTensorProductProjectionSubalgebra q A (x ⊗ₜ[R] (1 : A)) := by
  -- Proof comment: the main comparison is now the canonical completion map; the tensor-product
  -- projection statement is just the companion rewrite via the existing left-generator formula.
  calc
    finiteSubalgebraPiCompletionCoordHom (R := R) (q := q) A r hAfin hrq haway
        (x ⊗ₜ[R] (1 : A)) =
      maximalIdealCompletionMap
        (Localization.localRingHom (q.under R) q (algebraMap R S) rfl) x := by
          exact
            finiteSubalgebraPiCompletionCoord_tmul_one_baseMap
              (R := R) (q := q) A r hAfin hrq haway x
    _ = completedTensorProductProjectionSubalgebra q A (x ⊗ₜ[R] (1 : A)) := by
          symm
          exact completedTensorProductProjectionSubalgebra_tmul_one q A x

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 3: the distinguished `qLift` coordinate of the lifted
`Π`-decomposition agrees with the canonical tensor-product projection on the right generator
`1 ⊗ₜ[R] a`. -/
private theorem finiteSubalgebraPiCompletionCoord_one_tmul
    (A : Subalgebra R S) (r a : A) (hAfin : Module.Finite R A)
    (hrq : (r : S) ∉ q)
    (haway : Function.Bijective (Localization.awayMap A.val.toRingHom r)) :
    finiteSubalgebraPiCompletionCoordHom (R := R) (q := q) A r hAfin hrq haway
        ((1 : R_qR^) ⊗ₜ[R] a) =
      completedTensorProductProjectionSubalgebra q A ((1 : R_qR^) ⊗ₜ[R] a) := by
  -- Route correction: compute the distinguished coordinate on the dense right tensor generator
  -- directly through the cached `07N9` transport, then use the two dense `algebraMap`
  -- comparison lemmas instead of reopening arbitrary completion transport.
  rw [finiteSubalgebraPiCompletionCoordHom]
  simp only [RingHom.comp_apply]
  have hraw :
      ((Pi.evalRingHom
            (fun q0 :
              (uliftBaseUnderPrime (R := R) (q := q)).asIdeal.primesOver (ULift.{u} A) ↦
                AdicCompletion (maximalIdeal (Localization.AtPrime q0.1))
                  (Localization.AtPrime q0.1))
            (uliftSubalgebraComapPrimePrimesOver (R := R) (q := q) A)).comp
          (finiteSubalgebraPiCompletionRingEquiv (R := R) (q := q) A hAfin).toRingHom)
          ((1 : R_qR^) ⊗ₜ[R] a) =
        algebraMap
          (Localization.AtPrime
            (Ideal.comap
              (uliftSubalgebraRingHom (R := R) (S := S) A)
              (Ideal.comap A.val.toRingHom q)))
          (AdicCompletion
            (maximalIdeal
              (Localization.AtPrime
                (Ideal.comap
                  (uliftSubalgebraRingHom (R := R) (S := S) A)
                  (Ideal.comap A.val.toRingHom q))))
            (Localization.AtPrime
              (Ideal.comap
                (uliftSubalgebraRingHom (R := R) (S := S) A)
                (Ideal.comap A.val.toRingHom q))))
          (algebraMap
            (ULift.{u} A)
            (Localization.AtPrime
              (Ideal.comap
                (uliftSubalgebraRingHom (R := R) (S := S) A)
                (Ideal.comap A.val.toRingHom q)))
            ((ULift.algEquiv : ULift.{u} A ≃ₐ[ULift.{v} R] A).symm a)) := by
    -- Proof comment: all three cached tensor/completion transports preserve the pure tensor
    -- `1 ⊗ₜ[R] a`, so the distinguished coordinate is the dense local image of `a`.
    simpa [finiteSubalgebraPiCompletionRingEquiv, finiteSubalgebraPiCompletionTensorCongr,
      finiteSubalgebraPiCompletionPiRingEquiv, tensorProductOverUliftBaseAlgEquiv_tmul,
      uliftSubalgebraComapPrimePrimesOver_asIdeal]
  have hcoord :
    finiteSubalgebraPiCompletionCoordHom (R := R) (q := q) A r hAfin hrq haway
        ((1 : R_qR^) ⊗ₜ[R] a) =
      (finiteSubalgebraPiCompletionDistinguishedCoordRingEquiv
          (R := R) (q := q) A r hrq haway)
        (algebraMap
          (Localization.AtPrime
            (Ideal.comap
              (uliftSubalgebraRingHom (R := R) (S := S) A)
              (Ideal.comap A.val.toRingHom q)))
          (AdicCompletion
            (maximalIdeal
              (Localization.AtPrime
                (Ideal.comap
                  (uliftSubalgebraRingHom (R := R) (S := S) A)
                  (Ideal.comap A.val.toRingHom q))))
            (Localization.AtPrime
              (Ideal.comap
                (uliftSubalgebraRingHom (R := R) (S := S) A)
                (Ideal.comap A.val.toRingHom q))))
          (algebraMap
            (ULift.{u} A)
            (Localization.AtPrime
              (Ideal.comap
                (uliftSubalgebraRingHom (R := R) (S := S) A)
                (Ideal.comap A.val.toRingHom q)))
            ((ULift.algEquiv : ULift.{u} A ≃ₐ[ULift.{v} R] A).symm a)) := by
      simpa [finiteSubalgebraPiCompletionCoordHom, RingHom.comp_apply] using
        congrArg
          (finiteSubalgebraPiCompletionDistinguishedCoordRingEquiv
            (R := R) (q := q) A r hrq haway)
          hraw
  rw [hcoord]
  rw [uliftLocalizationAtPrimeCompletionRingEquiv_apply_algebraMap]
  simpa [completedTensorProductProjectionSubalgebra_one_tmul] using
    (completedLocalRingRingEquivOfAwayBijectiveAtPrime_apply_algebraMap
      (R := R) (q := q) A r a hrq haway)

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 3: after transporting the distinguished `qLift` coordinate of
the lifted `Π`-decomposition back to `S_q^`, one recovers the canonical tensor-product
projection. -/
private theorem finiteSubalgebraPiCompletionCoord
    (A : Subalgebra R S) (r : A) (hAfin : Module.Finite R A)
    (hrq : (r : S) ∉ q)
    (haway : Function.Bijective (Localization.awayMap A.val.toRingHom r))
    (z : R_qR^ ⊗[R] A) :
    finiteSubalgebraPiCompletionCoordHom (R := R) (q := q) A r hAfin hrq haway z =
      completedTensorProductProjectionSubalgebra q A z := by
  -- Proof comment: once the two tensor-generator formulas are available, tensor-product
  -- extensionality identifies the whole coordinate map with the canonical projection.
  let f :=
    finiteSubalgebraPiCompletionCoordHom (R := R) (q := q) A r hAfin hrq haway
  let g := completedTensorProductProjectionSubalgebra q A
  have hfg : f = g :=
    tensorProductRingHom_eq_of_generators
      (R := R) (S := S) (q := q) A f g
      (finiteSubalgebraPiCompletionCoord_tmul_one
        (R := R) (q := q) A r hAfin hrq haway)
      (fun a ↦
        finiteSubalgebraPiCompletionCoord_one_tmul
          (R := R) (q := q) A r a hAfin hrq haway)
  exact DFunLike.congr_fun hfg z

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 3: once the distinguished `qLift` coordinate is normalized,
splitting the lifted `Π` target yields the desired ring product decomposition with canonical first
projection. -/
private theorem finiteSubalgebraPiCompletionSplit
    (A : Subalgebra R S) (r : A) (hAfin : Module.Finite R A)
    (hrq : (r : S) ∉ q)
    (haway : Function.Bijective (Localization.awayMap A.val.toRingHom r)) :
    ∃ (B0 : Type (max u v)) (_ : CommRing B0)
      (E0 : (R_qR^ ⊗[R] A) ≃+* (S_q^ × B0)),
      ∀ z : R_qR^ ⊗[R] A,
        RingHom.fst S_q^ B0 (E0 z) = completedTensorProductProjectionSubalgebra q A z := by
  classical
  let i0 := uliftSubalgebraComapPrimePrimesOver (R := R) (q := q) A
  let B0 : Type (max u v) :=
    (j :
      { i :
          (uliftBaseUnderPrime (R := R) (q := q)).asIdeal.primesOver (ULift.{u} A) //
        i ≠ i0 }) →
      AdicCompletion (maximalIdeal (Localization.AtPrime j.1.1)) (Localization.AtPrime j.1.1)
  let Eπ :
      (R_qR^ ⊗[R] A) ≃+*
        (AdicCompletion (maximalIdeal (Localization.AtPrime i0.1))
            (Localization.AtPrime i0.1) × B0) :=
    ringEquivProdOfPiSplitAt
      (finiteSubalgebraPiCompletionRingEquiv (R := R) (q := q) A hAfin) i0
  let E0 : (R_qR^ ⊗[R] A) ≃+* (S_q^ × B0) :=
    Eπ.trans <|
      RingEquiv.prodCongr
        (finiteSubalgebraPiCompletionDistinguishedCoordRingEquiv
          (R := R) (q := q) A r hrq haway)
        (RingEquiv.refl B0)
  refine ⟨B0, inferInstance, E0, ?_⟩
  intro z
  -- Proof comment: split the `Π`-target at the distinguished owner, then transport only that
  -- first coordinate across the cached comparison to `S_q^`.
  calc
    RingHom.fst S_q^ B0 (E0 z) =
        finiteSubalgebraPiCompletionDistinguishedCoordRingEquiv
          (R := R) (q := q) A r hrq haway
          (RingHom.fst
            (AdicCompletion (maximalIdeal (Localization.AtPrime i0.1))
              (Localization.AtPrime i0.1))
            B0
            (Eπ z)) := by
          simpa [E0] using
            (ringEquivTransProdCongr_fst
              Eπ
              (finiteSubalgebraPiCompletionDistinguishedCoordRingEquiv
                (R := R) (q := q) A r hrq haway)
              (RingEquiv.refl B0)
              z)
    _ =
        finiteSubalgebraPiCompletionDistinguishedCoordRingEquiv
          (R := R) (q := q) A r hrq haway
          ((finiteSubalgebraPiCompletionRingEquiv (R := R) (q := q) A hAfin) z i0) := by
          rw [ringEquivProdOfPiSplitAt_fst]
    _ =
        finiteSubalgebraPiCompletionCoordHom
          (R := R) (q := q) A r hAfin hrq haway z := by
          rfl
    _ = completedTensorProductProjectionSubalgebra q A z := by
          exact
            finiteSubalgebraPiCompletionCoord
              (R := R) (q := q) A r hAfin hrq haway z

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 3: the finite away model already splits off the distinguished
completed local factor, with first projection equal to the finite-side canonical tensor map. -/
private theorem finiteSubalgebraCanonicalProjectionSplit
    (A : Subalgebra R S) (r : A) (hAfin : Module.Finite R A)
    (hrq : (r : S) ∉ q)
    (haway : Function.Bijective (Localization.awayMap A.val.toRingHom r)) :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R_qR^ B)
      (E : (R_qR^ ⊗[R] A) ≃ₐ[R_qR^] (S_q^ × B)),
      ∀ z : R_qR^ ⊗[R] A,
        (RingHom.fst S_q^ B) (E z) = completedTensorProductProjectionSubalgebra q A z := by
  rcases
      finiteSubalgebraPiCompletionSplit
        (R := R) (q := q) A r hAfin hrq haway with
    ⟨B, hB, E0, hE0⟩
  rcases
      algEquivOfRingEquivProdOfFirstProjectionExplicit
        (K := R_qR^)
        (π := completedTensorProductProjectionSubalgebra q A)
        E0 hE0 with
    ⟨hAlg, E, rfl⟩
  -- Proof comment: the repaired ring product split already has the correct first projection, so
  -- the generic upgrade package turns it into an `R_qR^`-algebra product split verbatim.
  exact ⟨B, hB, hAlg, E, hE0⟩

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 3: the finite-side quotient by `1 - e` used to isolate the
distinguished factor of `R_qR^ ⊗[R] A`. -/
private abbrev subalgebraIdempotentQuotient
    (A : Subalgebra R S) (e : R_qR^ ⊗[R] A) :=
  (R_qR^ ⊗[R] A) ⧸ Ideal.span ({1 - e} : Set (R_qR^ ⊗[R] A))

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 3: the canonical quotient map onto the finite-side idempotent
quotient. -/
private noncomputable def subalgebraIdempotentQuotientMk
    (A : Subalgebra R S) (e : R_qR^ ⊗[R] A) :
    (R_qR^ ⊗[R] A) →ₐ[R_qR^] subalgebraIdempotentQuotient (R := R) (q := q) A e :=
  Ideal.Quotient.mkₐ R_qR^ (Ideal.span ({1 - e} : Set (R_qR^ ⊗[R] A)))

/-- Helper for Chap10 Lemma 10 124 3: the finite-side idempotent quotient carries the canonical
`R_(q ∩ R)^∧`-algebra structure inherited from the source tensor product. -/
noncomputable local instance subalgebraIdempotentQuotientCommRing
    (A : Subalgebra R S) (e : R_qR^ ⊗[R] A) :
    CommRing (subalgebraIdempotentQuotient (R := R) (q := q) A e) := by
  delta subalgebraIdempotentQuotient
  infer_instance

/-- Helper for Chap10 Lemma 10 124 3: the finite-side idempotent quotient carries the canonical
`R_(q ∩ R)^∧`-algebra structure inherited from the source tensor product. -/
noncomputable local instance subalgebraIdempotentQuotientAlgebra
    (A : Subalgebra R S) (e : R_qR^ ⊗[R] A) :
    Algebra R_qR^ (subalgebraIdempotentQuotient (R := R) (q := q) A e) :=
  inferInstance

/-- Helper for Chap10 Lemma 10 124 3: the original base action factors through
`R → R_(q ∩ R)^∧ → subalgebraIdempotentQuotient q A e`. -/
noncomputable local instance subalgebraIdempotentQuotientIsScalarTower
    (A : Subalgebra R S) (e : R_qR^ ⊗[R] A) :
    IsScalarTower R R_qR^ (subalgebraIdempotentQuotient (R := R) (q := q) A e) :=
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    simp [subalgebraIdempotentQuotient]

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 3: the ambient quotient by the image of `1 - e` inside
`R_qR^ ⊗[R] S`. -/
private abbrev ambientIdempotentImageQuotient
    (A : Subalgebra R S) (e : R_qR^ ⊗[R] A) :=
  (R_qR^ ⊗[R] S) ⧸
    Ideal.span ({1 - tensorProductMapOfSubalgebra q A e} : Set (R_qR^ ⊗[R] S))

/-- Helper for Chap10 Lemma 10 124 3: the ambient idempotent-image quotient is a commutative
ring. -/
noncomputable local instance ambientIdempotentImageQuotientCommRing
    (A : Subalgebra R S) (e : R_qR^ ⊗[R] A) :
    CommRing (ambientIdempotentImageQuotient (R := R) (q := q) A e) := by
  delta ambientIdempotentImageQuotient
  infer_instance

/-- Helper for Chap10 Lemma 10 124 3: the ambient idempotent-image quotient carries the canonical
`R_(q ∩ R)^∧`-algebra structure inherited from the source tensor product. -/
noncomputable local instance ambientIdempotentImageQuotientAlgebra
    (A : Subalgebra R S) (e : R_qR^ ⊗[R] A) :
    Algebra R_qR^ (ambientIdempotentImageQuotient (R := R) (q := q) A e) :=
  inferInstance

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 3: the canonical quotient map onto the ambient idempotent-image
quotient. -/
private noncomputable def ambientIdempotentImageQuotientMk
    (A : Subalgebra R S) (e : R_qR^ ⊗[R] A) :
    (R_qR^ ⊗[R] S) →ₐ[R_qR^] ambientIdempotentImageQuotient (R := R) (q := q) A e :=
  Ideal.Quotient.mkₐ R_qR^
    (Ideal.span ({1 - tensorProductMapOfSubalgebra q A e} : Set (R_qR^ ⊗[R] S)))

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 3: once the finite model is split with the canonical first
projection, the distinguished factor is the quotient by the complementary idempotent on
`R_qR^ ⊗[R] A`. -/
private theorem finiteSubalgebraCanonicalProjectionQuotientEquiv
    (A : Subalgebra R S) (r : A) (hAfin : Module.Finite R A)
    (hrq : (r : S) ∉ q)
    (haway : Function.Bijective (Localization.awayMap A.val.toRingHom r)) :
    ∃ e : R_qR^ ⊗[R] A,
      IsIdempotentElem e ∧
        ∃ first :
          subalgebraIdempotentQuotient (R := R) (q := q) A e ≃ₐ[R_qR^] S_q^,
          ∀ z : R_qR^ ⊗[R] A,
            first (subalgebraIdempotentQuotientMk (R := R) (q := q) A e z) =
              completedTensorProductProjectionSubalgebra q A z := by
  rcases
      finiteSubalgebraCanonicalProjectionSplit
        (R := R) (q := q) A r hAfin hrq haway with
    ⟨B, _, _, E, hE⟩
  -- Proof comment: once the finite side is split with the canonical first projection, the generic
  -- idempotent-quotient package identifies that first factor with the quotient by `1 - e`.
  exact
    idempotentQuotientEquivOfAlgEquivProd
      (K := R_qR^)
      E
      (completedTensorProductProjectionSubalgebra q A)
      hE

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 3: after adjoining the finite idempotent quotient, every
ambient quotient class comes from the finite quotient because the right tensor generator is
obtained by clearing a power of the distinguished denominator. -/
private theorem ambientIdempotentImageQuotientMap_surjective
    (A : Subalgebra R S) (r : A)
    (hrq : (r : S) ∉ q)
    (haway : Function.Bijective (Localization.awayMap A.val.toRingHom r))
    {e : R_qR^ ⊗[R] A}
    (first :
      subalgebraIdempotentQuotient (R := R) (q := q) A e ≃ₐ[R_qR^] S_q^)
    (hfirst :
      ∀ z : R_qR^ ⊗[R] A,
        first (subalgebraIdempotentQuotientMk (R := R) (q := q) A e z) =
          completedTensorProductProjectionSubalgebra q A z) :
    Function.Surjective
      (quotientMapOfIdempotentImage (tensorProductMapOfSubalgebra q A) e) := by
  letI : CommRing (subalgebraIdempotentQuotient (R := R) (q := q) A e) := inferInstance
  letI : CommRing (ambientIdempotentImageQuotient (R := R) (q := q) A e) := inferInstance
  letI : Monoid (subalgebraIdempotentQuotient (R := R) (q := q) A e) := inferInstance
  letI : Monoid (ambientIdempotentImageQuotient (R := R) (q := q) A e) := inferInstance
  let f :=
    quotientMapOfIdempotentImage (tensorProductMapOfSubalgebra q A) e
  have hunit_first :
      IsUnit
        (first
          (subalgebraIdempotentQuotientMk (R := R) (q := q) A e
            ((1 : R_qR^) ⊗ₜ[R] r))) := by
    -- Proof comment: the finite-side first projection sends the distinguished denominator to the
    -- canonical completed-local image, which is a unit because `r ∉ q`.
    simpa [hfirst ((1 : R_qR^) ⊗ₜ[R] r)] using
      (completedTensorProductProjectionSubalgebra_one_tmul_isUnit
        (q := q) A (a := r) hrq)
  have hunit_r :
      IsUnit
        (subalgebraIdempotentQuotientMk (R := R) (q := q) A e
          ((1 : R_qR^) ⊗ₜ[R] r)) := by
    -- Proof comment: transport the unit back through the finite quotient equivalence.
    simpa using hunit_first.map first.symm.toRingHom
  have hright :
      ∀ s : S,
        ∃ y : subalgebraIdempotentQuotient (R := R) (q := q) A e,
          f y =
            ambientIdempotentImageQuotientMk (R := R) (q := q) A e
              ((1 : R_qR^) ⊗ₜ[R] s) := by
    intro s
    obtain ⟨a, n, ha⟩ := (Localization.awayMap_surjective_iff).mp haway.2 s
    let u : Units (subalgebraIdempotentQuotient (R := R) (q := q) A e) :=
      hunit_r.unit
    let v : Units (ambientIdempotentImageQuotient (R := R) (q := q) A e) :=
      Units.map f.toMonoidHom u
    have hmap_r :
        f (subalgebraIdempotentQuotientMk (R := R) (q := q) A e
            ((1 : R_qR^) ⊗ₜ[R] r)) =
          ambientIdempotentImageQuotientMk (R := R) (q := q) A e
            ((1 : R_qR^) ⊗ₜ[R] ((r : S))) := by
      -- Proof comment: the quotient map acts on representatives by the ambient tensor-inclusion.
      rw [quotientMapOfIdempotentImage_mk]
      simp [subalgebraIdempotentQuotientMk, ambientIdempotentImageQuotientMk,
        tensorProductMapOfSubalgebra_denominator]
    have hv :
        ((v : Units (ambientIdempotentImageQuotient (R := R) (q := q) A e)) :
            ambientIdempotentImageQuotient (R := R) (q := q) A e) =
          ambientIdempotentImageQuotientMk (R := R) (q := q) A e
            ((1 : R_qR^) ⊗ₜ[R] ((r : S))) := by
      -- Proof comment: the mapped unit is exactly the ambient class of the distinguished
      -- denominator.
      change f (↑u) =
        ambientIdempotentImageQuotientMk (R := R) (q := q) A e
          ((1 : R_qR^) ⊗ₜ[R] ((r : S)))
      simpa [u] using hmap_r
    have hmap_a :
        f (subalgebraIdempotentQuotientMk (R := R) (q := q) A e
            ((1 : R_qR^) ⊗ₜ[R] a)) =
          ambientIdempotentImageQuotientMk (R := R) (q := q) A e
            ((1 : R_qR^) ⊗ₜ[R] ((a : S))) := by
      -- Proof comment: finite-side generators coming from `A` map to the matching ambient
      -- tensor generator.
      rw [quotientMapOfIdempotentImage_mk]
      simp [subalgebraIdempotentQuotientMk, ambientIdempotentImageQuotientMk,
        tensorProductMapOfSubalgebra_tmul]
    have ha_tensor :
        ambientIdempotentImageQuotientMk (R := R) (q := q) A e
            ((1 : R_qR^) ⊗ₜ[R] ((a : S))) =
          (ambientIdempotentImageQuotientMk (R := R) (q := q) A e
              ((1 : R_qR^) ⊗ₜ[R] ((r : S)))) ^ n *
            ambientIdempotentImageQuotientMk (R := R) (q := q) A e
              ((1 : R_qR^) ⊗ₜ[R] s) := by
      -- Proof comment: the away-surjectivity relation `r^n * s = a` becomes a tensor identity
      -- after placing everything in the ambient quotient.
      apply congrArg (ambientIdempotentImageQuotientMk (R := R) (q := q) A e)
      calc
        ((1 : R_qR^) ⊗ₜ[R] ((a : S))) =
            ((1 : R_qR^) ⊗ₜ[R] (((r : S) ^ n) * s)) := by
              simpa [ha]
        _ = (((1 : R_qR^) ⊗ₜ[R] ((r : S) ^ n)) : R_qR^ ⊗[R] S) *
              ((1 : R_qR^) ⊗ₜ[R] s) := by
                rw [Algebra.TensorProduct.tmul_mul_tmul]
                simp
        _ = ((((1 : R_qR^) ⊗ₜ[R] ((r : S))) : R_qR^ ⊗[R] S) ^ n) *
              ((1 : R_qR^) ⊗ₜ[R] s) := by
                simp
    refine ⟨(↑(u⁻¹ ^ n) :
        subalgebraIdempotentQuotient (R := R) (q := q) A e) *
      subalgebraIdempotentQuotientMk (R := R) (q := q) A e
        ((1 : R_qR^) ⊗ₜ[R] a), ?_⟩
    -- Proof comment: invert the ambient denominator using the unit class of `1 ⊗ₜ[R] r`.
    calc
      f
          ((↑(u⁻¹ ^ n) :
              subalgebraIdempotentQuotient (R := R) (q := q) A e) *
            subalgebraIdempotentQuotientMk (R := R) (q := q) A e
              ((1 : R_qR^) ⊗ₜ[R] a)) =
        (↑(v⁻¹ ^ n) :
            ambientIdempotentImageQuotient (R := R) (q := q) A e) *
          ambientIdempotentImageQuotientMk (R := R) (q := q) A e
            ((1 : R_qR^) ⊗ₜ[R] ((a : S))) := by
              rw [map_mul, hmap_a]
              simp [v]
      _ =
        (↑(v⁻¹ ^ n) :
            ambientIdempotentImageQuotient (R := R) (q := q) A e) *
          ((ambientIdempotentImageQuotientMk (R := R) (q := q) A e
              ((1 : R_qR^) ⊗ₜ[R] ((r : S)))) ^ n *
            ambientIdempotentImageQuotientMk (R := R) (q := q) A e
              ((1 : R_qR^) ⊗ₜ[R] s)) := by
              rw [ha_tensor]
      _ =
        ambientIdempotentImageQuotientMk (R := R) (q := q) A e
          ((1 : R_qR^) ⊗ₜ[R] s) := by
            rw [hv]
            simp [mul_assoc]
  intro z
  refine Quotient.inductionOn' z ?_
  intro x
  -- Proof comment: every ambient quotient class is represented by an ambient tensor, and tensor
  -- induction reduces that representative to left and right generators.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · refine ⟨0, ?_⟩
    simp [f, ambientIdempotentImageQuotientMk]
  · intro x s
    obtain ⟨y, hy⟩ := hright s
    have hleft :
        f (subalgebraIdempotentQuotientMk (R := R) (q := q) A e
            (x ⊗ₜ[R] (1 : A))) =
          ambientIdempotentImageQuotientMk (R := R) (q := q) A e
            (x ⊗ₜ[R] (1 : S)) := by
      -- Proof comment: the left tensor generator is already in the finite subalgebra.
      rw [quotientMapOfIdempotentImage_mk]
      simp [subalgebraIdempotentQuotientMk, ambientIdempotentImageQuotientMk,
        tensorProductMapOfSubalgebra_tmul]
    refine ⟨subalgebraIdempotentQuotientMk (R := R) (q := q) A e
        (x ⊗ₜ[R] (1 : A)) * y, ?_⟩
    calc
      f
          (subalgebraIdempotentQuotientMk (R := R) (q := q) A e
              (x ⊗ₜ[R] (1 : A)) * y) =
        ambientIdempotentImageQuotientMk (R := R) (q := q) A e
            (x ⊗ₜ[R] (1 : S)) *
          ambientIdempotentImageQuotientMk (R := R) (q := q) A e
            ((1 : R_qR^) ⊗ₜ[R] s) := by
              rw [map_mul, hleft, hy]
      _ =
        ambientIdempotentImageQuotientMk (R := R) (q := q) A e
          (((x ⊗ₜ[R] (1 : S)) : R_qR^ ⊗[R] S) * ((1 : R_qR^) ⊗ₜ[R] s)) := by
            rw [← map_mul]
      _ =
        ambientIdempotentImageQuotientMk (R := R) (q := q) A e
          (x ⊗ₜ[R] s) := by
            congr 1
            rw [Algebra.TensorProduct.tmul_mul_tmul]
            simp
  · intro x y hx hy
    rcases hx with ⟨zx, hzx⟩
    rcases hy with ⟨zy, hzy⟩
    refine ⟨zx + zy, ?_⟩
    rw [map_add, hzx, hzy, map_add]

omit [Algebra.FiniteType R S] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 124 3: the two structure maps used to lift
`R_(q ∩ R)^∧ ⊗[R] S` into the finite idempotent quotient commute because the target quotient ring
is commutative. -/
private theorem subalgebraTensorLiftToIdempotentQuotient_commute
    (A : Subalgebra R S)
    {e : R_qR^ ⊗[R] A}
    (ψS :
      S →ₐ[R]
        subalgebraIdempotentQuotient (R := R) (q := q) A e) :
    ∀ x : R_qR^, ∀ s : S,
      Commute
        ((Algebra.ofId R_qR^
          (subalgebraIdempotentQuotient (R := R) (q := q) A e)) x)
        (ψS s) := by
  intro x s
  -- Proof comment: every pair of elements commutes in the commutative quotient ring.
  exact Commute.all _ _

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 3: once the finite quotient projection agrees with the
canonical maps on the two tensor generators, it agrees with
`completedTensorProductProjection_q` on all tensors. -/
private noncomputable def subalgebraTensorLiftToIdempotentQuotient
    (A : Subalgebra R S)
    {e : R_qR^ ⊗[R] A}
    (ψS :
      S →ₐ[R]
        subalgebraIdempotentQuotient (R := R) (q := q) A e) :
    (R_qR^ ⊗[R] S) →ₐ[R_qR^]
      subalgebraIdempotentQuotient (R := R) (q := q) A e :=
  Algebra.TensorProduct.lift
    (Algebra.ofId R_qR^
      (subalgebraIdempotentQuotient (R := R) (q := q) A e))
    ψS
    (subalgebraTensorLiftToIdempotentQuotient_commute
      (R := R) (q := q) A ψS)

omit [Algebra.FiniteType R S] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 124 3: an `R_(q ∩ R)^∧`-algebra homomorphism out of
`R_(q ∩ R)^∧ ⊗[R] S` is determined by its values on the generators `x ⊗ₜ[R] 1` and
`1 ⊗ₜ[R] s`. -/
private theorem tensorProductAlgHom_eq_of_generators
    {T : Type*} [CommRing T] [Algebra R_qR^ T]
    (f g : (R_qR^ ⊗[R] S) →ₐ[R_qR^] T)
    (hleft : ∀ x : R_qR^, f (x ⊗ₜ[R] (1 : S)) = g (x ⊗ₜ[R] (1 : S)))
    (hright : ∀ s : S, f ((1 : R_qR^) ⊗ₜ[R] s) = g ((1 : R_qR^) ⊗ₜ[R] s)) :
    f = g := by
  ext z
  -- Proof comment: the underlying ring homomorphisms are determined by the two tensor generators,
  -- so the algebra homomorphisms agree pointwise once those generator values match.
  have hfg : f.toRingHom = g.toRingHom := by
    apply Algebra.TensorProduct.ringHom_ext
    · apply RingHom.ext
      intro x
      -- Proof comment: the left structure map is evaluation at `x ⊗ₜ[R] 1`.
      simpa [RingHom.comp_apply] using hleft x
    · apply RingHom.ext
      intro s
      -- Proof comment: the right structure map is evaluation at `1 ⊗ₜ[R] s`.
      simpa [RingHom.comp_apply, Algebra.TensorProduct.includeRight_apply] using hright s
  exact DFunLike.congr_fun hfg z

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 3: on a pure tensor, the ambient lift to the finite
idempotent quotient followed by the distinguished factor map agrees with the canonical completed
tensor-product projection. -/
private theorem firstSubalgebraTensorLiftToIdempotentQuotient_tmul
    (A : Subalgebra R S)
    {e : R_qR^ ⊗[R] A}
    (first :
      subalgebraIdempotentQuotient (R := R) (q := q) A e ≃ₐ[R_qR^] S_q^)
    (ψS :
      S →ₐ[R]
        subalgebraIdempotentQuotient (R := R) (q := q) A e)
    (hψS_proj :
      ∀ s : S, first (ψS s) = algebraMap S S_q^ s)
    (x : R_qR^) (s : S) :
    first
        (subalgebraTensorLiftToIdempotentQuotient (R := R) (q := q) A ψS
          (x ⊗ₜ[R] s)) =
      completedTensorProductProjection_q (x ⊗ₜ[R] s) := by
  -- Proof comment: evaluate both tensor-product lifts on a pure tensor and compare the two
  -- structure maps separately.
  have hleft :
      first ((Algebra.ofId R_qR^ _) x) = algebraMap R_qR^ S_q^ x := by
    simp using first.commutes x
  calc
    first
        (subalgebraTensorLiftToIdempotentQuotient (R := R) (q := q) A ψS
          (x ⊗ₜ[R] s)) =
      first ((Algebra.ofId R_qR^ _) x * ψS s) := by
        rw [subalgebraTensorLiftToIdempotentQuotient]
        simpa using
          Algebra.TensorProduct.lift_tmul
            (Algebra.ofId R_qR^
              (subalgebraIdempotentQuotient (R := R) (q := q) A e))
            ψS
            (subalgebraTensorLiftToIdempotentQuotient_commute
              (R := R) (q := q) A ψS)
            x s
    _ = first ((Algebra.ofId R_qR^ _) x) * first (ψS s) := by
        rw [map_mul]
    _ = algebraMap R_qR^ S_q^ x * algebraMap S S_q^ s := by
        rw [hleft, hψS_proj s]
    _ = completedTensorProductProjection_q (x ⊗ₜ[R] s) := by
        symm
        simp [completedTensorProductProjection]

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 3: once the finite quotient projection agrees with the
canonical maps on the two tensor generators, it agrees with
`completedTensorProductProjection_q` on all tensors. -/
private theorem firstCompTensorProductLift_eq_completedTensorProductProjection
    (A : Subalgebra R S)
    {e : R_qR^ ⊗[R] A}
    (first :
      subalgebraIdempotentQuotient (R := R) (q := q) A e ≃ₐ[R_qR^] S_q^)
    (_hfirst :
      ∀ z : R_qR^ ⊗[R] A,
        first (subalgebraIdempotentQuotientMk (R := R) (q := q) A e z) =
          completedTensorProductProjectionSubalgebra q A z)
    (_mkT :
      (R_qR^ ⊗[R] A) →ₐ[R_qR^]
        subalgebraIdempotentQuotient (R := R) (q := q) A e)
    (ψS :
      S →ₐ[R]
        subalgebraIdempotentQuotient (R := R) (q := q) A e)
    (hψS_proj :
      ∀ s : S, first (ψS s) = algebraMap S S_q^ s)
    (_hψQ_comp :
      (subalgebraTensorLiftToIdempotentQuotient (R := R) (q := q) A ψS).comp
          (tensorProductMapOfSubalgebra q A) = _mkT) :
    ∀ z : R_qR^ ⊗[R] S,
      first
          (subalgebraTensorLiftToIdempotentQuotient (R := R) (q := q) A ψS z) =
        completedTensorProductProjection_q z := by
  -- Route correction: the pure-tensor normalization is now cached in
  -- `firstSubalgebraTensorLiftToIdempotentQuotient_tmul`; the remaining step is to compare the
  -- two ambient maps at the `AlgHom` level, so the theorem does not reopen any `toRingHom`
  -- normalization on the fixed composite map.
  let f : R_qR^ ⊗[R] S →ₐ[R_qR^] S_q^ :=
    first.toAlgHom.comp (subalgebraTensorLiftToIdempotentQuotient (R := R) (q := q) A ψS)
  let g : R_qR^ ⊗[R] S →ₐ[R_qR^] S_q^ := completedTensorProductProjection_q
  have hfg : f = g := by
    -- Proof comment: the new generator-ext wrapper consumes the cached pure-tensor formulas
    -- directly and keeps the comparison in the canonical `AlgHom` spelling.
    apply tensorProductAlgHom_eq_of_generators (R := R) (q := q)
    · intro x
      simpa [f, g] using
        (firstSubalgebraTensorLiftToIdempotentQuotient_tmul
          (R := R) (q := q) A first ψS hψS_proj x (1 : S))
    · intro s
      simpa [f, g] using
        (firstSubalgebraTensorLiftToIdempotentQuotient_tmul
          (R := R) (q := q) A first ψS hψS_proj (1 : R_qR^) s)
  intro z
  exact DFunLike.congr_fun hfg z

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 3: if the lifted ambient map and the quotient map agree on the
two tensor generators of `R_(q ∩ R)^∧ ⊗[R] A`, then they agree on the whole finite tensor
product. -/
private theorem subalgebraTensorLift_comp_tensorProductMap_eq_quotientMk
    (A : Subalgebra R S)
    {e : R_qR^ ⊗[R] A}
    (first :
      subalgebraIdempotentQuotient (R := R) (q := q) A e ≃ₐ[R_qR^] S_q^)
    (hfirst :
      ∀ z : R_qR^ ⊗[R] A,
        first (subalgebraIdempotentQuotientMk (R := R) (q := q) A e z) =
          completedTensorProductProjectionSubalgebra q A z)
    (ψS :
      S →ₐ[R]
        subalgebraIdempotentQuotient (R := R) (q := q) A e)
    (hψS_proj :
      ∀ s : S, first (ψS s) = algebraMap S S_q^ s) :
    (subalgebraTensorLiftToIdempotentQuotient (R := R) (q := q) A ψS).comp
        (tensorProductMapOfSubalgebra q A) =
      subalgebraIdempotentQuotientMk (R := R) (q := q) A e := by
  letI : Algebra R_qR^ (subalgebraIdempotentQuotient (R := R) (q := q) A e) := inferInstance
  let f : (R_qR^ ⊗[R] A) →ₐ[R_qR^] S_q^ :=
    first.toAlgHom.comp
      ((subalgebraTensorLiftToIdempotentQuotient (R := R) (q := q) A ψS).comp
        (tensorProductMapOfSubalgebra q A))
  let g : (R_qR^ ⊗[R] A) →ₐ[R_qR^] S_q^ :=
    first.toAlgHom.comp (subalgebraIdempotentQuotientMk (R := R) (q := q) A e)
  have hfg : f.toRingHom = g.toRingHom := by
    apply tensorProductRingHom_eq_of_generators (R := R) (S := S) (q := q) A
    · intro x
      calc
        f.toRingHom (x ⊗ₜ[R] (1 : A)) =
            completedTensorProductProjection_q (x ⊗ₜ[R] (1 : S)) := by
              simp [f, AlgHom.comp_apply, RingHom.comp_apply, tensorProductMapOfSubalgebra_tmul,
                firstSubalgebraTensorLiftToIdempotentQuotient_tmul]
        _ =
            completedTensorProductProjectionSubalgebra q A (x ⊗ₜ[R] (1 : A)) := by
              rw [completedTensorProductProjection_tmul_one]
              exact (completedTensorProductProjectionSubalgebra_tmul_one q A x).symm
        _ = g.toRingHom (x ⊗ₜ[R] (1 : A)) := by
              simp [g, AlgHom.comp_apply, RingHom.comp_apply, hfirst]
    · intro a
      calc
        f.toRingHom ((1 : R_qR^) ⊗ₜ[R] a) =
            completedTensorProductProjection_q ((1 : R_qR^) ⊗ₜ[R] (a : S)) := by
              simp [f, AlgHom.comp_apply, RingHom.comp_apply, tensorProductMapOfSubalgebra_tmul,
                firstSubalgebraTensorLiftToIdempotentQuotient_tmul]
        _ = completedTensorProductProjectionSubalgebra q A ((1 : R_qR^) ⊗ₜ[R] a) := by
            rw [completedTensorProductProjection_one_tmul]
            exact (completedTensorProductProjectionSubalgebra_one_tmul q A a).symm
        _ = g.toRingHom ((1 : R_qR^) ⊗ₜ[R] a) := by
              simp [g, AlgHom.comp_apply, RingHom.comp_apply, hfirst]
  ext z
  apply first.injective
  exact DFunLike.congr_fun hfg z

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 3: after descending the finite quotient map across the ambient
idempotent-image quotient, the resulting projection computes on quotient classes as the canonical
map `completedTensorProductProjection_q`. -/
private theorem ambientIdempotentImageQuotientProjection_mk
    (A : Subalgebra R S)
    {e : R_qR^ ⊗[R] A}
    (first :
      subalgebraIdempotentQuotient (R := R) (q := q) A e ≃ₐ[R_qR^] S_q^)
    (πQ :
      (R_qR^ ⊗[R] S) →ₐ[R_qR^]
        subalgebraIdempotentQuotient (R := R) (q := q) A e)
    (hπQ_proj :
      ∀ z : R_qR^ ⊗[R] S, first (πQ z) = completedTensorProductProjection_q z)
    (hπe : πQ (tensorProductMapOfSubalgebra q A e) = 1) :
    ∀ z : R_qR^ ⊗[R] S,
      (first.toAlgHom.comp
          (quotientLiftOfIdempotentImageToOne
            (tensorProductMapOfSubalgebra q A) e πQ hπe))
        (ambientIdempotentImageQuotientMk (R := R) (q := q) A e z) =
        completedTensorProductProjection_q z := by
  letI : Algebra R_qR^ (subalgebraIdempotentQuotient (R := R) (q := q) A e) := inferInstance
  letI : Algebra R_qR^ (ambientIdempotentImageQuotient (R := R) (q := q) A e) := inferInstance
  intro z
  -- Proof comment: the quotient lift evaluates on representatives by `πQ`, so the claimed
  -- formula reduces immediately to the already-known identity `first ∘ πQ`.
  calc
    (first.toAlgHom.comp
        (quotientLiftOfIdempotentImageToOne
          (tensorProductMapOfSubalgebra q A) e πQ hπe))
        (ambientIdempotentImageQuotientMk (R := R) (q := q) A e z) =
      first (πQ z) := by
        rw [AlgHom.comp_apply, ambientIdempotentImageQuotientMk,
          quotientLiftOfIdempotentImageToOne_mk]
    _ = completedTensorProductProjection_q z := hπQ_proj z

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 3: once the descended ambient quotient map agrees with the
finite quotient equivalence on the image of the finite quotient, it is bijective. -/
private theorem ambientIdempotentImageQuotientProjection_bijective
    (A : Subalgebra R S) (r : A)
    (hrq : (r : S) ∉ q)
    (haway : Function.Bijective (Localization.awayMap A.val.toRingHom r))
    {e : R_qR^ ⊗[R] A}
    (first :
      subalgebraIdempotentQuotient (R := R) (q := q) A e ≃ₐ[R_qR^] S_q^)
    (hfirst :
      ∀ z : R_qR^ ⊗[R] A,
        first (subalgebraIdempotentQuotientMk (R := R) (q := q) A e z) =
          completedTensorProductProjectionSubalgebra q A z)
    (ambientFirst :
      ambientIdempotentImageQuotient (R := R) (q := q) A e →ₐ[R_qR^] S_q^)
    (hambientFirst_qmap :
      ∀ y : subalgebraIdempotentQuotient (R := R) (q := q) A e,
        ambientFirst
            ((quotientMapOfIdempotentImage (tensorProductMapOfSubalgebra q A) e) y) =
          first y) :
    Function.Bijective ambientFirst := by
  have hqmap_surj :
      Function.Surjective
        (quotientMapOfIdempotentImage (tensorProductMapOfSubalgebra q A) e) := by
    -- Proof comment: denominator clearing moves every ambient quotient class into the image of
    -- the finite quotient.
    simpa using
      ambientIdempotentImageQuotientMap_surjective
        (R := R) (q := q) A r hrq haway first hfirst
  refine ⟨?_, ?_⟩
  · intro x y hxy
    obtain ⟨x0, rfl⟩ := hqmap_surj x
    obtain ⟨y0, rfl⟩ := hqmap_surj y
    -- Proof comment: after replacing ambient classes by finite quotient representatives, the
    -- claimed equality is transported to `S_q^` through `first`, which is injective.
    have hxy0 : first x0 = first y0 := by
      rw [← hambientFirst_qmap x0, ← hambientFirst_qmap y0]
      exact hxy
    have : x0 = y0 := first.injective hxy0
    simp [this]
  · intro z
    -- Proof comment: surjectivity is immediate from the finite quotient representative
    -- `first.symm z`.
    refine ⟨
      (quotientMapOfIdempotentImage (tensorProductMapOfSubalgebra q A) e) (first.symm z),
      ?_⟩
    calc
      ambientFirst
          ((quotientMapOfIdempotentImage (tensorProductMapOfSubalgebra q A) e) (first.symm z)) =
        first (first.symm z) := by
          exact hambientFirst_qmap (first.symm z)
      _ = z := by
          exact first.apply_symm_apply z

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 3: the descended ambient quotient map agrees with the finite
quotient equivalence on the image of the finite quotient. -/
private theorem ambientIdempotentImageQuotientProjection_qmap
    (A : Subalgebra R S)
    {e : R_qR^ ⊗[R] A}
    (first :
      subalgebraIdempotentQuotient (R := R) (q := q) A e ≃ₐ[R_qR^] S_q^)
    (πQ :
      (R_qR^ ⊗[R] S) →ₐ[R_qR^]
        subalgebraIdempotentQuotient (R := R) (q := q) A e)
    (hπe : πQ (tensorProductMapOfSubalgebra q A e) = 1)
    (hcomp :
      πQ.comp (tensorProductMapOfSubalgebra q A) =
        subalgebraIdempotentQuotientMk (R := R) (q := q) A e) :
    ∀ y : subalgebraIdempotentQuotient (R := R) (q := q) A e,
      (first.toAlgHom.comp
          (quotientLiftOfIdempotentImageToOne
            (tensorProductMapOfSubalgebra q A) e πQ hπe))
        ((quotientMapOfIdempotentImage (tensorProductMapOfSubalgebra q A) e) y) =
          first y := by
  letI : Algebra R_qR^ (subalgebraIdempotentQuotient (R := R) (q := q) A e) := inferInstance
  letI : Algebra R_qR^ (ambientIdempotentImageQuotient (R := R) (q := q) A e) := inferInstance
  intro y
  -- Proof comment: the quotient lift is a left inverse to the quotient map, so composing with
  -- `first` recovers the original finite quotient coordinate.
  simpa [AlgHom.comp_apply] using
    congrArg first
      (DFunLike.congr_fun
        (quotientLiftOfIdempotentImageToOne_comp_quotientMap
          (tensorProductMapOfSubalgebra q A) e πQ hπe
          hcomp)
        y)

omit [Algebra.FiniteType R S] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 124 3: a bijective ambient quotient map with the canonical class
formula yields the required product splitting of `R_(q ∩ R)^∧ ⊗[R] S`. -/
private theorem ambientIdempotentImageProductSplit
    (A : Subalgebra R S)
    {e : R_qR^ ⊗[R] A}
    (he : IsIdempotentElem e)
    (ambientFirst :
      ambientIdempotentImageQuotient (R := R) (q := q) A e →ₐ[R_qR^] S_q^)
    (hambientFirst_mk :
      ∀ z : R_qR^ ⊗[R] S,
        ambientFirst (ambientIdempotentImageQuotientMk (R := R) (q := q) A e z) =
          completedTensorProductProjection_q z)
    (hbij : Function.Bijective ambientFirst) :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R_qR^ B)
      (E : (R_qR^ ⊗[R] S) ≃ₐ[R_qR^] (S_q^ × B)),
      ∀ z : R_qR^ ⊗[R] S,
        (RingHom.fst S_q^ B) (E z) = completedTensorProductProjection_q z := by
  let ambientFirstEquiv :
      ambientIdempotentImageQuotient (R := R) (q := q) A e ≃ₐ[R_qR^] S_q^ :=
    AlgEquiv.ofBijective ambientFirst hbij
  have himageIdem :
      IsIdempotentElem (tensorProductMapOfSubalgebra q A e) := by
    -- Proof comment: transport the finite-side idempotent across the ambient tensor inclusion.
    exact algHom_map_isIdempotentElem (tensorProductMapOfSubalgebra q A) he
  have hambientFirst_quot :
      ∀ z : R_qR^ ⊗[R] S,
        ambientFirstEquiv
            ((Ideal.Quotient.mk
                (Ideal.span
                  ({1 - tensorProductMapOfSubalgebra q A e} :
                    Set (R_qR^ ⊗[R] S)))) z) =
          completedTensorProductProjection_q z := by
    intro z
    -- Proof comment: the ambient quotient abbreviation is definitionally the displayed quotient.
    simpa [ambientFirstEquiv, ambientIdempotentImageQuotientMk] using hambientFirst_mk z
  -- Proof comment: after upgrading the ambient quotient map to an equivalence, the generic
  -- idempotent-splitting theorem supplies the required product decomposition.
  exact
    algEquivProdOfIdempotentQuotientEquiv
      (K := R_qR^)
      (T := R_qR^ ⊗[R] S)
      (C := S_q^)
      (π := completedTensorProductProjection_q)
      himageIdem
      ambientFirstEquiv
      hambientFirst_quot

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 3: transporting the canonical map `S → S_q^` back through the
finite quotient equivalence still commutes with the base algebra map from `R`. -/
private theorem subalgebraIdempotentQuotientSymmCompAlgebraMap_commutes
    (A : Subalgebra R S)
    {e : R_qR^ ⊗[R] A}
    (first :
      subalgebraIdempotentQuotient (R := R) (q := q) A e ≃ₐ[R_qR^] S_q^)
    (x : R) :
    ((first.symm.toRingHom.comp (algebraMap S S_q^)) ((algebraMap R S) x)) =
      algebraMap R (subalgebraIdempotentQuotient (R := R) (q := q) A e) x := by
  letI : Algebra R_qR^ S_q^ := completedLocalRingAlgebra q
  letI : Algebra R_qR^ (subalgebraIdempotentQuotient (R := R) (q := q) A e) := inferInstance
  letI : SMul R_qR^ (subalgebraIdempotentQuotient (R := R) (q := q) A e) := Algebra.toSMul
  letI :
      IsScalarTower R R_qR^ (subalgebraIdempotentQuotient (R := R) (q := q) A e) :=
    subalgebraIdempotentQuotientIsScalarTower (R := R) (q := q) A e
  apply first.injective
  calc
    first ((first.symm.toRingHom.comp (algebraMap S S_q^)) ((algebraMap R S) x)) =
      algebraMap S S_q^ ((algebraMap R S) x) := by
        exact first.apply_symm_apply ((algebraMap S S_q^) ((algebraMap R S) x))
    _ = algebraMap R_qR^ S_q^ ((algebraMap R R_qR^) x) := by
        simpa using completedLocalRing_algebraMap_eq (R := R) (S := S) (q := q) x
    _ = first
          (algebraMap
            R_qR^
            (subalgebraIdempotentQuotient (R := R) (q := q) A e)
            ((algebraMap R R_qR^) x)) := by
              simpa using (first.commutes ((algebraMap R R_qR^) x)).symm
    _ = first (algebraMap R (subalgebraIdempotentQuotient (R := R) (q := q) A e) x) := by
          congr 1
          exact
            (IsScalarTower.algebraMap_eq
              R R_qR^ (subalgebraIdempotentQuotient (R := R) (q := q) A e) x).symm

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 3: descend the finite-side idempotent quotient across
`tensorProductMapOfSubalgebra q A` to recover the ambient canonical projection. -/
private theorem tensorProductMapOfSubalgebraCanonicalProjectionTransport
    (A : Subalgebra R S) (r : A) (hAfin : Module.Finite R A)
    (hrq : (r : S) ∉ q)
    (haway : Function.Bijective (Localization.awayMap A.val.toRingHom r)) :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R_qR^ B)
      (E : (R_qR^ ⊗[R] S) ≃ₐ[R_qR^] (S_q^ × B)),
      ∀ z : R_qR^ ⊗[R] S,
        (RingHom.fst S_q^ B) (E z) = completedTensorProductProjection_q z := by
  rcases
      finiteSubalgebraCanonicalProjectionQuotientEquiv
        (R := R) (q := q) A r hAfin hrq haway with
    ⟨e, he, first, hfirst⟩
  letI : Algebra R_qR^ S_q^ := completedLocalRingAlgebra q
  letI : Algebra R_qR^ (subalgebraIdempotentQuotient (R := R) (q := q) A e) := inferInstance
  letI : SMul R_qR^ (subalgebraIdempotentQuotient (R := R) (q := q) A e) := Algebra.toSMul
  letI :
      IsScalarTower R R_qR^ (subalgebraIdempotentQuotient (R := R) (q := q) A e) :=
    subalgebraIdempotentQuotientIsScalarTower (R := R) (q := q) A e
  let ψS :
      S →ₐ[R] subalgebraIdempotentQuotient (R := R) (q := q) A e :=
    { toRingHom := first.symm.toRingHom.comp (algebraMap S S_q^)
      commutes' := subalgebraIdempotentQuotientSymmCompAlgebraMap_commutes
        (R := R) (q := q) A first }
  have hψS_proj : ∀ s : S, first (ψS s) = algebraMap S S_q^ s := by
    intro s
    -- Proof comment: `ψS` is defined by transporting the canonical map `S → S_q^` back through
    -- the finite quotient equivalence.
    change first (((first.symm.toRingHom.comp (algebraMap S S_q^)) s)) = algebraMap S S_q^ s
    exact first.apply_symm_apply ((algebraMap S S_q^) s)
  let πQ :
      (R_qR^ ⊗[R] S) →ₐ[R_qR^]
        subalgebraIdempotentQuotient (R := R) (q := q) A e :=
    subalgebraTensorLiftToIdempotentQuotient (R := R) (q := q) A ψS
  have hcomp :
      πQ.comp (tensorProductMapOfSubalgebra q A) =
        subalgebraIdempotentQuotientMk (R := R) (q := q) A e := by
    -- Proof comment: the lifted ambient map and the finite quotient map agree on the tensor
    -- generators, so they agree on the whole finite tensor product.
    simpa [πQ] using
      subalgebraTensorLift_comp_tensorProductMap_eq_quotientMk
        (R := R) (q := q) A first hfirst ψS hψS_proj
  have hπQ_proj :
      ∀ z : R_qR^ ⊗[R] S, first (πQ z) = completedTensorProductProjection_q z := by
    -- Proof comment: after the finite-side restriction is identified with the quotient map, the
    -- global tensor map is the canonical completed tensor-product projection.
    simpa [πQ] using
      firstCompTensorProductLift_eq_completedTensorProductProjection
        (R := R) (q := q) A first hfirst
        (subalgebraIdempotentQuotientMk (R := R) (q := q) A e)
        ψS hψS_proj hcomp
  have hπe : πQ (tensorProductMapOfSubalgebra q A e) = 1 := by
    -- Proof comment: the restriction formula on the finite quotient forces the chosen
    -- idempotent image to become `1`.
    exact
      algHom_image_eq_one_of_comp_quotient_mk
        (tensorProductMapOfSubalgebra q A) e πQ hcomp
  let ambientFirst :
      ambientIdempotentImageQuotient (R := R) (q := q) A e →ₐ[R_qR^] S_q^ :=
    first.toAlgHom.comp
      (quotientLiftOfIdempotentImageToOne
        (tensorProductMapOfSubalgebra q A) e πQ hπe)
  have hambientFirst_mk :
      ∀ z : R_qR^ ⊗[R] S,
        ambientFirst (ambientIdempotentImageQuotientMk (R := R) (q := q) A e z) =
          completedTensorProductProjection_q z := by
    -- Proof comment: evaluate the descended ambient map on quotient classes and reuse the
    -- previously proved formula for `first ∘ πQ`.
    simpa [ambientFirst] using
      ambientIdempotentImageQuotientProjection_mk
        (R := R) (q := q) A first πQ hπQ_proj hπe
  have hambientFirst_qmap :
      ∀ y : subalgebraIdempotentQuotient (R := R) (q := q) A e,
        ambientFirst
            ((quotientMapOfIdempotentImage (tensorProductMapOfSubalgebra q A) e) y) =
          first y := by
    -- Proof comment: the ambient quotient map is still the finite quotient equivalence on the
    -- image of the finite quotient inside the ambient quotient.
    simpa [ambientFirst] using
      ambientIdempotentImageQuotientProjection_qmap
        (R := R) (q := q) A first πQ hπe hcomp
  have hbij : Function.Bijective ambientFirst := by
    -- Proof comment: bijectivity follows from the existing denominator-clearing surjectivity
    -- theorem once the ambient quotient map has the expected finite-image formula.
    exact
      ambientIdempotentImageQuotientProjection_bijective
        (R := R) (q := q) A r hrq haway first hfirst ambientFirst hambientFirst_qmap
  -- Proof comment: the final assembly is now delegated to the dedicated ambient quotient helper,
  -- so this wrapper only packages the finite quotient data and its transport formulas.
  exact
    ambientIdempotentImageProductSplit
      (R := R) (q := q) A he ambientFirst hambientFirst_mk hbij

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 3: the finite-away model gives a product splitting whose
first coordinate is the canonical completed tensor-product projection. -/
private theorem finiteAwayCompletionTensorProductCanonicalProjectionSplit
    (A : Subalgebra R S) (r : A) (hAfin : Module.Finite R A)
    (hrq : (r : S) ∉ q)
    (haway : Function.Bijective (Localization.awayMap A.val.toRingHom r)) :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R_qR^ B)
      (E : (R_qR^ ⊗[R] S) ≃ₐ[R_qR^] (S_q^ × B)),
      ∀ z : R_qR^ ⊗[R] S, (RingHom.fst S_q^ B) (E z) = completedTensorProductProjection_q z :=
        by
  -- Proof comment: this is just the ambient transport package once the finite-away quotient
  -- descent has been established.
  exact
    tensorProductMapOfSubalgebraCanonicalProjectionTransport
      (R := R) (q := q) A r hAfin hrq haway

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 3: the finite-away Zariski-main model identifies the canonical
projection with the quotient by the complementary idempotent. -/
private theorem completedTensorProductProjection_quotientEquivOfFiniteAway
    (A : Subalgebra R S) (r : A) (hAfin : Module.Finite R A)
    (hrq : (r : S) ∉ q)
    (haway : Function.Bijective (Localization.awayMap A.val.toRingHom r)) :
    ∃ e : R_qR^ ⊗[R] S,
      IsIdempotentElem e ∧
        ∃ first :
          ((R_qR^ ⊗[R] S) ⧸
            Ideal.span ({1 - e} : Set (R_qR^ ⊗[R] S))) ≃ₐ[R_qR^] S_q^,
          ∀ z : R_qR^ ⊗[R] S,
            first ((Ideal.Quotient.mk
              (Ideal.span ({1 - e} : Set (R_qR^ ⊗[R] S)))) z) =
              completedTensorProductProjection_q z := by
  rcases
      finiteAwayCompletionTensorProductCanonicalProjectionSplit
        (R := R) (q := q) A r hAfin hrq haway with
    ⟨B, _, _, E, hfst⟩
  -- Convert the ambient product split into the quotient by the complementary idempotent.
  exact
    idempotentQuotientEquivOfAlgEquivProd
      (K := R_qR^)
      E
      completedTensorProductProjection_q
      hfst

variable [Algebra.QuasiFiniteAt R q]

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 3: once Zariski's main theorem provides a finite-away model,
the ambient canonical-projection split closes the target statement directly. -/
private theorem existsCompletionTensorProductAlgEquivOfFiniteAwayWitness
    (A : Subalgebra R S) (r : A) (hAfin : Module.Finite R A)
    (hrq : (r : S) ∉ q)
    (haway : Function.Bijective (Localization.awayMap A.val.toRingHom r)) :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R_qR^ B)
      (E : (R_qR^ ⊗[R] S) ≃ₐ[R_qR^] (S_q^ × B)),
      ∀ z : R_qR^ ⊗[R] S,
        (RingHom.fst S_q^ B) (E z) = completedTensorProductProjection q z := by
  -- Route correction: the terminal theorem is only a wrapper over the finite-away splitting. The
  -- substantial structural work is upstream in the `07N9`-based product comparison used there.
  -- Proof comment: reuse the ambient canonical-projection split verbatim and only unfold the
  -- local notation `completedTensorProductProjection_q` back to the source-facing name.
  simpa using
    finiteAwayCompletionTensorProductCanonicalProjectionSplit
      (R := R) (q := q) A r hAfin hrq haway

-- Proof sketch: use Lemma `10.123.14` to replace the quasi-finite finite-type algebra by a finite
-- subalgebra with the same localization at `q`, apply Lemma `10.97.8` to that finite algebra
-- after base change to the completion of `R_(q∩R)`, and identify the factor cut out by `q` with
-- `S_q^` because the chosen element becomes a unit in that factor; then split off the distinguished
  -- `q`-factor and record that its projection agrees with the canonical maps from `R_(q∩R)^` and
-- `S`.

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 124 3: Zariski's main theorem supplies a finite subalgebra and a
basic-open localization around the chosen quasi-finite prime. -/
private theorem existsFiniteSubalgebraAwayMapBijectiveAtPrime :
    ∃ (A : Subalgebra R S) (r : A),
      Module.Finite R A ∧ r.1 ∉ q ∧
        Function.Bijective (Localization.awayMap A.val.toRingHom r) := by
  obtain ⟨A, hAfg, r, hrq, haway⟩ :=
    Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective
      (R := R) (S := S) q
  have hAfin : Module.Finite R A := by
    -- Convert the finite generation returned by Zariski's main theorem into `Module.Finite`.
    exact ⟨(Subalgebra.toSubmodule A).fg_top.mpr hAfg⟩
  exact ⟨A, r, hAfin, hrq, haway⟩

/-- Chap10 Lemma 10 124 3: if `R → S` is finite type, `R` is Noetherian, and `q` is a prime of `S`
such that `R → S` is quasi-finite at `q`, then the completed base change
`R_(q∩R)^∧ ⊗[R] S` splits, as an `R_(q∩R)^∧`-algebra, as the product of the completed local ring
`S_q^∧` and another factor. -/
@[stacks 07NC]
theorem exists_completionTensorProduct_algEquiv_completedLocalRing_prod :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R_qR^ B)
      (E : (R_qR^ ⊗[R] S) ≃ₐ[R_qR^] (S_q^ × B)),
      ∀ z : R_qR^ ⊗[R] S,
        (RingHom.fst S_q^ B) (E z) = completedTensorProductProjection q z := by
  -- Proof comment: choose the finite-away model supplied by Zariski's main theorem.
  obtain ⟨A, r, hAfin, hrq, haway⟩ := existsFiniteSubalgebraAwayMapBijectiveAtPrime
  -- Proof comment: with the finite-away witness fixed, the dedicated wrapper helper closes the
  -- theorem without reopening the internal quotient-splitting construction.
  exact
    existsCompletionTensorProductAlgEquivOfFiniteAwayWitness
      (R := R) (q := q) A r hAfin hrq haway

end
