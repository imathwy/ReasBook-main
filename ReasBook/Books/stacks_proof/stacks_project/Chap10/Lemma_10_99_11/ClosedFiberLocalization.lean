import stacks_proof.stacks_project.Chap10.Lemma_10_99_11.LocalCriterionUniverse

open CategoryTheory.Limits IsLocalRing
open scoped TensorProduct Pointwise

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Finite S M]

/-- Helper for Lemma 10.99.11: once the quotient closed fiber is flat over `R ⧸ I`, localizing it
at the induced prime of `S ⧸ IS` gives a flat module over the localized quotient base. -/
lemma flat_localized_closed_fiber_over_quotient_algebra
    {Abar : Type u} {Bbar : Type v} {Qbar : Type w}
    [CommRing Abar] [CommRing Bbar] [Algebra Abar Bbar]
    [AddCommGroup Qbar] [Module Bbar Qbar] [Module Abar Qbar] [IsScalarTower Abar Bbar Qbar]
    (qbar : PrimeSpectrum Bbar) (hflatQ : Module.Flat Abar Qbar) :
    Module.Flat (Localization.AtPrime (qbar.asIdeal.under Abar))
      (LocalizedModule.AtPrime qbar.asIdeal Qbar) := by
  -- Proof comment: this is exactly the standard localization-of-a-flat-module statement over the
  -- quotient-algebra map `Abar → Bbar`.
  simpa using
    (flat_localizedModule_atPrime_over_under_of_flat
      (R := Abar) (A := Bbar) (M := Qbar) hflatQ qbar)

/-- Helper for Chap10 Lemma 10 99 11: the prime of `S` containing `IS` induces a prime of the
quotient ring `S ⧸ IS`. -/
lemma localized_closed_fiber_quotient_prime_isPrime
    (I : Ideal R) (q : PrimeSpectrum S) (hq : I.map (algebraMap R S) ≤ q.asIdeal) :
    (Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap R S) I)) q.asIdeal).IsPrime := by
  -- Proof comment: the quotient map is surjective and its kernel is exactly `IS`, which lies in
  -- `q` by the closed-fiber containment hypothesis.
  exact
    Ideal.map_isPrime_of_surjective
      (f := Ideal.Quotient.mk (Ideal.map (algebraMap R S) I))
      Ideal.Quotient.mk_surjective
      (by simpa [Ideal.mk_ker] using hq)

/-- Helper for Chap10 Lemma 10 99 11: the induced quotient prime of `S / IS` contracts to
the quotient prime of `R / I` induced by `q ∩ R`. -/
lemma localized_closed_fiber_quotient_prime_under_eq
    (I : Ideal R) (q : PrimeSpectrum S) (hq : I.map (algebraMap R S) ≤ q.asIdeal) :
    let IS : Ideal S := Ideal.map (algebraMap R S) I
    let Abar : Type u := R ⧸ I
    let Bbar : Type v := S ⧸ IS
    let p : Ideal R := q.asIdeal.under R
    let hqbarPrime : (Ideal.map (Ideal.Quotient.mk IS) q.asIdeal).IsPrime :=
      localized_closed_fiber_quotient_prime_isPrime (R := R) (S := S) I q hq
    let qbar : PrimeSpectrum Bbar := ⟨Ideal.map (Ideal.Quotient.mk IS) q.asIdeal, hqbarPrime⟩
    qbar.asIdeal.under Abar = Ideal.map (Ideal.Quotient.mk I) p := by
  intro IS Abar Bbar p hqbarPrime qbar
  have hIp : I ≤ p := by
    intro x hx
    exact (Ideal.map_le_iff_le_comap.mp hq) hx
  ext x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  constructor
  · intro hx
    -- Proof comment: pull quotient membership back through `S → S / IS`, then descend it through
    -- `R → R / I`.
    change Ideal.Quotient.mk IS (algebraMap R S r) ∈
      Ideal.map (Ideal.Quotient.mk IS) q.asIdeal at hx
    have hrq : algebraMap R S r ∈ q.asIdeal := by
      simpa [IS] using
        (Ideal.mem_quotient_iff_mem (I := IS) (J := q.asIdeal) (by simpa [IS] using hq)).mp hx
    exact (Ideal.mem_quotient_iff_mem (I := I) (J := p) hIp).mpr
      (by simpa [p, Ideal.under_def] using hrq)
  · intro hx
    -- Proof comment: membership in the source quotient prime pushes forward through
    -- `R / I → S / IS`.
    change Ideal.Quotient.mk IS (algebraMap R S r) ∈
      Ideal.map (Ideal.Quotient.mk IS) q.asIdeal
    have hrp : r ∈ p := (Ideal.mem_quotient_iff_mem (I := I) (J := p) hIp).mp hx
    exact (Ideal.mem_quotient_iff_mem (I := IS) (J := q.asIdeal) (by simpa [IS] using hq)).mpr
      (by simpa [p, Ideal.under_def] using hrp)

/-- Helper for Chap10 Lemma 10 99 11: localizing the mapped source ideal through `S` gives the
same ideal in `S_q` as mapping the source ideal directly to `S_q`. -/
lemma localized_closed_fiber_sourceIdeal_map_eq
    (I : Ideal R) (q : PrimeSpectrum S) :
    let Sq := Localization.AtPrime q.asIdeal
    let IS : Ideal S := Ideal.map (algebraMap R S) I
    Ideal.map (algebraMap S Sq) IS = Ideal.map (algebraMap R Sq) I := by
  -- Proof comment: this is functoriality of ideal map for the composite `R → S → S_q`.
  intro Sq IS
  dsimp [IS]
  rw [Ideal.map_map]
  exact congrArg (fun f : R →+* Sq ↦ Ideal.map f I) (by
    ext r
    rfl)

/-- Helper for Chap10 Lemma 10 99 11: the closed-fiber target ideal maps into its localized
image after pulling back along `S → S_q`. -/
lemma localized_closed_fiber_target_ideal_le_comap
    (I : Ideal R) (q : PrimeSpectrum S) :
    let Sq := Localization.AtPrime q.asIdeal
    let IS : Ideal S := Ideal.map (algebraMap R S) I
    let KqS : Ideal Sq := Ideal.map (algebraMap S Sq) IS
    IS ≤ Ideal.comap (algebraMap S Sq) KqS := by
  intro Sq IS KqS
  -- Proof comment: this is the universal containment `I ≤ comap (map I)`, specialized to the
  -- quotient-localized target denominator.
  exact Ideal.le_comap_map

/-- Helper for Chap10 Lemma 10 99 11: the two localized source ideals give the same denominator
submodule in `M_q`. -/
lemma localized_closed_fiber_sourceIdeal_smul_top_eq
    (I : Ideal R) (q : PrimeSpectrum S) :
    let Sq := Localization.AtPrime q.asIdeal
    let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
    let IS : Ideal S := Ideal.map (algebraMap R S) I
    let Kq : Ideal Sq := Ideal.map (algebraMap R Sq) I
    let KqS : Ideal Sq := Ideal.map (algebraMap S Sq) IS
    Kq • (⊤ : Submodule Sq Mq) = KqS • (⊤ : Submodule Sq Mq) := by
  intro Sq Mq IS Kq KqS
  -- Proof comment: promote the ideal-map equality to the quotient denominator submodules.
  exact congrArg (fun K : Ideal Sq ↦ K • (⊤ : Submodule Sq Mq))
    (localized_closed_fiber_sourceIdeal_map_eq (R := R) (S := S) I q).symm

/-- Helper for Chap10 Lemma 10 99 11: the quotient `M_q / (IS)_q M_q` is an `S`-to-`S / IS`
scalar tower for the quotient-localization algebra structure. -/
lemma localized_closed_fiber_target_isScalarTower_source_quotient
    (I : Ideal R) (q : PrimeSpectrum S) :
    let Sq := Localization.AtPrime q.asIdeal
    let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
    let IS : Ideal S := Ideal.map (algebraMap R S) I
    let Bbar : Type v := S ⧸ IS
    let KqS : Ideal Sq := Ideal.map (algebraMap S Sq) IS
    let TgtS := Mq ⧸ (KqS • (⊤ : Submodule Sq Mq))
    letI : Algebra Bbar (Sq ⧸ KqS) :=
      source_localized_quotient_target_algebra (A := S) (p := q.asIdeal) IS
    letI : Module (Sq ⧸ KqS) TgtS := inferInstance
    letI : Module Bbar TgtS := Module.compHom TgtS (algebraMap Bbar (Sq ⧸ KqS))
    IsScalarTower S Bbar TgtS := by
  intro Sq Mq IS Bbar KqS TgtS
  letI : Algebra Bbar (Sq ⧸ KqS) :=
    source_localized_quotient_target_algebra (A := S) (p := q.asIdeal) IS
  let instQuotientModule : Module (Sq ⧸ KqS) TgtS := inferInstance
  letI : Module (Sq ⧸ KqS) TgtS := instQuotientModule
  letI : SMul (Sq ⧸ KqS) TgtS := instQuotientModule.toSMul
  let instBbarModule : Module Bbar TgtS :=
    Module.compHom TgtS (algebraMap Bbar (Sq ⧸ KqS))
  letI : Module Bbar TgtS := instBbarModule
  -- Proof comment: on quotient generators, the quotient-algebra action is the original `S_q`
  -- action of the localized numerator.
  refine IsScalarTower.of_algebraMap_smul ?_
  intro s x
  refine Submodule.Quotient.induction_on (KqS • (⊤ : Submodule Sq Mq)) x ?_
  intro y
  change (algebraMap Bbar (Sq ⧸ KqS) (algebraMap S Bbar s)) •
      (Submodule.Quotient.mk y : TgtS) =
    s • (Submodule.Quotient.mk y : TgtS)
  have hmap : algebraMap Bbar (Sq ⧸ KqS) (algebraMap S Bbar s) =
      Ideal.Quotient.mk KqS (algebraMap S Sq s) := by
    dsimp [Bbar, KqS]
  rw [hmap]
  rw [Module.Quotient.mk_smul_mk]
  rw [← Submodule.Quotient.mk_smul (KqS • (⊤ : Submodule Sq Mq)) (r := s) (x := y)]
  rw [IsScalarTower.algebraMap_smul Sq s y]

/-- Helper for Chap10 Lemma 10 99 11: for any scalar extension `A → B`, the quotient target
`N / (J B)N` carries the canonical scalar tower from `A` through `A / J`. -/
lemma quotient_target_isScalarTower_source_quotient
    {A B N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (J : Ideal A) :
    let K : Ideal B := Ideal.map (algebraMap A B) J
    letI : Algebra (A ⧸ J) (B ⧸ K) := Ideal.Quotient.algebraQuotientMapQuotient
    letI : Module (B ⧸ K) (N ⧸ (K • (⊤ : Submodule B N))) := inferInstance
    letI : Module (A ⧸ J) (N ⧸ (K • (⊤ : Submodule B N))) :=
      Module.compHom _ (algebraMap (A ⧸ J) (B ⧸ K))
    IsScalarTower A (A ⧸ J) (N ⧸ (K • (⊤ : Submodule B N))) := by
  intro K
  letI : Algebra (A ⧸ J) (B ⧸ K) := Ideal.Quotient.algebraQuotientMapQuotient
  let instQuotientModule : Module (B ⧸ K) (N ⧸ (K • (⊤ : Submodule B N))) :=
    inferInstance
  letI : Module (B ⧸ K) (N ⧸ (K • (⊤ : Submodule B N))) := instQuotientModule
  letI : SMul (B ⧸ K) (N ⧸ (K • (⊤ : Submodule B N))) :=
    instQuotientModule.toSMul
  let instSourceQuotientModule : Module (A ⧸ J) (N ⧸ (K • (⊤ : Submodule B N))) :=
    Module.compHom _ (algebraMap (A ⧸ J) (B ⧸ K))
  letI : Module (A ⧸ J) (N ⧸ (K • (⊤ : Submodule B N))) :=
    instSourceQuotientModule
  -- Proof comment: check the tower on quotient generators; both sides are the action of the
  -- image of the source scalar in `B`.
  refine IsScalarTower.of_algebraMap_smul ?_
  intro a x
  refine Submodule.Quotient.induction_on (K • (⊤ : Submodule B N)) x ?_
  intro n
  change (algebraMap (A ⧸ J) (B ⧸ K) (algebraMap A (A ⧸ J) a)) •
      (Submodule.Quotient.mk n : N ⧸ (K • (⊤ : Submodule B N))) =
    a • (Submodule.Quotient.mk n : N ⧸ (K • (⊤ : Submodule B N)))
  have hmap : algebraMap (A ⧸ J) (B ⧸ K) (algebraMap A (A ⧸ J) a) =
      Ideal.Quotient.mk K (algebraMap A B a) := by
    rfl
  rw [hmap]
  rw [Module.Quotient.mk_smul_mk]
  rw [← Submodule.Quotient.mk_smul (K • (⊤ : Submodule B N)) (r := a) (x := n)]
  rw [IsScalarTower.algebraMap_smul B a n]

/-- Helper for Chap10 Lemma 10 99 11: if `J` maps into `K`, then the quotient target
`N / K N` carries the canonical scalar tower from `A` through `A ⧸ J`. -/
lemma quotient_target_isScalarTower_of_le_comap
    {A B N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (J : Ideal A) (K : Ideal B) (hJK : J ≤ Ideal.comap (algebraMap A B) K) :
    letI : Algebra (A ⧸ J) (B ⧸ K) := Ideal.Quotient.algebraQuotientOfLEComap hJK
    letI : Module (B ⧸ K) (N ⧸ (K • (⊤ : Submodule B N))) := inferInstance
    letI : Module (A ⧸ J) (N ⧸ (K • (⊤ : Submodule B N))) :=
      Module.compHom _ (algebraMap (A ⧸ J) (B ⧸ K))
    IsScalarTower A (A ⧸ J) (N ⧸ (K • (⊤ : Submodule B N))) := by
  letI : Algebra (A ⧸ J) (B ⧸ K) := Ideal.Quotient.algebraQuotientOfLEComap hJK
  let instQuotientModule : Module (B ⧸ K) (N ⧸ (K • (⊤ : Submodule B N))) :=
    inferInstance
  letI : Module (B ⧸ K) (N ⧸ (K • (⊤ : Submodule B N))) := instQuotientModule
  letI : SMul (B ⧸ K) (N ⧸ (K • (⊤ : Submodule B N))) :=
    instQuotientModule.toSMul
  let instSourceQuotientModule : Module (A ⧸ J) (N ⧸ (K • (⊤ : Submodule B N))) :=
    Module.compHom _ (algebraMap (A ⧸ J) (B ⧸ K))
  letI : Module (A ⧸ J) (N ⧸ (K • (⊤ : Submodule B N))) :=
    instSourceQuotientModule
  -- Proof comment: quotient generators reduce the tower identity to the original `A → B`
  -- scalar compatibility on `N`.
  refine IsScalarTower.of_algebraMap_smul ?_
  intro a x
  refine Submodule.Quotient.induction_on (K • (⊤ : Submodule B N)) x ?_
  intro n
  change (algebraMap (A ⧸ J) (B ⧸ K) (algebraMap A (A ⧸ J) a)) •
      (Submodule.Quotient.mk n : N ⧸ (K • (⊤ : Submodule B N))) =
    a • (Submodule.Quotient.mk n : N ⧸ (K • (⊤ : Submodule B N)))
  have hmap : algebraMap (A ⧸ J) (B ⧸ K) (algebraMap A (A ⧸ J) a) =
      Ideal.Quotient.mk K (algebraMap A B a) := by
    rfl
  rw [hmap]
  rw [Module.Quotient.mk_smul_mk]
  rw [← Submodule.Quotient.mk_smul (K • (⊤ : Submodule B N)) (r := a) (x := n)]
  rw [IsScalarTower.algebraMap_smul B a n]

/-- Helper for Chap10 Lemma 10 99 11: a module action pulled back along a ring homomorphism
compatible with an algebra map forms the expected scalar tower. -/
lemma isScalarTower_compHom_of_algebraMap_eq
    {A B C N : Type*} [CommSemiring A] [Semiring B] [Semiring C] [Algebra A B] [Algebra A C]
    [AddCommMonoid N] [Module C N] (f : B →+* C)
    (hf : ∀ a : A, f (algebraMap A B a) = algebraMap A C a) :
    letI : Module B N := Module.compHom N f
    letI : Module A N := Module.compHom N (algebraMap A C)
    IsScalarTower A B N := by
  letI : Module B N := Module.compHom N f
  letI : Module A N := Module.compHom N (algebraMap A C)
  -- Proof comment: after unfolding the two pulled-back actions, the tower identity is precisely
  -- the compatibility of `f` with the algebra maps.
  refine IsScalarTower.of_algebraMap_smul ?_
  intro a n
  change f (algebraMap A B a) • n = (algebraMap A C a) • n
  rw [hf a]

/-- Helper for Chap10 Lemma 10 99 11: flatness descends through a flat base change when the
two pulled-back module actions come from compatible maps into the same scalar ring. -/
lemma flat_compHom_of_flat_compHom_algebra
    {A B C N : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B]
    [AddCommGroup N] [Module C N] (fA : A →+* C) (fB : B →+* C)
    (hf : ∀ a : A, fB (algebraMap A B a) = fA a)
    (hflatAB : Module.Flat A B)
    (hflatBN : letI : Module B N := Module.compHom N fB; Module.Flat B N) :
    letI : Module A N := Module.compHom N fA
    Module.Flat A N := by
  letI : Algebra A C := fA.toAlgebra
  letI : Module B N := Module.compHom N fB
  letI : Module A N := Module.compHom N fA
  have htower : IsScalarTower A B N := by
    -- Proof comment: the scalar-tower condition is exactly the supplied ring-map square.
    exact isScalarTower_compHom_of_algebraMap_eq
      (A := A) (B := B) (C := C) (N := N) fB (by
        intro a
        simpa [RingHom.algebraMap_toAlgebra] using hf a)
  letI : IsScalarTower A B N := htower
  letI : Module.Flat A B := hflatAB
  letI : Module.Flat B N := hflatBN
  -- Proof comment: with the compatible tower installed, ordinary flatness transitivity closes
  -- the transport.
  exact Module.Flat.trans A B N

/-- Helper for Chap10 Lemma 10 99 11: a ring-map equality after postcomposing an algebra
equivalence gives the corresponding pointwise formula after applying the inverse equivalence. -/
lemma ringHom_comp_algEquiv_symm_apply
    {A B C D : Type*} [CommSemiring A] [Semiring B] [Semiring C] [Semiring D]
    [Algebra A B] [Algebra A C] (e : B ≃ₐ[A] C) (f : B →+* D) (g : C →+* D)
    (h : f = g.comp e.toRingHom) :
    ∀ c : C, f (e.symm c) = g c := by
  intro c
  -- Proof comment: evaluate the ring-hom equality at the inverse image of `c`, then simplify
  -- the equivalence cancellation explicitly.
  calc
    f (e.symm c) = (g.comp e.toRingHom) (e.symm c) := RingHom.congr_fun h (e.symm c)
    _ = g c := by
      rw [RingHom.comp_apply]
      exact congrArg g (e.toRingEquiv.apply_symm_apply c)

/-- Helper for Chap10 Lemma 10 99 11: the closed-fiber comparison map from `M / ISM` to the
localized quotient `M_q / (IS)_q M_q`, made linear over `S / IS`. -/
noncomputable def localized_closed_fiber_comparison_map
    (I : Ideal R) (q : PrimeSpectrum S) :
    let Sq := Localization.AtPrime q.asIdeal
    let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
    let IS : Ideal S := Ideal.map (algebraMap R S) I
    let Bbar : Type v := S ⧸ IS
    let Qbar : Type w := M ⧸ (IS • (⊤ : Submodule S M))
    let KqS : Ideal Sq := Ideal.map (algebraMap S Sq) IS
    let TgtS := Mq ⧸ (KqS • (⊤ : Submodule Sq Mq))
    Qbar →ₗ[Bbar] TgtS :=
  let Sq := Localization.AtPrime q.asIdeal
  let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
  let IS : Ideal S := Ideal.map (algebraMap R S) I
  let Bbar : Type v := S ⧸ IS
  let Qbar : Type w := M ⧸ (IS • (⊤ : Submodule S M))
  let Kq : Ideal Sq := Ideal.map (algebraMap R Sq) I
  let KqS : Ideal Sq := Ideal.map (algebraMap S Sq) IS
  let TgtS := Mq ⧸ (KqS • (⊤ : Submodule Sq Mq))
  let eS0 :=
    (localized_quotient_equiv_mapped_ideal (R := R) (S := S) (M := M) I q).restrictScalars S
  let fS0 : Qbar →ₗ[S] (Mq ⧸ (Kq • (⊤ : Submodule Sq Mq))) :=
    eS0.toLinearMap.comp (LocalizedModule.mkLinearMap q.asIdeal.primeCompl Qbar)
  let eKqS : (Mq ⧸ (Kq • (⊤ : Submodule Sq Mq))) ≃ₗ[Sq] TgtS :=
    Submodule.quotEquivOfEq _ _
      (localized_closed_fiber_sourceIdeal_smul_top_eq (R := R) (S := S) (M := M) I q)
  let fS : Qbar →ₗ[S] TgtS :=
    (eKqS.restrictScalars S).toLinearMap.comp fS0
  letI : Algebra Bbar (Sq ⧸ KqS) :=
    source_localized_quotient_target_algebra (A := S) (p := q.asIdeal) IS
  let instQuotientModule : Module (Sq ⧸ KqS) TgtS := inferInstance
  letI : Module (Sq ⧸ KqS) TgtS := instQuotientModule
  letI : SMul (Sq ⧸ KqS) TgtS := instQuotientModule.toSMul
  let instBbarModule : Module Bbar TgtS :=
    Module.compHom TgtS (algebraMap Bbar (Sq ⧸ KqS))
  letI : Module Bbar TgtS := instBbarModule
  letI : IsScalarTower S Bbar TgtS :=
    localized_closed_fiber_target_isScalarTower_source_quotient (R := R) (S := S) (M := M) I q
  LinearMap.extendScalarsOfSurjective (R := S) (S := Bbar)
    (M := Qbar) (N := TgtS) Ideal.Quotient.mk_surjective fS

/-- Helper for Chap10 Lemma 10 99 11: the comparison map is the localization of the quotient
closed fiber at the induced prime of `S / IS`. -/
lemma localized_closed_fiber_comparison_isLocalizedModule
    (I : Ideal R) (q : PrimeSpectrum S) (hq : I.map (algebraMap R S) ≤ q.asIdeal) :
    let IS : Ideal S := Ideal.map (algebraMap R S) I
    let Bbar : Type v := S ⧸ IS
    let hqbarPrime : (Ideal.map (Ideal.Quotient.mk IS) q.asIdeal).IsPrime :=
      localized_closed_fiber_quotient_prime_isPrime (R := R) (S := S) I q hq
    let qbar : PrimeSpectrum Bbar := ⟨Ideal.map (Ideal.Quotient.mk IS) q.asIdeal, hqbarPrime⟩
    IsLocalizedModule qbar.asIdeal.primeCompl
      (localized_closed_fiber_comparison_map (R := R) (S := S) (M := M) I q) := by
  intro IS Bbar hqbarPrime qbar
  let Sq := Localization.AtPrime q.asIdeal
  let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
  let Qbar : Type w := M ⧸ (IS • (⊤ : Submodule S M))
  let Kq : Ideal Sq := Ideal.map (algebraMap R Sq) I
  let KqS : Ideal Sq := Ideal.map (algebraMap S Sq) IS
  let TgtS := Mq ⧸ (KqS • (⊤ : Submodule Sq Mq))
  let eS0 :=
    (localized_quotient_equiv_mapped_ideal (R := R) (S := S) (M := M) I q).restrictScalars S
  let fS0 : Qbar →ₗ[S] (Mq ⧸ (Kq • (⊤ : Submodule Sq Mq))) :=
    eS0.toLinearMap.comp (LocalizedModule.mkLinearMap q.asIdeal.primeCompl Qbar)
  let eKqS : (Mq ⧸ (Kq • (⊤ : Submodule Sq Mq))) ≃ₗ[Sq] TgtS :=
    Submodule.quotEquivOfEq _ _
      (localized_closed_fiber_sourceIdeal_smul_top_eq (R := R) (S := S) (M := M) I q)
  let fS : Qbar →ₗ[S] TgtS :=
    (eKqS.restrictScalars S).toLinearMap.comp fS0
  have hSLoc0 : IsLocalizedModule q.asIdeal.primeCompl fS0 := by
    -- Proof comment: the standard localized quotient equivalence identifies this with the
    -- canonical localization map.
    exact IsLocalizedModule.of_linearEquiv q.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl Qbar) eS0
  letI : IsLocalizedModule q.asIdeal.primeCompl fS0 := hSLoc0
  have hSLocCore : IsLocalizedModule q.asIdeal.primeCompl fS :=
    -- Proof comment: replacing the denominator by an equal mapped ideal preserves localization.
    IsLocalizedModule.of_linearEquiv q.asIdeal.primeCompl fS0
      (eKqS.restrictScalars S)
  letI : IsLocalizedModule q.asIdeal.primeCompl fS := hSLocCore
  letI : Algebra Bbar (Sq ⧸ KqS) :=
    source_localized_quotient_target_algebra (A := S) (p := q.asIdeal) IS
  let instQuotientModule : Module (Sq ⧸ KqS) TgtS := inferInstance
  letI : Module (Sq ⧸ KqS) TgtS := instQuotientModule
  letI : SMul (Sq ⧸ KqS) TgtS := instQuotientModule.toSMul
  let instBbarModule : Module Bbar TgtS :=
    Module.compHom TgtS (algebraMap Bbar (Sq ⧸ KqS))
  letI : Module Bbar TgtS := instBbarModule
  letI : IsScalarTower S Bbar TgtS :=
    localized_closed_fiber_target_isScalarTower_source_quotient (R := R) (S := S) (M := M) I q
  let fB : Qbar →ₗ[Bbar] TgtS :=
    LinearMap.extendScalarsOfSurjective (R := S) (S := Bbar)
      (M := Qbar) (N := TgtS) Ideal.Quotient.mk_surjective fS
  have hBLoc0 : IsLocalizedModule (Algebra.algebraMapSubmonoid Bbar q.asIdeal.primeCompl)
      fB := by
    -- Proof comment: descend the localized-module structure through the surjective quotient map
    -- `S → S / IS`.
    have hrestrict : IsLocalizedModule q.asIdeal.primeCompl (fB.restrictScalars S) := by
      simpa [fB] using hSLocCore
    letI : IsLocalizedModule q.asIdeal.primeCompl (fB.restrictScalars S) := hrestrict
    exact IsLocalizedModule.of_restrictScalars q.asIdeal.primeCompl fB
  have hprimeCompl :
      Algebra.algebraMapSubmonoid Bbar q.asIdeal.primeCompl = qbar.asIdeal.primeCompl := by
    -- Proof comment: the prime complement in the quotient is the image of the original prime
    -- complement.
    simpa [Bbar, qbar, hqbarPrime] using
      (quotient_primeCompl_eq_algebraMapSubmonoid_at_under
        (A := S) IS q.asIdeal (by simpa [IS] using hq))
  -- Proof comment: unfold the packaged comparison map only after the localization property has
  -- been proved for its source-linear core.
  simpa [localized_closed_fiber_comparison_map, Sq, Mq, IS, Bbar, Qbar, Kq, KqS, TgtS,
    hprimeCompl] using hBLoc0

/-- Helper for Chap10 Lemma 10 99 11: the localized closed fiber over `S / IS` is linearly
equivalent to the concrete quotient `M_q / (IS)_q M_q`. -/
noncomputable def localized_closed_fiber_owner_equiv
    (I : Ideal R) (q : PrimeSpectrum S) (hq : I.map (algebraMap R S) ≤ q.asIdeal) :
    let Sq := Localization.AtPrime q.asIdeal
    let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
    let IS : Ideal S := Ideal.map (algebraMap R S) I
    let Bbar : Type v := S ⧸ IS
    let Qbar : Type w := M ⧸ (IS • (⊤ : Submodule S M))
    let KqS : Ideal Sq := Ideal.map (algebraMap S Sq) IS
    let TgtS := Mq ⧸ (KqS • (⊤ : Submodule Sq Mq))
    let hqbarPrime : (Ideal.map (Ideal.Quotient.mk IS) q.asIdeal).IsPrime :=
      localized_closed_fiber_quotient_prime_isPrime (R := R) (S := S) I q hq
    let qbar : PrimeSpectrum Bbar := ⟨Ideal.map (Ideal.Quotient.mk IS) q.asIdeal, hqbarPrime⟩
    LocalizedModule.AtPrime qbar.asIdeal Qbar ≃ₗ[Bbar] TgtS :=
  let Sq := Localization.AtPrime q.asIdeal
  let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
  let IS : Ideal S := Ideal.map (algebraMap R S) I
  let Bbar : Type v := S ⧸ IS
  let Qbar : Type w := M ⧸ (IS • (⊤ : Submodule S M))
  let KqS : Ideal Sq := Ideal.map (algebraMap S Sq) IS
  let TgtS := Mq ⧸ (KqS • (⊤ : Submodule Sq Mq))
  let hqbarPrime : (Ideal.map (Ideal.Quotient.mk IS) q.asIdeal).IsPrime :=
    localized_closed_fiber_quotient_prime_isPrime (R := R) (S := S) I q hq
  let qbar : PrimeSpectrum Bbar := ⟨Ideal.map (Ideal.Quotient.mk IS) q.asIdeal, hqbarPrime⟩
  letI : IsLocalizedModule qbar.asIdeal.primeCompl
      (localized_closed_fiber_comparison_map (R := R) (S := S) (M := M) I q) :=
    localized_closed_fiber_comparison_isLocalizedModule (R := R) (S := S) (M := M) I q hq
  IsLocalizedModule.iso qbar.asIdeal.primeCompl
    (localized_closed_fiber_comparison_map (R := R) (S := S) (M := M) I q)

/-- Helper for Chap10 Lemma 10 99 11: mapping the localized source ideal from `R_p` to `S_q`
recovers the denominator ideal obtained by first mapping `I` to `S` and then localizing. -/
lemma localized_closed_fiber_under_sourceIdeal_map_eq
    (I : Ideal R) (q : PrimeSpectrum S) :
    let p : Ideal R := q.asIdeal.under R
    let Rp := Localization.AtPrime p
    let Sq := Localization.AtPrime q.asIdeal
    let J : Ideal Rp := Ideal.map (algebraMap R Rp) I
    let IS : Ideal S := Ideal.map (algebraMap R S) I
    let KqS : Ideal Sq := Ideal.map (algebraMap S Sq) IS
    let f : Rp →+* Sq := Localization.localRingHom p q.asIdeal (algebraMap R S) rfl
    letI : Algebra Rp Sq := f.toAlgebra
    Ideal.map (algebraMap Rp Sq) J = KqS := by
  intro p Rp Sq J IS KqS f
  letI : Algebra Rp Sq := f.toAlgebra
  have hJmap : Ideal.map (algebraMap Rp Sq) J = Ideal.map (algebraMap R Sq) I := by
    -- Proof comment: the local map `R_p → S_q` composes with `R → R_p` as the ordinary
    -- localization map `R → S_q`.
    dsimp [J]
    rw [Ideal.map_map]
    exact congrArg (fun g : R →+* Sq ↦ Ideal.map g I) (by
      ext r
      calc
        (algebraMap Rp Sq) ((algebraMap R Rp) r) =
            algebraMap S Sq ((algebraMap R S) r) := by
              simpa [p, Rp, Sq, f, RingHom.algebraMap_toAlgebra] using
                (Localization.localRingHom_to_map (q.asIdeal.under R) q.asIdeal
                  (algebraMap R S) rfl r)
        _ = algebraMap R Sq r := by
              rw [IsScalarTower.algebraMap_apply R S Sq])
  -- Proof comment: the right-hand ideal is the same direct localized image of `I`.
  calc
    Ideal.map (algebraMap Rp Sq) J = Ideal.map (algebraMap R Sq) I := hJmap
    _ = KqS := by
      simpa [Sq, IS, KqS] using
        (localized_closed_fiber_sourceIdeal_map_eq (R := R) (S := S) I q).symm

/-- Helper for Chap10 Lemma 10 99 11: the localized source ideal maps into the target
denominator ideal in `S_q`. -/
lemma localized_closed_fiber_source_ideal_le_target_comap
    (I : Ideal R) (q : PrimeSpectrum S) :
    let p : Ideal R := q.asIdeal.under R
    let Rp := Localization.AtPrime p
    let Sq := Localization.AtPrime q.asIdeal
    let J : Ideal Rp := Ideal.map (algebraMap R Rp) I
    let IS : Ideal S := Ideal.map (algebraMap R S) I
    let KqS : Ideal Sq := Ideal.map (algebraMap S Sq) IS
    let f : Rp →+* Sq := Localization.localRingHom p q.asIdeal (algebraMap R S) rfl
    letI : Algebra Rp Sq := f.toAlgebra
    J ≤ Ideal.comap (algebraMap Rp Sq) KqS := by
  intro p Rp Sq J IS KqS f
  letI : Algebra Rp Sq := f.toAlgebra
  -- Proof comment: rewrite the containment through `map_le_iff_le_comap`, then use the existing
  -- equality identifying the mapped source ideal with the target denominator.
  rw [← Ideal.map_le_iff_le_comap]
  exact le_of_eq (by
    simpa [p, Rp, Sq, J, IS, KqS, f] using
      localized_closed_fiber_under_sourceIdeal_map_eq (R := R) (S := S) I q)

/-- Helper for Chap10 Lemma 10 99 11: the canonical algebra
`R_(q ∩ R) ⧸ J → S_q ⧸ KqS` is induced by the ideal containment above. -/
@[reducible]
noncomputable def localized_closed_fiber_source_quotient_target_algebra
    (I : Ideal R) (q : PrimeSpectrum S) :
    let p : Ideal R := q.asIdeal.under R
    let Rp := Localization.AtPrime p
    let Sq := Localization.AtPrime q.asIdeal
    let J : Ideal Rp := Ideal.map (algebraMap R Rp) I
    let IS : Ideal S := Ideal.map (algebraMap R S) I
    let KqS : Ideal Sq := Ideal.map (algebraMap S Sq) IS
    let f : Rp →+* Sq := Localization.localRingHom p q.asIdeal (algebraMap R S) rfl
    letI : Algebra Rp Sq := f.toAlgebra
    Algebra (Rp ⧸ J) (Sq ⧸ KqS) :=
  let p : Ideal R := q.asIdeal.under R
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q.asIdeal
  let J : Ideal Rp := Ideal.map (algebraMap R Rp) I
  let IS : Ideal S := Ideal.map (algebraMap R S) I
  let KqS : Ideal Sq := Ideal.map (algebraMap S Sq) IS
  let f : Rp →+* Sq := Localization.localRingHom p q.asIdeal (algebraMap R S) rfl
  letI : Algebra Rp Sq := f.toAlgebra
  Ideal.Quotient.algebraQuotientOfLEComap
    (localized_closed_fiber_source_ideal_le_target_comap (R := R) (S := S) I q)

/-- Helper for Chap10 Lemma 10 99 11: the canonical map
`R_(q ∩ R) ⧸ J → S_q ⧸ KqS` sends a quotient generator to the corresponding localized
target quotient generator. -/
lemma localized_closed_fiber_source_quotient_target_algebraMap_mk
    (I : Ideal R) (q : PrimeSpectrum S) (r : Localization.AtPrime (q.asIdeal.under R)) :
    let p : Ideal R := q.asIdeal.under R
    let Rp := Localization.AtPrime p
    let Sq := Localization.AtPrime q.asIdeal
    let J : Ideal Rp := Ideal.map (algebraMap R Rp) I
    let IS : Ideal S := Ideal.map (algebraMap R S) I
    let KqS : Ideal Sq := Ideal.map (algebraMap S Sq) IS
    let f : Rp →+* Sq := Localization.localRingHom p q.asIdeal (algebraMap R S) rfl
    letI : Algebra Rp Sq := f.toAlgebra
    letI : Algebra (Rp ⧸ J) (Sq ⧸ KqS) :=
      localized_closed_fiber_source_quotient_target_algebra (R := R) (S := S) I q
    algebraMap (Rp ⧸ J) (Sq ⧸ KqS) (Ideal.Quotient.mk J r) =
      Ideal.Quotient.mk KqS (algebraMap Rp Sq r) := by
  intro p Rp Sq J IS KqS f
  letI : Algebra Rp Sq := f.toAlgebra
  letI : Algebra (Rp ⧸ J) (Sq ⧸ KqS) :=
    localized_closed_fiber_source_quotient_target_algebra (R := R) (S := S) I q
  -- Proof comment: after unfolding the named algebra, this is the generator formula for
  -- `Ideal.Quotient.algebraQuotientOfLEComap`.
  rfl

/-- Helper for Chap10 Lemma 10 99 11: after restricting scalars from `S_q` to `R_p`, the
denominator `(IS)_q M_q` is the textbook denominator `J M_q`. -/
lemma localized_closed_fiber_denominator_restrictScalars_eq
    (I : Ideal R) (q : PrimeSpectrum S) :
    let p : Ideal R := q.asIdeal.under R
    let Rp := Localization.AtPrime p
    let Sq := Localization.AtPrime q.asIdeal
    let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
    let J : Ideal Rp := Ideal.map (algebraMap R Rp) I
    let IS : Ideal S := Ideal.map (algebraMap R S) I
    let KqS : Ideal Sq := Ideal.map (algebraMap S Sq) IS
    let f : Rp →+* Sq := Localization.localRingHom p q.asIdeal (algebraMap R S) rfl
    letI : Algebra Rp Sq := f.toAlgebra
    ((KqS • (⊤ : Submodule Sq Mq)).restrictScalars Rp) =
      J • (⊤ : Submodule Rp Mq) := by
  dsimp
  let p : Ideal R := q.asIdeal.under R
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q.asIdeal
  let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
  let J : Ideal Rp := Ideal.map (algebraMap R Rp) I
  let IS : Ideal S := Ideal.map (algebraMap R S) I
  let KqS : Ideal Sq := Ideal.map (algebraMap S Sq) IS
  let f : Rp →+* Sq := Localization.localRingHom p q.asIdeal (algebraMap R S) rfl
  letI : Algebra Rp Sq := f.toAlgebra
  have hJmapToKqS : Ideal.map (algebraMap Rp Sq) J = KqS := by
    simpa [p, Rp, Sq, J, IS, KqS, f] using
      localized_closed_fiber_under_sourceIdeal_map_eq (R := R) (S := S) I q
  -- Proof comment: the claim is now the standard restriction-of-scalars formula for ideal
  -- multiples.
  calc
    ((KqS • (⊤ : Submodule Sq Mq)).restrictScalars Rp) =
        ((Ideal.map (algebraMap Rp Sq) J • (⊤ : Submodule Sq Mq)).restrictScalars Rp) := by
          rw [← hJmapToKqS]
    _ = J • (⊤ : Submodule Rp Mq) := by
          simpa using
            (Ideal.smul_restrictScalars (R := Rp) (S := Sq) (M := Mq) (I := J)
              (N := (⊤ : Submodule Sq Mq)))

/-- Helper for Chap10 Lemma 10 99 11: the mapped source ideal `J` and the localized target
ideal `KqS` define the same denominator submodule in `M_q`. -/
lemma localized_closed_fiber_under_sourceIdeal_smul_top_eq
    (I : Ideal R) (q : PrimeSpectrum S) :
    let p : Ideal R := q.asIdeal.under R
    let Rp := Localization.AtPrime p
    let Sq := Localization.AtPrime q.asIdeal
    let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
    let J : Ideal Rp := Ideal.map (algebraMap R Rp) I
    let IS : Ideal S := Ideal.map (algebraMap R S) I
    let KqS : Ideal Sq := Ideal.map (algebraMap S Sq) IS
    let f : Rp →+* Sq := Localization.localRingHom p q.asIdeal (algebraMap R S) rfl
    letI : Algebra Rp Sq := f.toAlgebra
    (Ideal.map (algebraMap Rp Sq) J) • (⊤ : Submodule Sq Mq) =
      KqS • (⊤ : Submodule Sq Mq) := by
  intro p Rp Sq Mq J IS KqS f
  letI : Algebra Rp Sq := f.toAlgebra
  -- Proof comment: first normalize the ideals in `S_q`, then apply congruence to the
  -- denominator submodule construction.
  exact congrArg (fun K : Ideal Sq ↦ K • (⊤ : Submodule Sq Mq)) <| by
    simpa [p, Rp, Sq, J, IS, KqS, f] using
      localized_closed_fiber_under_sourceIdeal_map_eq (R := R) (S := S) I q

/-- Helper for Chap10 Lemma 10 99 11: the concrete target denominator is the image of the
localized source denominator under `R_(q ∩ R) → S_q`. -/
lemma localized_closed_fiber_target_denominator_eq_mapped_source
    (I : Ideal R) (q : PrimeSpectrum S) :
    let p : Ideal R := q.asIdeal.under R
    let Rp := Localization.AtPrime p
    let Sq := Localization.AtPrime q.asIdeal
    let J : Ideal Rp := Ideal.map (algebraMap R Rp) I
    let IS : Ideal S := Ideal.map (algebraMap R S) I
    let KqS : Ideal Sq := Ideal.map (algebraMap S Sq) IS
    let f : Rp →+* Sq := Localization.localRingHom p q.asIdeal (algebraMap R S) rfl
    letI : Algebra Rp Sq := f.toAlgebra
    KqS = Ideal.map (algebraMap Rp Sq) J := by
  intro p Rp Sq J IS KqS f
  letI : Algebra Rp Sq := f.toAlgebra
  -- Proof comment: this is the denominator-normalization direction needed for scalar-tower
  -- comparisons; it is the symmetric form of the existing ideal-map computation.
  symm
  simpa [p, Rp, Sq, J, IS, KqS, f] using
    localized_closed_fiber_under_sourceIdeal_map_eq (R := R) (S := S) I q

/-- Helper for Chap10 Lemma 10 99 11: flatness transfers across an additive equivalence when the
source module structure is transported along that equivalence. -/
lemma flat_of_addEquiv_module
    {A X Y : Type*} [CommSemiring A] [AddCommMonoid X] [AddCommMonoid Y]
    [Module A X] [Module.Flat A X] (e : Y ≃+ X) :
    letI : Module A Y := AddEquiv.module A e
    Module.Flat A Y := by
  letI : Module A Y := AddEquiv.module A e
  -- Proof comment: the transported module structure makes the additive equivalence linear, so
  -- flatness follows by invariance under linear equivalence.
  exact Module.Flat.of_linearEquiv (AddEquiv.linearEquiv (A := A) e)

/-- Helper for Chap10 Lemma 10 99 11: a flat module remains flat after transferring the module
structure across an additive equivalence. -/
lemma flat_of_addEquiv_module_from_flat
    {A X Y : Type*} [CommSemiring A] [AddCommMonoid X] [AddCommMonoid Y]
    [Module A X] (hflat : Module.Flat A X) (e : Y ≃+ X) :
    letI : Module A Y := AddEquiv.module A e
    Module.Flat A Y := by
  letI : Module.Flat A X := hflat
  -- Proof comment: install the known flatness as an instance, then use the transported-module
  -- flatness helper.
  exact flat_of_addEquiv_module (A := A) e

/-- Helper for Chap10 Lemma 10 99 11: flatness transfers across the inverse of an additive
equivalence when the target carries the transported module structure. -/
lemma flat_of_addEquiv_symm_module_from_flat
    {A X Y : Type*} [CommSemiring A] [AddCommMonoid X] [AddCommMonoid Y]
    [Module A X] (hflat : Module.Flat A X) (e : X ≃+ Y) :
    letI : Module A Y := AddEquiv.module A e.symm
    Module.Flat A Y := by
  -- Proof comment: delegate to the forward transported-module helper, with the inverse
  -- equivalence as the transport owner.
  exact flat_of_addEquiv_module_from_flat (A := A) hflat e.symm

/-- Helper for Chap10 Lemma 10 99 11: a linear equivalence over a source ring transports
flatness over a surjective quotient scalar ring once both modules carry compatible quotient scalar
towers. -/
lemma flat_of_linearEquiv_extendScalarsOfSurjective
    {A B X Y : Type*} [CommSemiring A] [CommSemiring B] [Algebra A B]
    [AddCommMonoid X] [AddCommMonoid Y]
    [Module A X] [Module B X] [IsScalarTower A B X]
    [Module A Y] [Module B Y] [IsScalarTower A B Y]
    (h : Function.Surjective (algebraMap A B)) (hflat : Module.Flat B X)
    (e : X ≃ₗ[A] Y) :
    Module.Flat B Y := by
  -- Proof comment: surjectivity upgrades the source-linear equivalence to a quotient-linear
  -- equivalence, and flatness is invariant under linear equivalence.
  letI : Module.Flat B X := hflat
  let eB : X ≃ₗ[B] Y := e.extendScalarsOfSurjective h
  exact Module.Flat.of_linearEquiv eB.symm

/-- Helper for Chap10 Lemma 10 99 11: flatness transfers across a supplied linear equivalence
from a flat source module to the target module. -/
lemma flat_of_linearEquiv_from_flat
    {A X Y : Type*} [CommSemiring A] [AddCommMonoid X] [AddCommMonoid Y]
    [Module A X] [Module A Y] (hflat : Module.Flat A X) (e : X ≃ₗ[A] Y) :
    Module.Flat A Y := by
  letI : Module.Flat A X := hflat
  -- Proof comment: install the source flatness once, then use invariance under linear
  -- equivalence in the forward direction.
  exact Module.Flat.of_linearEquiv e.symm

/-- Helper for Chap10 Lemma 10 99 11: flatness transfers across a supplied linear equivalence
when the source flatness is already available as an instance. -/
lemma flat_of_linearEquiv_instance
    {A X Y : Type*} [CommSemiring A] [AddCommMonoid X] [AddCommMonoid Y]
    [Module A X] [Module A Y] [Module.Flat A X] (e : X ≃ₗ[A] Y) :
    Module.Flat A Y := by
  -- Proof comment: this keeps the final transport proof term small in larger declarations.
  exact Module.Flat.of_linearEquiv e.symm

/-- Helper for Chap10 Lemma 10 99 11: flatness composes when both flatness hypotheses are passed
explicitly rather than synthesized by typeclass search in a larger proof. -/
lemma flat_trans_from_flat
    {A B N : Type*} [CommSemiring A] [CommSemiring B] [Algebra A B]
    [AddCommMonoid N] [Module A N] [Module B N] [IsScalarTower A B N]
    (hAB : Module.Flat A B) (hBN : Module.Flat B N) :
    Module.Flat A N := by
  -- Proof comment: install the two flatness facts locally and call the standard transitivity
  -- theorem once in this small helper.
  letI : Module.Flat A B := hAB
  letI : Module.Flat B N := hBN
  exact Module.Flat.trans A B N

/-- Helper for Chap10 Lemma 10 99 11: a flat quotient by a target denominator remains flat
after replacing the denominator by its source-restricted form. -/
lemma flat_of_target_denominator_linearEquiv
    {A B N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (J : Ideal A) (K : Ideal B)
    (hdenom : ((K • (⊤ : Submodule B N)).restrictScalars A) =
      J • (⊤ : Submodule A N))
    [Module (A ⧸ J) (N ⧸ (K • (⊤ : Submodule B N)))]
    [IsScalarTower A (A ⧸ J) (N ⧸ (K • (⊤ : Submodule B N)))]
    (hflat : Module.Flat (A ⧸ J) (N ⧸ (K • (⊤ : Submodule B N)))) :
    Module.Flat (A ⧸ J) (N ⧸ (J • (⊤ : Submodule A N))) := by
  let e : (N ⧸ (K • (⊤ : Submodule B N))) ≃ₗ[A]
      (N ⧸ (J • (⊤ : Submodule A N))) :=
    localized_closed_fiber_target_equiv (A := A) (B := B) (N := N) J K hdenom
  -- Proof comment: extend the denominator comparison across `A → A / J`, then use invariance of
  -- flatness under quotient-linear equivalence.
  exact
    flat_of_linearEquiv_extendScalarsOfSurjective
      (A := A) (B := A ⧸ J) (X := N ⧸ (K • (⊤ : Submodule B N)))
      (Y := N ⧸ (J • (⊤ : Submodule A N)))
      Ideal.Quotient.mk_surjective hflat e

/-- Helper for Chap10 Lemma 10 99 11: the denominator comparison transfers flatness once the
source quotient action is known to be compatible with the source-ring action. -/
lemma flat_of_target_denominator_linearEquiv_of_sourceTower
    {A B N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (J : Ideal A) (K : Ideal B)
    (hdenom : ((K • (⊤ : Submodule B N)).restrictScalars A) =
      J • (⊤ : Submodule A N))
    [Module (A ⧸ J) (N ⧸ (K • (⊤ : Submodule B N)))]
    (hsourceTower : IsScalarTower A (A ⧸ J) (N ⧸ (K • (⊤ : Submodule B N))))
    (hflat : Module.Flat (A ⧸ J) (N ⧸ (K • (⊤ : Submodule B N)))) :
    Module.Flat (A ⧸ J) (N ⧸ (J • (⊤ : Submodule A N))) := by
  -- Proof comment: install the explicit source quotient tower and delegate to the quotient-linear
  -- denominator equivalence.
  letI : IsScalarTower A (A ⧸ J) (N ⧸ (K • (⊤ : Submodule B N))) := hsourceTower
  exact flat_of_target_denominator_linearEquiv (A := A) (B := B) (N := N) J K hdenom hflat

/-- Helper for Chap10 Lemma 10 99 11: the quotient-prime complement in `R ⧸ I` is the image of
the under-prime complement from `R`. -/
lemma localized_closed_fiber_base_primeCompl_eq
    (I : Ideal R) (q : PrimeSpectrum S) (hq : I.map (algebraMap R S) ≤ q.asIdeal) :
    let p : Ideal R := q.asIdeal.under R
    let IS : Ideal S := Ideal.map (algebraMap R S) I
    let Abar : Type u := R ⧸ I
    let Bbar : Type v := S ⧸ IS
    let hqbarPrime : (Ideal.map (Ideal.Quotient.mk IS) q.asIdeal).IsPrime :=
      localized_closed_fiber_quotient_prime_isPrime (R := R) (S := S) I q hq
    let qbar : PrimeSpectrum Bbar := ⟨Ideal.map (Ideal.Quotient.mk IS) q.asIdeal, hqbarPrime⟩
    (qbar.asIdeal.under Abar).primeCompl = Algebra.algebraMapSubmonoid Abar p.primeCompl := by
  intro p IS Abar Bbar hqbarPrime qbar
  have hUnder : qbar.asIdeal.under Abar = Ideal.map (Ideal.Quotient.mk I) p := by
    -- Proof comment: first identify the base prime with the quotient of `q ∩ R`.
    simpa [IS, Abar, Bbar, p, qbar, hqbarPrime] using
      localized_closed_fiber_quotient_prime_under_eq (R := R) (S := S) I q hq
  have hIp : I ≤ p := by
    -- Proof comment: the closed-fiber containment is exactly containment after contraction.
    intro x hx
    exact (Ideal.map_le_iff_le_comap.mp hq) hx
  have hmapPrime : (Ideal.map (Ideal.Quotient.mk I) p).IsPrime := by
    rw [← hUnder]
    infer_instance
  letI : (Ideal.map (Ideal.Quotient.mk I) p).IsPrime := hmapPrime
  -- Proof comment: quotienting carries the original prime complement to the quotient-prime
  -- complement.
  ext x
  have hmap := quotient_primeCompl_eq_algebraMapSubmonoid_at_under (A := R) I p hIp
  rw [hmap]
  change (x ∉ qbar.asIdeal.under Abar) ↔ x ∉ Ideal.map (Ideal.Quotient.mk I) p
  rw [hUnder]

/-- Helper for Chap10 Lemma 10 99 11: the quotient-localized base
`(R / I)_(q ∩ R)` is flat over the textbook base `R_(q ∩ R) / J`. -/
lemma localized_closed_fiber_base_flat
    (I : Ideal R) (q : PrimeSpectrum S) (hq : I.map (algebraMap R S) ≤ q.asIdeal) :
    let p : Ideal R := q.asIdeal.under R
    let Rp := Localization.AtPrime p
    let J : Ideal Rp := Ideal.map (algebraMap R Rp) I
    let IS : Ideal S := Ideal.map (algebraMap R S) I
    let Abar : Type u := R ⧸ I
    let Bbar : Type v := S ⧸ IS
    let hqbarPrime : (Ideal.map (Ideal.Quotient.mk IS) q.asIdeal).IsPrime :=
      localized_closed_fiber_quotient_prime_isPrime (R := R) (S := S) I q hq
    let qbar : PrimeSpectrum Bbar := ⟨Ideal.map (Ideal.Quotient.mk IS) q.asIdeal, hqbarPrime⟩
    ∃ algBase : Algebra (Rp ⧸ J) (Localization.AtPrime (qbar.asIdeal.under Abar)),
      letI : Algebra (Rp ⧸ J) (Localization.AtPrime (qbar.asIdeal.under Abar)) := algBase
      Module.Flat (Rp ⧸ J) (Localization.AtPrime (qbar.asIdeal.under Abar)) := by
  intro p Rp J IS Abar Bbar hqbarPrime qbar
  letI : Algebra Abar (Rp ⧸ J) :=
    source_localized_quotient_target_algebra (A := R) (p := p) I
  let eBase0 :
      Localization (Algebra.algebraMapSubmonoid Abar p.primeCompl) ≃ₐ[Abar] (Rp ⧸ J) :=
    Localization.algEquiv (Algebra.algebraMapSubmonoid Abar p.primeCompl) (Rp ⧸ J)
  have hUnder : qbar.asIdeal.under Abar = Ideal.map (Ideal.Quotient.mk I) p := by
    -- Proof comment: normalize the base prime of the quotient-localized closed fiber to the
    -- quotient of the under-prime `q ∩ R`.
    simpa [IS, Abar, Bbar, p, qbar, hqbarPrime] using
      localized_closed_fiber_quotient_prime_under_eq (R := R) (S := S) I q hq
  have hIp : I ≤ p := by
    -- Proof comment: the closed-fiber containment says precisely that `I` lies in the contraction.
    intro x hx
    exact (Ideal.map_le_iff_le_comap.mp hq) hx
  have hmapPrime : (Ideal.map (Ideal.Quotient.mk I) p).IsPrime := by
    rw [← hUnder]
    infer_instance
  letI : (Ideal.map (Ideal.Quotient.mk I) p).IsPrime := hmapPrime
  have hPrimeCompl :
      (qbar.asIdeal.under Abar).primeCompl = Algebra.algebraMapSubmonoid Abar p.primeCompl := by
    -- Proof comment: after the previous prime identification, complements are the quotient images
    -- of the original prime complement.
    ext x
    have hmap := quotient_primeCompl_eq_algebraMapSubmonoid_at_under (A := R) I p hIp
    rw [hmap]
    change (x ∉ qbar.asIdeal.under Abar) ↔ x ∉ Ideal.map (Ideal.Quotient.mk I) p
    rw [hUnder]
  let eBase : Localization.AtPrime (qbar.asIdeal.under Abar) ≃ₐ[Abar] (Rp ⧸ J) := by
    unfold Localization.AtPrime
    exact hPrimeCompl.symm ▸ eBase0
  let algBase : Algebra (Rp ⧸ J) (Localization.AtPrime (qbar.asIdeal.under Abar)) :=
    eBase.symm.toAlgHom.toAlgebra
  refine ⟨algBase, ?_⟩
  letI : Algebra (Rp ⧸ J) (Localization.AtPrime (qbar.asIdeal.under Abar)) := algBase
  letI : Module (Rp ⧸ J) (Localization.AtPrime (qbar.asIdeal.under Abar)) := Algebra.toModule
  let eAlg : Localization.AtPrime (qbar.asIdeal.under Abar) ≃ₐ[Rp ⧸ J] (Rp ⧸ J) :=
    AlgEquiv.ofRingEquiv (R := Rp ⧸ J) (f := eBase.toRingEquiv) (by
      intro x
      change eBase (eBase.symm x) = x
      simp)
  letI : Module (Rp ⧸ J) (Rp ⧸ J) := Semiring.toModule
  letI : Module.Flat (Rp ⧸ J) (Rp ⧸ J) := Module.Flat.self (R := Rp ⧸ J)
  -- Proof comment: flatness follows because the two base rings are algebra-equivalent.
  exact Module.Flat.of_linearEquiv eAlg.toLinearEquiv

/-- Helper for Chap10 Lemma 10 99 11: the quotient-localized base carries the named
`R_(q ∩ R) / J`-algebra structure used in the closed-fiber comparison. -/
@[reducible]
noncomputable def localized_closed_fiber_base_algebra
    (I : Ideal R) (q : PrimeSpectrum S) (hq : I.map (algebraMap R S) ≤ q.asIdeal) :
    let p : Ideal R := q.asIdeal.under R
    let Rp := Localization.AtPrime p
    let J : Ideal Rp := Ideal.map (algebraMap R Rp) I
    let IS : Ideal S := Ideal.map (algebraMap R S) I
    let Abar : Type u := R ⧸ I
    let Bbar : Type v := S ⧸ IS
    let hqbarPrime : (Ideal.map (Ideal.Quotient.mk IS) q.asIdeal).IsPrime :=
      localized_closed_fiber_quotient_prime_isPrime (R := R) (S := S) I q hq
    let qbar : PrimeSpectrum Bbar := ⟨Ideal.map (Ideal.Quotient.mk IS) q.asIdeal, hqbarPrime⟩
    Algebra (Rp ⧸ J) (Localization.AtPrime (qbar.asIdeal.under Abar)) :=
  Classical.choose (localized_closed_fiber_base_flat (R := R) (S := S) I q hq)

/-- Helper for Chap10 Lemma 10 99 11: the named quotient-localized base algebra is flat over
`R_(q ∩ R) / J`. -/
lemma localized_closed_fiber_base_algebra_flat
    (I : Ideal R) (q : PrimeSpectrum S) (hq : I.map (algebraMap R S) ≤ q.asIdeal) :
    let p : Ideal R := q.asIdeal.under R
    let Rp := Localization.AtPrime p
    let J : Ideal Rp := Ideal.map (algebraMap R Rp) I
    let IS : Ideal S := Ideal.map (algebraMap R S) I
    let Abar : Type u := R ⧸ I
    let Bbar : Type v := S ⧸ IS
    let hqbarPrime : (Ideal.map (Ideal.Quotient.mk IS) q.asIdeal).IsPrime :=
      localized_closed_fiber_quotient_prime_isPrime (R := R) (S := S) I q hq
    let qbar : PrimeSpectrum Bbar := ⟨Ideal.map (Ideal.Quotient.mk IS) q.asIdeal, hqbarPrime⟩
    letI : Algebra (Rp ⧸ J) (Localization.AtPrime (qbar.asIdeal.under Abar)) :=
      localized_closed_fiber_base_algebra (R := R) (S := S) I q hq
    Module.Flat (Rp ⧸ J) (Localization.AtPrime (qbar.asIdeal.under Abar)) := by
  -- Proof comment: the named algebra is exactly the witness chosen from the existing
  -- quotient-localized base flatness helper.
  simpa [localized_closed_fiber_base_algebra] using
    Classical.choose_spec (localized_closed_fiber_base_flat (R := R) (S := S) I q hq)

/-- Helper for Chap10 Lemma 10 99 11: the quotient `S_q ⧸ (IS)_q` is the localization of
`S ⧸ IS` at the quotient prime induced by `q`. -/
lemma localized_closed_fiber_target_quotient_isLocalization
    (I : Ideal R) (q : PrimeSpectrum S) (hq : I.map (algebraMap R S) ≤ q.asIdeal) :
    let IS : Ideal S := Ideal.map (algebraMap R S) I
    let Bbar : Type v := S ⧸ IS
    let Sq := Localization.AtPrime q.asIdeal
    let KqS : Ideal Sq := Ideal.map (algebraMap S Sq) IS
    let hqbarPrime : (Ideal.map (Ideal.Quotient.mk IS) q.asIdeal).IsPrime :=
      localized_closed_fiber_quotient_prime_isPrime (R := R) (S := S) I q hq
    let qbar : PrimeSpectrum Bbar := ⟨Ideal.map (Ideal.Quotient.mk IS) q.asIdeal, hqbarPrime⟩
    letI : Algebra Bbar (Sq ⧸ KqS) :=
      source_localized_quotient_target_algebra (A := S) (p := q.asIdeal) IS
    IsLocalization qbar.asIdeal.primeCompl (Sq ⧸ KqS) := by
  intro IS Bbar Sq KqS hqbarPrime qbar
  letI : Algebra Bbar (Sq ⧸ KqS) :=
    source_localized_quotient_target_algebra (A := S) (p := q.asIdeal) IS
  have hLocMap : IsLocalization (Submonoid.map (Ideal.Quotient.mk IS) q.asIdeal.primeCompl)
      (Sq ⧸ KqS) := by
    -- Proof comment: localizing `S` and then quotienting by `IS` descends through the
    -- surjective quotient map `S → S / IS`.
    refine IsLocalization.of_surjective q.asIdeal.primeCompl Sq
      (Ideal.Quotient.mk IS) Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk KqS) Ideal.Quotient.mk_surjective ?_ ?_
    · ext s
      rfl
    · intro x hx
      simpa [KqS, Ideal.mk_ker, IS] using hx
  have hprimeCompl :
      Submonoid.map (Ideal.Quotient.mk IS) q.asIdeal.primeCompl = qbar.asIdeal.primeCompl := by
    -- Proof comment: the image of the complement of `q` is the complement of the induced
    -- quotient prime.
    simpa [Bbar, qbar, hqbarPrime] using
      (quotient_primeCompl_eq_algebraMapSubmonoid_at_under
        (A := S) IS q.asIdeal (by simpa [IS] using hq))
  -- Proof comment: rewrite the source submonoid to the named quotient-prime complement.
  simpa [hprimeCompl] using hLocMap

/-- Helper for Chap10 Lemma 10 99 11: the concrete mapped-ideal quotient of `M_q` carries the
localized-base module structure induced by the closed-fiber localization map. -/
@[reducible]
noncomputable def localized_closed_fiber_mapped_target_module
    (I : Ideal R) (q : PrimeSpectrum S) (hq : I.map (algebraMap R S) ≤ q.asIdeal) :
    let IS : Ideal S := Ideal.map (algebraMap R S) I
    let Abar : Type u := R ⧸ I
    let Bbar : Type v := S ⧸ IS
    let Qbar : Type w := M ⧸ (IS • (⊤ : Submodule S M))
    let Sq := Localization.AtPrime q.asIdeal
    let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
    let KqS : Ideal Sq := Ideal.map (algebraMap S Sq) IS
    let TgtS := Mq ⧸ (KqS • (⊤ : Submodule Sq Mq))
    let hqbarPrime : (Ideal.map (Ideal.Quotient.mk IS) q.asIdeal).IsPrime :=
      localized_closed_fiber_quotient_prime_isPrime (R := R) (S := S) I q hq
    let qbar : PrimeSpectrum Bbar := ⟨Ideal.map (Ideal.Quotient.mk IS) q.asIdeal, hqbarPrime⟩
    Module (Localization.AtPrime (qbar.asIdeal.under Abar)) TgtS :=
  let IS : Ideal S := Ideal.map (algebraMap R S) I
  let Abar : Type u := R ⧸ I
  let Bbar : Type v := S ⧸ IS
  let Qbar : Type w := M ⧸ (IS • (⊤ : Submodule S M))
  let Sq := Localization.AtPrime q.asIdeal
  let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
  let KqS : Ideal Sq := Ideal.map (algebraMap S Sq) IS
  let TgtS := Mq ⧸ (KqS • (⊤ : Submodule Sq Mq))
  let hqbarPrime : (Ideal.map (Ideal.Quotient.mk IS) q.asIdeal).IsPrime :=
    localized_closed_fiber_quotient_prime_isPrime (R := R) (S := S) I q hq
  let qbar : PrimeSpectrum Bbar := ⟨Ideal.map (Ideal.Quotient.mk IS) q.asIdeal, hqbarPrime⟩
  let Lbase := Localization.AtPrime (qbar.asIdeal.under Abar)
  let Lqbar := Localization.AtPrime qbar.asIdeal
  letI : Algebra Bbar (Sq ⧸ KqS) :=
    source_localized_quotient_target_algebra (A := S) (p := q.asIdeal) IS
  letI : IsLocalization qbar.asIdeal.primeCompl (Sq ⧸ KqS) :=
    localized_closed_fiber_target_quotient_isLocalization (R := R) (S := S) I q hq
  let instQuotientModule : Module (Sq ⧸ KqS) TgtS := inferInstance
  letI : Module (Sq ⧸ KqS) TgtS := instQuotientModule
  let gBase : Lbase →+* Lqbar :=
    Localization.localRingHom (qbar.asIdeal.under Abar) qbar.asIdeal (algebraMap Abar Bbar) rfl
  let eTarget : Lqbar ≃ₐ[Bbar] (Sq ⧸ KqS) :=
    Localization.algEquiv qbar.asIdeal.primeCompl (Sq ⧸ KqS)
  let gTarget : Lbase →+* (Sq ⧸ KqS) := eTarget.toRingHom.comp gBase
  let instBaseAlg : Algebra Lbase (Sq ⧸ KqS) := gTarget.toAlgebra
  letI : Algebra Lbase (Sq ⧸ KqS) := instBaseAlg
  Module.compHom TgtS (algebraMap Lbase (Sq ⧸ KqS))

/-- Helper for Chap10 Lemma 10 99 11: the localized quotient closed fiber is equivalent over
`(S ⧸ IS)_qbar` to the concrete mapped-ideal quotient of `M_q`. -/
noncomputable def localized_closed_fiber_mapped_target_lqbarLinearEquiv
    (I : Ideal R) (q : PrimeSpectrum S) (hq : I.map (algebraMap R S) ≤ q.asIdeal) :
    let IS : Ideal S := Ideal.map (algebraMap R S) I
    let Abar : Type u := R ⧸ I
    let Bbar : Type v := S ⧸ IS
    let Qbar : Type w := M ⧸ (IS • (⊤ : Submodule S M))
    let Sq := Localization.AtPrime q.asIdeal
    let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
    let KqS : Ideal Sq := Ideal.map (algebraMap S Sq) IS
    let TgtS := Mq ⧸ (KqS • (⊤ : Submodule Sq Mq))
    let hqbarPrime : (Ideal.map (Ideal.Quotient.mk IS) q.asIdeal).IsPrime :=
      localized_closed_fiber_quotient_prime_isPrime (R := R) (S := S) I q hq
    let qbar : PrimeSpectrum Bbar := ⟨Ideal.map (Ideal.Quotient.mk IS) q.asIdeal, hqbarPrime⟩
    let Lqbar := Localization.AtPrime qbar.asIdeal
    letI : Algebra Bbar (Sq ⧸ KqS) :=
      source_localized_quotient_target_algebra (A := S) (p := q.asIdeal) IS
    letI : IsLocalization qbar.asIdeal.primeCompl (Sq ⧸ KqS) :=
      localized_closed_fiber_target_quotient_isLocalization (R := R) (S := S) I q hq
    let eTarget : Lqbar ≃ₐ[Bbar] (Sq ⧸ KqS) :=
      Localization.algEquiv qbar.asIdeal.primeCompl (Sq ⧸ KqS)
    letI : Algebra Lqbar (Sq ⧸ KqS) := eTarget.toAlgHom.toAlgebra
    letI : Module Lqbar TgtS :=
      Module.compHom TgtS (algebraMap Lqbar (Sq ⧸ KqS))
    LocalizedModule.AtPrime qbar.asIdeal Qbar ≃ₗ[Lqbar] TgtS :=
  let IS : Ideal S := Ideal.map (algebraMap R S) I
  let Abar : Type u := R ⧸ I
  let Bbar : Type v := S ⧸ IS
  let Qbar : Type w := M ⧸ (IS • (⊤ : Submodule S M))
  let Sq := Localization.AtPrime q.asIdeal
  let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
  let KqS : Ideal Sq := Ideal.map (algebraMap S Sq) IS
  let TgtS := Mq ⧸ (KqS • (⊤ : Submodule Sq Mq))
  let hqbarPrime : (Ideal.map (Ideal.Quotient.mk IS) q.asIdeal).IsPrime :=
    localized_closed_fiber_quotient_prime_isPrime (R := R) (S := S) I q hq
  let qbar : PrimeSpectrum Bbar := ⟨Ideal.map (Ideal.Quotient.mk IS) q.asIdeal, hqbarPrime⟩
  let Lqbar := Localization.AtPrime qbar.asIdeal
  let fB : Qbar →ₗ[Bbar] TgtS :=
    localized_closed_fiber_comparison_map (R := R) (S := S) (M := M) I q
  let instLocalized : IsLocalizedModule qbar.asIdeal.primeCompl fB :=
    localized_closed_fiber_comparison_isLocalizedModule (R := R) (S := S) (M := M) I q hq
  letI : Algebra Bbar (Sq ⧸ KqS) :=
    source_localized_quotient_target_algebra (A := S) (p := q.asIdeal) IS
  letI : IsLocalization qbar.asIdeal.primeCompl (Sq ⧸ KqS) :=
    localized_closed_fiber_target_quotient_isLocalization (R := R) (S := S) I q hq
  let instQuotientModule : Module (Sq ⧸ KqS) TgtS := inferInstance
  letI : Module (Sq ⧸ KqS) TgtS := instQuotientModule
  let eTarget : Lqbar ≃ₐ[Bbar] (Sq ⧸ KqS) :=
    Localization.algEquiv qbar.asIdeal.primeCompl (Sq ⧸ KqS)
  let instLqbarAlg : Algebra Lqbar (Sq ⧸ KqS) := eTarget.toAlgHom.toAlgebra
  letI : Algebra Lqbar (Sq ⧸ KqS) := instLqbarAlg
  let instLqbarModule : Module Lqbar TgtS :=
    Module.compHom TgtS (algebraMap Lqbar (Sq ⧸ KqS))
  letI : Module Lqbar TgtS := instLqbarModule
  let instBbarModule : Module Bbar TgtS :=
    Module.compHom TgtS (algebraMap Bbar (Sq ⧸ KqS))
  letI : Module Bbar TgtS := instBbarModule
  let instLqbarTowerTarget : IsScalarTower Bbar Lqbar TgtS :=
    isScalarTower_compHom_of_algebraMap_eq
      (A := Bbar) (B := Lqbar) (C := Sq ⧸ KqS) (N := TgtS)
      (algebraMap Lqbar (Sq ⧸ KqS)) eTarget.commutes
  letI : IsScalarTower Bbar Lqbar TgtS := instLqbarTowerTarget
  letI : IsLocalizedModule qbar.asIdeal.primeCompl fB := instLocalized
  IsLocalizedModule.mapEquiv qbar.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap qbar.asIdeal.primeCompl Qbar) fB Lqbar
    (LinearEquiv.refl Bbar Qbar)

/-- Helper for Chap10 Lemma 10 99 11: the localized quotient closed fiber is linearly equivalent
over the localized base to the concrete mapped-ideal quotient of `M_q`. -/
lemma localized_closed_fiber_mapped_target_linearEquiv
    (I : Ideal R) (q : PrimeSpectrum S) (hq : I.map (algebraMap R S) ≤ q.asIdeal) :
    let IS : Ideal S := Ideal.map (algebraMap R S) I
    let Abar : Type u := R ⧸ I
    let Bbar : Type v := S ⧸ IS
    let Qbar : Type w := M ⧸ (IS • (⊤ : Submodule S M))
    let Sq := Localization.AtPrime q.asIdeal
    let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
    let KqS : Ideal Sq := Ideal.map (algebraMap S Sq) IS
    let TgtS := Mq ⧸ (KqS • (⊤ : Submodule Sq Mq))
    let hqbarPrime : (Ideal.map (Ideal.Quotient.mk IS) q.asIdeal).IsPrime :=
      localized_closed_fiber_quotient_prime_isPrime (R := R) (S := S) I q hq
    let qbar : PrimeSpectrum Bbar := ⟨Ideal.map (Ideal.Quotient.mk IS) q.asIdeal, hqbarPrime⟩
    letI : Module (Localization.AtPrime (qbar.asIdeal.under Abar)) TgtS :=
      localized_closed_fiber_mapped_target_module (R := R) (S := S) (M := M) I q hq
    Nonempty
      (LocalizedModule.AtPrime qbar.asIdeal Qbar
        ≃ₗ[Localization.AtPrime (qbar.asIdeal.under Abar)] TgtS) := by
  intro IS Abar Bbar Qbar Sq Mq KqS TgtS hqbarPrime qbar
  let Lbase := Localization.AtPrime (qbar.asIdeal.under Abar)
  let Lqbar := Localization.AtPrime qbar.asIdeal
  letI : Algebra Bbar (Sq ⧸ KqS) :=
    source_localized_quotient_target_algebra (A := S) (p := q.asIdeal) IS
  letI : IsLocalization qbar.asIdeal.primeCompl (Sq ⧸ KqS) :=
    localized_closed_fiber_target_quotient_isLocalization (R := R) (S := S) I q hq
  let eTarget : Lqbar ≃ₐ[Bbar] (Sq ⧸ KqS) :=
    Localization.algEquiv qbar.asIdeal.primeCompl (Sq ⧸ KqS)
  let instLqbarAlg : Algebra Lqbar (Sq ⧸ KqS) := eTarget.toAlgHom.toAlgebra
  letI : Algebra Lqbar (Sq ⧸ KqS) := instLqbarAlg
  let instLqbarModule : Module Lqbar TgtS :=
    Module.compHom TgtS (algebraMap Lqbar (Sq ⧸ KqS))
  letI : Module Lqbar TgtS := instLqbarModule
  letI : SMul Lqbar TgtS := instLqbarModule.toSMul
  letI : DistribMulAction Lqbar TgtS := instLqbarModule.toDistribMulAction
  letI : MulAction Lqbar TgtS := instLqbarModule.toDistribMulAction.toMulAction
  let gBase : Lbase →+* Lqbar :=
    Localization.localRingHom (qbar.asIdeal.under Abar) qbar.asIdeal (algebraMap Abar Bbar) rfl
  letI : Algebra Lbase Lqbar := gBase.toAlgebra
  let instSourceBase : Module Lbase (LocalizedModule.AtPrime qbar.asIdeal Qbar) :=
    Module.compHom (LocalizedModule.AtPrime qbar.asIdeal Qbar) (algebraMap Lbase Lqbar)
  letI : Module Lbase (LocalizedModule.AtPrime qbar.asIdeal Qbar) := instSourceBase
  letI : SMul Lbase (LocalizedModule.AtPrime qbar.asIdeal Qbar) := instSourceBase.toSMul
  letI : DistribMulAction Lbase (LocalizedModule.AtPrime qbar.asIdeal Qbar) :=
    instSourceBase.toDistribMulAction
  letI : MulAction Lbase (LocalizedModule.AtPrime qbar.asIdeal Qbar) :=
    instSourceBase.toDistribMulAction.toMulAction
  let instTarget : Module Lbase TgtS :=
    localized_closed_fiber_mapped_target_module (R := R) (S := S) (M := M) I q hq
  letI : Module Lbase TgtS := instTarget
  letI : SMul Lbase TgtS := instTarget.toSMul
  letI : DistribMulAction Lbase TgtS := instTarget.toDistribMulAction
  letI : MulAction Lbase TgtS := instTarget.toDistribMulAction.toMulAction
  let eLq : LocalizedModule.AtPrime qbar.asIdeal Qbar ≃ₗ[Lqbar] TgtS :=
    localized_closed_fiber_mapped_target_lqbarLinearEquiv (R := R) (S := S) (M := M) I q hq
  have hmap_smul :
      ∀ (c : Lbase) (x : LocalizedModule.AtPrime qbar.asIdeal Qbar),
        eLq (c • x) = c • eLq x := by
    -- Proof comment: the `Lbase`-action on both sides is the pullback of the `Lqbar`-action.
    intro c x
    change eLq ((algebraMap Lbase Lqbar c) • x) =
      (algebraMap Lbase Lqbar c) • eLq x
    exact eLq.map_smul (algebraMap Lbase Lqbar c) x
  let f : LocalizedModule.AtPrime qbar.asIdeal Qbar →ₗ[Lbase] TgtS :=
    { toFun := eLq
      map_add' := eLq.map_add
      map_smul' := hmap_smul }
  have hleft : Function.LeftInverse eLq.symm f := by
    intro x
    exact eLq.left_inv x
  have hright : Function.RightInverse eLq.symm f := by
    intro x
    exact eLq.right_inv x
  -- Proof comment: assemble the base-linear equivalence from the cached `Lqbar`-linear map and
  -- its inverse function, avoiding another transported inverse-linear proof.
  exact ⟨LinearEquiv.mk f eLq.symm hleft hright⟩

/-- Helper for Chap10 Lemma 10 99 11: the localized closed fiber over the quotient base is flat
after replacing it by the concrete mapped-ideal quotient of `M_q`. -/
lemma localized_closed_fiber_flat_over_mapped_target_quotient
    (I : Ideal R) (q : PrimeSpectrum S) (hq : I.map (algebraMap R S) ≤ q.asIdeal)
    (hflatQ : Module.Flat (R ⧸ I)
      (M ⧸ ((Ideal.map (algebraMap R S) I) • (⊤ : Submodule S M)))) :
    let IS : Ideal S := Ideal.map (algebraMap R S) I
    let Abar : Type u := R ⧸ I
    let Bbar : Type v := S ⧸ IS
    let Qbar : Type w := M ⧸ (IS • (⊤ : Submodule S M))
    let Sq := Localization.AtPrime q.asIdeal
    let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
    let KqS : Ideal Sq := Ideal.map (algebraMap S Sq) IS
    let TgtS := Mq ⧸ (KqS • (⊤ : Submodule Sq Mq))
    let hqbarPrime : (Ideal.map (Ideal.Quotient.mk IS) q.asIdeal).IsPrime :=
      localized_closed_fiber_quotient_prime_isPrime (R := R) (S := S) I q hq
    let qbar : PrimeSpectrum Bbar := ⟨Ideal.map (Ideal.Quotient.mk IS) q.asIdeal, hqbarPrime⟩
    letI : Module (Localization.AtPrime (qbar.asIdeal.under Abar)) TgtS :=
      localized_closed_fiber_mapped_target_module (R := R) (S := S) (M := M) I q hq
    Module.Flat (Localization.AtPrime (qbar.asIdeal.under Abar)) TgtS := by
  intro IS Abar Bbar Qbar Sq Mq KqS TgtS hqbarPrime qbar
  let Lbase := Localization.AtPrime (qbar.asIdeal.under Abar)
  let instTarget : Module Lbase TgtS :=
    localized_closed_fiber_mapped_target_module (R := R) (S := S) (M := M) I q hq
  letI : Module Lbase TgtS := instTarget
  obtain ⟨eOwner⟩ : Nonempty (LocalizedModule.AtPrime qbar.asIdeal Qbar ≃ₗ[Lbase] TgtS) := by
    -- Proof comment: separate the owner equivalence from the flatness transfer so each
    -- declaration pays for one transport layer.
    simpa [IS, Abar, Bbar, Qbar, Sq, Mq, KqS, TgtS, hqbarPrime, qbar, Lbase] using
      localized_closed_fiber_mapped_target_linearEquiv (R := R) (S := S) (M := M) I q hq
  have hflatLoc : Module.Flat Lbase (LocalizedModule.AtPrime qbar.asIdeal Qbar) := by
    -- Proof comment: localizing the flat quotient closed fiber preserves flatness over the
    -- localized quotient base.
    simpa [Lbase, Qbar, Abar, Bbar] using
      flat_localized_closed_fiber_over_quotient_algebra
        (Abar := Abar) (Bbar := Bbar) (Qbar := Qbar) qbar
        (by simpa [Abar, Qbar, IS] using hflatQ)
  letI : Module.Flat Lbase (LocalizedModule.AtPrime qbar.asIdeal Qbar) := hflatLoc
  -- Proof comment: the localized-module universal property upgrades the owner comparison to a
  -- linear equivalence over `Bbar_qbar`, hence over the localized base.
  exact Module.Flat.of_linearEquiv eOwner.symm

/-- Helper for Chap10 Lemma 10 99 11: the localized-base map to the target quotient agrees,
after the explicit base equivalence, with the canonical quotient map
`R_(q ∩ R) ⧸ J → S_q ⧸ (IS)_q`. -/
lemma localized_closed_fiber_base_to_target_quotient_ringHom_eq
    (I : Ideal R) (q : PrimeSpectrum S) (hq : I.map (algebraMap R S) ≤ q.asIdeal) :
    let p : Ideal R := q.asIdeal.under R
    let Rp := Localization.AtPrime p
    let J : Ideal Rp := Ideal.map (algebraMap R Rp) I
    let IS : Ideal S := Ideal.map (algebraMap R S) I
    let Abar : Type u := R ⧸ I
    let Bbar : Type v := S ⧸ IS
    let Sq := Localization.AtPrime q.asIdeal
    let KqS : Ideal Sq := Ideal.map (algebraMap S Sq) IS
    let hqbarPrime : (Ideal.map (Ideal.Quotient.mk IS) q.asIdeal).IsPrime :=
      localized_closed_fiber_quotient_prime_isPrime (R := R) (S := S) I q hq
    let qbar : PrimeSpectrum Bbar := ⟨Ideal.map (Ideal.Quotient.mk IS) q.asIdeal, hqbarPrime⟩
    let Lbase := Localization.AtPrime (qbar.asIdeal.under Abar)
    let Lqbar := Localization.AtPrime qbar.asIdeal
    letI : Algebra Bbar (Sq ⧸ KqS) :=
      source_localized_quotient_target_algebra (A := S) (p := q.asIdeal) IS
    letI : IsLocalization qbar.asIdeal.primeCompl (Sq ⧸ KqS) :=
      localized_closed_fiber_target_quotient_isLocalization (R := R) (S := S) I q hq
    let gBase : Lbase →+* Lqbar :=
      Localization.localRingHom (qbar.asIdeal.under Abar) qbar.asIdeal (algebraMap Abar Bbar) rfl
    let eTarget : Lqbar ≃ₐ[Bbar] (Sq ⧸ KqS) :=
      Localization.algEquiv qbar.asIdeal.primeCompl (Sq ⧸ KqS)
    let gTarget : Lbase →+* (Sq ⧸ KqS) := eTarget.toRingHom.comp gBase
    let f : Rp →+* Sq := Localization.localRingHom p q.asIdeal (algebraMap R S) rfl
    letI : Algebra Rp Sq := f.toAlgebra
    ∀ (hJK : J ≤ Ideal.comap (algebraMap Rp Sq) KqS),
    letI : Algebra (Rp ⧸ J) (Sq ⧸ KqS) :=
      Ideal.Quotient.algebraQuotientOfLEComap hJK
    ∀ (eBase : Lbase ≃ₐ[Abar] (Rp ⧸ J)),
      (∀ r : R,
        eBase (algebraMap Abar Lbase (Ideal.Quotient.mk I r)) =
          Ideal.Quotient.mk J (algebraMap R Rp r)) →
      ∀ a : Rp ⧸ J,
        gTarget (eBase.symm a) = algebraMap (Rp ⧸ J) (Sq ⧸ KqS) a := by
  intro p Rp J IS Abar Bbar Sq KqS hqbarPrime qbar Lbase Lqbar
  intro gBase eTarget gTarget f hJK eBase hBase_mk a
  letI : Algebra Bbar (Sq ⧸ KqS) :=
    source_localized_quotient_target_algebra (A := S) (p := q.asIdeal) IS
  letI : IsLocalization qbar.asIdeal.primeCompl (Sq ⧸ KqS) :=
    localized_closed_fiber_target_quotient_isLocalization (R := R) (S := S) I q hq
  letI : Algebra Rp Sq := f.toAlgebra
  letI : Algebra (Rp ⧸ J) (Sq ⧸ KqS) :=
    Ideal.Quotient.algebraQuotientOfLEComap hJK
  have hRingL :
      gTarget = (algebraMap (Rp ⧸ J) (Sq ⧸ KqS)).comp eBase.toRingHom := by
    -- Proof comment: two maps out of the localized quotient base are equal once they agree on
    -- generators coming from `R`.
    apply IsLocalization.ringHom_ext (qbar.asIdeal.under Abar).primeCompl
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro r
    simp only [RingHom.comp_apply]
    calc
      gTarget (algebraMap Abar Lbase (Ideal.Quotient.mk I r)) =
          eTarget (gBase (algebraMap Abar Lbase (Ideal.Quotient.mk I r))) := rfl
      _ = eTarget (algebraMap Bbar Lqbar ((algebraMap Abar Bbar) (Ideal.Quotient.mk I r))) := by
        rw [Localization.localRingHom_to_map]
      _ = eTarget (algebraMap Bbar Lqbar (Ideal.Quotient.mk IS (algebraMap R S r))) := by
        rfl
      _ = Ideal.Quotient.mk KqS (algebraMap S Sq (algebraMap R S r)) := by
        rw [eTarget.commutes]
        simpa [source_localized_quotient_target_algebra] using
          Ideal.Quotient.algebraMap_quotient_map_quotient
            (p := IS) (S := Sq) (x := algebraMap R S r)
      _ = Ideal.Quotient.mk KqS (algebraMap Rp Sq (algebraMap R Rp r)) := by
        have hloc :
            algebraMap Rp Sq (algebraMap R Rp r) =
              algebraMap S Sq (algebraMap R S r) := by
          dsimp [RingHom.algebraMap_toAlgebra, f, Rp, Sq, p]
          exact
            Localization.localRingHom_to_map
              (I := q.asIdeal.under R) (J := q.asIdeal) (f := algebraMap R S) rfl r
        exact congrArg (Ideal.Quotient.mk KqS) hloc.symm
      _ = algebraMap (Rp ⧸ J) (Sq ⧸ KqS)
          (eBase (algebraMap Abar Lbase (Ideal.Quotient.mk I r))) := by
        rw [hBase_mk r]
        change Ideal.Quotient.mk KqS (algebraMap Rp Sq (algebraMap R Rp r)) =
          Ideal.quotientMap KqS (algebraMap Rp Sq) hJK
            (Ideal.Quotient.mk J (algebraMap R Rp r))
        rw [Ideal.quotientMap_mk]
      _ = ((algebraMap (Rp ⧸ J) (Sq ⧸ KqS)).comp eBase.toRingHom)
          (algebraMap Abar Lbase (Ideal.Quotient.mk I r)) := rfl
  -- Proof comment: evaluate the ring-hom equality at the inverse base equivalence.
  exact ringHom_comp_algEquiv_symm_apply eBase gTarget
    (algebraMap (Rp ⧸ J) (Sq ⧸ KqS)) hRingL a

/-- Helper for Chap10 Lemma 10 99 11: flatness over the mapped localized closed fiber transfers to
the canonical target quotient action over `R_(q ∩ R) ⧸ J`. -/
lemma localized_closed_fiber_flat_over_canonical_target_quotient
    (I : Ideal R) (q : PrimeSpectrum S) (hq : I.map (algebraMap R S) ≤ q.asIdeal) :
    let p : Ideal R := q.asIdeal.under R
    let Rp := Localization.AtPrime p
    let J : Ideal Rp := Ideal.map (algebraMap R Rp) I
    let IS : Ideal S := Ideal.map (algebraMap R S) I
    let Abar : Type u := R ⧸ I
    let Bbar : Type v := S ⧸ IS
    let Sq := Localization.AtPrime q.asIdeal
    let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
    let KqS : Ideal Sq := Ideal.map (algebraMap S Sq) IS
    let TgtS := Mq ⧸ (KqS • (⊤ : Submodule Sq Mq))
    let hqbarPrime : (Ideal.map (Ideal.Quotient.mk IS) q.asIdeal).IsPrime :=
      localized_closed_fiber_quotient_prime_isPrime (R := R) (S := S) I q hq
    let qbar : PrimeSpectrum Bbar := ⟨Ideal.map (Ideal.Quotient.mk IS) q.asIdeal, hqbarPrime⟩
    let Lbase := Localization.AtPrime (qbar.asIdeal.under Abar)
    letI : Module Lbase TgtS :=
      localized_closed_fiber_mapped_target_module (R := R) (S := S) (M := M) I q hq
    Module.Flat Lbase TgtS →
      let f : Rp →+* Sq := Localization.localRingHom p q.asIdeal (algebraMap R S) rfl
      letI : Algebra Rp Sq := f.toAlgebra
      ∀ (hJK : J ≤ Ideal.comap (algebraMap Rp Sq) KqS),
      letI : Algebra (Rp ⧸ J) (Sq ⧸ KqS) :=
        Ideal.Quotient.algebraQuotientOfLEComap hJK
      letI : Module (Sq ⧸ KqS) TgtS := inferInstance
      letI : Module (Rp ⧸ J) TgtS :=
        Module.compHom TgtS (algebraMap (Rp ⧸ J) (Sq ⧸ KqS))
      Module.Flat (Rp ⧸ J) TgtS := by
  intro p Rp J IS Abar Bbar Sq Mq KqS TgtS hqbarPrime qbar Lbase hflatTgtS_Lbase
  intro f hJK
  letI : Algebra Rp Sq := f.toAlgebra
  letI : Algebra (Rp ⧸ J) (Sq ⧸ KqS) :=
    Ideal.Quotient.algebraQuotientOfLEComap hJK
  let instQuotientModule : Module (Sq ⧸ KqS) TgtS := inferInstance
  letI : Module (Sq ⧸ KqS) TgtS := instQuotientModule
  let instTargetRpJ : Module (Rp ⧸ J) TgtS :=
    Module.compHom TgtS (algebraMap (Rp ⧸ J) (Sq ⧸ KqS))
  letI : Module (Rp ⧸ J) TgtS := instTargetRpJ
  let Lqbar := Localization.AtPrime qbar.asIdeal
  letI : Algebra Bbar (Sq ⧸ KqS) :=
    source_localized_quotient_target_algebra (A := S) (p := q.asIdeal) IS
  letI : IsLocalization qbar.asIdeal.primeCompl (Sq ⧸ KqS) :=
    localized_closed_fiber_target_quotient_isLocalization (R := R) (S := S) I q hq
  let gBase : Lbase →+* Lqbar :=
    Localization.localRingHom (qbar.asIdeal.under Abar) qbar.asIdeal (algebraMap Abar Bbar) rfl
  let eTarget : Lqbar ≃ₐ[Bbar] (Sq ⧸ KqS) :=
    Localization.algEquiv qbar.asIdeal.primeCompl (Sq ⧸ KqS)
  let gTarget : Lbase →+* (Sq ⧸ KqS) := eTarget.toRingHom.comp gBase
  have hflatTgtS_gTarget :
      letI : Module Lbase TgtS := Module.compHom TgtS gTarget
      Module.Flat Lbase TgtS := by
    -- Proof comment: expose the defining pullback map of the mapped-target module once.
    simpa [localized_closed_fiber_mapped_target_module, IS, Abar, Bbar, Sq, Mq, KqS,
      TgtS, hqbarPrime, qbar, Lbase, Lqbar, gBase, eTarget, gTarget] using
      hflatTgtS_Lbase
  let eBase : Lbase ≃ₐ[Abar] (Rp ⧸ J) := by
    letI : Algebra Abar (Rp ⧸ J) :=
      source_localized_quotient_target_algebra (A := R) (p := p) I
    let eBase0 :
        Localization (Algebra.algebraMapSubmonoid Abar p.primeCompl) ≃ₐ[Abar] (Rp ⧸ J) :=
      Localization.algEquiv (Algebra.algebraMapSubmonoid Abar p.primeCompl) (Rp ⧸ J)
    have hPrimeCompl :
        (qbar.asIdeal.under Abar).primeCompl = Algebra.algebraMapSubmonoid Abar p.primeCompl := by
      simpa [p, IS, Abar, Bbar, qbar, hqbarPrime] using
        localized_closed_fiber_base_primeCompl_eq (R := R) (S := S) I q hq
    -- Proof comment: identify the quotient-prime localization with the explicit source quotient.
    unfold Lbase Localization.AtPrime
    exact hPrimeCompl.symm ▸ eBase0
  letI : Algebra (Rp ⧸ J) Lbase := eBase.symm.toAlgHom.toAlgebra
  have hflatBase : Module.Flat (Rp ⧸ J) Lbase := by
    letI : Module (Rp ⧸ J) Lbase := Algebra.toModule
    let eAlg : Lbase ≃ₐ[Rp ⧸ J] (Rp ⧸ J) :=
      AlgEquiv.ofRingEquiv (R := Rp ⧸ J) (f := eBase.toRingEquiv) (by
        intro x
        change eBase (eBase.symm x) = x
        simp)
    letI : Module (Rp ⧸ J) (Rp ⧸ J) := Semiring.toModule
    letI : Module.Flat (Rp ⧸ J) (Rp ⧸ J) := Module.Flat.self (R := Rp ⧸ J)
    -- Proof comment: the explicit base equivalence gives flatness of `Lbase` over `Rp ⧸ J`.
    exact Module.Flat.of_linearEquiv eAlg.toLinearEquiv
  have hmapSquare :
      ∀ a : Rp ⧸ J,
        gTarget (eBase.symm a) =
          algebraMap (Rp ⧸ J) (Sq ⧸ KqS) a := by
    have hBase_mk :
        ∀ r : R,
          eBase (algebraMap Abar Lbase (Ideal.Quotient.mk I r)) =
            Ideal.Quotient.mk J (algebraMap R Rp r) := by
      -- Proof comment: evaluate the base equivalence on quotient-localization generators.
      intro r
      calc
        eBase (algebraMap Abar Lbase (Ideal.Quotient.mk I r)) =
            algebraMap Abar (Rp ⧸ J) (Ideal.Quotient.mk I r) := by
          exact eBase.commutes (Ideal.Quotient.mk I r)
        _ = Ideal.Quotient.mk J (algebraMap R Rp r) := by
          rfl
    -- Proof comment: the pure ring-map square is handled by the standalone extensionality lemma.
    exact
      localized_closed_fiber_base_to_target_quotient_ringHom_eq
        (R := R) (S := S) I q hq hJK eBase hBase_mk
  -- Proof comment: with the commuting square installed, flatness transports by transitivity.
  exact
    flat_compHom_of_flat_compHom_algebra
      (A := Rp ⧸ J) (B := Lbase) (C := Sq ⧸ KqS) (N := TgtS)
      (fA := algebraMap (Rp ⧸ J) (Sq ⧸ KqS)) (fB := gTarget)
      hmapSquare hflatBase hflatTgtS_gTarget

/-- Helper for Chap10 Lemma 10 99 11: flatness over the localized quotient base transfers across
the denominator comparison to the textbook closed fiber over `R_(q ∩ R) ⧸ J`. -/
lemma localized_closed_fiber_flat_over_target_quotient_from_mapped_target_core
    (I : Ideal R) (q : PrimeSpectrum S) (hq : I.map (algebraMap R S) ≤ q.asIdeal) :
    let p : Ideal R := q.asIdeal.under R
    let Rp := Localization.AtPrime p
    let J : Ideal Rp := Ideal.map (algebraMap R Rp) I
    let IS : Ideal S := Ideal.map (algebraMap R S) I
    let Abar : Type u := R ⧸ I
    let Bbar : Type v := S ⧸ IS
    let Sq := Localization.AtPrime q.asIdeal
    let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
    let KqS : Ideal Sq := Ideal.map (algebraMap S Sq) IS
    let TgtS := Mq ⧸ (KqS • (⊤ : Submodule Sq Mq))
    let hqbarPrime : (Ideal.map (Ideal.Quotient.mk IS) q.asIdeal).IsPrime :=
      localized_closed_fiber_quotient_prime_isPrime (R := R) (S := S) I q hq
    let qbar : PrimeSpectrum Bbar := ⟨Ideal.map (Ideal.Quotient.mk IS) q.asIdeal, hqbarPrime⟩
    let Lbase := Localization.AtPrime (qbar.asIdeal.under Abar)
    letI : Module Lbase TgtS :=
      localized_closed_fiber_mapped_target_module (R := R) (S := S) (M := M) I q hq
    Module.Flat Lbase TgtS →
      Module.Flat (Rp ⧸ J) (Mq ⧸ (J • (⊤ : Submodule Rp Mq))) := by
  intro p Rp J IS Abar Bbar Sq Mq KqS TgtS hqbarPrime qbar Lbase hflatTgtS_Lbase
  -- Route correction: instead of pulling the `Rp ⧸ J`-action back through `Lbase`, first install
  -- the canonical quotient-target action coming from `J ≤ comap KqS`.
  let f : Rp →+* Sq := Localization.localRingHom p q.asIdeal (algebraMap R S) rfl
  letI : Algebra Rp Sq := f.toAlgebra
  have hJK : J ≤ Ideal.comap (algebraMap Rp Sq) KqS := by
    -- Proof comment: the denominator ideal in `S_q` is the image of `J`, so `J` lies in its
    -- comap.
    simpa [p, Rp, Sq, J, IS, KqS, f] using
      localized_closed_fiber_source_ideal_le_target_comap (R := R) (S := S) I q
  have hdenom :
      ((KqS • (⊤ : Submodule Sq Mq)).restrictScalars Rp) =
        J • (⊤ : Submodule Rp Mq) := by
    -- Proof comment: replace the target denominator by the source-restricted denominator.
    simpa [p, Rp, Sq, Mq, J, IS, KqS, f] using
      localized_closed_fiber_denominator_restrictScalars_eq (R := R) (S := S) (M := M) I q
  letI : Algebra (Rp ⧸ J) (Sq ⧸ KqS) :=
    Ideal.Quotient.algebraQuotientOfLEComap hJK
  let instQuotientModule : Module (Sq ⧸ KqS) TgtS := inferInstance
  letI : Module (Sq ⧸ KqS) TgtS := instQuotientModule
  letI : SMul (Sq ⧸ KqS) TgtS := instQuotientModule.toSMul
  let instTargetRpJ : Module (Rp ⧸ J) TgtS :=
    Module.compHom TgtS (algebraMap (Rp ⧸ J) (Sq ⧸ KqS))
  letI : Module (Rp ⧸ J) TgtS := instTargetRpJ
  letI : SMul (Rp ⧸ J) TgtS := instTargetRpJ.toSMul
  letI : DistribMulAction (Rp ⧸ J) TgtS := instTargetRpJ.toDistribMulAction
  letI : MulAction (Rp ⧸ J) TgtS := instTargetRpJ.toDistribMulAction.toMulAction
  have hsourceTower : IsScalarTower Rp (Rp ⧸ J) TgtS := by
    -- Proof comment: the canonical quotient-target action has the source scalar tower by the
    -- generic quotient-target lemma.
    simpa using
      quotient_target_isScalarTower_of_le_comap
        (A := Rp) (B := Sq) (N := Mq) J KqS hJK
  letI : IsScalarTower Rp (Rp ⧸ J) TgtS := hsourceTower
  have hflatTgtS_RpJ : Module.Flat (Rp ⧸ J) TgtS := by
    -- Proof comment: package the quotient-localization owner transfer in a fresh declaration
    -- budget; this proof only passes the canonical denominator containment.
    exact
      localized_closed_fiber_flat_over_canonical_target_quotient
        (R := R) (S := S) (M := M) I q hq hflatTgtS_Lbase hJK
  -- Proof comment: finally transfer flatness across the equality between the target denominator
  -- and the source denominator.
  exact
    flat_of_target_denominator_linearEquiv_of_sourceTower
      (A := Rp) (B := Sq) (N := Mq) J KqS hdenom hsourceTower hflatTgtS_RpJ

/-- Helper for Lemma 10.99.11: after transporting the localized closed fiber along the quotient
ring and module identifications, the target quotient `M_q / J M_q` is flat over `R_(q ∩ R) / J`.
-/
lemma localized_closed_fiber_flat_over_target_quotient
    (I : Ideal R) (q : PrimeSpectrum S) (hq : I.map (algebraMap R S) ≤ q.asIdeal)
    (hflatQ : Module.Flat (R ⧸ I)
      (M ⧸ ((Ideal.map (algebraMap R S) I) • (⊤ : Submodule S M)))) :
    let p : Ideal R := q.asIdeal.under R
    let Rp := Localization.AtPrime p
    let J : Ideal Rp := Ideal.map (algebraMap R Rp) I
    let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
    Module.Flat (Rp ⧸ J) (Mq ⧸ (J • (⊤ : Submodule Rp Mq))) := by
  intro p Rp J Mq
  let IS : Ideal S := Ideal.map (algebraMap R S) I
  let Abar : Type u := R ⧸ I
  let Bbar : Type v := S ⧸ IS
  let Qbar : Type w := M ⧸ (IS • (⊤ : Submodule S M))
  let Sq := Localization.AtPrime q.asIdeal
  let KqS : Ideal Sq := Ideal.map (algebraMap S Sq) IS
  let TgtS := Mq ⧸ (KqS • (⊤ : Submodule Sq Mq))
  let hqbarPrime : (Ideal.map (Ideal.Quotient.mk IS) q.asIdeal).IsPrime :=
    localized_closed_fiber_quotient_prime_isPrime (R := R) (S := S) I q hq
  let qbar : PrimeSpectrum Bbar := ⟨Ideal.map (Ideal.Quotient.mk IS) q.asIdeal, hqbarPrime⟩
  let Lbase := Localization.AtPrime (qbar.asIdeal.under Abar)
  let instTarget : Module Lbase TgtS :=
    localized_closed_fiber_mapped_target_module (R := R) (S := S) (M := M) I q hq
  letI : Module Lbase TgtS := instTarget
  have hflatTgtS_Lbase : Module.Flat Lbase TgtS := by
    -- Proof comment: consume the localized-module comparison lemma in the concrete notation used
    -- by the target.
    simpa [IS, Abar, Bbar, Qbar, Sq, Mq, KqS, TgtS, hqbarPrime, qbar, Lbase] using
      localized_closed_fiber_flat_over_mapped_target_quotient
        (R := R) (S := S) (M := M) I q hq hflatQ
  -- Proof comment: delegate the base-flatness and denominator-transfer part to the smaller
  -- helper so this declaration does not re-elaborate all scalar-owner plumbing.
  simpa [p, Rp, J, IS, Abar, Bbar, Sq, Mq, KqS, TgtS, hqbarPrime, qbar, Lbase] using
    localized_closed_fiber_flat_over_target_quotient_from_mapped_target_core
      (R := R) (S := S) (M := M) I q hq hflatTgtS_Lbase

end
