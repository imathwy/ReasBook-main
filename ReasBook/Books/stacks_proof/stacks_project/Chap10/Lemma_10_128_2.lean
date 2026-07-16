import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_60_10
import stacks_proof.stacks_project.Chap10.Lemma_10_99_10_Variant_of_the_local_criterion
import stacks_proof.stacks_project.Chap10.Lemma_10_100_2
import stacks_proof.stacks_project.Chap10.Lemma_10_106_3
import stacks_proof.stacks_project.Chap10.Lemma_10_106_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory CategoryTheory.Limits
open RingTheory Sequence IsLocalRing
open scoped Pointwise TensorProduct

noncomputable section

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsRegularLocalRing R] [IsLocalRing S] [IsNoetherianRing S]
variable [IsLocalHom (algebraMap R S)]

/- Domain-style sampling pass.
* primary domain: local commutative algebra of flat local homomorphisms out of a regular local
  ring, detected by the image of a regular system of parameters;
* sampled owner declarations:
  `IsRegularSystemOfParameters`,
  `IsRegularSystemOfParameters.isRegular`,
  `IsRegularSystemOfParameters.isRegularLocalRing_quotient_parameterIdeal`,
  `flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal`;
* best owner abstraction: the source-facing primitive datum is the chosen family
  `x : Fin d → maximalIdeal R` together with `hx : IsRegularSystemOfParameters x`; the list
  `List.ofFn fun i ↦ algebraMap R S (x i : R)` is only the bridge/view presenting the induced
  sequence in `S`, while the conclusion belongs on the canonical flatness owner `Module.Flat R S`.
* primitive data: the local map `R → S`, the regular-local owner on `R`, the Noetherian-local
  owner on `S`, the chosen regular system of parameters `x`, and regularity of its image in `S`;
* derived API: regularity of the underlying sequence in `R` from `hx.isRegular`, the regular-local
  prefix quotients from
  `IsRegularSystemOfParameters.isRegularLocalRing_quotient_parameterIdeal`, and the inductive
  flatness step furnished by `flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal`.

Source/core/bridge triage:
* source-facing: Lemma `10.128.2` itself;
* core/canonical: `IsRegularSystemOfParameters`, `Sequence.IsRegular`, and `Module.Flat`;
* bridge/view: the `List.ofFn` presentation of the image sequence in `S`.
-/

-- Proof sketch: let `d = ringKrullDim R`, and write the chosen regular system of parameters as
-- `x₁, …, x_d`. Since `R / (x₁, …, x_d)` is a field, the final quotient of `S` is flat over the
-- final quotient of `R`. Then apply
-- `flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal` inductively up the regular sequence,
-- using at each step that the next parameter is a nonzerodivisor on the corresponding quotient of
-- `S`.

/-- Helper for Lemma 10.128.2: on a commutative ring, scalar-regularity on the regular module
recovers regularity of the underlying ring element. -/
lemma isRegular_of_isSMulRegular_self
    {A : Type u} [CommRing A] {a : A} (h : IsSMulRegular A a) :
    IsRegular a := by
  -- Proof comment: for the regular module over a commutative ring, scalar multiplication is
  -- multiplication in the ring.
  rw [isSMulRegular_iff_right_eq_zero_of_smul] at h
  rw [isRegular_iff_mem_nonZeroDivisors, mem_nonZeroDivisors_iff_left]
  simpa [Algebra.smul_def, mul_comm] using h

/-- Helper for Lemma 10.128.2: ordinary regularity of a ring element is the same as
scalar-regularity on the regular module. -/
lemma isSMulRegular_self_of_isRegular
    {A : Type u} [CommRing A] {a : A} (h : IsRegular a) :
    IsSMulRegular A a := by
  rw [isSMulRegular_iff_right_eq_zero_of_smul]
  rw [isRegular_iff_mem_nonZeroDivisors, mem_nonZeroDivisors_iff_left] at h
  simpa [Algebra.smul_def, mul_comm] using h

/-- Helper for Lemma 10.128.2: regularity is preserved when a regular sequence is transported
across a ring equivalence. -/
lemma isRegular_map_iff_of_ringEquiv
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (e : A ≃+* B) (rs : List A) :
    Sequence.IsRegular A rs ↔ Sequence.IsRegular B (rs.map e) := by
  -- Proof comment: for self-modules, compatibility with scalar multiplication is exactly
  -- preservation of multiplication.
  refine e.toAddEquiv.isRegular_congr <| List.forall₂_map_right_iff.mpr ?_
  rw [List.forall₂_same]
  intro a ha x
  simpa [Algebra.smul_def] using e.map_mul a x

/-- Helper for Lemma 10.128.2: the owner quotient module `QuotSMulTop r A` is equivalent to the
principal quotient ring for regularity questions on the tail. -/
lemma isRegular_quotSMulTop_iff_quotient_span_singleton
    {A : Type u} [CommRing A] {r : A} {rs : List A} :
    Sequence.IsRegular (QuotSMulTop r A) rs ↔
      Sequence.IsRegular (A ⧸ Ideal.span ({r} : Set A))
        (rs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set A)))) := by
  have hspan : Ideal.span ({r} : Set A) = r • (⊤ : Ideal A) := by
    -- Proof comment: the principal ring quotient is the same additive quotient as `A / rA`.
    simpa using (Submodule.ideal_span_singleton_smul (R := A) (M := A) r (⊤ : Submodule A A))
  let e : QuotSMulTop r A ≃+ A ⧸ Ideal.span ({r} : Set A) :=
    (Ideal.quotientEquivAlgOfEq A hspan).symm.toRingEquiv.toAddEquiv
  -- Proof comment: transport regularity across the quotient equivalence while mapping scalars.
  refine e.isRegular_congr <| List.forall₂_map_right_iff.mpr ?_
  rw [List.forall₂_same]
  intro a ha x
  change e (a • x) = Ideal.Quotient.mk (Ideal.span ({r} : Set A)) a • e x
  rcases Quotient.exists_rep x with ⟨y, rfl⟩
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  simp [e, smul_eq_mul]

/-- Helper for Lemma 10.128.2: quotienting by the head parameter of a regular system of
parameters leaves a regular system of parameters on the tail. -/
lemma head_quotient_tail_isRegularSystemOfParameters {d : ℕ}
    {x : Fin (d + 1) → maximalIdeal R} (hx : IsRegularSystemOfParameters x) :
    let R' := R ⧸ headParameterIdeal x
    letI : Nontrivial R' := Ideal.Quotient.nontrivial_iff.mpr (headParameterIdeal_ne_top x)
    letI : IsLocalRing R' :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (headParameterIdeal x))
        Ideal.Quotient.mk_surjective
    IsRegularSystemOfParameters (head_quotient_tail x) := by
  let R' := R ⧸ headParameterIdeal x
  letI : Nontrivial R' := Ideal.Quotient.nontrivial_iff.mpr (headParameterIdeal_ne_top x)
  letI : IsLocalRing R' :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (headParameterIdeal x))
      Ideal.Quotient.mk_surjective
  have hparameter :
      parameterIdeal (head_quotient_tail x) = maximalIdeal R' := by
    -- Proof comment: modding out by the head generator kills only that generator and sends the
    -- full parameter ideal to the maximal ideal downstairs.
    calc
      parameterIdeal (head_quotient_tail x) =
          Ideal.map (Ideal.Quotient.mk (headParameterIdeal x)) (parameterIdeal x) := by
            symm
            simpa [head_quotient_tail] using
              map_parameterIdeal_eq_tail_parameterIdeal (A := R) x
      _ = Ideal.map (Ideal.Quotient.mk (headParameterIdeal x)) (maximalIdeal R) := by
            rw [hx.2]
      _ = maximalIdeal R' := by
            exact IsLocalRing.map_maximalIdeal_of_surjective
              (Ideal.Quotient.mk (headParameterIdeal x)) Ideal.Quotient.mk_surjective
  have hdim : ringKrullDim R' = d := by
    -- Proof comment: the one-step quotient theorem packages the dimension drop.
    simpa [R', headParameterIdeal] using
      (head_parameter_quotient_regular_local_and_dim (R := R) (x := x) hx).2
  -- Proof comment: the quotient tail satisfies the defining dimension and maximal-ideal clauses.
  exact
    (isRegularSystemOfParameters_iff_of_ringKrullDim_eq (R := R') hdim (head_quotient_tail x)).2
      hparameter

omit [IsLocalRing S] [IsNoetherianRing S] [IsLocalHom (algebraMap R S)] in
/-- Helper for Lemma 10.128.2: mapping the head-parameter ideal to the target ring gives the
principal ideal generated by the image of the head parameter. -/
lemma mapped_headParameterIdeal_eq_span_singleton {d : ℕ}
    (x : Fin (d + 1) → maximalIdeal R) :
    Ideal.map (algebraMap R S) (headParameterIdeal x) =
      Ideal.span ({algebraMap R S (x 0 : R)} : Set S) := by
  -- Proof comment: `headParameterIdeal x` is already the principal ideal generated by the head.
  rw [headParameterIdeal, Ideal.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact Set.mem_singleton _
  · intro hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact ⟨(x 0 : R), Set.mem_singleton _, rfl⟩

omit [IsLocalRing S] [IsNoetherianRing S] [IsLocalHom (algebraMap R S)] in
/-- Helper for Lemma 10.128.2: regularity of the image sequence descends to the quotient by the
head parameter, stated on the canonical quotient by the mapped ideal. -/
lemma image_tail_isRegular_on_head_quotient {d : ℕ}
    (x : Fin (d + 1) → maximalIdeal R)
    (hreg : Sequence.IsRegular S (List.ofFn fun i ↦ algebraMap R S (x i : R))) :
    let I : Ideal R := headParameterIdeal x
    let J : Ideal S := Ideal.map (algebraMap R S) I
    Sequence.IsRegular (S ⧸ J)
      (List.ofFn fun i : Fin d ↦
        Ideal.Quotient.mk J (algebraMap R S (x i.succ : R))) := by
  let a : S := algebraMap R S (x 0 : R)
  let rs : List S := List.ofFn fun i : Fin d ↦ algebraMap R S (x i.succ : R)
  let I : Ideal R := headParameterIdeal x
  let J : Ideal S := Ideal.map (algebraMap R S) I
  have hlist :
      List.ofFn (fun i : Fin (d + 1) ↦ algebraMap R S (x i : R)) = a :: rs := by
    -- Proof comment: `List.ofFn_cons` splits the image sequence into its head and successor tail.
    simpa [a, rs] using
      (List.ofFn_cons (algebraMap R S (x 0 : R))
        (fun i : Fin d ↦ algebraMap R S (x i.succ : R)))
  rw [hlist] at hreg
  rcases (isRegular_cons_iff (M := S) a rs).1 hreg with ⟨ha, htail⟩
  have hquot_span :
      Sequence.IsRegular (S ⧸ Ideal.span ({a} : Set S))
        (rs.map (Ideal.Quotient.mk (Ideal.span ({a} : Set S)))) := by
    -- Proof comment: the tail is regular on the quotient by the head image.
    exact
      (isRegular_quotSMulTop_iff_quotient_span_singleton (A := S) (r := a) (rs := rs)).1 htail
  have hmap :
      J = Ideal.span ({a} : Set S) := by
    -- Proof comment: the target quotient model is the mapped head ideal, which is principal.
    simpa [a, I, J] using mapped_headParameterIdeal_eq_span_singleton (R := R) (S := S) x
  let e : (S ⧸ Ideal.span ({a} : Set S)) ≃+* (S ⧸ J) :=
    (Ideal.quotientEquivAlgOfEq S hmap.symm).toRingEquiv
  have htransport :
      Sequence.IsRegular (S ⧸ J)
        ((rs.map (Ideal.Quotient.mk (Ideal.span ({a} : Set S)))).map e) := by
    -- Proof comment: transport the quotient-tail regularity across the single quotient equivalence.
    exact (isRegular_map_iff_of_ringEquiv e _).1 hquot_span
  simpa [a, rs, I, J, hmap] using htransport

/-- Helper for Lemma 10.128.2: quotienting a lifted module by `J • ⊤` is canonically the same as
quotienting the original module by `J • ⊤`. -/
lemma ulift_module_quotient_equiv_exists
    {A : Type u} [CommRing A] {J : Ideal A}
    {N : Type v} [AddCommGroup N] [Module A N] :
    Nonempty ((((ULift.{u} N) ⧸ (J • (⊤ : Submodule A (ULift.{u} N)))) ≃ₗ[A ⧸ J]
      (N ⧸ (J • (⊤ : Submodule A N))))) := by
  let eA :
      ((ULift.{u} N) ⧸ (J • (⊤ : Submodule A (ULift.{u} N)))) ≃ₗ[A]
        (N ⧸ (J • (⊤ : Submodule A N))) :=
    Submodule.Quotient.equiv
      (J • (⊤ : Submodule A (ULift.{u} N)))
      (J • (⊤ : Submodule A N))
      (ULift.moduleEquiv : ULift.{u} N ≃ₗ[A] N)
      (by
        -- Proof comment: `ULift.moduleEquiv` preserves the quotient denominator `J • ⊤`.
        simpa [Submodule.map_smul''])
  -- Proof comment: both quotient modules carry the canonical `A ⧸ J`-action.
  exact ⟨eA.extendScalarsOfSurjective Ideal.Quotient.mk_surjective⟩

/-- Helper for Lemma 10.128.2: choose the quotient-module equivalence induced by
`ULift.moduleEquiv`. -/
noncomputable def ulift_module_quotient_equiv
    {A : Type u} [CommRing A] {J : Ideal A}
    {N : Type v} [AddCommGroup N] [Module A N] :
    ((ULift.{u} N) ⧸ (J • (⊤ : Submodule A (ULift.{u} N)))) ≃ₗ[A ⧸ J]
      (N ⧸ (J • (⊤ : Submodule A N))) :=
  Classical.choice ulift_module_quotient_equiv_exists

/-- Helper for Lemma 10.128.2: regularity of `f` on both the source ring and a same-universe
module forces the principal quotient `Tor₁` to vanish. -/
lemma tor_one_module_quotient_by_regular_element_vanishes
    {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M]
    (f : A) (hfA : IsRegular f) (hfM : IsSMulRegular M f) :
    IsZero ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
      (ModuleCat.of A (A ⧸ Ideal.span ({f} : Set A))))) := by
  let _ := hfM
  let I : Ideal A := Ideal.span ({f} : Set A)
  let φ : A →ₗ[A] I :=
    { toFun := fun a ↦ ⟨a * f, (Ideal.mem_span_singleton').2 ⟨a, rfl⟩⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        simpa [add_mul]
      map_smul' := by
        intro a b
        apply Subtype.ext
        simp [mul_left_comm, mul_comm] }
  let hspan : A ≃ₗ[A] I := by
    -- Proof comment: multiplication by `f` identifies `A` with the principal ideal `(f)`,
    -- because every element of `(f)` is a multiple of `f` and `f` acts injectively on `A`.
    refine LinearEquiv.ofBijective φ ?_
    constructor
    · intro a b hab
      apply Subtype.ext_iff.mp at hab
      exact hfA.right hab
    · intro x
      rcases (Ideal.mem_span_singleton').1 x.2 with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      apply Subtype.ext_iff.mpr
      simpa [φ] using ha
  let μ : I ⊗[A] M →ₗ[A] M :=
    TensorProduct.lift ((LinearMap.lsmul A M).comp I.subtype)
  let e : I ⊗[A] M ≃ₗ[A] A ⊗[A] M :=
    TensorProduct.congr hspan.symm (LinearEquiv.refl A M)
  have hμ :
      μ =
        (LinearMap.lsmul A M f).comp
          ((TensorProduct.lid A M).toLinearMap.comp e.toLinearMap) := by
    -- Proof comment: after identifying `(f)` with `A`, the tensor multiplication map is exactly
    -- multiplication by `f` on `M`.
    ext a m
    change a.1 • m = f • ((hspan.symm a : A) • m)
    rw [← mul_smul]
    have ha : (hspan.symm a : A) * f = a.1 := by
      exact congrArg Subtype.val (hspan.apply_symm_apply a)
    calc
      a.1 • m = ((hspan.symm a : A) * f) • m := by simpa [ha]
      _ = (f * hspan.symm a) • m := by rw [mul_comm]
  have hμ_injective : Function.Injective μ := by
    rw [hμ]
    exact hfM.comp ((TensorProduct.lid A M).injective.comp e.injective)
  have hker : LinearMap.ker μ = ⊥ := by
    exact LinearMap.ker_eq_bot.mpr hμ_injective
  -- Proof comment: the principal-ideal kernel now vanishes, so Remark `10.75.9` kills the Tor
  -- owner itself.
  simpa [I] using
    tor_one_module_quotient_vanishes_of_ker_eq_bot (A := A) (I := I) (N := M) hker

/-- Helper for Lemma 10.128.2: quotienting by the image ideal in a `ULift` ring recovers the
original quotient ring. -/
lemma ulift_quotient_ring_equiv_aux
    {A : Type u} [CommRing A] (K : Ideal A) :
    K =
      (K.map (algebraMap A (ULift.{v} A))).map
        ((ULift.algEquiv (R := A) (A := A) : ULift.{v} A ≃ₐ[A] A) : ULift.{v} A →+* A) := by
  let eu : ULift.{v} A ≃ₐ[A] A := ULift.algEquiv (R := A) (A := A)
  calc
    K = K.map (RingHom.id A) := by simp
    _ = K.map ((eu : ULift.{v} A →+* A).comp (algebraMap A (ULift.{v} A))) := by
          ext a
          rfl
    _ = (K.map (algebraMap A (ULift.{v} A))).map (eu : ULift.{v} A →+* A) := by
          rw [Ideal.map_map]

/-- Helper for Lemma 10.128.2: the canonical `ULift` presentation of a quotient ring is
ring-equivalent to the original quotient ring. -/
noncomputable def ulift_quotient_ring_equiv
    {A : Type u} [CommRing A] (K : Ideal A) :
    ((ULift.{v} A) ⧸ K.map (algebraMap A (ULift.{v} A))) ≃+* (A ⧸ K) :=
  (Ideal.quotientEquivAlg _ _ (ULift.algEquiv (R := A) (A := A))
    (ulift_quotient_ring_equiv_aux (A := A) K)).toRingEquiv

/-- Helper for Lemma 10.128.2: the `ULift` of a local homomorphism is again local. -/
lemma ringHom_ulift_isLocalHom
    {A : Type u} {B : Type v} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (g : A →+* B) [IsLocalHom g] :
    IsLocalHom (RingHom.ulift g) := by
  letI : IsLocalRing (ULift A) :=
    by
      exact IsLocalRing.of_surjective'
        (ULift.ringEquiv.symm.toRingHom : A →+* ULift A)
        (by
          intro x
          exact ⟨ULift.down x, by cases x; rfl⟩)
  letI : IsLocalRing (ULift B) :=
    by
      exact IsLocalRing.of_surjective'
        (ULift.ringEquiv.symm.toRingHom : B →+* ULift B)
        (by
          intro x
          exact ⟨ULift.down x, by cases x; rfl⟩)
  letI : IsLocalHom (ULift.ringEquiv.toRingHom : ULift A →+* A) :=
    Function.Surjective.isLocalHom _ ULift.ringEquiv.surjective
  letI : IsLocalHom (ULift.ringEquiv.symm.toRingHom : B →+* ULift B) :=
    Function.Surjective.isLocalHom _ ULift.ringEquiv.symm.surjective
  -- Proof comment: the lifted map is the original local map conjugated by the two canonical
  -- `ULift` ring equivalences.
  simpa [RingHom.ulift] using
    (RingHom.isLocalHom_comp (ULift.ringEquiv.symm.toRingHom)
      (g.comp ULift.ringEquiv.toRingHom))

/-- Helper for Lemma 10.128.2: a principal-quotient flatness step can be checked after lifting the
source ring and target ring to a common universe. -/
lemma flat_of_regular_element_and_flat_mod_ideal_self_univ
    (f : R) (hI : Ideal.span ({f} : Set R) ≠ ⊤)
    (hf_source : IsRegular f) (hf_target : IsSMulRegular S f)
    (hflat :
      Module.Flat (R ⧸ Ideal.span ({f} : Set R))
        (S ⧸ (Ideal.span ({f} : Set R) • (⊤ : Submodule R S)))) :
    Module.Flat R S := by
  let I : Ideal R := Ideal.span ({f} : Set R)
  let Ru : Type max u v := ULift.{v} R
  let Su : Type max u v := ULift.{u} S
  let fu : Ru := algebraMap R Ru f
  let Iu : Ideal Ru := Ideal.map (algebraMap R Ru) I
  let Tu : Type max u v := Ru ⧸ Iu
  let B : Type u := R ⧸ I
  let eRing : Tu ≃+* B := ulift_quotient_ring_equiv (A := R) I
  let _ : Algebra R Su := ULift.algebra
  let _ : Algebra Ru Su := ULift.algebra' R Su
  letI : IsRegularLocalRing Ru := by
    exact IsRegularLocalRing.of_ringEquiv (R := R) (ULift.ringEquiv : Ru ≃+* R).symm
  letI : IsLocalRing Su := by
    exact IsLocalRing.of_surjective'
      (ULift.ringEquiv.symm.toRingHom : S →+* Su)
      (by
        intro x
        exact ⟨ULift.down x, by cases x; rfl⟩)
  letI : IsNoetherianRing Ru := by
    exact isNoetherianRing_of_ringEquiv R (ULift.ringEquiv : Ru ≃+* R).symm
  letI : IsNoetherianRing Su := by
    exact isNoetherianRing_of_ringEquiv S (ULift.ringEquiv : Su ≃+* S).symm
  letI : IsLocalHom (algebraMap Ru Su) := by
    simpa [Ru, Su] using ringHom_ulift_isLocalHom (g := algebraMap R S)
  have hsurjRu : Function.Surjective (algebraMap R Ru) := by
    intro x
    rcases x with ⟨x⟩
    exact ⟨x, rfl⟩
  have hIu : Iu ≠ ⊤ := by
    let _ : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr hI
    let _ : Nontrivial Tu := eRing.toEquiv.nontrivial
    exact Ideal.Quotient.nontrivial_iff.mp inferInstance
  letI : Algebra Ru R := (ULift.ringEquiv : Ru ≃+* R).toRingHom.toAlgebra
  letI : Module Ru S := Module.compHom S (algebraMap Ru R)
  have hf_source_Ru_on_R : IsSMulRegular R fu := by
    -- Proof comment: via the canonical map `Ru → R`, the lifted source element acts as `f`.
    simpa [fu] using isSMulRegular_self_of_isRegular (A := R) hf_source
  have hf_source_Ru : IsSMulRegular Ru fu := by
    let eRu : Ru ≃ₗ[Ru] R := ULift.moduleEquiv
    exact (LinearEquiv.isSMulRegular_congr eRu fu).2 hf_source_Ru_on_R
  have hfRu : IsRegular fu := isRegular_of_isSMulRegular_self hf_source_Ru
  have hf_target_Ru_on_S : IsSMulRegular S fu := by
    -- Proof comment: after restricting scalars along `Ru → R`, the lifted source element still
    -- acts as the original `f` on `S`.
    simpa [fu] using hf_target
  have hfSu : IsSMulRegular Su fu := by
    let eSu : Su ≃ₗ[Ru] S := ULift.moduleEquiv
    exact (LinearEquiv.isSMulRegular_congr eSu fu).2 hf_target_Ru_on_S
  have hIu_eq : Iu = Ideal.span ({fu} : Set Ru) := by
    simpa [Iu, I, fu, Ideal.map_span, Set.image_singleton]
  have hTor_u :
      IsZero (Tor₁[Ru](Su, Ru ⧸ Iu)) := by
    -- Proof comment: in the common-universe model, the already proved same-universe principal
    -- quotient vanishing theorem applies directly.
    rw [hIu_eq]
    exact
      tor_one_module_quotient_by_regular_element_vanishes
        (A := Ru) (M := Su) fu hfRu hfSu
  letI : Algebra Tu B := eRing.toRingHom.toAlgebra
  letI : Module Tu (S ⧸ (I • (⊤ : Submodule R S))) :=
    Module.compHom (S ⧸ (I • (⊤ : Submodule R S))) (algebraMap Tu B)
  letI : IsScalarTower R Tu (S ⧸ (I • (⊤ : Submodule R S))) :=
    IsScalarTower.of_compHom R Tu (S ⧸ (I • (⊤ : Submodule R S)))
  letI : IsScalarTower Tu B (S ⧸ (I • (⊤ : Submodule R S))) :=
    IsScalarTower.of_compHom Tu B (S ⧸ (I • (⊤ : Submodule R S)))
  have hIu_restrict :
      ((Iu • (⊤ : Submodule Ru Su)).restrictScalars R) =
        (I • (⊤ : Submodule R Su)) := by
    -- Proof comment: restricting the lifted denominator from `Ru` back to `R` recovers the
    -- original denominator generated by `f`.
    simpa [Iu] using
      (Ideal.smul_restrictScalars
        (R := R) (S := Ru) (M := Su) (I := I) (N := (⊤ : Submodule Ru Su)))
  have hsurjRT : Function.Surjective (algebraMap R Tu) := by
    -- Proof comment: every quotient class upstairs has a representative coming from `R`, because
    -- both the `ULift` ring and the quotient are represented by source elements.
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rcases x with ⟨x⟩
    exact ⟨x, rfl⟩
  have eOwnerA :
      (Su ⧸ (Iu • (⊤ : Submodule Ru Su))) ≃ₗ[R]
        S ⧸ (I • (⊤ : Submodule R S)) := by
    let eRestrict :
        (Su ⧸ ((Iu • (⊤ : Submodule Ru Su)).restrictScalars R)) ≃ₗ[R]
          Su ⧸ (Iu • (⊤ : Submodule Ru Su)) :=
      Submodule.Quotient.restrictScalarsEquiv R (Iu • (⊤ : Submodule Ru Su))
    let eDenom :
        (Su ⧸ ((Iu • (⊤ : Submodule Ru Su)).restrictScalars R)) ≃ₗ[R]
          Su ⧸ (I • (⊤ : Submodule R Su)) :=
      Submodule.quotEquivOfEq
        ((Iu • (⊤ : Submodule Ru Su)).restrictScalars R)
        (I • (⊤ : Submodule R Su))
        hIu_restrict
    let eULift :
        (Su ⧸ (I • (⊤ : Submodule R Su))) ≃ₗ[R]
          S ⧸ (I • (⊤ : Submodule R S)) :=
      (ulift_module_quotient_equiv (A := R) (J := I) (N := S)).restrictScalars R
    -- Proof comment: compare the lifted quotient to the original one by first restricting
    -- scalars, then normalizing the denominator, and finally removing the `ULift`.
    exact eRestrict.symm.trans (eDenom.trans eULift)
  let eOwner :
      (Su ⧸ (Iu • (⊤ : Submodule Ru Su))) ≃ₗ[Tu]
        S ⧸ (I • (⊤ : Submodule R S)) :=
    eOwnerA.extendScalarsOfSurjective hsurjRT
  have hflatTB : Module.Flat Tu B := by
    let eAlg : B ≃ₐ[Tu] Tu :=
      AlgEquiv.ofRingEquiv (R := Tu) (f := eRing.symm) (by
        intro x
        change eRing.symm (eRing x) = x
        exact eRing.symm_apply_apply x)
    exact Module.Flat.of_linearEquiv eAlg.toLinearEquiv
  have hflatTarget : Module.Flat Tu (S ⧸ (I • (⊤ : Submodule R S))) := by
    letI : Module.Flat Tu B := hflatTB
    letI : Module.Flat B (S ⧸ (I • (⊤ : Submodule R S))) := hflat
    exact Module.Flat.trans Tu B (S ⧸ (I • (⊤ : Submodule R S)))
  have hflat_uquot :
      Module.Flat Tu (Su ⧸ (Iu • (⊤ : Submodule Ru Su))) := by
    letI : Module.Flat Tu (S ⧸ (I • (⊤ : Submodule R S))) := hflatTarget
    exact Module.Flat.of_linearEquiv eOwner
  have hflatRuSu : Module.Flat Ru Su := by
    -- Proof comment: all lifted hypotheses now match the exact common-universe owner expected by
    -- the imported variant local criterion.
    exact
      flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal
        (R := Ru) (S := Su) (M := Su) Iu hIu hTor_u hflat_uquot
  have hflatRSu : Module.Flat R Su := by
    have hflatRRu : Module.Flat R Ru := by
      exact Module.Flat.of_linearEquiv (ULift.algEquiv (R := R) (A := R)).toLinearEquiv
    letI : Module.Flat R Ru := hflatRRu
    letI : Module.Flat Ru Su := hflatRuSu
    exact Module.Flat.trans R Ru Su
  letI : Module.Flat R Su := hflatRSu
  -- Proof comment: remove the remaining `ULift` on the target module.
  exact Module.Flat.of_linearEquiv (ULift.moduleEquiv (R := R) (M := S)).symm

/-- Lemma 10.128.2: let `R → S` be a local homomorphism of Noetherian local rings. If `R` is a
regular local ring and a regular system of parameters of length `d = ringKrullDim R` maps to a
regular sequence in `S`, then `S` is flat over `R`. -/
@[stacks 07DY]
theorem flat_of_regularSystemOfParameters_image_isRegular
    {d : ℕ} (x : Fin d → maximalIdeal R)
    (hx : IsRegularSystemOfParameters x)
    (hreg : IsRegular S (List.ofFn fun i ↦ algebraMap R S (x i : R))) :
    Module.Flat R S := by
  induction d generalizing R S with
  | zero =>
      have hdim : ringKrullDim R = 0 := by
        simpa using hx.1.1
      let _ : Field R :=
        (isField_of_isRegularLocalRing_of_ringKrullDim_eq_zero (R := R) hdim).toField
      let _ : Module.Free R S := Module.Free.of_divisionRing R S
      -- Proof comment: over a field every module is free, hence flat.
      exact Module.Flat.of_free
  | succ d ih =>
      let aR : R := (x 0 : R)
      let aS : S := algebraMap R S aR
      let rsR : List R := List.ofFn fun i : Fin d ↦ (x i.succ : R)
      let rsS : List S := List.ofFn fun i : Fin d ↦ algebraMap R S (x i.succ : R)
      let I : Ideal R := headParameterIdeal x
      let J : Ideal S := Ideal.map (algebraMap R S) I
      let R' : Type u := R ⧸ I
      let S' : Type v := S ⧸ J
      letI : Nontrivial R' := Ideal.Quotient.nontrivial_iff.mpr (headParameterIdeal_ne_top x)
      letI : IsLocalRing R' :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      letI : IsRegularLocalRing R' := by
        -- Proof comment: quotienting by the head parameter keeps the source regular local.
        simpa [R', I, headParameterIdeal] using
          (head_parameter_quotient_regular_local_and_dim (R := R) (x := x) hx).1
      have hI_le_max : I ≤ maximalIdeal R := by
        -- Proof comment: the head parameter ideal is generated by an element of the maximal ideal.
        dsimp [I, headParameterIdeal]
        exact
          (Ideal.span_singleton_le_iff_mem (I := maximalIdeal R) (x := (x 0 : R))).2
            (x 0).2
      have hJ_lt_top : J < ⊤ := by
        -- Proof comment: the mapped head ideal stays proper inside the local target.
        exact lt_of_le_of_lt (Ideal.map_mono hI_le_max)
          (IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S))
      letI : Nontrivial S' := Ideal.Quotient.nontrivial_iff.mpr hJ_lt_top.ne
      letI : IsLocalRing S' :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
      letI : IsNoetherianRing S' := inferInstance
      letI : IsLocalHom (algebraMap R' S') := by
        -- Proof comment: reuse the earlier quotient-local API instead of duplicating it here.
        simpa [R', S', I, J] using
          (quotient_algebraMap_isLocalHom
            (R := R) (S := S) (I := I) (headParameterIdeal_ne_top x))
      have hreg_full : IsRegular S (List.ofFn fun i : Fin (d + 1) ↦ algebraMap R S (x i : R)) := hreg
      have hsource_reg : IsRegular R (List.ofFn fun i : Fin (d + 1) ↦ (x i : R)) := by
        -- Proof comment: a regular system of parameters is already a regular sequence upstairs.
        exact hx.isRegular
      have hlistR :
          List.ofFn (fun i : Fin (d + 1) ↦ (x i : R)) = aR :: rsR := by
        -- Proof comment: split the source sequence into head and tail.
        simpa [aR, rsR] using
          (List.ofFn_cons (x 0 : R) (fun i : Fin d ↦ (x i.succ : R)))
      rw [hlistR] at hsource_reg
      rcases (isRegular_cons_iff (M := R) aR rsR).1 hsource_reg with ⟨haR, _⟩
      have hhead_source : IsRegular aR := by
        -- Proof comment: on the regular module `R`, scalar-regularity is ordinary regularity.
        exact isRegular_of_isSMulRegular_self haR
      have hlistS :
          List.ofFn (fun i : Fin (d + 1) ↦ algebraMap R S (x i : R)) = aS :: rsS := by
        -- Proof comment: split the image sequence in the target ring in the same way.
        simpa [aS, rsS, aR] using
          (List.ofFn_cons (algebraMap R S (x 0 : R))
            (fun i : Fin d ↦ algebraMap R S (x i.succ : R)))
      rw [hlistS] at hreg
      rcases (isRegular_cons_iff (M := S) aS rsS).1 hreg with ⟨haS, _⟩
      have hhead_target : IsSMulRegular S aR := by
        -- Proof comment: scalar multiplication by `aR` on `S` is multiplication by its image.
        exact (isSMulRegular_algebraMap_iff S).1 haS
      have htail_sys : IsRegularSystemOfParameters (head_quotient_tail x) := by
        -- Proof comment: the quotient source carries the tail parameters as a new regular system.
        simpa [R', I] using head_quotient_tail_isRegularSystemOfParameters (R := R) hx
      have htail_reg :
          IsRegular S'
            (List.ofFn fun i : Fin d ↦
              Ideal.Quotient.mk J (algebraMap R S (x i.succ : R))) := by
        -- Proof comment: the target quotient sees the image tail as a regular sequence.
        simpa [S', J, I] using
          image_tail_isRegular_on_head_quotient (R := R) (S := S) x hreg_full
      have hflat_quot : Module.Flat R' S' := by
        -- Proof comment: recurse on the quotient pair after removing the head parameter.
        exact ih (R := R') (S := S') (x := head_quotient_tail x) htail_sys htail_reg
      have hflat_mapped :
          Module.Flat R' ((S ⧸ (J • (⊤ : Submodule S S))) : Type v) := by
        -- Proof comment: for the target ring as a module over itself, quotienting by `J • ⊤`
        -- is the same owner as the ring quotient by `J`.
        have hJ_top : (J • (⊤ : Submodule S S)) = (J : Submodule S S) := by
          simpa [Ideal.smul_eq_mul] using (Ideal.mul_top J)
        let eS :
            ((S ⧸ (J • (⊤ : Submodule S S))) : Type v) ≃ₗ[S] (S ⧸ J) :=
          Submodule.quotEquivOfEq _ _ hJ_top
        let eT : ((S ⧸ (J • (⊤ : Submodule S S))) : Type v) ≃ₗ[S'] (S ⧸ J) :=
          eS.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
        have hflat_over_S' : Module.Flat S' ((S ⧸ (J • (⊤ : Submodule S S))) : Type v) := by
          letI : Module.Flat S' (S ⧸ J) := inferInstance
          exact Module.Flat.of_linearEquiv eT
        letI : IsScalarTower R' S' ((S ⧸ (J • (⊤ : Submodule S S))) : Type v) :=
          IsScalarTower.of_compHom R' S' ((S ⧸ (J • (⊤ : Submodule S S))) : Type v)
        letI : Module.Flat R' S' := hflat_quot
        letI : Module.Flat S' ((S ⧸ (J • (⊤ : Submodule S S))) : Type v) := hflat_over_S'
        exact Module.Flat.trans R' S' ((S ⧸ (J • (⊤ : Submodule S S))) : Type v)
      have hflat_mod :
          Module.Flat R' (S ⧸ (I • (⊤ : Submodule R S))) := by
        -- Proof comment: compare the mapped-ideal quotient owner with the source quotient owner.
        let e :=
          quotient_source_owner_over_quotient_local_ring (R := R) (S := S) (N := S) I
        letI : Module.Flat R' ((S ⧸ (J • (⊤ : Submodule S S))) : Type v) := hflat_mapped
        exact Module.Flat.of_linearEquiv e.symm
      -- Proof comment: the source-faithful induction now matches the local criterion exactly.
      exact
        flat_of_regular_element_and_flat_mod_ideal_self_univ
          (R := R) (S := S) aR
          (by simpa [I, headParameterIdeal, aR] using headParameterIdeal_ne_top x)
          hhead_source hhead_target hflat_mod

end
