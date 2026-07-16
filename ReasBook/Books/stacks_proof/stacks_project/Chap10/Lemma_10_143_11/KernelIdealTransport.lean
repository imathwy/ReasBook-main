import stacks_proof.stacks_project.Chap10.Lemma_10_143_11.IdealAndCotangentMaps

-- Declarations moved out of `Lemma_10_143_11.lean` to keep the active proof file small.

open scoped TensorProduct

universe u v w x

namespace RingHom

section

variable {Aprime : Type u} {A : Type v} {Bprime : Type w} {B : Type x}
variable [CommRing Aprime] [CommRing A] [CommRing Bprime] [CommRing B]
variable (g : Aprime →+* Bprime) (qA : Aprime →+* A) (qB : Bprime →+* B) (f : A →+* B)

/-- Helper for Lemma 10.143.11: once a comparison map induces a bijection on the source and target
kernels, surjectivity of the quotient maps upgrades it to a bijection of rings. -/
lemma comparison_bijective_of_ker_restrict_bijective
    {C : Type*} [CommRing C] {qC : C →+* B} {φ : C →+* Bprime}
    (hSurjC : Function.Surjective qC)
    (hcomp : qB.comp φ = qC)
    (hker_bij :
      Function.Bijective
        (kernel_restrict (qC := qC) (qB := qB) (φ := φ) hcomp)) :
    Function.Bijective φ := by
  constructor
  · intro x y hxy
    -- Compare `x - y` inside the source kernel and use injectivity of the kernel restriction.
    have hxy_ker : x - y ∈ ker qC := by
      rw [RingHom.mem_ker, map_sub]
      have hq_eq : qC x = qC y := by
        have hxq : qB (φ x) = qC x := by
          simpa [RingHom.comp_apply] using congrArg (fun h : C →+* B ↦ h x) hcomp
        have hyq : qB (φ y) = qC y := by
          simpa [RingHom.comp_apply] using congrArg (fun h : C →+* B ↦ h y) hcomp
        calc
          qC x = qB (φ x) := hxq.symm
          _ = qB (φ y) := by rw [hxy]
          _ = qC y := hyq
      exact sub_eq_zero.mpr hq_eq
    have hzero_mem : (0 : C) ∈ ker qC := by
      rw [RingHom.mem_ker]
      simp
    have hk_eq :
        kernel_restrict (qC := qC) (qB := qB) (φ := φ) hcomp
          ⟨x - y, hxy_ker⟩ =
        kernel_restrict (qC := qC) (qB := qB) (φ := φ) hcomp
          ⟨0, hzero_mem⟩ := by
      apply Subtype.ext
      simp [kernel_restrict, hxy, map_sub]
    have hsub_zero :
        (⟨x - y, hxy_ker⟩ : ker qC) = ⟨0, hzero_mem⟩ :=
      hker_bij.1 hk_eq
    exact sub_eq_zero.mp (Subtype.ext_iff.mp hsub_zero)
  · intro y
    -- Lift `qB y` through `qC`, then correct the error term inside the target kernel.
    obtain ⟨x₀, hx₀⟩ := hSurjC (qB y)
    have hy_diff_ker : y - φ x₀ ∈ ker qB := by
      rw [RingHom.mem_ker, map_sub]
      have hx₀' : qB (φ x₀) = qB y := by
        calc
          qB (φ x₀) = qC x₀ := by
            simpa [RingHom.comp_apply] using congrArg (fun h : C →+* B ↦ h x₀) hcomp
          _ = qB y := hx₀
      exact sub_eq_zero.mpr hx₀'.symm
    obtain ⟨z, hz⟩ := hker_bij.2 ⟨y - φ x₀, hy_diff_ker⟩
    refine ⟨x₀ + z.1, ?_⟩
    have hz_val : φ z.1 = y - φ x₀ := Subtype.ext_iff.mp hz
    calc
      φ (x₀ + z.1) = φ x₀ + φ z.1 := by simp
      _ = φ x₀ + (y - φ x₀) := by rw [hz_val]
      _ = y := by abel

/-- Helper for Lemma 10.143.11: if the restricted kernel map becomes the identity after
transporting both kernels to a common model, then the restricted kernel map is bijective. -/
lemma kernel_restrict_bijective_of_transport_identity
    {C : Type*} [CommRing C] {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    {qC : C →+* B₀} {qB : B₁ →+* B₀} {φ : C →+* B₁}
    {M : Type*}
    (hcomp : qB.comp φ = qC)
    (eSrc : M ≃ ker qC) (eTgt : M ≃ ker qB)
    (htransport :
      ∀ x : M,
        eTgt.symm (kernel_restrict (qC := qC) (qB := qB) (φ := φ) hcomp (eSrc x)) = x) :
    Function.Bijective (kernel_restrict (qC := qC) (qB := qB) (φ := φ) hcomp) := by
  let inv : ker qB → ker qC := fun y ↦ eSrc (eTgt.symm y)
  constructor
  · intro x y hxy
    -- Apply the transported inverse candidate to both sides and simplify with the identity model.
    have hx :
        inv (kernel_restrict (qC := qC) (qB := qB) (φ := φ) hcomp x) = x := by
      simpa [inv] using congrArg eSrc (htransport (eSrc.symm x))
    have hy :
        inv (kernel_restrict (qC := qC) (qB := qB) (φ := φ) hcomp y) = y := by
      simpa [inv] using congrArg eSrc (htransport (eSrc.symm y))
    simpa [hx, hy] using congrArg inv hxy
  · intro y
    -- The same transported identity evaluated at the target coordinate supplies a preimage.
    refine ⟨inv y, ?_⟩
    apply eTgt.symm.injective
    simpa [inv] using htransport (eTgt.symm y)

/-- Helper for Lemma 10.143.11: an explicit kernel equality identifies the textbook ideal model
with the actual kernel subtype. -/
noncomputable def ideal_equiv_ker
    {R : Type*} [CommRing R] {S : Type*} [CommRing S]
    (q : R →+* S) (J : Ideal R) (hJ : RingHom.ker q = J) :
    J ≃ RingHom.ker q where
  toFun x := ⟨x.1, by simpa [hJ] using x.2⟩
  invFun x := ⟨x.1, by simpa [hJ] using x.2⟩
  left_inv x := by
    rfl
  right_inv x := by
    rfl

/-- Helper for Lemma 10.143.11: after identifying `ker qC` and `ker qB` with the mapped ideals
`Ideal.map c I` and `Ideal.map g I`, the kernel restriction is exactly the explicit ideal map
transporting `φ`. -/
lemma kernel_restrict_eq_ideal_map_restrict
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    {I : Ideal R} {c : R →+* C} {g : R →+* B₁}
    {qC : C →+* B₀} {qB : B₁ →+* B₀} {φ : C →+* B₁}
    (hq : qB.comp φ = qC) (hg : φ.comp c = g)
    (hSrc : RingHom.ker qC = Ideal.map c I)
    (hTgt : RingHom.ker qB = Ideal.map g I)
    (x : Ideal.map c I) :
    (ideal_equiv_ker qB (Ideal.map g I) hTgt).symm
      (kernel_restrict (qC := qC) (qB := qB) (φ := φ) hq
        ((ideal_equiv_ker qC (Ideal.map c I) hSrc) x)) =
      ideal_map_restrict c g φ I hg x := by
  -- Both sides are the same subtype element with underlying value `φ x.1`.
  apply Subtype.ext
  rfl

/-- Helper for Lemma 10.143.11: the explicit textbook map `IC → J` is already surjective once
the lifted quotient map `qC : C → B` is surjective and the target kernel is square-zero. -/
lemma ideal_map_restrict_surjective_of_square_zero
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    {I : Ideal R} {c : R →+* C} {g : R →+* B₁}
    {qC : C →+* B₀} {qB : B₁ →+* B₀} {φ : C →+* B₁}
    (hSurjC : Function.Surjective qC)
    (hq : qB.comp φ = qC) (hg : φ.comp c = g)
    (hSqB : (RingHom.ker qB) ^ 2 = ⊥)
    (hTgt : RingHom.ker qB = Ideal.map g I) :
    Function.Surjective (ideal_map_restrict c g φ I hg) := by
  intro y
  suffices hpre : ∃ x, x ∈ Ideal.map c I ∧ φ x = y by
    rcases hpre with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  -- Build preimages by induction on the target ideal, using square-zero to correct coefficients.
  refine Submodule.span_induction
    (p := fun z (_hz : z ∈ Ideal.map g I) ↦ ∃ x, x ∈ Ideal.map c I ∧ φ x = z) ?_ ?_ ?_ ?_
    y.2
  · intro z hz
    rcases hz with ⟨i, hi, rfl⟩
    refine ⟨c i, Ideal.mem_map_of_mem c hi, ?_⟩
    simpa [RingHom.comp_apply] using congrArg (fun h : R →+* B₁ ↦ h i) hg
  · exact ⟨0, Ideal.zero_mem _, by simp⟩
  · intro x y _hx _hy hx hy
    rcases hx with ⟨x', hx', rfl⟩
    rcases hy with ⟨y', hy', rfl⟩
    exact ⟨x' + y', (Ideal.map c I).add_mem hx' hy', by simp⟩
  · intro a z _hz hz
    rcases hz with ⟨x, hx, rfl⟩
    obtain ⟨b, hb⟩ := hSurjC (qB a)
    refine ⟨b * x, (Ideal.map c I).mul_mem_left _ hx, ?_⟩
    have hq_at_b : qB (φ b) = qC b := by
      simpa [RingHom.comp_apply] using congrArg (fun h : C →+* B₀ ↦ h b) hq
    have hdiff_ker : a - φ b ∈ RingHom.ker qB := by
      rw [RingHom.mem_ker, map_sub]
      exact sub_eq_zero.mpr (hb.symm.trans hq_at_b.symm)
    have hz_ker : φ x ∈ RingHom.ker qB := by
      rw [hTgt]
      exact mapsTo_ideal_map_of_comp_eq (I := I) hg hx
    have hmul_zero : (a - φ b) * φ x = 0 := by
      have hmul_mem : (a - φ b) * φ x ∈ (RingHom.ker qB) ^ 2 := by
        rw [pow_two]
        exact Ideal.mul_mem_mul hdiff_ker hz_ker
      rw [hSqB] at hmul_mem
      simpa using hmul_mem
    calc
      φ (b * x) = φ b * φ x := by simp
      _ = a * φ x := by
        apply (sub_eq_zero.mp ?_).symm
        simpa [sub_mul] using hmul_zero
      _ = a • φ x := by simp [smul_eq_mul]

/-- Helper for Lemma 10.143.11: surjectivity on the textbook ideal comparison `IC → J`
upgrades to surjectivity of the whole comparison map `C → B'`. -/
lemma comparison_surjective_of_ideal_map_surjective
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    {I : Ideal R} {c : R →+* C} {g : R →+* B₁}
    {qC : C →+* B₀} {qB : B₁ →+* B₀} {φ : C →+* B₁}
    (hSurjC : Function.Surjective qC)
    (hq : qB.comp φ = qC) (hg : φ.comp c = g)
    (hTgt : RingHom.ker qB = Ideal.map g I)
    (hφI_surj : Function.Surjective (ideal_map_restrict c g φ I hg)) :
    Function.Surjective φ := by
  intro y
  -- First lift the quotient class of `y`, then correct the residual error term inside `J`.
  obtain ⟨x₀, hx₀⟩ := hSurjC (qB y)
  have hy_diff_ker : y - φ x₀ ∈ RingHom.ker qB := by
    rw [RingHom.mem_ker, map_sub]
    have hx₀' : qB (φ x₀) = qB y := by
      calc
        qB (φ x₀) = qC x₀ := by
          simpa [RingHom.comp_apply] using congrArg (fun h : C →+* B₀ ↦ h x₀) hq
        _ = qB y := hx₀
    exact sub_eq_zero.mpr hx₀'.symm
  have hy_diff_map : y - φ x₀ ∈ Ideal.map g I := by
    simpa [hTgt] using hy_diff_ker
  obtain ⟨z, hz⟩ := hφI_surj ⟨y - φ x₀, hy_diff_map⟩
  refine ⟨x₀ + z.1, ?_⟩
  have hz_val : φ z.1 = y - φ x₀ := Subtype.ext_iff.mp hz
  calc
    φ (x₀ + z.1) = φ x₀ + φ z.1 := by simp
    _ = φ x₀ + (y - φ x₀) := by rw [hz_val]
    _ = y := by abel

/-- Helper for Lemma 10.143.11: injectivity on the textbook ideal comparison `IC → J`
upgrades to injectivity of the whole comparison map `C → B'`. -/
lemma comparison_injective_of_ideal_map_injective
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    {I : Ideal R} {c : R →+* C} {g : R →+* B₁}
    {qC : C →+* B₀} {qB : B₁ →+* B₀} {φ : C →+* B₁}
    (hq : qB.comp φ = qC) (hg : φ.comp c = g)
    (hSrc : RingHom.ker qC = Ideal.map c I)
    (hφI_inj : Function.Injective (ideal_map_restrict c g φ I hg)) :
    Function.Injective φ := by
  intro x y hxy
  -- Compare `x - y` with zero inside `IC` and use injectivity of the ideal comparison map.
  have hxy_ker : x - y ∈ RingHom.ker qC := by
    rw [RingHom.mem_ker, map_sub]
    have hq_eq : qC x = qC y := by
      have hxq : qB (φ x) = qC x := by
        simpa [RingHom.comp_apply] using congrArg (fun h : C →+* B₀ ↦ h x) hq
      have hyq : qB (φ y) = qC y := by
        simpa [RingHom.comp_apply] using congrArg (fun h : C →+* B₀ ↦ h y) hq
      calc
        qC x = qB (φ x) := hxq.symm
        _ = qB (φ y) := by rw [hxy]
        _ = qC y := hyq
    exact sub_eq_zero.mpr hq_eq
  have hxy_src : x - y ∈ Ideal.map c I := by
    simpa [hSrc] using hxy_ker
  have hzero_src : (0 : C) ∈ Ideal.map c I := Ideal.zero_mem _
  have hmap_eq :
      ideal_map_restrict c g φ I hg ⟨x - y, hxy_src⟩ =
        ideal_map_restrict c g φ I hg ⟨0, hzero_src⟩ := by
    apply Subtype.ext
    simp [ideal_map_restrict, hxy, map_sub]
  have hsub_eq : (⟨x - y, hxy_src⟩ : Ideal.map c I) = ⟨0, hzero_src⟩ := hφI_inj hmap_eq
  exact sub_eq_zero.mp (Subtype.ext_iff.mp hsub_eq)

/-- Helper for Lemma 10.143.11: once the source-faithful ideal models `IC` and `J` are identified
with a common object, the remaining kernel bijectivity is just the existing transported-identity
argument with the trivial ideal-to-kernel casts folded in. -/
lemma kernel_restrict_bijective_of_ideal_transport_identity
    {C : Type*} [CommRing C] {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    {qC : C →+* B₀} {qB : B₁ →+* B₀} {φ : C →+* B₁}
    {M : Type*} {JSrc : Ideal C} {JTgt : Ideal B₁}
    (hcomp : qB.comp φ = qC)
    (hSrc : RingHom.ker qC = JSrc)
    (hTgt : RingHom.ker qB = JTgt)
    (eIdealSrc : M ≃ JSrc) (eIdealTgt : M ≃ JTgt)
    (htransport :
      ∀ x : M,
        eIdealTgt.symm
          ((ideal_equiv_ker qB JTgt hTgt).symm
            (kernel_restrict (qC := qC) (qB := qB) (φ := φ) hcomp
              ((eIdealSrc.trans (ideal_equiv_ker qC JSrc hSrc)) x))) = x) :
    Function.Bijective (kernel_restrict (qC := qC) (qB := qB) (φ := φ) hcomp) := by
  let eSrc : M ≃ ker qC := eIdealSrc.trans (ideal_equiv_ker qC JSrc hSrc)
  let eTgt : M ≃ ker qB := eIdealTgt.trans (ideal_equiv_ker qB JTgt hTgt)
  -- The only remaining work is to reuse the kernel-model transport lemma with the ideal casts
  -- absorbed into the chosen source and target equivalences.
  refine kernel_restrict_bijective_of_transport_identity
    (qC := qC) (qB := qB) (φ := φ) hcomp eSrc eTgt ?_
  intro x
  simpa [eSrc, eTgt, ideal_equiv_ker, Equiv.trans_apply] using htransport x

/-- Helper for Lemma 10.143.11: once the source and target textbook ideals are identified with a
common model on which the restricted kernel map is the identity, the whole comparison map is
bijective. -/
lemma comparison_bijective_of_ideal_transport_identity
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    {I : Ideal R} {c : R →+* C} {g : R →+* B₁}
    {qC : C →+* B₀} {qB : B₁ →+* B₀} {φ : C →+* B₁}
    {M : Type u}
    (hSurjC : Function.Surjective qC)
    (hq : qB.comp φ = qC)
    (hSrc : RingHom.ker qC = Ideal.map c I)
    (hTgt : RingHom.ker qB = Ideal.map g I)
    (eIdealSrc : M ≃ Ideal.map c I) (eIdealTgt : M ≃ Ideal.map g I)
    (htransport :
      ∀ x : M,
        eIdealTgt.symm
          ((ideal_equiv_ker qB (Ideal.map g I) hTgt).symm
            (kernel_restrict (qC := qC) (qB := qB) (φ := φ) hq
              ((eIdealSrc.trans (ideal_equiv_ker qC (Ideal.map c I) hSrc)) x))) = x) :
    Function.Bijective φ := by
  -- First upgrade the common-model identity to bijectivity on the kernel comparison.
  have hker_bij :
      Function.Bijective (kernel_restrict (qC := qC) (qB := qB) (φ := φ) hq) :=
    kernel_restrict_bijective_of_ideal_transport_identity
      (qC := qC) (qB := qB) (φ := φ) hq hSrc hTgt eIdealSrc eIdealTgt htransport
  -- Then reuse the quotient-surjectivity argument that upgrades kernel bijectivity to ring bijectivity.
  exact comparison_bijective_of_ker_restrict_bijective
    (qC := qC) (qB := qB) (φ := φ) hSurjC hq hker_bij
/-- Helper for Lemma 10.143.11: if the textbook ideal comparison `IC → J` becomes the identity
after transporting both ideals to a common model, then the ideal comparison is injective. -/
lemma ideal_map_restrict_injective_of_transport_identity
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] {T : Type*} [CommRing T]
    {I : Ideal R} {f : R →+* S} {g : R →+* T} {φ : S →+* T}
    {M : Type*}
    (hcomp : φ.comp f = g)
    (eIdealSrc : M ≃ Ideal.map f I) (eIdealTgt : M ≃ Ideal.map g I)
    (htransport :
      ∀ x : M,
        eIdealTgt.symm (ideal_map_restrict f g φ I hcomp (eIdealSrc x)) = x) :
    Function.Injective (ideal_map_restrict f g φ I hcomp) := by
  intro x y hxy
  -- Evaluate the transported identity on the source coordinates of `x` and `y`, then compare the
  -- common-model images through the given equality of the ideal comparison.
  apply eIdealSrc.symm.injective
  calc
    eIdealSrc.symm x =
        eIdealTgt.symm (ideal_map_restrict f g φ I hcomp x) := by
          simpa using (htransport (eIdealSrc.symm x)).symm
    _ = eIdealTgt.symm (ideal_map_restrict f g φ I hcomp y) := by
          rw [hxy]
    _ = eIdealSrc.symm y := by
          simpa using htransport (eIdealSrc.symm y)

/-- Helper for Lemma 10.143.11: once the source and target textbook ideals are identified with a
common model on which the textbook ideal comparison is the identity, the whole comparison map is
injective. -/
lemma comparison_injective_of_ideal_transport_identity
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    {I : Ideal R} {c : R →+* C} {g : R →+* B₁}
    {qC : C →+* B₀} {qB : B₁ →+* B₀} {φ : C →+* B₁}
    {M : Type*}
    (hq : qB.comp φ = qC) (hg : φ.comp c = g)
    (hSrc : RingHom.ker qC = Ideal.map c I)
    (eIdealSrc : M ≃ Ideal.map c I) (eIdealTgt : M ≃ Ideal.map g I)
    (htransport :
      ∀ x : M,
        eIdealTgt.symm (ideal_map_restrict c g φ I hg (eIdealSrc x)) = x) :
    Function.Injective φ := by
  -- First transport injectivity from the common model back to the textbook ideal comparison.
  have hφI_inj : Function.Injective (ideal_map_restrict c g φ I hg) :=
    ideal_map_restrict_injective_of_transport_identity
      (f := c) (g := g) (φ := φ) (I := I) hg eIdealSrc eIdealTgt htransport
  -- Then upgrade ideal-level injectivity to injectivity of the whole comparison map.
  exact comparison_injective_of_ideal_map_injective
    (I := I) (c := c) (g := g) (qC := qC) (qB := qB) (φ := φ) hq hg hSrc hφI_inj

/-- Helper for Lemma 10.143.11: if the source and target textbook ideals are identified with any
common model on which the textbook ideal comparison is the identity, then one can rebase that
transport to the literal source ideal `Ideal.map c I`. -/
lemma rebase_ideal_transport_data_to_source
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] {T : Type*} [CommRing T]
    {I : Ideal R} {f : R →+* S} {g : R →+* T} {φ : S →+* T}
    {M : Type*}
    (hcomp : φ.comp f = g)
    (eIdealSrc : M ≃ Ideal.map f I) (eIdealTgt : M ≃ Ideal.map g I)
    (htransport :
      ∀ x : M,
        eIdealTgt.symm (ideal_map_restrict f g φ I hcomp (eIdealSrc x)) = x) :
    ∃ eIdealTgt' : Ideal.map f I ≃ Ideal.map g I,
      ∀ x : Ideal.map f I,
        eIdealTgt'.symm (ideal_map_restrict f g φ I hcomp x) = x := by
  let eIdealTgt' : Ideal.map f I ≃ Ideal.map g I := eIdealSrc.symm.trans eIdealTgt
  refine ⟨eIdealTgt', ?_⟩
  intro x
  -- Evaluate the common-model identity at the source coordinate of `x` and then re-express the
  -- resulting target comparison through the rebased equivalence.
  simpa [eIdealTgt', Equiv.trans_apply] using congrArg eIdealSrc (htransport (eIdealSrc.symm x))


end

end RingHom
