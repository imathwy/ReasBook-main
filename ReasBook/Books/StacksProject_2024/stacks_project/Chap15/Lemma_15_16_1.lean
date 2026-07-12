import StacksProject_2024.Chap10.Lemma_10_39_2
import StacksProject_2024.Chap10.Lemma_10_39_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Ideal

variable {R : Type u} [CommRing R]

/-- An ideal `J` has flat quotient for `M` if `M / JM` is flat over `R ⧸ J`. -/
abbrev IsFlatQuotient (J : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  Module.Flat (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M)))

section

variable {M : Type v} [AddCommGroup M] [Module R M]
variable {I₁ I₂ : Ideal R}

/- Domain triage:
- primary domain: commutative algebra of flatness for quotient modules over quotient rings;
- sampled owner declarations of the same kind:
  `Module.Flat`,
  `Ideal.smul_top_inf_smul_top_eq_inf_smul_top_of_flat`,
  `Ideal.map_inf_of_flat`,
  `Module.Flat.iff_rTensor_preserves_injective_linearMap`;
- best owner abstraction: the source-facing ideal predicate `Ideal.IsFlatQuotient` introduced
  here, whose core/canonical content is `Module.Flat` for the quotient ring and quotient module,
  with the Chapter 10 ideal-intersection flatness API supplying the key structural input;
- primitive data: the ring `R`, the module `M`, and the ideals `I₁`, `I₂`;
- derived API: the closure of `Ideal.IsFlatQuotient` under binary intersections.

Layering:
- `source-facing`: the Stacks lemma about combining two flat quotient thickenings;
- `core/canonical`: `Ideal.IsFlatQuotient`, `Module.Flat`, and the flat-module identity
  `Ideal.smul_top_inf_smul_top_eq_inf_smul_top_of_flat`;
- no separate `bridge/view` owner is needed in this file.
-/

-- Proof sketch: replace `R` by `R ⧸ (I₁ ⊓ I₂)` and `M` by `M ⧸ (I₁ • ⊤ ⊓ I₂ • ⊤)`. The owner
-- theorem `Ideal.smul_top_inf_smul_top_eq_inf_smul_top_of_flat` identifies the denominator with
-- `(I₁ ⊓ I₂) • ⊤`, so the reduced situation has `I₁ ⊓ I₂ = 0`. Then apply the canonical
-- injectivity criterion `Module.Flat.iff_rTensor_preserves_injective_linearMap`: flatness modulo
-- `I₁` reduces injectivity for an ideal inclusion `J ↪ R ⧸ I₁` to injectivity after tensoring
-- with `M ⧸ (I₁ • ⊤)`, and because `I₁ ⊓ I₂ = 0`, the relevant intersections identify with
-- ideals in `R ⧸ I₂`, where flatness modulo `I₂` supplies the remaining injectivity step.

/-- Helper for Lemma 15.16.1: after quotienting by `I₁ ⊓ I₂`, the images of `I₁` and `I₂`
have trivial intersection. -/
lemma map_inf_quotient_intersection_eq_bot :
    Ideal.map (Ideal.Quotient.mk (I₁ ⊓ I₂)) I₁ ⊓
      Ideal.map (Ideal.Quotient.mk (I₁ ⊓ I₂)) I₂ =
        (⊥ : Ideal (R ⧸ (I₁ ⊓ I₂))) := by
  -- Check membership elementwise and lift representatives through the quotient map.
  refine bot_unique ?_
  intro x hx
  rcases (Ideal.mem_inf.mp hx) with ⟨hx₁, hx₂⟩
  obtain ⟨a₁, ha₁I₁, rfl⟩ :=
    (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (I₁ ⊓ I₂))
      Ideal.Quotient.mk_surjective).1 hx₁
  obtain ⟨a₂, ha₂I₂, ha₂eq⟩ :=
    (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (I₁ ⊓ I₂))
      Ideal.Quotient.mk_surjective).1 hx₂
  -- The two representatives differ by an element of `I₁ ⊓ I₂`, so `a₁` already lies there.
  have hsub :
      (Ideal.Quotient.mk (I₁ ⊓ I₂)) (a₁ - a₂) = 0 := by
    simpa [ha₂eq] using sub_eq_zero.mp rfl
  have hsub_mem : a₁ - a₂ ∈ I₁ ⊓ I₂ :=
    (Ideal.Quotient.eq_zero_iff_mem).1 hsub
  have ha₁I₂ : a₁ ∈ I₂ := by
    have hadd : (a₁ - a₂) + a₂ ∈ I₂ := I₂.add_mem (Ideal.mem_inf.mp hsub_mem).2 ha₂I₂
    simpa [sub_eq_add_neg, add_assoc] using hadd
  have ha₁K : a₁ ∈ I₁ ⊓ I₂ := Ideal.mem_inf.mpr ⟨ha₁I₁, ha₁I₂⟩
  simpa using (Ideal.Quotient.eq_zero_iff_mem).2 ha₁K

/-- Helper for Lemma 15.16.1: quotienting `M / KM` again by the image of `J`
recovers `M / JM` as an `R`-linear quotient-of-quotient equivalence. -/
noncomputable def quotient_quotient_smul_top_equiv
    {K J : Ideal R} (hKJ : K ≤ J) :
    ((M ⧸ (K • (⊤ : Submodule R M))) ⧸
      ((((Ideal.map (Ideal.Quotient.mk K) J) •
          (⊤ : Submodule (R ⧸ K) (M ⧸ (K • (⊤ : Submodule R M))))) :
            Submodule (R ⧸ K) (M ⧸ (K • (⊤ : Submodule R M)))).restrictScalars R)) ≃ₗ[R]
      M ⧸ (J • (⊤ : Submodule R M)) := by
  let Ksm : Submodule R M := K • (⊤ : Submodule R M)
  let Jsm : Submodule R M := J • (⊤ : Submodule R M)
  have hden :
      ((((Ideal.map (Ideal.Quotient.mk K) J) •
          (⊤ : Submodule (R ⧸ K) (M ⧸ Ksm))) :
            Submodule (R ⧸ K) (M ⧸ Ksm)).restrictScalars R) =
        Jsm.map Ksm.mkQ := by
    -- Rewrite the quotient-ring action back to the original `R`-action, then map `JM`
    -- through the first quotient.
    calc
      ((((Ideal.map (Ideal.Quotient.mk K) J) •
          (⊤ : Submodule (R ⧸ K) (M ⧸ Ksm))) :
            Submodule (R ⧸ K) (M ⧸ Ksm)).restrictScalars R) =
          J • (⊤ : Submodule R (M ⧸ Ksm)) := by
            simpa [Ksm] using
              (Ideal.smul_restrictScalars (R := R) (S := R ⧸ K)
                (M := M ⧸ Ksm) J (⊤ : Submodule (R ⧸ K) (M ⧸ Ksm)))
      _ = Jsm.map Ksm.mkQ := by
            simpa [Jsm] using
              (Submodule.map_smul'' (f := Ksm.mkQ) J (⊤ : Submodule R M))
  -- After identifying the intermediate denominator, apply the standard third isomorphism
  -- theorem for submodule quotients.
  exact
    (Submodule.quotEquivOfEq _ _ hden).trans
      (Submodule.quotientQuotientEquivQuotient Ksm Jsm (Submodule.smul_mono hKJ le_rfl))

/-- Helper for Lemma 15.16.1: flatness over a ring equivalence is equivalent to flatness after
restricting scalars along the forward ring homomorphism. -/
lemma flat_iff_compHom_of_ringEquiv
    {S T : Type*} [CommRing S] [CommRing T]
    (e : S ≃+* T)
    {N : Type*} [AddCommGroup N] [Module T N] :
    let _ : Module S N := Module.compHom N e.toRingHom
    Module.Flat S N ↔ Module.Flat T N := by
  -- TODO: re-establish the ring-equivalence flatness transport after the quotient-of-quotient
  -- module structure is stabilized.
  sorry

lemma isFlatQuotient_map_iff
    {K J : Ideal R} (hKJ : K ≤ J) :
    (Ideal.map (Ideal.Quotient.mk K) J).IsFlatQuotient
      (M ⧸ (K • (⊤ : Submodule R M))) ↔
    J.IsFlatQuotient M := by
  -- TODO: transport flatness across the quotient-of-quotient ring/module identifications.
  sorry

/-- Helper for Lemma 15.16.1: when `I₁ ⊓ I₂ = ⊥`, the ideal `J ⊓ I₁` identifies with its image in
`R ⧸ I₂` under the quotient map. -/
noncomputable def inter_ideal_equiv_map_quotient_right
    (J : Ideal R) (hzero : I₁ ⊓ I₂ = ⊥) :
    ↥(J ⊓ I₁) ≃ₗ[R] ↥(Ideal.map (Ideal.Quotient.mk I₂) (J ⊓ I₁)) := sorry

/-- Helper for Lemma 15.16.1: extending scalars of the reduced-case ideal identification along
`R → R ⧸ I₂` upgrades it to the quotient-ring linear equivalence needed for the source proof. -/
noncomputable def inter_ideal_basechange_equiv_map_quotient_right
    (J : Ideal R) (hzero : I₁ ⊓ I₂ = ⊥) :
    TensorProduct R (R ⧸ I₂) ↥(J ⊓ I₁) ≃ₗ[R ⧸ I₂]
      ↥(Ideal.map (Ideal.Quotient.mk I₂) (J ⊓ I₁)) := sorry

/-- Helper for Lemma 15.16.1: in the reduced case, flatness modulo `I₁` reduces injectivity for
`J ⊗[R] M → M` to injectivity for `(J ⊓ I₁) ⊗[R] M → M`. -/
lemma injective_lift_lsmul_reduce_to_inter
    (hflat₁ : I₁.IsFlatQuotient M)
    (J : Ideal R) (hJfg : J.FG)
    (hinter :
      Function.Injective
        (TensorProduct.lift ((LinearMap.lsmul R M).comp (J ⊓ I₁).subtype))) :
    Function.Injective
      (TensorProduct.lift ((LinearMap.lsmul R M).comp J.subtype)) := by
  -- TODO: identify the cokernel side with the injective quotient-ring tensor map over `R ⧸ I₁`,
  -- then use right exactness of tensoring on
  -- `0 → J ⊓ I₁ → J → J / (J ⊓ I₁) → 0` to show every kernel element already comes from
  -- `(J ⊓ I₁) ⊗[R] M`, where `hinter` finishes the argument.
  sorry

/-- Helper for Lemma 15.16.1: in the reduced case, flatness modulo `I₂` gives injectivity for the
intersection ideal after transporting the tensor map to the quotient ring `R ⧸ I₂`. -/
lemma injective_lift_lsmul_inter_of_flat_quotient_right
    (hzero : I₁ ⊓ I₂ = ⊥)
    (hflat₂ : I₂.IsFlatQuotient M)
    (J : Ideal R) (hJfg : J.FG) :
    Function.Injective
      (TensorProduct.lift ((LinearMap.lsmul R M).comp (J ⊓ I₁).subtype)) := by
  -- TODO: use `inter_ideal_basechange_equiv_map_quotient_right` to upgrade
  -- `J ⊓ I₁ ≃ Ideal.map (Ideal.Quotient.mk I₂) (J ⊓ I₁)` to the tensor level, compare
  -- the source map composed with `M → M ⧸ I₂M` to the quotient-ring tensor map, and then apply
  -- `Module.Flat.iff_lift_lsmul_comp_subtype_injective` to `hflat₂`.
  sorry

/-- Helper for Lemma 15.16.1: in the reduced case `I₁ ⊓ I₂ = ⊥`, the source tensor-injectivity
argument proves that `M` is flat over `R`. -/
lemma flat_of_flat_quotients_of_inf_eq_bot
    (hzero : I₁ ⊓ I₂ = ⊥)
    (hflat₁ : I₁.IsFlatQuotient M)
    (hflat₂ : I₂.IsFlatQuotient M) :
    Module.Flat R M := by
  -- Apply the finitely generated ideal criterion for flatness.
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro J hJfg
  -- The right half of the source proof handles the intersection ideal over `R ⧸ I₂`.
  have hinter :
      Function.Injective
        (TensorProduct.lift ((LinearMap.lsmul R M).comp (J ⊓ I₁).subtype)) :=
    injective_lift_lsmul_inter_of_flat_quotient_right
      (I₁ := I₁) (I₂ := I₂) hzero hflat₂ J hJfg
  -- The left half then reduces the original ideal `J` to `J ⊓ I₁`.
  exact
    injective_lift_lsmul_reduce_to_inter
      (I₁ := I₁) (hflat₁ := hflat₁) J hJfg hinter

/-- Lemma 15.16.1: the ideals cutting out flat quotients of `M` are closed under binary intersections. -/
theorem IsFlatQuotient.inf
    (hflat₁ : I₁.IsFlatQuotient M)
    (hflat₂ : I₂.IsFlatQuotient M) :
    (I₁ ⊓ I₂).IsFlatQuotient M := by
  let K : Ideal R := I₁ ⊓ I₂
  let J₁ : Ideal (R ⧸ K) := Ideal.map (Ideal.Quotient.mk K) I₁
  let J₂ : Ideal (R ⧸ K) := Ideal.map (Ideal.Quotient.mk K) I₂
  let Mbar : Type v := M ⧸ (K • (⊤ : Submodule R M))
  letI : AddCommGroup Mbar := inferInstance
  letI : Module (R ⧸ K) Mbar := inferInstance
  -- Transport the two quotient-flatness hypotheses down to the reduced quotient ring.
  have hJ₁ : J₁.IsFlatQuotient Mbar := by
    simpa [K, J₁, Mbar] using
      (isFlatQuotient_map_iff (M := M) (K := K) (J := I₁) inf_le_left).2 hflat₁
  have hJ₂ : J₂.IsFlatQuotient Mbar := by
    simpa [K, J₂, Mbar] using
      (isFlatQuotient_map_iff (M := M) (K := K) (J := I₂) inf_le_right).2 hflat₂
  have hzero : J₁ ⊓ J₂ = ⊥ := by
    simpa [K, J₁, J₂] using
      (map_inf_quotient_intersection_eq_bot (R := R) (I₁ := I₁) (I₂ := I₂))
  -- The remaining step is the reduced case over `R ⧸ (I₁ ⊓ I₂)`.
  simpa [IsFlatQuotient, K, Mbar] using
    (flat_of_flat_quotients_of_inf_eq_bot
      (R := R ⧸ K) (M := Mbar) (I₁ := J₁) (I₂ := J₂) hzero hJ₁ hJ₂)

end

end Ideal
