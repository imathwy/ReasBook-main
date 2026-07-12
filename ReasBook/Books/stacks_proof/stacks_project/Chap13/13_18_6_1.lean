import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable {K L : CochainComplex 𝒜 ℤ} (α : K ⟶ L) [QuasiIso α]

/-
Domain-style sampling for 13.18.6.1:
- primary domain: cochain complexes in an abelian category, with degreewise exactness expressed by
  the short-complex API on cochain complexes, together with the translation of exactness into
  subobject equalities in an abelian category;
- sampled owner declarations:
  `ShortComplex.cokernelSequence`,
  `ShortComplex.ShortExact`,
  `HomologicalComplex.Acyclic`,
  `CategoryTheory.ShortComplex.exact_iff_image_eq_kernel`;
- best owner abstraction: `HomologicalComplex.Acyclic` applied to `cokernel α`, with the canonical
  short exact row `ShortComplex.cokernelSequence α` supplying the bridge from the quasi-isomorphism
  hypothesis to degreewise exactness;
- primitive data: the morphism `α : K ⟶ L`, the quasi-isomorphism structure, and the termwise
  monomorphism hypothesis;
- derived API: the source-facing image/intersection identity inside `L.X n`.

Source/core/bridge triage:
- `source-facing`: the image/intersection identity inside `L.X n`;
- `core/canonical`: `HomologicalComplex.Acyclic` and `HomologicalComplex.ExactAt` for
  `cokernel α`;
- `bridge/view`: the canonical short exact row `ShortComplex.cokernelSequence α`, together with
  its long exact homology sequence, and then
  `CategoryTheory.ShortComplex.exact_iff_image_eq_kernel` to convert degreewise exactness into the
  source-facing subobject identity.
-/

-- Proof sketch: use the canonical short exact row `0 ⟶ K ⟶ L ⟶ cokernel α ⟶ 0`, encoded by
-- `ShortComplex.cokernelSequence α`. Its long exact homology sequence shows that the homology of
-- `cokernel α` vanishes in every degree because `α` is a quasi-isomorphism.
/-- The cokernel complex of a termwise monomorphic quasi-isomorphism is acyclic. -/
theorem cokernel_acyclic_of_termwiseMono_quasiIso
    (hmono : ∀ n : ℤ, Mono (α.f n)) :
    (cokernel α).Acyclic := by
  rw [HomologicalComplex.acyclic_iff]
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  let S := ShortComplex.cokernelSequence α
  have hS : S.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_
      (HomologicalComplex.mono_of_mono_f α hmono) inferInstance
    exact ShortComplex.cokernelSequence_exact α
  refine ((hS.homology_exact₃ n (n + 1) (by simp)).isZero_X₂ ?_ ?_)
  · rw [← (hS.homology_exact₂ n).epi_f_iff]
    have : Epi (homologyMap α n) := by infer_instance
    simpa [S] using this
  · rw [← (hS.homology_exact₁ n (n + 1) (by simp)).mono_g_iff]
    have : Mono (homologyMap α (n + 1)) := by infer_instance
    simpa [S] using this

/-- Helper for 13.18.6.1: a subobject arrow identifies the subobject with the kernel of its
cokernel projection. -/
private theorem subobject_eq_kernel_cokernel {A : 𝒜} (X : Subobject A) :
    X = kernelSubobject (cokernel.π X.arrow) := by
  -- Replace the subobject by the image of its mono arrow, then use the exact cokernel sequence.
  calc
    X = imageSubobject X.arrow := by
      symm
      simpa using (Limits.imageSubobject_mono X.arrow)
    _ = kernelSubobject (cokernel.π X.arrow) := by
      simpa using
        (ShortComplex.exact_iff_image_eq_kernel
          (ShortComplex.mk X.arrow (cokernel.π X.arrow) (cokernel.condition X.arrow))).1
          (ShortComplex.exact_cokernel X.arrow)

/-- Helper for 13.18.6.1: precomposing with an epimorphism does not change the image subobject. -/
private theorem imageSubobject_comp_eq_of_epi {X Y Z : 𝒜}
    (f : X ⟶ Y) [Epi f] (g : Y ⟶ Z) :
    imageSubobject (f ≫ g) = imageSubobject g := by
  -- The comparison map onto the larger image is both mono and epi, hence an isomorphism.
  have hle : imageSubobject (f ≫ g) ≤ imageSubobject g :=
    imageSubobject_comp_le f g
  haveI : Epi (Subobject.ofLE _ _ hle) :=
    imageSubobject_comp_le_epi_of_epi f g
  haveI : IsIso (Subobject.ofLE _ _ hle) :=
    isIso_of_mono_of_epi (Subobject.ofLE _ _ hle)
  refine Subobject.eq_of_comm (asIso (Subobject.ofLE _ _ hle)) ?_
  simp

/-- Helper for 13.18.6.1: composing with a monomorphism maps image subobjects forward along that
monomorphism. -/
private theorem image_subobject_comp_eq_map_of_mono {X Y Z : 𝒜}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Mono g] :
    imageSubobject (f ≫ g) = (Subobject.map g).obj (imageSubobject f) := by
  -- First replace `f` by its epi factorization through the image, then `map_mk` finishes.
  calc
    imageSubobject (f ≫ g)
        = imageSubobject ((imageSubobject f).arrow ≫ g) := by
            simpa [Category.assoc, imageSubobject_arrow_comp] using
              imageSubobject_comp_eq_of_epi (factorThruImageSubobject f)
                ((imageSubobject f).arrow ≫ g)
    _ = Subobject.mk ((imageSubobject f).arrow ≫ g) := by
          simpa using (Limits.imageSubobject_mono ((imageSubobject f).arrow ≫ g))
    _ = (Subobject.map g).obj (Subobject.mk (imageSubobject f).arrow) := by
          rw [Subobject.map_mk]
    _ = (Subobject.map g).obj (imageSubobject f) := by
          rw [Subobject.mk_arrow]

/-- Helper for 13.18.6.1: in the acyclic cokernel complex, the pullback of the boundary subobject
of `L.X n` along a termwise monomorphism `α.f n` is exactly the boundary subobject of `K.X n`. -/
private theorem pullback_image_dTo_eq_image_dTo_of_cokernel_acyclic
    (hmono : ∀ m : ℤ, Mono (α.f m))
    (_hac : (cokernel α).Acyclic) (n : ℤ) :
    (Subobject.pullback (α.f n)).obj (imageSubobject (L.dTo n)) = imageSubobject (K.dTo n) := by
  let p : ℤ := (ComplexShape.up ℤ).prev n
  let pp : ℤ := (ComplexShape.up ℤ).prev p
  let P : Subobject (K.X n) := (Subobject.pullback (α.f n)).obj (imageSubobject (L.dTo n))
  let x : (P : 𝒜) ⟶ K.X n := P.arrow
  let z₀ : (P : 𝒜) ⟶ imageSubobject (L.dTo n) :=
    Subobject.pullbackπ (α.f n) (imageSubobject (L.dTo n))
  have hxpull : z₀ ≫ (imageSubobject (L.dTo n)).arrow = x ≫ α.f n := by
    -- The chosen pullback representative carries the universal pullback square.
    simpa [P, x, z₀] using (Subobject.isPullback (α.f n) (imageSubobject (L.dTo n))).w
  have hleft : imageSubobject (K.dTo n) ≤ P := by
    -- The easy inclusion is the chain-map square for `α`, expressed via pullback factorization.
    have hFactorsImage : (imageSubobject (L.dTo n)).Factors (K.dTo n ≫ α.f n) := by
      rw [show K.dTo n ≫ α.f n = α.f p ≫ L.dTo n by
        simpa [p] using (α.comm p n).symm]
      exact Limits.imageSubobject_factors_comp_self (f := L.dTo n) (α.f p)
    have hFactorsPull : P.Factors (K.dTo n) :=
      Limits.pullback_factors (α.f n) (imageSubobject (L.dTo n)) (K.dTo n) hFactorsImage
    exact Limits.imageSubobject_le (K.dTo n) (P.factorThru (K.dTo n) hFactorsPull)
      (P.factorThru_arrow (K.dTo n) hFactorsPull)
  have hright : P ≤ imageSubobject (K.dTo n) := by
    -- Route correction: use the canonical local-boundary criterion for `Mono (homologyMap α n)`.
    -- This packages the same boundary-chasing argument into a transport-stable mathlib theorem.
    let q : ℤ := (ComplexShape.up ℤ).next n
    obtain ⟨A₁, ρ₁, hρ₁, y, hy⟩ :=
      surjective_up_to_refinements_of_epi (factorThruImageSubobject (L.dTo n)) z₀
    have hyx : ρ₁ ≫ x ≫ α.f n = y ≫ L.dTo n := by
      calc
        ρ₁ ≫ x ≫ α.f n = ρ₁ ≫ (x ≫ α.f n) := by simp
        _ = ρ₁ ≫ (z₀ ≫ (imageSubobject (L.dTo n)).arrow) := by rw [hxpull]
        _ = (ρ₁ ≫ z₀) ≫ (imageSubobject (L.dTo n)).arrow := by simp
        _ = y ≫ factorThruImageSubobject (L.dTo n) ≫ (imageSubobject (L.dTo n)).arrow := by
              simpa using
                congrArg (fun t => t ≫ (imageSubobject (L.dTo n)).arrow) hy
        _ = y ≫ L.dTo n := by simp
    have hcycleKα : ((ρ₁ ≫ x) ≫ K.d n q) ≫ α.f q = 0 := by
      calc
        ((ρ₁ ≫ x) ≫ K.d n q) ≫ α.f q = ρ₁ ≫ x ≫ (K.d n q ≫ α.f q) := by
          simp [Category.assoc]
        _ = ρ₁ ≫ x ≫ (α.f n ≫ L.d n q) := by
              rw [show K.d n q ≫ α.f q = α.f n ≫ L.d n q by
                simpa [q] using (α.comm n q)]
        _ = ρ₁ ≫ x ≫ α.f n ≫ L.d n q := by simp
        _ = y ≫ L.dTo n ≫ L.d n q := by
              simpa [Category.assoc] using congrArg (fun t => t ≫ L.d n q) hyx
        _ = y ≫ (L.dTo n ≫ L.d n q) := by simp
        _ = y ≫ (L.d p n ≫ L.d n q) := by simp [p]
        _ = 0 := by rw [L.d_comp_d p n q, comp_zero]
    have hcycleK : (ρ₁ ≫ x) ≫ K.d n q = 0 := by
      letI : Mono (α.f q) := hmono q
      exact (cancel_mono (α.f q)).1 (by simpa [Category.assoc] using hcycleKα)
    letI : Mono (homologyMap α n) := by infer_instance
    obtain ⟨A₂, ρ₂, hρ₂, v, hv⟩ :=
      ((HomologicalComplex.mono_homologyMap_iff_up_to_refinements
          (K := K) (L := L) (φ := α) p n q (by simp [p]) (by simp [q])).1
        (inferInstanceAs (Mono (homologyMap α n))))
        (ρ₁ ≫ x) hcycleK y (by simpa [p] using hyx)
    have hfacx : (ρ₂ ≫ ρ₁) ≫ x = v ≫ K.dTo n := by
      simpa [p, Category.assoc] using hv
    let e : A₂ ⟶ P := ρ₂ ≫ ρ₁
    haveI : Epi e := by
      dsimp [e]
      infer_instance
    calc
      P = imageSubobject x := by
            symm
            simpa [P, x] using (Limits.imageSubobject_mono x)
      _ = imageSubobject (e ≫ x) := by
            symm
            simpa [e] using imageSubobject_comp_eq_of_epi e x
      _ ≤ imageSubobject (K.dTo n) := by
            rw [hfacx]
            exact imageSubobject_comp_le v (K.dTo n)
  exact le_antisymm hright hleft

-- Proof sketch: apply `cokernel_acyclic_of_termwiseMono_quasiIso` to the cokernel complex of the
-- termwise-monomorphic quasi-isomorphism `α`, specialize the resulting acyclicity to degree `n`,
-- and then rewrite exactness in `𝒜` via `ShortComplex.exact_iff_image_eq_kernel` together with
-- the abelian mono/cokernel API.
/-- 13.18.6.1: for a quasi-isomorphism of cochain complexes that is termwise monomorphic, the
image of the incoming differential of `K` inside `L.X n` equals the intersection of the image of
`α.f n` with the image of the incoming differential of `L`. -/
@[stacks 013Q]
theorem image_prev_d_eq_inf_of_termwiseMono_quasiIso
    (hmono : ∀ n : ℤ, Mono (α.f n))
    (n : ℤ) :
    imageSubobject (K.dTo n ≫ α.f n) =
      imageSubobject (α.f n) ⊓ imageSubobject (L.dTo n) := by
  let hac : (cokernel α).Acyclic :=
    cokernel_acyclic_of_termwiseMono_quasiIso α hmono
  let _ : Mono (α.f n) := hmono n
  -- Rewrite both sides through the mono `α.f n`, then identify the pullback via cokernel exactness.
  calc
    imageSubobject (K.dTo n ≫ α.f n)
        = (Subobject.map (α.f n)).obj (imageSubobject (K.dTo n)) := by
            exact image_subobject_comp_eq_map_of_mono (K.dTo n) (α.f n)
    _ = (Subobject.map (α.f n)).obj
          ((Subobject.pullback (α.f n)).obj (imageSubobject (L.dTo n))) := by
            rw [pullback_image_dTo_eq_image_dTo_of_cokernel_acyclic (α := α) hmono hac n]
    _ = imageSubobject (α.f n) ⊓ imageSubobject (L.dTo n) := by
          simpa [Limits.imageSubobject_mono] using
            (Subobject.inf_eq_map_pullback' (MonoOver.mk (α.f n)) (imageSubobject (L.dTo n))).symm

end CochainComplex
