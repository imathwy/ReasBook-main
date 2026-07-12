import Mathlib
import LinearRepresentations_Serre_1977.Chap03.Definition_3_3_3_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Representation

noncomputable section

open DirectSum
open CategoryTheory Rep
open CategoryTheory Rep

section InducedFromSubrepresentation

variable {k : Type u} {G : Type v} [CommRing k] [Group G]
variable {V V' : Type (max u v w)} [AddCommGroup V] [AddCommGroup V']
variable [Module k V] [Module k V']

variable (ρ : Representation k G V) (H : Subgroup G)
variable (W : Subrepresentation (ρ.comp H.subtype))

/-- The chosen representative `q.out` realizes the `q`-indexed translate of `W`. -/
@[simp] theorem leftQuotientSubmodule_out (q : G ⧸ H) :
    ρ.leftQuotientSubmodule H W q = W.toSubmodule.map (ρ q.out) := by
  simpa using (ρ.leftQuotientSubmodule_mk H W q.out)

/-- Helper for Lemma 3-3.3-2: unwrap `IsInducedFromSubrepresentation` to the underlying internal
direct-sum statement. -/
private theorem isInternal_of_isInducedFromSubrepresentation
    (hρ : ρ.IsInducedFromSubrepresentation H W) :
    let _ : DecidableEq (G ⧸ H) := Classical.decEq (G ⧸ H)
    DirectSum.IsInternal (ρ.leftQuotientSubmodule H W) := by
  classical
  simpa [IsInducedFromSubrepresentation] using hρ

/-- Helper for Lemma 3-3.3-2: the restriction of a `G`-intertwining map to `W` is
`H`-equivariant. -/
private theorem restrictIntertwiningMap_isIntertwining
    (ρ' : Representation k G V') (F : ρ.IntertwiningMap ρ') :
    ∀ h : H, ∀ w : W.toSubmodule,
      (F.toLinearMap.comp W.toSubmodule.subtype) (W.toRepresentation h w) =
        (ρ'.comp H.subtype) h ((F.toLinearMap.comp W.toSubmodule.subtype) w) := by
  intro h w
  simpa using congr($(F.isIntertwining' h) w)

/-- Helper for Lemma 3-3.3-2: the restriction operator on intertwining maps is linear. -/
def restrictIntertwiningMap
    (ρ : Representation k G V) (H : Subgroup G) (W : Subrepresentation (ρ.comp H.subtype))
    (ρ' : Representation k G V') :
    ρ.IntertwiningMap ρ' →ₗ[k] W.toRepresentation.IntertwiningMap (ρ'.comp H.subtype) :=
  { toFun := fun F ↦
      (F.toLinearMap.comp W.toSubmodule.subtype).intertwiningMap_of_isIntertwiningMap
        W.toRepresentation (ρ'.comp H.subtype)
        (restrictIntertwiningMap_isIntertwining ρ H W ρ' F)
    map_add' := by
      intro F F'
      ext w
      rfl
    map_smul' := by
      intro a F
      ext w
      rfl }

@[simp] theorem restrictIntertwiningMap_apply
    (ρ : Representation k G V) (H : Subgroup G) (W : Subrepresentation (ρ.comp H.subtype))
    (ρ' : Representation k G V') (F : ρ.IntertwiningMap ρ') (w : W.toSubmodule) :
    restrictIntertwiningMap ρ H W ρ' F w = F w := by
  rfl

/-- The canonical morphism from `Ind_H^G(W)` to `ρ`, adjoint to the inclusion
`W ↪ Res_H^G(ρ)`. -/
noncomputable abbrev inducedFromSubrepresentationHom :
    Rep.ind H.subtype (Rep.of W.toRepresentation) ⟶ Rep.of ρ :=
  (Rep.indResHomEquiv H.subtype (Rep.of W.toRepresentation) (Rep.of ρ)).symm
    ((Rep.res H.subtype (Rep.of ρ)).subtype W.toSubmodule W.apply_mem_toSubmodule)

/-- Evaluating `inducedFromSubrepresentationHom` on `⟦g ⊗ w⟧` gives `ρ g⁻¹ w`. -/
@[simp] theorem inducedFromSubrepresentationHom_mk
    (g : G) (w : W.toSubmodule) :
    (inducedFromSubrepresentationHom ρ H W).hom (IndV.mk H.subtype W.toRepresentation g w) =
      ρ g⁻¹ w := by
  simpa [inducedFromSubrepresentationHom] using
    congrArg (ρ g⁻¹)
      (show ((Rep.res H.subtype (Rep.of ρ)).subtype W.toSubmodule W.apply_mem_toSubmodule).hom w =
          (w : V) from rfl)

/-- Helper for Lemma 3-3.3-2: transport `W` onto the `q`-indexed summand via the chosen
representative `q.out`. -/
noncomputable def leftQuotientSubmoduleEquiv (q : G ⧸ H) :
    W.toSubmodule ≃ₗ[k] ρ.leftQuotientSubmodule H W q :=
  let e : V ≃ₗ[k] V := LinearEquiv.ofBijective (ρ q.out) (ρ.apply_bijective q.out)
  (e.submoduleMap W.toSubmodule).trans
    (LinearEquiv.ofEq _ _ (ρ.leftQuotientSubmodule_out H W q).symm)

/-- Helper for Lemma 3-3.3-2: the transport equivalence acts by `ρ q.out` on `W`. -/
@[simp] theorem leftQuotientSubmoduleEquiv_apply (q : G ⧸ H) (w : W.toSubmodule) :
    ((ρ.leftQuotientSubmoduleEquiv H W q w : ρ.leftQuotientSubmodule H W q) : V) = ρ q.out w := by
  simp [leftQuotientSubmoduleEquiv]

/-- Helper for Lemma 3-3.3-2: the inverse transport equivalence acts by `ρ q.out⁻¹` on the
ambient vectors in the `q`-indexed summand. -/
@[simp] theorem leftQuotientSubmoduleEquiv_symm_apply
    (q : G ⧸ H) (x : ρ.leftQuotientSubmodule H W q) :
    (((ρ.leftQuotientSubmoduleEquiv H W q).symm x : W.toSubmodule) : V) = ρ (q.out⁻¹) x := by
  let e : V ≃ₗ[k] V := LinearEquiv.ofBijective (ρ q.out) (ρ.apply_bijective q.out)
  change (((e.submoduleMap W.toSubmodule).symm
      ((LinearEquiv.ofEq _ _ (ρ.leftQuotientSubmodule_out H W q).symm).symm x) : W.toSubmodule) :
        V) = ρ (q.out⁻¹) x
  apply (ρ.apply_bijective q.out).injective
  simp [e]

/-- Helper for Lemma 3-3.3-2: on the `q`-indexed homogeneous summand, extend `f` by first pulling
back to `W` and then translating by `ρ' q.out`. -/
def leftQuotientSubmoduleExtension
    (ρ' : Representation k G V')
    (f : W.toRepresentation.IntertwiningMap (ρ'.comp H.subtype))
    (q : G ⧸ H) :
    ρ.leftQuotientSubmodule H W q →ₗ[k] V' :=
  (ρ' q.out).comp (f.toLinearMap.comp (ρ.leftQuotientSubmoduleEquiv H W q).symm.toLinearMap)

/-- Helper for Lemma 3-3.3-2: the canonical linear extension obtained from the internal direct-sum
decomposition of the coset translates of `W`. -/
def extensionLinearMap
    (hρ : ρ.IsInducedFromSubrepresentation H W) (ρ' : Representation k G V')
    (f : W.toRepresentation.IntertwiningMap (ρ'.comp H.subtype)) :
    V →ₗ[k] V' :=
  letI : DecidableEq (G ⧸ H) := Classical.decEq _
  let hInternal : DirectSum.IsInternal (ρ.leftQuotientSubmodule H W) := by
    simpa [IsInducedFromSubrepresentation] using hρ
  letI := DirectSum.IsInternal.chooseDecomposition (ρ.leftQuotientSubmodule H W) hInternal
  (DirectSum.toModule k (G ⧸ H) V' (ρ.leftQuotientSubmoduleExtension H W ρ' f)).comp
    (DirectSum.decomposeLinearEquiv (ρ.leftQuotientSubmodule H W)).toLinearMap

/-- Helper for Lemma 3-3.3-2: an element supported on a single homogeneous summand is sent by the
global extension to the corresponding component extension. -/
theorem extensionLinearMap_apply_of_mem
    (hρ : ρ.IsInducedFromSubrepresentation H W) (ρ' : Representation k G V')
    (f : W.toRepresentation.IntertwiningMap (ρ'.comp H.subtype))
    {x : V} {q : G ⧸ H} (hx : x ∈ ρ.leftQuotientSubmodule H W q) :
    ρ.extensionLinearMap H W hρ ρ' f x =
      ρ.leftQuotientSubmoduleExtension H W ρ' f q ⟨x, hx⟩ := by
  classical
  letI : DecidableEq (G ⧸ H) := Classical.decEq _
  have hInternal : DirectSum.IsInternal (ρ.leftQuotientSubmodule H W) := by
    simpa [IsInducedFromSubrepresentation] using hρ
  letI := DirectSum.IsInternal.chooseDecomposition (ρ.leftQuotientSubmodule H W) hInternal
  have hxdecomp :
      DirectSum.decomposeLinearEquiv (ρ.leftQuotientSubmodule H W) x =
        DirectSum.lof k (G ⧸ H) (fun i ↦ ρ.leftQuotientSubmodule H W i) q ⟨x, hx⟩ := by
    simpa using
      (DirectSum.decomposeLinearEquiv_apply_coe
        (R := k) (ι := G ⧸ H) (ℳ := ρ.leftQuotientSubmodule H W) q ⟨x, hx⟩)
  rw [extensionLinearMap]
  calc
    (DirectSum.toModule k (G ⧸ H) V' (ρ.leftQuotientSubmoduleExtension H W ρ' f))
        ((DirectSum.decomposeLinearEquiv (ρ.leftQuotientSubmodule H W)).toLinearMap x)
        =
          (DirectSum.toModule k (G ⧸ H) V' (ρ.leftQuotientSubmoduleExtension H W ρ' f))
            (DirectSum.lof k (G ⧸ H) (fun i ↦ ρ.leftQuotientSubmodule H W i) q ⟨x, hx⟩) := by
          simpa [LinearMap.comp_apply] using
            congrArg
              (DirectSum.toModule k (G ⧸ H) V'
                (ρ.leftQuotientSubmoduleExtension H W ρ' f))
              hxdecomp
    _ = ρ.leftQuotientSubmoduleExtension H W ρ' f q ⟨x, hx⟩ := by
          exact DirectSum.toModule_lof
            (R := k) (ι := G ⧸ H)
            (M := fun i ↦ ρ.leftQuotientSubmodule H W i)
            (N := V') (φ := ρ.leftQuotientSubmoduleExtension H W ρ' f) q ⟨x, hx⟩

/-- Helper for Lemma 3-3.3-2: the canonical linear extension agrees with `f` on the original
subrepresentation `W`. -/
theorem extensionLinearMap_extends
    (hρ : ρ.IsInducedFromSubrepresentation H W) (ρ' : Representation k G V')
    (f : W.toRepresentation.IntertwiningMap (ρ'.comp H.subtype))
    (w : W.toSubmodule) :
    ρ.extensionLinearMap H W hρ ρ' f w = f w := by
  classical
  let q : G ⧸ H := QuotientGroup.mk 1
  have hq_rel : QuotientGroup.leftRel H q.out 1 := by
    exact Quotient.exact' (by simp [q])
  rw [QuotientGroup.leftRel_apply] at hq_rel
  have hq_mem : q.out ∈ H := by
    simpa using H.inv_mem hq_rel
  let h : H := ⟨q.out, hq_mem⟩
  let winv : W.toSubmodule := ⟨ρ (q.out⁻¹) w, W.apply_mem_toSubmodule h⁻¹ w.property⟩
  have hwq : (w : V) ∈ ρ.leftQuotientSubmodule H W q := by
    rw [ρ.leftQuotientSubmodule_out H W q]
    exact Submodule.mem_map.mpr ⟨winv, winv.property, by
      change ρ q.out (ρ (q.out⁻¹) w) = w
      simp⟩
  have hsymm :
      (ρ.leftQuotientSubmoduleEquiv H W q).symm ⟨w, hwq⟩ = winv := by
    ext
    simp [winv]
  rw [ρ.extensionLinearMap_apply_of_mem H W hρ ρ' f hwq]
  change ρ' q.out (f ((ρ.leftQuotientSubmoduleEquiv H W q).symm ⟨w, hwq⟩)) = f w
  rw [hsymm]
  have hwint : f winv = ρ' (q.out⁻¹) (f w) := by
    simpa [h, winv] using
      (Representation.IntertwiningMap.isIntertwining (f := f) (g := h⁻¹) (v := w))
  rw [hwint]
  simp

/-- Helper for Lemma 3-3.3-2: the canonical linear extension is `G`-equivariant. -/
theorem extensionLinearMap_isIntertwining
    (hρ : ρ.IsInducedFromSubrepresentation H W) (ρ' : Representation k G V')
    (f : W.toRepresentation.IntertwiningMap (ρ'.comp H.subtype)) :
    ∀ s : G, ∀ x : V,
      ρ.extensionLinearMap H W hρ ρ' f (ρ s x) =
        ρ' s (ρ.extensionLinearMap H W hρ ρ' f x) := by
  classical
  let ℳ : G ⧸ H → Submodule k V := ρ.leftQuotientSubmodule H W
  letI : DecidableEq (G ⧸ H) := Classical.decEq _
  have hInternal : DirectSum.IsInternal ℳ := by
    simpa [ℳ, IsInducedFromSubrepresentation] using hρ
  letI := DirectSum.IsInternal.chooseDecomposition ℳ hInternal
  intro s x
  refine DirectSum.Decomposition.inductionOn (ℳ := ℳ)
      (motive := fun x : V ↦
        ρ.extensionLinearMap H W hρ ρ' f (ρ s x) =
          ρ' s (ρ.extensionLinearMap H W hρ ρ' f x))
      ?_ ?_ ?_ x
  · simp [extensionLinearMap]
  · intro q x
    let w : W.toSubmodule := (ρ.leftQuotientSubmoduleEquiv H W q).symm x
    have hx :
        (x : V) = ρ q.out w := by
      calc
        (x : V) = ((ρ.leftQuotientSubmoduleEquiv H W q w : ρ.leftQuotientSubmodule H W q) : V) := by
          exact congrArg
            (fun y : ρ.leftQuotientSubmodule H W q ↦ (y : V))
            ((ρ.leftQuotientSubmoduleEquiv H W q).apply_symm_apply x).symm
        _ = ρ q.out w := by simp
    have hq :
        QuotientGroup.leftRel H ((s • q).out) (s * q.out) := by
      apply Quotient.exact'
      calc
        ((s • q).out : G ⧸ H) = s • q := Quotient.out_eq' (s • q)
        _ = s • (q.out : G ⧸ H) := by
          exact congrArg (fun z : G ⧸ H ↦ s • z) (Quotient.out_eq' q).symm
        _ = (s * q.out : G ⧸ H) := rfl
    rw [QuotientGroup.leftRel_apply] at hq
    let t : H := ⟨((s • q).out)⁻¹ * (s * q.out), hq⟩
    let wt : W.toSubmodule := ⟨ρ t w, W.apply_mem_toSubmodule t w.property⟩
    have hsx :
        (ρ s x : V) = ρ (s • q).out wt := by
      calc
        ρ s x = ρ s (ρ q.out w) := by rw [hx]
        _ = ρ (s * q.out) w := by
          simp [Module.End.mul_apply, map_mul]
        _ = ρ ((s • q).out * t) w := by
          congr 1
          simp [t]
        _ = ρ (s • q).out (ρ t w) := by
          simp [Module.End.mul_apply, map_mul]
        _ = ρ (s • q).out wt := rfl
    have hsx_mem : ρ s x ∈ ρ.leftQuotientSubmodule H W (s • q) := by
      rw [ρ.leftQuotientSubmodule_out H W (s • q)]
      exact Submodule.mem_map.mpr ⟨wt, wt.property, hsx.symm⟩
    have hsymm_smul :
        (ρ.leftQuotientSubmoduleEquiv H W (s • q)).symm ⟨ρ s x, hsx_mem⟩ = wt := by
      ext
      simp [wt, hsx]
    calc
      ρ.extensionLinearMap H W hρ ρ' f (ρ s x) =
          ρ.leftQuotientSubmoduleExtension H W ρ' f (s • q) ⟨ρ s x, hsx_mem⟩ := by
        exact ρ.extensionLinearMap_apply_of_mem H W hρ ρ' f hsx_mem
      _ = ρ' (s • q).out (f wt) := by
        simp [leftQuotientSubmoduleExtension, hsymm_smul, wt]
      _ = ρ' (s * q.out) (f w) := by
        have hwt_def : wt = W.toRepresentation t w := by
          ext
          rfl
        have hwt : f wt = ρ' t (f w) := by
          rw [hwt_def]
          exact Representation.IntertwiningMap.isIntertwining (f := f) (g := t) (v := w)
        rw [hwt]
        calc
          ρ' (s • q).out (ρ' t (f w)) = ρ' (((s • q).out : G) * t) (f w) := by
            simp [Module.End.mul_apply, map_mul]
          _ = ρ' (s * q.out) (f w) := by
            congr 1
            simp [t]
      _ = ρ' s (ρ' q.out (f w)) := by
        calc
          ρ' (s * q.out) (f w) = ((ρ' s * ρ' q.out)) (f w) := by
            exact LinearMap.congr_fun (ρ'.map_mul s q.out) (f w)
          _ = ρ' s (ρ' q.out (f w)) := by simp [Module.End.mul_apply]
      _ = ρ' s (ρ.extensionLinearMap H W hρ ρ' f x) := by
        congr 1
        simpa [leftQuotientSubmoduleExtension, w] using
          (ρ.extensionLinearMap_apply_of_mem H W hρ ρ' f (x := x) (q := q) x.property).symm
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- Helper for Lemma 3-3.3-2: bundle the canonical extension as a `G`-intertwining map. -/
noncomputable abbrev extensionIntertwiningMap
    (hρ : ρ.IsInducedFromSubrepresentation H W) (ρ' : Representation k G V')
    (f : W.toRepresentation.IntertwiningMap (ρ'.comp H.subtype)) :
    ρ.IntertwiningMap ρ' :=
  (ρ.extensionLinearMap H W hρ ρ' f).intertwiningMap_of_isIntertwiningMap
    ρ ρ' (ρ.extensionLinearMap_isIntertwining H W hρ ρ' f)

/-- Helper for Lemma 3-3.3-2: a `G`-equivariant extension is determined by its values on `W`
because the translates of `W` form an internal direct sum. -/
theorem extensionIntertwiningMap_unique
    (hρ : ρ.IsInducedFromSubrepresentation H W) (ρ' : Representation k G V')
    (f : W.toRepresentation.IntertwiningMap (ρ'.comp H.subtype))
    (F : ρ.IntertwiningMap ρ') (hF : ∀ w : W.toSubmodule, F w = f w) :
    F = ρ.extensionIntertwiningMap H W hρ ρ' f := by
  classical
  apply IntertwiningMap.ext
  ext v
  let ℳ : G ⧸ H → Submodule k V := ρ.leftQuotientSubmodule H W
  letI : DecidableEq (G ⧸ H) := Classical.decEq _
  have hInternal : DirectSum.IsInternal ℳ := by
    simpa [ℳ, IsInducedFromSubrepresentation] using hρ
  letI := DirectSum.IsInternal.chooseDecomposition ℳ hInternal
  refine DirectSum.Decomposition.inductionOn (ℳ := ℳ)
      (motive := fun x : V ↦ F x = ρ.extensionIntertwiningMap H W hρ ρ' f x)
      ?_ ?_ ?_ v
  · simp [extensionIntertwiningMap, extensionLinearMap]
  · intro q x
    let w : W.toSubmodule := (ρ.leftQuotientSubmoduleEquiv H W q).symm x
    have hx :
        (x : V) = ρ q.out w := by
      calc
        (x : V) = ((ρ.leftQuotientSubmoduleEquiv H W q w : ρ.leftQuotientSubmodule H W q) : V) := by
          exact congrArg
            (fun y : ρ.leftQuotientSubmodule H W q ↦ (y : V))
            ((ρ.leftQuotientSubmoduleEquiv H W q).apply_symm_apply x).symm
        _ = ρ q.out w := by simp
    calc
      F x = F (ρ q.out w) := by rw [hx]
      _ = ρ' q.out (F w) := by
        simpa using
          (Representation.IntertwiningMap.isIntertwining (f := F) (g := q.out) (v := w))
      _ = ρ' q.out (f w) := by rw [hF w]
      _ = ρ.leftQuotientSubmoduleExtension H W ρ' f q x := by
        simp [leftQuotientSubmoduleExtension, w]
      _ = ρ.extensionIntertwiningMap H W hρ ρ' f x := by
        symm
        simpa [extensionIntertwiningMap] using
          ρ.extensionLinearMap_apply_of_mem H W hρ ρ' f (x := x) (q := q) x.property
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- Lemma 3-3.3-2: if `ρ` is induced from the `H`-subrepresentation `W`, then every `H`-equivariant
linear map from `W` to the restriction of `ρ'` extends uniquely to a `G`-equivariant linear map
from `V` to `V'`. -/
theorem existsUnique_intertwiningMap_of_isInducedFromSubrepresentation
    (ρ : Representation k G V) (H : Subgroup G) (W : Subrepresentation (ρ.comp H.subtype))
    (hρ : ρ.IsInducedFromSubrepresentation H W) (ρ' : Representation k G V')
    (f : W.toRepresentation.IntertwiningMap (ρ'.comp H.subtype)) :
    ∃! F : ρ.IntertwiningMap ρ', ∀ w : W.toSubmodule, F w = f w := by
  refine ⟨ρ.extensionIntertwiningMap H W hρ ρ' f, ?_, ?_⟩
  · exact ρ.extensionLinearMap_extends H W hρ ρ' f
  · intro F hF
    exact ρ.extensionIntertwiningMap_unique H W hρ ρ' f F hF

/-- Helper for Lemma 3-3.3-2: if `ρ` is induced from the `H`-subrepresentation `W`, then the
restriction map on intertwining spaces is bijective. -/
theorem bijective_restrictIntertwiningMap_of_isInducedFromSubrepresentation
    (ρ : Representation k G V) (H : Subgroup G) (W : Subrepresentation (ρ.comp H.subtype))
    (hρ : ρ.IsInducedFromSubrepresentation H W) (ρ' : Representation k G V') :
    Function.Bijective (restrictIntertwiningMap ρ H W ρ') := by
  constructor
  · intro F F' hFF'
    let f : W.toRepresentation.IntertwiningMap (ρ'.comp H.subtype) :=
      restrictIntertwiningMap ρ H W ρ' F
    have hF : ∀ w : W.toSubmodule, F w = f w := by
      intro w
      rfl
    have hF' : ∀ w : W.toSubmodule, F' w = f w := by
      intro w
      have hw := congrArg
        (fun g : W.toRepresentation.IntertwiningMap (ρ'.comp H.subtype) ↦ g w) hFF'
      simpa [f, restrictIntertwiningMap_apply] using hw.symm
    exact
      (ρ.existsUnique_intertwiningMap_of_isInducedFromSubrepresentation H W hρ ρ' f).unique
        hF hF'
  · intro f
    rcases
      ρ.existsUnique_intertwiningMap_of_isInducedFromSubrepresentation H W hρ ρ' f
        with ⟨F, hF, _⟩
    refine ⟨F, ?_⟩
    ext w
    simpa [restrictIntertwiningMap_apply] using hF w

/-- Helper for Lemma 3-3.3-2: unpack
`existsUnique_intertwiningMap_of_isInducedFromSubrepresentation` on the underlying linear maps. -/
theorem existsUnique_intertwiningMap_comp_subtype_eq_of_isInducedFromSubrepresentation
    (ρ : Representation k G V) (H : Subgroup G) (W : Subrepresentation (ρ.comp H.subtype))
    (hρ : ρ.IsInducedFromSubrepresentation H W) (ρ' : Representation k G V')
    (f : W.toRepresentation.IntertwiningMap (ρ'.comp H.subtype)) :
    ∃! F : ρ.IntertwiningMap ρ',
      F.toLinearMap.comp W.toSubmodule.subtype = f.toLinearMap := by
  let hrestrict :=
    existsUnique_intertwiningMap_of_isInducedFromSubrepresentation ρ H W hρ ρ' f
  exact (existsUnique_congr fun F ↦ by
    constructor
    · intro hF
      ext w
      exact hF w
    · intro hF w
      exact LinearMap.congr_fun hF w).1 hrestrict

end InducedFromSubrepresentation

end

end Representation
