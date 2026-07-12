import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Distributive.Monoidal
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.LinearAlgebra.TensorProduct.Submodule
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import StacksProject_2024.Chap15.Definition_15_28_2
import StacksProject_2024.Chap15.Lemma_15_28_3
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory
open HomologicalComplex
open MonoidalCategory
open scoped KoszulComplex

section

variable {R : Type u} [CommRing R]
variable {E E' : Type u} [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R E']

/- Domain-style sampling:
- primary domain: tensor-product comparisons for Koszul chain complexes;
- owner declarations inspected: `koszulComplex`, `koszulLinearForm`, `KoszulComplex.map`,
  `LinearEquiv.sumArrowLequivProdArrow`, `LinearEquiv.piCongrLeft`,
  `AlternatingMap.domCoprod`, and
  `HomologicalComplex.Hom.isoOfComponents`;
- best owner abstraction: the linear-map-level Koszul complex `koszulComplex`, with the
  finite-family bridge owned upstream by `koszulLinearForm`, `K^•(-)`, and the canonical
  function-space linear equivalences;
- primitive data: linear forms `φ : E →ₗ[R] R` and `ψ : E' →ₗ[R] R`;
- derived API: the `Fin.append` comparison for `K^•(-)`, obtained from the owner-level direct-sum
  comparison after transporting along the canonical tuple owner `koszulLinearForm` and the
  canonical tuple-index owner `finSumFinEquiv`;
- layer triage: `koszulComplex_coprod_iso_tensorObj` is the public `core/canonical` bridge, while
  `koszulComplexOn_append_iso_tensorObj` is the public `bridge/view` specialization matching the
  source family notation.
-/

-- Thin private linear bridge expressing `Fin.append` and its canonical splitting directly.
private noncomputable def finAppendLinearEquiv (r s : ℕ) :
    ((Fin r → R) × (Fin s → R)) ≃ₗ[R] (Fin (r + s) → R) :=
  { toFun := fun x ↦ Fin.append x.1 x.2
    invFun := fun x ↦ (fun i ↦ x (Fin.castAdd s i), fun i ↦ x (Fin.natAdd r i))
    map_add' := by
      intro x y
      ext i
      cases i using Fin.addCases <;> simp [Fin.append]
    map_smul' := by
      intro a x
      ext i
      cases i using Fin.addCases <;> simp [Fin.append]
    left_inv := by
      intro x
      ext i <;> simp [Fin.append_left, Fin.append_right]
    right_inv := by
      intro x
      ext i
      cases i using Fin.addCases <;> simp [Fin.append_left, Fin.append_right] }

@[simp] private theorem finAppendLinearEquiv_apply {r s : ℕ} (x : (Fin r → R) × (Fin s → R)) :
    finAppendLinearEquiv r s x = Fin.append x.1 x.2 :=
  rfl

@[simp] private theorem finAppendLinearEquiv_symm_apply {r s : ℕ} (x : Fin (r + s) → R) :
    (finAppendLinearEquiv r s).symm x = (fun i ↦ x (Fin.castAdd s i), fun i ↦ x (Fin.natAdd r i)) :=
  rfl

-- Proof sketch: the canonical linear equivalence from `((Fin r → R) × (Fin s → R))` to
-- `(Fin (r + s) → R)` identifies a pair of coefficient functions with the function on
-- `Fin (r + s)` obtained by `Fin.append`; evaluating `Module.piEquiv` on the concatenated family
-- then splits into the two summands defining `LinearMap.coprod`.
private theorem koszulLinearForm_append_comp_symm {r s : ℕ}
    (f : Fin r → R) (g : Fin s → R) :
    ((koszulLinearForm f).coprod (koszulLinearForm g)).comp
        (finAppendLinearEquiv r s).symm.toLinearMap =
      koszulLinearForm (Fin.append f g) := by
  apply LinearMap.ext
  intro x
  -- Rewrite both linear forms as explicit finite sums, then split the `Fin (r + s)` sum along the
  -- canonical `Fin r ⊕ Fin s ≃ Fin (r + s)` equivalence.
  calc
    ((koszulLinearForm f).coprod (koszulLinearForm g))
        ((finAppendLinearEquiv r s).symm x) =
      ∑ i : Fin r, x (Fin.castAdd s i) * f i + ∑ i : Fin s, x (Fin.natAdd r i) * g i := by
        simp [koszulLinearForm, Module.piEquiv_apply_apply, finAppendLinearEquiv_symm_apply,
          mul_comm]
    _ = ∑ z : Fin r ⊕ Fin s, Sum.elim
          (fun i : Fin r ↦ x (Fin.castAdd s i) * f i)
          (fun j : Fin s ↦ x (Fin.natAdd r j) * g j) z := by
        symm
        exact Fintype.sum_sum_type _
    _ = ∑ i : Fin (r + s), x i * Fin.append f g i := by
        refine Fintype.sum_equiv finSumFinEquiv _ _ ?_
        intro z
        cases z <;> simp [finSumFinEquiv, Fin.append]
    _ = koszulLinearForm (Fin.append f g) x := by
        simp [koszulLinearForm, Module.piEquiv_apply_apply]

-- Proof sketch: compose the previous compatibility with the canonical linear equivalence from
-- `((Fin r → R) × (Fin s → R))` to `(Fin (r + s) → R)` and use that it is inverse to its own
-- inverse.
private theorem koszulLinearForm_append_comp {r s : ℕ}
    (f : Fin r → R) (g : Fin s → R) :
    (koszulLinearForm (Fin.append f g)).comp (finAppendLinearEquiv r s).toLinearMap =
      (koszulLinearForm f).coprod (koszulLinearForm g) := by
  apply LinearMap.ext
  intro x
  -- Evaluate on a split pair and rewrite the concatenated sum back into the two original parts.
  calc
    koszulLinearForm (Fin.append f g) ((finAppendLinearEquiv r s) x) =
      ∑ i : Fin (r + s), Fin.append x.1 x.2 i * Fin.append f g i := by
        simp [koszulLinearForm, Module.piEquiv_apply_apply, finAppendLinearEquiv_apply, mul_comm]
    _ = ∑ z : Fin r ⊕ Fin s, Sum.elim
          (fun i : Fin r ↦ x.1 i * f i)
          (fun j : Fin s ↦ x.2 j * g j) z := by
        refine Fintype.sum_equiv finSumFinEquiv.symm _ _ ?_
        intro i
        cases i using Fin.addCases <;> simp [finSumFinEquiv, Fin.append]
    _ = ∑ i : Fin r, x.1 i * f i + ∑ i : Fin s, x.2 i * g i := by
        exact Fintype.sum_sum_type _
    _ = ((koszulLinearForm f).coprod (koszulLinearForm g)) x := by
        simp [koszulLinearForm, Module.piEquiv_apply_apply]

-- Proof sketch: identify the Koszul complex on the direct-sum linear form `φ.coprod ψ` with the
-- tensor product differential graded algebra generated by the two factors. On exterior powers,
-- this yields the standard totalized tensor-product differential, which is exactly `tensorObj` on
-- chain complexes in mathlib.
private noncomputable def koszulComplex_coprod_to_tensorObjSummand
    (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) (n : ℕ) (p : Fin (n + 1)) :
    _root_.AlternatingMap R (ModuleCat.of R (E × E'))
      ((HomologicalComplex.tensorObj (koszulComplex φ) (koszulComplex ψ)).X n) (Fin n) :=
  let q : ℕ := n - p
  let hpq : (p : ℕ) + q = n := Nat.add_sub_of_le p.is_le
  let left : (E × E') [⋀^Fin p]→ₗ[R] ⋀[R]^p E :=
    (exteriorPower.ιMulti R p).compLinearMap (LinearMap.fst R E E')
  let right : (E × E') [⋀^Fin q]→ₗ[R] ⋀[R]^q E' :=
    (exteriorPower.ιMulti R q).compLinearMap (LinearMap.snd R E E')
  let alternating :
      _root_.AlternatingMap R (ModuleCat.of R (E × E'))
        ((((koszulComplex φ).X p) ⊗ ((koszulComplex ψ).X q) : ModuleCat R)) (Fin n) :=
    (left.domCoprod right).domDomCongr (finSumFinEquiv.trans (finCongr hpq))
  let ι :
      ((((koszulComplex φ).X p) ⊗ ((koszulComplex ψ).X q) : ModuleCat R)) ⟶
        (HomologicalComplex.tensorObj (koszulComplex φ) (koszulComplex ψ)).X n :=
    HomologicalComplex.ιTensorObj (koszulComplex φ) (koszulComplex ψ) p q n hpq
  ι.hom.compAlternatingMap alternating

private noncomputable def koszulComplex_coprod_to_tensorObjComponent
    (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) (n : ℕ) :
    (koszulComplex (φ.coprod ψ)).X n ⟶
      (HomologicalComplex.tensorObj (koszulComplex φ) (koszulComplex ψ)).X n :=
  ModuleCat.ofHom <|
    exteriorPower.alternatingMapLinearEquiv
      (∑ p : Fin (n + 1), koszulComplex_coprod_to_tensorObjSummand φ ψ n p)

/-- Helper for Lemma 15.28.12: after coercing to the ambient exterior algebra, the degreewise
exterior-power map induced by a linear map agrees with the ambient algebra map. -/
private theorem exteriorPower_map_coe
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) (x : ⋀[R]^n M) :
    ((exteriorPower.map n f x : ⋀[R]^n N) : ExteriorAlgebra R N) = ExteriorAlgebra.map f x := by
  -- Proof comment: the universal property of `⋀^n` reduces the comparison to `ιMulti`
  -- generators, where both maps are definitionally the same ambient exterior-algebra map.
  have hsubtype :
      (Submodule.subtype (⋀[R]^n N)).comp (exteriorPower.map n f) =
        (ExteriorAlgebra.map f).toLinearMap.comp (Submodule.subtype (⋀[R]^n M)) := by
    apply exteriorPower.linearMap_ext
    ext m
    simp [LinearMap.comp_apply]
  exact LinearMap.congr_fun hsubtype x

/-- Helper for Lemma 15.28.12: before restricting back to a fixed exterior-power degree, the
reverse summand multiplies the two images in the ambient exterior algebra on `E × E'`. -/
private noncomputable def tensorObj_to_koszulComplex_coprodSummandAmbient
    (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) (p q : ℕ) :
    TensorProduct R (⋀[R]^p E) (⋀[R]^q E') →ₗ[R] ExteriorAlgebra R (E × E') :=
  let left : ⋀[R]^p E →ₗ[R] ExteriorAlgebra R (E × E') :=
    (ExteriorAlgebra.map (LinearMap.inl R E E')).toLinearMap.comp (Submodule.subtype _)
  let right : ⋀[R]^q E' →ₗ[R] ExteriorAlgebra R (E × E') :=
    (ExteriorAlgebra.map (LinearMap.inr R E E')).toLinearMap.comp (Submodule.subtype _)
  (LinearMap.mul' R (ExteriorAlgebra R (E × E'))).comp (TensorProduct.map left right)

/-- Helper for Lemma 15.28.12: on a pure tensor, the ambient reverse multiplication lands in
degree `p + q` because the two factors already lie in degrees `p` and `q`. -/
private theorem tensorObj_to_koszulComplex_coprodSummandAmbient_mem_tmul
    (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) (p q : ℕ)
    (x : ⋀[R]^p E) (y : ⋀[R]^q E') :
    tensorObj_to_koszulComplex_coprodSummandAmbient φ ψ p q (x ⊗ₜ[R] y) ∈
      ⋀[R]^(p + q) (E × E') := by
  have hleft : ExteriorAlgebra.map (LinearMap.inl R E E') x ∈ ⋀[R]^p (E × E') := by
    -- Coerce the degree-`p` exterior-power map to the ambient algebra and read off membership.
    rw [← exteriorPower_map_coe (f := LinearMap.inl R E E') (n := p) x]
    exact (exteriorPower.map p (LinearMap.inl R E E') x).2
  have hright : ExteriorAlgebra.map (LinearMap.inr R E E') y ∈ ⋀[R]^q (E × E') := by
    -- The right factor is identical after the same degreewise-to-ambient comparison.
    rw [← exteriorPower_map_coe (f := LinearMap.inr R E E') (n := q) y]
    exact (exteriorPower.map q (LinearMap.inr R E E') y).2
  -- Multiply the two ambient graded pieces and use the graded-algebra product rule.
  simp only [tensorObj_to_koszulComplex_coprodSummandAmbient, LinearMap.comp_apply,
    TensorProduct.map_tmul, LinearMap.mul'_apply]
  rw [ExteriorAlgebra.exteriorPower] at hleft hright ⊢
  simpa [add_comm, add_left_comm, add_assoc] using SetLike.mul_mem_graded hleft hright

/-- Helper for Lemma 15.28.12: the ambient reverse summand lands in degree `p + q`, so it can be
restricted back to the `(p + q)`th exterior power. -/
private theorem tensorObj_to_koszulComplex_coprodSummand_ambient_mem
    (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) (p q : ℕ)
    (z : TensorProduct R (⋀[R]^p E) (⋀[R]^q E')) :
    tensorObj_to_koszulComplex_coprodSummandAmbient φ ψ p q z ∈ ⋀[R]^(p + q) (E × E') := by
  -- Reduce the codomain-membership check to pure tensors, where graded multiplication is explicit.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp [tensorObj_to_koszulComplex_coprodSummandAmbient]
  · intro x y
    exact tensorObj_to_koszulComplex_coprodSummandAmbient_mem_tmul φ ψ p q x y
  · intro z w hz hw
    -- The ambient reverse summand is linear, so the degree condition is stable under addition.
    simpa [map_add] using Submodule.add_mem (⋀[R]^(p + q) (E × E')) hz hw

/-- Helper for Lemma 15.28.12: the reverse degree-`(p,q)` summand is the multiplication map from
the `LinearMap.inl` and `LinearMap.inr` images of the two fixed-degree exterior powers. -/
private noncomputable def tensorObj_to_koszulComplex_coprodSummand
    (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) (p q : ℕ) :
    (((koszulComplex φ).X p) ⊗ ((koszulComplex ψ).X q) : ModuleCat R) ⟶
      (koszulComplex (φ.coprod ψ)).X (p + q) :=
  -- Route correction: use the ambient exterior-algebra multiplication first, then restrict to
  -- degree `p + q` with the separate grading lemma above.
  ModuleCat.ofHom <|
    LinearMap.codRestrict
      (⋀[R]^(p + q) (E × E'))
      (tensorObj_to_koszulComplex_coprodSummandAmbient φ ψ p q)
      (tensorObj_to_koszulComplex_coprodSummand_ambient_mem φ ψ p q)

/-- Helper for Lemma 15.28.12: in the ambient exterior algebra, multiplying the `inl` image of a
`p`-fold wedge with the `inr` image of a `q`-fold wedge gives the concatenated wedge on
`Fin.append`. -/
private theorem ambient_ιMulti_append_inl_inr
    (p q : ℕ) (u : Fin p → E) (v : Fin q → E') :
    ExteriorAlgebra.map (LinearMap.inl R E E') (exteriorPower.ιMulti R p u) *
        ExteriorAlgebra.map (LinearMap.inr R E E') (exteriorPower.ιMulti R q v) =
      exteriorPower.ιMulti R (p + q)
        (Fin.append (LinearMap.inl R E E' ∘ u) (LinearMap.inr R E E' ∘ v)) := by
  -- TODO(Lemma 15.28.12): prove the ambient append formula by induction on `p`, using
  -- `ExteriorAlgebra.map_apply_ιMulti`, `ExteriorAlgebra.ιMulti_succ_apply`, and an explicit
  -- `Matrix.vecTail` identification for `Fin.append`.
  sorry

/-- Helper for Lemma 15.28.12: on pure `ιMulti` tensors, the reverse degree-`(p,q)` summand is
exactly the concatenated wedge in degree `p + q`. -/
private theorem tensorObj_to_koszulComplex_coprodSummand_apply_ιMulti_tmul_ιMulti
    (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) (p q : ℕ)
    (u : Fin p → E) (v : Fin q → E') :
    tensorObj_to_koszulComplex_coprodSummand φ ψ p q
        (exteriorPower.ιMulti R p u ⊗ₜ[R] exteriorPower.ιMulti R q v) =
      exteriorPower.ιMulti R (p + q)
        (Fin.append (LinearMap.inl R E E' ∘ u) (LinearMap.inr R E E' ∘ v)) := by
  -- Proof comment: `codRestrict` only repackages the ambient multiplication formula as a point of
  -- the fixed degree-`p + q` exterior power.
  apply Subtype.ext
  simp only [tensorObj_to_koszulComplex_coprodSummand, LinearMap.codRestrict_apply,
    tensorObj_to_koszulComplex_coprodSummandAmbient, LinearMap.comp_apply,
    TensorProduct.map_tmul, LinearMap.mul'_apply]
  exact ambient_ιMulti_append_inl_inr (R := R) p q u v

/-- Helper for Lemma 15.28.12: on the left block of an appended `inl`/`inr` generator family,
the first projection recovers the original left tuple. -/
private theorem fst_append_inl_inr_castAdd
    (p q : ℕ) (u : Fin p → E) (v : Fin q → E') :
    (fun i : Fin p ↦
        LinearMap.fst R E E'
          ((Fin.append (LinearMap.inl R E E' ∘ u) (LinearMap.inr R E E' ∘ v))
            (Fin.castAdd q i))) = u := by
  -- Proof comment: `Fin.castAdd` stays in the left block, where `Fin.append` is the `inl`
  -- branch and `LinearMap.fst` cancels `LinearMap.inl`.
  funext i
  simp [Fin.append]

/-- Helper for Lemma 15.28.12: on the right block of an appended `inl`/`inr` generator family,
the second projection recovers the original right tuple. -/
private theorem snd_append_inl_inr_natAdd
    (p q : ℕ) (u : Fin p → E) (v : Fin q → E') :
    (fun i : Fin q ↦
        LinearMap.snd R E E'
          ((Fin.append (LinearMap.inl R E E' ∘ u) (LinearMap.inr R E E' ∘ v))
            (Fin.natAdd p i))) = v := by
  -- Proof comment: `Fin.natAdd` lands in the right block, where `Fin.append` is the `inr`
  -- branch and `LinearMap.snd` cancels `LinearMap.inr`.
  funext i
  simp [Fin.append]

/-- Helper for Lemma 15.28.12: on the left block of an appended `inl`/`inr` generator family,
the second projection is zero. -/
private theorem snd_append_inl_inr_castAdd
    (p q : ℕ) (u : Fin p → E) (v : Fin q → E') :
    (fun i : Fin p ↦
        LinearMap.snd R E E'
          ((Fin.append (LinearMap.inl R E E' ∘ u) (LinearMap.inr R E E' ∘ v))
            (Fin.castAdd q i))) = 0 := by
  -- Proof comment: the left block consists of `LinearMap.inl` generators, and their second
  -- projection vanishes.
  funext i
  simp [Fin.append]

/-- Helper for Lemma 15.28.12: on the right block of an appended `inl`/`inr` generator family,
the first projection is zero. -/
private theorem fst_append_inl_inr_natAdd
    (p q : ℕ) (u : Fin p → E) (v : Fin q → E') :
    (fun i : Fin q ↦
        LinearMap.fst R E E'
          ((Fin.append (LinearMap.inl R E E' ∘ u) (LinearMap.inr R E E' ∘ v))
            (Fin.natAdd p i))) = 0 := by
  -- Proof comment: the right block consists of `LinearMap.inr` generators, and their first
  -- projection vanishes.
  funext i
  simp [Fin.append]

/-- Helper for Lemma 15.28.12: transporting the reverse `(p,q)` summand along an equality
`p + q = n` gives the corresponding map into degree `n`. -/
private noncomputable def tensorObj_to_koszulComplex_coprodSummandTo
    (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) (p q n : ℕ) (h : p + q = n) :
    (((koszulComplex φ).X p) ⊗ ((koszulComplex ψ).X q) : ModuleCat R) ⟶
      (koszulComplex (φ.coprod ψ)).X n :=
  h ▸ tensorObj_to_koszulComplex_coprodSummand φ ψ p q

/-- Helper for Lemma 15.28.12: the reverse degree-`n` component is obtained by descending the
degreewise multiplication maps from the tensor totalization summands. -/
private noncomputable def tensorObj_to_koszulComplex_coprodComponent
    (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) (n : ℕ) :
    (HomologicalComplex.tensorObj (koszulComplex φ) (koszulComplex ψ)).X n ⟶
      (koszulComplex (φ.coprod ψ)).X n :=
  -- Proof comment: the totalized tensor product is a coproduct over all decompositions
  -- `p + q = n`, so `mapBifunctorDesc` is the canonical owner-level descender.
  HomologicalComplex.mapBifunctorDesc
    (K₁ := koszulComplex φ) (K₂ := koszulComplex ψ)
    (F := curriedTensor (ModuleCat R)) (c := ComplexShape.down ℕ)
    (fun p q h ↦ tensorObj_to_koszulComplex_coprodSummandTo φ ψ p q n h)

/-- Helper for Lemma 15.28.12: precomposing the reverse degree-`n` component with a tensor
summand inclusion recovers the corresponding `(p,q)` summand map. -/
@[reassoc]
private theorem ιTensorObj_tensorObj_to_koszulComplex_coprodComponent
    (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) (n p q : ℕ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj (koszulComplex φ) (koszulComplex ψ) p q n h ≫
        tensorObj_to_koszulComplex_coprodComponent φ ψ n =
      tensorObj_to_koszulComplex_coprodSummandTo φ ψ p q n h := by
  -- Proof comment: cross the `tensorObj` abbreviation once, then use the owner universal
  -- property `ι_mapBifunctorDesc` for the descended reverse component.
  simpa only [HomologicalComplex.ιTensorObj] using
    (HomologicalComplex.ι_mapBifunctorDesc
      (K₁ := koszulComplex φ) (K₂ := koszulComplex ψ)
      (F := curriedTensor (ModuleCat R)) (c := ComplexShape.down ℕ)
      (A := (koszulComplex (φ.coprod ψ)).X n) (j := n)
      (f := fun p q h ↦ tensorObj_to_koszulComplex_coprodSummandTo φ ψ p q n h) p q h)

/-- Helper for Lemma 15.28.12: the matching forward summand sends an appended `ιMulti`
generator to the canonical `(p,q)` tensor summand. -/
private theorem koszulComplex_coprod_to_tensorObjSummand_apply_ιMulti_append
    (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) (p q : ℕ)
    (u : Fin p → E) (v : Fin q → E') :
    (exteriorPower.alternatingMapLinearEquiv
        (koszulComplex_coprod_to_tensorObjSummand φ ψ (p + q)
          ⟨p, Nat.lt_succ_of_le (Nat.le_add_right p q)⟩))
        (exteriorPower.ιMulti R (p + q)
          (Fin.append (LinearMap.inl R E E' ∘ u) (LinearMap.inr R E E' ∘ v))) =
      HomologicalComplex.ιTensorObj (koszulComplex φ) (koszulComplex ψ) p q (p + q) rfl
        (exteriorPower.ιMulti R p u ⊗ₜ[R] exteriorPower.ιMulti R q v) := by
  -- TODO(Lemma 15.28.12): convert back through `alternatingMapLinearEquiv`, unfold the matching
  -- `domCoprod` summand once, and rewrite the two projected blocks with
  -- `fst_append_inl_inr_castAdd` and `snd_append_inl_inr_natAdd`.
  sorry

/-- Helper for Lemma 15.28.12: every off-diagonal forward summand vanishes on appended
`ιMulti` generators because one projected coordinate is forced to zero. -/
private theorem koszulComplex_coprod_to_tensorObjSummand_apply_ιMulti_append_eq_zero_of_ne
    (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) (p q : ℕ)
    (p' : Fin (p + q + 1))
    (hp' : p' ≠ ⟨p, Nat.lt_succ_of_le (Nat.le_add_right p q)⟩)
    (u : Fin p → E) (v : Fin q → E') :
    (exteriorPower.alternatingMapLinearEquiv
        (koszulComplex_coprod_to_tensorObjSummand φ ψ (p + q) p'))
        (exteriorPower.ιMulti R (p + q)
          (Fin.append (LinearMap.inl R E E' ∘ u) (LinearMap.inr R E E' ∘ v))) = 0 := by
  -- TODO(Lemma 15.28.12): after moving back to the underlying alternating map, split on
  -- `(p' : ℕ) < p` versus `p < (p' : ℕ)` and kill the right or left factor with
  -- `AlternatingMap.map_coord_zero`.
  sorry

/-- Helper for Lemma 15.28.12: the full forward degree-`p + q` component collapses to the
unique matching summand on appended `ιMulti` generators. -/
private theorem koszulComplex_coprod_to_tensorObjComponent_apply_ιMulti_append
    (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) (p q : ℕ)
    (u : Fin p → E) (v : Fin q → E') :
    koszulComplex_coprod_to_tensorObjComponent φ ψ (p + q)
        (exteriorPower.ιMulti R (p + q)
          (Fin.append (LinearMap.inl R E E' ∘ u) (LinearMap.inr R E E' ∘ v))) =
      HomologicalComplex.ιTensorObj (koszulComplex φ) (koszulComplex ψ) p q (p + q) rfl
        (exteriorPower.ιMulti R p u ⊗ₜ[R] exteriorPower.ιMulti R q v) := by
  -- TODO(Lemma 15.28.12): pull the finite sum through `alternatingMapLinearEquiv`, isolate the
  -- diagonal index with `Finset.sum_eq_single`, and use the two preceding generator formulas.
  sorry

private theorem koszulComplex_coprod_to_tensorObjComponent_commSq
    (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    CommSq
      (koszulComplex_coprod_to_tensorObjComponent φ ψ i)
      ((koszulComplex (φ.coprod ψ)).d i j)
      ((HomologicalComplex.tensorObj (koszulComplex φ) (koszulComplex ψ)).d i j)
      (koszulComplex_coprod_to_tensorObjComponent φ ψ j) := by
  rcases i with _ | i
  · cases hij
  · obtain rfl : j = i := by
      simpa [ComplexShape.down] using hij
    refine ⟨?_⟩
    -- TODO(Lemma 15.28.12): compare the degree-`i+1` differential on `φ.coprod ψ` with the two
    -- summands of the tensor-product differential on `koszulComplex φ ⊗ koszulComplex ψ`,
    -- then check equality on `ιMulti` generators using the explicit summand formula.
    sorry

private theorem isIso_koszulComplex_coprod_to_tensorObjComponent
    (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) (n : ℕ) :
    IsIso (koszulComplex_coprod_to_tensorObjComponent φ ψ n) := by
  -- Proof comment: the inverse component is now the explicit descended multiplication map
  -- `tensorObj_to_koszulComplex_coprodComponent φ ψ n`; what remains is to prove the two
  -- composites are identities on tensor summands and `ιMulti` generators.
  -- TODO(Lemma 15.28.12): use `tensorObj_to_koszulComplex_coprodComponent φ ψ n` as the inverse,
  -- prove `hom_inv_id` by `HomologicalComplex.mapBifunctor.hom_ext` on each `(p,q)` summand, and
  -- prove `inv_hom_id` by `ModuleCat.hom_ext` and `exteriorPower.linearMap_ext` on `ιMulti`
  -- generators of `⋀[R]^n (E × E')`.
  sorry

private noncomputable def koszulComplex_coprod_tensorObjComponentIso
    (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) (n : ℕ) :
    (koszulComplex (φ.coprod ψ)).X n ≅
      (HomologicalComplex.tensorObj (koszulComplex φ) (koszulComplex ψ)).X n :=
  let _ := isIso_koszulComplex_coprod_to_tensorObjComponent φ ψ n
  asIso (koszulComplex_coprod_to_tensorObjComponent φ ψ n)

/-- The Koszul complex of the coproduct linear form `φ.coprod ψ` is canonically isomorphic to the
tensor product of the Koszul complexes of `φ` and `ψ`. This is the owner-level comparison from
which tuple-indexed `Fin.append` specializations are obtained by transport along
`koszulLinearForm`. -/
noncomputable def koszulComplex_coprod_iso_tensorObj
    (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) :
    koszulComplex (φ.coprod ψ) ≅ koszulComplex φ ⊗ koszulComplex ψ :=
  Hom.isoOfComponents
    (koszulComplex_coprod_tensorObjComponentIso φ ψ)
    (fun i j hij ↦ (koszulComplex_coprod_to_tensorObjComponent_commSq φ ψ i j hij).w)

private def koszulComplexOn_append_iso_coprod {r s : ℕ}
    (f : Fin r → R) (g : Fin s → R) :
    K^•(Fin.append f g) ≅
      koszulComplex ((koszulLinearForm f).coprod (koszulLinearForm g)) where
  hom := KoszulComplex.map (finAppendLinearEquiv r s).symm.toLinearMap
    (koszulLinearForm_append_comp_symm f g)
  inv := KoszulComplex.map (finAppendLinearEquiv r s).toLinearMap
    (koszulLinearForm_append_comp f g)
  hom_inv_id := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    -- The degreewise maps are exterior-power functor images of inverse linear equivalences.
    apply exteriorPower.linearMap_ext
    ext m
    change
      ModuleCat.exteriorPower.map
          (ModuleCat.ofHom (finAppendLinearEquiv r s).toLinearMap) n
          (ModuleCat.exteriorPower.map
            (ModuleCat.ofHom (finAppendLinearEquiv r s).symm.toLinearMap) n
            (ModuleCat.exteriorPower.mk m)) =
        ModuleCat.exteriorPower.mk m
    rw [ModuleCat.exteriorPower.map_mk, ModuleCat.exteriorPower.map_mk]
    congr 1
    ext i x
    simpa [finAppendLinearEquiv] using
      congrArg (fun h : Fin (r + s) → R => h x) ((finAppendLinearEquiv r s).right_inv (m i))
  inv_hom_id := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    -- The reverse composite is identical after the same generator-level simplification.
    apply exteriorPower.linearMap_ext
    ext m
    change
      ModuleCat.exteriorPower.map
          (ModuleCat.ofHom (finAppendLinearEquiv r s).symm.toLinearMap) n
          (ModuleCat.exteriorPower.map
            (ModuleCat.ofHom (finAppendLinearEquiv r s).toLinearMap) n
            (ModuleCat.exteriorPower.mk m)) =
        ModuleCat.exteriorPower.mk m
    rw [ModuleCat.exteriorPower.map_mk, ModuleCat.exteriorPower.map_mk]
    congr 1
    ext i
    · simpa [finAppendLinearEquiv] using
        congrArg (fun h : (Fin r → R) × (Fin s → R) => h.1 x)
          ((finAppendLinearEquiv r s).left_inv (m i))
    · simpa [finAppendLinearEquiv] using
        congrArg (fun h : (Fin r → R) × (Fin s → R) => h.2 x)
          ((finAppendLinearEquiv r s).left_inv (m i))

/-- Lemma 15.28.12: for finite families `f : Fin r → R` and `g : Fin s → R`, the Koszul complex
on the concatenated family `Fin.append f g` is isomorphic to the tensor product of the Koszul
complexes on `f` and `g`, written in Lean as `K^•(f) ⊗ K^•(g)`. -/
@[stacks 0664]
noncomputable def koszulComplexOn_append_iso_tensorObj {r s : ℕ}
    (f : Fin r → R) (g : Fin s → R) :
    K^•(Fin.append f g) ≅ K^•(f) ⊗ K^•(g) :=
  by
    simpa using
      koszulComplexOn_append_iso_coprod f g ≪≫
        koszulComplex_coprod_iso_tensorObj (koszulLinearForm f) (koszulLinearForm g)

end
