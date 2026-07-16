import Mathlib
import stacks_proof.stacks_project.LinearAlgebra.PowerOperations

universe u v w z

open PrimeSpectrum
open TensorProduct.AlgebraTensorModule

section

variable {R : Type u} [CommRing R]

/-- Helper for Chap10 Lemma 10 108 6: alternating maps out of a module are determined by
their values on tuples whose entries lie in a spanning set. -/
theorem alternatingMap_ext_of_span_fin
    {A : Type w} [CommRing A]
    {V : Type v} [AddCommGroup V] [Module A V]
    {N : Type z} [AddCommGroup N] [Module A N]
    (s : Set V) (hs : Submodule.span A s = ⊤) :
    ∀ (n : ℕ) {f g : V [⋀^Fin n]→ₗ[A] N},
      (∀ v : Fin n → V, (∀ j, v j ∈ s) → f v = g v) → f = g
  | 0, f, g, h => by
      -- In degree zero there are no coordinates, so the spanning condition is vacuous.
      apply AlternatingMap.ext
      intro v
      exact h v (by intro j; exact Fin.elim0 j)
  | n + 1, f, g, h => by
      have hcurry : f.curryLeft = g.curryLeft := by
        -- Curry in the first coordinate and use linear-map extensionality on the spanning set.
        apply LinearMap.ext_on hs
        intro x hx
        apply alternatingMap_ext_of_span_fin s hs n
        intro v hv
        rw [AlternatingMap.curryLeft_apply_apply, AlternatingMap.curryLeft_apply_apply]
        exact h (Matrix.vecCons x v) (by
          intro j
          refine Fin.cases ?_ ?_ j
          · simpa [Matrix.vecCons] using hx
          · intro j
            simpa [Matrix.vecCons] using hv j)
      -- Reassemble each tuple from its head and tail, then compare the curried maps.
      apply AlternatingMap.ext
      intro v
      calc
        f v = f (Matrix.vecCons (v 0) (Fin.tail v)) := by
          simpa [Matrix.vecCons] using congrArg f (Fin.cons_self_tail v).symm
        _ = f.curryLeft (v 0) (Fin.tail v) := by
          rw [AlternatingMap.curryLeft_apply_apply]
        _ = g.curryLeft (v 0) (Fin.tail v) := by
          rw [hcurry]
        _ = g (Matrix.vecCons (v 0) (Fin.tail v)) := by
          rw [AlternatingMap.curryLeft_apply_apply]
        _ = g v := by
          simpa [Matrix.vecCons] using congrArg g (Fin.cons_self_tail v)

/-- Helper for Chap10 Lemma 10 108 6: alternating maps on a tensor product are determined by
their values on pure tensor tuples. -/
theorem alternatingMap_tensorProduct_ext_pure
    {A : Type w} [CommRing A] [Algebra R A]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type z} [AddCommGroup N] [Module A N]
    {n : ℕ} {f g : (TensorProduct R A M) [⋀^Fin n]→ₗ[A] N}
    (h : ∀ (a : Fin n → A) (m : Fin n → M),
      f (fun j => a j ⊗ₜ[R] m j) = g (fun j => a j ⊗ₜ[R] m j)) :
    f = g := by
  let s : Set (TensorProduct R A M) := {t | ∃ (a : A) (m : M), a ⊗ₜ[R] m = t}
  -- Pure tensors span `A ⊗[R] M` as an `A`-module, so the previous helper applies.
  apply alternatingMap_ext_of_span_fin s ?_ n
  · intro v hv
    choose a m hm using hv
    have hv_eq : (fun j : Fin n => a j ⊗ₜ[R] m j) = v := funext hm
    simpa [hv_eq] using h a m
  · have hR : Submodule.span R s = ⊤ := by
      simpa [s] using TensorProduct.span_tmul_eq_top R A M
    exact Submodule.span_eq_top_of_span_eq_top R A s hR

/-- Helper for Chap10 Lemma 10 108 6: the scalar-tower identity for multilinear-map spaces is
checked pointwise in the codomain. -/
theorem multilinearMap_smul_assoc_of_codomain
    {A : Type w} [CommRing A] [Algebra R A]
    {S : Type*} [Semiring S]
    {ι : Type*} {M : ι → Type v} [∀ i, AddCommMonoid (M i)] [∀ i, Module S (M i)]
    {N : Type z} [AddCommMonoid N] [Module S N] [Module A N] [Module R N]
    [IsScalarTower R A N] [SMulCommClass S A N] [SMulCommClass S R N]
    (r : R) (a : A) (f : MultilinearMap S M N) :
    (r • a) • f = r • a • f := by
  -- Pointwise evaluation reduces the scalar-tower law to the one already available on `N`.
  ext m
  simp [smul_assoc]

/-- Helper for Chap10 Lemma 10 108 6: scalar actions on the codomain induce the expected scalar
tower on spaces of multilinear maps. -/
local instance baseChangeMultilinearMapIsScalarTower
    {A : Type w} [CommRing A] [Algebra R A]
    {S : Type*} [Semiring S]
    {ι : Type*} {M : ι → Type v} [∀ i, AddCommMonoid (M i)] [∀ i, Module S (M i)]
    {N : Type z} [AddCommMonoid N] [Module S N] [Module A N] [Module R N]
    [IsScalarTower R A N] [SMulCommClass S A N] [SMulCommClass S R N] :
    IsScalarTower R A (MultilinearMap S M N) where
  smul_assoc := multilinearMap_smul_assoc_of_codomain

/-- Helper for Chap10 Lemma 10 108 6: the successor step in scalar extension of
multilinear maps, written as a function before packaging its linearity. -/
noncomputable def baseChangeMultilinearMapSuccFun
    {A : Type w} [CommRing A] [Algebra R A]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type z} [AddCommGroup N] [Module A N] [Module R N]
    [IsScalarTower R A N] [SMulCommClass R A N]
    (n : ℕ)
    (L : MultilinearMap R (fun _ : Fin n => M) N →ₗ[A]
        MultilinearMap A (fun _ : Fin n => TensorProduct R A M) N)
    (f : MultilinearMap R (fun _ : Fin (n + 1) => M) N) :
    MultilinearMap A (fun _ : Fin (n + 1) => TensorProduct R A M) N :=
  LinearMap.uncurryLeft (R := A)
    (M := fun _ : Fin (n + 1) => TensorProduct R A M) (M₂ := N)
    ((((L.restrictScalars R).comp (MultilinearMap.curryLeft f)).liftBaseChange A))

/-- Helper for Chap10 Lemma 10 108 6: the successor scalar-extension function is additive in
the multilinear map being extended. -/
theorem baseChangeMultilinearMapSuccFun_add
    {A : Type w} [CommRing A] [Algebra R A]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type z} [AddCommGroup N] [Module A N] [Module R N]
    [IsScalarTower R A N] [SMulCommClass R A N]
    (n : ℕ)
    (L : MultilinearMap R (fun _ : Fin n => M) N →ₗ[A]
        MultilinearMap A (fun _ : Fin n => TensorProduct R A M) N)
    (f g : MultilinearMap R (fun _ : Fin (n + 1) => M) N) :
    baseChangeMultilinearMapSuccFun (R := R) n L (f + g) =
      baseChangeMultilinearMapSuccFun (R := R) n L f +
        baseChangeMultilinearMapSuccFun (R := R) n L g := by
  -- Curry is additive, and `liftBaseChangeEquiv` carries that additive identity to tensor
  -- arguments before uncurry evaluates it.
  ext v
  simp only [baseChangeMultilinearMapSuccFun, LinearMap.uncurryLeft_apply]
  have hcur : (f + g).curryLeft = f.curryLeft + g.curryLeft := rfl
  rw [hcur, LinearMap.comp_add]
  have hlift := map_add (LinearMap.liftBaseChangeEquiv A)
    ((L.restrictScalars R).comp f.curryLeft) ((L.restrictScalars R).comp g.curryLeft)
  simpa [LinearMap.liftBaseChange, LinearMap.uncurryLeft_apply] using
    congrFun (congrFun hlift (v 0)) (Fin.tail v)

/-- Helper for Chap10 Lemma 10 108 6: the successor scalar-extension function is compatible
with scalar multiplication on the codomain. -/
theorem baseChangeMultilinearMapSuccFun_smul
    {A : Type w} [CommRing A] [Algebra R A]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type z} [AddCommGroup N] [Module A N] [Module R N]
    [IsScalarTower R A N] [SMulCommClass R A N]
    (n : ℕ)
    (L : MultilinearMap R (fun _ : Fin n => M) N →ₗ[A]
        MultilinearMap A (fun _ : Fin n => TensorProduct R A M) N)
    (a : A) (f : MultilinearMap R (fun _ : Fin (n + 1) => M) N) :
    baseChangeMultilinearMapSuccFun (R := R) n L (a • f) =
      a • baseChangeMultilinearMapSuccFun (R := R) n L f := by
  -- Push the scalar through curry and through the `A`-linear map `L`, then use linearity of
  -- `liftBaseChangeEquiv`.
  ext v
  simp only [baseChangeMultilinearMapSuccFun, LinearMap.uncurryLeft_apply]
  have hcur : (a • f).curryLeft = a • f.curryLeft := rfl
  rw [hcur]
  have hcomp :
      (L.restrictScalars R).comp (a • f.curryLeft) =
        a • ((L.restrictScalars R).comp f.curryLeft) := by
    ext x y
    exact congrFun (congrArg DFunLike.coe (L.map_smul a (f.curryLeft x))) y
  rw [hcomp]
  have hlift := map_smul (LinearMap.liftBaseChangeEquiv A) a
    ((L.restrictScalars R).comp f.curryLeft)
  simpa [LinearMap.liftBaseChange, LinearMap.uncurryLeft_apply] using
    congrFun (congrFun hlift (v 0)) (Fin.tail v)

/-- Helper for Chap10 Lemma 10 108 6: the successor step as an `A`-linear map on spaces of
multilinear maps. -/
noncomputable def baseChangeMultilinearMapSuccLinear
    {A : Type w} [CommRing A] [Algebra R A]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type z} [AddCommGroup N] [Module A N] [Module R N]
    [IsScalarTower R A N] [SMulCommClass R A N]
    (n : ℕ)
    (L : MultilinearMap R (fun _ : Fin n => M) N →ₗ[A]
        MultilinearMap A (fun _ : Fin n => TensorProduct R A M) N) :
    MultilinearMap R (fun _ : Fin (n + 1) => M) N →ₗ[A]
        MultilinearMap A (fun _ : Fin (n + 1) => TensorProduct R A M) N where
  toFun := baseChangeMultilinearMapSuccFun (R := R) n L
  map_add' := baseChangeMultilinearMapSuccFun_add (R := R) n L
  map_smul' := baseChangeMultilinearMapSuccFun_smul (R := R) n L

/-- Helper for Chap10 Lemma 10 108 6: scalar extension of finite multilinear maps from `M`
to maps on `A ⊗[R] M`. -/
noncomputable def baseChangeMultilinearMapLinear
    {A : Type w} [CommRing A] [Algebra R A]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type z} [AddCommGroup N] [Module A N] [Module R N]
    [IsScalarTower R A N] [SMulCommClass R A N] :
    ∀ n : ℕ,
      MultilinearMap R (fun _ : Fin n => M) N →ₗ[A]
        MultilinearMap A (fun _ : Fin n => TensorProduct R A M) N
  | 0 =>
      (MultilinearMap.constLinearEquivOfIsEmpty
        (R := A) (S := A) (M₁ := fun _ : Fin 0 => TensorProduct R A M) (M₂ := N)).toLinearMap.comp
        (MultilinearMap.constLinearEquivOfIsEmpty
          (R := R) (S := A) (M₁ := fun _ : Fin 0 => M) (M₂ := N)).symm.toLinearMap
  | n + 1 =>
      baseChangeMultilinearMapSuccLinear (R := R) (A := A) (M := M) (N := N) n
        (baseChangeMultilinearMapLinear n)

/-- Helper for Chap10 Lemma 10 108 6: on pure tensor tuples, scalar extension of a multilinear
map multiplies by the product of the scalars. -/
theorem baseChangeMultilinearMapLinear_apply_pure
    {A : Type w} [CommRing A] [Algebra R A]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type z} [AddCommGroup N] [Module A N] [Module R N]
    [IsScalarTower R A N] [SMulCommClass R A N] :
    ∀ (n : ℕ) (f : MultilinearMap R (fun _ : Fin n => M) N)
      (a : Fin n → A) (m : Fin n → M),
      baseChangeMultilinearMapLinear (R := R) (A := A) (M := M) (N := N) n f
          (fun j => a j ⊗ₜ[R] m j) =
        (∏ j, a j) • f m
  | 0, f, a, m => by
      -- In degree zero both sides are the same constant value.
      simpa [baseChangeMultilinearMapLinear] using congrArg f (Subsingleton.elim (0 : Fin 0 → M) m)
  | n + 1, f, a, m => by
      -- Peel off the first coordinate, use the induction hypothesis on the tail, and normalize
      -- the product over `Fin (n + 1)`.
      simp [baseChangeMultilinearMapLinear, baseChangeMultilinearMapSuccLinear,
        baseChangeMultilinearMapSuccFun, LinearMap.uncurryLeft_apply]
      have htail :=
        baseChangeMultilinearMapLinear_apply_pure n (f.curryLeft (m 0))
          (Fin.tail a) (Fin.tail m)
      simpa [Fin.tail, Fin.prod_univ_succ, Matrix.vecCons, smul_smul] using
        congrArg (fun x ↦ a 0 • x) htail

/-- Helper for Chap10 Lemma 10 108 6: a bilinear map has zero diagonal everywhere once this
is true on a spanning set and the generator cross terms cancel. -/
theorem bilinearMap_diag_eq_zero_of_span_cross
    {A : Type w} [CommRing A]
    {V : Type v} [AddCommGroup V] [Module A V]
    {N : Type z} [AddCommGroup N] [Module A N]
    (B : V →ₗ[A] V →ₗ[A] N) (s : Set V) (hs : Submodule.span A s = ⊤)
    (hdiag : ∀ x ∈ s, B x x = 0)
    (hcross : ∀ x ∈ s, ∀ y ∈ s, B x y + B y x = 0) :
    ∀ x, B x x = 0 := by
  have hcrossSpan :
      ∀ x ∈ Submodule.span A s, ∀ y ∈ Submodule.span A s, B x y + B y x = 0 := by
    intro x hx y hy
    -- First extend the generator cross-cancellation relation bilinearly in both variables.
    refine Submodule.span_induction₂ (R := A) (s := s) (t := s)
      (p := fun x y _ _ => B x y + B y x = 0) ?mem ?zero_left ?zero_right ?add_left
      ?add_right ?smul_left ?smul_right hx hy
    · intro x y hx hy
      exact hcross x hx y hy
    · intro y hy
      simp
    · intro x hx
      simp
    · intro x y z hx hy hz hxz hyz
      simp only [map_add, LinearMap.add_apply]
      calc
        _ = ((B x) z + (B z) x) + ((B y) z + (B z) y) := by abel
        _ = 0 := by rw [hxz, hyz, zero_add]
    · intro x y z hx hy hz hxy hxz
      simp only [map_add, LinearMap.add_apply]
      calc
        _ = ((B x) y + (B y) x) + ((B x) z + (B z) x) := by abel
        _ = 0 := by rw [hxy, hxz, zero_add]
    · intro a x y hx hy hxy
      simp only [map_smul, LinearMap.smul_apply]
      rw [← smul_add, hxy, smul_zero]
    · intro a x y hx hy hxy
      simp only [map_smul, LinearMap.smul_apply]
      rw [← smul_add, hxy, smul_zero]
  intro x
  have hxmem : x ∈ Submodule.span A s := by rw [hs]; exact Submodule.mem_top
  -- The diagonal of a sum expands into two diagonal terms and one cross-cancellation term.
  exact Submodule.span_induction (R := A) (s := s)
    (p := fun y _ => B y y = 0)
    (fun y hy => hdiag y hy)
    (by simp)
    (fun y z hy hz hydiag hzdiag => by
      simp only [map_add, LinearMap.add_apply]
      calc
        _ = (B y) y + (B z) z + ((B y) z + (B z) y) := by abel
        _ = 0 := by rw [hydiag, hzdiag, hcrossSpan y hy z hz]; simp)
    (fun a y hy hydiag => by
      simp only [map_smul, LinearMap.smul_apply]
      rw [hydiag, smul_zero, smul_zero])
    hxmem

/-- Helper for Chap10 Lemma 10 108 6: a multilinear map that vanishes on all tuples from a
spanning set vanishes on all tuples. -/
theorem multilinearMap_eq_zero_of_span_fin
    {A : Type w} [CommRing A]
    {V : Type v} [AddCommGroup V] [Module A V]
    {N : Type z} [AddCommGroup N] [Module A N]
    (s : Set V) (hs : Submodule.span A s = ⊤) :
    ∀ (n : ℕ) (F : MultilinearMap A (fun _ : Fin n => V) N),
      (∀ v : Fin n → V, (∀ j, v j ∈ s) → F v = 0) → ∀ v, F v = 0
  | 0, F, h, v => by
      -- There are no coordinates in degree zero, so the spanning condition is vacuous.
      exact h v (by intro j; exact Fin.elim0 j)
  | n + 1, F, h, v => by
      have hcurry : F.curryLeft = 0 := by
        -- Curry in the first coordinate and use linear-map extensionality on the spanning set.
        apply LinearMap.ext_on hs
        intro x hx
        apply MultilinearMap.ext
        intro tail
        apply multilinearMap_eq_zero_of_span_fin s hs n
        intro w hw
        rw [MultilinearMap.curryLeft_apply]
        exact h (Matrix.vecCons x w) (by
          intro j
          refine Fin.cases ?_ ?_ j
          · simpa [Matrix.vecCons] using hx
          · intro j
            simpa [Matrix.vecCons] using hw j)
      -- Reassemble the tuple from its head and tail and evaluate the zero curried map.
      calc
        F v = F (Matrix.vecCons (v 0) (Fin.tail v)) := by
          simpa [Matrix.vecCons] using congrArg F (Fin.cons_self_tail v).symm
        _ = F.curryLeft (v 0) (Fin.tail v) := by
          simpa [Matrix.vecCons] using
            (MultilinearMap.curryLeft_apply F (v 0) (Fin.tail v)).symm
        _ = 0 := by rw [hcurry]; rfl

/-- Helper for Chap10 Lemma 10 108 6: generator diagonal and cross-cancellation conditions in
the first and one tail coordinate force first-tail diagonal vanishing for arbitrary tail values. -/
theorem multilinearMap_vecCons_update_eq_zero_of_span_pair
    {A : Type w} [CommRing A]
    {V : Type v} [AddCommGroup V] [Module A V]
    {N : Type z} [AddCommGroup N] [Module A N]
    (s : Set V) (hs : Submodule.span A s = ⊤)
    {n : ℕ} (F : MultilinearMap A (fun _ : Fin (n + 2) => V) N) (k : Fin (n + 1))
    (hdiag : ∀ x ∈ s, ∀ tail : Fin (n + 1) → V,
      (∀ r, tail r ∈ s) → F (Matrix.vecCons x (Function.update tail k x)) = 0)
    (hcross : ∀ x ∈ s, ∀ y ∈ s, ∀ tail : Fin (n + 1) → V,
      (∀ r, tail r ∈ s) →
        F (Matrix.vecCons x (Function.update tail k y)) +
          F (Matrix.vecCons y (Function.update tail k x)) = 0) :
    ∀ tail : Fin (n + 1) → V, F (Matrix.vecCons (tail k) tail) = 0 := by
  intro tail
  let B : V →ₗ[A] V →ₗ[A] N :=
    { toFun := fun x => (F.curryLeft x).toLinearMap tail k
      map_add' := by
        intro x y
        ext z
        simp [MultilinearMap.curryLeft_apply, MultilinearMap.toLinearMap]
      map_smul' := by
        intro a x
        ext z
        simp [MultilinearMap.curryLeft_apply, MultilinearMap.toLinearMap] }
  have hdiagSpan : ∀ x ∈ s, B x x = 0 := by
    intro x hx
    have hzero : ((F.curryLeft x).curryMid k x) (k.removeNth tail) = 0 := by
      -- With the two repeated entries fixed to a generator, only the remaining coordinates need
      -- the spanning-set induction.
      apply multilinearMap_eq_zero_of_span_fin s hs n
      intro w hw
      rw [MultilinearMap.curryMid_apply_apply]
      rw [MultilinearMap.curryLeft_apply]
      simpa [Matrix.vecCons, Function.update_eq_self_iff] using
        hdiag x hx (k.insertNth x w) (by
          intro r
          by_cases hr : r = k
          · subst hr
            simpa using hx
          · rcases Fin.exists_succAbove_eq hr with ⟨r', hr'⟩
            rw [← hr']
            simpa using hw r')
    simpa [B, MultilinearMap.toLinearMap, MultilinearMap.curryMid_apply_apply,
      MultilinearMap.curryLeft_apply, Fin.insertNth_removeNth, Matrix.vecCons] using hzero
  have hcrossSpan : ∀ x ∈ s, ∀ y ∈ s, B x y + B y x = 0 := by
    intro x hx y hy
    have hzero :
        (((F.curryLeft x).curryMid k y) + ((F.curryLeft y).curryMid k x))
          (k.removeNth tail) = 0 := by
      -- The same remaining-coordinate induction extends the pure cross-cancellation relation.
      apply multilinearMap_eq_zero_of_span_fin s hs n
      intro w hw
      simp only [MultilinearMap.add_apply]
      rw [MultilinearMap.curryMid_apply_apply, MultilinearMap.curryMid_apply_apply]
      rw [MultilinearMap.curryLeft_apply, MultilinearMap.curryLeft_apply]
      simpa [Matrix.vecCons, Function.update_eq_self_iff] using
        hcross x hx y hy (k.insertNth y w) (by
          intro r
          by_cases hr : r = k
          · subst hr
            simpa using hy
          · rcases Fin.exists_succAbove_eq hr with ⟨r', hr'⟩
            rw [← hr']
            simpa using hw r')
    simpa [B, MultilinearMap.toLinearMap, MultilinearMap.curryMid_apply_apply,
      MultilinearMap.curryLeft_apply, Fin.insertNth_removeNth, Matrix.vecCons] using hzero
  have hdiagAll := bilinearMap_diag_eq_zero_of_span_cross B s hs hdiagSpan hcrossSpan (tail k)
  have hupdate :
      Function.update (Matrix.vecCons (tail k) tail) k.succ (tail k) =
        Matrix.vecCons (tail k) tail := by
    funext r
    by_cases hr : r = k.succ
    · subst hr
      simp [Function.update, Matrix.vecCons]
    · rw [Function.update_of_ne hr]
  have hdiagAll' :
      F (Function.update (Matrix.vecCons (tail k) tail) k.succ (tail k)) = 0 := by
    simpa [B, MultilinearMap.toLinearMap, MultilinearMap.curryLeft_apply, Matrix.vecCons]
      using hdiagAll
  rwa [hupdate] at hdiagAll'

/-- Helper for Chap10 Lemma 10 108 6: evaluating the scalar-extended map on a pure first
coordinate peels off the corresponding scalar and curried multilinear map. -/
theorem baseChangeMultilinearMapLinear_apply_cons_tmul
    {A : Type w} [CommRing A] [Algebra R A]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type z} [AddCommGroup N] [Module A N] [Module R N]
    [IsScalarTower R A N] [SMulCommClass R A N]
    (n : ℕ) (f : MultilinearMap R (fun _ : Fin (n + 1) => M) N)
    (a : A) (m : M) (tail : Fin n → TensorProduct R A M) :
    baseChangeMultilinearMapLinear (R := R) (A := A) (M := M) (N := N) (n + 1) f
        (Matrix.vecCons (a ⊗ₜ[R] m) tail) =
      a • baseChangeMultilinearMapLinear (R := R) (A := A) (M := M) (N := N) n
        (f.curryLeft m) tail := by
  -- Unfold one successor step and use the base-change computation on a pure tensor.
  simp [baseChangeMultilinearMapLinear, baseChangeMultilinearMapSuccLinear,
    baseChangeMultilinearMapSuccFun, LinearMap.uncurryLeft_apply, Matrix.vecCons,
    LinearMap.liftBaseChange_tmul]

/-- Helper for Chap10 Lemma 10 108 6: on pure tensor tuples, scalar extension of an alternating
map vanishes when the underlying `M`-tuple has two equal entries. -/
theorem baseChangeMultilinearMapLinear_apply_pure_eq_zero_of_eq
    {A : Type w} [CommRing A] [Algebra R A]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type z} [AddCommGroup N] [Module A N] [Module R N]
    [IsScalarTower R A N] [SMulCommClass R A N]
    (n : ℕ) (f : M [⋀^Fin n]→ₗ[R] N)
    (a : Fin n → A) (m : Fin n → M) {i j : Fin n}
    (hm : m i = m j) (hij : i ≠ j) :
    baseChangeMultilinearMapLinear (R := R) (A := A) (M := M) (N := N) n
        f.toMultilinearMap (fun k => a k ⊗ₜ[R] m k) = 0 := by
  -- The pure-tensor formula reduces this to the defining alternating-map vanishing relation.
  rw [baseChangeMultilinearMapLinear_apply_pure]
  simpa using congrArg (fun y ↦ (∏ k, a k) • y) (f.map_eq_zero_of_eq m hm hij)

/-- Helper for Chap10 Lemma 10 108 6: on pure tensor tuples, scalar extension of an alternating
map satisfies the additive swap relation. -/
theorem baseChangeMultilinearMapLinear_apply_pure_swap_add
    {A : Type w} [CommRing A] [Algebra R A]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type z} [AddCommGroup N] [Module A N] [Module R N]
    [IsScalarTower R A N] [SMulCommClass R A N]
    (n : ℕ) (f : M [⋀^Fin n]→ₗ[R] N)
    (a : Fin n → A) (m : Fin n → M) {i j : Fin n} (hij : i ≠ j) :
    baseChangeMultilinearMapLinear (R := R) (A := A) (M := M) (N := N) n
        f.toMultilinearMap (fun k => a k ⊗ₜ[R] m k) +
      baseChangeMultilinearMapLinear (R := R) (A := A) (M := M) (N := N) n
        f.toMultilinearMap (fun k => (a ∘ Equiv.swap i j) k ⊗ₜ[R]
          (m ∘ Equiv.swap i j) k) = 0 := by
  -- The product of scalars is invariant under the swap, leaving exactly `f.map_add_swap`.
  rw [baseChangeMultilinearMapLinear_apply_pure,
    baseChangeMultilinearMapLinear_apply_pure]
  have hprod : (∏ k, (a ∘ Equiv.swap i j) k) = ∏ k, a k := by
    simpa [Function.comp_def] using (Equiv.prod_comp (Equiv.swap i j) a)
  rw [hprod, ← smul_add]
  simpa using congrArg (fun y ↦ (∏ k, a k) • y) (f.map_add_swap (v := m) hij)

/-- Helper for Chap10 Lemma 10 108 6: scalar extension of an alternating multilinear map
vanishes on equal tensor-product coordinates. -/
theorem baseChangeMultilinearMapLinear_map_eq_zero_of_alternating
    {A : Type w} [CommRing A] [Algebra R A]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type z} [AddCommGroup N] [Module A N] [Module R N]
    [IsScalarTower R A N] [SMulCommClass R A N]
    (n : ℕ) (f : M [⋀^Fin n]→ₗ[R] N) :
    ∀ (v : Fin n → TensorProduct R A M) (i j : Fin n), v i = v j → i ≠ j →
      baseChangeMultilinearMapLinear (R := R) (A := A) (M := M) (N := N) n
        f.toMultilinearMap v = 0 := by
  classical
  induction n with
  | zero =>
      -- In degree zero there are no distinct repeated coordinates.
      intro v i
      exact Fin.elim0 i
  | succ n ih =>
      intro v i j hv hij
      let s : Set (TensorProduct R A M) := {t | ∃ (a : A) (m : M), a ⊗ₜ[R] m = t}
      have hs : Submodule.span A s = ⊤ := by
        -- Pure tensors span the scalar extension as an `A`-module.
        have hR : Submodule.span R s = ⊤ := by
          simpa [s] using TensorProduct.span_tmul_eq_top R A M
        exact Submodule.span_eq_top_of_span_eq_top R A s hR
      let F : MultilinearMap A (fun _ : Fin (n + 1) => TensorProduct R A M) N :=
        baseChangeMultilinearMapLinear (R := R) (A := A) (M := M) (N := N) (n + 1)
          f.toMultilinearMap
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero => exact (hij rfl).elim
          | succ j =>
              -- The first-tail diagonal is reduced to pure diagonal and pure swap relations,
              -- then the abstract bilinear span helper extends it to arbitrary tensors.
              cases n with
              | zero => exact Fin.elim0 j
              | succ n =>
                  have hfirst :
                      F (Matrix.vecCons (Fin.tail v j) (Fin.tail v)) = 0 := by
                    apply multilinearMap_vecCons_update_eq_zero_of_span_pair s hs F j
                    · intro x hx tail htail
                      rcases hx with ⟨a₀, m₀, rfl⟩
                      choose aTail mTail hTail using htail
                      let a : Fin (n + 2) → A :=
                        Matrix.vecCons a₀ (Function.update aTail j a₀)
                      let m : Fin (n + 2) → M :=
                        Matrix.vecCons m₀ (Function.update mTail j m₀)
                      have hpure :
                          F (fun k => a k ⊗ₜ[R] m k) = 0 :=
                        baseChangeMultilinearMapLinear_apply_pure_eq_zero_of_eq
                          (R := R) (A := A) (M := M) (N := N) (n + 2) f
                          a m (i := 0) (j := j.succ) (by simp [m])
                          (Fin.succ_ne_zero j).symm
                      have htuple :
                          (fun k => a k ⊗ₜ[R] m k) =
                            Matrix.vecCons (a₀ ⊗ₜ[R] m₀)
                              (Function.update tail j (a₀ ⊗ₜ[R] m₀)) := by
                        funext k
                        cases k using Fin.cases with
                        | zero =>
                            simp [a, m, Matrix.vecCons,
                              Function.update_of_ne (Fin.succ_ne_zero j).symm]
                        | succ k =>
                            by_cases hk : k = j
                            · subst hk
                              simp [a, m, Matrix.vecCons]
                            · have hk_succ : k.succ ≠ j.succ := by
                                intro h
                                exact hk (Fin.succ_injective _ h)
                              simp [a, m, Matrix.vecCons, Function.update_of_ne hk_succ,
                                Function.update_of_ne hk, hTail k]
                      rw [htuple] at hpure
                      simpa [F] using hpure
                    · intro x hx y hy tail htail
                      rcases hx with ⟨a₀, m₀, rfl⟩
                      rcases hy with ⟨a₁, m₁, rfl⟩
                      choose aTail mTail hTail using htail
                      let a : Fin (n + 2) → A :=
                        Matrix.vecCons a₀ (Function.update aTail j a₁)
                      let m : Fin (n + 2) → M :=
                        Matrix.vecCons m₀ (Function.update mTail j m₁)
                      have hpure :
                          F (fun k => a k ⊗ₜ[R] m k) +
                            F (fun k => (a ∘ Equiv.swap 0 j.succ) k ⊗ₜ[R]
                              (m ∘ Equiv.swap 0 j.succ) k) = 0 :=
                        baseChangeMultilinearMapLinear_apply_pure_swap_add
                          (R := R) (A := A) (M := M) (N := N) (n + 2) f
                          a m (i := 0) (j := j.succ) (Fin.succ_ne_zero j).symm
                      have htuple₁ :
                          (fun k => a k ⊗ₜ[R] m k) =
                            Matrix.vecCons (a₀ ⊗ₜ[R] m₀)
                              (Function.update tail j (a₁ ⊗ₜ[R] m₁)) := by
                        funext k
                        cases k using Fin.cases with
                        | zero =>
                            simp [a, m, Matrix.vecCons,
                              Function.update_of_ne (Fin.succ_ne_zero j).symm]
                        | succ k =>
                            by_cases hk : k = j
                            · subst hk
                              simp [a, m, Matrix.vecCons]
                            · have hk_succ : k.succ ≠ j.succ := by
                                intro h
                                exact hk (Fin.succ_injective _ h)
                              simp [a, m, Matrix.vecCons, Function.update_of_ne hk_succ,
                                Function.update_of_ne hk, hTail k]
                      have htuple₂ :
                          (fun k => (a ∘ Equiv.swap 0 j.succ) k ⊗ₜ[R]
                              (m ∘ Equiv.swap 0 j.succ) k) =
                            Matrix.vecCons (a₁ ⊗ₜ[R] m₁)
                              (Function.update tail j (a₀ ⊗ₜ[R] m₀)) := by
                        funext k
                        simp only [Function.comp_apply]
                        cases k using Fin.cases with
                        | zero =>
                            have hsw : (Equiv.swap (0 : Fin (n + 2)) j.succ) 0 = j.succ :=
                              Equiv.swap_apply_left _ _
                            rw [hsw]
                            simp [a, m, Matrix.vecCons]
                        | succ k =>
                            by_cases hk : k = j
                            · subst hk
                              have hsw :
                                  (Equiv.swap (0 : Fin (n + 2)) k.succ) k.succ = 0 :=
                                Equiv.swap_apply_right _ _
                              rw [hsw]
                              simp [a, m, Matrix.vecCons,
                                Function.update_of_ne (Fin.succ_ne_zero k).symm]
                            · have hk_succ : k.succ ≠ j.succ := by
                                intro h
                                exact hk (Fin.succ_injective _ h)
                              have hsw :
                                  (Equiv.swap (0 : Fin (n + 2)) j.succ) k.succ = k.succ :=
                                Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero k) hk_succ
                              rw [hsw]
                              simp [a, m, Matrix.vecCons, Function.update_of_ne hk_succ,
                                Function.update_of_ne hk, hTail k]
                      rw [htuple₁, htuple₂] at hpure
                      simpa [F] using hpure
                  calc
                    F v = F (Matrix.vecCons (v 0) (Fin.tail v)) := by
                      simpa [F, Matrix.vecCons] using congrArg F (Fin.cons_self_tail v).symm
                    _ = F (Matrix.vecCons (Fin.tail v j) (Fin.tail v)) := by
                      rw [hv]
                      rfl
                    _ = 0 := hfirst
      | succ i =>
          cases j using Fin.cases with
          | zero =>
              -- Swap the equality direction and reuse the first-tail case by symmetry.
              cases n with
              | zero => exact Fin.elim0 i
              | succ n =>
                  have hfirst :
                      F (Matrix.vecCons (Fin.tail v i) (Fin.tail v)) = 0 := by
                    apply multilinearMap_vecCons_update_eq_zero_of_span_pair s hs F i
                    · intro x hx tail htail
                      rcases hx with ⟨a₀, m₀, rfl⟩
                      choose aTail mTail hTail using htail
                      let a : Fin (n + 2) → A :=
                        Matrix.vecCons a₀ (Function.update aTail i a₀)
                      let m : Fin (n + 2) → M :=
                        Matrix.vecCons m₀ (Function.update mTail i m₀)
                      have hpure :
                          F (fun k => a k ⊗ₜ[R] m k) = 0 :=
                        baseChangeMultilinearMapLinear_apply_pure_eq_zero_of_eq
                          (R := R) (A := A) (M := M) (N := N) (n + 2) f
                          a m (i := 0) (j := i.succ) (by simp [m])
                          (Fin.succ_ne_zero i).symm
                      have htuple :
                          (fun k => a k ⊗ₜ[R] m k) =
                            Matrix.vecCons (a₀ ⊗ₜ[R] m₀)
                              (Function.update tail i (a₀ ⊗ₜ[R] m₀)) := by
                        funext k
                        cases k using Fin.cases with
                        | zero =>
                            simp [a, m, Matrix.vecCons,
                              Function.update_of_ne (Fin.succ_ne_zero i).symm]
                        | succ k =>
                            by_cases hk : k = i
                            · subst hk
                              simp [a, m, Matrix.vecCons]
                            · have hk_succ : k.succ ≠ i.succ := by
                                intro h
                                exact hk (Fin.succ_injective _ h)
                              simp [a, m, Matrix.vecCons, Function.update_of_ne hk_succ,
                                Function.update_of_ne hk, hTail k]
                      rw [htuple] at hpure
                      simpa [F] using hpure
                    · intro x hx y hy tail htail
                      rcases hx with ⟨a₀, m₀, rfl⟩
                      rcases hy with ⟨a₁, m₁, rfl⟩
                      choose aTail mTail hTail using htail
                      let a : Fin (n + 2) → A :=
                        Matrix.vecCons a₀ (Function.update aTail i a₁)
                      let m : Fin (n + 2) → M :=
                        Matrix.vecCons m₀ (Function.update mTail i m₁)
                      have hpure :
                          F (fun k => a k ⊗ₜ[R] m k) +
                            F (fun k => (a ∘ Equiv.swap 0 i.succ) k ⊗ₜ[R]
                              (m ∘ Equiv.swap 0 i.succ) k) = 0 :=
                        baseChangeMultilinearMapLinear_apply_pure_swap_add
                          (R := R) (A := A) (M := M) (N := N) (n + 2) f
                          a m (i := 0) (j := i.succ) (Fin.succ_ne_zero i).symm
                      have htuple₁ :
                          (fun k => a k ⊗ₜ[R] m k) =
                            Matrix.vecCons (a₀ ⊗ₜ[R] m₀)
                              (Function.update tail i (a₁ ⊗ₜ[R] m₁)) := by
                        funext k
                        cases k using Fin.cases with
                        | zero =>
                            simp [a, m, Matrix.vecCons,
                              Function.update_of_ne (Fin.succ_ne_zero i).symm]
                        | succ k =>
                            by_cases hk : k = i
                            · subst hk
                              simp [a, m, Matrix.vecCons]
                            · have hk_succ : k.succ ≠ i.succ := by
                                intro h
                                exact hk (Fin.succ_injective _ h)
                              simp [a, m, Matrix.vecCons, Function.update_of_ne hk_succ,
                                Function.update_of_ne hk, hTail k]
                      have htuple₂ :
                          (fun k => (a ∘ Equiv.swap 0 i.succ) k ⊗ₜ[R]
                              (m ∘ Equiv.swap 0 i.succ) k) =
                            Matrix.vecCons (a₁ ⊗ₜ[R] m₁)
                              (Function.update tail i (a₀ ⊗ₜ[R] m₀)) := by
                        funext k
                        simp only [Function.comp_apply]
                        cases k using Fin.cases with
                        | zero =>
                            have hsw : (Equiv.swap (0 : Fin (n + 2)) i.succ) 0 = i.succ :=
                              Equiv.swap_apply_left _ _
                            rw [hsw]
                            simp [a, m, Matrix.vecCons]
                        | succ k =>
                            by_cases hk : k = i
                            · subst hk
                              have hsw :
                                  (Equiv.swap (0 : Fin (n + 2)) k.succ) k.succ = 0 :=
                                Equiv.swap_apply_right _ _
                              rw [hsw]
                              simp [a, m, Matrix.vecCons,
                                Function.update_of_ne (Fin.succ_ne_zero k).symm]
                            · have hk_succ : k.succ ≠ i.succ := by
                                intro h
                                exact hk (Fin.succ_injective _ h)
                              have hsw :
                                  (Equiv.swap (0 : Fin (n + 2)) i.succ) k.succ = k.succ :=
                                Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero k) hk_succ
                              rw [hsw]
                              simp [a, m, Matrix.vecCons, Function.update_of_ne hk_succ,
                                Function.update_of_ne hk, hTail k]
                      rw [htuple₁, htuple₂] at hpure
                      simpa [F] using hpure
                  calc
                    F v = F (Matrix.vecCons (v 0) (Fin.tail v)) := by
                      simpa [F, Matrix.vecCons] using congrArg F (Fin.cons_self_tail v).symm
                    _ = F (Matrix.vecCons (Fin.tail v i) (Fin.tail v)) := by
                      rw [hv.symm]
                      rfl
                    _ = 0 := hfirst
          | succ j =>
              -- If both repeated coordinates are in the tail, first extend the curried
              -- tail-vanishing statement from pure first coordinates to arbitrary tensors.
              let L : TensorProduct R A M →ₗ[A] N :=
                { toFun := fun x => F.curryLeft x (Fin.tail v)
                  map_add' := by intro x y; simp [F]
                  map_smul' := by intro a x; simp [F] }
              have hLzero : L = 0 := by
                apply LinearMap.ext_on hs
                rintro _ ⟨a, m, rfl⟩
                have htail :
                    baseChangeMultilinearMapLinear (R := R) (A := A) (M := M) (N := N) n
                        ((f.curryLeft m).toMultilinearMap) (Fin.tail v) = 0 :=
                  ih (f.curryLeft m) (Fin.tail v) i j
                    (by simpa [Fin.tail] using hv)
                    (by intro hij'; exact hij (by simpa using congrArg Fin.succ hij'))
                calc
                  L (a ⊗ₜ[R] m) =
                      baseChangeMultilinearMapLinear (R := R) (A := A) (M := M) (N := N)
                        (n + 1) f.toMultilinearMap
                        (Matrix.vecCons (a ⊗ₜ[R] m) (Fin.tail v)) := by
                        rfl
                  _ = a •
                      baseChangeMultilinearMapLinear (R := R) (A := A) (M := M) (N := N) n
                        ((f.curryLeft m).toMultilinearMap) (Fin.tail v) := by
                        exact baseChangeMultilinearMapLinear_apply_cons_tmul
                          (R := R) (A := A) (M := M) (N := N) n
                          f.toMultilinearMap a m (Fin.tail v)
                  _ = 0 := by rw [htail, smul_zero]
              calc
                F v = F (Matrix.vecCons (v 0) (Fin.tail v)) := by
                  simpa [F, Matrix.vecCons] using congrArg F (Fin.cons_self_tail v).symm
                _ = L (v 0) := by rfl
                _ = 0 := by rw [hLzero]; rfl

/-- Helper for Chap10 Lemma 10 108 6: scalar extension of an alternating map from `M` to
an `A`-module. -/
noncomputable def baseChangeAlternatingMap
    {A : Type w} [CommRing A] [Algebra R A]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type z} [AddCommGroup N] [Module A N] [Module R N]
    [IsScalarTower R A N] [SMulCommClass R A N]
    (n : ℕ) (f : M [⋀^Fin n]→ₗ[R] N) :
    (TensorProduct R A M) [⋀^Fin n]→ₗ[A] N :=
  { baseChangeMultilinearMapLinear (R := R) (A := A) (M := M) (N := N) n
      f.toMultilinearMap with
    map_eq_zero_of_eq' := baseChangeMultilinearMapLinear_map_eq_zero_of_alternating
      (R := R) (A := A) (M := M) (N := N) n f }

/-- Helper for Chap10 Lemma 10 108 6: the scalar-extended alternating map has the expected
pure tensor formula. -/
theorem baseChangeAlternatingMap_apply_pure
    {A : Type w} [CommRing A] [Algebra R A]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type z} [AddCommGroup N] [Module A N] [Module R N]
    [IsScalarTower R A N] [SMulCommClass R A N]
    (n : ℕ) (f : M [⋀^Fin n]→ₗ[R] N)
    (a : Fin n → A) (m : Fin n → M) :
    baseChangeAlternatingMap (R := R) (A := A) (M := M) (N := N) n f
        (fun j => a j ⊗ₜ[R] m j) =
      (∏ j, a j) • f m := by
  -- Forget the alternating structure and use the multilinear pure-tensor computation.
  exact baseChangeMultilinearMapLinear_apply_pure (R := R) (A := A) (M := M) (N := N)
    n f.toMultilinearMap a m
end
