import Mathlib
import StacksProject_2024.Chap10.Proposition_10_89_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

open scoped TensorProduct

/- Domain triage: this proposition is about the tensor-product comparison map from a tensor with
an arbitrary product to the product of the tensors.
- `source-facing`: the TFAE identifying finite presentation of `M` with bijectivity of those
  comparison maps.
- `core/canonical`: the owner maps `TensorProduct.piRightHom` and `TensorProduct.piScalarRightHom`
  from mathlib.
- `bridge/view`: the constant-family and scalar-family clauses are just specializations of those
  owner maps, not separate primitive data.
Primitive data are only the ring, the module, and the chosen family `Q`. -/

/- Route correction: the statement needs the same universe alignment as Proposition `10.89.2`.
The source-faithful proof tests clause `(4)` on `ULift M`, so the product index universe must be
large enough to contain `M`. -/

-- Proof sketch: `(1) → (2)` follows from a finite presentation of `M` and exactness of tensor
-- product, using that finite products commute with tensoring by finite free modules. The
-- implications `(2) → (3) → (4)` are immediate specializations. For `(4) → (1)`, combine
-- Proposition `10.89.2` to obtain finite generation of `M`, choose a surjection from a finite free
-- module onto `M`, and compare kernels after tensoring with `R^A`; surjectivity of the induced map
-- on the kernel then yields finite generation of that kernel, hence finite presentation of `M`.
/-- Helper for Proposition 10.89.3: `TensorProduct.piRightHom` commutes with tensoring a map on
the left. -/
lemma piRightHom_rTensor_apply_linear {X : Type*} [AddCommGroup X] [Module R X] {Y : Type*}
    [AddCommGroup Y] [Module R Y] {A : Type w} {Q : A → Type x}
    [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)] (f : X →ₗ[R] Y)
    (t : X ⊗[R] (∀ a, Q a)) :
    TensorProduct.piRightHom R R Y Q (f.rTensor (∀ a, Q a) t) =
      fun a ↦ f.rTensor (Q a) ((TensorProduct.piRightHom R R X Q t) a) := by
  -- Compute on pure tensors and extend by tensor induction.
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · ext a
    simp
  · intro x q
    ext a
    simp [TensorProduct.piRightHom_tmul]
  · intro t₁ t₂ ht₁ ht₂
    ext a
    simp [ht₁, ht₂]

/-- Helper for Proposition 10.89.3: `TensorProduct.piScalarRightHom` commutes with tensoring a map
on the left. -/
lemma piScalarRightHom_rTensor_apply {X : Type*} [AddCommGroup X] [Module R X] {Y : Type*}
    [AddCommGroup Y] [Module R Y] {A : Type w} (f : X →ₗ[R] Y)
    (t : X ⊗[R] (A → R)) :
    TensorProduct.piScalarRightHom R R Y A (f.rTensor (A → R) t) =
      fun a ↦ f ((TensorProduct.piScalarRightHom R R X A t) a) := by
  -- Compute on pure tensors and extend by tensor induction.
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · ext a
    simp
  · intro x q
    ext a
    simp [TensorProduct.piScalarRightHom_tmul]
  · intro t₁ t₂ ht₁ ht₂
    ext a
    simp [ht₁, ht₂]

/-- Helper for Proposition 10.89.3: after identifying a tensor with a finite free module on the
left with a tuple, `TensorProduct.piScalarRightHom` is just transposition of indices. -/
lemma piScalarRightHom_fin_free_tensor_equiv {n : ℕ} {A : Type w}
    (t : ((Fin n → R) ⊗[R] (A → R))) :
    TensorProduct.piScalarRightHom R R (Fin n → R) A t =
      fun a i ↦ fin_free_tensor_equiv (R := R) n (A → R) t i a := by
  -- Reduce to pure tensors, where both sides are coordinatewise evaluation.
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · ext a i
    simp [fin_free_tensor_equiv]
  · intro f q
    ext a i
    simp [fin_free_tensor_equiv, TensorProduct.piScalarRightHom_tmul, mul_comm]
  · intro t₁ t₂ ht₁ ht₂
    ext a i
    simp [ht₁, ht₂]

/-- Helper for Proposition 10.89.3: for a finite free module on the left,
`TensorProduct.piRightHom` is bijective. -/
lemma piRightHom_bijective_fin_free (n : ℕ) (A : Type w) (Q : A → Type x)
    [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)] :
    Function.Bijective (TensorProduct.piRightHom R R (Fin n → R) Q) := by
  constructor
  · intro t₁ t₂ h
    apply (fin_free_tensor_equiv (R := R) n (∀ a, Q a)).injective
    ext i a
    have hcoord :
        fin_free_tensor_equiv (R := R) n (Q a)
          ((TensorProduct.piRightHom R R (Fin n → R) Q t₁) a) =
        fin_free_tensor_equiv (R := R) n (Q a)
          ((TensorProduct.piRightHom R R (Fin n → R) Q t₂) a) := by
      exact congrArg (fin_free_tensor_equiv (R := R) n (Q a)) (congr_fun h a)
    have h₁ := congr_fun (piRightHom_fin_free_tensor_equiv (R := R) (Q := Q) t₁) a
    have h₂ := congr_fun (piRightHom_fin_free_tensor_equiv (R := R) (Q := Q) t₂) a
    calc
      fin_free_tensor_equiv (R := R) n (∀ a, Q a) t₁ i a
          = fin_free_tensor_equiv (R := R) n (Q a)
              ((TensorProduct.piRightHom R R (Fin n → R) Q t₁) a) i := by
                  simpa using (congr_fun h₁ i).symm
      _ = fin_free_tensor_equiv (R := R) n (Q a)
            ((TensorProduct.piRightHom R R (Fin n → R) Q t₂) a) i := by
              simpa using congr_fun hcoord i
      _ = fin_free_tensor_equiv (R := R) n (∀ a, Q a) t₂ i a := by
            simpa using congr_fun h₂ i
  · -- Reuse the finite-generation surjectivity lemma from Proposition `10.89.2`.
    exact piRightHom_surjective_fin_free (R := R) n A Q

/-- Helper for Proposition 10.89.3: for a finite free module on the left,
`TensorProduct.piScalarRightHom` is bijective. -/
lemma piScalarRightHom_bijective_fin_free (n : ℕ) (A : Type w) :
    Function.Bijective (TensorProduct.piScalarRightHom R R (Fin n → R) A) := by
  constructor
  · intro t₁ t₂ h
    apply (fin_free_tensor_equiv (R := R) n (A → R)).injective
    ext i a
    have hswap :
        (fun a i ↦ fin_free_tensor_equiv (R := R) n (A → R) t₁ i a) =
          fun a i ↦ fin_free_tensor_equiv (R := R) n (A → R) t₂ i a := by
      calc
        (fun a i ↦ fin_free_tensor_equiv (R := R) n (A → R) t₁ i a)
            = TensorProduct.piScalarRightHom R R (Fin n → R) A t₁ := by
                symm
                exact piScalarRightHom_fin_free_tensor_equiv (R := R) t₁
        _ = TensorProduct.piScalarRightHom R R (Fin n → R) A t₂ := h
        _ = (fun a i ↦ fin_free_tensor_equiv (R := R) n (A → R) t₂ i a) := by
              exact piScalarRightHom_fin_free_tensor_equiv (R := R) t₂
    exact congr_fun (congr_fun hswap a) i
  · intro y
    let z : Fin n → A → R := fun i a ↦ y a i
    refine ⟨(fin_free_tensor_equiv (R := R) n (A → R)).symm z, ?_⟩
    ext a i
    -- The finite-free tensor identification turns the map into index transposition.
    simpa [z] using congr_fun
      (congr_fun
        (piScalarRightHom_fin_free_tensor_equiv (R := R)
          ((fin_free_tensor_equiv (R := R) n (A → R)).symm z)) a) i

/-- Helper for Proposition 10.89.3: finite modules satisfy surjectivity of
`TensorProduct.piRightHom` for arbitrary index and fiber universes. -/
lemma piRightHom_surjective_of_finite_universe_lift {N : Type*} [AddCommGroup N] [Module R N]
    [Module.Finite R N] {A : Type w} {Q : A → Type x}
    [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)] :
    Function.Surjective (TensorProduct.piRightHom R R N Q) := by
  intro y
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R N
  obtain ⟨y₀, hy₀⟩ := Function.Surjective.piMap
    (fun a ↦ LinearMap.rTensor_surjective (Q a) hf) y
  obtain ⟨t, ht⟩ := piRightHom_surjective_fin_free (R := R) n A Q y₀
  refine ⟨f.rTensor (∀ a, Q a) t, ?_⟩
  ext a
  calc
    TensorProduct.piRightHom R R N Q (f.rTensor (∀ a, Q a) t) a
        = f.rTensor (Q a) ((TensorProduct.piRightHom R R (Fin n → R) Q t) a) := by
            simpa using congr_fun
              (piRightHom_rTensor_apply_linear (R := R) (Q := Q) f t) a
    _ = f.rTensor (Q a) (y₀ a) := by rw [ht]
    _ = y a := by simpa using congr_fun hy₀ a

/-- Helper for Proposition 10.89.3: replacing the constant family `ULift R` by `R` on the tensor
source is a linear equivalence for arbitrary index universes. -/
def pi_ulift_scalar_domain_equiv_univ (A : Type*) :
    (M ⊗[R] (A → ULift.{max u x} R)) ≃ₗ[R] (M ⊗[R] (A → R)) :=
  TensorProduct.congr (LinearEquiv.refl R M)
    (LinearEquiv.piCongrRight fun _ ↦ ULift.moduleEquiv)

/-- Helper for Proposition 10.89.3: replacing the constant family `ULift R` by `R` on the target
product is a linear equivalence for arbitrary index universes. -/
def pi_ulift_scalar_codomain_equiv_univ (A : Type*) :
    (A → M ⊗[R] ULift.{max u x} R) ≃ₗ[R] (A → M) :=
  LinearEquiv.piCongrRight fun _ ↦
    TensorProduct.congr (LinearEquiv.refl R M) ULift.moduleEquiv ≪≫ₗ TensorProduct.rid R M

/-- Helper for Proposition 10.89.3: after transporting the constant family `ULift R` back to `R`
for an arbitrary index universe, the canonical map `TensorProduct.piRightHom` becomes
`TensorProduct.piScalarRightHom`. -/
lemma piScalarRightHom_eq_piRightHom_ulift_univ (A : Type*)
    (t : M ⊗[R] (A → ULift.{max u x} R)) :
    TensorProduct.piScalarRightHom R R M A
        ((pi_ulift_scalar_domain_equiv_univ (R := R) (M := M) A) t) =
      pi_ulift_scalar_codomain_equiv_univ (R := R) (M := M) A
        (TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) t) := by
  -- Both sides are linear in `t`, so it suffices to compute on pure tensors.
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · ext a
    simp [pi_ulift_scalar_domain_equiv_univ, pi_ulift_scalar_codomain_equiv_univ]
  · intro m f
    ext a
    simp [pi_ulift_scalar_domain_equiv_univ, pi_ulift_scalar_codomain_equiv_univ,
      TensorProduct.piRightHom_tmul, TensorProduct.piScalarRightHom_tmul]
  · intro t₁ t₂ ht₁ ht₂
    ext a
    simp [ht₁, ht₂]

/-- Helper for Proposition 10.89.3: bijectivity of `TensorProduct.piScalarRightHom` is equivalent
to bijectivity of the constant-family comparison map with coefficients in `ULift R`. -/
lemma piScalarRightHom_bijective_iff_piRightHom_ulift_bijective
    (A : Type (max u v w)) :
    Function.Bijective (TensorProduct.piScalarRightHom R R M A) ↔
      Function.Bijective (TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R)) := by
  let d := pi_ulift_scalar_domain_equiv_univ (R := R) (M := M) A
  let c := pi_ulift_scalar_codomain_equiv_univ (R := R) (M := M) A
  constructor
  · intro hScalar
    constructor
    · intro t₁ t₂ hEq
      have hEq' :
          TensorProduct.piScalarRightHom R R M A (d t₁) =
            TensorProduct.piScalarRightHom R R M A (d t₂) := by
        calc
          TensorProduct.piScalarRightHom R R M A (d t₁)
              = c (TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) t₁) := by
                  simpa [d, c] using
                    piScalarRightHom_eq_piRightHom_ulift_univ (R := R) (M := M) A t₁
          _ = c (TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) t₂) := by
                rw [hEq]
          _ = TensorProduct.piScalarRightHom R R M A (d t₂) := by
                simpa [d, c] using
                  (piScalarRightHom_eq_piRightHom_ulift_univ (R := R) (M := M) A t₂).symm
      exact d.injective (hScalar.1 hEq')
    · intro y
      let y' := c y
      obtain ⟨t, ht⟩ := hScalar.2 y'
      have hd : d (d.symm t) = t := by
        simpa [d] using d.apply_symm_apply t
      have htransport :
          c (TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) (d.symm t)) =
            TensorProduct.piScalarRightHom R R M A (d (d.symm t)) := by
        calc
          c (TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) (d.symm t))
              = TensorProduct.piScalarRightHom R R M A
                  ((pi_ulift_scalar_domain_equiv_univ (R := R) (M := M) A) (d.symm t)) := by
                    simpa [c] using
                      (piScalarRightHom_eq_piRightHom_ulift_univ (R := R) (M := M) A
                        (d.symm t)).symm
          _ = TensorProduct.piScalarRightHom R R M A (d (d.symm t)) := by rfl
      refine ⟨d.symm t, ?_⟩
      apply c.injective
      calc
        c (TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) (d.symm t))
            = TensorProduct.piScalarRightHom R R M A (d (d.symm t)) := htransport
        _ = TensorProduct.piScalarRightHom R R M A t := by rw [hd]
        _ = y' := ht
        _ = c y := rfl
  · intro hPi
    constructor
    · intro t₁ t₂ hEq
      let s₁ := d.symm t₁
      let s₂ := d.symm t₂
      have hs₁ : d s₁ = t₁ := by
        simpa [s₁, d] using d.apply_symm_apply t₁
      have hs₂ : d s₂ = t₂ := by
        simpa [s₂, d] using d.apply_symm_apply t₂
      have hs₁_transport :
          c (TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) s₁) =
            TensorProduct.piScalarRightHom R R M A (d s₁) := by
        calc
          c (TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) s₁)
              = TensorProduct.piScalarRightHom R R M A
                  ((pi_ulift_scalar_domain_equiv_univ (R := R) (M := M) A) s₁) := by
                    simpa [c] using
                      (piScalarRightHom_eq_piRightHom_ulift_univ (R := R) (M := M) A s₁).symm
          _ = TensorProduct.piScalarRightHom R R M A (d s₁) := by rfl
      have hs₂_transport :
          TensorProduct.piScalarRightHom R R M A (d s₂) =
            c (TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) s₂) := by
        calc
          TensorProduct.piScalarRightHom R R M A (d s₂)
              = TensorProduct.piScalarRightHom R R M A
                  ((pi_ulift_scalar_domain_equiv_univ (R := R) (M := M) A) s₂) := by
                    rfl
          _ = c (TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) s₂) := by
                simpa [c] using
                  piScalarRightHom_eq_piRightHom_ulift_univ (R := R) (M := M) A s₂
      have hEq' :
          TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) s₁ =
            TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) s₂ := by
        apply c.injective
        calc
          c (TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) s₁)
              = TensorProduct.piScalarRightHom R R M A (d s₁) := hs₁_transport
          _ = TensorProduct.piScalarRightHom R R M A t₁ := by rw [hs₁]
          _ = TensorProduct.piScalarRightHom R R M A t₂ := hEq
          _ = TensorProduct.piScalarRightHom R R M A (d s₂) := by rw [hs₂]
          _ = c (TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) s₂) :=
                hs₂_transport
      simpa [s₁, s₂, d] using congrArg d (hPi.1 hEq')
    · intro y
      let y' := c.symm y
      obtain ⟨t, ht⟩ := hPi.2 y'
      refine ⟨d t, ?_⟩
      calc
        TensorProduct.piScalarRightHom R R M A (d t)
            = c (TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) t) := by
                simpa [d, c] using
                      piScalarRightHom_eq_piRightHom_ulift_univ (R := R) (M := M) A t
        _ = c y' := by rw [ht]
        _ = y := by simp [y']

/-- Helper for Proposition 10.89.3: exactness plus surjectivity on the kernel and bijectivity on
the finite free cover give bijectivity on the quotient module. -/
lemma piRightHom_bijective_of_exact {K : Type*} [AddCommGroup K] [Module R K] {F : Type*}
    [AddCommGroup F] [Module R F] (κ : K →ₗ[R] F) (π : F →ₗ[R] M)
    (hExact : Function.Exact κ π) (hπ : Function.Surjective π) {A : Type w}
    {Q : A → Type x} [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)]
    (hK : Function.Surjective (TensorProduct.piRightHom R R K Q))
    (hF : Function.Bijective (TensorProduct.piRightHom R R F Q)) :
    Function.Bijective (TensorProduct.piRightHom R R M Q) := by
  constructor
  · intro t₁ t₂ hEq
    obtain ⟨u, hu⟩ := LinearMap.rTensor_surjective (∀ a, Q a) hπ (t₁ - t₂)
    have hcoord_zero :
        ∀ a,
          π.rTensor (Q a) ((TensorProduct.piRightHom R R F Q u) a) = 0 := by
      intro a
      calc
        π.rTensor (Q a) ((TensorProduct.piRightHom R R F Q u) a)
            = TensorProduct.piRightHom R R M Q (π.rTensor (∀ a, Q a) u) a := by
                symm
                simpa using congr_fun
                  (piRightHom_rTensor_apply_linear (R := R) (Q := Q) π u) a
        _ = TensorProduct.piRightHom R R M Q (t₁ - t₂) a := by rw [hu]
        _ = (TensorProduct.piRightHom R R M Q t₁) a -
              (TensorProduct.piRightHom R R M Q t₂) a := by
                simp
        _ = 0 := by
              simpa using sub_eq_zero.mpr (congr_fun hEq a)
    have hcoord_range :
        ∀ a, (TensorProduct.piRightHom R R F Q u) a ∈
          LinearMap.range (κ.rTensor (Q a)) := by
      intro a
      rw [← Function.Exact.linearMap_ker_eq (rTensor_exact (Q a) hExact hπ)]
      simpa [LinearMap.mem_ker] using hcoord_zero a
    classical
    choose z hz using hcoord_range
    obtain ⟨s, hs⟩ := hK z
    have hu_eq :
        u = κ.rTensor (∀ a, Q a) s := by
      apply hF.1
      ext a
      calc
        TensorProduct.piRightHom R R F Q u a = κ.rTensor (Q a) (z a) := (hz a).symm
        _ = κ.rTensor (Q a) ((TensorProduct.piRightHom R R K Q s) a) := by rw [hs]
        _ = TensorProduct.piRightHom R R F Q (κ.rTensor (∀ a, Q a) s) a := by
              symm
              simpa using congr_fun
                (piRightHom_rTensor_apply_linear (R := R) (Q := Q) κ s) a
    have hsub : t₁ - t₂ = 0 := by
      calc
        t₁ - t₂ = π.rTensor (∀ a, Q a) u := hu.symm
        _ = π.rTensor (∀ a, Q a) (κ.rTensor (∀ a, Q a) s) := by rw [hu_eq]
        _ = ((π.rTensor (∀ a, Q a)).comp (κ.rTensor (∀ a, Q a))) s := rfl
        _ = ((π.comp κ).rTensor (∀ a, Q a)) s := by
              rw [← LinearMap.rTensor_comp]
        _ = 0 := by
              rw [hExact.linearMap_comp_eq_zero, LinearMap.rTensor_zero, LinearMap.zero_apply]
    exact sub_eq_zero.mp hsub
  · intro y
    -- Lift the target family coordinatewise through `π`, then use bijectivity on `F`.
    obtain ⟨y₀, hy₀⟩ := Function.Surjective.piMap
      (fun a ↦ LinearMap.rTensor_surjective (Q a) hπ) y
    obtain ⟨t, ht⟩ := hF.2 y₀
    refine ⟨π.rTensor (∀ a, Q a) t, ?_⟩
    ext a
    calc
      TensorProduct.piRightHom R R M Q (π.rTensor (∀ a, Q a) t) a
          = π.rTensor (Q a) ((TensorProduct.piRightHom R R F Q t) a) := by
              simpa using congr_fun
                (piRightHom_rTensor_apply_linear (R := R) (Q := Q) π t) a
      _ = π.rTensor (Q a) (y₀ a) := by rw [ht]
      _ = y a := by simpa using congr_fun hy₀ a

/-- Helper for Proposition 10.89.3: if the scalar comparison maps are bijective for a surjection
from a finite free module onto `M`, then the scalar comparison map is surjective on the kernel. -/
lemma piScalarRightHom_surjective_of_exact {F : Type*} [AddCommGroup F] [Module R F]
    (π : F →ₗ[R] M) (hπ : Function.Surjective π) (A : Type w)
    (hF : Function.Bijective (TensorProduct.piScalarRightHom R R F A))
    (hM : Function.Bijective (TensorProduct.piScalarRightHom R R M A)) :
    Function.Surjective (TensorProduct.piScalarRightHom R R (LinearMap.ker π) A) := by
  intro y
  let yF : A → F := fun a ↦ y a
  -- Lift the family of kernel elements to the finite free cover.
  obtain ⟨tF, htF⟩ := hF.2 yF
  have htF_zero : π.rTensor (A → R) tF = 0 := by
    apply hM.1
    ext a
    calc
      TensorProduct.piScalarRightHom R R M A (π.rTensor (A → R) tF) a
          = π ((TensorProduct.piScalarRightHom R R F A tF) a) := by
              simpa using congr_fun
                (piScalarRightHom_rTensor_apply (R := R) (A := A) π tF) a
      _ = π (yF a) := by rw [htF]
      _ = 0 := by
            change π (y a) = 0
            exact (y a).property
  have hmem : tF ∈ LinearMap.range ((LinearMap.ker π).subtype.rTensor (A → R)) := by
    rw [← Function.Exact.linearMap_ker_eq
      (rTensor_exact (A → R) (LinearMap.exact_subtype_ker_map π) hπ)]
    simpa [LinearMap.mem_ker] using htF_zero
  obtain ⟨u, hu⟩ := hmem
  refine ⟨u, ?_⟩
  ext a
  calc
    (((TensorProduct.piScalarRightHom R R (LinearMap.ker π) A u) a : LinearMap.ker π) : F)
        = TensorProduct.piScalarRightHom R R F A
            ((LinearMap.ker π).subtype.rTensor (A → R) u) a := by
              symm
              simpa using congr_fun
                (piScalarRightHom_rTensor_apply (R := R) (A := A)
                  (LinearMap.ker π).subtype u) a
    _ = yF a := by rw [hu, htF]
    _ = y a := rfl

/-- Proposition 10.89.3: for an `R`-module `M`, the following are equivalent: `M` is finitely
presented; for every family `(Q α)`, the canonical map
`M ⊗[R] (∀ α, Q α) → ∀ α, M ⊗[R] Q α` is bijective; for every `R`-module `Q` and every set `A`,
the canonical map `M ⊗[R] (A → Q) → A → (M ⊗[R] Q)` is bijective; and for every set `A`, the
canonical map `M ⊗[R] (A → R) → A → M` is bijective. -/
theorem module_finitePresentation_tfae_tensorProduct_pi_bijective :
    List.TFAE
      [ Module.FinitePresentation R M,
        ∀ (A : Type (max u v w)) (Q : A → Type (max u x))
            [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)],
          Function.Bijective (TensorProduct.piRightHom R R M Q),
        ∀ (A : Type (max u v w)) (Q : Type (max u x)) [AddCommGroup Q] [Module R Q],
          Function.Bijective (TensorProduct.piRightHom R R M (fun _ : A ↦ Q)),
        ∀ (A : Type (max u v w)),
          Function.Bijective (TensorProduct.piScalarRightHom R R M A) ] := by
  -- Route correction: align the quantified index universe with the ring universe so clause `(4)`
  -- can be tested on `ULift (LinearMap.ker π)` in the kernel step of the source proof.
  tfae_have 1 → 2 := by
    intro hM
    letI : Module.FinitePresentation R M := hM
    letI : Module.Finite R M := inferInstance
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
    letI : Module.Finite R (LinearMap.ker π) := by
      exact Module.Finite.of_fg (Module.FinitePresentation.fg_ker π hπ)
    intro A Q _ _
    -- Compare the exact rows obtained from the finite free cover of `M`.
    exact piRightHom_bijective_of_exact
      (R := R) ((LinearMap.ker π).subtype) π
      (LinearMap.exact_subtype_ker_map π) hπ
      (piRightHom_surjective_of_finite_universe_lift (R := R)
        (N := LinearMap.ker π) (A := A) (Q := Q))
      (piRightHom_bijective_fin_free (R := R) n A Q)
  tfae_have 2 → 3 := by
    intro h A Q _ _
    -- This is the constant-family specialization of clause `(2)`.
    simpa using h A (fun _ : A ↦ Q)
  tfae_have 3 → 4 := by
    intro h A
    -- Transport the constant `ULift R` family back to the scalar comparison map.
    exact (piScalarRightHom_bijective_iff_piRightHom_ulift_bijective
      (R := R) (M := M) A).2 (h A (ULift.{max u x} R))
  tfae_have 4 → 1 := by
    intro h
    have hMfinite : Module.Finite R M := by
      obtain ⟨t, ht⟩ := (h (ULift.{max u v w} M)).2 ULift.down
      exact module_finite_of_piScalarRightHom_eq_surjective
        (R := R) (M := M) (A := ULift.{max u v w} M) (d := ULift.down)
        (fun x ↦ ⟨⟨x⟩, rfl⟩) ht
    letI : Module.Finite R M := hMfinite
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
    have hker_surj :
        ∀ (A : Type (max u v w)),
          Function.Surjective
            (TensorProduct.piScalarRightHom R R (LinearMap.ker π) A) := by
      intro A
      -- The second source diagram chase transfers scalar-map surjectivity to the kernel.
      exact piScalarRightHom_surjective_of_exact (R := R) π hπ A
        (piScalarRightHom_bijective_fin_free (R := R) n A) (h A)
    have hker_finite : Module.Finite R (LinearMap.ker π) := by
      obtain ⟨t, ht⟩ := hker_surj (ULift.{max u v w} (LinearMap.ker π)) ULift.down
      exact module_finite_of_piScalarRightHom_eq_surjective
        (R := R) (M := LinearMap.ker π) (A := ULift.{max u v w} (LinearMap.ker π))
        (d := ULift.down) (fun x ↦ ⟨⟨x⟩, rfl⟩) ht
    letI : Module.Finite R (LinearMap.ker π) := hker_finite
    -- Finite generation of the kernel upgrades the finite free cover to a finite presentation.
    exact Module.finitePresentation_of_surjective π hπ Submodule.FG.of_finite
  tfae_finish

end
