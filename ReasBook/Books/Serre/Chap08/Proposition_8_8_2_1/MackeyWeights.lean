import Serre.Chap08.Proposition_8_8_2_1.InductionBridge

open CategoryTheory

universe u v w x

namespace Representation

noncomputable section

section SemidirectAbelian

open scoped Representation

variable {A : Type u} [CommGroup A]
variable {H : Type v} [Group H]
variable (φ : H →* MulAut A)

/-- Helper for Proposition 8-8.2-1: the `ψ`-weight space for the action of the normal factor `A`
inside a representation of `A ⋊[φ] H`. -/
noncomputable abbrev transportedCharacter
    (h : H) (ψ : A →* ℂˣ) : A →* ℂˣ := by
  let _ := characterMulAction φ
  exact h • ψ

/-- Helper for Proposition 8-8.2-1: the transported character is obtained by precomposing with the
inverse `A`-action. -/
@[simp] theorem transportedCharacter_apply
    (h : H) (ψ : A →* ℂˣ) (a : A) :
    transportedCharacter (φ := φ) h ψ a = ψ ((MulEquiv.symm (φ h)) a) := by
  let _ := characterMulAction φ
  simpa [transportedCharacter] using smul_character_apply (φ := φ) h ψ a

/-- Helper for Proposition 8-8.2-1: transporting by `h` and then by `h⁻¹` returns the original
character. -/
@[simp] theorem transportedCharacter_inv_cancel
    (h : H) (ψ : A →* ℂˣ) :
    transportedCharacter (φ := φ) h⁻¹ (transportedCharacter (φ := φ) h ψ) = ψ := by
  let _ := characterMulAction φ
  simpa [transportedCharacter] using (smul_smul h⁻¹ h ψ)

/-- Helper for Proposition 8-8.2-1: transporting by `h⁻¹` and then by `h` returns the original
character. -/
@[simp] theorem transportedCharacter_inv_cancel'
    (h : H) (ψ : A →* ℂˣ) :
    transportedCharacter (φ := φ) h (transportedCharacter (φ := φ) h⁻¹ ψ) = ψ := by
  let _ := characterMulAction φ
  simpa [transportedCharacter] using (smul_smul h h⁻¹ ψ)

/-- Helper for Proposition 8-8.2-1: conjugating an element of the normal factor `A` by
`s : A ⋊[φ] H` keeps the second coordinate trivial and transports the first coordinate through the
inverse `H`-action. -/
@[simp] theorem semidirectProduct_inv_mul_inl_mul
    (s : A ⋊[φ] H) (a : A) :
    s⁻¹ * (⟨a, 1⟩ : A ⋊[φ] H) * s =
      (⟨MulEquiv.symm (φ s.right) a, 1⟩ : A ⋊[φ] H) := by
  ext
  · change
      (φ s.right⁻¹ s.left⁻¹ * φ s.right⁻¹ a) * φ (s.right⁻¹ * 1) s.left =
        MulEquiv.symm (φ s.right) a
    simp [mul_assoc]
  · simp

/-- Helper for Proposition 8-8.2-1: the normal element `(a,1)` always lies in the explicit packet
subgroup because its `H`-component is trivial. -/
@[simp] theorem semidirectProduct_inl_mem_character_stabilizer_subgroup
    (χ : A →* ℂˣ) (a : A) :
    (⟨a, 1⟩ : A ⋊[φ] H) ∈ character_stabilizer_subgroup (φ := φ) χ := by
  let _ := characterMulAction φ
  change ((1 : H) • χ : A →* ℂˣ) = χ
  simp

/-- Helper for Proposition 8-8.2-1: conjugating a normal element `(a,1)` by any semidirect-product
element still lands in the explicit packet subgroup. -/
@[simp] theorem semidirectProduct_inv_mul_inl_mul_mem_character_stabilizer_subgroup
    (χ : A →* ℂˣ) (s : A ⋊[φ] H) (a : A) :
    s⁻¹ * (⟨a, 1⟩ : A ⋊[φ] H) * s ∈ character_stabilizer_subgroup (φ := φ) χ := by
  rw [semidirectProduct_inv_mul_inl_mul]
  simpa using
    semidirectProduct_inl_mem_character_stabilizer_subgroup (φ := φ) χ
      (MulEquiv.symm (φ s.right) a)

/-- Helper for Proposition 8-8.2-1: the packet source on the explicit stabilizer subgroup acts on
the normal element `(a,1)` by the scalar `χ(a)`. -/
@[simp] theorem character_stabilizer_subgroup_source_apply_inl
    (χ : A →* ℂˣ) (ρ : Rep.{w} ℂ H_[φ; χ])
    (a : A)
    (ha : (⟨a, 1⟩ : A ⋊[φ] H) ∈ character_stabilizer_subgroup (φ := φ) χ)
    (v : ρ) :
    (((stabilizerRepresentation φ χ ρ).ρ.comp
        (character_stabilizer_subgroup_equiv (φ := φ) χ).symm.toMonoidHom)
      ⟨⟨a, 1⟩, ha⟩) v =
      (χ a : ℂ) • v := by
  change (stabilizerRepresentation φ χ ρ).ρ
      ((character_stabilizer_subgroup_equiv (φ := φ) χ).symm ⟨⟨a, 1⟩, ha⟩) v =
    (χ a : ℂ) • v
  change
      ((stabilizerCharacter φ χ (⟨a, (1 : H_[φ; χ])⟩) : ℂ) •
        ρ.ρ (1 : H_[φ; χ]) v) =
        (χ a : ℂ) • v
  simp [stabilizerCharacter_apply]

/-- Helper for Proposition 8-8.2-1: if `s` is outside the explicit packet subgroup, then its
`H`-component moves `χ` to a distinct character. -/
theorem transportedCharacter_ne_of_not_mem_character_stabilizer_subgroup
    (χ : A →* ℂˣ) {s : A ⋊[φ] H}
    (hs : s ∉ character_stabilizer_subgroup (φ := φ) χ) :
    transportedCharacter (φ := φ) s.right χ ≠ χ := by
  intro htransport
  apply hs
  let _ := characterMulAction φ
  change ((s.right : H) • χ : A →* ℂˣ) = χ
  simpa [transportedCharacter] using htransport

/-- Helper for Proposition 8-8.2-1: if one group element acts by two distinct scalars on the
source and target, then every intertwiner between the two representations is zero. -/
theorem intertwiningMap_eq_zero_of_scalar_action_mismatch
    {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    {g : G} {c d : ℂ}
    (hρ : ∀ v : V, ρ g v = c • v)
    (hσ : ∀ w : W, σ g w = d • w)
    (hcd : c ≠ d) (f : ρ.IntertwiningMap σ) :
    f = 0 := by
  apply Representation.IntertwiningMap.ext
  ext v
  have hintertwine := LinearMap.congr_fun (f.isIntertwining' g) v
  have hscalar :
      c • f.toLinearMap v = d • f.toLinearMap v := by
    calc
      c • f.toLinearMap v = f.toLinearMap (c • v) := by simp
      _ = f.toLinearMap (ρ g v) := by rw [hρ v]
      _ = σ g (f.toLinearMap v) := hintertwine
      _ = d • f.toLinearMap v := by rw [hσ (f.toLinearMap v)]
  have hsub : (c - d) • f.toLinearMap v = 0 := by
    calc
      (c - d) • f.toLinearMap v = c • f.toLinearMap v - d • f.toLinearMap v := by
        simp [sub_smul]
      _ = 0 := by rw [hscalar, sub_self]
  exact (smul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hcd)

/-- Helper for Proposition 8-8.2-1: if `s` is outside the explicit packet subgroup, then some
normal element `(a,1)` detects the resulting character mismatch on `A`. -/
theorem exists_character_mismatch_of_not_mem_character_stabilizer_subgroup
    (χ : A →* ℂˣ) {s : A ⋊[φ] H}
    (hs : s ∉ character_stabilizer_subgroup (φ := φ) χ) :
    ∃ a : A, transportedCharacter (φ := φ) s.right χ a ≠ χ a := by
  have htransport_ne :
      transportedCharacter (φ := φ) s.right χ ≠ χ :=
    transportedCharacter_ne_of_not_mem_character_stabilizer_subgroup (φ := φ) χ hs
  refine not_forall.mp ?_
  intro hall
  apply htransport_ne
  ext a
  exact congrArg (fun z : ℂˣ ↦ (z : ℂ)) (hall a)

/-- Helper for Proposition 8-8.2-1: the file-local Mackey conjugation map sends the normal element
`(a,1)` to `((φ s.right)⁻¹ a, 1)`. This is the concrete semidirect-product input needed for the
remaining Mackey-disjointness step. -/
theorem localMackeyConjMap_inl
    (χ : A →* ℂˣ) (s : A ⋊[φ] H) (a : A)
    (ha : (⟨a, 1⟩ : A ⋊[φ] H) ∈ character_stabilizer_subgroup (φ := φ) χ) :
    localMackeyConjMap (φ := φ) (character_stabilizer_subgroup (φ := φ) χ) s ⟨⟨a, 1⟩, ha⟩ =
      (⟨MulEquiv.symm (φ s.right) a, 1⟩ : A ⋊[φ] H) := by
  simpa [localMackeyConjMap] using semidirectProduct_inv_mul_inl_mul (φ := φ) s a

/-- Helper for Proposition 8-8.2-1: the normal element `(a,1)` lies in the file-local Mackey
subgroup attached to the packet subgroup and the element `s`. -/
theorem semidirectProduct_inl_mem_localMackeySubgroup
    (χ : A →* ℂˣ) (s : A ⋊[φ] H) (a : A) :
    ⟨⟨a, 1⟩,
      semidirectProduct_inl_mem_character_stabilizer_subgroup (φ := φ) χ a⟩ ∈
      localMackeySubgroup (φ := φ)
        (character_stabilizer_subgroup (φ := φ) χ)
        (character_stabilizer_subgroup (φ := φ) χ)
        s := by
  change
    localMackeyConjMap (φ := φ)
      (character_stabilizer_subgroup (φ := φ) χ) s
      ⟨⟨a, 1⟩,
        semidirectProduct_inl_mem_character_stabilizer_subgroup (φ := φ) χ a⟩ ∈
      character_stabilizer_subgroup (φ := φ) χ
  rw [localMackeyConjMap_inl (φ := φ) χ s a]
  simpa using
    semidirectProduct_inl_mem_character_stabilizer_subgroup (φ := φ) χ
      (MulEquiv.symm (φ s.right) a)

/-- Helper for Proposition 8-8.2-1: the normal element `(a,1)` viewed as an element of the
file-local Mackey subgroup attached to `s`. -/
abbrev localMackeySubgroup_inl
    (χ : A →* ℂˣ) (s : A ⋊[φ] H) (a : A) :
    localMackeySubgroup (φ := φ)
      (character_stabilizer_subgroup (φ := φ) χ)
      (character_stabilizer_subgroup (φ := φ) χ)
      s :=
  ⟨⟨⟨a, 1⟩,
      semidirectProduct_inl_mem_character_stabilizer_subgroup (φ := φ) χ a⟩,
    semidirectProduct_inl_mem_localMackeySubgroup (φ := φ) χ s a⟩

/-- Helper for Proposition 8-8.2-1: the file-local Mackey twist of the packet source acts on the
normal element `(a,1)` by the transported character `s • χ`. -/
@[simp] theorem theta_local_mackey_twist_apply_inl_scalar
    (χ : A →* ℂˣ) (ρ : Rep.{w} ℂ H_[φ; χ]) (s : A ⋊[φ] H) (a : A) (v : ρ) :
    (((localMackeyTwist (φ := φ)
        (character_stabilizer_subgroup (φ := φ) χ)
        (character_stabilizer_subgroup (φ := φ) χ)
        (theta_packet_source (φ := φ) χ ρ)
        s).ρ) (localMackeySubgroup_inl (φ := φ) χ s a) v) =
      (transportedCharacter (φ := φ) s.right χ a : ℂ) • v := by
  change
    ((theta_packet_source (φ := φ) χ ρ).ρ
      (localMackeyConjHom (φ := φ)
        (character_stabilizer_subgroup (φ := φ) χ)
        (character_stabilizer_subgroup (φ := φ) χ)
        s
        (localMackeySubgroup_inl (φ := φ) χ s a))) v =
      (transportedCharacter (φ := φ) s.right χ a : ℂ) • v
  have hconj :
      localMackeyConjHom (φ := φ)
        (character_stabilizer_subgroup (φ := φ) χ)
        (character_stabilizer_subgroup (φ := φ) χ)
        s
        (localMackeySubgroup_inl (φ := φ) χ s a) =
        ⟨⟨MulEquiv.symm (φ s.right) a, 1⟩,
          semidirectProduct_inl_mem_character_stabilizer_subgroup (φ := φ) χ
            (MulEquiv.symm (φ s.right) a)⟩ := by
    apply Subtype.ext
    simpa [localMackeySubgroup_inl, localMackeyConjHom] using
      localMackeyConjMap_inl (φ := φ) χ s a
        (semidirectProduct_inl_mem_character_stabilizer_subgroup (φ := φ) χ a)
  rw [hconj]
  simpa [theta_packet_source, transportedCharacter_apply] using
    character_stabilizer_subgroup_source_apply_inl
      (φ := φ) χ ρ (MulEquiv.symm (φ s.right) a)
      (semidirectProduct_inl_mem_character_stabilizer_subgroup (φ := φ) χ
        (MulEquiv.symm (φ s.right) a))
      v

/-- Helper for Proposition 8-8.2-1: if `s` is outside the explicit packet subgroup, then the
corresponding file-local Mackey twist is disjoint from the restricted packet source. -/
theorem theta_local_mackey_disjoint
    (χ : A →* ℂˣ) (ρ : Rep.{w} ℂ H_[φ; χ]) {s : A ⋊[φ] H}
    (hs : s ∉ character_stabilizer_subgroup (φ := φ) χ)
    (f :
      localMackeyTwist (φ := φ)
        (character_stabilizer_subgroup (φ := φ) χ)
        (character_stabilizer_subgroup (φ := φ) χ)
        (theta_packet_source (φ := φ) χ ρ)
        s ⟶
      Rep.res
        (localMackeySubgroup (φ := φ)
          (character_stabilizer_subgroup (φ := φ) χ)
          (character_stabilizer_subgroup (φ := φ) χ)
          s).subtype
        (theta_packet_source (φ := φ) χ ρ)) :
    f = 0 := by
  obtain ⟨a, ha⟩ :=
    exists_character_mismatch_of_not_mem_character_stabilizer_subgroup (φ := φ) χ hs
  let x :
      localMackeySubgroup (φ := φ)
        (character_stabilizer_subgroup (φ := φ) χ)
        (character_stabilizer_subgroup (φ := φ) χ)
        s := localMackeySubgroup_inl (φ := φ) χ s a
  apply (Rep.homLinearEquiv _ _).injective
  exact intertwiningMap_eq_zero_of_scalar_action_mismatch
    (g := x)
    (c := (transportedCharacter (φ := φ) s.right χ a : ℂ))
    (d := (χ a : ℂ))
    (hρ := theta_local_mackey_twist_apply_inl_scalar (φ := φ) χ ρ s a)
    (hσ := fun v ↦ by
      change
        ((theta_packet_source (φ := φ) χ ρ).ρ x.1) v =
          (χ a : ℂ) • v
      simpa [x, theta_packet_source] using
        character_stabilizer_subgroup_source_apply_inl
          (φ := φ) χ ρ a
          (semidirectProduct_inl_mem_character_stabilizer_subgroup (φ := φ) χ a)
          v)
    (hcd := by
      intro hEq
      apply ha
      exact Units.ext hEq)
    ((Rep.homLinearEquiv _ _) f)

/-- Helper for Proposition 8-8.2-1: the `ψ`-weight space for the action of the normal factor `A`
inside a representation of `A ⋊[φ] H`. -/
def character_weight_submodule
    (τ : Rep.{x} ℂ (A ⋊[φ] H)) (ψ : A →* ℂˣ) :
    Submodule ℂ τ where
  carrier := {x | ∀ a : A, τ.ρ ⟨a, 1⟩ x = (ψ a : ℂ) • x}
  zero_mem' := by
    intro a
    simp
  add_mem' := by
    intro x y hx hy a
    calc
      τ.ρ ⟨a, 1⟩ (x + y) = τ.ρ ⟨a, 1⟩ x + τ.ρ ⟨a, 1⟩ y := by simp
      _ = (ψ a : ℂ) • x + (ψ a : ℂ) • y := by rw [hx a, hy a]
      _ = (ψ a : ℂ) • (x + y) := by simp [smul_add]
  smul_mem' := by
    intro c x hx a
    calc
      τ.ρ ⟨a, 1⟩ (c • x) = c • τ.ρ ⟨a, 1⟩ x := by simp
      _ = c • ((ψ a : ℂ) • x) := by rw [hx a]
      _ = (ψ a : ℂ) • (c • x) := by simp [smul_smul, mul_comm]

/-- Helper for Proposition 8-8.2-1: multiplying an `A`-weight vector by `(1,h)` transports its
weight by the `H`-action on characters. -/
theorem character_weight_submodule_transport_mem
    (τ : Rep.{x} ℂ (A ⋊[φ] H)) (ψ : A →* ℂˣ) (h : H)
    {x : τ} (hx : x ∈ character_weight_submodule (φ := φ) τ ψ) :
    τ.ρ ⟨1, h⟩ x ∈ character_weight_submodule (φ := φ) τ
      (transportedCharacter (φ := φ) h ψ) := by
  intro a
  calc
    τ.ρ ⟨a, 1⟩ (τ.ρ ⟨1, h⟩ x) = τ.ρ (⟨a, 1⟩ * ⟨1, h⟩) x := by
      simp [map_mul]
    _ = τ.ρ (⟨1, h⟩ * ⟨MulEquiv.symm (φ h) a, 1⟩) x := by
      have hmul :
          (⟨a, 1⟩ : A ⋊[φ] H) * ⟨1, h⟩ =
            ⟨1, h⟩ * ⟨MulEquiv.symm (φ h) a, 1⟩ := by
        ext
        · change a * (φ (1 : H)) (1 : A) = 1 * φ h (MulEquiv.symm (φ h) a)
          simp
        · change (1 : H) * h = h * 1
          simp
      rw [hmul]
    _ = τ.ρ ⟨1, h⟩ (τ.ρ ⟨MulEquiv.symm (φ h) a, 1⟩ x) := by
      simp [map_mul]
    _ = τ.ρ ⟨1, h⟩ (((ψ (MulEquiv.symm (φ h) a) : ℂ)) • x) := by
      rw [hx (MulEquiv.symm (φ h) a)]
    _ = (ψ (MulEquiv.symm (φ h) a) : ℂ) • τ.ρ ⟨1, h⟩ x := by
      simp
    _ = ((transportedCharacter (φ := φ) h ψ a : ℂ)) • τ.ρ ⟨1, h⟩ x := by
      rw [transportedCharacter_apply]

/-- Helper for Proposition 8-8.2-1: `(1,h)` gives a linear equivalence between the `ψ`-weight
space and the `(h • ψ)`-weight space. -/
noncomputable def character_weight_submodule_transport_equiv
    (τ : Rep.{x} ℂ (A ⋊[φ] H)) (ψ : A →* ℂˣ) (h : H) :
    character_weight_submodule (φ := φ) τ ψ ≃ₗ[ℂ]
      character_weight_submodule (φ := φ) τ (transportedCharacter (φ := φ) h ψ) where
  toFun := fun x ↦
    ⟨τ.ρ ⟨1, h⟩ x,
      character_weight_submodule_transport_mem (φ := φ) τ ψ h x.property⟩
  invFun := fun y ↦ by
    refine ⟨τ.ρ ⟨1, h⁻¹⟩ y, ?_⟩
    simpa using
      character_weight_submodule_transport_mem (φ := φ) τ
        (transportedCharacter (φ := φ) h ψ) h⁻¹ y.property
  left_inv := by
    intro x
    apply Subtype.ext
    change τ.ρ ⟨1, h⁻¹⟩ (τ.ρ ⟨1, h⟩ x) = x
    calc
      τ.ρ ⟨1, h⁻¹⟩ (τ.ρ ⟨1, h⟩ x) = τ.ρ (⟨1, h⁻¹⟩ * ⟨1, h⟩) x := by
        simp [map_mul]
      _ = τ.ρ (1 : A ⋊[φ] H) x := by
        congr 1
        ext <;> simp [SemidirectProduct.mul_def]
      _ = x := by
        simp
  right_inv := by
    intro y
    apply Subtype.ext
    change τ.ρ ⟨1, h⟩ (τ.ρ ⟨1, h⁻¹⟩ y) = y
    calc
      τ.ρ ⟨1, h⟩ (τ.ρ ⟨1, h⁻¹⟩ y) = τ.ρ (⟨1, h⟩ * ⟨1, h⁻¹⟩) y := by
        simp [map_mul]
      _ = τ.ρ (1 : A ⋊[φ] H) y := by
        congr 1
        ext <;> simp [SemidirectProduct.mul_def]
      _ = y := by
        simp
  map_add' := by
    intro x y
    ext
    simp
  map_smul' := by
    intro c x
    ext
    simp

/-- Helper for Proposition 8-8.2-1: elements of the stabilizer preserve the corresponding
character-weight space. -/
theorem character_weight_submodule_stabilizer_mem
    (τ : Rep.{x} ℂ (A ⋊[φ] H)) (ψ : A →* ℂˣ) (h : H_[φ; ψ])
    {x : τ} (hx : x ∈ character_weight_submodule (φ := φ) τ ψ) :
    τ.ρ ⟨1, h⟩ x ∈ character_weight_submodule (φ := φ) τ ψ := by
  have htransport :=
    character_weight_submodule_transport_mem (φ := φ) τ ψ h hx
  have hfix : transportedCharacter (φ := φ) (h : H) ψ = ψ := by
    ext a
    exact congrArg (fun η : A →* ℂˣ ↦ (η a : ℂ)) h.property
  simpa [hfix] using htransport

/-- Helper for Proposition 8-8.2-1: the stabilizer acts linearly on its own character-weight
space by the operators `τ(1,h)`. -/
noncomputable def character_weight_subrepresentation_map
    (τ : Rep.{x} ℂ (A ⋊[φ] H)) (ψ : A →* ℂˣ) (h : H_[φ; ψ]) :
    character_weight_submodule (φ := φ) τ ψ →ₗ[ℂ]
      character_weight_submodule (φ := φ) τ ψ where
  toFun := fun x ↦
    ⟨τ.ρ ⟨1, h⟩ x,
      character_weight_submodule_stabilizer_mem (φ := φ) τ ψ h x.property⟩
  map_add' := by
    intro x y
    ext
    simp
  map_smul' := by
    intro c x
    ext
    simp

/-- Helper for Proposition 8-8.2-1: the stabilizer action on a character-weight space has the
expected identity operator. -/
theorem character_weight_subrepresentation_map_one
    (τ : Rep.{x} ℂ (A ⋊[φ] H)) (ψ : A →* ℂˣ) :
    character_weight_subrepresentation_map (φ := φ) τ ψ 1 = 1 := by
  ext x
  change τ.ρ ⟨1, (1 : H_[φ; ψ])⟩ x = x
  simpa using LinearMap.congr_fun (τ.ρ.map_one) x

/-- Helper for Proposition 8-8.2-1: the stabilizer action on a character-weight space respects
group multiplication. -/
theorem character_weight_subrepresentation_map_mul
    (τ : Rep.{x} ℂ (A ⋊[φ] H)) (ψ : A →* ℂˣ) (h h' : H_[φ; ψ]) :
    character_weight_subrepresentation_map (φ := φ) τ ψ (h * h') =
      character_weight_subrepresentation_map (φ := φ) τ ψ h *
        character_weight_subrepresentation_map (φ := φ) τ ψ h' := by
  ext x
  change τ.ρ ⟨1, h * h'⟩ x = τ.ρ ⟨1, h⟩ (τ.ρ ⟨1, h'⟩ x)
  have hmul :
      (⟨1, h * h'⟩ : A ⋊[φ] H) = ⟨1, h⟩ * ⟨1, h'⟩ := by
    ext
    · change (1 : A) = 1 * φ (h : H) (1 : A)
      simp
    · simp
  calc
    τ.ρ ⟨1, h * h'⟩ x = τ.ρ (⟨1, h⟩ * ⟨1, h'⟩) x := by rw [hmul]
    _ = τ.ρ ⟨1, h⟩ (τ.ρ ⟨1, h'⟩ x) := by
      simp [map_mul]

/-- Helper for Proposition 8-8.2-1: the `ψ`-weight space of `τ` is naturally a representation of
the stabilizer `H_[φ; ψ]`. -/
noncomputable def character_weight_subrepresentation
    (τ : Rep.{x} ℂ (A ⋊[φ] H)) (ψ : A →* ℂˣ) :
    Rep.{x} ℂ H_[φ; ψ] :=
  Rep.of <| {
    toFun := character_weight_subrepresentation_map (φ := φ) τ ψ
    map_one' := character_weight_subrepresentation_map_one (φ := φ) τ ψ
    map_mul' := character_weight_subrepresentation_map_mul (φ := φ) τ ψ
  }

/-- Helper for Proposition 8-8.2-1: representation equivalences preserve the `A`-weight
submodules. -/
theorem map_mem_character_weight_submodule_of_equiv
    {τ τ' : Rep.{x} ℂ (A ⋊[φ] H)} (e : τ.ρ.Equiv τ'.ρ)
    (ψ : A →* ℂˣ) {x : τ}
    (hx : x ∈ character_weight_submodule (φ := φ) τ ψ) :
    e x ∈ character_weight_submodule (φ := φ) τ' ψ := by
  intro a
  have hcomm := LinearMap.congr_fun (e.isIntertwining' ⟨a, 1⟩) x
  calc
    τ'.ρ ⟨a, 1⟩ (e x) = e (τ.ρ ⟨a, 1⟩ x) := by simpa using hcomm.symm
    _ = e ((ψ a : ℂ) • x) := by rw [hx a]
    _ = (ψ a : ℂ) • e x := by simp

section Proposition

open scoped Representation

variable [Finite H]

/-- Helper for Proposition 8-8.2-1: multiplying on the right by a normal element `(a,1)` can be
rewritten as multiplying on the left by the transported normal element. -/
theorem semidirectProduct_mul_inl_eq_inl_mul
    (u : A ⋊[φ] H) (a : A) :
    u * (⟨a, 1⟩ : A ⋊[φ] H) = (⟨φ u.right a, 1⟩ : A ⋊[φ] H) * u := by
  rcases u with ⟨x, h⟩
  ext
  · simpa only [SemidirectProduct.mul_def, map_one, MulAut.one_apply, mul_comm]
  · simp

/-- Helper for Proposition 8-8.2-1: after passing from the explicit subgroup model of `θ` to the
finite-index coinduced model, the underlying representation is unchanged up to equivalence. -/
noncomputable def theta_coind_character_stabilizer_subgroup_equiv
    (χ : A →* ℂˣ) (ρ : Rep.{w} ℂ H_[φ; χ]) :
    (θ[φ; χ, ρ]).ρ.Equiv
      (Rep.coind (character_stabilizer_subgroup (φ := φ) χ).subtype
        (theta_packet_source (φ := φ) χ ρ)).ρ := by
  let S : Subgroup (A ⋊[φ] H) := character_stabilizer_subgroup (φ := φ) χ
  letI : Finite ((A ⋊[φ] H) ⧸ S) := character_stabilizer_subgroup_quotient_finite (φ := φ) χ
  letI : S.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  letI : DecidableRel ⇑(QuotientGroup.rightRel S) := Classical.decRel _
  exact
    (theta_equiv_ind_character_stabilizer_subgroup (φ := φ) χ ρ).trans
      (Representation.equivOfIso (Rep.indCoindIso (theta_packet_source (φ := φ) χ ρ)))

/-- Helper for Proposition 8-8.2-1: if a character weight space of `θ[φ; χ, ρ]` is nonzero, then
the corresponding character lies in the `H`-orbit of `χ`. -/
theorem theta_weight_nonzero_imp_mem_orbit
    (χ : A →* ℂˣ) (ρ : Rep.{w} ℂ H_[φ; χ]) (ψ : A →* ℂˣ)
    (hψ : character_weight_submodule (φ := φ) (θ[φ; χ, ρ]) ψ ≠ ⊥) :
    ∃ h : H, transportedCharacter (φ := φ) h χ = ψ := by
  obtain ⟨x, hx, hx0⟩ :=
    (Submodule.ne_bot_iff
      (character_weight_submodule (φ := φ) (θ[φ; χ, ρ]) ψ)).mp hψ
  let e := theta_coind_character_stabilizer_subgroup_equiv (φ := φ) χ ρ
  let y := e x
  have hy_weight :
      y ∈ character_weight_submodule (φ := φ)
        (Rep.coind (character_stabilizer_subgroup (φ := φ) χ).subtype
          (theta_packet_source (φ := φ) χ ρ)) ψ := by
    simpa [y] using
      map_mem_character_weight_submodule_of_equiv
        (φ := φ) e ψ hx
  have hy0 : y ≠ 0 := by
    intro hy
    apply hx0
    calc
      x = e.symm (e x) := by simpa using (e.left_inv x).symm
      _ = e.symm y := by rfl
      _ = e.symm 0 := by rw [hy]
      _ = 0 := by simpa using e.symm.map_zero
  obtain ⟨s, hs⟩ : ∃ s : A ⋊[φ] H, y.1 s ≠ 0 := by
    by_contra hzero
    push_neg at hzero
    apply hy0
    apply Subtype.ext
    funext t
    exact hzero t
  refine ⟨s.right⁻¹, ?_⟩
  ext a
  have hs_mem :
      (⟨φ s.right a, 1⟩ : A ⋊[φ] H) ∈ character_stabilizer_subgroup (φ := φ) χ := by
    simpa using
      semidirectProduct_inl_mem_character_stabilizer_subgroup (φ := φ) χ (φ s.right a)
  have hy_coind :=
    (Representation.mem_coindV
      (φ := (character_stabilizer_subgroup (φ := φ) χ).subtype)
      (σ := (theta_packet_source (φ := φ) χ ρ).ρ)
      (f := y.1)).mp y.2
  have hweight_eval :
      y.1 (s * (⟨a, 1⟩ : A ⋊[φ] H)) = (ψ a : ℂ) • y.1 s := by
    simpa [Representation.coind_apply] using
      congrArg (fun z ↦ z.1 s) (hy_weight a)
  rw [semidirectProduct_mul_inl_eq_inl_mul (φ := φ) s a] at hweight_eval
  let gS : character_stabilizer_subgroup (φ := φ) χ := ⟨⟨φ s.right a, 1⟩, hs_mem⟩
  have hsource_eval :
      y.1 ((⟨φ s.right a, 1⟩ : A ⋊[φ] H) * s) =
        (χ (φ s.right a) : ℂ) • y.1 s := by
    calc
      y.1 (gS.1 * s) = (theta_packet_source (φ := φ) χ ρ).ρ gS (y.1 s) := by
        simpa using hy_coind gS s
      _ = (χ (φ s.right a) : ℂ) • y.1 s := by
        simpa [gS] using
          character_stabilizer_subgroup_source_apply_inl
            (φ := φ) χ ρ (φ s.right a) hs_mem (y.1 s)
  have hscalar :
      (ψ a : ℂ) = (χ (φ s.right a) : ℂ) := by
    exact (smul_left_injective ℂ hs) <| by
      calc
        (ψ a : ℂ) • y.1 s =
            y.1 ((⟨φ s.right a, 1⟩ : A ⋊[φ] H) * s) := by
              simpa using hweight_eval.symm
        _ = (χ (φ s.right a) : ℂ) • y.1 s := hsource_eval
  calc
    ((transportedCharacter (φ := φ) s.right⁻¹ χ a : ℂ)) = (χ (φ s.right a) : ℂ) := by
      rw [transportedCharacter_apply]
      simp
    _ = (ψ a : ℂ) := hscalar.symm

end Proposition

end SemidirectAbelian

end

end Representation
