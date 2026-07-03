import Mathlib
import Mathlib.Analysis.Matrix.PosDef

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_16_16_3_9 (from Chap16) -/
open CategoryTheory
open scoped BigOperators TensorProduct

noncomputable section

namespace Representation

namespace FDRep

variable {A : Type} [CommRing A] [IsLocalRing A]
variable {G : Type} [Group G]

/-- Helper for Exercise 16-16.3-9: a residue-field representation has an `(R')`-lift if it is the
reduction of a stable lattice in a simple characteristic-zero representation. -/
def HasRPrimeLift (S : FDRep (IsLocalRing.ResidueField A) G)
    (K : Type) [Field K] [Algebra A K] [IsFractionRing A K] : Prop :=
  ∃ X : FDRep K G, Simple X ∧
    ∃ L : StableLattice A X.ρ, Nonempty (FDRep.of L.reductionRepresentation ≅ S)

end FDRep

section SpecialLinear

variable {p : ℕ} [Fact p.Prime]
variable {V : Type} [AddCommGroup V] [Module (ZMod p) V]

local notation "ρSL" =>
  Representation.ofDistribMulAction (ZMod p) (SpecialLinearGroup (ZMod p) V) V

/-- Helper for Exercise 16-16.3-9: the standard upper-unipotent matrix in `SL₂(𝔽_p)`. -/
def upper_unipotent_matrix (a : ZMod p) :
    Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
  ⟨!![1, a; 0, 1], by
    -- The determinant of the standard upper-unipotent matrix is `1`.
    simp [Matrix.det_fin_two_of]⟩

/-- Helper for Exercise 16-16.3-9: the standard lower-unipotent matrix in `SL₂(𝔽_p)`. -/
def lower_unipotent_matrix (a : ZMod p) :
    Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
  ⟨!![1, 0; a, 1], by
    -- The determinant of the standard lower-unipotent matrix is `1`.
    simp [Matrix.det_fin_two_of]⟩

/-- Helper for Exercise 16-16.3-9: the upper-unipotent element of the standard special linear
group on `𝔽_p²`. -/
noncomputable def upper_unipotent (a : ZMod p) :
    SpecialLinearGroup (ZMod p) (Fin 2 → ZMod p) :=
  Matrix.SpecialLinearGroup.toLin'_equiv (n := Fin 2) (R := ZMod p)
    (upper_unipotent_matrix (p := p) a)

/-- Helper for Exercise 16-16.3-9: the lower-unipotent element of the standard special linear
group on `𝔽_p²`. -/
noncomputable def lower_unipotent (a : ZMod p) :
    SpecialLinearGroup (ZMod p) (Fin 2 → ZMod p) :=
  Matrix.SpecialLinearGroup.toLin'_equiv (n := Fin 2) (R := ZMod p)
    (lower_unipotent_matrix (p := p) a)

/-- Helper for Exercise 16-16.3-9: the upper-unipotent parameters add under multiplication. -/
theorem upper_unipotent_add
    (a b : ZMod p) :
    upper_unipotent (p := p) (a + b) =
      upper_unipotent (p := p) a * upper_unipotent (p := p) b := by
  -- Read both sides on the standard basis of `𝔽_p²`; the matrix entries add in the upper-right
  -- corner and nothing else changes.
  ext v i
  fin_cases i
  · simp [upper_unipotent, upper_unipotent_matrix,
      Matrix.SpecialLinearGroup.toLin'_equiv, Matrix.SpecialLinearGroup.toLin'_apply,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct, add_mul, add_comm, add_left_comm]
  · simp [upper_unipotent, upper_unipotent_matrix,
      Matrix.SpecialLinearGroup.toLin'_equiv, Matrix.SpecialLinearGroup.toLin'_apply,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

/-- Helper for Exercise 16-16.3-9: the zero upper-unipotent parameter gives the identity. -/
theorem upper_unipotent_zero :
    upper_unipotent (p := p) (0 : ZMod p) = 1 := by
  -- At parameter `0`, the upper-unipotent matrix is the identity matrix.
  ext v i
  fin_cases i
  · simp [upper_unipotent, upper_unipotent_matrix,
      Matrix.SpecialLinearGroup.toLin'_equiv, Matrix.SpecialLinearGroup.toLin'_apply,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  · simp [upper_unipotent, upper_unipotent_matrix,
      Matrix.SpecialLinearGroup.toLin'_equiv, Matrix.SpecialLinearGroup.toLin'_apply,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

/-- Helper for Exercise 16-16.3-9: the upper-unipotent family is a homomorphic copy of the
additive group of `𝔽_p`. -/
noncomputable def upper_unipotent_hom :
    Multiplicative (ZMod p) →* SpecialLinearGroup (ZMod p) (Fin 2 → ZMod p) where
  toFun a := upper_unipotent (p := p) a.toAdd
  map_one' := by
    -- The multiplicative unit corresponds to the additive zero parameter.
    simpa using upper_unipotent_zero (p := p)
  map_mul' a b := by
    -- Multiplication in `Multiplicative (ZMod p)` is addition in `ZMod p`.
    simpa using upper_unipotent_add (p := p) a.toAdd b.toAdd

/-- Helper for Exercise 16-16.3-9: the additive group of `𝔽_p` is a finite `p`-group, so the
upper-unipotent one-parameter subgroup is a `p`-group source for the fixed-vector argument. -/
theorem upper_unipotent_family_isPGroup :
    IsPGroup p (Multiplicative (ZMod p)) := by
  -- The underlying type has exactly `p` elements, hence cardinality `p^1`.
  refine IsPGroup.of_card (n := 1) ?_
  change Nat.card (ZMod p) = p ^ 1
  rw [pow_one, Nat.card_zmod]

/-- Helper for Exercise 16-16.3-9: the upper-unipotent element fixes the first standard basis
vector of `𝔽_p²`. -/
theorem upper_unipotent_apply_basisFun_zero
    (a : ZMod p) :
    upper_unipotent (p := p) a (Pi.basisFun (ZMod p) (Fin 2) 0) =
      Pi.basisFun (ZMod p) (Fin 2) 0 := by
  -- Rewrite the action through the matrix model and read off the first column.
  ext i
  fin_cases i
  · simp [upper_unipotent, upper_unipotent_matrix,
      Matrix.SpecialLinearGroup.toLin'_equiv, Matrix.SpecialLinearGroup.toLin'_apply,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  · simp [upper_unipotent, upper_unipotent_matrix,
      Matrix.SpecialLinearGroup.toLin'_equiv, Matrix.SpecialLinearGroup.toLin'_apply,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

/-- Helper for Exercise 16-16.3-9: the upper-unipotent element sends the second standard basis
vector to `a e₀ + e₁`. -/
theorem upper_unipotent_apply_basisFun_one
    (a : ZMod p) :
    upper_unipotent (p := p) a (Pi.basisFun (ZMod p) (Fin 2) 1) =
      a • Pi.basisFun (ZMod p) (Fin 2) 0 + Pi.basisFun (ZMod p) (Fin 2) 1 := by
  -- Rewrite the action through the matrix model and read off the second column.
  ext i
  fin_cases i
  · simp [upper_unipotent, upper_unipotent_matrix,
      Matrix.SpecialLinearGroup.toLin'_equiv, Matrix.SpecialLinearGroup.toLin'_apply,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  · simp [upper_unipotent, upper_unipotent_matrix,
      Matrix.SpecialLinearGroup.toLin'_equiv, Matrix.SpecialLinearGroup.toLin'_apply,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

/-- Helper for Exercise 16-16.3-9: the lower-unipotent element sends the first standard basis
vector to `e₀ + a e₁`. -/
theorem lower_unipotent_apply_basisFun_zero
    (a : ZMod p) :
    lower_unipotent (p := p) a (Pi.basisFun (ZMod p) (Fin 2) 0) =
      Pi.basisFun (ZMod p) (Fin 2) 0 + a • Pi.basisFun (ZMod p) (Fin 2) 1 := by
  -- Rewrite the action through the matrix model and read off the first column.
  ext i
  fin_cases i
  · simp [lower_unipotent, lower_unipotent_matrix,
      Matrix.SpecialLinearGroup.toLin'_equiv, Matrix.SpecialLinearGroup.toLin'_apply,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  · simp [lower_unipotent, lower_unipotent_matrix,
      Matrix.SpecialLinearGroup.toLin'_equiv, Matrix.SpecialLinearGroup.toLin'_apply,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

/-- Helper for Exercise 16-16.3-9: the lower-unipotent element fixes the second standard basis
vector of `𝔽_p²`. -/
theorem lower_unipotent_apply_basisFun_one
    (a : ZMod p) :
    lower_unipotent (p := p) a (Pi.basisFun (ZMod p) (Fin 2) 1) =
      Pi.basisFun (ZMod p) (Fin 2) 1 := by
  -- Rewrite the action through the matrix model and read off the second column.
  ext i
  fin_cases i
  · simp [lower_unipotent, lower_unipotent_matrix,
      Matrix.SpecialLinearGroup.toLin'_equiv, Matrix.SpecialLinearGroup.toLin'_apply,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  · simp [lower_unipotent, lower_unipotent_matrix,
      Matrix.SpecialLinearGroup.toLin'_equiv, Matrix.SpecialLinearGroup.toLin'_apply,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

section ScalarExtension

variable {K : Type} [Field K] [Algebra (ZMod p) K]

local notation "ρSLₖ" =>
  (Representation.scalarExtension ρSL :
    Representation K (SpecialLinearGroup (ZMod p) V) (K ⊗[ZMod p] V))

/-- Helper for Exercise 16-16.3-9: precomposing a representation with a group equivalence
preserves irreducibility. -/
theorem isIrreducible_comp_of_mulEquiv_local
    {A B : Type} [Group A] [Group B]
    {W : Type} [AddCommGroup W] [Module K W]
    (e : A ≃* B) (σ : Representation K B W)
    [Representation.IsIrreducible σ] :
    Representation.IsIrreducible (σ.comp e.toMonoidHom) := by
  classical
  -- Transport subrepresentations across the group equivalence and reuse irreducibility of `σ`.
  letI : Nontrivial (Subrepresentation (σ.comp e.toMonoidHom)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have h' : (⊥ : Subrepresentation σ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      simpa using congrArg Subrepresentation.toSubmodule h
    exact IsSimpleOrder.bot_ne_top h'
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro W hW
  let W' : Subrepresentation σ :=
    { toSubmodule := W.toSubmodule
      apply_mem_toSubmodule := by
        intro b x hx
        simpa using W.apply_mem_toSubmodule (e.symm b) hx }
  have hW'_ne_bot : W' ≠ ⊥ := by
    intro hW'
    apply hW
    apply Subrepresentation.toSubmodule_injective
    simpa [W'] using congrArg Subrepresentation.toSubmodule hW'
  have hW'_top : W' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W').resolve_left hW'_ne_bot
  apply Subrepresentation.toSubmodule_injective
  simpa [W'] using congrArg Subrepresentation.toSubmodule hW'_top

/-- Helper for Exercise 16-16.3-9: a representation equivalence survives scalar extension by
base-changing the intertwining linear equivalence. -/
theorem scalarExtension_equiv_of_equiv
    {G : Type} [Group G]
    {W W' : Type} [AddCommGroup W] [Module (ZMod p) W]
    [AddCommGroup W'] [Module (ZMod p) W']
    {ρ : Representation (ZMod p) G W} {σ : Representation (ZMod p) G W'}
    (e : Representation.Equiv ρ σ) :
    Nonempty
      ((Representation.scalarExtension (k := K) ρ).Equiv
        (Representation.scalarExtension (k := K) σ)) := by
  let eK : K ⊗[ZMod p] W ≃ₗ[K] K ⊗[ZMod p] W' :=
    e.toLinearEquiv.baseChange (ZMod p) K W W'
  refine ⟨Representation.Equiv.mk eK ?_⟩
  intro g
  -- Check the intertwining identity on pure tensors, where base change is explicit.
  apply TensorProduct.AlgebraTensorModule.ext
  intro a x
  have hgx := LinearMap.congr_fun (e.isIntertwining' g) x
  simpa [Representation.scalarExtension]
    using congrArg (fun y ↦ a ⊗ₜ[(ZMod p)] y) hgx

/-- Helper for Exercise 16-16.3-9: an equivalence of representations induces an equivalence on
their `n`th symmetric powers. -/
theorem nthSymmetricPower_equiv_of_equiv
    {G : Type} [Group G]
    {W W' : Type} [AddCommGroup W] [Module K W]
    [AddCommGroup W'] [Module K W']
    {ρ : Representation K G W} {σ : Representation K G W'}
    (e : Representation.Equiv ρ σ) (n : ℕ) :
    Nonempty ((nthSymmetricPower ρ n).Equiv (nthSymmetricPower σ n)) := by
  let f : Sym[K]^n W →ₗ[K] Sym[K]^n W' :=
    SymmetricPower.map n e.toLinearMap
  let g : Sym[K]^n W' →ₗ[K] Sym[K]^n W :=
    SymmetricPower.map n e.symm.toLinearMap
  have hleft : g.comp f = LinearMap.id := by
    -- Functoriality of `SymmetricPower.map` carries the inverse pair `e.symm ∘ e = id`.
    calc
      g.comp f = SymmetricPower.map n (e.symm.toLinearMap.comp e.toLinearMap) := by
        rw [← SymmetricPower.map_comp n e.toLinearMap e.symm.toLinearMap]
      _ = SymmetricPower.map n LinearMap.id := by
        congr
        ext x
        exact e.left_inv x
      _ = LinearMap.id := SymmetricPower.map_id n
  have hright : f.comp g = LinearMap.id := by
    -- The same argument gives the other inverse identity.
    calc
      f.comp g = SymmetricPower.map n (e.toLinearMap.comp e.symm.toLinearMap) := by
        rw [← SymmetricPower.map_comp n e.symm.toLinearMap e.toLinearMap]
      _ = SymmetricPower.map n LinearMap.id := by
        congr
        ext x
        exact e.right_inv x
      _ = LinearMap.id := SymmetricPower.map_id n
  let eSym : Sym[K]^n W ≃ₗ[K] Sym[K]^n W' :=
    LinearEquiv.ofBijective f
      ⟨by
          intro x y hxy
          calc
            x = g (f x) := by
                  symm
                  exact LinearMap.congr_fun hleft x
            _ = g (f y) := by rw [hxy]
            _ = y := LinearMap.congr_fun hleft y,
        by
          intro y
          refine ⟨g y, ?_⟩
          exact LinearMap.congr_fun hright y⟩
  refine ⟨Representation.Equiv.mk eSym ?_⟩
  intro g
  -- Functoriality turns the intertwining relation for `e` into one for symmetric powers.
  ext y
  have hy :=
    LinearMap.congr_fun (congrArg (SymmetricPower.map n) (e.isIntertwining' g)) y
  simpa [f, Representation.nthSymmetricPower, SymmetricPower.map_comp] using hy

/-- Helper for Exercise 16-16.3-9: a two-dimensional `𝔽_p`-space identifies `SL(V)` with the
standard special linear group on `𝔽_p²`. -/
noncomputable def special_linear_group_standard_equiv_of_finrank_eq_two
    (hV : Module.finrank (ZMod p) V = 2) :
    SpecialLinearGroup (ZMod p) V ≃* SpecialLinearGroup (ZMod p) (Fin 2 → ZMod p) :=
  SpecialLinearGroup.congr_linearEquiv
    (two_dimensional_linear_equiv_of_finrank_eq_two (V := V) hV)

/-- Helper for Exercise 16-16.3-9: after identifying `V` with the standard plane, the natural
`SL(V)`-action becomes the standard `SL₂`-action. -/
theorem special_linear_standard_equiv_of_finrank_eq_two
    (hV : Module.finrank (ZMod p) V = 2) :
    Nonempty
      (Representation.Equiv
        ((ρSL).comp
          (special_linear_group_standard_equiv_of_finrank_eq_two (V := V) hV).symm.toMonoidHom)
        (Representation.ofDistribMulAction (ZMod p)
          (SpecialLinearGroup (ZMod p) (Fin 2 → ZMod p)) (Fin 2 → ZMod p))) := by
  let eV := two_dimensional_linear_equiv_of_finrank_eq_two (V := V) hV
  let eG := special_linear_group_standard_equiv_of_finrank_eq_two (V := V) hV
  let ρstd :
      Representation (ZMod p) (SpecialLinearGroup (ZMod p) (Fin 2 → ZMod p))
        (Fin 2 → ZMod p) :=
    Representation.ofDistribMulAction (ZMod p)
      (SpecialLinearGroup (ZMod p) (Fin 2 → ZMod p)) (Fin 2 → ZMod p)
  refine ⟨Representation.Equiv.mk eV ?_⟩
  intro g
  -- The group transport is exactly conjugation by the chosen linear equivalence `eV`.
  ext x i
  change eV (((SpecialLinearGroup.congr_linearEquiv eV).symm g : V ≃ₗ[(ZMod p)] V) x) i =
    g (eV x) i
  rw [SpecialLinearGroup.congr_linearEquiv_symm]
  simp

/-- Helper for Exercise 16-16.3-9: transporting to the standard plane and then taking symmetric
powers produces the standard `SL₂` symmetric-power model. -/
theorem special_linear_nthSymmetricPower_standard_equiv
    (hV : Module.finrank (ZMod p) V = 2) (n : ℕ) :
    Nonempty
      (Representation.Equiv
        ((nthSymmetricPower ρSLₖ n).comp
          (special_linear_group_standard_equiv_of_finrank_eq_two (V := V) hV).symm.toMonoidHom)
        (nthSymmetricPower
          (Representation.scalarExtension
            (Representation.ofDistribMulAction (ZMod p)
              (SpecialLinearGroup (ZMod p) (Fin 2 → ZMod p)) (Fin 2 → ZMod p))) n)) := by
  rcases special_linear_standard_equiv_of_finrank_eq_two (V := V) (p := p) hV with ⟨e₀⟩
  rcases scalarExtension_equiv_of_equiv (K := K) e₀ with ⟨e₁⟩
  -- First scalar-extend the standard-model transport, then pass to symmetric powers.
  simpa using nthSymmetricPower_equiv_of_equiv (K := K) e₁ n

/-- Helper for Exercise 16-16.3-9: conjugating the scalar-extended standard `SL₂` representation
by the canonical tensor/Finsupp coordinate equivalence yields a cleaner coordinate model on
`Fin 2 →₀ K`. -/
noncomputable def standard_sl2_coordinate_model :
    Representation K (SpecialLinearGroup (ZMod p) (Fin 2 → ZMod p)) (Fin 2 →₀ K) :=
  let ρstd :
      Representation K (SpecialLinearGroup (ZMod p) (Fin 2 → ZMod p))
        (K ⊗[ZMod p] (Fin 2 → ZMod p)) :=
    Representation.scalarExtension
      (Representation.ofDistribMulAction (ZMod p)
        (SpecialLinearGroup (ZMod p) (Fin 2 → ZMod p)) (Fin 2 → ZMod p))
  let eCoord : K ⊗[ZMod p] (Fin 2 → ZMod p) ≃ₗ[K] (Fin 2 →₀ K) :=
    TensorProduct.piScalarRight (ZMod p) K K (Fin 2) ≪≫ₗ
      (Finsupp.linearEquivFunOnFinite K K (Fin 2)).symm
  (LinearEquiv.conjRingEquiv eCoord).toMonoidHom.comp ρstd

/-- Helper for Exercise 16-16.3-9: the raw scalar-extended standard model is equivariantly
identified with the coordinate model on `Fin 2 →₀ K`. -/
theorem standard_sl2_coordinate_model_equiv :
    Nonempty
      ((Representation.scalarExtension
          (Representation.ofDistribMulAction (ZMod p)
            (SpecialLinearGroup (ZMod p) (Fin 2 → ZMod p)) (Fin 2 → ZMod p))).Equiv
        (standard_sl2_coordinate_model (K := K) (p := p))) := by
  let ρstd :
      Representation K (SpecialLinearGroup (ZMod p) (Fin 2 → ZMod p))
        (K ⊗[ZMod p] (Fin 2 → ZMod p)) :=
    Representation.scalarExtension
      (Representation.ofDistribMulAction (ZMod p)
        (SpecialLinearGroup (ZMod p) (Fin 2 → ZMod p)) (Fin 2 → ZMod p))
  let eCoord : K ⊗[ZMod p] (Fin 2 → ZMod p) ≃ₗ[K] (Fin 2 →₀ K) :=
    TensorProduct.piScalarRight (ZMod p) K K (Fin 2) ≪≫ₗ
      (Finsupp.linearEquivFunOnFinite K K (Fin 2)).symm
  refine ⟨Representation.Equiv.mk eCoord ?_⟩
  intro g
  -- The coordinate action was defined by conjugating the raw scalar-extension action.
  apply TensorProduct.AlgebraTensorModule.ext
  intro a x
  have hx :
      (TensorProduct.piScalarRight (ZMod p) K K (Fin 2)).symm (fun j ↦ x j • a) =
        a ⊗ₜ[ZMod p] x := by
    apply (TensorProduct.piScalarRight (ZMod p) K K (Fin 2)).injective
    simp [TensorProduct.piScalarRightHom_tmul]
  -- Rewrite the inverse coordinate transport back to the original pure tensor
  -- during simplification.
  simp [standard_sl2_coordinate_model, eCoord, hx]

/-- Helper for Exercise 16-16.3-9: scalar extension acts on a pure tensor by keeping the scalar
in `K` and applying the original representation to the module factor. -/
private theorem scalarExtension_apply_tmul_local
    {G : Type} [Group G]
    {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    (ρ : Representation (ZMod p) G W) (g : G) (a : K) (x : W) :
    (Representation.scalarExtension (k := K) ρ) g (a ⊗ₜ[(ZMod p)] x) =
      a ⊗ₜ[(ZMod p)] (ρ g x) := by
  -- `Representation.scalarExtension` is defined by `Module.End.baseChangeHom`, so pure tensors
  -- are computed by the base-change formula.
  change ((Module.End.baseChangeHom (ZMod p) K W) (ρ g)) (a ⊗ₜ[(ZMod p)] x) =
    a ⊗ₜ[(ZMod p)] (ρ g x)
  exact LinearMap.baseChange_tmul (f := ρ g) (A := K) a x

/-- Helper for Exercise 16-16.3-9: after applying `piScalarRight`, the first basis vector of
`𝔽_p²` becomes the first basis function over `K`. -/
private theorem coordinate_basis_function_zero_over_K :
    (fun j : Fin 2 ↦ (Pi.basisFun (ZMod p) (Fin 2) 0) j • (1 : K)) =
      Pi.basisFun K (Fin 2) 0 := by
  -- On the two coordinates, this is exactly the statement that `1·1 = 1` and `0·1 = 0`.
  funext j
  fin_cases j <;> simp [Pi.basisFun]

/-- Helper for Exercise 16-16.3-9: after applying `piScalarRight`, the second basis vector of
`𝔽_p²` becomes the second basis function over `K`. -/
private theorem coordinate_basis_function_one_over_K :
    (fun j : Fin 2 ↦ (Pi.basisFun (ZMod p) (Fin 2) 1) j • (1 : K)) =
      Pi.basisFun K (Fin 2) 1 := by
  -- Again, check the two coordinates explicitly.
  funext j
  fin_cases j <;> simp [Pi.basisFun]

/-- Helper for Exercise 16-16.3-9: the inverse coordinate equivalence sends the singleton basis
vector back to the corresponding pure tensor in `K ⊗[𝔽_p] 𝔽_p²`. -/
private theorem standard_sl2_coordinate_model_equiv_symm_single
    (j : Fin 2) :
    ((TensorProduct.piScalarRight (ZMod p) K K (Fin 2) ≪≫ₗ
        (Finsupp.linearEquivFunOnFinite K K (Fin 2)).symm).symm)
      (Finsupp.single j (1 : K)) =
      (1 : K) ⊗ₜ[(ZMod p)] Pi.basisFun (ZMod p) (Fin 2) j := by
  -- Route correction: normalize the conjugating equivalence once, so later action formulas can
  -- stay on pure tensors instead of repeatedly unfolding the transport.
  simp [LinearEquiv.trans_apply]

/-- Helper for Exercise 16-16.3-9: transporting the upper and lower unipotent actions from the
standard plane to the `Fin 2 →₀ K` coordinate model gives the expected formulas on the singleton
basis vectors. -/
theorem standard_sl2_coordinate_model_upper_lower_on_singletons
    (a : ZMod p) :
    (standard_sl2_coordinate_model (K := K) (p := p))
        (upper_unipotent (p := p) a) (Finsupp.single 0 (1 : K)) =
        Finsupp.single 0 (1 : K) ∧
      (standard_sl2_coordinate_model (K := K) (p := p))
          (upper_unipotent (p := p) a) (Finsupp.single 1 (1 : K)) =
          algebraMap (ZMod p) K a • Finsupp.single 0 (1 : K) + Finsupp.single 1 (1 : K) ∧
        (standard_sl2_coordinate_model (K := K) (p := p))
            (lower_unipotent (p := p) a) (Finsupp.single 0 (1 : K)) =
            algebraMap (ZMod p) K a • Finsupp.single 1 (1 : K) + Finsupp.single 0 (1 : K) ∧
          (standard_sl2_coordinate_model (K := K) (p := p))
              (lower_unipotent (p := p) a) (Finsupp.single 1 (1 : K)) =
              Finsupp.single 1 (1 : K) := by
  let ρstd :
      Representation K (SpecialLinearGroup (ZMod p) (Fin 2 → ZMod p))
        (K ⊗[(ZMod p)] (Fin 2 → ZMod p)) :=
    Representation.scalarExtension
      (Representation.ofDistribMulAction (ZMod p)
        (SpecialLinearGroup (ZMod p) (Fin 2 → ZMod p)) (Fin 2 → ZMod p))
  let eCoord : K ⊗[(ZMod p)] (Fin 2 → ZMod p) ≃ₗ[K] (Fin 2 →₀ K) :=
    TensorProduct.piScalarRight (ZMod p) K K (Fin 2) ≪≫ₗ
      (Finsupp.linearEquivFunOnFinite K K (Fin 2)).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The first singleton is fixed by the upper-unipotent action after transport.
    change eCoord (ρstd (upper_unipotent (p := p) a) (eCoord.symm (Finsupp.single 0 (1 : K)))) =
      Finsupp.single 0 (1 : K)
    rw [standard_sl2_coordinate_model_equiv_symm_single (K := K) (p := p) 0]
    rw [scalarExtension_apply_tmul_local (K := K)
      (ρ := Representation.ofDistribMulAction (ZMod p)
        (SpecialLinearGroup (ZMod p) (Fin 2 → ZMod p)) (Fin 2 → ZMod p))]
    have hbasis :
        ((Representation.ofDistribMulAction (ZMod p)
            (SpecialLinearGroup (ZMod p) (Fin 2 → ZMod p)) (Fin 2 → ZMod p))
          (upper_unipotent (p := p) a))
          (Pi.basisFun (ZMod p) (Fin 2) 0) =
        Pi.basisFun (ZMod p) (Fin 2) 0 := by
      -- On the source plane, `upper_unipotent` fixes the first basis vector.
      simpa using upper_unipotent_apply_basisFun_zero (p := p) a
    rw [hbasis]
    change (Finsupp.linearEquivFunOnFinite K K (Fin 2)).symm
        ((TensorProduct.piScalarRight (ZMod p) K K (Fin 2))
          (1 ⊗ₜ[(ZMod p)] Pi.basisFun (ZMod p) (Fin 2) 0)) =
      Finsupp.single 0 (1 : K)
    rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      coordinate_basis_function_zero_over_K]
    convert
      (Finsupp.linearEquivFunOnFinite_symm_single
        (R := K) (M := K) (α := Fin 2) 0 (1 : K)) using 1
    simp [Pi.basisFun]
  · -- The second singleton picks up the expected upper-triangular shear term.
    change eCoord (ρstd (upper_unipotent (p := p) a) (eCoord.symm (Finsupp.single 1 (1 : K)))) =
      algebraMap (ZMod p) K a • Finsupp.single 0 (1 : K) + Finsupp.single 1 (1 : K)
    rw [standard_sl2_coordinate_model_equiv_symm_single (K := K) (p := p) 1]
    rw [scalarExtension_apply_tmul_local (K := K)
      (ρ := Representation.ofDistribMulAction (ZMod p)
        (SpecialLinearGroup (ZMod p) (Fin 2 → ZMod p)) (Fin 2 → ZMod p))]
    have hbasis :
        ((Representation.ofDistribMulAction (ZMod p)
            (SpecialLinearGroup (ZMod p) (Fin 2 → ZMod p)) (Fin 2 → ZMod p))
          (upper_unipotent (p := p) a))
          (Pi.basisFun (ZMod p) (Fin 2) 1) =
        a • Pi.basisFun (ZMod p) (Fin 2) 0 + Pi.basisFun (ZMod p) (Fin 2) 1 := by
      -- On the source plane, `upper_unipotent` sends `e₁` to `a e₀ + e₁`.
      simpa using upper_unipotent_apply_basisFun_one (p := p) a
    rw [hbasis]
    change (Finsupp.linearEquivFunOnFinite K K (Fin 2)).symm
        ((TensorProduct.piScalarRight (ZMod p) K K (Fin 2))
          (1 ⊗ₜ[(ZMod p)]
            (a • Pi.basisFun (ZMod p) (Fin 2) 0 + Pi.basisFun (ZMod p) (Fin 2) 1))) =
      algebraMap (ZMod p) K a • Finsupp.single 0 (1 : K) + Finsupp.single 1 (1 : K)
    rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    have hfun :
        (fun j : Fin 2 ↦
          (a • Pi.basisFun (ZMod p) (Fin 2) 0 + Pi.basisFun (ZMod p) (Fin 2) 1) j • (1 : K)) =
          algebraMap (ZMod p) K a • Pi.basisFun K (Fin 2) 0 + Pi.basisFun K (Fin 2) 1 := by
      -- Evaluate the transported shear formula on the two coordinates.
      funext j
      fin_cases j <;> simp [Pi.basisFun]
    rw [hfun]
    ext j
    fin_cases j <;> simp [Finsupp.linearEquivFunOnFinite_symm_single, Pi.basisFun]
  · -- The lower-unipotent action shears the first singleton in the complementary direction.
    change eCoord (ρstd (lower_unipotent (p := p) a) (eCoord.symm (Finsupp.single 0 (1 : K)))) =
      algebraMap (ZMod p) K a • Finsupp.single 1 (1 : K) + Finsupp.single 0 (1 : K)
    rw [standard_sl2_coordinate_model_equiv_symm_single (K := K) (p := p) 0]
    rw [scalarExtension_apply_tmul_local (K := K)
      (ρ := Representation.ofDistribMulAction (ZMod p)
        (SpecialLinearGroup (ZMod p) (Fin 2 → ZMod p)) (Fin 2 → ZMod p))]
    have hbasis :
        ((Representation.ofDistribMulAction (ZMod p)
            (SpecialLinearGroup (ZMod p) (Fin 2 → ZMod p)) (Fin 2 → ZMod p))
          (lower_unipotent (p := p) a))
          (Pi.basisFun (ZMod p) (Fin 2) 0) =
        Pi.basisFun (ZMod p) (Fin 2) 0 + a • Pi.basisFun (ZMod p) (Fin 2) 1 := by
      -- On the source plane, `lower_unipotent` sends `e₀` to `e₀ + a e₁`.
      simpa [add_comm] using lower_unipotent_apply_basisFun_zero (p := p) a
    rw [hbasis]
    change (Finsupp.linearEquivFunOnFinite K K (Fin 2)).symm
        ((TensorProduct.piScalarRight (ZMod p) K K (Fin 2))
          (1 ⊗ₜ[(ZMod p)]
            (Pi.basisFun (ZMod p) (Fin 2) 0 + a • Pi.basisFun (ZMod p) (Fin 2) 1))) =
      algebraMap (ZMod p) K a • Finsupp.single 1 (1 : K) + Finsupp.single 0 (1 : K)
    rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    have hfun :
        (fun j : Fin 2 ↦
          (Pi.basisFun (ZMod p) (Fin 2) 0 + a • Pi.basisFun (ZMod p) (Fin 2) 1) j • (1 : K)) =
          Pi.basisFun K (Fin 2) 0 + algebraMap (ZMod p) K a • Pi.basisFun K (Fin 2) 1 := by
      -- This is the same coordinate computation, but for the lower-triangular shear.
      funext j
      fin_cases j <;> simp [Pi.basisFun, add_comm]
    rw [hfun]
    ext j
    fin_cases j <;> simp [Finsupp.linearEquivFunOnFinite_symm_single, Pi.basisFun, add_comm]
  · -- The second singleton is fixed by the lower-unipotent action after transport.
    change eCoord (ρstd (lower_unipotent (p := p) a) (eCoord.symm (Finsupp.single 1 (1 : K)))) =
      Finsupp.single 1 (1 : K)
    rw [standard_sl2_coordinate_model_equiv_symm_single (K := K) (p := p) 1]
    rw [scalarExtension_apply_tmul_local (K := K)
      (ρ := Representation.ofDistribMulAction (ZMod p)
        (SpecialLinearGroup (ZMod p) (Fin 2 → ZMod p)) (Fin 2 → ZMod p))]
    have hbasis :
        ((Representation.ofDistribMulAction (ZMod p)
            (SpecialLinearGroup (ZMod p) (Fin 2 → ZMod p)) (Fin 2 → ZMod p))
          (lower_unipotent (p := p) a))
          (Pi.basisFun (ZMod p) (Fin 2) 1) =
        Pi.basisFun (ZMod p) (Fin 2) 1 := by
      -- On the source plane, `lower_unipotent` fixes the second basis vector.
      simpa using lower_unipotent_apply_basisFun_one (p := p) a
    rw [hbasis]
    change (Finsupp.linearEquivFunOnFinite K K (Fin 2)).symm
        ((TensorProduct.piScalarRight (ZMod p) K K (Fin 2))
          (1 ⊗ₜ[(ZMod p)] Pi.basisFun (ZMod p) (Fin 2) 1)) =
      Finsupp.single 1 (1 : K)
    rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      coordinate_basis_function_one_over_K]
    convert
      (Finsupp.linearEquivFunOnFinite_symm_single
        (R := K) (M := K) (α := Fin 2) 1 (1 : K)) using 1
    simp [Pi.basisFun]

/-- Helper for Exercise 16-16.3-9: functoriality of symmetric powers carries a pure symmetric
tensor generator to the generator built from the images of the factors. -/
theorem symmetricPower_map_tprod
    {W : Type} [AddCommGroup W] [Module K W]
    {W' : Type} [AddCommGroup W'] [Module K W']
    (n : ℕ) (f : W →ₗ[K] W') (x : Fin n → W) :
    SymmetricPower.map n f (SymmetricPower.tprod K x) =
      SymmetricPower.tprod K (fun j ↦ f (x j)) := by
  -- Unfold the quotient-level definitions and use the tensor-power map on a pure tensor.
  change
    (AddCon.mk' (addConGen (SymmetricPower.Rel K (Fin n) W')))
        (PiTensorProduct.map (fun _ : Fin n ↦ f) (PiTensorProduct.tprod K x)) =
      (SymmetricPower.mk K (Fin n) W') (PiTensorProduct.tprod K (fun j ↦ f (x j)))
  exact congrArg
    (AddCon.mk' (addConGen (SymmetricPower.Rel K (Fin n) W')))
    (PiTensorProduct.map_tprod (f := fun _ : Fin n ↦ f) x)

/-- Helper for Exercise 16-16.3-9: when `i < p`, the binomial coefficients `choose i r` stay
nonzero after passing from `ℕ` to any field over `𝔽_p`. This is the arithmetic side condition
needed for LinearRepresentations_Serre_1977's binary-form highest-weight argument. -/
theorem nat_choose_cast_ne_zero_of_lt_prime
    {i r : ℕ} (hr : r ≤ i) (hi : i < p) :
    (Nat.choose i r : K) ≠ 0 := by
  have hp : Nat.Prime p := Fact.out
  have hchoose_ne_zero : Nat.choose i r ≠ 0 := Nat.choose_ne_zero hr
  have hchoose_zmod_ne_zero : ((Nat.choose i r : ℕ) : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv : p ∣ Nat.choose i r := by
      exact (ZMod.natCast_eq_zero_iff (Nat.choose i r) p).mp hzero
    have hfactor_pos : 0 < (Nat.choose i r).factorization p :=
      hp.factorization_pos_of_dvd hchoose_ne_zero hdiv
    exact hfactor_pos.ne' <|
      Nat.factorization_choose_eq_zero_of_lt (n := i) (k := r) (p := p) hi
  intro hzero
  apply hchoose_zmod_ne_zero
  apply (FaithfulSMul.algebraMap_injective (ZMod p) K)
  simpa using hzero

/-- Helper for Exercise 16-16.3-9: natural numbers bounded by `i < p` remain distinct after
casting to `K`. This is the distinct-parameter input for the Vandermonde step in the binary-form
model. -/
theorem nat_cast_injective_of_lt_prime
    {a b i : ℕ} (ha : a ≤ i) (hb : b ≤ i) (hi : i < p)
    (hab : (a : K) = (b : K)) :
    a = b := by
  have ha' : a < p := lt_of_le_of_lt ha hi
  have hb' : b < p := lt_of_le_of_lt hb hi
  have hzmod : (a : ZMod p) = (b : ZMod p) := by
    apply (FaithfulSMul.algebraMap_injective (ZMod p) K)
    simpa using hab
  have hval := congrArg ZMod.val hzmod
  simpa [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] using hval

/-- Helper for Exercise 16-16.3-9: the degree-`i` binary-form monomial
`X₀^(i-r) X₁^r` lies in the homogeneous binary-form space of degree `i`. -/
theorem binary_form_monomial_mem_homogeneousSubmodule
    {i r : ℕ} (hr : r ≤ i) :
    MvPolynomial.monomial
        (Finsupp.single (0 : Fin 2) (i - r) + Finsupp.single (1 : Fin 2) r) (1 : K) ∈
      MvPolynomial.homogeneousSubmodule (Fin 2) K i := by
  -- The exponent vector has total degree `(i - r) + r = i`, so the monomial is homogeneous of
  -- the required degree.
  rw [MvPolynomial.mem_homogeneousSubmodule]
  refine MvPolynomial.isHomogeneous_monomial (1 : K) ?_
  rw [Finsupp.degree_eq_sum]
  simpa [add_comm] using Nat.sub_add_cancel hr

/-- Helper for Exercise 16-16.3-9: LinearRepresentations_Serre_1977's highest binary form `X₀^i` is a degree-`i`
homogeneous polynomial. -/
theorem highest_binary_form_mem_homogeneousSubmodule (i : ℕ) :
    MvPolynomial.monomial (Finsupp.single (0 : Fin 2) i) (1 : K) ∈
      MvPolynomial.homogeneousSubmodule (Fin 2) K i := by
  -- This is the `r = 0` instance of the general binary-form monomial degree calculation.
  simpa using
    binary_form_monomial_mem_homogeneousSubmodule (K := K) (i := i) (r := 0) (Nat.zero_le i)

/-- Helper for Exercise 16-16.3-9: the highest-weight vector in LinearRepresentations_Serre_1977's binary-form model is the
degree-`i` monomial `X₀^i`. -/
def highest_binary_form (i : ℕ) : MvPolynomial.homogeneousSubmodule (Fin 2) K i :=
  ⟨MvPolynomial.monomial (Finsupp.single (0 : Fin 2) i) (1 : K),
    highest_binary_form_mem_homogeneousSubmodule (K := K) i⟩

/-- Helper for Exercise 16-16.3-9: the exponent vector of the binary-form monomial
`X₀^(i-r) X₁^r`. -/
def binary_form_exponent_vector (i r : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single (0 : Fin 2) (i - r) + Finsupp.single (1 : Fin 2) r

/-- Helper for Exercise 16-16.3-9: the standard monomial basis vector
`X₀^(i-r) X₁^r` in the degree-`i` binary-form space. -/
def binary_form_basisVec
    (i r : ℕ) (hr : r ≤ i) :
    MvPolynomial.homogeneousSubmodule (Fin 2) K i :=
  ⟨MvPolynomial.monomial (binary_form_exponent_vector i r) (1 : K), by
    -- The named basis vector is homogeneous because its exponent vector has total degree `i`.
    simpa [binary_form_exponent_vector] using
      binary_form_monomial_mem_homogeneousSubmodule (K := K) (i := i) (r := r) hr⟩

/-- Helper for Exercise 16-16.3-9: coercing the named binary-form basis vector forgets only the
homogeneous-submodule wrapper. -/
theorem binary_form_basisVec_coe
    {i r : ℕ} (hr : r ≤ i) :
    ((binary_form_basisVec (K := K) i r hr :
        MvPolynomial.homogeneousSubmodule (Fin 2) K i) :
      MvPolynomial (Fin 2) K) =
      MvPolynomial.monomial (binary_form_exponent_vector i r) (1 : K) := by
  -- This is definitional after introducing the named subtype wrapper.
  rfl

/-- Helper for Exercise 16-16.3-9: extend the binary-form monomial basis by zero outside the
allowable index range `0, …, i`, so natural-number sums can use the basis without dependent
proof arguments. -/
def binary_form_basisVec_or_zero
    (i r : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin 2) K i :=
  if hr : r ≤ i then binary_form_basisVec (K := K) i r hr else 0

/-- Helper for Exercise 16-16.3-9: on the allowed range `r ≤ i`, the zero-extended basis agrees
with the named binary-form monomial basis vector. -/
theorem binary_form_basisVec_or_zero_eq
    {i r : ℕ} (hr : r ≤ i) :
    binary_form_basisVec_or_zero (K := K) i r =
      binary_form_basisVec (K := K) i r hr := by
  -- On the valid degree range, the extension by zero takes its nonzero branch.
  simp [binary_form_basisVec_or_zero, hr]

/-- Helper for Exercise 16-16.3-9: taking the coefficient of a named binary-form basis vector at a
binary exponent simply detects whether the `X₁`-degrees agree. -/
theorem coeff_binary_form_basisVec
    {i r s : ℕ} (hr : r ≤ i) :
    MvPolynomial.coeff (binary_form_exponent_vector i s)
        (((binary_form_basisVec (K := K) i r hr :
            MvPolynomial.homogeneousSubmodule (Fin 2) K i) :
          MvPolynomial (Fin 2) K)) =
      if s = r then 1 else 0 := by
  -- After forgetting the subtype wrapper, this is the monomial coefficient test.
  rw [binary_form_basisVec_coe hr, MvPolynomial.coeff_monomial]
  by_cases hsr : s = r
  · subst hsr
    simp
  · have hexp :
        binary_form_exponent_vector i s ≠ binary_form_exponent_vector i r := by
      intro hEq
      apply hsr
      simpa [binary_form_exponent_vector] using congrArg (fun d : Fin 2 →₀ ℕ ↦ d 1) hEq
    have hexp' :
        binary_form_exponent_vector i r ≠ binary_form_exponent_vector i s := fun hEq ↦
          hexp hEq.symm
    simp [hsr, hexp']

/-- Helper for Exercise 16-16.3-9: LinearRepresentations_Serre_1977's highest binary form is the first basis vector
`X₀^i = X₀^(i-0) X₁^0`. -/
theorem highest_binary_form_eq_binary_form_basisVec_zero
    (i : ℕ) :
    highest_binary_form (K := K) i =
      binary_form_basisVec (K := K) i 0 (Nat.zero_le i) := by
  -- Both subtype elements have the same underlying monomial `X₀^i`.
  apply Subtype.ext
  simp [highest_binary_form, binary_form_basisVec, binary_form_exponent_vector]

/-- Helper for Exercise 16-16.3-9: the binary-form exponent vector has total degree `i`. -/
theorem binary_form_exponent_degree
    {i r : ℕ} (hr : r ≤ i) :
    (binary_form_exponent_vector i r).degree = i := by
  -- The two coordinates contribute `(i - r)` and `r`, so the total degree is `i`.
  rw [binary_form_exponent_vector, Finsupp.degree_eq_sum, Fin.sum_univ_two]
  simp [Nat.sub_add_cancel hr, add_comm]

/-- Helper for Exercise 16-16.3-9: in a degree-`i` binary exponent vector, the `X₁`-exponent is
bounded by `i`. -/
theorem binary_form_right_le_of_degree
    {i : ℕ} {d : Fin 2 →₀ ℕ} (hd : d.degree = i) :
    d 1 ≤ i := by
  -- Rewrite the degree constraint as the two-coordinate sum `d 0 + d 1 = i`.
  have hsum : d 0 + d 1 = i := by
    simpa [Finsupp.degree_eq_sum, Fin.sum_univ_two, add_comm, add_left_comm, add_assoc] using hd
  have hle : d 1 ≤ d 0 + d 1 := Nat.le_add_left (d 1) (d 0)
  simpa [add_comm, hsum] using hle

/-- Helper for Exercise 16-16.3-9: every degree-`i` exponent vector in two variables is uniquely
determined by its `X₁`-exponent. -/
theorem degree_eq_binary_form_exponent
    {i : ℕ} {d : Fin 2 →₀ ℕ} (hd : d.degree = i) :
    d = binary_form_exponent_vector i (d 1) := by
  -- On `Fin 2`, the degree equation recovers the `X₀`-exponent as `i - d 1`.
  ext j
  fin_cases j
  · have hsum : d 0 + d 1 = i := by
      simpa [Finsupp.degree_eq_sum, Fin.sum_univ_two, add_comm, add_left_comm, add_assoc] using hd
    rw [binary_form_exponent_vector]
    simp [Nat.eq_sub_of_add_eq hsum]
  · rw [binary_form_exponent_vector]
    simp

/-- Helper for Exercise 16-16.3-9: the degree-`i` exponent vectors for binary forms are indexed
by the possible `X₁`-exponents `0, …, i`. -/
noncomputable def binary_form_degree_support_equiv (i : ℕ) :
    {d : Fin 2 →₀ ℕ // d.degree = i} ≃ Fin (i + 1) where
  toFun d :=
    ⟨d.1 1, Nat.lt_succ_of_le (binary_form_right_le_of_degree (i := i) d.2)⟩
  invFun r :=
    ⟨binary_form_exponent_vector i r,
      binary_form_exponent_degree (Nat.le_of_lt_succ r.2)⟩
  left_inv d := by
    -- The degree equation shows the inverse recovers the original exponent vector.
    apply Subtype.ext
    simpa using (degree_eq_binary_form_exponent (i := i) d.2).symm
  right_inv r := by
    -- The inverse was chosen so that the `X₁`-exponent is exactly `r`.
    apply Fin.ext
    simp [binary_form_exponent_vector]

/-- Helper for Exercise 16-16.3-9: the binary-form homogeneous piece of degree `i` has
dimension `i + 1`. -/
theorem finrank_binary_form_homogeneousSubmodule
    (i : ℕ) :
    Module.finrank K (MvPolynomial.homogeneousSubmodule (Fin 2) K i) = i + 1 := by
  classical
  let s : Set (Fin 2 →₀ ℕ) := {d | d.degree = i}
  letI : Fintype s := Fintype.ofEquiv (Fin (i + 1)) (binary_form_degree_support_equiv (i := i)).symm
  letI : FiniteDimensional K (MvPolynomial.restrictSupport K s) :=
    (MvPolynomial.basisRestrictSupport K s).finiteDimensional_of_finite
  have hs :
      MvPolynomial.homogeneousSubmodule (Fin 2) K i = MvPolynomial.restrictSupport K s := by
    -- Replace the homogeneous piece by the finite-support model indexed by degree-`i` exponents.
    simpa [s, MvPolynomial.restrictSupport] using
      (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (σ := Fin 2) (R := K) i)
  letI : FiniteDimensional K (MvPolynomial.homogeneousSubmodule (Fin 2) K i) := by
    exact hs.symm ▸ (inferInstance : FiniteDimensional K (MvPolynomial.restrictSupport K s))
  calc
    Module.finrank K (MvPolynomial.homogeneousSubmodule (Fin 2) K i) =
        Module.finrank K (MvPolynomial.restrictSupport K s) := by
          rw [hs]
    _ = Fintype.card s := by
          simpa using (Module.finrank_eq_card_basis (MvPolynomial.basisRestrictSupport K s))
    _ = Fintype.card (Fin (i + 1)) := by
          exact Fintype.card_congr (binary_form_degree_support_equiv (i := i))
    _ = i + 1 := Fintype.card_fin (i + 1)

/-- Helper for Exercise 16-16.3-9: in degree `0`, the symmetric-power permutation relation adds no
new identifications because there are no tensor factors to permute. -/
private theorem symmetric_zero_rel_eq_local
    {x y : PiTensorProduct K (fun _ : Fin 0 ↦ Fin 2 →₀ K)}
    (h : addConGen (SymmetricPower.Rel K (Fin 0) (Fin 2 →₀ K)) x y) :
    x = y := by
  induction h with
  | of x y h =>
      cases h with
      | perm e f =>
          have hfun : f = fun i : Fin 0 ↦ f (e i) := by
            funext i
            exact Fin.elim0 i
          exact congrArg (PiTensorProduct.tprod K) hfun
  | refl =>
      rfl
  | symm _ ih =>
      exact ih.symm
  | trans _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂
  | add _ _ ih₁ ih₂ =>
      exact congrArg₂ (· + ·) ih₁ ih₂

/-- Helper for Exercise 16-16.3-9: the `0`th symmetric power is one-dimensional. -/
theorem finrank_symmetricPower_zero_local :
    Module.finrank K (SymmetricPower K (Fin 0) (Fin 2 →₀ K)) = 1 := by
  let eTensor : PiTensorProduct K (fun _ : Fin 0 ↦ Fin 2 →₀ K) ≃ₗ[K] K :=
    PiTensorProduct.isEmptyEquiv (R := K) (ι := Fin 0) (s := fun _ : Fin 0 ↦ Fin 2 →₀ K)
  have hmk_injective : Function.Injective (SymmetricPower.mk K (Fin 0) (Fin 2 →₀ K)) := by
    intro x y hxy
    change
      ((x : (addConGen (SymmetricPower.Rel K (Fin 0) (Fin 2 →₀ K))).Quotient) =
        (y : (addConGen (SymmetricPower.Rel K (Fin 0) (Fin 2 →₀ K))).Quotient)) at hxy
    -- In degree `0`, the permutation relation is trivial because there are no tensor factors.
    refine symmetric_zero_rel_eq_local
      (((addConGen (SymmetricPower.Rel K (Fin 0) (Fin 2 →₀ K))).eq).1 hxy)
  let eSymm : PiTensorProduct K (fun _ : Fin 0 ↦ Fin 2 →₀ K) ≃ₗ[K]
      SymmetricPower K (Fin 0) (Fin 2 →₀ K) :=
    LinearEquiv.ofBijective (SymmetricPower.mk K (Fin 0) (Fin 2 →₀ K))
      ⟨hmk_injective, by
          -- The quotient map onto the symmetric power is always surjective.
          simpa [LinearMap.range_eq_top] using
            (SymmetricPower.range_mk (R := K) (ι := Fin 0) (M := Fin 2 →₀ K))⟩
  -- Identify `Sym^0` with the empty tensor power and then with the scalar owner `K`.
  simpa using (eSymm.symm.trans eTensor).finrank_eq

/-- Helper for Exercise 16-16.3-9: the standard plane has symmetric-power dimension `i + 1` in
degree `i`. -/
theorem finrank_standard_coordinate_symmetricPower
    (i : ℕ) :
    Module.finrank K (Sym[K]^i (Fin 2 →₀ K)) = i + 1 := by
  have hfinrank_plane : Module.finrank K (Fin 2 →₀ K) = 2 := by
    calc
      Module.finrank K (Fin 2 →₀ K) = Module.finrank K (Fin 2 → K) := by
        exact (Finsupp.linearEquivFunOnFinite K K (Fin 2)).finrank_eq
      _ = 2 := by
        simp
  cases i with
  | zero =>
      -- Degree `0` symmetric power is the one-dimensional trivial line.
      simpa using finrank_symmetricPower_zero_local (K := K)
  | succ n =>
      -- Positive degrees are counted by the multichoose formula specialized to a plane.
      calc
        Module.finrank K (Sym[K]^(n + 1) (Fin 2 →₀ K)) =
            (Module.finrank K (Fin 2 →₀ K)).multichoose (n + 1) := by
              simpa using
                (finrank_symmetricPower_eq_multichoose (k := K) (V := Fin 2 →₀ K) n)
        _ = (2 : ℕ).multichoose (n + 1) := by rw [hfinrank_plane]
        _ = n + 2 := by simp [Nat.multichoose_two]

/-- Helper for Exercise 16-16.3-9: the pure tensor giving `X₀^(i-r) X₁^r` is represented by
`i-r` copies of `0` followed by `r` copies of `1`. -/
def binary_form_index_tuple
    (i r : ℕ) (hr : r ≤ i) :
    Fin i → Fin 2 :=
  fun j ↦
    Fin.append
      (fun _ : Fin (i - r) ↦ (0 : Fin 2))
      (fun _ : Fin r ↦ (1 : Fin 2))
      (j.cast (Nat.sub_add_cancel hr).symm)

/-- Helper for Exercise 16-16.3-9: counting the entries of the binary-form index tuple recovers
the exponent vector of `X₀^(i-r) X₁^r`. -/
theorem sum_single_binary_form_index_tuple
    {i r : ℕ} (hr : r ≤ i) :
    (∑ j : Fin i, Finsupp.single (binary_form_index_tuple i r hr j) (1 : ℕ)) =
      binary_form_exponent_vector i r := by
  -- After rewriting the tuple through `Fin.append`, the two blocks contribute the two exponents.
  ext j
  fin_cases j
  · have hsplit : i = (i - r) + r := (Nat.sub_add_cancel hr).symm
    let g : Fin ((i - r) + r) → Fin 2 :=
      Fin.append
        (fun _ : Fin (i - r) ↦ (0 : Fin 2))
        (fun _ : Fin r ↦ (1 : Fin 2))
    have hrewrite :
        ∑ j : Fin i, Finsupp.single (binary_form_index_tuple i r hr j) (1 : ℕ) =
          ∑ j : Fin ((i - r) + r), Finsupp.single (g j) (1 : ℕ) := by
      change
        ∑ j : Fin i, Finsupp.single (g (j.cast hsplit)) (1 : ℕ) =
          ∑ j : Fin ((i - r) + r), Finsupp.single (g j) (1 : ℕ)
      exact
        Fin.sum_congr'
          (f := fun j : Fin ((i - r) + r) ↦ Finsupp.single (g j) (1 : ℕ))
          hsplit
    calc
      (∑ j : Fin i, Finsupp.single (binary_form_index_tuple i r hr j) (1 : ℕ)) 0 =
          (∑ j : Fin ((i - r) + r), Finsupp.single (g j) (1 : ℕ)) 0 := by
            exact congrArg (fun z ↦ z 0) hrewrite
      _ = (∑ j : Fin (i - r), Finsupp.single (0 : Fin 2) (1 : ℕ) 0) +
            ∑ j : Fin r, Finsupp.single (1 : Fin 2) (1 : ℕ) 0 := by
              rw [Fin.sum_univ_add]
              simp [g, Fin.append_left, Fin.append_right]
      _ = (i - r) := by simp
      _ = (binary_form_exponent_vector i r) 0 := by
            simp [binary_form_exponent_vector]
  · have hsplit : i = (i - r) + r := (Nat.sub_add_cancel hr).symm
    let g : Fin ((i - r) + r) → Fin 2 :=
      Fin.append
        (fun _ : Fin (i - r) ↦ (0 : Fin 2))
        (fun _ : Fin r ↦ (1 : Fin 2))
    have hrewrite :
        ∑ j : Fin i, Finsupp.single (binary_form_index_tuple i r hr j) (1 : ℕ) =
          ∑ j : Fin ((i - r) + r), Finsupp.single (g j) (1 : ℕ) := by
      change
        ∑ j : Fin i, Finsupp.single (g (j.cast hsplit)) (1 : ℕ) =
          ∑ j : Fin ((i - r) + r), Finsupp.single (g j) (1 : ℕ)
      exact
        Fin.sum_congr'
          (f := fun j : Fin ((i - r) + r) ↦ Finsupp.single (g j) (1 : ℕ))
          hsplit
    calc
      (∑ j : Fin i, Finsupp.single (binary_form_index_tuple i r hr j) (1 : ℕ)) 1 =
          (∑ j : Fin ((i - r) + r), Finsupp.single (g j) (1 : ℕ)) 1 := by
            exact congrArg (fun z ↦ z 1) hrewrite
      _ = (∑ j : Fin (i - r), Finsupp.single (0 : Fin 2) (1 : ℕ) 1) +
            ∑ j : Fin r, Finsupp.single (1 : Fin 2) (1 : ℕ) 1 := by
              rw [Fin.sum_univ_add]
              simp [g, Fin.append_left, Fin.append_right]
      _ = r := by simp
      _ = (binary_form_exponent_vector i r) 1 := by
            simp [binary_form_exponent_vector]

/-- Helper for Exercise 16-16.3-9: each binary monomial has a concrete preimage under the
coordinate symmetric-power map. -/
theorem coordinate_to_binary_form_monomial_preimage
    (i : ℕ) (d : Fin 2 →₀ ℕ) (hd : d.degree = i) :
    ∃ x,
      symmetricPower_coordinate_to_homogeneousSubmodule (K := K) (ι := Fin 2) i x =
        ⟨MvPolynomial.monomial d (1 : K), by
          rw [MvPolynomial.mem_homogeneousSubmodule]
          exact MvPolynomial.isHomogeneous_monomial (1 : K) hd⟩ := by
  let r : ℕ := d 1
  let hr : r ≤ i := binary_form_right_le_of_degree (i := i) hd
  refine ⟨SymmetricPower.tprod K
      (fun j ↦ Finsupp.single (binary_form_index_tuple i r hr j) (1 : K)), ?_⟩
  -- The explicit generator formula lands on the monomial with exponent vector `d`.
  have himage :=
    symmetricPower_coordinate_to_homogeneousSubmodule_apply_single_tprod
      (K := K) (ι := Fin 2) i (binary_form_index_tuple i r hr)
  apply Subtype.ext
  have hval := congrArg Subtype.val himage
  calc
    ↑((symmetricPower_coordinate_to_homogeneousSubmodule (K := K) (ι := Fin 2) i)
          (SymmetricPower.tprod K
            (fun j ↦ Finsupp.single (binary_form_index_tuple i r hr j) (1 : K)))) =
        MvPolynomial.monomial
          (∑ j : Fin i, Finsupp.single (binary_form_index_tuple i r hr j) (1 : ℕ)) (1 : K) := by
            simpa [SymmetricPower.tprod] using hval
    _ = MvPolynomial.monomial (binary_form_exponent_vector i r) (1 : K) := by
          rw [sum_single_binary_form_index_tuple (i := i) (r := r) hr]
    _ = MvPolynomial.monomial d (1 : K) := by
          rw [degree_eq_binary_form_exponent (i := i) hd]

/-- Helper for Exercise 16-16.3-9: the coordinate symmetric-power map already surjects onto the
degree-`i` binary-form space. -/
theorem coordinate_to_binary_form_surjective
    (i : ℕ) :
    Function.Surjective
      (symmetricPower_coordinate_to_homogeneousSubmodule (K := K) (ι := Fin 2) i) := by
  classical
  let f := symmetricPower_coordinate_to_homogeneousSubmodule (K := K) (ι := Fin 2) i
  intro p
  let preimageOfMonomial : (Fin 2 →₀ ℕ) → Sym[K]^i (Fin 2 →₀ K) := fun d ↦
    if hd : d.degree = i then
      Classical.choose (coordinate_to_binary_form_monomial_preimage (K := K) i d hd)
    else 0
  let x : Sym[K]^i (Fin 2 →₀ K) :=
    Finset.sum p.1.support fun d ↦
      (MvPolynomial.coeff d p.1) • preimageOfMonomial d
  refine ⟨x, ?_⟩
  apply Subtype.ext
  change ↑(f x) = p.1
  calc
    ↑(f x) =
        Finset.sum p.1.support fun d ↦
          MvPolynomial.coeff d p.1 • ↑(f (preimageOfMonomial d)) := by
            simp [x, f, map_sum, map_smul]
    _ =
        Finset.sum p.1.support fun d ↦
          MvPolynomial.coeff d p.1 • MvPolynomial.monomial d (1 : K) := by
            refine Finset.sum_congr rfl ?_
            intro d hd
            have hddeg : d.degree = i := by
              -- Every support monomial of a homogeneous polynomial has degree `i`.
              rw [Finsupp.degree_eq_weight_one]
              exact p.2 (by simpa [MvPolynomial.mem_support_iff] using hd)
            have hpre :
                f (preimageOfMonomial d) =
                  ⟨MvPolynomial.monomial d (1 : K), by
                    rw [MvPolynomial.mem_homogeneousSubmodule]
                    exact MvPolynomial.isHomogeneous_monomial (1 : K) hddeg⟩ := by
              simpa [preimageOfMonomial, hddeg] using
                Classical.choose_spec
                  (coordinate_to_binary_form_monomial_preimage (K := K) i d hddeg)
            have hpre_val : ↑(f (preimageOfMonomial d)) = MvPolynomial.monomial d (1 : K) := by
              exact congrArg Subtype.val hpre
            rw [hpre_val]
    _ = p.1 := by
          -- Reassemble the homogeneous polynomial from its monomial basis coordinates.
          rw [p.1.support_sum_monomial_coeff.symm]
          simp [Algebra.smul_def, MvPolynomial.C_mul_monomial]

/-- Helper for Exercise 16-16.3-9: the coordinate symmetric-power carrier is canonically
equivalent to LinearRepresentations_Serre_1977's degree-`i` binary-form model. -/
noncomputable def standard_sl2_binary_form_linearEquiv
    (i : ℕ) :
    Sym[K]^i (Fin 2 →₀ K) ≃ₗ[K] MvPolynomial.homogeneousSubmodule (Fin 2) K i := by
  let f := symmetricPower_coordinate_to_homogeneousSubmodule (K := K) (ι := Fin 2) i
  let hsurj : Function.Surjective f := coordinate_to_binary_form_surjective (K := K) i
  letI : FiniteDimensional K (Sym[K]^i (Fin 2 →₀ K)) := by infer_instance
  let s : Set (Fin 2 →₀ ℕ) := {d | d.degree = i}
  letI : Fintype s := Fintype.ofEquiv (Fin (i + 1)) (binary_form_degree_support_equiv (i := i)).symm
  letI : FiniteDimensional K (MvPolynomial.restrictSupport K s) :=
    (MvPolynomial.basisRestrictSupport K s).finiteDimensional_of_finite
  have hs :
      MvPolynomial.homogeneousSubmodule (Fin 2) K i = MvPolynomial.restrictSupport K s := by
    simpa [s, MvPolynomial.restrictSupport] using
      (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (σ := Fin 2) (R := K) i)
  letI : FiniteDimensional K (MvPolynomial.homogeneousSubmodule (Fin 2) K i) := by
    exact hs.symm ▸ (inferInstance : FiniteDimensional K (MvPolynomial.restrictSupport K s))
  have hdim :
      Module.finrank K (Sym[K]^i (Fin 2 →₀ K)) =
        Module.finrank K (MvPolynomial.homogeneousSubmodule (Fin 2) K i) := by
    rw [finrank_standard_coordinate_symmetricPower (K := K) i,
      finrank_binary_form_homogeneousSubmodule (K := K) i]
  have hinj : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj
  -- Route correction: package the Chapter 9 map as the named linear equivalence needed before
  -- starting LinearRepresentations_Serre_1977's fixed-line and orbit-span arguments on binary forms.
  exact LinearEquiv.ofBijective f ⟨hinj, hsurj⟩

/-- Helper for Exercise 16-16.3-9: transporting the standard coordinate symmetric-power action
through the binary-form linear equivalence gives LinearRepresentations_Serre_1977's binary-form representation. -/
noncomputable def standard_sl2_binary_form_model
    (i : ℕ) :
    Representation K (SpecialLinearGroup (ZMod p) (Fin 2 → ZMod p))
      (MvPolynomial.homogeneousSubmodule (Fin 2) K i) :=
  let eBin := standard_sl2_binary_form_linearEquiv (K := K) i
  (LinearEquiv.conjRingEquiv eBin).toMonoidHom.comp
    (nthSymmetricPower (standard_sl2_coordinate_model (K := K) (p := p)) i)

/-- Helper for Exercise 16-16.3-9: the coordinate symmetric-power model and the binary-form model
are equivalent representations. -/
theorem standard_sl2_binary_form_model_equiv
    (i : ℕ) :
    Nonempty
      ((nthSymmetricPower (standard_sl2_coordinate_model (K := K) (p := p)) i).Equiv
        (standard_sl2_binary_form_model (K := K) (p := p) i)) := by
  let eBin := standard_sl2_binary_form_linearEquiv (K := K) i
  refine ⟨Representation.Equiv.mk eBin ?_⟩
  intro g
  -- The binary-form action was defined by conjugating the coordinate symmetric-power action.
  ext x m
  simp only [standard_sl2_binary_form_model, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply]
  simp [eBin]

/-- Helper for Exercise 16-16.3-9: the binary-form equivalence sends the repeated first singleton
generator to the highest binary form `X₀^i`. -/
theorem standard_sl2_binary_form_linearEquiv_tprod_single_zero
    (i : ℕ) :
    standard_sl2_binary_form_linearEquiv (K := K) i
      (SymmetricPower.tprod K (fun _ : Fin i ↦ Finsupp.single 0 (1 : K))) =
      highest_binary_form (K := K) i := by
  -- Evaluate the Chapter 9 coordinate-to-polynomial map on the constant `0` tuple and compare
  -- the resulting monomial with the named highest-weight vector.
  change
    symmetricPower_coordinate_to_homogeneousSubmodule (K := K) (ι := Fin 2) i
        (SymmetricPower.tprod K (fun _ : Fin i ↦ Finsupp.single 0 (1 : K))) =
      highest_binary_form (K := K) i
  rw [symmetricPower_coordinate_to_homogeneousSubmodule_apply_single_tprod]
  have hsum :
      (∑ _j : Fin i, Finsupp.single (0 : Fin 2) (1 : ℕ)) =
        Finsupp.single (0 : Fin 2) i := by
    ext j
    fin_cases j <;> simp
  apply Subtype.ext
  simp [highest_binary_form, hsum]

/-- Helper for Exercise 16-16.3-9: the inverse binary-form equivalence sends the highest binary
form back to the repeated first singleton generator. -/
theorem standard_sl2_binary_form_linearEquiv_symm_highest_binary_form
    (i : ℕ) :
    (standard_sl2_binary_form_linearEquiv (K := K) i).symm (highest_binary_form (K := K) i) =
      SymmetricPower.tprod K (fun _ : Fin i ↦ Finsupp.single 0 (1 : K)) := by
  -- Apply the binary-form equivalence and use the explicit image formula from the previous lemma.
  apply (standard_sl2_binary_form_linearEquiv (K := K) i).injective
  simp [standard_sl2_binary_form_linearEquiv_tprod_single_zero (K := K) i]

/-- Helper for Exercise 16-16.3-9: the highest binary form is fixed by every upper-unipotent
element in LinearRepresentations_Serre_1977's binary-form model. -/
theorem highest_binary_form_fixed_by_upper_unipotent
    (i : ℕ) (a : ZMod p) :
    (standard_sl2_binary_form_model (K := K) (p := p) i)
      (upper_unipotent (p := p) a) (highest_binary_form (K := K) i) =
      highest_binary_form (K := K) i := by
  -- Transport to the coordinate symmetric-power model, where every tensor factor is the fixed
  -- singleton `e₀`, and then return through the binary-form equivalence.
  change
    (standard_sl2_binary_form_linearEquiv (K := K) i)
      ((nthSymmetricPower (standard_sl2_coordinate_model (K := K) (p := p)) i)
        (upper_unipotent (p := p) a)
        ((standard_sl2_binary_form_linearEquiv (K := K) i).symm
          (highest_binary_form (K := K) i))) =
      highest_binary_form (K := K) i
  rw [standard_sl2_binary_form_linearEquiv_symm_highest_binary_form (K := K) i]
  change
    (standard_sl2_binary_form_linearEquiv (K := K) i)
      (SymmetricPower.map i
        ((standard_sl2_coordinate_model (K := K) (p := p))
          (upper_unipotent (p := p) a))
        (SymmetricPower.tprod K (fun _ : Fin i ↦ Finsupp.single 0 (1 : K)))) =
      highest_binary_form (K := K) i
  rw [symmetricPower_map_tprod]
  rw [(standard_sl2_coordinate_model_upper_lower_on_singletons (K := K) (p := p) a).1]
  exact standard_sl2_binary_form_linearEquiv_tprod_single_zero (K := K) i

/-- Helper for Exercise 16-16.3-9: every nonzero subrepresentation of the binary-form model
contains a nonzero vector fixed by every upper-unipotent element. -/
theorem nonzero_subrepresentation_has_upper_fixed_vector
    (i : ℕ)
    (W : Subrepresentation (standard_sl2_binary_form_model (K := K) (p := p) i))
    (hW : W ≠ ⊥) :
    ∃ f ∈ W.toSubmodule, f ≠ 0 ∧
      ∀ a : ZMod p,
        (standard_sl2_binary_form_model (K := K) (p := p) i)
          (upper_unipotent (p := p) a) f = f := by
  let ρU :
      Representation K (Multiplicative (ZMod p)) ↥W.toSubmodule :=
    W.toRepresentation.comp (upper_unipotent_hom (p := p))
  have hW_ne_bot : W.toSubmodule ≠ ⊥ := by
    -- Pass the nontriviality assumption to the underlying carrier of the subrepresentation.
    intro hWbot
    apply hW
    exact Subrepresentation.toSubmodule_injective hWbot
  letI : Nontrivial W.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hW_ne_bot
  letI : AddCommGroup W.toSubmodule := inferInstance
  letI : CharP K p := by
    rw [← Algebra.charP_iff (ZMod p) K p]
    exact ZMod.charP p
  -- Apply the Chapter 8 fixed-vector argument on the subgroup-typed carrier once and then
  -- specialize the resulting invariant vector to the parameter `1`.
  have hInv :
      Representation.invariants ρU ≠ ⊥ := by
    simpa [ρU] using
      (invariants_ne_bot_of_isPGroup_charP
        (ρ := (show Representation K (Multiplicative (ZMod p)) ↥W.toSubmodule from
          W.toRepresentation.comp (upper_unipotent_hom (p := p))))
        (upper_unipotent_family_isPGroup (p := p)))
  rcases (Representation.invariants ρU).ne_bot_iff.mp hInv with ⟨f, hfInv, hf0⟩
  refine ⟨f.1, f.2, ?_, ?_⟩
  · -- A nonzero invariant vector in the subtype carrier is nonzero after forgetting the subtype.
    intro hf
    apply hf0
    exact Subtype.ext hf
  · -- Membership in the invariant submodule is exactly fixedness under every upper-unipotent.
    have hf_all :
        ∀ a : Multiplicative (ZMod p), ρU a f = f := by
      simpa [ρU] using (Representation.mem_invariants (ρ := ρU) f).mp hfInv
    intro a
    exact congrArg Subtype.val (hf_all (Multiplicative.ofAdd a))

/-- Helper for Exercise 16-16.3-9: the inverse binary-form equivalence sends the named monomial
basis vector back to the corresponding pure symmetric tensor. -/
theorem standard_sl2_binary_form_linearEquiv_symm_basisVec
    {i s : ℕ} (hs : s ≤ i) :
    (standard_sl2_binary_form_linearEquiv (K := K) i).symm
      (binary_form_basisVec (K := K) i s hs) =
      SymmetricPower.tprod K
        (fun j ↦ Finsupp.single (binary_form_index_tuple i s hs j) (1 : K)) := by
  -- The Chapter 9 coordinate-to-polynomial map sends this concrete tensor generator to the
  -- corresponding binary monomial, so injectivity recovers the inverse image.
  apply (standard_sl2_binary_form_linearEquiv (K := K) i).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  change
    MvPolynomial.monomial (binary_form_exponent_vector i s) (1 : K) =
      ↑((symmetricPower_coordinate_to_homogeneousSubmodule (K := K) (ι := Fin 2) i)
        (SymmetricPower.tprod K
          (fun j ↦ Finsupp.single (binary_form_index_tuple i s hs j) (1 : K))))
  rw [symmetricPower_coordinate_to_homogeneousSubmodule_apply_single_tprod]
  simp [sum_single_binary_form_index_tuple, binary_form_exponent_vector]

/-- Helper for Exercise 16-16.3-9: after transporting the upper-unipotent action on
`X₀^(i-s) X₁^s` back to the symmetric tensor model, the tensor factors become the appended tuple
with `i - s` copies of `e₀` and `s` copies of `e₀ + e₁`. -/
theorem upper_unipotent_one_basisVec_factor_tuple
    {i s : ℕ} (hs : s ≤ i) :
    (fun j : Fin i ↦
      (standard_sl2_coordinate_model (K := K) (p := p))
        (upper_unipotent (p := p) (1 : ZMod p))
        (Finsupp.single (binary_form_index_tuple i s hs j) (1 : K))) =
    (fun j ↦
      Fin.append
        (fun _ : Fin (i - s) ↦ Finsupp.single 0 (1 : K))
        (fun _ : Fin s ↦ Finsupp.single 0 (1 : K) + Finsupp.single 1 (1 : K))
        (j.cast (Nat.sub_add_cancel hs).symm)) := by
  -- Route correction: isolate the cast-heavy tuple transport before passing to the polynomial
  -- model, so the main theorem can use only stable rewrite lemmas afterward.
  funext j
  let hsplit : (i - s) + s = i := Nat.sub_add_cancel hs
  dsimp [binary_form_index_tuple]
  -- Read the reindexed factor through the left and right blocks of `Fin.append`.
  refine Fin.addCases ?_ ?_ (j.cast hsplit.symm)
  · intro j₀
    simp [standard_sl2_coordinate_model_upper_lower_on_singletons]
  · intro j₁
    simp [standard_sl2_coordinate_model_upper_lower_on_singletons]

/-- Helper for Exercise 16-16.3-9: the appended tuple from
`upper_unipotent_one_basisVec_factor_tuple` contributes the product
`X₀^(i-s) (X₀ + X₁)^s` under the Chapter 9 coordinate map. -/
theorem coordinateLinearForm_prod_append_upper_basis
    {i s : ℕ} (hs : s ≤ i) :
    (∏ j : Fin i,
      coordinateLinearForm (K := K) (ι := Fin 2)
        (Fin.append
          (fun _ : Fin (i - s) ↦ Finsupp.single 0 (1 : K))
          (fun _ : Fin s ↦ Finsupp.single 0 (1 : K) + Finsupp.single 1 (1 : K))
          (j.cast (Nat.sub_add_cancel hs).symm))) =
      (MvPolynomial.X (0 : Fin 2)) ^ (i - s) *
        (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)) ^ s := by
  let hsplit : i = (i - s) + s := (Nat.sub_add_cancel hs).symm
  -- Reindex the product to the literal appended tuple, then split it into the two blocks.
  calc
    (∏ j : Fin i,
        coordinateLinearForm (K := K) (ι := Fin 2)
          (Fin.append
            (fun _ : Fin (i - s) ↦ Finsupp.single 0 (1 : K))
            (fun _ : Fin s ↦ Finsupp.single 0 (1 : K) + Finsupp.single 1 (1 : K))
            (j.cast hsplit))) =
        ∏ j : Fin ((i - s) + s),
          coordinateLinearForm (K := K) (ι := Fin 2)
            (Fin.append
              (fun _ : Fin (i - s) ↦ Finsupp.single 0 (1 : K))
              (fun _ : Fin s ↦ Finsupp.single 0 (1 : K) + Finsupp.single 1 (1 : K))
              j) := by
          exact
            Fin.prod_congr'
              (f := fun j : Fin ((i - s) + s) ↦
                coordinateLinearForm (K := K) (ι := Fin 2)
                  (Fin.append
                    (fun _ : Fin (i - s) ↦ Finsupp.single 0 (1 : K))
                    (fun _ : Fin s ↦ Finsupp.single 0 (1 : K) + Finsupp.single 1 (1 : K))
                    j))
              hsplit
    _ = (∏ _ : Fin (i - s),
          coordinateLinearForm (K := K) (ι := Fin 2) (Finsupp.single 0 (1 : K))) *
        ∏ _ : Fin s,
          coordinateLinearForm (K := K) (ι := Fin 2)
            (Finsupp.single 0 (1 : K) + Finsupp.single 1 (1 : K)) := by
          rw [Fin.prod_univ_add]
          simp [Fin.append_left, Fin.append_right]
    _ = (MvPolynomial.X (0 : Fin 2)) ^ (i - s) *
        (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)) ^ s := by
          rw [Fin.prod_const, Fin.prod_const,
            coordinateLinearForm_single (K := K) (ι := Fin 2) (0 : Fin 2)]
          have hsum :
              coordinateLinearForm (K := K) (ι := Fin 2)
                  (Finsupp.single 0 (1 : K) + Finsupp.single 1 (1 : K)) =
                MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) := by
            rw [map_add, coordinateLinearForm_single, coordinateLinearForm_single]
          rw [hsum]

/-- Helper for Exercise 16-16.3-9: coercing the binary-form equivalence output to an ordinary
polynomial is just the underlying Chapter 9 coordinate-to-polynomial map. -/
theorem standard_sl2_binary_form_linearEquiv_apply_coe
    (i : ℕ) (x : Sym[K]^i(Fin 2 →₀ K)) :
    (((standard_sl2_binary_form_linearEquiv (K := K) i) x :
        MvPolynomial.homogeneousSubmodule (Fin 2) K i) :
      MvPolynomial (Fin 2) K) =
      ↑((symmetricPower_coordinate_to_homogeneousSubmodule (K := K) (ι := Fin 2) i) x) := by
  -- The chosen linear equivalence was defined with this coordinate map as its forward function.
  rfl

/-- Helper for Exercise 16-16.3-9: coercing the binary-form action to an ordinary polynomial
rewrites the conjugated symmetric-power action through the Chapter 9 coordinate map. -/
theorem standard_sl2_binary_form_model_apply_coe
    (i : ℕ) (g : SpecialLinearGroup (ZMod p) (Fin 2 → ZMod p))
    (f : MvPolynomial.homogeneousSubmodule (Fin 2) K i) :
    (((standard_sl2_binary_form_model (K := K) (p := p) i) g f :
        MvPolynomial.homogeneousSubmodule (Fin 2) K i) :
      MvPolynomial (Fin 2) K) =
      ↑((symmetricPower_coordinate_to_homogeneousSubmodule (K := K) (ι := Fin 2) i)
        ((nthSymmetricPower (standard_sl2_coordinate_model (K := K) (p := p)) i) g
          ((standard_sl2_binary_form_linearEquiv (K := K) i).symm f))) := by
  -- Unfold the conjugated action once, then forget the homogeneous wrapper via the Chapter 9
  -- coordinate-to-polynomial map.
  change
    (((standard_sl2_binary_form_linearEquiv (K := K) i)
        ((nthSymmetricPower (standard_sl2_coordinate_model (K := K) (p := p)) i) g
          ((standard_sl2_binary_form_linearEquiv (K := K) i).symm f)) :
        MvPolynomial.homogeneousSubmodule (Fin 2) K i) :
      MvPolynomial (Fin 2) K) =
      ↑((symmetricPower_coordinate_to_homogeneousSubmodule (K := K) (ι := Fin 2) i)
        ((nthSymmetricPower (standard_sl2_coordinate_model (K := K) (p := p)) i) g
          ((standard_sl2_binary_form_linearEquiv (K := K) i).symm f)))
  rw [standard_sl2_binary_form_linearEquiv_apply_coe]

theorem upper_unipotent_one_basisVec_coe
    {i s : ℕ} (hs : s ≤ i) :
    (((standard_sl2_binary_form_model (K := K) (p := p) i)
        (upper_unipotent (p := p) (1 : ZMod p))
        (binary_form_basisVec (K := K) i s hs) :
          MvPolynomial.homogeneousSubmodule (Fin 2) K i) :
          MvPolynomial (Fin 2) K) =
      (MvPolynomial.X (0 : Fin 2)) ^ (i - s) *
        (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)) ^ s := by
  -- Route correction: rewrite the transported action once through the coordinate model, then let
  -- the Chapter 9 tensor-to-polynomial map evaluate the explicit factor tuple.
  rw [standard_sl2_binary_form_model_apply_coe (K := K) (p := p) (i := i)
    (g := upper_unipotent (p := p) (1 : ZMod p))
    (f := binary_form_basisVec (K := K) i s hs)]
  rw [standard_sl2_binary_form_linearEquiv_symm_basisVec (K := K) (i := i) (s := s) hs]
  change
    ↑((symmetricPower_coordinate_to_homogeneousSubmodule (K := K) (ι := Fin 2) i)
        (SymmetricPower.map i
          ((standard_sl2_coordinate_model (K := K) (p := p))
            (upper_unipotent (p := p) (1 : ZMod p)))
          (SymmetricPower.tprod K
            (fun j ↦ Finsupp.single (binary_form_index_tuple i s hs j) (1 : K))))) =
      (((MvPolynomial.X (0 : Fin 2)) ^ (i - s) *
        (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)) ^ s) :
          MvPolynomial (Fin 2) K)
  rw [symmetricPower_map_tprod]
  rw [upper_unipotent_one_basisVec_factor_tuple (K := K) (p := p) (i := i) (s := s) hs]
  have hpoly :=
    congrArg Subtype.val
      (symmetricPower_coordinate_to_homogeneousSubmodule_apply_tprod
        (K := K) (ι := Fin 2) i
        (fun j ↦
          Fin.append
            (fun _ : Fin (i - s) ↦ Finsupp.single 0 (1 : K))
            (fun _ : Fin s ↦ Finsupp.single 0 (1 : K) + Finsupp.single 1 (1 : K))
            (j.cast (Nat.sub_add_cancel hs).symm)))
  simpa [coordinateLinearForm_prod_append_upper_basis (K := K) (i := i) (s := s) hs] using hpoly

/-- Helper for Exercise 16-16.3-9: the lower-unipotent singleton shear corresponds to the linear
form `X₀ + a X₁` on the binary-form side. -/
theorem coordinateLinearForm_lower_unipotent_singleton
    (a : ZMod p) :
    coordinateLinearForm (K := K) (ι := Fin 2)
        (algebraMap (ZMod p) K a • Finsupp.single 1 (1 : K) + Finsupp.single 0 (1 : K)) =
      MvPolynomial.X (0 : Fin 2) +
        algebraMap (ZMod p) K a • MvPolynomial.X (1 : Fin 2) := by
  -- Route correction: isolate the linear-form normalization once so the lower-orbit proof can
  -- rewrite the transported tensor factors without broad simplification.
  calc
    coordinateLinearForm (K := K) (ι := Fin 2)
        (algebraMap (ZMod p) K a • Finsupp.single 1 (1 : K) + Finsupp.single 0 (1 : K)) =
        coordinateLinearForm (K := K) (ι := Fin 2)
            (algebraMap (ZMod p) K a • Finsupp.single 1 (1 : K)) +
          coordinateLinearForm (K := K) (ι := Fin 2) (Finsupp.single 0 (1 : K)) := by
            rw [map_add]
    _ = algebraMap (ZMod p) K a •
          coordinateLinearForm (K := K) (ι := Fin 2) (Finsupp.single 1 (1 : K)) +
        coordinateLinearForm (K := K) (ι := Fin 2) (Finsupp.single 0 (1 : K)) := by
          rw [map_smul]
    _ = algebraMap (ZMod p) K a • MvPolynomial.X (1 : Fin 2) + MvPolynomial.X (0 : Fin 2) := by
          rw [coordinateLinearForm_single, coordinateLinearForm_single]
    _ = MvPolynomial.X (0 : Fin 2) +
          algebraMap (ZMod p) K a • MvPolynomial.X (1 : Fin 2) := by
          rw [add_comm]

/-- Helper for Exercise 16-16.3-9: the upper-unipotent singleton shear at parameter `1`
corresponds to the linear form `X₀ + X₁` on the binary-form side. -/
theorem coordinateLinearForm_upper_unipotent_one_singleton :
    coordinateLinearForm (K := K) (ι := Fin 2)
        (Finsupp.single 0 (1 : K) + Finsupp.single 1 (1 : K)) =
      MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) := by
  -- Normalize the transported `e₁` factor once so the upper basis-vector computation can work
  -- with the literal product of the two expected linear forms.
  calc
    coordinateLinearForm (K := K) (ι := Fin 2)
        (Finsupp.single 0 (1 : K) + Finsupp.single 1 (1 : K)) =
        coordinateLinearForm (K := K) (ι := Fin 2) (Finsupp.single 0 (1 : K)) +
          coordinateLinearForm (K := K) (ι := Fin 2) (Finsupp.single 1 (1 : K)) := by
            rw [map_add]
    _ = MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) := by
          rw [coordinateLinearForm_single, coordinateLinearForm_single]

/-- Helper for Exercise 16-16.3-9: in the binary-form model, the lower-unipotent orbit of the
highest vector is represented by the polynomial `(X₀ + a X₁)^i`. -/
theorem lower_unipotent_highest_binary_form_coe
    (i : ℕ) (a : ZMod p) :
    (((standard_sl2_binary_form_model (K := K) (p := p) i)
        (lower_unipotent (p := p) a) (highest_binary_form (K := K) i) :
          MvPolynomial.homogeneousSubmodule (Fin 2) K i) :
      MvPolynomial (Fin 2) K) =
      (MvPolynomial.X (0 : Fin 2) +
        algebraMap (ZMod p) K a • MvPolynomial.X (1 : Fin 2)) ^ i := by
  let coeffs : Fin 2 →₀ K :=
    algebraMap (ZMod p) K a • Finsupp.single 1 (1 : K) + Finsupp.single 0 (1 : K)
  -- Route correction: first rewrite the conjugated action through the transport-stable
  -- coordinate bridge, and only then compute the lower shear on the repeated `e₀` generator.
  rw [standard_sl2_binary_form_model_apply_coe (K := K) (p := p) (i := i)
    (g := lower_unipotent (p := p) a) (f := highest_binary_form (K := K) i)]
  rw [standard_sl2_binary_form_linearEquiv_symm_highest_binary_form (K := K) i]
  have hmap :
      ((nthSymmetricPower (standard_sl2_coordinate_model (K := K) (p := p)) i)
          (lower_unipotent (p := p) a))
        (SymmetricPower.tprod K (fun _ : Fin i ↦ Finsupp.single 0 (1 : K))) =
      SymmetricPower.map i
        ((standard_sl2_coordinate_model (K := K) (p := p))
          (lower_unipotent (p := p) a))
        (SymmetricPower.tprod K (fun _ : Fin i ↦ Finsupp.single 0 (1 : K))) := by
    rfl
  rw [hmap]
  rw [symmetricPower_map_tprod]
  rw [(standard_sl2_coordinate_model_upper_lower_on_singletons (K := K) (p := p) a).2.2.1]
  have hpoly :=
    congrArg Subtype.val
      (symmetricPower_coordinate_to_homogeneousSubmodule_apply_tprod
        (K := K) (ι := Fin 2) i
        (fun _ : Fin i ↦ coeffs))
  -- Every tensor factor becomes the same linear form `X₀ + a X₁`, so the product is its `i`th
  -- power.
  have hpoly' :
      ↑((symmetricPower_coordinate_to_homogeneousSubmodule (K := K) (ι := Fin 2) i)
          (SymmetricPower.tprod K (fun _ : Fin i ↦ coeffs))) =
        (coordinateLinearForm (K := K) (ι := Fin 2) coeffs) ^ i := by
    simpa [coeffs, Finset.prod_const] using hpoly
  have hlinear :
      coordinateLinearForm (K := K) (ι := Fin 2) coeffs =
        MvPolynomial.X (0 : Fin 2) +
          algebraMap (ZMod p) K a • MvPolynomial.X (1 : Fin 2) := by
    simpa [coeffs] using
      coordinateLinearForm_lower_unipotent_singleton (K := K) (p := p) a
  rw [hlinear] at hpoly'
  exact hpoly'

/-- Helper for Exercise 16-16.3-9: the coefficient of the lower-unipotent orbit of the highest
binary form is the expected binomial term. -/
theorem lower_unipotent_highest_binary_form_coeff
    {i r : ℕ} (hr : r ≤ i) (a : ZMod p) :
    MvPolynomial.coeff (binary_form_exponent_vector i r)
      (((standard_sl2_binary_form_model (K := K) (p := p) i)
          (lower_unipotent (p := p) a) (highest_binary_form (K := K) i) :
            MvPolynomial.homogeneousSubmodule (Fin 2) K i) :
        MvPolynomial (Fin 2) K) =
      (Nat.choose i r : K) * (algebraMap (ZMod p) K a) ^ r := by
  let coeffs : Fin 2 →₀ K :=
    algebraMap (ZMod p) K a • Finsupp.single 1 (1 : K) + Finsupp.single 0 (1 : K)
  have hlinear :
      coordinateLinearForm (K := K) (ι := Fin 2) coeffs =
        MvPolynomial.X (0 : Fin 2) +
          algebraMap (ZMod p) K a • MvPolynomial.X (1 : Fin 2) := by
    -- This is exactly the named normalization of the lower-unipotent singleton shear.
    simpa [coeffs] using
      coordinateLinearForm_lower_unipotent_singleton (K := K) (p := p) a
  have hsum :
      (binary_form_exponent_vector i r).sum (fun _ m ↦ m) = i := by
    -- The source-faithful coefficient formula uses only that the exponent vector has total
    -- degree `i`.
    convert binary_form_exponent_degree (i := i) hr using 1
  have hmultinomial :
      ((binary_form_exponent_vector i r).multinomial : K) = (Nat.choose i r : K) := by
    -- In two variables, the multinomial coefficient is the usual binomial coefficient.
    calc
      ((binary_form_exponent_vector i r).multinomial : K) = (Nat.choose i (i - r) : K) := by
        rw [Finsupp.multinomial_eq_of_support_subset (f := binary_form_exponent_vector i r)
          (s := Finset.univ) (Finset.subset_univ _), Finset.univ_fin2,
          Nat.binomial_eq_choose Fin.zero_ne_one]
        simp [binary_form_exponent_vector, Nat.sub_add_cancel hr]
      _ = (Nat.choose i r : K) := by
        rw [Nat.choose_symm hr]
  have hprod :
      (binary_form_exponent_vector i r).prod (fun j m ↦ coeffs j ^ m) =
        (algebraMap (ZMod p) K a) ^ r := by
    -- Only the `X₁` coefficient contributes nontrivially, because the `X₀` coefficient is `1`.
    rw [binary_form_exponent_vector, Finsupp.prod_add_index]
    · simpa [coeffs, add_comm] using
        (show (a • (1 : K)) ^ r = (algebraMap (ZMod p) K a) ^ r by
          rw [Algebra.smul_def]
          simp)
    · intro j
      simp
    · intro j m n
      simp [pow_add]
  -- Rewrite the lower orbit as a power of one linear combination and then read off its
  -- `X₀^(i-r) X₁^r` coefficient by the binary multinomial formula.
  rw [lower_unipotent_highest_binary_form_coe (K := K) (p := p) (i := i) (a := a), ← hlinear]
  rw [coordinateLinearForm, MvPolynomial.coeff_linearCombination_X_pow, if_pos hsum,
    hmultinomial, hprod]

/-- Helper for Exercise 16-16.3-9: at parameter `1`, the upper-unipotent action sends the binary
basis vector `X₀^(i-r) X₁^r` to a polynomial whose `X₀^(i-t) X₁^t` coefficient is the expected
binomial coefficient when `t ≤ r`, and vanishes otherwise. -/
theorem upper_unipotent_one_basisVec_coeff
    {i r t : ℕ} (hr : r ≤ i) (ht : t ≤ i) :
    MvPolynomial.coeff (binary_form_exponent_vector i t)
      (((standard_sl2_binary_form_model (K := K) (p := p) i)
          (upper_unipotent (p := p) (1 : ZMod p))
          (binary_form_basisVec (K := K) i r hr) :
            MvPolynomial.homogeneousSubmodule (Fin 2) K i) :
        MvPolynomial (Fin 2) K) =
      if t ≤ r then (Nat.choose r t : K) else 0 := by
  -- Route correction: compute the upper translate on the named basis vector first, then read the
  -- requested coefficient by stripping off the fixed `X₀^(i-r)` factor.
  rw [upper_unipotent_one_basisVec_coe (K := K) (p := p) (i := i) (s := r) hr,
    MvPolynomial.X_pow_eq_monomial]
  by_cases htr : t ≤ r
  · have hleft :
        Finsupp.single (0 : Fin 2) (i - r) ≤ binary_form_exponent_vector i t := by
      intro j
      fin_cases j
      · simpa [binary_form_exponent_vector] using (show i - r ≤ i - t by omega)
      · simp [binary_form_exponent_vector]
    rw [MvPolynomial.coeff_monomial_mul' (binary_form_exponent_vector i t)
      (Finsupp.single (0 : Fin 2) (i - r)) (1 : K)
      ((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)) ^ r), if_pos hleft]
    have hsub :
        binary_form_exponent_vector i t - Finsupp.single (0 : Fin 2) (i - r) =
          binary_form_exponent_vector r t := by
      ext j
      fin_cases j
      · simp [binary_form_exponent_vector]
        omega
      · simp [binary_form_exponent_vector]
    rw [hsub]
    have hcoeff :
        MvPolynomial.coeff (binary_form_exponent_vector r t)
          ((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)) ^ r) =
        (Nat.choose r t : K) := by
      -- The remaining coefficient is the `a = 1` instance of the lower-unipotent binomial
      -- formula, after normalizing `algebraMap 1` to `1`.
      calc
        MvPolynomial.coeff (binary_form_exponent_vector r t)
            ((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)) ^ r) =
          MvPolynomial.coeff (binary_form_exponent_vector r t)
            ((MvPolynomial.X (0 : Fin 2) +
                algebraMap (ZMod p) K (1 : ZMod p) • MvPolynomial.X (1 : Fin 2)) ^ r) := by
                  simp
        _ = MvPolynomial.coeff (binary_form_exponent_vector r t)
            (((standard_sl2_binary_form_model (K := K) (p := p) r)
                (lower_unipotent (p := p) (1 : ZMod p))
                (highest_binary_form (K := K) r) :
                  MvPolynomial.homogeneousSubmodule (Fin 2) K r) :
              MvPolynomial (Fin 2) K) := by
                rw [lower_unipotent_highest_binary_form_coe
                  (K := K) (p := p) (i := r) (a := (1 : ZMod p))]
        _ = (Nat.choose r t : K) * (algebraMap (ZMod p) K (1 : ZMod p)) ^ t := by
              simpa using
                lower_unipotent_highest_binary_form_coeff
                  (K := K) (p := p) (i := r) (r := t) htr (a := (1 : ZMod p))
        _ = (Nat.choose r t : K) := by simp
    simpa [if_pos htr] using hcoeff
  · have hleft :
        ¬ Finsupp.single (0 : Fin 2) (i - r) ≤ binary_form_exponent_vector i t := by
      intro hleft
      apply htr
      have hzero : i - r ≤ i - t := by
        simpa [binary_form_exponent_vector] using hleft 0
      omega
    rw [MvPolynomial.coeff_monomial_mul' (binary_form_exponent_vector i t)
      (Finsupp.single (0 : Fin 2) (i - r)) (1 : K)
      ((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)) ^ r), if_neg hleft]
    simp [htr]

/-- Helper for Exercise 16-16.3-9: two degree-`i` binary forms are equal once their coefficients
agree on the ordered degree-`i` monomial basis. -/
theorem binary_form_coefficient_ext
    {i : ℕ}
    {f g : MvPolynomial.homogeneousSubmodule (Fin 2) K i}
    (hcoeff :
      ∀ r, r ≤ i →
        MvPolynomial.coeff (binary_form_exponent_vector i r) (f : MvPolynomial (Fin 2) K) =
          MvPolynomial.coeff (binary_form_exponent_vector i r) (g : MvPolynomial (Fin 2) K)) :
    f = g := by
  -- Compare arbitrary coefficients; homogeneity kills the wrong degrees, and degree `i`
  -- monomials are exactly the ordered binary-form basis vectors.
  apply Subtype.ext
  ext d
  by_cases hd : d.degree = i
  · let r : ℕ := d 1
    have hr : r ≤ i := binary_form_right_le_of_degree (i := i) hd
    rw [degree_eq_binary_form_exponent (i := i) hd]
    exact hcoeff r hr
  · have hf_zero :
        MvPolynomial.coeff d (f : MvPolynomial (Fin 2) K) = 0 := by
      exact f.2.coeff_eq_zero hd
    have hg_zero :
        MvPolynomial.coeff d (g : MvPolynomial (Fin 2) K) = 0 := by
      exact g.2.coeff_eq_zero hd
    rw [hf_zero, hg_zero]

/-- Helper for Exercise 16-16.3-9: package coefficient extraction on degree-`i` binary forms as a
linear map, so later coefficient arguments avoid repeated subtype transport. -/
def binary_form_coefficient_linear_map
    (i : ℕ) (d : Fin 2 →₀ ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin 2) K i →ₗ[K] K :=
  (MvPolynomial.lcoeff (R := K) d).comp (Submodule.subtype _)

/-- Helper for Exercise 16-16.3-9: the packaged coefficient map reads exactly the requested
coefficient of the underlying polynomial. -/
@[simp] theorem binary_form_coefficient_linear_map_apply
    {i : ℕ} {d : Fin 2 →₀ ℕ}
    (f : MvPolynomial.homogeneousSubmodule (Fin 2) K i) :
    binary_form_coefficient_linear_map (K := K) i d f =
      MvPolynomial.coeff d (f : MvPolynomial (Fin 2) K) := by
  -- This is definitional once coefficient extraction is packaged through `Submodule.subtype`.
  rfl

/-- Helper for Exercise 16-16.3-9: every degree-`i` binary form expands in the ordered monomial
basis `X₀^i, X₀^(i-1) X₁, …, X₁^i`. -/
theorem binary_form_eq_sum_basisVec
    {i : ℕ} (f : MvPolynomial.homogeneousSubmodule (Fin 2) K i) :
    (f =
      Finset.sum (Finset.range (i + 1)) fun r ↦
        MvPolynomial.coeff (binary_form_exponent_vector i r) (f : MvPolynomial (Fin 2) K) •
          binary_form_basisVec_or_zero (K := K) i r) := by
  -- Compare the ordered-basis expansion coefficientwise through the packaged coefficient map.
  apply binary_form_coefficient_ext
  intro s hs
  let coeffMap :=
    binary_form_coefficient_linear_map (K := K) i (binary_form_exponent_vector i s)
  change coeffMap f =
    coeffMap
      (Finset.sum (Finset.range (i + 1)) fun r ↦
        MvPolynomial.coeff (binary_form_exponent_vector i r) (f : MvPolynomial (Fin 2) K) •
          binary_form_basisVec_or_zero (K := K) i r)
  symm
  calc
    coeffMap
        (Finset.sum (Finset.range (i + 1)) fun r ↦
          MvPolynomial.coeff (binary_form_exponent_vector i r) (f : MvPolynomial (Fin 2) K) •
            binary_form_basisVec_or_zero (K := K) i r) =
      Finset.sum (Finset.range (i + 1)) fun r ↦
        MvPolynomial.coeff (binary_form_exponent_vector i r) (f : MvPolynomial (Fin 2) K) *
          (if s = r then 1 else 0) := by
            -- Each basis vector contributes only to its own coefficient.
            rw [map_sum]
            refine Finset.sum_congr rfl ?_
            intro r hr_mem
            rw [map_smul]
            have hr : r ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hr_mem)
            simp [coeffMap, binary_form_basisVec_or_zero_eq (K := K) hr,
              coeff_binary_form_basisVec (K := K) hr]
    _ = MvPolynomial.coeff (binary_form_exponent_vector i s) (f : MvPolynomial (Fin 2) K) := by
          -- Only the `r = s` summand survives.
          rw [Finset.sum_eq_single s]
          · simp
          · intro r hr_mem hrs
            by_cases hsr : s = r
            · exact False.elim (hrs hsr.symm)
            · simp [hsr]
          · intro hs_mem
            exact False.elim (hs_mem (Finset.mem_range.mpr (Nat.lt_succ_of_le hs)))
    _ = coeffMap f := by
          simp [coeffMap]

/-- Helper for Exercise 16-16.3-9: the coefficients of an upper-unipotent-fixed binary form obey
the triangular binomial relation coming from the translate `X₁ ↦ X₀ + X₁`. -/
theorem upper_unipotent_one_fixed_coeff_eq_sum
    {i t : ℕ} (ht : t ≤ i)
    {f : MvPolynomial.homogeneousSubmodule (Fin 2) K i}
    (hfix :
      (standard_sl2_binary_form_model (K := K) (p := p) i)
        (upper_unipotent (p := p) (1 : ZMod p)) f = f) :
    (MvPolynomial.coeff (binary_form_exponent_vector i t) (f : MvPolynomial (Fin 2) K) =
      Finset.sum (Finset.range (i + 1)) fun r ↦
        MvPolynomial.coeff (binary_form_exponent_vector i r) (f : MvPolynomial (Fin 2) K) *
          (if t ≤ r then (Nat.choose r t : K) else 0)) := by
  let coeffMap :=
    binary_form_coefficient_linear_map (K := K) i (binary_form_exponent_vector i t)
  let upperOne :
      MvPolynomial.homogeneousSubmodule (Fin 2) K i →ₗ[K]
        MvPolynomial.homogeneousSubmodule (Fin 2) K i :=
    (standard_sl2_binary_form_model (K := K) (p := p) i)
      (upper_unipotent (p := p) (1 : ZMod p))
  -- Apply the coefficient map to the fixed-vector identity, then expand `f` in the ordered basis.
  calc
    MvPolynomial.coeff (binary_form_exponent_vector i t) (f : MvPolynomial (Fin 2) K)
      = coeffMap (upperOne f) := by
              simpa [coeffMap] using congrArg coeffMap hfix.symm
    _ = coeffMap
          (upperOne
            (Finset.sum (Finset.range (i + 1)) fun r ↦
              MvPolynomial.coeff (binary_form_exponent_vector i r)
                (f : MvPolynomial (Fin 2) K) •
                  binary_form_basisVec_or_zero (K := K) i r)) := by
          simpa using
            congrArg
              (fun x ↦ coeffMap (upperOne x))
              (binary_form_eq_sum_basisVec (K := K) (i := i) f)
    _ = Finset.sum (Finset.range (i + 1)) fun r ↦
          MvPolynomial.coeff (binary_form_exponent_vector i r) (f : MvPolynomial (Fin 2) K) *
            (if t ≤ r then (Nat.choose r t : K) else 0) := by
          -- The representation and the coefficient map are both linear, so the sum reduces to
          -- the coefficient formula for each translated basis vector.
          rw [map_sum, map_sum]
          refine Finset.sum_congr rfl ?_
          intro r hr_mem
          rw [map_smul, map_smul]
          have hr : r ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hr_mem)
          simp [coeffMap, upperOne, binary_form_basisVec_or_zero_eq (K := K) hr,
            upper_unipotent_one_basisVec_coeff (K := K) (p := p) (r := r) (t := t) hr ht,
            mul_comm]

/-- Helper for Exercise 16-16.3-9: if a degree-`i` binary form fixed by the upper-unipotent
element has no terms of `X₁`-degree greater than `r`, then its `X₁`-degree-`r` coefficient also
vanishes. -/
theorem upper_unipotent_fixed_highest_degree_step
    {i r : ℕ}
    (hi : i < p) (hr0 : 0 < r) (hr : r ≤ i)
    {f : MvPolynomial.homogeneousSubmodule (Fin 2) K i}
    (hfix :
      (standard_sl2_binary_form_model (K := K) (p := p) i)
        (upper_unipotent (p := p) (1 : ZMod p)) f = f)
    (hvanish :
      ∀ s, r < s → s ≤ i →
        MvPolynomial.coeff (binary_form_exponent_vector i s)
          (f : MvPolynomial (Fin 2) K) = 0) :
    MvPolynomial.coeff (binary_form_exponent_vector i r)
      (f : MvPolynomial (Fin 2) K) = 0 := by
  let coeff : ℕ → K := fun s ↦
    MvPolynomial.coeff (binary_form_exponent_vector i s) (f : MvPolynomial (Fin 2) K)
  let phi : ℕ → K := fun s ↦
    coeff s * (if r - 1 ≤ s then (Nat.choose s (r - 1) : K) else 0)
  have hpred : r - 1 ≤ i := by omega
  have htri :
      coeff (r - 1) = Finset.sum (Finset.range (i + 1)) phi := by
    -- Route correction: use the triangular coefficient relation at degree `r - 1`.
    simpa [coeff, phi] using
      upper_unipotent_one_fixed_coeff_eq_sum (K := K) (p := p)
        (i := i) (t := r - 1) hpred hfix
  have hsmall :
      Finset.sum (Finset.range (r - 1)) phi = 0 := by
    -- All indices strictly below `r - 1` vanish because the triangular factor is zero there.
    refine Finset.sum_eq_zero ?_
    intro s hs
    have hslt : s < r - 1 := Finset.mem_range.mp hs
    have hnot : ¬ r - 1 ≤ s := Nat.not_le.mpr hslt
    simp [hnot]
  have htail :
      Finset.sum (Finset.Ico (r + 1) (i + 1)) phi = 0 := by
    -- All terms above `r` vanish by the assumed highest-degree support bound.
    refine Finset.sum_eq_zero ?_
    intro s hs
    have hs_left : r + 1 ≤ s := (Finset.mem_Ico.mp hs).1
    have hs_right : s < i + 1 := (Finset.mem_Ico.mp hs).2
    have hrs : r < s := Nat.lt_of_lt_of_le (Nat.lt_succ_self r) hs_left
    have hsi : s ≤ i := Nat.le_of_lt_succ hs_right
    simp [coeff, hvanish s hrs hsi]
  have hsum_range_r :
      Finset.sum (Finset.range r) phi = coeff (r - 1) := by
    -- Inside `range r`, only the terminal term `s = r - 1` can survive.
    rw [show r = (r - 1) + 1 by omega, Finset.sum_range_succ, hsmall]
    simp [coeff]
  have hsum :
      Finset.sum (Finset.range (i + 1)) phi =
        coeff (r - 1) + coeff r * (Nat.choose r (r - 1) : K) := by
    -- Split the triangular sum into the initial block `s ≤ r` and the vanishing tail `s > r`.
    calc
      Finset.sum (Finset.range (i + 1)) phi
          = Finset.sum (Finset.range (r + 1)) phi +
              Finset.sum (Finset.Ico (r + 1) (i + 1)) phi := by
                rw [Finset.sum_range_add_sum_Ico _ (Nat.succ_le_succ hr)]
      _ = Finset.sum (Finset.range (r + 1)) phi := by rw [htail, add_zero]
      _ = Finset.sum (Finset.range r) phi + phi r := by
            rw [Finset.sum_range_succ]
      _ = coeff (r - 1) + coeff r * (Nat.choose r (r - 1) : K) := by
            rw [hsum_range_r]
            simp [phi, coeff]
  have hzero_mul : coeff r * (Nat.choose r (r - 1) : K) = 0 := by
    -- Cancel the common `coeff (r - 1)` term from the triangular identity.
    have hcancel :
        coeff (r - 1) + 0 = coeff (r - 1) + coeff r * (Nat.choose r (r - 1) : K) := by
      simpa [hsum] using htri
    simpa using (add_left_cancel hcancel).symm
  have hchoose_ne :
      (Nat.choose r (r - 1) : K) ≠ 0 := by
    exact nat_choose_cast_ne_zero_of_lt_prime (K := K) (p := p)
      (i := r) (r := r - 1) (Nat.sub_le _ _) (lt_of_le_of_lt hr hi)
  exact (mul_eq_zero.mp hzero_mul).resolve_right hchoose_ne

/-- Helper for Exercise 16-16.3-9: the only degree-`i` binary forms fixed by the upper-unipotent
element with parameter `1` are scalar multiples of the highest-weight vector `X₀^i`. -/
-- TODO: iterate `upper_unipotent_fixed_highest_degree_step` downward on the `X₁`-degree and then
-- collapse the ordered basis expansion of `f` to the `r = 0` summand.
theorem upper_unipotent_one_fixed_eq_smul_highest_binary_form
    {i : ℕ}
    (hi : i < p)
    {f : MvPolynomial.homogeneousSubmodule (Fin 2) K i}
    (hfix :
      (standard_sl2_binary_form_model (K := K) (p := p) i)
        (upper_unipotent (p := p) (1 : ZMod p)) f = f) :
    ∃ c : K, f = c • highest_binary_form (K := K) i := by
  classical
  let coeff : ℕ → K := fun r ↦
    MvPolynomial.coeff (binary_form_exponent_vector i r) (f : MvPolynomial (Fin 2) K)
  let S : Finset ℕ :=
    (Finset.range (i + 1)).filter fun r ↦ 0 < r ∧ coeff r ≠ 0
  have hS_empty : ¬ S.Nonempty := by
    intro hS
    let r := S.max' hS
    have hr_mem : r ∈ S := Finset.max'_mem S hS
    have hr_range : r ∈ Finset.range (i + 1) := (Finset.mem_filter.mp hr_mem).1
    have hr0 : 0 < r := (Finset.mem_filter.mp hr_mem).2.1
    have hr_ne : coeff r ≠ 0 := (Finset.mem_filter.mp hr_mem).2.2
    have hr : r ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hr_range)
    have hvanish :
        ∀ s, r < s → s ≤ i → coeff s = 0 := by
      intro s hrs hs
      by_contra hs_ne
      have hs_mem : s ∈ S := by
        refine Finset.mem_filter.mpr ?_
        refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hs), ?_⟩
        exact ⟨lt_trans hr0 hrs, hs_ne⟩
      have hmax : s ≤ r := Finset.le_max' S s hs_mem
      exact (not_lt_of_ge hmax hrs).elim
    have hzero :
        coeff r = 0 := by
      -- Route correction: choose the maximal positive `X₁`-degree and apply the previous
      -- highest-degree elimination step instead of trying to recurse blindly on coefficients.
      simpa [coeff] using
        upper_unipotent_fixed_highest_degree_step (K := K) (p := p)
          (i := i) (r := r) hi hr0 hr hfix hvanish
    exact hr_ne hzero
  have hpositive_zero :
      ∀ r, 0 < r → r ≤ i → coeff r = 0 := by
    intro r hr0 hr
    by_contra hr_ne
    apply hS_empty
    exact ⟨r, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hr), ⟨hr0, hr_ne⟩⟩⟩
  refine ⟨coeff 0, ?_⟩
  -- Once all positive `X₁`-degree coefficients vanish, the ordered basis expansion collapses to
  -- the highest-weight line spanned by `X₀^i`.
  calc
    f =
      Finset.sum (Finset.range (i + 1)) fun r ↦
        coeff r • binary_form_basisVec_or_zero (K := K) i r := by
          simpa [coeff] using binary_form_eq_sum_basisVec (K := K) (i := i) f
    _ = coeff 0 • binary_form_basisVec_or_zero (K := K) i 0 := by
          refine Finset.sum_eq_single 0 ?_ ?_
          · intro r hr hr_ne
            have hr' : r ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
            have hr0 : 0 < r := Nat.pos_of_ne_zero hr_ne
            simp [coeff, hpositive_zero r hr0 hr']
          · intro hzero
            exact False.elim (hzero (by simp))
    _ = coeff 0 • highest_binary_form (K := K) i := by
          rw [binary_form_basisVec_or_zero_eq (K := K) (i := i) (r := 0) (Nat.zero_le i)]
          rw [← highest_binary_form_eq_binary_form_basisVec_zero (K := K) i]


/-- Helper for Exercise 16-16.3-9: the highest binary form `X₀^i` is nonzero. -/
theorem highest_binary_form_ne_zero
    (i : ℕ) :
    highest_binary_form (K := K) i ≠ 0 := by
  -- The coefficient of the highest monomial is `1`, so the polynomial cannot vanish.
  intro hzero
  rw [highest_binary_form_eq_binary_form_basisVec_zero (K := K) i] at hzero
  have hcoeff :
      MvPolynomial.coeff (binary_form_exponent_vector i 0)
          ((binary_form_basisVec (K := K) i 0 (Nat.zero_le i) :
              MvPolynomial.homogeneousSubmodule (Fin 2) K i) :
            MvPolynomial (Fin 2) K) = 0 := by
    simpa using
      congrArg
        (fun f : MvPolynomial.homogeneousSubmodule (Fin 2) K i ↦
          MvPolynomial.coeff (binary_form_exponent_vector i 0) (f : MvPolynomial (Fin 2) K))
        hzero
  have hone :
      MvPolynomial.coeff (binary_form_exponent_vector i 0)
          ((binary_form_basisVec (K := K) i 0 (Nat.zero_le i) :
              MvPolynomial.homogeneousSubmodule (Fin 2) K i) :
            MvPolynomial (Fin 2) K) = 1 := by
    simpa [binary_form_exponent_vector] using
      coeff_binary_form_basisVec (K := K) (i := i) (r := 0) (s := 0)
        (Nat.zero_le i)
  rw [hone] at hcoeff
  exact one_ne_zero hcoeff

/-- Helper for Exercise 16-16.3-9: for parameters `0, …, i` with `i < p`, casting first to
`ZMod p` and then to `K` agrees with the direct natural-number cast to `K`. -/
theorem fin_cast_zmod_to_field_eq_nat_cast
    {i : ℕ} (a : Fin (i + 1)) :
    algebraMap (ZMod p) K (((a : ℕ) : ZMod p)) = ((a : ℕ) : K) := by
  simp

/-- Helper for Exercise 16-16.3-9: a linear relation among the lower-unipotent orbit vectors
forces every corresponding Vandermonde moment to vanish. -/
theorem lower_unipotent_orbit_moment_zero
    {i : ℕ} (hi : i < p)
    {c : Fin (i + 1) → K}
    (hrelation :
      ∑ a : Fin (i + 1),
        c a •
          (standard_sl2_binary_form_model (K := K) (p := p) i)
            (lower_unipotent (p := p) ((a : ℕ) : ZMod p))
            (highest_binary_form (K := K) i) = 0) :
    ∀ r : Fin (i + 1),
      ∑ a : Fin (i + 1), c a * (((a : ℕ) : K) ^ (r : ℕ)) = 0 := by
  intro r
  let coeffMap :=
    binary_form_coefficient_linear_map (K := K) i (binary_form_exponent_vector i (r : ℕ))
  have hr : (r : ℕ) ≤ i := Nat.le_of_lt_succ r.2
  have hcoeff :
      (Nat.choose i (r : ℕ) : K) *
          (∑ a : Fin (i + 1), c a * (((a : ℕ) : K) ^ (r : ℕ))) = 0 := by
    -- Apply the coefficient map to the orbit relation and rewrite each orbit vector explicitly.
    simpa [coeffMap, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm,
      fin_cast_zmod_to_field_eq_nat_cast (K := K) (p := p) (i := i),
      lower_unipotent_highest_binary_form_coeff (K := K) (p := p)
        (i := i) (r := (r : ℕ)) hr] using congrArg coeffMap hrelation
  have hchoose_ne :
      (Nat.choose i (r : ℕ) : K) ≠ 0 :=
    nat_choose_cast_ne_zero_of_lt_prime (K := K) (p := p)
      (i := i) (r := (r : ℕ)) hr hi
  exact (mul_eq_zero.mp hcoeff).resolve_left hchoose_ne

/-- Helper for Exercise 16-16.3-9: for `i < p`, the lower-unipotent orbit of the highest binary
form at the parameters `0, …, i` is linearly independent. -/
theorem lower_unipotent_highest_binary_form_orbit_linearIndependent
    {i : ℕ} (hi : i < p) :
    LinearIndependent K
      (fun a : Fin (i + 1) ↦
        (standard_sl2_binary_form_model (K := K) (p := p) i)
          (lower_unipotent (p := p) ((a : ℕ) : ZMod p))
          (highest_binary_form (K := K) i)) :=
  by
  let orbit : Fin (i + 1) → MvPolynomial.homogeneousSubmodule (Fin 2) K i := fun a ↦
    (standard_sl2_binary_form_model (K := K) (p := p) i)
      (lower_unipotent (p := p) ((a : ℕ) : ZMod p))
      (highest_binary_form (K := K) i)
  rw [linearIndependent_iff]
  intro l hl
  have hl' : ∑ a : Fin (i + 1), l a • orbit a = 0 := by
    -- Rewrite the finitely supported linear combination as the full finite-index sum.
    simpa [orbit, Finsupp.linearCombination_apply, Finsupp.sum_fintype] using hl
  have hmoment :
      ∀ r : Fin (i + 1), ∑ a : Fin (i + 1), l a * (((a : ℕ) : K) ^ (r : ℕ)) = 0 :=
    lower_unipotent_orbit_moment_zero (K := K) (p := p) (i := i) hi hl'
  have hinj : Function.Injective (fun a : Fin (i + 1) ↦ ((a : ℕ) : K)) := by
    -- The parameters `0, …, i` stay distinct after casting into the characteristic-`p` field.
    intro a b hab
    apply Fin.ext
    exact nat_cast_injective_of_lt_prime (K := K) (p := p)
      (a := (a : ℕ)) (b := (b : ℕ)) (i := i)
      (Nat.le_of_lt_succ a.2) (Nat.le_of_lt_succ b.2) hi hab
  have hzero_fun :
      (fun a : Fin (i + 1) ↦ l a) = 0 :=
    Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hinj hmoment
  ext a
  exact congrFun hzero_fun a

/-- Helper for Exercise 16-16.3-9: for `i < p`, the lower-unipotent orbit of the highest binary
form spans the full degree-`i` binary-form space. -/
theorem lower_unipotent_highest_binary_form_orbit_span_eq_top
    {i : ℕ} (hi : i < p) :
    Submodule.span K
      (Set.range fun a : Fin (i + 1) ↦
        (standard_sl2_binary_form_model (K := K) (p := p) i)
          (lower_unipotent (p := p) ((a : ℕ) : ZMod p))
          (highest_binary_form (K := K) i)) = ⊤ :=
  by
  let orbit : Fin (i + 1) → MvPolynomial.homogeneousSubmodule (Fin 2) K i := fun a ↦
    (standard_sl2_binary_form_model (K := K) (p := p) i)
      (lower_unipotent (p := p) ((a : ℕ) : ZMod p))
      (highest_binary_form (K := K) i)
  let s : Set (Fin 2 →₀ ℕ) := {d | d.degree = i}
  letI : Fintype s := Fintype.ofEquiv (Fin (i + 1)) (binary_form_degree_support_equiv (i := i)).symm
  letI : FiniteDimensional K (MvPolynomial.restrictSupport K s) :=
    (MvPolynomial.basisRestrictSupport K s).finiteDimensional_of_finite
  have hs :
      MvPolynomial.homogeneousSubmodule (Fin 2) K i = MvPolynomial.restrictSupport K s := by
    -- Reuse the same finite-support model as in the binary-form linear equivalence.
    simpa [s, MvPolynomial.restrictSupport] using
      (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (σ := Fin 2) (R := K) i)
  letI : FiniteDimensional K (MvPolynomial.homogeneousSubmodule (Fin 2) K i) := by
    exact hs.symm ▸ (inferInstance : FiniteDimensional K (MvPolynomial.restrictSupport K s))
  have horbit :
      LinearIndependent K orbit :=
    lower_unipotent_highest_binary_form_orbit_linearIndependent (K := K) (p := p) hi
  -- The independent orbit already has the full ambient cardinality `i + 1`, so it spans.
  simpa [orbit] using
    horbit.span_eq_top_of_card_eq_finrank' (by
      rw [Fintype.card_fin, finrank_binary_form_homogeneousSubmodule (K := K) i])

/-- Exercise 16-16.3-9: if `V` has dimension `2` over `𝔽_p` and `i < p`, then for every
algebraically closed extension field `K` of `𝔽_p`, the natural representation of `SL(V)` on the
`i`th symmetric power of `K ⊗[𝔽_p] V` is irreducible. This is the statement that the modular
representation on `V_i = Sym^i(V)` is absolutely irreducible. -/
theorem specialLinearNthSymmetricPower_isAbsolutelyIrreducible_of_finrank_eq_two
    [IsAlgClosed K]
    (hV : Module.finrank (ZMod p) V = 2)
    {i : ℕ} (hi : i < p) :
    (nthSymmetricPower ρSLₖ i).IsIrreducible := by
  let eG := special_linear_group_standard_equiv_of_finrank_eq_two (V := V) hV
  let ρstd :
      Representation K (SpecialLinearGroup (ZMod p) (Fin 2 → ZMod p))
        (K ⊗[ZMod p] (Fin 2 → ZMod p)) :=
    Representation.scalarExtension
      (Representation.ofDistribMulAction (ZMod p)
        (SpecialLinearGroup (ZMod p) (Fin 2 → ZMod p)) (Fin 2 → ZMod p))
  have htransport :
      Nonempty (Representation.Equiv
        ((nthSymmetricPower ρSLₖ i).comp eG.symm.toMonoidHom)
        (nthSymmetricPower ρstd i)) :=
    special_linear_nthSymmetricPower_standard_equiv
      (V := V) (p := p) hV i
  let ρcoord :
      Representation K (SpecialLinearGroup (ZMod p) (Fin 2 → ZMod p)) (Fin 2 →₀ K) :=
    standard_sl2_coordinate_model (K := K) (p := p)
  have hstd :
      (nthSymmetricPower ρstd i).IsIrreducible := by
    have hstd_coord :
        Nonempty ((nthSymmetricPower ρstd i).Equiv (nthSymmetricPower ρcoord i)) := by
      rcases standard_sl2_coordinate_model_equiv (K := K) (p := p) with ⟨eCoord⟩
      -- First pass the carrier transport through `nthSymmetricPower`.
      simpa [ρcoord] using nthSymmetricPower_equiv_of_equiv (K := K) eCoord i
    have hcoord :
        (nthSymmetricPower ρcoord i).IsIrreducible := by
      have hcoord_bin :
          Nonempty ((nthSymmetricPower ρcoord i).Equiv
            (standard_sl2_binary_form_model (K := K) (p := p) i)) := by
        simpa [ρcoord] using
          standard_sl2_binary_form_model_equiv (K := K) (p := p) i
      have hbin :
          (standard_sl2_binary_form_model (K := K) (p := p) i).IsIrreducible := by
        -- Route correction: the transport to LinearRepresentations_Serre_1977's binary-form carrier is explicit, so the last
        -- step is LinearRepresentations_Serre_1977's highest-weight argument on binary forms.
        have hfixed :
            ∀ W : Subrepresentation (standard_sl2_binary_form_model (K := K) (p := p) i),
              W ≠ ⊥ →
                ∃ f ∈ W.toSubmodule, f ≠ 0 ∧
                  ∀ a : ZMod p,
                    (standard_sl2_binary_form_model (K := K) (p := p) i)
                      (upper_unipotent (p := p) a) f = f :=
          nonzero_subrepresentation_has_upper_fixed_vector (K := K) (p := p) i
        letI : Nontrivial (MvPolynomial.homogeneousSubmodule (Fin 2) K i) := by
          refine ⟨⟨0, highest_binary_form (K := K) i, ?_⟩⟩
          simpa [ne_comm] using highest_binary_form_ne_zero (K := K) i
        letI :
            Nontrivial
              (Subrepresentation (standard_sl2_binary_form_model (K := K) (p := p) i)) := by
          refine ⟨⟨⊥, ⊤, ?_⟩⟩
          intro hbot_top
          have hmem :
              highest_binary_form (K := K) i ∈
                (⊥ :
                  Subrepresentation
                    (standard_sl2_binary_form_model (K := K) (p := p) i)).toSubmodule := by
            have htop_mem :
                highest_binary_form (K := K) i ∈
                  (⊤ :
                    Subrepresentation
                      (standard_sl2_binary_form_model (K := K) (p := p) i)).toSubmodule := by
              exact Submodule.mem_top
            simpa [hbot_top] using htop_mem
          exact (highest_binary_form_ne_zero (K := K) i) (by simpa using hmem)
        refine IsSimpleOrder.of_forall_eq_top ?_
        intro W hW
        rcases hfixed W hW with ⟨f, hfW, hf0, hfix_all⟩
        have hfix_one :
            (standard_sl2_binary_form_model (K := K) (p := p) i)
              (upper_unipotent (p := p) (1 : ZMod p)) f = f :=
          hfix_all (1 : ZMod p)
        rcases upper_unipotent_one_fixed_eq_smul_highest_binary_form
            (K := K) (p := p) (i := i) hi hfix_one with ⟨c, hfc⟩
        have hc : c ≠ 0 := by
          intro hc
          apply hf0
          simpa [hc] using hfc
        have hhighest_mem :
            highest_binary_form (K := K) i ∈ W.toSubmodule := by
          -- The nonzero fixed vector spans the same line as the highest-weight vector.
          have hsmul_mem : c • highest_binary_form (K := K) i ∈ W.toSubmodule := by
            simpa [hfc] using hfW
          exact (W.toSubmodule.smul_mem_iff hc).mp hsmul_mem
        let orbit : Fin (i + 1) → MvPolynomial.homogeneousSubmodule (Fin 2) K i := fun a ↦
          (standard_sl2_binary_form_model (K := K) (p := p) i)
            (lower_unipotent (p := p) ((a : ℕ) : ZMod p))
            (highest_binary_form (K := K) i)
        have horbit_mem :
            ∀ a : Fin (i + 1), orbit a ∈ W.toSubmodule := by
          intro a
          -- Subrepresentations are stable under the lower-unipotent action.
          exact W.apply_mem_toSubmodule
            (lower_unipotent (p := p) ((a : ℕ) : ZMod p)) hhighest_mem
        have hspan_le :
            Submodule.span K (Set.range orbit) ≤ W.toSubmodule := by
          refine Submodule.span_le.mpr ?_
          rintro _ ⟨a, rfl⟩
          exact horbit_mem a
        have htop_le :
            (⊤ : Submodule K (MvPolynomial.homogeneousSubmodule (Fin 2) K i)) ≤ W.toSubmodule := by
          rw [← lower_unipotent_highest_binary_form_orbit_span_eq_top
            (K := K) (p := p) (i := i) hi]
          simpa [orbit] using hspan_le
        apply Subrepresentation.toSubmodule_injective
        exact top_le_iff.mp htop_le
      letI : (standard_sl2_binary_form_model (K := K) (p := p) i).IsIrreducible := hbin
      exact
        Representation.isIrreducible_of_nonempty_equiv
          (ρ := standard_sl2_binary_form_model (K := K) (p := p) i)
          (σ := nthSymmetricPower ρcoord i)
          ⟨(Classical.choice hcoord_bin).symm⟩
    letI : (nthSymmetricPower ρcoord i).IsIrreducible := hcoord
    exact
      Representation.isIrreducible_of_nonempty_equiv
        (ρ := nthSymmetricPower ρcoord i)
        (σ := nthSymmetricPower ρstd i)
        ⟨(Classical.choice hstd_coord).symm⟩
  have hcomp :
      Representation.IsIrreducible ((nthSymmetricPower ρSLₖ i).comp eG.symm.toMonoidHom) := by
    letI : (nthSymmetricPower ρstd i).IsIrreducible := hstd
    exact
      Representation.isIrreducible_of_nonempty_equiv
        (ρ := nthSymmetricPower ρstd i)
        (σ := (nthSymmetricPower ρSLₖ i).comp eG.symm.toMonoidHom)
        ⟨(Classical.choice htransport).symm⟩
  letI :
      Representation.IsIrreducible ((nthSymmetricPower ρSLₖ i).comp eG.symm.toMonoidHom) := hcomp
  have hback :
      Representation.IsIrreducible
        (((nthSymmetricPower ρSLₖ i).comp eG.symm.toMonoidHom).comp eG.toMonoidHom) :=
    isIrreducible_comp_of_mulEquiv_local (K := K) eG
      ((nthSymmetricPower ρSLₖ i).comp eG.symm.toMonoidHom)
  letI :
      Representation.IsIrreducible
        (((nthSymmetricPower ρSLₖ i).comp eG.symm.toMonoidHom).comp eG.toMonoidHom) := hback
  have hcomp_id :
      Nonempty
        (Representation.Equiv
          (((nthSymmetricPower ρSLₖ i).comp eG.symm.toMonoidHom).comp eG.toMonoidHom)
          (nthSymmetricPower ρSLₖ i)) := by
    refine ⟨Representation.Equiv.mk (LinearEquiv.refl K _) ?_⟩
    intro g
    ext x
    simp [eG]
  -- The double precomposition is canonically the original representation because
  -- `eG.symm * eG = id`.
  exact
    Representation.isIrreducible_of_nonempty_equiv
      (ρ := (((nthSymmetricPower ρSLₖ i).comp eG.symm.toMonoidHom).comp eG.toMonoidHom))
      (σ := nthSymmetricPower ρSLₖ i)
      hcomp_id

end ScalarExtension

/-- Helper for Exercise 16-16.3-9: the modulus `7` is prime, so `ZMod 7` carries its canonical
field structure. -/
instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

section ModSevenExample

variable {V : Type} [AddCommGroup V] [Module (ZMod 7) V]

local notation "G₇" => SpecialLinearGroup (ZMod 7) V
local notation "ρSL₇" =>
  Representation.ofDistribMulAction (ZMod 7) G₇ V

/-- Helper for Exercise 16-16.3-9: an isomorphism in `FDRep` preserves the underlying
dimension. -/
theorem fdRep_finrank_eq_of_iso
    {k : Type} [Field k] {H : Type} [Group H]
    (X Y : FDRep k H) (e : X ≅ Y) :
    Module.finrank k X = Module.finrank k Y := by
  -- Forgetting the equivariant structure gives a linear equivalence of the carriers.
  simpa using (FDRep.isoToLinearEquiv e).finrank_eq

/-- Helper for Exercise 16-16.3-9: an equivariant identification after scalar extension preserves
the degree of the original residue-field representation. -/
theorem finrank_eq_of_scalarExtension_equiv
    {k : Type} [Field k] [Algebra k (ZMod 7)]
    {H : Type} [Group H]
    (T : FDRep k H)
    {W : Type} [AddCommGroup W] [Module (ZMod 7) W] [FiniteDimensional (ZMod 7) W]
    {σ : Representation (ZMod 7) H W}
    (e : Representation.Equiv ((FDRep.scalarExtension (k := ZMod 7) T).ρ) σ) :
    Module.finrank k T = Module.finrank (ZMod 7) W := by
  have hBaseChange :
      Module.finrank k T =
        Module.finrank (ZMod 7) (FDRep.scalarExtension (k := ZMod 7) T) := by
    -- Scalar extension only changes the coefficients, not the linear-algebra dimension formula.
    exact (Module.finrank_baseChange (R := ZMod 7) (S := k) (M' := T)).symm
  have hIso :
      FDRep.of ((FDRep.scalarExtension (k := ZMod 7) T).ρ) ≅ FDRep.of σ :=
    Action.mkIso e.toLinearEquiv.toFGModuleCatIso fun g ↦ by
      ext x
      exact LinearMap.congr_fun (e.isIntertwining' g) x
  calc
    Module.finrank k T = Module.finrank (ZMod 7) (FDRep.scalarExtension (k := ZMod 7) T) :=
      hBaseChange
    _ = Module.finrank (ZMod 7) (FDRep.of σ) := by
      -- Repackage the intertwiner as an isomorphism of finite-dimensional representations.
      simpa [FDRep.scalarExtension] using
        fdRep_finrank_eq_of_iso
          (FDRep.scalarExtension (k := ZMod 7) T) (FDRep.of σ) hIso
    _ = Module.finrank (ZMod 7) W := by
      rfl

/-- Helper for Exercise 16-16.3-9: an isomorphism from a lattice reduction to `T` preserves the
reduction degree. -/
theorem reduction_finrank_eq_of_iso
    {A : Type} [CommRing A] [IsLocalRing A]
    {H : Type} [Group H]
    {E : Type} [AddCommGroup E] [Module (IsLocalRing.ResidueField A) E]
    [Module.Finite (IsLocalRing.ResidueField A) E]
    {ρ : Representation (IsLocalRing.ResidueField A) H E}
    (T : FDRep (IsLocalRing.ResidueField A) H)
    (e : FDRep.of ρ ≅ T) :
    Module.finrank (IsLocalRing.ResidueField A) E =
      Module.finrank (IsLocalRing.ResidueField A) T := by
  -- Again, forget the representation structure and compare vector-space dimensions.
  simpa using (FDRep.isoToLinearEquiv e).finrank_eq

/-- Helper for Exercise 16-16.3-9: if `V` has dimension `2` over `𝔽_7`, then `SL(V)` has order
`336`. -/
theorem special_linear_group_card_eq_336_of_finrank_eq_two
    [FiniteDimensional (ZMod 7) V]
    (hV : Module.finrank (ZMod 7) V = 2) :
    Nat.card G₇ = 336 := by
  let eSL := special_linear_group_matrix_equiv_of_finrank_eq_two (V := V) hV
  let detHom : GL (Fin 2) (ZMod 7) →* (ZMod 7)ˣ := Matrix.GeneralLinearGroup.det
  have hcard_gl : Nat.card (GL (Fin 2) (ZMod 7)) = 2016 := by
    calc
      Nat.card (GL (Fin 2) (ZMod 7))
          = ∏ i : Fin 2, (7 ^ 2 - 7 ^ (i : ℕ)) := by
              simpa using Matrix.card_GL_field (n := 2) (𝔽 := ZMod 7)
      _ = 2016 := by decide
  have hdet_surj : Function.Surjective detHom := by
    intro u
    refine ⟨Matrix.GeneralLinearGroup.mk'' !![(u : ZMod 7), 0; 0, 1] ?_, ?_⟩
    · refine ⟨u, ?_⟩
      simp
    · apply Units.ext
      simp [detHom, Matrix.det_fin_two]
  have hcard_range : Nat.card detHom.range = 6 := by
    rw [MonoidHom.range_eq_top.2 hdet_surj]
    calc
      Nat.card ((⊤ : Subgroup (ZMod 7)ˣ)) = Nat.card ((ZMod 7)ˣ) := by
        exact Nat.card_congr Subgroup.topEquiv.toEquiv
      _ = 6 := by
        rw [Nat.card_units, Nat.card_zmod]
  have hcard_ker :
      Nat.card detHom.ker = Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)) := by
    let e : detHom.ker ≃ Matrix.SpecialLinearGroup (Fin 2) (ZMod 7) :=
      { toFun := fun g ↦
          ⟨(g.1 : Matrix (Fin 2) (Fin 2) (ZMod 7)), by
            simpa [detHom] using congrArg Units.val g.2⟩
        invFun := fun g ↦
          ⟨(g : GL (Fin 2) (ZMod 7)), by
            simp [detHom]⟩
        left_inv := by
          intro g
          apply Subtype.ext
          exact Matrix.GeneralLinearGroup.ext fun i j ↦ rfl
        right_inv := by
          intro g
          apply Matrix.SpecialLinearGroup.ext
          intro i j
          rfl }
    exact Nat.card_congr e
  have hker_mul_range :
      Nat.card detHom.ker * Nat.card detHom.range = Nat.card (GL (Fin 2) (ZMod 7)) := by
    calc
      Nat.card detHom.ker * Nat.card detHom.range
          = Nat.card detHom.ker * detHom.ker.index := by
              rw [Subgroup.index_ker]
      _ = Nat.card (GL (Fin 2) (ZMod 7)) := detHom.ker.card_mul_index
  have hcard_matrix_sl : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)) = 336 := by
    rw [hcard_ker] at hker_mul_range
    rw [hcard_range, hcard_gl] at hker_mul_range
    omega
  -- Transport the abstract special linear group to the standard matrix model.
  calc
    Nat.card G₇ = Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)) := by
      exact Nat.card_congr eSL.toEquiv
    _ = 336 := hcard_matrix_sl

/-- Helper for Exercise 16-16.3-9: for a two-dimensional `𝔽_7`-space, the order of `SL(V)` is
not divisible by `5`. -/
theorem five_not_dvd_special_linear_group_card_of_finrank_eq_two
    [FiniteDimensional (ZMod 7) V]
    (hV : Module.finrank (ZMod 7) V = 2) :
    ¬ 5 ∣ Nat.card G₇ := by
  -- Reduce to the explicit order computation.
  rw [special_linear_group_card_eq_336_of_finrank_eq_two hV]
  norm_num

/-- Helper for Exercise 16-16.3-9: every two-dimensional `𝔽_7`-space has fourth symmetric power
of dimension `5`. -/
theorem sym4_degree_eq_five
    (hV : Module.finrank (ZMod 7) V = 2) :
    Module.finrank (ZMod 7) (Sym[ZMod 7]^4 V) = 5 := by
  letI : FiniteDimensional (ZMod 7) V := finiteDimensional_of_finrank_eq_two hV
  let eFin : Fin (Module.finrank (ZMod 7) V) ≃ Fin 2 := by
    simpa [hV] using (_root_.Equiv.refl (Fin 2))
  let b : Module.Basis (Fin 2) (ZMod 7) V := (Module.finBasis (ZMod 7) V).reindex eFin
  let e : V ≃ₗ[(ZMod 7)] (Fin 2 → ZMod 7) := b.equivFun
  let f := SymmetricPower.map 4 e.toLinearMap
  let g := SymmetricPower.map 4 e.symm.toLinearMap
  have hleft : g.comp f = LinearMap.id := by
    -- The symmetric-power functor carries inverse linear equivalences to inverse endomorphisms.
    calc
      g.comp f = SymmetricPower.map 4 (e.symm.toLinearMap.comp e.toLinearMap) := by
        rw [← SymmetricPower.map_comp 4 e.toLinearMap e.symm.toLinearMap]
      _ = SymmetricPower.map 4 LinearMap.id := by
        congr
        ext x
        simp
      _ = LinearMap.id := SymmetricPower.map_id 4
  have hright : f.comp g = LinearMap.id := by
    calc
      f.comp g = SymmetricPower.map 4 (e.toLinearMap.comp e.symm.toLinearMap) := by
        rw [← SymmetricPower.map_comp 4 e.symm.toLinearMap e.toLinearMap]
      _ = SymmetricPower.map 4 LinearMap.id := by
        congr
        ext x
        simp
      _ = LinearMap.id := SymmetricPower.map_id 4
  let esym : Sym[ZMod 7]^4 V ≃ₗ[(ZMod 7)] Sym[ZMod 7]^4 (Fin 2 → ZMod 7) :=
    LinearEquiv.ofBijective f ⟨by
      intro x y hxy
      calc
        x = g (f x) := by
              symm
              exact LinearMap.congr_fun hleft x
        _ = g (f y) := by rw [hxy]
        _ = y := LinearMap.congr_fun hleft y,
      by
      intro y
      refine ⟨g y, ?_⟩
      exact LinearMap.congr_fun hright y⟩
  let eCoord : (Fin 2 →₀ ZMod 7) ≃ₗ[(ZMod 7)] (Fin 2 → ZMod 7) :=
    Finsupp.linearEquivFunOnFinite (ZMod 7) (ZMod 7) (Fin 2)
  let fCoord := SymmetricPower.map 4 eCoord.toLinearMap
  let gCoord := SymmetricPower.map 4 eCoord.symm.toLinearMap
  have hleftCoord : gCoord.comp fCoord = LinearMap.id := by
    calc
      gCoord.comp fCoord =
          SymmetricPower.map 4 (eCoord.symm.toLinearMap.comp eCoord.toLinearMap) := by
            rw [← SymmetricPower.map_comp 4 eCoord.toLinearMap eCoord.symm.toLinearMap]
      _ = SymmetricPower.map 4 LinearMap.id := by
            congr
            ext x
            simp
      _ = LinearMap.id := SymmetricPower.map_id 4
  have hrightCoord : fCoord.comp gCoord = LinearMap.id := by
    calc
      fCoord.comp gCoord =
          SymmetricPower.map 4 (eCoord.toLinearMap.comp eCoord.symm.toLinearMap) := by
            rw [← SymmetricPower.map_comp 4 eCoord.symm.toLinearMap eCoord.toLinearMap]
      _ = SymmetricPower.map 4 LinearMap.id := by
            simp
      _ = LinearMap.id := SymmetricPower.map_id 4
  let eCoordSym :
      Sym[ZMod 7]^4 (Fin 2 →₀ ZMod 7) ≃ₗ[(ZMod 7)] Sym[ZMod 7]^4 (Fin 2 → ZMod 7) :=
    LinearEquiv.ofBijective fCoord ⟨by
      intro x y hxy
      calc
        x = gCoord (fCoord x) := by
              symm
              exact LinearMap.congr_fun hleftCoord x
        _ = gCoord (fCoord y) := by rw [hxy]
        _ = y := LinearMap.congr_fun hleftCoord y,
      by
      intro y
      refine ⟨gCoord y, ?_⟩
      exact LinearMap.congr_fun hrightCoord y⟩
  -- Transport the standard symmetric-power dimension formula along the chosen basis.
  calc
    Module.finrank (ZMod 7) (Sym[ZMod 7]^4 V) =
        Module.finrank (ZMod 7) (Sym[ZMod 7]^4 (Fin 2 → ZMod 7)) := esym.finrank_eq
    _ = Module.finrank (ZMod 7) (Sym[ZMod 7]^4 (Fin 2 →₀ ZMod 7)) := by
      symm
      exact eCoordSym.finrank_eq
    _ = 5 := by
      simpa using finrank_standard_coordinate_symmetricPower (K := ZMod 7) 4

/-- Helper for Exercise 16-16.3-9: over an algebraically closed characteristic-zero field, a
simple `SL(V)`-representation of degree `5` contradicts the Chapter `6` divisibility theorem when
`dim V = 2` over `𝔽_7`. -/
theorem simple_fdRep_degree_five_absurd_of_finrank_eq_two
    {K : Type} [Field K] [CharZero K] [IsAlgClosed K]
    (X : FDRep K G₇) [CategoryTheory.Simple X]
    [FiniteDimensional (ZMod 7) V]
    (hV : Module.finrank (ZMod 7) V = 2)
    (hX : Module.finrank K X = 5) :
    False := by
  let eSL := special_linear_group_matrix_equiv_of_finrank_eq_two (V := V) hV
  letI : Finite G₇ :=
    Finite.of_equiv (Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)) eSL.symm.toEquiv
  letI : Representation.IsIrreducible X.ρ := by
    simpa using (FDRep.isIrreducible_of_simple X)
  have hdiv : Module.finrank K X ∣ Nat.card G₇ := by
    -- In characteristic zero, an irreducible degree divides the group order.
    simpa using (finrank_dvd_card (ρ := X.ρ))
  have hfive : ¬ 5 ∣ Nat.card G₇ :=
    five_not_dvd_special_linear_group_card_of_finrank_eq_two (V := V) hV
  rw [hX] at hdiv
  exact hfive hdiv

/-- LinearRepresentations_Serre_1977's parenthetical example: when `p = 7` and `dim V = 2`, the fourth symmetric-power
representation of `SL(V)` over `𝔽_7` is not obtained, even up to equivariant identification, by
scalar extension from any residue-field representation that satisfies the Chapter `16` lift owner
`FDRep.HasRPrimeLift` through a sufficiently large characteristic-zero fraction field, once the
usual stable-lattice degree comparison is available. -/
theorem specialLinearFourthSymmetricPowerModSeven_not_rPrimeLiftable
    (hV : Module.finrank (ZMod 7) V = 2)
    {A : Type} [CommRing A] [IsLocalRing A]
    {K : Type} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] [IsAlgClosed K]
    [Algebra (IsLocalRing.ResidueField A) (ZMod 7)]
    (hBridge :
      ∀ {X : FDRep K G₇} [CategoryTheory.Simple X] (L : StableLattice A X.ρ),
        Module.finrank K X = Module.finrank (IsLocalRing.ResidueField A) L.reduction) :
    ¬ ∃ T : FDRep (IsLocalRing.ResidueField A) G₇,
        FDRep.HasRPrimeLift T K ∧
          Nonempty (Representation.Equiv
            (FDRep.scalarExtension T).ρ (nthSymmetricPower ρSL₇ 4)) := by
  intro hLift
  rcases hLift with ⟨T, hT, hEquiv⟩
  rcases hT with ⟨X, hXsimple, L, hReduction⟩
  letI : CategoryTheory.Simple X := hXsimple
  letI : FiniteDimensional (ZMod 7) V := finiteDimensional_of_finrank_eq_two hV
  have hReductionDim :
      Module.finrank (IsLocalRing.ResidueField A) L.reduction =
        Module.finrank (IsLocalRing.ResidueField A) T := by
    -- The reduced lattice and `T` are isomorphic as residue-field representations.
    rcases hReduction with ⟨e⟩
    simpa using reduction_finrank_eq_of_iso (T := T) e
  have hTdim :
      Module.finrank (IsLocalRing.ResidueField A) T =
        Module.finrank (ZMod 7) (Sym[ZMod 7]^4 V) := by
    -- Scalar extension identifies `T` with the actual fourth symmetric power.
    rcases hEquiv with ⟨e⟩
    simpa using finrank_eq_of_scalarExtension_equiv (T := T) e
  have hReductionFive :
      Module.finrank (IsLocalRing.ResidueField A) L.reduction = 5 := by
    calc
      Module.finrank (IsLocalRing.ResidueField A) L.reduction =
          Module.finrank (IsLocalRing.ResidueField A) T := hReductionDim
      _ = Module.finrank (ZMod 7) (Sym[ZMod 7]^4 V) := hTdim
      _ = 5 := sym4_degree_eq_five (V := V) hV
  have hXfive : Module.finrank K X = 5 := by
    rw [hBridge L, hReductionFive]
  exact
    simple_fdRep_degree_five_absurd_of_finrank_eq_two
      (V := V) (X := X) hV hXfive

/-- Bridge companion to
`specialLinearFourthSymmetricPowerModSeven_not_rPrimeLiftable`: a fixed residue-field
representation with an `(R')`-lift still cannot have scalar extension equivariantly identified
with `Sym⁴(V)`. -/
theorem specialLinearFourthSymmetricPowerModSeven_not_equiv_scalarExtension_of_hasRPrimeLift
    (hV : Module.finrank (ZMod 7) V = 2)
    {A : Type} [CommRing A] [IsLocalRing A]
    {K : Type} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] [IsAlgClosed K]
    [Algebra (IsLocalRing.ResidueField A) (ZMod 7)]
    (hBridge :
      ∀ {X : FDRep K G₇} [CategoryTheory.Simple X] (L : StableLattice A X.ρ),
        Module.finrank K X = Module.finrank (IsLocalRing.ResidueField A) L.reduction)
    (T : FDRep (IsLocalRing.ResidueField A) G₇) (hT : FDRep.HasRPrimeLift T K) :
    ¬ Nonempty (Representation.Equiv
      (FDRep.scalarExtension T).ρ (nthSymmetricPower ρSL₇ 4)) := by
  intro hEquiv
  -- Feed the fixed residue-field object into the already established global obstruction.
  exact
    specialLinearFourthSymmetricPowerModSeven_not_rPrimeLiftable
      (V := V) (A := A) (K := K) hV hBridge ⟨T, hT, hEquiv⟩

end ModSevenExample

end SpecialLinear

end Representation
