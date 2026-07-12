import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Theorem_2_2_3_5
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_6_3.Shared

noncomputable section

open scoped MatrixGroups

open Representation

local notation "A5" => alternatingGroup (Fin 5)
local notation "𝔽₄" => FiniteField.Extension (ZMod 2) 2 2

/-- Helper for Exercise 18-18.6-3: the alternating group `A₅` has order `60`. -/
private theorem alternating_group_fin5_card_eq_sixty :
    Nat.card A5 = 60 := by
  -- Reduce to the computable `Fintype.card` of permutations on five letters.
  simpa using (show Fintype.card A5 = 60 by decide)

/-- Helper for Exercise 18-18.6-3: the chosen finite field `𝔽₄` has cardinality `4`. -/
private theorem finite_field_f4_card_eq_four :
    Nat.card 𝔽₄ = 4 := by
  -- Unfold the chosen extension field only far enough to use the generic finite-field formula.
  simpa using (FiniteField.natCard_extension (k := ZMod 2) (p := 2) (n := 2))

/-- Helper for Exercise 18-18.6-3: the special linear group `SL(2, 𝔽₄)` has order `60`. -/
private theorem specialLinearGroup_fin_two_f4_card_eq_sixty :
    Nat.card (SL(2, 𝔽₄)) = 60 := by
  letI : Fintype 𝔽₄ := Fintype.ofFinite 𝔽₄
  letI : DecidableEq 𝔽₄ := Classical.decEq 𝔽₄
  let detHom : GL (Fin 2) 𝔽₄ →* 𝔽₄ˣ := Matrix.GeneralLinearGroup.det
  have hcard_gl : Nat.card (GL (Fin 2) 𝔽₄) = 180 := by
    -- Compute `|GL(2, 𝔽₄)|` from the standard finite-field product formula.
    calc
      Nat.card (GL (Fin 2) 𝔽₄)
          = ∏ i : Fin 2, (Fintype.card 𝔽₄ ^ 2 - Fintype.card 𝔽₄ ^ (i : ℕ)) := by
            simpa using Matrix.card_GL_field (𝔽 := 𝔽₄) 2
      _ = ∏ i : Fin 2, (4 ^ 2 - 4 ^ (i : ℕ)) := by
            refine Finset.prod_congr rfl ?_
            intro i _
            rw [← Nat.card_eq_fintype_card, finite_field_f4_card_eq_four]
      _ = 180 := by decide
  have hdet_surj : Function.Surjective detHom := by
    -- Diagonal matrices `diag(u, 1)` realize every determinant value.
    intro u
    refine ⟨Matrix.GeneralLinearGroup.mk'' !![(u : 𝔽₄), 0; 0, 1] ?_, ?_⟩
    · refine ⟨u, ?_⟩
      simp
    · apply Units.ext
      simp [detHom, Matrix.det_fin_two]
  have hcard_range : Nat.card detHom.range = 3 := by
    rw [MonoidHom.range_eq_top.2 hdet_surj]
    calc
      Nat.card ((⊤ : Subgroup 𝔽₄ˣ)) = Nat.card (𝔽₄ˣ) := by
        exact Nat.card_congr Subgroup.topEquiv.toEquiv
      _ = 3 := by
        rw [Nat.card_units, finite_field_f4_card_eq_four]
  have hcard_ker :
      Nat.card detHom.ker = Nat.card (SL(2, 𝔽₄)) := by
    -- Identify `SL(2, 𝔽₄)` with the determinant kernel inside `GL(2, 𝔽₄)`.
    let e : detHom.ker ≃ SL(2, 𝔽₄) :=
      { toFun := fun g ↦
          ⟨(g.1 : Matrix (Fin 2) (Fin 2) 𝔽₄), by
            simpa [detHom] using congrArg Units.val g.2⟩
        invFun := fun g ↦
          ⟨(g : GL (Fin 2) 𝔽₄), by
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
      Nat.card detHom.ker * Nat.card detHom.range = Nat.card (GL (Fin 2) 𝔽₄) := by
    calc
      Nat.card detHom.ker * Nat.card detHom.range
          = Nat.card detHom.ker * detHom.ker.index := by
              rw [Subgroup.index_ker]
      _ = Nat.card (GL (Fin 2) 𝔽₄) := detHom.ker.card_mul_index
  have hcard_kernel_sixty : Nat.card detHom.ker = 60 := by
    -- Divide the general linear order by `|𝔽₄ˣ| = 3`.
    have hker_eq : Nat.card detHom.ker * 3 = 180 := by
      rw [← hcard_range, hker_mul_range, hcard_gl]
    omega
  rw [← hcard_ker]
  exact hcard_kernel_sixty

/-- Helper for Exercise 18-18.6-3: once `A₅` is embedded in `SL(2, 𝔽₄)`, the order comparison
forces the embedding to be surjective and hence an isomorphism. -/
private theorem alternatingGroup_fin5_mulEquiv_sl2_f4_of_injective
    (φ : A5 →* SL(2, 𝔽₄)) (hφ : Function.Injective φ) :
    Nonempty (A5 ≃* SL(2, 𝔽₄)) := by
  letI : Fintype 𝔽₄ := Fintype.ofFinite 𝔽₄
  letI : DecidableEq 𝔽₄ := Classical.decEq 𝔽₄
  letI : Fintype (SL(2, 𝔽₄)) := Fintype.ofFinite (SL(2, 𝔽₄))
  have hcard_dom : Fintype.card A5 = Fintype.card (SL(2, 𝔽₄)) := by
    -- Compare both groups with the shared cardinal `60`.
    rw [← Nat.card_eq_fintype_card, alternating_group_fin5_card_eq_sixty]
    rw [← Nat.card_eq_fintype_card, specialLinearGroup_fin_two_f4_card_eq_sixty]
  have hφ_surj : Function.Surjective φ := by
    exact ((Fintype.bijective_iff_injective_and_card φ).2 ⟨hφ, hcard_dom⟩).2
  exact ⟨MulEquiv.ofBijective φ ⟨hφ, hφ_surj⟩⟩

/-- Helper for Exercise 18-18.6-3: the determinant character of any `A₅ → GL(2, 𝔽₄)` hom is
trivial. -/
private theorem alternatingGroup_fin5_det_comp_gl2_eq_one
    (φ : A5 →* GL (Fin 2) 𝔽₄) :
    Matrix.GeneralLinearGroup.det.comp φ = 1 := by
  -- Compose with determinant and use that every `A₅ → 𝔽₄ˣ` character is trivial.
  exact Representation.alternatingGroup_fin5_units_hom_eq_one_over_any_field
    (L := 𝔽₄) (Matrix.GeneralLinearGroup.det.comp φ)

/-- Helper for Exercise 18-18.6-3: an injective hom `A₅ → GL(2, 𝔽₄)` already lands in
`SL(2, 𝔽₄)`, so the order comparison yields the desired group isomorphism. -/
private theorem alternatingGroup_fin5_mulEquiv_sl2_f4_of_gl2_injective
    (φ : A5 →* GL (Fin 2) 𝔽₄) (hφ : Function.Injective φ) :
    Nonempty (A5 ≃* SL(2, 𝔽₄)) := by
  let ψ : A5 →* SL(2, 𝔽₄) :=
    { toFun := fun g ↦
        ⟨(φ g : Matrix (Fin 2) (Fin 2) 𝔽₄), by
          -- The determinant side-condition is exactly the trivial determinant character.
          have hdetg : Matrix.GeneralLinearGroup.det (φ g) = 1 := by
            simpa using congrArg (fun f : A5 →* 𝔽₄ˣ => f g)
              (alternatingGroup_fin5_det_comp_gl2_eq_one φ)
          exact congrArg Units.val hdetg⟩
      map_one' := by
        -- Equality in `SL(2, 𝔽₄)` is checked entrywise on underlying matrices.
        apply Matrix.SpecialLinearGroup.ext
        intro i j
        simp
      map_mul' := by
        -- The underlying matrices multiply exactly as they do in `GL(2, 𝔽₄)`.
        intro g h
        apply Matrix.SpecialLinearGroup.ext
        intro i j
        simp }
  have hψ : Function.Injective ψ := by
    intro g h hgh
    apply hφ
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    have hmat :
        ((ψ g : SL(2, 𝔽₄)) : Matrix (Fin 2) (Fin 2) 𝔽₄) =
          ((ψ h : SL(2, 𝔽₄)) : Matrix (Fin 2) (Fin 2) 𝔽₄) := by
      -- Read the equality in `SL(2, 𝔽₄)` on the underlying matrices.
      simpa using congrArg (fun x : SL(2, 𝔽₄) => (x : Matrix (Fin 2) (Fin 2) 𝔽₄)) hgh
    simpa [ψ] using congrArg (fun A : Matrix (Fin 2) (Fin 2) 𝔽₄ => A i j) hmat
  exact alternatingGroup_fin5_mulEquiv_sl2_f4_of_injective ψ hψ

/-- Helper for Exercise 18-18.6-3: a two-dimensional trivial `A₅`-action over any field is
reducible, because the line spanned by the first basis vector is a proper stable
subrepresentation. -/
private theorem trivial_action_fin_two_not_irreducible_over_any_field
    {k : Type*} [Field k]
    (ρ : Representation k A5 (Fin 2 → k))
    (htriv : ∀ g : A5, ρ g = 1) :
    ¬ ρ.IsIrreducible := by
  letI : DecidableEq k := Classical.decEq k
  let e0 : Fin 2 → k := Pi.single 0 1
  let W : Subrepresentation ρ :=
    { toSubmodule := Submodule.span k {e0}
      apply_mem_toSubmodule := by
        -- Under the trivial action, every vector stays fixed, so the chosen line is stable.
        intro g x hx
        simpa [htriv g] using hx }
  have hW_ne_bot : W ≠ ⊥ := by
    -- The first basis vector lies in the chosen line, so that line is nonzero.
    intro hW
    have he0_mem : e0 ∈ W.toSubmodule := Submodule.subset_span (by simp [e0])
    have he0_zero : e0 = 0 := by
      simpa [hW] using he0_mem
    have : (1 : k) = 0 := by
      simpa [e0] using congrFun he0_zero 0
    exact one_ne_zero this
  have hW_ne_top : W ≠ ⊤ := by
    -- The second basis vector does not lie in the first-coordinate line, so the line is proper.
    intro hW
    let e1 : Fin 2 → k := Pi.single 1 1
    have he1_mem : e1 ∈ W.toSubmodule := by
      simpa [hW] using
        (show e1 ∈ (⊤ : Submodule k (Fin 2 → k)) by simp [e1])
    rcases Submodule.mem_span_singleton.mp he1_mem with ⟨a, ha⟩
    have h0 : a = 0 := by
      simpa [e0, e1] using congrFun ha 0
    have hone : (1 : k) = 0 := by
      simpa [e0, e1, h0] using congrFun ha 1
    exact one_ne_zero hone
  intro hρ
  -- Route correction: once the action is known to be trivial, reducibility is a pure subspace
  -- statement and no longer depends on the coefficient field.
  exact hW_ne_top ((IsSimpleOrder.eq_bot_or_eq_top W).resolve_left hW_ne_bot)

/-- Helper for Exercise 18-18.6-3: the transported standard-plane model of a two-dimensional
irreducible `𝔽₄[A₅]`-representation gives an injective hom `A₅ → GL(2, 𝔽₄)`. -/
theorem alternatingGroup_fin5_mulEquiv_sl2_f4_of_source_witness
    (hsource :
      ∃ (W : Type) (_ : AddCommGroup W) (_ : Module 𝔽₄ W) (_ : FiniteDimensional 𝔽₄ W)
        (ρ : Representation 𝔽₄ A5 W),
        ρ.IsIrreducible ∧ Module.finrank 𝔽₄ W = 2) :
    Nonempty (A5 ≃* SL(2, 𝔽₄)) := by
  rcases hsource with ⟨W, _instAddCommGroupW, _instModuleW, _instFiniteDimensionalW,
      ρ, hρirr, hWdim⟩
  letI : ρ.IsIrreducible := hρirr
  let eFin : Fin (Module.finrank 𝔽₄ W) ≃ Fin 2 := by
    -- Reindex the canonical finite basis using the known dimension formula.
    simpa [hWdim] using (_root_.Equiv.refl (Fin 2))
  let b : Module.Basis (Fin 2) 𝔽₄ W := (Module.finBasis 𝔽₄ W).reindex eFin
  let eW : W ≃ₗ[𝔽₄] (Fin 2 → 𝔽₄) := b.equivFun
  let ρstd : Representation 𝔽₄ A5 (Fin 2 → 𝔽₄) :=
    { toFun := fun g ↦ eW.conj (ρ g)
      map_one' := by
        -- Conjugating the identity action by the basis equivalence stays the identity.
        ext x i
        simp [LinearEquiv.conj_apply_apply]
      map_mul' := by
        -- Conjugation preserves multiplication in the endomorphism ring.
        intro g h
        ext x i
        simp [LinearEquiv.conj_apply_apply] }
  have hρstd_equiv : ρ.Equiv ρstd :=
    Representation.Equiv.mk eW fun g => by
      -- The coordinate change is equivariant by construction of `ρstd`.
      ext x i
      simp [ρstd, LinearEquiv.conj_apply_apply]
  have hρstd_irreducible : ρstd.IsIrreducible := by
    -- Irreducibility is invariant under equivariant transport to the standard plane.
    exact Representation.isIrreducible_of_nonempty_equiv
      (ρ := ρ) (σ := ρstd) ⟨hρstd_equiv⟩
  letI : ρstd.IsIrreducible := hρstd_irreducible
  let ρGL : A5 →* LinearMap.GeneralLinearGroup 𝔽₄ (Fin 2 → 𝔽₄) :=
    { toFun := fun g ↦
        ⟨ρstd g, ρstd g⁻¹, by
          ext x i
          simp [ρstd]
        , by
          ext x i
          simp [ρstd]⟩
      map_one' := by
        -- The identity group element acts as the identity automorphism.
        apply Units.ext
        ext x i
        simp [ρstd]
      map_mul' := by
        -- Multiplication in the automorphism group matches composition of the transported action.
        intro g h
        apply Units.ext
        ext x i
        simp [ρstd, map_mul] }
  let φ : A5 →* GL (Fin 2) 𝔽₄ :=
    (Matrix.GeneralLinearGroup.toLin' (Pi.basisFun 𝔽₄ (Fin 2))).symm.toMonoidHom.comp ρGL
  have hφ_ker_ne_top : φ.ker ≠ ⊤ := by
    intro hker_top
    have htriv : ∀ g : A5, ρstd g = 1 := by
      intro g
      have hgker : g ∈ φ.ker := by
        simp [hker_top]
      have hφg : φ g = 1 := by
        simpa [MonoidHom.mem_ker] using hgker
      have hρGLg : ρGL g = 1 := by
        -- Applying the basis-dependent `GL₂ ↔ Aut` equivalence identifies `φ g` with `ρstd g`.
        simpa [φ] using congrArg
          (fun M : GL (Fin 2) 𝔽₄ =>
            Matrix.GeneralLinearGroup.toLin' (Pi.basisFun 𝔽₄ (Fin 2)) M)
          hφg
      simpa [ρGL] using congrArg
        (fun u : LinearMap.GeneralLinearGroup 𝔽₄ (Fin 2 → 𝔽₄) =>
          (u : (Fin 2 → 𝔽₄) →ₗ[𝔽₄] (Fin 2 → 𝔽₄)))
        hρGLg
    -- A top kernel would make the transported action trivial, contradicting irreducibility.
    exact (trivial_action_fin_two_not_irreducible_over_any_field (k := 𝔽₄) ρstd htriv)
      hρstd_irreducible
  have hφ_ker_eq_bot : φ.ker = ⊥ := by
    -- Simplicity of `A₅` leaves only the bottom or top kernel; the top case was excluded above.
    rcases Subgroup.Normal.eq_bot_or_eq_top (H := φ.ker)
        (inferInstance : φ.ker.Normal) with hbot | htop
    · exact hbot
    · exact False.elim (hφ_ker_ne_top htop)
  have hφ_injective : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hφ_ker_eq_bot
  exact alternatingGroup_fin5_mulEquiv_sl2_f4_of_gl2_injective φ hφ_injective
