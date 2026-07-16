import LinearRepresentations_Serre_1977.Serre.Chap16.Lemma_16_16_3_1.PositiveConeBridge

noncomputable section

universe u w

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra Representation TensorProduct ZeroObject

namespace Representation

section ResidueFieldPositiveSubsetHelpers

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

/-- Helper for Lemma 16-16.3-1: choose one representative of each isomorphism class of simple
finite-dimensional `k[G]`-representations. -/
private theorem exists_complete_pairwise_nonisomorphic_simple_family_over_field :
    ∃ (ι : Type (u + 1)) (π : ι → FDRep k G),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  let SimpleRep : Type (u + 1) := { τ : FDRep k G // Simple τ }
  let r : Setoid SimpleRep :=
    { r := fun a b ↦ Nonempty (a.1 ≅ b.1)
      iseqv :=
        ⟨fun a ↦ ⟨Iso.refl _⟩,
          fun {a b} hab ↦ by
            rcases hab with ⟨e⟩
            exact ⟨e.symm⟩,
          fun {a b c} hab hbc ↦ by
            rcases hab with ⟨eab⟩
            rcases hbc with ⟨ebc⟩
            exact ⟨eab.trans ebc⟩⟩ }
  let ι : Type (u + 1) := Quotient r
  let π : ι → FDRep k G := fun q ↦ (Quotient.out q).1
  have hπ_pairwise : PairwiseNonisomorphic π := by
    -- Isomorphic representatives define the same quotient class, so distinct classes stay
    -- pairwise nonisomorphic.
    intro q q' hqq' hIso
    rcases hIso with ⟨e⟩
    have hclasses : (⟦Quotient.out q⟧ : ι) = (⟦Quotient.out q'⟧ : ι) := by
      apply Quotient.sound
      exact ⟨e⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : ι) := (Quotient.out_eq q).symm
      _ = (⟦Quotient.out q'⟧ : ι) := hclasses
      _ = q' := Quotient.out_eq q'
  have hπ_complete : IsCompleteIrreducibleFamily π := by
    refine ⟨?_, ?_⟩
    · intro q
      exact (Quotient.out q).2
    · intro τ hτ
      let q : ι := ⟦⟨τ, hτ⟩⟧
      refine ⟨q, ?_⟩
      have hq :
          Nonempty (((Quotient.out q).1) ≅ τ) := by
        exact Quotient.exact (Quotient.out_eq q)
      rcases hq with ⟨e⟩
      exact ⟨e.symm⟩
  exact ⟨ι, π, hπ_pairwise, hπ_complete⟩

/-- Helper for Lemma 16-16.3-1: the source of a projective envelope of a simple module is cyclic,
hence finitely generated. -/
private theorem moduleFinite_of_projectiveEnvelope_simple
    {P M : Type u} [AddCommGroup P] [Module k[G] P]
    [AddCommGroup M] [Module k[G] M] [IsSimpleModule k[G] M]
    {f : P →ₗ[k[G]] M} (hf : f.IsProjectiveEnvelope) :
    Module.Finite k[G] P := by
  letI : Nontrivial M := IsSimpleModule.nontrivial (R := k[G]) (M := M)
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨x, hx⟩ := hf.surjective m
  let N : Submodule k[G] P := Submodule.span k[G] {x}
  have hmap_ne_bot : N.map f ≠ ⊥ := by
    intro hbot
    have hxmem : f x ∈ N.map f := by
      exact ⟨x, Submodule.mem_span_singleton_self x, rfl⟩
    have : f x = 0 := by
      rw [hbot] at hxmem
      simpa using hxmem
    exact hm <| by simpa [hx] using this
  have hmap_top : N.map f = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top (N.map f)).resolve_left hmap_ne_bot
  have hN_top : N = ⊤ := hf.toIsEssential.eq_top_of_map_eq_top N hmap_top
  -- Once the cyclic span is all of `P`, the singleton generator gives a surjection from `k[G]`.
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton k[G] P x) := by
    simpa [LinearMap.toSpanSingleton_apply] using
      (Submodule.span_singleton_eq_top_iff (R := k[G]) (x := x)).1 (by simpa [N] using hN_top)
  exact Module.Finite.of_surjective (LinearMap.toSpanSingleton k[G] P x) hsurj

/-- Helper for Lemma 16-16.3-1: every simple finite-dimensional `k[G]`-representation admits a
finite projective envelope in the category of `k[G]`-modules. -/
private theorem exists_finite_projectiveEnvelope_of_simple
    (τ : FDRep k G) [CategoryTheory.Simple τ] :
    ∃ P : FiniteProjectiveGroupAlgebraModule k G,
      ∃ f : P.V →ₗ[k[G]] asModule τ.ρ, f.IsProjectiveEnvelope := by
  let ρ : Representation k G τ := τ.ρ
  letI : Module k[G] τ := by
    simpa using (inferInstance : Module k[G] ρ.asModule)
  letI : Representation.IsIrreducible ρ := by
    simpa [ρ] using (FDRep.isIrreducible_of_simple τ)
  letI : IsSimpleModule k[G] τ := by
    -- Translate simplicity of the `FDRep` owner to simplicity of its `k[G]`-module.
    simpa [ρ] using (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  let M : ModuleCat k[G] := ModuleCat.of k[G] τ
  let _ : Module.Finite k k[G] := MonoidAlgebra.moduleFinite
  let _ : IsArtinianRing k[G] := IsArtinianRing.of_finite k k[G]
  obtain ⟨P', f', hf'⟩ := exists_isProjectiveEnvelope M
  have hfinite : Module.Finite k[G] P' :=
    moduleFinite_of_projectiveEnvelope_simple
      (P := P') (M := τ) (f := f'.hom) hf'
  let Pfg : FGModuleCat k[G] := by
    refine ⟨P', ?_⟩
    change Module.Finite k[G] P'
    exact hfinite
  have hproj : Module.Projective k[G] Pfg := by
    -- The Artinian projective envelope already carries projectivity on its source.
    change Module.Projective k[G] P'
    infer_instance
  let P : FiniteProjectiveGroupAlgebraModule k G := ⟨Pfg, hproj⟩
  refine ⟨P, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [ρ] using f'.hom
  -- Repackage the `ModuleCat` envelope as a linear-map envelope on the bundled finite projective
  -- source.
  simpa [P, ρ] using hf'

/-- Helper for Lemma 16-16.3-1: for `Representation.ofModule'`, the induced `k[G]`-action is the
original scalar action on the module. -/
private theorem ofModule'_asAlgebraHom_apply_local
    (M : Type u) [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (r : k[G]) (m : M) :
    ((Representation.ofModule' (k := k) (G := G) M).asAlgebraHom r) m = r • m := by
  refine MonoidAlgebra.induction_on
    (p := fun s : k[G] =>
      ((Representation.ofModule' (k := k) (G := G) M).asAlgebraHom s) m = s • m) r ?_ ?_ ?_
  · intro g
    simp [Representation.ofModule', MonoidAlgebra.of]
  · intro a b ha hb
    simp [ha, hb, add_smul]
  · intro a b hb
    simp [hb]

/-- Helper for Lemma 16-16.3-1: the owner module of `Representation.ofModule' M` is canonically
the original `k[G]`-module `M`. -/
private theorem nonempty_ofModule'_asModuleLinearEquiv_local
    (M : Type u) [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M] :
    Nonempty ((Representation.ofModule' (k := k) (G := G) M).asModule ≃ₗ[k[G]] M) := by
  let toFun : (Representation.ofModule' (k := k) (G := G) M).asModule → M :=
    fun x => (Representation.ofModule' (k := k) (G := G) M).asModuleEquiv x
  let invFun : M → (Representation.ofModule' (k := k) (G := G) M).asModule :=
    fun x => (Representation.ofModule' (k := k) (G := G) M).asModuleEquiv.symm x
  have hleft : Function.LeftInverse invFun toFun := by
    intro x
    simp [toFun, invFun]
  have hright : Function.RightInverse invFun toFun := by
    intro x
    simp [toFun, invFun]
  have hadd : ∀ x y, toFun (x + y) = toFun x + toFun y := by
    intro x y
    rfl
  have hsmul : ∀ (r : k[G]) x, toFun (r • x) = r • toFun x := by
    intro r x
    calc
      (Representation.ofModule' (k := k) (G := G) M).asModuleEquiv (r • x)
          = ((Representation.ofModule' (k := k) (G := G) M).asAlgebraHom r)
              ((Representation.ofModule' (k := k) (G := G) M).asModuleEquiv x) := by
                simpa using
                  (Representation.asModuleEquiv_map_smul
                    (ρ := Representation.ofModule' (k := k) (G := G) M) r x)
      _ = r • (Representation.ofModule' (k := k) (G := G) M).asModuleEquiv x := by
            simpa using
              (ofModule'_asAlgebraHom_apply_local
                (k := k) (G := G) M r
                ((Representation.ofModule' (k := k) (G := G) M).asModuleEquiv x))
  refine ⟨?_⟩
  exact
    { toFun := toFun
      invFun := invFun
      left_inv := hleft
      right_inv := hright
      map_add' := hadd
      map_smul' := hsmul }

/-- Helper for Lemma 16-16.3-1: a simple `k[G]`-module rebundled by `Representation.ofModule'`
is irreducible. -/
private theorem ofModule'_isIrreducible_of_isSimpleModule_local
    (M : Type u) [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    [IsSimpleModule k[G] M] :
    (Representation.ofModule' (k := k) (G := G) M).IsIrreducible := by
  rcases nonempty_ofModule'_asModuleLinearEquiv_local (k := k) (G := G) M with ⟨eM⟩
  exact
    (Representation.irreducible_iff_isSimpleModule_asModule
      (Representation.ofModule' (k := k) (G := G) M)).2
      (@IsSimpleModule.congr (k[G]) inferInstance
        ((Representation.ofModule' (k := k) (G := G) M).asModule)
        (Representation.ofModule' (k := k) (G := G) M).instAddCommGroupAsModule
        (Representation.ofModule' (k := k) (G := G) M).instModuleMonoidAlgebraAsModule
        M inferInstance inferInstance eM inferInstance)

/-- Helper for Lemma 16-16.3-1: an isomorphism of finite-dimensional `k[G]`-representations
induces a linear equivalence of the underlying `k[G]`-modules. -/
private theorem nonempty_asModuleLinearEquiv_of_nonempty_fdRepIso_local
    (τ σ : FDRep k G) (hτσ : Nonempty (τ ≅ σ)) :
    Nonempty (asModule τ.ρ ≃ₗ[k[G]] asModule σ.ρ) := by
  rcases hτσ with ⟨e⟩
  exact ⟨by
    simpa using
      (((forget₂ (FDRep k G) (Rep k G)) ⋙ Rep.toModuleMonoidAlgebra
        (k := k) (G := G)).mapIso e).toLinearEquiv⟩

end ResidueFieldPositiveSubsetHelpers

section ResidueFieldPositiveSubset

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type w}
variable (π : ι → FDRep k G)
variable (hπ_pairwise : PairwiseNonisomorphic π)
variable (hπ_complete : IsCompleteIrreducibleFamily π)
variable (P : ι → FiniteProjectiveGroupAlgebraModule k G)
variable (hP_envelope :
  ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)

local notation "bP" =>
  projectiveEnvelope_classes_basis_of_complete_family
    π hπ_pairwise hπ_complete P hP_envelope

-- Proof sketch: the zero object is already a finite projective `k[G]`-module, and its
-- Grothendieck class is the zero element.
/-- Helper for Lemma 16-16.3-1: the source-facing positive subset over a field contains `0`. -/
private theorem zero_mem_projectivePositiveSubset :
    (0 : P₀[k](G)) ∈ P⁺[k](G) := by
  -- Use the zero finite projective module as the actual witness for the zero Grothendieck class.
  refine (mem_projectivePositiveSubset_iff k G).2 ?_
  refine ⟨(0 : FiniteProjectiveGroupAlgebraModule k G), ?_⟩
  exact by
    simpa using
      (finiteProjectiveGroupAlgebraGrothendieckClass_zero (A := k) (G := G))

-- Proof sketch: for actual projective classes, addition is realized by the product owner on the
-- underlying `k[G]`-modules.
/-- Helper for Lemma 16-16.3-1: the class of the product of two finite projective `k[G]`-modules
is the sum of their classes. -/
private theorem projective_class_prod_eq_add
    (Q R : FiniteProjectiveGroupAlgebraModule k G) :
    ∃ W : FiniteProjectiveGroupAlgebraModule k G,
      [W]ₚ₀ = [Q]ₚ₀ + [R]ₚ₀ := by
  let W0 : ModuleCat k[G] := ModuleCat.of k[G] (Q.V × R.V)
  have hfinite : Module.Finite k[G] W0 := by
    change Module.Finite k[G] (Q.V × R.V)
    infer_instance
  let Wfg : FGModuleCat k[G] := ⟨W0, hfinite⟩
  have hproj : Module.Projective k[G] Wfg := by
    change Module.Projective k[G] (Q.V × R.V)
    infer_instance
  let W : FiniteProjectiveGroupAlgebraModule k G := ⟨Wfg, hproj⟩
  let f : Q ⟶ W :=
    ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.inl k[G] Q.V R.V))
  let g : W ⟶ R :=
    ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.snd k[G] Q.V R.V))
  let r : W ⟶ Q :=
    ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.fst k[G] Q.V R.V))
  let s : R ⟶ W :=
    ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.inr k[G] Q.V R.V))
  let T : ShortComplex (FiniteProjectiveGroupAlgebraModule k G) :=
    ShortComplex.mk f g (by ext x; rfl)
  have hsplit : T.Splitting := by
    -- The standard product projections and inclusions split the short complex.
    refine
      { r := r
        s := s
        f_r := ?_
        s_g := ?_
        id := ?_ }
    · apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      ext x
      change (LinearMap.fst k[G] Q.V R.V) ((LinearMap.inl k[G] Q.V R.V) x) = x
      simp
    · apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      ext x
      change (LinearMap.snd k[G] Q.V R.V) ((LinearMap.inr k[G] Q.V R.V) x) = x
      simp
    · apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      rintro ⟨x, y⟩
      change
        (LinearMap.inl k[G] Q.V R.V ((LinearMap.fst k[G] Q.V R.V) (x, y)) +
            LinearMap.inr k[G] Q.V R.V ((LinearMap.snd k[G] Q.V R.V) (x, y))) =
          (x, y)
      simp
  have hclass :=
    finiteProjectiveGroupAlgebraGrothendieckClass_middle_eq_left_add_right
      (A := k) (G := G) T ⟨LinearEquiv.refl k[G] (Q.V × R.V)⟩
  refine ⟨W, ?_⟩
  simpa [T, W, Wfg, W0] using hclass

/-- Helper for Lemma 16-16.3-1: the canonical binary product module is an actual witness for the
sum of two projective Grothendieck classes. -/
private theorem exists_product_projective_module_class_eq_add
    (Q R : FiniteProjectiveGroupAlgebraModule k G) :
    ∃ W : FiniteProjectiveGroupAlgebraModule k G,
      Nonempty (W.V ≃ₗ[k[G]] (Q.V × R.V)) ∧
      [W]ₚ₀ = [Q]ₚ₀ + [R]ₚ₀ := by
  let W0 : ModuleCat k[G] := ModuleCat.of k[G] (Q.V × R.V)
  have hfinite : Module.Finite k[G] W0 := by
    -- Finite generation is preserved by the binary product of the two actual witnesses.
    change Module.Finite k[G] (Q.V × R.V)
    infer_instance
  let Wfg : FGModuleCat k[G] := ⟨W0, hfinite⟩
  have hproj : Module.Projective k[G] Wfg := by
    -- Projectivity is likewise inherited by the binary product module.
    change Module.Projective k[G] (Q.V × R.V)
    infer_instance
  let W : FiniteProjectiveGroupAlgebraModule k G := ⟨Wfg, hproj⟩
  -- Reuse the short-exact product argument from the additive helper above for this canonical
  -- witness.
  have hclass : [W]ₚ₀ = [Q]ₚ₀ + [R]ₚ₀ := by
    let f : Q ⟶ W :=
      ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.inl k[G] Q.V R.V))
    let g : W ⟶ R :=
      ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.snd k[G] Q.V R.V))
    let r : W ⟶ Q :=
      ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.fst k[G] Q.V R.V))
    let s : R ⟶ W :=
      ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.inr k[G] Q.V R.V))
    let T : ShortComplex (FiniteProjectiveGroupAlgebraModule k G) :=
      ShortComplex.mk f g (by ext x; rfl)
    have hsplit : T.Splitting := by
      -- The standard product projections and inclusions split the short complex.
      refine
        { r := r
          s := s
          f_r := ?_
          s_g := ?_
          id := ?_ }
      · apply ObjectProperty.hom_ext
        apply ObjectProperty.hom_ext
        apply ModuleCat.hom_ext
        ext x
        change (LinearMap.fst k[G] Q.V R.V) ((LinearMap.inl k[G] Q.V R.V) x) = x
        simp
      · apply ObjectProperty.hom_ext
        apply ObjectProperty.hom_ext
        apply ModuleCat.hom_ext
        ext x
        change (LinearMap.snd k[G] Q.V R.V) ((LinearMap.inr k[G] Q.V R.V) x) = x
        simp
      · apply ObjectProperty.hom_ext
        apply ObjectProperty.hom_ext
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        rintro ⟨x, y⟩
        change
          (LinearMap.inl k[G] Q.V R.V ((LinearMap.fst k[G] Q.V R.V) (x, y)) +
              LinearMap.inr k[G] Q.V R.V ((LinearMap.snd k[G] Q.V R.V) (x, y))) =
            (x, y)
        simp
    have hclass :=
      finiteProjectiveGroupAlgebraGrothendieckClass_middle_eq_left_add_right
        (A := k) (G := G) T ⟨LinearEquiv.refl k[G] (Q.V × R.V)⟩
    simpa [T, W, Wfg, W0] using hclass
  refine ⟨W, ?_, hclass⟩
  refine ⟨LinearEquiv.refl k[G] (Q.V × R.V)⟩

/-- Helper for Lemma 16-16.3-1: a finite family of actual projective classes can be assembled into
one actual finite projective module whose class is the finite sum of the family classes. -/
private theorem exists_projective_module_fin_family_class_eq_sum :
    ∀ {n : ℕ} (Q : Fin n → FiniteProjectiveGroupAlgebraModule k G),
      ∃ W : FiniteProjectiveGroupAlgebraModule k G,
        [W]ₚ₀ = ∑ i, [Q i]ₚ₀
  | 0, Q => by
      -- The empty family corresponds to the zero projective module and the empty sum.
      refine ⟨0, ?_⟩
      simpa using finiteProjectiveGroupAlgebraGrothendieckClass_zero (A := k) (G := G)
  | n + 1, Q => by
      -- Split off the head term and apply the induction hypothesis to the tail family.
      obtain ⟨Wtail, htailClass⟩ :=
        exists_projective_module_fin_family_class_eq_sum
          (Q := fun i : Fin n ↦ Q i.succ)
      obtain ⟨W, hprodClass⟩ :=
        projective_class_prod_eq_add (k := k) (G := G) (Q 0) Wtail
      refine ⟨W, ?_⟩
      · -- The class of the assembled witness is the head class plus the tail sum.
        calc
          [W]ₚ₀ = [Q 0]ₚ₀ + [Wtail]ₚ₀ := hprodClass
          _ = [Q 0]ₚ₀ + ∑ i : Fin n, [Q i.succ]ₚ₀ := by rw [htailClass]
          _ = ∑ i : Fin (n + 1), [Q i]ₚ₀ := by
                simpa using (Fin.sum_univ_succ fun i : Fin (n + 1) ↦ [Q i]ₚ₀).symm

/-- Helper for Lemma 16-16.3-1: a finite family of actual projective classes can be assembled into
one actual finite projective module whose owner module is linearly equivalent to the finite
product of the family owners, and whose class is the corresponding finite sum. -/
private theorem exists_projective_module_fin_family_class_eq_sum_with_equiv :
    ∀ {n : ℕ} (Q : Fin n → FiniteProjectiveGroupAlgebraModule k G),
      ∃ W : FiniteProjectiveGroupAlgebraModule k G,
        Nonempty (W.V ≃ₗ[k[G]] ((i : Fin n) → (Q i).V)) ∧
        [W]ₚ₀ = ∑ i, [Q i]ₚ₀
  | 0, Q => by
      -- The empty product is the zero projective module, whose class is the empty sum.
      let W0 : ModuleCat k[G] := ModuleCat.of k[G] (ULift.{u, 0} PUnit)
      have hfinite : Module.Finite k[G] W0 := by
        change Module.Finite k[G] (ULift.{u, 0} PUnit)
        infer_instance
      let Wfg : FGModuleCat k[G] := ⟨W0, hfinite⟩
      have hproj : Module.Projective k[G] Wfg := by
        change Module.Projective k[G] (ULift.{u, 0} PUnit)
        infer_instance
      let W : FiniteProjectiveGroupAlgebraModule k G := ⟨Wfg, hproj⟩
      refine ⟨W, ?_, ?_⟩
      · refine ⟨by
          change W0 ≃ₗ[k[G]] ((i : Fin 0) → (Q i).V)
          exact LinearEquiv.ofSubsingleton _ _⟩
      · have hW0_zero : IsZero W0 := by
          exact
            (ModuleCat.isZero_of_iff_subsingleton (R := k[G]) (M := ULift.{u, 0} PUnit)).2
              inferInstance
        have hWfg_zero : IsZero Wfg := by
          exact IsZero.of_full_of_faithful_of_isZero (ModuleCat.isFG k[G]).ι Wfg hW0_zero
        have hW_zero : IsZero W := by
          exact
            IsZero.of_full_of_faithful_of_isZero
              (ObjectProperty.ι (fun M : FGModuleCat k[G] ↦ Module.Projective k[G] M))
              W hWfg_zero
        calc
          [W]ₚ₀ = [(0 : FiniteProjectiveGroupAlgebraModule k G)]ₚ₀ := by
            exact
              finiteProjectiveGroupAlgebraGrothendieckClass_eq_of_nonempty_iso
                (A := k) (G := G) ⟨hW_zero.isoZero⟩
          _ = 0 := finiteProjectiveGroupAlgebraGrothendieckClass_zero (A := k) (G := G)
  | n + 1, Q => by
      -- Split off the head factor, realize the tail by induction, and then use the binary product
      -- owner for the head and tail representatives.
      obtain ⟨Wtail, hWtail_equiv, hWtail_class⟩ :=
        exists_projective_module_fin_family_class_eq_sum_with_equiv
          (Q := fun i : Fin n ↦ Q i.succ)
      obtain ⟨W, hW_equiv, hW_class⟩ :=
        exists_product_projective_module_class_eq_add (k := k) (G := G) (Q 0) Wtail
      refine ⟨W, ?_, ?_⟩
      · rcases hW_equiv with ⟨eW⟩
        rcases hWtail_equiv with ⟨eTail⟩
        refine ⟨?_⟩
        let eProd : W.V ≃ₗ[k[G]] ((Q 0).V × ((i : Fin n) → (Q i.succ).V)) :=
          eW.trans ((LinearEquiv.refl k[G] (Q 0).V).prodCongr eTail)
        exact eProd.trans (Fin.consLinearEquiv k[G] (fun i : Fin (n + 1) ↦ (Q i).V))
      · calc
          [W]ₚ₀ = [Q 0]ₚ₀ + [Wtail]ₚ₀ := hW_class
          _ = [Q 0]ₚ₀ + ∑ i : Fin n, [Q i.succ]ₚ₀ := by rw [hWtail_class]
          _ = ∑ i : Fin (n + 1), [Q i]ₚ₀ := by
                simpa using (Fin.sum_univ_succ fun i : Fin (n + 1) ↦ [Q i]ₚ₀).symm

/-- Helper for Lemma 16-16.3-1: the largest semisimple quotient of a finite projective
`k[G]`-module is finite-dimensional over `k`. -/
private theorem moduleFinite_largestSemisimpleQuotient
    (Q : FiniteProjectiveGroupAlgebraModule k G) :
    Module.Finite k (Q.V ⧸ Module.jacobson k[G] Q.V) := by
  let _ : Module.Finite k Q.V := Q.finite
  exact
    Module.Finite.of_surjective
      ((Module.jacobson k[G] Q.V).mkQ.restrictScalars k)
      (by
        intro x
        rcases Submodule.mkQ_surjective (Module.jacobson k[G] Q.V) x with ⟨y, rfl⟩
        exact ⟨y, rfl⟩)

-- Proof sketch: actual projective classes are closed under addition because binary sums are
-- represented by the product of the two witnesses.
/-- Helper for Lemma 16-16.3-1: `P_k^+(G)` is closed under addition. -/
private theorem add_mem_projectivePositiveSubset
    {x y : P₀[k](G)} (hx : x ∈ P⁺[k](G)) (hy : y ∈ P⁺[k](G)) :
    x + y ∈ P⁺[k](G) := by
  rcases (mem_projectivePositiveSubset_iff k G).1 hx with ⟨Q, rfl⟩
  rcases (mem_projectivePositiveSubset_iff k G).1 hy with ⟨R, rfl⟩
  -- Combine the two actual witnesses by taking their product module.
  refine (mem_projectivePositiveSubset_iff k G).2 ?_
  rcases projective_class_prod_eq_add (k := k) (G := G) Q R with ⟨W, hW⟩
  exact ⟨W, hW⟩

-- Proof sketch: repeated addition of an actual projective class stays actual.
/-- Helper for Lemma 16-16.3-1: nonnegative multiples of an actual projective class stay in
`P_k^+(G)`. -/
private theorem nsmul_mem_projectivePositiveSubset
    {x : P₀[k](G)} (n : ℕ) (hx : x ∈ P⁺[k](G)) :
    n • x ∈ P⁺[k](G) := by
  induction n with
  | zero =>
      simpa using zero_mem_projectivePositiveSubset (k := k) (G := G)
  | succ n ihn =>
      -- Rewrite the successor multiple as one more copy of `x`.
      simpa [succ_nsmul] using
        add_mem_projectivePositiveSubset (k := k) (G := G) ihn hx

-- Proof sketch: a nonnegative integer scalar is the same as a natural-number multiple, so the
-- previous closure statement upgrades from `ℕ`-multiples to nonnegative `ℤ`-multiples.
/-- Helper for Lemma 16-16.3-1: a nonnegative integer multiple of an actual projective class is
again actual. -/
private theorem zsmul_mem_projectivePositiveSubset_of_nonneg
    {x : P₀[k](G)} {n : ℤ} (hn : 0 ≤ n) (hx : x ∈ P⁺[k](G)) :
    n • x ∈ P⁺[k](G) := by
  -- Convert the integer scalar to the corresponding natural scalar.
  lift n to ℕ using hn
  simpa using nsmul_mem_projectivePositiveSubset (k := k) (G := G) n hx

-- Proof sketch: if the basis coordinates of `x` are all nonnegative, write `x` as the finite sum
-- of those nonnegative coordinate multiples of the basis vectors `[P i]ₚ₀`.
/-- Helper for Lemma 16-16.3-1: every element of the positive cone of the distinguished
projective-envelope basis already belongs to the actual positive subset `P_k^+(G)`. -/
private theorem positiveCone_subset_projectivePositiveSubset :
    (bP).positiveCone ⊆ P⁺[k](G) := by
  classical
  intro x hx
  let c := (bP).repr x
  have hsum :
      ∀ d : ι →₀ ℤ, (∀ i, 0 ≤ d i) → d.sum (fun i a ↦ a • (bP i)) ∈ P⁺[k](G) := by
    intro d
    -- Build the basis expansion by adding one nonnegative coordinate term at a time.
    refine Finsupp.induction₂ d ?_ ?_
    · intro _
      simpa using zero_mem_projectivePositiveSubset (k := k) (G := G)
    · intro i a f hi ha hf hnonneg
      have ha_nonneg : 0 ≤ a := by
        have hia : f i = 0 := by
          exact Finsupp.notMem_support_iff.mp hi
        simpa [Finsupp.single_apply, hia] using hnonneg i
      have hf_nonneg : ∀ j, 0 ≤ f j := by
        intro j
        by_cases hji : j = i
        · subst hji
          simp [Finsupp.notMem_support_iff.mp hi]
        · simpa [Finsupp.single_apply, hji] using hnonneg j
      have hPi : bP i ∈ P⁺[k](G) := by
        refine (mem_projectivePositiveSubset_iff k G).2 ?_
        refine ⟨P i, ?_⟩
        exact
          (projectiveEnvelope_classes_basis_of_complete_family_apply
            (π := π) (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)
            (P := P) (hP_envelope := hP_envelope) i).symm
      have hsingle : a • (bP i) ∈ P⁺[k](G) :=
        zsmul_mem_projectivePositiveSubset_of_nonneg
          (k := k) (G := G) ha_nonneg hPi
      have hrest : f.sum (fun j b ↦ b • (bP j)) ∈ P⁺[k](G) :=
        hf hf_nonneg
      have hadd :
          (f.sum (fun j b ↦ b • (bP j))) + a • (bP i) ∈ P⁺[k](G) :=
        add_mem_projectivePositiveSubset (k := k) (G := G) hrest hsingle
      simpa [Finsupp.sum_add_index, Finsupp.sum_single_index, add_smul] using hadd
  have hsum' : c.sum (fun i a ↦ a • (bP i)) ∈ P⁺[k](G) :=
    hsum c hx
  -- Expand `x` in the basis and apply the closure result to that finite sum.
  have hx_sum :
      c.sum (fun i a ↦ a • (bP i)) = x := by
    simpa [c, Finsupp.linearCombination_apply, Finsupp.sum] using
      (bP).linearCombination_repr x
  rw [← hx_sum]
  exact hsum'

/-- Helper for Lemma 16-16.3-1: an indecomposable finite projective `k[G]`-module contributes one
distinguished projective-envelope basis vector of `P_k(G)`. -/
private theorem indecomposable_projective_class_eq_basis_vector
    (Q : FiniteProjectiveGroupAlgebraModule k G)
    (hQ_indecomp : Indecomposable Q.V) :
    ∃ i : ι, [Q]ₚ₀ = bP i := by
  classical
  have hsimple :
      IsSimpleModule k[G] (Q.V ⧸ Module.jacobson k[G] Q.V) := by
    -- Corollary `14-14.3-2` identifies the simple top as the hallmark of indecomposability.
    exact
      (indecomposable_projective_module_iff_simple_largestSemisimpleQuotient
        (k := k) (G := G) (P := Q.V)).1 hQ_indecomp
  let M : Type u := Q.V ⧸ Module.jacobson k[G] Q.V
  let _ : Module.Finite k M := moduleFinite_largestSemisimpleQuotient (k := k) (G := G) Q
  let τ : Representation k G M := Representation.ofModule' (k := k) (G := G) M
  have hτ_irred : τ.IsIrreducible := by
    -- Rebundling the simple top as a representation gives an irreducible object.
    simpa [τ, M] using
      ofModule'_isIrreducible_of_isSimpleModule_local (k := k) (G := G) M
  obtain ⟨i, hτi⟩ :=
    IsCompleteIrreducibleFamily.exists_iso_of_representation
      (K := k) (G := G) π hπ_complete τ hτ_irred
  obtain ⟨eτ⟩ :=
    nonempty_asModuleLinearEquiv_of_nonempty_fdRepIso_local
      (k := k) (G := G) (FDRep.of τ) (π i) hτi
  obtain ⟨eM⟩ := nonempty_ofModule'_asModuleLinearEquiv_local (k := k) (G := G) M
  let ρπ : Representation k G (π i) := (π i).ρ
  let Mπ : Type u := asModule ρπ
  letI : AddCommGroup Mπ := ρπ.instAddCommGroupAsModule
  letI : Module k[G] Mπ := ρπ.instModuleMonoidAlgebraAsModule
  let eQuot : M ≃ₗ[k[G]] Mπ := by
    -- Transport the quotient module first through `Representation.ofModule'`, then into `π i`.
    simpa [τ, M] using eM.symm.trans eτ
  let _ : Module.Finite k k[G] := MonoidAlgebra.moduleFinite
  let _ : IsArtinianRing k[G] := IsArtinianRing.of_finite k k[G]
  let _ : IsArtinian k[G] Q.V := by infer_instance
  let qQ : Q.V →ₗ[k[G]] M := (Module.jacobson k[G] Q.V).mkQ
  have hqQ : qQ.IsProjectiveEnvelope := by
    -- The canonical Jacobson quotient map of `Q` is its reference projective envelope.
    simpa [qQ, M] using
      (show ((Module.jacobson k[G] Q.V).mkQ :
          Q.V →ₗ[k[G]] Q.V ⧸ Module.jacobson k[G] Q.V).IsProjectiveEnvelope
        from LinearMap.largestSemisimpleQuotientMk_isProjectiveEnvelope)
  let fP : (P i).V →ₗ[k[G]] Mπ := Classical.choose (hP_envelope i)
  have hfP : fP.IsProjectiveEnvelope := Classical.choose_spec (hP_envelope i)
  let fP' : (P i).V →ₗ[k[G]] M := eQuot.symm.toLinearMap.comp fP
  have hfP' : fP'.IsProjectiveEnvelope := by
    letI : fP'.IsEssential := by
      refine ⟨?_⟩
      intro N hN
      have hmap : (N.map fP).map eQuot.symm.toLinearMap = ⊤ := by
        simpa [fP', Submodule.map_comp] using hN
      have hNmap : N.map fP = ⊤ := by
        exact (Submodule.map_eq_top_iff (p := N.map fP) (e := eQuot.symm)).1 hmap
      exact hfP.toIsEssential.eq_top_of_map_eq_top N hNmap
    -- Surjectivity of the chosen projective envelope transports back across the quotient
    -- equivalence.
    refine LinearMap.IsProjectiveEnvelope.mk ?_
    intro y
    obtain ⟨x, hx⟩ := hfP.surjective (eQuot y)
    refine ⟨x, ?_⟩
    simpa [fP', hx]
  obtain ⟨eSrc, _⟩ := LinearMap.isProjectiveEnvelope_unique hqQ hfP'
  have hIso : Nonempty (Q ≅ P i) := by
    -- Two projective envelopes of the same simple top are isomorphic on their sources.
    exact
      (finiteProjectiveGroupAlgebraModule_nonempty_iso_iff_nonempty_linearEquiv
        (A := k) (G := G) Q (P i)).2 ⟨eSrc⟩
  refine ⟨i, ?_⟩
  calc
    [Q]ₚ₀ = [P i]ₚ₀ := by
      exact
        finiteProjectiveGroupAlgebraGrothendieckClass_eq_of_nonempty_iso
          (A := k) (G := G) hIso
    _ = bP i := by
      symm
      exact
        projectiveEnvelope_classes_basis_of_complete_family_apply
          (π := π) (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)
          (P := P) (hP_envelope := hP_envelope) i

/-- Helper for Lemma 16-16.3-1: every actual projective `k[G]`-class is a finite nonnegative
integral combination of the distinguished projective-envelope basis vectors. -/
private theorem projective_class_eq_nonneg_basis_combination
    (Q : FiniteProjectiveGroupAlgebraModule k G) :
    ∃ c : ι →₀ ℤ,
      (∀ i, 0 ≤ c i) ∧
        Finsupp.linearCombination ℤ (fun i ↦ bP i) c = [Q]ₚ₀ := by
  classical
  obtain ⟨κ, _, Qdec, eQ, hQdec⟩ :
      ∃ (κ : Type w) (_ : Finite κ) (Qdec : κ → ModuleCat k[G]) (_ : Q.V ≅ ⨁ Qdec),
        ∀ j, Module.Finite k[G] (Qdec j) ∧
          Module.Projective k[G] (Qdec j) ∧ Indecomposable (Qdec j) := by
    simpa using
      (finite_projective_module_exists_indecomposable_decomposition
        (k := k) (G := G) (M := Q.V))
  letI : Fintype κ := Fintype.ofFinite κ
  let n : ℕ := Fintype.card κ
  let eκ : κ ≃ Fin n := Fintype.equivFin κ
  let Qfin : Fin n → ModuleCat k[G] := fun j ↦ Qdec (eκ.symm j)
  have hQwhisker (j : κ) : Qfin (eκ j) ≅ Qdec j := by
    simpa [Qfin] using Iso.refl (Qdec j)
  let eQfin : Q.V ≅ ⨁ Qfin := eQ ≪≫ biproduct.whiskerEquiv eκ hQwhisker
  let eQpi : Q.V ≃ₗ[k[G]] ((j : Fin n) → Qfin j) :=
    (eQfin ≪≫ ModuleCat.biproductIsoPi Qfin).toLinearEquiv
  let Qproj : Fin n → FiniteProjectiveGroupAlgebraModule k G := fun j ↦
    ⟨⟨Qfin j, (hQdec (eκ.symm j)).1⟩, (hQdec (eκ.symm j)).2.1⟩
  obtain ⟨W, hW_equiv, hW_class⟩ :=
    exists_projective_module_fin_family_class_eq_sum_with_equiv (k := k) (G := G) Qproj
  have hQ_class :
      [Q]ₚ₀ = ∑ j : Fin n, [Qproj j]ₚ₀ := by
    rcases hW_equiv with ⟨eW⟩
    have hIso : Nonempty (Q ≅ W) := by
      refine
        (finiteProjectiveGroupAlgebraModule_nonempty_iso_iff_nonempty_linearEquiv
          (A := k) (G := G) Q W).2 ?_
      let eDec : ((j : Fin n) → Qfin j) ≃ₗ[k[G]] W.V := by
        simpa [Qproj, Qfin] using eW.symm
      exact ⟨eQpi.trans eDec⟩
    calc
      [Q]ₚ₀ = [W]ₚ₀ := by
        exact
          finiteProjectiveGroupAlgebraGrothendieckClass_eq_of_nonempty_iso
            (A := k) (G := G) hIso
      _ = ∑ j : Fin n, [Qproj j]ₚ₀ := hW_class
  choose i hi using
    fun j : Fin n ↦
      indecomposable_projective_class_eq_basis_vector
        (k := k) (G := G) (π := π) (hπ_pairwise := hπ_pairwise)
        (hπ_complete := hπ_complete) (P := P) (hP_envelope := hP_envelope) (Qproj j)
        (by simpa [Qproj, Qfin] using (hQdec (eκ.symm j)).2.2)
  let c : ι →₀ ℤ := ∑ j : Fin n, Finsupp.single (i j) (1 : ℤ)
  refine ⟨c, ?_, ?_⟩
  · intro i0
    -- The coefficient of `i0` counts how many indecomposable summands map to `bP i0`.
    simpa [c] using
      (Finset.sum_nonneg fun j _ ↦ by
        by_cases hij : i j = i0
        · simp [Finsupp.single_apply, hij]
        · simp [Finsupp.single_apply, hij])
  · -- Expand the finite sum of singleton coefficients and rewrite each summand through the chosen
    -- basis-vector identity.
    calc
      Finsupp.linearCombination ℤ (fun i ↦ bP i) c
          = ∑ j : Fin n,
              Finsupp.linearCombination ℤ (fun i ↦ bP i) (Finsupp.single (i j) (1 : ℤ)) := by
                simp [c]
      _ = ∑ j : Fin n, bP (i j) := by
            simp
      _ = ∑ j : Fin n, [Qproj j]ₚ₀ := by
            simp [hi]
      _ = [Q]ₚ₀ := hQ_class.symm

-- Proof sketch: Corollary `14-14.3-3` already owns the existence of the projective-envelope basis
-- of `P_k(G)`. The source-facing positive subset is therefore exactly the positive cone of that
-- canonical basis.
/-- For the distinguished projective-envelope basis of `P_k(G)` attached to a complete family of
pairwise nonisomorphic simple `k[G]`-modules, Serre's positive subset `P_k^+(G)`, written here as
`P⁺[k](G)`, is exactly the positive cone of that basis. -/
theorem projectivePositiveSubset_eq_positiveCone_of_complete_simple_family :
    P⁺[k](G) = (bP).positiveCone := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases (mem_projectivePositiveSubset_iff k G).1 hx with ⟨Q, rfl⟩
    rcases
      projective_class_eq_nonneg_basis_combination
        (k := k) (G := G) (π := π) (hπ_pairwise := hπ_pairwise)
        (hπ_complete := hπ_complete) (P := P) (hP_envelope := hP_envelope) Q
      with ⟨c, hc, hclass⟩
    -- The indecomposable decomposition expresses the actual class as a basis combination with
    -- nonnegative coefficients, hence it lies in the positive cone.
    rw [← hclass]
    exact Module.Basis.linearCombination_mem_positiveCone_of_nonneg (bP) c hc
  · -- The converse direction is now purely formal from closure of actual projective classes.
    exact positiveCone_subset_projectivePositiveSubset
      (k := k) (G := G) (π := π) (hπ_pairwise := hπ_pairwise)
      (hπ_complete := hπ_complete) (P := P) (hP_envelope := hP_envelope)

-- Proof sketch: identify `P⁺[k](G)` with the positive cone of the canonical projective-envelope
-- basis, then apply `Module.Basis.mem_positiveCone_of_nsmul_mem_positiveCone`.
theorem mem_projectivePositiveSubset_of_nsmul_mem_residueField
    {x : P₀[k](G)} {n : ℕ} (hn : 1 ≤ n)
    (hx : n • x ∈ P⁺[k](G)) :
    x ∈ P⁺[k](G) := by
  classical
  obtain ⟨ι, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_over_field (k := k) (G := G)
  choose P hP_envelope using
    fun i : ι ↦ exists_finite_projectiveEnvelope_of_simple (k := k) (G := G) (π i)
  -- Rewrite `P⁺[k](G)` as the positive cone of the distinguished projective-envelope basis.
  exact Module.Basis.mem_of_nsmul_mem_of_eq_positiveCone
    (b := projectiveEnvelope_classes_basis_of_complete_family
      π hπ_pairwise hπ_complete P hP_envelope)
    hn
    (projectivePositiveSubset_eq_positiveCone_of_complete_simple_family
      (k := k) (G := G) (π := π) (hπ_pairwise := hπ_pairwise)
      (hπ_complete := hπ_complete) (P := P) (hP_envelope := hP_envelope))
    hx

end ResidueFieldPositiveSubset

end Representation
