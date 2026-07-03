import Mathlib
import LinearRepresentations_Serre_1977.Chap08.Proposition_8_8_3_7
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_3
import LinearRepresentations_Serre_1977.Chap14.Proposition_14_14_3_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_1_2.FiniteRepTensorRing

noncomputable section

universe u

open CategoryTheory
open scoped MonoidAlgebra
open scoped MonoidalCategory
open scoped Representation
open scoped ZeroObject

namespace Representation

section

variable {p : ℕ}
variable {k : Type u} [Field k] [CharP k p]
variable {G : Type u} [Group G]
variable [Fact p.Prime]

omit [CharP k p] [Fact p.Prime] in
/-- Helper for Theorem 16-16.1-5: choose one representative of each isomorphism class of simple
finite-dimensional `k[G]`-representations. -/
private theorem exists_complete_pairwise_nonisomorphic_simple_family_local
    [Finite G] :
    ∃ (ι : Type (u + 1)) (π : ι → FDRep k G),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  let SimpleRep : Type (u + 1) := { τ : FDRep k G // CategoryTheory.Simple τ }
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
      have hq : Nonempty (((Quotient.out q).1) ≅ τ) := by
        exact Quotient.exact (Quotient.out_eq q)
      rcases hq with ⟨e⟩
      exact ⟨e.symm⟩
  exact ⟨ι, π, hπ_pairwise, hπ_complete⟩

omit [Fact p.Prime] in
/-- Helper for Theorem 16-16.1-5: the quotient-additive and ring-derived natural scalar actions on
`R₀[k](H)` agree. -/
private theorem quotient_nsmul_eq_ring_nsmul
    {H : Type u} [Group H] (n : ℕ) (x : R₀[k](H)) :
    @HSMul.hSMul ℕ R₀[k](H) R₀[k](H)
        (@instHSMul ℕ R₀[k](H)
          (@AddMonoid.toNSMul R₀[k](H)
            (QuotientAddGroup.Quotient.addGroup
              (finiteRepGrothendieckRelations k H)).toAddMonoid))
        n x =
      n • x := by
  change
    (@nsmulAddMonoidHom (R₀[k](H))
      (QuotientAddGroup.Quotient.addCommGroup
        (finiteRepGrothendieckRelations k H)).toAddCommMonoid
      n) x =
      n • x
  have hmul :
      (@nsmulAddMonoidHom (R₀[k](H))
        (QuotientAddGroup.Quotient.addCommGroup
          (finiteRepGrothendieckRelations k H)).toAddCommMonoid
        n) x =
        (n : R₀[k](H)) * x := by
    induction n with
    | zero =>
        simp [nsmulAddMonoidHom]
    | succ n ih =>
        rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
        simpa [nsmulAddMonoidHom, succ_nsmul, add_comm, add_left_comm, add_assoc] using
          congrArg (fun z ↦ x + z) ih
  exact hmul.trans (nsmul_eq_mul n x).symm

/-- Helper for Theorem 16-16.1-5: the Sylow-cardinality formula identifies the order of a Sylow
`p`-subgroup with the `p`-part `p ^ n` appearing in the factorization `|G| = p ^ n * m`. -/
theorem sylow_card_eq_p_pow_of_card_factorization
    [Finite G]
    (P : Sylow p G) (n m : ℕ) (hcard : Nat.card G = p ^ n * m) (hm : Nat.Coprime p m) :
    Nat.card (P : Subgroup G) = p ^ n := by
  rw [P.card_eq_multiplicity]
  have hp' : Nat.Prime p := Fact.out
  have hm0 : m ≠ 0 := by
    intro hmz
    have : Nat.Coprime p 0 := by
      simpa [hmz] using hm
    exact hp'.ne_one <| by
      simpa [Nat.coprime_zero_right] using this
  have hfactorization : (Nat.card G).factorization p = n := by
    rw [hcard]
    have hmul :=
      Nat.factorization_mul (a := p ^ n) (b := m) (pow_ne_zero _ hp'.ne_zero) hm0
    have hfactorization_m : m.factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hdiv
      have hm1 : p ∣ 1 := by
        exact hm.dvd_of_dvd_mul_left (by simpa using hdiv)
      exact hp'.not_dvd_one hm1
    rw [hmul]
    simp [hp'.factorization_pow, hfactorization_m]
  rw [hfactorization]

omit [CharP k p] [Fact p.Prime] in
/-- Helper for Theorem 16-16.1-5: a simple trivial finite-dimensional representation is
one-dimensional over the coefficient field. -/
theorem finrank_eq_one_of_simple_of_isTrivial
    {H : Type u} [Group H]
    (W : FDRep k H) [Simple W] [Representation.IsTrivial W.ρ] :
    Module.finrank k W = 1 := by
  letI : Representation.IsIrreducible W.ρ := FDRep.isIrreducible_of_simple W
  have hW_nontrivial : Nontrivial W := by
    have hW_not_subsingleton : ¬ Subsingleton W := by
      intro hW
      letI : Subsingleton W := hW
      have hzero : (𝟙 W : W ⟶ W) = 0 := by
        ext x
        exact Subsingleton.elim _ _
      exact CategoryTheory.id_nonzero W hzero
    exact not_subsingleton_iff_nontrivial.mp hW_not_subsingleton
  letI : Nontrivial W := hW_nontrivial
  obtain ⟨w, hw0⟩ := exists_ne (0 : W)
  let U : Subrepresentation W.ρ :=
    { toSubmodule := Submodule.span k {w}
      apply_mem_toSubmodule := by
        intro g x hx
        rw [Submodule.mem_span_singleton] at hx ⊢
        rcases hx with ⟨c, rfl⟩
        refine ⟨c, ?_⟩
        simp }
  have hU_ne_bot : U ≠ ⊥ := by
    intro hU
    have hw_mem : w ∈ U.toSubmodule := by
      exact Submodule.subset_span (by simp)
    have hw_bot : w ∈ (⊥ : Subrepresentation W.ρ).toSubmodule := by
      simpa [hU] using hw_mem
    have : w = 0 := by
      simpa using hw_bot
    exact hw0 this
  have hU_top : U = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top U).resolve_left hU_ne_bot
  have hspan : Submodule.span k {w} = ⊤ := by
    simpa [U] using congrArg Subrepresentation.toSubmodule hU_top
  exact (finrank_eq_one_iff_of_nonzero' w hw0).2 fun x ↦ by
    have hx : x ∈ Submodule.span k {w} := by
      simpa [hspan] using (show x ∈ (⊤ : Submodule k W) from Submodule.mem_top)
    simpa [Submodule.mem_span_singleton] using hx

omit [CharP k p] [Fact p.Prime] in
/-- Helper for Theorem 16-16.1-5: a simple trivial finite-dimensional representation is
isomorphic to the one-dimensional trivial representation. -/
theorem nonempty_iso_trivial_of_simple_of_isTrivial
    {H : Type u} [Group H]
    (W : FDRep k H) [Simple W] [Representation.IsTrivial W.ρ] :
    Nonempty (W ≅ FDRep.of (Representation.trivial k H k)) := by
  have hdim :
      Module.finrank k W = 1 :=
    finrank_eq_one_of_simple_of_isTrivial (k := k) W
  rcases Module.nonempty_linearEquiv_of_finrank_eq_one hdim with ⟨e⟩
  have hWrho : W ≅ FDRep.of W.ρ :=
    Action.mkIso (Iso.refl _) fun g => by
      ext x
      rfl
  let hEquiv : Representation.Equiv W.ρ (Representation.trivial k H k) :=
    Representation.Equiv.mk e.symm <| by
      intro g
      ext z
      simp
  exact ⟨hWrho.trans (Representation.Equiv.toFDRepIso hEquiv)⟩

/-- Helper for Theorem 16-16.1-5: a one-dimensional trivial finite-dimensional representation is
isomorphic to the one-dimensional trivial representation. -/
theorem nonempty_iso_trivial_of_finrank_one_of_isTrivial
    {H : Type u} [Group H]
    (W : FDRep k H) [Representation.IsTrivial W.ρ]
    (hW : Module.finrank k W = 1) :
    Nonempty (W ≅ FDRep.of (Representation.trivial k H k)) := by
  rcases Module.nonempty_linearEquiv_of_finrank_eq_one hW with ⟨e⟩
  let hWrho : W ≅ FDRep.of W.ρ :=
    Action.mkIso (Iso.refl _) fun g => by
      ext x
      rfl
  let hEquiv : Representation.Equiv W.ρ (Representation.trivial k H k) :=
    Representation.Equiv.mk e.symm <| by
      intro g
      ext z
      simp
  exact ⟨hWrho.trans (Representation.Equiv.toFDRepIso hEquiv)⟩

/-- Helper for Theorem 16-16.1-5: a nonzero invariant vector spans a trivial one-dimensional
subrepresentation. -/
theorem invariant_line_nonempty_iso_trivial
    {H : Type u} [Group H]
    (W : FDRep k H) {x : W} (hx : x ∈ Representation.invariants W.ρ) (hx0 : x ≠ 0) :
    let U : Subrepresentation W.ρ :=
      { toSubmodule := Submodule.span k {x}
        apply_mem_toSubmodule := by
          intro g y hy
          rw [Submodule.mem_span_singleton] at hy ⊢
          rcases hy with ⟨a, rfl⟩
          refine ⟨a, ?_⟩
          calc
            a • x = a • (W.ρ g x) := by rw [(Representation.mem_invariants (ρ := W.ρ) x).1 hx g]
            _ = W.ρ g (a • x) := by rw [LinearMap.map_smul] }
    Nonempty (FDRep.of U.toRepresentation ≅ FDRep.of (Representation.trivial k H k)) := by
  let U : Subrepresentation W.ρ :=
    { toSubmodule := Submodule.span k {x}
      apply_mem_toSubmodule := by
        intro g y hy
        rw [Submodule.mem_span_singleton] at hy ⊢
        rcases hy with ⟨a, rfl⟩
        refine ⟨a, ?_⟩
        calc
          a • x = a • (W.ρ g x) := by rw [(Representation.mem_invariants (ρ := W.ρ) x).1 hx g]
          _ = W.ρ g (a • x) := by rw [LinearMap.map_smul] }
  have hUfinrank : Module.finrank k U.toSubmodule = 1 := by
    simpa [U] using finrank_span_singleton hx0
  letI : Representation.IsTrivial U.toRepresentation := by
    refine ⟨fun g ↦ ?_⟩
    ext y
    rcases y with ⟨y, hy⟩
    change (W.ρ g y : W) = y
    rw [Submodule.mem_span_singleton] at hy
    rcases hy with ⟨a, rfl⟩
    exact by
      simp [(Representation.mem_invariants (ρ := W.ρ) x).1 hx g]
  letI : Representation.IsTrivial (FDRep.of U.toRepresentation).ρ := by
    simpa using (inferInstance : Representation.IsTrivial U.toRepresentation)
  exact
    nonempty_iso_trivial_of_finrank_one_of_isTrivial
      (k := k) (H := H) (W := FDRep.of U.toRepresentation) <| by
        simpa using hUfinrank

/-- Helper for Theorem 16-16.1-5: if the ambient coefficient extension `R → S` is free, then
restricting scalars along `R → S` carries a projective `S`-module to a projective `R`-module. -/
theorem projective_restrictScalars_of_free_hom
    {R : Type u} [Semiring R]
    {S : Type u} [Semiring S] (σ : R →+* S)
    {M : Type*} [AddCommMonoid M] [Module S M]
    [Module R S] [Module R M] [IsScalarTower R S M]
    (hsmulS : ∀ (r : R) (s : S), (r • s : S) = σ r * s)
    [Module.Free R S] [Module.Projective S M] :
    Module.Projective R M := by
  obtain ⟨P, _instAddCommMonoid, _instModule, _instFree, i, s, hs⟩ :=
    (Module.Projective.iff_split (R := S) (P := M)).mp inferInstance
  let _ : Module R P := Module.compHom P σ
  let _ : IsScalarTower R S P := by
    refine ⟨?_⟩
    intro r s' x
    calc
      (r • s' : S) • x = (σ r * s') • x := by rw [hsmulS]
      _ = (σ r) • (s' • x) := by simpa using (mul_smul (σ r) s' x)
  let _ : Module.Free R P :=
    Module.Free.of_basis
      ((Module.Free.chooseBasis R S).smulTower (Module.Free.chooseBasis S P))
  exact Module.Projective.of_split (i.restrictScalars R) (s.restrictScalars R) <| by
    ext x
    exact LinearMap.congr_fun hs x

/-- Helper for Theorem 16-16.1-5: once `k[G]` is known to be free over `k[H]`, restricting a
projective `k[G]`-module to `H ≤ G` preserves projectivity on the underlying carrier. -/
theorem projective_restrictScalars_of_subgroup_groupAlgebra
    (H : Subgroup G)
    (E : FiniteProjectiveGroupAlgebraModule k G)
    (hfree :
      let σ : k[↥H] →+* k[G] := MonoidAlgebra.mapDomainRingHom k H.subtype
      let _ : Module k[↥H] k[G] := Module.compHom k[G] σ
      Module.Free k[↥H] k[G]) :
    let σ : k[↥H] →+* k[G] := MonoidAlgebra.mapDomainRingHom k H.subtype
    let _ : Module k[↥H] E.V := Module.compHom E.V σ
    Module.Projective k[↥H] E.V := by
  let σ : k[↥H] →+* k[G] := MonoidAlgebra.mapDomainRingHom k H.subtype
  let _ : Module k[↥H] k[G] := Module.compHom k[G] σ
  let _ : Module.Free k[↥H] k[G] := hfree
  let _ : Module k[↥H] E.V := Module.compHom E.V σ
  let _ : IsScalarTower k[↥H] k[G] E.V := by
    refine ⟨?_⟩
    intro r s x
    simpa [σ, Module.compHom] using (mul_smul (σ r) s x)
  exact projective_restrictScalars_of_free_hom (R := k[↥H]) (S := k[G])
    (σ := σ) (M := E.V) (fun (r : k[↥H]) (s : k[G]) => rfl)

/-- Helper for Theorem 16-16.1-5: an invariant vector in a `k[H]`-module spans a line on which the
whole group algebra acts by scalars. -/
theorem invariant_groupAlgebra_smul_eq_scalar
    {H : Type u} [Group H]
    {M : Type u} [AddCommGroup M] [Module k M] [Module k[H] M] [IsScalarTower k k[H] M]
    {x : M}
    (hx : x ∈ Representation.invariants (Representation.ofModule' (k := k) (G := H) M)) :
    ∀ r : k[H], ∃ c : k, r • x = c • x := by
  intro r
  refine MonoidAlgebra.induction_on (p := fun r => ∃ c : k, r • x = c • x) r ?_ ?_ ?_
  · intro g
    refine ⟨1, ?_⟩
    simpa [Representation.ofModule'] using
      ((Representation.mem_invariants
        (ρ := Representation.ofModule' (k := k) (G := H) M) x).1 hx g)
  · intro a b ha hb
    rcases ha with ⟨ca, hca⟩
    rcases hb with ⟨cb, hcb⟩
    refine ⟨ca + cb, ?_⟩
    rw [add_smul, hca, hcb, add_smul]
  · intro a b hb
    rcases hb with ⟨cb, hcb⟩
    refine ⟨a * cb, ?_⟩
    calc
      (a • b : k[H]) • x = a • (b • x) := by rw [smul_assoc]
      _ = a • (cb • x) := by rw [hcb]
      _ = (a * cb) • x := by rw [smul_smul]

/-- Helper for Theorem 16-16.1-5: every simple finite-dimensional representation of a finite
`p`-group over a field of characteristic `p` is the trivial one-dimensional representation. -/
theorem simple_fdRep_nonempty_iso_trivial_of_isPGroup
    {H : Type u} [Group H] [Finite H]
    (hH : IsPGroup p H) (W : FDRep k H) [Simple W] :
    Nonempty (W ≅ FDRep.of (Representation.trivial k H k)) := by
  have hW_nontrivial : Nontrivial W := by
    have hW_not_subsingleton : ¬ Subsingleton W := by
      intro hW
      letI : Subsingleton W := hW
      have hzero : (𝟙 W : W ⟶ W) = 0 := by
        ext x
        exact Subsingleton.elim _ _
      exact CategoryTheory.id_nonzero W hzero
    exact not_subsingleton_iff_nontrivial.mp hW_not_subsingleton
  letI : Nontrivial W := hW_nontrivial
  letI : Representation.IsIrreducible W.ρ := FDRep.isIrreducible_of_simple W
  have hinv_ne_bot : Representation.invariants W.ρ ≠ ⊥ := by
    simpa using invariants_ne_bot_of_isPGroup_charP (ρ := W.ρ) hH
  obtain ⟨x, hx, hx0⟩ := (Representation.invariants W.ρ).ne_bot_iff.1 hinv_ne_bot
  let U : Subrepresentation W.ρ :=
    { toSubmodule := Submodule.span k {x}
      apply_mem_toSubmodule := by
        intro g y hy
        rw [Submodule.mem_span_singleton] at hy ⊢
        rcases hy with ⟨a, rfl⟩
        refine ⟨a, ?_⟩
        calc
          a • x = a • (W.ρ g x) := by rw [(Representation.mem_invariants (ρ := W.ρ) x).1 hx g]
          _ = W.ρ g (a • x) := by rw [LinearMap.map_smul] }
  have hU_ne_bot : U ≠ ⊥ := by
    intro hU
    have hx_mem : x ∈ U.toSubmodule := by
      exact Submodule.subset_span (by simp)
    have hx_bot : x ∈ (⊥ : Subrepresentation W.ρ).toSubmodule := by
      simpa [hU] using hx_mem
    exact hx0 (by simpa using hx_bot)
  have hU_top : U = ⊤ := (eq_bot_or_eq_top U).resolve_left hU_ne_bot
  letI : Representation.IsTrivial W.ρ := by
    refine ⟨fun g ↦ ?_⟩
    ext y
    have hy : y ∈ U.toSubmodule := by
      simpa [hU_top] using (show y ∈ (⊤ : Submodule k W) from Submodule.mem_top)
    rw [Submodule.mem_span_singleton] at hy
    rcases hy with ⟨a, rfl⟩
    simp [(Representation.mem_invariants (ρ := W.ρ) x).1 hx g]
  exact nonempty_iso_trivial_of_simple_of_isTrivial (k := k) (H := H) W

/-- Helper for Theorem 16-16.1-5: the class of a simple finite-dimensional representation of a
finite `p`-group is the trivial class. -/
theorem simple_fdRep_class_eq_trivial_of_isPGroup
    {H : Type u} [Group H] [Finite H]
    (hH : IsPGroup p H) (W : FDRep k H) [Simple W] :
    [W]₀ = ([𝟙_ (FDRep k H)]₀ : R₀[k](H)) := by
  exact finiteRepGrothendieckClass_eq_of_nonempty_iso
    (simple_fdRep_nonempty_iso_trivial_of_isPGroup (p := p) (k := k) hH W)

/-- Helper for Theorem 16-16.1-5: the free abelian group lift of `k`-dimension on actual
finite-dimensional representations. -/
private abbrev finiteRepDimensionLift_local
    {H : Type u} [Group H] :
    FreeAbelianGroup (FDRep k H) →+ ℤ :=
  FreeAbelianGroup.lift fun V : FDRep k H ↦
    Int.ofNat (Module.finrank k V.1)

/-- Helper for Theorem 16-16.1-5: the Grothendieck relations are killed by the local
dimension lift because finite-dimensional `k`-dimension is additive on short exact sequences. -/
private theorem finiteRepGrothendieckRelations_le_dimensionLift_ker_local
    {H : Type u} [Group H] :
    finiteRepGrothendieckRelations k H ≤
      (finiteRepDimensionLift_local (k := k) (H := H)).ker := by
  -- Forget to `ModuleCat k`, where a short exact sequence records the usual dimension additivity.
  rw [finiteRepGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  let F : FDRep k H ⥤ ModuleCat k :=
    (forget₂ (FDRep k H) (Rep k H)) ⋙ (forget₂ (Rep k H) (ModuleCat k))
  have hSF : (S.map F).ShortExact := by
    simpa [F] using hS.map_of_exact F
  let f : S.X₁.V →ₗ[k] S.X₂.V := (F.map S.f).hom
  let g : S.X₂.V →ₗ[k] S.X₃.V := (F.map S.g).hom
  have hExact : Function.Exact f g := by
    simpa [f, g] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map F)).mp hSF.exact
  have hf : Function.Injective f := by
    simpa [f] using (ModuleCat.mono_iff_injective _).1 hSF.mono_f
  have hg : Function.Surjective g := by
    simpa [g] using (ModuleCat.epi_iff_surjective _).1 hSF.epi_g
  have hdim :
      Module.finrank k S.X₂.V = Module.finrank k S.X₁.V + Module.finrank k S.X₃.V := by
    -- Route correction: compute the coefficient by dimension on the genuine p-group owner,
    -- rather than by another ambient-owner class chase.
    calc
      Module.finrank k S.X₂.V
          = Module.finrank k (LinearMap.range g) +
              Module.finrank k (LinearMap.ker g) := by
              symm
              exact LinearMap.finrank_range_add_finrank_ker g
      _ = Module.finrank k S.X₃.V + Module.finrank k (LinearMap.range f) := by
            rw [hExact.linearMap_ker_eq, LinearMap.range_eq_top.2 hg]
            simp
      _ = Module.finrank k S.X₃.V + Module.finrank k S.X₁.V := by
            rw [LinearMap.finrank_range_of_inj hf]
      _ = Module.finrank k S.X₁.V + Module.finrank k S.X₃.V := by
            rw [add_comm]
  change
    finiteRepDimensionLift_local (k := k) (H := H)
        (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  -- Evaluate the free lift on the defining generator and cancel the resulting exact-sequence sum.
  simp only [finiteRepDimensionLift_local, map_sub, FreeAbelianGroup.lift_apply_of,
    Int.ofNat_eq_natCast]
  rw [hdim, Int.natCast_add]
  abel

/-- Helper for Theorem 16-16.1-5: the dimension homomorphism on LinearRepresentations_Serre_1977's Grothendieck group. -/
private def finiteRepGrothendieckDimension_local
    {H : Type u} [Group H] :
    R₀[k](H) →+ ℤ :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations k H)
    (finiteRepDimensionLift_local (k := k) (H := H))
    (finiteRepGrothendieckRelations_le_dimensionLift_ker_local (k := k) (H := H))

/-- Helper for Theorem 16-16.1-5: the local dimension hom reads a generator class as the ordinary
`k`-dimension of the underlying finite-dimensional representation. -/
@[simp] private theorem finiteRepGrothendieckDimension_local_apply_class
    {H : Type u} [Group H] (W : FDRep k H) :
    finiteRepGrothendieckDimension_local (k := k) (H := H) [W]₀ =
      Module.finrank k W := by
  simp [finiteRepGrothendieckDimension_local, finiteRepDimensionLift_local,
    finiteRepGrothendieckClass]

/-- Helper for Theorem 16-16.1-5: on a finite `p`-group, every finite-dimensional class is its
dimension times the trivial class. -/
theorem fdRep_class_eq_finrank_nsmul_trivial_of_isPGroup
    {H : Type u} [Group H] [Finite H]
    (hH : IsPGroup p H) (W : FDRep k H) :
    [W]₀ = (Module.finrank k W : ℕ) • ([𝟙_ (FDRep k H)]₀ : R₀[k](H)) := by
  classical
  letI : AddCommMonoid (R₀[k](H)) :=
    (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k H)).toAddCommMonoid
  letI : AddCommGroup (R₀[k](H)) :=
    QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k H)
  letI : Module ℤ (R₀[k](H)) := AddCommGroup.toIntModule (R₀[k](H))
  obtain ⟨ι, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_local (k := k) (G := H)
  let b : Module.Basis ι ℤ (R₀[k](H)) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  let t : R₀[k](H) := ([𝟙_ (FDRep k H)]₀ : R₀[k](H))
  have hsimple : ∀ i, b i = t := by
    intro i
    letI : Simple (π i) := hπ_complete.isSimple i
    -- Every simple basis vector collapses to the trivial class on a finite `p`-group.
    simpa [b, t, simple_finiteRep_classes_basis_of_complete_family_apply] using
      (simple_fdRep_class_eq_trivial_of_isPGroup (p := p) (k := k) (H := H) hH (π i))
  have hexpand : [W]₀ = (((b.repr [W]₀).sum fun i a ↦ a) : ℤ) • t := by
    -- Expand `[W]₀` in the simple basis and replace every simple class by the trivial class.
    calc
      [W]₀ = (b.repr [W]₀).sum fun i a ↦ a • b i := by
        symm
        simpa [Finsupp.linearCombination_apply, Finsupp.sum, zsmul_eq_mul] using
          b.linearCombination_repr [W]₀
      _ = (b.repr [W]₀).sum fun i a ↦ a • t := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [hsimple i]
      _ = (((b.repr [W]₀).sum fun i a ↦ a) : ℤ) • t := by
            symm
            simpa [Finsupp.sum] using
              (Finset.sum_smul
                (s := (b.repr [W]₀).support)
                (f := fun i ↦ (b.repr [W]₀) i)
                (x := t))
  have hcoeff : (((b.repr [W]₀).sum fun i a ↦ a) : ℤ) = Module.finrank k W := by
    -- Route correction: read the unique coefficient by the dimension hom instead of another
    -- basis comparison.
    have hdim :=
      congrArg (finiteRepGrothendieckDimension_local (k := k) (H := H)) hexpand
    have htrivial_dim : Module.finrank k (𝟙_ (FDRep k H)) = 1 := by
      change Module.finrank k k = 1
      exact Module.finrank_self k
    have hcoeff_mul :
        (((b.repr [W]₀).sum fun i a ↦ a) : ℤ) *
            (Module.finrank k (𝟙_ (FDRep k H)) : ℤ) =
          Module.finrank k W := by
      simpa [t, finiteRepGrothendieckDimension_local_apply_class, zsmul_eq_mul] using hdim.symm
    rw [htrivial_dim] at hcoeff_mul
    simpa using hcoeff_mul
  -- Convert the resulting integer scalar back to the natural-number scalar used by the statement.
  calc
    [W]₀ = (((b.repr [W]₀).sum fun i a ↦ a) : ℤ) • t := hexpand
    _ = (Module.finrank k W : ℤ) • t := by
          rw [hcoeff]
    _ =
        @HSMul.hSMul ℕ R₀[k](H) R₀[k](H)
          (@instHSMul ℕ R₀[k](H)
            (@AddMonoid.toNSMul R₀[k](H)
              (QuotientAddGroup.Quotient.addGroup
                (finiteRepGrothendieckRelations k H)).toAddMonoid))
          (Module.finrank k W) t := by
            symm
            exact natCast_zsmul t (Module.finrank k W)
    _ = (Module.finrank k W : ℕ) • t := by
          exact quotient_nsmul_eq_ring_nsmul (k := k) (H := H) (Module.finrank k W) t

/-- Helper for Theorem 16-16.1-5: a finite-dimensional representation with subsingleton carrier has
zero Grothendieck class. -/
theorem finiteRepGrothendieckClass_eq_zero_of_subsingleton
    {H : Type u} [Group H]
    (W : FDRep k H) [Subsingleton W] :
    [W]₀ = 0 := by
  have hId : (𝟙 W : W ⟶ W) = 0 := by
    ext x
    exact Subsingleton.elim _ _
  have hZero : CategoryTheory.Limits.IsZero W :=
    (CategoryTheory.Limits.IsZero.iff_id_eq_zero W).2 hId
  simpa using
    (finiteRepGrothendieckClass_eq_of_nonempty_iso (L := k) (G := H)
      (V := W) (W := 0) ⟨hZero.iso (CategoryTheory.Limits.isZero_zero (FDRep k H))⟩)

omit [CharP k p] [Fact p.Prime] in
/-- Helper for Theorem 16-16.1-5: the regular representation of a Sylow subgroup has
`k`-dimension `p ^ n` when the subgroup order is `p ^ n`. -/
theorem sylow_regular_fdRep_finrank_eq_p_pow
    [Finite G]
    (P : Sylow p G) (n : ℕ) (hPcard : Nat.card (P : Subgroup G) = p ^ n) :
    Module.finrank k (FDRep.of (Representation.leftRegular k ↥(P : Subgroup G))) = p ^ n := by
  let H : Type u := ↥(P : Subgroup G)
  letI : Fintype H := Fintype.ofFinite H
  have hcardH : Fintype.card H = p ^ n := by
    simpa [H, Nat.card_eq_fintype_card] using hPcard
  rw [show Module.finrank k (FDRep.of (Representation.leftRegular k H)) = Fintype.card H by
        simpa [Representation.leftRegular] using (Module.finrank_finsupp_self (R := k) (ι := H))]
  exact hcardH

/-- Helper for Theorem 16-16.1-5: if one Cartan-range multiple divides another, the larger
multiple stays in the Cartan range. -/
theorem nsmul_mem_cartan_range_of_dvd
    [Finite G] {N M : ℕ} {y : R₀[k](G)}
    (hNM : N ∣ M) (hy : (N : ℕ) • y ∈ (cartanHom k G).range) :
    (M : ℕ) • y ∈ (cartanHom k G).range := by
  rcases hNM with ⟨t, rfl⟩
  rcases hy with ⟨x, hx⟩
  refine ⟨t • x, ?_⟩
  calc
    cartanHom k G (t • x) = (t : ℕ) • cartanHom k G x := by rw [map_nsmul]
    _ = (t : ℕ) • ((N : ℕ) • y) := by rw [hx]
    _ = ((N * t : ℕ) • y) := by
          simpa [mul_comm] using (smul_smul t N y)

/-- Helper for Theorem 16-16.1-5: if a finite group is a `q`-group for a prime `q ≠ p`, then its
order is prime to `p`. -/
theorem coprime_card_of_isPGroup_of_ne
    {q : ℕ} [Fact q.Prime] {Q : Type u} [Group Q] [Finite Q]
    (hpq : p ≠ q) (hQ : IsPGroup q Q) :
    Nat.Coprime p (Nat.card Q) := by
  obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq hQ
  rw [hn]
  have hnot : ¬ q ∣ p := by
    intro hqp
    exact hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime q) (Fact.out : Nat.Prime p)).mp
      hqp).symm
  exact Nat.Prime.coprime_pow_of_not_dvd (p := q) (a := p) (m := n) (Fact.out : Nat.Prime q) hnot

/-- Helper for Theorem 16-16.1-5: on a product whose left factor has order prime to `p` and whose
right factor is a `p`-group, the `p`-part of the total order is exactly the order of the right
factor. -/
theorem ordProj_card_prod_eq_card_right_of_coprime_left
    {S : Type u} [Group S] [Finite S] {Q : Type u} [Group Q] [Finite Q]
    (hS : Nat.Coprime p (Nat.card S)) (hQ : IsPGroup p Q) :
    ordProj[p] (Nat.card (S × Q)) = Nat.card Q := by
  obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq hQ
  rw [Nat.card_prod, hn]
  have hfacS : (Nat.card S).factorization p = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hpdiv
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).mp hS hpdiv
  rw [Nat.factorization_mul (a := Nat.card S) (b := p ^ n) Nat.card_pos.ne'
    (pow_ne_zero _ (Nat.Prime.ne_zero (Fact.out : Nat.Prime p)))]
  simp [hfacS, Fact.out]

omit [Group G] in
/-- Helper for Theorem 16-16.1-5: the displayed factorization of `|G|` identifies its `p`-part
with `p ^ n`. -/
theorem ordProj_card_eq_p_pow_of_card_factorization
    [Finite G] (n m : ℕ) (hcard : Nat.card G = p ^ n * m) (hm : Nat.Coprime p m) :
    ordProj[p] (Nat.card G) = p ^ n := by
  let hp' : Nat.Prime p := Fact.out
  have hm0 : m ≠ 0 := by
    intro hm_eq_zero
    have : Nat.Coprime p 0 := by
      simpa [hm_eq_zero] using hm
    exact hp'.ne_one <| by
      simpa [Nat.coprime_zero_right] using this
  have hfactorization_m : m.factorization p = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdiv
    have hm1 : p ∣ 1 := by
      exact hm.dvd_of_dvd_mul_left (by simpa using hdiv)
    exact hp'.not_dvd_one hm1
  change p ^ (Nat.card G).factorization p = p ^ n
  rw [hcard]
  rw [Nat.factorization_mul (a := p ^ n) (b := m) (pow_ne_zero _ hp'.ne_zero) hm0]
  simp [hp'.factorization_pow, hfactorization_m]

end

end Representation
