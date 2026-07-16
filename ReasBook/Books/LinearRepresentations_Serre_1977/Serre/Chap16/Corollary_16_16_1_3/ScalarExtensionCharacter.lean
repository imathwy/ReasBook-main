import LinearRepresentations_Serre_1977.Serre.Chap16.Corollary_16_16_1_3.GrothendieckCharacter
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_2_6.Index

noncomputable section

open CategoryTheory
open scoped Representation

universe u v w

namespace Representation

namespace ProjectiveScalarExtensionSplitInjective

section

variable {K : Type} [Field K]
variable {K' : Type} [Field K'] [Algebra K K'] [FiniteDimensional K K']
variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
/-- Helper for Corollary 16-16.1-3: scalar extension sends the reversed characteristic
polynomial of the negated action endomorphism to the coefficientwise image of the original
polynomial. -/
theorem negCharpolyReverse_scalarExtension_eq_map_local
    {Ω : Type*} [Field Ω] [Algebra K Ω]
    {X : Type v} [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    (τ : Representation K G X) (g : G) :
    ((-(Representation.scalarExtension (k := Ω) τ g)).charpoly.reverse : Polynomial Ω) =
      Polynomial.map (algebraMap K Ω) (((-τ g).charpoly.reverse : Polynomial K)) := by
  have hneg :
      -(Representation.scalarExtension (k := Ω) τ g) = LinearMap.baseChange Ω (-τ g) := by
    simp [Representation.scalarExtension, Module.End.baseChangeHom, LinearMap.baseChangeHom_apply]
  rw [hneg, LinearMap.charpoly_baseChange]
  symm
  exact
    polynomial_reverse_map (f := algebraMap K Ω)
      (hf := FaithfulSMul.algebraMap_injective K Ω) ((-τ g).charpoly)

omit [Finite G] in
/-- Helper for Corollary 16-16.1-3: an upstairs scalar-extension equivalence forces equality of
the determinant polynomials `det (1 + ρ(g) T)` downstairs. -/
theorem detOneAddPolynomialEq_of_scalarExtension_equiv_local
    {Ω : Type*} [Field Ω] [Algebra K Ω]
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {W : Type v} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (hΩ :
      Nonempty
        ((Representation.scalarExtension (k := Ω) ρ).Equiv
          (Representation.scalarExtension (k := Ω) σ))) :
    ∀ g : G, (-ρ g).charpoly.reverse = (-σ g).charpoly.reverse := by
  rcases hΩ with ⟨eΩ⟩
  intro g
  have hcharΩ :
      (-(Representation.scalarExtension (k := Ω) ρ g)).charpoly =
        (-(Representation.scalarExtension (k := Ω) σ g)).charpoly := by
    have hconj_pos :
        eΩ.toLinearEquiv.conj ((Representation.scalarExtension (k := Ω) ρ) g) =
          (Representation.scalarExtension (k := Ω) σ) g := by
      simpa using
        (Representation.Equiv.conj_apply_self
          (ρ := Representation.scalarExtension (k := Ω) ρ)
          (σ := Representation.scalarExtension (k := Ω) σ) g eΩ)
    have hconj :
        eΩ.toLinearEquiv.conj (-(Representation.scalarExtension (k := Ω) ρ g)) =
          -(Representation.scalarExtension (k := Ω) σ g) := by
      simp [hconj_pos]
    have hchar := LinearEquiv.charpoly_conj eΩ.toLinearEquiv
      (-(Representation.scalarExtension (k := Ω) ρ g))
    rw [hconj] at hchar
    exact hchar.symm
  have hmap :
      Polynomial.map (algebraMap K Ω) (((-ρ g).charpoly.reverse : Polynomial K)) =
        Polynomial.map (algebraMap K Ω) (((-σ g).charpoly.reverse : Polynomial K)) := by
    calc
      Polynomial.map (algebraMap K Ω) (((-ρ g).charpoly.reverse : Polynomial K))
          = ((-(Representation.scalarExtension (k := Ω) ρ g)).charpoly.reverse :
              Polynomial Ω) := by
              symm
              exact negCharpolyReverse_scalarExtension_eq_map_local (τ := ρ) g
      _ = ((-(Representation.scalarExtension (k := Ω) σ g)).charpoly.reverse :
            Polynomial Ω) := by
            exact congrArg Polynomial.reverse hcharΩ
      _ = Polynomial.map (algebraMap K Ω) (((-σ g).charpoly.reverse : Polynomial K)) := by
            exact negCharpolyReverse_scalarExtension_eq_map_local (τ := σ) g
  exact
    (Polynomial.map_injective (algebraMap K Ω)
      (FaithfulSMul.algebraMap_injective K Ω)) hmap

omit [Finite G] in
/-- Helper for Corollary 16-16.1-3: an equivalence of the descended common-image modules
intertwines the original monoid representations. -/
theorem nonempty_equiv_of_common_kernel_quotient_linearEquiv_local
    {A : Type*} [Ring A] [Algebra K A]
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {W : Type v} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (φV : A →ₐ[K] Module.End K V) (φW : A →ₐ[K] Module.End K W)
    (liftι : MonoidAlgebra K G →ₐ[K] A)
    (hφV : φV.comp liftι = ρ.asAlgebraHom)
    (hφW : φW.comp liftι = σ.asAlgebraHom)
    [Module A V] [Module A W]
    [IsScalarTower K A V] [IsScalarTower K A W]
    (hsmulV : ∀ a : A, ∀ x : V, a • x = (φV a) x)
    (hsmulW : ∀ a : A, ∀ x : W, a • x = (φW a) x)
    (e : V ≃ₗ[A] W) :
    Nonempty (ρ.Equiv σ) := by
  refine ⟨Representation.Equiv.mk (e.restrictScalars K) ?_⟩
  intro g
  ext x
  have hρg : ρ g = φV (liftι (MonoidAlgebra.of K G g)) := by
    simpa [AlgHom.comp_apply, Representation.asAlgebraHom_of] using
      congrArg
        (fun f : MonoidAlgebra K G →ₐ[K] Module.End K V ↦ f (MonoidAlgebra.of K G g))
        hφV.symm
  have hσg : σ g = φW (liftι (MonoidAlgebra.of K G g)) := by
    simpa [AlgHom.comp_apply, Representation.asAlgebraHom_of] using
      congrArg
        (fun f : MonoidAlgebra K G →ₐ[K] Module.End K W ↦ f (MonoidAlgebra.of K G g))
        hφW.symm
  calc
    e (ρ g x) = e (liftι (MonoidAlgebra.of K G g) • x) := by rw [hρg, hsmulV]
    _ = liftι (MonoidAlgebra.of K G g) • e x := by
          exact e.map_smul (liftι (MonoidAlgebra.of K G g)) x
    _ = (φW (liftι (MonoidAlgebra.of K G g))) (e x) := by rw [hsmulW]
    _ = σ g (e x) := by rw [← hσg]

omit [Finite G] in
/-- Helper for Corollary 16-16.1-3: determinant-polynomial equality identifies two semisimple
finite-dimensional monoid representations. -/
theorem nonempty_equiv_of_isSemisimple_of_det_one_add_polynomial_eq_local
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {W : Type v} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (hρ : IsSemisimpleRepresentation ρ)
    (hσ : IsSemisimpleRepresentation σ)
    (hdet : ∀ g : G, (-ρ g).charpoly.reverse = (-σ g).charpoly.reverse) :
    Nonempty (ρ.Equiv σ) := by
  -- This is exactly the Chapter 18 Brauer-Nesbitt criterion for semisimple representations.
  exact
    Representation.nonempty_equiv_of_isSemisimple_of_det_one_add_polynomial_eq_support
      (k := K) (G := G) (X := V) (Y := W) (ρ := ρ) (ρ' := σ) hρ hσ hdet

omit [Finite G] in
/-- Helper for Corollary 16-16.1-3: if two semisimple `G`-representations become equivalent
after scalar extension to a larger field, then the equivalence already descends to the base
field. -/
theorem nonempty_equiv_of_scalarExtension_equiv_local
    {Ω : Type*} [Field Ω] [Algebra K Ω]
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {W : Type v} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (hρ : IsSemisimpleRepresentation ρ)
    (hσ : IsSemisimpleRepresentation σ)
    (hΩ :
      Nonempty
        ((Representation.scalarExtension (k := Ω) ρ).Equiv
          (Representation.scalarExtension (k := Ω) σ))) :
    Nonempty (ρ.Equiv σ) :=
  nonempty_equiv_of_isSemisimple_of_det_one_add_polynomial_eq_local (ρ := ρ) (σ := σ) hρ hσ
    (detOneAddPolynomialEq_of_scalarExtension_equiv_local (ρ := ρ) (σ := σ) hΩ)

omit [FiniteDimensional K K'] [Finite G] in
/-- Helper for Corollary 16-16.1-3: a basiswise retract upgrades to a genuine left inverse once
ordinary scalar extension is known to be injective. -/
theorem finiteRepGrothendieckScalarExtension_leftInverse_of_rightInverse_and_injective_local
    (r : R₀[K'](G) →+ R₀[K](G))
    (hr : (finiteRepGrothendieckScalarExtensionHom K K' G).comp r = AddMonoidHom.id _)
    (hinj : Function.Injective (finiteRepGrothendieckScalarExtensionHom K K' G)) :
    Function.LeftInverse r (finiteRepGrothendieckScalarExtensionHom K K' G) := by
  intro x
  -- Apply the right-inverse identity at `f x` and then reflect back along injectivity.
  apply hinj
  have hr_apply :=
    congrArg (fun f : R₀[K'](G) →+ R₀[K'](G) =>
      f ((finiteRepGrothendieckScalarExtensionHom K K' G) x)) hr
  simpa [AddMonoidHom.comp_apply] using hr_apply

omit [FiniteDimensional K K'] [Finite G] in
/-- Helper for Corollary 16-16.1-3: once a complete simple family over `K` stays complete and
pairwise nonisomorphic after scalar extension to `K'`, the induced map on `R₀` is a basis
transport isomorphism. -/
theorem finiteRepGrothendieckScalarExtension_retract_data_of_complete_simple_family_local
    {ι : Type*}
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hπ'_pairwise :
      PairwiseNonisomorphic (fun i ↦ ((FDRep.scalarExtension (π i) : FDRep K' G))))
    (hπ'_complete :
      IsCompleteIrreducibleFamily (fun i ↦ ((FDRep.scalarExtension (π i) : FDRep K' G)))) :
    ∃ r : R₀[K'](G) →+ R₀[K](G),
      (finiteRepGrothendieckScalarExtensionHom K K' G).comp r = AddMonoidHom.id _ ∧
        Function.Injective (finiteRepGrothendieckScalarExtensionHom K K' G) := by
  classical
  let b : Module.Basis ι ℤ (R₀[K](G)) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  let b' : Module.Basis ι ℤ (R₀[K'](G)) :=
    simple_finiteRep_classes_basis_of_complete_family
      (fun i ↦ ((FDRep.scalarExtension (π i) : FDRep K' G))) hπ'_pairwise hπ'_complete
  let fL : R₀[K](G) →ₗ[ℤ] R₀[K'](G) :=
    (finiteRepGrothendieckScalarExtensionHom K K' G).toIntLinearMap
  let rL : R₀[K'](G) →ₗ[ℤ] R₀[K](G) := b'.constr ℤ b
  have hbasis_add : ∀ i,
      finiteRepGrothendieckScalarExtensionHom K K' G (b i) = b' i := by
    intro i
    -- Scalar extension sends the simple basis class `[π i]₀` to the matching simple class over
    -- `K'`, so the two chosen bases are transported termwise.
    rw [show b i = [π i]₀ by
      simp [b, simple_finiteRep_classes_basis_of_complete_family_apply]]
    rw [show b' i = [((FDRep.scalarExtension (π i) : FDRep K' G))]₀ by
      simp [b', simple_finiteRep_classes_basis_of_complete_family_apply]]
    rw [finiteRepGrothendieckScalarExtensionHom_class_eq]
  have hbasis : ∀ i, fL (b i) = b' i := by
    intro i
    simpa [fL] using hbasis_add i
  have hrightL : fL.comp rL = LinearMap.id := by
    -- On the target simple basis, the reconstruction map sends each basis vector back to its
    -- chosen source preimage and scalar extension returns the original basis vector.
    apply b'.ext
    intro i
    simp [rL, hbasis i]
  have hleftL : rL.comp fL = LinearMap.id := by
    -- The same basis comparison shows that the transported basis vectors over `K` are recovered
    -- after applying scalar extension and then the basis-defined inverse.
    apply b.ext
    intro i
    simp [rL, hbasis i]
  let r : R₀[K'](G) →+ R₀[K](G) := rL.toAddMonoidHom
  refine ⟨r, ?_, ?_⟩
  · -- Repackage the linear right-inverse identity as an equality of additive homomorphisms.
    apply AddMonoidHom.ext
    intro x
    have hright_apply :=
      congrArg (fun t : R₀[K'](G) →ₗ[ℤ] R₀[K'](G) => t x) hrightL
    simpa [fL, r, LinearMap.comp_apply] using hright_apply
  · -- The linear left-inverse identity immediately gives injectivity of scalar extension.
    intro x y hxy
    have hleft_apply_x :=
      congrArg (fun t : R₀[K](G) →ₗ[ℤ] R₀[K](G) => t x) hleftL
    have hleft_apply_y :=
      congrArg (fun t : R₀[K](G) →ₗ[ℤ] R₀[K](G) => t y) hleftL
    calc
      x = rL (fL x) := by simpa [LinearMap.comp_apply] using hleft_apply_x.symm
      _ = rL (fL y) := by simpa [fL] using congrArg rL hxy
      _ = y := by simpa [LinearMap.comp_apply] using hleft_apply_y

end

end ProjectiveScalarExtensionSplitInjective

end Representation
