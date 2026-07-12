import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape DerivedCategory HomotopyCategory

noncomputable section

universe v u

namespace CochainComplex

attribute [local instance] HasDerivedCategory.standard

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- Helper for Remark 13.19.5: the bounded-above cochain complexes whose terms are projective. -/
private abbrev ProjectiveMinus
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :=
  { P : CochainComplex 𝒜 ℤ //
      ∃ d : ℤ, P.IsStrictlyLE d ∧ ∀ n : ℤ, Projective (P.X n) }

/-
Domain-style sampling:
- primary domain: morphisms from bounded-above projective cochain complexes in the homotopy and
  derived categories of an abelian category;
- sampled owner declarations:
  `ProjectiveMinus`,
  `CochainComplex.IsKProjective`,
  `DerivedCategory.isIso_Q_map_iff_quasiIso`,
  `NatIso.isIso_map_iff`;
- best owner abstraction: `ProjectiveMinus 𝒜` is the local owner for the bounded-above
  projective source, and its bounded-above/projective data feed the canonical `IsKProjective`
  API directly;
- primitive data: a quasi-isomorphism `α : K ⟶ L` and a source complex `P : ProjectiveMinus 𝒜`;
- derived API: bijectivity of postcomposition by `α` in the homotopy category.

This remark is therefore a `bridge/view`: it should take the source-facing owner
`ProjectiveMinus 𝒜` directly and transport postcomposition bijectivity from the derived category
through the canonical `IsKProjective` comparison theorem, rather than routing through the stale
chapter dependency that currently blocks this item.
-/

-- Proof sketch: the bounded-above/projective data on `P` give the canonical `IsKProjective`
-- instance for the source complex. The quasi-isomorphism `α` becomes an isomorphism in the
-- derived category, where postcomposition is bijective. Transporting that bijection back across
-- the `Qh.map` comparison for K-projective sources yields the homotopy-category bijection.
/-- Remark 13.19.5: if `α : K^• ⟶ L^•` is a quasi-isomorphism and `P^•` is a bounded-above
cochain complex of projective objects, then postcomposition with `α` induces a bijection
`Hom_{K(\mathcal A)}(P^•, K^•) ≃ Hom_{K(\mathcal A)}(P^•, L^•)`. -/
@[stacks 0648]
theorem homotopyCategory_postcomp_bijective_of_quasiIso_from_boundedAbove_projective
    {K L : CochainComplex 𝒜 ℤ} (α : K ⟶ L) [QuasiIso α] (P : ProjectiveMinus 𝒜) :
    Function.Bijective
      (fun g : (quotient 𝒜 (up ℤ)).obj P ⟶ (quotient 𝒜 (up ℤ)).obj K ↦
        g ≫ (quotient 𝒜 (up ℤ)).map α) := by
  let Q := quotient 𝒜 (up ℤ)
  obtain ⟨d, hd, hproj⟩ := P.2
  let _ : (P : CochainComplex 𝒜 ℤ).IsStrictlyLE d := hd
  let _ : ∀ n : ℤ, Projective ((P : CochainComplex 𝒜 ℤ).X n) := hproj
  let _ : IsKProjective (P : CochainComplex 𝒜 ℤ) :=
    isKProjective_of_projective (P : CochainComplex 𝒜 ℤ) d
  -- Transport the quasi-isomorphism to an isomorphism in the derived category.
  have hα : IsIso (Qh.map (Q.map α)) := by
    change IsIso ((Q ⋙ Qh).map α)
    exact ((NatIso.isIso_map_iff (quotientCompQhIso 𝒜) α)).2
      ((isIso_Q_map_iff_quasiIso 𝒜 α).2 inferInstance)
  -- Postcomposition by an isomorphism is bijective in the derived category.
  have hpostD :
      Function.Bijective
        (fun g : Qh.obj (Q.obj P) ⟶ Qh.obj (Q.obj K) ↦ g ≫ Qh.map (Q.map α)) := by
    refine ⟨?_, ?_⟩
    · intro g₁ g₂ h
      exact (cancel_mono (Qh.map (Q.map α))).1 h
    · intro g
      refine ⟨g ≫ inv (Qh.map (Q.map α)), ?_⟩
      simp [Category.assoc]
  -- The bounded-above projective owner carries the canonical `IsKProjective` instance.
  have hK :
      Function.Bijective
        (Qh.map : (Q.obj P ⟶ Q.obj K) → (Qh.obj (Q.obj P) ⟶ Qh.obj (Q.obj K))) := by
    simpa using IsKProjective.Qh_map_bijective (P : CochainComplex 𝒜 ℤ) (Q.obj K)
  have hL :
      Function.Bijective
        (Qh.map : (Q.obj P ⟶ Q.obj L) → (Qh.obj (Q.obj P) ⟶ Qh.obj (Q.obj L))) := by
    simpa using IsKProjective.Qh_map_bijective (P : CochainComplex 𝒜 ℤ) (Q.obj L)
  -- This is the commutative square relating postcomposition in `K(𝒜)` and in `D(𝒜)`.
  have hcomp :
      ((Qh.map : (Q.obj P ⟶ Q.obj L) → (Qh.obj (Q.obj P) ⟶ Qh.obj (Q.obj L))) ∘
        fun g : Q.obj P ⟶ Q.obj K ↦ g ≫ Q.map α) =
      (fun g : Qh.obj (Q.obj P) ⟶ Qh.obj (Q.obj K) ↦ g ≫ Qh.map (Q.map α)) ∘
        (Qh.map : (Q.obj P ⟶ Q.obj K) → (Qh.obj (Q.obj P) ⟶ Qh.obj (Q.obj K))) := by
    funext g
    simp [Functor.map_comp]
  -- Conjugate the derived-category bijection across the two comparison bijections.
  have hbijcomp :
      Function.Bijective
        (((Qh.map : (Q.obj P ⟶ Q.obj L) → (Qh.obj (Q.obj P) ⟶ Qh.obj (Q.obj L))) ∘
          fun g : Q.obj P ⟶ Q.obj K ↦ g ≫ Q.map α)) := by
    rw [hcomp]
    exact hpostD.comp hK
  exact (Function.Bijective.of_comp_iff' hL _).mp hbijcomp

end CochainComplex
