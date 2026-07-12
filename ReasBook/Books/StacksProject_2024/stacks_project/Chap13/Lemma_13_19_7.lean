import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape DerivedCategory HomotopyCategory

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable {K L : CochainComplex 𝒜 ℤ}

attribute [local instance] HasDerivedCategory.standard

local notation "KQ" => HomotopyCategory.quotient 𝒜 (up ℤ)

/-- Helper for Lemma 13.19.7: the bounded-above cochain complexes whose terms are projective. -/
private abbrev ProjectiveMinus
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :=
  { P : CochainComplex 𝒜 ℤ //
      ∃ d : ℤ, P.IsStrictlyLE d ∧ ∀ n : ℤ, Projective (P.X n) }

/- Domain-style sampling:
- primary domain: uniqueness of homotopy lifts from bounded-above projective cochain complexes
  along quasi-isomorphisms;
- sampled owner declarations:
  `CochainComplex.ProjectiveMinus`,
  `CochainComplex.MinusWithTermsIn.minus`,
  `CochainComplex.MinusWithTermsIn.term_mem`,
  `homotopyCategory_postcomp_bijective_of_quasiIso_from_boundedAbove_projective`,
  `HomotopyCategory.eq_of_homotopy`,
  `HomotopyCategory.homotopyOfEq`;
- best owner abstraction: `ProjectiveMinus 𝒜` is the chapter owner for a bounded-above complex of
  projective objects, so this lemma should take that owner directly
  instead of separate boundedness and termwise-projective hypotheses;
- primitive data: a projective-minus source complex `P`, a quasi-isomorphism `α : L ⟶ K`, and
  maps `γ : P ⟶ K`, `β₁, β₂ : P ⟶ L`;
- derived API: uniqueness of lifts up to homotopy, obtained from the owner-level bijectivity of
  postcomposition in the homotopy category.

Source/core/bridge triage:
- `source-facing`: the uniqueness-up-to-homotopy statement below;
- `core/canonical`: `ProjectiveMinus 𝒜` and the homotopy-category postcomposition bijection for
  K-projective sources;
- `bridge/view`: the passage from commuting-up-to-homotopy triangles to equality in the homotopy
  category, then back to a homotopy via `homotopyOfEq`.
-/

-- Proof sketch: pass to the homotopy category. The hypotheses `β₁ ≫ α ∼ γ` and `β₂ ≫ α ∼ γ`
-- say that postcomposition by `α` sends the classes of `β₁` and `β₂` to the same morphism
-- `P^• ⟶ K^•`. By the earlier bijectivity theorem for bounded-above projective sources,
-- postcomposition with the quasi-isomorphism `α` is bijective on maps out of `P^•`, so those
-- classes are equal; then
-- `HomotopyCategory.homotopyOfEq` yields a homotopy `β₁ ∼ β₂`.
/-- Helper for Lemma 13.19.7: a homotopy between `β ≫ α` and `γ` becomes an equality after
passing to the homotopy category. -/
lemma postcomp_image_eq_of_homotopy
    (P : ProjectiveMinus 𝒜) (α : L ⟶ K)
    (γ : (P : CochainComplex 𝒜 ℤ) ⟶ K)
    (β : (P : CochainComplex 𝒜 ℤ) ⟶ L)
    (h : Homotopy (β ≫ α) γ) :
    ((KQ).map β) ≫ ((KQ).map α) = (KQ).map γ := by
  -- The homotopy gives equality of quotient classes, and the quotient functor preserves
  -- composition.
  let Q := HomotopyCategory.quotient 𝒜 (up ℤ)
  simpa [Q, Functor.map_comp] using (eq_of_homotopy _ _ h)

/-- Helper for Lemma 13.19.7: postcomposition with a quasi-isomorphism is bijective on
homotopy-category morphisms out of a bounded-above projective complex. -/
theorem postcomp_bijective_of_quasiIso_from_boundedAbove_projective
    (P : ProjectiveMinus 𝒜) (α : L ⟶ K) [QuasiIso α] :
    Function.Bijective
      (fun g : (KQ).obj P ⟶ (KQ).obj L ↦
        g ≫ (KQ).map α) := by
  let Q := KQ
  obtain ⟨d, hd, hproj⟩ := P.2
  let _ : (P : CochainComplex 𝒜 ℤ).IsStrictlyLE d := hd
  let _ : ∀ n : ℤ, Projective ((P : CochainComplex 𝒜 ℤ).X n) := hproj
  let _ : (P : CochainComplex 𝒜 ℤ).IsKProjective :=
    isKProjective_of_projective (P : CochainComplex 𝒜 ℤ) d
  -- Transport the quasi-isomorphism to an isomorphism in the derived category.
  have hα : IsIso (Qh.map (Q.map α)) := by
    change IsIso ((Q ⋙ Qh).map α)
    exact ((NatIso.isIso_map_iff (quotientCompQhIso 𝒜) α)).2
      ((isIso_Q_map_iff_quasiIso 𝒜 α).2 inferInstance)
  -- Postcomposition with an isomorphism is bijective in the derived category.
  have hpostD :
      Function.Bijective
        (fun g : Qh.obj (Q.obj P) ⟶ Qh.obj (Q.obj L) ↦ g ≫ Qh.map (Q.map α)) := by
    refine ⟨?_, ?_⟩
    · intro g₁ g₂ h
      exact (cancel_mono (Qh.map (Q.map α))).1 h
    · intro g
      refine ⟨g ≫ inv (Qh.map (Q.map α)), ?_⟩
      simp [Category.assoc]
  -- Compare homotopy and derived morphisms using K-projectivity of the bounded-above
  -- projective source.
  have hL :
      Function.Bijective
        (Qh.map : (Q.obj P ⟶ Q.obj L) → (Qh.obj (Q.obj P) ⟶ Qh.obj (Q.obj L))) := by
    simpa using IsKProjective.Qh_map_bijective (P : CochainComplex 𝒜 ℤ) (Q.obj L)
  have hK :
      Function.Bijective
        (Qh.map : (Q.obj P ⟶ Q.obj K) → (Qh.obj (Q.obj P) ⟶ Qh.obj (Q.obj K))) := by
    simpa using IsKProjective.Qh_map_bijective (P : CochainComplex 𝒜 ℤ) (Q.obj K)
  have hcomp :
      ((Qh.map : (Q.obj P ⟶ Q.obj K) → (Qh.obj (Q.obj P) ⟶ Qh.obj (Q.obj K))) ∘
        fun g : Q.obj P ⟶ Q.obj L ↦ g ≫ Q.map α) =
      (fun g : Qh.obj (Q.obj P) ⟶ Qh.obj (Q.obj L) ↦ g ≫ Qh.map (Q.map α)) ∘
        (Qh.map : (Q.obj P ⟶ Q.obj L) → (Qh.obj (Q.obj P) ⟶ Qh.obj (Q.obj L))) := by
    funext g
    simp [Functor.map_comp]
  have hbijcomp :
      Function.Bijective
        (((Qh.map : (Q.obj P ⟶ Q.obj K) → (Qh.obj (Q.obj P) ⟶ Qh.obj (Q.obj K))) ∘
          fun g : Q.obj P ⟶ Q.obj L ↦ g ≫ Q.map α)) := by
    rw [hcomp]
    exact hpostD.comp hL
  exact (Function.Bijective.of_comp_iff' hK _).mp hbijcomp

/-- Lemma 13.19.7: if `α : L^• ⟶ K^•` is a quasi-isomorphism, `P^•` is bounded above with
projective terms, and two morphisms `β₁, β₂ : P^• ⟶ L^•` both make the triangle with
`γ : P^• ⟶ K^•` commute up to homotopy, then `β₁` and `β₂` are homotopic. -/
theorem homotopic_lifts_along_quasiIso_from_boundedAbove_projective
    (P : ProjectiveMinus 𝒜) (α : L ⟶ K) [QuasiIso α]
    (γ : (P : CochainComplex 𝒜 ℤ) ⟶ K)
    (β₁ β₂ : (P : CochainComplex 𝒜 ℤ) ⟶ L)
    (hβ₁ : Nonempty (Homotopy (β₁ ≫ α) γ))
    (hβ₂ : Nonempty (Homotopy (β₂ ≫ α) γ)) :
    Nonempty (Homotopy β₁ β₂) := by
  let Q := HomotopyCategory.quotient 𝒜 (up ℤ)
  obtain ⟨hβ₁⟩ := hβ₁
  obtain ⟨hβ₂⟩ := hβ₂
  -- Route correction: keep the source-proof route in the homotopy category, rather than
  -- unfolding bounded-above/projective data on `P`.
  refine ⟨homotopyOfEq _ _ ?_⟩
  -- Injectivity of postcomposition with `α` in the homotopy category reduces the goal to
  -- equality after composing with `α`.
  apply (postcomp_bijective_of_quasiIso_from_boundedAbove_projective P α).injective
  -- Both postcompositions agree with the common class of `γ`, so the two lift classes coincide.
  simpa [Q, Functor.map_comp] using
    (eq_of_homotopy _ _ hβ₁).trans (eq_of_homotopy _ _ hβ₂).symm

end CochainComplex
