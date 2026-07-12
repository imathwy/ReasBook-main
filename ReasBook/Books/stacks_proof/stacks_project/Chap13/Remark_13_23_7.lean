import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape DerivedCategory HomotopyCategory

noncomputable section

universe v u

namespace CochainComplex

attribute [local instance] HasDerivedCategory.standard

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- Helper for Remark 13.23.7: an injective resolution of a cochain complex is a quasi-isomorphism
into a bounded-below cochain complex with injective terms. -/
structure InjectiveResolution (K : CochainComplex 𝒜 ℤ) where
  /-- The resolving bounded-below cochain complex. -/
  complex : CochainComplex 𝒜 ℤ
  /-- The resolving complex vanishes in sufficiently negative degrees. -/
  boundedBelow : ∃ a : ℤ, complex.IsStrictlyGE a
  /-- Each term of the resolving complex is injective. -/
  injective : ∀ n : ℤ, Injective (complex.X n)
  /-- The comparison morphism from the source complex to the resolving complex. -/
  ι : K ⟶ complex
  /-- The comparison morphism is a quasi-isomorphism. -/
  quasiIso : QuasiIso ι

attribute [instance] InjectiveResolution.quasiIso

/- Domain-style sampling:
- primary domain: canonical comparison morphisms between injective resolutions of the same
  cochain complex in the homotopy category;
- sampled owner declarations:
  `CochainComplex.InjectiveResolution`,
  `CochainComplex.InjectiveResolution.injective`,
  `CochainComplex.InjectiveResolution.plus`,
  `CochainComplex.homotopyCategory_precomp_bijective_of_quasiIso_to_boundedBelow_injective`;
- best owner abstraction: the source-facing owner here is
  `CochainComplex.InjectiveResolution`, while the precomposition bijection of Remark 13.18.5 is
  the core/canonical theorem controlling comparison morphisms into a bounded-below injective
  complex;
- primitive data: a cochain complex `K` together with injective resolutions `I`, `J` of `K`;
- derived API: the canonical homotopy-category comparison morphism `I ⟶ J` and the
  source-facing uniqueness statement that characterizes it.

Source/core/bridge triage:
- `source-facing`: the `InjectiveResolution` comparison morphism and its uniqueness statement;
- `core/canonical`: `homotopyCategory_precomp_bijective_of_quasiIso_to_boundedBelow_injective`;
- `bridge/view`: none; this file should use the core bijection directly rather than introducing a
  parallel local comparison-morphism API outside the injective-resolution owner namespace.
-/

namespace InjectiveResolution

/-- Helper for Remark 13.23.7: an injective resolution is used through its underlying cochain
complex. -/
instance {K : CochainComplex 𝒜 ℤ} : CoeOut (InjectiveResolution K) (CochainComplex 𝒜 ℤ) where
  coe I := I.complex

/-- Helper for Remark 13.23.7: the resolving complex of an injective resolution is K-injective. -/
instance instIsKInjective {K : CochainComplex 𝒜 ℤ} (I : InjectiveResolution K) :
    IsKInjective (I : CochainComplex 𝒜 ℤ) := by
  obtain ⟨a, ha⟩ := I.boundedBelow
  let _ : (I : CochainComplex 𝒜 ℤ).IsStrictlyGE a := ha
  let _ : ∀ n : ℤ, Injective ((I : CochainComplex 𝒜 ℤ).X n) := I.injective
  exact isKInjective_of_injective (I : CochainComplex 𝒜 ℤ) a

/-- Helper for Remark 13.23.7: precomposition with the quasi-isomorphism of an injective
resolution is bijective on homotopy-category morphisms into another injective resolution. -/
private theorem comparison_bijective {K : CochainComplex 𝒜 ℤ} (I J : InjectiveResolution K) :
    Function.Bijective
      (fun a : (quotient 𝒜 (up ℤ)).obj I ⟶ (quotient 𝒜 (up ℤ)).obj J ↦
        (quotient 𝒜 (up ℤ)).map I.ι ≫ a) := by
  let Q := quotient 𝒜 (up ℤ)
  -- Pass to the derived category, where the quasi-isomorphism becomes an isomorphism.
  have hι : IsIso (Qh.map (Q.map I.ι)) := by
    change IsIso ((Q ⋙ Qh).map I.ι)
    exact ((NatIso.isIso_map_iff (quotientCompQhIso 𝒜) I.ι)).2
      ((isIso_Q_map_iff_quasiIso 𝒜 I.ι).2 inferInstance)
  let eι : Qh.obj (Q.obj K) ≅ Qh.obj (Q.obj I) := asIso (Qh.map (Q.map I.ι))
  have hpreD :
      Function.Bijective
        (fun g : Qh.obj (Q.obj I) ⟶ Qh.obj (Q.obj J) ↦ Qh.map (Q.map I.ι) ≫ g) := by
    refine ⟨?_, ?_⟩
    · intro g₁ g₂ h
      exact (eι.symm.homCongr (Iso.refl _)).injective (by simpa [eι] using h)
    · intro g
      obtain ⟨g', hg'⟩ := (eι.symm.homCongr (Iso.refl _)).surjective g
      refine ⟨g', ?_⟩
      simpa [eι] using hg'
  -- Compare homotopy and derived morphisms using K-injectivity of the target resolution.
  let hI := IsKInjective.Qh_map_bijective (Q.obj I) J
  let hK := IsKInjective.Qh_map_bijective (Q.obj K) J
  have hcomp :
      ((Qh.map :
          (Q.obj K ⟶ Q.obj J) → (Qh.obj (Q.obj K) ⟶ Qh.obj (Q.obj J))) ∘
        fun g : Q.obj I ⟶ Q.obj J ↦ Q.map I.ι ≫ g) =
      (fun g : Qh.obj (Q.obj I) ⟶ Qh.obj (Q.obj J) ↦ Qh.map (Q.map I.ι) ≫ g) ∘
        (Qh.map : (Q.obj I ⟶ Q.obj J) → (Qh.obj (Q.obj I) ⟶ Qh.obj (Q.obj J))) := by
    funext g
    simp
  have hbijcomp :
      Function.Bijective
        ((Qh.map :
            (Q.obj K ⟶ Q.obj J) → (Qh.obj (Q.obj K) ⟶ Qh.obj (Q.obj J))) ∘
          fun g : Q.obj I ⟶ Q.obj J ↦ Q.map I.ι ≫ g) := by
    rw [hcomp]
    exact hpreD.comp hI
  exact (Function.Bijective.of_comp_iff' hK _).mp hbijcomp

/-- Helper for Remark 13.23.7: precomposition with `I.ι` gives the canonical bijection on hom-sets
into the homotopy-category image of `J`. -/
private noncomputable def comparisonEquiv {K : CochainComplex 𝒜 ℤ} (I J : InjectiveResolution K) :
    ((quotient 𝒜 (up ℤ)).obj I ⟶ (quotient 𝒜 (up ℤ)).obj J) ≃
      ((quotient 𝒜 (up ℤ)).obj K ⟶ (quotient 𝒜 (up ℤ)).obj J) :=
  let Q := quotient 𝒜 (up ℤ)
  Equiv.ofBijective (fun a : Q.obj I ⟶ Q.obj J ↦ Q.map I.ι ≫ a) (comparison_bijective I J)

-- Proof sketch: apply the core owner theorem
-- `homotopyCategory_precomp_bijective_of_quasiIso_to_boundedBelow_injective` to the
-- quasi-isomorphism `I.ι : K ⟶ I`. The desired morphism is the unique preimage of the class of
-- `J.ι` under the resulting bijection.
/-- The canonical comparison morphism between two injective resolutions of the same cochain
complex in the homotopy category. -/
noncomputable def homotopyComparison {K : CochainComplex 𝒜 ℤ} (I J : InjectiveResolution K) :
    (quotient 𝒜 (up ℤ)).obj I ⟶ (quotient 𝒜 (up ℤ)).obj J :=
  (comparisonEquiv I J).symm ((quotient 𝒜 (up ℤ)).map J.ι)

/-- Helper for Remark 13.23.7: the canonical comparison morphism composes with `I.ι` to the class
of `J.ι` in the homotopy category. -/
@[reassoc]
theorem ι_homotopyComparison {K : CochainComplex 𝒜 ℤ} (I J : InjectiveResolution K) :
    (quotient 𝒜 (up ℤ)).map I.ι ≫ homotopyComparison I J =
      (quotient 𝒜 (up ℤ)).map J.ι := by
  let Q := quotient 𝒜 (up ℤ)
  let e := comparisonEquiv I J
  -- Evaluate the defining equivalence on the chosen preimage of `Q.map J.ι`.
  change (fun a : Q.obj I ⟶ Q.obj J ↦ Q.map I.ι ≫ a) (e.symm (Q.map J.ι)) = Q.map J.ι
  exact e.apply_symm_apply (Q.map J.ι)

attribute [simp] ι_homotopyComparison_assoc

/-- Helper for Remark 13.23.7: the factorization property determines the comparison morphism
uniquely. -/
theorem homotopyComparison_unique {K : CochainComplex 𝒜 ℤ} (I J : InjectiveResolution K)
    {a : (quotient 𝒜 (up ℤ)).obj I ⟶ (quotient 𝒜 (up ℤ)).obj J}
    (ha : (quotient 𝒜 (up ℤ)).map I.ι ≫ a = (quotient 𝒜 (up ℤ)).map J.ι) :
    a = homotopyComparison I J := by
  let hbij := comparison_bijective I J
  -- Injectivity of precomposition identifies any other factorization with the canonical preimage.
  exact hbij.injective (ha.trans (I.ι_homotopyComparison J).symm)

/-- Remark 13.23.7: for injective resolutions `I` and `J` of a cochain complex `K`, there is a
unique morphism from `I` to `J` in the homotopy category whose composite with the map `K ⟶ I` is
the map `K ⟶ J`. The source text assumes `K` bounded below, but that hypothesis is redundant once
`I` and `J` are given. -/
@[stacks 013Y]
theorem existsUnique_homotopyComparison
    {K : CochainComplex 𝒜 ℤ} (I J : InjectiveResolution K) :
    ∃! a :
        (quotient 𝒜 (up ℤ)).obj I ⟶
          (quotient 𝒜 (up ℤ)).obj J,
      (quotient 𝒜 (up ℤ)).map I.ι ≫ a =
        (quotient 𝒜 (up ℤ)).map J.ι := by
  -- The witness is the canonical preimage of `Q.map J.ι` under the precomposition bijection.
  refine ⟨homotopyComparison I J, I.ι_homotopyComparison J, ?_⟩
  -- Any competing morphism has the same image under precomposition, hence equals the witness.
  intro a ha
  exact homotopyComparison_unique I J ha

end InjectiveResolution

end CochainComplex
