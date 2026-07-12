import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Pretriangulated
open ComplexShape
open DerivedCategory

universe w v u

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

local notation "KHom" => HomotopyCategory 𝒜 (up ℤ)
local notation "D" => DerivedCategory 𝒜
local notation "Qis" => HomotopyCategory.quasiIso 𝒜 (up ℤ)

/- Domain-style sampling:
- primary domain: morphisms of distinguished triangles in the homotopy category `K(𝒜)` and
  quasi-isomorphisms detected by the localization `Qh : K(𝒜) ⥤ D(𝒜)`;
- sampled owner declarations:
  `Pretriangulated.isIso₃_of_isIso₁₂`,
  `Pretriangulated.isIso₂_of_isIso₁₃`,
  `Pretriangulated.isIso₁_of_isIso₂₃`,
  `DerivedCategory.isIso_Qh_map_iff`;
- best owner abstraction:
  `source-facing`: the Mayer-Vietoris comparison morphism satisfies the triangle-level
    quasi-isomorphism two-out-of-three property;
  `core/canonical`: the distinguished-triangle two-out-of-three isomorphism theorems in
    `CategoryTheory.Pretriangulated`;
  `bridge/view`: the localization criterion `DerivedCategory.isIso_Qh_map_iff`, which transports
    those owner isomorphism results back to quasi-isomorphisms in `K(𝒜)`.

Primitive data are only a morphism of distinguished triangles and the quasi-isomorphism
hypotheses on two of its components. The three directional implications are therefore derived
bridge API from the owner abstractions above, so this file should keep the single source-facing
two-out-of-three theorem and expose the three directional applications as companion lemmas.
-/

-- Proof sketch: apply `Qh.mapTriangle` to the given morphism of distinguished triangles. In the
-- derived category, quasi-isomorphisms become isomorphisms by `DerivedCategory.isIso_Qh_map_iff`,
-- so the owner theorems `Pretriangulated.isIso₃_of_isIso₁₂`,
-- `Pretriangulated.isIso₂_of_isIso₁₃`, and `Pretriangulated.isIso₁_of_isIso₂₃` yield the third
-- component isomorphism in each case. Translating back with `DerivedCategory.isIso_Qh_map_iff`
-- gives quasi-isomorphism of the original component in `K(𝒜)`.
/-- Lemma 21.26.2: for a morphism of distinguished triangles in `K(𝒜)`, the three
component maps satisfy two-out-of-three for quasi-isomorphisms. In the Mayer-Vietoris
application, these are the comparison maps `c^K_i(X, Z, Y, E)`. -/
@[stacks 0EWP]
theorem triangleMorphism_quasiIso_two_out_of_three_of_distinguished
    {T T' : Triangle KHom} (φ : T ⟶ T')
    (hT : T ∈ distTriang KHom) (hT' : T' ∈ distTriang KHom) :
    (Qis φ.hom₁ ∧ Qis φ.hom₂ → Qis φ.hom₃) ∧
      (Qis φ.hom₁ ∧ Qis φ.hom₃ → Qis φ.hom₂) ∧
      (Qis φ.hom₂ ∧ Qis φ.hom₃ → Qis φ.hom₁) := by
  let QhF : KHom ⥤ D := Qh
  let Qht := Functor.mapTriangle QhF
  let φQ := Qht.map φ
  have hTQ : Qht.obj T ∈ distTriang D := by
    simpa [QhF, Qht] using Functor.map_distinguished QhF T hT
  have hTQ' : Qht.obj T' ∈ distTriang D := by
    simpa [QhF, Qht] using Functor.map_distinguished QhF T' hT'
  constructor
  · rintro ⟨h₁, h₂⟩
    have hQ₁ : IsIso (QhF.map φ.hom₁) := by
      simpa [QhF] using (isIso_Qh_map_iff φ.hom₁).2 h₁
    have hQ₂ : IsIso (QhF.map φ.hom₂) := by
      simpa [QhF] using (isIso_Qh_map_iff φ.hom₂).2 h₂
    have hQ₃ : IsIso (QhF.map φ.hom₃) := by
      simpa [φQ] using
        (isIso₃_of_isIso₁₂ φQ hTQ hTQ' hQ₁ hQ₂ : IsIso φQ.hom₃)
    exact (isIso_Qh_map_iff φ.hom₃).1 (by simpa [QhF] using hQ₃)
  constructor
  · rintro ⟨h₁, h₃⟩
    have hQ₁ : IsIso (QhF.map φ.hom₁) := by
      simpa [QhF] using (isIso_Qh_map_iff φ.hom₁).2 h₁
    have hQ₃ : IsIso (QhF.map φ.hom₃) := by
      simpa [QhF] using (isIso_Qh_map_iff φ.hom₃).2 h₃
    have hQ₂ : IsIso (QhF.map φ.hom₂) := by
      simpa [φQ] using
        (isIso₂_of_isIso₁₃ φQ hTQ hTQ' hQ₁ hQ₃ : IsIso φQ.hom₂)
    exact (isIso_Qh_map_iff φ.hom₂).1 (by simpa [QhF] using hQ₂)
  · rintro ⟨h₂, h₃⟩
    have hQ₂ : IsIso (QhF.map φ.hom₂) := by
      simpa [QhF] using (isIso_Qh_map_iff φ.hom₂).2 h₂
    have hQ₃ : IsIso (QhF.map φ.hom₃) := by
      simpa [QhF] using (isIso_Qh_map_iff φ.hom₃).2 h₃
    have hQ₁ : IsIso (QhF.map φ.hom₁) := by
      simpa [φQ] using
        (isIso₁_of_isIso₂₃ φQ hTQ hTQ' hQ₂ hQ₃ : IsIso φQ.hom₁)
    exact (isIso_Qh_map_iff φ.hom₁).1 (by simpa [QhF] using hQ₁)

/-- Companion to Lemma 21.26.2: in a morphism of distinguished triangles in `K(𝒜)`,
if the first two components are quasi-isomorphisms, then so is the third. -/
theorem triangleMorphism_quasiIso₃_of_quasiIso₁₂_of_distinguished
    {T T' : Triangle KHom} (φ : T ⟶ T')
    (hT : T ∈ distTriang KHom) (hT' : T' ∈ distTriang KHom)
    (h₁ : Qis φ.hom₁) (h₂ : Qis φ.hom₂) :
    Qis φ.hom₃ :=
  (triangleMorphism_quasiIso_two_out_of_three_of_distinguished φ hT hT').1 ⟨h₁, h₂⟩

/-- Companion to Lemma 21.26.2: in a morphism of distinguished triangles in `K(𝒜)`,
if the first and third components are quasi-isomorphisms, then so is the second. -/
theorem triangleMorphism_quasiIso₂_of_quasiIso₁₃_of_distinguished
    {T T' : Triangle KHom} (φ : T ⟶ T')
    (hT : T ∈ distTriang KHom) (hT' : T' ∈ distTriang KHom)
    (h₁ : Qis φ.hom₁) (h₃ : Qis φ.hom₃) :
    Qis φ.hom₂ :=
  (triangleMorphism_quasiIso_two_out_of_three_of_distinguished φ hT hT').2.1 ⟨h₁, h₃⟩

/-- Companion to Lemma 21.26.2: in a morphism of distinguished triangles in `K(𝒜)`,
if the second and third components are quasi-isomorphisms, then so is the first. -/
theorem triangleMorphism_quasiIso₁_of_quasiIso₂₃_of_distinguished
    {T T' : Triangle KHom} (φ : T ⟶ T')
    (hT : T ∈ distTriang KHom) (hT' : T' ∈ distTriang KHom)
    (h₂ : Qis φ.hom₂) (h₃ : Qis φ.hom₃) :
    Qis φ.hom₁ :=
  (triangleMorphism_quasiIso_two_out_of_three_of_distinguished φ hT hT').2.2 ⟨h₂, h₃⟩

end

end CategoryTheory
