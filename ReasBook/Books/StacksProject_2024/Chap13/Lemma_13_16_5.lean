import Mathlib
import StacksProject_2024.Chap13.Lemma_13_4_22
import StacksProject_2024.Chap13.Lemma_13_16_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open DerivedCategory.TStructure

universe w v₁ v₂ u₁ u₂

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]

variable (F : 𝒜 ⥤ ℬ) [F.Additive]
variable [PreservesFiniteLimits F]

/-
Domain-style sampling for Lemma 13.16.5:
- primary domain: bounded-below right acyclicity for a left exact additive functor in short exact
  sequences;
- sampled owner declarations:
  `IsBoundedBelowRightAcyclicForAdditiveFunctor`,
  `Functor.boundedBelowHigherRightDerivedVanishes`,
  `isBoundedBelowRightAcyclicForAdditiveFunctor_iff_boundedBelowHigherRightDerivedVanishes`,
  `Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono`,
  `ShortComplex.ShortExact`;
- best owner abstraction: the source-facing owner on objects is
  `IsBoundedBelowRightAcyclicForAdditiveFunctor F`; the unbounded injective-resolution notion
  `IsRightAcyclicForAdditiveFunctor F` is only a stronger bridge/view under extra assumptions and
  should not drive the main statements here;
- primitive data: a short exact sequence in `𝒜` and bounded-below right acyclicity of the
  relevant objects;
- derived API: the five bounded-below acyclicity closure theorems and their mapped-short-exactness
  corollaries; proofs may pass through Lemma `13.16.4` and a chosen bounded-below right derived
  functor, but that proof route is not part of the public API; the exact-functor statement with
  explicit hypothesis `Epi (F.map S.g)` is a stronger companion.

Source/core/bridge triage:
- `source-facing`: bounded-below right acyclicity in the six short-exact-sequence cases from the
  source text;
- `core/canonical`: `IsBoundedBelowRightAcyclicForAdditiveFunctor`,
  `Functor.boundedBelowHigherRightDerivedVanishes`, `ShortComplex.ShortExact`, and
  `Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono`;
-- `bridge/view`: the unbounded injective-resolution owners
  `IsRightAcyclicForAdditiveFunctor` and `Functor.higherRightDerivedVanishes`, which belong only
  in stronger-assumption companion statements. -/

section BoundedBelow

variable [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]

/-- Helper for Lemma 13.16.5: the bounded-below degree-zero embedding followed by the canonical
inclusion into the unbounded derived category identifies with the usual degree-zero embedding. -/
private noncomputable def single0ToDerivedIso :
    single0ToDplus 𝒜 ⋙ ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜))) ≅
      DerivedCategory.singleFunctor 𝒜 0 :=
  (𝟭 𝒜).single0PlusToSingleFunctorIso ≪≫ Functor.leftUnitor _

/-- Helper for Lemma 13.16.5: a short exact sequence in `𝒜` yields a bounded-below triangle on
degree-zero objects by transporting the usual connecting morphism through `single0ToDerivedIso`. -/
private noncomputable def single0ToDplusTriangle {S : ShortComplex 𝒜} (hS : S.ShortExact) :
    Triangle (D⁺(𝒜)) :=
  Triangle.mk
    ((single0ToDplus 𝒜).map S.f)
    ((single0ToDplus 𝒜).map S.g)
    ((ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))).preimage
      ((single0ToDerivedIso.hom.app S.X₃) ≫ hS.singleδ ≫
        ((single0ToDerivedIso.inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
          ((ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))).commShiftIso (1 : ℤ)).inv.app
            ((single0ToDplus 𝒜).obj S.X₁)))

/-- Helper for Lemma 13.16.5: the transported bounded-below triangle attached to a short exact
sequence is distinguished. -/
private theorem single0ToDplus_triangle_distinguished {S : ShortComplex 𝒜}
    (hS : S.ShortExact) :
    single0ToDplusTriangle (𝒜 := 𝒜) hS ∈ distTriang (D⁺(𝒜)) := by
  -- Route correction: the intended proof maps this triangle to `D(𝒜)`, compares it with
  -- `hS.singleTriangle` via `single0ToDerivedIso`, and then applies
  -- `isomorphic_distinguished _ hS.singleTriangle_distinguished`.
  rw [← (ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))).map_distinguished_iff]
  change
    Triangle.mk
        ((ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))).map
          ((single0ToDplus 𝒜).map S.f))
        ((ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))).map
          ((single0ToDplus 𝒜).map S.g))
        ((ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))).map
            ((ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))).preimage
              ((single0ToDerivedIso.hom.app S.X₃) ≫ hS.singleδ ≫
                ((single0ToDerivedIso.inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
                  ((ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))).commShiftIso
                    (1 : ℤ)).inv.app ((single0ToDplus 𝒜).obj S.X₁))) ≫
          ((ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))).commShiftIso
            (1 : ℤ)).hom.app ((single0ToDplus 𝒜).obj S.X₁)) ∈
      distTriang (D(𝒜))
  rw [(ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))).map_preimage]
  refine isomorphic_distinguished _ hS.singleTriangle_distinguished _ ?_
  refine Triangle.isoMk _ _
    (single0ToDerivedIso.app S.X₁)
    (single0ToDerivedIso.app S.X₂)
    (single0ToDerivedIso.app S.X₃)
    ?_ ?_ ?_
  · simpa using single0ToDerivedIso.hom.naturality S.f
  · simpa using single0ToDerivedIso.hom.naturality S.g
  · -- After cancelling the commutation isomorphism and the shifted comparison isomorphism,
    -- the transported connecting morphism reduces to `hS.singleδ`.
    have hshift :
        (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.inv.app S.X₁) ≫
            (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.hom.app S.X₁) =
          𝟙 (((DerivedCategory.singleFunctor 𝒜 0).obj S.X₁)⟦(1 : ℤ)⟧) := by
      simpa using
        congrArg
          (fun k ↦ (shiftFunctor (D(𝒜)) (1 : ℤ)).map k)
          (single0ToDerivedIso.inv_hom_id_app S.X₁)
    have hthird :
      single0ToDerivedIso.hom.app S.X₃ ≫
          hS.singleδ ≫
            (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.inv.app S.X₁) ≫
              (Functor.commShiftIso (ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜))))
                (1 : ℤ)).inv.app ((single0ToDplus 𝒜).obj S.X₁) ≫
                (Functor.commShiftIso (ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜))))
                  (1 : ℤ)).hom.app ((single0ToDplus 𝒜).obj S.X₁) ≫
                  (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.hom.app S.X₁)
          =
        single0ToDerivedIso.hom.app S.X₃ ≫ hS.singleδ := by
      calc
        single0ToDerivedIso.hom.app S.X₃ ≫
            hS.singleδ ≫
              (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.inv.app S.X₁) ≫
                (Functor.commShiftIso (ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜))))
                  (1 : ℤ)).inv.app ((single0ToDplus 𝒜).obj S.X₁) ≫
                  (Functor.commShiftIso (ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜))))
                    (1 : ℤ)).hom.app ((single0ToDplus 𝒜).obj S.X₁) ≫
                    (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.hom.app S.X₁)
            =
          single0ToDerivedIso.hom.app S.X₃ ≫
            hS.singleδ ≫
              (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.inv.app S.X₁) ≫
                (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.hom.app S.X₁) := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ single0ToDerivedIso.hom.app S.X₃ ≫
                hS.singleδ ≫
                  (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.inv.app S.X₁) ≫
                    k ≫
                      (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.hom.app S.X₁))
              ((Functor.commShiftIso (ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜))))
                (1 : ℤ)).inv_hom_id_app ((single0ToDplus 𝒜).obj S.X₁))
        _ = single0ToDerivedIso.hom.app S.X₃ ≫ hS.singleδ := by
          calc
            single0ToDerivedIso.hom.app S.X₃ ≫
                hS.singleδ ≫
                  (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.inv.app S.X₁) ≫
                    (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.hom.app S.X₁)
                =
              single0ToDerivedIso.hom.app S.X₃ ≫ hS.singleδ ≫
                𝟙 (((DerivedCategory.singleFunctor 𝒜 0).obj S.X₁)⟦(1 : ℤ)⟧) := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ single0ToDerivedIso.hom.app S.X₃ ≫ hS.singleδ ≫ k) hshift
            _ = single0ToDerivedIso.hom.app S.X₃ ≫ hS.singleδ := by
              simp
    simpa [single0ToDplusTriangle, ShortComplex.ShortExact.singleTriangle, Category.assoc] using
      hthird

instance isClosedUnderExtensions_isBoundedBelowRightAcyclicForAdditiveFunctor :
    ObjectProperty.IsClosedUnderExtensions
      (IsBoundedBelowRightAcyclicForAdditiveFunctor F : ObjectProperty 𝒜) where
  prop_X₂_of_shortExact := by
    intro S hS h₁ h₃
    -- The main source-faithful skeleton is now in place: use the distinguished bounded-below
    -- triangle on `A[0]`, `B[0]`, `C[0]`, extract the five-term exact window, and then apply
    -- Lemma `13.16.4` degreewise to kill the endpoint terms.
    have hT : single0ToDplusTriangle (𝒜 := 𝒜) hS ∈ distTriang (D⁺(𝒜)) :=
      single0ToDplus_triangle_distinguished (𝒜 := 𝒜) hS
    clear hT
    -- TODO: the source-faithful proof uses the positive-degree long exact sequence for a
    -- bounded-below right derived functor of `F`, but that global right-derived-functor owner is
    -- not yet available in the dependency closure of this file.
    sorry

omit [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ] in
/-- Helper for Lemma 13.16.5: left exactness gives the exactness and monicity on the left of the
mapped short complex attached to a short exact sequence in `𝒜`. -/
theorem exact_mono_map_of_shortExact
    {S : ShortComplex 𝒜} (hS : S.ShortExact) :
    (S.map F).Exact ∧ Mono (F.map S.f) := by
  -- The preservation-of-finite-limits criterion packages the left exactness of `F`.
  rcases
    (F.preservesFiniteLimits_iff_forall_exact_map_and_mono).1
      (inferInstance : PreservesFiniteLimits F) S hS with
    ⟨h_exact, h_mono⟩
  exact ⟨h_exact, h_mono⟩

omit [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ] in
/-- Helper for Lemma 13.16.5: left exactness preserves exactness at the middle term of the mapped
short complex. -/
theorem exact_map_of_shortExact
    {S : ShortComplex 𝒜} (hS : S.ShortExact) :
    (S.map F).Exact := by
  -- This is the exactness component of the packaged left-exactness statement above.
  exact (exact_mono_map_of_shortExact (F := F) hS).1

omit [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ] in
/-- Helper for Lemma 13.16.5: left exactness preserves the monomorphism on the left of the mapped
short complex. -/
theorem mono_map_f_of_shortExact
    {S : ShortComplex 𝒜} (hS : S.ShortExact) :
    Mono (F.map S.f) := by
  -- This is the monomorphism component of the same left-exactness package.
  exact (exact_mono_map_of_shortExact (F := F) hS).2

omit [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ] in
/-- Helper for Lemma 13.16.5: once `F.map S.g` is known to be an epimorphism, the mapped sequence
is short exact. -/
theorem map_shortExact_of_epi_map_g_aux
    {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (h_epi : Epi (F.map S.g)) :
    (S.map F).ShortExact := by
  -- Combine left exactness on the left with the supplied surjectivity on the right.
  have h_exact : (S.map F).Exact := exact_map_of_shortExact (F := F) hS
  have h_mono : Mono (F.map S.f) := mono_map_f_of_shortExact (F := F) hS
  exact ShortComplex.ShortExact.mk' h_exact h_mono h_epi

/-- Helper for Lemma 13.16.5: in the end-acyclic case, the source-faithful long exact sequence
should show that `F.map S.g` is an epimorphism. -/
theorem epi_map_g_of_isBoundedBelowRightAcyclicForAdditiveFunctor_ends
    {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (h₁ : IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₁)
    (h₃ : IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₃) :
    Epi (F.map S.g) := by
  -- TODO: follow the exact degree-zero window
  -- `0 ⟶ F(S.X₁) ⟶ F(S.X₂) ⟶ F(S.X₃) ⟶ R¹F(S.X₁) ⟶ ⋯`;
  -- the acyclicity of `S.X₁` kills `R¹F(S.X₁)`, so exactness forces `F.map S.g` to be epi.
  sorry

/-- Helper for Lemma 13.16.5: under the ambient bounded-below derived-category hypotheses, the
mapped short exact sequence in the end-acyclic case follows from the epi bridge. -/
theorem map_shortExact_of_isBoundedBelowRightAcyclicForAdditiveFunctor_ends_aux
    {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (h₁ : IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₁)
    (h₃ : IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₃) :
    (S.map F).ShortExact := by
  -- First obtain surjectivity on the right from the degree-zero exact window.
  have h_epi : Epi (F.map S.g) :=
    epi_map_g_of_isBoundedBelowRightAcyclicForAdditiveFunctor_ends (F := F) hS h₁ h₃
  -- Then combine it with left exactness on the first two terms.
  exact map_shortExact_of_epi_map_g_aux (F := F) hS h_epi

-- Proof sketch: rewrite the two endpoint acyclicity hypotheses using Lemma `13.16.4` as the
-- vanishing of the positive bounded-below right derived functors for some chosen bounded-below
-- right derived functor of `F`. The long exact sequence attached to `hS` then forces the
-- corresponding groups for `S.X₂` to vanish, hence `S.X₂` is bounded-below right acyclic for
-- `F`.
omit [HasDerivedCategory.{w} 𝒜] in
/-- Lemma 13.16.5 (1): in a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0`, if `A` and `C` are right
acyclic for the bounded-below right derived functor of `F`, equivalently if the positive bounded-
below right derived functors of `F` vanish on `A` and `C`, then `B` is right acyclic for the
bounded-below right derived functor of `F`. -/
theorem isBoundedBelowRightAcyclicForAdditiveFunctor_middle_of_shortExact
    {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (h₁ : IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₁)
    (h₃ : IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₃) :
    IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₂ := by
  -- Reuse the local extension-closure instance; the remaining blocker is concentrated in the
  -- instance proof above, where the long-exact-sequence argument belongs.
  exact
    ObjectProperty.prop_X₂_of_shortExact
      (P := IsBoundedBelowRightAcyclicForAdditiveFunctor F) hS h₁ h₃

-- Proof sketch: the same long exact sequence begins
-- `0 ⟶ F(S.X₁) ⟶ F(S.X₂) ⟶ F(S.X₃) ⟶ R¹F(S.X₁) ⟶ ⋯`. Under the bounded-below right-acyclicity
-- assumptions on `S.X₁` and `S.X₃`, Lemma `13.16.4` kills the positive bounded-below derived
-- terms, so `F(S.X₂) ⟶ F(S.X₃)` is epi and the image sequence is short exact.
omit [HasDerivedCategory.{w} 𝒜] in
/-- Lemma 13.16.5 (2): in the first case of Lemma 13.16.5, applying `F` to the short exact
sequence again yields a short exact sequence. -/
theorem map_shortExact_of_isBoundedBelowRightAcyclicForAdditiveFunctor_ends
    {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (h₁ : IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₁)
    (h₃ : IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₃) :
    (S.map F).ShortExact := by
  -- Reuse the auxiliary theorem so the remaining blocker stays isolated in the epi bridge.
  exact
    map_shortExact_of_isBoundedBelowRightAcyclicForAdditiveFunctor_ends_aux
      (F := F) hS h₁ h₃

-- Proof sketch: after identifying bounded-below right acyclicity with vanishing of the positive
-- bounded-below right derived functors, use the long exact sequence attached to `hS`. The
-- vanishings for `S.X₁` and `S.X₂` force the corresponding groups for `S.X₃` to vanish, so
-- `S.X₃` is bounded-below right acyclic.
omit [HasDerivedCategory.{w} 𝒜] in
/-- Lemma 13.16.5 (3): in a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0`, if `A` and `B` are right
acyclic for the bounded-below right derived functor of `F`, equivalently if the positive bounded-
below right derived functors of `F` vanish on `A` and `B`, then `C` is right acyclic for the
bounded-below right derived functor of `F`. -/
theorem isBoundedBelowRightAcyclicForAdditiveFunctor_cokernel_of_shortExact
    {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (h₁ : IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₁)
    (h₂ : IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₂) :
    IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₃ := by
  -- TODO: realize the source-faithful long-exact-sequence proof either from a dependency-closed
  -- bounded-below right-derived-functor owner for `KplusToDplus` or from a local pointwise
  -- derived-value triangle in `K⁺(𝒜)` whose third vertex is quasi-isomorphic to `single0Plus C`.
  sorry

-- Proof sketch: the long exact sequence in bounded-below right derived functors gives
-- `0 ⟶ F(S.X₁) ⟶ F(S.X₂) ⟶ F(S.X₃) ⟶ R¹F(S.X₁) ⟶ ⋯`; when `S.X₁` and `S.X₂` are bounded-below
-- right acyclic, the term `R¹F(S.X₁)` vanishes by Lemma `13.16.4`, so the image sequence is
-- short exact.
omit [HasDerivedCategory.{w} 𝒜] in
/-- Lemma 13.16.5 (4): in the second case of Lemma 13.16.5, applying `F` to the short exact
sequence again yields a short exact sequence. -/
theorem map_shortExact_of_isBoundedBelowRightAcyclicForAdditiveFunctor_left_middle
    {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (h₁ : IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₁)
    (h₂ : IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₂) :
    (S.map F).ShortExact := by
  exact
    map_shortExact_of_isBoundedBelowRightAcyclicForAdditiveFunctor_ends F hS h₁
      (isBoundedBelowRightAcyclicForAdditiveFunctor_cokernel_of_shortExact F hS h₁ h₂)

-- Proof sketch: rewrite bounded-below right acyclicity using Lemma `13.16.4` and inspect the
-- long exact sequence of bounded-below right derived functors for `hS`. The vanishing for `S.X₂`
-- and `S.X₃`, together with the surjectivity of `F.map S.g`, remove the boundary term at degree
-- `0`, forcing the positive bounded-below right derived functors of `S.X₁` to vanish and hence
-- making `S.X₁` bounded-below right acyclic.
omit [HasDerivedCategory.{w} 𝒜] in
/-- Lemma 13.16.5 (5): in a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0`, if `B` and `C` are right
acyclic for the bounded-below right derived functor of `F` and `F(B) ⟶ F(C)` is an
epimorphism, equivalently if the positive bounded-below right derived functors of `F` vanish on
`B` and `C` and `F(B) ⟶ F(C)` is epi, then `A` is right acyclic for the bounded-below right
derived functor of `F`. -/
theorem isBoundedBelowRightAcyclicForAdditiveFunctor_kernel_of_shortExact_of_epi_map_g
    {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (h₂ : IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₂)
    (h₃ : IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₃)
    (h_epi : Epi (F.map S.g)) :
    IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₁ := by
  -- TODO: combine the degree-zero epi hypothesis with the positive-degree long exact window once
  -- the same dependency-closed derived-value owner used in the cokernel case is available.
  sorry

-- Proof sketch: left exactness gives exactness and monicity on the left of the mapped sequence,
-- and the additional hypothesis `Epi (F.map S.g)` supplies the right exactness. Hence the image
-- of the original short exact sequence under `F` is again short exact, so the mapped short-
-- exactness conclusion of Lemma 13.16.5 (6) does not in fact need the bounded-below right
-- acyclicity hypotheses on `B` and `C`.
omit [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ] in
/-- Lemma 13.16.5 (6): in the third case of Lemma 13.16.5, if `F(B) ⟶ F(C)` is an epimorphism,
then applying `F` to the short exact sequence again yields a short exact sequence. The source's
bounded-below right acyclicity hypotheses on `B` and `C` are mathematically redundant for this
mapped short-exactness conclusion. -/
theorem map_shortExact_of_epi_map_g
    {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (h_epi : Epi (F.map S.g)) :
    (S.map F).ShortExact := by
  -- This is the epi-only core used by the two source-facing mapped-short-exactness corollaries.
  exact map_shortExact_of_epi_map_g_aux (F := F) hS h_epi

end BoundedBelow

end

end CategoryTheory
