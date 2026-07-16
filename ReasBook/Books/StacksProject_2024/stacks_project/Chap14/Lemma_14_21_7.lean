import Mathlib
import StacksProject_2024.stacks_project.Chap14.Lemma_14_18_3

open CategoryTheory Limits Opposite Simplicial

universe u

noncomputable section

namespace SSet

/- 
Domain-style sampling for Lemma 14.21.7:
- primary domain: simplicial-set inclusions obtained by adjoining a single simplex, and the
  resulting canonical pushout squares in `SSet`;
- sampled owner-style declarations:
  `SSet.Subcomplex.N`,
  `SSet.Subcomplex.ofSimplex`,
  `CategoryTheory.Subfunctor.range_ι`,
  `SSet.boundary`,
  `SSet.skeletonOfMono`,
  `SSet.Subcomplex.BicartSq.isPushout`,
  `SSet.yonedaEquiv`;
- best owner abstraction:
  `source-facing`: a new nondegenerate simplex `x : U.N` whose boundary already lands in the
    source subcomplex `U`, together with the canonical equality saying that adjoining `x.simplex`
    generates all of `V`;
  `core/canonical`: the ambient owners `Subcomplex.N`, `Subcomplex.ofSimplex`, `SSet.boundary`,
    `Subcomplex.range`, and `Subcomplex.BicartSq.isPushout`;
  `bridge/view`: the induced boundary map `∂Δ[x.dim] ⟶ U` and the canonical `IsPushout` square;
- primitive data: only the source subcomplex `U`, the new simplex `x : U.N`, the canonical
  boundary-factorization predicate `x.boundary_range_le`, and the equality
  `U ⊔ Subcomplex.ofSimplex x.simplex = ⊤`;
- derived API: the boundary map `∂Δ[x.dim] ⟶ U` induced by `x.boundary_range_le` and the
  resulting pushout square.
-/

namespace Subcomplex
namespace N

variable {V : SSet.{u}} {U : V.Subcomplex} (x : U.N)

/-- The boundary of the simplex classified by `x.simplex` lands in the source subcomplex `U`. -/
abbrev boundary_range_le : Prop :=
  Subcomplex.range (∂Δ[x.dim].ι ≫ yonedaEquiv.symm x.simplex) ≤ U

end N
end Subcomplex

/-- Helper for Lemma 14.21.7: the boundary map from `∂Δ[x.dim]` to `U` induced by the fact that
the boundary of `x.simplex` already lands in `U`. -/
private abbrev attached_boundary_map
    {V : SSet.{u}} (U : V.Subcomplex) (x : U.N)
    (hboundary : x.boundary_range_le) :
    ∂Δ[x.dim].toSSet ⟶ U.toSSet :=
  U.lift (∂Δ[x.dim].ι ≫ yonedaEquiv.symm x.simplex) hboundary

/-- Helper for Lemma 14.21.7: the induced boundary map into `U` composes back to the original
boundary of the attached simplex in `V`. -/
private theorem attached_boundary_map_comp
    {V : SSet.{u}} (U : V.Subcomplex) (x : U.N)
    (hboundary : x.boundary_range_le) :
    attached_boundary_map U x hboundary ≫ U.ι =
      ∂Δ[x.dim].ι ≫ yonedaEquiv.symm x.simplex := by
  -- The induced boundary map is defined by factoring the original boundary map through `U`.
  simpa [attached_boundary_map] using
    (U.lift_ι (∂Δ[x.dim].ι ≫ yonedaEquiv.symm x.simplex) hboundary)

/-- Helper for Lemma 14.21.7: the canonical map from the literal pushout object to `V`. -/
private noncomputable abbrev attached_pushout_desc
    {V : SSet.{u}} (U : V.Subcomplex) (x : U.N)
    (hboundary : x.boundary_range_le) :
    pushout ∂Δ[x.dim].ι (attached_boundary_map U x hboundary) ⟶ V :=
  pushout.desc (yonedaEquiv.symm x.simplex) U.ι
    (attached_boundary_map_comp U x hboundary).symm

/-- Helper for Lemma 14.21.7: a surjective endomorphism of the simplex category is the identity. -/
private theorem surjective_endomorphism_eq_id
    {n : ℕ} (θ : ⦋n⦌ ⟶ ⦋n⦌)
    (hθ : Function.Surjective θ.toOrderHom) :
    θ = 𝟙 _ := by
  -- A surjective endomorphism of a finite linear order is an order automorphism, and those are
  -- unique on `Fin (n + 1)`.
  apply SimplexCategory.Hom.ext
  let hmono := θ.toOrderHom.monotone
  have hinj : Function.Injective θ.toOrderHom :=
    (Finite.injective_iff_surjective (f := θ.toOrderHom)).2 hθ
  have hstrict : StrictMono θ.toOrderHom :=
    (Monotone.strictMono_iff_injective hmono).2 hinj
  let e : Fin (n + 1) ≃o Fin (n + 1) :=
    StrictMono.orderIsoOfSurjective (f := θ.toOrderHom) hstrict hθ
  have he : e = OrderIso.refl _ := Subsingleton.elim _ _
  ext i
  -- After identifying the order automorphism with the unique one, the pointwise equality is
  -- immediate.
  change (((e : Fin (n + 1) ≃o Fin (n + 1)) i : Fin (n + 1)).1) = i.1
  simp [he]

/-- Helper for Lemma 14.21.7: if a surjective simplex of `Δ[x.dim]` lands in `U`, then the top
simplex `x` already lies in `U`. -/
private theorem simplex_mem_of_surjective_image_mem
    {V : SSet.{u}} {U : V.Subcomplex} (x : U.N)
    {Δ' : SimplexCategory} (θ : Δ' ⟶ ⦋x.dim⦌)
    (hθ : Function.Surjective θ.toOrderHom)
    (hyU : V.map θ.op x.simplex ∈ U.obj (op Δ')) :
    x.simplex ∈ U.obj (op ⦋x.dim⦌) := by
  cases Δ' with
  | mk m =>
      -- We induct on the domain length and peel off degeneracies from a surjective simplex map.
      induction m using Nat.strong_induction_on with
      | h m ih =>
          letI : Epi θ := (SimplexCategory.epi_iff_surjective).2 hθ
          have hle : x.dim ≤ m := SimplexCategory.le_of_epi θ
          by_cases hm : m = x.dim
          · subst hm
            have hθid : θ = 𝟙 _ := surjective_endomorphism_eq_id θ hθ
            -- In the equal-length case the surjective map is the identity, so the hypothesis is
            -- exactly that `x.simplex` lies in `U`.
            simpa [hθid] using hyU
          · cases m with
            | zero =>
                exact False.elim (hm (Nat.le_zero.mp hle).symm)
            | succ m =>
                have hlt : x.dim < m.succ := lt_of_le_of_ne hle fun hEq ↦ hm hEq.symm
                have hnotinj : ¬ Function.Injective θ.toOrderHom := by
                  intro hmono
                  haveI : Mono θ := (SimplexCategory.mono_iff_injective).2 hmono
                  exact Nat.not_le_of_gt hlt (SimplexCategory.le_of_mono θ)
                obtain ⟨i, θ', hθfac⟩ := SimplexCategory.eq_σ_comp_of_not_injective θ hnotinj
                have hθcomp :
                    θ.toOrderHom = θ'.toOrderHom.comp (SimplexCategory.σ i).toOrderHom := by
                  simp [hθfac]
                have hθ' : Function.Surjective θ'.toOrderHom := by
                  intro b
                  obtain ⟨a, ha⟩ := hθ b
                  refine ⟨(SimplexCategory.σ i).toOrderHom a, ?_⟩
                  have hcomp := congrArg (fun f ↦ f a) hθcomp
                  simpa [ha] using hcomp.symm
                have hyU' : V.map θ'.op x.simplex ∈ U.obj (op ⦋m⦌) := by
                  -- Precompose with the canonical face section of `σ i` to remove one degeneracy.
                  have hyUσ :
                      V.map (SimplexCategory.σ i).op (V.map θ'.op x.simplex) ∈ U.obj (op ⦋m + 1⦌) := by
                    simpa [hθfac, op_comp, Functor.map_comp] using hyU
                  have hyδ := U.map (SimplexCategory.δ i.castSucc).op hyUσ
                  have hsection :
                      V.map (SimplexCategory.σ i).op ≫
                          V.map (SimplexCategory.δ i.castSucc).op =
                        𝟙 (V.obj (op ⦋m⦌)) := by
                    simpa [Functor.map_comp, op_comp] using
                      congrArg V.map
                        (congrArg Quiver.Hom.op (SimplexCategory.δ_comp_σ_self (i := i)))
                  have hyδ' :
                      V.map (SimplexCategory.δ i.castSucc).op
                          (V.map (SimplexCategory.σ i).op (V.map θ'.op x.simplex)) ∈
                        U.obj (op ⦋m⦌) := by
                    simpa [Set.mem_preimage] using hyδ
                  have hcancel :
                      V.map (SimplexCategory.δ i.castSucc).op
                          (V.map (SimplexCategory.σ i).op (V.map θ'.op x.simplex)) =
                        V.map θ'.op x.simplex := by
                    simpa using congrFun hsection (V.map θ'.op x.simplex)
                  rw [hcancel] at hyδ'
                  exact hyδ'
                exact ih m (Nat.lt_succ_self m) θ' hθ' hyU'

/-- Helper for Lemma 14.21.7: a simplex of `Δ[x.dim]` whose image already lies in `U` must belong
to the boundary. -/
private theorem simplex_mem_boundary_of_image_mem
    {V : SSet.{u}} {U : V.Subcomplex} (x : U.N)
    {m : SimplexCategoryᵒᵖ} {z : Δ[x.dim].obj m}
    (hzU : (yonedaEquiv.symm x.simplex).app m z ∈ U.obj m) :
    z ∈ (∂Δ[x.dim]).obj m := by
  obtain ⟨θ, rfl⟩ := SSet.stdSimplex.objEquiv.symm.surjective z
  by_contra hz
  have hθ : Function.Surjective θ.toOrderHom := by
    simpa [SSet.boundary] using hz
  -- A simplex outside the boundary is surjective, so its image in `U` would force `x ∈ U`.
  exact x.notMem (simplex_mem_of_surjective_image_mem x θ hθ hzU)

/-- Helper for Lemma 14.21.7: the attached simplex meets the old subcomplex exactly along the
boundary image. -/
private theorem attached_simplex_boundary_range_eq_inf
    {V : SSet.{u}} {U : V.Subcomplex} (x : U.N)
    (hboundary : x.boundary_range_le) :
    Subcomplex.range (∂Δ[x.dim].ι ≫ yonedaEquiv.symm x.simplex) =
      U ⊓ Subcomplex.range (yonedaEquiv.symm x.simplex) := by
  let f : Δ[x.dim] ⟶ V := yonedaEquiv.symm x.simplex
  apply le_antisymm
  · intro m y hy
    -- The boundary image lands in `U` by assumption and certainly lands in the full simplex image.
    constructor
    · exact hboundary _ hy
    · simp only [SSet.Subcomplex.range, CategoryTheory.Subfunctor.range_obj, Set.mem_range] at hy ⊢
      rcases hy with ⟨z, rfl⟩
      exact ⟨(∂Δ[x.dim].ι).app m z, rfl⟩
  · intro m y hy
    -- Conversely, any point of the intersection comes from a simplex whose image is already in
    -- `U`, hence from a boundary simplex by the previous helper.
    rcases hy with ⟨hyU, hyf⟩
    simp only [SSet.Subcomplex.range, CategoryTheory.Subfunctor.range_obj, Set.mem_range] at hyf ⊢
    rcases hyf with ⟨z, rfl⟩
    exact ⟨⟨z, simplex_mem_boundary_of_image_mem x hyU⟩, rfl⟩

/-- Helper for Lemma 14.21.7: the boundary range, the attached simplex range, `U`, and `⊤`
assemble into the canonical bicartesian square of subcomplexes. -/
private theorem attached_simplex_bicart_sq
    {V : SSet.{u}} {U : V.Subcomplex} (x : U.N)
    (hboundary : x.boundary_range_le)
    (hgen : U ⊔ Subcomplex.ofSimplex x.simplex = ⊤) :
    (Subcomplex.range (∂Δ[x.dim].ι ≫ yonedaEquiv.symm x.simplex)).BicartSq
      (Subcomplex.range (yonedaEquiv.symm x.simplex)) U (⊤ : V.Subcomplex) := by
  -- The top-right corner is the simplex range, the bottom-left corner is `U`, and the previous
  -- helper identifies their intersection with the boundary range.
  refine ⟨?_, ?_⟩
  · calc
      Subcomplex.range (yonedaEquiv.symm x.simplex) ⊔ U
          = Subcomplex.ofSimplex x.simplex ⊔ U := by
              simpa using congrArg (fun A ↦ A ⊔ U)
                (SSet.Subcomplex.range_eq_ofSimplex (yonedaEquiv.symm x.simplex))
      _ = ⊤ := by
            simpa [sup_comm] using hgen
  · simpa [inf_comm] using (attached_simplex_boundary_range_eq_inf x hboundary).symm

/-- Helper for Lemma 14.21.7: every simplex of `V` outside `U` is a surjective image of the
attached simplex `x`. -/
private theorem simplex_outside_subcomplex_is_surjective_image
    {V : SSet.{u}} {U : V.Subcomplex} (x : U.N)
    (hboundary : x.boundary_range_le)
    (hgen : U ⊔ Subcomplex.ofSimplex x.simplex = ⊤)
    {m : ℕ} {z : V _⦋m⦌}
    (hzU : z ∉ U.obj (op ⦋m⦌)) :
    ∃ θ : ⦋m⦌ ⟶ ⦋x.dim⦌,
      Function.Surjective θ.toOrderHom ∧ V.map θ.op x.simplex = z := by
  have hzSup : z ∈ (U ⊔ Subcomplex.ofSimplex x.simplex).obj (op ⦋m⦌) := by
    have hzTop : z ∈ (⊤ : V.Subcomplex).obj (op ⦋m⦌) := by
      simp
    simpa [hgen] using hzTop
  have hzSimplex : z ∈ (Subcomplex.ofSimplex x.simplex).obj (op ⦋m⦌) := by
    rcases hzSup with hzSup | hzSup
    · exact False.elim (hzU hzSup)
    · exact hzSup
  rcases (Subcomplex.mem_ofSimplex_obj_iff x.simplex z).1 hzSimplex with ⟨θ, hθz⟩
  refine ⟨θ, ?_, hθz⟩
  by_contra hθ
  -- A non-surjective simplex operator factors through the boundary, so its image already lies in
  -- `U`, contradicting the assumption that `z` is outside `U`.
  have hzBoundary : SSet.stdSimplex.objEquiv.symm θ ∈ (∂Δ[x.dim]).obj (op ⦋m⦌) := by
    simpa [SSet.boundary] using hθ
  have hzRange :
      z ∈ (Subcomplex.range (∂Δ[x.dim].ι ≫ yonedaEquiv.symm x.simplex)).obj (op ⦋m⦌) := by
    refine ⟨⟨SSet.stdSimplex.objEquiv.symm θ, hzBoundary⟩, ?_⟩
    -- The witness is the same simplex operator, now viewed as a simplex in the boundary.
    simpa using hθz
  exact hzU (hboundary _ hzRange)

/-- Helper for Lemma 14.21.7: a nondegenerate simplex of `Δ[x.dim]` is either already in the
boundary or is the unique top simplex. -/
private theorem stdSimplex_nondegenerate_boundary_or_top
    {V : SSet.{u}} {U : V.Subcomplex} (x : U.N)
    {m : ℕ} (z : Δ[x.dim].nonDegenerate m) :
    z.1 ∈ (∂Δ[x.dim]).obj (op ⦋m⦌) ∨
      (m = x.dim ∧ HEq z.1 (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋x.dim⦌))) := by
  by_cases hlt : m < x.dim
  · left
    obtain ⟨θ, hθ⟩ := SSet.stdSimplex.objEquiv.symm.surjective z.1
    by_contra hzBoundary
    have hzsurj : Function.Surjective (SSet.stdSimplex.objEquiv z.1).toOrderHom := by
      -- Outside the boundary means the simplex operator is surjective.
      simpa [SSet.boundary] using hzBoundary
    have hθeq : θ = SSet.stdSimplex.objEquiv z.1 := by
      -- The chosen representative `θ` is exactly the simplex operator of `z`.
      simpa using congrArg SSet.stdSimplex.objEquiv hθ
    have hsurj : Function.Surjective θ.toOrderHom := by
      simpa [hθeq] using hzsurj
    letI : Epi θ := (SimplexCategory.epi_iff_surjective).2 hsurj
    exact (Nat.not_le_of_gt hlt) (SimplexCategory.le_of_epi θ)
  · have hle : x.dim ≤ m := Nat.le_of_not_gt hlt
    by_cases hgt : x.dim < m
    · exfalso
      have hzdeg : z.1 ∈ (Δ[x.dim]).degenerate m := by
        -- In degrees strictly above `x.dim`, every simplex of `Δ[x.dim]` is degenerate.
        rw [((Δ[x.dim]).degenerate_eq_top_of_hasDimensionLT (x.dim + 1) m hgt)]
        simp
      exact (SSet.mem_nonDegenerate_iff_notMem_degenerate _ z.1).1 z.2 hzdeg
    · right
      have hm : m = x.dim := le_antisymm (Nat.le_of_not_gt hgt) hle
      subst hm
      have hznondeg : z.1 ∈ Δ[x.dim].nonDegenerate x.dim := z.2
      rw [SSet.stdSimplex.mem_nonDegenerate_iff_mono] at hznondeg
      have hθid : SSet.stdSimplex.objEquiv z.1 = 𝟙 ⦋x.dim⦌ :=
        SimplexCategory.eq_id_of_mono (SSet.stdSimplex.objEquiv z.1)
      have hzEq : z.1 = SSet.stdSimplex.objEquiv.symm (𝟙 ⦋x.dim⦌) := by
        -- In top degree, nondegeneracy says the simplex operator is mono, hence the identity.
        apply SSet.stdSimplex.objEquiv.injective
        simpa using hθid
      refine ⟨rfl, ?_⟩
      exact hzEq ▸ HEq.rfl

/-- Helper for Lemma 14.21.7: the only nondegenerate simplex of `V` outside `U` is the attached
simplex `x` itself. -/
private theorem nondegenerate_outside_subcomplex_eq_attached_simplex
    {V : SSet.{u}} {U : V.Subcomplex} (x : U.N)
    (hboundary : x.boundary_range_le)
    (hgen : U ⊔ Subcomplex.ofSimplex x.simplex = ⊤)
    {m : ℕ} (z : V.nonDegenerate m)
    (hzU : z.1 ∉ U.obj (op ⦋m⦌)) :
    ∃ _hm : m = x.dim, HEq z.1 x.simplex := by
  rcases simplex_outside_subcomplex_is_surjective_image x hboundary hgen hzU with
    ⟨θ, hθsurj, hθz⟩
  have hθinj : Function.Injective θ.toOrderHom := by
    by_contra hθinj
    cases m with
    | zero =>
        exact hθinj (by
          intro a b _
          fin_cases a
          fin_cases b
          rfl)
    | succ m =>
        obtain ⟨i, θ', hθfac⟩ := SimplexCategory.eq_σ_comp_of_not_injective θ hθinj
        have hzdeg : z.1 ∈ V.degenerate (m + 1) := by
          rw [SSet.mem_degenerate_iff]
          refine ⟨m, Nat.lt_succ_self m, SimplexCategory.σ i, inferInstance,
            V.map θ'.op x.simplex, ?_⟩
          -- The non-injective simplex operator factors through a degeneracy.
          simpa [hθfac, op_comp, Functor.map_comp] using hθz
        exact (SSet.mem_nonDegenerate_iff_notMem_degenerate _ z.1).1 z.2 hzdeg
  have hm_le : m ≤ x.dim := by
    letI : Mono θ := (SimplexCategory.mono_iff_injective).2 hθinj
    exact SimplexCategory.le_of_mono θ
  have hx_le : x.dim ≤ m := by
    letI : Epi θ := (SimplexCategory.epi_iff_surjective).2 hθsurj
    exact SimplexCategory.le_of_epi θ
  have hm : m = x.dim := le_antisymm hm_le hx_le
  subst hm
  letI : Mono θ := (SimplexCategory.mono_iff_injective).2 hθinj
  have hθid : θ = 𝟙 _ := SimplexCategory.eq_id_of_mono θ
  have hzEq : z.1 = x.simplex := by
    simpa [hθid] using hθz.symm
  refine ⟨rfl, ?_⟩
  exact hzEq ▸ HEq.rfl

/-- Helper for Lemma 14.21.7: evaluating the literal attached-simplex pushout in degree `m`
produces a pushout square in `Type`. -/
private theorem attached_pushout_app_isPushout
    {V : SSet.{u}} (U : V.Subcomplex) (x : U.N)
    (hboundary : x.boundary_range_le) (m : ℕ) :
    IsPushout
      ((∂Δ[x.dim].ι).app (op ⦋m⦌))
      ((attached_boundary_map U x hboundary).app (op ⦋m⦌))
      ((pushout.inl ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app (op ⦋m⦌))
      ((pushout.inr ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app (op ⦋m⦌)) := by
  letI :
      PreservesColimit
        (span ∂Δ[x.dim].ι (attached_boundary_map U x hboundary))
        ((evaluation _ _).obj (op ⦋m⦌)) := by
    infer_instance
  let c : PushoutCocone ∂Δ[x.dim].ι (attached_boundary_map U x hboundary) :=
    pushout.cocone ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)
  have hcType :
      IsColimit (((evaluation _ _).obj (op ⦋m⦌)).mapCocone c) := by
    exact
      Limits.isColimitOfPreserves ((evaluation _ _).obj (op ⦋m⦌))
        (pushout.isColimit ∂Δ[x.dim].ι (attached_boundary_map U x hboundary))
  exact IsPushout.of_isColimit_cocone hcType

/-- Helper for Lemma 14.21.7: if a nondegenerate simplex of the literal pushout comes from the
`U`-leg, then its representative in `U` is already nondegenerate. -/
private theorem nondegenerate_of_attached_pushout_inr
    {V : SSet.{u}} (U : V.Subcomplex) (x : U.N)
    (hboundary : x.boundary_range_le) {m : ℕ}
    (y : (pushout ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).nonDegenerate m)
    {u : U.toSSet.obj (op ⦋m⦌)}
    (hu :
      ((pushout.inr ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app (op ⦋m⦌)) u = y.1) :
    u ∈ U.toSSet.nonDegenerate m := by
  -- Proof comment: a degeneracy witness for `u` would transport through the pushout right leg to
  -- a degeneracy witness for the nondegenerate simplex `y`.
  refine (SSet.mem_nonDegenerate_iff_notMem_degenerate (X := U.toSSet) (x := u)).2 ?_
  intro hudeg
  have hy_nondeg :
      y.1 ∉ (pushout ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).degenerate m := by
    exact
      (SSet.mem_nonDegenerate_iff_notMem_degenerate
        (X := pushout ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)) (x := y.1)).1 y.2
  rw [SSet.mem_degenerate_iff] at hudeg
  rcases hudeg with ⟨j, hj, f, hf, u', hu'⟩
  have hydeg :
      y.1 ∈ (pushout ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).degenerate m := by
    rw [SSet.mem_degenerate_iff]
    refine ⟨j, hj, f, hf,
      ((pushout.inr ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app (op ⦋j⦌)) u', ?_⟩
    calc
      (pushout ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).map f.op
          (((pushout.inr ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app (op ⦋j⦌)) u') =
        ((pushout.inr ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app (op ⦋m⦌))
          (U.toSSet.map f.op u') := by
            simpa using
              (congrFun
                ((pushout.inr ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).naturality f.op)
                u').symm
      _ =
        ((pushout.inr ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app (op ⦋m⦌)) u := by
          exact congrArg
            ((pushout.inr ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app (op ⦋m⦌)) hu'
      _ = y.1 := hu
  exact hy_nondeg hydeg

/-- Helper for Lemma 14.21.7: if a nondegenerate simplex of the literal pushout comes from the
`Δ[x.dim]`-leg, then its representative simplex of `Δ[x.dim]` is already nondegenerate. -/
private theorem nondegenerate_of_attached_pushout_inl
    {V : SSet.{u}} (U : V.Subcomplex) (x : U.N)
    (hboundary : x.boundary_range_le) {m : ℕ}
    (y : (pushout ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).nonDegenerate m)
    {z : (Δ[x.dim] : SSet).obj (op ⦋m⦌)}
    (hz :
      ((pushout.inl ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app (op ⦋m⦌)) z = y.1) :
    z ∈ (Δ[x.dim] : SSet).nonDegenerate m := by
  -- Proof comment: a degeneracy witness for `z` would transport through the pushout left leg to
  -- a degeneracy witness for the nondegenerate simplex `y`.
  refine (SSet.mem_nonDegenerate_iff_notMem_degenerate (X := (Δ[x.dim] : SSet)) (x := z)).2 ?_
  intro hzdeg
  have hy_nondeg :
      y.1 ∉ (pushout ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).degenerate m := by
    exact
      (SSet.mem_nonDegenerate_iff_notMem_degenerate
        (X := pushout ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)) (x := y.1)).1 y.2
  rw [SSet.mem_degenerate_iff] at hzdeg
  rcases hzdeg with ⟨j, hj, f, hf, z', hz'⟩
  have hydeg :
      y.1 ∈ (pushout ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).degenerate m := by
    rw [SSet.mem_degenerate_iff]
    refine ⟨j, hj, f, hf,
      ((pushout.inl ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app (op ⦋j⦌)) z', ?_⟩
    calc
      (pushout ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).map f.op
          (((pushout.inl ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app (op ⦋j⦌)) z') =
        ((pushout.inl ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app (op ⦋m⦌))
          ((Δ[x.dim] : SSet).map f.op z') := by
            simpa using
              (congrFun
                ((pushout.inl ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).naturality f.op)
                z').symm
      _ =
        ((pushout.inl ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app (op ⦋m⦌)) z := by
          exact congrArg
            ((pushout.inl ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app (op ⦋m⦌)) hz'
      _ = y.1 := hz
  exact hy_nondeg hydeg

/-- Helper for Lemma 14.21.7: every degree-`m` simplex of the literal pushout comes from either
the `Δ[x.dim]`-leg or the `U`-leg. -/
private theorem attached_pushout_simplex_cases
    {V : SSet.{u}} (U : V.Subcomplex) (x : U.N)
    (hboundary : x.boundary_range_le) {m : ℕ}
    (y : (pushout ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).obj (op ⦋m⦌)) :
    (∃ z : (Δ[x.dim] : SSet).obj (op ⦋m⦌),
        ((pushout.inl ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app (op ⦋m⦌)) z = y) ∨
      ∃ u : U.toSSet.obj (op ⦋m⦌),
        ((pushout.inr ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app (op ⦋m⦌)) u = y := by
  -- Proof comment: the evaluated pushout square is a pushout in `Type`, so every element of the
  -- apex has a representative on one of the two visible legs.
  simpa using
    Types.eq_or_eq_of_isPushout (attached_pushout_app_isPushout U x hboundary m) y

/-- Helper for Lemma 14.21.7: every nondegenerate simplex of the literal pushout is either
already represented by a nondegenerate simplex of `U`, or is the unique attached top simplex. -/
private theorem pushout_nondegenerate_representation
    {V : SSet.{u}} (U : V.Subcomplex) (x : U.N)
    (hboundary : x.boundary_range_le) {m : ℕ}
    (y : (pushout ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).nonDegenerate m) :
    (∃ u : U.toSSet.nonDegenerate m,
        ((pushout.inr ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app (op ⦋m⦌)) u.1 = y.1) ∨
      ∃ _hm : m = x.dim,
        HEq y.1
          (((pushout.inl ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app (op ⦋x.dim⦌))
            (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋x.dim⦌))) := by
  rcases attached_pushout_simplex_cases U x hboundary y.1 with hcases | hcases
  · rcases hcases with ⟨z, hz⟩
    have hz_nondeg :
        z ∈ (Δ[x.dim] : SSet).nonDegenerate m :=
      nondegenerate_of_attached_pushout_inl U x hboundary y hz
    rcases stdSimplex_nondegenerate_boundary_or_top x ⟨z, hz_nondeg⟩ with hzBoundary | ⟨hm, hzTop⟩
    · let u0 : U.toSSet.obj (op ⦋m⦌) :=
        ((attached_boundary_map U x hboundary).app (op ⦋m⦌)) ⟨z, hzBoundary⟩
      have hcondition :
          ((pushout.inl ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app (op ⦋m⦌)) z =
            ((pushout.inr ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app (op ⦋m⦌)) u0 := by
        -- Proof comment: the boundary branch is identified with the `U`-leg by the pushout
        -- relation itself.
        simpa [u0] using
          congrFun
            (congrArg (fun k ↦ k.app (op ⦋m⦌))
              (pushout.condition (f := ∂Δ[x.dim].ι)
                (g := attached_boundary_map U x hboundary)))
            ⟨z, hzBoundary⟩
      have hu0 :
          ((pushout.inr ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app (op ⦋m⦌)) u0 = y.1 :=
        hcondition.symm.trans hz
      let u : U.toSSet.nonDegenerate m :=
        ⟨u0, nondegenerate_of_attached_pushout_inr U x hboundary y hu0⟩
      exact Or.inl ⟨u, hu0⟩
    · refine Or.inr ?_
      refine ⟨hm, ?_⟩
      subst hm
      have hzEq : z = SSet.stdSimplex.objEquiv.symm (𝟙 ⦋x.dim⦌) := eq_of_heq hzTop
      have hyEq :
          y.1 =
            ((pushout.inl ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app (op ⦋x.dim⦌))
              (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋x.dim⦌)) := by
        calc
          y.1 =
              ((pushout.inl ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app (op ⦋x.dim⦌))
                z := hz.symm
          _ =
              ((pushout.inl ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app (op ⦋x.dim⦌))
                (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋x.dim⦌)) := by simpa [hzEq]
      exact hyEq ▸ HEq.rfl
  · rcases hcases with ⟨u0, hu0⟩
    let u : U.toSSet.nonDegenerate m :=
      ⟨u0, nondegenerate_of_attached_pushout_inr U x hboundary y hu0⟩
    exact Or.inl ⟨u, hu0⟩

/-- Helper for Lemma 14.21.7: a simplex of the subcomplex simplicial set is nondegenerate exactly
when its image in the ambient simplicial set is nondegenerate. -/
private theorem subcomplex_nondegenerate_iff
    {V : SSet.{u}} (U : V.Subcomplex) {m : ℕ}
    (u : U.toSSet.obj (op ⦋m⦌)) :
    u ∈ U.toSSet.nonDegenerate m ↔
      (U.ι.app (op ⦋m⦌) u) ∈ V.nonDegenerate m := by
  -- Proof comment: this is the standard nondegenerate comparison for a simplicial subset.
  simpa using U.mem_nonDegenerate_iff u

/-- Helper for Lemma 14.21.7: on a simplex represented by the `U`-leg, the pushout comparison map
acts on the nondegenerate summand by the ambient inclusion `U ⟶ V`. -/
private theorem attached_pushout_desc_split_inr
    {V : SSet.{u}} (U : V.Subcomplex) (x : U.N)
    (hboundary : x.boundary_range_le) {m : ℕ}
    (y : (pushout ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).nonDegenerate m)
    (u : U.toSSet.nonDegenerate m)
    (hy :
      ((pushout.inr ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app (op ⦋m⦌)) u.1 = y.1) :
    (pushout ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).nonDegenerateSplitting.φ
        (attached_pushout_desc U x hboundary) m y =
      U.ι.app (op ⦋m⦌) u.1 := by
  -- Proof comment: the splitting map is the underlying degreewise map, so the right pushout
  -- computation reduces directly to `pushout.inr_desc`.
  change (attached_pushout_desc U x hboundary).app (op ⦋m⦌) y.1 =
    U.ι.app (op ⦋m⦌) u.1
  rw [← hy]
  simpa [attached_pushout_desc] using
    congrFun
      (congrArg (fun k ↦ k.app (op ⦋m⦌))
        (pushout.inr_desc (yonedaEquiv.symm x.simplex) U.ι
          (by simpa using (attached_boundary_map_comp U x hboundary).symm)))
      u.1

/-- Helper for Lemma 14.21.7: on the unique attached top simplex, the pushout comparison map acts
on the nondegenerate summand by sending it to `x.simplex`. -/
private theorem attached_pushout_desc_split_top
    {V : SSet.{u}} (U : V.Subcomplex) (x : U.N)
    (hboundary : x.boundary_range_le)
    (y : (pushout ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).nonDegenerate x.dim)
    (hy :
      HEq y.1
        (((pushout.inl ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app (op ⦋x.dim⦌))
          (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋x.dim⦌)))) :
    (pushout ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).nonDegenerateSplitting.φ
        (attached_pushout_desc U x hboundary) x.dim y =
      x.simplex := by
  -- Proof comment: after identifying the source simplex with the visible top simplex of the
  -- `Δ[x.dim]`-leg, the left pushout rule computes the image immediately.
  change (attached_pushout_desc U x hboundary).app (op ⦋x.dim⦌) y.1 = x.simplex
  rw [eq_of_heq hy]
  simpa [attached_pushout_desc] using
    congrFun
      (congrArg (fun k ↦ k.app (op ⦋x.dim⦌))
        (pushout.inl_desc (yonedaEquiv.symm x.simplex) U.ι
          (by simpa using (attached_boundary_map_comp U x hboundary).symm)))
      (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋x.dim⦌))

/-- Helper for Lemma 14.21.7: the canonical map from the literal pushout object to `V` is an
isomorphism. -/
private theorem pushout_desc_isIso
    {V : SSet.{u}} (U : V.Subcomplex) (x : U.N)
    (hboundary : x.boundary_range_le)
    (hgen : U ⊔ Subcomplex.ofSimplex x.simplex = ⊤) :
    IsIso (attached_pushout_desc U x hboundary) := by
  -- Route correction: the failed range-transport route would require `yonedaEquiv.symm x.simplex`
  -- to be mono, which is false in general. The source-faithful finish instead analyzes the actual
  -- pushout object and proves this comparison map is an isomorphism.
  let P := pushout ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)
  let f : P ⟶ V := attached_pushout_desc U x hboundary
  change IsIso f
  have hNew :
      ∀ {m : ℕ} (z : V.nonDegenerate m),
        z.1 ∉ U.obj (op ⦋m⦌) → ∃ hm : m = x.dim, HEq z.1 x.simplex :=
    fun z hzU ↦ nondegenerate_outside_subcomplex_eq_attached_simplex x hboundary hgen z hzU
  have hPreserves :
      ∀ ⦃m : ℕ⦄ (y : P.nonDegenerate m),
        (P.nonDegenerateSplitting.φ f m) y ∈ V.nonDegenerate m := by
    intro m y
    -- Proof comment: every nondegenerate simplex of the literal pushout comes from either the old
    -- `U`-branch or the unique new top simplex branch.
    rcases pushout_nondegenerate_representation U x hboundary y with hy | hy
    · rcases hy with ⟨u, hu⟩
      rw [show P.nonDegenerateSplitting.φ f m y =
        U.ι.app (op ⦋m⦌) u.1 by
          simpa [P, f] using attached_pushout_desc_split_inr U x hboundary y u hu]
      exact (subcomplex_nondegenerate_iff U u.1).1 u.2
    · rcases hy with ⟨hm, hy⟩
      subst hm
      rw [show P.nonDegenerateSplitting.φ f x.dim y = x.simplex by
        simpa [P, f] using attached_pushout_desc_split_top U x hboundary y hy]
      exact x.nonDegenerate
  have hPreimageNondeg :
      ∀ {m : ℕ} {y : P.obj (op ⦋m⦌)},
        f.app (op ⦋m⦌) y ∈ V.nonDegenerate m → y ∈ P.nonDegenerate m := by
    intro m y hy
    -- Proof comment: degeneracy is preserved by every simplicial map, so a degenerate source
    -- simplex cannot map to a nondegenerate target simplex.
    refine (SSet.mem_nonDegenerate_iff_notMem_degenerate (X := P) (x := y)).2 ?_
    intro hydeg
    rw [SSet.mem_degenerate_iff] at hydeg
    rcases hydeg with ⟨j, hj, g, hg, y', hy'⟩
    have himage_deg : f.app (op ⦋m⦌) y ∈ V.degenerate m := by
      rw [SSet.mem_degenerate_iff]
      refine ⟨j, hj, g, hg, f.app (op ⦋j⦌) y', ?_⟩
      calc
        V.map g.op (f.app (op ⦋j⦌) y') = f.app (op ⦋m⦌) (P.map g.op y') := by
          simpa using (congrFun (f.naturality g.op) y').symm
        _ = f.app (op ⦋m⦌) y := by
              exact congrArg (f.app (op ⦋m⦌)) hy'
    exact
      (SSet.mem_nonDegenerate_iff_notMem_degenerate (X := V)
        (x := f.app (op ⦋m⦌) y)).1 hy himage_deg
  have hBijective :
      ∀ m : ℕ, Function.Bijective ((SSet.toNonDegenerateSplitHom f hPreserves).f m) := by
    intro m
    constructor
    · intro y₁ y₂ hy
      have hy_val : P.nonDegenerateSplitting.φ f m y₁ = P.nonDegenerateSplitting.φ f m y₂ :=
        congrArg Subtype.val hy
      -- Proof comment: compare the two source simplices by splitting both into the old branch or
      -- the unique new top branch.
      rcases pushout_nondegenerate_representation U x hboundary y₁ with hy₁ | hy₁
      · rcases hy₁ with ⟨u₁, hu₁⟩
        rcases pushout_nondegenerate_representation U x hboundary y₂ with hy₂ | hy₂
        · rcases hy₂ with ⟨u₂, hu₂⟩
          have hsplit₁ :
              P.nonDegenerateSplitting.φ f m y₁ = U.ι.app (op ⦋m⦌) u₁.1 := by
            simpa [P, f] using attached_pushout_desc_split_inr U x hboundary y₁ u₁ hu₁
          have hsplit₂ :
              P.nonDegenerateSplitting.φ f m y₂ = U.ι.app (op ⦋m⦌) u₂.1 := by
            simpa [P, f] using attached_pushout_desc_split_inr U x hboundary y₂ u₂ hu₂
          have hι_injective : Function.Injective (U.ι.app (op ⦋m⦌)) := by
            exact (mono_iff_injective _).1 inferInstance
          have hu : u₁.1 = u₂.1 := hι_injective <| by
            calc
              U.ι.app (op ⦋m⦌) u₁.1 = P.nonDegenerateSplitting.φ f m y₁ := hsplit₁.symm
              _ = P.nonDegenerateSplitting.φ f m y₂ := hy_val
              _ = U.ι.app (op ⦋m⦌) u₂.1 := hsplit₂
          apply Subtype.ext
          calc
            y₁.1 =
                ((pushout.inr ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app
                  (op ⦋m⦌)) u₁.1 := hu₁.symm
            _ =
                ((pushout.inr ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app
                  (op ⦋m⦌)) u₂.1 := by simpa [hu]
            _ = y₂.1 := hu₂
        · rcases hy₂ with ⟨hm₂, hy₂⟩
          subst hm₂
          have hsplit₁ :
              P.nonDegenerateSplitting.φ f x.dim y₁ = U.ι.app (op ⦋x.dim⦌) u₁.1 := by
            simpa [P, f] using attached_pushout_desc_split_inr U x hboundary y₁ u₁ hu₁
          have hsplit₂ :
              P.nonDegenerateSplitting.φ f x.dim y₂ = x.simplex := by
            simpa [P, f] using attached_pushout_desc_split_top U x hboundary y₂ hy₂
          have hx_mem : x.simplex ∈ U.obj (op ⦋x.dim⦌) := by
            have hxu : U.ι.app (op ⦋x.dim⦌) u₁.1 = x.simplex := by
              calc
                U.ι.app (op ⦋x.dim⦌) u₁.1 = P.nonDegenerateSplitting.φ f x.dim y₁ := hsplit₁.symm
                _ = P.nonDegenerateSplitting.φ f x.dim y₂ := hy_val
                _ = x.simplex := hsplit₂
            exact hxu ▸ u₁.1.2
          exact False.elim (x.notMem hx_mem)
      · rcases hy₁ with ⟨hm₁, hy₁⟩
        subst hm₁
        rcases pushout_nondegenerate_representation U x hboundary y₂ with hy₂ | hy₂
        · rcases hy₂ with ⟨u₂, hu₂⟩
          have hsplit₁ :
              P.nonDegenerateSplitting.φ f x.dim y₁ = x.simplex := by
            simpa [P, f] using attached_pushout_desc_split_top U x hboundary y₁ hy₁
          have hsplit₂ :
              P.nonDegenerateSplitting.φ f x.dim y₂ = U.ι.app (op ⦋x.dim⦌) u₂.1 := by
            simpa [P, f] using attached_pushout_desc_split_inr U x hboundary y₂ u₂ hu₂
          have hx_mem : x.simplex ∈ U.obj (op ⦋x.dim⦌) := by
            have hxu : U.ι.app (op ⦋x.dim⦌) u₂.1 = x.simplex := by
              calc
                U.ι.app (op ⦋x.dim⦌) u₂.1 = P.nonDegenerateSplitting.φ f x.dim y₂ := hsplit₂.symm
                _ = P.nonDegenerateSplitting.φ f x.dim y₁ := hy_val.symm
                _ = x.simplex := hsplit₁
            exact hxu ▸ u₂.1.2
          exact False.elim (x.notMem hx_mem)
        · rcases hy₂ with ⟨hm₂, hy₂⟩
          clear hm₂
          apply Subtype.ext
          calc
            y₁.1 =
                ((pushout.inl ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app
                  (op ⦋x.dim⦌))
                  (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋x.dim⦌)) := eq_of_heq hy₁
            _ = y₂.1 := by simpa using (eq_of_heq hy₂).symm
    · intro z
      by_cases hzU : z.1 ∈ U.obj (op ⦋m⦌)
      · let u₀ : U.toSSet.obj (op ⦋m⦌) := ⟨z.1, hzU⟩
        have hu₀ : u₀ ∈ U.toSSet.nonDegenerate m := by
          exact (subcomplex_nondegenerate_iff U u₀).2 (by simpa [u₀] using z.2)
        let u : U.toSSet.nonDegenerate m := ⟨u₀, hu₀⟩
        let y₀ : P.obj (op ⦋m⦌) :=
          ((pushout.inr ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app (op ⦋m⦌)) u.1
        have hy₀_image : f.app (op ⦋m⦌) y₀ ∈ V.nonDegenerate m := by
          have hy₀_eq : f.app (op ⦋m⦌) y₀ = z.1 := by
            change (attached_pushout_desc U x hboundary).app (op ⦋m⦌)
                (((pushout.inr ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app
                  (op ⦋m⦌)) u.1) = z.1
            simpa [attached_pushout_desc, y₀, u]
              using congrFun
                (congrArg (fun k ↦ k.app (op ⦋m⦌))
                  (pushout.inr_desc (yonedaEquiv.symm x.simplex) U.ι
                    (by simpa using (attached_boundary_map_comp U x hboundary).symm)))
                u.1
          simpa [hy₀_eq] using z.2
        let y : P.nonDegenerate m := ⟨y₀, hPreimageNondeg hy₀_image⟩
        refine ⟨y, ?_⟩
        apply Subtype.ext
        change P.nonDegenerateSplitting.φ f m y = z.1
        have hy_branch :
            ((pushout.inr ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app (op ⦋m⦌))
              u.1 = y.1 := rfl
        calc
          P.nonDegenerateSplitting.φ f m y = U.ι.app (op ⦋m⦌) u.1 := by
            simpa [P, f, y, y₀] using attached_pushout_desc_split_inr U x hboundary y u hy_branch
          _ = z.1 := rfl
      · rcases hNew z hzU with ⟨hm, hzTop⟩
        subst hm
        let y₀ : P.obj (op ⦋x.dim⦌) :=
          ((pushout.inl ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app (op ⦋x.dim⦌))
            (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋x.dim⦌))
        have hy₀_image : f.app (op ⦋x.dim⦌) y₀ ∈ V.nonDegenerate x.dim := by
          have hy₀_eq : f.app (op ⦋x.dim⦌) y₀ = x.simplex := by
            change (attached_pushout_desc U x hboundary).app (op ⦋x.dim⦌)
                (((pushout.inl ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app
                  (op ⦋x.dim⦌)) (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋x.dim⦌))) = x.simplex
            simpa [attached_pushout_desc, y₀]
              using congrFun
                (congrArg (fun k ↦ k.app (op ⦋x.dim⦌))
                  (pushout.inl_desc (yonedaEquiv.symm x.simplex) U.ι
                    (by simpa using (attached_boundary_map_comp U x hboundary).symm)))
                (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋x.dim⦌))
          simpa [hy₀_eq] using x.nonDegenerate
        let y : P.nonDegenerate x.dim := ⟨y₀, hPreimageNondeg hy₀_image⟩
        refine ⟨y, ?_⟩
        apply Subtype.ext
        change P.nonDegenerateSplitting.φ f x.dim y = z.1
        have hy_branch :
            HEq y.1
              (((pushout.inl ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)).app
                  (op ⦋x.dim⦌))
                (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋x.dim⦌))) := HEq.rfl
        calc
          P.nonDegenerateSplitting.φ f x.dim y = x.simplex := by
            simpa [P, f, y, y₀] using attached_pushout_desc_split_top U x hboundary y hy_branch
          _ = z.1 := by simpa using (eq_of_heq hzTop).symm
  have hDegreewise :
      ∀ m : ℕ, Function.Bijective (f.app (op ⦋m⦌)) :=
    SSet.degreewise_bijective_of_nondegenerate_bijective (f := f) hPreserves hBijective
  -- Proof comment: Lemma 14.18.3 upgrades bijectivity on nondegenerate summands to bijectivity
  -- in every degree, and `SSet` checks isomorphy degreewise in `Type`.
  rw [NatTrans.isIso_iff_isIso_app]
  intro Δ
  cases Δ with
  | op Δ =>
      cases Δ with
      | mk m =>
          rw [isIso_iff_bijective]
          exact hDegreewise m

/-- Lemma 14.21.7: if a subcomplex `U ⊆ V` is obtained by adjoining the new nondegenerate simplex
`x : U.N`, if the boundary of `x.simplex` already lands in `U`, and if adjoining `x.simplex`
generates all of `V`, then the square `∂Δ[x.dim] ⟶ U`, `Δ[x.dim] ⟶ V` defined by `x.simplex` is
a pushout square. -/
-- Proof sketch: the boundary of the canonical map `Δ[x.dim] ⟶ V` classified by `x.simplex`
-- factors through `U` by `hboundary`. Then identify the image of `Δ[x.dim] ⟶ V` with
-- `Subcomplex.ofSimplex x.simplex`, use `hgen` to express that adjoining this subcomplex to `U`
-- gives all of `V`, identify its intersection with `U` with the boundary, and apply
-- `SSet.Subcomplex.BicartSq.isPushout` to the resulting bicartesian square of subcomplexes.
theorem isPushout_of_subcomplex_adjoin_simplex
    {V : SSet.{u}} (U : V.Subcomplex) (x : U.N)
    (hboundary : x.boundary_range_le)
    (hgen : U ⊔ Subcomplex.ofSimplex x.simplex = ⊤) :
    IsPushout ∂Δ[x.dim].ι
      (U.lift (∂Δ[x.dim].ι ≫ yonedaEquiv.symm x.simplex) hboundary)
      (yonedaEquiv.symm x.simplex) U.ι := by
  have hcomm :
      ∂Δ[x.dim].ι ≫ yonedaEquiv.symm x.simplex =
        attached_boundary_map U x hboundary ≫ U.ι := by
    -- Proof comment: this is the defining commutativity of the boundary factorization through `U`.
    simpa using (attached_boundary_map_comp U x hboundary).symm
  have hcanonical :
      IsPushout ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)
        (pushout.inl ∂Δ[x.dim].ι (attached_boundary_map U x hboundary))
        (pushout.inr ∂Δ[x.dim].ι (attached_boundary_map U x hboundary)) :=
    IsPushout.of_hasPushout _ _
  haveI : IsIso (attached_pushout_desc U x hboundary) :=
    pushout_desc_isIso U x hboundary hgen
  have hcolim :
      IsColimit
        (PushoutCocone.mk (yonedaEquiv.symm x.simplex) U.ι hcomm) := by
    let e :
        pushout ∂Δ[x.dim].ι (attached_boundary_map U x hboundary) ≅ V := by
      letI : IsIso (attached_pushout_desc U x hboundary) :=
        pushout_desc_isIso U x hboundary hgen
      exact asIso (attached_pushout_desc U x hboundary)
    refine IsColimit.ofIsoColimit hcanonical.isColimit ?_
    refine PushoutCocone.ext e ?_ ?_
    · -- Proof comment: the comparison map restricts to the simplex leg by the left pushout rule.
      simpa using
        (pushout.inl_desc (yonedaEquiv.symm x.simplex) U.ι hcomm)
    · -- Proof comment: the comparison map restricts to the subcomplex leg by the right pushout rule.
      simpa using
        (pushout.inr_desc (yonedaEquiv.symm x.simplex) U.ι hcomm)
  exact IsPushout.of_isColimit hcolim

end SSet
