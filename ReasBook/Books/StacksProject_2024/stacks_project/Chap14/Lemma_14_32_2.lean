import Mathlib
import StacksProject_2024.Chap14.Definition_14_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite CategoryTheory.SimplicialObject
open CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.SimplicialObject
open SSet (ι₀ ι₁)
open scoped Simplicial
open scoped MonoidalCategory

universe u

variable {V U : SSet.{u}} {n : ℕ} {f₀ f₁ : V ⟶ U}

/- Domain-style sampling for Lemma 14.32.2:
- primary domain: simplicial-set homotopies and coskeleta.
- inspected owner declarations:
  `SSet.Homotopy`,
  `SSet.Homotopy.toSimplicialObjectHomotopy`,
  `SimplicialObject.IsCoskeletal`,
  `SimplicialObject.isoCoskOfIsCoskeletal`.
- best owner abstraction:
  the source-facing existence statement should land on the simplicial-set owner
  `SSet.Homotopy f₀ f₁`; the combinatorial owner `SimplicialObject.Homotopy f₀ f₁` is the
  canonical bridge/view obtained from `SSet.Homotopy.toSimplicialObjectHomotopy`.
- primitive-vs-derived split:
  primitive data: the two maps `f₀, f₁`, their agreement in degrees `< n`, and the coskeletality
  hypotheses on `U` and `V`;
  derived API: the combinatorial homotopy operators and the zigzag relation `Homotopic`.

Source/core/bridge triage:
- `source-facing`: existence of a homotopy between the simplicial-set maps `f₀` and `f₁`;
- `core/canonical`: `SSet.Homotopy`;
- `bridge/view`: `SSet.Homotopy.toSimplicialObjectHomotopy`.

The previous statement used the bridge owner `SimplicialObject.Homotopy` as the main target. Since
mathlib already organizes simplicial-set homotopies around `SSet.Homotopy`, the refined public
surface should use that owner directly and leave the combinatorial formulation as derived API. -/

-- Proof sketch: by Lemma 14.32.1, quotient the `n`-simplices of `U` by the relations
-- `f₀(y) ∼ f₁(y)` to obtain a trivial Kan fibration `U ⟶ W`, and let `f : V ⟶ W` be the common
-- composite of `f₀` and `f₁`. Then Lemma 14.30.2 gives a lift in the square
-- `∂Δ[1] × V ⟶ U` over `Δ[1] × V ⟶ W`, producing the required simplicial homotopy from `f₀` to
-- `f₁`. The bridge to the combinatorial owner is
-- `SSet.Homotopy.toSimplicialObjectHomotopy`.
variable
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌))
    (hU : U.IsCoskeletal n)
    (hV : V.IsCoskeletal n)

/-- Helper for Lemma 14.32.2: if an `n`-simplex comes from a lower simplicial degree, then `f₀`
and `f₁` agree on it because they already agree in that lower degree. -/
private theorem eq_on_top_simplex_from_lower_degree
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌))
    {m : ℕ} (hm : m < n) (θ : ⦋n⦌ ⟶ ⦋m⦌) (v : V.obj (op ⦋m⦌)) :
    f₀.app (op ⦋n⦌) (V.map θ.op v) = f₁.app (op ⦋n⦌) (V.map θ.op v) := by
  -- Rewrite both sides back down to simplicial degree `m`, where `hbelow` applies directly.
  have hmv : f₀.app (op ⦋m⦌) v = f₁.app (op ⦋m⦌) v := by
    exact congrFun (hbelow m hm) v
  calc
    f₀.app (op ⦋n⦌) (V.map θ.op v) = U.map θ.op (f₀.app (op ⦋m⦌) v) := by
      simpa using congrFun (f₀.naturality θ.op) v
    _ = U.map θ.op (f₁.app (op ⦋m⦌) v) := by
      rw [hmv]
    _ = f₁.app (op ⦋n⦌) (V.map θ.op v) := by
      simpa using (congrFun (f₁.naturality θ.op) v).symm

/-- Helper for Lemma 14.32.2: if a simplex of `Δ[1]` takes the value `1` at `0`, then every
precomposition still takes the value `1` at `0`. -/
private theorem deltaOne_map_zero_eq_one_of_zero_eq_one
    {m l : ℕ} (θ : ⦋m⦌ ⟶ ⦋l⦌) {α : (Δ[1] : SSet).obj (op ⦋l⦌)}
    (hα : SSet.stdSimplex.asOrderHom α 0 = (1 : Fin 2)) :
    SSet.stdSimplex.asOrderHom ((Δ[1] : SSet).map θ.op α) 0 = (1 : Fin 2) := by
  -- Monotonicity forces every vertex of `α` to be `1`, so the precomposed simplex is still `1`
  -- at the initial vertex.
  change SSet.stdSimplex.asOrderHom α (θ.toOrderHom 0) = (1 : Fin 2)
  apply le_antisymm
  · exact Fin.le_last _
  · exact hα ▸ (SSet.stdSimplex.asOrderHom α).monotone (Fin.zero_le _)

/-- Helper for Lemma 14.32.2: this is the degreewise candidate for the `n`-truncated cylinder
map used in the second source proof. In top degree it switches to `f₁` exactly on the constant
`1` simplex of `Δ[1]`; otherwise it uses `f₀`. -/
private def truncatedCylinderHomotopyComponent
    (Δ : (SimplexCategory.Truncated n)ᵒᵖ) :
    (((SSet.truncation n).obj (V ⊗ Δ[1])).obj Δ) →
      (((SSet.truncation n).obj U).obj Δ) :=
  fun x ↦
    if Δ.unop.1.len = n then
      if SSet.stdSimplex.asOrderHom x.2 0 = (1 : Fin 2) then
        f₁.app (op Δ.unop.1) x.1
      else
        f₀.app (op Δ.unop.1) x.1
    else
      f₀.app (op Δ.unop.1) x.1

/-- Helper for Lemma 14.32.2: the degreewise cylinder candidate restricts to `f₀` on the
`0`-endpoint. -/
private theorem truncatedCylinderHomotopyComponent_zero_endpoint
    (_hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌))
    {m : ℕ} (hm : m ≤ n) (v : V.obj (op ⦋m⦌)) :
    truncatedCylinderHomotopyComponent (f₀ := f₀) (f₁ := f₁)
        (op (⟨SimplexCategory.mk m, hm⟩ : SimplexCategory.Truncated n))
        ((ι₀ : V ⟶ V ⊗ Δ[1]).app (op ⦋m⦌) v) =
      f₀.app (op ⦋m⦌) v := by
  -- The second factor of `ι₀` is the constant `0` simplex, so the top-degree branch cannot use
  -- `f₁`.
  dsimp [truncatedCylinderHomotopyComponent]
  by_cases htop : m = n
  · have hzero :
        SSet.stdSimplex.asOrderHom ((ι₀.app (op ⦋m⦌) v).2) 0 = (0 : Fin 2) := by
      change ((ι₀.app (op ⦋m⦌) v).2) 0 = (0 : Fin 2)
      exact SSet.ι₀_app_snd_apply v 0
    split_ifs with hone
    · exfalso
      exact Fin.zero_ne_one (hzero.symm.trans hone)
    · rfl
  · simp [htop]

/-- Helper for Lemma 14.32.2: the degreewise cylinder candidate restricts to `f₁` on the
`1`-endpoint. Below the top degree this uses the hypothesis `hbelow`; in top degree the branch is
definitionally the `f₁` branch. -/
private theorem truncatedCylinderHomotopyComponent_one_endpoint
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌))
    {m : ℕ} (hm : m ≤ n) (v : V.obj (op ⦋m⦌)) :
    truncatedCylinderHomotopyComponent (f₀ := f₀) (f₁ := f₁)
        (op (⟨SimplexCategory.mk m, hm⟩ : SimplexCategory.Truncated n))
        ((ι₁ : V ⟶ V ⊗ Δ[1]).app (op ⦋m⦌) v) =
      f₁.app (op ⦋m⦌) v := by
  -- At the `1`-endpoint the second factor is the constant `1` simplex. If `m < n`, the
  -- definition still chooses the lower-degree `f₀` branch, and `hbelow` identifies it with `f₁`.
  dsimp [truncatedCylinderHomotopyComponent]
  by_cases htop : m = n
  · have hone :
        SSet.stdSimplex.asOrderHom ((ι₁.app (op ⦋m⦌) v).2) 0 = (1 : Fin 2) := by
      change ((ι₁.app (op ⦋m⦌) v).2) 0 = (1 : Fin 2)
      exact SSet.ι₁_app_snd_apply v 0
    split_ifs with hzero
    · rfl
    · exfalso
      exact hzero hone
  · have hm_lt : m < n := lt_of_le_of_ne hm htop
    simp [htop, congrFun (hbelow m hm_lt) v]

/-- Helper for Lemma 14.32.2: a non-surjective endomorphism of the top simplex factors through a
strictly lower simplicial degree. -/
private theorem simplex_endomorphism_factor_through_lower_of_not_surjective
    {m : ℕ} (θ : ⦋m + 1⦌ ⟶ ⦋m + 1⦌)
    (hθ : ¬ Function.Surjective θ.toOrderHom) :
    ∃ (i : Fin (m + 2)) (θ' : ⦋m + 1⦌ ⟶ ⦋m⦌), θ = θ' ≫ SimplexCategory.δ i := by
  -- This is exactly the standard `δ`-factorization for a map missing some vertex.
  simpa using SimplexCategory.eq_comp_δ_of_not_surjective θ hθ

/-- Helper for Lemma 14.32.2: in the only hard top-degree branch, the simplex operator misses the
initial vertex and therefore factors through a lower degree, so `f₀` and `f₁` still agree after
precomposition. -/
private theorem truncatedCylinderHomotopyComponent_top_mixed_naturality
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌))
    (θ : ⦋n⦌ ⟶ ⦋n⦌) (x : (V ⊗ Δ[1]).obj (op ⦋n⦌))
    (hx : SSet.stdSimplex.asOrderHom x.2 0 ≠ (1 : Fin 2))
    (hθx : SSet.stdSimplex.asOrderHom (((Δ[1] : SSet).map θ.op) x.2) 0 = (1 : Fin 2)) :
    f₁.app (op ⦋n⦌) (V.map θ.op x.1) = U.map θ.op (f₀.app (op ⦋n⦌) x.1) := by
  -- Route correction: the previous attempt stalled in this mixed branch. The source proof shows
  -- that if the precomposed `Δ[1]`-simplex becomes constant `1`, then `θ` misses the vertex `0`
  -- and hence factors through a lower degree.
  cases n with
  | zero =>
      -- In degree `0`, every endomorphism is the identity, so the mixed branch is impossible.
      exfalso
      have hθid : θ = 𝟙 _ := Subsingleton.elim _ _
      have hx' :
          SSet.stdSimplex.asOrderHom (((Δ[1] : SSet).map θ.op) x.2) 0 =
            SSet.stdSimplex.asOrderHom x.2 0 := by
        simpa [hθid]
      exact hx (hx'.symm.trans hθx)
  | succ m =>
      have hx0 : SSet.stdSimplex.asOrderHom x.2 0 = (0 : Fin 2) := by
        have hcases :
            SSet.stdSimplex.asOrderHom x.2 0 = (0 : Fin 2) ∨
              SSet.stdSimplex.asOrderHom x.2 0 = (1 : Fin 2) := by
          fin_cases h0 : SSet.stdSimplex.asOrderHom x.2 0
          · exact Or.inl h0
          · exact Or.inr h0
        rcases hcases with h0 | h0
        · exact h0
        · exact False.elim (hx h0)
      have hmissing_zero : ∀ y, θ.toOrderHom y ≠ 0 := by
        intro y hy
        have hθ0_le : θ.toOrderHom 0 ≤ θ.toOrderHom y :=
          θ.toOrderHom.monotone (Fin.zero_le y)
        rw [hy] at hθ0_le
        have hθ0 : θ.toOrderHom 0 = 0 := le_antisymm hθ0_le (Fin.zero_le _)
        change SSet.stdSimplex.asOrderHom x.2 (θ.toOrderHom 0) = (1 : Fin 2) at hθx
        rw [hθ0, hx0] at hθx
        exact Fin.zero_ne_one hθx
      have hnot_surj : ¬ Function.Surjective θ.toOrderHom := by
        intro hsurj
        obtain ⟨y, hy⟩ := hsurj 0
        exact hmissing_zero y hy
      obtain ⟨i, θ', hfac⟩ :=
        simplex_endomorphism_factor_through_lower_of_not_surjective θ hnot_surj
      have htop_eq :
          f₀.app (op ⦋m + 1⦌) (V.map θ.op x.1) =
            f₁.app (op ⦋m + 1⦌) (V.map θ.op x.1) := by
        -- Rewrite the top simplex through the lower-degree factor and then use `hbelow`.
        rw [hfac, op_comp, V.map_comp]
        simpa using
          eq_on_top_simplex_from_lower_degree
            (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow
            (m := m) (Nat.lt_succ_self m) (SimplexCategory.δ i) (V.map θ'.op x.1)
      calc
        f₁.app (op ⦋m + 1⦌) (V.map θ.op x.1) =
            f₀.app (op ⦋m + 1⦌) (V.map θ.op x.1) := htop_eq.symm
        _ = U.map θ.op (f₀.app (op ⦋m + 1⦌) x.1) := by
            simpa using congrFun (f₀.naturality θ.op) x.1

/-- Helper for Lemma 14.32.2: below top degree, the truncated cylinder component always uses the
`f₀` branch. -/
private theorem truncatedCylinderHomotopyComponent_of_lt
    {m : ℕ} (hm : m ≤ n) (hm_lt : m < n) (y : (V ⊗ Δ[1]).obj (op ⦋m⦌)) :
    truncatedCylinderHomotopyComponent (f₀ := f₀) (f₁ := f₁)
        (op (⟨SimplexCategory.mk m, hm⟩ : SimplexCategory.Truncated n)) y =
      f₀.app (op ⦋m⦌) y.1 := by
  -- Below top degree, the outer branch of `truncatedCylinderHomotopyComponent` immediately picks
  -- `f₀`, so no information about the `Δ[1]`-coordinate is needed.
  dsimp [truncatedCylinderHomotopyComponent]
  simp [Nat.ne_of_lt hm_lt]

/-- Helper for Lemma 14.32.2: in top degree, the cylinder component is the `f₁` branch exactly
when the `Δ[1]`-coordinate is constant `1` at the initial vertex. -/
private theorem truncatedCylinderHomotopyComponent_of_top_zero_eq_one
    {m : ℕ} (hm : m ≤ n) (hm_eq : m = n) (y : (V ⊗ Δ[1]).obj (op ⦋m⦌))
    (hy : SSet.stdSimplex.asOrderHom y.2 0 = (1 : Fin 2)) :
    truncatedCylinderHomotopyComponent (f₀ := f₀) (f₁ := f₁)
        (op (⟨SimplexCategory.mk m, hm⟩ : SimplexCategory.Truncated n)) y =
      f₁.app (op ⦋m⦌) y.1 := by
  -- In top degree, the inner branch is controlled exactly by the initial vertex of the
  -- `Δ[1]`-coordinate; the hypothesis says we are in the `f₁` branch.
  subst m
  dsimp [truncatedCylinderHomotopyComponent]
  split_ifs with hzero
  · rfl
  · exact False.elim (hzero hy)

/-- Helper for Lemma 14.32.2: in top degree, if the initial vertex of the `Δ[1]`-coordinate is
not `1`, then the cylinder component uses the `f₀` branch. -/
private theorem truncatedCylinderHomotopyComponent_of_top_zero_ne_one
    {m : ℕ} (hm : m ≤ n) (hm_eq : m = n) (y : (V ⊗ Δ[1]).obj (op ⦋m⦌))
    (hy : SSet.stdSimplex.asOrderHom y.2 0 ≠ (1 : Fin 2)) :
    truncatedCylinderHomotopyComponent (f₀ := f₀) (f₁ := f₁)
        (op (⟨SimplexCategory.mk m, hm⟩ : SimplexCategory.Truncated n)) y =
      f₀.app (op ⦋m⦌) y.1 := by
  -- In top degree, if the initial vertex is not `1`, the definition stays on the `f₀` branch.
  subst m
  dsimp [truncatedCylinderHomotopyComponent]
  split_ifs with hzero
  · exact False.elim (hy hzero)
  · rfl

/-- Helper for Lemma 14.32.2: if the source degree is strictly below `n`, the degreewise cylinder
candidate is natural because the source branch is forced to use `f₀`. -/
private theorem truncatedCylinderHomotopyComponent_naturality_raw_source_low
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌))
    {k l : ℕ} (hk : k ≤ n) (hl : l ≤ n) (hk_lt : k < n)
    (θ : ⦋k⦌ ⟶ ⦋l⦌) (x : (V ⊗ Δ[1]).obj (op ⦋l⦌)) :
    truncatedCylinderHomotopyComponent (f₀ := f₀) (f₁ := f₁)
        (op (⟨SimplexCategory.mk k, hk⟩ : SimplexCategory.Truncated n))
        ((V ⊗ Δ[1]).map θ.op x) =
      U.map θ.op
        (truncatedCylinderHomotopyComponent (f₀ := f₀) (f₁ := f₁)
          (op (⟨SimplexCategory.mk l, hl⟩ : SimplexCategory.Truncated n)) x) := by
  -- The source degree is below `n`, so the left-hand side is forced onto the `f₀` branch.
  rw [truncatedCylinderHomotopyComponent_of_lt
    (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hk hk_lt ((V ⊗ Δ[1]).map θ.op x)]
  rcases Nat.lt_or_eq_of_le hl with hl_lt | hl_eq
  · -- If the target degree is also below `n`, both sides use `f₀`, so naturality of `f₀`
    -- closes the square.
    rw [truncatedCylinderHomotopyComponent_of_lt
      (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hl hl_lt x]
    simpa using congrFun (f₀.naturality θ.op) x.1
  · by_cases hx : SSet.stdSimplex.asOrderHom x.2 0 = (1 : Fin 2)
    · -- If the top-degree target branch chooses `f₁`, naturality of `f₁` transports the right
      -- side to degree `k`, where `hbelow` identifies `f₀` and `f₁`.
      rw [truncatedCylinderHomotopyComponent_of_top_zero_eq_one
        (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hl hl_eq x hx]
      calc
        f₀.app (op ⦋k⦌) (((V ⊗ Δ[1]).map θ.op x).1) =
            f₁.app (op ⦋k⦌) (((V ⊗ Δ[1]).map θ.op x).1) := by
              exact congrFun (hbelow k hk_lt) (((V ⊗ Δ[1]).map θ.op x).1)
        _ = U.map θ.op (f₁.app (op ⦋l⦌) x.1) := by
              simpa using congrFun (f₁.naturality θ.op) x.1
    · -- Otherwise the top-degree target branch also uses `f₀`.
      rw [truncatedCylinderHomotopyComponent_of_top_zero_ne_one
        (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hl hl_eq x hx]
      simpa using congrFun (f₀.naturality θ.op) x.1

/-- Helper for Lemma 14.32.2: if the target degree is strictly below `n`, the only possible top
branch on the left comes from a degenerate top simplex and is reduced to the lower degree by
`eq_on_top_simplex_from_lower_degree`. -/
private theorem truncatedCylinderHomotopyComponent_naturality_raw_target_low
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌))
    {k l : ℕ} (hk : k ≤ n) (hl : l ≤ n) (hk_eq : k = n) (hl_lt : l < n)
    (θ : ⦋k⦌ ⟶ ⦋l⦌) (x : (V ⊗ Δ[1]).obj (op ⦋l⦌)) :
    truncatedCylinderHomotopyComponent (f₀ := f₀) (f₁ := f₁)
        (op (⟨SimplexCategory.mk k, hk⟩ : SimplexCategory.Truncated n))
        ((V ⊗ Δ[1]).map θ.op x) =
      U.map θ.op
        (truncatedCylinderHomotopyComponent (f₀ := f₀) (f₁ := f₁)
          (op (⟨SimplexCategory.mk l, hl⟩ : SimplexCategory.Truncated n)) x) := by
  -- The target degree is below `n`, so the right-hand side is always the `f₀` branch. The only
  -- extra work is the possible `f₁` branch on the left, which occurs on a degenerate top simplex.
  subst k
  rw [truncatedCylinderHomotopyComponent_of_lt
    (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hl hl_lt x]
  by_cases hpre :
      SSet.stdSimplex.asOrderHom ((((Δ[1] : SSet).map θ.op) x.2)) 0 = (1 : Fin 2)
  · rw [truncatedCylinderHomotopyComponent_of_top_zero_eq_one
      (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) le_rfl rfl ((V ⊗ Δ[1]).map θ.op x)]
    · calc
        f₁.app (op ⦋n⦌) (((V ⊗ Δ[1]).map θ.op x).1) =
            f₀.app (op ⦋n⦌) (((V ⊗ Δ[1]).map θ.op x).1) := by
              symm
              simpa using
                eq_on_top_simplex_from_lower_degree
                  (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow
                  (m := l) hl_lt θ x.1
        _ = U.map θ.op (f₀.app (op ⦋l⦌) x.1) := by
              simpa using congrFun (f₀.naturality θ.op) x.1
    · simpa using hpre
  · rw [truncatedCylinderHomotopyComponent_of_top_zero_ne_one
      (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) le_rfl rfl ((V ⊗ Δ[1]).map θ.op x)]
    · simpa using congrFun (f₀.naturality θ.op) x.1
    · simpa using hpre

/-- Helper for Lemma 14.32.2: in top degree, the naturality check splits into the two easy
same-branch cases and the one mixed case already handled by the factor-through-lower-degree
argument. -/
private theorem truncatedCylinderHomotopyComponent_naturality_raw_top_top
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌))
    (θ : ⦋n⦌ ⟶ ⦋n⦌) (x : (V ⊗ Δ[1]).obj (op ⦋n⦌)) :
    truncatedCylinderHomotopyComponent (f₀ := f₀) (f₁ := f₁)
        (op (⟨SimplexCategory.mk n, le_rfl⟩ : SimplexCategory.Truncated n))
        ((V ⊗ Δ[1]).map θ.op x) =
      U.map θ.op
        (truncatedCylinderHomotopyComponent (f₀ := f₀) (f₁ := f₁)
          (op (⟨SimplexCategory.mk n, le_rfl⟩ : SimplexCategory.Truncated n)) x) := by
  -- In top degree, the source proof splits according to whether the original and precomposed
  -- `Δ[1]`-simplices are constant `1` at the initial vertex.
  by_cases hx : SSet.stdSimplex.asOrderHom x.2 0 = (1 : Fin 2)
  · have hpre :
        SSet.stdSimplex.asOrderHom ((((Δ[1] : SSet).map θ.op) x.2)) 0 = (1 : Fin 2) :=
      deltaOne_map_zero_eq_one_of_zero_eq_one (θ := θ) hx
    rw [truncatedCylinderHomotopyComponent_of_top_zero_eq_one
      (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) le_rfl rfl ((V ⊗ Δ[1]).map θ.op x)]
    · rw [truncatedCylinderHomotopyComponent_of_top_zero_eq_one
        (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) le_rfl rfl x hx]
      simpa using congrFun (f₁.naturality θ.op) x.1
    · simpa using hpre
  · by_cases hpre :
      SSet.stdSimplex.asOrderHom ((((Δ[1] : SSet).map θ.op) x.2)) 0 = (1 : Fin 2)
    · rw [truncatedCylinderHomotopyComponent_of_top_zero_eq_one
        (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) le_rfl rfl ((V ⊗ Δ[1]).map θ.op x)]
      · rw [truncatedCylinderHomotopyComponent_of_top_zero_ne_one
          (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) le_rfl rfl x hx]
        exact truncatedCylinderHomotopyComponent_top_mixed_naturality
          (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow θ x hx hpre
      · simpa using hpre
    · rw [truncatedCylinderHomotopyComponent_of_top_zero_ne_one
        (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) le_rfl rfl ((V ⊗ Δ[1]).map θ.op x)]
      · rw [truncatedCylinderHomotopyComponent_of_top_zero_ne_one
          (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) le_rfl rfl x hx]
        simpa using congrFun (f₀.naturality θ.op) x.1
      · simpa using hpre

/-- Helper for Lemma 14.32.2: the degreewise cylinder candidate is natural after dispatching the
source proof's three cases on the raw simplicial degrees `k,l ≤ n`. -/
private theorem truncatedCylinderHomotopyComponent_naturality_raw_degreewise
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌))
    {k l : ℕ} (hk : k ≤ n) (hl : l ≤ n)
    (θ : ⦋k⦌ ⟶ ⦋l⦌) (x : (V ⊗ Δ[1]).obj (op ⦋l⦌)) :
    truncatedCylinderHomotopyComponent (f₀ := f₀) (f₁ := f₁)
        (op (⟨SimplexCategory.mk k, hk⟩ : SimplexCategory.Truncated n))
        ((V ⊗ Δ[1]).map θ.op x) =
      U.map θ.op
        (truncatedCylinderHomotopyComponent (f₀ := f₀) (f₁ := f₁)
          (op (⟨SimplexCategory.mk l, hl⟩ : SimplexCategory.Truncated n)) x) := by
  -- Dispatch exactly along the source proof's three degree patterns.
  rcases Nat.lt_or_eq_of_le hk with hk_lt | hk_eq
  · exact truncatedCylinderHomotopyComponent_naturality_raw_source_low
      (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow hk hl hk_lt θ x
  · rcases Nat.lt_or_eq_of_le hl with hl_lt | hl_eq
    · exact truncatedCylinderHomotopyComponent_naturality_raw_target_low
        (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow hk hl hk_eq hl_lt θ x
    · subst k
      subst l
      simpa using
        truncatedCylinderHomotopyComponent_naturality_raw_top_top
          (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow θ x

/-- Helper for Lemma 14.32.2: the degreewise cylinder candidate is natural on the truncated
simplex category, so it defines a morphism of `n`-truncated simplicial sets. -/
private theorem truncatedCylinderHomotopyComponent_naturality
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌))
    {Δ₁ Δ₂ : SimplexCategory.Truncated n} (φ : Δ₁ ⟶ Δ₂)
    (x : (((SSet.truncation n).obj (V ⊗ Δ[1])).obj (op Δ₂))) :
    truncatedCylinderHomotopyComponent (f₀ := f₀) (f₁ := f₁) (op Δ₁)
        (((SSet.truncation n).obj (V ⊗ Δ[1])).map φ.op x) =
      (((SSet.truncation n).obj U).map φ.op)
        (truncatedCylinderHomotopyComponent (f₀ := f₀) (f₁ := f₁) (op Δ₂) x) := by
  -- The wrapper theorem is just the raw degreewise statement written in the truncated syntax.
  simpa using
    truncatedCylinderHomotopyComponent_naturality_raw_degreewise
      (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow
      (hk := Δ₁.2) (hl := Δ₂.2) (θ := (show Δ₁.1 ⟶ Δ₂.1 from φ)) (x := x)

/-- Helper for Lemma 14.32.2: the degreewise natural family packages into a morphism of
`n`-truncated simplicial sets. -/
private noncomputable def truncatedCylinderHomotopy :
    ((SSet.truncation n).obj (V ⊗ Δ[1])) ⟶ ((SSet.truncation n).obj U) where
  app Δ := truncatedCylinderHomotopyComponent (f₀ := f₀) (f₁ := f₁) Δ
  naturality := fun {_ _} φ ↦
    funext (truncatedCylinderHomotopyComponent_naturality
      (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow φ.unop)

/-- Helper for Lemma 14.32.2: after packaging the truncated cylinder, its restriction along the
`0`-endpoint is exactly the truncation of `f₀`. -/
private theorem truncatedCylinderHomotopy_zero_endpoint
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌)) :
    (SSet.truncation n).map (ι₀ : V ⟶ V ⊗ Δ[1]) ≫
        truncatedCylinderHomotopy (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow =
      (SSet.truncation n).map f₀ := by
  -- Evaluate at each truncated degree and apply the already proved endpoint component formula.
  ext Δ v
  simpa using truncatedCylinderHomotopyComponent_zero_endpoint
    (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow Δ.unop.2 v

/-- Helper for Lemma 14.32.2: after packaging the truncated cylinder, its restriction along the
`1`-endpoint is exactly the truncation of `f₁`. -/
private theorem truncatedCylinderHomotopy_one_endpoint
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌)) :
    (SSet.truncation n).map (ι₁ : V ⟶ V ⊗ Δ[1]) ≫
        truncatedCylinderHomotopy (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow =
      (SSet.truncation n).map f₁ := by
  -- Evaluate at each truncated degree and apply the already proved endpoint component formula.
  ext Δ v
  simpa using truncatedCylinderHomotopyComponent_one_endpoint
    (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow Δ.unop.2 v

/-- Helper for Lemma 14.32.2: the truncated cylinder morphism lifts uniquely to a map into the
coskeleton of `U`. -/
private noncomputable def truncatedCylinderHomotopyLiftToCosk
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌)) :
    V ⊗ Δ[1] ⟶ (SSet.Truncated.cosk n).obj ((SSet.truncation n).obj U) :=
  ((coskAdj n).homEquiv (V ⊗ Δ[1]) ((SSet.truncation n).obj U)).symm
    (truncatedCylinderHomotopy (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow)

/-- Helper for Lemma 14.32.2: composing the lifted map with the coskeletal comparison isomorphism
of `U` gives the actual cylinder map `V × Δ[1] ⟶ U`. -/
private noncomputable def liftedCylinderMap
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌))
    (hU : U.IsCoskeletal n) :
    V ⊗ Δ[1] ⟶ U :=
  letI : U.IsCoskeletal n := hU
  truncatedCylinderHomotopyLiftToCosk (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow ≫
    (U.isoCoskOfIsCoskeletal n).inv

/-- Helper for Lemma 14.32.2: under `coskAdj n`, the truncation of a map into an `n`-coskeletal
target transports back to the map composed with the canonical comparison into the coskeleton. -/
private theorem coskAdj_symm_truncation_map
    (g : V ⟶ U) (hU : U.IsCoskeletal n) :
    ((coskAdj n).homEquiv V ((SSet.truncation n).obj U)).symm ((SSet.truncation n).map g) =
      g ≫ (U.isoCoskOfIsCoskeletal n).hom := by
  letI : U.IsCoskeletal n := hU
  -- Compare the adjunction inverse with the unit and then identify the unit with
  -- `U.isoCoskOfIsCoskeletal n`.
  calc
    ((coskAdj n).homEquiv V ((SSet.truncation n).obj U)).symm ((SSet.truncation n).map g) =
        (coskAdj n).unit.app V ≫ (SSet.Truncated.cosk n).map ((SSet.truncation n).map g) := by
          simpa using
            (Adjunction.homEquiv_unit (adj := coskAdj n) (f := (SSet.truncation n).map g))
    _ = g ≫ (coskAdj n).unit.app U := by
          simpa using ((coskAdj n).unit.naturality g).symm
    _ = g ≫ (U.isoCoskOfIsCoskeletal n).hom := by
          rfl

/-- Helper for Lemma 14.32.2: if the truncated cylinder already has the desired endpoint after
truncation, then the lifted cylinder has that endpoint before truncation as well. -/
private theorem liftedCylinderMap_endpoint_via_coskAdj
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌))
    (hU : U.IsCoskeletal n) (ept : V ⟶ V ⊗ Δ[1]) (g : V ⟶ U)
    (hept :
      (SSet.truncation n).map ept ≫
          truncatedCylinderHomotopy (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow =
        (SSet.truncation n).map g) :
    ept ≫ liftedCylinderMap (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow hU = g := by
  letI : U.IsCoskeletal n := hU
  let ht :=
    truncatedCylinderHomotopy (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow
  let hcosk :=
    truncatedCylinderHomotopyLiftToCosk (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow
  let e : U ≅ (SSet.Truncated.cosk n).obj ((SSet.truncation n).obj U) := U.isoCoskOfIsCoskeletal n
  have hhcosk : ept ≫ hcosk = g ≫ e.hom := by
    -- Move the endpoint equation through the inverse hom-set equivalence of `coskAdj n`.
    calc
      ept ≫ hcosk =
          ((coskAdj n).homEquiv V ((SSet.truncation n).obj U)).symm
            ((SSet.truncation n).map ept ≫ ht) := by
              symm
              simpa [hcosk, ht] using
                (coskAdj n).homEquiv_naturality_left_symm ept ht
      _ = ((coskAdj n).homEquiv V ((SSet.truncation n).obj U)).symm
            ((SSet.truncation n).map g) := by
              rw [hept]
      _ = g ≫ e.hom := by
            simpa [e] using coskAdj_symm_truncation_map
              (V := V) (U := U) (n := n) g hU
  -- Postcompose the equality in the coskeleton with the inverse comparison isomorphism.
  calc
    ept ≫ liftedCylinderMap (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow hU =
        (ept ≫ hcosk) ≫ e.inv := by
          simp [liftedCylinderMap, hcosk, e, Category.assoc]
    _ = (g ≫ e.hom) ≫ e.inv := by rw [hhcosk]
    _ = g := by simp [Category.assoc]

/-- Helper for Lemma 14.32.2: the lifted cylinder map restricts to `f₀` along the `0`-endpoint. -/
private theorem liftedCylinderMap_zero_endpoint
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌))
    (hU : U.IsCoskeletal n) :
    ι₀ ≫ liftedCylinderMap (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow hU = f₀ := by
  -- Apply the generic `coskAdj` endpoint transport to the already verified truncated endpoint.
  refine liftedCylinderMap_endpoint_via_coskAdj
    (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) (n := n) hbelow hU ι₀ f₀ ?_
  simpa using truncatedCylinderHomotopy_zero_endpoint
    (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow

/-- Helper for Lemma 14.32.2: the lifted cylinder map restricts to `f₁` along the `1`-endpoint. -/
private theorem liftedCylinderMap_one_endpoint
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌))
    (hU : U.IsCoskeletal n) :
    ι₁ ≫ liftedCylinderMap (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow hU = f₁ := by
  -- Apply the generic `coskAdj` endpoint transport to the already verified truncated endpoint.
  refine liftedCylinderMap_endpoint_via_coskAdj
    (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) (n := n) hbelow hU ι₁ f₁ ?_
  simpa using truncatedCylinderHomotopy_one_endpoint
    (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow

/-- Helper for Lemma 14.32.2: the relative condition for the bottom subcomplex is vacuous, so
the lifted cylinder map automatically satisfies it. -/
private theorem liftedCylinderMap_bot_relative
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌))
    (hU : U.IsCoskeletal n) :
    (⊥ : V.Subcomplex).ι ▷ Δ[1] ≫
        liftedCylinderMap (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow hU =
      fst (⊥ : V.Subcomplex).toSSet Δ[1] ≫
        SSet.Subcomplex.isInitialBot.to (⊥ : V.Subcomplex).toSSet ≫
        (⊥ : U.Subcomplex).ι := by
  -- There are no simplices in the bottom subcomplex, so extensionality closes the goal.
  ext Δ z
  exact False.elim z.1.2

/-- Lemma 14.32.2: if two maps of simplicial sets `f₀, f₁ : V ⟶ U` agree in all degrees
strictly below `n`, and both `U` and `V` are `n`-coskeletal (equivalently, their canonical maps
to the `n`-coskeleton are isomorphisms), then there exists a simplicial-set homotopy from `f₀`
to `f₁`.
The combinatorial simplicial-object homotopy is the derived bridge
`SSet.Homotopy.toSimplicialObjectHomotopy`. -/
theorem homotopy_of_eq_below_of_coskeletal :
    Nonempty (SSet.Homotopy f₀ f₁) := by
  -- The source-faithful route is the second proof from Stacks: package the degreewise truncated
  -- cylinder map, lift it through `coskAdj n`, and read off the two endpoint identities.
  refine ⟨{ h := liftedCylinderMap (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow hU
          , h₀ := liftedCylinderMap_zero_endpoint
            (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow hU
          , h₁ := liftedCylinderMap_one_endpoint
            (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow hU
          , rel := liftedCylinderMap_bot_relative
            (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow hU }⟩

-- Proof sketch: apply the source-facing existence theorem above and convert the resulting
-- simplicial-set homotopy through `SSet.Homotopy.toSimplicialObjectHomotopy`, then into the
-- chapter's canonical zigzag relation via `SimplicialObject.Homotopic.of_homotopy`.
/-- Under the hypotheses of `homotopy_of_eq_below_of_coskeletal`, the two maps are homotopic in
the Chapter 14 zigzag sense. -/
theorem homotopic_of_eq_below_of_coskeletal : Homotopic f₀ f₁ := by
  rcases homotopy_of_eq_below_of_coskeletal with ⟨H⟩
  exact Homotopic.of_homotopy H.toSimplicialObjectHomotopy
