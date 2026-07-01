import Mathlib
import stacks_project.Chap14.Definition_14_26_1

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
      have hθid : θ = 𝟙 _ := by
        ext i
        fin_cases i
        rfl
      have hx' :
          SSet.stdSimplex.asOrderHom (((Δ[1] : SSet).map θ.op) x.2) 0 =
            SSet.stdSimplex.asOrderHom x.2 0 := by
        simpa [hθid]
      exact hx (hx'.symm.trans hθx)
  | succ m =>
      have hx0 : SSet.stdSimplex.asOrderHom x.2 0 = (0 : Fin 2) := by
        fin_cases h0 : SSet.stdSimplex.asOrderHom x.2 0
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
  let θ : Δ₁.1 ⟶ Δ₂.1 := φ
  -- Split first by whether the target truncated degree is the top degree `n`.
  by_cases hk : Δ₁.1.len = n
  · by_cases hl : Δ₂.1.len = n
    · obtain rfl : Δ₁.1 = ⦋n⦌ := by simpa [hk] using Δ₁.1.mk_len
      obtain rfl : Δ₂.1 = ⦋n⦌ := by simpa [hl] using Δ₂.1.mk_len
      -- In top degree, the only real work is the mixed branch where precomposition creates the
      -- constant `1` simplex.
      by_cases hx : SSet.stdSimplex.asOrderHom x.2 0 = (1 : Fin 2)
      · have hmap :
            SSet.stdSimplex.asOrderHom (((Δ[1] : SSet).map θ.op) x.2) 0 = (1 : Fin 2) := by
          simpa using deltaOne_map_zero_eq_one_of_zero_eq_one θ hx
        simp [truncatedCylinderHomotopyComponent, hk, hl, hx, hmap]
        simpa using congrFun (f₁.naturality θ.op) x.1
      · by_cases hmap :
            SSet.stdSimplex.asOrderHom (((Δ[1] : SSet).map θ.op) x.2) 0 = (1 : Fin 2)
        · simp [truncatedCylinderHomotopyComponent, hk, hl, hx, hmap]
          exact truncatedCylinderHomotopyComponent_top_mixed_naturality
            (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow θ x hx hmap
        · simp [truncatedCylinderHomotopyComponent, hk, hl, hx, hmap]
          simpa using congrFun (f₀.naturality θ.op) x.1
    · have hl_lt : Δ₂.1.len < n := lt_of_le_of_ne Δ₂.2 hl
      by_cases hmap :
          SSet.stdSimplex.asOrderHom (((Δ[1] : SSet).map θ.op) x.2) 0 = (1 : Fin 2)
      · -- The target degree is still `n`, but the source degree is lower, so `f₀ = f₁` already
        -- holds on the source simplex.
        simp [truncatedCylinderHomotopyComponent, hk, hl, hmap]
        have hsrc : f₀.app (op Δ₂.1) x.1 = f₁.app (op Δ₂.1) x.1 := by
          exact congrFun (hbelow Δ₂.1.len hl_lt) x.1
        calc
          f₁.app (op Δ₁.1) (((SSet.truncation n).obj (V ⊗ Δ[1])).map φ.op x).1 =
              U.map θ.op (f₁.app (op Δ₂.1) x.1) := by
                simpa using congrFun (f₁.naturality θ.op) x.1
          _ = U.map θ.op (f₀.app (op Δ₂.1) x.1) := by rw [hsrc.symm]
      · simp [truncatedCylinderHomotopyComponent, hk, hl, hmap]
        simpa using congrFun (f₀.naturality θ.op) x.1
  · have hk_lt : Δ₁.1.len < n := lt_of_le_of_ne Δ₁.2 hk
    by_cases hl : Δ₂.1.len = n
    · obtain rfl : Δ₂.1 = ⦋n⦌ := by simpa [hl] using Δ₂.1.mk_len
      by_cases hx : SSet.stdSimplex.asOrderHom x.2 0 = (1 : Fin 2)
      · have hmap :
            SSet.stdSimplex.asOrderHom
                (((SSet.truncation n).obj (V ⊗ Δ[1])).map φ.op x).2 0 =
              (1 : Fin 2) := by
          simpa using deltaOne_map_zero_eq_one_of_zero_eq_one θ hx
        simp [truncatedCylinderHomotopyComponent, hk, hl, hx, hmap]
        have htarget :
            f₀.app (op Δ₁.1)
                (((SSet.truncation n).obj (V ⊗ Δ[1])).map φ.op x).1 =
              f₁.app (op Δ₁.1)
                (((SSet.truncation n).obj (V ⊗ Δ[1])).map φ.op x).1 := by
          exact congrFun (hbelow Δ₁.1.len hk_lt)
            ((((SSet.truncation n).obj (V ⊗ Δ[1])).map φ.op x).1)
        calc
          f₀.app (op Δ₁.1) (((SSet.truncation n).obj (V ⊗ Δ[1])).map φ.op x).1 =
              f₁.app (op Δ₁.1) (((SSet.truncation n).obj (V ⊗ Δ[1])).map φ.op x).1 := htarget
          _ = U.map θ.op (f₁.app (op ⦋n⦌) x.1) := by
                simpa using congrFun (f₁.naturality θ.op) x.1
      · simp [truncatedCylinderHomotopyComponent, hk, hl, hx]
        simpa using congrFun (f₀.naturality θ.op) x.1
    · simp [truncatedCylinderHomotopyComponent, hk, hl]
      simpa using congrFun (f₀.naturality θ.op) x.1

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
    (f₀ := f₀) (f₁ := f₁) (V := V) (hbelow := hbelow) Δ.unop.2 v

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
    (f₀ := f₀) (f₁ := f₁) (V := V) (hbelow := hbelow) Δ.unop.2 v

/-- Helper for Lemma 14.32.2: the truncated cylinder morphism lifts uniquely to a map into the
coskeleton of `U`. -/
private noncomputable def truncatedCylinderHomotopyLiftToCosk
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌)) :
    V ⊗ Δ[1] ⟶ (SSet.cosk n).obj ((SSet.truncation n).obj U) :=
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

/-- Helper for Lemma 14.32.2: the lifted cylinder map restricts to `f₀` along the `0`-endpoint. -/
private theorem liftedCylinderMap_zero_endpoint
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌))
    (hU : U.IsCoskeletal n) :
    ι₀ ≫ liftedCylinderMap (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow hU = f₀ := by
  letI : U.IsCoskeletal n := hU
  let ht :=
    truncatedCylinderHomotopy (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow
  let hcosk :=
    truncatedCylinderHomotopyLiftToCosk (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow
  let e : U ≅ (SSet.cosk n).obj ((SSet.truncation n).obj U) := U.isoCoskOfIsCoskeletal n
  have hhcosk : ι₀ ≫ hcosk = f₀ ≫ e.hom := by
    -- Compare both maps after applying the `coskAdj n` hom-set equivalence.
    apply ((coskAdj n).homEquiv V ((SSet.truncation n).obj U)).injective
    calc
      (coskAdj n).homEquiv V ((SSet.truncation n).obj U) (ι₀ ≫ hcosk) =
          (SSet.truncation n).map ι₀ ≫ ht := by
            symm
            simpa [hcosk, ht] using
              (coskAdj n).homEquiv_naturality_left ι₀ ht
      _ = (SSet.truncation n).map f₀ := by
            simpa [ht] using
              truncatedCylinderHomotopy_zero_endpoint
                (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow
      _ = (coskAdj n).homEquiv V ((SSet.truncation n).obj U) (f₀ ≫ e.hom) := by
            calc
              (SSet.truncation n).map f₀ =
                  (coskAdj n).homEquiv V ((SSet.truncation n).obj U)
                    ((SSet.truncation n).map f₀) := by
                      simp
              _ = f₀ ≫ e.hom := by
                    calc
                      (coskAdj n).homEquiv V ((SSet.truncation n).obj U)
                          ((SSet.truncation n).map f₀) =
                            (coskAdj n).unit.app V ≫
                              (SSet.cosk n).map ((SSet.truncation n).map f₀) := by
                                simpa using
                                  (Adjunction.homEquiv_unit
                                    (adj := coskAdj n) (f := (SSet.truncation n).map f₀))
                      _ = f₀ ≫ (coskAdj n).unit.app U := by
                            simpa using ((coskAdj n).unit.naturality f₀).symm
                      _ = f₀ ≫ e.hom := by rfl
  -- Postcompose the equality in the coskeleton with the inverse comparison isomorphism.
  calc
    ι₀ ≫ liftedCylinderMap (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow hU =
        (ι₀ ≫ hcosk) ≫ e.inv := by
          simp [liftedCylinderMap, hcosk, e, Category.assoc]
    _ = (f₀ ≫ e.hom) ≫ e.inv := by rw [hhcosk]
    _ = f₀ := by simp [Category.assoc]

/-- Helper for Lemma 14.32.2: the lifted cylinder map restricts to `f₁` along the `1`-endpoint. -/
private theorem liftedCylinderMap_one_endpoint
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌))
    (hU : U.IsCoskeletal n) :
    ι₁ ≫ liftedCylinderMap (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow hU = f₁ := by
  letI : U.IsCoskeletal n := hU
  let ht :=
    truncatedCylinderHomotopy (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow
  let hcosk :=
    truncatedCylinderHomotopyLiftToCosk (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow
  let e : U ≅ (SSet.cosk n).obj ((SSet.truncation n).obj U) := U.isoCoskOfIsCoskeletal n
  have hhcosk : ι₁ ≫ hcosk = f₁ ≫ e.hom := by
    -- Compare both maps after applying the `coskAdj n` hom-set equivalence.
    apply ((coskAdj n).homEquiv V ((SSet.truncation n).obj U)).injective
    calc
      (coskAdj n).homEquiv V ((SSet.truncation n).obj U) (ι₁ ≫ hcosk) =
          (SSet.truncation n).map ι₁ ≫ ht := by
            symm
            simpa [hcosk, ht] using
              (coskAdj n).homEquiv_naturality_left ι₁ ht
      _ = (SSet.truncation n).map f₁ := by
            simpa [ht] using
              truncatedCylinderHomotopy_one_endpoint
                (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow
      _ = (coskAdj n).homEquiv V ((SSet.truncation n).obj U) (f₁ ≫ e.hom) := by
            calc
              (SSet.truncation n).map f₁ =
                  (coskAdj n).homEquiv V ((SSet.truncation n).obj U)
                    ((SSet.truncation n).map f₁) := by
                      simp
              _ = f₁ ≫ e.hom := by
                    calc
                      (coskAdj n).homEquiv V ((SSet.truncation n).obj U)
                          ((SSet.truncation n).map f₁) =
                            (coskAdj n).unit.app V ≫
                              (SSet.cosk n).map ((SSet.truncation n).map f₁) := by
                                simpa using
                                  (Adjunction.homEquiv_unit
                                    (adj := coskAdj n) (f := (SSet.truncation n).map f₁))
                      _ = f₁ ≫ (coskAdj n).unit.app U := by
                            simpa using ((coskAdj n).unit.naturality f₁).symm
                      _ = f₁ ≫ e.hom := by rfl
  -- Postcompose the equality in the coskeleton with the inverse comparison isomorphism.
  calc
    ι₁ ≫ liftedCylinderMap (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow hU =
        (ι₁ ≫ hcosk) ≫ e.inv := by
          simp [liftedCylinderMap, hcosk, e, Category.assoc]
    _ = (f₁ ≫ e.hom) ≫ e.inv := by rw [hhcosk]
    _ = f₁ := by simp [Category.assoc]

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
          h₀ := liftedCylinderMap_zero_endpoint
            (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow hU
          h₁ := liftedCylinderMap_one_endpoint
            (f₀ := f₀) (f₁ := f₁) (V := V) (U := U) hbelow hU }⟩

-- Proof sketch: apply the source-facing existence theorem above and convert the resulting
-- simplicial-set homotopy through `SSet.Homotopy.toSimplicialObjectHomotopy`, then into the
-- chapter's canonical zigzag relation via `SimplicialObject.Homotopic.of_homotopy`.
/-- Under the hypotheses of `homotopy_of_eq_below_of_coskeletal`, the two maps are homotopic in
the Chapter 14 zigzag sense. -/
theorem homotopic_of_eq_below_of_coskeletal : Homotopic f₀ f₁ := by
  rcases homotopy_of_eq_below_of_coskeletal with ⟨H⟩
  exact Homotopic.of_homotopy H.toSimplicialObjectHomotopy
