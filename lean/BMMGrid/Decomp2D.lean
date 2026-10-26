import BMMGrid.MinDegreeAndDyadicSift

/-!
# Sections 4.3 & 4.4: Capped and Uncapped 2D Decompositions (`BMMGrid/Decomp2D.lean`)

This module formalizes Sections 4.3 and 4.4 of `paper.tex`:
1. **Algorithm 4 (`FindRect` and `Decompose2D`, §4.3)** (`cappedGoodRect`, `cappedADecomposition`,
   `aDecomposition`, and their concrete and `CostM`-tracked counterparts).
2. **Lemma 4.3 (`\label{lem:find-rect}`), Theorem 4.4 (`\label{thm:2d-decomp}`), Corollary 4.5
   (`\label{cor:uncapped-2d}`), and Lemma 4.6 (`\label{lem:riemann}`, §4.3)**:
   - Single-piece rectangle search and shrinkage `\eqref{eq:capped-goodrect-shrinkage}`
     (`goodRectLoop_spec`, `cappedGoodRect_spec`).
   - Capped 2D decomposition structural, shrinkage, piece-count ($S_\ell \le 47$ on `"regular"`
     pieces and $L_s \le 2^D M_{\text{rect2D}}(\varepsilon_2, D) 2^{s D}$), mass-conservation,
     and `CostM` time bounds (`thm_2d_decomp`, `thm_2d_decomp_concrete`).
   - Uncapped 2D decomposition across all $D \ge 2$ (`thm_2d_decomp_uncapped`,
     `thm_2d_decomp_uncapped_concrete`).
   - Riemann-sum telescoping bound `\eqref{eq:riemann-telescoping}` (`rpow_sub_le_of_concave`,
     `riemann_density_weighted_step`, `thm_2d_decomp_riemann_telescoping`).
3. **Proposition 4.7 (`\label{prop:tightness}`, §4.4)**:
   `rem_obstacles_single_step_tightness` and `rem_obstacles_multiblock_sift_tightness`,
   establishing the single-step density-decrement and multi-block $2^{-\lfloor d^2/2 \rfloor}$
   sifting tightness bounds.
-/

namespace BMMGrid

open scoped BigOperators

variable {α β : Type*}

/-!
## Sub-Rectangle Restriction and Zeroing-Out Operations (§4.3 of `paper.tex`)
-/

section SubrectOps

/-- Restrict a matrix $A : \alpha \to \beta \to \mathbb{R}$ to a sub-rectangle $X' \times Y'$,
zeroing out all entries outside $X' \times Y'$. -/
noncomputable def restrictSubrect (A : α → β → ℝ) (X' : Finset α) (Y' : Finset β) :
    α → β → ℝ :=
  letI := Classical.dec
  fun x y => if x ∈ X' ∧ y ∈ Y' then A x y else 0

/-- `restrictSubrect A X' Y'` is already zero-extended outside `X' × Y'`. -/
theorem restrictSubrect_eq_submatZeroExt [DecidableEq α] [DecidableEq β]
    (A : α → β → ℝ) (X' : Finset α) (Y' : Finset β) (x : α) (y : β) :
    restrictSubrect A X' Y' x y = submatZeroExt X' Y' (restrictSubrect A X' Y') x y := by
  dsimp [restrictSubrect, submatZeroExt]
  split_ifs <;> rfl

/-- Zero out all entries of $A : \alpha \to \beta \to \mathbb{R}$ inside a sub-rectangle
$X' \times Y'$ ($A_{\text{rem}}[X', Y'] \leftarrow 0$, §4.3 of `paper.tex`). -/
noncomputable def zeroOutSubrect (A : α → β → ℝ) (X' : Finset α) (Y' : Finset β) :
    α → β → ℝ :=
  letI := Classical.dec
  fun x y => if x ∈ X' ∧ y ∈ Y' then 0 else A x y

/-- Pointwise partition of unity: $A = A|_{X' \times Y'} + (A \setminus (X' \times Y'))$. -/
theorem restrictSubrect_add_zeroOutSubrect (A : α → β → ℝ) (X' : Finset α) (Y' : Finset β)
    (x : α) (y : β) :
    restrictSubrect A X' Y' x y + zeroOutSubrect A X' Y' x y = A x y := by
  classical
  unfold restrictSubrect zeroOutSubrect
  by_cases h : x ∈ X' ∧ y ∈ Y' <;> simp [h]

/-- On $X' \times Y'$, `restrictSubrect A X' Y'` agrees with $A$. -/
theorem restrictSubrect_eq_on {A : α → β → ℝ} {X' : Finset α} {Y' : Finset β}
    {x : α} {y : β} (hx : x ∈ X') (hy : y ∈ Y') :
    restrictSubrect A X' Y' x y = A x y := by
  classical
  unfold restrictSubrect
  exact if_pos ⟨hx, hy⟩

/-- On $X' \times Y'$, `matDensity X' Y' (restrictSubrect A X' Y') = matDensity X' Y' A`. -/
theorem matDensity_restrictSubrect_eq (A : α → β → ℝ) (X' : Finset α) (Y' : Finset β) :
    matDensity X' Y' (restrictSubrect A X' Y') = matDensity X' Y' A := by
  unfold matDensity rowDeg expectSet
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  exact restrictSubrect_eq_on hx hy

/-- Zeroing out a sub-rectangle preserves `IsBinaryMatrix`. -/
theorem IsBinaryMatrix.zeroOut {X X' : Finset α} {Y Y' : Finset β} {A : α → β → ℝ}
    (hA : IsBinaryMatrix X Y A) :
    IsBinaryMatrix X Y (zeroOutSubrect A X' Y') := by
  classical
  intro x hx y hy
  unfold zeroOutSubrect
  by_cases h : x ∈ X' ∧ y ∈ Y'
  · simp [h]
  · simp [h, hA x hx y hy]

/-- Restricting to a sub-rectangle preserves `IsBinaryMatrix`. -/
theorem IsBinaryMatrix.restrict {X X' : Finset α} {Y Y' : Finset β} {A : α → β → ℝ}
    (hA : IsBinaryMatrix X Y A) :
    IsBinaryMatrix X Y (restrictSubrect A X' Y') := by
  classical
  intro x hx y hy
  unfold restrictSubrect
  by_cases h : x ∈ X' ∧ y ∈ Y'
  · simp [h, hA x hx y hy]
  · simp [h]

/-- Exact sum decomposition over $X \times Y$ when splitting off $X' \times Y' \subseteq X \times Y$. -/
lemma sum_zeroOutSubrect_eq {X X' : Finset α} {Y Y' : Finset β} (A : α → β → ℝ)
    (hX' : X' ⊆ X) (hY' : Y' ⊆ Y) :
    (∑ x ∈ X, ∑ y ∈ Y, zeroOutSubrect A X' Y' x y) +
      (∑ x ∈ X', ∑ y ∈ Y', A x y) =
      ∑ x ∈ X, ∑ y ∈ Y, A x y := by
  classical
  have h_restrict : ∑ x ∈ X', ∑ y ∈ Y', A x y =
      ∑ x ∈ X, ∑ y ∈ Y, restrictSubrect A X' Y' x y := by
    have h1 : ∑ x ∈ X, ∑ y ∈ Y, restrictSubrect A X' Y' x y =
        ∑ x ∈ X, if x ∈ X' then (∑ y ∈ Y', A x y) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx' : x ∈ X'
      · rw [if_pos hx']
        have hY_split : ∑ y ∈ Y, restrictSubrect A X' Y' x y =
            ∑ y ∈ Y, if y ∈ Y' then A x y else 0 := by
          apply Finset.sum_congr rfl
          intro y _
          unfold restrictSubrect
          simp [hx']
        rw [hY_split, Finset.sum_ite, Finset.sum_const_zero, add_zero]
        have hfilterY : Y.filter (fun y => y ∈ Y') = Y' :=
          Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr hY')
        rw [hfilterY]
      · rw [if_neg hx']
        apply Finset.sum_eq_zero
        intro y _
        unfold restrictSubrect
        simp [hx']
    rw [h1, Finset.sum_ite, Finset.sum_const_zero, add_zero]
    have hfilterX : X.filter (fun x => x ∈ X') = X' :=
      Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr hX')
    rw [hfilterX]
  rw [h_restrict, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  rw [add_comm]
  exact restrictSubrect_add_zeroOutSubrect A X' Y' x y

/-- **Exact Density-Decrement Identity (§4.3 of `paper.tex`)**:
For any sub-rectangle $X' \times Y' \subseteq X \times Y$ with $X, Y$ non-empty,
$$\mathbb{E}_{X \times Y}[\text{zeroOutSubrect } A\, X'\, Y'] =
  \mathbb{E}_{X \times Y}[A] - \frac{|X'|}{|X|} \frac{|Y'|}{|Y|} \mathbb{E}_{X' \times Y'}[A].$$ -/
theorem matDensity_zeroOutSubrect_eq {X X' : Finset α} {Y Y' : Finset β} (A : α → β → ℝ)
    (hX : X.Nonempty) (hY : Y.Nonempty) (hX' : X' ⊆ X) (hY' : Y' ⊆ Y) :
    matDensity X Y (zeroOutSubrect A X' Y') =
      matDensity X Y A -
        ((X'.card : ℝ) / (X.card : ℝ)) * ((Y'.card : ℝ) / (Y.card : ℝ)) *
          matDensity X' Y' A := by
  have hX_pos : (0 : ℝ) < (X.card : ℝ) := Nat.cast_pos.mpr hX.card_pos
  have hY_pos : (0 : ℝ) < (Y.card : ℝ) := Nat.cast_pos.mpr hY.card_pos
  have hsum := sum_zeroOutSubrect_eq A hX' hY'
  have hdens_eq : ∀ (U : Finset α) (V : Finset β) (M : α → β → ℝ),
      (U.card : ℝ) * ((V.card : ℝ) * matDensity U V M) = ∑ x ∈ U, ∑ y ∈ V, M x y := by
    intro U V M
    by_cases hU0 : U.card = 0
    · have hUe : U = ∅ := Finset.card_eq_zero.mp hU0
      simp [hUe]
    · by_cases hV0 : V.card = 0
      · have hVe : V = ∅ := Finset.card_eq_zero.mp hV0
        simp [hVe]
      · have hU_ne : (U.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hU0
        have hV_ne : (V.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hV0
        unfold matDensity rowDeg expectSet
        dsimp only
        rw [← Finset.sum_div]
        field_simp [hU_ne, hV_ne]
  have h1 := hdens_eq X Y (zeroOutSubrect A X' Y')
  have h2 := hdens_eq X' Y' A
  have h3 := hdens_eq X Y A
  have hcomb : (X.card : ℝ) * ((Y.card : ℝ) * matDensity X Y (zeroOutSubrect A X' Y')) +
      (X'.card : ℝ) * ((Y'.card : ℝ) * matDensity X' Y' A) =
      (X.card : ℝ) * ((Y.card : ℝ) * matDensity X Y A) := by
    linarith [h1, h2, h3, hsum]
  have hX_ne : (X.card : ℝ) ≠ 0 := hX_pos.ne'
  have hY_ne : (Y.card : ℝ) ≠ 0 := hY_pos.ne'
  apply mul_left_cancel₀ hX_ne
  apply mul_left_cancel₀ hY_ne
  calc
    (Y.card : ℝ) * ((X.card : ℝ) * matDensity X Y (zeroOutSubrect A X' Y')) =
        (X.card : ℝ) * ((Y.card : ℝ) * matDensity X Y A) -
          (X'.card : ℝ) * ((Y'.card : ℝ) * matDensity X' Y' A) := by linarith [hcomb]
    _ = (Y.card : ℝ) * ((X.card : ℝ) *
        (matDensity X Y A -
          ((X'.card : ℝ) / (X.card : ℝ)) * ((Y'.card : ℝ) / (Y.card : ℝ)) *
            matDensity X' Y' A)) := by
      field_simp [hX_ne, hY_ne]

end SubrectOps

/-!
## 2D Minimum-Degree Pruning and Single-Step `FindRect` Transition (§4.3 of `paper.tex`)
-/

section GoodRectDefs

/-- Iteration fuel for `CappedGoodRect` (`rRect2DFuel`, §4.3 of `paper.tex`):
$84 \cdot \lceil 1 / \varepsilon_2 \rceil \le 97 / \varepsilon_2$ (for $0 < \varepsilon_2 \le 1 / 160$), guaranteeing that
$(1 + \varepsilon_2 / 2)^{\text{rRect2DFuel}(\varepsilon_2)} \ge (3/2)^{84} > 2^{48}$
so the loop never runs out of fuel inside the active density window $[\alpha_{\text{low}}, \alpha_{\text{cap}})$. -/
noncomputable def rRect2DFuel (ε₂ : ℝ) : ℕ :=
  84 * Nat.ceil (1 / ε₂)

/-- Iteration fuel for uncapped `FindRect` (`rUncappedRect2DFuel`, §4.3 of `paper.tex`):
$2(D + 1) \cdot \lceil 1 / \varepsilon_2 \rceil + 1$, guaranteeing that
$(1 + \varepsilon_2 / 2)^{\text{rUncappedRect2DFuel}(\varepsilon_2, D)} \ge 2^{D+1}$
so the loop never runs out of fuel when $\mathbb{E}[A] \ge 2^{-D}$. -/
noncomputable def rUncappedRect2DFuel (ε₂ : ℝ) (D : ℕ) : ℕ :=
  2 * (D + 1) * Nat.ceil (1 / ε₂) + 1

/-- Single iteration of the `FindRect` inner loop (Algorithm 4, §4.3 of `paper.tex`):
Given current $(X', Y', \bar{s})$, density cap $\alpha_{\text{cap}}$, and an `ApproxGridNorm` oracle
`oracleV : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → (α → ℝ)`:
1. If $\mathbb{E}[A[X', Y']] \ge \alpha_{\text{cap}}$, returns `Sum.inr (X', Y', RectTag.aBoosted, s_bar)`.
2. Calls single-sided row `minDegree X' Y' A ε₂ (1 / 2)`.
3. If `case_tag = 2` (or $\mathbb{E}[A[X_1, Y']] \ge (1 + \varepsilon_2 / 2)\mathbb{E}[A[X', Y']]$), returns `Sum.inl (X₁, Y', s_bar, 0)`.
4. If $\mathbb{E}[A[X_1, Y']] \ge \alpha_{\text{cap}}$, returns `Sum.inr (X₁, Y', RectTag.aBoosted, s_bar)`.
5. Runs `dyadicSift X₁ Y' A ε₂ D V`: either returns `Sum.inr (X₁, Y', RectTag.regular, s_bar)`
   when certified $(\varepsilon_2, 2, D)$-regular, or returns
   `Sum.inl (X_next, Y_next, s_bar + s, s)` accumulating scale $S_\ell = \sum_t s_t$ additively. -/
noncomputable def goodRectStep [DecidableEq α] [DecidableEq β]
    (X' : Finset α) (Y' : Finset β) (A : α → β → ℝ) (ε₂ : ℝ) (D : ℕ) (α_cap : ℝ)
    (oracleV : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → (α → ℝ))
    (s_bar : ℕ) :
    (Finset α × Finset β × ℕ × ℕ) ⊕ (Finset α × Finset β × RectTag × ℕ) :=
  letI : Decidable (matDensity X' Y' A ≥ α_cap) := Classical.propDecidable _
  if matDensity X' Y' A ≥ α_cap then
    Sum.inr (X', Y', RectTag.aBoosted, s_bar)
  else
    let resMin := minDegree X' Y' A ε₂ (1 / 2)
    let X₁ := resMin.1
    letI : Decidable (resMin.2 = 2 ∨ matDensity X₁ Y' A ≥ (1 + ε₂ / 2) * matDensity X' Y' A) :=
      Classical.propDecidable _
    letI : Decidable (matDensity X₁ Y' A ≥ α_cap) := Classical.propDecidable _
    if resMin.2 = 2 ∨ matDensity X₁ Y' A ≥ (1 + ε₂ / 2) * matDensity X' Y' A then
      Sum.inl (X₁, Y', s_bar, 0)
    else if matDensity X₁ Y' A ≥ α_cap then
      Sum.inr (X₁, Y', RectTag.aBoosted, s_bar)
    else
      let δ := (1 + ε₂ / 2) * matDensity X₁ Y' A
      let α_grid := ε₂ * δ ^ 3 / 32
      let V := oracleV X₁ Y' A α_grid D
      let resSift := dyadicSift X₁ Y' A ε₂ D V
      if resSift.1 = "regular" then
        Sum.inr (X₁, Y', RectTag.regular, s_bar)
      else
        let s := resSift.2.2.2
        Sum.inl (resSift.2.1, resSift.2.2.1, s_bar + s, s)

/-- Cost-tracked single iteration `goodRectStepTracked` in `CostM`. -/
noncomputable def goodRectStepTracked [DecidableEq α] [DecidableEq β]
    (X' : Finset α) (Y' : Finset β) (A : α → β → ℝ) (ε₂ : ℝ) (D : ℕ) (α_cap : ℝ)
    (oracleVTracked : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → CostM (α → ℝ))
    (s_bar : ℕ) :
    CostM ((Finset α × Finset β × ℕ × ℕ) ⊕ (Finset α × Finset β × RectTag × ℕ)) :=
  letI : Decidable (matDensity X' Y' A ≥ α_cap) := Classical.propDecidable _
  if matDensity X' Y' A ≥ α_cap then
    scanMatrixTracked X' Y' (Sum.inr (X', Y', RectTag.aBoosted, s_bar))
  else
    CostM.bind (minDegreeTracked X' Y' A ε₂ (1 / 2)) (fun resMin =>
      let X₁ := resMin.1
      letI : Decidable (resMin.2 = 2 ∨ matDensity X₁ Y' A ≥ (1 + ε₂ / 2) * matDensity X' Y' A) :=
        Classical.propDecidable _
      letI : Decidable (matDensity X₁ Y' A ≥ α_cap) := Classical.propDecidable _
      if resMin.2 = 2 ∨ matDensity X₁ Y' A ≥ (1 + ε₂ / 2) * matDensity X' Y' A then
        retTracked (Sum.inl (X₁, Y', s_bar, 0))
      else if matDensity X₁ Y' A ≥ α_cap then
        retTracked (Sum.inr (X₁, Y', RectTag.aBoosted, s_bar))
      else
        let δ := (1 + ε₂ / 2) * matDensity X₁ Y' A
        let α_grid := ε₂ * δ ^ 3 / 32
        CostM.bind (dyadicSiftTracked X₁ Y' A ε₂ D (oracleVTracked X₁ Y' A α_grid D)) (fun resSift =>
          if resSift.1 = "regular" then
            retTracked (Sum.inr (X₁, Y', RectTag.regular, s_bar))
          else
            let s := resSift.2.2.2
            retTracked (Sum.inl (resSift.2.1, resSift.2.2.1, s_bar + s, s))))

@[simp]
theorem goodRectStepTracked_fst [DecidableEq α] [DecidableEq β]
    (X' : Finset α) (Y' : Finset β) (A : α → β → ℝ) (ε₂ : ℝ) (D : ℕ) (α_cap : ℝ)
    (oracleVTracked : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → CostM (α → ℝ))
    (s_bar : ℕ) :
    (goodRectStepTracked X' Y' A ε₂ D α_cap oracleVTracked s_bar).1 =
      goodRectStep X' Y' A ε₂ D α_cap
        (fun U V M α_g d => (oracleVTracked U V M α_g d).1) s_bar := by
  unfold goodRectStepTracked goodRectStep
  by_cases hcap0 : matDensity X' Y' A ≥ α_cap
  · rw [if_pos hcap0, if_pos hcap0]; rfl
  · rw [if_neg hcap0, if_neg hcap0, CostM.bind_fst, minDegreeTracked_fst]
    dsimp only
    by_cases h1 : (minDegree X' Y' A ε₂ (1 / 2)).2 = 2 ∨
        matDensity (minDegree X' Y' A ε₂ (1 / 2)).1 Y' A ≥ (1 + ε₂ / 2) * matDensity X' Y' A
    · rw [if_pos h1, if_pos h1]; rfl
    · rw [if_neg h1, if_neg h1]
      by_cases hcap1 :
          matDensity (minDegree X' Y' A ε₂ (1 / 2)).1 Y' A ≥ α_cap
      · rw [if_pos hcap1, if_pos hcap1]; rfl
      · rw [if_neg hcap1, if_neg hcap1, CostM.bind_fst, dyadicSiftTracked_fst]
        split_ifs <;> rfl

/-- Bounded-iteration loop for `FindRect` (Algorithm 4, §4.3 of `paper.tex`):
Given remaining iteration budget `fuel`, current rectangle `(X', Y')`, running cumulative scale
`s_bar`, and step counter `steps_done`, returns `(X_out, Y_out, tag, s_bar_out, steps_used)`. -/
noncomputable def goodRectLoop [DecidableEq α] [DecidableEq β] :
    ℕ → Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → ℝ →
    (Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → (α → ℝ)) → ℕ → ℕ →
    Finset α × Finset β × RectTag × ℕ × ℕ
  | 0, X', Y', _A, _ε₂, _D, _α_cap, _oracleV, s_bar, steps_done =>
    (X', Y', RectTag.aBoosted, s_bar, steps_done)
  | fuel + 1, X', Y', A, ε₂, D, α_cap, oracleV, s_bar, steps_done =>
    match goodRectStep X' Y' A ε₂ D α_cap oracleV s_bar with
    | Sum.inr (X_out, Y_out, tag_out, s_final) =>
      (X_out, Y_out, tag_out, s_final, steps_done)
    | Sum.inl (X_next, Y_next, s_bar_next, _s_step) =>
      goodRectLoop fuel X_next Y_next A ε₂ D α_cap oracleV s_bar_next (steps_done + 1)

/-- Cost-tracked loop `goodRectLoopTracked` in `CostM`. -/
noncomputable def goodRectLoopTracked [DecidableEq α] [DecidableEq β] :
    ℕ → Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → ℝ →
    (Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → CostM (α → ℝ)) → ℕ → ℕ →
    CostM (Finset α × Finset β × RectTag × ℕ × ℕ)
  | 0, X', Y', _A, _ε₂, _D, _α_cap, _oracleV, s_bar, steps_done =>
    retTracked (X', Y', RectTag.aBoosted, s_bar, steps_done)
  | fuel + 1, X', Y', A, ε₂, D, α_cap, oracleVTracked, s_bar, steps_done =>
    CostM.bind (goodRectStepTracked X' Y' A ε₂ D α_cap oracleVTracked s_bar) (fun stepRes =>
      match stepRes with
      | Sum.inr (X_out, Y_out, tag_out, s_final) =>
        retTracked (X_out, Y_out, tag_out, s_final, steps_done)
      | Sum.inl (X_next, Y_next, s_bar_next, _s_step) =>
        goodRectLoopTracked fuel X_next Y_next A ε₂ D α_cap oracleVTracked s_bar_next (steps_done + 1))

@[simp]
theorem goodRectLoopTracked_fst [DecidableEq α] [DecidableEq β]
    (fuel : ℕ) (X' : Finset α) (Y' : Finset β) (A : α → β → ℝ) (ε₂ : ℝ) (D : ℕ) (α_cap : ℝ)
    (oracleVTracked : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → CostM (α → ℝ))
    (s_bar steps_done : ℕ) :
    (goodRectLoopTracked fuel X' Y' A ε₂ D α_cap oracleVTracked s_bar steps_done).1 =
      goodRectLoop fuel X' Y' A ε₂ D α_cap
        (fun U V M α_g d => (oracleVTracked U V M α_g d).1) s_bar steps_done := by
  induction fuel generalizing X' Y' s_bar steps_done with
  | zero => rfl
  | succ k ih =>
    unfold goodRectLoopTracked goodRectLoop
    rw [CostM.bind_fst, goodRectStepTracked_fst]
    cases goodRectStep X' Y' A ε₂ D α_cap (fun U V M α_g d => (oracleVTracked U V M α_g d).1) s_bar with
    | inr val => rfl
    | inl val => exact ih val.1 val.2.1 val.2.2.1 (steps_done + 1)

/-- **Algorithm 4 (`FindRect`, §4.3 of `paper.tex`)**:
Capped rectangle extraction with density cap $\alpha_{\text{cap}}$ and iteration budget `rRect2DFuel ε₂`:
halts with `RectTag.regular` (at $S_\ell \le 47$ when $0 < \varepsilon_2 \le 1/160$ and
$2^D(1+\varepsilon_2/2)\mathbb{E}[A] > 1$), `RectTag.aBoosted` at $\alpha_{\text{cap}}$, or on fuel exhaustion. -/
noncomputable def cappedGoodRect [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (A : α → β → ℝ) (ε₂ : ℝ) (D : ℕ) (α_cap : ℝ)
    (oracleV : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → (α → ℝ)) :
    Finset α × Finset β × RectTag × ℕ × ℕ :=
  goodRectLoop (rRect2DFuel ε₂) X Y A ε₂ D α_cap oracleV 0 0

/-- Cost-tracked Algorithm 4 (`FindRect`, `cappedGoodRectTracked`) in `CostM`. -/
noncomputable def cappedGoodRectTracked [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (A : α → β → ℝ) (ε₂ : ℝ) (D : ℕ) (α_cap : ℝ)
    (oracleVTracked : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → CostM (α → ℝ)) :
    CostM (Finset α × Finset β × RectTag × ℕ × ℕ) :=
  goodRectLoopTracked (rRect2DFuel ε₂) X Y A ε₂ D α_cap oracleVTracked 0 0

@[simp]
theorem cappedGoodRectTracked_fst [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (A : α → β → ℝ) (ε₂ : ℝ) (D : ℕ) (α_cap : ℝ)
    (oracleVTracked : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → CostM (α → ℝ)) :
    (cappedGoodRectTracked X Y A ε₂ D α_cap oracleVTracked).1 =
      cappedGoodRect X Y A ε₂ D α_cap (fun U V M α_g d => (oracleVTracked U V M α_g d).1) :=
  goodRectLoopTracked_fst (rRect2DFuel ε₂) X Y A ε₂ D α_cap oracleVTracked 0 0

/-- Outer decomposition loop for `Decompose2D` (Algorithm 4, §4.3 of `paper.tex`):
Iteratively extracts pieces via `goodRectLoop maxIter` with density cap `α_cap` while
$\mathbb{E}[A_{\text{rem}}] > \rho_2$ and zeroes out $A_{\text{rem}}[X_\ell, Y_\ell] \leftarrow 0$,
finally appending the residual piece `(X, Y, restrictSubrect A_rem X Y, RectTag.residual, 0)`. -/
noncomputable def aDecompositionLoop [DecidableEq α] [DecidableEq β] :
    ℕ → ℕ → Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → ℝ → ℝ →
    (Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → (α → ℝ)) →
    List (RectPiece α β) → List (RectPiece α β)
  | 0, _maxIter, X, Y, A_rem, _ε₂, _D, _ρ₂, _α_cap, _oracleV, acc =>
    acc.reverse ++ [⟨X, Y, restrictSubrect A_rem X Y, RectTag.residual, 0⟩]
  | fuel + 1, maxIter, X, Y, A_rem, ε₂, D, ρ₂, α_cap, oracleV, acc =>
    letI : Decidable (matDensity X Y A_rem ≤ ρ₂) := Classical.propDecidable _
    if matDensity X Y A_rem ≤ ρ₂ then
      acc.reverse ++ [⟨X, Y, restrictSubrect A_rem X Y, RectTag.residual, 0⟩]
    else
      let res := goodRectLoop maxIter X Y A_rem ε₂ D α_cap oracleV 0 0
      let X_l := res.1
      let Y_l := res.2.1
      let tag_l := res.2.2.1
      let s_l := res.2.2.2.1
      let piece_l : RectPiece α β := ⟨X_l, Y_l, restrictSubrect A_rem X_l Y_l, tag_l, s_l⟩
      let A_next := zeroOutSubrect A_rem X_l Y_l
      aDecompositionLoop fuel maxIter X Y A_next ε₂ D ρ₂ α_cap oracleV (piece_l :: acc)

/-- Cost-tracked outer decomposition loop in `CostM`. -/
noncomputable def aDecompositionLoopTracked [DecidableEq α] [DecidableEq β] :
    ℕ → ℕ → Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → ℝ → ℝ →
    (Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → CostM (α → ℝ)) →
    List (RectPiece α β) → CostM (List (RectPiece α β))
  | 0, _maxIter, X, Y, A_rem, _ε₂, _D, _ρ₂, _α_cap, _oracleV, acc =>
    scanMatrixTracked X Y (acc.reverse ++ [⟨X, Y, restrictSubrect A_rem X Y, RectTag.residual, 0⟩])
  | fuel + 1, maxIter, X, Y, A_rem, ε₂, D, ρ₂, α_cap, oracleVTracked, acc =>
    letI : Decidable (matDensity X Y A_rem ≤ ρ₂) := Classical.propDecidable _
    if matDensity X Y A_rem ≤ ρ₂ then
      scanMatrixTracked X Y (acc.reverse ++ [⟨X, Y, restrictSubrect A_rem X Y, RectTag.residual, 0⟩])
    else
      CostM.bind (goodRectLoopTracked maxIter X Y A_rem ε₂ D α_cap oracleVTracked 0 0) (fun res =>
        let X_l := res.1
        let Y_l := res.2.1
        let tag_l := res.2.2.1
        let s_l := res.2.2.2.1
        let piece_l : RectPiece α β := ⟨X_l, Y_l, restrictSubrect A_rem X_l Y_l, tag_l, s_l⟩
        let A_next := zeroOutSubrect A_rem X_l Y_l
        CostM.bind (scanMatrixTracked X Y ()) (fun _ =>
          aDecompositionLoopTracked fuel maxIter X Y A_next ε₂ D ρ₂ α_cap oracleVTracked (piece_l :: acc)))

@[simp]
theorem aDecompositionLoopTracked_fst [DecidableEq α] [DecidableEq β]
    (fuel maxIter : ℕ) (X : Finset α) (Y : Finset β) (A_rem : α → β → ℝ)
    (ε₂ : ℝ) (D : ℕ) (ρ₂ α_cap : ℝ)
    (oracleVTracked : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → CostM (α → ℝ))
    (acc : List (RectPiece α β)) :
    (aDecompositionLoopTracked fuel maxIter X Y A_rem ε₂ D ρ₂ α_cap oracleVTracked acc).1 =
      aDecompositionLoop fuel maxIter X Y A_rem ε₂ D ρ₂ α_cap
        (fun U V M α_g d => (oracleVTracked U V M α_g d).1) acc := by
  induction fuel generalizing A_rem acc with
  | zero =>
    unfold aDecompositionLoopTracked aDecompositionLoop
    rfl
  | succ k ih =>
    unfold aDecompositionLoopTracked aDecompositionLoop
    dsimp only
    split_ifs with hlt
    · rfl
    · rw [CostM.bind_fst, goodRectLoopTracked_fst, CostM.bind_fst]
      exact ih _ _

/-- **Uncapped `Decompose2D` (`aDecomposition`, Algorithm 4 & Corollary 4.5, §4.3 of `paper.tex`)**:
Uncapped 2D decomposition with piece budget `maxPieces` and step budget `maxIter`. -/
noncomputable def aDecomposition [DecidableEq α] [DecidableEq β]
    (maxPieces maxIter : ℕ) (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (ε₂ : ℝ) (D : ℕ) (ρ₂ : ℝ)
    (oracleV : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → (α → ℝ)) :
    List (RectPiece α β) :=
  aDecompositionLoop maxPieces maxIter X Y A ε₂ D ρ₂ 2 oracleV []

/-- Cost-tracked uncapped `Decompose2D` (`aDecompositionTracked`) in `CostM`. -/
noncomputable def aDecompositionTracked [DecidableEq α] [DecidableEq β]
    (maxPieces maxIter : ℕ) (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (ε₂ : ℝ) (D : ℕ) (ρ₂ : ℝ)
    (oracleVTracked : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → CostM (α → ℝ)) :
    CostM (List (RectPiece α β)) :=
  aDecompositionLoopTracked maxPieces maxIter X Y A ε₂ D ρ₂ 2 oracleVTracked []

@[simp]
theorem aDecompositionTracked_fst [DecidableEq α] [DecidableEq β]
    (maxPieces maxIter : ℕ) (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (ε₂ : ℝ) (D : ℕ) (ρ₂ : ℝ)
    (oracleVTracked : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → CostM (α → ℝ)) :
    (aDecompositionTracked maxPieces maxIter X Y A ε₂ D ρ₂ oracleVTracked).1 =
      aDecomposition maxPieces maxIter X Y A ε₂ D ρ₂
        (fun U V M α_g d => (oracleVTracked U V M α_g d).1) :=
  aDecompositionLoopTracked_fst maxPieces maxIter X Y A ε₂ D ρ₂ 2 oracleVTracked []

/-- **Capped `Decompose2D` (`cappedADecomposition`, Algorithm 4, §4.3 of `paper.tex`)**:
Capped 2D decomposition with threshold $\tau_{\text{low}} = \max(2^{-D}, \alpha_{\text{low}})$,
density cap $\alpha_{\text{cap}}$, and per-piece iteration budget `rRect2DFuel ε₂`. -/
noncomputable def cappedADecomposition [DecidableEq α] [DecidableEq β]
    (maxPieces : ℕ) (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (ε₂ : ℝ) (D : ℕ) (α_low α_cap : ℝ)
    (oracleV : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → (α → ℝ)) :
    List (RectPiece α β) :=
  aDecompositionLoop maxPieces (rRect2DFuel ε₂) X Y A ε₂ D
    (max (((2 : ℝ) ^ D)⁻¹) α_low) α_cap oracleV []

/-- Cost-tracked capped `Decompose2D` (`cappedADecompositionTracked`) in `CostM`. -/
noncomputable def cappedADecompositionTracked [DecidableEq α] [DecidableEq β]
    (maxPieces : ℕ) (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (ε₂ : ℝ) (D : ℕ) (α_low α_cap : ℝ)
    (oracleVTracked : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → CostM (α → ℝ)) :
    CostM (List (RectPiece α β)) :=
  aDecompositionLoopTracked maxPieces (rRect2DFuel ε₂) X Y A ε₂ D
    (max (((2 : ℝ) ^ D)⁻¹) α_low) α_cap oracleVTracked []

@[simp]
theorem cappedADecompositionTracked_fst [DecidableEq α] [DecidableEq β]
    (maxPieces : ℕ) (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (ε₂ : ℝ) (D : ℕ) (α_low α_cap : ℝ)
    (oracleVTracked : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → CostM (α → ℝ)) :
    (cappedADecompositionTracked maxPieces X Y A ε₂ D α_low α_cap oracleVTracked).1 =
      cappedADecomposition maxPieces X Y A ε₂ D α_low α_cap
        (fun U V M α_g d => (oracleVTracked U V M α_g d).1) :=
  aDecompositionLoopTracked_fst maxPieces (rRect2DFuel ε₂) X Y A ε₂ D
    (max (((2 : ℝ) ^ D)⁻¹) α_low) α_cap oracleVTracked []

end GoodRectDefs

/-!
## Lemma 4.3, Theorem 4.4 & Corollary 4.5: Shrinkage and Piece-Count Bounds (§4.3 of `paper.tex`)
-/

section ShrinkageAndPieceCount

/-- **Theorem 4.4 Piece-Count Bound at Dyadic Scale $s$ (`adecomp_piece_count_at_scale_le`,
`\label{thm:2d-decomp}`, §4.3 of `paper.tex`)**:
Suppose $L_s$ extracted pieces at scale $\bar{s}_\ell = s$ each contribute density decrement
$\Delta_\ell \ge 2^{-s D} M_{\text{rect}}^{-1} \cdot 2^s \rho_2$ where $\rho_2 \ge 2^{-D}$ and
$M_{\text{rect}} > 0$, and the total density decrement over those $L_s$ pieces is at most
$\mu_0 \le 1$. Then (relaxing $2^{s(D - 1)} \le 2^{s D}$ via $2^s \ge 1$):
1. $L_s \le M_{\text{rect}} \rho_2^{-1} 2^{s D} \mu_0 \le M_{\text{rect}} \rho_2^{-1} 2^{s D}$, and
2. Using $\rho_2 \ge 2^{-D}$, $L_s \le 2^D M_{\text{rect}} 2^{s D}$. -/
theorem adecomp_piece_count_at_scale_le
    {L_s s D : ℕ} {M_rect ρ₂ μ₀ total_dec : ℝ}
    (hM_pos : 0 < M_rect) (hρ_pos : 0 < ρ₂) (hρ_ge : ((2 : ℝ) ^ D)⁻¹ ≤ ρ₂)
    (hμ₀_le_one : μ₀ ≤ 1)
    (h_each_dec : (L_s : ℝ) * ((((2 : ℝ) ^ (s * D))⁻¹) * M_rect⁻¹ * ((2 : ℝ) ^ s * ρ₂)) ≤ total_dec)
    (h_tot_le : total_dec ≤ μ₀) :
    (L_s : ℝ) ≤ M_rect * ρ₂⁻¹ * (2 : ℝ) ^ (s * D) * μ₀ ∧
    (L_s : ℝ) ≤ M_rect * ρ₂⁻¹ * (2 : ℝ) ^ (s * D) ∧
    (L_s : ℝ) ≤ (2 : ℝ) ^ D * M_rect * (2 : ℝ) ^ (s * D) := by
  have h2s_ge_one : (1 : ℝ) ≤ (2 : ℝ) ^ s := one_le_pow₀ (by norm_num)
  have h2sD_pos : (0 : ℝ) < (2 : ℝ) ^ (s * D) := by positivity
  have h2D_pos : (0 : ℝ) < (2 : ℝ) ^ D := by positivity
  have h_unit_le : (((2 : ℝ) ^ (s * D))⁻¹) * M_rect⁻¹ * ρ₂ ≤
      (((2 : ℝ) ^ (s * D))⁻¹) * M_rect⁻¹ * ((2 : ℝ) ^ s * ρ₂) := by
    have h1 : ρ₂ ≤ (2 : ℝ) ^ s * ρ₂ := by nlinarith
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have h_L_mul : (L_s : ℝ) * ((((2 : ℝ) ^ (s * D))⁻¹) * M_rect⁻¹ * ρ₂) ≤ μ₀ := by
    calc
      (L_s : ℝ) * ((((2 : ℝ) ^ (s * D))⁻¹) * M_rect⁻¹ * ρ₂) ≤
          (L_s : ℝ) * ((((2 : ℝ) ^ (s * D))⁻¹) * M_rect⁻¹ * ((2 : ℝ) ^ s * ρ₂)) :=
        mul_le_mul_of_nonneg_left h_unit_le (Nat.cast_nonneg L_s)
      _ ≤ total_dec := h_each_dec
      _ ≤ μ₀ := h_tot_le
  have h_mult_pos : 0 < M_rect * ρ₂⁻¹ * (2 : ℝ) ^ (s * D) := by positivity
  have h_cancel : ((((2 : ℝ) ^ (s * D))⁻¹) * M_rect⁻¹ * ρ₂) *
      (M_rect * ρ₂⁻¹ * (2 : ℝ) ^ (s * D)) = 1 := by
    field_simp [hM_pos.ne', hρ_pos.ne', h2sD_pos.ne']
  have h_bound1 : (L_s : ℝ) ≤ M_rect * ρ₂⁻¹ * (2 : ℝ) ^ (s * D) * μ₀ := by
    calc
      (L_s : ℝ) = (L_s : ℝ) * ((((2 : ℝ) ^ (s * D))⁻¹) * M_rect⁻¹ * ρ₂ *
          (M_rect * ρ₂⁻¹ * (2 : ℝ) ^ (s * D))) := by rw [h_cancel, mul_one]
      _ = ((L_s : ℝ) * ((((2 : ℝ) ^ (s * D))⁻¹) * M_rect⁻¹ * ρ₂)) *
          (M_rect * ρ₂⁻¹ * (2 : ℝ) ^ (s * D)) := by ring
      _ ≤ μ₀ * (M_rect * ρ₂⁻¹ * (2 : ℝ) ^ (s * D)) :=
        mul_le_mul_of_nonneg_right h_L_mul (le_of_lt h_mult_pos)
      _ = M_rect * ρ₂⁻¹ * (2 : ℝ) ^ (s * D) * μ₀ := by ring
  have h_bound2 : (L_s : ℝ) ≤ M_rect * ρ₂⁻¹ * (2 : ℝ) ^ (s * D) := by
    calc
      (L_s : ℝ) ≤ M_rect * ρ₂⁻¹ * (2 : ℝ) ^ (s * D) * μ₀ := h_bound1
      _ ≤ M_rect * ρ₂⁻¹ * (2 : ℝ) ^ (s * D) * 1 :=
        mul_le_mul_of_nonneg_left hμ₀_le_one (le_of_lt h_mult_pos)
      _ = M_rect * ρ₂⁻¹ * (2 : ℝ) ^ (s * D) := mul_one _
  have h_ρ_inv_le : ρ₂⁻¹ ≤ (2 : ℝ) ^ D := by
    have h1 := inv_anti₀ (by positivity) hρ_ge
    rwa [inv_inv] at h1
  have h_bound3 : (L_s : ℝ) ≤ (2 : ℝ) ^ D * M_rect * (2 : ℝ) ^ (s * D) := by
    calc
      (L_s : ℝ) ≤ M_rect * ρ₂⁻¹ * (2 : ℝ) ^ (s * D) := h_bound2
      _ = ρ₂⁻¹ * (M_rect * (2 : ℝ) ^ (s * D)) := by ring
      _ ≤ (2 : ℝ) ^ D * (M_rect * (2 : ℝ) ^ (s * D)) :=
        mul_le_mul_of_nonneg_right h_ρ_inv_le (by positivity)
      _ = (2 : ℝ) ^ D * M_rect * (2 : ℝ) ^ (s * D) := by ring
  exact ⟨h_bound1, h_bound2, h_bound3⟩

/-- Per-step row-shrinkage factor $(\frac{\varepsilon_2}{48}) \cdot 2^{-2D}$ in 2D `FindRect`
(§4.3 of `paper.tex`, `\eqref{eq:capped-goodrect-shrinkage}`). -/
noncomputable def goodRect2DStepFactor (ε₂ : ℝ) (D : ℕ) : ℝ :=
  (ε₂ / 48) * (((2 : ℝ) ^ (2 * D))⁻¹)

/-- Parameterized worst-case inverse area-shrinkage constant
$M_{\text{rect2D}}(\text{maxIter}, \varepsilon_2, D)$ for `goodRectLoop maxIter` (§4.3 of `paper.tex`). -/
noncomputable def M_rect2D_of_fuel (maxIter : ℕ) (ε₂ : ℝ) (D : ℕ) : ℝ :=
  3 * (((goodRect2DStepFactor ε₂ D)⁻¹) * ((2 : ℝ) ^ (2 * D))) ^ maxIter

/-- Worst-case inverse area-shrinkage constant $M_{\text{rect2D}}(\varepsilon_2, D)$ for
2D `CappedGoodRect` (§4.3 of `paper.tex`). -/
noncomputable def M_rect2D (ε₂ : ℝ) (D : ℕ) : ℝ :=
  3 * (((goodRect2DStepFactor ε₂ D)⁻¹) * ((2 : ℝ) ^ (2 * D))) ^ (rRect2DFuel ε₂)

/-- Piece-count budget `rDecomp2DFuel` for 2D `CappedADecomposition` (§4.3 of `paper.tex`). -/
noncomputable def rDecomp2DFuel (ε₂ : ℝ) (D : ℕ) : ℕ :=
  Nat.ceil ((2 : ℝ) ^ (D + D ^ 2) * M_rect2D ε₂ D) + 1

/-- Worst-case inverse area-shrinkage constant $M_{\text{uncappedRect2D}}(\varepsilon_2, D)$ for
uncapped 2D `FindRect` with adaptive step budget `rUncappedRect2DFuel ε₂ D` (§4.3 of `paper.tex`). -/
noncomputable def M_uncappedRect2D (ε₂ : ℝ) (D : ℕ) : ℝ :=
  M_rect2D_of_fuel (rUncappedRect2DFuel ε₂ D) ε₂ D

/-- Piece-count budget `rUncappedDecomp2DFuel` for uncapped 2D `ADecomposition` (§4.3 of `paper.tex`). -/
noncomputable def rUncappedDecomp2DFuel (ε₂ : ℝ) (D : ℕ) : ℕ :=
  Nat.ceil ((2 : ℝ) ^ (D + D ^ 2) * M_uncappedRect2D ε₂ D) + 1

/-- Predicate certifying that `oracleV` satisfies the Lemma 4.1 `ApproxGridNorm` guarantee
required by `dyadicSift` (§4.2 of `paper.tex`), stated under the density precondition
`δ > 2^{-D}` of Lemma 4.2; this is the regime in which `dyadicSift` consults the estimator. -/
def IsValidOracleV (oracleV : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → (α → ℝ))
    (ε₂ : ℝ) (D : ℕ) : Prop :=
  ∀ (U : Finset α) (V : Finset β) (M : α → β → ℝ),
    U.Nonempty → IsBinaryMatrix U V M →
    1 < (2 : ℝ) ^ D * ((1 + ε₂ / 2) * matDensity U V M) →
    let δ := (1 + ε₂ / 2) * matDensity U V M
    let α_grid := ε₂ * δ ^ 3 / 32
    ∀ x ∈ U, 0 < rowDeg V M x →
      0 ≤ oracleV U V M α_grid D x ∧
      |(oracleV U V M α_grid D x) ^ ((1 : ℝ) / (D : ℝ)) -
        gridNorm U (rowSupport V M x) M 1 D| ≤ α_grid / rowDeg V M x

private lemma isBinaryMatrix_subset_2D {X X' : Finset α} {Y Y' : Finset β} {A : α → β → ℝ}
    (hX : X' ⊆ X) (hY : Y' ⊆ Y) (hA : IsBinaryMatrix X Y A) :
    IsBinaryMatrix X' Y' A :=
  fun x hx y hy => hA x (hX hx) y (hY hy)

private lemma isBinaryMatrix_nonneg_2D {X : Finset α} {Y : Finset β} {A : α → β → ℝ}
    (hA : IsBinaryMatrix X Y A) :
    ∀ x ∈ X, ∀ y ∈ Y, 0 ≤ A x y := by
  intro x hx y hy
  rcases hA x hx y hy with h0 | h1 <;> linarith

private lemma isBinaryMatrix_le_one_2D {X : Finset α} {Y : Finset β} {A : α → β → ℝ}
    (hA : IsBinaryMatrix X Y A) :
    ∀ x ∈ X, ∀ y ∈ Y, A x y ≤ 1 := by
  intro x hx y hy
  rcases hA x hx y hy with h0 | h1 <;> linarith

private lemma expectSet_congr_2D {γ : Type*} {S : Finset γ} {f g : γ → ℝ}
    (h : ∀ x ∈ S, f x = g x) :
    expectSet S f = expectSet S g := by
  unfold expectSet
  congr 1
  exact Finset.sum_congr rfl h

private lemma matDensity_le_one_of_isBinaryMatrix_2D {X : Finset α} {Y : Finset β} {A : α → β → ℝ}
    (hA : IsBinaryMatrix X Y A) :
    matDensity X Y A ≤ 1 := by
  rcases X.eq_empty_or_nonempty with rfl | hX
  · simp [matDensity]
  · rcases Y.eq_empty_or_nonempty with rfl | hY
    · unfold matDensity rowDeg expectSet
      simp
    · exact expectSet_le_of_le hX (fun x hx =>
        expectSet_le_of_le hY (isBinaryMatrix_le_one_2D hA x hx))

private lemma matDensity_nonneg_of_isBinaryMatrix_2D {X : Finset α} {Y : Finset β} {A : α → β → ℝ}
    (hA : IsBinaryMatrix X Y A) :
    0 ≤ matDensity X Y A :=
  expectSet_nonneg (fun x hx => expectSet_nonneg (fun y hy => isBinaryMatrix_nonneg_2D hA x hx y hy))

private lemma rowDeg_restrictSubrect_eq {X' : Finset α} {Y' : Finset β} (A : α → β → ℝ)
    {x : α} (hx : x ∈ X') :
    rowDeg Y' (restrictSubrect A X' Y') x = rowDeg Y' A x := by
  unfold rowDeg
  exact expectSet_congr_2D (fun y hy => restrictSubrect_eq_on hx hy)

private lemma isGridRegular_of_eq_on_2D {U : Finset α} {V : Finset β} {M₁ M₂ : α → β → ℝ}
    (heq : ∀ u ∈ U, ∀ v ∈ V, M₁ u v = M₂ u v)
    {ε : ℝ} {k ℓ : ℕ} (hreg : IsGridRegular U V M₁ ε k ℓ) :
    IsGridRegular U V M₂ ε k ℓ := by
  have hgn : gridNormPow U V M₁ k ℓ = gridNormPow U V M₂ k ℓ := by
    unfold gridNormPow
    refine expectSet_congr_2D (fun us hus => ?_)
    have hus_mem : ∀ i : Fin k, us i ∈ U := Fintype.mem_piFinset.mp hus
    congr 1
    refine expectSet_congr_2D (fun v hv => ?_)
    exact Finset.prod_congr rfl (fun i _ => heq (us i) (hus_mem i) v hv)
  have hdens : matDensity U V M₁ = matDensity U V M₂ := by
    unfold matDensity rowDeg
    refine expectSet_congr_2D (fun u hu => expectSet_congr_2D (fun v hv => heq u hu v hv))
  unfold IsGridRegular gridNorm at hreg ⊢
  rw [← hgn, ← hdens]
  exact hreg

private lemma isEpsMinDegree_of_eq_on_2D {U : Finset α} {V : Finset β} {M₁ M₂ : α → β → ℝ}
    (heq : ∀ u ∈ U, ∀ v ∈ V, M₁ u v = M₂ u v)
    {ε : ℝ} (hmin : IsEpsMinDegree U V M₁ ε) :
    IsEpsMinDegree U V M₂ ε := by
  have hrow : ∀ u ∈ U, rowDeg V M₁ u = rowDeg V M₂ u :=
    fun u hu => expectSet_congr_2D (fun v hv => heq u hu v hv)
  have hdens : matDensity U V M₁ = matDensity U V M₂ :=
    expectSet_congr_2D (fun u hu => hrow u hu)
  intro u hu
  rw [← hrow u hu, ← hdens]
  exact hmin u hu

private lemma goodRect2DStepFactor_bounds {ε₂ : ℝ} (hε0 : 0 < ε₂) (hε1 : ε₂ ≤ 1) (D : ℕ) :
    0 < goodRect2DStepFactor ε₂ D ∧
    goodRect2DStepFactor ε₂ D ≤ 1 / 3 ∧
    goodRect2DStepFactor ε₂ D ≤ 1 := by
  unfold goodRect2DStepFactor
  have h2D_ge : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * D) := one_le_pow₀ (by norm_num)
  have hinv_le : (((2 : ℝ) ^ (2 * D))⁻¹) ≤ 1 := inv_le_one_of_one_le₀ h2D_ge
  have hpos : 0 < (ε₂ / 48) * (((2 : ℝ) ^ (2 * D))⁻¹) := by positivity
  have hle48 : (ε₂ / 48) * (((2 : ℝ) ^ (2 * D))⁻¹) ≤ 1 / 48 := by
    calc
      (ε₂ / 48) * (((2 : ℝ) ^ (2 * D))⁻¹) ≤ (1 / 48) * 1 :=
        mul_le_mul (by linarith) hinv_le (by positivity) (by norm_num)
      _ = 1 / 48 := mul_one _
  refine ⟨hpos, by linarith, by linarith⟩

/-- $(1 + \varepsilon_2 / 2)^{\text{rRect2DFuel}(\varepsilon_2)} \ge 2^{48}$
for all $\varepsilon_2 > 0$ (§4.3 of `paper.tex`). -/
lemma pow_rRect2DFuel_ge {ε₂ : ℝ} (hε0 : 0 < ε₂) :
    (2 : ℝ) ^ (48 : ℕ) ≤ (1 + ε₂ / 2) ^ (rRect2DFuel ε₂) := by
  unfold rRect2DFuel
  let k := Nat.ceil (1 / ε₂)
  have hk_ge : 1 / ε₂ ≤ (k : ℝ) := Nat.le_ceil (1 / ε₂)
  have hk_mul : 1 ≤ (k : ℝ) * ε₂ := (div_le_iff₀ hε0).mp hk_ge
  have hk_half : (1 / 2 : ℝ) ≤ (k : ℝ) * (ε₂ / 2) := by linarith
  have hbern : 1 + (k : ℝ) * (ε₂ / 2) ≤ (1 + ε₂ / 2) ^ k :=
    one_add_mul_le_pow (by linarith) k
  have h32 : (3 / 2 : ℝ) ≤ (1 + ε₂ / 2) ^ k := by linarith
  have h84 : ((3 / 2 : ℝ) ^ (84 : ℕ)) ≤ ((1 + ε₂ / 2) ^ k) ^ (84 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) h32 84
  have hnorm : (2 : ℝ) ^ (48 : ℕ) ≤ (3 / 2 : ℝ) ^ (84 : ℕ) := by norm_num
  rw [mul_comm 84 k, pow_mul]
  exact hnorm.trans h84

/-- $(1 + \varepsilon_2 / 2)^{\text{rUncappedRect2DFuel}(\varepsilon_2, D)} \ge 2^{D+1}$
for all $\varepsilon_2 > 0$ and $D \in \mathbb{N}$ (§4.3 of `paper.tex`). -/
lemma pow_rUncappedRect2DFuel_ge {ε₂ : ℝ} (hε0 : 0 < ε₂) (D : ℕ) :
    (2 : ℝ) ^ (D + 1) ≤ (1 + ε₂ / 2) ^ (rUncappedRect2DFuel ε₂ D) := by
  unfold rUncappedRect2DFuel
  let k := Nat.ceil (1 / ε₂)
  have hk_ge : 1 / ε₂ ≤ (k : ℝ) := Nat.le_ceil (1 / ε₂)
  have hk_mul : 1 ≤ (k : ℝ) * ε₂ := (div_le_iff₀ hε0).mp hk_ge
  have hk_half : (1 / 2 : ℝ) ≤ (k : ℝ) * (ε₂ / 2) := by linarith
  have hbern : 1 + (k : ℝ) * (ε₂ / 2) ≤ (1 + ε₂ / 2) ^ k :=
    one_add_mul_le_pow (by linarith) k
  have h32 : (3 / 2 : ℝ) ≤ (1 + ε₂ / 2) ^ k := by linarith
  have h2_le_sq : (2 : ℝ) ≤ ((1 + ε₂ / 2) ^ k) ^ (2 : ℕ) := by
    have h94 : (2 : ℝ) ≤ (3 / 2 : ℝ) ^ (2 : ℕ) := by norm_num
    exact h94.trans (pow_le_pow_left₀ (by norm_num) h32 2)
  have hD1 : (2 : ℝ) ^ (D + 1) ≤ (((1 + ε₂ / 2) ^ k) ^ (2 : ℕ)) ^ (D + 1) :=
    pow_le_pow_left₀ (by norm_num) h2_le_sq (D + 1)
  have hpow_eq :
      (((1 + ε₂ / 2) ^ k) ^ (2 : ℕ)) ^ (D + 1) =
        (1 + ε₂ / 2) ^ (2 * (D + 1) * k) := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [hpow_eq] at hD1
  have hmono :
      (1 + ε₂ / 2) ^ (2 * (D + 1) * k) ≤
        (1 + ε₂ / 2) ^ (2 * (D + 1) * k + 1) :=
    pow_le_pow_right₀ (by linarith) (Nat.le_succ _)
  exact hD1.trans hmono

/-- Single-step specification for `goodRectStep` (Algorithm 4, §4.3 of `paper.tex`). -/
lemma goodRectStep_spec [DecidableEq α] [DecidableEq β]
    {X' : Finset α} {Y' : Finset β} {A : α → β → ℝ} {ε₂ : ℝ} {D : ℕ} {α_cap : ℝ}
    {oracleV : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → (α → ℝ)}
    (s_bar : ℕ)
    (hX' : X'.Nonempty) (hY' : Y'.Nonempty) (hA : IsBinaryMatrix X' Y' A)
    (hε0 : 0 < ε₂) (hε1 : ε₂ < 1) (hD : 2 ≤ D)
    (hA_ge : ((2 : ℝ) ^ D)⁻¹ ≤ matDensity X' Y' A)
    (h_oracle : IsValidOracleV oracleV ε₂ D) :
    match goodRectStep X' Y' A ε₂ D α_cap oracleV s_bar with
    | Sum.inr (X_out, Y_out, tag, s_out) =>
      X_out ⊆ X' ∧ Y_out ⊆ Y' ∧ X_out.Nonempty ∧ Y_out.Nonempty ∧
      s_out = s_bar ∧
      matDensity X' Y' A ≤ matDensity X_out Y_out A ∧
      (1 / 3 : ℝ) * (X'.card : ℝ) ≤ (X_out.card : ℝ) ∧
      (Y'.card : ℝ) ≤ (Y_out.card : ℝ) ∧
      (tag = RectTag.regular ∨ tag = RectTag.aBoosted) ∧
      (tag = RectTag.aBoosted → α_cap ≤ matDensity X_out Y_out A) ∧
      (tag = RectTag.regular →
        matDensity X_out Y_out A < α_cap ∧
        IsGridRegular X_out Y_out (restrictSubrect A X_out Y_out) ε₂ 2 D ∧
        IsEpsMinDegree X_out Y_out (restrictSubrect A X_out Y_out) ε₂)
    | Sum.inl (X_next, Y_next, s_bar_next, s_step) =>
      X_next ⊆ X' ∧ Y_next ⊆ Y' ∧ X_next.Nonempty ∧ Y_next.Nonempty ∧
      s_bar_next = s_bar + s_step ∧
      (2 : ℝ) ^ s_step * (1 + ε₂ / 2) * matDensity X' Y' A ≤
        matDensity X_next Y_next A ∧
      (((2 : ℝ) ^ (s_step * D))⁻¹) * goodRect2DStepFactor ε₂ D * (X'.card : ℝ) ≤
        (X_next.card : ℝ) ∧
      (((2 : ℝ) ^ (2 * D))⁻¹) * (Y'.card : ℝ) ≤ (Y_next.card : ℝ) := by
  have hγ_pos : (0 : ℝ) < 1 / 2 := by norm_num
  have hγ_le_half : (1 / 2 : ℝ) ≤ 1 / 2 := le_rfl
  have hfac_bds := goodRect2DStepFactor_bounds hε0 hε1.le D
  have hX'_pos : (0 : ℝ) < X'.card := Nat.cast_pos.mpr hX'.card_pos
  have hY'_pos : (0 : ℝ) < Y'.card := Nat.cast_pos.mpr hY'.card_pos
  have hA_d_nonneg : 0 ≤ matDensity X' Y' A := le_trans (by positivity) hA_ge
  by_cases hcap0 : matDensity X' Y' A ≥ α_cap
  · have hstep : goodRectStep X' Y' A ε₂ D α_cap oracleV s_bar =
        Sum.inr (X', Y', RectTag.aBoosted, s_bar) := by
      unfold goodRectStep; dsimp only; rw [if_pos hcap0]
    rw [hstep]
    exact ⟨Finset.Subset.rfl, Finset.Subset.rfl, hX', hY', rfl, le_rfl,
      by linarith, le_rfl, Or.inr rfl, fun _ => hcap0, (fun h => by cases h)⟩
  · have hM_nonneg : ∀ x ∈ X', 0 ≤ rowDeg Y' A x :=
      fun x hx => expectSet_nonneg (fun y hy => isBinaryMatrix_nonneg_2D hA x hx y hy)
    have hmin := lem_min_degree hX' hε0 hε1 hγ_pos hγ_le_half hM_nonneg
    rcases hmin with ⟨hX₁_sub, hX₁_ne, hX₁_third, hX₁_dens, hmin_cases, hmin1_spec, hmin2_spec, _⟩
    let resMin := minDegree X' Y' A ε₂ (1 / 2)
    let X₁ := resMin.1
    have hA_X₁ : IsBinaryMatrix X₁ Y' A := isBinaryMatrix_subset_2D hX₁_sub Finset.Subset.rfl hA
    have hX₁_ge : ((2 : ℝ) ^ D)⁻¹ ≤ matDensity X₁ Y' A := hA_ge.trans hX₁_dens
    by_cases hcase2 : resMin.2 = 2 ∨ matDensity X₁ Y' A ≥ (1 + ε₂ / 2) * matDensity X' Y' A
    · have hstep : goodRectStep X' Y' A ε₂ D α_cap oracleV s_bar =
          Sum.inl (X₁, Y', s_bar, 0) := by
        unfold goodRectStep; dsimp only; rw [if_neg hcap0, if_pos hcase2]
      rw [hstep]
      have hboost2 : (1 + ε₂ / 2) * matDensity X' Y' A ≤ matDensity X₁ Y' A := by
        rcases hcase2 with h2 | hdens_ge
        · have h2s := (hmin2_spec h2).2.2.2.2.2.2.1
          linarith
        · exact hdens_ge
      have h2D_le : (((2 : ℝ) ^ (2 * D))⁻¹) ≤ 1 :=
        inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
      refine ⟨hX₁_sub, Finset.Subset.rfl, hX₁_ne, hY', (Nat.add_zero s_bar).symm, ?_, ?_, ?_⟩
      · simp only [pow_zero, one_mul]; exact hboost2
      · simp only [zero_mul, pow_zero, inv_one, one_mul]
        calc
          goodRect2DStepFactor ε₂ D * (X'.card : ℝ) ≤ (1 / 3 : ℝ) * (X'.card : ℝ) :=
            mul_le_mul_of_nonneg_right hfac_bds.2.1 hX'_pos.le
          _ ≤ (X₁.card : ℝ) := hX₁_third
      · calc
          (((2 : ℝ) ^ (2 * D))⁻¹) * (Y'.card : ℝ) ≤ 1 * (Y'.card : ℝ) :=
            mul_le_mul_of_nonneg_right h2D_le hY'_pos.le
          _ = (Y'.card : ℝ) := one_mul _
    · have hcase1 : resMin.2 = 1 := by
        rcases hmin_cases with h1 | h2
        · exact h1
        · exact False.elim (hcase2 (Or.inl h2))
      rcases hmin1_spec hcase1 with ⟨hmin_deg_M, _, _, _, _, _⟩
      have hmin_deg_X₁ : IsEpsMinDegree X₁ Y' (restrictSubrect A X₁ Y') ε₂ := by
        refine isEpsMinDegree_of_eq_on_2D (fun x hx y hy => ?_) hmin_deg_M
        exact (restrictSubrect_eq_on hx hy).symm
      by_cases hcap1 : matDensity X₁ Y' A ≥ α_cap
      · have hstep : goodRectStep X' Y' A ε₂ D α_cap oracleV s_bar =
            Sum.inr (X₁, Y', RectTag.aBoosted, s_bar) := by
          unfold goodRectStep; dsimp only; rw [if_neg hcap0, if_neg hcase2, if_pos hcap1]
        rw [hstep]
        exact ⟨hX₁_sub, Finset.Subset.rfl, hX₁_ne, hY', rfl, hX₁_dens, hX₁_third, le_rfl,
          Or.inr rfl, fun _ => hcap1, (fun h => by cases h)⟩
      · have hcap1_lt : matDensity X₁ Y' A < α_cap := not_le.mp hcap1
        have hδ_gt : 1 < (2 : ℝ) ^ D * ((1 + ε₂ / 2) * matDensity X₁ Y' A) := by
          have h2D_pos : (0 : ℝ) < (2 : ℝ) ^ D := by positivity
          have h1 : 1 ≤ (2 : ℝ) ^ D * matDensity X₁ Y' A := by
            have hmul := mul_le_mul_of_nonneg_left hX₁_ge h2D_pos.le
            rwa [mul_inv_cancel₀ h2D_pos.ne'] at hmul
          have hpos_d : 0 < matDensity X₁ Y' A := lt_of_lt_of_le (by positivity) hX₁_ge
          nlinarith
        let δ := (1 + ε₂ / 2) * matDensity X₁ Y' A
        let α_grid := ε₂ * δ ^ 3 / 32
        let V := oracleV X₁ Y' A α_grid D
        have hV_approx := h_oracle X₁ Y' A hX₁_ne hA_X₁ hδ_gt
        have hsift := lem_dyadic_sift hX₁_ne hY' hA_X₁ hε0 hε1 hD hδ_gt hV_approx
        rcases hsift with ⟨hsift_cases, hsift_sub_spec, hsift_reg_spec⟩
        let resSift := dyadicSift X₁ Y' A ε₂ D V
        by_cases hsift_reg : resSift.1 = "regular"
        · have hstep : goodRectStep X' Y' A ε₂ D α_cap oracleV s_bar =
              Sum.inr (X₁, Y', RectTag.regular, s_bar) := by
            unfold goodRectStep; dsimp only
            rw [if_neg hcap0, if_neg hcase2, if_neg hcap1, if_pos hsift_reg]
          have hreg_A := (hsift_reg_spec hsift_reg).2.2.2.2
          have hreg_sub : IsGridRegular X₁ Y' (restrictSubrect A X₁ Y') ε₂ 2 D :=
            isGridRegular_of_eq_on_2D (fun x hx y hy => (restrictSubrect_eq_on hx hy).symm) hreg_A
          rw [hstep]
          exact ⟨hX₁_sub, Finset.Subset.rfl, hX₁_ne, hY', rfl, hX₁_dens, hX₁_third, le_rfl,
            Or.inl rfl, (fun h => by cases h), (fun _ => ⟨hcap1_lt, hreg_sub, hmin_deg_X₁⟩)⟩
        · have hsift_sub_eq : resSift.1 = "subrect" := by
            rcases hsift_cases with h1 | h2
            · exact h1
            · exact False.elim (hsift_reg h2)
          rcases hsift_sub_spec hsift_sub_eq with
            ⟨_hs_lt_D, hX_next_sub, hY_next_sub, hX_next_ne, hY_next_ne,
              hX_next_dens, hX_next_card, _, hY_next_card⟩
          let X_next := resSift.2.1
          let Y_next := resSift.2.2.1
          let s := resSift.2.2.2
          have hstep : goodRectStep X' Y' A ε₂ D α_cap oracleV s_bar =
              Sum.inl (X_next, Y_next, s_bar + s, s) := by
            unfold goodRectStep; dsimp only
            rw [if_neg hcap0, if_neg hcase2, if_neg hcap1, if_neg hsift_reg]
          rw [hstep]
          refine ⟨hX_next_sub.trans hX₁_sub, hY_next_sub, hX_next_ne, hY_next_ne, rfl, ?_, ?_, hY_next_card.le⟩
          · have h2 : (1 + ε₂ / 2) * matDensity X' Y' A ≤ (1 + ε₂ / 2) * matDensity X₁ Y' A :=
              mul_le_mul_of_nonneg_left hX₁_dens (by linarith)
            calc
              (2 : ℝ) ^ s * (1 + ε₂ / 2) * matDensity X' Y' A
                = (2 : ℝ) ^ s * ((1 + ε₂ / 2) * matDensity X' Y' A) := by ring
              _ ≤ (2 : ℝ) ^ s * ((1 + ε₂ / 2) * matDensity X₁ Y' A) :=
                mul_le_mul_of_nonneg_left h2 (by positivity)
              _ = (2 : ℝ) ^ s * (1 + ε₂ / 2) * matDensity X₁ Y' A := by ring
              _ ≤ matDensity X_next Y_next A := hX_next_dens
          · have hpow_split :
                (((2 : ℝ) ^ ((s + 2) * D))⁻¹) =
                  (((2 : ℝ) ^ (s * D))⁻¹) * (((2 : ℝ) ^ (2 * D))⁻¹) := by
              rw [Nat.add_mul, pow_add, mul_inv]
            calc
              (((2 : ℝ) ^ (s * D))⁻¹) * goodRect2DStepFactor ε₂ D * (X'.card : ℝ)
                = (ε₂ / 16) * (((2 : ℝ) ^ ((s + 2) * D))⁻¹) * ((1 / 3 : ℝ) * (X'.card : ℝ)) := by
                  unfold goodRect2DStepFactor
                  rw [hpow_split]
                  ring
              _ ≤ (ε₂ / 16) * (((2 : ℝ) ^ ((s + 2) * D))⁻¹) * (X₁.card : ℝ) :=
                  mul_le_mul_of_nonneg_left hX₁_third (by positivity)
              _ ≤ (X_next.card : ℝ) := hX_next_card

/-- **Inductive Specification of `goodRectLoop` (`goodRectLoop_spec`, `paper.tex` Section 4.3,
§4.3)**:
For any binary matrix `A` on `X' × Y'` with density at least `2^{-D}`, valid `ApproxGridNorm`
oracle `oracleV`, and fuel satisfying `α_cap ≤ (1 + ε₂ / 2) ^ fuel * matDensity X' Y' A`,
`goodRectLoop` returns `(X_out, Y_out, tag, s_out, steps_out)` satisfying:
1. $X_{\text{out}} \subseteq X'$, $Y_{\text{out}} \subseteq Y'$, both non-empty,
2. $s_{\text{bar}} \le s_{\text{out}}$ and $\text{steps}_{\text{done}} \le \text{steps}_{\text{out}} \le \text{steps}_{\text{done}} + \text{fuel}$,
3. Density boost $\mathbb{E}[A[X_{\text{out}}, Y_{\text{out}}]] \ge 2^{s_{\text{out}} - s_{\text{bar}}} (1 + \varepsilon_2 / 2)^{\text{steps}_{\text{out}} - \text{steps}_{\text{done}}} \mathbb{E}[A[X', Y']]$,
4. Row shrinkage $|X_{\text{out}}| \ge \frac{1}{3} \cdot 2^{-(s_{\text{out}} - s_{\text{bar}})D} (\text{goodRect2DStepFactor } \varepsilon_2\, D)^{\text{steps}_{\text{out}} - \text{steps}_{\text{done}}} |X'|$,
5. Column shrinkage $|Y_{\text{out}}| \ge 2^{-2(\text{steps}_{\text{out}} - \text{steps}_{\text{done}})D} |Y'|$,
6. If `tag = RectTag.aBoosted`, then $\mathbb{E}[A[X_{\text{out}}, Y_{\text{out}}]] \ge \alpha_{\text{cap}}$,
7. If `tag = RectTag.regular`, then $\mathbb{E}[A[X_{\text{out}}, Y_{\text{out}}]] < \alpha_{\text{cap}}$,
   and `restrictSubrect A X_out Y_out` is $(\varepsilon_2, 2, D)$-grid-regular and $\varepsilon_2$-min-degree. -/
theorem goodRectLoop_spec [DecidableEq α] [DecidableEq β]
    (fuel : ℕ) {X' : Finset α} {Y' : Finset β} {A : α → β → ℝ} {ε₂ : ℝ} {D : ℕ} {α_cap : ℝ}
    {oracleV : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → (α → ℝ)}
    (s_bar steps_done : ℕ)
    (hX' : X'.Nonempty) (hY' : Y'.Nonempty) (hA : IsBinaryMatrix X' Y' A)
    (hε0 : 0 < ε₂) (hε1 : ε₂ < 1) (hD : 2 ≤ D)
    (hA_ge : ((2 : ℝ) ^ D)⁻¹ ≤ matDensity X' Y' A)
    (h_oracle : IsValidOracleV oracleV ε₂ D)
    (hfuel_cap : α_cap ≤ (1 + ε₂ / 2) ^ fuel * matDensity X' Y' A) :
    let res := goodRectLoop fuel X' Y' A ε₂ D α_cap oracleV s_bar steps_done
    let X_out := res.1
    let Y_out := res.2.1
    let tag := res.2.2.1
    let s_out := res.2.2.2.1
    let steps_out := res.2.2.2.2
    X_out ⊆ X' ∧ Y_out ⊆ Y' ∧ X_out.Nonempty ∧ Y_out.Nonempty ∧
    s_bar ≤ s_out ∧ steps_done ≤ steps_out ∧ steps_out ≤ steps_done + fuel ∧
    (2 : ℝ) ^ (s_out - s_bar) *
      (1 + ε₂ / 2) ^ (steps_out - steps_done) * matDensity X' Y' A ≤
        matDensity X_out Y_out A ∧
    (1 / 3 : ℝ) * (((2 : ℝ) ^ ((s_out - s_bar) * D))⁻¹) *
      (goodRect2DStepFactor ε₂ D) ^ (steps_out - steps_done) * (X'.card : ℝ) ≤
        (X_out.card : ℝ) ∧
    (((2 : ℝ) ^ (2 * D))⁻¹) ^ (steps_out - steps_done) * (Y'.card : ℝ) ≤ (Y_out.card : ℝ) ∧
    (tag = RectTag.regular ∨ tag = RectTag.aBoosted) ∧
    (tag = RectTag.aBoosted → α_cap ≤ matDensity X_out Y_out A) ∧
    (tag = RectTag.regular →
      matDensity X_out Y_out A < α_cap ∧
      IsGridRegular X_out Y_out (restrictSubrect A X_out Y_out) ε₂ 2 D ∧
      IsEpsMinDegree X_out Y_out (restrictSubrect A X_out Y_out) ε₂) := by
  have hfac_bds := goodRect2DStepFactor_bounds hε0 hε1.le D
  induction fuel generalizing X' Y' s_bar steps_done with
  | zero =>
    dsimp only [goodRectLoop]
    rw [pow_zero, one_mul] at hfuel_cap
    refine ⟨Finset.Subset.rfl, Finset.Subset.rfl, hX', hY', le_rfl, le_rfl, by omega,
      ?_, ?_, ?_, Or.inr rfl, fun _ => hfuel_cap, (fun h => by cases h)⟩
    · simp only [Nat.sub_self, pow_zero, one_mul]; exact le_rfl
    · simp only [Nat.sub_self, zero_mul, pow_zero, inv_one, mul_one]
      have : (0 : ℝ) ≤ X'.card := Nat.cast_nonneg _
      linarith
    · simp only [Nat.sub_self, pow_zero, one_mul]; exact le_rfl
  | succ k ih =>
    dsimp only [goodRectLoop]
    have hstep_spec := goodRectStep_spec (α_cap := α_cap) s_bar hX' hY' hA hε0 hε1 hD hA_ge h_oracle
    rcases hstep : goodRectStep X' Y' A ε₂ D α_cap oracleV s_bar with
      ⟨X_next, Y_next, s_bar_next, s_step⟩ | ⟨X_out, Y_out, tag_out, s_final⟩
    · rw [hstep] at hstep_spec
      dsimp only at hstep_spec ⊢
      rcases hstep_spec with ⟨hX_next_sub, hY_next_sub, hX_next_ne, hY_next_ne,
        hs_eq, hboost_s, hX_step, hY_step⟩
      subst hs_eq
      have hA_next : IsBinaryMatrix X_next Y_next A :=
        isBinaryMatrix_subset_2D hX_next_sub hY_next_sub hA
      have hA_d_nonneg : 0 ≤ matDensity X' Y' A := le_trans (by positivity) hA_ge
      have h2s_ge : (1 : ℝ) ≤ (2 : ℝ) ^ s_step := one_le_pow₀ (by norm_num)
      have hboost_1 :
          (1 + ε₂ / 2) * matDensity X' Y' A ≤ matDensity X_next Y_next A := by
        have h1 : 1 * ((1 + ε₂ / 2) * matDensity X' Y' A) ≤
            (2 : ℝ) ^ s_step * ((1 + ε₂ / 2) * matDensity X' Y' A) :=
          mul_le_mul_of_nonneg_right h2s_ge (by positivity)
        linarith
      have hnext_ge : ((2 : ℝ) ^ D)⁻¹ ≤ matDensity X_next Y_next A := by
        have h1 : matDensity X' Y' A ≤ (1 + ε₂ / 2) * matDensity X' Y' A := by
          have : 0 ≤ (ε₂ / 2) * matDensity X' Y' A := by positivity
          linarith
        exact hA_ge.trans (h1.trans hboost_1)
      have hfuel_next :
          α_cap ≤ (1 + ε₂ / 2) ^ k * matDensity X_next Y_next A := by
        calc
          α_cap ≤ (1 + ε₂ / 2) ^ (k + 1) * matDensity X' Y' A := hfuel_cap
          _ = (1 + ε₂ / 2) ^ k *
                ((1 + ε₂ / 2) * matDensity X' Y' A) := by rw [pow_succ]; ring
          _ ≤ (1 + ε₂ / 2) ^ k * matDensity X_next Y_next A :=
            mul_le_mul_of_nonneg_left hboost_1 (by positivity)
      have h_ih := ih (s_bar + s_step) (steps_done + 1) hX_next_ne hY_next_ne hA_next hnext_ge hfuel_next
      dsimp only at h_ih
      rcases h_out : goodRectLoop k X_next Y_next A ε₂ D α_cap oracleV (s_bar + s_step) (steps_done + 1) with
        ⟨X_f, Y_f, tag_f, s_f, steps_f⟩
      rw [h_out] at h_ih
      dsimp only at h_ih ⊢
      rcases h_ih with ⟨hsubX, hsubY, hneX, hneY, hs_le, hsteps_lo, hsteps_hi,
        hdens_ih, hX_ih, hY_ih, htag_ih, hboost_ih, hreg_ih⟩
      have hs_sub_eq : s_f - s_bar = (s_f - (s_bar + s_step)) + s_step := by omega
      have hsteps_sub_eq : steps_f - steps_done = (steps_f - (steps_done + 1)) + 1 := by omega
      refine ⟨hsubX.trans hX_next_sub, hsubY.trans hY_next_sub,
        hneX, hneY, by omega, by omega, by omega, ?_, ?_, ?_, htag_ih, hboost_ih, hreg_ih⟩
      · rw [hs_sub_eq, hsteps_sub_eq, pow_add, pow_succ]
        calc
          ((2 : ℝ) ^ (s_f - (s_bar + s_step)) * (2 : ℝ) ^ s_step) *
              ((1 + ε₂ / 2) ^ (steps_f - (steps_done + 1)) *
                (1 + ε₂ / 2)) * matDensity X' Y' A
            = (2 : ℝ) ^ (s_f - (s_bar + s_step)) *
                (1 + ε₂ / 2) ^ (steps_f - (steps_done + 1)) *
                ((2 : ℝ) ^ s_step * (1 + ε₂ / 2) * matDensity X' Y' A) := by ring
          _ ≤ (2 : ℝ) ^ (s_f - (s_bar + s_step)) *
                (1 + ε₂ / 2) ^ (steps_f - (steps_done + 1)) *
                matDensity X_next Y_next A :=
              mul_le_mul_of_nonneg_left hboost_s (by positivity)
          _ ≤ matDensity X_f Y_f A := hdens_ih
      · have hpow_sub_split :
            (((2 : ℝ) ^ ((s_f - s_bar) * D))⁻¹) =
              (((2 : ℝ) ^ ((s_f - (s_bar + s_step)) * D))⁻¹) * (((2 : ℝ) ^ (s_step * D))⁻¹) := by
          rw [hs_sub_eq, Nat.add_mul, pow_add, mul_inv]
        rw [hpow_sub_split, hsteps_sub_eq, pow_succ]
        calc
          (1 / 3 : ℝ) *
              ((((2 : ℝ) ^ ((s_f - (s_bar + s_step)) * D))⁻¹) * (((2 : ℝ) ^ (s_step * D))⁻¹)) *
              ((goodRect2DStepFactor ε₂ D) ^ (steps_f - (steps_done + 1)) *
                goodRect2DStepFactor ε₂ D) * (X'.card : ℝ)
            = (1 / 3 : ℝ) * (((2 : ℝ) ^ ((s_f - (s_bar + s_step)) * D))⁻¹) *
                (goodRect2DStepFactor ε₂ D) ^ (steps_f - (steps_done + 1)) *
                ((((2 : ℝ) ^ (s_step * D))⁻¹) * goodRect2DStepFactor ε₂ D * (X'.card : ℝ)) := by ring
          _ ≤ (1 / 3 : ℝ) * (((2 : ℝ) ^ ((s_f - (s_bar + s_step)) * D))⁻¹) *
                (goodRect2DStepFactor ε₂ D) ^ (steps_f - (steps_done + 1)) *
                (X_next.card : ℝ) := by
              refine mul_le_mul_of_nonneg_left hX_step ?_
              have := hfac_bds.1
              positivity
          _ ≤ (X_f.card : ℝ) := hX_ih
      · rw [hsteps_sub_eq, pow_succ]
        calc
          ((((2 : ℝ) ^ (2 * D))⁻¹) ^ (steps_f - (steps_done + 1)) *
              (((2 : ℝ) ^ (2 * D))⁻¹)) * (Y'.card : ℝ)
            = (((2 : ℝ) ^ (2 * D))⁻¹) ^ (steps_f - (steps_done + 1)) *
                ((((2 : ℝ) ^ (2 * D))⁻¹) * (Y'.card : ℝ)) := by ring
          _ ≤ (((2 : ℝ) ^ (2 * D))⁻¹) ^ (steps_f - (steps_done + 1)) *
                (Y_next.card : ℝ) :=
              mul_le_mul_of_nonneg_left hY_step (by positivity)
          _ ≤ (Y_f.card : ℝ) := hY_ih
    · rw [hstep] at hstep_spec
      dsimp only at hstep_spec ⊢
      rcases hstep_spec with ⟨hX_sub, hY_sub, hX_ne, hY_ne, hs_eq, hdens_le, hX_card, hY_card,
        htag, hboost, hreg⟩
      subst hs_eq
      refine ⟨hX_sub, hY_sub, hX_ne, hY_ne, le_rfl, le_rfl, by omega,
        ?_, ?_, ?_, htag, hboost, hreg⟩
      · simp only [Nat.sub_self, pow_zero, one_mul]; exact hdens_le
      · simp only [Nat.sub_self, zero_mul, pow_zero, inv_one, mul_one]; exact hX_card
      · simp only [Nat.sub_self, pow_zero, one_mul]; exact hY_card

lemma M_rect2D_of_fuel_pos (maxIter : ℕ) {ε₂ : ℝ} (hε0 : 0 < ε₂) (D : ℕ) :
    0 < M_rect2D_of_fuel maxIter ε₂ D := by
  unfold M_rect2D_of_fuel goodRect2DStepFactor
  positivity

lemma M_rect2D_pos {ε₂ : ℝ} (hε0 : 0 < ε₂) (D : ℕ) : 0 < M_rect2D ε₂ D :=
  M_rect2D_of_fuel_pos (rRect2DFuel ε₂) hε0 D

lemma M_uncappedRect2D_pos {ε₂ : ℝ} (hε0 : 0 < ε₂) (D : ℕ) : 0 < M_uncappedRect2D ε₂ D :=
  M_rect2D_of_fuel_pos (rUncappedRect2DFuel ε₂ D) hε0 D

private lemma one_le_pow_density_boost {ε₂ : ℝ} (hε0 : 0 < ε₂) (n : ℕ) :
    1 ≤ (1 + ε₂ / 2) ^ n := by
  exact one_le_pow₀ (by linarith)

private lemma area_shrinkage_of_step_bounds_of_fuel {maxIter : ℕ} {ε₂ : ℝ} {D s_out steps_out : ℕ}
    {x_in y_in x_out y_out : ℝ}
    (hε0 : 0 < ε₂) (hε1 : ε₂ ≤ 1)
    (hx_in : 0 ≤ x_in) (hy_in : 0 ≤ y_in)
    (hsteps : steps_out ≤ maxIter)
    (hx : (1 / 3 : ℝ) * (((2 : ℝ) ^ (s_out * D))⁻¹) *
      (goodRect2DStepFactor ε₂ D) ^ steps_out * x_in ≤ x_out)
    (hy : (((2 : ℝ) ^ (2 * D))⁻¹) ^ steps_out * y_in ≤ y_out) :
    (((2 : ℝ) ^ (s_out * D))⁻¹) * (M_rect2D_of_fuel maxIter ε₂ D)⁻¹ * (x_in * y_in) ≤ x_out * y_out := by
  have hfac := goodRect2DStepFactor_bounds hε0 hε1 D
  have hfac_pos : 0 < goodRect2DStepFactor ε₂ D := hfac.1
  have hfac_le1 : goodRect2DStepFactor ε₂ D ≤ 1 := hfac.2.2
  have h2D_pos : (0 : ℝ) < ((2 : ℝ) ^ (2 * D))⁻¹ := by positivity
  have h2D_le1 : (((2 : ℝ) ^ (2 * D))⁻¹) ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hpow_fac : (goodRect2DStepFactor ε₂ D) ^ maxIter ≤
      (goodRect2DStepFactor ε₂ D) ^ steps_out :=
    pow_le_pow_of_le_one hfac_pos.le hfac_le1 hsteps
  have hpow_2D : (((2 : ℝ) ^ (2 * D))⁻¹) ^ maxIter ≤
      (((2 : ℝ) ^ (2 * D))⁻¹) ^ steps_out :=
    pow_le_pow_of_le_one h2D_pos.le h2D_le1 hsteps
  have hMinv : (M_rect2D_of_fuel maxIter ε₂ D)⁻¹ =
      (1 / 3 : ℝ) * (goodRect2DStepFactor ε₂ D) ^ maxIter *
        (((2 : ℝ) ^ (2 * D))⁻¹) ^ maxIter := by
    unfold M_rect2D_of_fuel
    rw [mul_inv, ← inv_pow, mul_inv, inv_inv, mul_pow]
    ring
  have hprod_pow :
      (goodRect2DStepFactor ε₂ D) ^ maxIter *
          (((2 : ℝ) ^ (2 * D))⁻¹) ^ maxIter ≤
        (goodRect2DStepFactor ε₂ D) ^ steps_out * (((2 : ℝ) ^ (2 * D))⁻¹) ^ steps_out :=
    mul_le_mul hpow_fac hpow_2D (by positivity) (by positivity)
  have hx_lhs_nonneg : 0 ≤ (1 / 3 : ℝ) * (((2 : ℝ) ^ (s_out * D))⁻¹) *
      (goodRect2DStepFactor ε₂ D) ^ steps_out * x_in := by positivity
  have hy_lhs_nonneg : 0 ≤ (((2 : ℝ) ^ (2 * D))⁻¹) ^ steps_out * y_in := by positivity
  calc
    (((2 : ℝ) ^ (s_out * D))⁻¹) * (M_rect2D_of_fuel maxIter ε₂ D)⁻¹ * (x_in * y_in)
      = (1 / 3 : ℝ) * (((2 : ℝ) ^ (s_out * D))⁻¹) * (x_in * y_in) *
          ((goodRect2DStepFactor ε₂ D) ^ maxIter *
            (((2 : ℝ) ^ (2 * D))⁻¹) ^ maxIter) := by
        rw [hMinv]; ring
    _ ≤ (1 / 3 : ℝ) * (((2 : ℝ) ^ (s_out * D))⁻¹) * (x_in * y_in) *
          ((goodRect2DStepFactor ε₂ D) ^ steps_out * (((2 : ℝ) ^ (2 * D))⁻¹) ^ steps_out) :=
        mul_le_mul_of_nonneg_left hprod_pow (by positivity)
    _ = ((1 / 3 : ℝ) * (((2 : ℝ) ^ (s_out * D))⁻¹) *
          (goodRect2DStepFactor ε₂ D) ^ steps_out * x_in) *
          ((((2 : ℝ) ^ (2 * D))⁻¹) ^ steps_out * y_in) := by ring
    _ ≤ x_out * y_out :=
        mul_le_mul hx hy hy_lhs_nonneg (hx_lhs_nonneg.trans hx)

private lemma area_shrinkage_of_step_bounds {ε₂ : ℝ} {D s_out steps_out : ℕ}
    {x_in y_in x_out y_out : ℝ}
    (hε0 : 0 < ε₂) (hε1 : ε₂ ≤ 1)
    (hx_in : 0 ≤ x_in) (hy_in : 0 ≤ y_in)
    (hsteps : steps_out ≤ rRect2DFuel ε₂)
    (hx : (1 / 3 : ℝ) * (((2 : ℝ) ^ (s_out * D))⁻¹) *
      (goodRect2DStepFactor ε₂ D) ^ steps_out * x_in ≤ x_out)
    (hy : (((2 : ℝ) ^ (2 * D))⁻¹) ^ steps_out * y_in ≤ y_out) :
    (((2 : ℝ) ^ (s_out * D))⁻¹) * (M_rect2D ε₂ D)⁻¹ * (x_in * y_in) ≤ x_out * y_out :=
  area_shrinkage_of_step_bounds_of_fuel hε0 hε1 hx_in hy_in hsteps hx hy

/-- **Specification of `cappedGoodRect` (`cappedGoodRect_spec`, `paper.tex` Algorithm 4 (`FindRect` / `Decompose2D`) &
Lemma 4.3 `\label{lem:find-rect}` & Theorem 4.4 `\label{thm:2d-decomp}`, §4.3)**:
When `max (((2 : ℝ) ^ D)⁻¹) α_low ≤ matDensity X Y A_rem` and `α_cap ≤ 2^{48} α_low` with
`α_low > 0`, `cappedGoodRect` returns `(X_out, Y_out, tag, s_out, steps_out)` satisfying:
1. $X_{\text{out}} \subseteq X$, $Y_{\text{out}} \subseteq Y$, both non-empty,
2. $\text{steps}_{\text{out}} \le \text{rRect2DFuel}(\varepsilon_2)$,
3. Density boost $\mathbb{E}[A_{\text{rem}}[X_{\text{out}}, Y_{\text{out}}]] \ge 2^{s_{\text{out}}} \mathbb{E}[A_{\text{rem}}[X, Y]]$,
4. Area shrinkage $|X_{\text{out}}||Y_{\text{out}}| \ge 2^{-s_{\text{out}} D} M_{\text{rect2D}}(\varepsilon_2, D)^{-1} |X||Y|$,
5. `tag = RectTag.regular ∨ tag = RectTag.aBoosted`,
6. If `tag = RectTag.aBoosted`, then $\mathbb{E}[A_{\text{rem}}[X_{\text{out}}, Y_{\text{out}}]] \ge \alpha_{\text{cap}}$,
7. If `tag = RectTag.regular`, then $\mathbb{E}[A_{\text{rem}}[X_{\text{out}}, Y_{\text{out}}]] < \alpha_{\text{cap}}$,
   $s_{\text{out}} \le 47$, and `restrictSubrect A_rem X_out Y_out` is $(\varepsilon_2, 2, D)$-grid-regular
   and $\varepsilon_2$-min-degree. -/
theorem cappedGoodRect_spec [DecidableEq α] [DecidableEq β]
    {X : Finset α} {Y : Finset β} {A_rem : α → β → ℝ} {ε₂ : ℝ} {D : ℕ} {α_low α_cap : ℝ}
    {oracleV : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → (α → ℝ)}
    (hX : X.Nonempty) (hY : Y.Nonempty) (hA : IsBinaryMatrix X Y A_rem)
    (hε0 : 0 < ε₂) (hε1 : ε₂ < 1) (hD : 2 ≤ D)
    (hα_low_pos : 0 < α_low)
    (hcap_le : α_cap ≤ (2 : ℝ) ^ (48 : ℕ) * α_low)
    (hA_ge : max (((2 : ℝ) ^ D)⁻¹) α_low ≤ matDensity X Y A_rem)
    (h_oracle : IsValidOracleV oracleV ε₂ D) :
    let res := cappedGoodRect X Y A_rem ε₂ D α_cap oracleV
    let X_out := res.1
    let Y_out := res.2.1
    let tag := res.2.2.1
    let s_out := res.2.2.2.1
    let steps_out := res.2.2.2.2
    X_out ⊆ X ∧ Y_out ⊆ Y ∧ X_out.Nonempty ∧ Y_out.Nonempty ∧
    steps_out ≤ rRect2DFuel ε₂ ∧
    (2 : ℝ) ^ s_out * matDensity X Y A_rem ≤ matDensity X_out Y_out A_rem ∧
    (((2 : ℝ) ^ (s_out * D))⁻¹) * (M_rect2D ε₂ D)⁻¹ * ((X.card : ℝ) * (Y.card : ℝ)) ≤
      (X_out.card : ℝ) * (Y_out.card : ℝ) ∧
    (tag = RectTag.regular ∨ tag = RectTag.aBoosted) ∧
    (tag = RectTag.aBoosted → α_cap ≤ matDensity X_out Y_out A_rem) ∧
    (tag = RectTag.regular →
      matDensity X_out Y_out A_rem < α_cap ∧
      s_out ≤ 47 ∧
      IsGridRegular X_out Y_out (restrictSubrect A_rem X_out Y_out) ε₂ 2 D ∧
      IsEpsMinDegree X_out Y_out (restrictSubrect A_rem X_out Y_out) ε₂) := by
  have hA_ge_2D : ((2 : ℝ) ^ D)⁻¹ ≤ matDensity X Y A_rem :=
    (le_max_left _ _).trans hA_ge
  have hA_ge_low : α_low ≤ matDensity X Y A_rem :=
    (le_max_right _ _).trans hA_ge
  have hpow48 := pow_rRect2DFuel_ge hε0
  have hfuel_cap :
      α_cap ≤ (1 + ε₂ / 2) ^ (rRect2DFuel ε₂) * matDensity X Y A_rem := by
    calc
      α_cap ≤ (2 : ℝ) ^ (48 : ℕ) * α_low := hcap_le
      _ ≤ (1 + ε₂ / 2) ^ (rRect2DFuel ε₂) * matDensity X Y A_rem :=
        mul_le_mul hpow48 hA_ge_low hα_low_pos.le (by positivity)
  have hloop := goodRectLoop_spec (rRect2DFuel ε₂) 0 0 hX hY hA hε0 hε1 hD hA_ge_2D h_oracle hfuel_cap
  unfold cappedGoodRect
  dsimp only at hloop ⊢
  rcases hloop with ⟨hsubX, hsubY, hneX, hneY, _, _, hsteps_hi,
    hdens_boost, hX_card, hY_card, htag, hboost, hreg⟩
  simp only [Nat.sub_zero, zero_add] at hsteps_hi hdens_boost hX_card hY_card
  have hpow_steps_ge1 :
      1 ≤ (1 + ε₂ / 2) ^
        (goodRectLoop (rRect2DFuel ε₂) X Y A_rem ε₂ D α_cap oracleV 0 0).2.2.2.2 :=
    one_le_pow_density_boost hε0 _
  have hdens_2s :
      (2 : ℝ) ^ (goodRectLoop (rRect2DFuel ε₂) X Y A_rem ε₂ D α_cap oracleV 0 0).2.2.2.1 *
        matDensity X Y A_rem ≤
      matDensity (goodRectLoop (rRect2DFuel ε₂) X Y A_rem ε₂ D α_cap oracleV 0 0).1
        (goodRectLoop (rRect2DFuel ε₂) X Y A_rem ε₂ D α_cap oracleV 0 0).2.1 A_rem := by
    calc
      (2 : ℝ) ^ (goodRectLoop (rRect2DFuel ε₂) X Y A_rem ε₂ D α_cap oracleV 0 0).2.2.2.1 *
          matDensity X Y A_rem
        = (2 : ℝ) ^ (goodRectLoop (rRect2DFuel ε₂) X Y A_rem ε₂ D α_cap oracleV 0 0).2.2.2.1 *
            1 * matDensity X Y A_rem := by ring
      _ ≤ (2 : ℝ) ^ (goodRectLoop (rRect2DFuel ε₂) X Y A_rem ε₂ D α_cap oracleV 0 0).2.2.2.1 *
            (1 + ε₂ / 2) ^
              (goodRectLoop (rRect2DFuel ε₂) X Y A_rem ε₂ D α_cap oracleV 0 0).2.2.2.2 *
            matDensity X Y A_rem := by
          refine mul_le_mul_of_nonneg_right ?_ (hα_low_pos.le.trans hA_ge_low)
          exact mul_le_mul_of_nonneg_left hpow_steps_ge1 (by positivity)
      _ ≤ _ := hdens_boost
  have harea := area_shrinkage_of_step_bounds hε0 hε1.le
    (Nat.cast_nonneg X.card) (Nat.cast_nonneg Y.card) hsteps_hi hX_card hY_card
  refine ⟨hsubX, hsubY, hneX, hneY, hsteps_hi, hdens_2s, harea, htag, hboost, ?_⟩
  intro htag_reg
  rcases hreg htag_reg with ⟨h_lt_cap, hgrid_reg, hmin_deg⟩
  have hs_le_47 :
      (goodRectLoop (rRect2DFuel ε₂) X Y A_rem ε₂ D α_cap oracleV 0 0).2.2.2.1 ≤ 47 := by
    have h_lo :
        (2 : ℝ) ^ (goodRectLoop (rRect2DFuel ε₂) X Y A_rem ε₂ D α_cap oracleV 0 0).2.2.2.1 * α_low ≤
        matDensity (goodRectLoop (rRect2DFuel ε₂) X Y A_rem ε₂ D α_cap oracleV 0 0).1
          (goodRectLoop (rRect2DFuel ε₂) X Y A_rem ε₂ D α_cap oracleV 0 0).2.1 A_rem := by
      calc
        (2 : ℝ) ^ (goodRectLoop (rRect2DFuel ε₂) X Y A_rem ε₂ D α_cap oracleV 0 0).2.2.2.1 * α_low
          ≤ (2 : ℝ) ^ (goodRectLoop (rRect2DFuel ε₂) X Y A_rem ε₂ D α_cap oracleV 0 0).2.2.2.1 *
              matDensity X Y A_rem :=
            mul_le_mul_of_nonneg_left hA_ge_low (by positivity)
        _ ≤ _ := hdens_2s
    have hpow_lt :
        (2 : ℝ) ^ (goodRectLoop (rRect2DFuel ε₂) X Y A_rem ε₂ D α_cap oracleV 0 0).2.2.2.1 * α_low <
          (2 : ℝ) ^ (48 : ℕ) * α_low :=
      lt_of_le_of_lt h_lo (lt_of_lt_of_le h_lt_cap hcap_le)
    have h2s_lt :
        (2 : ℝ) ^ (goodRectLoop (rRect2DFuel ε₂) X Y A_rem ε₂ D α_cap oracleV 0 0).2.2.2.1 <
          (2 : ℝ) ^ (48 : ℕ) :=
      lt_of_mul_lt_mul_right hpow_lt hα_low_pos.le
    by_contra h_gt
    have h48_le : 48 ≤ (goodRectLoop (rRect2DFuel ε₂) X Y A_rem ε₂ D α_cap oracleV 0 0).2.2.2.1 := by
      omega
    have hpow_ge :
        (2 : ℝ) ^ (48 : ℕ) ≤
          (2 : ℝ) ^ (goodRectLoop (rRect2DFuel ε₂) X Y A_rem ε₂ D α_cap oracleV 0 0).2.2.2.1 :=
      pow_le_pow_right₀ (by norm_num) h48_le
    linarith
  exact ⟨h_lt_cap, hs_le_47, hgrid_reg, hmin_deg⟩

/-- Base case `fuel = 0` for `aDecompositionLoop` with empty accumulator. -/
lemma aDecompositionLoop_zero [DecidableEq α] [DecidableEq β]
    (maxIter : ℕ) (X : Finset α) (Y : Finset β) (A_rem : α → β → ℝ)
    (ε₂ : ℝ) (D : ℕ) (ρ₂ α_cap : ℝ)
    (oracleV : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → (α → ℝ)) :
    aDecompositionLoop 0 maxIter X Y A_rem ε₂ D ρ₂ α_cap oracleV [] =
      [⟨X, Y, restrictSubrect A_rem X Y, RectTag.residual, 0⟩] := rfl

/-- Halting case `matDensity X Y A_rem ≤ ρ₂` for `aDecompositionLoop (fuel + 1)` with empty accumulator. -/
lemma aDecompositionLoop_of_le [DecidableEq α] [DecidableEq β]
    (fuel maxIter : ℕ) (X : Finset α) (Y : Finset β) (A_rem : α → β → ℝ)
    (ε₂ : ℝ) (D : ℕ) (ρ₂ α_cap : ℝ)
    (oracleV : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → (α → ℝ))
    (hle : matDensity X Y A_rem ≤ ρ₂) :
    aDecompositionLoop (fuel + 1) maxIter X Y A_rem ε₂ D ρ₂ α_cap oracleV [] =
      [⟨X, Y, restrictSubrect A_rem X Y, RectTag.residual, 0⟩] := by
  unfold aDecompositionLoop
  dsimp only
  rw [if_pos hle]
  rfl

/-- Accumulator shift identity for `aDecompositionLoop`. -/
lemma aDecompositionLoop_acc_eq [DecidableEq α] [DecidableEq β]
    (fuel maxIter : ℕ) (X : Finset α) (Y : Finset β) (A_rem : α → β → ℝ)
    (ε₂ : ℝ) (D : ℕ) (ρ₂ α_cap : ℝ)
    (oracleV : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → (α → ℝ))
    (acc : List (RectPiece α β)) :
    aDecompositionLoop fuel maxIter X Y A_rem ε₂ D ρ₂ α_cap oracleV acc =
      acc.reverse ++ aDecompositionLoop fuel maxIter X Y A_rem ε₂ D ρ₂ α_cap oracleV [] := by
  induction fuel generalizing A_rem acc with
  | zero =>
    unfold aDecompositionLoop
    simp
  | succ k ih =>
    unfold aDecompositionLoop
    dsimp only
    split_ifs with hlt
    · simp
    · rw [ih _ ( _ :: acc), ih _ [_]]
      simp [List.reverse_cons, List.append_assoc]

/-- Unfolding `aDecompositionLoop (fuel + 1)` with empty accumulator when `¬ matDensity X Y A_rem ≤ ρ₂`. -/
lemma aDecompositionLoop_cons_eq [DecidableEq α] [DecidableEq β]
    (fuel maxIter : ℕ) (X : Finset α) (Y : Finset β) (A_rem : α → β → ℝ)
    (ε₂ : ℝ) (D : ℕ) (ρ₂ α_cap : ℝ)
    (oracleV : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → (α → ℝ))
    (h_gt : ¬ matDensity X Y A_rem ≤ ρ₂) :
    let res := goodRectLoop maxIter X Y A_rem ε₂ D α_cap oracleV 0 0
    let piece_l : RectPiece α β := ⟨res.1, res.2.1, restrictSubrect A_rem res.1 res.2.1, res.2.2.1, res.2.2.2.1⟩
    let A_next := zeroOutSubrect A_rem res.1 res.2.1
    aDecompositionLoop (fuel + 1) maxIter X Y A_rem ε₂ D ρ₂ α_cap oracleV [] =
      piece_l :: aDecompositionLoop fuel maxIter X Y A_next ε₂ D ρ₂ α_cap oracleV [] := by
  dsimp only
  conv_lhs => unfold aDecompositionLoop
  dsimp only
  rw [if_neg h_gt, aDecompositionLoop_acc_eq]
  rfl

private lemma filter_singleton_residual_ne (X : Finset α) (Y : Finset β) (M : α → β → ℝ) :
    ([⟨X, Y, M, RectTag.residual, 0⟩] : List (RectPiece α β)).filter
      (fun P => P.tag ≠ RectTag.residual) = [] := by
  rw [List.filter_cons_of_neg]
  · rfl
  · simp

private lemma filter_singleton_residual_scale (X : Finset α) (Y : Finset β) (M : α → β → ℝ) (s : ℕ) :
    ([⟨X, Y, M, RectTag.residual, 0⟩] : List (RectPiece α β)).filter
      (fun P => P.tag ≠ RectTag.residual ∧ P.scale = s) = [] := by
  rw [List.filter_cons_of_neg]
  · rfl
  · simp

private lemma tag_ne_residual_of_reg_or_boost {t : RectTag}
    (ht : t = RectTag.regular ∨ t = RectTag.aBoosted) :
    t ≠ RectTag.residual := by
  rcases ht with rfl | rfl <;> intro h <;> cases h

/-- **First-Moment / Area-Mass Conservation Bound (`sum_extracted_area_le_initial_mass`,
`paper.tex` Section 4.3)**:
Across all non-residual pieces extracted by `aDecompositionLoop`, the sum of
$2^{\bar{s}_\ell} \rho_2 |X_\ell||Y_\ell|$ is bounded by the initial matrix mass
$|X||Y|\mathbb{E}[A_{\text{rem}}]$. -/
theorem sum_extracted_area_le_initial_mass [DecidableEq α] [DecidableEq β]
    (fuel maxIter : ℕ) {X : Finset α} {Y : Finset β} {A_rem : α → β → ℝ}
    {ε₂ : ℝ} {D : ℕ} {ρ₂ α_cap : ℝ}
    {oracleV : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → (α → ℝ)}
    (hX : X.Nonempty) (hY : Y.Nonempty) (hA : IsBinaryMatrix X Y A_rem)
    (hε0 : 0 < ε₂) (hε1 : ε₂ < 1) (hD : 2 ≤ D)
    (hρ_ge : ((2 : ℝ) ^ D)⁻¹ ≤ ρ₂)
    (h_oracle : IsValidOracleV oracleV ε₂ D)
    (hfuel_cap : α_cap ≤ (1 + ε₂ / 2) ^ maxIter * ρ₂) :
    let pieces := aDecompositionLoop fuel maxIter X Y A_rem ε₂ D ρ₂ α_cap oracleV []
    (((pieces.filter (fun P => P.tag ≠ RectTag.residual)).map
      (fun P => (2 : ℝ) ^ P.scale * ρ₂ * ((P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ)))).sum) ≤
      (X.card : ℝ) * (Y.card : ℝ) * matDensity X Y A_rem := by
  dsimp only
  have hX_pos : (0 : ℝ) < X.card := Nat.cast_pos.mpr hX.card_pos
  have hY_pos : (0 : ℝ) < Y.card := Nat.cast_pos.mpr hY.card_pos
  induction fuel generalizing A_rem with
  | zero =>
    rw [aDecompositionLoop_zero, filter_singleton_residual_ne, List.map_nil, List.sum_nil]
    have h_nonneg : 0 ≤ matDensity X Y A_rem := matDensity_nonneg_of_isBinaryMatrix_2D hA
    positivity
  | succ k ih =>
    by_cases hle : matDensity X Y A_rem ≤ ρ₂
    · rw [aDecompositionLoop_of_le k maxIter X Y A_rem ε₂ D ρ₂ α_cap oracleV hle,
        filter_singleton_residual_ne, List.map_nil, List.sum_nil]
      have h_nonneg : 0 ≤ matDensity X Y A_rem := matDensity_nonneg_of_isBinaryMatrix_2D hA
      positivity
    · have hgt : ρ₂ < matDensity X Y A_rem := not_le.mp hle
      have hA_ge : ((2 : ℝ) ^ D)⁻¹ ≤ matDensity X Y A_rem := hρ_ge.trans hgt.le
      have hfuel_A :
          α_cap ≤ (1 + ε₂ / 2) ^ maxIter * matDensity X Y A_rem :=
        hfuel_cap.trans (mul_le_mul_of_nonneg_left hgt.le (by positivity))
      have hloop := goodRectLoop_spec maxIter 0 0 hX hY hA hε0 hε1 hD hA_ge h_oracle hfuel_A
      dsimp only at hloop
      rcases hloop with ⟨hsubX, hsubY, _, _, _, _, _, hdens_boost, _, _, htag, _, _⟩
      simp only [Nat.sub_zero] at hdens_boost
      rw [aDecompositionLoop_cons_eq k maxIter X Y A_rem ε₂ D ρ₂ α_cap oracleV hle]
      set res := goodRectLoop maxIter X Y A_rem ε₂ D α_cap oracleV 0 0
      set piece_l : RectPiece α β := ⟨res.1, res.2.1, restrictSubrect A_rem res.1 res.2.1, res.2.2.1, res.2.2.2.1⟩
      set A_next := zeroOutSubrect A_rem res.1 res.2.1
      have htag_ne : piece_l.tag ≠ RectTag.residual := tag_ne_residual_of_reg_or_boost htag
      have hA_next : IsBinaryMatrix X Y A_next := IsBinaryMatrix.zeroOut hA
      have h_ih := ih hA_next
      have hpow_ge1 : 1 ≤ (1 + ε₂ / 2) ^ res.2.2.2.2 :=
        one_le_pow_density_boost hε0 _
      have h_piece_dens : (2 : ℝ) ^ res.2.2.2.1 * ρ₂ ≤ matDensity res.1 res.2.1 A_rem := by
        calc
          (2 : ℝ) ^ res.2.2.2.1 * ρ₂
            ≤ (2 : ℝ) ^ res.2.2.2.1 * 1 * matDensity X Y A_rem := by
              rw [mul_one]
              exact mul_le_mul_of_nonneg_left hgt.le (by positivity)
          _ ≤ (2 : ℝ) ^ res.2.2.2.1 * (1 + ε₂ / 2) ^ res.2.2.2.2 *
                matDensity X Y A_rem := by
              refine mul_le_mul_of_nonneg_right ?_ (le_trans (by positivity) hA_ge)
              exact mul_le_mul_of_nonneg_left hpow_ge1 (by positivity)
          _ ≤ matDensity res.1 res.2.1 A_rem := hdens_boost
      have hdec := matDensity_zeroOutSubrect_eq A_rem hX hY hsubX hsubY
      have h_mass_eq :
          (X.card : ℝ) * (Y.card : ℝ) * matDensity X Y A_next +
            (res.1.card : ℝ) * (res.2.1.card : ℝ) * matDensity res.1 res.2.1 A_rem =
          (X.card : ℝ) * (Y.card : ℝ) * matDensity X Y A_rem := by
        dsimp only [A_next]
        rw [hdec]
        field_simp [hX_pos.ne', hY_pos.ne']
        ring
      have h_piece_mass :
          (2 : ℝ) ^ piece_l.scale * ρ₂ * ((piece_l.X_sub.card : ℝ) * (piece_l.Y_sub.card : ℝ)) ≤
            (res.1.card : ℝ) * (res.2.1.card : ℝ) * matDensity res.1 res.2.1 A_rem := by
        dsimp only [piece_l]
        calc
          (2 : ℝ) ^ res.2.2.2.1 * ρ₂ * ((res.1.card : ℝ) * (res.2.1.card : ℝ))
            = ((res.1.card : ℝ) * (res.2.1.card : ℝ)) * ((2 : ℝ) ^ res.2.2.2.1 * ρ₂) := by ring
          _ ≤ ((res.1.card : ℝ) * (res.2.1.card : ℝ)) * matDensity res.1 res.2.1 A_rem :=
              mul_le_mul_of_nonneg_left h_piece_dens (by positivity)
          _ = (res.1.card : ℝ) * (res.2.1.card : ℝ) * matDensity res.1 res.2.1 A_rem := by ring
      rw [List.filter_cons, if_pos (decide_eq_true htag_ne), List.map_cons, List.sum_cons]
      linarith

/-- Inductive bound on the number of extracted pieces at scale `s` in `aDecompositionLoop`
for arbitrary inner step budget `maxIter`. -/
lemma aDecompositionLoop_scale_count_bound_of_fuel [DecidableEq α] [DecidableEq β]
    (fuel maxIter : ℕ) (s : ℕ) {X : Finset α} {Y : Finset β} {A_rem : α → β → ℝ}
    {ε₂ : ℝ} {D : ℕ} {ρ₂ α_cap : ℝ}
    {oracleV : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → (α → ℝ)}
    (hX : X.Nonempty) (hY : Y.Nonempty) (hA : IsBinaryMatrix X Y A_rem)
    (hε0 : 0 < ε₂) (hε1 : ε₂ < 1) (hD : 2 ≤ D)
    (hρ_ge : ((2 : ℝ) ^ D)⁻¹ ≤ ρ₂)
    (h_oracle : IsValidOracleV oracleV ε₂ D)
    (hfuel_cap : α_cap ≤ (1 + ε₂ / 2) ^ maxIter * ρ₂) :
    let pieces := aDecompositionLoop fuel maxIter X Y A_rem ε₂ D ρ₂ α_cap oracleV []
    let L_s := (pieces.filter (fun P => P.tag ≠ RectTag.residual ∧ P.scale = s)).length
    (L_s : ℝ) * ((((2 : ℝ) ^ (s * D))⁻¹) * (M_rect2D_of_fuel maxIter ε₂ D)⁻¹ * ((2 : ℝ) ^ s * ρ₂)) ≤
      matDensity X Y A_rem := by
  dsimp only
  have hX_pos : (0 : ℝ) < X.card := Nat.cast_pos.mpr hX.card_pos
  have hY_pos : (0 : ℝ) < Y.card := Nat.cast_pos.mpr hY.card_pos
  induction fuel generalizing A_rem with
  | zero =>
    rw [aDecompositionLoop_zero, filter_singleton_residual_scale, List.length_nil,
      Nat.cast_zero, zero_mul]
    exact matDensity_nonneg_of_isBinaryMatrix_2D hA
  | succ k ih =>
    by_cases hle : matDensity X Y A_rem ≤ ρ₂
    · rw [aDecompositionLoop_of_le k maxIter X Y A_rem ε₂ D ρ₂ α_cap oracleV hle,
        filter_singleton_residual_scale, List.length_nil, Nat.cast_zero, zero_mul]
      exact matDensity_nonneg_of_isBinaryMatrix_2D hA
    · have hgt : ρ₂ < matDensity X Y A_rem := not_le.mp hle
      have hA_ge : ((2 : ℝ) ^ D)⁻¹ ≤ matDensity X Y A_rem := hρ_ge.trans hgt.le
      have hfuel_A :
          α_cap ≤ (1 + ε₂ / 2) ^ maxIter * matDensity X Y A_rem :=
        hfuel_cap.trans (mul_le_mul_of_nonneg_left hgt.le (by positivity))
      have hloop := goodRectLoop_spec maxIter 0 0 hX hY hA hε0 hε1 hD hA_ge h_oracle hfuel_A
      dsimp only at hloop
      rcases hloop with ⟨hsubX, hsubY, _, _, _, _, hsteps_hi,
        hdens_boost, hX_card, hY_card, htag, _, _⟩
      simp only [Nat.sub_zero, zero_add] at hsteps_hi hdens_boost hX_card hY_card
      rw [aDecompositionLoop_cons_eq k maxIter X Y A_rem ε₂ D ρ₂ α_cap oracleV hle]
      set res := goodRectLoop maxIter X Y A_rem ε₂ D α_cap oracleV 0 0
      set piece_l : RectPiece α β := ⟨res.1, res.2.1, restrictSubrect A_rem res.1 res.2.1, res.2.2.1, res.2.2.2.1⟩
      set A_next := zeroOutSubrect A_rem res.1 res.2.1
      have htag_ne : piece_l.tag ≠ RectTag.residual := tag_ne_residual_of_reg_or_boost htag
      have hA_next : IsBinaryMatrix X Y A_next := IsBinaryMatrix.zeroOut hA
      have h_ih := ih hA_next
      have hdec := matDensity_zeroOutSubrect_eq A_rem hX hY hsubX hsubY
      have h_dens_res_nonneg : 0 ≤ matDensity res.1 res.2.1 A_rem :=
        matDensity_nonneg_of_isBinaryMatrix_2D (isBinaryMatrix_subset_2D hsubX hsubY hA)
      have h_next_le : matDensity X Y A_next ≤ matDensity X Y A_rem := by
        dsimp only [A_next]
        rw [hdec]
        have : 0 ≤ ((res.1.card : ℝ) / (X.card : ℝ)) * ((res.2.1.card : ℝ) / (Y.card : ℝ)) *
            matDensity res.1 res.2.1 A_rem := by positivity
        linarith
      by_cases hs : piece_l.scale = s
      · have hcond : piece_l.tag ≠ RectTag.residual ∧ piece_l.scale = s := ⟨htag_ne, hs⟩
        rw [List.filter_cons, if_pos (decide_eq_true hcond), List.length_cons, Nat.cast_add,
          Nat.cast_one]
        have harea := area_shrinkage_of_step_bounds_of_fuel hε0 hε1.le
          (Nat.cast_nonneg X.card) (Nat.cast_nonneg Y.card) hsteps_hi hX_card hY_card
        have h_area_ratio :
            (((2 : ℝ) ^ (s * D))⁻¹) * (M_rect2D_of_fuel maxIter ε₂ D)⁻¹ ≤
              ((res.1.card : ℝ) / (X.card : ℝ)) * ((res.2.1.card : ℝ) / (Y.card : ℝ)) := by
          have hs_eq : res.2.2.2.1 = s := hs
          rw [hs_eq] at harea
          rw [div_mul_div_comm, le_div_iff₀ (mul_pos hX_pos hY_pos)]
          exact harea
        have hpow_ge1 : 1 ≤ (1 + ε₂ / 2) ^ res.2.2.2.2 :=
          one_le_pow_density_boost hε0 _
        have h_piece_dens : (2 : ℝ) ^ s * ρ₂ ≤ matDensity res.1 res.2.1 A_rem := by
          have hs_eq : res.2.2.2.1 = s := hs
          rw [← hs_eq]
          calc
            (2 : ℝ) ^ res.2.2.2.1 * ρ₂
              ≤ (2 : ℝ) ^ res.2.2.2.1 * 1 * matDensity X Y A_rem := by
                rw [mul_one]
                exact mul_le_mul_of_nonneg_left hgt.le (by positivity)
            _ ≤ (2 : ℝ) ^ res.2.2.2.1 * (1 + ε₂ / 2) ^ res.2.2.2.2 *
                  matDensity X Y A_rem := by
                refine mul_le_mul_of_nonneg_right ?_ (le_trans (by positivity) hA_ge)
                exact mul_le_mul_of_nonneg_left hpow_ge1 (by positivity)
            _ ≤ matDensity res.1 res.2.1 A_rem := hdens_boost
        have h_unit_le_dec :
            (((2 : ℝ) ^ (s * D))⁻¹) * (M_rect2D_of_fuel maxIter ε₂ D)⁻¹ * ((2 : ℝ) ^ s * ρ₂) ≤
              matDensity X Y A_rem - matDensity X Y A_next := by
          have hM_pos : 0 < M_rect2D_of_fuel maxIter ε₂ D := M_rect2D_of_fuel_pos maxIter hε0 D
          have hρ_pos : 0 < ρ₂ := lt_of_lt_of_le (by positivity) hρ_ge
          have hmul := mul_le_mul h_area_ratio h_piece_dens
            (by positivity) (by positivity)
          dsimp only [A_next]
          linarith [hdec, hmul]
        linarith
      · simp only [List.filter_cons, hs, and_false, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact h_ih.trans h_next_le

/-- Inductive bound on the number of extracted pieces at scale `s` in `aDecompositionLoop`
when `maxIter = rRect2DFuel ε₂`. -/
lemma aDecompositionLoop_scale_count_bound [DecidableEq α] [DecidableEq β]
    (fuel : ℕ) (s : ℕ) {X : Finset α} {Y : Finset β} {A_rem : α → β → ℝ}
    {ε₂ : ℝ} {D : ℕ} {ρ₂ α_cap : ℝ}
    {oracleV : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → (α → ℝ)}
    (hX : X.Nonempty) (hY : Y.Nonempty) (hA : IsBinaryMatrix X Y A_rem)
    (hε0 : 0 < ε₂) (hε1 : ε₂ < 1) (hD : 2 ≤ D)
    (hρ_ge : ((2 : ℝ) ^ D)⁻¹ ≤ ρ₂)
    (h_oracle : IsValidOracleV oracleV ε₂ D)
    (hfuel_cap : α_cap ≤ (1 + ε₂ / 2) ^ (rRect2DFuel ε₂) * ρ₂) :
    let pieces := aDecompositionLoop fuel (rRect2DFuel ε₂) X Y A_rem ε₂ D ρ₂ α_cap oracleV []
    let L_s := (pieces.filter (fun P => P.tag ≠ RectTag.residual ∧ P.scale = s)).length
    (L_s : ℝ) * ((((2 : ℝ) ^ (s * D))⁻¹) * (M_rect2D ε₂ D)⁻¹ * ((2 : ℝ) ^ s * ρ₂)) ≤
      matDensity X Y A_rem :=
  aDecompositionLoop_scale_count_bound_of_fuel fuel (rRect2DFuel ε₂) s
    hX hY hA hε0 hε1 hD hρ_ge h_oracle hfuel_cap

/-- Inductive residual sparsity invariant for `aDecompositionLoop`
(`paper.tex` Algorithm 4 (`FindRect` / `Decompose2D`) & Theorem 4.4 `\label{thm:2d-decomp}` Clause 4, §4.3):
Whenever `matDensity X Y A_rem * ((2 : ℝ) ^ (D + D ^ 2) * M_rect2D_of_fuel maxIter ε₂ D) ≤ (fuel : ℝ)`,
every residual piece `P` in `aDecompositionLoop fuel maxIter X Y A_rem ε₂ D ρ₂ α_cap oracleV []`
satisfies `P.X_sub = X`, `P.Y_sub = Y`, and `matDensity X Y P.A_sub ≤ ρ₂`. -/
lemma aDecompositionLoop_residual_density_le_aux_of_fuel [DecidableEq α] [DecidableEq β]
    (fuel maxIter : ℕ) {X : Finset α} {Y : Finset β} {A_rem : α → β → ℝ}
    {ε₂ : ℝ} {D : ℕ} {ρ₂ α_cap : ℝ}
    {oracleV : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → (α → ℝ)}
    (hX : X.Nonempty) (hY : Y.Nonempty) (hA : IsBinaryMatrix X Y A_rem)
    (hε0 : 0 < ε₂) (hε1 : ε₂ < 1) (hD : 2 ≤ D)
    (hρ_ge : ((2 : ℝ) ^ D)⁻¹ ≤ ρ₂)
    (h_oracle : IsValidOracleV oracleV ε₂ D)
    (hfuel_cap : α_cap ≤ (1 + ε₂ / 2) ^ maxIter * ρ₂)
    (hfuel : matDensity X Y A_rem * ((2 : ℝ) ^ (D + D ^ 2) * M_rect2D_of_fuel maxIter ε₂ D) ≤ (fuel : ℝ)) :
    ∀ P ∈ aDecompositionLoop fuel maxIter X Y A_rem ε₂ D ρ₂ α_cap oracleV [],
      P.tag = RectTag.residual →
        P.X_sub = X ∧ P.Y_sub = Y ∧ matDensity X Y P.A_sub ≤ ρ₂ := by
  have hX_pos : (0 : ℝ) < X.card := Nat.cast_pos.mpr hX.card_pos
  have hY_pos : (0 : ℝ) < Y.card := Nat.cast_pos.mpr hY.card_pos
  have hM_pos : 0 < M_rect2D_of_fuel maxIter ε₂ D := M_rect2D_of_fuel_pos maxIter hε0 D
  have hρ_pos : 0 < ρ₂ := lt_of_lt_of_le (by positivity) hρ_ge
  induction fuel generalizing A_rem with
  | zero =>
    intro P hP _
    rw [aDecompositionLoop_zero, List.mem_singleton] at hP
    subst hP
    dsimp only
    rw [matDensity_restrictSubrect_eq]
    simp only [Nat.cast_zero] at hfuel
    have hfac_pos : 0 < (2 : ℝ) ^ (D + D ^ 2) * M_rect2D_of_fuel maxIter ε₂ D := by positivity
    have hA_le0 : matDensity X Y A_rem ≤ 0 := nonpos_of_mul_nonpos_left hfuel hfac_pos
    exact ⟨rfl, rfl, hA_le0.trans hρ_pos.le⟩
  | succ k ih =>
    intro P hP hP_res
    by_cases hle : matDensity X Y A_rem ≤ ρ₂
    · rw [aDecompositionLoop_of_le k maxIter X Y A_rem ε₂ D ρ₂ α_cap oracleV hle,
        List.mem_singleton] at hP
      subst hP
      dsimp only
      rw [matDensity_restrictSubrect_eq]
      exact ⟨rfl, rfl, hle⟩
    · have hgt : ρ₂ < matDensity X Y A_rem := not_le.mp hle
      have hA_ge : ((2 : ℝ) ^ D)⁻¹ ≤ matDensity X Y A_rem := hρ_ge.trans hgt.le
      have hfuel_A :
          α_cap ≤ (1 + ε₂ / 2) ^ maxIter * matDensity X Y A_rem :=
        hfuel_cap.trans (mul_le_mul_of_nonneg_left hgt.le (by positivity))
      have hloop := goodRectLoop_spec maxIter 0 0 hX hY hA hε0 hε1 hD hA_ge h_oracle hfuel_A
      dsimp only at hloop
      rcases hloop with ⟨hsubX, hsubY, _, _, _, _, hsteps_hi,
        hdens_boost, hX_card, hY_card, htag, _, _⟩
      simp only [Nat.sub_zero, zero_add] at hsteps_hi hdens_boost hX_card hY_card
      rw [aDecompositionLoop_cons_eq k maxIter X Y A_rem ε₂ D ρ₂ α_cap oracleV hle] at hP
      set res := goodRectLoop maxIter X Y A_rem ε₂ D α_cap oracleV 0 0
      set piece_l : RectPiece α β := ⟨res.1, res.2.1, restrictSubrect A_rem res.1 res.2.1, res.2.2.1, res.2.2.2.1⟩
      set A_next := zeroOutSubrect A_rem res.1 res.2.1
      have htag_ne : piece_l.tag ≠ RectTag.residual := tag_ne_residual_of_reg_or_boost htag
      simp only [List.mem_cons] at hP
      rcases hP with rfl | hP_tail
      · exact False.elim (htag_ne hP_res)
      · have hA_next : IsBinaryMatrix X Y A_next := IsBinaryMatrix.zeroOut hA
        apply ih hA_next ?_ P hP_tail hP_res
        have hpow_ge1 : 1 ≤ (1 + ε₂ / 2) ^ res.2.2.2.2 :=
          one_le_pow_density_boost hε0 _
        have h_piece_dens : (2 : ℝ) ^ res.2.2.2.1 * ((2 : ℝ) ^ D)⁻¹ ≤ matDensity res.1 res.2.1 A_rem := by
          calc
            (2 : ℝ) ^ res.2.2.2.1 * ((2 : ℝ) ^ D)⁻¹
              ≤ (2 : ℝ) ^ res.2.2.2.1 * 1 * matDensity X Y A_rem := by
                rw [mul_one]
                exact mul_le_mul_of_nonneg_left hA_ge (by positivity)
            _ ≤ (2 : ℝ) ^ res.2.2.2.1 * (1 + ε₂ / 2) ^ res.2.2.2.2 *
                  matDensity X Y A_rem := by
                refine mul_le_mul_of_nonneg_right ?_ (le_trans (by positivity) hA_ge)
                exact mul_le_mul_of_nonneg_left hpow_ge1 (by positivity)
            _ ≤ matDensity res.1 res.2.1 A_rem := hdens_boost
        have hs_le_D : res.2.2.2.1 ≤ D := by
          have hdens_le_1 : matDensity res.1 res.2.1 A_rem ≤ 1 :=
            matDensity_le_one_of_isBinaryMatrix_2D (isBinaryMatrix_subset_2D hsubX hsubY hA)
          have h1 : (2 : ℝ) ^ res.2.2.2.1 * ((2 : ℝ) ^ D)⁻¹ ≤ 1 := h_piece_dens.trans hdens_le_1
          have h2 : (2 : ℝ) ^ D * ((2 : ℝ) ^ D)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
          have hle_pow : (2 : ℝ) ^ res.2.2.2.1 ≤ (2 : ℝ) ^ D := by
            by_contra! hgt_pow
            have hmul := mul_lt_mul_of_pos_right hgt_pow (by positivity : (0 : ℝ) < ((2 : ℝ) ^ D)⁻¹)
            linarith
          exact (pow_le_pow_iff_right₀ (by norm_num)).mp hle_pow
        have hSD_le : res.2.2.2.1 * D ≤ D ^ 2 := by
          rw [sq]
          exact Nat.mul_le_mul_right D hs_le_D
        have h_inv_SD : (((2 : ℝ) ^ (D ^ 2))⁻¹) ≤ (((2 : ℝ) ^ (res.2.2.2.1 * D))⁻¹) :=
          inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hSD_le)
        have h2s_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ res.2.2.2.1 := one_le_pow₀ (by norm_num)
        have h_dens_2D : ((2 : ℝ) ^ D)⁻¹ ≤ matDensity res.1 res.2.1 A_rem := by
          have h1 : 1 * ((2 : ℝ) ^ D)⁻¹ ≤ (2 : ℝ) ^ res.2.2.2.1 * ((2 : ℝ) ^ D)⁻¹ :=
            mul_le_mul_of_nonneg_right h2s_ge1 (by positivity)
          linarith
        have harea := area_shrinkage_of_step_bounds_of_fuel hε0 hε1.le
          (Nat.cast_nonneg X.card) (Nat.cast_nonneg Y.card) hsteps_hi hX_card hY_card
        have h_area_ratio :
            (((2 : ℝ) ^ (D ^ 2))⁻¹) * (M_rect2D_of_fuel maxIter ε₂ D)⁻¹ ≤
              ((res.1.card : ℝ) / (X.card : ℝ)) * ((res.2.1.card : ℝ) / (Y.card : ℝ)) := by
          have h0 :
              (((2 : ℝ) ^ (D ^ 2))⁻¹) * (M_rect2D_of_fuel maxIter ε₂ D)⁻¹ ≤
                (((2 : ℝ) ^ (res.2.2.2.1 * D))⁻¹) * (M_rect2D_of_fuel maxIter ε₂ D)⁻¹ :=
            mul_le_mul_of_nonneg_right h_inv_SD (by positivity)
          refine h0.trans ?_
          rw [div_mul_div_comm, le_div_iff₀ (mul_pos hX_pos hY_pos)]
          exact harea
        have hdec := matDensity_zeroOutSubrect_eq A_rem hX hY hsubX hsubY
        have h_drop :
            (((2 : ℝ) ^ (D ^ 2))⁻¹) * (M_rect2D_of_fuel maxIter ε₂ D)⁻¹ * ((2 : ℝ) ^ D)⁻¹ ≤
              matDensity X Y A_rem - matDensity X Y A_next := by
          have hmul := mul_le_mul h_area_ratio h_dens_2D (by positivity) (by positivity)
          dsimp only [A_next]
          linarith [hdec, hmul]
        have h_step1 :
            1 ≤ (matDensity X Y A_rem - matDensity X Y A_next) *
              ((2 : ℝ) ^ (D + D ^ 2) * M_rect2D_of_fuel maxIter ε₂ D) := by
          have hmul := mul_le_mul_of_nonneg_right h_drop
            (by positivity : 0 ≤ (2 : ℝ) ^ (D + D ^ 2) * M_rect2D_of_fuel maxIter ε₂ D)
          have h_id :
              ((((2 : ℝ) ^ (D ^ 2))⁻¹) * (M_rect2D_of_fuel maxIter ε₂ D)⁻¹ * ((2 : ℝ) ^ D)⁻¹) *
                ((2 : ℝ) ^ (D + D ^ 2) * M_rect2D_of_fuel maxIter ε₂ D) = 1 := by
            have h2D : (2 : ℝ) ^ D ≠ 0 := by positivity
            have h2D2 : (2 : ℝ) ^ (D ^ 2) ≠ 0 := by positivity
            rw [pow_add]
            field_simp [h2D, h2D2, hM_pos.ne']
          rwa [h_id] at hmul
        push_cast at hfuel
        linarith

/-- Inductive residual sparsity invariant for `aDecompositionLoop` when `maxIter = rRect2DFuel ε₂`. -/
lemma aDecompositionLoop_residual_density_le_aux [DecidableEq α] [DecidableEq β]
    (fuel : ℕ) {X : Finset α} {Y : Finset β} {A_rem : α → β → ℝ}
    {ε₂ : ℝ} {D : ℕ} {ρ₂ α_cap : ℝ}
    {oracleV : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → (α → ℝ)}
    (hX : X.Nonempty) (hY : Y.Nonempty) (hA : IsBinaryMatrix X Y A_rem)
    (hε0 : 0 < ε₂) (hε1 : ε₂ < 1) (hD : 2 ≤ D)
    (hρ_ge : ((2 : ℝ) ^ D)⁻¹ ≤ ρ₂)
    (h_oracle : IsValidOracleV oracleV ε₂ D)
    (hfuel_cap : α_cap ≤ (1 + ε₂ / 2) ^ (rRect2DFuel ε₂) * ρ₂)
    (hfuel : matDensity X Y A_rem * ((2 : ℝ) ^ (D + D ^ 2) * M_rect2D ε₂ D) ≤ (fuel : ℝ)) :
    ∀ P ∈ aDecompositionLoop fuel (rRect2DFuel ε₂) X Y A_rem ε₂ D ρ₂ α_cap oracleV [],
      P.tag = RectTag.residual →
        P.X_sub = X ∧ P.Y_sub = Y ∧ matDensity X Y P.A_sub ≤ ρ₂ :=
  aDecompositionLoop_residual_density_le_aux_of_fuel fuel (rRect2DFuel ε₂)
    hX hY hA hε0 hε1 hD hρ_ge h_oracle hfuel_cap hfuel

/-- Residual sparsity bound for `aDecompositionLoop` when `rDecomp2DFuel ε₂ D ≤ fuel`. -/
lemma aDecompositionLoop_residual_density_le [DecidableEq α] [DecidableEq β]
    (fuel : ℕ) {X : Finset α} {Y : Finset β} {A_rem : α → β → ℝ}
    {ε₂ : ℝ} {D : ℕ} {ρ₂ α_cap : ℝ}
    {oracleV : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → (α → ℝ)}
    (hX : X.Nonempty) (hY : Y.Nonempty) (hA : IsBinaryMatrix X Y A_rem)
    (hε0 : 0 < ε₂) (hε1 : ε₂ < 1) (hD : 2 ≤ D)
    (hρ_ge : ((2 : ℝ) ^ D)⁻¹ ≤ ρ₂)
    (h_oracle : IsValidOracleV oracleV ε₂ D)
    (hfuel_cap : α_cap ≤ (1 + ε₂ / 2) ^ (rRect2DFuel ε₂) * ρ₂)
    (hfuel_ge : rDecomp2DFuel ε₂ D ≤ fuel) :
    ∀ P ∈ aDecompositionLoop fuel (rRect2DFuel ε₂) X Y A_rem ε₂ D ρ₂ α_cap oracleV [],
      P.tag = RectTag.residual →
        P.X_sub = X ∧ P.Y_sub = Y ∧ matDensity X Y P.A_sub ≤ ρ₂ := by
  have hA_le1 : matDensity X Y A_rem ≤ 1 := matDensity_le_one_of_isBinaryMatrix_2D hA
  have hM_pos : 0 < M_rect2D ε₂ D := M_rect2D_pos hε0 D
  have hfuel : matDensity X Y A_rem * ((2 : ℝ) ^ (D + D ^ 2) * M_rect2D ε₂ D) ≤ (fuel : ℝ) := by
    have h1 : matDensity X Y A_rem * ((2 : ℝ) ^ (D + D ^ 2) * M_rect2D ε₂ D) ≤
        1 * ((2 : ℝ) ^ (D + D ^ 2) * M_rect2D ε₂ D) :=
      mul_le_mul_of_nonneg_right hA_le1 (by positivity)
    have h2 : (2 : ℝ) ^ (D + D ^ 2) * M_rect2D ε₂ D ≤
        (Nat.ceil ((2 : ℝ) ^ (D + D ^ 2) * M_rect2D ε₂ D) : ℝ) := Nat.le_ceil _
    have h3 : (Nat.ceil ((2 : ℝ) ^ (D + D ^ 2) * M_rect2D ε₂ D) : ℝ) ≤ (rDecomp2DFuel ε₂ D : ℝ) := by
      unfold rDecomp2DFuel
      exact_mod_cast Nat.le_succ _
    have h4 : (rDecomp2DFuel ε₂ D : ℝ) ≤ (fuel : ℝ) := by exact_mod_cast hfuel_ge
    linarith
  exact aDecompositionLoop_residual_density_le_aux fuel hX hY hA hε0 hε1 hD hρ_ge h_oracle hfuel_cap hfuel

/-- **Theorem 4.4 Clauses 1–4 (`thm_2d_decomp_regularity_and_shrinkage`, `\label{thm:2d-decomp}`, §4.3 of `paper.tex`)**:
Full regularity, shrinkage, and piece-count specification for `cappedADecomposition`
(Algorithm 4 (`FindRect` / `Decompose2D`)):
For `pieces := cappedADecomposition fuel X Y A ε₂ D α_low α_cap oracleV`:
1. **Exact Matrix Partition**: For all $x \in X, y \in Y$, $\sum_{P \in \text{pieces}} P.A_{\text{sub}}(x, y) = A(x, y)$.
2. **Valid Binary Sub-Rectangles & Residual Sparsity**: Every piece $P \in \text{pieces}$ has
   $P.X_{\text{sub}} \subseteq X$, $P.Y_{\text{sub}} \subseteq Y$, both non-empty,
   `IsBinaryMatrix P.X_sub P.Y_sub P.A_sub`, and when `rDecomp2DFuel ε₂ D ≤ fuel`, any residual piece
   ($P.\text{tag} = \text{RectTag.residual}$) satisfies $\mathbb{E}_{X \times Y}[P.A_{\text{sub}}] \le \tau_{\text{low}}$.
3. **Extracted Piece Regularity & Shrinkage**: Every non-residual piece $P \in \text{pieces}$
   ($P.\text{tag} \ne \text{RectTag.residual}$) satisfies:
   - $P.\text{tag} = \text{RectTag.regular} \lor P.\text{tag} = \text{RectTag.aBoosted}$,
   - $\mathbb{E}[P.A_{\text{sub}}] \ge 2^{P.\text{scale}} \max(2^{-D}, \alpha_{\text{low}})$,
   - $|P.X_{\text{sub}}||P.Y_{\text{sub}}| \ge 2^{-P.\text{scale} \cdot D} M_{\text{rect2D}}(\varepsilon_2, D)^{-1} |X||Y|$,
   - If $P.\text{tag} = \text{RectTag.aBoosted}$, then $\mathbb{E}[P.A_{\text{sub}}] \ge \alpha_{\text{cap}}$,
   - If $P.\text{tag} = \text{RectTag.regular}$, then $\mathbb{E}[P.A_{\text{sub}}] < \alpha_{\text{cap}}$,
     $P.\text{scale} \le 47$, and $P.A_{\text{sub}}$ is $(\varepsilon_2, 2, D)$-grid-regular and
     $\varepsilon_2$-min-degree on $P.X_{\text{sub}} \times P.Y_{\text{sub}}$.
4. **Per-Scale Piece Count Bound (`\label{thm:2d-decomp}`)**: For every scale $s \in \mathbb{N}$,
   the number $L_s$ of non-residual pieces at scale $s$ satisfies
   $L_s \le M_{\text{rect2D}}(\varepsilon_2, D) \tau_{\text{low}}^{-1} 2^{s D} \mathbb{E}[A]
     \le 2^D M_{\text{rect2D}}(\varepsilon_2, D) 2^{s D}$. -/
theorem thm_2d_decomp_regularity_and_shrinkage [DecidableEq α] [DecidableEq β]
    (fuel : ℕ) {X : Finset α} {Y : Finset β} {A : α → β → ℝ}
    {ε₂ : ℝ} {D : ℕ} {α_low α_cap : ℝ}
    {oracleV : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → (α → ℝ)}
    (hX : X.Nonempty) (hY : Y.Nonempty) (hA : IsBinaryMatrix X Y A)
    (hε0 : 0 < ε₂) (hε1 : ε₂ < 1) (hD : 2 ≤ D)
    (hα_low_pos : 0 < α_low)
    (hcap_le : α_cap ≤ (2 : ℝ) ^ (48 : ℕ) * α_low)
    (h_oracle : IsValidOracleV oracleV ε₂ D) :
    let pieces := cappedADecomposition fuel X Y A ε₂ D α_low α_cap oracleV
    let τ_low := max (((2 : ℝ) ^ D)⁻¹) α_low
    (∀ x ∈ X, ∀ y ∈ Y, ((pieces.map (fun P => P.A_sub x y)).sum) = A x y) ∧
    (∀ P ∈ pieces,
      P.X_sub ⊆ X ∧ P.Y_sub ⊆ Y ∧ P.X_sub.Nonempty ∧ P.Y_sub.Nonempty ∧
      IsBinaryMatrix P.X_sub P.Y_sub P.A_sub ∧
      (rDecomp2DFuel ε₂ D ≤ fuel → P.tag = RectTag.residual →
        matDensity X Y P.A_sub ≤ τ_low) ∧
      (P.tag ≠ RectTag.residual →
        (P.tag = RectTag.regular ∨ P.tag = RectTag.aBoosted) ∧
        (2 : ℝ) ^ P.scale * τ_low ≤ matDensity P.X_sub P.Y_sub P.A_sub ∧
        (((2 : ℝ) ^ (P.scale * D))⁻¹) * (M_rect2D ε₂ D)⁻¹ * ((X.card : ℝ) * (Y.card : ℝ)) ≤
          (P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ) ∧
        (P.tag = RectTag.aBoosted → α_cap ≤ matDensity P.X_sub P.Y_sub P.A_sub) ∧
        (P.tag = RectTag.regular →
          matDensity P.X_sub P.Y_sub P.A_sub < α_cap ∧
          P.scale ≤ 47 ∧
          IsGridRegular P.X_sub P.Y_sub P.A_sub ε₂ 2 D ∧
          IsEpsMinDegree P.X_sub P.Y_sub P.A_sub ε₂))) ∧
    (∀ s : ℕ,
      let L_s := (pieces.filter (fun P => P.tag ≠ RectTag.residual ∧ P.scale = s)).length
      (L_s : ℝ) ≤ M_rect2D ε₂ D * τ_low⁻¹ * (2 : ℝ) ^ (s * D) * matDensity X Y A ∧
      (L_s : ℝ) ≤ (2 : ℝ) ^ D * M_rect2D ε₂ D * (2 : ℝ) ^ (s * D)) := by
  unfold cappedADecomposition
  dsimp only
  set τ_low := max (((2 : ℝ) ^ D)⁻¹) α_low
  have hτ_ge_2D : ((2 : ℝ) ^ D)⁻¹ ≤ τ_low := le_max_left _ _
  have hτ_ge_low : α_low ≤ τ_low := le_max_right _ _
  have hτ_pos : 0 < τ_low := lt_of_lt_of_le hα_low_pos hτ_ge_low
  have hpow48 := pow_rRect2DFuel_ge hε0
  have hfuel_cap : α_cap ≤ (1 + ε₂ / 2) ^ (rRect2DFuel ε₂) * τ_low := by
    calc
      α_cap ≤ (2 : ℝ) ^ (48 : ℕ) * α_low := hcap_le
      _ ≤ (1 + ε₂ / 2) ^ (rRect2DFuel ε₂) * τ_low :=
        mul_le_mul hpow48 hτ_ge_low hα_low_pos.le (by positivity)
  have h_part12 :
      ∀ (k : ℕ) {A_rem : α → β → ℝ}, IsBinaryMatrix X Y A_rem →
        let pcs := aDecompositionLoop k (rRect2DFuel ε₂) X Y A_rem ε₂ D τ_low α_cap oracleV []
        (∀ x ∈ X, ∀ y ∈ Y, ((pcs.map (fun P => P.A_sub x y)).sum) = A_rem x y) ∧
        (∀ P ∈ pcs,
          P.X_sub ⊆ X ∧ P.Y_sub ⊆ Y ∧ P.X_sub.Nonempty ∧ P.Y_sub.Nonempty ∧
          IsBinaryMatrix P.X_sub P.Y_sub P.A_sub ∧
          (P.tag ≠ RectTag.residual →
            (P.tag = RectTag.regular ∨ P.tag = RectTag.aBoosted) ∧
            (2 : ℝ) ^ P.scale * τ_low ≤ matDensity P.X_sub P.Y_sub P.A_sub ∧
            (((2 : ℝ) ^ (P.scale * D))⁻¹) * (M_rect2D ε₂ D)⁻¹ * ((X.card : ℝ) * (Y.card : ℝ)) ≤
              (P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ) ∧
            (P.tag = RectTag.aBoosted → α_cap ≤ matDensity P.X_sub P.Y_sub P.A_sub) ∧
            (P.tag = RectTag.regular →
              matDensity P.X_sub P.Y_sub P.A_sub < α_cap ∧
              P.scale ≤ 47 ∧
              IsGridRegular P.X_sub P.Y_sub P.A_sub ε₂ 2 D ∧
              IsEpsMinDegree P.X_sub P.Y_sub P.A_sub ε₂))) := by
    intro k
    induction k with
    | zero =>
      intro A_rem hA_rem
      dsimp only
      rw [aDecompositionLoop_zero]
      refine ⟨?_, ?_⟩
      · intro x hx y hy
        simp [restrictSubrect_eq_on hx hy]
      · intro P hP
        simp only [List.mem_singleton] at hP
        subst hP
        refine ⟨Finset.Subset.rfl, Finset.Subset.rfl, hX, hY, IsBinaryMatrix.restrict hA_rem, ?_⟩
        intro hne
        exact False.elim (hne rfl)
    | succ m ih =>
      intro A_rem hA_rem
      dsimp only
      by_cases hle : matDensity X Y A_rem ≤ τ_low
      · rw [aDecompositionLoop_of_le m (rRect2DFuel ε₂) X Y A_rem ε₂ D τ_low α_cap oracleV hle]
        refine ⟨?_, ?_⟩
        · intro x hx y hy
          simp [restrictSubrect_eq_on hx hy]
        · intro P hP
          simp only [List.mem_singleton] at hP
          subst hP
          refine ⟨Finset.Subset.rfl, Finset.Subset.rfl, hX, hY, IsBinaryMatrix.restrict hA_rem, ?_⟩
          intro hne
          exact False.elim (hne rfl)
      · have hgt : τ_low < matDensity X Y A_rem := not_le.mp hle
        rw [aDecompositionLoop_cons_eq m (rRect2DFuel ε₂) X Y A_rem ε₂ D τ_low α_cap oracleV hle]
        have hspec := cappedGoodRect_spec hX hY hA_rem hε0 hε1 hD hα_low_pos hcap_le hgt.le h_oracle
        unfold cappedGoodRect at hspec
        dsimp only at hspec
        rcases hspec with ⟨hsubX, hsubY, hneX, hneY, _, hdens_2s, harea, htag, hboost, hreg⟩
        rcases ih (IsBinaryMatrix.zeroOut hA_rem) with ⟨hsum_ih, hmem_ih⟩
        refine ⟨?_, ?_⟩
        · intro x hx y hy
          simp only [List.map_cons, List.sum_cons]
          rw [hsum_ih x hx y hy]
          exact restrictSubrect_add_zeroOutSubrect A_rem _ _ x y
        · intro P hP
          simp only [List.mem_cons] at hP
          rcases hP with rfl | hP_tail
          · have hbin_P : IsBinaryMatrix _ _
                (restrictSubrect A_rem
                  (goodRectLoop (rRect2DFuel ε₂) X Y A_rem ε₂ D α_cap oracleV 0 0).1
                  (goodRectLoop (rRect2DFuel ε₂) X Y A_rem ε₂ D α_cap oracleV 0 0).2.1) :=
              IsBinaryMatrix.restrict (isBinaryMatrix_subset_2D hsubX hsubY hA_rem)
            have hdens_eq :
                matDensity
                  (goodRectLoop (rRect2DFuel ε₂) X Y A_rem ε₂ D α_cap oracleV 0 0).1
                  (goodRectLoop (rRect2DFuel ε₂) X Y A_rem ε₂ D α_cap oracleV 0 0).2.1
                  (restrictSubrect A_rem
                    (goodRectLoop (rRect2DFuel ε₂) X Y A_rem ε₂ D α_cap oracleV 0 0).1
                    (goodRectLoop (rRect2DFuel ε₂) X Y A_rem ε₂ D α_cap oracleV 0 0).2.1) =
                matDensity
                  (goodRectLoop (rRect2DFuel ε₂) X Y A_rem ε₂ D α_cap oracleV 0 0).1
                  (goodRectLoop (rRect2DFuel ε₂) X Y A_rem ε₂ D α_cap oracleV 0 0).2.1 A_rem :=
              matDensity_restrictSubrect_eq A_rem _ _
            refine ⟨hsubX, hsubY, hneX, hneY, hbin_P, ?_⟩
            intro _
            rw [hdens_eq]
            have h_lo_τ :
                (2 : ℝ) ^ (goodRectLoop (rRect2DFuel ε₂) X Y A_rem ε₂ D α_cap oracleV 0 0).2.2.2.1 *
                  τ_low ≤
                matDensity
                  (goodRectLoop (rRect2DFuel ε₂) X Y A_rem ε₂ D α_cap oracleV 0 0).1
                  (goodRectLoop (rRect2DFuel ε₂) X Y A_rem ε₂ D α_cap oracleV 0 0).2.1 A_rem :=
              (mul_le_mul_of_nonneg_left hgt.le (by positivity)).trans hdens_2s
            refine ⟨htag, h_lo_τ, harea, hboost, ?_⟩
            intro htag_reg
            rcases hreg htag_reg with ⟨hcap_lt, hs47, hgrid, hmin⟩
            exact ⟨hcap_lt, hs47, hgrid, hmin⟩
          · exact hmem_ih P hP_tail
  rcases h_part12 fuel hA with ⟨hsum, hpieces⟩
  refine ⟨hsum, ?_, ?_⟩
  · intro P hP
    rcases hpieces P hP with ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨h1, h2, h3, h4, h5, ?_, h6⟩
    intro hfuel_ge hP_res
    exact (aDecompositionLoop_residual_density_le fuel hX hY hA hε0 hε1 hD hτ_ge_2D h_oracle hfuel_cap hfuel_ge P hP hP_res).2.2
  · intro s
    have hscale := aDecompositionLoop_scale_count_bound fuel s hX hY hA hε0 hε1 hD hτ_ge_2D h_oracle hfuel_cap
    have hA_le1 : matDensity X Y A ≤ 1 := matDensity_le_one_of_isBinaryMatrix_2D hA
    have hM_pos : 0 < M_rect2D ε₂ D := M_rect2D_pos hε0 D
    have hbd := adecomp_piece_count_at_scale_le hM_pos hτ_pos hτ_ge_2D hA_le1 hscale le_rfl
    exact ⟨hbd.1, hbd.2.2⟩

end ShrinkageAndPieceCount

/-!
## Lemma 4.6 (`\label{lem:riemann}`): Riemann-Sum Telescoping Bound (`paper.tex` §4.3)
-/

section RiemannTelescoping

/-- **Concavity Tangent Inequality for $u \mapsto u^p$ (`rpow_sub_le_of_concave`,
`paper.tex` Section 4.3)**:
For any exponent $p \in (0, 1)$ and reals $0 \le b \le a$ with $0 < a$,
$$p \cdot a^{p - 1} \cdot (a - b) \le a^p - b^p \quad \text{and} \quad
  a^{p - 1} \cdot (a - b) \le \frac{1}{p} (a^p - b^p).$$
Proved directly from the weighted AM-GM inequality `Real.geom_mean_le_arith_mean2_weighted`
with weights $(1 - p, p)$ on $(a, b)$. -/
theorem rpow_sub_le_of_concave {a b p : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (_hba : b ≤ a) (hp0 : 0 < p) (hp1 : p < 1) :
    p * a ^ (p - 1) * (a - b) ≤ a ^ p - b ^ p ∧
    a ^ (p - 1) * (a - b) ≤ (1 / p) * (a ^ p - b ^ p) := by
  have hw1 : 0 ≤ 1 - p := by linarith
  have hw2 : 0 ≤ p := le_of_lt hp0
  have ha0 : 0 ≤ a := le_of_lt ha
  have hamgm : a ^ (1 - p) * b ^ p ≤ (1 - p) * a + p * b :=
    Real.geom_mean_le_arith_mean2_weighted hw1 hw2 ha0 hb (by ring)
  have hap1_nonneg : 0 ≤ a ^ (p - 1) := Real.rpow_nonneg ha0 (p - 1)
  have hmul := mul_le_mul_of_nonneg_left hamgm hap1_nonneg
  have h_lhs : a ^ (p - 1) * (a ^ (1 - p) * b ^ p) = b ^ p := by
    rw [← mul_assoc, ← Real.rpow_add ha]
    have hexp0 : (p - 1) + (1 - p) = 0 := by ring
    rw [hexp0, Real.rpow_zero, one_mul]
  have h_ap : a ^ (p - 1) * a = a ^ p := by
    nth_rw 2 [← Real.rpow_one a]
    rw [← Real.rpow_add ha]
    congr 1
    ring
  have h_rhs : a ^ (p - 1) * ((1 - p) * a + p * b) = a ^ p - p * a ^ (p - 1) * (a - b) := by
    calc
      a ^ (p - 1) * ((1 - p) * a + p * b) =
          a ^ (p - 1) * a - p * a ^ (p - 1) * (a - b) := by ring
      _ = a ^ p - p * a ^ (p - 1) * (a - b) := by rw [h_ap]
  rw [h_lhs, h_rhs] at hmul
  have h1 : p * a ^ (p - 1) * (a - b) ≤ a ^ p - b ^ p := by linarith
  refine ⟨h1, ?_⟩
  rw [ one_div, le_inv_mul_iff₀ hp0]
  linarith

/-- **Single-Step Density-Weighted Riemann-Sum Bound (`riemann_density_weighted_step`,
`paper.tex` Section 4.3)**:
For any piece $\ell \in \{1, \dots, L-1\}$ with density $\mu_{\text{piece}} = \mathbb{E}[A_\ell] \ge \mu_{\text{prev}} = \mathbb{E}[A^{(\ell)}] > 0$,
residual density $\mu_{\text{curr}} = \mathbb{E}[A^{(\ell+1)}] \ge 0$, area fraction
$w = \frac{|X_\ell||Y_\ell|}{|X||Y|} \ge 0$, and exact density decrement
$\mu_{\text{prev}} - \mu_{\text{curr}} = w \cdot \mu_{\text{piece}}$, we have for every $p \in (0, 1)$:
$$w \cdot \mu_{\text{piece}}^p = \mu_{\text{piece}}^{-(1 - p)} (\mu_{\text{prev}} - \mu_{\text{curr}})
  \le \mu_{\text{prev}}^{-(1 - p)} (\mu_{\text{prev}} - \mu_{\text{curr}})
  \le \frac{1}{p} (\mu_{\text{prev}}^p - \mu_{\text{curr}}^p).$$ -/
theorem riemann_density_weighted_step
    {μ_prev μ_curr μ_piece w p : ℝ}
    (hμ_prev_pos : 0 < μ_prev) (hμ_curr_nonneg : 0 ≤ μ_curr)
    (h_piece_ge : μ_prev ≤ μ_piece) (hw_nonneg : 0 ≤ w)
    (hp0 : 0 < p) (hp1 : p < 1)
    (h_dec_eq : μ_prev - μ_curr = w * μ_piece) :
    w * μ_piece ^ p ≤ μ_prev ^ (p - 1) * (μ_prev - μ_curr) ∧
    μ_prev ^ (p - 1) * (μ_prev - μ_curr) ≤ (1 / p) * (μ_prev ^ p - μ_curr ^ p) := by
  have hμ_piece_pos : 0 < μ_piece := lt_of_lt_of_le hμ_prev_pos h_piece_ge
  have h_diff_nonneg : 0 ≤ μ_prev - μ_curr := by
    rw [h_dec_eq]
    exact mul_nonneg hw_nonneg (le_of_lt hμ_piece_pos)
  have hμ_le : μ_curr ≤ μ_prev := by linarith
  -- Step 1: `w * μ_piece ^ p = (w * μ_piece) * μ_piece ^ (p - 1) = (μ_prev - μ_curr) * μ_piece ^ (p - 1)`
  have h_id : w * μ_piece ^ p = μ_piece ^ (p - 1) * (μ_prev - μ_curr) := by
    have hpow : μ_piece ^ p = μ_piece * μ_piece ^ (p - 1) := by
      nth_rw 2 [← Real.rpow_one μ_piece]
      rw [← Real.rpow_add hμ_piece_pos]
      congr 1
      ring
    rw [hpow, ← mul_assoc, ← h_dec_eq, mul_comm]
  -- Step 2: Since `0 < μ_prev ≤ μ_piece` and `p - 1 ≤ 0`, `μ_piece ^ (p - 1) ≤ μ_prev ^ (p - 1)`
  have h_rpow_anti : μ_piece ^ (p - 1) ≤ μ_prev ^ (p - 1) := by
    have h1p_nonneg : 0 ≤ 1 - p := by linarith
    have h_pos_exp : μ_prev ^ (1 - p) ≤ μ_piece ^ (1 - p) :=
      Real.rpow_le_rpow (le_of_lt hμ_prev_pos) h_piece_ge h1p_nonneg
    have h_inv_prev : μ_prev ^ (p - 1) = (μ_prev ^ (1 - p))⁻¹ := by
      have : p - 1 = -(1 - p) := by ring
      rw [this, Real.rpow_neg (le_of_lt hμ_prev_pos)]
    have h_inv_piece : μ_piece ^ (p - 1) = (μ_piece ^ (1 - p))⁻¹ := by
      have : p - 1 = -(1 - p) := by ring
      rw [this, Real.rpow_neg (le_of_lt hμ_piece_pos)]
    rw [h_inv_piece, h_inv_prev]
    exact inv_anti₀ (Real.rpow_pos_of_pos hμ_prev_pos (1 - p)) h_pos_exp
  have h_step1 : w * μ_piece ^ p ≤ μ_prev ^ (p - 1) * (μ_prev - μ_curr) := by
    rw [h_id]
    exact mul_le_mul_of_nonneg_right h_rpow_anti h_diff_nonneg
  have h_step2 := (rpow_sub_le_of_concave hμ_prev_pos hμ_curr_nonneg hμ_le hp0 hp1).2
  exact ⟨h_step1, h_step2⟩

/-- **Lemma 4.6 (`\label{lem:riemann}`) Coupled to `aDecompositionLoop` (`thm_2d_decomp_riemann_telescoping`,
`\eqref{eq:riemann-telescoping}`, §4.3 of `paper.tex`)**:
For `pieces := aDecompositionLoop fuel maxIter X Y A_rem ε₂ D ρ₂ α_cap oracleV []` and any
exponent $p \in (0, 1)$, both the sum over all extracted (non-residual) pieces and the sum over
all pieces (including the final residual piece) satisfy:
$$\sum_{P \in \text{pieces}} (\mathbb{E}[P.A_{\text{sub}}])^p |P.X_{\text{sub}}||P.Y_{\text{sub}}|
  \le \frac{1}{p} (\mathbb{E}[A_{\text{rem}}])^p |X||Y|.$$ -/
theorem thm_2d_decomp_riemann_telescoping [DecidableEq α] [DecidableEq β]
    (fuel maxIter : ℕ) {X : Finset α} {Y : Finset β} {A_rem : α → β → ℝ}
    {ε₂ : ℝ} {D : ℕ} {ρ₂ α_cap p : ℝ}
    {oracleV : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → (α → ℝ)}
    (hX : X.Nonempty) (hY : Y.Nonempty) (hA : IsBinaryMatrix X Y A_rem)
    (hε0 : 0 < ε₂) (hε1 : ε₂ < 1) (hD : 2 ≤ D)
    (hρ_ge : ((2 : ℝ) ^ D)⁻¹ ≤ ρ₂)
    (h_oracle : IsValidOracleV oracleV ε₂ D)
    (hfuel_cap : α_cap ≤ (1 + ε₂ / 2) ^ maxIter * ρ₂)
    (hp0 : 0 < p) (hp1 : p < 1) :
    let pieces := aDecompositionLoop fuel maxIter X Y A_rem ε₂ D ρ₂ α_cap oracleV []
    (((pieces.filter (fun P => P.tag ≠ RectTag.residual)).map
      (fun P => (matDensity P.X_sub P.Y_sub P.A_sub) ^ p *
        ((P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ)))).sum) ≤
      (1 / p) * (matDensity X Y A_rem) ^ p * ((X.card : ℝ) * (Y.card : ℝ)) ∧
    (((pieces.map
      (fun P => (matDensity P.X_sub P.Y_sub P.A_sub) ^ p *
        ((P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ)))).sum) ≤
      (1 / p) * (matDensity X Y A_rem) ^ p * ((X.card : ℝ) * (Y.card : ℝ))) := by
  dsimp only
  have hX_pos : (0 : ℝ) < X.card := Nat.cast_pos.mpr hX.card_pos
  have hY_pos : (0 : ℝ) < Y.card := Nat.cast_pos.mpr hY.card_pos
  have h1_le_inv_p : 1 ≤ 1 / p := le_of_lt (one_lt_one_div hp0 hp1)
  induction fuel generalizing A_rem with
  | zero =>
    rw [aDecompositionLoop_zero, filter_singleton_residual_ne, List.map_nil, List.sum_nil,
      List.map_singleton, List.sum_singleton]
    dsimp only
    rw [matDensity_restrictSubrect_eq]
    have h_nonneg : 0 ≤ matDensity X Y A_rem := matDensity_nonneg_of_isBinaryMatrix_2D hA
    have h_rpow_nonneg : 0 ≤ (matDensity X Y A_rem) ^ p := Real.rpow_nonneg h_nonneg p
    refine ⟨by positivity, ?_⟩
    calc
      (matDensity X Y A_rem) ^ p * ((X.card : ℝ) * (Y.card : ℝ))
        = 1 * ((matDensity X Y A_rem) ^ p * ((X.card : ℝ) * (Y.card : ℝ))) := by ring
      _ ≤ (1 / p) * ((matDensity X Y A_rem) ^ p * ((X.card : ℝ) * (Y.card : ℝ))) :=
          mul_le_mul_of_nonneg_right h1_le_inv_p (by positivity)
      _ = (1 / p) * (matDensity X Y A_rem) ^ p * ((X.card : ℝ) * (Y.card : ℝ)) := by ring
  | succ k ih =>
    by_cases hle : matDensity X Y A_rem ≤ ρ₂
    · rw [aDecompositionLoop_of_le k maxIter X Y A_rem ε₂ D ρ₂ α_cap oracleV hle,
        filter_singleton_residual_ne, List.map_nil, List.sum_nil,
        List.map_singleton, List.sum_singleton]
      dsimp only
      rw [matDensity_restrictSubrect_eq]
      have h_nonneg : 0 ≤ matDensity X Y A_rem := matDensity_nonneg_of_isBinaryMatrix_2D hA
      have h_rpow_nonneg : 0 ≤ (matDensity X Y A_rem) ^ p := Real.rpow_nonneg h_nonneg p
      refine ⟨by positivity, ?_⟩
      calc
        (matDensity X Y A_rem) ^ p * ((X.card : ℝ) * (Y.card : ℝ))
          = 1 * ((matDensity X Y A_rem) ^ p * ((X.card : ℝ) * (Y.card : ℝ))) := by ring
        _ ≤ (1 / p) * ((matDensity X Y A_rem) ^ p * ((X.card : ℝ) * (Y.card : ℝ))) :=
            mul_le_mul_of_nonneg_right h1_le_inv_p (by positivity)
        _ = (1 / p) * (matDensity X Y A_rem) ^ p * ((X.card : ℝ) * (Y.card : ℝ)) := by ring
    · have hgt : ρ₂ < matDensity X Y A_rem := not_le.mp hle
      have hA_ge : ((2 : ℝ) ^ D)⁻¹ ≤ matDensity X Y A_rem := hρ_ge.trans hgt.le
      have hμ_prev_pos : 0 < matDensity X Y A_rem := lt_of_lt_of_le (by positivity) hA_ge
      have hfuel_A :
          α_cap ≤ (1 + ε₂ / 2) ^ maxIter * matDensity X Y A_rem :=
        hfuel_cap.trans (mul_le_mul_of_nonneg_left hgt.le (by positivity))
      have hloop := goodRectLoop_spec maxIter 0 0 hX hY hA hε0 hε1 hD hA_ge h_oracle hfuel_A
      dsimp only at hloop
      rcases hloop with ⟨hsubX, hsubY, _, _, _, _, _, hdens_boost, _, _, htag, _, _⟩
      simp only [Nat.sub_zero] at hdens_boost
      rw [aDecompositionLoop_cons_eq k maxIter X Y A_rem ε₂ D ρ₂ α_cap oracleV hle]
      set res := goodRectLoop maxIter X Y A_rem ε₂ D α_cap oracleV 0 0
      set piece_l : RectPiece α β := ⟨res.1, res.2.1, restrictSubrect A_rem res.1 res.2.1, res.2.2.1, res.2.2.2.1⟩
      set A_next := zeroOutSubrect A_rem res.1 res.2.1
      have htag_ne : piece_l.tag ≠ RectTag.residual := tag_ne_residual_of_reg_or_boost htag
      have hA_next : IsBinaryMatrix X Y A_next := IsBinaryMatrix.zeroOut hA
      rcases ih hA_next with ⟨h_ih_filt, h_ih_full⟩
      have hpow_ge1 : 1 ≤ (1 + ε₂ / 2) ^ res.2.2.2.2 :=
        one_le_pow_density_boost hε0 _
      have h2s_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ res.2.2.2.1 := one_le_pow₀ (by norm_num)
      have h_piece_ge : matDensity X Y A_rem ≤ matDensity res.1 res.2.1 A_rem := by
        have h1 : 1 ≤ (2 : ℝ) ^ res.2.2.2.1 * (1 + ε₂ / 2) ^ res.2.2.2.2 := by
          calc
            (1 : ℝ) = 1 * 1 := by ring
            _ ≤ (2 : ℝ) ^ res.2.2.2.1 * (1 + ε₂ / 2) ^ res.2.2.2.2 :=
              mul_le_mul h2s_ge1 hpow_ge1 (by norm_num) (by linarith [hpow_ge1])
        calc
          matDensity X Y A_rem = 1 * matDensity X Y A_rem := (one_mul _).symm
          _ ≤ (2 : ℝ) ^ res.2.2.2.1 * (1 + ε₂ / 2) ^ res.2.2.2.2 *
                matDensity X Y A_rem :=
              mul_le_mul_of_nonneg_right h1 hμ_prev_pos.le
          _ ≤ matDensity res.1 res.2.1 A_rem := hdens_boost
      have hμ_curr_nonneg : 0 ≤ matDensity X Y A_next :=
        matDensity_nonneg_of_isBinaryMatrix_2D hA_next
      let w := ((res.1.card : ℝ) / (X.card : ℝ)) * ((res.2.1.card : ℝ) / (Y.card : ℝ))
      have hw_nonneg : 0 ≤ w := by positivity
      have hdec := matDensity_zeroOutSubrect_eq A_rem hX hY hsubX hsubY
      have h_dec_eq :
          matDensity X Y A_rem - matDensity X Y A_next = w * matDensity res.1 res.2.1 A_rem := by
        dsimp only [A_next, w]
        linarith [hdec]
      have h_step := riemann_density_weighted_step hμ_prev_pos hμ_curr_nonneg h_piece_ge hw_nonneg hp0 hp1 h_dec_eq
      have h_w_le :
          w * (matDensity res.1 res.2.1 A_rem) ^ p ≤
            (1 / p) * ((matDensity X Y A_rem) ^ p - (matDensity X Y A_next) ^ p) :=
        h_step.1.trans h_step.2
      have h_head :
          (matDensity piece_l.X_sub piece_l.Y_sub piece_l.A_sub) ^ p *
              ((piece_l.X_sub.card : ℝ) * (piece_l.Y_sub.card : ℝ)) ≤
            (1 / p) * ((matDensity X Y A_rem) ^ p - (matDensity X Y A_next) ^ p) *
              ((X.card : ℝ) * (Y.card : ℝ)) := by
        dsimp only [piece_l]
        rw [matDensity_restrictSubrect_eq]
        have hmul := mul_le_mul_of_nonneg_right h_w_le (mul_pos hX_pos hY_pos).le
        have h_lhs :
            w * (matDensity res.1 res.2.1 A_rem) ^ p * ((X.card : ℝ) * (Y.card : ℝ)) =
              (matDensity res.1 res.2.1 A_rem) ^ p * ((res.1.card : ℝ) * (res.2.1.card : ℝ)) := by
          dsimp only [w]
          field_simp [hX_pos.ne', hY_pos.ne']
        rwa [h_lhs] at hmul
      rw [List.filter_cons, if_pos (decide_eq_true htag_ne), List.map_cons, List.sum_cons,
        List.map_cons, List.sum_cons]
      have h_alg :
          (1 / p) * ((matDensity X Y A_rem) ^ p - (matDensity X Y A_next) ^ p) *
              ((X.card : ℝ) * (Y.card : ℝ)) +
            (1 / p) * (matDensity X Y A_next) ^ p * ((X.card : ℝ) * (Y.card : ℝ)) =
          (1 / p) * (matDensity X Y A_rem) ^ p * ((X.card : ℝ) * (Y.card : ℝ)) := by ring
      refine ⟨(add_le_add h_head h_ih_filt).trans_eq h_alg,
        (add_le_add h_head h_ih_full).trans_eq h_alg⟩

/-- **Structural and telescoping conclusions of the capped 2D decomposition (Theorem 4.4) (`thm_2d_decomp`, `\label{thm:2d-decomp}`, `paper.tex` §4.3)**:
Combines the structural, shrinkage, and telescoping conclusions of Theorem 4.4 and Lemma 4.6 directly on the output of `cappedADecomposition`
(Algorithm 4 (`FindRect` / `Decompose2D`); for `CostM` complexity bounds see `cappedGoodRectConcreteTracked_snd_le` and `cappedADecompositionConcreteTracked_snd_le`):
1. Exact matrix partition, valid binary sub-rectangles, regularity/min-degree and dyadic scale
   bound $S_\ell \le 47$ for `"regular"` pieces, density threshold $\ge \alpha_{\text{cap}}$ for
   `"A-boosted"` pieces, area shrinkage $|X_\ell||Y_\ell| \ge 2^{-S_\ell D} M_{\text{rect2D}}^{-1} |X||Y|$,
   and per-scale piece-count bound $L_s \le 2^D M_{\text{rect2D}}(\varepsilon_2, D) 2^{s D}$.
2. First-moment / extracted area-mass conservation bound (`sum_extracted_area_le_initial_mass`).
3. Density-weighted Riemann-sum telescoping bound `\eqref{eq:riemann-telescoping}` for all
   $p \in (0, 1)$ (with factor $1/p$) and specifically for $p = 1/4$ (with factor $4$). -/
theorem thm_2d_decomp [DecidableEq α] [DecidableEq β]
    (fuel : ℕ) {X : Finset α} {Y : Finset β} {A : α → β → ℝ}
    {ε₂ : ℝ} {D : ℕ} {α_low α_cap p : ℝ}
    {oracleV : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → (α → ℝ)}
    (hX : X.Nonempty) (hY : Y.Nonempty) (hA : IsBinaryMatrix X Y A)
    (hε0 : 0 < ε₂) (hε1 : ε₂ < 1) (hD : 2 ≤ D)
    (hα_low_pos : 0 < α_low)
    (hcap_le : α_cap ≤ (2 : ℝ) ^ (48 : ℕ) * α_low)
    (h_oracle : IsValidOracleV oracleV ε₂ D)
    (hp0 : 0 < p) (hp1 : p < 1) :
    let pieces := cappedADecomposition fuel X Y A ε₂ D α_low α_cap oracleV
    let τ_low := max (((2 : ℝ) ^ D)⁻¹) α_low
    (∀ x ∈ X, ∀ y ∈ Y, ((pieces.map (fun P => P.A_sub x y)).sum) = A x y) ∧
    (∀ P ∈ pieces,
      P.X_sub ⊆ X ∧ P.Y_sub ⊆ Y ∧ P.X_sub.Nonempty ∧ P.Y_sub.Nonempty ∧
      IsBinaryMatrix P.X_sub P.Y_sub P.A_sub ∧
      (rDecomp2DFuel ε₂ D ≤ fuel → P.tag = RectTag.residual →
        matDensity X Y P.A_sub ≤ τ_low) ∧
      (P.tag ≠ RectTag.residual →
        (P.tag = RectTag.regular ∨ P.tag = RectTag.aBoosted) ∧
        (2 : ℝ) ^ P.scale * τ_low ≤ matDensity P.X_sub P.Y_sub P.A_sub ∧
        (((2 : ℝ) ^ (P.scale * D))⁻¹) * (M_rect2D ε₂ D)⁻¹ * ((X.card : ℝ) * (Y.card : ℝ)) ≤
          (P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ) ∧
        (P.tag = RectTag.aBoosted → α_cap ≤ matDensity P.X_sub P.Y_sub P.A_sub) ∧
        (P.tag = RectTag.regular →
          matDensity P.X_sub P.Y_sub P.A_sub < α_cap ∧
          P.scale ≤ 47 ∧
          IsGridRegular P.X_sub P.Y_sub P.A_sub ε₂ 2 D ∧
          IsEpsMinDegree P.X_sub P.Y_sub P.A_sub ε₂))) ∧
    (∀ s : ℕ,
      let L_s := (pieces.filter (fun P => P.tag ≠ RectTag.residual ∧ P.scale = s)).length
      (L_s : ℝ) ≤ M_rect2D ε₂ D * τ_low⁻¹ * (2 : ℝ) ^ (s * D) * matDensity X Y A ∧
      (L_s : ℝ) ≤ (2 : ℝ) ^ D * M_rect2D ε₂ D * (2 : ℝ) ^ (s * D)) ∧
    (((pieces.filter (fun P => P.tag ≠ RectTag.residual)).map
      (fun P => (2 : ℝ) ^ P.scale * τ_low * ((P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ)))).sum) ≤
      (X.card : ℝ) * (Y.card : ℝ) * matDensity X Y A ∧
    (((pieces.map
      (fun P => (matDensity P.X_sub P.Y_sub P.A_sub) ^ p *
        ((P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ)))).sum) ≤
      (1 / p) * (matDensity X Y A) ^ p * ((X.card : ℝ) * (Y.card : ℝ))) ∧
    (((pieces.map
      (fun P => (matDensity P.X_sub P.Y_sub P.A_sub) ^ (1 / 4 : ℝ) *
        ((P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ)))).sum) ≤
      4 * (matDensity X Y A) ^ (1 / 4 : ℝ) * ((X.card : ℝ) * (Y.card : ℝ))) := by
  have h12 := thm_2d_decomp_regularity_and_shrinkage fuel hX hY hA hε0 hε1 hD hα_low_pos hcap_le h_oracle
  set τ_low := max (((2 : ℝ) ^ D)⁻¹) α_low
  have hτ_ge_2D : ((2 : ℝ) ^ D)⁻¹ ≤ τ_low := le_max_left _ _
  have hτ_ge_low : α_low ≤ τ_low := le_max_right _ _
  have hpow48 := pow_rRect2DFuel_ge hε0
  have hfuel_cap : α_cap ≤ (1 + ε₂ / 2) ^ (rRect2DFuel ε₂) * τ_low := by
    calc
      α_cap ≤ (2 : ℝ) ^ (48 : ℕ) * α_low := hcap_le
      _ ≤ (1 + ε₂ / 2) ^ (rRect2DFuel ε₂) * τ_low :=
        mul_le_mul hpow48 hτ_ge_low hα_low_pos.le (by positivity)
  have hmass := sum_extracted_area_le_initial_mass fuel (rRect2DFuel ε₂)
    hX hY hA hε0 hε1 hD hτ_ge_2D h_oracle hfuel_cap
  have hriem_p := (thm_2d_decomp_riemann_telescoping fuel (rRect2DFuel ε₂)
    hX hY hA hε0 hε1 hD hτ_ge_2D h_oracle hfuel_cap hp0 hp1).2
  have hriem_q := (thm_2d_decomp_riemann_telescoping fuel (rRect2DFuel ε₂)
    hX hY hA hε0 hε1 hD hτ_ge_2D h_oracle hfuel_cap
    (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)).2
  have h4 : (1 : ℝ) / (1 / 4 : ℝ) = 4 := by norm_num
  rw [h4] at hriem_q
  exact ⟨h12.1, h12.2.1, h12.2.2, hmass, hriem_p, hriem_q⟩

/-- **Corollary 4.5 Uncapped 2D Decomposition (`thm_2d_decomp_uncapped`, `\label{cor:uncapped-2d}`, `paper.tex` §4.3)**:
Structural, shrinkage, and Riemann-sum telescoping specification for uncapped `aDecomposition`
with adaptive inner step fuel `rUncappedRect2DFuel ε₂ D`, outer piece budget
`rUncappedDecomp2DFuel ε₂ D`, and density threshold $\rho_2 = 2^{-D}$, valid for **all** $D \ge 2$
(without any upper cap on $D$). Because `aDecomposition` sets $\alpha_{\text{cap}} = 2 > 1$ and
$(1 + \varepsilon_2 / 2)^{\text{rUncappedRect2DFuel}(\varepsilon_2, D)} \ge 2^{D+1}$, every
non-residual piece is certified `"regular"` with scale $S_\ell \le D$, and the residual piece has
density at most $2^{-D}$. -/
theorem thm_2d_decomp_uncapped [DecidableEq α] [DecidableEq β]
    {X : Finset α} {Y : Finset β} {A : α → β → ℝ}
    {ε₂ : ℝ} {D : ℕ} {p : ℝ}
    {oracleV : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → (α → ℝ)}
    (hX : X.Nonempty) (hY : Y.Nonempty) (hA : IsBinaryMatrix X Y A)
    (hε0 : 0 < ε₂) (hε1 : ε₂ < 1) (hD : 2 ≤ D)
    (h_oracle : IsValidOracleV oracleV ε₂ D)
    (hp0 : 0 < p) (hp1 : p < 1) :
    let pieces := aDecomposition (rUncappedDecomp2DFuel ε₂ D) (rUncappedRect2DFuel ε₂ D)
      X Y A ε₂ D (((2 : ℝ) ^ D)⁻¹) oracleV
    (∀ x ∈ X, ∀ y ∈ Y, ((pieces.map (fun P => P.A_sub x y)).sum) = A x y) ∧
    (∀ P ∈ pieces,
      P.X_sub ⊆ X ∧ P.Y_sub ⊆ Y ∧ P.X_sub.Nonempty ∧ P.Y_sub.Nonempty ∧
      IsBinaryMatrix P.X_sub P.Y_sub P.A_sub ∧
      (P.tag = RectTag.residual → matDensity X Y P.A_sub ≤ ((2 : ℝ) ^ D)⁻¹) ∧
      (P.tag ≠ RectTag.residual →
        P.tag = RectTag.regular ∧
        P.scale ≤ D ∧
        (2 : ℝ) ^ P.scale * ((2 : ℝ) ^ D)⁻¹ ≤ matDensity P.X_sub P.Y_sub P.A_sub ∧
        (((2 : ℝ) ^ (P.scale * D))⁻¹) * (M_uncappedRect2D ε₂ D)⁻¹ * ((X.card : ℝ) * (Y.card : ℝ)) ≤
          (P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ) ∧
        IsGridRegular P.X_sub P.Y_sub P.A_sub ε₂ 2 D ∧
        IsEpsMinDegree P.X_sub P.Y_sub P.A_sub ε₂)) ∧
    (∀ s : ℕ,
      let L_s := (pieces.filter (fun P => P.tag ≠ RectTag.residual ∧ P.scale = s)).length
      (L_s : ℝ) ≤ (2 : ℝ) ^ D * M_uncappedRect2D ε₂ D * (2 : ℝ) ^ (s * D)) ∧
    (((pieces.map
      (fun P => (matDensity P.X_sub P.Y_sub P.A_sub) ^ p *
        ((P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ)))).sum) ≤
      (1 / p) * (matDensity X Y A) ^ p * ((X.card : ℝ) * (Y.card : ℝ))) := by
  unfold aDecomposition
  dsimp only
  set ρ₂ := ((2 : ℝ) ^ D)⁻¹
  set maxIter := rUncappedRect2DFuel ε₂ D
  set fuel := rUncappedDecomp2DFuel ε₂ D
  have hρ_pos : 0 < ρ₂ := by positivity
  have hpowD1 : (2 : ℝ) ^ (D + 1) ≤ (1 + ε₂ / 2) ^ maxIter :=
    pow_rUncappedRect2DFuel_ge hε0 D
  have h2_eq : (2 : ℝ) = (2 : ℝ) ^ (D + 1) * ρ₂ := by
    dsimp only [ρ₂]
    rw [pow_succ, mul_comm ((2 : ℝ) ^ D) 2, mul_assoc,
      mul_inv_cancel₀ (by positivity), mul_one]
  have hfuel_cap : (2 : ℝ) ≤ (1 + ε₂ / 2) ^ maxIter * ρ₂ := by
    calc
      (2 : ℝ) = (2 : ℝ) ^ (D + 1) * ρ₂ := h2_eq
      _ ≤ (1 + ε₂ / 2) ^ maxIter * ρ₂ :=
        mul_le_mul_of_nonneg_right hpowD1 (by positivity)
  have h_part12 :
      ∀ (k : ℕ) {A_rem : α → β → ℝ}, IsBinaryMatrix X Y A_rem →
        let pcs := aDecompositionLoop k maxIter X Y A_rem ε₂ D ρ₂ 2 oracleV []
        (∀ x ∈ X, ∀ y ∈ Y, ((pcs.map (fun P => P.A_sub x y)).sum) = A_rem x y) ∧
        (∀ P ∈ pcs,
          P.X_sub ⊆ X ∧ P.Y_sub ⊆ Y ∧ P.X_sub.Nonempty ∧ P.Y_sub.Nonempty ∧
          IsBinaryMatrix P.X_sub P.Y_sub P.A_sub ∧
          (P.tag ≠ RectTag.residual →
            P.tag = RectTag.regular ∧
            P.scale ≤ D ∧
            (2 : ℝ) ^ P.scale * ρ₂ ≤ matDensity P.X_sub P.Y_sub P.A_sub ∧
            (((2 : ℝ) ^ (P.scale * D))⁻¹) * (M_uncappedRect2D ε₂ D)⁻¹ * ((X.card : ℝ) * (Y.card : ℝ)) ≤
              (P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ) ∧
            IsGridRegular P.X_sub P.Y_sub P.A_sub ε₂ 2 D ∧
            IsEpsMinDegree P.X_sub P.Y_sub P.A_sub ε₂)) := by
    intro k
    induction k with
    | zero =>
      intro A_rem hA_rem
      dsimp only
      rw [aDecompositionLoop_zero]
      refine ⟨?_, ?_⟩
      · intro x hx y hy
        simp [restrictSubrect_eq_on hx hy]
      · intro P hP
        simp only [List.mem_singleton] at hP
        subst hP
        refine ⟨Finset.Subset.rfl, Finset.Subset.rfl, hX, hY, IsBinaryMatrix.restrict hA_rem, ?_⟩
        intro hne
        exact False.elim (hne rfl)
    | succ m ih =>
      intro A_rem hA_rem
      dsimp only
      by_cases hle : matDensity X Y A_rem ≤ ρ₂
      · rw [aDecompositionLoop_of_le m maxIter X Y A_rem ε₂ D ρ₂ 2 oracleV hle]
        refine ⟨?_, ?_⟩
        · intro x hx y hy
          simp [restrictSubrect_eq_on hx hy]
        · intro P hP
          simp only [List.mem_singleton] at hP
          subst hP
          refine ⟨Finset.Subset.rfl, Finset.Subset.rfl, hX, hY, IsBinaryMatrix.restrict hA_rem, ?_⟩
          intro hne
          exact False.elim (hne rfl)
      · have hgt : ρ₂ < matDensity X Y A_rem := not_le.mp hle
        rw [aDecompositionLoop_cons_eq m maxIter X Y A_rem ε₂ D ρ₂ 2 oracleV hle]
        have hfuel_A : (2 : ℝ) ≤ (1 + ε₂ / 2) ^ maxIter * matDensity X Y A_rem :=
          hfuel_cap.trans (mul_le_mul_of_nonneg_left hgt.le (by positivity))
        have hloop := goodRectLoop_spec maxIter 0 0 hX hY hA_rem hε0 hε1 hD hgt.le h_oracle hfuel_A
        dsimp only at hloop
        rcases hloop with ⟨hsubX, hsubY, hneX, hneY, _, _, hsteps_hi,
          hdens_boost, hX_card, hY_card, htag, hboost, hreg⟩
        simp only [Nat.sub_zero, zero_add] at hsteps_hi hdens_boost hX_card hY_card
        rcases ih (IsBinaryMatrix.zeroOut hA_rem) with ⟨hsum_ih, hmem_ih⟩
        refine ⟨?_, ?_⟩
        · intro x hx y hy
          simp only [List.map_cons, List.sum_cons]
          rw [hsum_ih x hx y hy]
          exact restrictSubrect_add_zeroOutSubrect A_rem _ _ x y
        · intro P hP
          simp only [List.mem_cons] at hP
          rcases hP with rfl | hP_tail
          · set res := goodRectLoop maxIter X Y A_rem ε₂ D 2 oracleV 0 0
            have hbin_sub : IsBinaryMatrix res.1 res.2.1 A_rem :=
              isBinaryMatrix_subset_2D hsubX hsubY hA_rem
            have hbin_P : IsBinaryMatrix res.1 res.2.1 (restrictSubrect A_rem res.1 res.2.1) :=
              IsBinaryMatrix.restrict hbin_sub
            have hdens_eq :
                matDensity res.1 res.2.1 (restrictSubrect A_rem res.1 res.2.1) =
                  matDensity res.1 res.2.1 A_rem :=
              matDensity_restrictSubrect_eq A_rem _ _
            refine ⟨hsubX, hsubY, hneX, hneY, hbin_P, ?_⟩
            intro _
            rw [hdens_eq]
            have hdens_le1 : matDensity res.1 res.2.1 A_rem ≤ 1 :=
              matDensity_le_one_of_isBinaryMatrix_2D hbin_sub
            have htag_reg : res.2.2.1 = RectTag.regular := by
              rcases htag with h_r | h_b
              · exact h_r
              · have hge2 := hboost h_b
                linarith
            rcases hreg htag_reg with ⟨_, hgrid, hmin⟩
            have hpow_ge1 : 1 ≤ (1 + ε₂ / 2) ^ res.2.2.2.2 :=
              one_le_pow_density_boost hε0 _
            have h_lo_ρ : (2 : ℝ) ^ res.2.2.2.1 * ρ₂ ≤ matDensity res.1 res.2.1 A_rem := by
              calc
                (2 : ℝ) ^ res.2.2.2.1 * ρ₂
                  ≤ (2 : ℝ) ^ res.2.2.2.1 * 1 * matDensity X Y A_rem := by
                    rw [mul_one]
                    exact mul_le_mul_of_nonneg_left hgt.le (by positivity)
                _ ≤ (2 : ℝ) ^ res.2.2.2.1 * (1 + ε₂ / 2) ^ res.2.2.2.2 *
                      matDensity X Y A_rem := by
                    refine mul_le_mul_of_nonneg_right ?_ (hρ_pos.le.trans hgt.le)
                    exact mul_le_mul_of_nonneg_left hpow_ge1 (by positivity)
                _ ≤ matDensity res.1 res.2.1 A_rem := hdens_boost
            have hs_le_D : res.2.2.2.1 ≤ D := by
              have h1 : (2 : ℝ) ^ res.2.2.2.1 * ρ₂ ≤ 1 := h_lo_ρ.trans hdens_le1
              have h2 : (2 : ℝ) ^ D * ρ₂ = 1 := mul_inv_cancel₀ (by positivity)
              have hle_pow : (2 : ℝ) ^ res.2.2.2.1 ≤ (2 : ℝ) ^ D := by
                by_contra! hgt_pow
                have hmul := mul_lt_mul_of_pos_right hgt_pow hρ_pos
                linarith
              exact (pow_le_pow_iff_right₀ (by norm_num)).mp hle_pow
            have harea := area_shrinkage_of_step_bounds_of_fuel hε0 hε1.le
              (Nat.cast_nonneg X.card) (Nat.cast_nonneg Y.card) hsteps_hi hX_card hY_card
            exact ⟨htag_reg, hs_le_D, h_lo_ρ, harea, hgrid, hmin⟩
          · exact hmem_ih P hP_tail
  rcases h_part12 fuel hA with ⟨hpart, hpieces⟩
  have hA_le1 : matDensity X Y A ≤ 1 := matDensity_le_one_of_isBinaryMatrix_2D hA
  have hM_pos : 0 < M_uncappedRect2D ε₂ D := M_uncappedRect2D_pos hε0 D
  have hfuel_bound :
      matDensity X Y A * ((2 : ℝ) ^ (D + D ^ 2) * M_uncappedRect2D ε₂ D) ≤ (fuel : ℝ) := by
    have h1 : matDensity X Y A * ((2 : ℝ) ^ (D + D ^ 2) * M_uncappedRect2D ε₂ D) ≤
        1 * ((2 : ℝ) ^ (D + D ^ 2) * M_uncappedRect2D ε₂ D) :=
      mul_le_mul_of_nonneg_right hA_le1 (by positivity)
    have h2 : (2 : ℝ) ^ (D + D ^ 2) * M_uncappedRect2D ε₂ D ≤
        (Nat.ceil ((2 : ℝ) ^ (D + D ^ 2) * M_uncappedRect2D ε₂ D) : ℝ) := Nat.le_ceil _
    have h3 : (Nat.ceil ((2 : ℝ) ^ (D + D ^ 2) * M_uncappedRect2D ε₂ D) : ℝ) ≤ (fuel : ℝ) := by
      dsimp only [fuel, rUncappedDecomp2DFuel]
      exact_mod_cast Nat.le_succ _
    linarith
  have hres_all := aDecompositionLoop_residual_density_le_aux_of_fuel fuel maxIter
    hX hY hA hε0 hε1 hD le_rfl h_oracle hfuel_cap hfuel_bound
  have hriem := (thm_2d_decomp_riemann_telescoping fuel maxIter
    hX hY hA hε0 hε1 hD le_rfl h_oracle hfuel_cap hp0 hp1).2
  refine ⟨hpart, ?_, ?_, hriem⟩
  · intro P hP
    rcases hpieces P hP with ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨h1, h2, h3, h4, h5, ?_, h6⟩
    intro hP_res
    exact (hres_all P hP hP_res).2.2
  · intro s
    have hscale := aDecompositionLoop_scale_count_bound_of_fuel fuel maxIter s
      hX hY hA hε0 hε1 hD le_rfl h_oracle hfuel_cap
    exact (adecomp_piece_count_at_scale_le hM_pos hρ_pos le_rfl hA_le1 hscale le_rfl).2.2

end RiemannTelescoping

/-!
## Proposition 4.7 (`\label{prop:tightness}`): Tightness of Single-Step Shrinkage (§4.4 of `paper.tex`)
-/

section ObstaclesRemark

/-- **Proposition 4.7 (`\label{prop:tightness}`) (`rem_obstacles_single_step_tightness`, §4.4 of `paper.tex`)**:
For a single-step ($S = 1$) extraction where the sub-rectangle area fraction satisfies
$\frac{|X'|}{|X|} \cdot \frac{|Y'|}{|Y|} \ge c \cdot \mathbb{E}[A]^2$ and the extracted density
satisfies $\mathbb{E}[A'] \ge (1 + \varepsilon)\mathbb{E}[A]$:
1. The density decrement $\Delta = \frac{|X'|}{|X|} \cdot \frac{|Y'|}{|Y|} \cdot \mathbb{E}[A']$
   satisfies $\Delta \ge c(1 + \varepsilon)\mathbb{E}[A]^3$.
2. When the single-step $|Y'|/|Y| = \Theta(\mathbb{E}[A]^2)$ shrinkage is tight
   ($\frac{|X'|}{|X|} \cdot \frac{|Y'|}{|Y|} = c \cdot \mathbb{E}[A]^2$ and
   $\mathbb{E}[A'] = (1 + \varepsilon)\mathbb{E}[A]$), we have $\Delta = c(1 + \varepsilon)\mathbb{E}[A]^3$,
   so for $\mathbb{E}[A] \in (0, 1]$ the inverse-decrement piece cost satisfies
   $\frac{1}{\Delta} = \frac{1}{c(1 + \varepsilon)} \mathbb{E}[A]^{-3} \ge \frac{1}{c(1 + \varepsilon)} \mathbb{E}[A]^{-2}$,
   reflecting the $\int_{\rho}^1 u^{-3}\,du = \Theta(\rho^{-2})$ (and $\int_{\rho}^1 u^{-1}\,du = \ln(1/\rho)$
   in the $p \to 0$ limit) barrier that necessitates tracking the exact step count $S_\ell$ in
   Theorem 4.4 and Lemma 4.6. -/
theorem rem_obstacles_single_step_tightness
    {area_frac μ μ' Δ c ε : ℝ}
    (hc_pos : 0 < c) (hε_nonneg : 0 ≤ ε) (hμ_pos : 0 < μ) (hμ_le_one : μ ≤ 1)
    (h_area_ge : c * μ ^ 2 ≤ area_frac)
    (h_dens_ge : (1 + ε) * μ ≤ μ')
    (h_delta_eq : Δ = area_frac * μ') :
    c * (1 + ε) * μ ^ 3 ≤ Δ ∧
    (area_frac = c * μ ^ 2 → μ' = (1 + ε) * μ →
      Δ = c * (1 + ε) * μ ^ 3 ∧
      1 / Δ = (1 / (c * (1 + ε))) * (μ ^ 3)⁻¹ ∧
      (1 / (c * (1 + ε))) * (μ ^ 2)⁻¹ ≤ 1 / Δ) := by
  have h1_eps_pos : 0 < 1 + ε := by linarith
  have h_area_nonneg : 0 ≤ area_frac := le_trans (by positivity) h_area_ge
  have h_lower : c * (1 + ε) * μ ^ 3 ≤ Δ := by
    rw [h_delta_eq]
    calc
      c * (1 + ε) * μ ^ 3 = (c * μ ^ 2) * ((1 + ε) * μ) := by ring
      _ ≤ area_frac * μ' :=
        mul_le_mul h_area_ge h_dens_ge (by positivity) h_area_nonneg
  refine ⟨h_lower, ?_⟩
  intro h_area_tight h_dens_tight
  have h_tight : Δ = c * (1 + ε) * μ ^ 3 := by
    rw [h_delta_eq, h_area_tight, h_dens_tight]
    ring
  have h_inv_eq : 1 / Δ = (1 / (c * (1 + ε))) * (μ ^ 3)⁻¹ := by
    rw [h_tight, one_div, one_div, mul_inv]
  have h_pow_le : μ ^ 3 ≤ μ ^ 2 := by
    have : μ ^ 3 = μ ^ 2 * μ := by ring
    nlinarith [sq_pos_of_pos hμ_pos]
  have h_inv_pow : (μ ^ 2)⁻¹ ≤ (μ ^ 3)⁻¹ :=
    inv_anti₀ (by positivity) h_pow_le
  have h_inv_ge : (1 / (c * (1 + ε))) * (μ ^ 2)⁻¹ ≤ 1 / Δ := by
    rw [h_inv_eq]
    exact mul_le_mul_of_nonneg_left h_inv_pow (by positivity)
  exact ⟨h_tight, h_inv_eq, h_inv_ge⟩

/-- Multi-block $\{0, 1\}$ matrix on $X \times Y$ (`plantedMultiBlockMatrix`, Proposition 4.7 (`\label{prop:tightness}`),
§4.4 of `paper.tex`): takes value `1` if and only if $(x, y) \in X_m \times Y_m$ for some block
$m \in \text{Fin } B$, and `0` otherwise. -/
noncomputable def plantedMultiBlockMatrix
    {B : ℕ} (X_block : Fin B → Finset α) (Y_block : Fin B → Finset β) (x : α) (y : β) : ℝ :=
  letI := Classical.dec
  if ∃ m : Fin B, x ∈ X_block m ∧ y ∈ Y_block m then 1 else 0

/-- $B = 2^{\lfloor d^2 / 2 \rfloor}$-block counterexample configuration (`PlantedMultiBlockConfig`,
Proposition 4.7 (`\label{prop:tightness}`), §4.4 of `paper.tex`) on $X \times Y$:
partitions $X$ into $B = 2^{\lfloor d^2 / 2 \rfloor}$ disjoint equal-sized blocks $X_m$ of size
$|X| / B = 2^{-\lfloor d^2 / 2 \rfloor} |X|$ and assigns each block $X_m$ a column subset
$Y_m \subseteq Y$ of size $|Y_m| = \mu |Y|$ with $\mu = 2^{1-d}$ and pairwise intersections
$|Y_m \cap Y_{m'}| \le (1 + \varepsilon / 4) \mu^2 |Y|$ for $m \ne m'$. -/
structure PlantedMultiBlockConfig [DecidableEq β] (X : Finset α) (Y : Finset β) (d : ℕ) where
  X_block : Fin (2 ^ (d ^ 2 / 2)) → Finset α
  Y_block : Fin (2 ^ (d ^ 2 / 2)) → Finset β
  ε : ℝ
  hd : 4 ≤ d
  hε_pos : 0 < ε
  hε_lt : ε < 1 / 4
  hX_nonempty : X.Nonempty
  hY_nonempty : Y.Nonempty
  hX_sub : ∀ m, X_block m ⊆ X
  hX_cover : ∀ x ∈ X, ∃ m, x ∈ X_block m
  hX_disj : ∀ m m', m ≠ m' → Disjoint (X_block m) (X_block m')
  hX_card : ∀ m, ((X_block m).card : ℝ) = (X.card : ℝ) / ((2 ^ (d ^ 2 / 2) : ℕ) : ℝ)
  hY_sub : ∀ m, Y_block m ⊆ Y
  hY_card : ∀ m, ((Y_block m).card : ℝ) = (2 : ℝ) ^ (1 - (d : ℤ)) * (Y.card : ℝ)
  hY_inter : ∀ m m', m ≠ m' →
    ((Y_block m ∩ Y_block m').card : ℝ) ≤
      (1 + ε / 4) * ((2 : ℝ) ^ (1 - (d : ℤ))) ^ 2 * (Y.card : ℝ)

/-- Binary `{0, 1}` matrix $A(x, y) = 1 \iff \exists m,\, x \in X_m \land y \in Y_m$ associated to `cfg`. -/
noncomputable def PlantedMultiBlockConfig.matrix [DecidableEq β]
    {X : Finset α} {Y : Finset β} {d : ℕ} (cfg : PlantedMultiBlockConfig X Y d) : α → β → ℝ :=
  plantedMultiBlockMatrix cfg.X_block cfg.Y_block

lemma PlantedMultiBlockConfig.isBinaryMatrix [DecidableEq β]
    {X : Finset α} {Y : Finset β} {d : ℕ} (cfg : PlantedMultiBlockConfig X Y d) :
    IsBinaryMatrix X Y cfg.matrix := by
  intro x _ y _
  unfold PlantedMultiBlockConfig.matrix plantedMultiBlockMatrix
  split_ifs <;> simp

lemma PlantedMultiBlockConfig.matrix_apply_of_mem [DecidableEq β]
    {X : Finset α} {Y : Finset β} {d : ℕ} (cfg : PlantedMultiBlockConfig X Y d)
    {m : Fin (2 ^ (d ^ 2 / 2))} {x : α} (hx : x ∈ cfg.X_block m) (y : β) :
    cfg.matrix x y = if y ∈ cfg.Y_block m then 1 else 0 := by
  unfold PlantedMultiBlockConfig.matrix plantedMultiBlockMatrix
  have hiff : (∃ m', x ∈ cfg.X_block m' ∧ y ∈ cfg.Y_block m') ↔ y ∈ cfg.Y_block m := by
    constructor
    · rintro ⟨m', hx', hy'⟩
      by_cases h : m = m'
      · subst h; exact hy'
      · exact False.elim (Finset.disjoint_left.mp (cfg.hX_disj m m' h) hx hx')
    · intro hy
      exact ⟨m, hx, hy⟩
  by_cases hy : y ∈ cfg.Y_block m
  · rw [if_pos (hiff.mpr hy), if_pos hy]
  · rw [if_neg (mt hiff.mp hy), if_neg hy]

lemma PlantedMultiBlockConfig.sum_matrix_eq_card_inter [DecidableEq β]
    {X : Finset α} {Y : Finset β} {d : ℕ} (cfg : PlantedMultiBlockConfig X Y d)
    {m : Fin (2 ^ (d ^ 2 / 2))} {x : α} (hx : x ∈ cfg.X_block m) (V : Finset β) :
    ∑ y ∈ V, cfg.matrix x y = ((V ∩ cfg.Y_block m).card : ℝ) := by
  have hcongr : ∀ y ∈ V, cfg.matrix x y = (if y ∈ cfg.Y_block m then (1 : ℝ) else 0) :=
    fun y _ => cfg.matrix_apply_of_mem hx y
  rw [Finset.sum_congr rfl hcongr, Finset.sum_boole, Finset.filter_mem_eq_inter]

lemma PlantedMultiBlockConfig.rowSupport_eq [DecidableEq β]
    {X : Finset α} {Y : Finset β} {d : ℕ} (cfg : PlantedMultiBlockConfig X Y d)
    {m : Fin (2 ^ (d ^ 2 / 2))} {x : α} (hx : x ∈ cfg.X_block m) :
    rowSupport Y cfg.matrix x = cfg.Y_block m := by
  ext y
  rw [mem_rowSupport_iff, cfg.matrix_apply_of_mem hx]
  constructor
  · rintro ⟨_, hge⟩
    by_contra hy_not
    rw [if_neg hy_not] at hge
    linarith
  · intro hy
    exact ⟨cfg.hY_sub m hy, by rw [if_pos hy]⟩

lemma PlantedMultiBlockConfig.rowDeg_eq_of_mem [DecidableEq β]
    {X : Finset α} {Y : Finset β} {d : ℕ} (cfg : PlantedMultiBlockConfig X Y d)
    {m : Fin (2 ^ (d ^ 2 / 2))} {x : α} (hx : x ∈ cfg.X_block m) :
    rowDeg Y cfg.matrix x = (2 : ℝ) ^ (1 - (d : ℤ)) := by
  have hY_ne : (Y.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr cfg.hY_nonempty.card_pos.ne'
  unfold rowDeg expectSet
  rw [cfg.sum_matrix_eq_card_inter hx Y, Finset.inter_eq_right.mpr (cfg.hY_sub m),
    cfg.hY_card m, mul_div_cancel_right₀ _ hY_ne]

lemma PlantedMultiBlockConfig.rowDeg_eq [DecidableEq β]
    {X : Finset α} {Y : Finset β} {d : ℕ} (cfg : PlantedMultiBlockConfig X Y d)
    {x : α} (hx : x ∈ X) :
    rowDeg Y cfg.matrix x = (2 : ℝ) ^ (1 - (d : ℤ)) := by
  rcases cfg.hX_cover x hx with ⟨m, hxm⟩
  exact cfg.rowDeg_eq_of_mem hxm

lemma PlantedMultiBlockConfig.matDensity_eq [DecidableEq β]
    {X : Finset α} {Y : Finset β} {d : ℕ} (cfg : PlantedMultiBlockConfig X Y d) :
    matDensity X Y cfg.matrix = (2 : ℝ) ^ (1 - (d : ℤ)) := by
  have hX_ne : (X.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr cfg.hX_nonempty.card_pos.ne'
  unfold matDensity
  rw [expectSet_congr_2D (fun x hx => cfg.rowDeg_eq hx)]
  unfold expectSet
  rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel_left₀ _ hX_ne]

lemma PlantedMultiBlockConfig.Y_block_card_pos [DecidableEq β]
    {X : Finset α} {Y : Finset β} {d : ℕ} (cfg : PlantedMultiBlockConfig X Y d)
    (m : Fin (2 ^ (d ^ 2 / 2))) :
    (0 : ℝ) < ((cfg.Y_block m).card : ℝ) := by
  rw [cfg.hY_card m]
  have hY_pos : (0 : ℝ) < Y.card := Nat.cast_pos.mpr cfg.hY_nonempty.card_pos
  positivity

lemma PlantedMultiBlockConfig.rowDeg_on_block_eq_one [DecidableEq α] [DecidableEq β]
    {X : Finset α} {Y : Finset β} {d : ℕ} (cfg : PlantedMultiBlockConfig X Y d)
    {m : Fin (2 ^ (d ^ 2 / 2))} {x : α} (hx : x ∈ cfg.X_block m) :
    rowDeg (cfg.Y_block m) cfg.matrix x = 1 ∧
    rowDeg (cfg.Y_block m) (restrictSubrect cfg.matrix (cfg.X_block m) (cfg.Y_block m)) x = 1 := by
  have hYm_pos : (0 : ℝ) < (cfg.Y_block m).card := cfg.Y_block_card_pos m
  have h1 : rowDeg (cfg.Y_block m) cfg.matrix x = 1 := by
    unfold rowDeg expectSet
    rw [cfg.sum_matrix_eq_card_inter hx (cfg.Y_block m), Finset.inter_self,
      div_self hYm_pos.ne']
  refine ⟨h1, ?_⟩
  rw [rowDeg_restrictSubrect_eq cfg.matrix hx, h1]

lemma PlantedMultiBlockConfig.rowDeg_off_block_le [DecidableEq β]
    {X : Finset α} {Y : Finset β} {d : ℕ} (cfg : PlantedMultiBlockConfig X Y d)
    {m m' : Fin (2 ^ (d ^ 2 / 2))} (hne : m' ≠ m) {x' : α} (hx' : x' ∈ cfg.X_block m') :
    rowDeg (cfg.Y_block m) cfg.matrix x' =
      (((cfg.Y_block m ∩ cfg.Y_block m').card : ℝ) / ((cfg.Y_block m).card : ℝ)) ∧
    rowDeg (cfg.Y_block m) cfg.matrix x' ≤
      (1 + cfg.ε / 4) * (2 : ℝ) ^ (1 - (d : ℤ)) := by
  have hYm_pos : (0 : ℝ) < (cfg.Y_block m).card := cfg.Y_block_card_pos m
  have hdeg_eq :
      rowDeg (cfg.Y_block m) cfg.matrix x' =
        (((cfg.Y_block m ∩ cfg.Y_block m').card : ℝ) / ((cfg.Y_block m).card : ℝ)) := by
    unfold rowDeg expectSet
    rw [cfg.sum_matrix_eq_card_inter hx' (cfg.Y_block m)]
  refine ⟨hdeg_eq, ?_⟩
  rw [hdeg_eq, div_le_iff₀ hYm_pos]
  calc
    ((cfg.Y_block m ∩ cfg.Y_block m').card : ℝ)
      ≤ (1 + cfg.ε / 4) * ((2 : ℝ) ^ (1 - (d : ℤ))) ^ 2 * (Y.card : ℝ) :=
        cfg.hY_inter m m' (Ne.symm hne)
    _ = (1 + cfg.ε / 4) * (2 : ℝ) ^ (1 - (d : ℤ)) *
          ((2 : ℝ) ^ (1 - (d : ℤ)) * (Y.card : ℝ)) := by ring
    _ = (1 + cfg.ε / 4) * (2 : ℝ) ^ (1 - (d : ℤ)) * ((cfg.Y_block m).card : ℝ) := by
        rw [← cfg.hY_card m]

lemma PlantedMultiBlockConfig.gridNorm1Pow_block_ge [DecidableEq α] [DecidableEq β]
    {X : Finset α} {Y : Finset β} {d : ℕ} (cfg : PlantedMultiBlockConfig X Y d)
    (m : Fin (2 ^ (d ^ 2 / 2))) :
    (((2 : ℝ) ^ (d ^ 2 / 2))⁻¹) ≤ gridNorm1Pow X (cfg.Y_block m) cfg.matrix d := by
  have hX_pos : (0 : ℝ) < X.card := Nat.cast_pos.mpr cfg.hX_nonempty.card_pos
  unfold gridNorm1Pow expectSet
  rw [le_div_iff₀ hX_pos]
  have hnonneg : ∀ x' ∈ X, x' ∉ cfg.X_block m → 0 ≤ (rowDeg (cfg.Y_block m) cfg.matrix x') ^ d := by
    intro x' hx' _
    refine pow_nonneg ?_ d
    exact expectSet_nonneg (fun y hy =>
      isBinaryMatrix_nonneg_2D cfg.isBinaryMatrix x' hx' y (cfg.hY_sub m hy))
  have hsum_ge := Finset.sum_le_sum_of_subset_of_nonneg (cfg.hX_sub m) hnonneg
  have hsum_block :
      ∑ x' ∈ cfg.X_block m, (rowDeg (cfg.Y_block m) cfg.matrix x') ^ d =
        ((cfg.X_block m).card : ℝ) := by
    have h1 : ∀ x' ∈ cfg.X_block m, (rowDeg (cfg.Y_block m) cfg.matrix x') ^ d = 1 := by
      intro x' hx'
      rw [(cfg.rowDeg_on_block_eq_one hx').1, one_pow]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hsum_block, cfg.hX_card m, Nat.cast_pow, Nat.cast_ofNat, div_eq_inv_mul] at hsum_ge
  exact hsum_ge

lemma PlantedMultiBlockConfig.gridNorm2Pow_ge [DecidableEq α] [DecidableEq β]
    {X : Finset α} {Y : Finset β} {d : ℕ} (cfg : PlantedMultiBlockConfig X Y d) :
    let μ := (2 : ℝ) ^ (1 - (d : ℤ))
    (((2 : ℝ) ^ (d ^ 2 / 2))⁻¹) * μ ^ d ≤ gridNorm2Pow X Y cfg.matrix d ∧
    (((2 : ℝ) ^ (d ^ 2 / 2))⁻¹) * μ ^ (2 * d) ≤ gridNorm2Pow X Y cfg.matrix d := by
  dsimp only
  set μ := (2 : ℝ) ^ (1 - (d : ℤ))
  have h1 : (((2 : ℝ) ^ (d ^ 2 / 2))⁻¹) * μ ^ d ≤ gridNorm2Pow X Y cfg.matrix d := by
    rw [u2d_expansion cfg.isBinaryMatrix d,
      ← expectSet_const cfg.hX_nonempty ((((2 : ℝ) ^ (d ^ 2 / 2))⁻¹) * μ ^ d)]
    refine expectSet_mono (fun x hx => ?_)
    rcases cfg.hX_cover x hx with ⟨m, hxm⟩
    rw [cfg.rowDeg_eq_of_mem hxm, cfg.rowSupport_eq hxm]
    calc
      (((2 : ℝ) ^ (d ^ 2 / 2))⁻¹) * μ ^ d = μ ^ d * (((2 : ℝ) ^ (d ^ 2 / 2))⁻¹) := mul_comm _ _
      _ ≤ μ ^ d * gridNorm1Pow X (cfg.Y_block m) cfg.matrix d :=
        mul_le_mul_of_nonneg_left (cfg.gridNorm1Pow_block_ge m) (by positivity)
  have hμ_le1 : μ ≤ 1 := by
    dsimp only [μ]
    have hexp : 1 - (d : ℤ) ≤ 0 := by have := cfg.hd; omega
    exact zpow_le_one_of_nonpos₀ (by norm_num) hexp
  have h2 : (((2 : ℝ) ^ (d ^ 2 / 2))⁻¹) * μ ^ (2 * d) ≤ (((2 : ℝ) ^ (d ^ 2 / 2))⁻¹) * μ ^ d := by
    have hpow_le : μ ^ (2 * d) ≤ μ ^ d := by
      have h2d : 2 * d = d + d := by omega
      rw [h2d, pow_add]
      have h_d_le1 : μ ^ d ≤ 1 := pow_le_one₀ (by positivity) hμ_le1
      calc
        μ ^ d * μ ^ d ≤ μ ^ d * 1 := mul_le_mul_of_nonneg_left h_d_le1 (by positivity)
        _ = μ ^ d := mul_one _
    exact mul_le_mul_of_nonneg_left hpow_le (by positivity)
  exact ⟨h1, h2.trans h1⟩

lemma PlantedMultiBlockConfig.outerDyadicBucket_eq_empty [DecidableEq β]
    {X : Finset α} {Y : Finset β} {d : ℕ} (cfg : PlantedMultiBlockConfig X Y d) (s : ℕ) :
    outerDyadicBucket X Y cfg.matrix ((1 + cfg.ε / 2) * (2 : ℝ) ^ (1 - (d : ℤ))) s = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  rw [mem_outerDyadicBucket_iff] at hx
  have hdeg := cfg.rowDeg_eq hx.1
  have hμ_pos : (0 : ℝ) < (2 : ℝ) ^ (1 - (d : ℤ)) := by positivity
  have h2s_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ s := one_le_pow₀ (by norm_num)
  have h_δ_gt : (2 : ℝ) ^ (1 - (d : ℤ)) < (1 + cfg.ε / 2) * (2 : ℝ) ^ (1 - (d : ℤ)) := by
    have : 0 < cfg.ε / 2 * (2 : ℝ) ^ (1 - (d : ℤ)) := mul_pos (by linarith [cfg.hε_pos]) hμ_pos
    linarith
  have h_2s_ge : (1 + cfg.ε / 2) * (2 : ℝ) ^ (1 - (d : ℤ)) ≤
      (2 : ℝ) ^ s * ((1 + cfg.ε / 2) * (2 : ℝ) ^ (1 - (d : ℤ))) := by
    calc
      (1 + cfg.ε / 2) * (2 : ℝ) ^ (1 - (d : ℤ)) =
          1 * ((1 + cfg.ε / 2) * (2 : ℝ) ^ (1 - (d : ℤ))) := (one_mul _).symm
      _ ≤ (2 : ℝ) ^ s * ((1 + cfg.ε / 2) * (2 : ℝ) ^ (1 - (d : ℤ))) :=
        mul_le_mul_of_nonneg_right h2s_ge1 (by linarith [cfg.hε_pos])
  linarith [hx.2.1, hdeg]

lemma PlantedMultiBlockConfig.innerDyadicBucket_subset_block [DecidableEq β]
    {X : Finset α} {Y : Finset β} {d : ℕ} (cfg : PlantedMultiBlockConfig X Y d)
    (m : Fin (2 ^ (d ^ 2 / 2))) (s : ℕ) :
    innerDyadicBucket X (cfg.Y_block m) cfg.matrix
      ((1 + cfg.ε / 2) * (2 : ℝ) ^ (1 - (d : ℤ))) s ⊆ cfg.X_block m ∧
    ((innerDyadicBucket X (cfg.Y_block m) cfg.matrix
      ((1 + cfg.ε / 2) * (2 : ℝ) ^ (1 - (d : ℤ))) s).card : ℝ) ≤
      (X.card : ℝ) / ((2 ^ (d ^ 2 / 2) : ℕ) : ℝ) := by
  have hsub :
      innerDyadicBucket X (cfg.Y_block m) cfg.matrix
        ((1 + cfg.ε / 2) * (2 : ℝ) ^ (1 - (d : ℤ))) s ⊆ cfg.X_block m := by
    intro x' hx'
    rw [mem_innerDyadicBucket_iff] at hx'
    rcases cfg.hX_cover x' hx'.1 with ⟨m', hxm'⟩
    by_cases hm' : m' = m
    · subst hm'; exact hxm'
    · have hoff := (cfg.rowDeg_off_block_le hm' hxm').2
      have hμ_pos : (0 : ℝ) < (2 : ℝ) ^ (1 - (d : ℤ)) := by positivity
      have h2s_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ s := one_le_pow₀ (by norm_num)
      have h_lt_δ :
          (1 + cfg.ε / 4) * (2 : ℝ) ^ (1 - (d : ℤ)) <
            (1 + cfg.ε / 2) * (2 : ℝ) ^ (1 - (d : ℤ)) := by
        have : 0 < (cfg.ε / 4) * (2 : ℝ) ^ (1 - (d : ℤ)) := mul_pos (by linarith [cfg.hε_pos]) hμ_pos
        linarith
      have h_2s_ge :
          (1 + cfg.ε / 2) * (2 : ℝ) ^ (1 - (d : ℤ)) ≤
            (2 : ℝ) ^ s * ((1 + cfg.ε / 2) * (2 : ℝ) ^ (1 - (d : ℤ))) := by
        calc
          (1 + cfg.ε / 2) * (2 : ℝ) ^ (1 - (d : ℤ)) =
              1 * ((1 + cfg.ε / 2) * (2 : ℝ) ^ (1 - (d : ℤ))) := (one_mul _).symm
          _ ≤ (2 : ℝ) ^ s * ((1 + cfg.ε / 2) * (2 : ℝ) ^ (1 - (d : ℤ))) :=
            mul_le_mul_of_nonneg_right h2s_ge1 (by linarith [cfg.hε_pos])
      linarith [hx'.2.1, hoff]
  refine ⟨hsub, ?_⟩
  calc
    ((innerDyadicBucket X (cfg.Y_block m) cfg.matrix
      ((1 + cfg.ε / 2) * (2 : ℝ) ^ (1 - (d : ℤ))) s).card : ℝ)
      ≤ ((cfg.X_block m).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ = (X.card : ℝ) / ((2 ^ (d ^ 2 / 2) : ℕ) : ℝ) := cfg.hX_card m

/-- **Proposition 4.7 (`\label{prop:tightness}`) Multi-Block Sift Tightness (`rem_obstacles_multiblock_sift_tightness`,
§4.4 of `paper.tex`)**:
For any $B = 2^{\lfloor d^2 / 2 \rfloor}$-block configuration `cfg : PlantedMultiBlockConfig X Y d`
with binary matrix $A = \text{cfg.matrix}$, $\mu = 2^{1-d}$, and $\delta = (1 + \varepsilon / 2)\mu$:
1. $A$ is a $\{0, 1\}$-matrix on $X \times Y$, every row $x \in X$ has exact degree
   $\text{rowDeg } Y A x = \mu = 2^{1-d} > 2^{-d}$, and $\text{matDensity } X Y A = \mu$;
2. For every block $m \in \text{Fin } B$ and $x \in X_m$, $\text{rowSupport } Y A x = Y_m$,
   $\text{rowDeg } Y_m A x = 1$, $\text{rowDeg } Y_m (A|_{X_m \times Y_m}) x = 1$, and the diagonal
   blocks force $\text{gridNorm2Pow } X Y A d \ge \frac{1}{B} \mu^d \ge \frac{1}{B} \mu^{2d}$;
3. For every dyadic scale $s \in \mathbb{N}$, the Step 1 outer dyadic bucket is empty:
   `outerDyadicBucket X Y A δ s = ∅`;
4. For any witness block $m \in \text{Fin } B$ and witness row $x^* \in X_m$ (with
   $Y' = \text{rowSupport } Y A x^* = Y_m$), every off-block row $x' \in X_{m'}$ ($m' \ne m$) has
   $\text{rowDeg } Y_m A x' = \frac{|Y_m \cap Y_{m'}|}{|Y_m|} \le (1 + \varepsilon / 4)\mu < 2^s \delta$,
   so for every $s \in \mathbb{N}$ the Step 3 inner dyadic bucket satisfies
   `innerDyadicBucket X Y' A δ s ⊆ X_m` and has cardinality at most
   $|X_m| = |X| / B = 2^{-\lfloor d^2 / 2 \rfloor} |X|$. -/
theorem rem_obstacles_multiblock_sift_tightness [DecidableEq α] [DecidableEq β]
    {X : Finset α} {Y : Finset β} {d : ℕ} (cfg : PlantedMultiBlockConfig X Y d) :
    let B := 2 ^ (d ^ 2 / 2)
    let μ := (2 : ℝ) ^ (1 - (d : ℤ))
    let δ := (1 + cfg.ε / 2) * μ
    let A := cfg.matrix
    (IsBinaryMatrix X Y A ∧
      (2 : ℝ) ^ (-(d : ℤ)) < μ ∧
      (∀ x ∈ X, rowDeg Y A x = μ) ∧
      matDensity X Y A = μ) ∧
    ((∀ m : Fin B, ∀ x ∈ cfg.X_block m,
        rowSupport Y A x = cfg.Y_block m ∧
        rowDeg (cfg.Y_block m) A x = 1 ∧
        rowDeg (cfg.Y_block m) (restrictSubrect A (cfg.X_block m) (cfg.Y_block m)) x = 1) ∧
      (((2 : ℝ) ^ (d ^ 2 / 2))⁻¹) * μ ^ d ≤ gridNorm2Pow X Y A d ∧
      (((2 : ℝ) ^ (d ^ 2 / 2))⁻¹) * μ ^ (2 * d) ≤ gridNorm2Pow X Y A d) ∧
    (∀ s : ℕ, outerDyadicBucket X Y A δ s = ∅) ∧
    (∀ m : Fin B, ∀ x_star ∈ cfg.X_block m,
      let Y' := rowSupport Y A x_star
      Y' = cfg.Y_block m ∧
      (∀ m' : Fin B, m' ≠ m → ∀ x' ∈ cfg.X_block m',
        rowDeg Y' A x' = (((cfg.Y_block m ∩ cfg.Y_block m').card : ℝ) / ((cfg.Y_block m).card : ℝ)) ∧
        rowDeg Y' A x' ≤ (1 + cfg.ε / 4) * μ) ∧
      (∀ s : ℕ,
        innerDyadicBucket X Y' A δ s ⊆ cfg.X_block m ∧
        ((innerDyadicBucket X Y' A δ s).card : ℝ) ≤ (X.card : ℝ) / ((B : ℕ) : ℝ))) := by
  dsimp only
  have hμ_gt : (2 : ℝ) ^ (-(d : ℤ)) < (2 : ℝ) ^ (1 - (d : ℤ)) :=
    zpow_lt_zpow_right₀ (by norm_num) (by omega)
  have hgn := cfg.gridNorm2Pow_ge
  refine ⟨⟨cfg.isBinaryMatrix, hμ_gt, fun x hx => cfg.rowDeg_eq hx, cfg.matDensity_eq⟩,
    ⟨fun m x hx => ⟨cfg.rowSupport_eq hx, (cfg.rowDeg_on_block_eq_one hx).1,
      (cfg.rowDeg_on_block_eq_one hx).2⟩, hgn.1, hgn.2⟩,
    cfg.outerDyadicBucket_eq_empty, ?_⟩
  intro m x_star hx_star
  have hY' : rowSupport Y cfg.matrix x_star = cfg.Y_block m := cfg.rowSupport_eq hx_star
  refine ⟨hY', ?_, ?_⟩
  · intro m' hm' x' hx'
    rw [hY']
    exact cfg.rowDeg_off_block_le hm' hx'
  · intro s
    rw [hY']
    exact cfg.innerDyadicBucket_subset_block m s

end ObstaclesRemark

/-!
## Concrete Sampler-Conditional Instantiation and `CostM` Complexity Bounds for Section 4.3
(`concreteOracleV`, `cappedGoodRectConcrete`, `cappedADecompositionConcrete`, `aDecompositionConcrete`)
-/

section ConcreteDecomp2D

lemma ite_retTracked_snd {γ : Type*} (c : Prop) [Decidable c] (a b : γ) :
    (if c then retTracked a else retTracked b).2 = 1 := by
  split_ifs <;> rfl

/-- Unconditional subset preservation for `minDegreeLoop`. -/
lemma minDegreeLoop_fst_subset [DecidableEq α]
    (U : Finset α) (V : Finset β) (M : α → β → ℝ) (ε₀ γ₀ : ℝ) (U' : Finset α) :
    (minDegreeLoop U V M ε₀ γ₀ U').1 ⊆ U' := by
  induction h : U'.card using Nat.strong_induction_on generalizing U' with
  | _ k ih =>
    subst h
    rw [minDegreeLoop]
    split_ifs with hbad hthresh
    · exact Finset.erase_subset _ _
    · have hu : chooseMinBadRow U' V M ε₀ hbad ∈ U' :=
        (mem_minDegreeBadRows_iff.mp (chooseMinBadRow_mem U' V M ε₀ hbad)).1
      exact Finset.Subset.trans
        (ih _ (Finset.card_erase_lt_of_mem hu) (U'.erase (chooseMinBadRow U' V M ε₀ hbad)) rfl)
        (Finset.erase_subset _ _)
    · exact Finset.Subset.refl U'

/-- Unconditional subset preservation for `minDegree`. -/
lemma minDegree_fst_subset [DecidableEq α]
    (U : Finset α) (V : Finset β) (M : α → β → ℝ) (ε₀ γ₀ : ℝ) :
    (minDegree U V M ε₀ γ₀).1 ⊆ U :=
  minDegreeLoop_fst_subset U V M ε₀ γ₀ U

/-- Unconditional subset preservation for `dyadicSift`. -/
lemma dyadicSift_subset
    (X : Finset α) (Y : Finset β) (A : α → β → ℝ) (ε : ℝ) (d : ℕ) (V : α → ℝ) :
    (dyadicSift X Y A ε d V).2.1 ⊆ X ∧ (dyadicSift X Y A ε d V).2.2.1 ⊆ Y := by
  classical
  unfold dyadicSift
  dsimp only
  cases (List.range d).findSome? _ with
  | some s =>
    exact ⟨fun x hx => (mem_outerDyadicBucket_iff.mp hx).1, Finset.Subset.refl Y⟩
  | none =>
    split_ifs with hwit
    · dsimp only
      cases (List.range d).findSome? _ with
      | some s =>
        exact ⟨fun x' hx' => (mem_innerDyadicBucket_iff.mp hx').1, rowSupport_subset Y A _⟩
      | none =>
        exact ⟨Finset.Subset.refl X, Finset.Subset.refl Y⟩
    · exact ⟨Finset.Subset.refl X, Finset.Subset.refl Y⟩

/-- Unconditional subset preservation for a single step `goodRectStep`. -/
lemma goodRectStep_subset [DecidableEq α] [DecidableEq β]
    (X' : Finset α) (Y' : Finset β) (A : α → β → ℝ) (ε₂ : ℝ) (D : ℕ) (α_cap : ℝ)
    (oracleV : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → (α → ℝ)) (s_bar : ℕ) :
    match goodRectStep X' Y' A ε₂ D α_cap oracleV s_bar with
    | Sum.inl (X_next, Y_next, _, _) => X_next ⊆ X' ∧ Y_next ⊆ Y'
    | Sum.inr (X_out, Y_out, _, _) => X_out ⊆ X' ∧ Y_out ⊆ Y' := by
  have hmin := minDegree_fst_subset X' Y' A ε₂ (1 / 2)
  unfold goodRectStep
  dsimp only
  split_ifs with h0 h1 h2 h3
  · exact ⟨Finset.Subset.refl X', Finset.Subset.refl Y'⟩
  · exact ⟨hmin, Finset.Subset.refl Y'⟩
  · exact ⟨hmin, Finset.Subset.refl Y'⟩
  · exact ⟨hmin, Finset.Subset.refl Y'⟩
  · have hsift := dyadicSift_subset
      (minDegree X' Y' A ε₂ (1 / 2)).1 Y' A ε₂ D
      (oracleV (minDegree X' Y' A ε₂ (1 / 2)).1 Y' A
        (ε₂ * ((1 + ε₂ / 2) * matDensity
          (minDegree X' Y' A ε₂ (1 / 2)).1 Y' A) ^ 3 / 32) D)
    exact ⟨Finset.Subset.trans hsift.1 hmin, hsift.2⟩

/-- Concrete `ApproxGridNorm` oracle for 2D decompositions, instantiating `oracleV` with
`concreteApproxGridNormV S` from `BMMGrid/MinDegreeAndDyadicSift.lean`. -/
noncomputable def concreteOracleV {ε₂ : ℝ} (S : TwoStageSamplerOracle β ε₂)
    (U : Finset α) (V : Finset β) (M : α → β → ℝ) (_α_grid : ℝ) (d : ℕ) : α → ℝ :=
  concreteApproxGridNormV S U V M d

/-- Cost-tracked concrete `ApproxGridNorm` oracle in `CostM`. -/
noncomputable def concreteOracleVTracked {ε₂ : ℝ} (S : TwoStageSamplerOracle β ε₂)
    (U : Finset α) (V : Finset β) (M : α → β → ℝ) (_α_grid : ℝ) (d : ℕ) : CostM (α → ℝ) :=
  concreteApproxGridNormVTracked S U V M d

@[simp]
theorem concreteOracleVTracked_fst {ε₂ : ℝ} (S : TwoStageSamplerOracle β ε₂)
    (U : Finset α) (V : Finset β) (M : α → β → ℝ) (α_grid : ℝ) (d : ℕ) :
    (concreteOracleVTracked S U V M α_grid d).1 = concreteOracleV S U V M α_grid d :=
  concreteApproxGridNormVTracked_fst S U V M d

@[simp]
theorem concreteOracleVTracked_fst_eta {ε₂ : ℝ} (S : TwoStageSamplerOracle β ε₂) :
    (fun (U : Finset α) (V : Finset β) (M : α → β → ℝ) (α_g : ℝ) (d : ℕ) =>
      (concreteOracleVTracked S U V M α_g d).1) = concreteOracleV S := by
  funext U V M α_g d
  exact concreteOracleVTracked_fst S U V M α_g d

/-- Concrete Algorithm 4 (`FindRect` / `Decompose2D`) (`cappedGoodRectConcrete`, §4.3 of `paper.tex`). -/
noncomputable def cappedGoodRectConcrete [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (A : α → β → ℝ) (ε₂ : ℝ) (D : ℕ) (α_cap : ℝ)
    (S : TwoStageSamplerOracle β ε₂) :
    Finset α × Finset β × RectTag × ℕ × ℕ :=
  cappedGoodRect X Y A ε₂ D α_cap (concreteOracleV S)

/-- Cost-tracked Concrete Algorithm 4 (`FindRect` / `Decompose2D`) (`cappedGoodRectConcreteTracked`) in `CostM`. -/
noncomputable def cappedGoodRectConcreteTracked [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (A : α → β → ℝ) (ε₂ : ℝ) (D : ℕ) (α_cap : ℝ)
    (S : TwoStageSamplerOracle β ε₂) :
    CostM (Finset α × Finset β × RectTag × ℕ × ℕ) :=
  cappedGoodRectTracked X Y A ε₂ D α_cap (concreteOracleVTracked S)

@[simp]
theorem cappedGoodRectConcreteTracked_fst [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (A : α → β → ℝ) (ε₂ : ℝ) (D : ℕ) (α_cap : ℝ)
    (S : TwoStageSamplerOracle β ε₂) :
    (cappedGoodRectConcreteTracked X Y A ε₂ D α_cap S).1 =
      cappedGoodRectConcrete X Y A ε₂ D α_cap S := by
  unfold cappedGoodRectConcreteTracked cappedGoodRectConcrete
  rw [cappedGoodRectTracked_fst, concreteOracleVTracked_fst_eta]

/-- Concrete Algorithm 4 (`FindRect` / `Decompose2D`) (`cappedADecompositionConcrete`, §4.3 of `paper.tex`). -/
noncomputable def cappedADecompositionConcrete [DecidableEq α] [DecidableEq β]
    (maxPieces : ℕ) (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (ε₂ : ℝ) (D : ℕ) (α_low α_cap : ℝ) (S : TwoStageSamplerOracle β ε₂) :
    List (RectPiece α β) :=
  cappedADecomposition maxPieces X Y A ε₂ D α_low α_cap (concreteOracleV S)

/-- Cost-tracked Concrete Algorithm 4 (`FindRect` / `Decompose2D`) (`cappedADecompositionConcreteTracked`) in `CostM`. -/
noncomputable def cappedADecompositionConcreteTracked [DecidableEq α] [DecidableEq β]
    (maxPieces : ℕ) (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (ε₂ : ℝ) (D : ℕ) (α_low α_cap : ℝ) (S : TwoStageSamplerOracle β ε₂) :
    CostM (List (RectPiece α β)) :=
  cappedADecompositionTracked maxPieces X Y A ε₂ D α_low α_cap (concreteOracleVTracked S)

@[simp]
theorem cappedADecompositionConcreteTracked_fst [DecidableEq α] [DecidableEq β]
    (maxPieces : ℕ) (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (ε₂ : ℝ) (D : ℕ) (α_low α_cap : ℝ) (S : TwoStageSamplerOracle β ε₂) :
    (cappedADecompositionConcreteTracked maxPieces X Y A ε₂ D α_low α_cap S).1 =
      cappedADecompositionConcrete maxPieces X Y A ε₂ D α_low α_cap S := by
  unfold cappedADecompositionConcreteTracked cappedADecompositionConcrete
  rw [cappedADecompositionTracked_fst, concreteOracleVTracked_fst_eta]

/-- Concrete uncapped 2D decomposition (`aDecompositionConcrete`, Corollary 4.5 `\label{cor:uncapped-2d}`,
§4.3 of `paper.tex`). -/
noncomputable def aDecompositionConcrete [DecidableEq α] [DecidableEq β]
    (maxPieces maxIter : ℕ) (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (ε₂ : ℝ) (D : ℕ) (ρ₂ : ℝ) (S : TwoStageSamplerOracle β ε₂) :
    List (RectPiece α β) :=
  aDecomposition maxPieces maxIter X Y A ε₂ D ρ₂ (concreteOracleV S)

/-- Cost-tracked concrete uncapped 2D decomposition (`aDecompositionConcreteTracked`) in `CostM`. -/
noncomputable def aDecompositionConcreteTracked [DecidableEq α] [DecidableEq β]
    (maxPieces maxIter : ℕ) (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (ε₂ : ℝ) (D : ℕ) (ρ₂ : ℝ) (S : TwoStageSamplerOracle β ε₂) :
    CostM (List (RectPiece α β)) :=
  aDecompositionTracked maxPieces maxIter X Y A ε₂ D ρ₂ (concreteOracleVTracked S)

@[simp]
theorem aDecompositionConcreteTracked_fst [DecidableEq α] [DecidableEq β]
    (maxPieces maxIter : ℕ) (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (ε₂ : ℝ) (D : ℕ) (ρ₂ : ℝ) (S : TwoStageSamplerOracle β ε₂) :
    (aDecompositionConcreteTracked maxPieces maxIter X Y A ε₂ D ρ₂ S).1 =
      aDecompositionConcrete maxPieces maxIter X Y A ε₂ D ρ₂ S := by
  unfold aDecompositionConcreteTracked aDecompositionConcrete
  rw [aDecompositionTracked_fst, concreteOracleVTracked_fst_eta]

/-- Per-step cost bound factor for `goodRectStepTracked` with `concreteOracleVTracked`. -/
noncomputable def goodRectStepCostFactor (c k : ℕ) (ε₂ : ℝ) (D : ℕ) : ℕ :=
  concreteApproxGridNormCostFactor c k ε₂ D + 2 * (D + 1) + 6

/-- Cost bound for a single step `goodRectStepTracked` with `concreteOracleVTracked`. -/
theorem goodRectStepTracked_concrete_snd_le [DecidableEq α] [DecidableEq β]
    (X' : Finset α) (Y' : Finset β) (A : α → β → ℝ) (ε₂ : ℝ) (D : ℕ) (α_cap : ℝ)
    (S : TwoStageSamplerOracle β ε₂) (s_bar : ℕ) :
    (goodRectStepTracked X' Y' A ε₂ D α_cap (concreteOracleVTracked S) s_bar).2 ≤
      (X'.card + Y'.card + 2) * (X'.card + Y'.card + 2) * goodRectStepCostFactor S.c S.k ε₂ D := by
  unfold goodRectStepTracked goodRectStepCostFactor
  dsimp only
  let Q := (X'.card + Y'.card + 2) * (X'.card + Y'.card + 2)
  have hQ_scan : X'.card * Y'.card + 1 ≤ 2 * Q := by
    dsimp only [Q]; nlinarith
  have hQ_min_quad : X'.card * Y'.card + 1 + (X'.card + 1) * (X'.card + 1) + 1 ≤ 2 * Q := by
    dsimp only [Q]; nlinarith
  have h2Q_le : 2 * Q ≤ Q * (concreteApproxGridNormCostFactor S.c S.k ε₂ D + 2 * (D + 1) + 6) := by
    have hfac : 2 ≤ concreteApproxGridNormCostFactor S.c S.k ε₂ D + 2 * (D + 1) + 6 := by omega
    calc
      2 * Q = Q * 2 := by ring
      _ ≤ Q * (concreteApproxGridNormCostFactor S.c S.k ε₂ D + 2 * (D + 1) + 6) :=
        Nat.mul_le_mul_left Q hfac
  split_ifs with hcap0
  · rw [scanMatrixTracked_snd]
    exact le_trans hQ_scan h2Q_le
  · dsimp only [CostM.bind_snd]
    rw [minDegreeTracked_fst]
    have hmin_cost := minDegreeTracked_snd_le X' Y' A ε₂ (1 / 2)
    have hmin_sub := minDegree_fst_subset X' Y' A ε₂ (1 / 2)
    have hX1 : (minDegree X' Y' A ε₂ (1 / 2)).1.card ≤ X'.card :=
      Finset.card_le_card hmin_sub
    split_ifs with h1 hcap1
    · rw [retTracked_snd]
      exact le_trans (by omega) (le_trans hQ_min_quad h2Q_le)
    · rw [retTracked_snd]
      exact le_trans (by omega) (le_trans hQ_min_quad h2Q_le)
    · dsimp only [CostM.bind_snd]
      rw [ite_retTracked_snd]
      have hsift := dyadicSiftConcreteTracked_snd_le
        (minDegree X' Y' A ε₂ (1 / 2)).1 Y' A ε₂ D S
      unfold dyadicSiftConcreteTracked at hsift
      have hprod_le :
          ((minDegree X' Y' A ε₂ (1 / 2)).1.card + Y'.card + 2) ^ 2 ≤ Q := by
        dsimp only [Q]; rw [sq]; nlinarith
      have hmul_le :
          ((minDegree X' Y' A ε₂ (1 / 2)).1.card + Y'.card + 2) ^ 2 *
            (concreteApproxGridNormCostFactor S.c S.k ε₂ D + 2 * (D + 1)) ≤
          Q * (concreteApproxGridNormCostFactor S.c S.k ε₂ D + 2 * (D + 1)) :=
        Nat.mul_le_mul_right _ hprod_le
      have htot_Q :
          2 * Q + Q * (concreteApproxGridNormCostFactor S.c S.k ε₂ D + 2 * (D + 1)) ≤
            Q * (concreteApproxGridNormCostFactor S.c S.k ε₂ D + 2 * (D + 1) + 6) := by
        have h_eq :
            2 * Q + Q * (concreteApproxGridNormCostFactor S.c S.k ε₂ D + 2 * (D + 1)) =
              Q * (concreteApproxGridNormCostFactor S.c S.k ε₂ D + 2 * (D + 1) + 2) := by ring
        rw [h_eq]
        exact Nat.mul_le_mul_left Q (by omega)
      dsimp only [concreteOracleVTracked]
      exact le_trans (by omega) htot_Q

/-- Cost bound for `goodRectLoopTracked` with `concreteOracleVTracked`. -/
theorem goodRectLoopTracked_concrete_snd_le [DecidableEq α] [DecidableEq β]
    (fuel : ℕ) (X' : Finset α) (Y' : Finset β) (A : α → β → ℝ) (ε₂ : ℝ) (D : ℕ) (α_cap : ℝ)
    (S : TwoStageSamplerOracle β ε₂) (s_bar steps_done : ℕ) :
    (goodRectLoopTracked fuel X' Y' A ε₂ D α_cap (concreteOracleVTracked S) s_bar steps_done).2 ≤
      (fuel + 1) *
        ((X'.card + Y'.card + 2) * (X'.card + Y'.card + 2) *
          goodRectStepCostFactor S.c S.k ε₂ D + 1) := by
  induction fuel generalizing X' Y' s_bar steps_done with
  | zero =>
    unfold goodRectLoopTracked
    simp only [retTracked_snd, zero_add, one_mul]
    omega
  | succ k ih =>
    unfold goodRectLoopTracked
    rw [CostM.bind_snd, goodRectStepTracked_fst, concreteOracleVTracked_fst_eta]
    change (goodRectStepTracked X' Y' A ε₂ D α_cap (concreteOracleVTracked S) s_bar).2 +
      (match goodRectStep X' Y' A ε₂ D α_cap (concreteOracleV S) s_bar with
        | Sum.inr (X_out, Y_out, tag_out, s_final) =>
          retTracked (X_out, Y_out, tag_out, s_final, steps_done)
        | Sum.inl (X_next, Y_next, s_bar_next, _s_step) =>
          goodRectLoopTracked k X_next Y_next A ε₂ D α_cap (concreteOracleVTracked S) s_bar_next (steps_done + 1)).2 ≤ _
    have hstep_cost := goodRectStepTracked_concrete_snd_le X' Y' A ε₂ D α_cap S s_bar
    have hstep_sub := goodRectStep_subset X' Y' A ε₂ D α_cap (concreteOracleV S) s_bar
    cases hstep : goodRectStep X' Y' A ε₂ D α_cap (concreteOracleV S) s_bar with
    | inr val =>
      dsimp only [retTracked_snd]
      nlinarith
    | inl val =>
      rw [hstep] at hstep_sub
      dsimp only at hstep_sub ⊢
      have hX_le : val.1.card ≤ X'.card := Finset.card_le_card hstep_sub.1
      have hY_le : val.2.1.card ≤ Y'.card := Finset.card_le_card hstep_sub.2
      have hrec := ih val.1 val.2.1 val.2.2.1 (steps_done + 1)
      have hquad :
          (val.1.card + val.2.1.card + 2) * (val.1.card + val.2.1.card + 2) ≤
            (X'.card + Y'.card + 2) * (X'.card + Y'.card + 2) := by
        nlinarith
      have hfac :
          (val.1.card + val.2.1.card + 2) * (val.1.card + val.2.1.card + 2) *
            goodRectStepCostFactor S.c S.k ε₂ D + 1 ≤
          (X'.card + Y'.card + 2) * (X'.card + Y'.card + 2) *
            goodRectStepCostFactor S.c S.k ε₂ D + 1 := by
        nlinarith [Nat.mul_le_mul_right (goodRectStepCostFactor S.c S.k ε₂ D) hquad]
      have hrec' :
          (goodRectLoopTracked k val.1 val.2.1 A ε₂ D α_cap (concreteOracleVTracked S) val.2.2.1
            (steps_done + 1)).2 ≤
          (k + 1) *
            ((X'.card + Y'.card + 2) * (X'.card + Y'.card + 2) *
              goodRectStepCostFactor S.c S.k ε₂ D + 1) :=
        le_trans hrec (Nat.mul_le_mul_left (k + 1) hfac)
      nlinarith

/-- Cost bound for `cappedGoodRectConcreteTracked`. -/
theorem cappedGoodRectConcreteTracked_snd_le [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (A : α → β → ℝ) (ε₂ : ℝ) (D : ℕ) (α_cap : ℝ)
    (S : TwoStageSamplerOracle β ε₂) :
    (cappedGoodRectConcreteTracked X Y A ε₂ D α_cap S).2 ≤
      (rRect2DFuel ε₂ + 1) *
        ((X.card + Y.card + 2) * (X.card + Y.card + 2) *
          goodRectStepCostFactor S.c S.k ε₂ D + 1) :=
  goodRectLoopTracked_concrete_snd_le (rRect2DFuel ε₂) X Y A ε₂ D α_cap S 0 0

/-- Cost bound for `aDecompositionLoopTracked` with `concreteOracleVTracked`. -/
theorem aDecompositionLoopTracked_concrete_snd_le [DecidableEq α] [DecidableEq β]
    (fuel maxIter : ℕ) (X : Finset α) (Y : Finset β) (A_rem : α → β → ℝ)
    (ε₂ : ℝ) (D : ℕ) (ρ₂ α_cap : ℝ) (S : TwoStageSamplerOracle β ε₂)
    (acc : List (RectPiece α β)) :
    (aDecompositionLoopTracked fuel maxIter X Y A_rem ε₂ D ρ₂ α_cap (concreteOracleVTracked S) acc).2 ≤
      (fuel + 1) *
        ((maxIter + 1) *
          ((X.card + Y.card + 2) * (X.card + Y.card + 2) *
            goodRectStepCostFactor S.c S.k ε₂ D + 1) +
          X.card * Y.card + 1) := by
  induction fuel generalizing A_rem acc with
  | zero =>
    unfold aDecompositionLoopTracked
    simp only [scanMatrixTracked_snd, zero_add, one_mul]
    omega
  | succ k ih =>
    unfold aDecompositionLoopTracked
    dsimp only
    split_ifs with hlt
    · simp only [scanMatrixTracked_snd]
      calc
        X.card * Y.card + 1 ≤
            1 * ((maxIter + 1) *
              ((X.card + Y.card + 2) * (X.card + Y.card + 2) *
                goodRectStepCostFactor S.c S.k ε₂ D + 1) +
              X.card * Y.card + 1) := by omega
        _ ≤ (k + 1 + 1) *
              ((maxIter + 1) *
                ((X.card + Y.card + 2) * (X.card + Y.card + 2) *
                  goodRectStepCostFactor S.c S.k ε₂ D + 1) +
                X.card * Y.card + 1) :=
          Nat.mul_le_mul_right _ (by omega)
    · rw [CostM.bind_snd, CostM.bind_snd, scanMatrixTracked_snd]
      have hgr := goodRectLoopTracked_concrete_snd_le maxIter X Y A_rem ε₂ D α_cap S 0 0
      let res := (goodRectLoopTracked maxIter X Y A_rem ε₂ D α_cap (concreteOracleVTracked S) 0 0).1
      have hrec := ih (zeroOutSubrect A_rem res.1 res.2.1)
        (⟨res.1, res.2.1, restrictSubrect A_rem res.1 res.2.1, res.2.2.1, res.2.2.2.1⟩ :: acc)
      change (goodRectLoopTracked maxIter X Y A_rem ε₂ D α_cap (concreteOracleVTracked S) 0 0).2 +
        (X.card * Y.card + 1 + _) ≤ _
      nlinarith

/-- Cost bound for `cappedADecompositionConcreteTracked`. -/
theorem cappedADecompositionConcreteTracked_snd_le [DecidableEq α] [DecidableEq β]
    (maxPieces : ℕ) (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (ε₂ : ℝ) (D : ℕ) (α_low α_cap : ℝ) (S : TwoStageSamplerOracle β ε₂) :
    (cappedADecompositionConcreteTracked maxPieces X Y A ε₂ D α_low α_cap S).2 ≤
      (maxPieces + 1) *
        ((rRect2DFuel ε₂ + 1) *
          ((X.card + Y.card + 2) * (X.card + Y.card + 2) *
            goodRectStepCostFactor S.c S.k ε₂ D + 1) +
          X.card * Y.card + 1) :=
  aDecompositionLoopTracked_concrete_snd_le maxPieces (rRect2DFuel ε₂) X Y A ε₂ D
    (max (((2 : ℝ) ^ D)⁻¹) α_low) α_cap S []

/-- Cost bound for `aDecompositionConcreteTracked`. -/
theorem aDecompositionConcreteTracked_snd_le [DecidableEq α] [DecidableEq β]
    (maxPieces maxIter : ℕ) (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (ε₂ : ℝ) (D : ℕ) (ρ₂ : ℝ) (S : TwoStageSamplerOracle β ε₂) :
    (aDecompositionConcreteTracked maxPieces maxIter X Y A ε₂ D ρ₂ S).2 ≤
      (maxPieces + 1) *
        ((maxIter + 1) *
          ((X.card + Y.card + 2) * (X.card + Y.card + 2) *
            goodRectStepCostFactor S.c S.k ε₂ D + 1) +
          X.card * Y.card + 1) :=
  aDecompositionLoopTracked_concrete_snd_le maxPieces maxIter X Y A ε₂ D ρ₂ 2 S []

/-- `concreteOracleV S` satisfies `IsValidOracleV` via `concreteApproxGridNormV_approx`. -/
theorem concreteOracleV_isValid {ε₂ : ℝ} (S : TwoStageSamplerOracle β ε₂)
    (hε : 0 ≤ ε₂) {D : ℕ} (hD : 1 ≤ D) : IsValidOracleV (concreteOracleV (α := α) S) ε₂ D := by
  intro U V M hU hM hδ _δ _α_grid x hx hdeg
  exact concreteApproxGridNormV_approx S hU hM hε hD hδ x hx hdeg

/-- Structural piece-count bound for `aDecompositionLoop`: at most `fuel + 1` pieces total. -/
lemma aDecompositionLoop_length_le [DecidableEq α] [DecidableEq β]
    (fuel maxIter : ℕ) (X : Finset α) (Y : Finset β) (A_rem : α → β → ℝ)
    (ε₂ : ℝ) (D : ℕ) (ρ₂ α_cap : ℝ)
    (oracleV : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → (α → ℝ)) :
    (aDecompositionLoop fuel maxIter X Y A_rem ε₂ D ρ₂ α_cap oracleV []).length ≤ fuel + 1 := by
  induction fuel generalizing A_rem with
  | zero =>
    rw [aDecompositionLoop_zero]
    simp
  | succ k ih =>
    by_cases hle : matDensity X Y A_rem ≤ ρ₂
    · rw [aDecompositionLoop_of_le k maxIter X Y A_rem ε₂ D ρ₂ α_cap oracleV hle]
      simp
    · rw [aDecompositionLoop_cons_eq k maxIter X Y A_rem ε₂ D ρ₂ α_cap oracleV hle,
        List.length_cons]
      exact Nat.succ_le_succ (ih _)

/-- Inductive non-residual piece-count bound for `aDecompositionLoop` (§4.3 of `paper.tex`):
each extracted non-residual piece reduces `matDensity X Y A_rem` by at least
`2^{-(D + D^2)} M_rect2D_of_fuel⁻¹`. -/
lemma aDecompositionLoop_nonresidual_count_le_aux [DecidableEq α] [DecidableEq β]
    (fuel maxIter : ℕ) {X : Finset α} {Y : Finset β} {A_rem : α → β → ℝ}
    {ε₂ : ℝ} {D : ℕ} {ρ₂ α_cap : ℝ}
    {oracleV : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → (α → ℝ)}
    (hX : X.Nonempty) (hY : Y.Nonempty) (hA : IsBinaryMatrix X Y A_rem)
    (hε0 : 0 < ε₂) (hε1 : ε₂ < 1) (hD : 2 ≤ D)
    (hρ_ge : ((2 : ℝ) ^ D)⁻¹ ≤ ρ₂)
    (h_oracle : IsValidOracleV oracleV ε₂ D)
    (hfuel_cap : α_cap ≤ (1 + ε₂ / 2) ^ maxIter * ρ₂) :
    let pieces := aDecompositionLoop fuel maxIter X Y A_rem ε₂ D ρ₂ α_cap oracleV []
    (((pieces.filter (fun P => P.tag ≠ RectTag.residual)).length : ℝ) ≤
      matDensity X Y A_rem * ((2 : ℝ) ^ (D + D ^ 2) * M_rect2D_of_fuel maxIter ε₂ D)) := by
  dsimp only
  have hX_pos : (0 : ℝ) < X.card := Nat.cast_pos.mpr hX.card_pos
  have hY_pos : (0 : ℝ) < Y.card := Nat.cast_pos.mpr hY.card_pos
  have hM_pos : 0 < M_rect2D_of_fuel maxIter ε₂ D := M_rect2D_of_fuel_pos maxIter hε0 D
  induction fuel generalizing A_rem with
  | zero =>
    rw [aDecompositionLoop_zero, filter_singleton_residual_ne, List.length_nil, Nat.cast_zero]
    have h_nonneg : 0 ≤ matDensity X Y A_rem := matDensity_nonneg_of_isBinaryMatrix_2D hA
    positivity
  | succ k ih =>
    by_cases hle : matDensity X Y A_rem ≤ ρ₂
    · rw [aDecompositionLoop_of_le k maxIter X Y A_rem ε₂ D ρ₂ α_cap oracleV hle,
        filter_singleton_residual_ne, List.length_nil, Nat.cast_zero]
      have h_nonneg : 0 ≤ matDensity X Y A_rem := matDensity_nonneg_of_isBinaryMatrix_2D hA
      positivity
    · have hgt : ρ₂ < matDensity X Y A_rem := not_le.mp hle
      have hA_ge : ((2 : ℝ) ^ D)⁻¹ ≤ matDensity X Y A_rem := hρ_ge.trans hgt.le
      have hfuel_A :
          α_cap ≤ (1 + ε₂ / 2) ^ maxIter * matDensity X Y A_rem :=
        hfuel_cap.trans (mul_le_mul_of_nonneg_left hgt.le (by positivity))
      have hloop := goodRectLoop_spec maxIter 0 0 hX hY hA hε0 hε1 hD hA_ge h_oracle hfuel_A
      dsimp only at hloop
      rcases hloop with ⟨hsubX, hsubY, _, _, _, _, hsteps_hi,
        hdens_boost, hX_card, hY_card, htag, _, _⟩
      simp only [Nat.sub_zero, zero_add] at hsteps_hi hdens_boost hX_card hY_card
      rw [aDecompositionLoop_cons_eq k maxIter X Y A_rem ε₂ D ρ₂ α_cap oracleV hle]
      set res := goodRectLoop maxIter X Y A_rem ε₂ D α_cap oracleV 0 0
      set piece_l : RectPiece α β := ⟨res.1, res.2.1, restrictSubrect A_rem res.1 res.2.1, res.2.2.1, res.2.2.2.1⟩
      set A_next := zeroOutSubrect A_rem res.1 res.2.1
      have htag_ne : piece_l.tag ≠ RectTag.residual := tag_ne_residual_of_reg_or_boost htag
      have hA_next : IsBinaryMatrix X Y A_next := IsBinaryMatrix.zeroOut hA
      have h_ih := ih hA_next
      have hpow_ge1 : 1 ≤ (1 + ε₂ / 2) ^ res.2.2.2.2 :=
        one_le_pow_density_boost hε0 _
      have h_piece_dens : (2 : ℝ) ^ res.2.2.2.1 * ((2 : ℝ) ^ D)⁻¹ ≤ matDensity res.1 res.2.1 A_rem := by
        calc
          (2 : ℝ) ^ res.2.2.2.1 * ((2 : ℝ) ^ D)⁻¹
            ≤ (2 : ℝ) ^ res.2.2.2.1 * 1 * matDensity X Y A_rem := by
              rw [mul_one]
              exact mul_le_mul_of_nonneg_left hA_ge (by positivity)
          _ ≤ (2 : ℝ) ^ res.2.2.2.1 * (1 + ε₂ / 2) ^ res.2.2.2.2 *
                matDensity X Y A_rem := by
              refine mul_le_mul_of_nonneg_right ?_ (le_trans (by positivity) hA_ge)
              exact mul_le_mul_of_nonneg_left hpow_ge1 (by positivity)
          _ ≤ matDensity res.1 res.2.1 A_rem := hdens_boost
      have hs_le_D : res.2.2.2.1 ≤ D := by
        have hdens_le_1 : matDensity res.1 res.2.1 A_rem ≤ 1 :=
          matDensity_le_one_of_isBinaryMatrix_2D (isBinaryMatrix_subset_2D hsubX hsubY hA)
        have h1 : (2 : ℝ) ^ res.2.2.2.1 * ((2 : ℝ) ^ D)⁻¹ ≤ 1 := h_piece_dens.trans hdens_le_1
        have h2 : (2 : ℝ) ^ D * ((2 : ℝ) ^ D)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
        have hle_pow : (2 : ℝ) ^ res.2.2.2.1 ≤ (2 : ℝ) ^ D := by
          by_contra! hgt_pow
          have hmul := mul_lt_mul_of_pos_right hgt_pow (by positivity : (0 : ℝ) < ((2 : ℝ) ^ D)⁻¹)
          linarith
        exact (pow_le_pow_iff_right₀ (by norm_num)).mp hle_pow
      have hSD_le : res.2.2.2.1 * D ≤ D ^ 2 := by
        rw [sq]
        exact Nat.mul_le_mul_right D hs_le_D
      have h_inv_SD : (((2 : ℝ) ^ (D ^ 2))⁻¹) ≤ (((2 : ℝ) ^ (res.2.2.2.1 * D))⁻¹) :=
        inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hSD_le)
      have h2s_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ res.2.2.2.1 := one_le_pow₀ (by norm_num)
      have h_dens_2D : ((2 : ℝ) ^ D)⁻¹ ≤ matDensity res.1 res.2.1 A_rem := by
        have h1 : 1 * ((2 : ℝ) ^ D)⁻¹ ≤ (2 : ℝ) ^ res.2.2.2.1 * ((2 : ℝ) ^ D)⁻¹ :=
          mul_le_mul_of_nonneg_right h2s_ge1 (by positivity)
        linarith
      have harea := area_shrinkage_of_step_bounds_of_fuel hε0 hε1.le
        (Nat.cast_nonneg X.card) (Nat.cast_nonneg Y.card) hsteps_hi hX_card hY_card
      have h_area_ratio :
          (((2 : ℝ) ^ (D ^ 2))⁻¹) * (M_rect2D_of_fuel maxIter ε₂ D)⁻¹ ≤
            ((res.1.card : ℝ) / (X.card : ℝ)) * ((res.2.1.card : ℝ) / (Y.card : ℝ)) := by
        have h0 :
            (((2 : ℝ) ^ (D ^ 2))⁻¹) * (M_rect2D_of_fuel maxIter ε₂ D)⁻¹ ≤
              (((2 : ℝ) ^ (res.2.2.2.1 * D))⁻¹) * (M_rect2D_of_fuel maxIter ε₂ D)⁻¹ :=
          mul_le_mul_of_nonneg_right h_inv_SD (by positivity)
        refine h0.trans ?_
        rw [div_mul_div_comm, le_div_iff₀ (mul_pos hX_pos hY_pos)]
        exact harea
      have hdec := matDensity_zeroOutSubrect_eq A_rem hX hY hsubX hsubY
      have h_drop :
          (((2 : ℝ) ^ (D ^ 2))⁻¹) * (M_rect2D_of_fuel maxIter ε₂ D)⁻¹ * ((2 : ℝ) ^ D)⁻¹ ≤
            matDensity X Y A_rem - matDensity X Y A_next := by
        have hmul := mul_le_mul h_area_ratio h_dens_2D (by positivity) (by positivity)
        dsimp only [A_next]
        linarith [hdec, hmul]
      have h_step1 :
          1 ≤ (matDensity X Y A_rem - matDensity X Y A_next) *
            ((2 : ℝ) ^ (D + D ^ 2) * M_rect2D_of_fuel maxIter ε₂ D) := by
        have hmul := mul_le_mul_of_nonneg_right h_drop
          (by positivity : 0 ≤ (2 : ℝ) ^ (D + D ^ 2) * M_rect2D_of_fuel maxIter ε₂ D)
        have h_id :
            ((((2 : ℝ) ^ (D ^ 2))⁻¹) * (M_rect2D_of_fuel maxIter ε₂ D)⁻¹ * ((2 : ℝ) ^ D)⁻¹) *
              ((2 : ℝ) ^ (D + D ^ 2) * M_rect2D_of_fuel maxIter ε₂ D) = 1 := by
          have h2D : (2 : ℝ) ^ D ≠ 0 := by positivity
          have h2D2 : (2 : ℝ) ^ (D ^ 2) ≠ 0 := by positivity
          rw [pow_add]
          field_simp [h2D, h2D2, hM_pos.ne']
        rwa [h_id] at hmul
      rw [List.filter_cons, if_pos (decide_eq_true htag_ne), List.length_cons, Nat.cast_add,
        Nat.cast_one]
      linarith

/-- Column-width bound for every non-residual piece in `aDecompositionLoop` (§4.3 of `paper.tex`). -/
lemma aDecompositionLoop_width_le_of_fuel [DecidableEq α] [DecidableEq β]
    (fuel maxIter : ℕ) {X : Finset α} {Y : Finset β} {A_rem : α → β → ℝ}
    {ε₂ : ℝ} {D : ℕ} {ρ₂ α_cap : ℝ}
    {oracleV : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → (α → ℝ)}
    (hX : X.Nonempty) (hY : Y.Nonempty) (hA : IsBinaryMatrix X Y A_rem)
    (hε0 : 0 < ε₂) (hε1 : ε₂ < 1) (hD : 2 ≤ D)
    (hρ_ge : ((2 : ℝ) ^ D)⁻¹ ≤ ρ₂)
    (h_oracle : IsValidOracleV oracleV ε₂ D)
    (hfuel_cap : α_cap ≤ (1 + ε₂ / 2) ^ maxIter * ρ₂) :
    ∀ P ∈ aDecompositionLoop fuel maxIter X Y A_rem ε₂ D ρ₂ α_cap oracleV [],
      P.tag ≠ RectTag.residual →
        (((2 : ℝ) ^ (2 * D))⁻¹) ^ maxIter * (Y.card : ℝ) ≤ (P.Y_sub.card : ℝ) := by
  induction fuel generalizing A_rem with
  | zero =>
    intro P hP hne
    rw [aDecompositionLoop_zero, List.mem_singleton] at hP
    subst hP
    exact False.elim (hne rfl)
  | succ k ih =>
    intro P hP hne
    by_cases hle : matDensity X Y A_rem ≤ ρ₂
    · rw [aDecompositionLoop_of_le k maxIter X Y A_rem ε₂ D ρ₂ α_cap oracleV hle,
        List.mem_singleton] at hP
      subst hP
      exact False.elim (hne rfl)
    · have hgt : ρ₂ < matDensity X Y A_rem := not_le.mp hle
      have hA_ge : ((2 : ℝ) ^ D)⁻¹ ≤ matDensity X Y A_rem := hρ_ge.trans hgt.le
      have hfuel_A :
          α_cap ≤ (1 + ε₂ / 2) ^ maxIter * matDensity X Y A_rem :=
        hfuel_cap.trans (mul_le_mul_of_nonneg_left hgt.le (by positivity))
      have hloop := goodRectLoop_spec maxIter 0 0 hX hY hA hε0 hε1 hD hA_ge h_oracle hfuel_A
      dsimp only at hloop
      rcases hloop with ⟨_, _, _, _, _, _, hsteps_hi, _, _, hY_card, _, _, _⟩
      simp only [Nat.sub_zero, zero_add] at hsteps_hi hY_card
      rw [aDecompositionLoop_cons_eq k maxIter X Y A_rem ε₂ D ρ₂ α_cap oracleV hle] at hP
      rcases List.mem_cons.mp hP with rfl | hP_tail
      · dsimp only
        have h2D_le1 : (((2 : ℝ) ^ (2 * D))⁻¹) ≤ 1 :=
          inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
        have hpow_le :
            (((2 : ℝ) ^ (2 * D))⁻¹) ^ maxIter ≤
              (((2 : ℝ) ^ (2 * D))⁻¹) ^
                (goodRectLoop maxIter X Y A_rem ε₂ D α_cap oracleV 0 0).2.2.2.2 :=
          pow_le_pow_of_le_one (by positivity) h2D_le1 hsteps_hi
        exact (mul_le_mul_of_nonneg_right hpow_le (Nat.cast_nonneg Y.card)).trans hY_card
      · exact ih (IsBinaryMatrix.zeroOut hA) P hP_tail hne

lemma rRect2DFuel_le_div {ε₂ : ℝ} (hε0 : 0 < ε₂) (hε160 : ε₂ ≤ 1 / 160) :
    (rRect2DFuel ε₂ : ℝ) ≤ 97 / ε₂ := by
  unfold rRect2DFuel
  have h1 : 0 < 1 / ε₂ := div_pos one_pos hε0
  have hceil : (Nat.ceil (1 / ε₂) : ℝ) ≤ 1 / ε₂ + 1 := (Nat.ceil_lt_add_one h1.le).le
  have h160 : (1 : ℝ) ≤ 1 / (160 * ε₂) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hsub : 1 / ε₂ + 1 ≤ (161 / 160 : ℝ) * (1 / ε₂) := by
    have : (1 / (160 * ε₂) : ℝ) = (1 / 160 : ℝ) * (1 / ε₂) := by ring
    linarith
  push_cast
  calc
    84 * (Nat.ceil (1 / ε₂) : ℝ) ≤ 84 * ((161 / 160 : ℝ) * (1 / ε₂)) := by nlinarith
    _ ≤ 97 * (1 / ε₂) := by nlinarith [h1.le]
    _ = 97 / ε₂ := by ring

/-- Paper-constant corollary for the column-width factor when $\varepsilon_2 \le 1 / 160$:
$2^{-194 D / \varepsilon_2} |Y| \le (2^{-2D})^{\text{rRect2DFuel}(\varepsilon_2)} |Y|$. -/
theorem rRect2DFuel_width_le_paper {ε₂ : ℝ} (D : ℕ) (Y : Finset β)
    (hε0 : 0 < ε₂) (hε160 : ε₂ ≤ 1 / 160) :
    (2 : ℝ) ^ (- (194 * (D : ℝ) / ε₂)) * (Y.card : ℝ) ≤
      (((2 : ℝ) ^ (2 * D))⁻¹) ^ (rRect2DFuel ε₂) * (Y.card : ℝ) := by
  have hsteps_real : (rRect2DFuel ε₂ : ℝ) ≤ 97 / ε₂ := rRect2DFuel_le_div hε0 hε160
  have hpow_eq : (((2 : ℝ) ^ (2 * D))⁻¹) ^ (rRect2DFuel ε₂) =
      (2 : ℝ) ^ (- (2 * (D : ℝ) * (rRect2DFuel ε₂ : ℝ))) := by
    rw [inv_pow, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
    congr 1
    push_cast
    ring
  have hexp_le : - (194 * (D : ℝ) / ε₂) ≤ - (2 * (D : ℝ) * (rRect2DFuel ε₂ : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left hsteps_real (by positivity : (0 : ℝ) ≤ 2 * (D : ℝ))
    have heq : 2 * (D : ℝ) * (97 / ε₂) = 194 * (D : ℝ) / ε₂ := by ring
    linarith
  have hrpow_le :
      (2 : ℝ) ^ (- (194 * (D : ℝ) / ε₂)) ≤ (((2 : ℝ) ^ (2 * D))⁻¹) ^ (rRect2DFuel ε₂) := by
    rw [hpow_eq]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le
  exact mul_le_mul_of_nonneg_right hrpow_le (Nat.cast_nonneg Y.card)

private lemma filter_singleton_residual_aBoosted (X : Finset α) (Y : Finset β) (M : α → β → ℝ) :
    ([⟨X, Y, M, RectTag.residual, 0⟩] : List (RectPiece α β)).filter
      (fun P => P.tag = RectTag.aBoosted) = [] := by
  rw [List.filter_cons_of_neg]
  · rfl
  · simp

/-- Additional structural and mass-conservation guarantees for `aDecompositionLoop`:
1. Every piece `P` is zero outside `P.X_sub × P.Y_sub` (`P.A_sub x y = submatZeroExt P.X_sub P.Y_sub P.A_sub x y`).
2. Every non-residual piece `P` has `P.scale ≤ D` and strict density `ρ₂ < matDensity P.X_sub P.Y_sub P.A_sub`.
3. The sum of `matDensity P.X_sub P.Y_sub P.A_sub * (|P.X_sub| * |P.Y_sub|)` over `aBoosted` pieces
   is at most `|X| * |Y| * matDensity X Y A_rem` (Theorem 4.4 Clause 3). -/
lemma aDecompositionLoop_extra_spec [DecidableEq α] [DecidableEq β]
    (fuel maxIter : ℕ) {X : Finset α} {Y : Finset β} {A_rem : α → β → ℝ}
    {ε₂ : ℝ} {D : ℕ} {ρ₂ α_cap : ℝ}
    {oracleV : Finset α → Finset β → (α → β → ℝ) → ℝ → ℕ → (α → ℝ)}
    (hX : X.Nonempty) (hY : Y.Nonempty) (hA : IsBinaryMatrix X Y A_rem)
    (hε0 : 0 < ε₂) (hε1 : ε₂ < 1) (hD : 2 ≤ D)
    (hρ_ge : ((2 : ℝ) ^ D)⁻¹ ≤ ρ₂)
    (h_oracle : IsValidOracleV oracleV ε₂ D)
    (hfuel_cap : α_cap ≤ (1 + ε₂ / 2) ^ maxIter * ρ₂) :
    let pieces := aDecompositionLoop fuel maxIter X Y A_rem ε₂ D ρ₂ α_cap oracleV []
    (∀ P ∈ pieces, ∀ x y, P.A_sub x y = submatZeroExt P.X_sub P.Y_sub P.A_sub x y) ∧
    (∀ P ∈ pieces, P.tag ≠ RectTag.residual →
      P.scale ≤ D ∧ ρ₂ < matDensity P.X_sub P.Y_sub P.A_sub) ∧
    (((pieces.filter (fun P => P.tag = RectTag.aBoosted)).map
      (fun P => matDensity P.X_sub P.Y_sub P.A_sub *
        ((P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ)))).sum) ≤
      (X.card : ℝ) * (Y.card : ℝ) * matDensity X Y A_rem := by
  dsimp only
  have hX_pos : (0 : ℝ) < X.card := Nat.cast_pos.mpr hX.card_pos
  have hY_pos : (0 : ℝ) < Y.card := Nat.cast_pos.mpr hY.card_pos
  induction fuel generalizing A_rem with
  | zero =>
    rw [aDecompositionLoop_zero, filter_singleton_residual_aBoosted, List.map_nil, List.sum_nil]
    have h_nonneg : 0 ≤ matDensity X Y A_rem := matDensity_nonneg_of_isBinaryMatrix_2D hA
    refine ⟨?_, ?_, by positivity⟩
    · intro P hP x y
      simp only [List.mem_singleton] at hP
      subst hP
      exact restrictSubrect_eq_submatZeroExt A_rem X Y x y
    · intro P hP hne
      simp only [List.mem_singleton] at hP
      subst hP
      exact False.elim (hne rfl)
  | succ k ih =>
    by_cases hle : matDensity X Y A_rem ≤ ρ₂
    · rw [aDecompositionLoop_of_le k maxIter X Y A_rem ε₂ D ρ₂ α_cap oracleV hle,
        filter_singleton_residual_aBoosted, List.map_nil, List.sum_nil]
      have h_nonneg : 0 ≤ matDensity X Y A_rem := matDensity_nonneg_of_isBinaryMatrix_2D hA
      refine ⟨?_, ?_, by positivity⟩
      · intro P hP x y
        simp only [List.mem_singleton] at hP
        subst hP
        exact restrictSubrect_eq_submatZeroExt A_rem X Y x y
      · intro P hP hne
        simp only [List.mem_singleton] at hP
        subst hP
        exact False.elim (hne rfl)
    · have hgt : ρ₂ < matDensity X Y A_rem := not_le.mp hle
      have hA_ge : ((2 : ℝ) ^ D)⁻¹ ≤ matDensity X Y A_rem := hρ_ge.trans hgt.le
      have hfuel_A :
          α_cap ≤ (1 + ε₂ / 2) ^ maxIter * matDensity X Y A_rem :=
        hfuel_cap.trans (mul_le_mul_of_nonneg_left hgt.le (by positivity))
      have hloop := goodRectLoop_spec maxIter 0 0 hX hY hA hε0 hε1 hD hA_ge h_oracle hfuel_A
      dsimp only at hloop
      rcases hloop with ⟨hsubX, hsubY, _, _, _, _, _, hdens_boost, _, _, _, _, _⟩
      simp only [Nat.sub_zero] at hdens_boost
      rw [aDecompositionLoop_cons_eq k maxIter X Y A_rem ε₂ D ρ₂ α_cap oracleV hle]
      set res := goodRectLoop maxIter X Y A_rem ε₂ D α_cap oracleV 0 0
      set piece_l : RectPiece α β := ⟨res.1, res.2.1, restrictSubrect A_rem res.1 res.2.1, res.2.2.1, res.2.2.2.1⟩
      set A_next := zeroOutSubrect A_rem res.1 res.2.1
      have hA_next : IsBinaryMatrix X Y A_next := IsBinaryMatrix.zeroOut hA
      rcases ih hA_next with ⟨hzero_ih, hscale_ih, hboost_ih⟩
      have hpow_ge1 : 1 ≤ (1 + ε₂ / 2) ^ res.2.2.2.2 :=
        one_le_pow_density_boost hε0 _
      have h2s_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ res.2.2.2.1 := one_le_pow₀ (by norm_num)
      have h_piece_dens : (2 : ℝ) ^ res.2.2.2.1 * ((2 : ℝ) ^ D)⁻¹ ≤ matDensity res.1 res.2.1 A_rem := by
        calc
          (2 : ℝ) ^ res.2.2.2.1 * ((2 : ℝ) ^ D)⁻¹
            ≤ (2 : ℝ) ^ res.2.2.2.1 * 1 * matDensity X Y A_rem := by
              rw [mul_one]
              exact mul_le_mul_of_nonneg_left hA_ge (by positivity)
          _ ≤ (2 : ℝ) ^ res.2.2.2.1 * (1 + ε₂ / 2) ^ res.2.2.2.2 *
                matDensity X Y A_rem := by
              refine mul_le_mul_of_nonneg_right ?_ (le_trans (by positivity) hA_ge)
              exact mul_le_mul_of_nonneg_left hpow_ge1 (by positivity)
          _ ≤ matDensity res.1 res.2.1 A_rem := hdens_boost
      have hs_le_D : res.2.2.2.1 ≤ D := by
        have hdens_le_1 : matDensity res.1 res.2.1 A_rem ≤ 1 :=
          matDensity_le_one_of_isBinaryMatrix_2D (isBinaryMatrix_subset_2D hsubX hsubY hA)
        have h1 : (2 : ℝ) ^ res.2.2.2.1 * ((2 : ℝ) ^ D)⁻¹ ≤ 1 := h_piece_dens.trans hdens_le_1
        have h2 : (2 : ℝ) ^ D * ((2 : ℝ) ^ D)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
        have hle_pow : (2 : ℝ) ^ res.2.2.2.1 ≤ (2 : ℝ) ^ D := by
          by_contra! hgt_pow
          have hmul := mul_lt_mul_of_pos_right hgt_pow (by positivity : (0 : ℝ) < ((2 : ℝ) ^ D)⁻¹)
          linarith
        exact (pow_le_pow_iff_right₀ (by norm_num)).mp hle_pow
      have h_piece_gt : ρ₂ < matDensity res.1 res.2.1 A_rem := by
        have h1 : 1 ≤ (2 : ℝ) ^ res.2.2.2.1 * (1 + ε₂ / 2) ^ res.2.2.2.2 := by
          calc
            (1 : ℝ) = 1 * 1 := by ring
            _ ≤ (2 : ℝ) ^ res.2.2.2.1 * (1 + ε₂ / 2) ^ res.2.2.2.2 :=
              mul_le_mul h2s_ge1 hpow_ge1 (by norm_num) (by linarith [hpow_ge1])
        have h2 : matDensity X Y A_rem ≤ matDensity res.1 res.2.1 A_rem := by
          calc
            matDensity X Y A_rem = 1 * matDensity X Y A_rem := (one_mul _).symm
            _ ≤ (2 : ℝ) ^ res.2.2.2.1 * (1 + ε₂ / 2) ^ res.2.2.2.2 *
                  matDensity X Y A_rem :=
                mul_le_mul_of_nonneg_right h1 (le_trans (by positivity) hA_ge)
            _ ≤ matDensity res.1 res.2.1 A_rem := hdens_boost
        exact lt_of_lt_of_le hgt h2
      have hdec := matDensity_zeroOutSubrect_eq A_rem hX hY hsubX hsubY
      have h_mass_eq :
          (X.card : ℝ) * (Y.card : ℝ) * matDensity X Y A_next +
            matDensity res.1 res.2.1 A_rem * ((res.1.card : ℝ) * (res.2.1.card : ℝ)) =
          (X.card : ℝ) * (Y.card : ℝ) * matDensity X Y A_rem := by
        dsimp only [A_next]
        rw [hdec]
        field_simp [hX_pos.ne', hY_pos.ne']
        ring
      have h_piece_mass_nonneg :
          0 ≤ matDensity res.1 res.2.1 A_rem * ((res.1.card : ℝ) * (res.2.1.card : ℝ)) :=
        mul_nonneg (le_trans (by positivity) h_piece_dens) (by positivity)
      refine ⟨?_, ?_, ?_⟩
      · intro P hP x y
        rcases List.mem_cons.mp hP with rfl | hP_tail
        · exact restrictSubrect_eq_submatZeroExt A_rem res.1 res.2.1 x y
        · exact hzero_ih P hP_tail x y
      · intro P hP hne
        rcases List.mem_cons.mp hP with rfl | hP_tail
        · dsimp only [piece_l]
          rw [matDensity_restrictSubrect_eq]
          exact ⟨hs_le_D, h_piece_gt⟩
        · exact hscale_ih P hP_tail hne
      · rw [List.filter_cons]
        split_ifs with htag_b
        · rw [List.map_cons, List.sum_cons]
          dsimp only [piece_l]
          rw [matDensity_restrictSubrect_eq]
          linarith [hboost_ih, h_mass_eq]
        · linarith [hboost_ih, h_mass_eq, h_piece_mass_nonneg]

/-- Pointwise-to-filtered length bound over scales `s < K`: if every element `P` satisfying `p P`
has `P.scale < K` and `q P = true`, then `(xs.filter p).length` is at most the sum over `s ∈ Finset.range K`
of `(xs.filter (fun P => q P ∧ P.scale = s)).length`. -/
private lemma filter_length_le_sum_range_scale (xs : List (RectPiece α β)) (K : ℕ)
    (p q : RectPiece α β → Bool)
    (h_imp : ∀ P ∈ xs, p P = true → q P = true ∧ P.scale < K) :
    (xs.filter p).length ≤
      ∑ s ∈ Finset.range K, (xs.filter (fun P => q P && decide (P.scale = s))).length := by
  induction xs with
  | nil => simp
  | cons x tl ih =>
    have h_tl : ∀ P ∈ tl, p P = true → q P = true ∧ P.scale < K :=
      fun P hP => h_imp P (List.mem_cons_of_mem x hP)
    have ih_tl := ih h_tl
    rw [List.filter_cons]
    by_cases hpx : p x = true
    · rw [if_pos hpx, List.length_cons]
      rcases h_imp x List.mem_cons_self hpx with ⟨hqx, hs_lt⟩
      have h_mem_range : x.scale ∈ Finset.range K := Finset.mem_range.mpr hs_lt
      have h_sum_ge :
          (∑ s ∈ Finset.range K, (tl.filter (fun P => q P && decide (P.scale = s))).length) + 1 ≤
            ∑ s ∈ Finset.range K, ((x :: tl).filter (fun P => q P && decide (P.scale = s))).length := by
        rw [← Finset.sum_erase_add _ _ h_mem_range,
          ← Finset.sum_erase_add (Finset.range K) (fun s => ((x :: tl).filter (fun P => q P && decide (P.scale = s))).length) h_mem_range]
        have h_er :
            ∑ s ∈ (Finset.range K).erase x.scale,
              (tl.filter (fun P => q P && decide (P.scale = s))).length ≤
            ∑ s ∈ (Finset.range K).erase x.scale,
              ((x :: tl).filter (fun P => q P && decide (P.scale = s))).length := by
          apply Finset.sum_le_sum
          intro s _
          rw [List.filter_cons]
          split_ifs <;> simp
        have h_at :
            ((x :: tl).filter (fun P => q P && decide (P.scale = x.scale))).length =
              (tl.filter (fun P => q P && decide (P.scale = x.scale))).length + 1 := by
          rw [List.filter_cons, if_pos (by simp [hqx]), List.length_cons]
        omega
      omega
    · rw [if_neg hpx]
      refine ih_tl.trans (Finset.sum_le_sum (fun s _ => ?_))
      rw [List.filter_cons]
      split_ifs <;> simp

/-- Total count bound for certified `"regular"` pieces (`L_reg ≤ 48 * 2^{48 D} * M_rect2D ε₂ D`)
from the per-scale piece count bound and `P.scale ≤ 47`. -/
lemma regular_piece_count_le_of_scale_bound (pieces : List (RectPiece α β)) {ε₂ : ℝ} {D : ℕ}
    (hM_nonneg : 0 ≤ M_rect2D ε₂ D)
    (h_reg_scale : ∀ P ∈ pieces, P.tag = RectTag.regular → P.scale ≤ 47)
    (h_scale : ∀ s : ℕ,
      (((pieces.filter (fun P => P.tag ≠ RectTag.residual ∧ P.scale = s)).length : ℝ) ≤
        (2 : ℝ) ^ D * M_rect2D ε₂ D * (2 : ℝ) ^ (s * D))) :
    (((pieces.filter (fun P => P.tag = RectTag.regular)).length : ℝ) ≤
      48 * (2 : ℝ) ^ (48 * D) * M_rect2D ε₂ D) := by
  have h_nat := filter_length_le_sum_range_scale pieces 48
    (fun P => decide (P.tag = RectTag.regular))
    (fun P => decide (P.tag ≠ RectTag.residual))
    (fun P hP hreg => by
      have htag : P.tag = RectTag.regular := of_decide_eq_true hreg
      have hs47 : P.scale ≤ 47 := h_reg_scale P hP htag
      refine ⟨decide_eq_true (by rw [htag]; decide), by omega⟩)
  have h_real :
      (((pieces.filter (fun P => P.tag = RectTag.regular)).length : ℝ)) ≤
        ∑ s ∈ Finset.range 48,
          (((pieces.filter (fun P => P.tag ≠ RectTag.residual ∧ P.scale = s)).length : ℝ)) := by
    have hcast :
        (((pieces.filter (fun P => decide (P.tag = RectTag.regular))).length : ℝ)) ≤
          ∑ s ∈ Finset.range 48,
            (((pieces.filter (fun P => decide (P.tag ≠ RectTag.residual) && decide (P.scale = s))).length : ℝ)) := by
      exact_mod_cast h_nat
    simpa [Bool.decide_and] using hcast
  refine h_real.trans ?_
  calc
    ∑ s ∈ Finset.range 48,
        (((pieces.filter (fun P => P.tag ≠ RectTag.residual ∧ P.scale = s)).length : ℝ))
      ≤ ∑ s ∈ Finset.range 48, ((2 : ℝ) ^ D * M_rect2D ε₂ D * (2 : ℝ) ^ (s * D)) :=
        Finset.sum_le_sum (fun s _ => h_scale s)
    _ ≤ ∑ _s ∈ Finset.range 48, ((2 : ℝ) ^ (48 * D) * M_rect2D ε₂ D) := by
        apply Finset.sum_le_sum
        intro s hs
        have hs_lt : s < 48 := Finset.mem_range.mp hs
        have h_exp : D + s * D ≤ 48 * D := by
          have : 1 + s ≤ 48 := by omega
          calc
            D + s * D = (1 + s) * D := by ring
            _ ≤ 48 * D := Nat.mul_le_mul_right D this
        have h_pow : (2 : ℝ) ^ (D + s * D) ≤ (2 : ℝ) ^ (48 * D) :=
          pow_le_pow_right₀ (by norm_num) h_exp
        calc
          (2 : ℝ) ^ D * M_rect2D ε₂ D * (2 : ℝ) ^ (s * D)
            = (2 : ℝ) ^ (D + s * D) * M_rect2D ε₂ D := by rw [pow_add]; ring
          _ ≤ (2 : ℝ) ^ (48 * D) * M_rect2D ε₂ D :=
            mul_le_mul_of_nonneg_right h_pow hM_nonneg
    _ = 48 * (2 : ℝ) ^ (48 * D) * M_rect2D ε₂ D := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

/-- **Theorem 4.4 (`thm_2d_decomp_concrete`)** for the concrete estimator `concreteOracleV S`:
structural, column-width, piece-count, telescoping and `CostM` running-time clauses. -/
theorem thm_2d_decomp_concrete [DecidableEq α] [DecidableEq β]
    {X : Finset α} {Y : Finset β} {A : α → β → ℝ} {ε₂ : ℝ} {D : ℕ} {α_low α_cap p : ℝ}
    (S : TwoStageSamplerOracle β ε₂)
    (hX : X.Nonempty) (hY : Y.Nonempty) (hA : IsBinaryMatrix X Y A)
    (hε0 : 0 < ε₂) (hε1 : ε₂ < 1) (hD : 2 ≤ D) (hα_low_pos : 0 < α_low)
    (hcap_le : α_cap ≤ (2 : ℝ) ^ (48 : ℕ) * α_low) (hp0 : 0 < p) (hp1 : p < 1) :
    let fuel := rDecomp2DFuel ε₂ D
    let pieces := cappedADecompositionConcrete fuel X Y A ε₂ D α_low α_cap S
    let τ_low := max (((2 : ℝ) ^ D)⁻¹) α_low
    (cappedADecompositionConcreteTracked fuel X Y A ε₂ D α_low α_cap S).1 = pieces ∧
    (cappedADecompositionConcreteTracked fuel X Y A ε₂ D α_low α_cap S).2 ≤
      (fuel + 1) * ((rRect2DFuel ε₂ + 1) *
        ((X.card + Y.card + 2) * (X.card + Y.card + 2) * goodRectStepCostFactor S.c S.k ε₂ D + 1)
        + X.card * Y.card + 1) ∧
    pieces.length ≤ fuel + 1 ∧
    (((pieces.filter (fun P => P.tag ≠ RectTag.residual)).length : ℝ) ≤
       (2 : ℝ) ^ D * M_rect2D ε₂ D * (2 : ℝ) ^ (D ^ 2)) ∧
    (∀ P ∈ pieces, P.tag ≠ RectTag.residual →
      (((2 : ℝ) ^ (2 * D))⁻¹) ^ (rRect2DFuel ε₂) * (Y.card : ℝ) ≤ (P.Y_sub.card : ℝ)) ∧
    (∀ x ∈ X, ∀ y ∈ Y, ((pieces.map (fun P => P.A_sub x y)).sum) = A x y) ∧
    (∀ P ∈ pieces,
      P.X_sub ⊆ X ∧ P.Y_sub ⊆ Y ∧ P.X_sub.Nonempty ∧ P.Y_sub.Nonempty ∧
      IsBinaryMatrix P.X_sub P.Y_sub P.A_sub ∧
      (P.tag = RectTag.residual →
        matDensity X Y P.A_sub ≤ τ_low) ∧
      (P.tag ≠ RectTag.residual →
        (P.tag = RectTag.regular ∨ P.tag = RectTag.aBoosted) ∧
        (2 : ℝ) ^ P.scale * τ_low ≤ matDensity P.X_sub P.Y_sub P.A_sub ∧
        (((2 : ℝ) ^ (P.scale * D))⁻¹) * (M_rect2D ε₂ D)⁻¹ * ((X.card : ℝ) * (Y.card : ℝ)) ≤
          (P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ) ∧
        (P.tag = RectTag.aBoosted → α_cap ≤ matDensity P.X_sub P.Y_sub P.A_sub) ∧
        (P.tag = RectTag.regular →
          matDensity P.X_sub P.Y_sub P.A_sub < α_cap ∧
          P.scale ≤ 47 ∧
          IsGridRegular P.X_sub P.Y_sub P.A_sub ε₂ 2 D ∧
          IsEpsMinDegree P.X_sub P.Y_sub P.A_sub ε₂))) ∧
    (∀ s : ℕ,
      let L_s := (pieces.filter (fun P => P.tag ≠ RectTag.residual ∧ P.scale = s)).length
      (L_s : ℝ) ≤ M_rect2D ε₂ D * τ_low⁻¹ * (2 : ℝ) ^ (s * D) * matDensity X Y A ∧
      (L_s : ℝ) ≤ (2 : ℝ) ^ D * M_rect2D ε₂ D * (2 : ℝ) ^ (s * D)) ∧
    (((pieces.filter (fun P => P.tag ≠ RectTag.residual)).map
      (fun P => (2 : ℝ) ^ P.scale * τ_low * ((P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ)))).sum) ≤
      (X.card : ℝ) * (Y.card : ℝ) * matDensity X Y A ∧
    (((pieces.map
      (fun P => (matDensity P.X_sub P.Y_sub P.A_sub) ^ p *
        ((P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ)))).sum) ≤
      (1 / p) * (matDensity X Y A) ^ p * ((X.card : ℝ) * (Y.card : ℝ))) ∧
    (((pieces.map
      (fun P => (matDensity P.X_sub P.Y_sub P.A_sub) ^ (1 / 4 : ℝ) *
        ((P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ)))).sum) ≤
      4 * (matDensity X Y A) ^ (1 / 4 : ℝ) * ((X.card : ℝ) * (Y.card : ℝ))) ∧
    (∀ P ∈ pieces, P.tag = RectTag.residual → P.X_sub = X ∧ P.Y_sub = Y) ∧
    (∀ P ∈ pieces, ∀ x y, P.A_sub x y = submatZeroExt P.X_sub P.Y_sub P.A_sub x y) ∧
    (∀ P ∈ pieces, P.tag ≠ RectTag.residual →
      P.scale ≤ D ∧ τ_low < matDensity P.X_sub P.Y_sub P.A_sub) ∧
    (((pieces.filter (fun P => P.tag = RectTag.aBoosted)).map
      (fun P => matDensity P.X_sub P.Y_sub P.A_sub *
        ((P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ)))).sum) ≤
      (X.card : ℝ) * (Y.card : ℝ) * matDensity X Y A ∧
    (((pieces.filter (fun P => P.tag = RectTag.regular)).length : ℝ) ≤
      48 * (2 : ℝ) ^ (48 * D) * M_rect2D ε₂ D) := by
  dsimp only
  set fuel := rDecomp2DFuel ε₂ D
  set τ_low := max (((2 : ℝ) ^ D)⁻¹) α_low
  have h_oracle : IsValidOracleV (concreteOracleV (α := α) S) ε₂ D :=
    concreteOracleV_isValid S hε0.le (by omega)
  have hτ_ge_2D : ((2 : ℝ) ^ D)⁻¹ ≤ τ_low := le_max_left _ _
  have hτ_ge_low : α_low ≤ τ_low := le_max_right _ _
  have hpow48 := pow_rRect2DFuel_ge hε0
  have hfuel_cap : α_cap ≤ (1 + ε₂ / 2) ^ (rRect2DFuel ε₂) * τ_low := by
    calc
      α_cap ≤ (2 : ℝ) ^ (48 : ℕ) * α_low := hcap_le
      _ ≤ (1 + ε₂ / 2) ^ (rRect2DFuel ε₂) * τ_low :=
        mul_le_mul hpow48 hτ_ge_low hα_low_pos.le (by positivity)
  have hmain := thm_2d_decomp fuel hX hY hA hε0 hε1 hD hα_low_pos hcap_le h_oracle hp0 hp1
  dsimp only at hmain
  rcases hmain with ⟨hpart, hpieces, hscale, hmass, hriem_p, hriem_q⟩
  have hlen : (cappedADecompositionConcrete fuel X Y A ε₂ D α_low α_cap S).length ≤ fuel + 1 :=
    aDecompositionLoop_length_le fuel (rRect2DFuel ε₂) X Y A ε₂ D τ_low α_cap (concreteOracleV S)
  have hM_pos : 0 < M_rect2D ε₂ D := M_rect2D_pos hε0 D
  have hnonres_cnt :
      ((((cappedADecompositionConcrete fuel X Y A ε₂ D α_low α_cap S).filter
        (fun P => P.tag ≠ RectTag.residual)).length : ℝ) ≤
        (2 : ℝ) ^ D * M_rect2D ε₂ D * (2 : ℝ) ^ (D ^ 2)) := by
    have haux := aDecompositionLoop_nonresidual_count_le_aux fuel (rRect2DFuel ε₂)
      hX hY hA hε0 hε1 hD hτ_ge_2D h_oracle hfuel_cap
    have hA_le1 : matDensity X Y A ≤ 1 := matDensity_le_one_of_isBinaryMatrix_2D hA
    have hmul :
        matDensity X Y A * ((2 : ℝ) ^ (D + D ^ 2) * M_rect2D ε₂ D) ≤
          (2 : ℝ) ^ D * M_rect2D ε₂ D * (2 : ℝ) ^ (D ^ 2) := by
      calc
        matDensity X Y A * ((2 : ℝ) ^ (D + D ^ 2) * M_rect2D ε₂ D)
          ≤ 1 * ((2 : ℝ) ^ (D + D ^ 2) * M_rect2D ε₂ D) :=
            mul_le_mul_of_nonneg_right hA_le1 (by positivity)
        _ = (2 : ℝ) ^ D * M_rect2D ε₂ D * (2 : ℝ) ^ (D ^ 2) := by
            rw [pow_add]; ring
    exact haux.trans hmul
  have hwidth :
      ∀ P ∈ cappedADecompositionConcrete fuel X Y A ε₂ D α_low α_cap S,
        P.tag ≠ RectTag.residual →
          (((2 : ℝ) ^ (2 * D))⁻¹) ^ (rRect2DFuel ε₂) * (Y.card : ℝ) ≤ (P.Y_sub.card : ℝ) :=
    aDecompositionLoop_width_le_of_fuel fuel (rRect2DFuel ε₂)
      hX hY hA hε0 hε1 hD hτ_ge_2D h_oracle hfuel_cap
  have hres_xy :
      ∀ P ∈ cappedADecompositionConcrete fuel X Y A ε₂ D α_low α_cap S,
        P.tag = RectTag.residual → P.X_sub = X ∧ P.Y_sub = Y := by
    intro P hP hres
    have h := aDecompositionLoop_residual_density_le fuel hX hY hA hε0 hε1 hD
      hτ_ge_2D h_oracle hfuel_cap le_rfl P hP hres
    exact ⟨h.1, h.2.1⟩
  rcases aDecompositionLoop_extra_spec fuel (rRect2DFuel ε₂)
    hX hY hA hε0 hε1 hD hτ_ge_2D h_oracle hfuel_cap with ⟨hzero_ext, hscale_gt, hboost_mass⟩
  have hreg_cnt :
      ((((cappedADecompositionConcrete fuel X Y A ε₂ D α_low α_cap S).filter
        (fun P => P.tag = RectTag.regular)).length : ℝ) ≤
        48 * (2 : ℝ) ^ (48 * D) * M_rect2D ε₂ D) := by
    refine regular_piece_count_le_of_scale_bound _ hM_pos.le ?_ (fun s => (hscale s).2)
    intro P hP hreg
    have hne : P.tag ≠ RectTag.residual := by rw [hreg]; decide
    exact ((hpieces P hP).2.2.2.2.2.2 hne).2.2.2.2 hreg |>.2.1
  refine ⟨cappedADecompositionConcreteTracked_fst fuel X Y A ε₂ D α_low α_cap S,
    cappedADecompositionConcreteTracked_snd_le fuel X Y A ε₂ D α_low α_cap S,
    hlen, hnonres_cnt, hwidth, hpart, ?_, hscale, hmass, hriem_p, hriem_q,
    hres_xy, hzero_ext, hscale_gt, hboost_mass, hreg_cnt⟩
  intro P hP
  rcases hpieces P hP with ⟨hX_sub, hY_sub, hX_ne, hY_ne, hbin, hres, hnonres⟩
  exact ⟨hX_sub, hY_sub, hX_ne, hY_ne, hbin, hres le_rfl, hnonres⟩

/-- **Corollary 4.5 (`\label{cor:uncapped-2d}`) Concrete Uncapped Decomposition (`thm_2d_decomp_uncapped_concrete`,
§4.3 of `paper.tex`)**:
Combines all structural, shrinkage, piece-count, Riemann-sum telescoping, and `CostM` running-time
guarantees for `aDecompositionConcrete` / `aDecompositionConcreteTracked` with
`fuel := rUncappedDecomp2DFuel ε₂ D`, `maxIter := rUncappedRect2DFuel ε₂ D`, and `ρ₂ = 2^{-D}`
across all $D \ge 2$. -/
theorem thm_2d_decomp_uncapped_concrete [DecidableEq α] [DecidableEq β]
    {X : Finset α} {Y : Finset β} {A : α → β → ℝ} {ε₂ : ℝ} {D : ℕ} {p : ℝ}
    (S : TwoStageSamplerOracle β ε₂)
    (hX : X.Nonempty) (hY : Y.Nonempty) (hA : IsBinaryMatrix X Y A)
    (hε0 : 0 < ε₂) (hε1 : ε₂ < 1) (hD : 2 ≤ D) (hp0 : 0 < p) (hp1 : p < 1) :
    let fuel := rUncappedDecomp2DFuel ε₂ D
    let maxIter := rUncappedRect2DFuel ε₂ D
    let ρ₂ := ((2 : ℝ) ^ D)⁻¹
    let pieces := aDecompositionConcrete fuel maxIter X Y A ε₂ D ρ₂ S
    (aDecompositionConcreteTracked fuel maxIter X Y A ε₂ D ρ₂ S).1 = pieces ∧
    (aDecompositionConcreteTracked fuel maxIter X Y A ε₂ D ρ₂ S).2 ≤
      (fuel + 1) * ((maxIter + 1) *
        ((X.card + Y.card + 2) * (X.card + Y.card + 2) * goodRectStepCostFactor S.c S.k ε₂ D + 1)
        + X.card * Y.card + 1) ∧
    pieces.length ≤ fuel + 1 ∧
    (((pieces.filter (fun P => P.tag ≠ RectTag.residual)).length : ℝ) ≤
      (2 : ℝ) ^ D * M_uncappedRect2D ε₂ D * (2 : ℝ) ^ (D ^ 2)) ∧
    (∀ P ∈ pieces, P.tag ≠ RectTag.residual →
      (((2 : ℝ) ^ (2 * D))⁻¹) ^ maxIter * (Y.card : ℝ) ≤ (P.Y_sub.card : ℝ)) ∧
    (∀ x ∈ X, ∀ y ∈ Y, ((pieces.map (fun P => P.A_sub x y)).sum) = A x y) ∧
    (∀ P ∈ pieces,
      P.X_sub ⊆ X ∧ P.Y_sub ⊆ Y ∧ P.X_sub.Nonempty ∧ P.Y_sub.Nonempty ∧
      IsBinaryMatrix P.X_sub P.Y_sub P.A_sub ∧
      (P.tag = RectTag.residual →
        matDensity X Y P.A_sub ≤ ρ₂) ∧
      (P.tag ≠ RectTag.residual →
        P.tag = RectTag.regular ∧
        P.scale ≤ D ∧
        ρ₂ < matDensity P.X_sub P.Y_sub P.A_sub ∧
        (2 : ℝ) ^ P.scale * ρ₂ ≤ matDensity P.X_sub P.Y_sub P.A_sub ∧
        (((2 : ℝ) ^ (P.scale * D))⁻¹) * (M_uncappedRect2D ε₂ D)⁻¹ * ((X.card : ℝ) * (Y.card : ℝ)) ≤
          (P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ) ∧
        IsGridRegular P.X_sub P.Y_sub P.A_sub ε₂ 2 D ∧
        IsEpsMinDegree P.X_sub P.Y_sub P.A_sub ε₂)) ∧
    (∀ s : ℕ,
      let L_s := (pieces.filter (fun P => P.tag ≠ RectTag.residual ∧ P.scale = s)).length
      (L_s : ℝ) ≤ (2 : ℝ) ^ D * M_uncappedRect2D ε₂ D * (2 : ℝ) ^ (s * D)) ∧
    (((pieces.filter (fun P => P.tag ≠ RectTag.residual)).map
      (fun P => (2 : ℝ) ^ P.scale * ρ₂ * ((P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ)))).sum) ≤
      (X.card : ℝ) * (Y.card : ℝ) * matDensity X Y A ∧
    (((pieces.map
      (fun P => (matDensity P.X_sub P.Y_sub P.A_sub) ^ p *
        ((P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ)))).sum) ≤
      (1 / p) * (matDensity X Y A) ^ p * ((X.card : ℝ) * (Y.card : ℝ))) ∧
    (((pieces.map
      (fun P => (matDensity P.X_sub P.Y_sub P.A_sub) ^ (1 / 4 : ℝ) *
        ((P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ)))).sum) ≤
      4 * (matDensity X Y A) ^ (1 / 4 : ℝ) * ((X.card : ℝ) * (Y.card : ℝ))) ∧
    (∀ P ∈ pieces, P.tag = RectTag.residual → P.X_sub = X ∧ P.Y_sub = Y) ∧
    (∀ P ∈ pieces, ∀ x y, P.A_sub x y = submatZeroExt P.X_sub P.Y_sub P.A_sub x y) := by
  dsimp only
  set fuel := rUncappedDecomp2DFuel ε₂ D
  set maxIter := rUncappedRect2DFuel ε₂ D
  set ρ₂ := ((2 : ℝ) ^ D)⁻¹
  have h_oracle : IsValidOracleV (concreteOracleV (α := α) S) ε₂ D :=
    concreteOracleV_isValid S hε0.le (by omega)
  have hpowD1 : (2 : ℝ) ^ (D + 1) ≤ (1 + ε₂ / 2) ^ maxIter :=
    pow_rUncappedRect2DFuel_ge hε0 D
  have h2_eq : (2 : ℝ) = (2 : ℝ) ^ (D + 1) * ρ₂ := by
    dsimp only [ρ₂]
    rw [pow_succ, mul_comm ((2 : ℝ) ^ D) 2, mul_assoc,
      mul_inv_cancel₀ (by positivity), mul_one]
  have hfuel_cap : (2 : ℝ) ≤ (1 + ε₂ / 2) ^ maxIter * ρ₂ := by
    calc
      (2 : ℝ) = (2 : ℝ) ^ (D + 1) * ρ₂ := h2_eq
      _ ≤ (1 + ε₂ / 2) ^ maxIter * ρ₂ :=
        mul_le_mul_of_nonneg_right hpowD1 (by positivity)
  have hmain := thm_2d_decomp_uncapped hX hY hA hε0 hε1 hD h_oracle hp0 hp1
  dsimp only at hmain
  rcases hmain with ⟨hpart, hpieces, hscale, hriem_p⟩
  have hmass := sum_extracted_area_le_initial_mass fuel maxIter
    hX hY hA hε0 hε1 hD le_rfl h_oracle hfuel_cap
  have hriem_q := (thm_2d_decomp_riemann_telescoping fuel maxIter
    hX hY hA hε0 hε1 hD le_rfl h_oracle hfuel_cap
    (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)).2
  have h4 : (1 : ℝ) / (1 / 4 : ℝ) = 4 := by norm_num
  rw [h4] at hriem_q
  have hlen : (aDecompositionConcrete fuel maxIter X Y A ε₂ D ρ₂ S).length ≤ fuel + 1 :=
    aDecompositionLoop_length_le fuel maxIter X Y A ε₂ D ρ₂ 2 (concreteOracleV S)
  have hM_pos : 0 < M_uncappedRect2D ε₂ D := M_uncappedRect2D_pos hε0 D
  have hnonres_cnt :
      ((((aDecompositionConcrete fuel maxIter X Y A ε₂ D ρ₂ S).filter
        (fun P => P.tag ≠ RectTag.residual)).length : ℝ) ≤
        (2 : ℝ) ^ D * M_uncappedRect2D ε₂ D * (2 : ℝ) ^ (D ^ 2)) := by
    have haux := aDecompositionLoop_nonresidual_count_le_aux fuel maxIter
      hX hY hA hε0 hε1 hD le_rfl h_oracle hfuel_cap
    have hA_le1 : matDensity X Y A ≤ 1 := matDensity_le_one_of_isBinaryMatrix_2D hA
    have hmul :
        matDensity X Y A * ((2 : ℝ) ^ (D + D ^ 2) * M_uncappedRect2D ε₂ D) ≤
          (2 : ℝ) ^ D * M_uncappedRect2D ε₂ D * (2 : ℝ) ^ (D ^ 2) := by
      calc
        matDensity X Y A * ((2 : ℝ) ^ (D + D ^ 2) * M_uncappedRect2D ε₂ D)
          ≤ 1 * ((2 : ℝ) ^ (D + D ^ 2) * M_uncappedRect2D ε₂ D) :=
            mul_le_mul_of_nonneg_right hA_le1 (by positivity)
        _ = (2 : ℝ) ^ D * M_uncappedRect2D ε₂ D * (2 : ℝ) ^ (D ^ 2) := by
            rw [pow_add]; ring
    exact haux.trans hmul
  have hwidth :
      ∀ P ∈ aDecompositionConcrete fuel maxIter X Y A ε₂ D ρ₂ S,
        P.tag ≠ RectTag.residual →
          (((2 : ℝ) ^ (2 * D))⁻¹) ^ maxIter * (Y.card : ℝ) ≤ (P.Y_sub.card : ℝ) :=
    aDecompositionLoop_width_le_of_fuel fuel maxIter
      hX hY hA hε0 hε1 hD le_rfl h_oracle hfuel_cap
  have hA_le1 : matDensity X Y A ≤ 1 := matDensity_le_one_of_isBinaryMatrix_2D hA
  have hfuel_bound :
      matDensity X Y A * ((2 : ℝ) ^ (D + D ^ 2) * M_uncappedRect2D ε₂ D) ≤ (fuel : ℝ) := by
    have h1 : matDensity X Y A * ((2 : ℝ) ^ (D + D ^ 2) * M_uncappedRect2D ε₂ D) ≤
        1 * ((2 : ℝ) ^ (D + D ^ 2) * M_uncappedRect2D ε₂ D) :=
      mul_le_mul_of_nonneg_right hA_le1 (by positivity)
    have h2 : (2 : ℝ) ^ (D + D ^ 2) * M_uncappedRect2D ε₂ D ≤
        (Nat.ceil ((2 : ℝ) ^ (D + D ^ 2) * M_uncappedRect2D ε₂ D) : ℝ) := Nat.le_ceil _
    have h3 : (Nat.ceil ((2 : ℝ) ^ (D + D ^ 2) * M_uncappedRect2D ε₂ D) : ℝ) ≤
        (fuel : ℝ) := by
      dsimp only [fuel, rUncappedDecomp2DFuel]
      push_cast
      linarith
    linarith
  have hres_all := aDecompositionLoop_residual_density_le_aux_of_fuel fuel maxIter
    hX hY hA hε0 hε1 hD le_rfl h_oracle hfuel_cap hfuel_bound
  have hres_xy :
      ∀ P ∈ aDecompositionConcrete fuel maxIter X Y A ε₂ D ρ₂ S,
        P.tag = RectTag.residual → P.X_sub = X ∧ P.Y_sub = Y :=
    fun P hP hres => ⟨(hres_all P hP hres).1, (hres_all P hP hres).2.1⟩
  rcases aDecompositionLoop_extra_spec fuel maxIter
    hX hY hA hε0 hε1 hD le_rfl h_oracle hfuel_cap with ⟨hzero_ext, hscale_gt, _⟩
  refine ⟨aDecompositionConcreteTracked_fst fuel maxIter X Y A ε₂ D ρ₂ S,
    aDecompositionConcreteTracked_snd_le fuel maxIter X Y A ε₂ D ρ₂ S,
    hlen, hnonres_cnt, hwidth, hpart, ?_, hscale, hmass, hriem_p, hriem_q,
    hres_xy, hzero_ext⟩
  intro P hP
  rcases hpieces P hP with ⟨hX_sub, hY_sub, hX_ne, hY_ne, hbin, hres, hnonres⟩
  refine ⟨hX_sub, hY_sub, hX_ne, hY_ne, hbin, hres, ?_⟩
  intro hne
  rcases hnonres hne with ⟨htag, hs, hdens, harea, hgrid, hmin⟩
  exact ⟨htag, hs, (hscale_gt P hP hne).2, hdens, harea, hgrid, hmin⟩

end ConcreteDecomp2D

#verify_standard_axioms BMMGrid.thm_2d_decomp_uncapped
#verify_standard_axioms BMMGrid.thm_2d_decomp_uncapped_concrete

end BMMGrid
