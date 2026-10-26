import BMMGrid.DyadicBucketingAndGoodCube

/-!
# Section 5: 3D Regularity Potential & Recurrence (`BMMGrid/Decomp3DPotential.lean`)

This module formalizes the potential-budget, Base Case 2, 2D slice transfer, and depth-recurrence
components of Section 5 (`\label{sec:3d}`, §5.2, §5.4 & §5.5) of `paper.tex` (the full
recursive `Decompose3D` loop and Theorem 1.1 (`\label{thm:main-decomp}`) are assembled in
`BMMGrid/Decomp3D.lean`):
1. **Concavity & Fourth-Moment Cauchy–Schwarz Helpers (`\eqref{eq:concavity-drop}`)**:
   - `one_sub_rpow_quarter_le` (`(1 - u)^{1/4} ≤ 1 - u / 4` for `u ∈ [0, 1]`, §5.4),
   - Fourth-power Cauchy–Schwarz inequality `sum_pow_four_le`.
2. **Algorithm 5 (`Decompose3D` Line 23 `\label{line:3d-reca}`) (`bucketedRec` & `bucketedRecTracked`, §5.2)**:
   - Dyadic column-degree bucketing recursion wrapper and its tracked `CostM` counterpart,
   - Potential bound `bucketedRec_potential_bound` (`\eqref{eq:bucketed-rec-bound}`, §5.4).
3. **Table 6 (`\label{tab:potential-budget}`) Potential Budget Analysis (§5.4)**:
   - Concavity drop `concavity_drop_beta_rem` (`\eqref{eq:concavity-drop}`, §5.4),
   - Table 6 (`\label{tab:potential-budget}`) row numerical helpers (`four_mul_six_rpow_quarter_le_seven`
     and `twentyeight_mul_two_rpow_half_le_forty`, §5.4),
   - Five-term budget closure (`table1_budget_cinco_sum_le`, §5.4).
4. **Base Case 2 (`baseCase2Decomposition`), 2D Slice Transfer & Jump-Adaptive Depth Recurrence
   (`\eqref{eq:th-inductive}`, §5.2, §5.4 & §5.5)**:
   - `baseCase2Decomposition`, `baseCase2DecompositionTracked`, and Claim 5.6
     (`\label{clm:pot-base}`, `baseCase2Decomposition_potential_le`),
   - 2D slice transfer and Riemann-sum bounds `cappedADecomp3DLoop_rpow_quarter_sum_le`,
     `cappedADecomp3DLoop_scale_and_residual_spec`, and `cappedGoodCube_normal_extra_spec`,
   - Computable integer depth-jump increments `rawDeltaHBNat` / `rawDeltaHANat` and tree bound
     `QTree3D`, `GammaTree3D`, `T3DTree`, `T3DTree_jump_le`, and `step_T3DTree_close`.
-/

namespace BMMGrid

open scoped BigOperators

/-!
## Part 1: Concavity & Fourth-Power Cauchy–Schwarz Inequalities
(`paper.tex` `\eqref{eq:concavity-drop}`, §5.4)
-/

section ConcavityAndCauchySchwarz

/-- **Concavity Drop Inequality (`one_sub_rpow_quarter_le`, `\eqref{eq:concavity-drop}`,
§5.4 of `paper.tex`)**:
For all $u \in [0, 1]$, $(1 - u)^{1/4} \le 1 - \frac{1}{4} u$. -/
theorem one_sub_rpow_quarter_le {u : ℝ} (_hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (1 - u) ^ ((1 : ℝ) / 4) ≤ 1 - u / 4 := by
  have h1mu : 0 ≤ 1 - u := by linarith
  have h1mu4 : 0 ≤ 1 - u / 4 := by linarith
  have hpow4 : 1 - u ≤ (1 - u / 4) ^ (4 : ℕ) := by
    have hdiff : (1 - u / 4) ^ (4 : ℕ) - (1 - u) = (u / 16) ^ 2 * ((u - 8) ^ 2 + 32) := by ring
    have hnonneg : 0 ≤ (u / 16) ^ 2 * ((u - 8) ^ 2 + 32) := by positivity
    linarith
  calc
    (1 - u) ^ ((1 : ℝ) / 4) ≤ ((1 - u / 4) ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow h1mu hpow4 (by norm_num)
    _ = 1 - u / 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h1mu4]
      norm_num

lemma rpow_quarter_pow_four {x : ℝ} (hx : 0 ≤ x) :
    (x ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

lemma le_of_pow_four_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ (4 : ℕ) ≤ b ^ (4 : ℕ)) :
    a ≤ b := by
  calc
    a = (a ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
      norm_num
    _ ≤ (b ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (by positivity) h (by norm_num)
    _ = b := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hb]
      norm_num

/-- Fourth-power Cauchy–Schwarz inequality for a finite sum:
$\left(\sum_{s \in S} u(s)\right)^4 \le |S|^3 \sum_{s \in S} u(s)^4$. -/
lemma sum_pow_four_le {σ : Type*} (S : Finset σ) (u : σ → ℝ) :
    (∑ s ∈ S, u s) ^ (4 : ℕ) ≤ (S.card : ℝ) ^ (3 : ℕ) * ∑ s ∈ S, (u s) ^ (4 : ℕ) := by
  have h1 : (∑ s ∈ S, u s) ^ 2 ≤ (S.card : ℝ) * ∑ s ∈ S, (u s) ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) u
    simpa using hcs
  have h2 : (∑ s ∈ S, (u s) ^ 2) ^ 2 ≤ (S.card : ℝ) * ∑ s ∈ S, ((u s) ^ 2) ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun s => (u s) ^ 2)
    simpa using hcs
  have h1_sq : ((∑ s ∈ S, u s) ^ 2) ^ 2 ≤ ((S.card : ℝ) * ∑ s ∈ S, (u s) ^ 2) ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg _) h1 2
  have h4_eq : ∑ s ∈ S, ((u s) ^ 2) ^ 2 = ∑ s ∈ S, (u s) ^ (4 : ℕ) :=
    Finset.sum_congr rfl (fun s _ => by ring)
  calc
    (∑ s ∈ S, u s) ^ (4 : ℕ) = ((∑ s ∈ S, u s) ^ 2) ^ 2 := by ring
    _ ≤ ((S.card : ℝ) * ∑ s ∈ S, (u s) ^ 2) ^ 2 := h1_sq
    _ = (S.card : ℝ) ^ 2 * (∑ s ∈ S, (u s) ^ 2) ^ 2 := by ring
    _ ≤ (S.card : ℝ) ^ 2 * ((S.card : ℝ) * ∑ s ∈ S, ((u s) ^ 2) ^ 2) :=
      mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = (S.card : ℝ) ^ (3 : ℕ) * ∑ s ∈ S, (u s) ^ (4 : ℕ) := by rw [h4_eq]; ring

end ConcavityAndCauchySchwarz

/-!
## Part 2: Algorithm 5 (`Decompose3D` Line 23 `\label{line:3d-reca}`) (`bucketedRec` & `bucketedRecTracked`) and Potential Bound
(§5.2 & §5.4 of `paper.tex`, `\eqref{eq:bucketed-rec-bound}`)
-/

section BucketedRec

variable {α β γ : Type*}

lemma cubePotential_append (p q : ℝ) (S₁ S₂ : List (CubePiece α β γ)) :
    cubePotential p q (S₁ ++ S₂) = cubePotential p q S₁ + cubePotential p q S₂ := by
  unfold cubePotential
  rw [List.map_append, List.sum_append]

lemma cubePotential_flatMap {ι : Type*} (p q : ℝ) (L : List ι)
    (f : ι → List (CubePiece α β γ)) :
    cubePotential p q (L.flatMap f) = (L.map (fun i => cubePotential p q (f i))).sum := by
  induction L with
  | nil => simp [cubePotential]
  | cons a L ih =>
    rw [List.flatMap_cons, cubePotential_append, List.map_cons, List.sum_cons, ih]

lemma flatMapListTracked_snd_le_linear {σ τ : Type*} (f : σ → CostM (List τ))
    (xs : List σ) (K M : ℕ)
    (hf : ∀ x ∈ xs, (f x).2 ≤ K * (f x).1.length + M) :
    (flatMapListTracked f xs).2 ≤
      (K + 1) * (flatMapListTracked f xs).1.length + (M + 1) * xs.length + 1 := by
  induction xs with
  | nil =>
    simp [flatMapListTracked, retTracked]
  | cons x xs ih =>
    have hx := hf x List.mem_cons_self
    have hxs := ih (fun y hy => hf y (List.mem_cons_of_mem x hy))
    simp only [flatMapListTracked, CostM.bind_snd, appendListTracked_snd,
      CostM.bind_fst, appendListTracked_fst, List.length_append, List.length_cons] at hxs ⊢
    nlinarith

/-- **Algorithm 5 (`Decompose3D` Line 23 `\label{line:3d-reca}`) (`bucketedRec`, §5.2 of `paper.tex`)**:
Partitions $Y' = \bigsqcup_{j=0}^{D-1} Y'_j$ according to column degrees $\deg_{(A')^T}(y)$ via
`dyadicColBucket X' Y' A' μ j`, sets $\alpha'_j = 2^j \mu$ (`dyadicColAlpha μ j`), and unions the
recursive sub-decompositions over all non-empty buckets $Y'_j$ (passing the bucket index $j$ alongside
$\alpha'_j$ so recursive callers can maintain exact integer numerator/denominator representations). -/
noncomputable def bucketedRec [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X' : Finset α) (Y' : Finset β) (Z' : Finset γ)
    (A' : α → β → ℝ) (B' : β → γ → ℝ) (μ : ℝ) (D : ℕ)
    (recCall : Finset α → Finset β → Finset γ →
      (α → β → ℝ) → (β → γ → ℝ) → ℝ → ℕ → List (CubePiece α β γ)) :
    List (CubePiece α β γ) :=
  ((List.range D).filter (fun j => decide (dyadicColBucket X' Y' A' μ j).Nonempty)).flatMap
    (fun j =>
      let Y'_j := dyadicColBucket X' Y' A' μ j
      recCall X' Y'_j Z'
        (submatZeroExt X' Y'_j A') (submatZeroExt Y'_j Z' B') (dyadicColAlpha μ j) j)

/-- Tracked `CostM` implementation of Algorithm 5 (`Decompose3D` Line 23 `\label{line:3d-reca}`)
(`bucketedRecTracked`), binding `dyadicColBucketingTracked`, `filterListByTracked`,
`flatMapListTracked`, and `scanMatrixTracked` directly on the returned `(j, Y'_j)` bucket pairs. -/
noncomputable def bucketedRecTracked [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X' : Finset α) (Y' : Finset β) (Z' : Finset γ)
    (A' : α → β → ℝ) (B' : β → γ → ℝ) (μ : ℝ) (D : ℕ)
    (recCallTracked : Finset α → Finset β → Finset γ →
      (α → β → ℝ) → (β → γ → ℝ) → ℝ → ℕ → CostM (List (CubePiece α β γ))) :
    CostM (List (CubePiece α β γ)) :=
  CostM.bind (dyadicColBucketingTracked X' Y' A' μ D) (fun buckets =>
    CostM.bind
      (filterListByTracked
        (fun b : ℕ × Finset β => decide b.2.Nonempty)
        buckets)
      (fun activeBuckets =>
        CostM.bind
          (flatMapListTracked
            (fun b : ℕ × Finset β =>
              recCallTracked X' b.2 Z'
                (submatZeroExt X' b.2 A') (submatZeroExt b.2 Z' B') (dyadicColAlpha μ b.1) b.1)
            activeBuckets)
          (fun res => scanMatrixTracked Y' Z' res)))

@[simp]
theorem bucketedRecTracked_fst [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X' : Finset α) (Y' : Finset β) (Z' : Finset γ)
    (A' : α → β → ℝ) (B' : β → γ → ℝ) (μ : ℝ) (D : ℕ)
    (recCallTracked : Finset α → Finset β → Finset γ →
      (α → β → ℝ) → (β → γ → ℝ) → ℝ → ℕ → CostM (List (CubePiece α β γ))) :
    (bucketedRecTracked X' Y' Z' A' B' μ D recCallTracked).1 =
      bucketedRec X' Y' Z' A' B' μ D (fun X₁ Y₁ Z₁ A₁ B₁ α₁ j₁ =>
        (recCallTracked X₁ Y₁ Z₁ A₁ B₁ α₁ j₁).1) := by
  simp [bucketedRecTracked, bucketedRec, dyadicColBucketing,
    List.filter_map, List.flatMap_map, Function.comp_def]

lemma list_filter_map_sum_le (L : List ℕ) (p : ℕ → Bool) (f : ℕ → ℝ)
    (hf : ∀ j ∈ L, 0 ≤ f j) :
    ((L.filter p).map f).sum ≤ (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a l ih =>
    have ha : 0 ≤ f a := hf a List.mem_cons_self
    have hl : ∀ j ∈ l, 0 ≤ f j := fun j hj => hf j (List.mem_cons_of_mem a hj)
    have hih := ih hl
    simp only [List.filter_cons]
    split_ifs <;> simp only [List.map_cons, List.sum_cons] <;> linarith

lemma list_range_map_sum_eq (D : ℕ) (f : ℕ → ℝ) :
    ((List.range D).map f).sum = ∑ j ∈ Finset.range D, f j := by
  induction D with
  | zero => simp
  | succ d ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton, Finset.sum_range_succ, ih]

lemma list_filter_map_sum_le_finset_range {D : ℕ} (p : ℕ → Bool) (f : ℕ → ℝ)
    (hf : ∀ j ∈ Finset.range D, 0 ≤ f j) :
    (((List.range D).filter p).map f).sum ≤ ∑ j ∈ Finset.range D, f j := by
  rw [← list_range_map_sum_eq]
  exact list_filter_map_sum_le (List.range D) p f
    (fun j hj => hf j (Finset.mem_range.mpr (List.mem_range.mp hj)))

/-- **Equation (`\eqref{eq:bucketed-rec-bound}`, `bucketedRec_potential_bound`,
§5.4 of `paper.tex`)**:
If for each non-empty dyadic bucket $Y'_j$ ($0 \le j < D$), the recursive call `recCall` returns
a decomposition whose $(1/4, 1/4)$-potential is bounded by
$$\Lambda \cdot (2^j \mu)^{1/4} (\mathbb{E}[B'[Y'_j, Z']])^{1/4} |X'| |Y'_j| |Z'|,$$
then the combined decomposition returned by `bucketedRec` satisfies
$$C_{1/4, 1/4}(\text{bucketedRec}) \le \frac{7}{2} \Lambda \mu^{1/4} (\mathbb{E}[B'[Y', Z']])^{1/4} |X'| |Y'| |Z'|.$$ -/
theorem bucketedRec_potential_bound [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X' : Finset α) (Y' : Finset β) (Z' : Finset γ)
    (A' : α → β → ℝ) (B' : β → γ → ℝ) {μ Λ : ℝ} (D : ℕ)
    (hμ : 0 < μ) (hΛ : 0 ≤ Λ)
    (hA_nonneg : ∀ x ∈ X', ∀ y ∈ Y', 0 ≤ A' x y)
    (hB_nonneg : ∀ y ∈ Y', ∀ z ∈ Z', 0 ≤ B' y z)
    (hA_dens : matDensity X' Y' A' ≤ μ)
    (recCall : Finset α → Finset β → Finset γ →
      (α → β → ℝ) → (β → γ → ℝ) → ℝ → ℕ → List (CubePiece α β γ))
    (hrec_bound : ∀ j < D, (dyadicColBucket X' Y' A' μ j).Nonempty →
      let Y'_j := dyadicColBucket X' Y' A' μ j
      cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ)
        (recCall X' Y'_j Z'
          (submatZeroExt X' Y'_j A') (submatZeroExt Y'_j Z' B') (dyadicColAlpha μ j) j) ≤
        Λ * (dyadicColAlpha μ j) ^ ((1 : ℝ) / 4) *
          (matDensity Y'_j Z' B') ^ ((1 : ℝ) / 4) *
          (X'.card : ℝ) * (Y'_j.card : ℝ) * (Z'.card : ℝ)) :
    cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ)
      (bucketedRec X' Y' Z' A' B' μ D recCall) ≤
      (7 / 2 : ℝ) * Λ * μ ^ ((1 : ℝ) / 4) *
        (matDensity Y' Z' B') ^ ((1 : ℝ) / 4) *
        (X'.card : ℝ) * (Y'.card : ℝ) * (Z'.card : ℝ) := by
  unfold bucketedRec
  rw [cubePotential_flatMap]
  let term : ℕ → ℝ := fun j =>
    let Y'_j := dyadicColBucket X' Y' A' μ j
    Λ * (dyadicColAlpha μ j) ^ ((1 : ℝ) / 4) *
      (matDensity Y'_j Z' B') ^ ((1 : ℝ) / 4) *
      (X'.card : ℝ) * (Y'_j.card : ℝ) * (Z'.card : ℝ)
  have hterm_nonneg : ∀ j ∈ Finset.range D, 0 ≤ term j := by
    intro j _
    dsimp only [term]
    have hα_pos : 0 < dyadicColAlpha μ j := by unfold dyadicColAlpha; positivity
    have hβj_nonneg : 0 ≤ matDensity (dyadicColBucket X' Y' A' μ j) Z' B' :=
      matDensity_nonneg (fun y hy z hz => hB_nonneg y (dyadicColBucket_subset X' Y' A' μ j hy) z hz)
    have h1 : 0 ≤ Λ * (dyadicColAlpha μ j) ^ ((1 : ℝ) / 4) :=
      mul_nonneg hΛ (Real.rpow_nonneg hα_pos.le _)
    have h2 : 0 ≤ (matDensity (dyadicColBucket X' Y' A' μ j) Z' B') ^ ((1 : ℝ) / 4) :=
      Real.rpow_nonneg hβj_nonneg _
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1 h2) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hmap_le :
      ((((List.range D).filter (fun j => decide (dyadicColBucket X' Y' A' μ j).Nonempty)).map
        (fun j =>
          let Y'_j := dyadicColBucket X' Y' A' μ j
          cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ)
            (recCall X' Y'_j Z'
              (submatZeroExt X' Y'_j A') (submatZeroExt Y'_j Z' B') (dyadicColAlpha μ j) j))).sum) ≤
      ((((List.range D).filter (fun j => decide (dyadicColBucket X' Y' A' μ j).Nonempty)).map
        term).sum) := by
    refine List.sum_le_sum ?_
    intro j hj
    rw [List.mem_filter, List.mem_range, decide_eq_true_eq] at hj
    exact hrec_bound j hj.1 hj.2
  have hfilter_le :
      ((((List.range D).filter (fun j => decide (dyadicColBucket X' Y' A' μ j).Nonempty)).map
        term).sum) ≤
      ∑ j ∈ Finset.range D, term j :=
    list_filter_map_sum_le_finset_range _ term hterm_nonneg
  have hsum_factor :
      ∑ j ∈ Finset.range D, term j =
        Λ * ((X'.card : ℝ) * (Z'.card : ℝ)) *
          ∑ j ∈ Finset.range D,
            (dyadicColAlpha μ j) ^ ((1 : ℝ) / 4) *
              (matDensity (dyadicColBucket X' Y' A' μ j) Z' B') ^ ((1 : ℝ) / 4) *
              ((dyadicColBucket X' Y' A' μ j).card : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    dsimp only [term]
    ring
  have hlem41 :=
    (lem_dyadic_col_degree_bucketing X' Y' Z' A' B' hμ D hA_nonneg hB_nonneg hA_dens).2.2
  have hXZ_nonneg : 0 ≤ Λ * ((X'.card : ℝ) * (Z'.card : ℝ)) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hlem41 hXZ_nonneg
  calc
    ((((List.range D).filter (fun j => decide (dyadicColBucket X' Y' A' μ j).Nonempty)).map
      (fun j =>
        let Y'_j := dyadicColBucket X' Y' A' μ j
        cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ)
          (recCall X' Y'_j Z'
            (submatZeroExt X' Y'_j A') (submatZeroExt Y'_j Z' B') (dyadicColAlpha μ j) j))).sum)
      ≤ ∑ j ∈ Finset.range D, term j := hmap_le.trans hfilter_le
    _ = Λ * ((X'.card : ℝ) * (Z'.card : ℝ)) *
          ∑ j ∈ Finset.range D,
            (dyadicColAlpha μ j) ^ ((1 : ℝ) / 4) *
              (matDensity (dyadicColBucket X' Y' A' μ j) Z' B') ^ ((1 : ℝ) / 4) *
              ((dyadicColBucket X' Y' A' μ j).card : ℝ) := hsum_factor
    _ ≤ Λ * ((X'.card : ℝ) * (Z'.card : ℝ)) *
          ((7 / 2 : ℝ) * μ ^ ((1 : ℝ) / 4) *
            (matDensity Y' Z' B') ^ ((1 : ℝ) / 4) * (Y'.card : ℝ)) := hmul
    _ = (7 / 2 : ℝ) * Λ * μ ^ ((1 : ℝ) / 4) *
          (matDensity Y' Z' B') ^ ((1 : ℝ) / 4) *
          (X'.card : ℝ) * (Y'.card : ℝ) * (Z'.card : ℝ) := by ring

lemma list_flatMap_map_sum {ι κ : Type*} (L : List ι) (f : ι → List κ) (g : κ → ℝ) :
    ((L.flatMap f).map g).sum = (L.map (fun i => ((f i).map g).sum)).sum := by
  induction L with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons, ih]

lemma list_filter_map_sum_eq_of_false_zero {ι : Type*} (L : List ι) (p : ι → Bool) (f : ι → ℝ)
    (hzero : ∀ i ∈ L, p i = false → f i = 0) :
    (((L.filter p).map f).sum) = (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a l ih =>
    have hl : ∀ i ∈ l, p i = false → f i = 0 :=
      fun i hi hp => hzero i (List.mem_cons_of_mem a hi) hp
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    cases hp : p a
    · simp only [Bool.false_eq_true, ↓reduceIte, hzero a List.mem_cons_self hp, zero_add]
      exact ih hl
    · simp only [↓reduceIte, List.map_cons, List.sum_cons]
      rw [ih hl]

/-- Exact bilinear matrix product conservation across `bucketedRec`:
when $D \ge 1$, $\mu > 0$, $2^D \mu \ge 1$, every column $y \in Y'$ has $\deg_{(A')^T}(y) \le 1$,
and each recursive call preserves the bilinear product on $X' \times Z'$, `bucketedRec` sums to
$\text{stdMatMul } Y'\ A'\ B'\ x\ z$. -/
theorem bucketedRec_sum_eq [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X' : Finset α) (Y' : Finset β) (Z' : Finset γ)
    (A' : α → β → ℝ) (B' : β → γ → ℝ) {μ : ℝ} {D : ℕ}
    (hD : 1 ≤ D) (hμ : 0 < μ) (hμD : 1 ≤ (2 : ℝ) ^ D * μ)
    (hcol_le_one : ∀ y ∈ Y', colDeg X' A' y ≤ 1)
    (recCall : Finset α → Finset β → Finset γ →
      (α → β → ℝ) → (β → γ → ℝ) → ℝ → ℕ → List (CubePiece α β γ))
    {x : α} {z : γ} (hx : x ∈ X') (hz : z ∈ Z')
    (hrec_sum : ∀ j < D, (dyadicColBucket X' Y' A' μ j).Nonempty →
      let Y'_j := dyadicColBucket X' Y' A' μ j
      ((recCall X' Y'_j Z'
          (submatZeroExt X' Y'_j A') (submatZeroExt Y'_j Z' B') (dyadicColAlpha μ j) j).map
        (fun P => stdMatMul P.Y_k P.A_k P.B_k x z)).sum =
        stdMatMul Y'_j (submatZeroExt X' Y'_j A') (submatZeroExt Y'_j Z' B') x z) :
    ((bucketedRec X' Y' Z' A' B' μ D recCall).map
      (fun P => stdMatMul P.Y_k P.A_k P.B_k x z)).sum = stdMatMul Y' A' B' x z := by
  unfold bucketedRec
  rw [list_flatMap_map_sum]
  let active := (List.range D).filter (fun j => decide (dyadicColBucket X' Y' A' μ j).Nonempty)
  have hmap_eq :
      (active.map (fun j =>
        let Y'_j := dyadicColBucket X' Y' A' μ j
        ((recCall X' Y'_j Z'
            (submatZeroExt X' Y'_j A') (submatZeroExt Y'_j Z' B') (dyadicColAlpha μ j) j).map
          (fun P => stdMatMul P.Y_k P.A_k P.B_k x z)).sum)) =
      active.map (fun j =>
        ∑ y ∈ dyadicColBucket X' Y' A' μ j, A' x y * B' y z) := by
    refine List.map_congr_left (fun j hj => ?_)
    have hj_mem : j < D ∧ (dyadicColBucket X' Y' A' μ j).Nonempty := by
      simpa [active] using hj
    rw [hrec_sum j hj_mem.1 hj_mem.2]
    unfold stdMatMul submatZeroExt
    refine Finset.sum_congr rfl (fun y hy => ?_)
    simp [hx, hy, hz]
  rw [hmap_eq]
  have hfilter_eq :
      (active.map (fun j => ∑ y ∈ dyadicColBucket X' Y' A' μ j, A' x y * B' y z)).sum =
      ((List.range D).map (fun j => ∑ y ∈ dyadicColBucket X' Y' A' μ j, A' x y * B' y z)).sum := by
    refine list_filter_map_sum_eq_of_false_zero (List.range D) _ _ (fun j _ hj_f => ?_)
    have hnot_ne : ¬(dyadicColBucket X' Y' A' μ j).Nonempty := of_decide_eq_false hj_f
    rw [Finset.not_nonempty_iff_eq_empty.mp hnot_ne, Finset.sum_empty]
  rw [hfilter_eq, list_range_map_sum_eq]
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range D) : Set ℕ) (dyadicColBucket X' Y' A' μ) :=
    fun i _ j _ hij => dyadicColBucket_disjoint X' Y' A' hμ.le hij
  rw [← Finset.sum_biUnion hdisj, dyadicColBucket_biUnion_eq X' Y' A' hD hμ hμD hcol_le_one]
  rfl

lemma mem_bucketedRec_iff [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {X' : Finset α} {Y' : Finset β} {Z' : Finset γ}
    {A' : α → β → ℝ} {B' : β → γ → ℝ} {μ : ℝ} {D : ℕ}
    {recCall : Finset α → Finset β → Finset γ →
      (α → β → ℝ) → (β → γ → ℝ) → ℝ → ℕ → List (CubePiece α β γ)}
    {P : CubePiece α β γ} :
    P ∈ bucketedRec X' Y' Z' A' B' μ D recCall ↔
      ∃ j < D, (dyadicColBucket X' Y' A' μ j).Nonempty ∧
        let Y'_j := dyadicColBucket X' Y' A' μ j
        P ∈ recCall X' Y'_j Z'
          (submatZeroExt X' Y'_j A') (submatZeroExt Y'_j Z' B') (dyadicColAlpha μ j) j := by
  unfold bucketedRec
  simp only [List.mem_flatMap, List.mem_filter, List.mem_range, decide_eq_true_eq]
  tauto

end BucketedRec

/-!
## Part 3: Table 6 (`\label{tab:potential-budget}`) Potential Budget Analysis
(§5.4 of `paper.tex`: `two_rpow_quarter_le_two`, `concavity_drop_beta_rem`,
`four_mul_six_rpow_quarter_le_seven`, `twentyeight_mul_two_rpow_half_le_forty`,
`table1_budget_cinco_sum_le`)
-/

section Table1Budget

variable {α β γ : Type*}

lemma two_rpow_quarter_le_two : (2 : ℝ) ^ ((1 : ℝ) / 4) ≤ 2 := by
  calc
    (2 : ℝ) ^ ((1 : ℝ) / 4) ≤ ((2 : ℝ) ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
    _ = 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num

/-- **Concavity Drop on $\beta_{\text{rem}}$ (`\eqref{eq:concavity-drop}`, `concavity_drop_beta_rem`, §5.4 of `paper.tex`)**:
When $\beta > 0$, $\beta_{\text{rem}} \ge 0$, $q \ge 0$, $\beta^* \ge 0$, and
$\beta_{\text{rem}} = \beta - q \beta^*$,
1. $\beta_{\text{rem}}^{1/4} \le \beta^{1/4} - \frac{1}{4} (\beta^* / \beta)^{3/4} q (\beta^*)^{1/4}$, and
2. if additionally $\beta \le \beta^*$, then $\beta_{\text{rem}}^{1/4} \le \beta^{1/4} - \frac{1}{4} q (\beta^*)^{1/4}$. -/
theorem concavity_drop_beta_rem {β β_rem β_star q : ℝ}
    (hβ_pos : 0 < β) (hrem0 : 0 ≤ β_rem) (hq0 : 0 ≤ q) (hstar0 : 0 ≤ β_star)
    (heq : β_rem = β - q * β_star) :
    β_rem ^ ((1 : ℝ) / 4) ≤
      β ^ ((1 : ℝ) / 4) - (1 / 4 : ℝ) * (β_star / β) ^ ((3 : ℝ) / 4) * q * β_star ^ ((1 : ℝ) / 4) ∧
    (β ≤ β_star →
      β_rem ^ ((1 : ℝ) / 4) ≤ β ^ ((1 : ℝ) / 4) - (1 / 4 : ℝ) * q * β_star ^ ((1 : ℝ) / 4)) := by
  set u := q * (β_star / β)
  have hu0 : 0 ≤ u := by unfold u; positivity
  have hqstar_le : q * β_star ≤ β := by linarith
  have hu1 : u ≤ 1 := by
    unfold u
    rw [← mul_div_assoc, div_le_one hβ_pos]
    exact hqstar_le
  have hrem_eq : β_rem = β * (1 - u) := by
    unfold u
    have hβ_ne : β ≠ 0 := hβ_pos.ne'
    calc
      β_rem = β - q * β_star := heq
      _ = β * (1 - q * (β_star / β)) := by field_simp [hβ_ne]
  have hconc := one_sub_rpow_quarter_le hu0 hu1
  have hmul := mul_le_mul_of_nonneg_left hconc (Real.rpow_nonneg hβ_pos.le ((1 : ℝ) / 4))
  have hlhs : β ^ ((1 : ℝ) / 4) * (1 - u) ^ ((1 : ℝ) / 4) = β_rem ^ ((1 : ℝ) / 4) := by
    rw [← Real.mul_rpow hβ_pos.le (by linarith), ← hrem_eq]
  have hrhs :
      β ^ ((1 : ℝ) / 4) * (1 - u / 4) =
        β ^ ((1 : ℝ) / 4) -
          (1 / 4 : ℝ) * (β_star / β) ^ ((3 : ℝ) / 4) * q * β_star ^ ((1 : ℝ) / 4) := by
    unfold u
    rcases eq_or_lt_of_le hstar0 with rfl | hstar_pos
    · have h34 : (0 : ℝ) ^ ((3 : ℝ) / 4) = 0 := Real.zero_rpow (by norm_num)
      simp [h34]
    · have hsplit_star :
          β_star = β_star ^ ((3 : ℝ) / 4) * β_star ^ ((1 : ℝ) / 4) := by
        rw [← Real.rpow_add hstar_pos]
        norm_num
      have hsplit_β :
          β = β ^ ((3 : ℝ) / 4) * β ^ ((1 : ℝ) / 4) := by
        rw [← Real.rpow_add hβ_pos]
        norm_num
      have hdiv_rpow :
          (β_star / β) ^ ((3 : ℝ) / 4) =
            β_star ^ ((3 : ℝ) / 4) / β ^ ((3 : ℝ) / 4) :=
        Real.div_rpow hstar0 hβ_pos.le ((3 : ℝ) / 4)
      have hβ34_ne : β ^ ((3 : ℝ) / 4) ≠ 0 := (Real.rpow_pos_of_pos hβ_pos _).ne'
      have hβ14_ne : β ^ ((1 : ℝ) / 4) ≠ 0 := (Real.rpow_pos_of_pos hβ_pos _).ne'
      have hterm :
          β ^ ((1 : ℝ) / 4) * (q * (β_star / β) / 4) =
            (1 / 4 : ℝ) * (β_star / β) ^ ((3 : ℝ) / 4) * q * β_star ^ ((1 : ℝ) / 4) := by
        rw [hdiv_rpow]
        calc
          β ^ ((1 : ℝ) / 4) * (q * (β_star / β) / 4)
            = β ^ ((1 : ℝ) / 4) *
                (q * ((β_star ^ ((3 : ℝ) / 4) * β_star ^ ((1 : ℝ) / 4)) /
                  (β ^ ((3 : ℝ) / 4) * β ^ ((1 : ℝ) / 4))) / 4) := by
                rw [← hsplit_star, ← hsplit_β]
          _ = (1 / 4 : ℝ) * (β_star ^ ((3 : ℝ) / 4) / β ^ ((3 : ℝ) / 4)) *
                q * β_star ^ ((1 : ℝ) / 4) := by
                field_simp [hβ34_ne, hβ14_ne]
      linarith
  have hpart1 :
      β_rem ^ ((1 : ℝ) / 4) ≤
        β ^ ((1 : ℝ) / 4) -
          (1 / 4 : ℝ) * (β_star / β) ^ ((3 : ℝ) / 4) * q * β_star ^ ((1 : ℝ) / 4) := by
    rwa [hlhs, hrhs] at hmul
  refine ⟨hpart1, fun hle => ?_⟩
  have h1_le_div : 1 ≤ β_star / β := ( one_le_div hβ_pos ).mpr hle
  have h1_le_rpow : 1 ≤ (β_star / β) ^ ((3 : ℝ) / 4) :=
    Real.one_le_rpow h1_le_div (by norm_num)
  have hqstar14_nonneg : 0 ≤ (1 / 4 : ℝ) * q * β_star ^ ((1 : ℝ) / 4) :=
    mul_nonneg (mul_nonneg (by norm_num) hq0) (Real.rpow_nonneg hstar0 _)
  have hsub :
      (1 / 4 : ℝ) * q * β_star ^ ((1 : ℝ) / 4) ≤
        (1 / 4 : ℝ) * (β_star / β) ^ ((3 : ℝ) / 4) * q * β_star ^ ((1 : ℝ) / 4) := by
    have := mul_le_mul_of_nonneg_right h1_le_rpow hqstar14_nonneg
    linarith
  linarith

/-- Numerical helper $4 \cdot 6^{1/4} \le 7$ for Branch B Row 1 (`\mathcal{S}_{\text{direct}}`,
§5.4 of `paper.tex`: $4^4 \cdot 6 = 1536 \le 2401 = 7^4$). -/
lemma four_mul_six_rpow_quarter_le_seven :
    4 * (6 : ℝ) ^ ((1 : ℝ) / 4) ≤ 7 := by
  apply le_of_pow_four_le (by positivity) (by norm_num)
  rw [mul_pow, rpow_quarter_pow_four (by norm_num)]
  norm_num

/-- Numerical helper $28 \cdot 2^{1/2} \le 40$ for Branch B Row 4 (`regular` slices on
$Z^* \setminus Z_\ell$, §5.4 of `paper.tex`: $28^2 \cdot 2 = 1568 \le 1600 = 40^2$). -/
lemma twentyeight_mul_two_rpow_half_le_forty :
    28 * (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ 40 := by
  apply le_of_pow_four_le (by positivity) (by norm_num)
  have h2 : ((2 : ℝ) ^ ((1 : ℝ) / 2)) ^ (4 : ℕ) = 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [mul_pow, h2]
  norm_num

/-- **Table 6 (`\label{tab:potential-budget}`) Five-Term Budget Closure (`table1_budget_cinco_sum_le`, `paper.tex` Table 6 (`\label{tab:potential-budget}`) & §5.4)**:
In units of $W^* \ge 0$, the sum of the four recursive / direct contributions in Branch B
($\frac{14}{256} W^* + \frac{7}{256} W^* + \frac{2}{256} W^* + \frac{5}{256} W^* = \frac{28}{256} W^*$)
plus the residual call $\mathcal{S}^*$ bound ($\Lambda_h W - \frac{1}{4} W^*$) is at most $\Lambda_h W$. -/
theorem table1_budget_cinco_sum_le {Λ_h_W W_star : ℝ} (hW_star : 0 ≤ W_star) :
    (14 / 256 : ℝ) * W_star +
      (7 / 256 : ℝ) * W_star +
      (2 / 256 : ℝ) * W_star +
      (5 / 256 : ℝ) * W_star +
      (Λ_h_W - (1 / 4 : ℝ) * W_star) ≤ Λ_h_W := by
  linarith

end Table1Budget

/-!
## Part 4: Base Case 2 (`baseCase2Decomposition`), 2D Slice Transfer & Jump-Adaptive Depth Recurrence
(§5.2, §5.4 & §5.5 of `paper.tex`)
-/

section CappedABDecomposition

variable {α β γ : Type*}

lemma finset_toList_map_sum {σ : Type*} (s : Finset σ) (f : σ → ℝ) :
    (s.toList.map f).sum = ∑ x ∈ s, f x := by
  rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
  rfl

/-!
### Subsection 4.1: Algorithm 5 (`Decompose3D`) Base Case 2 (`baseCase2Decomposition`, §5.2 of `paper.tex`)
-/

open Classical in
/-- Support of $B$ on $Y \times Z$: the set of pairs $(y, z) \in Y \times Z$ with $B(y, z) = 1$
(`paper.tex` Algorithm 5 (`Decompose3D`) Line 14 `\label{line:3d-base2}`, §5.2). -/
noncomputable def suppBFinset [DecidableEq β] [DecidableEq γ]
    (Y : Finset β) (Z : Finset γ) (B : β → γ → ℝ) : Finset (β × γ) :=
  (Y ×ˢ Z).filter (fun p => B p.1 p.2 = 1)

/-- Fixed list enumeration of `suppBFinset Y Z B` (`\supp(B)` in Algorithm 5 Line 14). -/
noncomputable def suppBList [DecidableEq β] [DecidableEq γ]
    (Y : Finset β) (Z : Finset γ) (B : β → γ → ℝ) : List (β × γ) :=
  (suppBFinset Y Z B).toList

lemma suppBList_nodup [DecidableEq β] [DecidableEq γ]
    (Y : Finset β) (Z : Finset γ) (B : β → γ → ℝ) :
    (suppBList Y Z B).Nodup :=
  Finset.nodup_toList _

lemma suppBList_sub_product [DecidableEq β] [DecidableEq γ]
    (Y : Finset β) (Z : Finset γ) (B : β → γ → ℝ)
    {yz : β × γ} (h : yz ∈ suppBList Y Z B) :
    yz ∈ Y ×ˢ Z := by
  unfold suppBList suppBFinset at h
  exact (Finset.mem_filter.mp (Finset.mem_toList.mp h)).1

lemma card_product_pos_of_suppBList_ne_nil [DecidableEq β] [DecidableEq γ]
    {Y : Finset β} {Z : Finset γ} {B : β → γ → ℝ}
    (hne : suppBList Y Z B ≠ []) :
    0 < Y.card * Z.card := by
  rcases List.exists_mem_of_ne_nil (suppBList Y Z B) hne with ⟨yz, hyz⟩
  rcases Finset.mem_product.mp (suppBList_sub_product Y Z B hyz) with ⟨hy, hz⟩
  exact Nat.mul_pos (Finset.card_pos.mpr ⟨yz.1, hy⟩) (Finset.card_pos.mpr ⟨yz.2, hz⟩)

/-- Splits a list `L` into at most `K` contiguous chunks of length at most `c`
(`paper.tex` Algorithm 5 (`Decompose3D`) Line 14 `\label{line:3d-base2}`, §5.2). -/
def splitListChunks {σ : Type*} (c : ℕ) : ℕ → List σ → List (List σ)
  | 0, _ => []
  | _ + 1, [] => []
  | k + 1, L => L.take c :: splitListChunks c k (L.drop c)

lemma splitListChunks_length_le {σ : Type*} (c K : ℕ) (L : List σ) :
    (splitListChunks c K L).length ≤ K := by
  induction K generalizing L with
  | zero => simp [splitListChunks]
  | succ k ih =>
    cases L with
    | nil => simp [splitListChunks]
    | cons a l =>
      simp only [splitListChunks, List.length_cons]
      exact Nat.succ_le_succ (ih (List.drop c (a :: l)))

lemma splitListChunks_pos {σ : Type*} (c : ℕ) {K : ℕ} (hK : 1 ≤ K) {L : List σ} (hL : L ≠ []) :
    1 ≤ (splitListChunks c K L).length := by
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : K ≠ 0) with ⟨k, rfl⟩
  cases L with
  | nil => contradiction
  | cons a l =>
    simp [splitListChunks]

lemma splitListChunks_mem_length_le {σ : Type*} (c K : ℕ) (L : List σ)
    {chunk : List σ} (hmem : chunk ∈ splitListChunks c K L) :
    chunk.length ≤ c := by
  induction K generalizing L with
  | zero => simp [splitListChunks] at hmem
  | succ k ih =>
    cases L with
    | nil => simp [splitListChunks] at hmem
    | cons a l =>
      simp only [splitListChunks, List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · exact List.length_take_le c (a :: l)
      · exact ih _ htail

lemma splitListChunks_mem_sub {σ : Type*} (c K : ℕ) (L : List σ)
    {chunk : List σ} (hmem : chunk ∈ splitListChunks c K L) {x : σ} (hx : x ∈ chunk) :
    x ∈ L := by
  induction K generalizing L with
  | zero => simp [splitListChunks] at hmem
  | succ k ih =>
    cases L with
    | nil => simp [splitListChunks] at hmem
    | cons a l =>
      simp only [splitListChunks, List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · exact List.mem_of_mem_take hx
      · exact List.mem_of_mem_drop (ih (List.drop c (a :: l)) htail)

lemma splitListChunks_nodup {σ : Type*} (c K : ℕ) {L : List σ} (hL : L.Nodup)
    {chunk : List σ} (hmem : chunk ∈ splitListChunks c K L) :
    chunk.Nodup := by
  induction K generalizing L with
  | zero => simp [splitListChunks] at hmem
  | succ k ih =>
    cases L with
    | nil => simp [splitListChunks] at hmem
    | cons a l =>
      simp only [splitListChunks, List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · exact hL.sublist (List.take_sublist c (a :: l))
      · exact ih (hL.sublist (List.drop_sublist c (a :: l))) htail

lemma splitListChunks_map_sum_eq {σ : Type*} (c K : ℕ) (L : List σ) (f : σ → ℝ)
    (hlen : L.length ≤ K * c) :
    ((splitListChunks c K L).map (fun chunk => (chunk.map f).sum)).sum = (L.map f).sum := by
  induction K generalizing L with
  | zero =>
    simp only [Nat.zero_mul, Nat.le_zero_eq, List.length_eq_zero_iff] at hlen
    subst hlen
    simp [splitListChunks]
  | succ k ih =>
    cases L with
    | nil => simp [splitListChunks]
    | cons a l =>
      simp only [splitListChunks, List.map_cons, List.sum_cons]
      have hdrop_len : ((a :: l).drop c).length ≤ k * c := by
        rw [List.length_drop]
        have : (k + 1) * c = k * c + c := by ring
        omega
      rw [ih ((a :: l).drop c) hdrop_len]
      rw [← List.sum_append, ← List.map_append, List.take_append_drop]
      simp

/-- Submatrix of $B$ supported on a list `chunk : List (β × γ)` of index pairs. -/
def chunkMat [DecidableEq β] [DecidableEq γ]
    (B : β → γ → ℝ) (chunk : List (β × γ)) (y : β) (z : γ) : ℝ :=
  (chunk.map (fun yz => if y = yz.1 ∧ z = yz.2 then B y z else 0)).sum

lemma chunkMat_nonneg [DecidableEq β] [DecidableEq γ]
    {B : β → γ → ℝ} (chunk : List (β × γ)) {y : β} {z : γ} (hB : 0 ≤ B y z) :
    0 ≤ chunkMat B chunk y z := by
  unfold chunkMat
  refine List.sum_nonneg ?_
  intro v hv
  rw [List.mem_map] at hv
  rcases hv with ⟨yz, _, rfl⟩
  split_ifs <;> linarith

lemma chunkMat_eq_zero_of_not_mem [DecidableEq β] [DecidableEq γ]
    (B : β → γ → ℝ) (chunk : List (β × γ)) (y : β) (z : γ)
    (hnot : (y, z) ∉ chunk) :
    chunkMat B chunk y z = 0 := by
  induction chunk with
  | nil => rfl
  | cons a l ih =>
    simp only [List.mem_cons, not_or] at hnot
    unfold chunkMat
    simp only [List.map_cons, List.sum_cons]
    have hneq : ¬(y = a.1 ∧ z = a.2) := by
      rintro ⟨rfl, rfl⟩
      exact hnot.1 rfl
    rw [if_neg hneq, zero_add]
    exact ih hnot.2

lemma chunkMat_eq_of_mem_nodup [DecidableEq β] [DecidableEq γ]
    (B : β → γ → ℝ) {chunk : List (β × γ)} (hnd : chunk.Nodup) {y : β} {z : γ}
    (hmem : (y, z) ∈ chunk) :
    chunkMat B chunk y z = B y z := by
  induction chunk with
  | nil => cases hmem
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    rw [List.mem_cons] at hmem
    change (if y = a.1 ∧ z = a.2 then B y z else 0) + chunkMat B l y z = B y z
    rcases hmem with ha | hl
    · have hya : y = a.1 ∧ z = a.2 := ⟨congrArg Prod.fst ha, congrArg Prod.snd ha⟩
      rw [if_pos hya]
      have hnot_l : (y, z) ∉ l := by rw [ha]; exact hnd.1
      rw [chunkMat_eq_zero_of_not_mem B l y z hnot_l, add_zero]
    · have hya : ¬(y = a.1 ∧ z = a.2) := by
        rintro ⟨rfl, rfl⟩
        exact hnd.1 hl
      rw [if_neg hya, zero_add]
      exact ih hnd.2 hl

lemma chunkMat_eq_zero_or_eq [DecidableEq β] [DecidableEq γ]
    (B : β → γ → ℝ) {chunk : List (β × γ)} (hnd : chunk.Nodup) (y : β) (z : γ) :
    chunkMat B chunk y z = 0 ∨ chunkMat B chunk y z = B y z := by
  by_cases hmem : (y, z) ∈ chunk
  · exact Or.inr (chunkMat_eq_of_mem_nodup B hnd hmem)
  · exact Or.inl (chunkMat_eq_zero_of_not_mem B chunk y z hmem)

lemma chunkMat_suppBList_eq_submatZeroExt [DecidableEq β] [DecidableEq γ]
    (Y : Finset β) (Z : Finset γ) (B : β → γ → ℝ)
    (hB : IsBinaryMatrix Y Z B) (y : β) (z : γ) :
    chunkMat B (suppBList Y Z B) y z = submatZeroExt Y Z B y z := by
  classical
  by_cases hmem : (y, z) ∈ suppBFinset Y Z B
  · have hmem_list : (y, z) ∈ suppBList Y Z B := Finset.mem_toList.mpr hmem
    rw [chunkMat_eq_of_mem_nodup B (suppBList_nodup Y Z B) hmem_list]
    unfold suppBFinset at hmem
    rw [Finset.mem_filter, Finset.mem_product] at hmem
    simp [submatZeroExt, hmem.1.1, hmem.1.2]
  · have hnot_list : (y, z) ∉ suppBList Y Z B := by
      simpa [suppBList] using hmem
    rw [chunkMat_eq_zero_of_not_mem B (suppBList Y Z B) y z hnot_list]
    unfold submatZeroExt
    split_ifs with hyz
    · rcases hB y hyz.1 z hyz.2 with h0 | h1
      · exact h0.symm
      · exfalso
        apply hmem
        unfold suppBFinset
        rw [Finset.mem_filter, Finset.mem_product]
        exact ⟨hyz, h1⟩
    · rfl

lemma sum_chunkMat_eq [DecidableEq β] [DecidableEq γ]
    (Y : Finset β) (Z : Finset γ) (B : β → γ → ℝ)
    {chunk : List (β × γ)} (hsub : ∀ yz ∈ chunk, yz ∈ Y ×ˢ Z) :
    ∑ y ∈ Y, ∑ z ∈ Z, chunkMat B chunk y z = (chunk.map (fun yz => B yz.1 yz.2)).sum := by
  induction chunk with
  | nil =>
    unfold chunkMat
    simp
  | cons a l ih =>
    have ha : a ∈ Y ×ˢ Z := hsub a List.mem_cons_self
    rcases Finset.mem_product.mp ha with ⟨haY, haZ⟩
    have hl : ∀ yz ∈ l, yz ∈ Y ×ˢ Z := fun yz hyz => hsub yz (List.mem_cons_of_mem a hyz)
    have hsum_split :
        (∑ y ∈ Y, ∑ z ∈ Z, chunkMat B (a :: l) y z) =
          (∑ y ∈ Y, ∑ z ∈ Z, (if y = a.1 ∧ z = a.2 then B y z else 0)) +
            ∑ y ∈ Y, ∑ z ∈ Z, chunkMat B l y z := by
      simp_rw [chunkMat, List.map_cons, List.sum_cons, Finset.sum_add_distrib]
    rw [hsum_split, ih hl, List.map_cons, List.sum_cons]
    congr 1
    have h1 :
        (∑ y ∈ Y, ∑ z ∈ Z, if y = a.1 ∧ z = a.2 then B y z else 0) =
          ∑ y ∈ Y, if a.1 = y then B y a.2 else 0 := by
      refine Finset.sum_congr rfl (fun y _ => ?_)
      by_cases hy : y = a.1
      · simp only [hy, true_and, ↓reduceIte]
        have : (∑ z ∈ Z, if z = a.2 then B a.1 z else 0) =
            ∑ z ∈ Z, if a.2 = z then B a.1 a.2 else 0 := by
          refine Finset.sum_congr rfl (fun z _ => ?_)
          by_cases hz : z = a.2 <;> simp [hz, eq_comm]
        rw [this, Finset.sum_ite_eq Z a.2 (fun _ => B a.1 a.2), if_pos haZ]
      · have hy' : a.1 ≠ y := Ne.symm hy
        simp [hy, hy']
    rw [h1, Finset.sum_ite_eq Y a.1 (fun y => B y a.2), if_pos haY]

lemma matDensity_chunkMat_eq [DecidableEq β] [DecidableEq γ]
    (Y : Finset β) (Z : Finset γ) (B : β → γ → ℝ)
    {chunk : List (β × γ)} (hsub : ∀ yz ∈ chunk, yz ∈ Y ×ˢ Z) :
    matDensity Y Z (chunkMat B chunk) * ((Y.card : ℝ) * (Z.card : ℝ)) =
      (chunk.map (fun yz => B yz.1 yz.2)).sum := by
  rw [← sum_chunkMat_eq Y Z B hsub]
  rcases Nat.eq_zero_or_pos (Y.card * Z.card) with h0 | hpos
  · rcases Nat.mul_eq_zero.mp h0 with hY0 | hZ0
    · rw [Finset.card_eq_zero.mp hY0]; simp
    · rw [Finset.card_eq_zero.mp hZ0]; simp
  · have hY_ne : (Y.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_mul_pos_right hpos).ne'
    have hZ_ne : (Z.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_mul_pos_left hpos).ne'
    unfold matDensity rowDeg expectSet
    simp only [← Finset.sum_div]
    field_simp [hY_ne, hZ_ne]

/-- Sparse 3D subcube piece $(X, Y, Z, A[X, Y], B[Y, Z])$ with `isRegularPiece = false`. -/
def sparseCubePiece [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ) : CubePiece α β γ where
  X_k := X
  Y_k := Y
  Z_k := Z
  A_k := submatZeroExt X Y A
  B_k := submatZeroExt Y Z B
  isRegularPiece := false

/-- Chunk 3D subcube piece $(X, Y, Z, A[X, Y], B_{\text{chunk}}[Y, Z])$ for Base Case 2. -/
def chunkCubePiece [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ) (chunk : List (β × γ)) : CubePiece α β γ :=
  sparseCubePiece X Y Z A (chunkMat B chunk)

/-- **Algorithm 5 (`Decompose3D`) Line 14 (`\label{line:3d-base2}`, `baseCase2Decomposition`,
§5.2 & §5.4 Claim 5.6 `\label{clm:pot-base}` of `paper.tex`)**:
At maximum recursion depth $h = H$, partitions $\operatorname{supp}(B)$ (`suppBList Y Z B`) into
$N_{\text{split}} = \lceil \operatorname{nnz}(B) / \max(1, \lfloor 2^{-D}|Y||Z| \rfloor) \rceil \le 2 \cdot 2^D$
edge-disjoint matrices $B_1, \dots, B_{N_{\text{split}}}$ supported on $(Y, Z)$, each of support
size $\le \max(1, \lfloor 2^{-D}|Y||Z| \rfloor)$ (so $\mathbb{E}[B_s] \le 2^{-D}$ when $|Y||Z| \ge 2^D$
and $\operatorname{nnz}(B_s) \le 1$ when $|Y||Z| < 2^D$), and returns the pieces
$(X, Y, Z, A[X, Y], B_s)$ (`chunkCubePiece X Y Z A B chunk`). When $\operatorname{supp}(B) = \emptyset$
(degenerate standalone totalization; at Algorithm 5 Line 14, Base Case 1 has already excluded
$\mathbb{E}[B] \le 2^{-D}$), returns `[sparseCubePiece X Y Z A B]`. -/
noncomputable def baseCase2Decomposition [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ) (D : ℕ) : List (CubePiece α β γ) :=
  let L := suppBList Y Z B
  if L = [] then
    [sparseCubePiece X Y Z A B]
  else
    let c := max 1 ((Y.card * Z.card) / 2 ^ D)
    (splitListChunks c (2 * 2 ^ D) L).map (chunkCubePiece X Y Z A B)

/-- Cost-tracked Base Case 2 (`baseCase2DecompositionTracked`), partitioning `suppBList Y Z B`
into chunks of size $\max(1, \lfloor 2^{-D}|Y||Z| \rfloor)$ and constructing each piece via
`mapListTracked` and `scanMatrixPairTracked` (`paper.tex`, §5.2 Line 14). -/
noncomputable def baseCase2DecompositionTracked [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ) (D : ℕ) : CostM (List (CubePiece α β γ)) :=
  let L := suppBList Y Z B
  if L = [] then
    scanMatrixPairTracked X Y Z [sparseCubePiece X Y Z A B]
  else
    let c := max 1 ((Y.card * Z.card) / 2 ^ D)
    mapListTracked
      (fun chunk => scanMatrixPairTracked X Y Z (chunkCubePiece X Y Z A B chunk))
      (splitListChunks c (2 * 2 ^ D) L)

@[simp]
lemma baseCase2DecompositionTracked_fst [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ) (D : ℕ) :
    (baseCase2DecompositionTracked X Y Z A B D).1 =
      baseCase2Decomposition X Y Z A B D := by
  unfold baseCase2DecompositionTracked baseCase2Decomposition
  dsimp only
  split_ifs <;> simp

lemma baseCase2DecompositionTracked_snd_le [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ) (D : ℕ) :
    (baseCase2DecompositionTracked X Y Z A B D).2 ≤
      (baseCase2Decomposition X Y Z A B D).length *
        (X.card * Y.card + Y.card * Z.card + 2) + 1 := by
  unfold baseCase2DecompositionTracked baseCase2Decomposition
  dsimp only
  split_ifs with h0
  · simp only [scanMatrixPairTracked_snd, List.length_singleton, one_mul]
    omega
  · rw [mapListTracked_snd_const _ (X.card * Y.card + Y.card * Z.card + 1) _
      (fun _ _ => scanMatrixPairTracked_snd X Y Z _), List.length_map]

lemma prod_le_two_mul_pow_mul_div {N M : ℕ} (hM : 0 < M) (h : M ≤ N) :
    N ≤ (2 * M) * (N / M) := by
  have hdiv := Nat.div_add_mod N M
  have hmod : N % M < M := Nat.mod_lt N hM
  have hq_pos : 1 ≤ N / M := Nat.div_pos h hM
  nlinarith

lemma suppBList_length_le_two_mul_pow_mul_chunk [DecidableEq β] [DecidableEq γ]
    (Y : Finset β) (Z : Finset γ) (B : β → γ → ℝ) (D : ℕ) :
    (suppBList Y Z B).length ≤ (2 * 2 ^ D) * max 1 ((Y.card * Z.card) / 2 ^ D) := by
  have hsub : (suppBList Y Z B).length ≤ Y.card * Z.card := by
    unfold suppBList suppBFinset
    rw [Finset.length_toList, ← Finset.card_product]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have h2D_pos : 0 < 2 ^ D := by positivity
  by_cases hlt : Y.card * Z.card < 2 ^ D
  · have hdiv : (Y.card * Z.card) / 2 ^ D = 0 := Nat.div_eq_of_lt hlt
    rw [hdiv]
    simp only [Nat.max_zero, mul_one]
    omega
  · push_neg at hlt
    have hdiv_pos : 1 ≤ (Y.card * Z.card) / 2 ^ D := Nat.div_pos hlt h2D_pos
    rw [Nat.max_eq_right hdiv_pos]
    exact hsub.trans (prod_le_two_mul_pow_mul_div h2D_pos hlt)

lemma baseCase2Decomposition_length_bounds [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ) (D : ℕ) :
    1 ≤ (baseCase2Decomposition X Y Z A B D).length ∧
    (baseCase2Decomposition X Y Z A B D).length ≤ 3 * 2 ^ D := by
  unfold baseCase2Decomposition
  dsimp only
  have h2D_pos : 1 ≤ 2 ^ D := Nat.one_le_pow D 2 (by norm_num)
  split_ifs with h0
  · simp; omega
  · rw [List.length_map]
    refine ⟨splitListChunks_pos _ (by omega) h0, ?_⟩
    have hle := splitListChunks_length_le (max 1 ((Y.card * Z.card) / 2 ^ D)) (2 * 2 ^ D)
      (suppBList Y Z B)
    omega

theorem baseCase2Decomposition_sum_eq [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ) (D : ℕ)
    (hB : IsBinaryMatrix Y Z B)
    {x : α} {z : γ} (hx : x ∈ X) (hz : z ∈ Z) :
    ((baseCase2Decomposition X Y Z A B D).map
      (fun P => stdMatMul P.Y_k P.A_k P.B_k x z)).sum = stdMatMul Y A B x z := by
  unfold baseCase2Decomposition
  dsimp only
  split_ifs with h0
  · simp only [List.map_singleton, List.sum_singleton, sparseCubePiece]
    unfold stdMatMul submatZeroExt
    refine Finset.sum_congr rfl (fun y hy => ?_)
    simp [hx, hy, hz]
  · set c := max 1 ((Y.card * Z.card) / 2 ^ D)
    set L := suppBList Y Z B
    set chunks := splitListChunks c (2 * 2 ^ D) L
    rw [List.map_map]
    have hterm :
        ((fun P : CubePiece α β γ => stdMatMul P.Y_k P.A_k P.B_k x z) ∘
          chunkCubePiece X Y Z A B) =
        (fun chunk => (chunk.map (fun yz =>
          ∑ y ∈ Y, A x y * (if y = yz.1 ∧ z = yz.2 then B y z else 0))).sum) := by
      ext chunk
      dsimp only [Function.comp_apply, chunkCubePiece, sparseCubePiece]
      unfold stdMatMul submatZeroExt
      have h1 :
          (∑ y ∈ Y, (if x ∈ X ∧ y ∈ Y then A x y else 0) *
            (if y ∈ Y ∧ z ∈ Z then chunkMat B chunk y z else 0)) =
          ∑ y ∈ Y, A x y * chunkMat B chunk y z := by
        refine Finset.sum_congr rfl (fun y hy => ?_)
        simp [hx, hy, hz]
      rw [h1]
      clear h1
      unfold chunkMat
      induction chunk with
      | nil => simp
      | cons a l ih =>
        simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib]
        rw [ih]
    rw [hterm]
    have hlen : L.length ≤ (2 * 2 ^ D) * c :=
      suppBList_length_le_two_mul_pow_mul_chunk Y Z B D
    rw [splitListChunks_map_sum_eq c (2 * 2 ^ D) L _ hlen]
    have hfull := chunkMat_suppBList_eq_submatZeroExt Y Z B hB
    have hsum_y :
        ((L.map (fun yz =>
          ∑ y ∈ Y, A x y * (if y = yz.1 ∧ z = yz.2 then B y z else 0))).sum) =
        ∑ y ∈ Y, A x y * chunkMat B L y z := by
      unfold L suppBList
      rw [finset_toList_map_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [← Finset.mul_sum, ← finset_toList_map_sum]
      rfl
    rw [hsum_y]
    unfold stdMatMul
    refine Finset.sum_congr rfl (fun y hy => ?_)
    rw [hfull y z]
    simp [submatZeroExt, hy, hz]

open Classical in
theorem baseCase2Decomposition_pieces_spec [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ) (D : ℕ)
    (hB : IsBinaryMatrix Y Z B)
    {P : CubePiece α β γ} (hP : P ∈ baseCase2Decomposition X Y Z A B D) :
    P.X_k ⊆ X ∧ P.Y_k ⊆ Y ∧ P.Z_k ⊆ Z ∧
    P.A_k = submatZeroExt P.X_k P.Y_k A ∧
    (∀ x y, P.A_k x y = submatZeroExt P.X_k P.Y_k P.A_k x y) ∧
    (∀ y z, P.B_k y z = submatZeroExt P.Y_k P.Z_k P.B_k y z) ∧
    (∀ y ∈ P.Y_k, ∀ z ∈ P.Z_k, P.B_k y z = 0 ∨ P.B_k y z = B y z) ∧
    P.isRegularPiece = false ∧
    (min (matDensity P.X_k P.Y_k P.A_k) (matDensity P.Y_k P.Z_k P.B_k) ≤ (2 : ℝ) ^ (- (D : ℝ)) ∨
      ((P.Y_k ×ˢ P.Z_k).filter (fun p => P.B_k p.1 p.2 = 1)).card ≤ 1) := by
  unfold baseCase2Decomposition at hP
  dsimp only at hP
  split_ifs at hP with h0
  · simp only [List.mem_singleton] at hP
    subst hP
    dsimp only [sparseCubePiece]
    refine ⟨Finset.Subset.rfl, Finset.Subset.rfl, Finset.Subset.rfl, rfl, ?_, ?_, ?_, rfl, ?_⟩
    · intro x y; by_cases hxy : x ∈ X ∧ y ∈ Y <;> simp [submatZeroExt, hxy]
    · intro y z; by_cases hyz : y ∈ Y ∧ z ∈ Z <;> simp [submatZeroExt, hyz]
    · intro y hy z hz; right; simp [submatZeroExt, hy, hz]
    · right
      have hemp : (Y ×ˢ Z).filter (fun p => submatZeroExt Y Z B p.1 p.2 = 1) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro p hp hval
        rcases Finset.mem_product.mp hp with ⟨hpY, hpZ⟩
        simp only [submatZeroExt, hpY, hpZ, and_self, ↓reduceIte] at hval
        have hmem_supp : p ∈ suppBList Y Z B := by
          unfold suppBList suppBFinset
          rw [Finset.mem_toList, Finset.mem_filter]
          exact ⟨hp, hval⟩
        rw [h0] at hmem_supp
        cases hmem_supp
      rw [hemp, Finset.card_empty]
      omega
  · rw [List.mem_map] at hP
    rcases hP with ⟨chunk, hchunk_mem, rfl⟩
    dsimp only [chunkCubePiece, sparseCubePiece]
    have hnd : chunk.Nodup :=
      splitListChunks_nodup _ _ (suppBList_nodup Y Z B) hchunk_mem
    have hsub_prod : ∀ yz ∈ chunk, yz ∈ Y ×ˢ Z := by
      intro yz hyz
      exact suppBList_sub_product Y Z B (splitListChunks_mem_sub _ _ _ hchunk_mem hyz)
    refine ⟨Finset.Subset.rfl, Finset.Subset.rfl, Finset.Subset.rfl, rfl, ?_, ?_, ?_, rfl, ?_⟩
    · intro x y; by_cases hxy : x ∈ X ∧ y ∈ Y <;> simp [submatZeroExt, hxy]
    · intro y z; by_cases hyz : y ∈ Y ∧ z ∈ Z <;> simp [submatZeroExt, hyz]
    · intro y hy z hz
      simp only [submatZeroExt, hy, hz, and_self, ↓reduceIte]
      exact chunkMat_eq_zero_or_eq B hnd y z
    · have hlen_le : chunk.length ≤ max 1 ((Y.card * Z.card) / 2 ^ D) :=
        splitListChunks_mem_length_le _ _ _ hchunk_mem
      by_cases hlt : Y.card * Z.card < 2 ^ D
      · right
        have hdiv : (Y.card * Z.card) / 2 ^ D = 0 := Nat.div_eq_of_lt hlt
        rw [hdiv, Nat.max_zero] at hlen_le
        have hsub_chunk :
            (Y ×ˢ Z).filter (fun p => submatZeroExt Y Z (chunkMat B chunk) p.1 p.2 = 1) ⊆
              chunk.toFinset := by
          intro p hp
          rw [Finset.mem_filter] at hp
          rcases Finset.mem_product.mp hp.1 with ⟨hpY, hpZ⟩
          simp only [submatZeroExt, hpY, hpZ, and_self, ↓reduceIte] at hp
          rw [List.mem_toFinset]
          by_contra hnot
          have hzero := chunkMat_eq_zero_of_not_mem B chunk p.1 p.2 hnot
          linarith [hp.2]
        exact (Finset.card_le_card hsub_chunk).trans (List.toFinset_card_le chunk |>.trans hlen_le)
      · left
        push_neg at hlt
        have h2D_pos : 0 < 2 ^ D := by positivity
        have hdiv_pos : 1 ≤ (Y.card * Z.card) / 2 ^ D := Nat.div_pos hlt h2D_pos
        rw [Nat.max_eq_right hdiv_pos] at hlen_le
        have hB_le_one : ∀ y ∈ Y, ∀ z ∈ Z, B y z ≤ 1 := isBinaryMatrix_le_one hB
        refine (min_le_right _ _).trans ?_
        rw [matDensity_submatZeroExt_eq Y Z (chunkMat B chunk)]
        have hsum_le_len : (chunk.map (fun yz => B yz.1 yz.2)).sum ≤ (chunk.length : ℝ) := by
          have h1 : (chunk.map (fun yz => B yz.1 yz.2)).sum ≤ (chunk.map (fun _ => (1 : ℝ))).sum := by
            refine List.sum_le_sum (fun yz hyz => ?_)
            rcases Finset.mem_product.mp (hsub_prod yz hyz) with ⟨hy, hz⟩
            exact hB_le_one yz.1 hy yz.2 hz
          simpa using h1
        have hdiv_real : (((Y.card * Z.card) / 2 ^ D : ℕ) : ℝ) ≤
            ((Y.card : ℝ) * (Z.card : ℝ)) / (2 : ℝ) ^ D := by
          have hmul_le : ((Y.card * Z.card) / 2 ^ D) * 2 ^ D ≤ Y.card * Z.card :=
            Nat.div_mul_le_self _ _
          have hmul_real : (((Y.card * Z.card) / 2 ^ D : ℕ) : ℝ) * (2 : ℝ) ^ D ≤
              (Y.card : ℝ) * (Z.card : ℝ) := by
            exact_mod_cast hmul_le
          rw [le_div_iff₀ (by positivity)]
          exact hmul_real
        have hdens_mul := matDensity_chunkMat_eq Y Z B hsub_prod
        have hYZ_pos : (0 : ℝ) < (Y.card : ℝ) * (Z.card : ℝ) := by
          exact_mod_cast card_product_pos_of_suppBList_ne_nil h0
        have hpow_neg : (2 : ℝ) ^ (- (D : ℝ)) = ((2 : ℝ) ^ D)⁻¹ := by
          rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
        rw [hpow_neg]
        have hbound_prod :
            matDensity Y Z (chunkMat B chunk) * ((Y.card : ℝ) * (Z.card : ℝ)) ≤
              ((2 : ℝ) ^ D)⁻¹ * ((Y.card : ℝ) * (Z.card : ℝ)) := by
          calc
            matDensity Y Z (chunkMat B chunk) * ((Y.card : ℝ) * (Z.card : ℝ))
              = (chunk.map (fun yz => B yz.1 yz.2)).sum := hdens_mul
            _ ≤ (chunk.length : ℝ) := hsum_le_len
            _ ≤ (((Y.card * Z.card) / 2 ^ D : ℕ) : ℝ) := by exact_mod_cast hlen_le
            _ ≤ ((Y.card : ℝ) * (Z.card : ℝ)) / (2 : ℝ) ^ D := hdiv_real
            _ = ((2 : ℝ) ^ D)⁻¹ * ((Y.card : ℝ) * (Z.card : ℝ)) := by ring
        exact le_of_mul_le_mul_right hbound_prod hYZ_pos

lemma list_sum_rpow_quarter_le {σ : Type*} (L : List σ) (g : σ → ℝ)
    (hg : ∀ x ∈ L, 0 ≤ g x) :
    (L.map (fun x => (g x) ^ ((1 : ℝ) / 4))).sum ≤
      (L.length : ℝ) ^ ((3 : ℝ) / 4) * ((L.map g).sum) ^ ((1 : ℝ) / 4) := by
  have hlhs0 : 0 ≤ (L.map (fun x => (g x) ^ ((1 : ℝ) / 4))).sum := by
    refine List.sum_nonneg ?_
    intro v hv
    rw [List.mem_map] at hv
    rcases hv with ⟨x, hx, rfl⟩
    exact Real.rpow_nonneg (hg x hx) _
  have hsum0 : 0 ≤ (L.map g).sum := by
    refine List.sum_nonneg ?_
    intro v hv
    rw [List.mem_map] at hv
    rcases hv with ⟨x, hx, rfl⟩
    exact hg x hx
  have hrhs0 : 0 ≤ (L.length : ℝ) ^ ((3 : ℝ) / 4) * ((L.map g).sum) ^ ((1 : ℝ) / 4) := by
    positivity
  apply le_of_pow_four_le hlhs0 hrhs0
  rw [list_map_sum_eq_sum_fin]
  have hcs := sum_pow_four_le (Finset.univ : Finset (Fin L.length))
    (fun i => (g (L.get i)) ^ ((1 : ℝ) / 4))
  simp only [Finset.card_univ, Fintype.card_fin] at hcs
  have hsum4 :
      (∑ i : Fin L.length, ((g (L.get i)) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ)) = (L.map g).sum := by
    rw [list_map_sum_eq_sum_fin]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact rpow_quarter_pow_four (hg (L.get i) (List.get_mem L i))
  rw [hsum4] at hcs
  have hrhs4 :
      ((L.length : ℝ) ^ ((3 : ℝ) / 4) * ((L.map g).sum) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) =
        (L.length : ℝ) ^ (3 : ℕ) * (L.map g).sum := by
    rw [mul_pow, rpow_quarter_pow_four hsum0, ← Real.rpow_natCast,
      ← Real.rpow_mul (Nat.cast_nonneg L.length)]
    have hexp : ((3 : ℝ) / 4) * ((4 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
    rw [hexp, Real.rpow_natCast]
  linarith

/-- **Base Case 2 Potential Bound (`baseCase2Decomposition_potential_le`,
§5.4 Claim 5.6 `\label{clm:pot-base}` of `paper.tex`)**:
When $3 D \le 4 h$ (in particular $h \ge H = \lceil 3d/2 \rceil$ with $D = 2d$, or $h \ge \text{H3D } D$)
and $\mathbb{E}_{X \times Y}[A] \le 2\alpha_{\text{cap}}$,
$$C_{1/4, 1/4}(\text{baseCase2Decomposition } X Y Z A B D)
  \le \Lambda_h \alpha_{\text{cap}}^{1/4} (\mathbb{E}_{Y \times Z}[B])^{1/4} |X| |Y| |Z|.$$ -/
theorem baseCase2Decomposition_potential_le [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ) {D h : ℕ} {α_cap : ℝ}
    (hA_nonneg : ∀ x ∈ X, ∀ y ∈ Y, 0 ≤ A x y)
    (hB : IsBinaryMatrix Y Z B)
    (hα0 : 0 ≤ α_cap) (hA_le : matDensity X Y A ≤ 2 * α_cap)
    (hDh : 3 * D ≤ 4 * h) :
    cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ) (baseCase2Decomposition X Y Z A B D) ≤
      Lambda3D (h : ℝ) * α_cap ^ ((1 : ℝ) / 4) *
        (matDensity Y Z B) ^ ((1 : ℝ) / 4) *
        (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ) := by
  have hB_nonneg : ∀ y ∈ Y, ∀ z ∈ Z, 0 ≤ B y z := isBinaryMatrix_nonneg hB
  have hA0 : 0 ≤ matDensity X Y A := matDensity_nonneg hA_nonneg
  have hB0 : 0 ≤ matDensity Y Z B := matDensity_nonneg hB_nonneg
  have hα_rpow : (matDensity X Y A) ^ ((1 : ℝ) / 4) ≤ 2 * α_cap ^ ((1 : ℝ) / 4) := by
    calc
      (matDensity X Y A) ^ ((1 : ℝ) / 4) ≤ (2 * α_cap) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow hA0 hA_le (by norm_num)
      _ = (2 : ℝ) ^ ((1 : ℝ) / 4) * α_cap ^ ((1 : ℝ) / 4) :=
        Real.mul_rpow (by norm_num) hα0
      _ ≤ 2 * α_cap ^ ((1 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right two_rpow_quarter_le_two (Real.rpow_nonneg hα0 _)
  have hΛ_ge : 128 ≤ Lambda3D (h : ℝ) := Lambda3D_ge_128 (Nat.cast_nonneg h)
  unfold baseCase2Decomposition
  dsimp only
  split_ifs with h0
  · unfold cubePotential sparseCubePiece
    simp only [List.map_singleton, List.sum_singleton,
      matDensity_submatZeroExt_eq X Y A, matDensity_submatZeroExt_eq Y Z B]
    have h2_le_Λ : (matDensity X Y A) ^ ((1 : ℝ) / 4) ≤ Lambda3D (h : ℝ) * α_cap ^ ((1 : ℝ) / 4) := by
      have : 0 ≤ α_cap ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hα0 _
      nlinarith
    have hrest : 0 ≤ (matDensity Y Z B) ^ ((1 : ℝ) / 4) * (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ) := by
      have : 0 ≤ (matDensity Y Z B) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hB0 _
      positivity
    have hmul := mul_le_mul_of_nonneg_right h2_le_Λ hrest
    linarith
  · set c := max 1 ((Y.card * Z.card) / 2 ^ D)
    set L := suppBList Y Z B
    set chunks := splitListChunks c (2 * 2 ^ D) L
    unfold cubePotential
    rw [List.map_map]
    have hfactor :
        (chunks.map ((fun P : CubePiece α β γ =>
          (matDensity P.X_k P.Y_k P.A_k) ^ ((1 : ℝ) / 4) *
            (matDensity P.Y_k P.Z_k P.B_k) ^ ((1 : ℝ) / 4) *
            (P.X_k.card : ℝ) * (P.Y_k.card : ℝ) * (P.Z_k.card : ℝ)) ∘
          chunkCubePiece X Y Z A B)).sum =
        (matDensity X Y A) ^ ((1 : ℝ) / 4) *
          ((X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ)) *
          (chunks.map (fun chunk => (matDensity Y Z (chunkMat B chunk)) ^ ((1 : ℝ) / 4))).sum := by
      induction chunks with
      | nil => simp
      | cons ch chs ih =>
        simp only [List.map_cons, List.sum_cons, Function.comp_apply, chunkCubePiece,
          sparseCubePiece, matDensity_submatZeroExt_eq, ih]
        ring
    rw [hfactor]
    have hdens_nonneg : ∀ chunk ∈ chunks, 0 ≤ matDensity Y Z (chunkMat B chunk) := by
      intro chunk _
      exact matDensity_nonneg (fun y hy z hz => chunkMat_nonneg chunk (hB_nonneg y hy z hz))
    have hholder := list_sum_rpow_quarter_le chunks (fun chunk => matDensity Y Z (chunkMat B chunk))
      hdens_nonneg
    have hYZ_pos : (0 : ℝ) < (Y.card : ℝ) * (Z.card : ℝ) := by
      exact_mod_cast card_product_pos_of_suppBList_ne_nil h0
    have hsum_dens :
        (chunks.map (fun chunk => matDensity Y Z (chunkMat B chunk))).sum = matDensity Y Z B := by
      apply mul_right_cancel₀ hYZ_pos.ne'
      have h1 :
          (chunks.map (fun chunk => matDensity Y Z (chunkMat B chunk))).sum *
            ((Y.card : ℝ) * (Z.card : ℝ)) =
          (chunks.map (fun chunk => (chunk.map (fun yz => B yz.1 yz.2)).sum)).sum := by
        have hmap_congr :
            chunks.map (fun chunk => matDensity Y Z (chunkMat B chunk) * ((Y.card : ℝ) * (Z.card : ℝ))) =
            chunks.map (fun chunk => (chunk.map (fun yz => B yz.1 yz.2)).sum) := by
          refine List.map_congr_left (fun chunk hch => ?_)
          exact matDensity_chunkMat_eq Y Z B (fun yz hyz =>
            suppBList_sub_product Y Z B (splitListChunks_mem_sub _ _ _ hch hyz))
        rw [← hmap_congr]
        generalize chunks = Lc
        induction Lc with
        | nil => simp
        | cons a l ih => simp [List.map_cons, List.sum_cons, add_mul, ih]
      have hlen : L.length ≤ (2 * 2 ^ D) * c :=
        suppBList_length_le_two_mul_pow_mul_chunk Y Z B D
      have hL_sub : ∀ yz ∈ L, yz ∈ Y ×ˢ Z := fun _ h => suppBList_sub_product Y Z B h
      rw [h1, splitListChunks_map_sum_eq c (2 * 2 ^ D) L _ hlen,
        ← sum_chunkMat_eq Y Z B hL_sub]
      have h2 := matDensity_chunkMat_eq Y Z B hL_sub
      have h3 : matDensity Y Z (chunkMat B L) = matDensity Y Z B := by
        have hext := matDensity_submatZeroExt_eq Y Z B
        have hcongr : chunkMat B L = submatZeroExt Y Z B := by
          ext y z; exact chunkMat_suppBList_eq_submatZeroExt Y Z B hB y z
        rw [hcongr, hext]
      rw [← h3, h2]
      exact sum_chunkMat_eq Y Z B hL_sub
    rw [hsum_dens] at hholder
    have hlen_le : (chunks.length : ℝ) ≤ 2 * (2 : ℝ) ^ D := by
      have := splitListChunks_length_le c (2 * 2 ^ D) L
      exact_mod_cast this
    have htwo_tq : (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ 2 := by
      have : (3 : ℝ) / 4 ≤ 1 := by norm_num
      exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) this).trans (by norm_num)
    have hpow_h : ((2 : ℝ) ^ D) ^ ((3 : ℝ) / 4) ≤ (2 : ℝ) ^ (h : ℝ) := by
      rw [← Real.rpow_natCast 2 D, ← Real.rpow_mul (by norm_num)]
      have hexp : (D : ℝ) * ((3 : ℝ) / 4) ≤ (h : ℝ) := by
        have : (3 * (D : ℝ)) ≤ 4 * (h : ℝ) := by exact_mod_cast hDh
        linarith
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    have hN_rpow : (chunks.length : ℝ) ^ ((3 : ℝ) / 4) ≤ 2 * (2 : ℝ) ^ (h : ℝ) := by
      calc
        (chunks.length : ℝ) ^ ((3 : ℝ) / 4) ≤ (2 * (2 : ℝ) ^ D) ^ ((3 : ℝ) / 4) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hlen_le (by norm_num)
        _ = (2 : ℝ) ^ ((3 : ℝ) / 4) * ((2 : ℝ) ^ D) ^ ((3 : ℝ) / 4) :=
          Real.mul_rpow (by norm_num) (by positivity)
        _ ≤ 2 * (2 : ℝ) ^ (h : ℝ) :=
          mul_le_mul htwo_tq hpow_h (by positivity) (by norm_num)
    have hsum_le :
        (chunks.map (fun chunk => (matDensity Y Z (chunkMat B chunk)) ^ ((1 : ℝ) / 4))).sum ≤
          2 * (2 : ℝ) ^ (h : ℝ) * (matDensity Y Z B) ^ ((1 : ℝ) / 4) :=
      hholder.trans (mul_le_mul_of_nonneg_right hN_rpow (Real.rpow_nonneg hB0 _))
    have hA_N :
        (matDensity X Y A) ^ ((1 : ℝ) / 4) *
          (chunks.map (fun chunk => (matDensity Y Z (chunkMat B chunk)) ^ ((1 : ℝ) / 4))).sum ≤
        Lambda3D (h : ℝ) * α_cap ^ ((1 : ℝ) / 4) * (matDensity Y Z B) ^ ((1 : ℝ) / 4) := by
      have hprod := mul_le_mul hα_rpow hsum_le
        (by
          refine List.sum_nonneg ?_
          intro v hv; rw [List.mem_map] at hv; rcases hv with ⟨ch, hch, rfl⟩
          exact Real.rpow_nonneg (hdens_nonneg ch hch) _)
        (by positivity)
      unfold Lambda3D
      have : 0 ≤ (2 : ℝ) ^ (h : ℝ) * α_cap ^ ((1 : ℝ) / 4) * (matDensity Y Z B) ^ ((1 : ℝ) / 4) := by
        have : 0 ≤ α_cap ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hα0 _
        have : 0 ≤ (matDensity Y Z B) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hB0 _
        positivity
      nlinarith
    have hcards0 : 0 ≤ (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hA_N hcards0
    linarith

/-!
### Subsection 4.2: 2D Slice Transfer, Riemann-Sum & Scale-Sum Bounds for `cappedGoodCube`
(`paper.tex` Theorem 4.4 `\label{thm:2d-decomp}`, Lemma 4.6 `\eqref{eq:riemann-telescoping}`, & Lemma 5.3 `\label{lem:cube-step}`, §4.3 & §5.2–§5.4)
-/

/-- **Riemann-Integral Density-Weighted Telescoping on `cappedADecomp3DLoop` at $p = 1/4$
(`cappedADecomp3DLoop_rpow_quarter_sum_aux`, `paper.tex` Eq. `\eqref{eq:riemann-telescoping}`, §4.3)**:
Across the residual trajectory of `cappedADecomp3DLoop`, each extracted piece satisfies
`riemann_density_weighted_step` at $p = 1/4$, so
$$\sum_{P \in L} (\mathbb{E}[P.A_{\text{sub}}])^{1/4} |P.X_{\text{sub}}| |P.Y_{\text{sub}}|
  + 3 \sum_{P \in L : P.\text{tag} = \text{residual}} (\mathbb{E}[P.A_{\text{sub}}])^{1/4} |P.X_{\text{sub}}| |P.Y_{\text{sub}}|
  \le 4 (\mathbb{E}[A_{\text{rem}}])^{1/4} |X| |Y|.$$ -/
theorem cappedADecomp3DLoop_rpow_quarter_sum_aux [DecidableEq α] [DecidableEq β]
    (fuel : ℕ) {X : Finset α} {Y : Finset β} {A_rem : α → β → ℝ}
    {ε : ℝ} {D : ℕ} {α_low α_cap : ℝ}
    (S : TwoStageSamplerOracle β ε)
    (hX : X.Nonempty) (hY : Y.Nonempty) (hA : IsBinaryMatrix X Y A_rem)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hD : 2 ≤ D)
    (hwindow : α_cap ≤ (2 : ℝ) ^ (48 : ℕ) * α_low) :
    let L := cappedADecomp3DLoop fuel X Y A_rem ε D α_low α_cap S
    (L.map (fun P => (matDensity P.X_sub P.Y_sub P.A_sub) ^ ((1 : ℝ) / 4) *
      (P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ))).sum +
    3 * (L.map (fun P => if P.tag = RectTag.residual then
      (matDensity P.X_sub P.Y_sub P.A_sub) ^ ((1 : ℝ) / 4) *
        (P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ)
      else 0)).sum ≤
      4 * (matDensity X Y A_rem) ^ ((1 : ℝ) / 4) * (X.card : ℝ) * (Y.card : ℝ) := by
  classical
  have hX_pos : (0 : ℝ) < (X.card : ℝ) := Nat.cast_pos.mpr hX.card_pos
  have hY_pos : (0 : ℝ) < (Y.card : ℝ) := Nat.cast_pos.mpr hY.card_pos
  have hXY_pos : (0 : ℝ) < (X.card : ℝ) * (Y.card : ℝ) := mul_pos hX_pos hY_pos
  have hXY_ne : (X.card : ℝ) * (Y.card : ℝ) ≠ 0 := hXY_pos.ne'
  induction fuel generalizing A_rem with
  | zero =>
    dsimp only [cappedADecomp3DLoop]
    simp only [List.map_singleton, List.sum_singleton, ↓reduceIte, matDensity_submatZeroExt_eq]
    linarith
  | succ k ih =>
    dsimp only [cappedADecomp3DLoop]
    split_ifs with hle
    · simp only [List.map_singleton, List.sum_singleton, ↓reduceIte, matDensity_submatZeroExt_eq]
      linarith
    · push_neg at hle
      have hA_gt : (2 : ℝ) ^ (-(D : ℤ)) < matDensity X Y A_rem :=
        lt_of_le_of_lt (le_max_left _ _) hle
      have hα_low_lt : α_low < matDensity X Y A_rem :=
        lt_of_le_of_lt (le_max_right _ _) hle
      have hcap_win : α_cap ≤ (2 : ℝ) ^ (48 : ℕ) * matDensity X Y A_rem :=
        hwindow.trans (mul_le_mul_of_nonneg_left hα_low_lt.le (by positivity))
      rcases cappedGoodRect3D_spec S hX hY hA hε0 hε_le hD hA_gt hcap_win with
        ⟨hsubX, hsubY, _hneX, _hneY, hA_eq, _hsteps, _hS_D, hdens_scale,
          _hY_shrink, _hM_bound, htag_or, _hboost_spec, _hreg_spec⟩
      set res := cappedGoodRect3D X Y A_rem ε D α_cap S
      set A_next := zeroOutSubrect A_rem res.X_ell res.Y_ell
      have hA_next_bin : IsBinaryMatrix X Y A_next := isBinaryMatrix_zeroOutSubrect _ _ hA
      have hih := ih hA_next_bin
      have htag_ne : res.tag ≠ RectTag.residual := by
        rcases htag_or with h | h <;> rw [h] <;> decide
      have hμ_prev_pos : 0 < matDensity X Y A_rem := lt_trans (by positivity) hA_gt
      have hμ_curr_nonneg : 0 ≤ matDensity X Y A_next :=
        matDensity_nonneg (isBinaryMatrix_nonneg hA_next_bin)
      have h1_le_2s : (1 : ℝ) ≤ (2 : ℝ) ^ res.S_ell := one_le_pow₀ (by norm_num)
      have h_piece_ge : matDensity X Y A_rem ≤ matDensity res.X_ell res.Y_ell A_rem := by
        have : 1 * matDensity X Y A_rem ≤ (2 : ℝ) ^ res.S_ell * matDensity X Y A_rem :=
          mul_le_mul_of_nonneg_right h1_le_2s hμ_prev_pos.le
        linarith
      let w := ((res.X_ell.card : ℝ) * (res.Y_ell.card : ℝ)) / ((X.card : ℝ) * (Y.card : ℝ))
      have hw_nonneg : 0 ≤ w := by unfold w; positivity
      have hzero := matDensity_zeroOutSubrect_eq A_rem hX hY hsubX hsubY
      have h_dec_eq : matDensity X Y A_rem - matDensity X Y A_next =
          w * matDensity res.X_ell res.Y_ell A_rem := by
        change matDensity X Y A_rem - matDensity X Y (zeroOutSubrect A_rem res.X_ell res.Y_ell) = _
        rw [hzero]
        unfold w
        ring
      have hstep := riemann_density_weighted_step hμ_prev_pos hμ_curr_nonneg h_piece_ge
        hw_nonneg (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1) h_dec_eq
      have hstep_le :
          w * (matDensity res.X_ell res.Y_ell A_rem) ^ ((1 : ℝ) / 4) ≤
            4 * ((matDensity X Y A_rem) ^ ((1 : ℝ) / 4) -
              (matDensity X Y A_next) ^ ((1 : ℝ) / 4)) := by
        have h12 := hstep.1.trans hstep.2
        linarith
      have hstep_area :
          (matDensity res.X_ell res.Y_ell res.A_ell) ^ ((1 : ℝ) / 4) *
            (res.X_ell.card : ℝ) * (res.Y_ell.card : ℝ) ≤
          4 * ((matDensity X Y A_rem) ^ ((1 : ℝ) / 4) -
            (matDensity X Y A_next) ^ ((1 : ℝ) / 4)) * (X.card : ℝ) * (Y.card : ℝ) := by
        rw [hA_eq, matDensity_submatZeroExt_eq]
        have hmul := mul_le_mul_of_nonneg_right hstep_le hXY_pos.le
        have hlhs :
            w * (matDensity res.X_ell res.Y_ell A_rem) ^ ((1 : ℝ) / 4) *
              ((X.card : ℝ) * (Y.card : ℝ)) =
            (matDensity res.X_ell res.Y_ell A_rem) ^ ((1 : ℝ) / 4) *
              (res.X_ell.card : ℝ) * (res.Y_ell.card : ℝ) := by
          unfold w
          field_simp [hXY_ne]
        linarith
      simp only [List.map_cons, List.sum_cons, if_neg htag_ne, zero_add]
      linarith

theorem cappedADecomp3DLoop_rpow_quarter_sum_le [DecidableEq α] [DecidableEq β]
    (fuel : ℕ) {X : Finset α} {Y : Finset β} {A_rem : α → β → ℝ}
    {ε : ℝ} {D : ℕ} {α_low α_cap : ℝ}
    (S : TwoStageSamplerOracle β ε)
    (hX : X.Nonempty) (hY : Y.Nonempty) (hA : IsBinaryMatrix X Y A_rem)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hD : 2 ≤ D)
    (hwindow : α_cap ≤ (2 : ℝ) ^ (48 : ℕ) * α_low) :
    ((cappedADecomp3DLoop fuel X Y A_rem ε D α_low α_cap S).map
      (fun P => (matDensity P.X_sub P.Y_sub P.A_sub) ^ ((1 : ℝ) / 4) *
        (P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ))).sum ≤
      4 * (matDensity X Y A_rem) ^ ((1 : ℝ) / 4) * (X.card : ℝ) * (Y.card : ℝ) := by
  have haux := cappedADecomp3DLoop_rpow_quarter_sum_aux fuel S hX hY hA hε0 hε_le hD hwindow
  have hres_nonneg :
      0 ≤ ((cappedADecomp3DLoop fuel X Y A_rem ε D α_low α_cap S).map
        (fun P => if P.tag = RectTag.residual then
          (matDensity P.X_sub P.Y_sub P.A_sub) ^ ((1 : ℝ) / 4) *
            (P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ)
          else 0)).sum := by
    refine List.sum_nonneg ?_
    intro v hv
    rw [List.mem_map] at hv
    rcases hv with ⟨P, hP, rfl⟩
    split_ifs with htag
    · have hbin := (cappedADecomp3DLoop_mem_subset fuel hA hP).2.2.1
      have h0 : 0 ≤ matDensity P.X_sub P.Y_sub P.A_sub :=
        matDensity_nonneg (isBinaryMatrix_nonneg hbin)
      have : 0 ≤ (matDensity P.X_sub P.Y_sub P.A_sub) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg h0 _
      positivity
    · exact le_rfl
  linarith

/-- Scale-sum and residual-piece invariant for `cappedADecomp3DLoop`
(`paper.tex` Theorem 4.4 `\label{thm:2d-decomp}` Clauses 1 & 4, §4.3):
1. Exactly one piece in `cappedADecomp3DLoop` has `tag = RectTag.residual`,
2. Every piece has `P.scale ≤ D` and every non-residual piece has $\mathbb{E}[P.A_{\text{sub}}] > 2^{-D}$,
3. $\sum_{P \in L : P.\text{tag} \ne \text{residual}} 2^{-P.\text{scale} \cdot D} \le 2^D M_{\text{rect3D}}(\varepsilon, D) \mathbb{E}[A_{\text{rem}}]$,
4. When $\mathbb{E}[A_{\text{rem}}] \cdot 2^{D + D^2} M_{\text{rect3D}}(\varepsilon, D) \le \text{fuel}$, the residual piece
   satisfies $P.X_{\text{sub}} = X$, $P.Y_{\text{sub}} = Y$, and $\mathbb{E}[P.A_{\text{sub}}] \le \max(2^{-D}, \alpha_{\text{low}})$. -/
theorem cappedADecomp3DLoop_scale_and_residual_spec [DecidableEq α] [DecidableEq β]
    (fuel : ℕ) {X : Finset α} {Y : Finset β} {A_rem : α → β → ℝ}
    {ε : ℝ} {D : ℕ} {α_low α_cap : ℝ}
    (S : TwoStageSamplerOracle β ε)
    (hX : X.Nonempty) (hY : Y.Nonempty) (hA : IsBinaryMatrix X Y A_rem)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hD : 2 ≤ D)
    (hwindow : α_cap ≤ (2 : ℝ) ^ (48 : ℕ) * α_low) :
    let L := cappedADecomp3DLoop fuel X Y A_rem ε D α_low α_cap S
    (L.map (fun P => if P.tag = RectTag.residual then (1 : ℝ) else 0)).sum = 1 ∧
    (∀ P ∈ L, P.scale ≤ D ∧
      (P.tag ≠ RectTag.residual → (2 : ℝ) ^ (-(D : ℤ)) < matDensity P.X_sub P.Y_sub P.A_sub)) ∧
    (((L.filter (fun P => decide (P.tag ≠ RectTag.residual))).map
      (fun P => (2 : ℝ) ^ (-(P.scale * D : ℤ)))).sum ≤
      (2 : ℝ) ^ D * M_rect3D ε D * matDensity X Y A_rem) ∧
    (matDensity X Y A_rem * ((2 : ℝ) ^ (D + D ^ 2) * M_rect3D ε D) ≤ (fuel : ℝ) →
      ∀ P ∈ L, P.tag = RectTag.residual →
        P.X_sub = X ∧ P.Y_sub = Y ∧
        matDensity P.X_sub P.Y_sub P.A_sub ≤ max ((2 : ℝ) ^ (-(D : ℤ))) α_low) := by
  classical
  have hε1 : ε < 1 := by linarith
  have hM_pos : 0 < M_rect3D ε D := by
    unfold M_rect3D
    have := one_le_goodRect3DStepFactor hε0 hε1.le D
    positivity
  have hX_pos : (0 : ℝ) < (X.card : ℝ) := Nat.cast_pos.mpr hX.card_pos
  have hY_pos : (0 : ℝ) < (Y.card : ℝ) := Nat.cast_pos.mpr hY.card_pos
  have hXY_pos : (0 : ℝ) < (X.card : ℝ) * (Y.card : ℝ) := mul_pos hX_pos hY_pos
  have hXY_ne : (X.card : ℝ) * (Y.card : ℝ) ≠ 0 := hXY_pos.ne'
  induction fuel generalizing A_rem with
  | zero =>
    dsimp only [cappedADecomp3DLoop]
    have hA0 : 0 ≤ matDensity X Y A_rem := matDensity_nonneg (isBinaryMatrix_nonneg hA)
    refine ⟨by simp, ?_, ?_, ?_⟩
    · intro P hP
      simp only [List.mem_singleton] at hP
      subst hP
      exact ⟨Nat.zero_le D, fun h => False.elim (h rfl)⟩
    · simp only [ne_eq, not_true_eq_false, decide_false, List.filter_cons_of_neg,
        Bool.not_eq_true, List.filter_nil, List.map_nil, List.sum_nil]
      positivity
    · intro hfuel P hP _
      simp only [List.mem_singleton] at hP
      subst hP
      simp only [Nat.cast_zero] at hfuel
      have hfac_pos : 0 < (2 : ℝ) ^ (D + D ^ 2) * M_rect3D ε D := by positivity
      have hA_eq0 : matDensity X Y A_rem = 0 := by nlinarith
      refine ⟨rfl, rfl, ?_⟩
      dsimp only
      rw [matDensity_submatZeroExt_eq, hA_eq0]
      exact le_trans (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (-(D : ℤ))) (le_max_left _ _)
  | succ k ih =>
    dsimp only [cappedADecomp3DLoop]
    have hA0 : 0 ≤ matDensity X Y A_rem := matDensity_nonneg (isBinaryMatrix_nonneg hA)
    split_ifs with hle
    · refine ⟨by simp, ?_, ?_, ?_⟩
      · intro P hP
        simp only [List.mem_singleton] at hP
        subst hP
        exact ⟨Nat.zero_le D, fun h => False.elim (h rfl)⟩
      · simp only [ne_eq, not_true_eq_false, decide_false, List.filter_cons_of_neg,
          Bool.not_eq_true, List.filter_nil, List.map_nil, List.sum_nil]
        positivity
      · intro _ P hP _
        simp only [List.mem_singleton] at hP
        subst hP
        dsimp only
        rw [matDensity_submatZeroExt_eq]
        exact ⟨rfl, rfl, hle⟩
    · push_neg at hle
      have hA_gt : (2 : ℝ) ^ (-(D : ℤ)) < matDensity X Y A_rem :=
        lt_of_le_of_lt (le_max_left _ _) hle
      have hα_low_lt : α_low < matDensity X Y A_rem :=
        lt_of_le_of_lt (le_max_right _ _) hle
      have hcap_win : α_cap ≤ (2 : ℝ) ^ (48 : ℕ) * matDensity X Y A_rem :=
        hwindow.trans (mul_le_mul_of_nonneg_left hα_low_lt.le (by positivity))
      rcases cappedGoodRect3D_spec S hX hY hA hε0 hε_le hD hA_gt hcap_win with
        ⟨hsubX, hsubY, _hneX, _hneY, hA_eq, _hsteps, hS_D, hdens_scale,
          _hY_shrink, hM_bound, htag_or, _hboost_spec, _hreg_spec⟩
      set res := cappedGoodRect3D X Y A_rem ε D α_cap S
      set A_next := zeroOutSubrect A_rem res.X_ell res.Y_ell
      have hA_next_bin : IsBinaryMatrix X Y A_next := isBinaryMatrix_zeroOutSubrect _ _ hA
      rcases ih hA_next_bin with ⟨hih_res1, hih_scale, hih_sum, hih_fuel⟩
      have htag_ne : res.tag ≠ RectTag.residual := by
        rcases htag_or with h | h <;> rw [h] <;> decide
      have h1_le_2s : (1 : ℝ) ≤ (2 : ℝ) ^ res.S_ell := one_le_pow₀ (by norm_num)
      have hpiece_gt : (2 : ℝ) ^ (-(D : ℤ)) < matDensity res.X_ell res.Y_ell A_rem := by
        have hpos : 0 < matDensity X Y A_rem := lt_trans (by positivity) hA_gt
        have : 1 * matDensity X Y A_rem ≤ (2 : ℝ) ^ res.S_ell * matDensity X Y A_rem :=
          mul_le_mul_of_nonneg_right h1_le_2s hpos.le
        linarith
      have hzero := matDensity_zeroOutSubrect_eq A_rem hX hY hsubX hsubY
      have hdrop_ge :
          (2 : ℝ) ^ (-(D : ℤ)) * (M_rect3D ε D)⁻¹ * (2 : ℝ) ^ (-(res.S_ell * D : ℤ)) ≤
            matDensity X Y A_rem - matDensity X Y A_next := by
        have h1 :
            ((M_rect3D ε D)⁻¹ * (2 : ℝ) ^ (-(res.S_ell * D : ℤ)) * ((X.card : ℝ) * (Y.card : ℝ))) *
              (2 : ℝ) ^ (-(D : ℤ)) ≤
            ((res.X_ell.card : ℝ) * (res.Y_ell.card : ℝ)) * matDensity res.X_ell res.Y_ell A_rem :=
          mul_le_mul hM_bound hpiece_gt.le (by positivity) (by positivity)
        have h2 := div_le_div_of_nonneg_right h1 hXY_pos.le
        have hlhs :
            (((M_rect3D ε D)⁻¹ * (2 : ℝ) ^ (-(res.S_ell * D : ℤ)) * ((X.card : ℝ) * (Y.card : ℝ))) *
              (2 : ℝ) ^ (-(D : ℤ))) / ((X.card : ℝ) * (Y.card : ℝ)) =
            (2 : ℝ) ^ (-(D : ℤ)) * (M_rect3D ε D)⁻¹ * (2 : ℝ) ^ (-(res.S_ell * D : ℤ)) := by
          field_simp [hXY_ne]
        have hrhs :
            (((res.X_ell.card : ℝ) * (res.Y_ell.card : ℝ)) * matDensity res.X_ell res.Y_ell A_rem) /
              ((X.card : ℝ) * (Y.card : ℝ)) =
            matDensity X Y A_rem - matDensity X Y A_next := by
          change _ = matDensity X Y A_rem - matDensity X Y (zeroOutSubrect A_rem res.X_ell res.Y_ell)
          rw [hzero]
          field_simp [hXY_ne]
          ring
        rwa [hlhs, hrhs] at h2
      have hscale_step :
          (2 : ℝ) ^ (-(res.S_ell * D : ℤ)) ≤
            (2 : ℝ) ^ D * M_rect3D ε D * (matDensity X Y A_rem - matDensity X Y A_next) := by
        have hmul := mul_le_mul_of_nonneg_left hdrop_ge
          (by positivity : 0 ≤ (2 : ℝ) ^ D * M_rect3D ε D)
        have hid :
            (2 : ℝ) ^ D * M_rect3D ε D *
              ((2 : ℝ) ^ (-(D : ℤ)) * (M_rect3D ε D)⁻¹ * (2 : ℝ) ^ (-(res.S_ell * D : ℤ))) =
            (2 : ℝ) ^ (-(res.S_ell * D : ℤ)) := by
          have h2D : (2 : ℝ) ^ D * (2 : ℝ) ^ (-(D : ℤ)) = 1 := by
            rw [← zpow_natCast 2 D, ← zpow_add₀ (by norm_num), add_neg_cancel, zpow_zero]
          have hM : M_rect3D ε D * (M_rect3D ε D)⁻¹ = 1 := mul_inv_cancel₀ hM_pos.ne'
          calc
            (2 : ℝ) ^ D * M_rect3D ε D *
                ((2 : ℝ) ^ (-(D : ℤ)) * (M_rect3D ε D)⁻¹ * (2 : ℝ) ^ (-(res.S_ell * D : ℤ)))
              = ((2 : ℝ) ^ D * (2 : ℝ) ^ (-(D : ℤ))) * (M_rect3D ε D * (M_rect3D ε D)⁻¹) *
                  (2 : ℝ) ^ (-(res.S_ell * D : ℤ)) := by ring
            _ = (2 : ℝ) ^ (-(res.S_ell * D : ℤ)) := by rw [h2D, hM]; ring
        rwa [hid] at hmul
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [List.map_cons, List.sum_cons, if_neg htag_ne, zero_add, hih_res1]
      · intro P hP
        simp only [List.mem_cons] at hP
        rcases hP with rfl | hP_tail
        · refine ⟨hS_D, fun _ => ?_⟩
          dsimp only
          rwa [hA_eq, matDensity_submatZeroExt_eq]
        · exact hih_scale P hP_tail
      · rw [List.filter_cons]
        dsimp only
        rw [if_pos (decide_eq_true htag_ne), List.map_cons, List.sum_cons]
        dsimp only
        linarith
      · intro hfuel P hP hP_res
        simp only [List.mem_cons] at hP
        rcases hP with rfl | hP_tail
        · exact False.elim (htag_ne hP_res)
        · apply hih_fuel _ P hP_tail hP_res
          have hSD_le : res.S_ell * D ≤ D ^ 2 := by
            rw [sq]
            exact Nat.mul_le_mul_right D hS_D
          have hzpow_ge : (1 : ℝ) ≤ (2 : ℝ) ^ (D ^ 2) * (2 : ℝ) ^ (-(res.S_ell * D : ℤ)) := by
            have h1 : (2 : ℝ) ^ (res.S_ell * D) ≤ (2 : ℝ) ^ (D ^ 2) :=
              pow_le_pow_right₀ (by norm_num) hSD_le
            have h2 : (2 : ℝ) ^ (res.S_ell * D) * (2 : ℝ) ^ (-(res.S_ell * D : ℤ)) = 1 := by
              have hcast : (-(res.S_ell * D : ℤ)) = -((res.S_ell * D : ℕ) : ℤ) := by push_cast; ring
              rw [hcast, ← zpow_natCast 2 (res.S_ell * D), ← zpow_add₀ (by norm_num),
                add_neg_cancel, zpow_zero]
            have h3 := mul_le_mul_of_nonneg_right h1
              (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (-(res.S_ell * D : ℤ)))
            linarith
          have hstep1 :
              1 ≤ (matDensity X Y A_rem - matDensity X Y A_next) *
                ((2 : ℝ) ^ (D + D ^ 2) * M_rect3D ε D) := by
            have hmul := mul_le_mul_of_nonneg_left hscale_step (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (D ^ 2))
            have hrhs :
                (2 : ℝ) ^ (D ^ 2) *
                  ((2 : ℝ) ^ D * M_rect3D ε D * (matDensity X Y A_rem - matDensity X Y A_next)) =
                (matDensity X Y A_rem - matDensity X Y A_next) *
                  ((2 : ℝ) ^ (D + D ^ 2) * M_rect3D ε D) := by
              rw [pow_add]
              ring
            linarith
          push_cast at hfuel
          linarith

lemma processGoodCubePiece_inr_fields [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {Y' : Finset β} {Z_curr : Finset γ} {B : β → γ → ℝ} {ε γ_val : ℝ} {D : ℕ}
    {S : TwoStageSamplerOracle β ε}
    {P : RectPiece α β} {sl : GoodCubeSlice α β γ}
    (hinr : processGoodCubePiece Y' Z_curr B ε γ_val D S P = Sum.inr sl) :
    sl.X_ell = P.X_sub ∧ sl.Y_ell = P.Y_sub ∧ sl.A_ell = P.A_sub ∧
    sl.tag = P.tag ∧ sl.S_ell = P.scale ∧
    (P.tag = RectTag.residual →
      sl.Z_ell = if matDensity P.X_sub P.Y_sub P.A_sub ≤ (2 : ℝ) ^ (-(D : ℤ)) then Z_curr else ∅) := by
  classical
  unfold processGoodCubePiece at hinr
  cases htag : P.tag <;> rw [htag] at hinr
  · dsimp only at hinr
    split_ifs at hinr with h4a h4c h4d
    cases hinr
    dsimp only
    exact ⟨rfl, rfl, rfl, rfl, rfl, fun h => by cases h⟩
  · dsimp only at hinr
    split_ifs at hinr with h4a
    cases hinr
    dsimp only
    exact ⟨rfl, rfl, rfl, rfl, rfl, fun h => by cases h⟩
  · cases hinr
    dsimp only
    exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

lemma processGoodCubePieces_inr_map_eq [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {Y' : Finset β} {Z_curr : Finset γ} {B : β → γ → ℝ} {ε γ_val : ℝ} {D : ℕ}
    {S : TwoStageSamplerOracle β ε}
    {L : List (RectPiece α β)} {slices : List (GoodCubeSlice α β γ)}
    (hinr : processGoodCubePieces Y' Z_curr B ε γ_val D S L = Sum.inr slices) :
    (∀ (τ : Type*) (f : Finset α → Finset β → (α → β → ℝ) → RectTag → ℕ → τ),
      slices.map (fun sl => f sl.X_ell sl.Y_ell sl.A_ell sl.tag sl.S_ell) =
        L.map (fun P => f P.X_sub P.Y_sub P.A_sub P.tag P.scale)) ∧
    slices.length = L.length ∧
    (∀ sl ∈ slices, ∃ P ∈ L,
      sl.X_ell = P.X_sub ∧ sl.Y_ell = P.Y_sub ∧ sl.A_ell = P.A_sub ∧
      sl.tag = P.tag ∧ sl.S_ell = P.scale ∧
      (P.tag = RectTag.residual →
        sl.Z_ell = if matDensity P.X_sub P.Y_sub P.A_sub ≤ (2 : ℝ) ^ (-(D : ℤ)) then Z_curr else ∅)) := by
  induction L generalizing slices with
  | nil =>
    unfold processGoodCubePieces at hinr
    cases hinr
    exact ⟨fun _ _ => rfl, rfl, fun _ h => by cases h⟩
  | cons P rest ih =>
    unfold processGoodCubePieces at hinr
    cases hP : processGoodCubePiece Y' Z_curr B ε γ_val D S P with
    | inl step =>
      rw [hP] at hinr; cases hinr
    | inr sl =>
      rw [hP] at hinr
      cases hrest : processGoodCubePieces Y' Z_curr B ε γ_val D S rest with
      | inl step =>
        rw [hrest] at hinr; cases hinr
      | inr sls =>
        rw [hrest] at hinr
        cases hinr
        rcases processGoodCubePiece_inr_fields hP with ⟨hX, hY, hA, htag, hS, hZ⟩
        rcases ih hrest with ⟨hmap, hlen, hmem⟩
        refine ⟨fun τ f => ?_, by simp [hlen], fun s hs => ?_⟩
        · simp only [List.map_cons, hX, hY, hA, htag, hS, hmap τ f]
        · simp only [List.mem_cons] at hs
          rcases hs with rfl | hs_tail
          · exact ⟨P, List.mem_cons_self, hX, hY, hA, htag, hS, hZ⟩
          · rcases hmem s hs_tail with ⟨Q, hQ, hQX⟩
            exact ⟨Q, List.mem_cons_of_mem P hQ, hQX⟩

lemma cappedGoodCubeLoop_normal_slices_eq [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (fuel : ℕ) (X : Finset α) (Y_curr : Finset β) (Z_curr : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    (ε γ_val : ℝ) (D : ℕ) (α_cap β_init : ℝ)
    (S : TwoStageSamplerOracle β ε)
    (hmode : (cappedGoodCubeLoop fuel X Y_curr Z_curr A B ε γ_val D α_cap β_init S).mode =
      CubeMode.normal) :
    let res := cappedGoodCubeLoop fuel X Y_curr Z_curr A B ε γ_val D α_cap β_init S
    processGoodCubePieces res.Y_star res.Z_star B ε γ_val D S
      (cappedADecomp3D X res.Y_star A ε D (cLow3D * α_cap) (cCap3D * α_cap) S) =
      Sum.inr res.slices := by
  classical
  induction fuel generalizing Y_curr Z_curr with
  | zero =>
    unfold cappedGoodCubeLoop at hmode
    cases hmode
  | succ k ih =>
    dsimp only at hmode ⊢
    unfold cappedGoodCubeLoop at hmode ⊢
    dsimp only at hmode ⊢
    by_cases hboost : matDensity Y_curr Z_curr B ≥ 16 * β_init
    · rw [if_pos hboost] at hmode
      cases hmode
    · rw [if_neg hboost] at hmode ⊢
      by_cases hstep1 :
          (minDegree Y_curr Z_curr B (ε * γ_val / 2) (1 / 2)).2 = 2 ∨
            matDensity (minDegree Y_curr Z_curr B (ε * γ_val / 2) (1 / 2)).1 Z_curr B ≥
              (1 + ε * γ_val / 4) * matDensity Y_curr Z_curr B
      · rw [if_pos hstep1] at hmode ⊢
        exact ih _ _ hmode
      · rw [if_neg hstep1] at hmode ⊢
        revert hmode
        cases hproc :
            processGoodCubePieces (minDegree Y_curr Z_curr B (ε * γ_val / 2) (1 / 2)).1
              Z_curr B ε γ_val D S
              (cappedADecomp3D X (minDegree Y_curr Z_curr B (ε * γ_val / 2) (1 / 2)).1
                A ε D (cLow3D * α_cap) (cCap3D * α_cap) S) with
        | inl step =>
          rcases step with ⟨Y_next, Z_next, s_step⟩
          intro hmode
          exact ih _ _ hmode
        | inr slices =>
          intro _hmode
          exact hproc

lemma list_filter_decide_map_sum_eq {σ : Type*} (L : List σ) (p : σ → Prop) [DecidablePred p]
    (f : σ → ℝ) :
    ((L.filter (fun x => decide (p x))).map f).sum =
      (L.map (fun x => if p x then f x else 0)).sum := by
  induction L with
  | nil => simp
  | cons a l ih =>
    rw [List.filter_cons]
    by_cases h : p a <;> simp [h, ih]

/-- **Additional Slice Guarantees of `cappedGoodCube` in Normal Mode (`cappedGoodCube_normal_extra_spec`,
`paper.tex` Algorithm 5 Line 5 `\label{line:cube-zl}` & Lemma 5.3 `\label{lem:cube-step}`, §5.2 & §5.4)**:
When `res := cappedGoodCube X Y Z A B ε gamma3D D α_cap (matDensity Y Z B) S` has `res.mode = CubeMode.normal`,
`res.slices` inherits from `cappedADecomp3D X res.Y_star A ε D (cLow3D * α_cap) (cCap3D * α_cap) S`:
1. First-moment conservation $\sum_{sl} \mathbb{E}[sl.A_\ell] |sl.X_\ell| |sl.Y_\ell| = \mathbb{E}[A[X, Y^*]] |X| |Y^*|$,
2. Riemann $p = 1/4$ bound $\sum_{sl} (\mathbb{E}[sl.A_\ell])^{1/4} |sl.X_\ell| |sl.Y_\ell| \le 4 (\mathbb{E}[A[X, Y^*]])^{1/4} |X| |Y^*|$,
3. Residual indicator sum $\sum_{sl : \text{residual}} 1 = 1$,
4. Scale-sum bound $\sum_{sl : \text{non-residual}} 2^{-sl.S_\ell \cdot D} \le 2^D M_{\text{rect3D}}(\varepsilon, D)$,
5. Slice count `res.slices.length ≤ rDecompAFuel ε D + 1`, and
6. For every `sl ∈ res.slices`, `sl.S_ell ≤ D`, non-residual slices have $\mathbb{E}[sl.A_\ell] > 2^{-D}$,
   and residual slices have $sl.X_\ell = X, sl.Y_\ell = Y^*$ and $\mathbb{E}[sl.A_\ell] \le \max(2^{-D}, c_{\text{low}}\alpha_{\text{cap}})$. -/
theorem cappedGoodCube_normal_extra_spec [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {X : Finset α} {Y : Finset β} {Z : Finset γ}
    {A : α → β → ℝ} {B : β → γ → ℝ}
    {ε : ℝ} {D : ℕ} {α_cap : ℝ}
    (S : TwoStageSamplerOracle β ε)
    (hX : X.Nonempty) (hY : Y.Nonempty) (hZ : Z.Nonempty)
    (hA : IsBinaryMatrix X Y A) (hB : IsBinaryMatrix Y Z B)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hD : 2 ≤ D)
    (hα_nonneg : 0 ≤ α_cap)
    (hB_gt : (2 : ℝ) ^ (-(D : ℤ)) < matDensity Y Z B)
    (hmode : (cappedGoodCube X Y Z A B ε gamma3D D α_cap (matDensity Y Z B) S).mode =
      CubeMode.normal) :
    let res := cappedGoodCube X Y Z A B ε gamma3D D α_cap (matDensity Y Z B) S
    (res.slices.map (fun sl =>
      matDensity sl.X_ell sl.Y_ell sl.A_ell * (sl.X_ell.card : ℝ) * (sl.Y_ell.card : ℝ))).sum =
      matDensity X res.Y_star A * (X.card : ℝ) * (res.Y_star.card : ℝ) ∧
    (res.slices.map (fun sl =>
      (matDensity sl.X_ell sl.Y_ell sl.A_ell) ^ ((1 : ℝ) / 4) *
        (sl.X_ell.card : ℝ) * (sl.Y_ell.card : ℝ))).sum ≤
      4 * (matDensity X res.Y_star A) ^ ((1 : ℝ) / 4) * (X.card : ℝ) * (res.Y_star.card : ℝ) ∧
    (res.slices.map (fun sl => if sl.tag = RectTag.residual then (1 : ℝ) else 0)).sum = 1 ∧
    (((res.slices.filter (fun sl => decide (sl.tag ≠ RectTag.residual))).map
      (fun sl => (2 : ℝ) ^ (-(sl.S_ell * D : ℤ)))).sum ≤ (2 : ℝ) ^ D * M_rect3D ε D) ∧
    res.slices.length ≤ rDecompAFuel ε D + 1 ∧
    (∀ sl ∈ res.slices, sl.S_ell ≤ D ∧
      (sl.tag ≠ RectTag.residual → (2 : ℝ) ^ (-(D : ℤ)) < matDensity sl.X_ell sl.Y_ell sl.A_ell) ∧
      (sl.tag = RectTag.residual →
        sl.X_ell = X ∧ sl.Y_ell = res.Y_star ∧
        matDensity sl.X_ell sl.Y_ell sl.A_ell ≤ max ((2 : ℝ) ^ (-(D : ℤ))) (cLow3D * α_cap) ∧
        sl.Z_ell =
          if matDensity sl.X_ell sl.Y_ell sl.A_ell ≤ (2 : ℝ) ^ (-(D : ℤ)) then
            res.Z_star
          else
            ∅)) := by
  classical
  rcases thm_3d_decomp_part1 S hX hY hZ hA hB hε0 hε_le hD hα_nonneg hB_gt with
    ⟨_hX_eq, hsubY, _hsubZ, hneY, _hneZ, _⟩
  set res := cappedGoodCube X Y Z A B ε gamma3D D α_cap (matDensity Y Z B) S
  have hproc := cappedGoodCubeLoop_normal_slices_eq (rCubeFuel ε gamma3D)
    X Y Z A B ε gamma3D D α_cap (matDensity Y Z B) S hmode
  change processGoodCubePieces res.Y_star res.Z_star B ε gamma3D D S
    (cappedADecomp3D X res.Y_star A ε D (cLow3D * α_cap) (cCap3D * α_cap) S) = Sum.inr res.slices at hproc
  rcases processGoodCubePieces_inr_map_eq hproc with ⟨hmap, hlen, hmem⟩
  set L := cappedADecomp3D X res.Y_star A ε D (cLow3D * α_cap) (cCap3D * α_cap) S
  have hA_Ystar : IsBinaryMatrix X res.Y_star A := isBinaryMatrix_subset Finset.Subset.rfl hsubY hA
  have hwin : cCap3D * α_cap ≤ (2 : ℝ) ^ (48 : ℕ) * (cLow3D * α_cap) := by
    have : cCap3D * α_cap = (2 : ℝ) ^ (48 : ℕ) * (cLow3D * α_cap) := by
      unfold cCap3D cLow3D; norm_num; ring
    linarith
  have hmom := cappedADecomp3DLoop_first_moment_eq (rDecompAFuel ε D) hX hneY A ε D
    (cLow3D * α_cap) (cCap3D * α_cap) S
  have hrpow := cappedADecomp3DLoop_rpow_quarter_sum_le (rDecompAFuel ε D) S
    hX hneY hA_Ystar hε0 hε_le hD hwin
  rcases cappedADecomp3DLoop_scale_and_residual_spec (rDecompAFuel ε D) S
    hX hneY hA_Ystar hε0 hε_le hD hwin with ⟨hres1, hscale_D, hscale_sum, hres_spec⟩
  have hA_le_1 : matDensity X res.Y_star A ≤ 1 :=
    matDensity_le_one_of_isBinaryMatrix hA_Ystar
  have hε1 : ε < 1 := by linarith
  have hM_pos : 0 < M_rect3D ε D := by
    unfold M_rect3D
    have := one_le_goodRect3DStepFactor hε0 hε1.le D
    positivity
  have hfuel_bound :
      matDensity X res.Y_star A * ((2 : ℝ) ^ (D + D ^ 2) * M_rect3D ε D) ≤
        (rDecompAFuel ε D : ℝ) := by
    have h1 :
        matDensity X res.Y_star A * ((2 : ℝ) ^ (D + D ^ 2) * M_rect3D ε D) ≤
          1 * ((2 : ℝ) ^ (D + D ^ 2) * M_rect3D ε D) :=
      mul_le_mul_of_nonneg_right hA_le_1 (by positivity)
    rw [one_mul] at h1
    exact h1.trans (Nat.le_ceil _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmap ℝ (fun X_s Y_s A_s _ _ => matDensity X_s Y_s A_s * (X_s.card : ℝ) * (Y_s.card : ℝ))]
    exact hmom
  · rw [hmap ℝ (fun X_s Y_s A_s _ _ =>
      (matDensity X_s Y_s A_s) ^ ((1 : ℝ) / 4) * (X_s.card : ℝ) * (Y_s.card : ℝ))]
    exact hrpow
  · rw [hmap ℝ (fun _ _ _ tag _ => if tag = RectTag.residual then (1 : ℝ) else 0)]
    exact hres1
  · rw [list_filter_decide_map_sum_eq res.slices (fun sl => sl.tag ≠ RectTag.residual)
      (fun sl => (2 : ℝ) ^ (-(sl.S_ell * D : ℤ))),
      hmap ℝ (fun _ _ _ tag sc => if tag ≠ RectTag.residual then (2 : ℝ) ^ (-(sc * D : ℤ)) else 0),
      ← list_filter_decide_map_sum_eq L (fun P => P.tag ≠ RectTag.residual)
        (fun P => (2 : ℝ) ^ (-(P.scale * D : ℤ)))]
    have h1 : (2 : ℝ) ^ D * M_rect3D ε D * matDensity X res.Y_star A ≤
        (2 : ℝ) ^ D * M_rect3D ε D * 1 :=
      mul_le_mul_of_nonneg_left hA_le_1 (by positivity)
    exact hscale_sum.trans (by linarith [h1])
  · rw [hlen]
    exact cappedADecomp3DLoop_length_le (rDecompAFuel ε D) X res.Y_star A ε D
      (cLow3D * α_cap) (cCap3D * α_cap) S
  · intro sl hsl
    rcases hmem sl hsl with ⟨P, hP, hX_eq, hY_eq, hA_eq, htag_eq, hS_eq, hZ_eq⟩
    rw [hX_eq, hY_eq, hA_eq, htag_eq, hS_eq]
    rcases hscale_D P hP with ⟨hP_sc, hP_nonres⟩
    refine ⟨hP_sc, hP_nonres, fun hres => ?_⟩
    rcases hres_spec hfuel_bound P hP hres with ⟨hPX, hPY, hPdens⟩
    exact ⟨hPX, hPY, hPdens, hZ_eq hres⟩

/-!
### Subsection 4.3: Jump-Adaptive Depth Increments & Piece-Count Tree Bound
(`paper.tex` Algorithm 5 (`Decompose3D`) Lines 18 & 22 `\label{line:3d-dhb}`, `\label{line:3d-dhl}`, `\eqref{eq:th-inductive}`, §5.2 & §5.4 & §5.5)
-/

/-- Unclamped $B$-boost depth increment
$\max(1, \lfloor \frac{3}{4}\log_2(\beta^* / \beta) - 2 \rfloor)$
(`paper.tex` Algorithm 5 (`Decompose3D`) Line 18 `\label{line:3d-dhb}`, §5.2). -/
noncomputable def rawDeltaHB (β_star β : ℝ) : ℕ :=
  max 1 (Int.toNat (Int.floor ((3 / 4 : ℝ) * Real.logb 2 (β_star / β) - 2)))

lemma one_le_rawDeltaHB (β_star β : ℝ) : 1 ≤ rawDeltaHB β_star β :=
  le_max_left 1 _

/-- **Case A Depth-Jump Bound (`two_pow_min_rawDeltaHB_le`, §5.4 of `paper.tex`)**:
When $\beta > 0$ and $\beta^* \ge 16\beta$, for any remaining depth budget `rem : ℕ`,
$$2^{\min(\text{rem}, \text{rawDeltaHB }\beta^* \beta)} \le \frac{1}{4}\left(\frac{\beta^*}{\beta}\right)^{3/4}.$$ -/
theorem two_pow_min_rawDeltaHB_le (rem : ℕ) {β_star β : ℝ}
    (hβ_pos : 0 < β) (hboost : 16 * β ≤ β_star) :
    (2 : ℝ) ^ ((min rem (rawDeltaHB β_star β) : ℕ) : ℝ) ≤
      (1 / 4 : ℝ) * (β_star / β) ^ ((3 : ℝ) / 4) := by
  have hdiv_ge : 16 ≤ β_star / β := (le_div_iff₀ hβ_pos).mpr hboost
  have hdiv_pos : 0 < β_star / β := by linarith
  have hlog_ge : 4 ≤ Real.logb 2 (β_star / β) := by
    have h16 : (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by norm_num
    rw [h16] at hdiv_ge
    have h1 := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by norm_num) hdiv_ge
    rwa [Real.logb_rpow (by norm_num) (by norm_num)] at h1
  have hval_ge : 1 ≤ (3 / 4 : ℝ) * Real.logb 2 (β_star / β) - 2 := by linarith
  have hfloor_ge : (1 : ℤ) ≤ Int.floor ((3 / 4 : ℝ) * Real.logb 2 (β_star / β) - 2) :=
    Int.le_floor.mpr (by exact_mod_cast hval_ge)
  have hraw_eq :
      (rawDeltaHB β_star β : ℝ) =
        (Int.floor ((3 / 4 : ℝ) * Real.logb 2 (β_star / β) - 2) : ℝ) := by
    unfold rawDeltaHB
    have htonat : 1 ≤ (Int.floor ((3 / 4 : ℝ) * Real.logb 2 (β_star / β) - 2)).toNat := by omega
    rw [max_eq_right htonat]
    exact_mod_cast Int.toNat_of_nonneg (by omega)
  have hmin_le :
      ((min rem (rawDeltaHB β_star β) : ℕ) : ℝ) ≤
        (3 / 4 : ℝ) * Real.logb 2 (β_star / β) - 2 := by
    have h1 : ((min rem (rawDeltaHB β_star β) : ℕ) : ℝ) ≤ (rawDeltaHB β_star β : ℝ) := by
      exact_mod_cast min_le_right rem (rawDeltaHB β_star β)
    exact h1.trans (hraw_eq.trans_le (Int.floor_le _))
  calc
    (2 : ℝ) ^ ((min rem (rawDeltaHB β_star β) : ℕ) : ℝ)
      ≤ (2 : ℝ) ^ ((3 / 4 : ℝ) * Real.logb 2 (β_star / β) - 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hmin_le
    _ = (2 : ℝ) ^ (- (2 : ℝ)) * (2 : ℝ) ^ (Real.logb 2 (β_star / β) * ((3 : ℝ) / 4)) := by
        rw [sub_eq_add_neg, Real.rpow_add (by norm_num)]
        ring_nf
    _ = (1 / 4 : ℝ) * (β_star / β) ^ ((3 : ℝ) / 4) := by
        rw [Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hdiv_pos]
        norm_num

lemma scale_le_fifty_mul_rawDeltaHB {s : ℕ} {β_star β : ℝ}
    (hβ_pos : 0 < β) (hscale : (2 : ℝ) ^ s * β ≤ β_star) :
    s ≤ 50 * rawDeltaHB β_star β := by
  by_cases hs : s ≤ 50
  · have := one_le_rawDeltaHB β_star β
    omega
  · push_neg at hs
    have hdiv : (2 : ℝ) ^ (s : ℝ) ≤ β_star / β := by
      rw [Real.rpow_natCast, le_div_iff₀ hβ_pos]
      exact hscale
    have hlog : (s : ℝ) ≤ Real.logb 2 (β_star / β) := by
      have h1 := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) hdiv
      rwa [Real.logb_rpow (by norm_num) (by norm_num)] at h1
    have hfloor_gt :
        (3 / 4 : ℝ) * (s : ℝ) - 3 ≤
          (Int.floor ((3 / 4 : ℝ) * Real.logb 2 (β_star / β) - 2) : ℝ) := by
      have hlt := Int.sub_one_lt_floor ((3 / 4 : ℝ) * Real.logb 2 (β_star / β) - 2)
      linarith
    have hs_real : (51 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    have hpos_floor : 1 ≤ Int.floor ((3 / 4 : ℝ) * Real.logb 2 (β_star / β) - 2) := by
      apply Int.le_floor.mpr
      push_cast
      linarith
    have hraw_ge : (3 / 4 : ℝ) * (s : ℝ) - 3 ≤ (rawDeltaHB β_star β : ℝ) := by
      unfold rawDeltaHB
      have hle :
          (Int.floor ((3 / 4 : ℝ) * Real.logb 2 (β_star / β) - 2)).toNat ≤
            max 1 (Int.floor ((3 / 4 : ℝ) * Real.logb 2 (β_star / β) - 2)).toNat :=
        le_max_right _ _
      have hcast :
          (Int.floor ((3 / 4 : ℝ) * Real.logb 2 (β_star / β) - 2) : ℝ) ≤
            ((max 1 (Int.floor ((3 / 4 : ℝ) * Real.logb 2 (β_star / β) - 2)).toNat : ℕ) : ℝ) := by
        have htonat :
            ((Int.floor ((3 / 4 : ℝ) * Real.logb 2 (β_star / β) - 2)).toNat : ℤ) =
              Int.floor ((3 / 4 : ℝ) * Real.logb 2 (β_star / β) - 2) :=
          Int.toNat_of_nonneg (by omega)
        exact_mod_cast (htonat ▸ Int.ofNat_le.mpr hle)
      exact hfloor_gt.trans hcast
    have h50 : (s : ℝ) ≤ 50 * (rawDeltaHB β_star β : ℝ) := by linarith
    exact_mod_cast h50

/-- Unclamped $A$-boost depth increment
$\max(1, \lfloor \frac{3}{4}\log_2(\alpha_\ell / \alpha_{\text{cap}}) - 11 \rfloor)$
(`paper.tex` Algorithm 5 (`Decompose3D`) Line 22 `\label{line:3d-dhl}`, §5.2). -/
noncomputable def rawDeltaHA (α_ell α_cap : ℝ) : ℕ :=
  max 1 (Int.toNat (Int.floor ((3 / 4 : ℝ) * Real.logb 2 (α_ell / α_cap) - 11)))

lemma one_le_rawDeltaHA (α_ell α_cap : ℝ) : 1 ≤ rawDeltaHA α_ell α_cap :=
  le_max_left 1 _

/-- Exact computable `ℕ` evaluation of `rawDeltaHB (p₁ / q₁) (p₂ / q₂)` via integer division and
`Nat.log 2` (`paper.tex` Algorithm 5 (`Decompose3D`) Line 18 `\label{line:3d-dhb}`):
$$\text{rawDeltaHBNat}(p_1, q_1, p_2, q_2) := \max\left(1, \lfloor \log_2(\lfloor (p_1 q_2)^3 / (p_2 q_1)^3 \rfloor) \rfloor / 4 - 2\right).$$ -/
def rawDeltaHBNat (p₁ q₁ p₂ q₂ : ℕ) : ℕ :=
  max 1 (Nat.log 2 (((p₁ * q₂) ^ 3) / ((p₂ * q₁) ^ 3)) / 4 - 2)

/-- Cost-tracked evaluation of `rawDeltaHBNat` in `CostM`. -/
def rawDeltaHBNatTracked (p₁ q₁ p₂ q₂ : ℕ) : CostM ℕ :=
  CostM.bind (mulNatTracked p₁ q₂) (fun pq₁ =>
    CostM.bind (mulNatTracked p₂ q₁) (fun pq₂ =>
      CostM.bind (powNatTracked pq₁ 3) (fun num3 =>
        CostM.bind (powNatTracked pq₂ 3) (fun den3 =>
          CostM.bind (divNatTracked num3 den3) (fun quot =>
            CostM.bind (log2NatTracked quot) (fun lg =>
              CostM.bind (divNatTracked lg 4) (fun q4 =>
                CostM.bind (subNatTracked q4 2) (fun s =>
                  retTracked (max 1 s)))))))))

/-- Exact computable `ℕ` evaluation of `rawDeltaHA (p₁ / q₁) (p₂ / q₂)` via integer division and
`Nat.log 2` (`paper.tex` Algorithm 5 (`Decompose3D`) Line 22 `\label{line:3d-dhl}`):
$$\text{rawDeltaHANat}(p_1, q_1, p_2, q_2) := \max\left(1, \lfloor \log_2(\lfloor (p_1 q_2)^3 / (p_2 q_1)^3 \rfloor) \rfloor / 4 - 11\right).$$ -/
def rawDeltaHANat (p₁ q₁ p₂ q₂ : ℕ) : ℕ :=
  max 1 (Nat.log 2 (((p₁ * q₂) ^ 3) / ((p₂ * q₁) ^ 3)) / 4 - 11)

/-- Cost-tracked evaluation of `rawDeltaHANat` in `CostM`. -/
def rawDeltaHANatTracked (p₁ q₁ p₂ q₂ : ℕ) : CostM ℕ :=
  CostM.bind (mulNatTracked p₁ q₂) (fun pq₁ =>
    CostM.bind (mulNatTracked p₂ q₁) (fun pq₂ =>
      CostM.bind (powNatTracked pq₁ 3) (fun num3 =>
        CostM.bind (powNatTracked pq₂ 3) (fun den3 =>
          CostM.bind (divNatTracked num3 den3) (fun quot =>
            CostM.bind (log2NatTracked quot) (fun lg =>
              CostM.bind (divNatTracked lg 4) (fun q4 =>
                CostM.bind (subNatTracked q4 11) (fun s =>
                  retTracked (max 1 s)))))))))

/-- Support cardinality of `M` on `U × V`, bounded by `U.card * V.card`. -/
noncomputable def supportCountRealNat (U : Finset α) (V : Finset β) (M : α → β → ℝ) : ℕ :=
  letI := Classical.propDecidable
  ∑ x ∈ U, ∑ y ∈ V, if 0 < M x y then 1 else 0

lemma supportCountRealNat_le_card_mul (U : Finset α) (V : Finset β) (M : α → β → ℝ) :
    supportCountRealNat U V M ≤ U.card * V.card := by
  classical
  unfold supportCountRealNat
  calc
    (∑ x ∈ U, ∑ y ∈ V, if 0 < M x y then 1 else 0)
      ≤ ∑ _x ∈ U, ∑ _y ∈ V, 1 := by
        refine Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => ?_))
        split_ifs <;> omega
    _ = U.card * V.card := by simp

lemma matDensity_eq_supportCountRealNat_div {U : Finset α} {V : Finset β} {M : α → β → ℝ}
    (hM : IsBinaryMatrix U V M) :
    matDensity U V M =
      (supportCountRealNat U V M : ℝ) / ((U.card * V.card : ℕ) : ℝ) := by
  classical
  unfold matDensity rowDeg expectSet supportCountRealNat
  simp only [← Finset.sum_div, div_div, Nat.cast_sum, Nat.cast_mul, mul_comm (U.card : ℝ)]
  congr 1
  refine Finset.sum_congr rfl (fun x hx => Finset.sum_congr rfl (fun y hy => ?_))
  rcases hM x hx y hy with h0 | h1
  · simp [h0]
  · simp [h1]

lemma dyadicColAlpha_eq_mul_supportCount_div {X' : Finset α} {Y' : Finset β} {A' : α → β → ℝ}
    (hA' : IsBinaryMatrix X' Y' A') (j : ℕ) :
    dyadicColAlpha (matDensity X' Y' A') j =
      ((2 ^ j * supportCountRealNat X' Y' A' : ℕ) : ℝ) / ((X'.card * Y'.card : ℕ) : ℝ) := by
  unfold dyadicColAlpha
  rw [matDensity_eq_supportCountRealNat_div hA']
  push_cast
  ring

/-- Computable cost factor for `rawDeltaHANatTracked` and `clampDeltaHATracked` when the cap
numerator is bounded by $2^D \cdot S^2$. -/
def deltaHACostFactor (D : ℕ) : ℕ :=
  2400 * (D + 1) ^ 2

lemma bitLengthNat_le_of_le_two_pow_local {x k : ℕ} (hx : x ≤ 2 ^ k) :
    bitLengthNat x ≤ k + 1 := by
  unfold bitLengthNat
  have hlog : Nat.log 2 x ≤ k :=
    (Nat.log_mono_right hx).trans_eq (Nat.log_pow (by norm_num) k)
  omega

lemma rawDeltaHBNatTracked_snd_le {S p₁ q₁ p₂ q₂ : ℕ} (hS : 2 ≤ S)
    (hp₁ : p₁ ≤ S ^ 2) (hq₁ : q₁ ≤ S ^ 2) (hp₂ : p₂ ≤ S ^ 2) (hq₂ : q₂ ≤ S ^ 2) :
    (rawDeltaHBNatTracked p₁ q₁ p₂ q₂).2 + 1 + 2 * S ^ 2 ≤ 2400 * S ^ 2 := by
  have hS_pow : S ≤ 2 ^ S := Nat.le_of_lt Nat.lt_two_pow_self
  have hS2_pow : S ^ 2 ≤ 2 ^ (2 * S) := by
    calc
      S ^ 2 ≤ (2 ^ S) ^ 2 := Nat.pow_le_pow_left hS_pow 2
      _ = 2 ^ (2 * S) := by rw [← Nat.pow_mul, mul_comm]
  have hS4_pow : S ^ 2 * S ^ 2 ≤ 2 ^ (4 * S) := by
    calc
      S ^ 2 * S ^ 2 ≤ 2 ^ (2 * S) * 2 ^ (2 * S) := Nat.mul_le_mul hS2_pow hS2_pow
      _ = 2 ^ (2 * S + 2 * S) := (Nat.pow_add 2 (2 * S) (2 * S)).symm
      _ = 2 ^ (4 * S) := by congr 1; ring
  have hS12_pow : (S ^ 2 * S ^ 2) ^ 3 ≤ 2 ^ (12 * S) := by
    calc
      (S ^ 2 * S ^ 2) ^ 3 ≤ (2 ^ (4 * S)) ^ 3 := Nat.pow_le_pow_left hS4_pow 3
      _ = 2 ^ (4 * S * 3) := (Nat.pow_mul 2 (4 * S) 3).symm
      _ = 2 ^ (12 * S) := by congr 1; ring
  have hbp₁ : bitLengthNat p₁ ≤ 3 * S := by
    have := bitLengthNat_le_of_le_two_pow_local (hp₁.trans hS2_pow); omega
  have hbq₁ : bitLengthNat q₁ ≤ 3 * S := by
    have := bitLengthNat_le_of_le_two_pow_local (hq₁.trans hS2_pow); omega
  have hbp₂ : bitLengthNat p₂ ≤ 3 * S := by
    have := bitLengthNat_le_of_le_two_pow_local (hp₂.trans hS2_pow); omega
  have hbq₂ : bitLengthNat q₂ ≤ 3 * S := by
    have := bitLengthNat_le_of_le_two_pow_local (hq₂.trans hS2_pow); omega
  have hpq₁_le : p₁ * q₂ ≤ 2 ^ (4 * S) := (Nat.mul_le_mul hp₁ hq₂).trans hS4_pow
  have hpq₂_le : p₂ * q₁ ≤ 2 ^ (4 * S) := (Nat.mul_le_mul hp₂ hq₁).trans hS4_pow
  have hbpq₁ : bitLengthNat (p₁ * q₂) ≤ 5 * S := by
    have := bitLengthNat_le_of_le_two_pow_local hpq₁_le; omega
  have hbpq₂ : bitLengthNat (p₂ * q₁) ≤ 5 * S := by
    have := bitLengthNat_le_of_le_two_pow_local hpq₂_le; omega
  have hnum3_le : (p₁ * q₂) ^ 3 ≤ 2 ^ (12 * S) :=
    (Nat.pow_le_pow_left (Nat.mul_le_mul hp₁ hq₂) 3).trans hS12_pow
  have hden3_le : (p₂ * q₁) ^ 3 ≤ 2 ^ (12 * S) :=
    (Nat.pow_le_pow_left (Nat.mul_le_mul hp₂ hq₁) 3).trans hS12_pow
  have hbnum3 : bitLengthNat ((p₁ * q₂) ^ 3) ≤ 13 * S := by
    have := bitLengthNat_le_of_le_two_pow_local hnum3_le; omega
  have hbden3 : bitLengthNat ((p₂ * q₁) ^ 3) ≤ 13 * S := by
    have := bitLengthNat_le_of_le_two_pow_local hden3_le; omega
  set quot := ((p₁ * q₂) ^ 3) / ((p₂ * q₁) ^ 3)
  have hquot_le : quot ≤ 2 ^ (12 * S) := (Nat.div_le_self _ _).trans hnum3_le
  have hbquot : bitLengthNat quot ≤ 13 * S := by
    have := bitLengthNat_le_of_le_two_pow_local hquot_le; omega
  set lg := Nat.log 2 quot
  have hlg_le : lg ≤ 2 ^ (12 * S) := (Nat.log_le_self 2 quot).trans hquot_le
  have hblg : bitLengthNat lg ≤ 13 * S := by
    have := bitLengthNat_le_of_le_two_pow_local hlg_le; omega
  set q4 := lg / 4
  have hq4_le : q4 ≤ 2 ^ (12 * S) := (Nat.div_le_self lg 4).trans hlg_le
  have hbq4 : bitLengthNat q4 ≤ 13 * S := by
    have := bitLengthNat_le_of_le_two_pow_local hq4_le; omega
  have hb4 : bitLengthNat 4 ≤ 3 :=
    bitLengthNat_le_of_le_two_pow_local (by norm_num : 4 ≤ 2 ^ 2)
  have hb2 : bitLengthNat 2 ≤ 2 :=
    bitLengthNat_le_of_le_two_pow_local (by norm_num : 2 ≤ 2 ^ 1)
  have hm1 : bitLengthNat p₁ * bitLengthNat q₂ ≤ 9 * S ^ 2 := by
    calc bitLengthNat p₁ * bitLengthNat q₂ ≤ (3 * S) * (3 * S) := Nat.mul_le_mul hbp₁ hbq₂
    _ = 9 * S ^ 2 := by ring
  have hm2 : bitLengthNat p₂ * bitLengthNat q₁ ≤ 9 * S ^ 2 := by
    calc bitLengthNat p₂ * bitLengthNat q₁ ≤ (3 * S) * (3 * S) := Nat.mul_le_mul hbp₂ hbq₁
    _ = 9 * S ^ 2 := by ring
  have hp1 : (3 + 1) * (3 * bitLengthNat (p₁ * q₂) + 1) * (3 * bitLengthNat (p₁ * q₂) + 1) ≤
      900 * S ^ 2 + 120 * S + 4 := by
    have h1 : 3 * bitLengthNat (p₁ * q₂) + 1 ≤ 15 * S + 1 := by omega
    calc (3 + 1) * (3 * bitLengthNat (p₁ * q₂) + 1) * (3 * bitLengthNat (p₁ * q₂) + 1)
      ≤ 4 * (15 * S + 1) * (15 * S + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 4 h1) h1
      _ = 900 * S ^ 2 + 120 * S + 4 := by ring
  have hp2 : (3 + 1) * (3 * bitLengthNat (p₂ * q₁) + 1) * (3 * bitLengthNat (p₂ * q₁) + 1) ≤
      900 * S ^ 2 + 120 * S + 4 := by
    have h1 : 3 * bitLengthNat (p₂ * q₁) + 1 ≤ 15 * S + 1 := by omega
    calc (3 + 1) * (3 * bitLengthNat (p₂ * q₁) + 1) * (3 * bitLengthNat (p₂ * q₁) + 1)
      ≤ 4 * (15 * S + 1) * (15 * S + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 4 h1) h1
      _ = 900 * S ^ 2 + 120 * S + 4 := by ring
  have hdiv1 : bitLengthNat ((p₁ * q₂) ^ 3) * bitLengthNat ((p₂ * q₁) ^ 3) ≤ 169 * S ^ 2 := by
    calc bitLengthNat ((p₁ * q₂) ^ 3) * bitLengthNat ((p₂ * q₁) ^ 3)
      ≤ (13 * S) * (13 * S) := Nat.mul_le_mul hbnum3 hbden3
      _ = 169 * S ^ 2 := by ring
  have hdiv2 : bitLengthNat lg * bitLengthNat 4 ≤ 39 * S := by
    calc bitLengthNat lg * bitLengthNat 4 ≤ (13 * S) * 3 := Nat.mul_le_mul hblg hb4
    _ = 39 * S := by ring
  unfold rawDeltaHBNatTracked mulNatTracked powNatTracked divNatTracked log2NatTracked
    subNatTracked retTracked
  dsimp only [CostM.bind_snd, CostM.bind_fst, CostM.withCost]
  change (bitLengthNat p₁ * bitLengthNat q₂ + 1) +
    ((bitLengthNat p₂ * bitLengthNat q₁ + 1) +
      ((3 + 1) * (3 * bitLengthNat (p₁ * q₂) + 1) * (3 * bitLengthNat (p₁ * q₂) + 1) +
        ((3 + 1) * (3 * bitLengthNat (p₂ * q₁) + 1) * (3 * bitLengthNat (p₂ * q₁) + 1) +
          ((bitLengthNat ((p₁ * q₂) ^ 3) * bitLengthNat ((p₂ * q₁) ^ 3) + 1) +
            ((bitLengthNat quot + 1) +
              ((bitLengthNat lg * bitLengthNat 4 + 1) +
                ((bitLengthNat q4 + bitLengthNat 2 + 1) + 1))))))) + 1 + 2 * S ^ 2 ≤ 2400 * S ^ 2
  nlinarith

lemma rawDeltaHANatTracked_snd_le_of_le_pow {M p₁ q₁ p₂ q₂ : ℕ} (hM : 2 ≤ M)
    (hp₁ : p₁ ≤ 2 ^ (2 * M)) (hq₁ : q₁ ≤ 2 ^ (2 * M))
    (hp₂ : p₂ ≤ 2 ^ (2 * M)) (hq₂ : q₂ ≤ 2 ^ (2 * M)) :
    (rawDeltaHANatTracked p₁ q₁ p₂ q₂).2 + 1 + 2 * M ^ 2 ≤ 2400 * M ^ 2 := by
  have hM4_pow : 2 ^ (2 * M) * 2 ^ (2 * M) = 2 ^ (4 * M) := by
    rw [← Nat.pow_add]; congr 1; ring
  have hM12_pow : (2 ^ (4 * M)) ^ 3 = 2 ^ (12 * M) := by
    rw [← Nat.pow_mul]; congr 1; ring
  have hbp₁ : bitLengthNat p₁ ≤ 3 * M := by
    have := bitLengthNat_le_of_le_two_pow_local hp₁; omega
  have hbq₁ : bitLengthNat q₁ ≤ 3 * M := by
    have := bitLengthNat_le_of_le_two_pow_local hq₁; omega
  have hbp₂ : bitLengthNat p₂ ≤ 3 * M := by
    have := bitLengthNat_le_of_le_two_pow_local hp₂; omega
  have hbq₂ : bitLengthNat q₂ ≤ 3 * M := by
    have := bitLengthNat_le_of_le_two_pow_local hq₂; omega
  have hpq₁_le : p₁ * q₂ ≤ 2 ^ (4 * M) := (Nat.mul_le_mul hp₁ hq₂).trans_eq hM4_pow
  have hpq₂_le : p₂ * q₁ ≤ 2 ^ (4 * M) := (Nat.mul_le_mul hp₂ hq₁).trans_eq hM4_pow
  have hbpq₁ : bitLengthNat (p₁ * q₂) ≤ 5 * M := by
    have := bitLengthNat_le_of_le_two_pow_local hpq₁_le; omega
  have hbpq₂ : bitLengthNat (p₂ * q₁) ≤ 5 * M := by
    have := bitLengthNat_le_of_le_two_pow_local hpq₂_le; omega
  have hnum3_le : (p₁ * q₂) ^ 3 ≤ 2 ^ (12 * M) :=
    (Nat.pow_le_pow_left hpq₁_le 3).trans_eq hM12_pow
  have hden3_le : (p₂ * q₁) ^ 3 ≤ 2 ^ (12 * M) :=
    (Nat.pow_le_pow_left hpq₂_le 3).trans_eq hM12_pow
  have hbnum3 : bitLengthNat ((p₁ * q₂) ^ 3) ≤ 13 * M := by
    have := bitLengthNat_le_of_le_two_pow_local hnum3_le; omega
  have hbden3 : bitLengthNat ((p₂ * q₁) ^ 3) ≤ 13 * M := by
    have := bitLengthNat_le_of_le_two_pow_local hden3_le; omega
  set quot := ((p₁ * q₂) ^ 3) / ((p₂ * q₁) ^ 3)
  have hquot_le : quot ≤ 2 ^ (12 * M) := (Nat.div_le_self _ _).trans hnum3_le
  have hbquot : bitLengthNat quot ≤ 13 * M := by
    have := bitLengthNat_le_of_le_two_pow_local hquot_le; omega
  set lg := Nat.log 2 quot
  have hlg_le : lg ≤ 2 ^ (12 * M) := (Nat.log_le_self 2 quot).trans hquot_le
  have hblg : bitLengthNat lg ≤ 13 * M := by
    have := bitLengthNat_le_of_le_two_pow_local hlg_le; omega
  set q4 := lg / 4
  have hq4_le : q4 ≤ 2 ^ (12 * M) := (Nat.div_le_self lg 4).trans hlg_le
  have hbq4 : bitLengthNat q4 ≤ 13 * M := by
    have := bitLengthNat_le_of_le_two_pow_local hq4_le; omega
  have hb4 : bitLengthNat 4 ≤ 3 :=
    bitLengthNat_le_of_le_two_pow_local (by norm_num : 4 ≤ 2 ^ 2)
  have hb11 : bitLengthNat 11 ≤ 5 :=
    bitLengthNat_le_of_le_two_pow_local (by norm_num : 11 ≤ 2 ^ 4)
  have hm1 : bitLengthNat p₁ * bitLengthNat q₂ ≤ 9 * M ^ 2 := by
    calc bitLengthNat p₁ * bitLengthNat q₂ ≤ (3 * M) * (3 * M) := Nat.mul_le_mul hbp₁ hbq₂
    _ = 9 * M ^ 2 := by ring
  have hm2 : bitLengthNat p₂ * bitLengthNat q₁ ≤ 9 * M ^ 2 := by
    calc bitLengthNat p₂ * bitLengthNat q₁ ≤ (3 * M) * (3 * M) := Nat.mul_le_mul hbp₂ hbq₁
    _ = 9 * M ^ 2 := by ring
  have hp1 : (3 + 1) * (3 * bitLengthNat (p₁ * q₂) + 1) * (3 * bitLengthNat (p₁ * q₂) + 1) ≤
      900 * M ^ 2 + 120 * M + 4 := by
    have h1 : 3 * bitLengthNat (p₁ * q₂) + 1 ≤ 15 * M + 1 := by omega
    calc (3 + 1) * (3 * bitLengthNat (p₁ * q₂) + 1) * (3 * bitLengthNat (p₁ * q₂) + 1)
      ≤ 4 * (15 * M + 1) * (15 * M + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 4 h1) h1
      _ = 900 * M ^ 2 + 120 * M + 4 := by ring
  have hp2 : (3 + 1) * (3 * bitLengthNat (p₂ * q₁) + 1) * (3 * bitLengthNat (p₂ * q₁) + 1) ≤
      900 * M ^ 2 + 120 * M + 4 := by
    have h1 : 3 * bitLengthNat (p₂ * q₁) + 1 ≤ 15 * M + 1 := by omega
    calc (3 + 1) * (3 * bitLengthNat (p₂ * q₁) + 1) * (3 * bitLengthNat (p₂ * q₁) + 1)
      ≤ 4 * (15 * M + 1) * (15 * M + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 4 h1) h1
      _ = 900 * M ^ 2 + 120 * M + 4 := by ring
  have hdiv1 : bitLengthNat ((p₁ * q₂) ^ 3) * bitLengthNat ((p₂ * q₁) ^ 3) ≤ 169 * M ^ 2 := by
    calc bitLengthNat ((p₁ * q₂) ^ 3) * bitLengthNat ((p₂ * q₁) ^ 3)
      ≤ (13 * M) * (13 * M) := Nat.mul_le_mul hbnum3 hbden3
      _ = 169 * M ^ 2 := by ring
  have hdiv2 : bitLengthNat lg * bitLengthNat 4 ≤ 39 * M := by
    calc bitLengthNat lg * bitLengthNat 4 ≤ (13 * M) * 3 := Nat.mul_le_mul hblg hb4
    _ = 39 * M := by ring
  unfold rawDeltaHANatTracked mulNatTracked powNatTracked divNatTracked log2NatTracked
    subNatTracked retTracked
  dsimp only [CostM.bind_snd, CostM.bind_fst, CostM.withCost]
  change (bitLengthNat p₁ * bitLengthNat q₂ + 1) +
    ((bitLengthNat p₂ * bitLengthNat q₁ + 1) +
      ((3 + 1) * (3 * bitLengthNat (p₁ * q₂) + 1) * (3 * bitLengthNat (p₁ * q₂) + 1) +
        ((3 + 1) * (3 * bitLengthNat (p₂ * q₁) + 1) * (3 * bitLengthNat (p₂ * q₁) + 1) +
          ((bitLengthNat ((p₁ * q₂) ^ 3) * bitLengthNat ((p₂ * q₁) ^ 3) + 1) +
            ((bitLengthNat quot + 1) +
              ((bitLengthNat lg * bitLengthNat 4 + 1) +
                ((bitLengthNat q4 + bitLengthNat 11 + 1) + 1))))))) + 1 + 2 * M ^ 2 ≤ 2400 * M ^ 2
  nlinarith

lemma rawDeltaHANatTracked_snd_le {D S p₁ q₁ p₂ q₂ : ℕ} (hS : 2 ≤ S)
    (hp₁ : p₁ ≤ S ^ 2) (hq₁ : q₁ ≤ S ^ 2) (hp₂ : p₂ ≤ 2 ^ D * S ^ 2) (hq₂ : q₂ ≤ S ^ 2) :
    (rawDeltaHANatTracked p₁ q₁ p₂ q₂).2 + 1 + 2 * S ^ 2 ≤ deltaHACostFactor D * S ^ 2 := by
  set M := (D + 1) * S
  have hM : 2 ≤ M := by
    change 2 ≤ (D + 1) * S
    nlinarith
  have hS_pow : S ≤ 2 ^ S := Nat.le_of_lt Nat.lt_two_pow_self
  have hS2_pow : S ^ 2 ≤ 2 ^ (2 * S) := by
    calc
      S ^ 2 ≤ (2 ^ S) ^ 2 := Nat.pow_le_pow_left hS_pow 2
      _ = 2 ^ (2 * S) := by rw [← Nat.pow_mul, mul_comm]
  have h2S_le_2M : 2 * S ≤ 2 * M := by
    change 2 * S ≤ 2 * ((D + 1) * S)
    nlinarith
  have hD2S_le_2M : D + 2 * S ≤ 2 * M := by
    change D + 2 * S ≤ 2 * ((D + 1) * S)
    nlinarith
  have hS2_le_2M : S ^ 2 ≤ 2 ^ (2 * M) :=
    hS2_pow.trans (Nat.pow_le_pow_right (by norm_num) h2S_le_2M)
  have hDS2_le_2M : 2 ^ D * S ^ 2 ≤ 2 ^ (2 * M) := by
    calc
      2 ^ D * S ^ 2 ≤ 2 ^ D * 2 ^ (2 * S) := Nat.mul_le_mul_left (2 ^ D) hS2_pow
      _ = 2 ^ (D + 2 * S) := (Nat.pow_add 2 D (2 * S)).symm
      _ ≤ 2 ^ (2 * M) := Nat.pow_le_pow_right (by norm_num) hD2S_le_2M
  have hbound := rawDeltaHANatTracked_snd_le_of_le_pow hM
    (hp₁.trans hS2_le_2M) (hq₁.trans hS2_le_2M)
    (hp₂.trans hDS2_le_2M) (hq₂.trans hS2_le_2M)
  have hSM : S ^ 2 ≤ M ^ 2 := by
    have : 1 * S ≤ (D + 1) * S := Nat.mul_le_mul_right S (by omega)
    simpa [M] using Nat.pow_le_pow_left this 2
  have hbound2 : (rawDeltaHANatTracked p₁ q₁ p₂ q₂).2 + 1 + 2 * S ^ 2 ≤ 2400 * M ^ 2 :=
    (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hSM) _).trans hbound
  refine hbound2.trans_eq ?_
  unfold deltaHACostFactor M
  ring

/-- Exact integer polynomial equivalence for the floor-logarithm threshold
$\lfloor \frac{3}{4} \log_2(\frac{p_1 / q_1}{p_2 / q_2}) - c \rfloor$:
for any positive integers $p_1, q_1, p_2, q_2 > 0$ and any $k \ge 1$,
$$k \le \left\lfloor \frac{3}{4} \log_2\left(\frac{p_1 / q_1}{p_2 / q_2}\right) - c \right\rfloor
\iff 2^{4(k + c)} \cdot (p_2 q_1)^3 \le (p_1 q_2)^3.$$ -/
theorem le_floor_three_quarters_logb_iff_pow_mul_le (c : ℕ) {p₁ q₁ p₂ q₂ k : ℕ}
    (hp₁ : 0 < p₁) (hq₁ : 0 < q₁) (hp₂ : 0 < p₂) (hq₂ : 0 < q₂) :
    (k : ℤ) ≤ Int.floor ((3 / 4 : ℝ) * Real.logb 2 (((p₁ : ℝ) / (q₁ : ℝ)) / ((p₂ : ℝ) / (q₂ : ℝ))) - (c : ℝ)) ↔
      2 ^ (4 * (k + c)) * (p₂ * q₁) ^ 3 ≤ (p₁ * q₂) ^ 3 := by
  have hp₁R : (0 : ℝ) < p₁ := Nat.cast_pos.mpr hp₁
  have hq₁R : (0 : ℝ) < q₁ := Nat.cast_pos.mpr hq₁
  have hp₂R : (0 : ℝ) < p₂ := Nat.cast_pos.mpr hp₂
  have hq₂R : (0 : ℝ) < q₂ := Nat.cast_pos.mpr hq₂
  set u : ℝ := ((p₁ : ℝ) / (q₁ : ℝ)) / ((p₂ : ℝ) / (q₂ : ℝ))
  have hu_pos : 0 < u := by positivity
  have hu_eq : u = ((p₁ : ℝ) * (q₂ : ℝ)) / ((p₂ : ℝ) * (q₁ : ℝ)) := by
    dsimp [u]
    field_simp
  rw [Int.le_floor]
  have hlin :
      ((k : ℤ) : ℝ) ≤ (3 / 4 : ℝ) * Real.logb 2 u - (c : ℝ) ↔
        ((4 * (k + c) : ℕ) : ℝ) ≤ Real.logb 2 u * 3 := by
    push_cast
    constructor <;> intro h <;> linarith
  rw [hlin, ← Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2),
    Real.rpow_natCast, Real.rpow_mul (by norm_num),
    Real.rpow_logb (by norm_num) (by norm_num) hu_pos]
  have hpow3 : u ^ (3 : ℝ) = ((p₁ : ℝ) * (q₂ : ℝ)) ^ 3 / ((p₂ : ℝ) * (q₁ : ℝ)) ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hu_eq, div_pow]
  rw [hpow3, le_div_iff₀ (by positivity)]
  exact_mod_cast Iff.rfl

/-- Exact equality between the computable `ℕ` log-division formula and the real `floor` / `logb 2`
depth increment for any shift $c \in \mathbb{N}$ and positive integers $p_1, q_1, p_2, q_2 > 0$. -/
theorem max_one_natLog_cube_div_eq_floor_logb (c : ℕ) {p₁ q₁ p₂ q₂ : ℕ}
    (hp₁ : 0 < p₁) (hq₁ : 0 < q₁) (hp₂ : 0 < p₂) (hq₂ : 0 < q₂) :
    max 1 (Nat.log 2 (((p₁ * q₂) ^ 3) / ((p₂ * q₁) ^ 3)) / 4 - c) =
      max 1 (Int.toNat (Int.floor ((3 / 4 : ℝ) *
        Real.logb 2 (((p₁ : ℝ) / (q₁ : ℝ)) / ((p₂ : ℝ) / (q₂ : ℝ))) - (c : ℝ)))) := by
  have hiff : ∀ k : ℕ, 1 ≤ k →
      (k ≤ Nat.log 2 (((p₁ * q₂) ^ 3) / ((p₂ * q₁) ^ 3)) / 4 - c ↔
        k ≤ Int.toNat (Int.floor ((3 / 4 : ℝ) *
          Real.logb 2 (((p₁ : ℝ) / (q₁ : ℝ)) / ((p₂ : ℝ) / (q₂ : ℝ))) - (c : ℝ)))) := by
    intro k hk
    have h1 : k ≤ Nat.log 2 (((p₁ * q₂) ^ 3) / ((p₂ * q₁) ^ 3)) / 4 - c ↔
        4 * (k + c) ≤ Nat.log 2 (((p₁ * q₂) ^ 3) / ((p₂ * q₁) ^ 3)) := by omega
    have h2 : 4 * (k + c) ≤ Nat.log 2 (((p₁ * q₂) ^ 3) / ((p₂ * q₁) ^ 3)) ↔
        2 ^ (4 * (k + c)) ≤ ((p₁ * q₂) ^ 3) / ((p₂ * q₁) ^ 3) := by
      by_cases hQ : ((p₁ * q₂) ^ 3) / ((p₂ * q₁) ^ 3) = 0
      · rw [hQ, Nat.log_zero_right]
        have hpow_pos : 1 ≤ 2 ^ (4 * (k + c)) := Nat.one_le_two_pow
        omega
      · exact Nat.le_log_iff_pow_le (by norm_num) hQ
    have hden_pos : 0 < (p₂ * q₁) ^ 3 := by positivity
    have h3 : 2 ^ (4 * (k + c)) ≤ ((p₁ * q₂) ^ 3) / ((p₂ * q₁) ^ 3) ↔
        2 ^ (4 * (k + c)) * (p₂ * q₁) ^ 3 ≤ (p₁ * q₂) ^ 3 :=
      Nat.le_div_iff_mul_le hden_pos
    have h4 : k ≤ Int.toNat (Int.floor ((3 / 4 : ℝ) *
          Real.logb 2 (((p₁ : ℝ) / (q₁ : ℝ)) / ((p₂ : ℝ) / (q₂ : ℝ))) - (c : ℝ))) ↔
        (k : ℤ) ≤ Int.floor ((3 / 4 : ℝ) *
          Real.logb 2 (((p₁ : ℝ) / (q₁ : ℝ)) / ((p₂ : ℝ) / (q₂ : ℝ))) - (c : ℝ)) := by omega
    exact h1.trans (h2.trans (h3.trans
      ((le_floor_three_quarters_logb_iff_pow_mul_le c hp₁ hq₁ hp₂ hq₂).symm.trans h4.symm)))
  set A := Nat.log 2 (((p₁ * q₂) ^ 3) / ((p₂ * q₁) ^ 3)) / 4 - c
  set B := Int.toNat (Int.floor ((3 / 4 : ℝ) *
    Real.logb 2 (((p₁ : ℝ) / (q₁ : ℝ)) / ((p₂ : ℝ) / (q₂ : ℝ))) - (c : ℝ)))
  apply le_antisymm
  · rw [max_le_iff]
    refine ⟨le_max_left 1 B, ?_⟩
    by_cases hA : 1 ≤ A
    · exact le_trans ((hiff A hA).mp le_rfl) (le_max_right 1 B)
    · exact le_trans (by omega : A ≤ 1) (le_max_left 1 B)
  · rw [max_le_iff]
    refine ⟨le_max_left 1 A, ?_⟩
    by_cases hB : 1 ≤ B
    · exact le_trans ((hiff B hB).mpr le_rfl) (le_max_right 1 A)
    · exact le_trans (by omega : B ≤ 1) (le_max_left 1 A)

/-- **Unconditional Exact Rational/Integer Equivalence (`max_one_natLog_cube_div_eq_floor_logb_all`)**:
For **all** $c, p_1, q_1, p_2, q_2 \in \mathbb{N}$ (including boundary cases where any argument is `0`),
the computable `ℕ` log-division formula equals the real `floor` / `logb 2` depth increment. -/
theorem max_one_natLog_cube_div_eq_floor_logb_all (c p₁ q₁ p₂ q₂ : ℕ) :
    max 1 (Nat.log 2 (((p₁ * q₂) ^ 3) / ((p₂ * q₁) ^ 3)) / 4 - c) =
      max 1 (Int.toNat (Int.floor ((3 / 4 : ℝ) *
        Real.logb 2 (((p₁ : ℝ) / (q₁ : ℝ)) / ((p₂ : ℝ) / (q₂ : ℝ))) - (c : ℝ)))) := by
  have hfl : Int.floor (-(c : ℝ)) ≤ 1 := by
    rw [Int.floor_le_iff]
    have hc : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
    push_cast
    linarith
  rcases Nat.eq_zero_or_pos p₁ with rfl | hp₁
  · simp [hfl]
  rcases Nat.eq_zero_or_pos q₁ with rfl | hq₁
  · simp [hfl]
  rcases Nat.eq_zero_or_pos p₂ with rfl | hp₂
  · simp [hfl]
  rcases Nat.eq_zero_or_pos q₂ with rfl | hq₂
  · simp [hfl]
  exact max_one_natLog_cube_div_eq_floor_logb c hp₁ hq₁ hp₂ hq₂

/-- **Exact Rational/Integer Equivalence for `rawDeltaHB` (`paper.tex` Algorithm 5 (`Decompose3D`) Line 18 `\label{line:3d-dhb}`)**:
For all $p_1, q_1, p_2, q_2 \in \mathbb{N}$, the computable integer function
`rawDeltaHBNat p₁ q₁ p₂ q₂` is **identically equal** to `rawDeltaHB (p₁ / q₁) (p₂ / q₂)`. -/
theorem rawDeltaHBNat_eq_rawDeltaHB_all (p₁ q₁ p₂ q₂ : ℕ) :
    rawDeltaHBNat p₁ q₁ p₂ q₂ =
      rawDeltaHB ((p₁ : ℝ) / (q₁ : ℝ)) ((p₂ : ℝ) / (q₂ : ℝ)) := by
  simpa [rawDeltaHBNat, rawDeltaHB] using
    max_one_natLog_cube_div_eq_floor_logb_all 2 p₁ q₁ p₂ q₂

/-- **Exact Rational/Integer Equivalence for `rawDeltaHA` (`paper.tex` Algorithm 5 (`Decompose3D`) Line 22 `\label{line:3d-dhl}`)**:
For all $p_1, q_1, p_2, q_2 \in \mathbb{N}$, the computable integer function
`rawDeltaHANat p₁ q₁ p₂ q₂` is **identically equal** to `rawDeltaHA (p₁ / q₁) (p₂ / q₂)`. -/
theorem rawDeltaHANat_eq_rawDeltaHA_all (p₁ q₁ p₂ q₂ : ℕ) :
    rawDeltaHANat p₁ q₁ p₂ q₂ =
      rawDeltaHA ((p₁ : ℝ) / (q₁ : ℝ)) ((p₂ : ℝ) / (q₂ : ℝ)) := by
  simpa [rawDeltaHANat, rawDeltaHA] using
    max_one_natLog_cube_div_eq_floor_logb_all 11 p₁ q₁ p₂ q₂

/-- Computable cost-tracked clamped $B$-boost step `min remDepth (rawDeltaHBNat p₁ q₁ p₂ q₂)`
that executes `rawDeltaHBNatTracked p₁ q₁ p₂ q₂` via `CostM.bind`. -/
def clampDeltaHBTracked (remDepth p₁ q₁ p₂ q₂ : ℕ) : CostM ℕ :=
  CostM.bind (rawDeltaHBNatTracked p₁ q₁ p₂ q₂) (fun rawNat =>
    retTracked (min remDepth rawNat))

@[simp]
lemma clampDeltaHBTracked_snd (remDepth p₁ q₁ p₂ q₂ : ℕ) :
    (clampDeltaHBTracked remDepth p₁ q₁ p₂ q₂).2 =
      (rawDeltaHBNatTracked p₁ q₁ p₂ q₂).2 + 1 :=
  rfl

lemma clampDeltaHBTracked_snd_le {S remDepth p₁ q₁ p₂ q₂ : ℕ} (hS : 2 ≤ S)
    (hp₁ : p₁ ≤ S ^ 2) (hq₁ : q₁ ≤ S ^ 2) (hp₂ : p₂ ≤ S ^ 2) (hq₂ : q₂ ≤ S ^ 2) :
    (clampDeltaHBTracked remDepth p₁ q₁ p₂ q₂).2 + 2 * S ^ 2 ≤ 2400 * S ^ 2 := by
  rw [clampDeltaHBTracked_snd]
  exact rawDeltaHBNatTracked_snd_le hS hp₁ hq₁ hp₂ hq₂

/-- Computable cost-tracked clamped $A$-boost step `min remDepth (rawDeltaHANat p₁ q₁ p₂ q₂)`
that executes `rawDeltaHANatTracked p₁ q₁ p₂ q₂` via `CostM.bind`. -/
def clampDeltaHATracked (remDepth p₁ q₁ p₂ q₂ : ℕ) : CostM ℕ :=
  CostM.bind (rawDeltaHANatTracked p₁ q₁ p₂ q₂) (fun rawNat =>
    retTracked (min remDepth rawNat))

@[simp]
lemma clampDeltaHATracked_fst (remDepth p₁ q₁ p₂ q₂ : ℕ) :
    (clampDeltaHATracked remDepth p₁ q₁ p₂ q₂).1 =
      min remDepth (rawDeltaHANat p₁ q₁ p₂ q₂) :=
  rfl

@[simp]
lemma clampDeltaHATracked_snd (remDepth p₁ q₁ p₂ q₂ : ℕ) :
    (clampDeltaHATracked remDepth p₁ q₁ p₂ q₂).2 =
      (rawDeltaHANatTracked p₁ q₁ p₂ q₂).2 + 1 :=
  rfl

lemma clampDeltaHATracked_snd_le {D S remDepth p₁ q₁ p₂ q₂ : ℕ} (hS : 2 ≤ S)
    (hp₁ : p₁ ≤ S ^ 2) (hq₁ : q₁ ≤ S ^ 2) (hp₂ : p₂ ≤ 2 ^ D * S ^ 2) (hq₂ : q₂ ≤ S ^ 2) :
    (clampDeltaHATracked remDepth p₁ q₁ p₂ q₂).2 + 2 * S ^ 2 ≤ deltaHACostFactor D * S ^ 2 := by
  rw [clampDeltaHATracked_snd]
  exact rawDeltaHANatTracked_snd_le hS hp₁ hq₁ hp₂ hq₂

lemma rawDeltaHBNat_supportCount_eq {Y_star Y : Finset β} {Z_star Z : Finset γ} {B : β → γ → ℝ}
    (hB_star : IsBinaryMatrix Y_star Z_star B) (hB : IsBinaryMatrix Y Z B) :
    rawDeltaHBNat
      (supportCountRealNat Y_star Z_star B) (Y_star.card * Z_star.card)
      (supportCountRealNat Y Z B) (Y.card * Z.card) =
    rawDeltaHB (matDensity Y_star Z_star B) (matDensity Y Z B) := by
  rw [rawDeltaHBNat_eq_rawDeltaHB_all,
    ← matDensity_eq_supportCountRealNat_div hB_star,
    ← matDensity_eq_supportCountRealNat_div hB]

lemma rawDeltaHANat_supportCount_eq {X' : Finset α} {Y' : Finset β} {A' : α → β → ℝ}
    {α_cap : ℝ} {capNum capDen : ℕ}
    (hA' : IsBinaryMatrix X' Y' A')
    (hcap : α_cap = (capNum : ℝ) / (capDen : ℝ)) :
    rawDeltaHANat
      (supportCountRealNat X' Y' A') (X'.card * Y'.card) capNum capDen =
    rawDeltaHA (matDensity X' Y' A') α_cap := by
  rw [rawDeltaHANat_eq_rawDeltaHA_all,
    ← matDensity_eq_supportCountRealNat_div hA', ← hcap]

/-- When $0 \le \alpha_\ell < 2^{16}\alpha_{\text{cap}}$ ($\alpha_{\text{cap}} > 0$), `rawDeltaHA α_ell α_cap = 1`
(§5.4 of `paper.tex`). -/
lemma rawDeltaHA_eq_one_of_lt {α_ell α_cap : ℝ}
    (hα_ell0 : 0 ≤ α_ell) (hα_pos : 0 < α_cap) (hlt : α_ell < cCap3D * α_cap) :
    rawDeltaHA α_ell α_cap = 1 := by
  unfold rawDeltaHA
  have hlog_lt : Real.logb 2 (α_ell / α_cap) < 16 := by
    rcases eq_or_lt_of_le hα_ell0 with rfl | hgt0
    · simp [Real.logb]
    · have hdiv_lt : α_ell / α_cap < (2 : ℝ) ^ (16 : ℝ) := by
        rw [div_lt_iff₀ hα_pos]
        unfold cCap3D at hlt
        linarith
      have h1 := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) (div_pos hgt0 hα_pos) hdiv_lt
      rwa [Real.logb_rpow (by norm_num) (by norm_num)] at h1
  have hval_lt : (3 / 4 : ℝ) * Real.logb 2 (α_ell / α_cap) - 11 < 1 := by linarith
  have hfloor_le : Int.floor ((3 / 4 : ℝ) * Real.logb 2 (α_ell / α_cap) - 11) ≤ 0 := by
    have : Int.floor ((3 / 4 : ℝ) * Real.logb 2 (α_ell / α_cap) - 11) < 1 :=
      Int.floor_lt.mpr (by exact_mod_cast hval_lt)
    omega
  have htonat : (Int.floor ((3 / 4 : ℝ) * Real.logb 2 (α_ell / α_cap) - 11)).toNat = 0 :=
    Int.toNat_eq_zero.mpr hfloor_le
  rw [htonat]
  rfl

/-- **Normal-Branch Boosted-Slice Depth-Jump Bound (`two_pow_min_rawDeltaHA_mul_rpow_le`, Claim 5.8 `\label{clm:pot-normal}` & Table 6 `\label{tab:potential-budget}`, §5.4 of `paper.tex`)**:
When $\alpha_{\text{cap}} > 0$ and $\alpha_\ell \ge \text{cCap3D} \cdot \alpha_{\text{cap}} = 2^{16}\alpha_{\text{cap}}$,
for any remaining depth budget `rem : ℕ`,
$$2^{\min(\text{rem}, \text{rawDeltaHA }\alpha_\ell \alpha_{\text{cap}})} \alpha_\ell^{1/4}
  \le 2^{-11} \alpha_{\text{cap}}^{-3/4} \alpha_\ell.$$ -/
theorem two_pow_min_rawDeltaHA_mul_rpow_le (rem : ℕ) {α_ell α_cap : ℝ}
    (hα_pos : 0 < α_cap) (hboost : cCap3D * α_cap ≤ α_ell) :
    (2 : ℝ) ^ ((min rem (rawDeltaHA α_ell α_cap) : ℕ) : ℝ) * α_ell ^ ((1 : ℝ) / 4) ≤
      (2 : ℝ) ^ (- (11 : ℝ)) * α_cap ^ (- (3 : ℝ) / 4) * α_ell := by
  have hdiv_ge : (2 : ℝ) ^ (16 : ℝ) ≤ α_ell / α_cap := by
    rw [le_div_iff₀ hα_pos]
    unfold cCap3D at hboost
    linarith
  have hα_ell_pos : 0 < α_ell := by unfold cCap3D at hboost; linarith
  have hdiv_pos : 0 < α_ell / α_cap := div_pos hα_ell_pos hα_pos
  have hlog_ge : 16 ≤ Real.logb 2 (α_ell / α_cap) := by
    have h1 := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) hdiv_ge
    rwa [Real.logb_rpow (by norm_num) (by norm_num)] at h1
  have hval_ge : 1 ≤ (3 / 4 : ℝ) * Real.logb 2 (α_ell / α_cap) - 11 := by linarith
  have hfloor_ge : (1 : ℤ) ≤ Int.floor ((3 / 4 : ℝ) * Real.logb 2 (α_ell / α_cap) - 11) :=
    Int.le_floor.mpr (by exact_mod_cast hval_ge)
  have hraw_eq :
      (rawDeltaHA α_ell α_cap : ℝ) =
        (Int.floor ((3 / 4 : ℝ) * Real.logb 2 (α_ell / α_cap) - 11) : ℝ) := by
    unfold rawDeltaHA
    have htonat : 1 ≤ (Int.floor ((3 / 4 : ℝ) * Real.logb 2 (α_ell / α_cap) - 11)).toNat := by omega
    rw [max_eq_right htonat]
    exact_mod_cast Int.toNat_of_nonneg (by omega)
  have hmin_le :
      ((min rem (rawDeltaHA α_ell α_cap) : ℕ) : ℝ) ≤
        (3 / 4 : ℝ) * Real.logb 2 (α_ell / α_cap) - 11 := by
    have h1 : ((min rem (rawDeltaHA α_ell α_cap) : ℕ) : ℝ) ≤ (rawDeltaHA α_ell α_cap : ℝ) := by
      exact_mod_cast min_le_right rem (rawDeltaHA α_ell α_cap)
    exact h1.trans (hraw_eq.trans_le (Int.floor_le _))
  have hpow_le :
      (2 : ℝ) ^ ((min rem (rawDeltaHA α_ell α_cap) : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (- (11 : ℝ)) * (α_ell / α_cap) ^ ((3 : ℝ) / 4) := by
    calc
      (2 : ℝ) ^ ((min rem (rawDeltaHA α_ell α_cap) : ℕ) : ℝ)
        ≤ (2 : ℝ) ^ ((3 / 4 : ℝ) * Real.logb 2 (α_ell / α_cap) - 11) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hmin_le
      _ = (2 : ℝ) ^ (- (11 : ℝ)) * (2 : ℝ) ^ (Real.logb 2 (α_ell / α_cap) * ((3 : ℝ) / 4)) := by
          rw [sub_eq_add_neg, Real.rpow_add (by norm_num)]
          ring_nf
      _ = (2 : ℝ) ^ (- (11 : ℝ)) * (α_ell / α_cap) ^ ((3 : ℝ) / 4) := by
          rw [Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hdiv_pos]
  have hmul := mul_le_mul_of_nonneg_right hpow_le (Real.rpow_nonneg hα_ell_pos.le ((1 : ℝ) / 4))
  have hrhs_eq :
      (2 : ℝ) ^ (- (11 : ℝ)) * (α_ell / α_cap) ^ ((3 : ℝ) / 4) * α_ell ^ ((1 : ℝ) / 4) =
        (2 : ℝ) ^ (- (11 : ℝ)) * α_cap ^ (- (3 : ℝ) / 4) * α_ell := by
    rw [div_eq_mul_inv, Real.mul_rpow hα_ell_pos.le (inv_pos.mpr hα_pos).le,
      Real.inv_rpow hα_pos.le, ← Real.rpow_neg hα_pos.le]
    have hα_comb : α_ell ^ ((3 : ℝ) / 4) * α_ell ^ ((1 : ℝ) / 4) = α_ell := by
      rw [← Real.rpow_add hα_ell_pos]
      norm_num
    calc
      (2 : ℝ) ^ (- (11 : ℝ)) * (α_ell ^ ((3 : ℝ) / 4) * α_cap ^ (- ((3 : ℝ) / 4))) *
          α_ell ^ ((1 : ℝ) / 4)
        = (2 : ℝ) ^ (- (11 : ℝ)) * α_cap ^ (- (3 : ℝ) / 4) *
            (α_ell ^ ((3 : ℝ) / 4) * α_ell ^ ((1 : ℝ) / 4)) := by ring
      _ = (2 : ℝ) ^ (- (11 : ℝ)) * α_cap ^ (- (3 : ℝ) / 4) * α_ell := by rw [hα_comb]
  rwa [hrhs_eq] at hmul

/-- When $\alpha_\ell \ge 2^s c_{\text{low}}\alpha_{\text{cap}} = 2^{s-32}\alpha_{\text{cap}}$ ($\alpha_{\text{cap}} > 0$),
$s \le 50 \cdot \text{rawDeltaHA }\alpha_\ell \alpha_{\text{cap}}$ (§5.5 of `paper.tex`). -/
lemma scale_le_fifty_mul_rawDeltaHA {s : ℕ} {α_ell α_cap : ℝ}
    (hα_pos : 0 < α_cap) (hscale : (2 : ℝ) ^ s * (cLow3D * α_cap) ≤ α_ell) :
    s ≤ 50 * rawDeltaHA α_ell α_cap := by
  by_cases hs : s ≤ 50
  · have := one_le_rawDeltaHA α_ell α_cap
    omega
  · push_neg at hs
    have hdiv : (2 : ℝ) ^ ((s : ℝ) - 32) ≤ α_ell / α_cap := by
      rw [le_div_iff₀ hα_pos]
      have hpow : (2 : ℝ) ^ ((s : ℝ) - 32) * α_cap = (2 : ℝ) ^ s * (cLow3D * α_cap) := by
        rw [sub_eq_add_neg, Real.rpow_add (by norm_num), Real.rpow_natCast]
        unfold cLow3D
        norm_num
        ring
      exact hpow.trans_le hscale
    have hlog : (s : ℝ) - 32 ≤ Real.logb 2 (α_ell / α_cap) := by
      have h1 := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) hdiv
      rwa [Real.logb_rpow (by norm_num) (by norm_num)] at h1
    have hfloor_gt :
        (3 / 4 : ℝ) * (s : ℝ) - 36 ≤
          (Int.floor ((3 / 4 : ℝ) * Real.logb 2 (α_ell / α_cap) - 11) : ℝ) := by
      have hlt := Int.sub_one_lt_floor ((3 / 4 : ℝ) * Real.logb 2 (α_ell / α_cap) - 11)
      linarith
    have hs_real : (51 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    have hpos_floor : 1 ≤ Int.floor ((3 / 4 : ℝ) * Real.logb 2 (α_ell / α_cap) - 11) := by
      apply Int.le_floor.mpr
      push_cast
      linarith
    have hraw_ge : (3 / 4 : ℝ) * (s : ℝ) - 36 ≤ (rawDeltaHA α_ell α_cap : ℝ) := by
      unfold rawDeltaHA
      have hle :
          (Int.floor ((3 / 4 : ℝ) * Real.logb 2 (α_ell / α_cap) - 11)).toNat ≤
            max 1 (Int.floor ((3 / 4 : ℝ) * Real.logb 2 (α_ell / α_cap) - 11)).toNat :=
        le_max_right _ _
      have hcast :
          (Int.floor ((3 / 4 : ℝ) * Real.logb 2 (α_ell / α_cap) - 11) : ℝ) ≤
            ((max 1 (Int.floor ((3 / 4 : ℝ) * Real.logb 2 (α_ell / α_cap) - 11)).toNat : ℕ) : ℝ) := by
        have htonat :
            ((Int.floor ((3 / 4 : ℝ) * Real.logb 2 (α_ell / α_cap) - 11)).toNat : ℤ) =
              Int.floor ((3 / 4 : ℝ) * Real.logb 2 (α_ell / α_cap) - 11) :=
          Int.toNat_of_nonneg (by omega)
        exact_mod_cast (htonat ▸ Int.ofNat_le.mpr hle)
      exact hfloor_gt.trans hcast
    have h50 : (s : ℝ) ≤ 50 * (rawDeltaHA α_ell α_cap : ℝ) := by linarith
    exact_mod_cast h50

/-- Per-node scaling factor $Q := 2^{60 D} M_{\text{cube}}(\varepsilon, \gamma_{3D}, D) M_{\text{rect3D}}(\varepsilon, D)$
(§5.5 of `paper.tex`). -/
noncomputable def QTree3D (ε : ℝ) (D : ℕ) : ℝ :=
  (2 : ℝ) ^ (60 * D) * M_cube ε gamma3D D * M_rect3D ε D

/-- Per-level exponent multiplier $\Gamma := 50 D + \lceil \log_2((2D + 4) Q) \rceil$
(§5.5 of `paper.tex`). -/
noncomputable def GammaTree3D (ε : ℝ) (D : ℕ) : ℕ :=
  50 * D + Nat.clog 2 (Nat.ceil ((2 * (D : ℝ) + 4) * QTree3D ε D))

/-- Inductive piece-count tree bound $T(h) \le 3 \cdot 2^{D + D^2 + \Gamma(H - h)}$ parameterized
by remaining depth `remDepth = H - h` (`paper.tex` Eq. `\eqref{eq:th-inductive}`, §5.5). -/
noncomputable def T3DTree (ε : ℝ) (D remDepth : ℕ) : ℝ :=
  if remDepth = 0 then
    3 * (2 : ℝ) ^ D
  else
    3 * (2 : ℝ) ^ (D + D ^ 2 + GammaTree3D ε D * remDepth)

lemma T3DTree_zero (ε : ℝ) (D : ℕ) : T3DTree ε D 0 = 3 * (2 : ℝ) ^ D := rfl

lemma T3DTree_succ (ε : ℝ) (D k : ℕ) :
    T3DTree ε D (k + 1) = 3 * (2 : ℝ) ^ (D + D ^ 2 + GammaTree3D ε D * (k + 1)) :=
  if_neg (Nat.succ_ne_zero k)

lemma three_le_T3DTree (ε : ℝ) (D remDepth : ℕ) : 3 ≤ T3DTree ε D remDepth := by
  unfold T3DTree
  split_ifs
  · have : (1 : ℝ) ≤ (2 : ℝ) ^ D := one_le_pow₀ (by norm_num)
    linarith
  · have : (1 : ℝ) ≤ (2 : ℝ) ^ (D + D ^ 2 + GammaTree3D ε D * remDepth) :=
      one_le_pow₀ (by norm_num)
    linarith

lemma T3DTree_mono {ε : ℝ} {D r₁ r₂ : ℕ} (hle : r₁ ≤ r₂) :
    T3DTree ε D r₁ ≤ T3DTree ε D r₂ := by
  unfold T3DTree
  split_ifs with h1 h2
  · exact le_rfl
  · subst h1
    have hexp : D ≤ D + D ^ 2 + GammaTree3D ε D * r₂ := by omega
    have hpow : (2 : ℝ) ^ D ≤ (2 : ℝ) ^ (D + D ^ 2 + GammaTree3D ε D * r₂) :=
      pow_le_pow_right₀ (by norm_num) hexp
    linarith
  · omega
  · have hexp :
        D + D ^ 2 + GammaTree3D ε D * r₁ ≤ D + D ^ 2 + GammaTree3D ε D * r₂ :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ hle) _
    have hpow :
        (2 : ℝ) ^ (D + D ^ 2 + GammaTree3D ε D * r₁) ≤
          (2 : ℝ) ^ (D + D ^ 2 + GammaTree3D ε D * r₂) :=
      pow_le_pow_right₀ (by norm_num) hexp
    linarith

/-- **Jump-Scale Absorption into `T3DTree` (`T3DTree_jump_le`, §5.5 of `paper.tex`)**:
For any jump of scale $s \le D$ and raw depth increment $\Delta_{\text{raw}} \ge 1$ satisfying
$s \le 50 \Delta_{\text{raw}}$, setting $\Delta := \min(k + 1, \Delta_{\text{raw}})$ gives
$$T(k + 1 - \Delta) \le 2^{-s D} \cdot 2^{50 D} \cdot 3 \cdot 2^{D + D^2 + \Gamma k}$$
both when $\Delta = k + 1$ (hitting ceiling $H$, where $T(0) = 3 \cdot 2^D$ and $s D \le D^2$)
and when $\Delta < k + 1$ (where $s D \le 50 D \Delta$ and $\Gamma \ge 50 D$). -/
theorem T3DTree_jump_le (ε : ℝ) (D k : ℕ) {s Δ_raw : ℕ}
    (hs_D : s ≤ D) (hΔ1 : 1 ≤ Δ_raw) (hs_50 : s ≤ 50 * Δ_raw) :
    T3DTree ε D (k + 1 - min (k + 1) Δ_raw) ≤
      (2 : ℝ) ^ (-(s * D : ℤ)) * (2 : ℝ) ^ (50 * D) *
        (3 * (2 : ℝ) ^ (D + D ^ 2 + GammaTree3D ε D * k)) := by
  have hzpow : (2 : ℝ) ^ (s * D) * (2 : ℝ) ^ (-(s * D : ℤ)) = 1 := by
    have hcast : (-(s * D : ℤ)) = -((s * D : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, ← zpow_natCast 2 (s * D), ← zpow_add₀ (by norm_num), add_neg_cancel, zpow_zero]
  by_cases hceil : k + 1 ≤ Δ_raw
  · -- Ceiling case: `k + 1 - min (k + 1) Δ_raw = 0`
    rw [min_eq_left hceil, Nat.sub_self, T3DTree_zero]
    have hexp : D + s * D ≤ 50 * D + (D + D ^ 2 + GammaTree3D ε D * k) := by
      have : s * D ≤ D ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right D hs_D
      omega
    have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexp
    have hmul := mul_le_mul_of_nonneg_right hpow
      (by positivity : (0 : ℝ) ≤ 3 * (2 : ℝ) ^ (-(s * D : ℤ)))
    calc
      3 * (2 : ℝ) ^ D
        = ((2 : ℝ) ^ D * ((2 : ℝ) ^ (s * D) * (2 : ℝ) ^ (-(s * D : ℤ)))) * 3 := by
            rw [hzpow]; ring
      _ = ((2 : ℝ) ^ (D + s * D)) * (3 * (2 : ℝ) ^ (-(s * D : ℤ))) := by
            rw [pow_add (2 : ℝ) D (s * D)]; ring
      _ ≤ ((2 : ℝ) ^ (50 * D + (D + D ^ 2 + GammaTree3D ε D * k))) *
            (3 * (2 : ℝ) ^ (-(s * D : ℤ))) := hmul
      _ = (2 : ℝ) ^ (-(s * D : ℤ)) * (2 : ℝ) ^ (50 * D) *
            (3 * (2 : ℝ) ^ (D + D ^ 2 + GammaTree3D ε D * k)) := by
          rw [pow_add (2 : ℝ) (50 * D)]; ring
  · -- Interior case: `Δ_raw < k + 1`
    push_neg at hceil
    rw [min_eq_right hceil.le]
    have hrem_ne : k + 1 - Δ_raw ≠ 0 := by omega
    unfold T3DTree
    rw [if_neg hrem_ne]
    have hΓ_ge : 50 * D ≤ GammaTree3D ε D := Nat.le_add_right (50 * D) _
    have hexp :
        (D + D ^ 2 + GammaTree3D ε D * (k + 1 - Δ_raw)) + s * D ≤
          50 * D + (D + D ^ 2 + GammaTree3D ε D * k) := by
      have h1 : s * D ≤ 50 * D * Δ_raw := by
        have := Nat.mul_le_mul_right D hs_50
        linarith
      have h2 : 50 * D * (Δ_raw - 1) ≤ GammaTree3D ε D * (Δ_raw - 1) :=
        Nat.mul_le_mul_right (Δ_raw - 1) hΓ_ge
      have h3 : k + 1 - Δ_raw + (Δ_raw - 1) = k := by omega
      have h4 :
          GammaTree3D ε D * (k + 1 - Δ_raw) + GammaTree3D ε D * (Δ_raw - 1) =
            GammaTree3D ε D * k := by
        rw [← Nat.mul_add, h3]
      have h5 : 50 * D * (Δ_raw - 1) + 50 * D = 50 * D * Δ_raw := by
        cases Δ_raw with
        | zero => omega
        | succ m => simp [Nat.mul_add]
      omega
    have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexp
    have hmul := mul_le_mul_of_nonneg_right hpow
      (by positivity : (0 : ℝ) ≤ 3 * (2 : ℝ) ^ (-(s * D : ℤ)))
    calc
      3 * (2 : ℝ) ^ (D + D ^ 2 + GammaTree3D ε D * (k + 1 - Δ_raw))
        = ((2 : ℝ) ^ (D + D ^ 2 + GammaTree3D ε D * (k + 1 - Δ_raw)) *
            ((2 : ℝ) ^ (s * D) * (2 : ℝ) ^ (-(s * D : ℤ)))) * 3 := by
            rw [hzpow]; ring
      _ = ((2 : ℝ) ^ ((D + D ^ 2 + GammaTree3D ε D * (k + 1 - Δ_raw)) + s * D)) *
            (3 * (2 : ℝ) ^ (-(s * D : ℤ))) := by
            rw [pow_add (2 : ℝ) _ (s * D)]; ring
      _ ≤ ((2 : ℝ) ^ (50 * D + (D + D ^ 2 + GammaTree3D ε D * k))) *
            (3 * (2 : ℝ) ^ (-(s * D : ℤ))) := hmul
      _ = (2 : ℝ) ^ (-(s * D : ℤ)) * (2 : ℝ) ^ (50 * D) *
            (3 * (2 : ℝ) ^ (D + D ^ 2 + GammaTree3D ε D * k)) := by
            rw [pow_add (2 : ℝ) (50 * D)]; ring

lemma mul_QTree3D_le_pow_GammaTree3D {ε : ℝ} (D : ℕ)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) :
    (2 * (D : ℝ) + 4) * QTree3D ε D ≤ (2 : ℝ) ^ (GammaTree3D ε D - 50 * D) := by
  have hε1 : ε < 1 := by linarith
  have hQ_pos : 0 < QTree3D ε D := by
    unfold QTree3D M_cube M_rect3D
    have := one_le_goodCubeStepFactor hε0 hε1.le D
    have := one_le_goodRect3DStepFactor hε0 hε1.le D
    positivity
  have hsub :
      GammaTree3D ε D - 50 * D =
        Nat.clog 2 (Nat.ceil ((2 * (D : ℝ) + 4) * QTree3D ε D)) :=
    Nat.add_sub_cancel_left (50 * D) _
  rw [hsub]
  have h1 : (2 * (D : ℝ) + 4) * QTree3D ε D ≤
      (Nat.ceil ((2 * (D : ℝ) + 4) * QTree3D ε D) : ℝ) := Nat.le_ceil _
  have h2 :
      Nat.ceil ((2 * (D : ℝ) + 4) * QTree3D ε D) ≤
        2 ^ Nat.clog 2 (Nat.ceil ((2 * (D : ℝ) + 4) * QTree3D ε D)) :=
    Nat.le_pow_clog (by norm_num) _
  exact h1.trans (by exact_mod_cast h2)

lemma step_T3DTree_close {ε : ℝ} {D k : ℕ}
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) :
    1 + (2 * (D : ℝ) + 3) * QTree3D ε D *
      (3 * (2 : ℝ) ^ (D + D ^ 2 + GammaTree3D ε D * k)) ≤ T3DTree ε D (k + 1) := by
  rw [T3DTree_succ]
  have hε1 : ε < 1 := by linarith
  have hQ_ge_1 : 1 ≤ QTree3D ε D := by
    unfold QTree3D M_cube maxGoodCubeStepsReal M_rect3D
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (60 * D) := one_le_pow₀ (by norm_num)
    have hMc : (1 : ℝ) ≤ 3 * (goodCubeStepFactor ε D) ^ (1 + 16 / (ε * gamma3D)) := by
      have := one_le_goodCubeStepFactor hε0 hε1.le D
      have : (1 : ℝ) ≤ (goodCubeStepFactor ε D) ^ (1 + 16 / (ε * gamma3D)) :=
        Real.one_le_rpow this (by unfold gamma3D; positivity)
      linarith
    have hMr : (1 : ℝ) ≤ 3 * (goodRect3DStepFactor ε D) ^ (rRectFuel ε) := by
      have := one_le_goodRect3DStepFactor hε0 hε1.le D
      have : (1 : ℝ) ≤ (goodRect3DStepFactor ε D) ^ (rRectFuel ε) := one_le_pow₀ this
      linarith
    have h2Mc : (1 : ℝ) ≤
        (2 : ℝ) ^ (60 * D) * (3 * (goodCubeStepFactor ε D) ^ (1 + 16 / (ε * gamma3D))) := by
      nlinarith
    nlinarith
  have hpow_ge_1 : (1 : ℝ) ≤ 3 * (2 : ℝ) ^ (D + D ^ 2 + GammaTree3D ε D * k) := by
    have : (1 : ℝ) ≤ (2 : ℝ) ^ (D + D ^ 2 + GammaTree3D ε D * k) := one_le_pow₀ (by norm_num)
    linarith
  have h1_le : 1 ≤ QTree3D ε D * (3 * (2 : ℝ) ^ (D + D ^ 2 + GammaTree3D ε D * k)) := by
    nlinarith
  have hGamma := mul_QTree3D_le_pow_GammaTree3D D hε0 hε_le
  have hGamma_le :
      (2 * (D : ℝ) + 4) * QTree3D ε D ≤ (2 : ℝ) ^ (GammaTree3D ε D) := by
    have hle : GammaTree3D ε D - 50 * D ≤ GammaTree3D ε D := Nat.sub_le _ _
    exact hGamma.trans (pow_le_pow_right₀ (by norm_num) hle)
  have hmul := mul_le_mul_of_nonneg_right hGamma_le
    (by positivity : (0 : ℝ) ≤ 3 * (2 : ℝ) ^ (D + D ^ 2 + GammaTree3D ε D * k))
  have hsum_le :
      1 + (2 * (D : ℝ) + 3) * QTree3D ε D * (3 * (2 : ℝ) ^ (D + D ^ 2 + GammaTree3D ε D * k)) ≤
        (2 * (D : ℝ) + 4) * QTree3D ε D * (3 * (2 : ℝ) ^ (D + D ^ 2 + GammaTree3D ε D * k)) := by
    linarith [h1_le]
  calc
    1 + (2 * (D : ℝ) + 3) * QTree3D ε D * (3 * (2 : ℝ) ^ (D + D ^ 2 + GammaTree3D ε D * k))
      ≤ (2 * (D : ℝ) + 4) * QTree3D ε D * (3 * (2 : ℝ) ^ (D + D ^ 2 + GammaTree3D ε D * k)) :=
        hsum_le
    _ ≤ (2 : ℝ) ^ (GammaTree3D ε D) * (3 * (2 : ℝ) ^ (D + D ^ 2 + GammaTree3D ε D * k)) := hmul
    _ = 3 * (2 : ℝ) ^ (D + D ^ 2 + GammaTree3D ε D * (k + 1)) := by
        have hexp :
            D + D ^ 2 + GammaTree3D ε D * (k + 1) =
              GammaTree3D ε D + (D + D ^ 2 + GammaTree3D ε D * k) := by ring
        rw [hexp, pow_add]
        ring



end CappedABDecomposition

#verify_standard_axioms BMMGrid.one_sub_rpow_quarter_le
#verify_standard_axioms BMMGrid.bucketedRec_potential_bound
#verify_standard_axioms BMMGrid.table1_budget_cinco_sum_le

end BMMGrid
