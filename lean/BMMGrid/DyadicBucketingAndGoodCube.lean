import BMMGrid.Decomp2D

/-!
# Sections 5.1 & 5.2: Dyadic Column-Degree Bucketing & CappedGoodCube (`BMMGrid/DyadicBucketingAndGoodCube.lean`)

This module formalizes:
1. Lemma 5.1 (`\label{lem:dyadic-bucketing}`, `\eqref{eq:col-bucketing}`,
   `\eqref{eq:bucketing-potential}`, §5.1 of `paper.tex`).
2. Explicit 3D constants (`Table~\ref{tab:constants}`, §3.1 of `paper.tex`).
3. Algorithm 5 (`FindCube`) (`cappedGoodCube`, §5.2) and Lemma 5.3 (`\label{lem:cube-step}`)
   (`\eqref{eq:goodcube-M}`, `\eqref{eq:bprime-mindeg}`, §5.2 & §5.4 of `paper.tex`).
-/

namespace BMMGrid

open scoped BigOperators

/-!
## Basic Matrix Density and Degree Helpers
-/

section MatrixHelpers

variable {α β γ : Type*}

@[simp]
lemma expectSet_zero (S : Finset α) : expectSet S (fun _ => (0 : ℝ)) = 0 := by
  simp [expectSet]

lemma expectSet_congr {S : Finset α} {f g : α → ℝ} (h : ∀ x ∈ S, f x = g x) :
    expectSet S f = expectSet S g := by
  unfold expectSet
  rw [Finset.sum_congr rfl h]

lemma rowDeg_nonneg {Y : Finset β} {A : α → β → ℝ} {x : α}
    (hA : ∀ y ∈ Y, 0 ≤ A x y) : 0 ≤ rowDeg Y A x :=
  expectSet_nonneg hA

lemma colDeg_nonneg {X : Finset α} {A : α → β → ℝ} {y : β}
    (hA : ∀ x ∈ X, 0 ≤ A x y) : 0 ≤ colDeg X A y :=
  expectSet_nonneg hA

lemma matDensity_nonneg {X : Finset α} {Y : Finset β} {A : α → β → ℝ}
    (hA : ∀ x ∈ X, ∀ y ∈ Y, 0 ≤ A x y) : 0 ≤ matDensity X Y A :=
  expectSet_nonneg (fun x hx => rowDeg_nonneg (hA x hx))

lemma le_matDensity_of_colDeg_ge {X : Finset α} {Y : Finset β} (hY : Y.Nonempty)
    {A : α → β → ℝ} {m : ℝ} (hcol : ∀ y ∈ Y, m ≤ colDeg X A y) :
    m ≤ matDensity X Y A := by
  rw [matDensity_eq_colDeg]
  exact le_expectSet_of_le hY hcol

lemma matDensity_mul_card_eq_sum_colDeg (X : Finset α) (Y : Finset β) (A : α → β → ℝ) :
    matDensity X Y A * (Y.card : ℝ) = ∑ y ∈ Y, colDeg X A y := by
  rw [matDensity_eq_colDeg]
  unfold expectSet
  rcases Y.eq_empty_or_nonempty with rfl | hY
  · simp
  · have hcard : (Y.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hY.card_pos.ne'
    exact div_mul_cancel₀ _ hcard

lemma matDensity_mul_card_eq_sum_rowDeg (Y : Finset β) (Z : Finset γ) (B : β → γ → ℝ) :
    matDensity Y Z B * (Y.card : ℝ) = ∑ y ∈ Y, rowDeg Z B y := by
  unfold matDensity expectSet
  rcases Y.eq_empty_or_nonempty with rfl | hY
  · simp
  · have hcard : (Y.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hY.card_pos.ne'
    exact div_mul_cancel₀ _ hcard

end MatrixHelpers

/-!
## Geometric Series Helper (`geom_sum_two_neg_half_le_seven_halves`, §5.1 of `paper.tex`)
-/

section GeometricSeries

/-- $\sqrt{2} < \frac{3}{2}$ since $2 < \frac{9}{4}$ (§5.1 of `paper.tex`). -/
lemma sqrt_two_lt_three_halves : Real.sqrt 2 < 3 / 2 := by
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num

/-- $2^{-1/2} = \frac{\sqrt{2}}{2}$ (§5.1 of `paper.tex`). -/
lemma two_rpow_neg_half_eq : (2 : ℝ) ^ (-(1 : ℝ) / 2) = Real.sqrt 2 / 2 := by
  have h1 : (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) := by ring
  rw [h1, Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  exact inv_eq_of_mul_eq_one_right (by linarith)

/-- $\frac{1}{1 - 2^{-1/2}} = 2 + \sqrt{2}$ (§5.1 of `paper.tex`). -/
lemma one_div_one_sub_two_rpow_neg_half :
    1 / (1 - (2 : ℝ) ^ (-(1 : ℝ) / 2)) = 2 + Real.sqrt 2 := by
  rw [two_rpow_neg_half_eq]
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hlt : Real.sqrt 2 < 3 / 2 := sqrt_two_lt_three_halves
  have hden : 1 - Real.sqrt 2 / 2 ≠ 0 := by linarith
  rw [div_eq_iff hden]
  nlinarith

/-- $2 + \sqrt{2} < \frac{7}{2}$ (§5.1 of `paper.tex`). -/
lemma two_add_sqrt_two_lt_seven_halves : 2 + Real.sqrt 2 < 7 / 2 := by
  linarith [sqrt_two_lt_three_halves]

/-- $2^{-s/2} = (2^{-1/2})^s$ for all $s \in \mathbb{N}$ (§5.1 of `paper.tex`). -/
lemma two_rpow_neg_div_two_eq_pow (s : ℕ) :
    (2 : ℝ) ^ (-(s : ℝ) / 2) = ((2 : ℝ) ^ (-(1 : ℝ) / 2)) ^ s := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1
  ring

/-- Exponent combination $(2^j)^{1/4} (2^{-j})^{3/4} = 2^{-j/2}$ (§5.1 of `paper.tex`). -/
lemma two_rpow_quarter_mul_neg_three_quarters (j : ℕ) :
    ((2 : ℝ) ^ j) ^ ((1 : ℝ) / 4) * ((2 : ℝ) ^ (-(j : ℝ))) ^ ((3 : ℝ) / 4) =
      (2 : ℝ) ^ (-(j : ℝ) / 2) := by
  rw [← Real.rpow_natCast 2 j, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
  congr 1
  ring

/-- Partial geometric sum bound over `Finset.range D`:
$\sum_{j=0}^{D-1} 2^{-j/2} \le \frac{1}{1 - 2^{-1/2}}$ (§5.1 of `paper.tex`). -/
lemma geom_sum_range_two_neg_half_le (D : ℕ) :
    ∑ j ∈ Finset.range D, (2 : ℝ) ^ (-(j : ℝ) / 2) ≤
      1 / (1 - (2 : ℝ) ^ (-(1 : ℝ) / 2)) := by
  simp_rw [two_rpow_neg_div_two_eq_pow]
  set r : ℝ := (2 : ℝ) ^ (-(1 : ℝ) / 2)
  have hr_eq : r = Real.sqrt 2 / 2 := two_rpow_neg_half_eq
  have hr_nonneg : 0 ≤ r := by positivity
  have hr_lt_one : r < 1 := by
    rw [hr_eq]
    linarith [sqrt_two_lt_three_halves]
  have hr_ne : r ≠ 1 := hr_lt_one.ne
  rw [geom_sum_eq hr_ne]
  have hden_pos : 0 < 1 - r := by linarith
  have hr_sub_ne : r - 1 ≠ 0 := sub_ne_zero.mpr hr_ne
  have hrew : (r ^ D - 1) / (r - 1) = (1 - r ^ D) / (1 - r) := by
    rw [div_eq_div_iff hr_sub_ne hden_pos.ne']
    ring
  rw [hrew]
  apply div_le_div_of_nonneg_right _ hden_pos.le
  have hpow_nonneg : 0 ≤ r ^ D := pow_nonneg hr_nonneg D
  linarith

/-- **Geometric Series Helper (§5.1 of `paper.tex`)**:
For any finite set of scales $S \subseteq \mathbb{N}$,
$\sum_{s \in S} 2^{-s/2} \le \frac{1}{1 - 2^{-1/2}} = 2 + \sqrt{2} < \frac{7}{2}$. -/
theorem geom_sum_two_neg_half_le_seven_halves (S : Finset ℕ) :
    (∑ s ∈ S, (2 : ℝ) ^ (-(s : ℝ) / 2) ≤ 1 / (1 - (2 : ℝ) ^ (-(1 : ℝ) / 2))) ∧
    (1 / (1 - (2 : ℝ) ^ (-(1 : ℝ) / 2)) = 2 + Real.sqrt 2) ∧
    (2 + Real.sqrt 2 < 7 / 2) ∧
    (∑ s ∈ S, (2 : ℝ) ^ (-(s : ℝ) / 2) ≤ 7 / 2) := by
  let N := S.sup id + 1
  have hsub : S ⊆ Finset.range N := by
    intro s hs
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hs)
  have hsum_le_range :
      ∑ s ∈ S, (2 : ℝ) ^ (-(s : ℝ) / 2) ≤
        ∑ s ∈ Finset.range N, (2 : ℝ) ^ (-(s : ℝ) / 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have h1 : ∑ s ∈ S, (2 : ℝ) ^ (-(s : ℝ) / 2) ≤ 1 / (1 - (2 : ℝ) ^ (-(1 : ℝ) / 2)) :=
    hsum_le_range.trans (geom_sum_range_two_neg_half_le N)
  have h2 := one_div_one_sub_two_rpow_neg_half
  have h3 := two_add_sqrt_two_lt_seven_halves
  refine ⟨h1, h2, h3, ?_⟩
  linarith

end GeometricSeries

/-!
## Section 5.1: Universal First-Moment Dyadic Column-Degree Bucketing (Lemma 5.1)
-/

section DyadicBucketing

variable {α β γ : Type*}

/-- Upward dyadic column-degree cap $\alpha'_j := 2^j \mu$ for bucket $j$
(Lemma 5.1, §5.1 of `paper.tex`). -/
noncomputable def dyadicColAlpha (μ : ℝ) (j : ℕ) : ℝ :=
  (2 : ℝ) ^ j * μ

/-- Upward dyadic column-degree bucket $Y'_j$ relative to $\mu$ (`\eqref{eq:col-bucketing}`,
§5.1 of `paper.tex`):
- $Y'_0 := \{y \in Y' : \deg_{(A')^T}(y) \le 2\mu\}$,
- $Y'_j := \{y \in Y' : 2^j \mu < \deg_{(A')^T}(y) \le 2^{j+1}\mu\}$ for $j \ge 1$. -/
noncomputable def dyadicColBucket (X' : Finset α) (Y' : Finset β) (A' : α → β → ℝ)
    (μ : ℝ) (j : ℕ) : Finset β :=
  if j = 0 then
    Y'.filter (fun y => colDeg X' A' y ≤ 2 * μ)
  else
    Y'.filter (fun y => (2 : ℝ) ^ j * μ < colDeg X' A' y ∧ colDeg X' A' y ≤ (2 : ℝ) ^ (j + 1) * μ)

/-- List of all $D$ dyadic column-degree buckets $(j, Y'_j)$ for $j \in \{0, \dots, D-1\}$
(Lemma 5.1, §5.1 of `paper.tex`). -/
noncomputable def dyadicColBucketing (X' : Finset α) (Y' : Finset β) (A' : α → β → ℝ)
    (μ : ℝ) (D : ℕ) : List (ℕ × Finset β) :=
  (List.range D).map (fun j => (j, dyadicColBucket X' Y' A' μ j))

/-- Tracked `CostM` evaluation of a single upward dyadic column-degree bucket $Y'_j$. -/
noncomputable def dyadicColBucketTracked (X' : Finset α) (Y' : Finset β) (A' : α → β → ℝ)
    (μ : ℝ) (j : ℕ) : CostM (Finset β) :=
  scanMatrixTracked X' Y' (dyadicColBucket X' Y' A' μ j)

@[simp]
lemma dyadicColBucketTracked_fst (X' : Finset α) (Y' : Finset β) (A' : α → β → ℝ)
    (μ : ℝ) (j : ℕ) :
    (dyadicColBucketTracked X' Y' A' μ j).1 = dyadicColBucket X' Y' A' μ j := rfl

@[simp]
lemma dyadicColBucketTracked_snd (X' : Finset α) (Y' : Finset β) (A' : α → β → ℝ)
    (μ : ℝ) (j : ℕ) :
    (dyadicColBucketTracked X' Y' A' μ j).2 = X'.card * Y'.card + 1 :=
  scanMatrixTracked_snd X' Y' _

/-- Tracked recursive helper for `dyadicColBucketingTracked` over a list of bucket indices. -/
noncomputable def dyadicColBucketingLoopTracked (X' : Finset α) (Y' : Finset β) (A' : α → β → ℝ)
    (μ : ℝ) : List ℕ → CostM (List (ℕ × Finset β))
  | [] => retTracked []
  | j :: js =>
    CostM.bind (dyadicColBucketTracked X' Y' A' μ j) (fun b =>
      CostM.bind (dyadicColBucketingLoopTracked X' Y' A' μ js) (fun rest =>
        retTracked ((j, b) :: rest)))

@[simp]
lemma dyadicColBucketingLoopTracked_fst (X' : Finset α) (Y' : Finset β) (A' : α → β → ℝ)
    (μ : ℝ) (js : List ℕ) :
    (dyadicColBucketingLoopTracked X' Y' A' μ js).1 =
      js.map (fun j => (j, dyadicColBucket X' Y' A' μ j)) := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    unfold dyadicColBucketingLoopTracked
    rw [CostM.bind_fst, CostM.bind_fst, retTracked_fst, dyadicColBucketTracked_fst, ih, List.map_cons]

@[simp]
lemma dyadicColBucketingLoopTracked_snd (X' : Finset α) (Y' : Finset β) (A' : α → β → ℝ)
    (μ : ℝ) (js : List ℕ) :
    (dyadicColBucketingLoopTracked X' Y' A' μ js).2 =
      js.length * (X'.card * Y'.card + 2) + 1 := by
  induction js with
  | nil => simp [dyadicColBucketingLoopTracked]
  | cons j js ih =>
    simp only [dyadicColBucketingLoopTracked, CostM.bind_snd, dyadicColBucketTracked_snd,
      retTracked_snd, List.length_cons, ih]
    ring

/-- Tracked `CostM` evaluation of `dyadicColBucketing` across $j \in \{0, \dots, D-1\}$. -/
noncomputable def dyadicColBucketingTracked (X' : Finset α) (Y' : Finset β) (A' : α → β → ℝ)
    (μ : ℝ) (D : ℕ) : CostM (List (ℕ × Finset β)) :=
  dyadicColBucketingLoopTracked X' Y' A' μ (List.range D)

@[simp]
lemma dyadicColBucketingTracked_fst (X' : Finset α) (Y' : Finset β) (A' : α → β → ℝ)
    (μ : ℝ) (D : ℕ) :
    (dyadicColBucketingTracked X' Y' A' μ D).1 = dyadicColBucketing X' Y' A' μ D := by
  simp [dyadicColBucketingTracked, dyadicColBucketing]

@[simp]
lemma dyadicColBucketingTracked_snd (X' : Finset α) (Y' : Finset β) (A' : α → β → ℝ)
    (μ : ℝ) (D : ℕ) :
    (dyadicColBucketingTracked X' Y' A' μ D).2 = D * (X'.card * Y'.card + 2) + 1 := by
  simp [dyadicColBucketingTracked]

lemma dyadicColBucket_subset (X' : Finset α) (Y' : Finset β) (A' : α → β → ℝ) (μ : ℝ) (j : ℕ) :
    dyadicColBucket X' Y' A' μ j ⊆ Y' := by
  unfold dyadicColBucket
  split_ifs <;> exact Finset.filter_subset _ _

/-- **Column-Degree Bucketing (`\eqref{eq:col-bucketing}`, §5.1 of `paper.tex`)**:
Every $y \in Y'_j = \text{dyadicColBucket } X'\ Y'\ A'\ \mu\ j$ satisfies
$\deg_{(A')^T}(y) \le 2\alpha'_j$ with $\alpha'_j = 2^j \mu$, and for $j \ge 1$,
$\alpha'_j < \deg_{(A')^T}(y) \le 2\mathbb{E}[A'[X', Y'_j]]$. -/
theorem eq_col_bucketing (X' : Finset α) (Y' : Finset β) (A' : α → β → ℝ)
    (μ : ℝ) (j : ℕ) {y : β} (hy : y ∈ dyadicColBucket X' Y' A' μ j) :
    colDeg X' A' y ≤ 2 * dyadicColAlpha μ j ∧
    (1 ≤ j → dyadicColAlpha μ j < colDeg X' A' y ∧
      colDeg X' A' y ≤ 2 * matDensity X' (dyadicColBucket X' Y' A' μ j) A') := by
  unfold dyadicColBucket at hy ⊢
  unfold dyadicColAlpha
  split_ifs at hy ⊢ with hj
  · subst hj
    have hmem := Finset.mem_filter.mp hy
    refine ⟨by simpa using hmem.2, fun h1 => by omega⟩
  · have hmem := Finset.mem_filter.mp hy
    have hpow : (2 : ℝ) ^ (j + 1) * μ = 2 * ((2 : ℝ) ^ j * μ) := by ring
    refine ⟨by linarith [hmem.2.2], fun _ => ⟨hmem.2.1, ?_⟩⟩
    have hne : (Y'.filter (fun y =>
        (2 : ℝ) ^ j * μ < colDeg X' A' y ∧ colDeg X' A' y ≤ (2 : ℝ) ^ (j + 1) * μ)).Nonempty :=
      ⟨y, hy⟩
    have hlow : (2 : ℝ) ^ j * μ ≤ matDensity X'
        (Y'.filter (fun y => (2 : ℝ) ^ j * μ < colDeg X' A' y ∧
          colDeg X' A' y ≤ (2 : ℝ) ^ (j + 1) * μ)) A' :=
      le_matDensity_of_colDeg_ge hne (fun y' hy' => (Finset.mem_filter.mp hy').2.1.le)
    linarith [hmem.2.2]

/-- The buckets `dyadicColBucket X' Y' A' μ j` are pairwise disjoint for $i \ne j$ (when $\mu \ge 0$)
(Lemma 5.1, §5.1 of `paper.tex`). -/
lemma dyadicColBucket_disjoint (X' : Finset α) (Y' : Finset β) (A' : α → β → ℝ)
    {μ : ℝ} (hμ : 0 ≤ μ) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (dyadicColBucket X' Y' A' μ i) (dyadicColBucket X' Y' A' μ j) := by
  rw [Finset.disjoint_left]
  intro y hyi hyj
  wlog hlt : i < j generalizing i j
  · exact this hij.symm hyj hyi (Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) hij.symm)
  have hj_ne : j ≠ 0 := by omega
  have h1 : colDeg X' A' y ≤ (2 : ℝ) ^ (i + 1) * μ := by
    unfold dyadicColBucket at hyi
    split_ifs at hyi with hi
    · subst hi; simpa using (Finset.mem_filter.mp hyi).2
    · exact (Finset.mem_filter.mp hyi).2.2
  have h2 : (2 : ℝ) ^ j * μ < colDeg X' A' y := by
    unfold dyadicColBucket at hyj
    rw [if_neg hj_ne] at hyj
    exact (Finset.mem_filter.mp hyj).2.1
  have hpow : (2 : ℝ) ^ (i + 1) ≤ (2 : ℝ) ^ j :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hmul : (2 : ℝ) ^ (i + 1) * μ ≤ (2 : ℝ) ^ j * μ :=
    mul_le_mul_of_nonneg_right hpow hμ
  linarith

/-- Exact partition of $Y'$ by `dyadicColBucket`: when $\mu > 2^{-D}$ (so $2^D \mu > 1$) and
$D \ge 1$, $\bigsqcup_{j=0}^{D-1} Y'_j = Y'$ (Lemma 5.1, §5.1 of `paper.tex`). -/
lemma dyadicColBucket_biUnion_eq [DecidableEq β] (X' : Finset α) (Y' : Finset β) (A' : α → β → ℝ)
    {μ : ℝ} {D : ℕ} (hD : 1 ≤ D) (_hμ_pos : 0 < μ) (hμD : 1 ≤ (2 : ℝ) ^ D * μ)
    (hcol_le_one : ∀ y ∈ Y', colDeg X' A' y ≤ 1) :
    (Finset.range D).biUnion (dyadicColBucket X' Y' A' μ) = Y' := by
  apply Finset.Subset.antisymm
  · intro y hy
    rcases Finset.mem_biUnion.mp hy with ⟨j, _, hj⟩
    exact dyadicColBucket_subset X' Y' A' μ j hj
  · intro y hy
    rw [Finset.mem_biUnion]
    by_cases h0 : colDeg X' A' y ≤ 2 * μ
    · refine ⟨0, Finset.mem_range.mpr hD, ?_⟩
      simp [dyadicColBucket, hy, h0]
    · push_neg at h0
      have htop : colDeg X' A' y ≤ (2 : ℝ) ^ D * μ := (hcol_le_one y hy).trans hμD
      have hex_gen : ∀ m : ℕ, 1 ≤ m → colDeg X' A' y ≤ (2 : ℝ) ^ m * μ →
          ∃ k : ℕ, k < m ∧ (2 : ℝ) ^ k * μ < colDeg X' A' y ∧
            colDeg X' A' y ≤ (2 : ℝ) ^ (k + 1) * μ := by
        intro m
        induction m with
        | zero => omega
        | succ m ih =>
          intro hm1 htop_m
          by_cases hm0 : m = 0
          · subst hm0
            norm_num at htop_m
            linarith
          · by_cases hle_m : colDeg X' A' y ≤ (2 : ℝ) ^ m * μ
            · obtain ⟨k, hk_lt, hk_gt, hk_le⟩ := ih (by omega) hle_m
              exact ⟨k, by omega, hk_gt, hk_le⟩
            · push_neg at hle_m
              exact ⟨m, by omega, hle_m, htop_m⟩
      obtain ⟨k, hk_lt, hk_gt, hk_le⟩ := hex_gen D hD htop
      have hk_ne : k ≠ 0 := by
        intro hk0
        subst hk0
        norm_num at hk_le
        linarith
      refine ⟨k, Finset.mem_range.mpr hk_lt, ?_⟩
      unfold dyadicColBucket
      rw [if_neg hk_ne]
      exact Finset.mem_filter.mpr ⟨hy, hk_gt, hk_le⟩

/-- **Markov's Inequality on Column-Degree Buckets (§5.1 of `paper.tex`)**:
For every $j \in \mathbb{N}$, $|Y'_j| \le 2^{-j} |Y'|$. -/
lemma dyadicColBucket_card_markov (X' : Finset α) (Y' : Finset β) (A' : α → β → ℝ)
    {μ : ℝ} (hμ : 0 < μ) (hA_nonneg : ∀ x ∈ X', ∀ y ∈ Y', 0 ≤ A' x y)
    (hA_dens : matDensity X' Y' A' ≤ μ) (j : ℕ) :
    ((dyadicColBucket X' Y' A' μ j).card : ℝ) ≤ (2 : ℝ) ^ (-(j : ℝ)) * (Y'.card : ℝ) := by
  by_cases hj : j = 0
  · subst hj
    simp only [Nat.cast_zero, neg_zero, Real.rpow_zero, one_mul, Nat.cast_le]
    exact Finset.card_le_card (dyadicColBucket_subset X' Y' A' μ 0)
  · set Y'_j := dyadicColBucket X' Y' A' μ j
    have hsub : Y'_j ⊆ Y' := dyadicColBucket_subset X' Y' A' μ j
    have hlow : ∀ y ∈ Y'_j, (2 : ℝ) ^ j * μ ≤ colDeg X' A' y := by
      intro y hy
      exact (eq_col_bucketing X' Y' A' μ j hy).2 (Nat.one_le_iff_ne_zero.mpr hj) |>.1.le
    have hsum_low : (Y'_j.card : ℝ) * ((2 : ℝ) ^ j * μ) ≤ ∑ y ∈ Y'_j, colDeg X' A' y := by
      calc
        (Y'_j.card : ℝ) * ((2 : ℝ) ^ j * μ) = ∑ _y ∈ Y'_j, ((2 : ℝ) ^ j * μ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ y ∈ Y'_j, colDeg X' A' y := Finset.sum_le_sum hlow
    have hsum_sub : ∑ y ∈ Y'_j, colDeg X' A' y ≤ ∑ y ∈ Y', colDeg X' A' y :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun y hy _ => colDeg_nonneg (fun x hx => hA_nonneg x hx y hy))
    have hsum_tot : ∑ y ∈ Y', colDeg X' A' y ≤ μ * (Y'.card : ℝ) := by
      rw [← matDensity_mul_card_eq_sum_colDeg]
      exact mul_le_mul_of_nonneg_right hA_dens (Nat.cast_nonneg _)
    have hcomb : (Y'_j.card : ℝ) * ((2 : ℝ) ^ j * μ) ≤ μ * (Y'.card : ℝ) :=
      (hsum_low.trans hsum_sub).trans hsum_tot
    have hcomb2 : (Y'_j.card : ℝ) * (2 : ℝ) ^ j ≤ (Y'.card : ℝ) := by
      apply le_of_mul_le_mul_right _ hμ
      calc
        (Y'_j.card : ℝ) * (2 : ℝ) ^ j * μ = (Y'_j.card : ℝ) * ((2 : ℝ) ^ j * μ) := by ring
        _ ≤ μ * (Y'.card : ℝ) := hcomb
        _ = (Y'.card : ℝ) * μ := by ring
    have hpow_eq : (2 : ℝ) ^ (-(j : ℝ)) = ((2 : ℝ) ^ j)⁻¹ := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
    rw [hpow_eq]
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    calc
      (Y'_j.card : ℝ) = (Y'_j.card : ℝ) * (2 : ℝ) ^ j * ((2 : ℝ) ^ j)⁻¹ := by
        rw [mul_inv_cancel_right₀ h2pos.ne']
      _ ≤ (Y'.card : ℝ) * ((2 : ℝ) ^ j)⁻¹ :=
        mul_le_mul_of_nonneg_right hcomb2 (by positivity)
      _ = ((2 : ℝ) ^ j)⁻¹ * (Y'.card : ℝ) := by ring

/-- **Edge Conservation on $B'$ Across Buckets (§5.1 of `paper.tex`)**:
For every bucket $Y'_j \subseteq Y'$, $|Y'_j| \mathbb{E}[B'[Y'_j, Z']] \le |Y'| \mathbb{E}[B'[Y', Z']]$. -/
lemma dyadicColBucket_edge_conservation_le (X' : Finset α) (Y' : Finset β) (Z' : Finset γ)
    (A' : α → β → ℝ) (B' : β → γ → ℝ) (μ : ℝ) (j : ℕ)
    (hB_nonneg : ∀ y ∈ Y', ∀ z ∈ Z', 0 ≤ B' y z) :
    matDensity (dyadicColBucket X' Y' A' μ j) Z' B' * ((dyadicColBucket X' Y' A' μ j).card : ℝ) ≤
      matDensity Y' Z' B' * (Y'.card : ℝ) := by
  rw [matDensity_mul_card_eq_sum_rowDeg, matDensity_mul_card_eq_sum_rowDeg]
  exact Finset.sum_le_sum_of_subset_of_nonneg (dyadicColBucket_subset X' Y' A' μ j)
    (fun y hy _ => rowDeg_nonneg (hB_nonneg y hy))

/-- **Single-Bucket Potential Bound (§5.1 of `paper.tex`)**:
$(\alpha'_j)^{1/4} (\mathbb{E}[B'[Y'_j, Z']])^{1/4} |Y'_j| \le
2^{-j/2} \mu^{1/4} (\mathbb{E}[B'[Y', Z']])^{1/4} |Y'|$. -/
lemma dyadicColBucket_term_bound (X' : Finset α) (Y' : Finset β) (Z' : Finset γ)
    (A' : α → β → ℝ) (B' : β → γ → ℝ) {μ : ℝ} (hμ : 0 < μ)
    (hA_nonneg : ∀ x ∈ X', ∀ y ∈ Y', 0 ≤ A' x y)
    (hB_nonneg : ∀ y ∈ Y', ∀ z ∈ Z', 0 ≤ B' y z)
    (hA_dens : matDensity X' Y' A' ≤ μ) (j : ℕ) :
    (dyadicColAlpha μ j) ^ ((1 : ℝ) / 4) *
      (matDensity (dyadicColBucket X' Y' A' μ j) Z' B') ^ ((1 : ℝ) / 4) *
      ((dyadicColBucket X' Y' A' μ j).card : ℝ) ≤
      (2 : ℝ) ^ (-(j : ℝ) / 2) * μ ^ ((1 : ℝ) / 4) *
        (matDensity Y' Z' B') ^ ((1 : ℝ) / 4) * (Y'.card : ℝ) := by
  set Y'_j := dyadicColBucket X' Y' A' μ j
  have hsub : Y'_j ⊆ Y' := dyadicColBucket_subset X' Y' A' μ j
  have hβ_nonneg : 0 ≤ matDensity Y' Z' B' := matDensity_nonneg hB_nonneg
  have hβj_nonneg : 0 ≤ matDensity Y'_j Z' B' :=
    matDensity_nonneg (fun y hy z hz => hB_nonneg y (hsub hy) z hz)
  rcases Y'_j.eq_empty_or_nonempty with h_emp | h_ne
  · rw [h_emp, Finset.card_empty, Nat.cast_zero, mul_zero]
    positivity
  · have hcj_pos : (0 : ℝ) < (Y'_j.card : ℝ) := Nat.cast_pos.mpr h_ne.card_pos
    have hc_pos : (0 : ℝ) < (Y'.card : ℝ) :=
      Nat.cast_pos.mpr (h_ne.mono hsub).card_pos
    have hcj_split : (Y'_j.card : ℝ) =
        (Y'_j.card : ℝ) ^ ((3 : ℝ) / 4) * (Y'_j.card : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_add hcj_pos]
      norm_num
    have hc_split : (Y'.card : ℝ) =
        (Y'.card : ℝ) ^ ((3 : ℝ) / 4) * (Y'.card : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_add hc_pos]
      norm_num
    have hedge : (matDensity Y'_j Z' B') ^ ((1 : ℝ) / 4) * (Y'_j.card : ℝ) ^ ((1 : ℝ) / 4) ≤
        (matDensity Y' Z' B') ^ ((1 : ℝ) / 4) * (Y'.card : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [← Real.mul_rpow hβj_nonneg hcj_pos.le, ← Real.mul_rpow hβ_nonneg hc_pos.le]
      exact Real.rpow_le_rpow (mul_nonneg hβj_nonneg hcj_pos.le)
        (dyadicColBucket_edge_conservation_le X' Y' Z' A' B' μ j hB_nonneg) (by norm_num)
    have hmarkov : (Y'_j.card : ℝ) ^ ((3 : ℝ) / 4) ≤
        ((2 : ℝ) ^ (-(j : ℝ))) ^ ((3 : ℝ) / 4) * (Y'.card : ℝ) ^ ((3 : ℝ) / 4) := by
      rw [← Real.mul_rpow (by positivity) hc_pos.le]
      exact Real.rpow_le_rpow hcj_pos.le
        (dyadicColBucket_card_markov X' Y' A' hμ hA_nonneg hA_dens j) (by norm_num)
    have halpha : (dyadicColAlpha μ j) ^ ((1 : ℝ) / 4) =
        ((2 : ℝ) ^ j) ^ ((1 : ℝ) / 4) * μ ^ ((1 : ℝ) / 4) := by
      unfold dyadicColAlpha
      exact Real.mul_rpow (by positivity) hμ.le
    have hstep1 :
        (dyadicColAlpha μ j) ^ ((1 : ℝ) / 4) *
          (matDensity Y'_j Z' B') ^ ((1 : ℝ) / 4) * (Y'_j.card : ℝ) =
        (((2 : ℝ) ^ j) ^ ((1 : ℝ) / 4) * μ ^ ((1 : ℝ) / 4)) *
          (Y'_j.card : ℝ) ^ ((3 : ℝ) / 4) *
          ((matDensity Y'_j Z' B') ^ ((1 : ℝ) / 4) * (Y'_j.card : ℝ) ^ ((1 : ℝ) / 4)) := by
      rw [halpha]
      conv_lhs => rhs; rw [hcj_split]
      ring
    have hf1 : 0 ≤ ((2 : ℝ) ^ j) ^ ((1 : ℝ) / 4) * μ ^ ((1 : ℝ) / 4) :=
      mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hμ.le _)
    have hf2 : 0 ≤ (matDensity Y'_j Z' B') ^ ((1 : ℝ) / 4) * (Y'_j.card : ℝ) ^ ((1 : ℝ) / 4) :=
      mul_nonneg (Real.rpow_nonneg hβj_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hf3 : 0 ≤ ((2 : ℝ) ^ (-(j : ℝ))) ^ ((3 : ℝ) / 4) * (Y'.card : ℝ) ^ ((3 : ℝ) / 4) :=
      mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hstep2 :
        (((2 : ℝ) ^ j) ^ ((1 : ℝ) / 4) * μ ^ ((1 : ℝ) / 4)) *
          (Y'_j.card : ℝ) ^ ((3 : ℝ) / 4) *
          ((matDensity Y'_j Z' B') ^ ((1 : ℝ) / 4) * (Y'_j.card : ℝ) ^ ((1 : ℝ) / 4)) ≤
        (((2 : ℝ) ^ j) ^ ((1 : ℝ) / 4) * μ ^ ((1 : ℝ) / 4)) *
          (((2 : ℝ) ^ (-(j : ℝ))) ^ ((3 : ℝ) / 4) * (Y'.card : ℝ) ^ ((3 : ℝ) / 4)) *
          ((matDensity Y' Z' B') ^ ((1 : ℝ) / 4) * (Y'.card : ℝ) ^ ((1 : ℝ) / 4)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hmarkov hf1) hedge hf2 (mul_nonneg hf1 hf3)
    have hstep3 :
        (((2 : ℝ) ^ j) ^ ((1 : ℝ) / 4) * μ ^ ((1 : ℝ) / 4)) *
          (((2 : ℝ) ^ (-(j : ℝ))) ^ ((3 : ℝ) / 4) * (Y'.card : ℝ) ^ ((3 : ℝ) / 4)) *
          ((matDensity Y' Z' B') ^ ((1 : ℝ) / 4) * (Y'.card : ℝ) ^ ((1 : ℝ) / 4)) =
        (2 : ℝ) ^ (-(j : ℝ) / 2) * μ ^ ((1 : ℝ) / 4) *
          (matDensity Y' Z' B') ^ ((1 : ℝ) / 4) * (Y'.card : ℝ) := by
      calc
        (((2 : ℝ) ^ j) ^ ((1 : ℝ) / 4) * μ ^ ((1 : ℝ) / 4)) *
            (((2 : ℝ) ^ (-(j : ℝ))) ^ ((3 : ℝ) / 4) * (Y'.card : ℝ) ^ ((3 : ℝ) / 4)) *
            ((matDensity Y' Z' B') ^ ((1 : ℝ) / 4) * (Y'.card : ℝ) ^ ((1 : ℝ) / 4)) =
          (((2 : ℝ) ^ j) ^ ((1 : ℝ) / 4) * ((2 : ℝ) ^ (-(j : ℝ))) ^ ((3 : ℝ) / 4)) *
            μ ^ ((1 : ℝ) / 4) * (matDensity Y' Z' B') ^ ((1 : ℝ) / 4) *
            ((Y'.card : ℝ) ^ ((3 : ℝ) / 4) * (Y'.card : ℝ) ^ ((1 : ℝ) / 4)) := by ring
        _ = (2 : ℝ) ^ (-(j : ℝ) / 2) * μ ^ ((1 : ℝ) / 4) *
            (matDensity Y' Z' B') ^ ((1 : ℝ) / 4) * (Y'.card : ℝ) := by
          rw [two_rpow_quarter_mul_neg_three_quarters, ← hc_split]
    linarith

/-- **Lemma 5.1 (`lem_dyadic_col_degree_bucketing`, `\eqref{eq:bucketing-potential}`,
§5.1 of `paper.tex`)**:
Universal first-moment dyadic column-degree bucketing potential bound:
$$\sum_{j=0}^{D-1} (\alpha'_j)^{1/4} (\mathbb{E}[B'[Y'_j, Z']])^{1/4} |Y'_j|
\le (2 + \sqrt{2})\mu^{1/4}(\mathbb{E}[B'])^{1/4}|Y'|
\le \frac{7}{2}\mu^{1/4}(\mathbb{E}[B'])^{1/4}|Y'|.$$ -/
theorem lem_dyadic_col_degree_bucketing (X' : Finset α) (Y' : Finset β) (Z' : Finset γ)
    (A' : α → β → ℝ) (B' : β → γ → ℝ) {μ : ℝ} (hμ : 0 < μ) (D : ℕ)
    (hA_nonneg : ∀ x ∈ X', ∀ y ∈ Y', 0 ≤ A' x y)
    (hB_nonneg : ∀ y ∈ Y', ∀ z ∈ Z', 0 ≤ B' y z)
    (hA_dens : matDensity X' Y' A' ≤ μ) :
    (∑ j ∈ Finset.range D,
        (dyadicColAlpha μ j) ^ ((1 : ℝ) / 4) *
        (matDensity (dyadicColBucket X' Y' A' μ j) Z' B') ^ ((1 : ℝ) / 4) *
        ((dyadicColBucket X' Y' A' μ j).card : ℝ) ≤
      (2 + Real.sqrt 2) * μ ^ ((1 : ℝ) / 4) *
        (matDensity Y' Z' B') ^ ((1 : ℝ) / 4) * (Y'.card : ℝ)) ∧
    ((2 + Real.sqrt 2) * μ ^ ((1 : ℝ) / 4) *
        (matDensity Y' Z' B') ^ ((1 : ℝ) / 4) * (Y'.card : ℝ) ≤
      (7 / 2 : ℝ) * μ ^ ((1 : ℝ) / 4) *
        (matDensity Y' Z' B') ^ ((1 : ℝ) / 4) * (Y'.card : ℝ)) ∧
    (∑ j ∈ Finset.range D,
        (dyadicColAlpha μ j) ^ ((1 : ℝ) / 4) *
        (matDensity (dyadicColBucket X' Y' A' μ j) Z' B') ^ ((1 : ℝ) / 4) *
        ((dyadicColBucket X' Y' A' μ j).card : ℝ) ≤
      (7 / 2 : ℝ) * μ ^ ((1 : ℝ) / 4) *
        (matDensity Y' Z' B') ^ ((1 : ℝ) / 4) * (Y'.card : ℝ)) := by
  have hβ_nonneg : 0 ≤ matDensity Y' Z' B' := matDensity_nonneg hB_nonneg
  have hgeom := geom_sum_two_neg_half_le_seven_halves (Finset.range D)
  have hsum1 :
      ∑ j ∈ Finset.range D,
        (dyadicColAlpha μ j) ^ ((1 : ℝ) / 4) *
        (matDensity (dyadicColBucket X' Y' A' μ j) Z' B') ^ ((1 : ℝ) / 4) *
        ((dyadicColBucket X' Y' A' μ j).card : ℝ) ≤
      (∑ j ∈ Finset.range D, (2 : ℝ) ^ (-(j : ℝ) / 2)) *
        (μ ^ ((1 : ℝ) / 4) * (matDensity Y' Z' B') ^ ((1 : ℝ) / 4) * (Y'.card : ℝ)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun j _ => ?_)
    have hterm := dyadicColBucket_term_bound X' Y' Z' A' B' hμ hA_nonneg hB_nonneg hA_dens j
    linarith
  have h1 :
      ∑ j ∈ Finset.range D,
        (dyadicColAlpha μ j) ^ ((1 : ℝ) / 4) *
        (matDensity (dyadicColBucket X' Y' A' μ j) Z' B') ^ ((1 : ℝ) / 4) *
        ((dyadicColBucket X' Y' A' μ j).card : ℝ) ≤
      (2 + Real.sqrt 2) * μ ^ ((1 : ℝ) / 4) *
        (matDensity Y' Z' B') ^ ((1 : ℝ) / 4) * (Y'.card : ℝ) := by
    have hgeom_eq : ∑ j ∈ Finset.range D, (2 : ℝ) ^ (-(j : ℝ) / 2) ≤ 2 + Real.sqrt 2 := by
      linarith [hgeom.1, hgeom.2.1]
    have hmul :
        (∑ j ∈ Finset.range D, (2 : ℝ) ^ (-(j : ℝ) / 2)) *
          (μ ^ ((1 : ℝ) / 4) * (matDensity Y' Z' B') ^ ((1 : ℝ) / 4) * (Y'.card : ℝ)) ≤
        (2 + Real.sqrt 2) *
          (μ ^ ((1 : ℝ) / 4) * (matDensity Y' Z' B') ^ ((1 : ℝ) / 4) * (Y'.card : ℝ)) :=
      mul_le_mul_of_nonneg_right hgeom_eq (by positivity)
    linarith
  have h2 :
      (2 + Real.sqrt 2) * μ ^ ((1 : ℝ) / 4) *
        (matDensity Y' Z' B') ^ ((1 : ℝ) / 4) * (Y'.card : ℝ) ≤
      (7 / 2 : ℝ) * μ ^ ((1 : ℝ) / 4) *
        (matDensity Y' Z' B') ^ ((1 : ℝ) / 4) * (Y'.card : ℝ) := by
    have hlt : 2 + Real.sqrt 2 ≤ 7 / 2 := hgeom.2.2.1.le
    have hmul :
        (2 + Real.sqrt 2) *
          (μ ^ ((1 : ℝ) / 4) * (matDensity Y' Z' B') ^ ((1 : ℝ) / 4) * (Y'.card : ℝ)) ≤
        (7 / 2 : ℝ) *
          (μ ^ ((1 : ℝ) / 4) * (matDensity Y' Z' B') ^ ((1 : ℝ) / 4) * (Y'.card : ℝ)) :=
      mul_le_mul_of_nonneg_right hlt (by positivity)
    linarith
  exact ⟨h1, h2, h1.trans h2⟩

end DyadicBucketing

/-!
## Section 5.2: Explicit 3D Constants (`Table~\ref{tab:constants}`, §3.1 of `paper.tex`)
-/

section Constants3D

/-- Explicit 3D min-degree peeling parameter $\gamma = 1 / 2048 = 2^{-11}$
(`Table~\ref{tab:constants}`, §3.1 of `paper.tex`). -/
noncomputable def gamma3D : ℝ := 1 / 2048

/-- Explicit 3D lower density threshold factor $c_{\text{low}} = 2^{-32}$
(`Table~\ref{tab:constants}`, §3.1 of `paper.tex`). -/
noncomputable def cLow3D : ℝ := (2 : ℝ) ^ (-32 : ℤ)

/-- Explicit 3D upper density cap factor $C_{\text{cap}} = 2^{16}$
(`Table~\ref{tab:constants}`, §3.1 of `paper.tex`). -/
noncomputable def cCap3D : ℝ := (2 : ℝ) ^ (16 : ℕ)

/-- Depth-indexed potential multiplier $\Lambda_h = 128 \cdot 2^h$
(`Table~\ref{tab:constants}`, §3.1 of `paper.tex`). -/
noncomputable def Lambda3D (h : ℝ) : ℝ := 128 * (2 : ℝ) ^ h

/-- Maximum recursion depth $H = \lceil 3d / 2 \rceil = \lceil 3D / 4 \rceil = (3D + 3) / 4$
(`Table~\ref{tab:constants}`, §3.1 of `paper.tex`). -/
def H3D (D : ℕ) : ℕ := (3 * D + 3) / 4

lemma gamma3D_pos : 0 < gamma3D := by
  unfold gamma3D; norm_num

lemma gamma3D_le_one : gamma3D ≤ 1 := by
  unfold gamma3D; norm_num

lemma Lambda3D_zero : Lambda3D 0 = 128 := by
  unfold Lambda3D; norm_num

lemma Lambda3D_ge_128 {h : ℝ} (hh : 0 ≤ h) : 128 ≤ Lambda3D h := by
  unfold Lambda3D
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ h := Real.one_le_rpow (by norm_num) hh
  linarith

end Constants3D

/-!
## Section 5.2: Algorithm 5 (`FindCube`) (`cappedGoodCube` & `cappedGoodCubeTracked`) and Lemma 5.3 (`\label{lem:cube-step}`)
(`\eqref{eq:goodcube-M}`, `\eqref{eq:bprime-mindeg}`, §5.2 & §5.4 of `paper.tex`)
-/

section CappedGoodCube

variable {α β γ : Type*}

/-- Maximum number of recursive iterations $R_{\text{cube}} \le 1 + \frac{16}{\varepsilon \gamma}$
in `cappedGoodCube` (Lemma 5.3 (`\label{lem:cube-step}`), §5.2 of `paper.tex`). -/
noncomputable def maxGoodCubeStepsReal (ε γ_val : ℝ) : ℝ :=
  1 + 16 / (ε * γ_val)

/-- Per-step shrinkage base factor $\frac{144}{\varepsilon} 2^{4D + \frac{194 D}{\varepsilon}}$
in `cappedGoodCube` (`\eqref{eq:goodcube-M}`, §5.2 of `paper.tex`). -/
noncomputable def goodCubeStepFactor (ε : ℝ) (D : ℕ) : ℝ :=
  (144 / ε) * (2 : ℝ) ^ (4 * (D : ℝ) + 194 * (D : ℝ) / ε)

/-- Overall shrinkage factor $M_{\text{cube}} := 3\left(\frac{144}{\varepsilon} 2^{4D + \frac{194 D}{\varepsilon}}\right)^{1 + \frac{16}{\varepsilon\gamma}}$
(`\eqref{eq:goodcube-M}`, §5.2 of `paper.tex`). -/
noncomputable def M_cube (ε γ_val : ℝ) (D : ℕ) : ℝ :=
  3 * (goodCubeStepFactor ε D) ^ (maxGoodCubeStepsReal ε γ_val)

lemma one_le_goodCubeStepFactor {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (D : ℕ) :
    1 ≤ goodCubeStepFactor ε D := by
  unfold goodCubeStepFactor
  have h1 : 1 ≤ 144 / ε := by
    rw [le_div_iff₀ hε0]
    linarith
  have h2 : (0 : ℝ) ≤ 4 * (D : ℝ) + 194 * (D : ℝ) / ε := by positivity
  have h3 : 1 ≤ (2 : ℝ) ^ (4 * (D : ℝ) + 194 * (D : ℝ) / ε) :=
    Real.one_le_rpow (by norm_num) h2
  nlinarith

lemma three_le_M_cube {ε γ_val : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hγ0 : 0 < γ_val) (D : ℕ) :
    3 ≤ M_cube ε γ_val D := by
  unfold M_cube maxGoodCubeStepsReal
  have hbase : 1 ≤ goodCubeStepFactor ε D := one_le_goodCubeStepFactor hε0 hε1 D
  have hexp : 0 ≤ 1 + 16 / (ε * γ_val) := by positivity
  have hpow : 1 ≤ (goodCubeStepFactor ε D) ^ (1 + 16 / (ε * γ_val)) :=
    Real.one_le_rpow hbase hexp
  linarith

lemma M_cube_pos {ε γ_val : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hγ0 : 0 < γ_val) (D : ℕ) :
    0 < M_cube ε γ_val D := by
  linarith [three_le_M_cube hε0 hε1 hγ0 D]

/-- **Algorithm 5 Line 10 (`\label{line:cube-rec2}`) Density Boost (§5.2 of `paper.tex`)**:
When $\mathbb{E}[B_\ell] \ge (1 + \varepsilon\gamma)\mathbb{E}[B[Y_\ell, Z]]$ and
$\mathbb{E}[B[Y_\ell, Z]] \ge (1 - \frac{\varepsilon\gamma}{2})\mathbb{E}[B]$ with $0 \le \varepsilon\gamma \le 1/2$,
we have $\mathbb{E}[B_\ell] \ge (1 + \frac{\varepsilon\gamma}{4})\mathbb{E}[B]$. -/
theorem goodCube_step4c_density_boost {β_curr β_slice β_ell ε γ_val : ℝ}
    (hβ_nonneg : 0 ≤ β_curr) (hεγ_nonneg : 0 ≤ ε * γ_val) (hεγ_le : ε * γ_val ≤ 1 / 2)
    (hslice : (1 - ε * γ_val / 2) * β_curr ≤ β_slice)
    (hell : (1 + ε * γ_val) * β_slice ≤ β_ell) :
    (1 + ε * γ_val / 4) * β_curr ≤ β_ell := by
  have hquad : 1 + ε * γ_val / 4 ≤ (1 + ε * γ_val) * (1 - ε * γ_val / 2) := by nlinarith
  have hprod : (1 + ε * γ_val / 4) * β_curr ≤ (1 + ε * γ_val) * ((1 - ε * γ_val / 2) * β_curr) := by
    nlinarith
  have hstep : (1 + ε * γ_val) * ((1 - ε * γ_val / 2) * β_curr) ≤ (1 + ε * γ_val) * β_slice :=
    mul_le_mul_of_nonneg_left hslice (by linarith)
  exact (hprod.trans hstep).trans hell

/-- **Algorithm 5 Lines 7 & 10 Normal Bounds (§5.2 of `paper.tex`)**:
When Lines 7 and 10 do not recurse ($\mathbb{E}[B[Y_\ell, Z]] < 2\beta^*$ and
$\mathbb{E}[B_\ell] < (1 + \varepsilon\gamma)\mathbb{E}[B[Y_\ell, Z]]$ with $0 \le \varepsilon\gamma \le 1/2$
and $0 < \beta^*$), we have $\mathbb{E}[B_\ell] < 3\beta^*$ and
$(1 - \varepsilon)\mathbb{E}[B_\ell] < 2\beta^*$ (for $\gamma \le 1$). -/
theorem goodCube_step4c_normal_bounds {β_star β_slice β_ell ε γ_val : ℝ}
    (hβ_pos : 0 < β_star) (hslice_nonneg : 0 ≤ β_slice) (hβ_ell_nonneg : 0 ≤ β_ell)
    (hε_pos : 0 ≤ ε) (hγ_nonneg : 0 ≤ γ_val) (hγ_le : γ_val ≤ 1) (hεγ_le : ε * γ_val ≤ 1 / 2)
    (hstep4a : β_slice < 2 * β_star)
    (hstep4c : β_ell < (1 + ε * γ_val) * β_slice) :
    β_ell < 3 * β_star ∧ (1 - ε) * β_ell < 2 * β_star := by
  refine ⟨by nlinarith, ?_⟩
  have h1 : (1 - ε) * (1 + ε * γ_val) ≤ 1 := by
    have hsub : 0 ≤ ε * (1 - γ_val) := mul_nonneg hε_pos (by linarith)
    have hsq : 0 ≤ ε * (ε * γ_val) := mul_nonneg hε_pos (mul_nonneg hε_pos hγ_nonneg)
    nlinarith
  by_cases h1ε : 0 ≤ 1 - ε
  · have h2 : (1 - ε) * β_ell ≤ (1 - ε) * ((1 + ε * γ_val) * β_slice) :=
      mul_le_mul_of_nonneg_left hstep4c.le h1ε
    have h3 : (1 - ε) * ((1 + ε * γ_val) * β_slice) ≤ 1 * β_slice := by
      calc
        (1 - ε) * ((1 + ε * γ_val) * β_slice) = ((1 - ε) * (1 + ε * γ_val)) * β_slice := by ring
        _ ≤ 1 * β_slice := mul_le_mul_of_nonneg_right h1 hslice_nonneg
    linarith
  · push_neg at h1ε
    have hneg : (1 - ε) * β_ell ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h1ε.le hβ_ell_nonneg
    linarith

/-- **Algorithm 5 Line 11 (`\label{line:cube-sift}`) Progress Bound (§5.2 of `paper.tex`)**:
For $\varepsilon \in (0, 1/160]$ and $\gamma = 1/2048$,
$(1 + \frac{\varepsilon}{2})(1 - \frac{\varepsilon\gamma}{2}) \ge 1 + \frac{\varepsilon\gamma}{4}$. -/
theorem goodCube_step4d_factor_ge {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    1 + ε * gamma3D / 4 ≤ (1 + ε / 2) * (1 - ε * gamma3D / 2) := by
  unfold gamma3D
  nlinarith

/-- **Normal-Mode Scale Bound $S_B \le 4$ (§5.2 & §5.4 of `paper.tex`)**:
If $2^{S_B} \beta_{\text{init}} \le \beta^* < 17 \beta_{\text{init}}$ with $\beta_{\text{init}} > 0$,
then $S_B \le 4$. -/
theorem goodCube_normal_scale_le_four {S_B : ℕ} {β_init β_star : ℝ}
    (hβ_pos : 0 < β_init)
    (hlow : (2 : ℝ) ^ S_B * β_init ≤ β_star)
    (hhigh : β_star < 17 * β_init) :
    S_B ≤ 4 := by
  by_contra! hgt
  have h5 : 5 ≤ S_B := hgt
  have hpow : (32 : ℝ) ≤ (2 : ℝ) ^ S_B := by
    calc
      (32 : ℝ) = (2 : ℝ) ^ (5 : ℕ) := by norm_num
      _ ≤ (2 : ℝ) ^ S_B := pow_le_pow_right₀ (by norm_num) h5
  nlinarith

/-- **Global Scale Bound $S_B \le D$ (§5.2 of `paper.tex`)**:
If $\beta^* \le 1$, $\beta^* \ge 2^{S_B}\beta_{\text{init}}$, and $\beta_{\text{init}} > 2^{-D}$,
then $S_B \le D$. -/
theorem goodCube_scale_le_D {S_B D : ℕ} {β_init β_star : ℝ}
    (hβ_init : (2 : ℝ) ^ (-(D : ℤ)) < β_init)
    (hlow : (2 : ℝ) ^ S_B * β_init ≤ β_star)
    (hhigh : β_star ≤ 1) :
    S_B ≤ D := by
  by_contra! hgt
  have hpowD : (2 : ℝ) ^ D < (2 : ℝ) ^ S_B :=
    pow_lt_pow_right₀ (by norm_num) hgt
  have hprod : 1 < (2 : ℝ) ^ D * β_init := by
    have h1 : (2 : ℝ) ^ D * (2 : ℝ) ^ (-(D : ℤ)) = 1 := by
      rw [← zpow_natCast 2 D, ← zpow_add₀ (by norm_num), add_neg_cancel, zpow_zero]
    nlinarith [(by positivity : (0 : ℝ) < (2 : ℝ) ^ D)]
  have hβ_pos : 0 < β_init := lt_trans (by positivity) hβ_init
  nlinarith

/-- **Cube Shrinkage Bound (`\eqref{eq:goodcube-M}`, §5.2 of `paper.tex`)**:
Multiplying $R \le 1 + \frac{16}{\varepsilon\gamma}$ recursive steps of per-step shrinkage
$\ge (\text{goodCubeStepFactor } \varepsilon\ D)^{-1} 2^{-s_t D}$ and the final Step 1 factor $\frac{1}{3}$
yields $|Y^*||Z^*| \ge M_{\text{cube}}^{-1} 2^{-S_B D}|Y||Z|$. -/
theorem eq_goodcube_M {ε γ_val : ℝ} {D R S_B : ℕ} {area_init area_star : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (harea_nonneg : 0 ≤ area_init)
    (hR : (R : ℝ) ≤ maxGoodCubeStepsReal ε γ_val)
    (hstep : (3⁻¹ : ℝ) * ((goodCubeStepFactor ε D) ^ R)⁻¹ *
      (2 : ℝ) ^ (-(S_B * D : ℤ)) * area_init ≤ area_star) :
    (M_cube ε γ_val D)⁻¹ * (2 : ℝ) ^ (-(S_B * D : ℤ)) * area_init ≤ area_star := by
  refine le_trans ?_ hstep
  have hbase : 1 ≤ goodCubeStepFactor ε D := one_le_goodCubeStepFactor hε0 hε1 D
  have hpow : (goodCubeStepFactor ε D) ^ R ≤
      (goodCubeStepFactor ε D) ^ (maxGoodCubeStepsReal ε γ_val) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hbase hR
  have hM : 3 * (goodCubeStepFactor ε D) ^ R ≤ M_cube ε γ_val D := by
    unfold M_cube
    linarith
  have hinv : (M_cube ε γ_val D)⁻¹ ≤ (3⁻¹ : ℝ) * ((goodCubeStepFactor ε D) ^ R)⁻¹ := by
    rw [← mul_inv]
    exact inv_anti₀ (by positivity) hM
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hinv (by positivity)) harea_nonneg

/-- A single 2D/3D slice $(X_\ell, Y_\ell, Z_\ell, A_\ell, \text{tag}_\ell, S_\ell)$ in the normal-mode
return of `cappedGoodCube` (Algorithm 5 (`FindCube`), §5.2 of `paper.tex`). -/
structure GoodCubeSlice (α β γ : Type*) where
  X_ell : Finset α
  Y_ell : Finset β
  Z_ell : Finset γ
  A_ell : α → β → ℝ
  tag   : RectTag
  S_ell : ℕ

/-- Output structure of `cappedGoodCube` (Algorithm 5 (`FindCube`) & Lemma 5.3 (`\label{lem:cube-step}`), §5.2 of `paper.tex`). -/
structure GoodCubeResult (α β γ : Type*) where
  mode       : CubeMode
  X_star     : Finset α
  Y_star     : Finset β
  Z_star     : Finset γ
  Y_prime    : Finset β
  A_prime    : α → β → ℝ
  B_prime    : β → γ → ℝ
  alpha_star : ℝ
  S_B        : ℕ
  steps      : ℕ
  slices     : List (GoodCubeSlice α β γ)

open Classical in
/-- Bernoulli iteration budget $R_{\text{rect}} := 84 \lceil 1 / \varepsilon \rceil$ for 3D
`cappedGoodRect3D` (§4.3 of `paper.tex`):
since $(1 + \varepsilon / 2)^{\lceil 1 / \varepsilon \rceil} \ge 3 / 2$ and
$(3 / 2)^{84} = ((3 / 2)^7)^{12} > 16^{12} = 2^{48}$, this budget guarantees reaching the
$2^{48}$ density window ratio $C_{\text{cap}} / c_{\text{low}} = 2^{16} / 2^{-32} = 2^{48}$. -/
noncomputable def rRectFuel (ε : ℝ) : ℕ :=
  84 * Nat.ceil (1 / ε)

/-- Bernoulli iteration budget $R_{\text{cube}} := 13 \lceil 1 / (\varepsilon \gamma) \rceil$ for
Algorithm 5 (`FindCube`) (`cappedGoodCube`, §5.2 of `paper.tex`):
since $(1 + \varepsilon\gamma / 4)^{\lceil 1 / (\varepsilon\gamma) \rceil} \ge 5 / 4$ and
$(5 / 4)^{13} > 16 = C_{B, \text{cap}}$, this budget guarantees reaching the $16\times$ $B$-boost
threshold. -/
noncomputable def rCubeFuel (ε γ_val : ℝ) : ℕ :=
  13 * Nat.ceil (1 / (ε * γ_val))

lemma pow_rCubeFuel_ge {ε γ_val : ℝ} (hε0 : 0 < ε) (hγ0 : 0 < γ_val) :
    (16 : ℝ) ≤ (1 + ε * γ_val / 4) ^ (rCubeFuel ε γ_val) := by
  unfold rCubeFuel
  let k := Nat.ceil (1 / (ε * γ_val))
  have hpos : 0 < ε * γ_val := mul_pos hε0 hγ0
  have hk_ge : 1 / (ε * γ_val) ≤ (k : ℝ) := Nat.le_ceil (1 / (ε * γ_val))
  have hk_mul : 1 ≤ (k : ℝ) * (ε * γ_val) := (div_le_iff₀ hpos).mp hk_ge
  have hk_quarter : (1 / 4 : ℝ) ≤ (k : ℝ) * (ε * γ_val / 4) := by linarith
  have hbern : 1 + (k : ℝ) * (ε * γ_val / 4) ≤ (1 + ε * γ_val / 4) ^ k :=
    one_add_mul_le_pow (by linarith) k
  have h54 : (5 / 4 : ℝ) ≤ (1 + ε * γ_val / 4) ^ k := by linarith
  have h13 : ((5 / 4 : ℝ) ^ (13 : ℕ)) ≤ ((1 + ε * γ_val / 4) ^ k) ^ (13 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) h54 13
  have hnorm : (16 : ℝ) ≤ (5 / 4 : ℝ) ^ (13 : ℕ) := by norm_num
  rw [mul_comm 13 k, pow_mul]
  exact hnorm.trans h13

lemma rCubeFuel_le_maxGoodCubeStepsReal {ε γ_val : ℝ}
    (hε0 : 0 < ε) (hε160 : ε ≤ 1 / 160) (hγ0 : 0 < γ_val) (hγ1 : γ_val ≤ 1) :
    (rCubeFuel ε γ_val : ℝ) ≤ maxGoodCubeStepsReal ε γ_val := by
  unfold rCubeFuel maxGoodCubeStepsReal
  have hpos : 0 < ε * γ_val := mul_pos hε0 hγ0
  have h1 : 0 ≤ 1 / (ε * γ_val) := div_nonneg zero_le_one hpos.le
  have hceil : (Nat.ceil (1 / (ε * γ_val)) : ℝ) ≤ 1 / (ε * γ_val) + 1 :=
    (Nat.ceil_lt_add_one h1).le
  have hprod_le : ε * γ_val ≤ 1 / 160 := by nlinarith
  have h160 : (13 : ℝ) ≤ 3 / (ε * γ_val) := by
    rw [le_div_iff₀ hpos]
    linarith
  push_cast
  calc
    13 * (Nat.ceil (1 / (ε * γ_val)) : ℝ) ≤ 13 * (1 / (ε * γ_val) + 1) := by nlinarith
    _ = 13 / (ε * γ_val) + 13 := by ring
    _ ≤ 13 / (ε * γ_val) + 3 / (ε * γ_val) := by linarith
    _ = 16 / (ε * γ_val) := by ring
    _ ≤ 1 + 16 / (ε * γ_val) := by linarith

/-- Per-step area shrinkage factor $\frac{48}{\varepsilon} 2^{4D}$ in 3D `cappedGoodRect3D`. -/
noncomputable def goodRect3DStepFactor (ε : ℝ) (D : ℕ) : ℝ :=
  (48 / ε) * (2 : ℝ) ^ (4 * D)

/-- Overall area shrinkage factor $M_{\text{rect3D}} := 3 (\text{goodRect3DStepFactor } \varepsilon\ D)^{R_{\text{rect}}}$
for 3D `cappedGoodRect3D`. -/
noncomputable def M_rect3D (ε : ℝ) (D : ℕ) : ℝ :=
  3 * (goodRect3DStepFactor ε D) ^ (rRectFuel ε)

lemma one_le_goodRect3DStepFactor {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (D : ℕ) :
    1 ≤ goodRect3DStepFactor ε D := by
  unfold goodRect3DStepFactor
  have h1 : 1 ≤ 48 / ε := by
    rw [le_div_iff₀ hε0]
    linarith
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (4 * D) := one_le_pow₀ (by norm_num)
  nlinarith

lemma three_le_M_rect3D {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (D : ℕ) :
    3 ≤ M_rect3D ε D := by
  unfold M_rect3D
  have h1 : 1 ≤ (goodRect3DStepFactor ε D) ^ (rRectFuel ε) :=
    one_le_pow₀ (one_le_goodRect3DStepFactor hε0 hε1 D)
  linarith

lemma M_rect3D_pos {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (D : ℕ) :
    0 < M_rect3D ε D := by
  linarith [three_le_M_rect3D hε0 hε1 D]

/-- Output record of 3D `cappedGoodRect3D` (Algorithm 4 (`FindRect` / `Decompose2D`), §4.3 of `paper.tex`). -/
structure GoodRect3DResult (α β : Type*) where
  X_ell : Finset α
  Y_ell : Finset β
  A_ell : α → β → ℝ
  tag   : RectTag
  S_ell : ℕ
  steps : ℕ

open Classical in
/-- **Algorithm 4 (`FindRect` / `Decompose2D`) Inner Loop (`cappedGoodRect3DLoop`, §4.3 of `paper.tex`)**:
Iteratively runs `minDegree X Y A ε (1/2)` and `dyadicSiftConcrete X' Y A ε D S` while
$\mathbb{E}[A] < \alpha_{\text{cap}}$, accumulating dyadic scale $S_\ell$ and step count
bottom-up. -/
noncomputable def cappedGoodRect3DLoop [DecidableEq α] [DecidableEq β] :
    ℕ → Finset α → Finset β → (α → β → ℝ) → (ε : ℝ) → ℕ → ℝ →
    TwoStageSamplerOracle β ε → GoodRect3DResult α β
  | 0, X, Y, A, _ε, _D, _α_cap, _S =>
    { X_ell := X, Y_ell := Y, A_ell := submatZeroExt X Y A,
      tag := RectTag.aBoosted, S_ell := 0, steps := 0 }
  | fuel + 1, X, Y, A, ε, D, α_cap, S =>
    if matDensity X Y A ≥ α_cap then
      { X_ell := X, Y_ell := Y, A_ell := submatZeroExt X Y A,
        tag := RectTag.aBoosted, S_ell := 0, steps := 0 }
    else
      let minRes := minDegree X Y A ε (1 / 2)
      let X' := minRes.1
      let tag₁ := minRes.2
      if tag₁ = 2 ∨ matDensity X' Y A ≥ (1 + ε / 2) * matDensity X Y A then
        let sub := cappedGoodRect3DLoop fuel X' Y A ε D α_cap S
        { sub with steps := sub.steps + 1 }
      else if matDensity X' Y A ≥ α_cap then
        { X_ell := X', Y_ell := Y, A_ell := submatZeroExt X' Y A,
          tag := RectTag.aBoosted, S_ell := 0, steps := 0 }
      else
        let siftRes := dyadicSiftConcrete X' Y A ε D S
        if siftRes.1 = "subrect" then
          let X'' := siftRes.2.1
          let Y'' := siftRes.2.2.1
          let s := siftRes.2.2.2
          let sub := cappedGoodRect3DLoop fuel X'' Y'' A ε D α_cap S
          { sub with S_ell := sub.S_ell + s, steps := sub.steps + 1 }
        else
          { X_ell := X', Y_ell := Y, A_ell := submatZeroExt X' Y A,
            tag := RectTag.regular, S_ell := 0, steps := 0 }

open Classical in
/-- Cost-tracked inner loop `cappedGoodRect3DLoopTracked` in `CostM`. -/
noncomputable def cappedGoodRect3DLoopTracked [DecidableEq α] [DecidableEq β] :
    ℕ → Finset α → Finset β → (α → β → ℝ) → (ε : ℝ) → ℕ → ℝ →
    TwoStageSamplerOracle β ε → CostM (GoodRect3DResult α β)
  | 0, X, Y, A, _ε, _D, _α_cap, _S =>
    scanMatrixTracked X Y
      { X_ell := X, Y_ell := Y, A_ell := submatZeroExt X Y A,
        tag := RectTag.aBoosted, S_ell := 0, steps := 0 }
  | fuel + 1, X, Y, A, ε, D, α_cap, S =>
    if matDensity X Y A ≥ α_cap then
      scanMatrixTracked X Y
        { X_ell := X, Y_ell := Y, A_ell := submatZeroExt X Y A,
          tag := RectTag.aBoosted, S_ell := 0, steps := 0 }
    else
      CostM.bind (minDegreeTracked X Y A ε (1 / 2)) (fun minRes =>
        let X' := minRes.1
        let tag₁ := minRes.2
        if tag₁ = 2 ∨ matDensity X' Y A ≥ (1 + ε / 2) * matDensity X Y A then
          CostM.bind (cappedGoodRect3DLoopTracked fuel X' Y A ε D α_cap S) (fun sub =>
            scanMatrixTracked X Y { sub with steps := sub.steps + 1 })
        else if matDensity X' Y A ≥ α_cap then
          scanMatrixTracked X Y
            { X_ell := X', Y_ell := Y, A_ell := submatZeroExt X' Y A,
              tag := RectTag.aBoosted, S_ell := 0, steps := 0 }
        else
          CostM.bind (dyadicSiftConcreteTracked X' Y A ε D S) (fun siftRes =>
            if siftRes.1 = "subrect" then
              let X'' := siftRes.2.1
              let Y'' := siftRes.2.2.1
              let s := siftRes.2.2.2
              CostM.bind (cappedGoodRect3DLoopTracked fuel X'' Y'' A ε D α_cap S) (fun sub =>
                scanMatrixTracked X Y
                  { sub with S_ell := sub.S_ell + s, steps := sub.steps + 1 })
            else
              scanMatrixTracked X Y
                { X_ell := X', Y_ell := Y, A_ell := submatZeroExt X' Y A,
                  tag := RectTag.regular, S_ell := 0, steps := 0 }))

@[simp]
lemma cappedGoodRect3DLoopTracked_fst [DecidableEq α] [DecidableEq β]
    (fuel : ℕ) (X : Finset α) (Y : Finset β) (A : α → β → ℝ) (ε : ℝ) (D : ℕ) (α_cap : ℝ)
    (S : TwoStageSamplerOracle β ε) :
    (cappedGoodRect3DLoopTracked fuel X Y A ε D α_cap S).1 =
      cappedGoodRect3DLoop fuel X Y A ε D α_cap S := by
  classical
  induction fuel generalizing X Y with
  | zero => rfl
  | succ k ih =>
    unfold cappedGoodRect3DLoopTracked cappedGoodRect3DLoop
    dsimp only
    by_cases hcap : matDensity X Y A ≥ α_cap
    · rw [if_pos hcap, if_pos hcap]; rfl
    · rw [if_neg hcap, if_neg hcap]
      simp only [CostM.bind_fst, minDegreeTracked_fst]
      by_cases htag1 : (minDegree X Y A ε (1 / 2)).2 = 2 ∨
          matDensity (minDegree X Y A ε (1 / 2)).1 Y A ≥ (1 + ε / 2) * matDensity X Y A
      · rw [if_pos htag1, if_pos htag1]
        simp only [CostM.bind_fst, scanMatrixTracked_fst, ih]
      · rw [if_neg htag1, if_neg htag1]
        by_cases hcap2 : matDensity (minDegree X Y A ε (1 / 2)).1 Y A ≥ α_cap
        · rw [if_pos hcap2, if_pos hcap2]; rfl
        · rw [if_neg hcap2, if_neg hcap2]
          simp only [CostM.bind_fst, dyadicSiftConcreteTracked_fst]
          by_cases hsift :
              (dyadicSiftConcrete (minDegree X Y A ε (1 / 2)).1 Y A ε D S).1 = "subrect"
          · rw [if_pos hsift, if_pos hsift]
            simp only [CostM.bind_fst, scanMatrixTracked_fst, ih]
          · rw [if_neg hsift, if_neg hsift]; rfl

/-- **Algorithm 4 (`FindRect` / `Decompose2D`) (`cappedGoodRect3D`, §4.3 of `paper.tex`)**:
3D-windowed `CappedGoodRect` with iteration fuel `rRectFuel ε`. -/
noncomputable def cappedGoodRect3D [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (A : α → β → ℝ) (ε : ℝ) (D : ℕ) (α_cap : ℝ)
    (S : TwoStageSamplerOracle β ε) :
    GoodRect3DResult α β :=
  cappedGoodRect3DLoop (rRectFuel ε) X Y A ε D α_cap S

/-- Tracked `CostM` implementation of `cappedGoodRect3D`. -/
noncomputable def cappedGoodRect3DTracked [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (A : α → β → ℝ) (ε : ℝ) (D : ℕ) (α_cap : ℝ)
    (S : TwoStageSamplerOracle β ε) :
    CostM (GoodRect3DResult α β) :=
  cappedGoodRect3DLoopTracked (rRectFuel ε) X Y A ε D α_cap S

@[simp]
lemma cappedGoodRect3DTracked_fst [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (A : α → β → ℝ) (ε : ℝ) (D : ℕ) (α_cap : ℝ)
    (S : TwoStageSamplerOracle β ε) :
    (cappedGoodRect3DTracked X Y A ε D α_cap S).1 = cappedGoodRect3D X Y A ε D α_cap S :=
  cappedGoodRect3DLoopTracked_fst (rRectFuel ε) X Y A ε D α_cap S

lemma cappedGoodRect3DLoopTracked_snd_le [DecidableEq α] [DecidableEq β]
    (fuel : ℕ) (X : Finset α) (Y : Finset β) (A : α → β → ℝ) (ε : ℝ) (D : ℕ) (α_cap : ℝ)
    (S : TwoStageSamplerOracle β ε) :
    (cappedGoodRect3DLoopTracked fuel X Y A ε D α_cap S).2 ≤
      (fuel + 1) * ((X.card + Y.card + 2) ^ 2 *
        (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 6)) := by
  classical
  induction fuel generalizing X Y with
  | zero =>
    unfold cappedGoodRect3DLoopTracked
    simp only [scanMatrixTracked_snd, zero_add, one_mul]
    have : X.card * Y.card + 1 ≤ (X.card + Y.card + 2) ^ 2 * 1 := by nlinarith
    nlinarith
  | succ k ih =>
    unfold cappedGoodRect3DLoopTracked
    dsimp only
    have hbase : X.card * Y.card + 1 ≤ (X.card + Y.card + 2) ^ 2 := by nlinarith
    have hmin_cost := minDegreeTracked_snd_le X Y A ε (1 / 2)
    have hmin_sub : (minDegree X Y A ε (1 / 2)).1 ⊆ X := minDegree_fst_subset X Y A ε (1 / 2)
    have hX'_card : (minDegree X Y A ε (1 / 2)).1.card ≤ X.card := Finset.card_le_card hmin_sub
    split_ifs with hcap
    · simp only [scanMatrixTracked_snd]
      have h1 : (X.card + Y.card + 2) ^ 2 ≤
          (X.card + Y.card + 2) ^ 2 * (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 6) :=
        Nat.le_mul_of_pos_right _ (by omega)
      have h2 : (X.card + Y.card + 2) ^ 2 * (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 6) ≤
          (k + 1 + 1) * ((X.card + Y.card + 2) ^ 2 *
            (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 6)) :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
    · rw [CostM.bind_snd, minDegreeTracked_fst]
      split_ifs with htag1 hcap2
      · rw [CostM.bind_snd, scanMatrixTracked_snd]
        have hrec := ih (minDegree X Y A ε (1 / 2)).1 Y
        have hquad : ((minDegree X Y A ε (1 / 2)).1.card + Y.card + 2) ^ 2 ≤
            (X.card + Y.card + 2) ^ 2 := by nlinarith
        have hrec' : (cappedGoodRect3DLoopTracked k (minDegree X Y A ε (1 / 2)).1 Y A ε D α_cap S).2 ≤
            (k + 1) * ((X.card + Y.card + 2) ^ 2 *
              (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 6)) :=
          hrec.trans (Nat.mul_le_mul_left (k + 1) (Nat.mul_le_mul_right _ hquad))
        have hstep : (minDegreeTracked X Y A ε (1 / 2)).2 + (X.card * Y.card + 1) ≤
            (X.card + Y.card + 2) ^ 2 * (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 6) := by
          have : (minDegreeTracked X Y A ε (1 / 2)).2 + (X.card * Y.card + 1) ≤
              (X.card + Y.card + 2) ^ 2 * 6 := by nlinarith
          exact this.trans (Nat.mul_le_mul_left _ (by omega))
        linarith
      · rw [scanMatrixTracked_snd]
        have hstep : (minDegreeTracked X Y A ε (1 / 2)).2 + (X.card * Y.card + 1) ≤
            (X.card + Y.card + 2) ^ 2 * (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 6) := by
          have : (minDegreeTracked X Y A ε (1 / 2)).2 + (X.card * Y.card + 1) ≤
              (X.card + Y.card + 2) ^ 2 * 6 := by nlinarith
          exact this.trans (Nat.mul_le_mul_left _ (by omega))
        have h2 : (X.card + Y.card + 2) ^ 2 * (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 6) ≤
            (k + 1 + 1) * ((X.card + Y.card + 2) ^ 2 *
              (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 6)) :=
          Nat.le_mul_of_pos_left _ (by omega)
        omega
      · rw [CostM.bind_snd, dyadicSiftConcreteTracked_fst]
        have hsift_cost := dyadicSiftConcreteTracked_snd_le
          (minDegree X Y A ε (1 / 2)).1 Y A ε D S
        have hsift_sub := dyadicSift_subset
          (minDegree X Y A ε (1 / 2)).1 Y A ε D
          (concreteApproxGridNormV S (minDegree X Y A ε (1 / 2)).1 Y A D)
        have hprod_le :
            ((minDegree X Y A ε (1 / 2)).1.card + Y.card + 2) ^ 2 ≤
              (X.card + Y.card + 2) ^ 2 := by nlinarith
        have hsift_le :
            (dyadicSiftConcreteTracked (minDegree X Y A ε (1 / 2)).1 Y A ε D S).2 ≤
              (X.card + Y.card + 2) ^ 2 *
                (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * (D + 1)) :=
          hsift_cost.trans (Nat.mul_le_mul_right _ hprod_le)
        have hstep :
            (minDegreeTracked X Y A ε (1 / 2)).2 +
              (dyadicSiftConcreteTracked (minDegree X Y A ε (1 / 2)).1 Y A ε D S).2 +
              (X.card * Y.card + 1) ≤
              (X.card + Y.card + 2) ^ 2 *
                (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 6) := by
          have hmin6 : (minDegreeTracked X Y A ε (1 / 2)).2 + (X.card * Y.card + 1) ≤
              (X.card + Y.card + 2) ^ 2 * 4 := by nlinarith
          linarith
        split_ifs with hsift
        · rw [CostM.bind_snd, scanMatrixTracked_snd]
          have hX''_card : (dyadicSiftConcrete (minDegree X Y A ε (1 / 2)).1 Y A ε D S).2.1.card ≤
              X.card := (Finset.card_le_card hsift_sub.1).trans hX'_card
          have hY''_card : (dyadicSiftConcrete (minDegree X Y A ε (1 / 2)).1 Y A ε D S).2.2.1.card ≤
              Y.card := Finset.card_le_card hsift_sub.2
          have hquad :
              ((dyadicSiftConcrete (minDegree X Y A ε (1 / 2)).1 Y A ε D S).2.1.card +
                (dyadicSiftConcrete (minDegree X Y A ε (1 / 2)).1 Y A ε D S).2.2.1.card + 2) ^ 2 ≤
                (X.card + Y.card + 2) ^ 2 := by nlinarith
          have hrec := ih
            (dyadicSiftConcrete (minDegree X Y A ε (1 / 2)).1 Y A ε D S).2.1
            (dyadicSiftConcrete (minDegree X Y A ε (1 / 2)).1 Y A ε D S).2.2.1
          have hrec' :
              (cappedGoodRect3DLoopTracked k
                (dyadicSiftConcrete (minDegree X Y A ε (1 / 2)).1 Y A ε D S).2.1
                (dyadicSiftConcrete (minDegree X Y A ε (1 / 2)).1 Y A ε D S).2.2.1
                A ε D α_cap S).2 ≤
              (k + 1) * ((X.card + Y.card + 2) ^ 2 *
                (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 6)) :=
            hrec.trans (Nat.mul_le_mul_left (k + 1) (Nat.mul_le_mul_right _ hquad))
          linarith
        · rw [scanMatrixTracked_snd]
          have h2 : (X.card + Y.card + 2) ^ 2 *
              (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 6) ≤
              (k + 1 + 1) * ((X.card + Y.card + 2) ^ 2 *
                (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 6)) :=
            Nat.le_mul_of_pos_left _ (by omega)
          omega

lemma cappedGoodRect3DTracked_snd_le [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (A : α → β → ℝ) (ε : ℝ) (D : ℕ) (α_cap : ℝ)
    (S : TwoStageSamplerOracle β ε) :
    (cappedGoodRect3DTracked X Y A ε D α_cap S).2 ≤
      (rRectFuel ε + 1) * ((X.card + Y.card + 2) ^ 2 *
        (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 6)) :=
  cappedGoodRect3DLoopTracked_snd_le (rRectFuel ε) X Y A ε D α_cap S

lemma cappedGoodRect3DLoop_subset [DecidableEq α] [DecidableEq β]
    (fuel : ℕ) (X : Finset α) (Y : Finset β) (A : α → β → ℝ) (ε : ℝ) (D : ℕ) (α_cap : ℝ)
    (S : TwoStageSamplerOracle β ε) :
    let res := cappedGoodRect3DLoop fuel X Y A ε D α_cap S
    res.X_ell ⊆ X ∧ res.Y_ell ⊆ Y ∧ res.A_ell = submatZeroExt res.X_ell res.Y_ell A := by
  classical
  induction fuel generalizing X Y with
  | zero =>
    unfold cappedGoodRect3DLoop
    exact ⟨Finset.Subset.rfl, Finset.Subset.rfl, rfl⟩
  | succ k ih =>
    unfold cappedGoodRect3DLoop
    dsimp only
    have hmin_sub : (minDegree X Y A ε (1 / 2)).1 ⊆ X := minDegree_fst_subset X Y A ε (1 / 2)
    by_cases hcap : matDensity X Y A ≥ α_cap
    · rw [if_pos hcap]
      exact ⟨Finset.Subset.rfl, Finset.Subset.rfl, rfl⟩
    · rw [if_neg hcap]
      by_cases htag1 : (minDegree X Y A ε (1 / 2)).2 = 2 ∨
          matDensity (minDegree X Y A ε (1 / 2)).1 Y A ≥ (1 + ε / 2) * matDensity X Y A
      · rw [if_pos htag1]
        rcases ih (minDegree X Y A ε (1 / 2)).1 Y with ⟨hX, hY, hA⟩
        exact ⟨hX.trans hmin_sub, hY, hA⟩
      · rw [if_neg htag1]
        by_cases hcap2 : matDensity (minDegree X Y A ε (1 / 2)).1 Y A ≥ α_cap
        · rw [if_pos hcap2]
          exact ⟨hmin_sub, Finset.Subset.rfl, rfl⟩
        · rw [if_neg hcap2]
          by_cases hsift :
              (dyadicSiftConcrete (minDegree X Y A ε (1 / 2)).1 Y A ε D S).1 = "subrect"
          · rw [if_pos hsift]
            have hsift_sub := dyadicSift_subset (minDegree X Y A ε (1 / 2)).1 Y A ε D
              (concreteApproxGridNormV S (minDegree X Y A ε (1 / 2)).1 Y A D)
            rcases ih (dyadicSiftConcrete (minDegree X Y A ε (1 / 2)).1 Y A ε D S).2.1
              (dyadicSiftConcrete (minDegree X Y A ε (1 / 2)).1 Y A ε D S).2.2.1 with ⟨hX, hY, hA⟩
            exact ⟨hX.trans (hsift_sub.1.trans hmin_sub), hY.trans hsift_sub.2, hA⟩
          · rw [if_neg hsift]
            exact ⟨hmin_sub, Finset.Subset.rfl, rfl⟩

lemma isBinaryMatrix_subset {X X' : Finset α} {Y Y' : Finset β} {A : α → β → ℝ}
    (hX : X' ⊆ X) (hY : Y' ⊆ Y) (hA : IsBinaryMatrix X Y A) :
    IsBinaryMatrix X' Y' A :=
  fun x hx y hy => hA x (hX hx) y (hY hy)

lemma isBinaryMatrix_zeroOutSubrect [DecidableEq α] [DecidableEq β]
    {X : Finset α} {Y : Finset β} {A : α → β → ℝ} (X' : Finset α) (Y' : Finset β)
    (hA : IsBinaryMatrix X Y A) :
    IsBinaryMatrix X Y (zeroOutSubrect A X' Y') := by
  intro x hx y hy
  unfold zeroOutSubrect
  split_ifs
  · exact Or.inl rfl
  · exact hA x hx y hy

lemma isBinaryMatrix_matTranspose {Y : Finset β} {Z : Finset γ} {B : β → γ → ℝ}
    (hB : IsBinaryMatrix Y Z B) :
    IsBinaryMatrix Z Y (matTranspose B) :=
  fun z hz y hy => hB y hy z hz

lemma isBinaryMatrix_nonneg {X : Finset α} {Y : Finset β} {A : α → β → ℝ}
    (hA : IsBinaryMatrix X Y A) :
    ∀ x ∈ X, ∀ y ∈ Y, 0 ≤ A x y := by
  intro x hx y hy
  rcases hA x hx y hy with h0 | h1 <;> linarith

lemma isBinaryMatrix_le_one {X : Finset α} {Y : Finset β} {A : α → β → ℝ}
    (hA : IsBinaryMatrix X Y A) :
    ∀ x ∈ X, ∀ y ∈ Y, A x y ≤ 1 := by
  intro x hx y hy
  rcases hA x hx y hy with h0 | h1 <;> linarith

lemma matDensity_le_one_of_isBinaryMatrix {X : Finset α} {Y : Finset β} {A : α → β → ℝ}
    (hA : IsBinaryMatrix X Y A) :
    matDensity X Y A ≤ 1 := by
  rcases X.eq_empty_or_nonempty with rfl | hX
  · simp [matDensity]
  · rcases Y.eq_empty_or_nonempty with rfl | hY
    · simp [matDensity, rowDeg]
    · exact expectSet_le_of_le hX (fun x hx =>
        expectSet_le_of_le hY (isBinaryMatrix_le_one hA x hx))

lemma rowDeg_submatZeroExt_eq [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (A : α → β → ℝ) {x : α} (hx : x ∈ X) :
    rowDeg Y (submatZeroExt X Y A) x = rowDeg Y A x := by
  unfold rowDeg
  refine expectSet_congr (fun y hy => ?_)
  simp [submatZeroExt, hx, hy]

lemma matDensity_submatZeroExt_eq [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (A : α → β → ℝ) :
    matDensity X Y (submatZeroExt X Y A) = matDensity X Y A := by
  unfold matDensity
  exact expectSet_congr (fun x hx => rowDeg_submatZeroExt_eq X Y A hx)

lemma isGridRegular_of_eq_on {U : Finset α} {V : Finset β} {M₁ M₂ : α → β → ℝ}
    (heq : ∀ u ∈ U, ∀ v ∈ V, M₁ u v = M₂ u v)
    {ε : ℝ} {k ℓ : ℕ} (hreg : IsGridRegular U V M₁ ε k ℓ) :
    IsGridRegular U V M₂ ε k ℓ := by
  have hgn : gridNormPow U V M₁ k ℓ = gridNormPow U V M₂ k ℓ := by
    unfold gridNormPow
    refine expectSet_congr (fun us hus => ?_)
    have hus_mem : ∀ i : Fin k, us i ∈ U := Fintype.mem_piFinset.mp hus
    congr 1
    refine expectSet_congr (fun v hv => ?_)
    exact Finset.prod_congr rfl (fun i _ => heq (us i) (hus_mem i) v hv)
  have hdens : matDensity U V M₁ = matDensity U V M₂ := by
    unfold matDensity rowDeg
    refine expectSet_congr (fun u hu => expectSet_congr (fun v hv => heq u hu v hv))
  unfold IsGridRegular gridNorm at hreg ⊢
  rw [← hgn, ← hdens]
  exact hreg

lemma isEpsMinDegree_of_eq_on {U : Finset α} {V : Finset β} {M₁ M₂ : α → β → ℝ}
    (heq : ∀ u ∈ U, ∀ v ∈ V, M₁ u v = M₂ u v)
    {ε : ℝ} (hmin : IsEpsMinDegree U V M₁ ε) :
    IsEpsMinDegree U V M₂ ε := by
  have hrow : ∀ u ∈ U, rowDeg V M₁ u = rowDeg V M₂ u :=
    fun u hu => expectSet_congr (fun v hv => heq u hu v hv)
  have hdens : matDensity U V M₁ = matDensity U V M₂ :=
    expectSet_congr (fun u hu => hrow u hu)
  intro u hu
  rw [← hrow u hu, ← hdens]
  exact hmin u hu

/-- Full inductive specification of `cappedGoodRect3DLoop`. -/
theorem cappedGoodRect3DLoop_spec [DecidableEq α] [DecidableEq β]
    (fuel : ℕ) {X : Finset α} {Y : Finset β} {A : α → β → ℝ} {ε : ℝ} {D : ℕ} {α_cap : ℝ}
    (S : TwoStageSamplerOracle β ε)
    (hX : X.Nonempty) (hY : Y.Nonempty) (hA : IsBinaryMatrix X Y A)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hD : 2 ≤ D)
    (hA_gt : (2 : ℝ) ^ (-(D : ℤ)) < matDensity X Y A)
    (hfuel_cap : α_cap ≤ (1 + ε / 2) ^ fuel * matDensity X Y A) :
    let res := cappedGoodRect3DLoop fuel X Y A ε D α_cap S
    res.X_ell ⊆ X ∧ res.Y_ell ⊆ Y ∧ res.X_ell.Nonempty ∧ res.Y_ell.Nonempty ∧
    res.A_ell = submatZeroExt res.X_ell res.Y_ell A ∧
    res.steps ≤ fuel ∧
    (2 : ℝ) ^ res.S_ell * (1 + ε / 2) ^ res.steps * matDensity X Y A ≤
      matDensity res.X_ell res.Y_ell A ∧
    (((2 : ℝ) ^ (2 * D))⁻¹) ^ res.steps * (Y.card : ℝ) ≤ (res.Y_ell.card : ℝ) ∧
    (3⁻¹ : ℝ) * ((goodRect3DStepFactor ε D) ^ res.steps)⁻¹ *
      (2 : ℝ) ^ (-(res.S_ell * D : ℤ)) * ((X.card : ℝ) * (Y.card : ℝ)) ≤
        (res.X_ell.card : ℝ) * (res.Y_ell.card : ℝ) ∧
    (res.tag = RectTag.regular ∨ res.tag = RectTag.aBoosted) ∧
    (res.tag = RectTag.aBoosted → α_cap ≤ matDensity res.X_ell res.Y_ell A) ∧
    (res.tag = RectTag.regular →
      matDensity res.X_ell res.Y_ell A < α_cap ∧
      IsGridRegular res.X_ell res.Y_ell res.A_ell ε 2 D ∧
      IsEpsMinDegree res.X_ell res.Y_ell res.A_ell ε) := by
  classical
  induction fuel generalizing X Y with
  | zero =>
    unfold cappedGoodRect3DLoop
    dsimp only
    rw [pow_zero, one_mul] at hfuel_cap
    refine ⟨Finset.Subset.rfl, Finset.Subset.rfl, hX, hY, rfl, le_rfl, ?_, ?_, ?_,
      Or.inr rfl, fun _ => hfuel_cap, fun h => by cases h⟩
    · simp only [pow_zero, one_mul]; exact le_rfl
    · simp only [pow_zero, one_mul]; exact le_rfl
    · simp only [pow_zero, inv_one, Nat.cast_zero, zero_mul, neg_zero, zpow_zero, mul_one]
      have harea : 0 ≤ (X.card : ℝ) * (Y.card : ℝ) := by positivity
      linarith
  | succ k ih =>
    unfold cappedGoodRect3DLoop
    dsimp only
    have harea : 0 ≤ (X.card : ℝ) * (Y.card : ℝ) := by positivity
    by_cases hcap : matDensity X Y A ≥ α_cap
    · rw [if_pos hcap]
      dsimp only
      refine ⟨Finset.Subset.rfl, Finset.Subset.rfl, hX, hY, rfl, Nat.zero_le _, ?_, ?_,
        ?_, Or.inr rfl, fun _ => hcap, fun h => by cases h⟩
      · simp only [pow_zero, one_mul]; exact le_rfl
      · simp only [pow_zero, one_mul]; exact le_rfl
      · simp only [pow_zero, inv_one, Nat.cast_zero, zero_mul, neg_zero, zpow_zero, mul_one]
        linarith
    · rw [if_neg hcap]
      push_neg at hcap
      have hrow_nonneg : ∀ x ∈ X, 0 ≤ rowDeg Y A x :=
        fun x hx => expectSet_nonneg (fun y hy => isBinaryMatrix_nonneg hA x hx y hy)
      have hmin := lem_min_degree hX hε0 hε1 (by norm_num) (le_rfl) hrow_nonneg
      rcases hmin with ⟨hX'_sub, hX'_ne, hX'_third, hX'_dens, htag_cases, htag1_spec, htag2_spec, _⟩
      let X' := (minDegree X Y A ε (1 / 2)).1
      let tag₁ := (minDegree X Y A ε (1 / 2)).2
      have hA_X' : IsBinaryMatrix X' Y A := isBinaryMatrix_subset hX'_sub Finset.Subset.rfl hA
      have hX'_gt : (2 : ℝ) ^ (-(D : ℤ)) < matDensity X' Y A := lt_of_lt_of_le hA_gt hX'_dens
      by_cases hstep1 : tag₁ = 2 ∨ matDensity X' Y A ≥ (1 + ε / 2) * matDensity X Y A
      · -- Recursive Step 1 (`tag₁ = 2 ∨ matDensity X' Y A ≥ (1 + ε / 2) * matDensity X Y A`)
        rw [if_pos hstep1]
        have hboost1 : (1 + ε / 2) * matDensity X Y A ≤ matDensity X' Y A := by
          rcases hstep1 with h2 | hdens_ge
          · have h2s := htag2_spec h2
            linarith [h2s.2.2.2.2.2.2.1]
          · exact hdens_ge
        have hfuel_next : α_cap ≤ (1 + ε / 2) ^ k * matDensity X' Y A := by
          calc
            α_cap ≤ (1 + ε / 2) ^ (k + 1) * matDensity X Y A := hfuel_cap
            _ = (1 + ε / 2) ^ k * ((1 + ε / 2) * matDensity X Y A) := by rw [pow_succ]; ring
            _ ≤ (1 + ε / 2) ^ k * matDensity X' Y A :=
              mul_le_mul_of_nonneg_left hboost1 (by positivity)
        rcases ih hX'_ne hY hA_X' hX'_gt hfuel_next with
          ⟨hsubX, hsubY, hneX, hneY, hA_eq, hsteps_le, hdens_ih, hY_ih, harea_ih,
            htag_ih, hboost_ih, hreg_ih⟩
        dsimp only
        refine ⟨hsubX.trans hX'_sub, hsubY, hneX, hneY, hA_eq, Nat.succ_le_succ hsteps_le,
          ?_, ?_, ?_, htag_ih, hboost_ih, hreg_ih⟩
        · calc
            (2 : ℝ) ^ (cappedGoodRect3DLoop k X' Y A ε D α_cap S).S_ell *
                (1 + ε / 2) ^ ((cappedGoodRect3DLoop k X' Y A ε D α_cap S).steps + 1) *
                matDensity X Y A
              = (2 : ℝ) ^ (cappedGoodRect3DLoop k X' Y A ε D α_cap S).S_ell *
                  (1 + ε / 2) ^ (cappedGoodRect3DLoop k X' Y A ε D α_cap S).steps *
                  ((1 + ε / 2) * matDensity X Y A) := by rw [pow_succ]; ring
            _ ≤ (2 : ℝ) ^ (cappedGoodRect3DLoop k X' Y A ε D α_cap S).S_ell *
                  (1 + ε / 2) ^ (cappedGoodRect3DLoop k X' Y A ε D α_cap S).steps *
                  matDensity X' Y A :=
                mul_le_mul_of_nonneg_left hboost1 (by positivity)
            _ ≤ _ := hdens_ih
        · have h2D_le : (((2 : ℝ) ^ (2 * D))⁻¹) ≤ 1 :=
            inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
          calc
            (((2 : ℝ) ^ (2 * D))⁻¹) ^ ((cappedGoodRect3DLoop k X' Y A ε D α_cap S).steps + 1) *
                (Y.card : ℝ)
              = (((2 : ℝ) ^ (2 * D))⁻¹) *
                  ((((2 : ℝ) ^ (2 * D))⁻¹) ^ (cappedGoodRect3DLoop k X' Y A ε D α_cap S).steps *
                    (Y.card : ℝ)) := by rw [pow_succ']; ring
            _ ≤ 1 * ((((2 : ℝ) ^ (2 * D))⁻¹) ^ (cappedGoodRect3DLoop k X' Y A ε D α_cap S).steps *
                  (Y.card : ℝ)) :=
                mul_le_mul_of_nonneg_right h2D_le (by positivity)
            _ ≤ _ := by linarith
        · have hfac_ge_3 : 3 ≤ goodRect3DStepFactor ε D := by
            unfold goodRect3DStepFactor
            have h1 : 48 ≤ 48 / ε := by rw [le_div_iff₀ hε0]; linarith
            have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (4 * D) := one_le_pow₀ (by norm_num)
            nlinarith
          have hinv_le : (goodRect3DStepFactor ε D)⁻¹ ≤ (1 / 3 : ℝ) := by
            rw [one_div]
            exact inv_anti₀ (by norm_num) hfac_ge_3
          have hX'_area :
              (goodRect3DStepFactor ε D)⁻¹ * ((X.card : ℝ) * (Y.card : ℝ)) ≤
                (X'.card : ℝ) * (Y.card : ℝ) := by
            calc
              (goodRect3DStepFactor ε D)⁻¹ * ((X.card : ℝ) * (Y.card : ℝ))
                ≤ (1 / 3 : ℝ) * ((X.card : ℝ) * (Y.card : ℝ)) :=
                  mul_le_mul_of_nonneg_right hinv_le harea
              _ = ((1 / 3 : ℝ) * (X.card : ℝ)) * (Y.card : ℝ) := by ring
              _ ≤ (X'.card : ℝ) * (Y.card : ℝ) :=
                  mul_le_mul_of_nonneg_right hX'_third (Nat.cast_nonneg _)
          calc
            (3⁻¹ : ℝ) *
                ((goodRect3DStepFactor ε D) ^
                  ((cappedGoodRect3DLoop k X' Y A ε D α_cap S).steps + 1))⁻¹ *
                (2 : ℝ) ^ (-((cappedGoodRect3DLoop k X' Y A ε D α_cap S).S_ell * D : ℤ)) *
                ((X.card : ℝ) * (Y.card : ℝ))
              = (3⁻¹ : ℝ) *
                  ((goodRect3DStepFactor ε D) ^
                    (cappedGoodRect3DLoop k X' Y A ε D α_cap S).steps)⁻¹ *
                  (2 : ℝ) ^ (-((cappedGoodRect3DLoop k X' Y A ε D α_cap S).S_ell * D : ℤ)) *
                  ((goodRect3DStepFactor ε D)⁻¹ * ((X.card : ℝ) * (Y.card : ℝ))) := by
                rw [pow_succ, mul_inv]; ring
            _ ≤ (3⁻¹ : ℝ) *
                  ((goodRect3DStepFactor ε D) ^
                    (cappedGoodRect3DLoop k X' Y A ε D α_cap S).steps)⁻¹ *
                  (2 : ℝ) ^ (-((cappedGoodRect3DLoop k X' Y A ε D α_cap S).S_ell * D : ℤ)) *
                  ((X'.card : ℝ) * (Y.card : ℝ)) := by
                refine mul_le_mul_of_nonneg_left hX'_area ?_
                have := one_le_goodRect3DStepFactor hε0 hε1.le D
                positivity
            _ ≤ _ := harea_ih
      · rw [if_neg hstep1]
        by_cases hcap2 : matDensity X' Y A ≥ α_cap
        · -- Halts at Line 4 (`matDensity X' Y A ≥ α_cap`)
          rw [if_pos hcap2]
          dsimp only
          have hX'_area : (3⁻¹ : ℝ) * ((X.card : ℝ) * (Y.card : ℝ)) ≤ (X'.card : ℝ) * (Y.card : ℝ) := by
            have : (3⁻¹ : ℝ) * ((X.card : ℝ) * (Y.card : ℝ)) =
                ((1 / 3 : ℝ) * (X.card : ℝ)) * (Y.card : ℝ) := by ring
            rw [this]
            exact mul_le_mul_of_nonneg_right hX'_third (Nat.cast_nonneg _)
          refine ⟨hX'_sub, Finset.Subset.rfl, hX'_ne, hY, rfl, Nat.zero_le _, ?_, ?_,
            ?_, Or.inr rfl, fun _ => hcap2, fun h => by cases h⟩
          · simp only [pow_zero, one_mul]; exact hX'_dens
          · simp only [pow_zero, one_mul]; exact le_rfl
          · simp only [pow_zero, inv_one, Nat.cast_zero, zero_mul, neg_zero, zpow_zero, mul_one]
            exact hX'_area
        · -- Runs `dyadicSiftConcrete X' Y A ε D S`
          rw [if_neg hcap2]
          push_neg at hcap2
          have htag1_eq : tag₁ = 1 := by
            rcases htag_cases with h1 | h2
            · exact h1
            · exact False.elim (hstep1 (Or.inl h2))
          have hmin_reg := (htag1_spec htag1_eq).1
          have hδ_gt : 1 < (2 : ℝ) ^ D * ((1 + ε / 2) * matDensity X' Y A) := by
            have h1 : (2 : ℝ) ^ D * (2 : ℝ) ^ (-(D : ℤ)) = 1 := by
              rw [← zpow_natCast 2 D, ← zpow_add₀ (by norm_num), add_neg_cancel, zpow_zero]
            have h2 : (2 : ℝ) ^ (-(D : ℤ)) < (1 + ε / 2) * matDensity X' Y A := by
              have hpos_d : 0 < matDensity X' Y A := lt_trans (by positivity) hX'_gt
              nlinarith
            nlinarith [(by positivity : (0 : ℝ) < (2 : ℝ) ^ D)]
          have hsift := lem_dyadic_sift_concrete S hX'_ne hY hA_X' hε0 hε1 hD hδ_gt
          rcases hsift with ⟨hsift_cases, hsift_sub_spec, hsift_reg_spec⟩
          by_cases hsift_tag : (dyadicSiftConcrete X' Y A ε D S).1 = "subrect"
          · -- Recursive Step 2 (`siftRes.1 = "subrect"`)
            rw [if_pos hsift_tag]
            rcases hsift_sub_spec hsift_tag with
              ⟨hs_lt_D, hX''_sub, hY''_sub, hX''_ne, hY''_ne, hX''_dens, hX''_card, _, hY''_card⟩
            let X'' := (dyadicSiftConcrete X' Y A ε D S).2.1
            let Y'' := (dyadicSiftConcrete X' Y A ε D S).2.2.1
            let s := (dyadicSiftConcrete X' Y A ε D S).2.2.2
            have hA_X'' : IsBinaryMatrix X'' Y'' A := isBinaryMatrix_subset hX''_sub hY''_sub hA_X'
            have h2s_ge : (1 : ℝ) ≤ (2 : ℝ) ^ s := one_le_pow₀ (by norm_num)
            have hX'_pos : 0 < matDensity X' Y A := lt_trans (by positivity) hX'_gt
            have hboost2 : (1 + ε / 2) * matDensity X Y A ≤ matDensity X'' Y'' A := by
              have h1 : (1 + ε / 2) * matDensity X Y A ≤ (1 + ε / 2) * matDensity X' Y A :=
                mul_le_mul_of_nonneg_left hX'_dens (by linarith)
              have h2 : 1 * ((1 + ε / 2) * matDensity X' Y A) ≤
                  (2 : ℝ) ^ s * ((1 + ε / 2) * matDensity X' Y A) :=
                mul_le_mul_of_nonneg_right h2s_ge (by positivity)
              linarith [hX''_dens]
            have hX''_gt : (2 : ℝ) ^ (-(D : ℤ)) < matDensity X'' Y'' A := by
              have hpos_d : 0 < matDensity X Y A := lt_trans (by positivity) hA_gt
              nlinarith
            have hfuel_next : α_cap ≤ (1 + ε / 2) ^ k * matDensity X'' Y'' A := by
              calc
                α_cap ≤ (1 + ε / 2) ^ (k + 1) * matDensity X Y A := hfuel_cap
                _ = (1 + ε / 2) ^ k * ((1 + ε / 2) * matDensity X Y A) := by rw [pow_succ]; ring
                _ ≤ (1 + ε / 2) ^ k * matDensity X'' Y'' A :=
                  mul_le_mul_of_nonneg_left hboost2 (by positivity)
            rcases ih hX''_ne hY''_ne hA_X'' hX''_gt hfuel_next with
              ⟨hsubX, hsubY, hneX, hneY, hA_eq, hsteps_le, hdens_ih, hY_ih, harea_ih,
                htag_ih, hboost_ih, hreg_ih⟩
            dsimp only
            refine ⟨hsubX.trans (hX''_sub.trans hX'_sub), hsubY.trans hY''_sub,
              hneX, hneY, hA_eq, Nat.succ_le_succ hsteps_le, ?_, ?_, ?_,
              htag_ih, hboost_ih, hreg_ih⟩
            · have hstep_s :
                  (2 : ℝ) ^ s * (1 + ε / 2) * matDensity X Y A ≤ matDensity X'' Y'' A := by
                have h1 : (2 : ℝ) ^ s * (1 + ε / 2) * matDensity X Y A ≤
                    (2 : ℝ) ^ s * (1 + ε / 2) * matDensity X' Y A :=
                  mul_le_mul_of_nonneg_left hX'_dens (by positivity)
                exact h1.trans hX''_dens
              calc
                (2 : ℝ) ^ ((cappedGoodRect3DLoop k X'' Y'' A ε D α_cap S).S_ell + s) *
                    (1 + ε / 2) ^ ((cappedGoodRect3DLoop k X'' Y'' A ε D α_cap S).steps + 1) *
                    matDensity X Y A
                  = (2 : ℝ) ^ (cappedGoodRect3DLoop k X'' Y'' A ε D α_cap S).S_ell *
                      (1 + ε / 2) ^ (cappedGoodRect3DLoop k X'' Y'' A ε D α_cap S).steps *
                      ((2 : ℝ) ^ s * (1 + ε / 2) * matDensity X Y A) := by
                    rw [pow_add, pow_succ]; ring
                _ ≤ (2 : ℝ) ^ (cappedGoodRect3DLoop k X'' Y'' A ε D α_cap S).S_ell *
                      (1 + ε / 2) ^ (cappedGoodRect3DLoop k X'' Y'' A ε D α_cap S).steps *
                      matDensity X'' Y'' A :=
                    mul_le_mul_of_nonneg_left hstep_s (by positivity)
                _ ≤ _ := hdens_ih
            · calc
                (((2 : ℝ) ^ (2 * D))⁻¹) ^
                    ((cappedGoodRect3DLoop k X'' Y'' A ε D α_cap S).steps + 1) * (Y.card : ℝ)
                  = (((2 : ℝ) ^ (2 * D))⁻¹) ^ (cappedGoodRect3DLoop k X'' Y'' A ε D α_cap S).steps *
                      ((((2 : ℝ) ^ (2 * D))⁻¹) * (Y.card : ℝ)) := by rw [pow_succ]; ring
                _ ≤ (((2 : ℝ) ^ (2 * D))⁻¹) ^ (cappedGoodRect3DLoop k X'' Y'' A ε D α_cap S).steps *
                      (Y''.card : ℝ) :=
                    mul_le_mul_of_nonneg_left hY''_card.le (by positivity)
                _ ≤ _ := hY_ih
            · have hX''_X :
                  (ε / 48) * (((2 : ℝ) ^ ((s + 2) * D))⁻¹) * (X.card : ℝ) ≤ (X''.card : ℝ) := by
                calc
                  (ε / 48) * (((2 : ℝ) ^ ((s + 2) * D))⁻¹) * (X.card : ℝ)
                    = (ε / 16) * (((2 : ℝ) ^ ((s + 2) * D))⁻¹) * ((1 / 3 : ℝ) * (X.card : ℝ)) := by
                      ring
                  _ ≤ (ε / 16) * (((2 : ℝ) ^ ((s + 2) * D))⁻¹) * (X'.card : ℝ) :=
                      mul_le_mul_of_nonneg_left hX'_third (by positivity)
                  _ ≤ (X''.card : ℝ) := hX''_card
              have harea_step :
                  (goodRect3DStepFactor ε D)⁻¹ * (2 : ℝ) ^ (-(s * D : ℤ)) *
                    ((X.card : ℝ) * (Y.card : ℝ)) ≤ (X''.card : ℝ) * (Y''.card : ℝ) := by
                have hprod := mul_le_mul hX''_X hY''_card.le (by positivity) (by positivity)
                have hlhs_eq :
                    (goodRect3DStepFactor ε D)⁻¹ * (2 : ℝ) ^ (-(s * D : ℤ)) *
                      ((X.card : ℝ) * (Y.card : ℝ)) =
                    ((ε / 48) * (((2 : ℝ) ^ ((s + 2) * D))⁻¹) * (X.card : ℝ)) *
                      ((((2 : ℝ) ^ (2 * D))⁻¹) * (Y.card : ℝ)) := by
                  unfold goodRect3DStepFactor
                  have hzpow : (2 : ℝ) ^ (-((s : ℤ) * (D : ℤ))) = ((2 : ℝ) ^ (s * D))⁻¹ := by
                    have hcast : (s : ℤ) * (D : ℤ) = ((s * D : ℕ) : ℤ) := (Nat.cast_mul s D).symm
                    rw [hcast, zpow_neg, zpow_natCast]
                  have hpow : (2 : ℝ) ^ (4 * D) * (2 : ℝ) ^ (s * D) =
                      (2 : ℝ) ^ ((s + 2) * D) * (2 : ℝ) ^ (2 * D) := by
                    rw [← pow_add, ← pow_add]
                    congr 1
                    ring
                  rw [hzpow, mul_inv, inv_div]
                  calc
                    (ε / 48 * ((2 : ℝ) ^ (4 * D))⁻¹) * ((2 : ℝ) ^ (s * D))⁻¹ *
                        ((X.card : ℝ) * (Y.card : ℝ))
                      = (ε / 48) * (((2 : ℝ) ^ (4 * D) * (2 : ℝ) ^ (s * D))⁻¹) *
                          ((X.card : ℝ) * (Y.card : ℝ)) := by
                        rw [mul_inv]; ring
                    _ = (ε / 48) * (((2 : ℝ) ^ ((s + 2) * D) * (2 : ℝ) ^ (2 * D))⁻¹) *
                          ((X.card : ℝ) * (Y.card : ℝ)) := by
                        rw [hpow]
                    _ = ((ε / 48) * (((2 : ℝ) ^ ((s + 2) * D))⁻¹) * (X.card : ℝ)) *
                          ((((2 : ℝ) ^ (2 * D))⁻¹) * (Y.card : ℝ)) := by
                        rw [mul_inv]; ring
                rw [hlhs_eq]
                exact hprod
              have hzpow_add :
                  (2 : ℝ) ^ (-(((cappedGoodRect3DLoop k X'' Y'' A ε D α_cap S).S_ell + s) * D : ℤ)) =
                    (2 : ℝ) ^ (-((cappedGoodRect3DLoop k X'' Y'' A ε D α_cap S).S_ell * D : ℤ)) *
                      (2 : ℝ) ^ (-(s * D : ℤ)) := by
                have hexp :
                    (-(((cappedGoodRect3DLoop k X'' Y'' A ε D α_cap S).S_ell + s) * D : ℤ)) =
                      (-((cappedGoodRect3DLoop k X'' Y'' A ε D α_cap S).S_ell * D : ℤ)) +
                        (-(s * D : ℤ)) := by ring
                rw [hexp, zpow_add₀ (by norm_num)]
              calc
                (3⁻¹ : ℝ) *
                    ((goodRect3DStepFactor ε D) ^
                      ((cappedGoodRect3DLoop k X'' Y'' A ε D α_cap S).steps + 1))⁻¹ *
                    (2 : ℝ) ^ (-(((cappedGoodRect3DLoop k X'' Y'' A ε D α_cap S).S_ell + s) * D : ℤ)) *
                    ((X.card : ℝ) * (Y.card : ℝ))
                  = (3⁻¹ : ℝ) *
                      ((goodRect3DStepFactor ε D) ^
                        (cappedGoodRect3DLoop k X'' Y'' A ε D α_cap S).steps)⁻¹ *
                      (2 : ℝ) ^ (-((cappedGoodRect3DLoop k X'' Y'' A ε D α_cap S).S_ell * D : ℤ)) *
                      ((goodRect3DStepFactor ε D)⁻¹ * (2 : ℝ) ^ (-(s * D : ℤ)) *
                        ((X.card : ℝ) * (Y.card : ℝ))) := by
                    rw [pow_succ, mul_inv, hzpow_add]; ring
                _ ≤ (3⁻¹ : ℝ) *
                      ((goodRect3DStepFactor ε D) ^
                        (cappedGoodRect3DLoop k X'' Y'' A ε D α_cap S).steps)⁻¹ *
                      (2 : ℝ) ^ (-((cappedGoodRect3DLoop k X'' Y'' A ε D α_cap S).S_ell * D : ℤ)) *
                      ((X''.card : ℝ) * (Y''.card : ℝ)) := by
                    refine mul_le_mul_of_nonneg_left harea_step ?_
                    have := one_le_goodRect3DStepFactor hε0 hε1.le D
                    positivity
                _ ≤ _ := harea_ih
          · -- Halts at Line 6 (`\label{line:findrect-reg}`, `siftRes.1 = "regular"`)
            rw [if_neg hsift_tag]
            have hsift_reg_eq : (dyadicSiftConcrete X' Y A ε D S).1 = "regular" := by
              rcases hsift_cases with h1 | h2
              · exact False.elim (hsift_tag h1)
              · exact h2
            have hregA := (hsift_reg_spec hsift_reg_eq).2.2.2.2
            dsimp only
            have hX'_area : (3⁻¹ : ℝ) * ((X.card : ℝ) * (Y.card : ℝ)) ≤
                (X'.card : ℝ) * (Y.card : ℝ) := by
              have : (3⁻¹ : ℝ) * ((X.card : ℝ) * (Y.card : ℝ)) =
                  ((1 / 3 : ℝ) * (X.card : ℝ)) * (Y.card : ℝ) := by ring
              rw [this]
              exact mul_le_mul_of_nonneg_right hX'_third (Nat.cast_nonneg _)
            refine ⟨hX'_sub, Finset.Subset.rfl, hX'_ne, hY, rfl, Nat.zero_le _, ?_, ?_,
              ?_, Or.inl rfl, (fun h => by cases h), fun _ => ⟨hcap2, ?_, ?_⟩⟩
            · simp only [pow_zero, one_mul]; exact hX'_dens
            · simp only [pow_zero, one_mul]; exact le_rfl
            · simp only [pow_zero, inv_one, Nat.cast_zero, zero_mul, neg_zero, zpow_zero, mul_one]
              exact hX'_area
            · refine isGridRegular_of_eq_on (fun x hx y hy => ?_) hregA
              simp only [submatZeroExt, hx, hy, and_self, ↓reduceIte]
            · refine isEpsMinDegree_of_eq_on (fun x hx y hy => ?_) hmin_reg
              simp only [submatZeroExt, hx, hy, and_self, ↓reduceIte]


/-- Outer-loop piece budget $\lceil 2^{D + D^2} M_{\text{rect3D}}(\varepsilon, D) \rceil$
for `cappedADecomp3D`. -/
noncomputable def rDecompAFuel (ε : ℝ) (D : ℕ) : ℕ :=
  Nat.ceil ((2 : ℝ) ^ (D + D ^ 2) * M_rect3D ε D)

open Classical in
/-- **Algorithm 4 (`FindRect` / `Decompose2D`) Outer Loop (`cappedADecomp3DLoop`, §4.3 of `paper.tex`)**:
Iteratively extracts 2D pieces via `cappedGoodRect3D` while
$\mathbb{E}[A_{\text{rem}}] > \max(2^{-D}, \alpha_{\text{low}})$ and zeroes out
$A_{\text{rem}}[X_\ell, Y_\ell] \leftarrow 0$, finally emitting the residual piece
`⟨X, Y, submatZeroExt X Y A_rem, RectTag.residual, 0⟩`. -/
noncomputable def cappedADecomp3DLoop [DecidableEq α] [DecidableEq β] :
    ℕ → Finset α → Finset β → (α → β → ℝ) → (ε : ℝ) → ℕ → ℝ → ℝ →
    TwoStageSamplerOracle β ε → List (RectPiece α β)
  | 0, X, Y, A_rem, _ε, _D, _α_low, _α_cap, _S =>
    [⟨X, Y, submatZeroExt X Y A_rem, RectTag.residual, 0⟩]
  | fuel + 1, X, Y, A_rem, ε, D, α_low, α_cap, S =>
    if matDensity X Y A_rem ≤ max ((2 : ℝ) ^ (-(D : ℤ))) α_low then
      [⟨X, Y, submatZeroExt X Y A_rem, RectTag.residual, 0⟩]
    else
      let res := cappedGoodRect3D X Y A_rem ε D α_cap S
      let piece : RectPiece α β := ⟨res.X_ell, res.Y_ell, res.A_ell, res.tag, res.S_ell⟩
      let A_next := zeroOutSubrect A_rem res.X_ell res.Y_ell
      piece :: cappedADecomp3DLoop fuel X Y A_next ε D α_low α_cap S

open Classical in
/-- Cost-tracked outer loop `cappedADecomp3DLoopTracked` in `CostM`. -/
noncomputable def cappedADecomp3DLoopTracked [DecidableEq α] [DecidableEq β] :
    ℕ → Finset α → Finset β → (α → β → ℝ) → (ε : ℝ) → ℕ → ℝ → ℝ →
    TwoStageSamplerOracle β ε → CostM (List (RectPiece α β))
  | 0, X, Y, A_rem, _ε, _D, _α_low, _α_cap, _S =>
    scanMatrixTracked X Y [⟨X, Y, submatZeroExt X Y A_rem, RectTag.residual, 0⟩]
  | fuel + 1, X, Y, A_rem, ε, D, α_low, α_cap, S =>
    if matDensity X Y A_rem ≤ max ((2 : ℝ) ^ (-(D : ℤ))) α_low then
      scanMatrixTracked X Y [⟨X, Y, submatZeroExt X Y A_rem, RectTag.residual, 0⟩]
    else
      CostM.bind (cappedGoodRect3DTracked X Y A_rem ε D α_cap S) (fun res =>
        let piece : RectPiece α β := ⟨res.X_ell, res.Y_ell, res.A_ell, res.tag, res.S_ell⟩
        let A_next := zeroOutSubrect A_rem res.X_ell res.Y_ell
        CostM.bind (cappedADecomp3DLoopTracked fuel X Y A_next ε D α_low α_cap S) (fun rest =>
          scanMatrixTracked X Y (piece :: rest)))

@[simp]
lemma cappedADecomp3DLoopTracked_fst [DecidableEq α] [DecidableEq β]
    (fuel : ℕ) (X : Finset α) (Y : Finset β) (A_rem : α → β → ℝ)
    (ε : ℝ) (D : ℕ) (α_low α_cap : ℝ) (S : TwoStageSamplerOracle β ε) :
    (cappedADecomp3DLoopTracked fuel X Y A_rem ε D α_low α_cap S).1 =
      cappedADecomp3DLoop fuel X Y A_rem ε D α_low α_cap S := by
  classical
  induction fuel generalizing A_rem with
  | zero => rfl
  | succ k ih =>
    unfold cappedADecomp3DLoopTracked cappedADecomp3DLoop
    dsimp only
    split_ifs with hle
    · rfl
    · simp only [CostM.bind_fst, scanMatrixTracked_fst, cappedGoodRect3DTracked_fst, ih]

/-- **Algorithm 4 (`FindRect` / `Decompose2D`) (`cappedADecomp3D`, §4.3 & §5.2 of `paper.tex`)**:
3D-windowed `CappedADecomposition` with piece fuel `rDecompAFuel ε D`. -/
noncomputable def cappedADecomp3D [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (A : α → β → ℝ) (ε : ℝ) (D : ℕ) (α_low α_cap : ℝ)
    (S : TwoStageSamplerOracle β ε) :
    List (RectPiece α β) :=
  cappedADecomp3DLoop (rDecompAFuel ε D) X Y A ε D α_low α_cap S

/-- Tracked `CostM` implementation of `cappedADecomp3D`. -/
noncomputable def cappedADecomp3DTracked [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (A : α → β → ℝ) (ε : ℝ) (D : ℕ) (α_low α_cap : ℝ)
    (S : TwoStageSamplerOracle β ε) :
    CostM (List (RectPiece α β)) :=
  cappedADecomp3DLoopTracked (rDecompAFuel ε D) X Y A ε D α_low α_cap S

@[simp]
lemma cappedADecomp3DTracked_fst [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (A : α → β → ℝ) (ε : ℝ) (D : ℕ) (α_low α_cap : ℝ)
    (S : TwoStageSamplerOracle β ε) :
    (cappedADecomp3DTracked X Y A ε D α_low α_cap S).1 =
      cappedADecomp3D X Y A ε D α_low α_cap S :=
  cappedADecomp3DLoopTracked_fst (rDecompAFuel ε D) X Y A ε D α_low α_cap S

lemma cappedADecomp3DLoop_length_le [DecidableEq α] [DecidableEq β]
    (fuel : ℕ) (X : Finset α) (Y : Finset β) (A_rem : α → β → ℝ)
    (ε : ℝ) (D : ℕ) (α_low α_cap : ℝ) (S : TwoStageSamplerOracle β ε) :
    (cappedADecomp3DLoop fuel X Y A_rem ε D α_low α_cap S).length ≤ fuel + 1 := by
  classical
  induction fuel generalizing A_rem with
  | zero =>
    unfold cappedADecomp3DLoop
    simp
  | succ k ih =>
    unfold cappedADecomp3DLoop
    dsimp only
    split_ifs
    · simp
    · simp only [List.length_cons]
      have := ih (zeroOutSubrect A_rem (cappedGoodRect3D X Y A_rem ε D α_cap S).X_ell
        (cappedGoodRect3D X Y A_rem ε D α_cap S).Y_ell)
      omega

lemma cappedADecomp3DLoopTracked_snd_le [DecidableEq α] [DecidableEq β]
    (fuel : ℕ) (X : Finset α) (Y : Finset β) (A_rem : α → β → ℝ)
    (ε : ℝ) (D : ℕ) (α_low α_cap : ℝ) (S : TwoStageSamplerOracle β ε) :
    (cappedADecomp3DLoopTracked fuel X Y A_rem ε D α_low α_cap S).2 ≤
      (fuel + 1) * ((rRectFuel ε + 2) * ((X.card + Y.card + 2) ^ 2 *
        (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 6))) := by
  classical
  induction fuel generalizing A_rem with
  | zero =>
    unfold cappedADecomp3DLoopTracked
    simp only [scanMatrixTracked_snd, zero_add, one_mul]
    have hbase : X.card * Y.card + 1 ≤
        (X.card + Y.card + 2) ^ 2 * (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 6) := by
      have : X.card * Y.card + 1 ≤ (X.card + Y.card + 2) ^ 2 * 1 := by nlinarith
      exact this.trans (Nat.mul_le_mul_left _ (by omega))
    exact hbase.trans (Nat.le_mul_of_pos_left _ (by omega))
  | succ k ih =>
    unfold cappedADecomp3DLoopTracked
    dsimp only
    have hbase : X.card * Y.card + 1 ≤
        (X.card + Y.card + 2) ^ 2 * (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 6) := by
      have : X.card * Y.card + 1 ≤ (X.card + Y.card + 2) ^ 2 * 1 := by nlinarith
      exact this.trans (Nat.mul_le_mul_left _ (by omega))
    split_ifs with hle
    · simp only [scanMatrixTracked_snd]
      have h1 : (X.card + Y.card + 2) ^ 2 *
          (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 6) ≤
          (rRectFuel ε + 2) * ((X.card + Y.card + 2) ^ 2 *
            (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 6)) :=
        Nat.le_mul_of_pos_left _ (by omega)
      have h2 := h1.trans (Nat.le_mul_of_pos_left _ (by omega : 0 < k + 1 + 1))
      exact hbase.trans h2
    · rw [CostM.bind_snd, CostM.bind_snd, scanMatrixTracked_snd, cappedGoodRect3DTracked_fst]
      have hgr := cappedGoodRect3DTracked_snd_le X Y A_rem ε D α_cap S
      have hrec := ih (zeroOutSubrect A_rem (cappedGoodRect3D X Y A_rem ε D α_cap S).X_ell
        (cappedGoodRect3D X Y A_rem ε D α_cap S).Y_ell)
      change (cappedGoodRect3DTracked X Y A_rem ε D α_cap S).2 +
        ((cappedADecomp3DLoopTracked k X Y _ ε D α_low α_cap S).2 + (X.card * Y.card + 1)) ≤ _
      nlinarith

lemma cappedADecomp3DTracked_snd_le [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (A_rem : α → β → ℝ)
    (ε : ℝ) (D : ℕ) (α_low α_cap : ℝ) (S : TwoStageSamplerOracle β ε) :
    (cappedADecomp3DTracked X Y A_rem ε D α_low α_cap S).2 ≤
      (rDecompAFuel ε D + 1) * ((rRectFuel ε + 2) * ((X.card + Y.card + 2) ^ 2 *
        (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 6))) :=
  cappedADecomp3DLoopTracked_snd_le (rDecompAFuel ε D) X Y A_rem ε D α_low α_cap S

/-- Exact matrix entry decomposition for `cappedADecomp3DLoop`:
$\sum_{P \in L} P.A_{\text{sub}}(x, y) = \text{submatZeroExt } X Y A_{\text{rem}} x y$. -/
theorem cappedADecomp3DLoop_sum_eq [DecidableEq α] [DecidableEq β]
    (fuel : ℕ) (X : Finset α) (Y : Finset β) (A_rem : α → β → ℝ)
    (ε : ℝ) (D : ℕ) (α_low α_cap : ℝ) (S : TwoStageSamplerOracle β ε) (x : α) (y : β) :
    ((cappedADecomp3DLoop fuel X Y A_rem ε D α_low α_cap S).map
      (fun P => P.A_sub x y)).sum = submatZeroExt X Y A_rem x y := by
  classical
  induction fuel generalizing A_rem with
  | zero =>
    unfold cappedADecomp3DLoop
    simp
  | succ k ih =>
    unfold cappedADecomp3DLoop
    dsimp only
    split_ifs with hle
    · simp
    · simp only [List.map_cons, List.sum_cons]
      rw [ih]
      unfold cappedGoodRect3D
      have hsub := cappedGoodRect3DLoop_subset (rRectFuel ε) X Y A_rem ε D α_cap S
      rcases hsub with ⟨hX_sub, hY_sub, hA_eq⟩
      rw [hA_eq]
      unfold submatZeroExt zeroOutSubrect
      by_cases hx : x ∈ X <;> by_cases hy : y ∈ Y
      · by_cases hx' : x ∈ (cappedGoodRect3DLoop (rRectFuel ε) X Y A_rem ε D α_cap S).X_ell <;>
          by_cases hy' : y ∈ (cappedGoodRect3DLoop (rRectFuel ε) X Y A_rem ε D α_cap S).Y_ell <;>
          simp [hx, hy, hx', hy']
      · have hy' : y ∉ (cappedGoodRect3DLoop (rRectFuel ε) X Y A_rem ε D α_cap S).Y_ell :=
          fun h => hy (hY_sub h)
        simp [hx, hy, hy']
      · have hx' : x ∉ (cappedGoodRect3DLoop (rRectFuel ε) X Y A_rem ε D α_cap S).X_ell :=
          fun h => hx (hX_sub h)
        simp [hx, hy, hx']
      · have hx' : x ∉ (cappedGoodRect3DLoop (rRectFuel ε) X Y A_rem ε D α_cap S).X_ell :=
          fun h => hx (hX_sub h)
        simp [hx, hy, hx']

/-- First-moment conservation for `cappedADecomp3DLoop`:
$\sum_{P \in L} \mathbb{E}[P.A_{\text{sub}}] |P.X_{\text{sub}}| |P.Y_{\text{sub}}| = \mathbb{E}[A_{\text{rem}}] |X| |Y|$. -/
theorem cappedADecomp3DLoop_first_moment_eq [DecidableEq α] [DecidableEq β]
    (fuel : ℕ) {X : Finset α} {Y : Finset β} (hX : X.Nonempty) (hY : Y.Nonempty)
    (A_rem : α → β → ℝ) (ε : ℝ) (D : ℕ) (α_low α_cap : ℝ) (S : TwoStageSamplerOracle β ε) :
    ((cappedADecomp3DLoop fuel X Y A_rem ε D α_low α_cap S).map
      (fun P => matDensity P.X_sub P.Y_sub P.A_sub * (P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ))).sum =
      matDensity X Y A_rem * (X.card : ℝ) * (Y.card : ℝ) := by
  classical
  have hX_ne : (X.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hX.card_pos.ne'
  have hY_ne : (Y.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hY.card_pos.ne'
  induction fuel generalizing A_rem with
  | zero =>
    unfold cappedADecomp3DLoop
    simp [matDensity_submatZeroExt_eq]
  | succ k ih =>
    unfold cappedADecomp3DLoop
    dsimp only
    split_ifs with hle
    · simp [matDensity_submatZeroExt_eq]
    · simp only [List.map_cons, List.sum_cons]
      rw [ih]
      unfold cappedGoodRect3D
      have hsub := cappedGoodRect3DLoop_subset (rRectFuel ε) X Y A_rem ε D α_cap S
      rcases hsub with ⟨hX_sub, hY_sub, hA_eq⟩
      rw [hA_eq, matDensity_submatZeroExt_eq]
      have hzero := matDensity_zeroOutSubrect_eq A_rem hX hY hX_sub hY_sub
      have hmul := congrArg (fun t => t * (X.card : ℝ) * (Y.card : ℝ)) hzero
      dsimp only at hmul
      have hsimp :
          (matDensity X Y A_rem -
              ((cappedGoodRect3DLoop (rRectFuel ε) X Y A_rem ε D α_cap S).X_ell.card : ℝ) / (X.card : ℝ) *
                (((cappedGoodRect3DLoop (rRectFuel ε) X Y A_rem ε D α_cap S).Y_ell.card : ℝ) / (Y.card : ℝ)) *
                matDensity (cappedGoodRect3DLoop (rRectFuel ε) X Y A_rem ε D α_cap S).X_ell
                  (cappedGoodRect3DLoop (rRectFuel ε) X Y A_rem ε D α_cap S).Y_ell A_rem) *
            (X.card : ℝ) * (Y.card : ℝ) =
          matDensity X Y A_rem * (X.card : ℝ) * (Y.card : ℝ) -
            matDensity (cappedGoodRect3DLoop (rRectFuel ε) X Y A_rem ε D α_cap S).X_ell
              (cappedGoodRect3DLoop (rRectFuel ε) X Y A_rem ε D α_cap S).Y_ell A_rem *
              ((cappedGoodRect3DLoop (rRectFuel ε) X Y A_rem ε D α_cap S).X_ell.card : ℝ) *
              ((cappedGoodRect3DLoop (rRectFuel ε) X Y A_rem ε D α_cap S).Y_ell.card : ℝ) := by
        field_simp [hX_ne, hY_ne]
      linarith

/-- Unconditional subset and binary-matrix preservation for every piece in `cappedADecomp3DLoop`. -/
theorem cappedADecomp3DLoop_mem_subset [DecidableEq α] [DecidableEq β]
    (fuel : ℕ) {X : Finset α} {Y : Finset β} {A_rem : α → β → ℝ}
    {ε : ℝ} {D : ℕ} {α_low α_cap : ℝ} {S : TwoStageSamplerOracle β ε}
    (hA : IsBinaryMatrix X Y A_rem)
    {P : RectPiece α β} (hP : P ∈ cappedADecomp3DLoop fuel X Y A_rem ε D α_low α_cap S) :
    P.X_sub ⊆ X ∧ P.Y_sub ⊆ Y ∧
    IsBinaryMatrix P.X_sub P.Y_sub P.A_sub ∧
    (∀ x y, P.A_sub x y = submatZeroExt P.X_sub P.Y_sub P.A_sub x y) := by
  classical
  induction fuel generalizing A_rem with
  | zero =>
    unfold cappedADecomp3DLoop at hP
    simp only [List.mem_singleton] at hP
    subst hP
    refine ⟨Finset.Subset.rfl, Finset.Subset.rfl, ?_, fun x y => ?_⟩
    · intro x hx y hy
      simp only [submatZeroExt, hx, hy, and_self, ↓reduceIte]
      exact hA x hx y hy
    · dsimp only
      by_cases hxy : x ∈ X ∧ y ∈ Y <;> simp [submatZeroExt, hxy]
  | succ k ih =>
    unfold cappedADecomp3DLoop at hP
    dsimp only at hP
    split_ifs at hP with hle
    · simp only [List.mem_singleton] at hP
      subst hP
      refine ⟨Finset.Subset.rfl, Finset.Subset.rfl, ?_, fun x y => ?_⟩
      · intro x hx y hy
        simp only [submatZeroExt, hx, hy, and_self, ↓reduceIte]
        exact hA x hx y hy
      · dsimp only
        by_cases hxy : x ∈ X ∧ y ∈ Y <;> simp [submatZeroExt, hxy]
    · simp only [List.mem_cons] at hP
      rcases hP with rfl | hP_tail
      · unfold cappedGoodRect3D
        have hsub := cappedGoodRect3DLoop_subset (rRectFuel ε) X Y A_rem ε D α_cap S
        rcases hsub with ⟨hX_sub, hY_sub, hA_eq⟩
        dsimp only
        refine ⟨hX_sub, hY_sub, ?_, fun x y => ?_⟩
        · intro x hx y hy
          rw [hA_eq]
          simp only [submatZeroExt, hx, hy, and_self, ↓reduceIte]
          exact hA x (hX_sub hx) y (hY_sub hy)
        · rw [hA_eq]
          by_cases hxy :
              x ∈ (cappedGoodRect3DLoop (rRectFuel ε) X Y A_rem ε D α_cap S).X_ell ∧
              y ∈ (cappedGoodRect3DLoop (rRectFuel ε) X Y A_rem ε D α_cap S).Y_ell <;>
            simp [submatZeroExt, hxy]
      · exact ih (isBinaryMatrix_zeroOutSubrect _ _ hA) hP_tail

/-- **Lemma 4.3 (`\label{lem:find-rect}`) for 3D Window (`cappedGoodRect3D_spec`, §4.3 & §5.2 of `paper.tex`)**:
When $\alpha_{\text{cap}} \le 2^{48} \mathbb{E}_{X \times Y}[A]$ and $\mathbb{E}_{X \times Y}[A] > 2^{-D}$,
`cappedGoodRect3D X Y A ε D α_cap S` halts in at most `rRectFuel ε` steps with scale
$S_\ell \le D$, area lower bound
$$|X_\ell| |Y_\ell| \ge M_{\text{rect3D}}(\varepsilon, D)^{-1} 2^{-S_\ell D} |X| |Y|,$$
$Y$-shrinkage $|Y_\ell| \ge 2^{-194 D / \varepsilon} |Y|$, and either:
- `res.tag = RectTag.aBoosted` with $\mathbb{E}[A_\ell] \ge \max(\alpha_{\text{cap}}, 2^{S_\ell}\mathbb{E}[A])$, or
- `res.tag = RectTag.regular` with $S_\ell \le 47$, $\mathbb{E}[A_\ell] \in [\mathbb{E}[A], \alpha_{\text{cap}})$,
  $(\varepsilon, 2, D)$-grid-regularity, and $\varepsilon$-min-degree. -/
theorem cappedGoodRect3D_spec [DecidableEq α] [DecidableEq β]
    {X : Finset α} {Y : Finset β} {A : α → β → ℝ} {ε : ℝ} {D : ℕ} {α_cap : ℝ}
    (S : TwoStageSamplerOracle β ε)
    (hX : X.Nonempty) (hY : Y.Nonempty) (hA : IsBinaryMatrix X Y A)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hD : 2 ≤ D)
    (hA_gt : (2 : ℝ) ^ (-(D : ℤ)) < matDensity X Y A)
    (hcap_window : α_cap ≤ (2 : ℝ) ^ (48 : ℕ) * matDensity X Y A) :
    let res := cappedGoodRect3D X Y A ε D α_cap S
    res.X_ell ⊆ X ∧ res.Y_ell ⊆ Y ∧ res.X_ell.Nonempty ∧ res.Y_ell.Nonempty ∧
    res.A_ell = submatZeroExt res.X_ell res.Y_ell A ∧
    res.steps ≤ rRectFuel ε ∧
    res.S_ell ≤ D ∧
    (2 : ℝ) ^ res.S_ell * matDensity X Y A ≤ matDensity res.X_ell res.Y_ell A ∧
    (2 : ℝ) ^ (- (194 * (D : ℝ) / ε)) * (Y.card : ℝ) ≤ (res.Y_ell.card : ℝ) ∧
    (M_rect3D ε D)⁻¹ * (2 : ℝ) ^ (-(res.S_ell * D : ℤ)) *
      ((X.card : ℝ) * (Y.card : ℝ)) ≤ (res.X_ell.card : ℝ) * (res.Y_ell.card : ℝ) ∧
    (res.tag = RectTag.regular ∨ res.tag = RectTag.aBoosted) ∧
    (res.tag = RectTag.aBoosted → α_cap ≤ matDensity res.X_ell res.Y_ell A) ∧
    (res.tag = RectTag.regular →
      res.S_ell ≤ 47 ∧
      matDensity res.X_ell res.Y_ell A < α_cap ∧
      IsGridRegular res.X_ell res.Y_ell res.A_ell ε 2 D ∧
      IsEpsMinDegree res.X_ell res.Y_ell res.A_ell ε) := by
  have hε1 : ε < 1 := by linarith
  have hA_pos : 0 < matDensity X Y A := lt_trans (by positivity) hA_gt
  have hpow48 : (2 : ℝ) ^ (48 : ℕ) ≤ (1 + ε / 2) ^ (rRectFuel ε) := pow_rRect2DFuel_ge hε0
  have hfuel_cap : α_cap ≤ (1 + ε / 2) ^ (rRectFuel ε) * matDensity X Y A :=
    hcap_window.trans (mul_le_mul_of_nonneg_right hpow48 hA_pos.le)
  unfold cappedGoodRect3D
  rcases cappedGoodRect3DLoop_spec (rRectFuel ε) S hX hY hA hε0 hε1 hD hA_gt hfuel_cap with
    ⟨hsubX, hsubY, hneX, hneY, hA_eq, hsteps_le, hdens_loop, hY_loop, harea_loop,
      htag_or, hboost_spec, hreg_spec⟩
  let res := cappedGoodRect3DLoop (rRectFuel ε) X Y A ε D α_cap S
  have hpow_eps_ge : (1 : ℝ) ≤ (1 + ε / 2) ^ res.steps :=
    one_le_pow₀ (by linarith)
  have hdens_scale : (2 : ℝ) ^ res.S_ell * matDensity X Y A ≤ matDensity res.X_ell res.Y_ell A := by
    have h1 : (2 : ℝ) ^ res.S_ell * 1 * matDensity X Y A ≤
        (2 : ℝ) ^ res.S_ell * (1 + ε / 2) ^ res.steps * matDensity X Y A := by
      refine mul_le_mul_of_nonneg_right ?_ hA_pos.le
      exact mul_le_mul_of_nonneg_left hpow_eps_ge (by positivity)
    linarith
  have hS_le_D : res.S_ell ≤ D := by
    have hdens_le_1 : matDensity res.X_ell res.Y_ell A ≤ 1 :=
      matDensity_le_one_of_isBinaryMatrix (isBinaryMatrix_subset hsubX hsubY hA)
    have h1 : (2 : ℝ) ^ res.S_ell * (2 : ℝ) ^ (-(D : ℤ)) < 1 := by
      have : (2 : ℝ) ^ res.S_ell * (2 : ℝ) ^ (-(D : ℤ)) < (2 : ℝ) ^ res.S_ell * matDensity X Y A :=
        mul_lt_mul_of_pos_left hA_gt (by positivity)
      linarith
    have h2 : (2 : ℝ) ^ D * (2 : ℝ) ^ (-(D : ℤ)) = 1 := by
      rw [← zpow_natCast 2 D, ← zpow_add₀ (by norm_num), add_neg_cancel, zpow_zero]
    have hlt_pow : (2 : ℝ) ^ res.S_ell < (2 : ℝ) ^ D := by
      by_contra! hge
      have hmul := mul_le_mul_of_nonneg_right hge (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (-(D : ℤ)))
      linarith
    exact (Nat.lt_iff_add_one_le.mp ((pow_lt_pow_iff_right₀ (by norm_num)).mp hlt_pow)).trans
      (by omega) |> le_of_lt
  have hsteps_real : (res.steps : ℝ) ≤ 97 / ε := by
    have h1 : (res.steps : ℝ) ≤ (rRectFuel ε : ℝ) := by exact_mod_cast hsteps_le
    exact h1.trans (rRect2DFuel_le_div hε0 hε_le)
  have hY_shrink : (2 : ℝ) ^ (- (194 * (D : ℝ) / ε)) * (Y.card : ℝ) ≤ (res.Y_ell.card : ℝ) := by
    have hpow_eq : (((2 : ℝ) ^ (2 * D))⁻¹) ^ res.steps =
        (2 : ℝ) ^ (- (2 * (D : ℝ) * (res.steps : ℝ))) := by
      rw [inv_pow, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
      congr 1
      push_cast
      ring
    have hexp_le : - (194 * (D : ℝ) / ε) ≤ - (2 * (D : ℝ) * (res.steps : ℝ)) := by
      have hmul := mul_le_mul_of_nonneg_left hsteps_real (by positivity : (0 : ℝ) ≤ 2 * (D : ℝ))
      have heq : 2 * (D : ℝ) * (97 / ε) = 194 * (D : ℝ) / ε := by ring
      linarith
    have hrpow_le : (2 : ℝ) ^ (- (194 * (D : ℝ) / ε)) ≤ (((2 : ℝ) ^ (2 * D))⁻¹) ^ res.steps := by
      rw [hpow_eq]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le
    exact (mul_le_mul_of_nonneg_right hrpow_le (Nat.cast_nonneg _)).trans hY_loop
  have hM_bound :
      (M_rect3D ε D)⁻¹ * (2 : ℝ) ^ (-(res.S_ell * D : ℤ)) *
        ((X.card : ℝ) * (Y.card : ℝ)) ≤ (res.X_ell.card : ℝ) * (res.Y_ell.card : ℝ) := by
    have hfac1 : 1 ≤ goodRect3DStepFactor ε D := one_le_goodRect3DStepFactor hε0 hε1.le D
    have hpow_le : (goodRect3DStepFactor ε D) ^ res.steps ≤
        (goodRect3DStepFactor ε D) ^ (rRectFuel ε) :=
      pow_le_pow_right₀ hfac1 hsteps_le
    have h3_le : 3 * (goodRect3DStepFactor ε D) ^ res.steps ≤ M_rect3D ε D := by
      unfold M_rect3D
      linarith
    have hinv_le : (M_rect3D ε D)⁻¹ ≤ (3⁻¹ : ℝ) * ((goodRect3DStepFactor ε D) ^ res.steps)⁻¹ := by
      rw [← mul_inv]
      exact inv_anti₀ (by positivity) h3_le
    have hmul1 :
        (M_rect3D ε D)⁻¹ * (2 : ℝ) ^ (-(res.S_ell * D : ℤ)) ≤
          (3⁻¹ : ℝ) * ((goodRect3DStepFactor ε D) ^ res.steps)⁻¹ *
            (2 : ℝ) ^ (-(res.S_ell * D : ℤ)) :=
      mul_le_mul_of_nonneg_right hinv_le (by positivity)
    have hmul2 := mul_le_mul_of_nonneg_right hmul1
      (by positivity : 0 ≤ (X.card : ℝ) * (Y.card : ℝ))
    exact hmul2.trans harea_loop
  refine ⟨hsubX, hsubY, hneX, hneY, hA_eq, hsteps_le, hS_le_D, hdens_scale,
    hY_shrink, hM_bound, htag_or, hboost_spec, fun hreg => ?_⟩
  rcases hreg_spec hreg with ⟨hcap_lt, hgrid, hmindeg⟩
  have hS_le_47 : res.S_ell ≤ 47 := by
    have hlt48 : (2 : ℝ) ^ res.S_ell * matDensity X Y A < (2 : ℝ) ^ (48 : ℕ) * matDensity X Y A :=
      lt_of_le_of_lt hdens_scale (lt_of_lt_of_le hcap_lt hcap_window)
    have hpow_lt : (2 : ℝ) ^ res.S_ell < (2 : ℝ) ^ (48 : ℕ) :=
      lt_of_mul_lt_mul_right hlt48 hA_pos.le
    have hlt_nat : res.S_ell < 48 := (pow_lt_pow_iff_right₀ (by norm_num)).mp hpow_lt
    omega
  exact ⟨hS_le_47, hcap_lt, hgrid, hmindeg⟩

/-- Inductive invariant for `cappedADecomp3DLoop`: when $\alpha_{\text{cap}} \le 2^{48}\alpha_{\text{low}}$,
every piece $P \in \text{cappedADecomp3DLoop}$ has non-empty $X_{\text{sub}} \subseteq X$,
$Y_{\text{sub}} \subseteq Y$ with $|Y_{\text{sub}}| \ge 2^{-194 D / \varepsilon}|Y|$, and satisfies
the `regular` and `aBoosted` guarantees of Algorithm 4 (`FindRect` / `Decompose2D`; see
`cappedADecomp3DLoop_scale_and_residual_spec` for the `residual` guarantees). -/
theorem cappedADecomp3DLoop_pieces_spec [DecidableEq α] [DecidableEq β]
    (fuel : ℕ) {X : Finset α} {Y : Finset β} {A_rem : α → β → ℝ}
    {ε : ℝ} {D : ℕ} {α_low α_cap : ℝ}
    (S : TwoStageSamplerOracle β ε)
    (hX : X.Nonempty) (hY : Y.Nonempty) (hA : IsBinaryMatrix X Y A_rem)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hD : 2 ≤ D)
    (hwindow : α_cap ≤ (2 : ℝ) ^ (48 : ℕ) * α_low)
    {P : RectPiece α β} (hP : P ∈ cappedADecomp3DLoop fuel X Y A_rem ε D α_low α_cap S) :
    P.X_sub ⊆ X ∧ P.Y_sub ⊆ Y ∧ P.X_sub.Nonempty ∧ P.Y_sub.Nonempty ∧
    IsBinaryMatrix P.X_sub P.Y_sub P.A_sub ∧
    (∀ x y, P.A_sub x y = submatZeroExt P.X_sub P.Y_sub P.A_sub x y) ∧
    (2 : ℝ) ^ (- (194 * (D : ℝ) / ε)) * (Y.card : ℝ) ≤ (P.Y_sub.card : ℝ) ∧
    (P.tag = RectTag.aBoosted →
      α_cap ≤ matDensity P.X_sub P.Y_sub P.A_sub ∧
      (2 : ℝ) ^ P.scale * α_low ≤ matDensity P.X_sub P.Y_sub P.A_sub ∧
      (M_rect3D ε D)⁻¹ * (2 : ℝ) ^ (-(P.scale * D : ℤ)) *
        ((X.card : ℝ) * (Y.card : ℝ)) ≤ (P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ)) ∧
    (P.tag = RectTag.regular →
      P.scale ≤ 47 ∧
      (2 : ℝ) ^ (-(D : ℤ)) < matDensity P.X_sub P.Y_sub P.A_sub ∧
      α_low < matDensity P.X_sub P.Y_sub P.A_sub ∧
      matDensity P.X_sub P.Y_sub P.A_sub < α_cap ∧
      IsGridRegular P.X_sub P.Y_sub P.A_sub ε 2 D ∧
      IsEpsMinDegree P.X_sub P.Y_sub P.A_sub ε ∧
      (M_rect3D ε D)⁻¹ * (2 : ℝ) ^ (-(P.scale * D : ℤ)) *
        ((X.card : ℝ) * (Y.card : ℝ)) ≤ (P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ)) := by
  classical
  have hY_self : (2 : ℝ) ^ (- (194 * (D : ℝ) / ε)) * (Y.card : ℝ) ≤ (Y.card : ℝ) := by
    have hpos_exp : 0 ≤ 194 * (D : ℝ) / ε := by positivity
    have hle1 : (2 : ℝ) ^ (- (194 * (D : ℝ) / ε)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have := mul_le_mul_of_nonneg_right hle1 (Nat.cast_nonneg Y.card)
    linarith
  induction fuel generalizing A_rem with
  | zero =>
    unfold cappedADecomp3DLoop at hP
    simp only [List.mem_singleton] at hP
    subst hP
    refine ⟨Finset.Subset.rfl, Finset.Subset.rfl, hX, hY, ?_, ?_, hY_self,
      (fun h => by cases h), (fun h => by cases h)⟩
    · intro x hx y hy
      simp only [submatZeroExt, hx, hy, and_self, ↓reduceIte]
      exact hA x hx y hy
    · intro x y
      dsimp only
      by_cases hxy : x ∈ X ∧ y ∈ Y <;> simp [submatZeroExt, hxy]
  | succ k ih =>
    unfold cappedADecomp3DLoop at hP
    dsimp only at hP
    split_ifs at hP with hle
    · simp only [List.mem_singleton] at hP
      subst hP
      refine ⟨Finset.Subset.rfl, Finset.Subset.rfl, hX, hY, ?_, ?_, hY_self,
        (fun h => by cases h), (fun h => by cases h)⟩
      · intro x hx y hy
        simp only [submatZeroExt, hx, hy, and_self, ↓reduceIte]
        exact hA x hx y hy
      · intro x y
        dsimp only
        by_cases hxy : x ∈ X ∧ y ∈ Y <;> simp [submatZeroExt, hxy]
    · push_neg at hle
      have hA_gt : (2 : ℝ) ^ (-(D : ℤ)) < matDensity X Y A_rem :=
        lt_of_le_of_lt (le_max_left _ _) hle
      have hα_low_lt : α_low < matDensity X Y A_rem :=
        lt_of_le_of_lt (le_max_right _ _) hle
      have hcap_win : α_cap ≤ (2 : ℝ) ^ (48 : ℕ) * matDensity X Y A_rem :=
        hwindow.trans (mul_le_mul_of_nonneg_left hα_low_lt.le (by positivity))
      simp only [List.mem_cons] at hP
      rcases hP with rfl | hP_tail
      · rcases cappedGoodRect3D_spec S hX hY hA hε0 hε_le hD hA_gt hcap_win with
          ⟨hsubX, hsubY, hneX, hneY, hA_eq, _hsteps, _hS_D, hdens_scale,
            hY_shrink, hM_bound, _htag_or, hboost_spec, hreg_spec⟩
        let res := cappedGoodRect3D X Y A_rem ε D α_cap S
        have hdens_eq : matDensity res.X_ell res.Y_ell res.A_ell =
            matDensity res.X_ell res.Y_ell A_rem := by
          rw [hA_eq, matDensity_submatZeroExt_eq]
        dsimp only
        refine ⟨hsubX, hsubY, hneX, hneY, ?_, ?_, hY_shrink, ?_, ?_⟩
        · intro x hx y hy
          rw [hA_eq]
          simp only [submatZeroExt, hx, hy, and_self, ↓reduceIte]
          exact hA x (hsubX hx) y (hsubY hy)
        · intro x y
          rw [hA_eq]
          by_cases hxy :
              x ∈ (cappedGoodRect3D X Y A_rem ε D α_cap S).X_ell ∧
              y ∈ (cappedGoodRect3D X Y A_rem ε D α_cap S).Y_ell <;>
            simp [submatZeroExt, hxy]
        · intro hboost
          rw [hdens_eq]
          have hscale_low : (2 : ℝ) ^ res.S_ell * α_low ≤ matDensity res.X_ell res.Y_ell A_rem :=
            (mul_le_mul_of_nonneg_left hα_low_lt.le (by positivity)).trans hdens_scale
          exact ⟨hboost_spec hboost, hscale_low, hM_bound⟩
        · intro hreg
          rcases hreg_spec hreg with ⟨hS47, hcap_lt, hgrid, hmindeg⟩
          rw [hdens_eq]
          have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ res.S_ell := one_le_pow₀ (by norm_num)
          have hA_le_res : matDensity X Y A_rem ≤ matDensity res.X_ell res.Y_ell A_rem := by
            have hA_pos : 0 < matDensity X Y A_rem := lt_trans (by positivity) hA_gt
            have : 1 * matDensity X Y A_rem ≤ (2 : ℝ) ^ res.S_ell * matDensity X Y A_rem :=
              mul_le_mul_of_nonneg_right h1 hA_pos.le
            linarith
          exact ⟨hS47, lt_of_lt_of_le hA_gt hA_le_res, lt_of_lt_of_le hα_low_lt hA_le_res,
            hcap_lt, hgrid, hmindeg, hM_bound⟩
      · exact ih (isBinaryMatrix_zeroOutSubrect _ _ hA) hP_tail

open Classical in
/-- **Algorithm 5 (`FindCube`) Lines 5–11 Per-Piece Handler (`processGoodCubePiece`,
§5.2 of `paper.tex`)**:
Given `Y' ⊆ Y`, `Z_curr ⊆ Z`, and a 2D piece `P ∈ cappedADecomp3D`:
- If `P.tag = RectTag.residual` (Piece $\ell = L$): sets `Z_L := Z_curr` when
  $\mathbb{E}[A_L] \le 2^{-D}$ and `Z_L := ∅` otherwise (Line 5 `\label{line:cube-zl}`).
- If `P.tag = RectTag.aBoosted`: checks Line 7 ($\mathbb{E}[B[Y_\ell, Z_{\text{curr}}]] \ge 2\mathbb{E}[B']$),
  recursing on `(P.Y_sub, Z_curr, 0)` if so, and otherwise deferring with `Z_ell := ∅` (Line 8).
- If `P.tag = RectTag.regular`: checks Line 7, Lines 9–10 (`minDegree`), and
  Line 11 (`dyadicSiftConcrete`), recursing if any finds a denser sub-rectangle, and otherwise
  returning the certified slice `⟨P.X_sub, P.Y_sub, Z_ell, P.A_sub, RectTag.regular, P.scale⟩`. -/
noncomputable def processGoodCubePiece [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (Y' : Finset β) (Z_curr : Finset γ) (B : β → γ → ℝ) (ε γ_val : ℝ) (D : ℕ)
    (S : TwoStageSamplerOracle β ε)
    (P : RectPiece α β) : (Finset β × Finset γ × ℕ) ⊕ GoodCubeSlice α β γ :=
  match P.tag with
  | RectTag.residual =>
    let Z_L := if matDensity P.X_sub P.Y_sub P.A_sub ≤ (2 : ℝ) ^ (-(D : ℤ)) then Z_curr else ∅
    Sum.inr ⟨P.X_sub, P.Y_sub, Z_L, P.A_sub, RectTag.residual, P.scale⟩
  | RectTag.aBoosted =>
    if matDensity P.Y_sub Z_curr B ≥ 2 * matDensity Y' Z_curr B then
      Sum.inl (P.Y_sub, Z_curr, 0)
    else
      Sum.inr ⟨P.X_sub, P.Y_sub, ∅, P.A_sub, RectTag.aBoosted, P.scale⟩
  | RectTag.regular =>
    if matDensity P.Y_sub Z_curr B ≥ 2 * matDensity Y' Z_curr B then
      Sum.inl (P.Y_sub, Z_curr, 0)
    else
      let minZ := minDegree Z_curr P.Y_sub (matTranspose B) ε γ_val
      let Z_ell := minZ.1
      if minZ.2 = 2 ∨ matDensity P.Y_sub Z_ell B ≥ (1 + ε * γ_val) * matDensity P.Y_sub Z_curr B then
        Sum.inl (P.Y_sub, Z_ell, 0)
      else
        let siftZ := dyadicSiftConcrete Z_ell P.Y_sub (matTranspose B) ε D S
        if siftZ.1 = "subrect" then
          Sum.inl (siftZ.2.2.1, siftZ.2.1, siftZ.2.2.2)
        else
          Sum.inr ⟨P.X_sub, P.Y_sub, Z_ell, P.A_sub, RectTag.regular, P.scale⟩

open Classical in
/-- Cost-tracked per-piece handler `processGoodCubePieceTracked` in `CostM`. -/
noncomputable def processGoodCubePieceTracked [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (Y' : Finset β) (Z_curr : Finset γ) (B : β → γ → ℝ) (ε γ_val : ℝ) (D : ℕ)
    (S : TwoStageSamplerOracle β ε)
    (P : RectPiece α β) : CostM ((Finset β × Finset γ × ℕ) ⊕ GoodCubeSlice α β γ) :=
  match P.tag with
  | RectTag.residual =>
    let Z_L := if matDensity P.X_sub P.Y_sub P.A_sub ≤ (2 : ℝ) ^ (-(D : ℤ)) then Z_curr else ∅
    scanMatrixTracked P.X_sub P.Y_sub
      (Sum.inr ⟨P.X_sub, P.Y_sub, Z_L, P.A_sub, RectTag.residual, P.scale⟩)
  | RectTag.aBoosted =>
    if matDensity P.Y_sub Z_curr B ≥ 2 * matDensity Y' Z_curr B then
      scanMatrixTracked Y' Z_curr (Sum.inl (P.Y_sub, Z_curr, 0))
    else
      scanMatrixTracked Y' Z_curr
        (Sum.inr ⟨P.X_sub, P.Y_sub, ∅, P.A_sub, RectTag.aBoosted, P.scale⟩)
  | RectTag.regular =>
    if matDensity P.Y_sub Z_curr B ≥ 2 * matDensity Y' Z_curr B then
      scanMatrixTracked Y' Z_curr (Sum.inl (P.Y_sub, Z_curr, 0))
    else
      CostM.bind (minDegreeTracked Z_curr P.Y_sub (matTranspose B) ε γ_val) (fun minZ =>
        let Z_ell := minZ.1
        if minZ.2 = 2 ∨ matDensity P.Y_sub Z_ell B ≥ (1 + ε * γ_val) * matDensity P.Y_sub Z_curr B then
          scanMatrixTracked Y' Z_curr (Sum.inl (P.Y_sub, Z_ell, 0))
        else
          CostM.bind (dyadicSiftConcreteTracked Z_ell P.Y_sub (matTranspose B) ε D S) (fun siftZ =>
            if siftZ.1 = "subrect" then
              scanMatrixTracked Y' Z_curr (Sum.inl (siftZ.2.2.1, siftZ.2.1, siftZ.2.2.2))
            else
              scanMatrixTracked Y' Z_curr
                (Sum.inr ⟨P.X_sub, P.Y_sub, Z_ell, P.A_sub, RectTag.regular, P.scale⟩)))

@[simp]
lemma processGoodCubePieceTracked_fst [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (Y' : Finset β) (Z_curr : Finset γ) (B : β → γ → ℝ) (ε γ_val : ℝ) (D : ℕ)
    (S : TwoStageSamplerOracle β ε) (P : RectPiece α β) :
    (processGoodCubePieceTracked Y' Z_curr B ε γ_val D S P).1 =
      processGoodCubePiece Y' Z_curr B ε γ_val D S P := by
  classical
  unfold processGoodCubePieceTracked processGoodCubePiece
  cases P.tag
  · dsimp only
    by_cases h4a : matDensity P.Y_sub Z_curr B ≥ 2 * matDensity Y' Z_curr B
    · rw [if_pos h4a, if_pos h4a]; rfl
    · rw [if_neg h4a, if_neg h4a]
      simp only [CostM.bind_fst, minDegreeTracked_fst]
      by_cases h4c : (minDegree Z_curr P.Y_sub (matTranspose B) ε γ_val).2 = 2 ∨
          matDensity P.Y_sub (minDegree Z_curr P.Y_sub (matTranspose B) ε γ_val).1 B ≥
            (1 + ε * γ_val) * matDensity P.Y_sub Z_curr B
      · rw [if_pos h4c, if_pos h4c]; rfl
      · rw [if_neg h4c, if_neg h4c]
        simp only [CostM.bind_fst, dyadicSiftConcreteTracked_fst]
        by_cases h4d :
            (dyadicSiftConcrete (minDegree Z_curr P.Y_sub (matTranspose B) ε γ_val).1
              P.Y_sub (matTranspose B) ε D S).1 = "subrect"
        · rw [if_pos h4d, if_pos h4d]; rfl
        · rw [if_neg h4d, if_neg h4d]; rfl
  · dsimp only
    by_cases h4a : matDensity P.Y_sub Z_curr B ≥ 2 * matDensity Y' Z_curr B
    · rw [if_pos h4a, if_pos h4a]; rfl
    · rw [if_neg h4a, if_neg h4a]; rfl
  · rfl

/-- Iterates `processGoodCubePiece` across all pieces `L : List (RectPiece α β)`. -/
noncomputable def processGoodCubePieces [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (Y' : Finset β) (Z_curr : Finset γ) (B : β → γ → ℝ) (ε γ_val : ℝ) (D : ℕ)
    (S : TwoStageSamplerOracle β ε) :
    List (RectPiece α β) → (Finset β × Finset γ × ℕ) ⊕ List (GoodCubeSlice α β γ)
  | [] => Sum.inr []
  | P :: rest =>
    match processGoodCubePiece Y' Z_curr B ε γ_val D S P with
    | Sum.inl step => Sum.inl step
    | Sum.inr sl =>
      match processGoodCubePieces Y' Z_curr B ε γ_val D S rest with
      | Sum.inl step => Sum.inl step
      | Sum.inr sls => Sum.inr (sl :: sls)

/-- Cost-tracked list loop `processGoodCubePiecesTracked` in `CostM`. -/
noncomputable def processGoodCubePiecesTracked [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (Y' : Finset β) (Z_curr : Finset γ) (B : β → γ → ℝ) (ε γ_val : ℝ) (D : ℕ)
    (S : TwoStageSamplerOracle β ε) :
    List (RectPiece α β) → CostM ((Finset β × Finset γ × ℕ) ⊕ List (GoodCubeSlice α β γ))
  | [] => retTracked (Sum.inr [])
  | P :: rest =>
    CostM.bind (processGoodCubePieceTracked Y' Z_curr B ε γ_val D S P) (fun r1 =>
      match r1 with
      | Sum.inl step => retTracked (Sum.inl step)
      | Sum.inr sl =>
        CostM.bind (processGoodCubePiecesTracked Y' Z_curr B ε γ_val D S rest) (fun r2 =>
          match r2 with
          | Sum.inl step => retTracked (Sum.inl step)
          | Sum.inr sls => retTracked (Sum.inr (sl :: sls))))

@[simp]
lemma processGoodCubePiecesTracked_fst [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (Y' : Finset β) (Z_curr : Finset γ) (B : β → γ → ℝ) (ε γ_val : ℝ) (D : ℕ)
    (S : TwoStageSamplerOracle β ε) (L : List (RectPiece α β)) :
    (processGoodCubePiecesTracked Y' Z_curr B ε γ_val D S L).1 =
      processGoodCubePieces Y' Z_curr B ε γ_val D S L := by
  induction L with
  | nil => rfl
  | cons P rest ih =>
    unfold processGoodCubePiecesTracked processGoodCubePieces
    rw [CostM.bind_fst, processGoodCubePieceTracked_fst]
    cases processGoodCubePiece Y' Z_curr B ε γ_val D S P with
    | inl step => rfl
    | inr sl =>
      rw [CostM.bind_fst, ih]
      cases processGoodCubePieces Y' Z_curr B ε γ_val D S rest <;> rfl

open Classical in
/-- **Algorithm 5 (`FindCube`) Inner Loop (`cappedGoodCubeLoop`, §5.2 of `paper.tex`)**:
Executes Line 1 (`bBoost` check), Lines 2–3 (`minDegree` on $B[Y_{\text{curr}}, Z_{\text{curr}}]$),
Line 4 (`cappedADecomp3D` on $A[X, Y']$), and Lines 5–12 (`processGoodCubePieces`),
accumulating dyadic $B$-scale $S_B$ and step count bottom-up. -/
noncomputable def cappedGoodCubeLoop [DecidableEq α] [DecidableEq β] [DecidableEq γ] :
    ℕ → Finset α → Finset β → Finset γ → (α → β → ℝ) → (β → γ → ℝ) →
    (ε : ℝ) → ℝ → ℕ → ℝ → ℝ → TwoStageSamplerOracle β ε → GoodCubeResult α β γ
  | 0, X, Y_curr, Z_curr, A, B, _ε, _γ_val, _D, α_cap, _β_init, _S =>
    { mode       := CubeMode.bBoost
      X_star     := X
      Y_star     := Y_curr
      Z_star     := Z_curr
      Y_prime    := Y_curr
      A_prime    := submatZeroExt X Y_curr A
      B_prime    := submatZeroExt Y_curr Z_curr B
      alpha_star := α_cap
      S_B        := 0
      steps      := 0
      slices     := [] }
  | fuel + 1, X, Y_curr, Z_curr, A, B, ε, γ_val, D, α_cap, β_init, S =>
    if matDensity Y_curr Z_curr B ≥ 16 * β_init then
      { mode       := CubeMode.bBoost
        X_star     := X
        Y_star     := Y_curr
        Z_star     := Z_curr
        Y_prime    := Y_curr
        A_prime    := submatZeroExt X Y_curr A
        B_prime    := submatZeroExt Y_curr Z_curr B
        alpha_star := α_cap
        S_B        := 0
        steps      := 0
        slices     := [] }
    else
      let minB := minDegree Y_curr Z_curr B (ε * γ_val / 2) (1 / 2)
      let Y' := minB.1
      if minB.2 = 2 ∨ matDensity Y' Z_curr B ≥ (1 + ε * γ_val / 4) * matDensity Y_curr Z_curr B then
        let sub := cappedGoodCubeLoop fuel X Y' Z_curr A B ε γ_val D α_cap β_init S
        { sub with steps := sub.steps + 1 }
      else
        let piecesA := cappedADecomp3D X Y' A ε D (cLow3D * α_cap) (cCap3D * α_cap) S
        match processGoodCubePieces Y' Z_curr B ε γ_val D S piecesA with
        | Sum.inl (Y_next, Z_next, s_step) =>
          let sub := cappedGoodCubeLoop fuel X Y_next Z_next A B ε γ_val D α_cap β_init S
          { sub with S_B := sub.S_B + s_step, steps := sub.steps + 1 }
        | Sum.inr slices =>
          { mode       := CubeMode.normal
            X_star     := X
            Y_star     := Y'
            Z_star     := Z_curr
            Y_prime    := Y'
            A_prime    := submatZeroExt X Y' A
            B_prime    := submatZeroExt Y' Z_curr B
            alpha_star := α_cap
            S_B        := 0
            steps      := 0
            slices     := slices }

open Classical in
/-- Cost-tracked inner loop `cappedGoodCubeLoopTracked` in `CostM`. -/
noncomputable def cappedGoodCubeLoopTracked [DecidableEq α] [DecidableEq β] [DecidableEq γ] :
    ℕ → Finset α → Finset β → Finset γ → (α → β → ℝ) → (β → γ → ℝ) →
    (ε : ℝ) → ℝ → ℕ → ℝ → ℝ → TwoStageSamplerOracle β ε → CostM (GoodCubeResult α β γ)
  | 0, X, Y_curr, Z_curr, A, B, _ε, _γ_val, _D, α_cap, _β_init, _S =>
    scanMatrixPairTracked X Y_curr Z_curr
      { mode       := CubeMode.bBoost
        X_star     := X
        Y_star     := Y_curr
        Z_star     := Z_curr
        Y_prime    := Y_curr
        A_prime    := submatZeroExt X Y_curr A
        B_prime    := submatZeroExt Y_curr Z_curr B
        alpha_star := α_cap
        S_B        := 0
        steps      := 0
        slices     := [] }
  | fuel + 1, X, Y_curr, Z_curr, A, B, ε, γ_val, D, α_cap, β_init, S =>
    if matDensity Y_curr Z_curr B ≥ 16 * β_init then
      scanMatrixPairTracked X Y_curr Z_curr
        { mode       := CubeMode.bBoost
          X_star     := X
          Y_star     := Y_curr
          Z_star     := Z_curr
          Y_prime    := Y_curr
          A_prime    := submatZeroExt X Y_curr A
          B_prime    := submatZeroExt Y_curr Z_curr B
          alpha_star := α_cap
          S_B        := 0
          steps      := 0
          slices     := [] }
    else
      CostM.bind (minDegreeTracked Y_curr Z_curr B (ε * γ_val / 2) (1 / 2)) (fun minB =>
        let Y' := minB.1
        if minB.2 = 2 ∨ matDensity Y' Z_curr B ≥ (1 + ε * γ_val / 4) * matDensity Y_curr Z_curr B then
          CostM.bind (cappedGoodCubeLoopTracked fuel X Y' Z_curr A B ε γ_val D α_cap β_init S)
            (fun sub =>
              scanMatrixPairTracked X Y_curr Z_curr { sub with steps := sub.steps + 1 })
        else
          CostM.bind (cappedADecomp3DTracked X Y' A ε D (cLow3D * α_cap) (cCap3D * α_cap) S)
            (fun piecesA =>
              CostM.bind (processGoodCubePiecesTracked Y' Z_curr B ε γ_val D S piecesA)
                (fun procRes =>
                  match procRes with
                  | Sum.inl (Y_next, Z_next, s_step) =>
                    CostM.bind
                      (cappedGoodCubeLoopTracked fuel X Y_next Z_next A B ε γ_val D α_cap β_init S)
                      (fun sub =>
                        scanMatrixPairTracked X Y_curr Z_curr
                          { sub with S_B := sub.S_B + s_step, steps := sub.steps + 1 })
                  | Sum.inr slices =>
                    scanMatrixPairTracked X Y_curr Z_curr
                      { mode       := CubeMode.normal
                        X_star     := X
                        Y_star     := Y'
                        Z_star     := Z_curr
                        Y_prime    := Y'
                        A_prime    := submatZeroExt X Y' A
                        B_prime    := submatZeroExt Y' Z_curr B
                        alpha_star := α_cap
                        S_B        := 0
                        steps      := 0
                        slices     := slices })))

@[simp]
lemma cappedGoodCubeLoopTracked_fst [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (fuel : ℕ) (X : Finset α) (Y_curr : Finset β) (Z_curr : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    (ε γ_val : ℝ) (D : ℕ) (α_cap β_init : ℝ) (S : TwoStageSamplerOracle β ε) :
    (cappedGoodCubeLoopTracked fuel X Y_curr Z_curr A B ε γ_val D α_cap β_init S).1 =
      cappedGoodCubeLoop fuel X Y_curr Z_curr A B ε γ_val D α_cap β_init S := by
  classical
  induction fuel generalizing Y_curr Z_curr with
  | zero => rfl
  | succ k ih =>
    unfold cappedGoodCubeLoopTracked cappedGoodCubeLoop
    dsimp only
    by_cases hboost : matDensity Y_curr Z_curr B ≥ 16 * β_init
    · rw [if_pos hboost, if_pos hboost]; rfl
    · rw [if_neg hboost, if_neg hboost]
      simp only [CostM.bind_fst, minDegreeTracked_fst]
      by_cases hstep1 : (minDegree Y_curr Z_curr B (ε * γ_val / 2) (1 / 2)).2 = 2 ∨
          matDensity (minDegree Y_curr Z_curr B (ε * γ_val / 2) (1 / 2)).1 Z_curr B ≥
            (1 + ε * γ_val / 4) * matDensity Y_curr Z_curr B
      · rw [if_pos hstep1, if_pos hstep1]
        simp only [CostM.bind_fst, scanMatrixPairTracked_fst, ih]
      · rw [if_neg hstep1, if_neg hstep1]
        simp only [CostM.bind_fst, cappedADecomp3DTracked_fst, processGoodCubePiecesTracked_fst]
        cases processGoodCubePieces (minDegree Y_curr Z_curr B (ε * γ_val / 2) (1 / 2)).1
          Z_curr B ε γ_val D S
          (cappedADecomp3D X (minDegree Y_curr Z_curr B (ε * γ_val / 2) (1 / 2)).1
            A ε D (cLow3D * α_cap) (cCap3D * α_cap) S) with
        | inl step =>
          simp only [CostM.bind_fst, scanMatrixPairTracked_fst, ih]
        | inr slices =>
          rfl

/-- **Algorithm 5 (`FindCube`) (`cappedGoodCube`, §5.2 of `paper.tex`)**:
Invokes `cappedGoodCubeLoop` with Bernoulli iteration budget `rCubeFuel ε γ_val`. -/
noncomputable def cappedGoodCube [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    (ε γ_val : ℝ) (D : ℕ) (α_cap β_init : ℝ) (S : TwoStageSamplerOracle β ε) :
    GoodCubeResult α β γ :=
  cappedGoodCubeLoop (rCubeFuel ε γ_val) X Y Z A B ε γ_val D α_cap β_init S

/-- Tracked `CostM` implementation of Algorithm 5 (`FindCube`) (`cappedGoodCubeTracked`). -/
noncomputable def cappedGoodCubeTracked [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    (ε γ_val : ℝ) (D : ℕ) (α_cap β_init : ℝ) (S : TwoStageSamplerOracle β ε) :
    CostM (GoodCubeResult α β γ) :=
  cappedGoodCubeLoopTracked (rCubeFuel ε γ_val) X Y Z A B ε γ_val D α_cap β_init S

@[simp]
lemma cappedGoodCubeTracked_fst [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    (ε γ_val : ℝ) (D : ℕ) (α_cap β_init : ℝ) (S : TwoStageSamplerOracle β ε) :
    (cappedGoodCubeTracked X Y Z A B ε γ_val D α_cap β_init S).1 =
      cappedGoodCube X Y Z A B ε γ_val D α_cap β_init S :=
  cappedGoodCubeLoopTracked_fst (rCubeFuel ε γ_val) X Y Z A B ε γ_val D α_cap β_init S

lemma processGoodCubePieceTracked_snd_le [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {X : Finset α} {Y Y' : Finset β} {Z Z_curr : Finset γ}
    (B : β → γ → ℝ) (ε γ_val : ℝ) (D : ℕ) (S : TwoStageSamplerOracle β ε)
    (P : RectPiece α β)
    (hPX : P.X_sub.card ≤ X.card) (hPY : P.Y_sub.card ≤ Y.card)
    (hY' : Y'.card ≤ Y.card) (hZ_curr : Z_curr.card ≤ Z.card) :
    (processGoodCubePieceTracked Y' Z_curr B ε γ_val D S P).2 ≤
      (X.card + Y.card + Z.card + 2) ^ 2 *
        (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 6) := by
  classical
  unfold processGoodCubePieceTracked
  have hbase_XY : P.X_sub.card * P.Y_sub.card + 1 ≤ (X.card + Y.card + Z.card + 2) ^ 2 := by
    nlinarith
  have hbase_YZ : Y'.card * Z_curr.card + 1 ≤ (X.card + Y.card + Z.card + 2) ^ 2 := by
    nlinarith
  cases P.tag
  · -- `RectTag.regular`
    dsimp only
    split_ifs with h4a
    · simp only [scanMatrixTracked_snd]
      exact hbase_YZ.trans (Nat.le_mul_of_pos_right _ (by omega))
    · rw [CostM.bind_snd, minDegreeTracked_fst]
      have hmin_cost := minDegreeTracked_snd_le Z_curr P.Y_sub (matTranspose B) ε γ_val
      have hmin_sub : (minDegree Z_curr P.Y_sub (matTranspose B) ε γ_val).1 ⊆ Z_curr :=
        minDegree_fst_subset Z_curr P.Y_sub (matTranspose B) ε γ_val
      have hZ_ell_card : (minDegree Z_curr P.Y_sub (matTranspose B) ε γ_val).1.card ≤ Z.card :=
        (Finset.card_le_card hmin_sub).trans hZ_curr
      have hmin_le :
          (minDegreeTracked Z_curr P.Y_sub (matTranspose B) ε γ_val).2 +
            (Y'.card * Z_curr.card + 1) ≤
            (X.card + Y.card + Z.card + 2) ^ 2 * 4 := by
        nlinarith
      split_ifs with h4c
      · rw [scanMatrixTracked_snd]
        exact hmin_le.trans (Nat.mul_le_mul_left _ (by omega))
      · rw [CostM.bind_snd, dyadicSiftConcreteTracked_fst]
        have hsift_cost := dyadicSiftConcreteTracked_snd_le
          (minDegree Z_curr P.Y_sub (matTranspose B) ε γ_val).1 P.Y_sub (matTranspose B) ε D S
        have hprod_le :
            ((minDegree Z_curr P.Y_sub (matTranspose B) ε γ_val).1.card + P.Y_sub.card + 2) ^ 2 ≤
              (X.card + Y.card + Z.card + 2) ^ 2 := by
          nlinarith
        have hsift_le :
            (dyadicSiftConcreteTracked
              (minDegree Z_curr P.Y_sub (matTranspose B) ε γ_val).1 P.Y_sub (matTranspose B) ε D S).2 ≤
              (X.card + Y.card + Z.card + 2) ^ 2 *
                (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * (D + 1)) :=
          hsift_cost.trans (Nat.mul_le_mul_right _ hprod_le)
        split_ifs <;>
        · rw [scanMatrixTracked_snd]
          linarith
  · -- `RectTag.aBoosted`
    dsimp only
    split_ifs <;>
    · simp only [scanMatrixTracked_snd]
      exact hbase_YZ.trans (Nat.le_mul_of_pos_right _ (by omega))
  · -- `RectTag.residual`
    simp only [scanMatrixTracked_snd]
    exact hbase_XY.trans (Nat.le_mul_of_pos_right _ (by omega))

lemma processGoodCubePiecesTracked_snd_le [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {X : Finset α} {Y Y' : Finset β} {Z Z_curr : Finset γ}
    (B : β → γ → ℝ) (ε γ_val : ℝ) (D : ℕ) (S : TwoStageSamplerOracle β ε)
    (L : List (RectPiece α β))
    (hY' : Y'.card ≤ Y.card) (hZ_curr : Z_curr.card ≤ Z.card)
    (hL : ∀ P ∈ L, P.X_sub.card ≤ X.card ∧ P.Y_sub.card ≤ Y.card) :
    (processGoodCubePiecesTracked Y' Z_curr B ε γ_val D S L).2 ≤
      (L.length + 1) * ((X.card + Y.card + Z.card + 2) ^ 2 *
        (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 7)) := by
  classical
  induction L with
  | nil =>
    unfold processGoodCubePiecesTracked
    simp only [retTracked_snd, List.length_nil, zero_add, one_mul]
    have h1_le : 1 ≤ (X.card + Y.card + Z.card + 2) ^ 2 := Nat.one_le_pow 2 _ (by omega)
    have : 1 ≤ (X.card + Y.card + Z.card + 2) ^ 2 * 1 := by omega
    exact this.trans (Nat.mul_le_mul_left _ (by omega))
  | cons P rest ih =>
    unfold processGoodCubePiecesTracked
    rw [CostM.bind_snd, processGoodCubePieceTracked_fst]
    have hP := hL P List.mem_cons_self
    have hP_cost := processGoodCubePieceTracked_snd_le B ε γ_val D S P hP.1 hP.2 hY' hZ_curr
    have hrest_ih := ih (fun Q hQ => hL Q (List.mem_cons_of_mem P hQ))
    have h1_le : 1 ≤ (X.card + Y.card + Z.card + 2) ^ 2 := Nat.one_le_pow 2 _ (by omega)
    have hP_plus_1 :
        (processGoodCubePieceTracked Y' Z_curr B ε γ_val D S P).2 + 1 ≤
          (X.card + Y.card + Z.card + 2) ^ 2 *
            (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 7) := by
      linarith
    cases processGoodCubePiece Y' Z_curr B ε γ_val D S P with
    | inl step =>
      rw [retTracked_snd]
      simp only [List.length_cons]
      have hmul :
          (X.card + Y.card + Z.card + 2) ^ 2 *
            (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 7) ≤
          (rest.length + 1 + 1) * ((X.card + Y.card + Z.card + 2) ^ 2 *
            (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 7)) :=
        Nat.le_mul_of_pos_left _ (by omega)
      exact hP_plus_1.trans hmul
    | inr sl =>
      rw [CostM.bind_snd]
      simp only [List.length_cons]
      cases (processGoodCubePiecesTracked Y' Z_curr B ε γ_val D S rest).1 <;>
      · rw [retTracked_snd]
        linarith

/-- Per-step operation count factor for `cappedGoodCubeLoopTracked`. -/
noncomputable def goodCubeStepCostFactor (c k : ℕ) (ε : ℝ) (D : ℕ) : ℕ :=
  (rDecompAFuel ε D + 2) * (rRectFuel ε + 3) *
    (concreteApproxGridNormCostFactor c k ε D + 2 * D + 7)

lemma processGoodCubePiece_inl_subset [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {Y' Y_next : Finset β} {Z_curr Z_next : Finset γ} {s_step : ℕ}
    {B : β → γ → ℝ} {ε γ_val : ℝ} {D : ℕ} {S : TwoStageSamplerOracle β ε}
    {P : RectPiece α β}
    (hPY : P.Y_sub ⊆ Y')
    (hinl : processGoodCubePiece Y' Z_curr B ε γ_val D S P = Sum.inl (Y_next, Z_next, s_step)) :
    Y_next ⊆ Y' ∧ Z_next ⊆ Z_curr := by
  classical
  unfold processGoodCubePiece at hinl
  cases htag : P.tag <;> rw [htag] at hinl
  · -- `RectTag.regular`
    dsimp only at hinl
    split_ifs at hinl with h4a h4c h4d
    · cases hinl
      exact ⟨hPY, Finset.Subset.rfl⟩
    · cases hinl
      exact ⟨hPY, minDegree_fst_subset Z_curr P.Y_sub (matTranspose B) ε γ_val⟩
    · cases hinl
      have hmin_sub := minDegree_fst_subset Z_curr P.Y_sub (matTranspose B) ε γ_val
      have hsift_sub := dyadicSift_subset
        (minDegree Z_curr P.Y_sub (matTranspose B) ε γ_val).1 P.Y_sub (matTranspose B) ε D
        (concreteApproxGridNormV S
          (minDegree Z_curr P.Y_sub (matTranspose B) ε γ_val).1 P.Y_sub (matTranspose B) D)
      exact ⟨hsift_sub.2.trans hPY, hsift_sub.1.trans hmin_sub⟩
  · -- `RectTag.aBoosted`
    dsimp only at hinl
    split_ifs at hinl with h4a
    · cases hinl
      exact ⟨hPY, Finset.Subset.rfl⟩
  · -- `RectTag.residual`
    cases hinl

lemma processGoodCubePieces_inl_subset [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {Y' Y_next : Finset β} {Z_curr Z_next : Finset γ} {s_step : ℕ}
    {B : β → γ → ℝ} {ε γ_val : ℝ} {D : ℕ} {S : TwoStageSamplerOracle β ε}
    {L : List (RectPiece α β)}
    (hL : ∀ P ∈ L, P.Y_sub ⊆ Y')
    (hinl : processGoodCubePieces Y' Z_curr B ε γ_val D S L = Sum.inl (Y_next, Z_next, s_step)) :
    Y_next ⊆ Y' ∧ Z_next ⊆ Z_curr := by
  induction L with
  | nil => cases hinl
  | cons P rest ih =>
    unfold processGoodCubePieces at hinl
    cases hP : processGoodCubePiece Y' Z_curr B ε γ_val D S P with
    | inl step =>
      rw [hP] at hinl
      cases hinl
      exact processGoodCubePiece_inl_subset (hL P List.mem_cons_self) hP
    | inr sl =>
      rw [hP] at hinl
      cases hrest : processGoodCubePieces Y' Z_curr B ε γ_val D S rest with
      | inl step =>
        rw [hrest] at hinl
        cases hinl
        exact ih (fun Q hQ => hL Q (List.mem_cons_of_mem P hQ)) hrest
      | inr sls =>
        rw [hrest] at hinl
        cases hinl

lemma cappedADecomp3DLoop_mem_subset_raw [DecidableEq α] [DecidableEq β]
    (fuel : ℕ) (X : Finset α) (Y : Finset β) (A_rem : α → β → ℝ)
    (ε : ℝ) (D : ℕ) (α_low α_cap : ℝ) (S : TwoStageSamplerOracle β ε)
    {P : RectPiece α β} (hP : P ∈ cappedADecomp3DLoop fuel X Y A_rem ε D α_low α_cap S) :
    P.X_sub ⊆ X ∧ P.Y_sub ⊆ Y := by
  classical
  induction fuel generalizing A_rem with
  | zero =>
    unfold cappedADecomp3DLoop at hP
    simp only [List.mem_singleton] at hP
    subst hP
    exact ⟨Finset.Subset.rfl, Finset.Subset.rfl⟩
  | succ k ih =>
    unfold cappedADecomp3DLoop at hP
    dsimp only at hP
    split_ifs at hP with hle
    · simp only [List.mem_singleton] at hP
      subst hP
      exact ⟨Finset.Subset.rfl, Finset.Subset.rfl⟩
    · simp only [List.mem_cons] at hP
      rcases hP with rfl | hP_tail
      · unfold cappedGoodRect3D
        have hsub := cappedGoodRect3DLoop_subset (rRectFuel ε) X Y A_rem ε D α_cap S
        exact ⟨hsub.1, hsub.2.1⟩
      · exact ih _ hP_tail

lemma cappedGoodCubeLoopTracked_snd_le [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (fuel : ℕ) (X : Finset α) {Y Y_curr : Finset β} {Z Z_curr : Finset γ}
    (A : α → β → ℝ) (B : β → γ → ℝ)
    (ε γ_val : ℝ) (D : ℕ) (α_cap β_init : ℝ) (S : TwoStageSamplerOracle β ε)
    (hY_curr : Y_curr.card ≤ Y.card) (hZ_curr : Z_curr.card ≤ Z.card) :
    (cappedGoodCubeLoopTracked fuel X Y_curr Z_curr A B ε γ_val D α_cap β_init S).2 ≤
      (fuel + 1) *
        ((X.card + Y.card + Z.card + 2) ^ 2 * goodCubeStepCostFactor S.c S.k ε D) := by
  classical
  induction fuel generalizing Y_curr Z_curr with
  | zero =>
    unfold cappedGoodCubeLoopTracked
    simp only [scanMatrixPairTracked_snd, zero_add, one_mul]
    have hbase : X.card * Y_curr.card + Y_curr.card * Z_curr.card + 1 ≤
        (X.card + Y.card + Z.card + 2) ^ 2 * 1 := by nlinarith
    have hfac : 1 ≤ goodCubeStepCostFactor S.c S.k ε D := by
      unfold goodCubeStepCostFactor
      exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    exact hbase.trans (Nat.mul_le_mul_left _ hfac)
  | succ k ih =>
    unfold cappedGoodCubeLoopTracked
    dsimp only
    have hbase : X.card * Y_curr.card + Y_curr.card * Z_curr.card + 1 ≤
        (X.card + Y.card + Z.card + 2) ^ 2 := by nlinarith
    have hfac_pos : 1 ≤ goodCubeStepCostFactor S.c S.k ε D := by
      unfold goodCubeStepCostFactor
      exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    split_ifs with hboost
    · simp only [scanMatrixPairTracked_snd]
      have h1 := hbase.trans (Nat.le_mul_of_pos_right _ hfac_pos)
      exact h1.trans (Nat.le_mul_of_pos_left _ (by omega))
    · rw [CostM.bind_snd, minDegreeTracked_fst]
      have hmin_cost := minDegreeTracked_snd_le Y_curr Z_curr B (ε * γ_val / 2) (1 / 2)
      have hmin_sub : (minDegree Y_curr Z_curr B (ε * γ_val / 2) (1 / 2)).1 ⊆ Y_curr :=
        minDegree_fst_subset Y_curr Z_curr B (ε * γ_val / 2) (1 / 2)
      set Y' := (minDegree Y_curr Z_curr B (ε * γ_val / 2) (1 / 2)).1
      have hY'_card : Y'.card ≤ Y.card := (Finset.card_le_card hmin_sub).trans hY_curr
      have hmin_step :
          (minDegreeTracked Y_curr Z_curr B (ε * γ_val / 2) (1 / 2)).2 +
            (X.card * Y_curr.card + Y_curr.card * Z_curr.card + 1) ≤
            (X.card + Y.card + Z.card + 2) ^ 2 * 4 := by nlinarith
      split_ifs with hstep1
      · rw [CostM.bind_snd, scanMatrixPairTracked_snd]
        have hrec := ih hY'_card hZ_curr
        have hstep_le :
            (minDegreeTracked Y_curr Z_curr B (ε * γ_val / 2) (1 / 2)).2 +
              (X.card * Y_curr.card + Y_curr.card * Z_curr.card + 1) ≤
              (X.card + Y.card + Z.card + 2) ^ 2 * goodCubeStepCostFactor S.c S.k ε D := by
          have h4_le : 4 ≤ goodCubeStepCostFactor S.c S.k ε D := by
            unfold goodCubeStepCostFactor
            have h12 : 6 ≤ (rDecompAFuel ε D + 2) * (rRectFuel ε + 3) :=
              Nat.mul_le_mul (by omega : 2 ≤ rDecompAFuel ε D + 2) (by omega : 3 ≤ rRectFuel ε + 3)
            have h3 : 7 ≤ concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 7 := by omega
            exact le_trans (by omega : 4 ≤ 6 * 7) (Nat.mul_le_mul h12 h3)
          exact hmin_step.trans (Nat.mul_le_mul_left _ h4_le)
        have hsucc :
            (k + 1 + 1) * ((X.card + Y.card + Z.card + 2) ^ 2 * goodCubeStepCostFactor S.c S.k ε D) =
              (k + 1) * ((X.card + Y.card + Z.card + 2) ^ 2 * goodCubeStepCostFactor S.c S.k ε D) +
                (X.card + Y.card + Z.card + 2) ^ 2 * goodCubeStepCostFactor S.c S.k ε D :=
          Nat.succ_mul (k + 1) _
        linarith
      · rw [CostM.bind_snd, cappedADecomp3DTracked_fst,
          CostM.bind_snd, processGoodCubePiecesTracked_fst]
        set piecesA := cappedADecomp3D X Y' A ε D (cLow3D * α_cap) (cCap3D * α_cap) S
        have hdecomp_cost := cappedADecomp3DTracked_snd_le
          X Y' A ε D (cLow3D * α_cap) (cCap3D * α_cap) S
        have hquad_XY : (X.card + Y'.card + 2) ^ 2 ≤ (X.card + Y.card + Z.card + 2) ^ 2 := by
          nlinarith
        have hdecomp_le :
            (cappedADecomp3DTracked X Y' A ε D (cLow3D * α_cap) (cCap3D * α_cap) S).2 ≤
              (rDecompAFuel ε D + 1) * (rRectFuel ε + 2) *
                ((X.card + Y.card + Z.card + 2) ^ 2 *
                  (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 7)) := by
          have h1 :
              (X.card + Y'.card + 2) ^ 2 *
                (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 6) ≤
              (X.card + Y.card + Z.card + 2) ^ 2 *
                (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 7) :=
            Nat.mul_le_mul hquad_XY (by omega)
          have h2 := Nat.mul_le_mul_left (rDecompAFuel ε D + 1)
            (Nat.mul_le_mul_left (rRectFuel ε + 2) h1)
          have h3 := hdecomp_cost.trans h2
          have hmul_assoc :
              (rDecompAFuel ε D + 1) *
                ((rRectFuel ε + 2) *
                  ((X.card + Y.card + Z.card + 2) ^ 2 *
                     (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 7))) =
              (rDecompAFuel ε D + 1) * (rRectFuel ε + 2) *
                ((X.card + Y.card + Z.card + 2) ^ 2 *
                  (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 7)) := by
            ring
          omega
        have hpieces_len : piecesA.length ≤ rDecompAFuel ε D + 1 :=
          cappedADecomp3DLoop_length_le (rDecompAFuel ε D) X Y' A ε D
            (cLow3D * α_cap) (cCap3D * α_cap) S
        have hpieces_sub : ∀ P ∈ piecesA, P.X_sub ⊆ X ∧ P.Y_sub ⊆ Y' :=
          fun P hP => cappedADecomp3DLoop_mem_subset_raw
            (rDecompAFuel ε D) X Y' A ε D (cLow3D * α_cap) (cCap3D * α_cap) S hP
        have hpieces_cards : ∀ P ∈ piecesA, P.X_sub.card ≤ X.card ∧ P.Y_sub.card ≤ Y.card := by
          intro P hP
          rcases hpieces_sub P hP with ⟨hPX, hPY⟩
          exact ⟨Finset.card_le_card hPX, (Finset.card_le_card hPY).trans hY'_card⟩
        have hproc_cost := processGoodCubePiecesTracked_snd_le
          B ε γ_val D S piecesA hY'_card hZ_curr hpieces_cards
        have hproc_le :
            (processGoodCubePiecesTracked Y' Z_curr B ε γ_val D S piecesA).2 ≤
              (rDecompAFuel ε D + 2) *
                ((X.card + Y.card + Z.card + 2) ^ 2 *
                  (concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 7)) :=
          hproc_cost.trans (Nat.mul_le_mul_right _ (by omega))
        have htotal_step :
            (minDegreeTracked Y_curr Z_curr B (ε * γ_val / 2) (1 / 2)).2 +
              (cappedADecomp3DTracked X Y' A ε D (cLow3D * α_cap) (cCap3D * α_cap) S).2 +
              (processGoodCubePiecesTracked Y' Z_curr B ε γ_val D S piecesA).2 +
              (X.card * Y_curr.card + Y_curr.card * Z_curr.card + 1) ≤
              (X.card + Y.card + Z.card + 2) ^ 2 * goodCubeStepCostFactor S.c S.k ε D := by
          unfold goodCubeStepCostFactor
          set Q := (X.card + Y.card + Z.card + 2) ^ 2
          set F := concreteApproxGridNormCostFactor S.c S.k ε D + 2 * D + 7
          have hF4 : 4 ≤ F := by omega
          have hmin_QF :
              (minDegreeTracked Y_curr Z_curr B (ε * γ_val / 2) (1 / 2)).2 +
                (X.card * Y_curr.card + Y_curr.card * Z_curr.card + 1) ≤ 1 * (Q * F) := by
            rw [one_mul]
            exact hmin_step.trans (Nat.mul_le_mul_left Q hF4)
          have hcoeff :
              1 + (rDecompAFuel ε D + 1) * (rRectFuel ε + 2) + (rDecompAFuel ε D + 2) ≤
                (rDecompAFuel ε D + 2) * (rRectFuel ε + 3) := by
            have hid :
                (rDecompAFuel ε D + 2) * (rRectFuel ε + 3) =
                  (rDecompAFuel ε D + 1) * (rRectFuel ε + 2) + (rDecompAFuel ε D + 2) +
                    rRectFuel ε + 2 := by ring
            omega
          have hmul_QF := Nat.mul_le_mul_right (Q * F) hcoeff
          have hdistrib :
              (1 + (rDecompAFuel ε D + 1) * (rRectFuel ε + 2) + (rDecompAFuel ε D + 2)) * (Q * F) =
                1 * (Q * F) + (rDecompAFuel ε D + 1) * (rRectFuel ε + 2) * (Q * F) +
                  (rDecompAFuel ε D + 2) * (Q * F) := by ring
          have hrhs_QF :
              (rDecompAFuel ε D + 2) * (rRectFuel ε + 3) * (Q * F) =
                Q * ((rDecompAFuel ε D + 2) * (rRectFuel ε + 3) * F) := by ring
          omega
        cases hproc_eq : processGoodCubePieces Y' Z_curr B ε γ_val D S piecesA with
        | inl step =>
          rcases step with ⟨Y_next, Z_next, s_step⟩
          rw [CostM.bind_snd, scanMatrixPairTracked_snd]
          have hsub_next := processGoodCubePieces_inl_subset
            (fun P hP => (hpieces_sub P hP).2) hproc_eq
          have hY_next_card : Y_next.card ≤ Y.card :=
            (Finset.card_le_card hsub_next.1).trans hY'_card
          have hZ_next_card : Z_next.card ≤ Z.card :=
            (Finset.card_le_card hsub_next.2).trans hZ_curr
          have hrec := ih hY_next_card hZ_next_card
          have hsucc :
              (k + 1 + 1) * ((X.card + Y.card + Z.card + 2) ^ 2 * goodCubeStepCostFactor S.c S.k ε D) =
                (k + 1) * ((X.card + Y.card + Z.card + 2) ^ 2 * goodCubeStepCostFactor S.c S.k ε D) +
                  (X.card + Y.card + Z.card + 2) ^ 2 * goodCubeStepCostFactor S.c S.k ε D :=
            Nat.succ_mul (k + 1) _
          linarith
        | inr slices =>
          rw [scanMatrixPairTracked_snd]
          have h1 :
              (X.card + Y.card + Z.card + 2) ^ 2 * goodCubeStepCostFactor S.c S.k ε D ≤
                (k + 1 + 1) * ((X.card + Y.card + Z.card + 2) ^ 2 * goodCubeStepCostFactor S.c S.k ε D) :=
            Nat.le_mul_of_pos_left _ (by omega)
          linarith

/-- Total operation bound for `cappedGoodCubeTracked` (`paper.tex`, Lemma 5.3 (`\label{lem:cube-step}`)). -/
theorem cappedGoodCubeTracked_snd_le [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    (ε γ_val : ℝ) (D : ℕ) (α_cap β_init : ℝ) (S : TwoStageSamplerOracle β ε) :
    (cappedGoodCubeTracked X Y Z A B ε γ_val D α_cap β_init S).2 ≤
      (rCubeFuel ε γ_val + 1) *
        ((X.card + Y.card + Z.card + 2) ^ 2 * goodCubeStepCostFactor S.c S.k ε D) :=
  cappedGoodCubeLoopTracked_snd_le (rCubeFuel ε γ_val) X A B ε γ_val D α_cap β_init S le_rfl le_rfl

lemma matDensity_matTranspose_eq (U : Finset β) (V : Finset γ) (B : β → γ → ℝ) :
    matDensity V U (matTranspose B) = matDensity U V B :=
  expectSet_comm V U (matTranspose B)

lemma goodCubeStepFactor_eq (ε : ℝ) (D : ℕ) :
    goodCubeStepFactor ε D =
      (144 / ε) * (2 : ℝ) ^ (4 * D) * (2 : ℝ) ^ (194 * (D : ℝ) / ε) := by
  unfold goodCubeStepFactor
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have h4D : (4 * (D : ℝ)) = ((4 * D : ℕ) : ℝ) := by push_cast; ring
  rw [h4D, Real.rpow_natCast]
  ring

lemma three_mul_inv_goodCubeStepFactor_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (D : ℕ) :
    3 * (goodCubeStepFactor ε D)⁻¹ ≤
      (1 / 3 : ℝ) * (2 : ℝ) ^ (- (194 * (D : ℝ) / ε)) := by
  rw [goodCubeStepFactor_eq]
  have h144 : (9 : ℝ) ≤ 144 / ε := by
    rw [le_div_iff₀ hε0]
    linarith
  have h4D : (1 : ℝ) ≤ (2 : ℝ) ^ (4 * D) := one_le_pow₀ (by norm_num)
  have hprod : (9 : ℝ) ≤ (144 / ε) * (2 : ℝ) ^ (4 * D) := by nlinarith
  have hinv : ((144 / ε) * (2 : ℝ) ^ (4 * D))⁻¹ ≤ (1 / 9 : ℝ) := by
    rw [one_div]
    exact inv_anti₀ (by norm_num) hprod
  have hrpow_inv : ((2 : ℝ) ^ (194 * (D : ℝ) / ε))⁻¹ = (2 : ℝ) ^ (- (194 * (D : ℝ) / ε)) :=
    (Real.rpow_neg (by norm_num) (194 * (D : ℝ) / ε)).symm
  rw [mul_inv, hrpow_inv]
  have hpos : 0 ≤ (2 : ℝ) ^ (- (194 * (D : ℝ) / ε)) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hinv hpos
  linarith

lemma step4d_area_eq {ε : ℝ} (D s : ℕ) (cY cZ : ℝ) :
    (3 : ℝ) * (goodCubeStepFactor ε D)⁻¹ * (2 : ℝ) ^ (-(s * D : ℤ)) * (cY * cZ) =
      ((((2 : ℝ) ^ (2 * D))⁻¹) * ((2 : ℝ) ^ (- (194 * (D : ℝ) / ε)) * cY)) *
        ((ε / 48) * (((2 : ℝ) ^ ((s + 2) * D))⁻¹) * cZ) := by
  rw [goodCubeStepFactor_eq]
  have hzpow : (2 : ℝ) ^ (-((s : ℤ) * (D : ℤ))) = ((2 : ℝ) ^ (s * D))⁻¹ := by
    have hcast : (s : ℤ) * (D : ℤ) = ((s * D : ℕ) : ℤ) := (Nat.cast_mul s D).symm
    rw [hcast, zpow_neg, zpow_natCast]
  have hrpow_inv : ((2 : ℝ) ^ (194 * (D : ℝ) / ε))⁻¹ = (2 : ℝ) ^ (- (194 * (D : ℝ) / ε)) :=
    (Real.rpow_neg (by norm_num) (194 * (D : ℝ) / ε)).symm
  have hpow : (2 : ℝ) ^ (4 * D) * (2 : ℝ) ^ (s * D) =
      (2 : ℝ) ^ (2 * D) * (2 : ℝ) ^ ((s + 2) * D) := by
    rw [← pow_add, ← pow_add]
    congr 1
    ring
  rw [hzpow, mul_inv, mul_inv, inv_div, hrpow_inv]
  calc
    (3 : ℝ) * (ε / 144 * ((2 : ℝ) ^ (4 * D))⁻¹ * (2 : ℝ) ^ (-(194 * (D : ℝ) / ε))) *
        ((2 : ℝ) ^ (s * D))⁻¹ * (cY * cZ)
      = (ε / 48) * (((2 : ℝ) ^ (4 * D) * (2 : ℝ) ^ (s * D))⁻¹) *
          (2 : ℝ) ^ (-(194 * (D : ℝ) / ε)) * (cY * cZ) := by
        rw [mul_inv]; ring
    _ = (ε / 48) * (((2 : ℝ) ^ (2 * D) * (2 : ℝ) ^ ((s + 2) * D))⁻¹) *
          (2 : ℝ) ^ (-(194 * (D : ℝ) / ε)) * (cY * cZ) := by
        rw [hpow]
    _ = ((((2 : ℝ) ^ (2 * D))⁻¹) * ((2 : ℝ) ^ (- (194 * (D : ℝ) / ε)) * cY)) *
          ((ε / 48) * (((2 : ℝ) ^ ((s + 2) * D))⁻¹) * cZ) := by
        rw [mul_inv]; ring

/-- Per-piece specification of `processGoodCubePiece` (§5.2 of `paper.tex`). -/
theorem processGoodCubePiece_spec [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {X : Finset α} {Y' : Finset β} {Z_curr : Finset γ}
    {B : β → γ → ℝ} {ε : ℝ} {D : ℕ} {α_low α_cap β_curr : ℝ}
    (S : TwoStageSamplerOracle β ε)
    {P : RectPiece α β}
    (hZ : Z_curr.Nonempty) (hB : IsBinaryMatrix Y' Z_curr B)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hD : 2 ≤ D)
    (hβ_gt : (2 : ℝ) ^ (-(D : ℤ)) < β_curr)
    (hB'_ge : β_curr ≤ matDensity Y' Z_curr B)
    (hB'_min : IsEpsMinDegree Y' Z_curr B (ε * gamma3D / 2))
    (hPX : P.X_sub ⊆ X) (hPY : P.Y_sub ⊆ Y')
    (hPX_ne : P.X_sub.Nonempty) (hPY_ne : P.Y_sub.Nonempty)
    (hPA : IsBinaryMatrix P.X_sub P.Y_sub P.A_sub)
    (hPA_ext : ∀ x y, P.A_sub x y = submatZeroExt P.X_sub P.Y_sub P.A_sub x y)
    (hPY_card : (2 : ℝ) ^ (- (194 * (D : ℝ) / ε)) * (Y'.card : ℝ) ≤ (P.Y_sub.card : ℝ))
    (hP_boost : P.tag = RectTag.aBoosted →
      α_cap ≤ matDensity P.X_sub P.Y_sub P.A_sub ∧
      (2 : ℝ) ^ P.scale * α_low ≤ matDensity P.X_sub P.Y_sub P.A_sub ∧
      (M_rect3D ε D)⁻¹ * (2 : ℝ) ^ (-(P.scale * D : ℤ)) *
        ((X.card : ℝ) * (Y'.card : ℝ)) ≤ (P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ))
    (hP_reg : P.tag = RectTag.regular →
      P.scale ≤ 47 ∧
      (2 : ℝ) ^ (-(D : ℤ)) < matDensity P.X_sub P.Y_sub P.A_sub ∧
      α_low < matDensity P.X_sub P.Y_sub P.A_sub ∧
      matDensity P.X_sub P.Y_sub P.A_sub < α_cap ∧
      IsGridRegular P.X_sub P.Y_sub P.A_sub ε 2 D ∧
      IsEpsMinDegree P.X_sub P.Y_sub P.A_sub ε ∧
      (M_rect3D ε D)⁻¹ * (2 : ℝ) ^ (-(P.scale * D : ℤ)) *
        ((X.card : ℝ) * (Y'.card : ℝ)) ≤ (P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ)) :
    match processGoodCubePiece Y' Z_curr B ε gamma3D D S P with
    | Sum.inl (Y_next, Z_next, s_step) =>
      Y_next ⊆ Y' ∧ Z_next ⊆ Z_curr ∧ Y_next.Nonempty ∧ Z_next.Nonempty ∧
      (2 : ℝ) ^ s_step * (1 + ε * gamma3D / 4) * β_curr ≤ matDensity Y_next Z_next B ∧
      (3 : ℝ) * (goodCubeStepFactor ε D)⁻¹ * (2 : ℝ) ^ (-(s_step * D : ℤ)) *
        ((Y'.card : ℝ) * (Z_curr.card : ℝ)) ≤ (Y_next.card : ℝ) * (Z_next.card : ℝ)
    | Sum.inr sl =>
      sl.X_ell = P.X_sub ∧ sl.Y_ell = P.Y_sub ∧ sl.A_ell = P.A_sub ∧
      sl.tag = P.tag ∧ sl.S_ell = P.scale ∧ sl.Z_ell ⊆ Z_curr ∧
      sl.X_ell ⊆ X ∧ sl.Y_ell ⊆ Y' ∧ sl.X_ell.Nonempty ∧ sl.Y_ell.Nonempty ∧
      IsBinaryMatrix sl.X_ell sl.Y_ell sl.A_ell ∧
      (∀ x y, sl.A_ell x y = submatZeroExt sl.X_ell sl.Y_ell sl.A_ell x y) ∧
      (sl.tag = RectTag.residual →
        (sl.Z_ell.Nonempty →
          sl.Z_ell = Z_curr ∧ matDensity sl.X_ell sl.Y_ell sl.A_ell ≤ (2 : ℝ) ^ (-(D : ℤ))) ∧
        ((2 : ℝ) ^ (-(D : ℤ)) < matDensity sl.X_ell sl.Y_ell sl.A_ell → sl.Z_ell = ∅) ∧
        (matDensity sl.X_ell sl.Y_ell sl.A_ell ≤ (2 : ℝ) ^ (-(D : ℤ)) → sl.Z_ell = Z_curr)) ∧
      (sl.tag = RectTag.aBoosted →
        sl.Z_ell = ∅ ∧
        matDensity sl.Y_ell Z_curr B < 2 * matDensity Y' Z_curr B ∧
        α_cap ≤ matDensity sl.X_ell sl.Y_ell sl.A_ell ∧
        (2 : ℝ) ^ sl.S_ell * α_low ≤ matDensity sl.X_ell sl.Y_ell sl.A_ell ∧
        (M_rect3D ε D)⁻¹ * (2 : ℝ) ^ (-(sl.S_ell * D : ℤ)) *
          ((X.card : ℝ) * (Y'.card : ℝ)) ≤ (sl.X_ell.card : ℝ) * (sl.Y_ell.card : ℝ)) ∧
      (sl.tag = RectTag.regular →
        sl.Z_ell.Nonempty ∧
        sl.S_ell ≤ 47 ∧
        (2 : ℝ) ^ (-(D : ℤ)) < matDensity sl.X_ell sl.Y_ell sl.A_ell ∧
        matDensity sl.X_ell sl.Y_ell sl.A_ell < α_cap ∧
        IsGridRegular sl.X_ell sl.Y_ell sl.A_ell ε 2 D ∧
        IsEpsMinDegree sl.X_ell sl.Y_ell sl.A_ell ε ∧
        (M_rect3D ε D)⁻¹ * (2 : ℝ) ^ (-(sl.S_ell * D : ℤ)) *
          ((X.card : ℝ) * (Y'.card : ℝ)) ≤ (sl.X_ell.card : ℝ) * (sl.Y_ell.card : ℝ) ∧
        IsGridRegular sl.Z_ell sl.Y_ell (matTranspose B) ε 2 D ∧
        IsEpsMinDegree sl.Z_ell sl.Y_ell (matTranspose B) ε ∧
        (1 - ε * gamma3D / 2) * matDensity Y' Z_curr B ≤ matDensity sl.Y_ell sl.Z_ell B ∧
        (2 : ℝ) ^ (-((D + 1 : ℕ) : ℤ)) < matDensity sl.Y_ell sl.Z_ell B ∧
        matDensity sl.Y_ell sl.Z_ell B < 3 * matDensity Y' Z_curr B ∧
        ((Z_curr \ sl.Z_ell).card : ℝ) < gamma3D * (Z_curr.card : ℝ) ∧
        ((Z_curr \ sl.Z_ell).Nonempty →
          matDensity sl.Y_ell (Z_curr \ sl.Z_ell) B < 2 * matDensity Y' Z_curr B)) := by
  classical
  have hε1 : ε < 1 := by linarith only [hε_le]
  have hγ0 : 0 < gamma3D := gamma3D_pos
  have hγ_le_half : gamma3D ≤ 1 / 2 := by unfold gamma3D; norm_num
  have hεγ_le : ε * gamma3D ≤ 1 / 2 := by unfold gamma3D; linarith only [hε_le]
  have hβ_pos : 0 < β_curr := lt_trans (by positivity) hβ_gt
  have h4a_dens : ∀ (hdouble : matDensity P.Y_sub Z_curr B ≥ 2 * matDensity Y' Z_curr B),
      (2 : ℝ) ^ (0 : ℕ) * (1 + ε * gamma3D / 4) * β_curr ≤ matDensity P.Y_sub Z_curr B := by
    intro hdouble
    have hfac : 1 + ε * gamma3D / 4 ≤ 2 := by
      unfold gamma3D
      linarith
    have h1 : (2 : ℝ) ^ (0 : ℕ) * (1 + ε * gamma3D / 4) * β_curr ≤ 2 * matDensity Y' Z_curr B := by
      simp only [pow_zero, one_mul]
      exact mul_le_mul hfac hB'_ge hβ_pos.le (by norm_num)
    exact h1.trans hdouble
  have h4a_area :
      (3 : ℝ) * (goodCubeStepFactor ε D)⁻¹ * (2 : ℝ) ^ (-((0 : ℕ) * D : ℤ)) *
        ((Y'.card : ℝ) * (Z_curr.card : ℝ)) ≤ (P.Y_sub.card : ℝ) * (Z_curr.card : ℝ) := by
    simp only [Nat.cast_zero, zero_mul, neg_zero, zpow_zero, mul_one]
    have hfac := three_mul_inv_goodCubeStepFactor_le hε0 hε1.le D
    have h1 : (3 : ℝ) * (goodCubeStepFactor ε D)⁻¹ ≤ (2 : ℝ) ^ (- (194 * (D : ℝ) / ε)) := by
      have : 0 ≤ (2 : ℝ) ^ (- (194 * (D : ℝ) / ε)) := by positivity
      linarith
    have h2 : (3 : ℝ) * (goodCubeStepFactor ε D)⁻¹ * (Y'.card : ℝ) ≤ (P.Y_sub.card : ℝ) :=
      (mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)).trans hPY_card
    calc
      (3 : ℝ) * (goodCubeStepFactor ε D)⁻¹ * ((Y'.card : ℝ) * (Z_curr.card : ℝ))
        = ((3 : ℝ) * (goodCubeStepFactor ε D)⁻¹ * (Y'.card : ℝ)) * (Z_curr.card : ℝ) := by ring
      _ ≤ (P.Y_sub.card : ℝ) * (Z_curr.card : ℝ) :=
          mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _)
  unfold processGoodCubePiece
  cases htag : P.tag
  · -- `P.tag = RectTag.regular`
    dsimp only
    by_cases h4a : matDensity P.Y_sub Z_curr B ≥ 2 * matDensity Y' Z_curr B
    · rw [if_pos h4a]
      exact ⟨hPY, Finset.Subset.rfl, hPY_ne, hZ, h4a_dens h4a, h4a_area⟩
    · rw [if_neg h4a]
      push_neg at h4a
      have hB_PY : IsBinaryMatrix P.Y_sub Z_curr B := isBinaryMatrix_subset hPY Finset.Subset.rfl hB
      have hBT_PY : IsBinaryMatrix Z_curr P.Y_sub (matTranspose B) := isBinaryMatrix_matTranspose hB_PY
      have hrow_BT : ∀ z ∈ Z_curr, 0 ≤ rowDeg P.Y_sub (matTranspose B) z :=
        fun z hz => expectSet_nonneg (fun y hy => isBinaryMatrix_nonneg hBT_PY z hz y hy)
      have hminZ := lem_min_degree hZ hε0 hε1 hγ0 hγ_le_half hrow_BT
      rcases hminZ with ⟨hZ_sub, hZ_ne, hZ_third, hZ_dens_BT, hZ_cases, hZ_tag1, hZ_tag2, _⟩
      let Z_ell := (minDegree Z_curr P.Y_sub (matTranspose B) ε gamma3D).1
      let tagZ := (minDegree Z_curr P.Y_sub (matTranspose B) ε gamma3D).2
      have hZ_dens : matDensity P.Y_sub Z_curr B ≤ matDensity P.Y_sub Z_ell B := by
        rw [← matDensity_matTranspose_eq P.Y_sub Z_curr B,
          ← matDensity_matTranspose_eq P.Y_sub Z_ell B]
        exact hZ_dens_BT
      have hbprime1 : (1 - ε * gamma3D / 2) * matDensity Y' Z_curr B ≤ matDensity P.Y_sub Z_curr B :=
        le_expectSet_of_le hPY_ne (fun y hy => hB'_min y (hPY hy))
      have hbprime2 : (1 - ε * gamma3D / 2) * β_curr ≤ matDensity P.Y_sub Z_curr B :=
        (mul_le_mul_of_nonneg_left hB'_ge (by unfold gamma3D; linarith)).trans hbprime1
      have hbprime3 : (2 : ℝ) ^ (-((D + 1 : ℕ) : ℤ)) < matDensity P.Y_sub Z_curr B := by
        have hpow : (2 : ℝ) ^ (-((D + 1 : ℕ) : ℤ)) = (1 / 2 : ℝ) * (2 : ℝ) ^ (-(D : ℤ)) := by
          have hexp : (-((D + 1 : ℕ) : ℤ)) = (-1 : ℤ) + (-(D : ℤ)) := by push_cast; ring
          rw [hexp, zpow_add₀ (by norm_num)]
          norm_num
        rw [hpow]
        have hhalf : (1 / 2 : ℝ) < 1 - ε * gamma3D / 2 := by unfold gamma3D; linarith
        have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (-(D : ℤ)) := by positivity
        nlinarith
      by_cases h4c : tagZ = 2 ∨ matDensity P.Y_sub Z_ell B ≥ (1 + ε * gamma3D) * matDensity P.Y_sub Z_curr B
      · rw [if_pos h4c]
        have hboost_4c : (1 + ε * gamma3D) * matDensity P.Y_sub Z_curr B ≤ matDensity P.Y_sub Z_ell B := by
          rcases h4c with h2 | hge
          · have h2s := (hZ_tag2 h2).2.2.2.2.2.2.1
            rw [matDensity_matTranspose_eq P.Y_sub Z_curr B,
              matDensity_matTranspose_eq P.Y_sub Z_ell B] at h2s
            linarith only [h2s]
          · exact hge
        have hstep_dens :
            (2 : ℝ) ^ (0 : ℕ) * (1 + ε * gamma3D / 4) * β_curr ≤ matDensity P.Y_sub Z_ell B := by
          simp only [pow_zero, one_mul]
          exact goodCube_step4c_density_boost hβ_pos.le (by unfold gamma3D; positivity)
            (by unfold gamma3D; linarith only [hε_le]) hbprime2 hboost_4c
        have hstep_area :
            (3 : ℝ) * (goodCubeStepFactor ε D)⁻¹ * (2 : ℝ) ^ (-((0 : ℕ) * D : ℤ)) *
              ((Y'.card : ℝ) * (Z_curr.card : ℝ)) ≤ (P.Y_sub.card : ℝ) * (Z_ell.card : ℝ) := by
          simp only [Nat.cast_zero, zero_mul, neg_zero, zpow_zero, mul_one]
          have hfac := three_mul_inv_goodCubeStepFactor_le hε0 hε1.le D
          have hprod := mul_le_mul hPY_card hZ_third (by positivity) (by positivity)
          calc
            (3 : ℝ) * (goodCubeStepFactor ε D)⁻¹ * ((Y'.card : ℝ) * (Z_curr.card : ℝ))
              ≤ ((1 / 3 : ℝ) * (2 : ℝ) ^ (- (194 * (D : ℝ) / ε))) *
                  ((Y'.card : ℝ) * (Z_curr.card : ℝ)) :=
                mul_le_mul_of_nonneg_right hfac (by positivity)
            _ = ((2 : ℝ) ^ (- (194 * (D : ℝ) / ε)) * (Y'.card : ℝ)) *
                  ((1 / 3 : ℝ) * (Z_curr.card : ℝ)) := by ring
            _ ≤ (P.Y_sub.card : ℝ) * (Z_ell.card : ℝ) := hprod
        exact ⟨hPY, hZ_sub, hPY_ne, hZ_ne, hstep_dens, hstep_area⟩
      · rw [if_neg h4c]
        push_neg at h4c
        have htagZ_1 : tagZ = 1 := by
          rcases hZ_cases with h1 | h2
          · exact h1
          · exact False.elim (h4c.1 h2)
        rcases hZ_tag1 htagZ_1 with
          ⟨hZ_mindeg, _hZ_dens_1, hZ_sdiff_dens, hZ_sdiff_lt, _hZ_card_gt, _hZ_sdiff_empty⟩
        have hBT_Zell : IsBinaryMatrix Z_ell P.Y_sub (matTranspose B) :=
          isBinaryMatrix_subset hZ_sub Finset.Subset.rfl hBT_PY
        have hstep4d_boost :
            (1 + ε * gamma3D / 4) * β_curr ≤
              (1 + ε / 2) * matDensity Z_ell P.Y_sub (matTranspose B) := by
          rw [matDensity_matTranspose_eq P.Y_sub Z_ell B]
          have hfac := goodCube_step4d_factor_ge hε0.le hε1.le
          have h1 : (1 + ε * gamma3D / 4) * β_curr ≤
              (1 + ε / 2) * ((1 - ε * gamma3D / 2) * β_curr) := by
            have := mul_le_mul_of_nonneg_right hfac hβ_pos.le
            linarith only [this]
          have h2 : (1 + ε / 2) * ((1 - ε * gamma3D / 2) * β_curr) ≤
              (1 + ε / 2) * matDensity P.Y_sub Z_ell B :=
            mul_le_mul_of_nonneg_left (hbprime2.trans hZ_dens) (by linarith only [hε0])
          exact h1.trans h2
        have hδ_sift :
            1 < (2 : ℝ) ^ D * ((1 + ε / 2) * matDensity Z_ell P.Y_sub (matTranspose B)) := by
          have h1 : (2 : ℝ) ^ D * (2 : ℝ) ^ (-(D : ℤ)) = 1 := by
            rw [← zpow_natCast 2 D, ← zpow_add₀ (by norm_num), add_neg_cancel, zpow_zero]
          have h2 : (2 : ℝ) ^ (-(D : ℤ)) < (1 + ε / 2) * matDensity Z_ell P.Y_sub (matTranspose B) := by
            have hγ_pos : 0 < ε * gamma3D / 4 := by unfold gamma3D; positivity
            have hlt : β_curr < (1 + ε * gamma3D / 4) * β_curr := by nlinarith only [hγ_pos, hβ_pos]
            linarith only [hβ_gt, hlt, hstep4d_boost]
          have h2D_pos : (0 : ℝ) < (2 : ℝ) ^ D := by positivity
          nlinarith only [h1, h2, h2D_pos]
        rcases lem_dyadic_sift_concrete S hZ_ne hPY_ne hBT_Zell hε0 hε1 hD hδ_sift with
          ⟨hsift_cases, hsift_sub_spec, hsift_reg_spec⟩
        by_cases h4d :
            (dyadicSiftConcrete Z_ell P.Y_sub (matTranspose B) ε D S).1 = "subrect"
        · rw [if_pos h4d]
          rcases hsift_sub_spec h4d with
            ⟨_hs_lt_D, hZ''_sub, hY''_sub, hZ''_ne, hY''_ne, hZ''_dens, hZ''_card, _, hY''_card⟩
          let Z'' := (dyadicSiftConcrete Z_ell P.Y_sub (matTranspose B) ε D S).2.1
          let Y'' := (dyadicSiftConcrete Z_ell P.Y_sub (matTranspose B) ε D S).2.2.1
          let s := (dyadicSiftConcrete Z_ell P.Y_sub (matTranspose B) ε D S).2.2.2
          have hstep_dens :
              (2 : ℝ) ^ s * (1 + ε * gamma3D / 4) * β_curr ≤ matDensity Y'' Z'' B := by
            rw [← matDensity_matTranspose_eq Y'' Z'' B]
            have h1 :
                (2 : ℝ) ^ s * (1 + ε * gamma3D / 4) * β_curr ≤
                  (2 : ℝ) ^ s * ((1 + ε / 2) * matDensity Z_ell P.Y_sub (matTranspose B)) := by
              have hmul := mul_le_mul_of_nonneg_left hstep4d_boost (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ s)
              linarith only [hmul]
            have h2 :
                (2 : ℝ) ^ s * ((1 + ε / 2) * matDensity Z_ell P.Y_sub (matTranspose B)) ≤
                  matDensity Z'' Y'' (matTranspose B) := by
              linarith only [hZ''_dens]
            exact h1.trans h2
          have hstep_area :
              (3 : ℝ) * (goodCubeStepFactor ε D)⁻¹ * (2 : ℝ) ^ (-(s * D : ℤ)) *
                ((Y'.card : ℝ) * (Z_curr.card : ℝ)) ≤ (Y''.card : ℝ) * (Z''.card : ℝ) := by
            rw [step4d_area_eq]
            have hY''_bound :
                (((2 : ℝ) ^ (2 * D))⁻¹) * ((2 : ℝ) ^ (- (194 * (D : ℝ) / ε)) * (Y'.card : ℝ)) ≤
                  (Y''.card : ℝ) :=
              (mul_le_mul_of_nonneg_left hPY_card (by positivity)).trans hY''_card.le
            have hZ''_bound :
                (ε / 48) * (((2 : ℝ) ^ ((s + 2) * D))⁻¹) * (Z_curr.card : ℝ) ≤ (Z''.card : ℝ) := by
              calc
                (ε / 48) * (((2 : ℝ) ^ ((s + 2) * D))⁻¹) * (Z_curr.card : ℝ)
                  = (ε / 16) * (((2 : ℝ) ^ ((s + 2) * D))⁻¹) * ((1 / 3 : ℝ) * (Z_curr.card : ℝ)) := by
                    ring
                _ ≤ (ε / 16) * (((2 : ℝ) ^ ((s + 2) * D))⁻¹) * (Z_ell.card : ℝ) :=
                    mul_le_mul_of_nonneg_left hZ_third (by positivity)
                _ ≤ (Z''.card : ℝ) := hZ''_card
            exact mul_le_mul hY''_bound hZ''_bound (by positivity) (by positivity)
          exact ⟨hY''_sub.trans hPY, hZ''_sub.trans hZ_sub, hY''_ne, hZ''_ne, hstep_dens, hstep_area⟩
        · rw [if_neg h4d]
          have hsift_reg_eq :
              (dyadicSiftConcrete Z_ell P.Y_sub (matTranspose B) ε D S).1 = "regular" := by
            rcases hsift_cases with h1 | h2
            · exact False.elim (h4d h1)
            · exact h2
          have hregB := (hsift_reg_spec hsift_reg_eq).2.2.2.2
          rcases hP_reg htag with ⟨hS47, hPA_gt, _hPA_low_lt, hPA_lt, hPA_grid, hPA_mindeg, hPA_area⟩
          have hB'_pos : 0 < matDensity Y' Z_curr B := lt_of_lt_of_le hβ_pos hB'_ge
          have hslice_nonneg : 0 ≤ matDensity P.Y_sub Z_curr B :=
            matDensity_nonneg (isBinaryMatrix_nonneg hB_PY)
          have hBell_nonneg : 0 ≤ matDensity P.Y_sub Z_ell B :=
            hslice_nonneg.trans hZ_dens
          have h4c_bounds := goodCube_step4c_normal_bounds hB'_pos hslice_nonneg hBell_nonneg
            hε0.le hγ0.le gamma3D_le_one hεγ_le h4a h4c.2
          dsimp only
          refine ⟨rfl, rfl, rfl, rfl, rfl, hZ_sub, hPX, hPY, hPX_ne, hPY_ne,
            hPA, hPA_ext, (fun h => by cases h), (fun h => by cases h),
            fun _ => ⟨hZ_ne, hS47, hPA_gt, hPA_lt, hPA_grid, hPA_mindeg, hPA_area,
              hregB, hZ_mindeg, hbprime1.trans hZ_dens, lt_of_lt_of_le hbprime3 hZ_dens,
              h4c_bounds.1, hZ_sdiff_lt, fun hsdiff_ne => ?_⟩⟩
          have hsdiff_bt := hZ_sdiff_dens hsdiff_ne
          rw [matDensity_matTranspose_eq P.Y_sub (Z_curr \ Z_ell) B,
            matDensity_matTranspose_eq P.Y_sub Z_ell B] at hsdiff_bt
          exact lt_trans hsdiff_bt h4c_bounds.2
  · -- `P.tag = RectTag.aBoosted`
    dsimp only
    by_cases h4a : matDensity P.Y_sub Z_curr B ≥ 2 * matDensity Y' Z_curr B
    · rw [if_pos h4a]
      exact ⟨hPY, Finset.Subset.rfl, hPY_ne, hZ, h4a_dens h4a, h4a_area⟩
    · rw [if_neg h4a]
      push_neg at h4a
      rcases hP_boost htag with ⟨hPA_cap, hPA_low, hPA_area⟩
      dsimp only
      refine ⟨rfl, rfl, rfl, rfl, rfl, Finset.empty_subset _, hPX, hPY, hPX_ne, hPY_ne,
        hPA, hPA_ext, (fun h => by cases h),
        fun _ => ⟨rfl, h4a, hPA_cap, hPA_low, hPA_area⟩,
        (fun h => by cases h)⟩
  · -- `P.tag = RectTag.residual`
    dsimp only [processGoodCubePiece]
    have hZL_sub :
        (if matDensity P.X_sub P.Y_sub P.A_sub ≤ (2 : ℝ) ^ (-(D : ℤ)) then Z_curr else ∅) ⊆ Z_curr := by
      split_ifs
      · exact Finset.Subset.rfl
      · exact Finset.empty_subset _
    refine ⟨rfl, rfl, rfl, rfl, rfl, hZL_sub, hPX, hPY, hPX_ne, hPY_ne,
      hPA, hPA_ext, ?_, (fun h => by cases h), (fun h => by cases h)⟩
    intro _
    refine ⟨?_, ?_, ?_⟩
    · intro hne
      split_ifs at hne ⊢ with hle
      · exact ⟨rfl, hle⟩
      · exact False.elim (Finset.not_nonempty_empty hne)
    · intro hgt
      rw [if_neg (not_le.mpr hgt)]
    · intro hle
      rw [if_pos hle]

/-- List-level specification of `processGoodCubePieces` across `L : List (RectPiece α β)`. -/
theorem processGoodCubePieces_spec [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {X : Finset α} {Y' : Finset β} {Z_curr : Finset γ}
    {B : β → γ → ℝ} {ε : ℝ} {D : ℕ} {α_low α_cap β_curr : ℝ}
    (S : TwoStageSamplerOracle β ε)
    (L : List (RectPiece α β))
    (hZ : Z_curr.Nonempty) (hB : IsBinaryMatrix Y' Z_curr B)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hD : 2 ≤ D)
    (hβ_gt : (2 : ℝ) ^ (-(D : ℤ)) < β_curr)
    (hB'_ge : β_curr ≤ matDensity Y' Z_curr B)
    (hB'_min : IsEpsMinDegree Y' Z_curr B (ε * gamma3D / 2))
    (hL_spec : ∀ P ∈ L,
      P.X_sub ⊆ X ∧ P.Y_sub ⊆ Y' ∧ P.X_sub.Nonempty ∧ P.Y_sub.Nonempty ∧
      IsBinaryMatrix P.X_sub P.Y_sub P.A_sub ∧
      (∀ x y, P.A_sub x y = submatZeroExt P.X_sub P.Y_sub P.A_sub x y) ∧
      (2 : ℝ) ^ (- (194 * (D : ℝ) / ε)) * (Y'.card : ℝ) ≤ (P.Y_sub.card : ℝ) ∧
      (P.tag = RectTag.aBoosted →
        α_cap ≤ matDensity P.X_sub P.Y_sub P.A_sub ∧
        (2 : ℝ) ^ P.scale * α_low ≤ matDensity P.X_sub P.Y_sub P.A_sub ∧
        (M_rect3D ε D)⁻¹ * (2 : ℝ) ^ (-(P.scale * D : ℤ)) *
          ((X.card : ℝ) * (Y'.card : ℝ)) ≤ (P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ)) ∧
      (P.tag = RectTag.regular →
        P.scale ≤ 47 ∧
        (2 : ℝ) ^ (-(D : ℤ)) < matDensity P.X_sub P.Y_sub P.A_sub ∧
        α_low < matDensity P.X_sub P.Y_sub P.A_sub ∧
        matDensity P.X_sub P.Y_sub P.A_sub < α_cap ∧
        IsGridRegular P.X_sub P.Y_sub P.A_sub ε 2 D ∧
        IsEpsMinDegree P.X_sub P.Y_sub P.A_sub ε ∧
        (M_rect3D ε D)⁻¹ * (2 : ℝ) ^ (-(P.scale * D : ℤ)) *
          ((X.card : ℝ) * (Y'.card : ℝ)) ≤ (P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ))) :
    match processGoodCubePieces Y' Z_curr B ε gamma3D D S L with
    | Sum.inl (Y_next, Z_next, s_step) =>
      Y_next ⊆ Y' ∧ Z_next ⊆ Z_curr ∧ Y_next.Nonempty ∧ Z_next.Nonempty ∧
      (2 : ℝ) ^ s_step * (1 + ε * gamma3D / 4) * β_curr ≤ matDensity Y_next Z_next B ∧
      (3 : ℝ) * (goodCubeStepFactor ε D)⁻¹ * (2 : ℝ) ^ (-(s_step * D : ℤ)) *
        ((Y'.card : ℝ) * (Z_curr.card : ℝ)) ≤ (Y_next.card : ℝ) * (Z_next.card : ℝ)
    | Sum.inr slices =>
      (∀ x y, (slices.map (fun sl => sl.A_ell x y)).sum = (L.map (fun P => P.A_sub x y)).sum) ∧
      (slices.map (fun sl =>
        matDensity sl.X_ell sl.Y_ell sl.A_ell * (sl.X_ell.card : ℝ) * (sl.Y_ell.card : ℝ))).sum =
        (L.map (fun P =>
          matDensity P.X_sub P.Y_sub P.A_sub * (P.X_sub.card : ℝ) * (P.Y_sub.card : ℝ))).sum ∧
      (∀ sl ∈ slices,
        sl.Z_ell ⊆ Z_curr ∧ sl.X_ell ⊆ X ∧ sl.Y_ell ⊆ Y' ∧
        sl.X_ell.Nonempty ∧ sl.Y_ell.Nonempty ∧
        IsBinaryMatrix sl.X_ell sl.Y_ell sl.A_ell ∧
        (∀ x y, sl.A_ell x y = submatZeroExt sl.X_ell sl.Y_ell sl.A_ell x y) ∧
        (sl.tag = RectTag.residual →
          (sl.Z_ell.Nonempty →
            sl.Z_ell = Z_curr ∧ matDensity sl.X_ell sl.Y_ell sl.A_ell ≤ (2 : ℝ) ^ (-(D : ℤ))) ∧
          ((2 : ℝ) ^ (-(D : ℤ)) < matDensity sl.X_ell sl.Y_ell sl.A_ell → sl.Z_ell = ∅) ∧
          (matDensity sl.X_ell sl.Y_ell sl.A_ell ≤ (2 : ℝ) ^ (-(D : ℤ)) → sl.Z_ell = Z_curr)) ∧
        (sl.tag = RectTag.aBoosted →
          sl.Z_ell = ∅ ∧
          matDensity sl.Y_ell Z_curr B < 2 * matDensity Y' Z_curr B ∧
          α_cap ≤ matDensity sl.X_ell sl.Y_ell sl.A_ell ∧
          (2 : ℝ) ^ sl.S_ell * α_low ≤ matDensity sl.X_ell sl.Y_ell sl.A_ell ∧
          (M_rect3D ε D)⁻¹ * (2 : ℝ) ^ (-(sl.S_ell * D : ℤ)) *
            ((X.card : ℝ) * (Y'.card : ℝ)) ≤ (sl.X_ell.card : ℝ) * (sl.Y_ell.card : ℝ)) ∧
        (sl.tag = RectTag.regular →
          sl.Z_ell.Nonempty ∧
          sl.S_ell ≤ 47 ∧
          (2 : ℝ) ^ (-(D : ℤ)) < matDensity sl.X_ell sl.Y_ell sl.A_ell ∧
          matDensity sl.X_ell sl.Y_ell sl.A_ell < α_cap ∧
          IsGridRegular sl.X_ell sl.Y_ell sl.A_ell ε 2 D ∧
          IsEpsMinDegree sl.X_ell sl.Y_ell sl.A_ell ε ∧
          (M_rect3D ε D)⁻¹ * (2 : ℝ) ^ (-(sl.S_ell * D : ℤ)) *
            ((X.card : ℝ) * (Y'.card : ℝ)) ≤ (sl.X_ell.card : ℝ) * (sl.Y_ell.card : ℝ) ∧
          IsGridRegular sl.Z_ell sl.Y_ell (matTranspose B) ε 2 D ∧
          IsEpsMinDegree sl.Z_ell sl.Y_ell (matTranspose B) ε ∧
          (1 - ε * gamma3D / 2) * matDensity Y' Z_curr B ≤ matDensity sl.Y_ell sl.Z_ell B ∧
          (2 : ℝ) ^ (-((D + 1 : ℕ) : ℤ)) < matDensity sl.Y_ell sl.Z_ell B ∧
          matDensity sl.Y_ell sl.Z_ell B < 3 * matDensity Y' Z_curr B ∧
          ((Z_curr \ sl.Z_ell).card : ℝ) < gamma3D * (Z_curr.card : ℝ) ∧
          ((Z_curr \ sl.Z_ell).Nonempty →
            matDensity sl.Y_ell (Z_curr \ sl.Z_ell) B < 2 * matDensity Y' Z_curr B))) := by
  induction L with
  | nil =>
    unfold processGoodCubePieces
    exact ⟨fun _ _ => rfl, rfl, fun _ h => by cases h⟩
  | cons P rest ih =>
    unfold processGoodCubePieces
    rcases hL_spec P List.mem_cons_self with
      ⟨hPX, hPY, hPX_ne, hPY_ne, hPA, hPA_ext, hPY_card, hP_boost, hP_reg⟩
    have hP_res := processGoodCubePiece_spec S hZ hB hε0 hε_le hD hβ_gt hB'_ge hB'_min
      hPX hPY hPX_ne hPY_ne hPA hPA_ext hPY_card hP_boost hP_reg
    cases hP_eq : processGoodCubePiece Y' Z_curr B ε gamma3D D S P with
    | inl step =>
      rw [hP_eq] at hP_res
      exact hP_res
    | inr sl =>
      rw [hP_eq] at hP_res
      rcases hP_res with ⟨hX_eq, hY_eq, hA_eq, _htag_eq, _hS_eq, sl_rest⟩
      have hrest_res := ih (fun Q hQ => hL_spec Q (List.mem_cons_of_mem P hQ))
      cases hrest_eq : processGoodCubePieces Y' Z_curr B ε gamma3D D S rest with
      | inl step =>
        rw [hrest_eq] at hrest_res
        exact hrest_res
      | inr sls =>
        rw [hrest_eq] at hrest_res
        rcases hrest_res with ⟨hsum_A, hsum_mom, hsls_spec⟩
        refine ⟨fun x y => ?_, ?_, fun s hs => ?_⟩
        · simp only [List.map_cons, List.sum_cons, hA_eq, hsum_A x y]
        · simp only [List.map_cons, List.sum_cons, hX_eq, hY_eq, hA_eq, hsum_mom]
        · simp only [List.mem_cons] at hs
          rcases hs with rfl | hs_tail
          · exact sl_rest
          · exact hsls_spec s hs_tail

/-- Full inductive specification of `cappedGoodCubeLoop` (Algorithm 5 (`FindCube`), §5.2 of `paper.tex`). -/
theorem cappedGoodCubeLoop_spec [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (fuel : ℕ) {X : Finset α} {Y_curr : Finset β} {Z_curr : Finset γ}
    {A : α → β → ℝ} {B : β → γ → ℝ}
    {ε : ℝ} {D : ℕ} {α_cap β_init : ℝ}
    (S : TwoStageSamplerOracle β ε)
    (hX : X.Nonempty) (hY : Y_curr.Nonempty) (hZ : Z_curr.Nonempty)
    (hA : IsBinaryMatrix X Y_curr A) (hB : IsBinaryMatrix Y_curr Z_curr B)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hD : 2 ≤ D)
    (_hα_nonneg : 0 ≤ α_cap)
    (hβ_gt : (2 : ℝ) ^ (-(D : ℤ)) < β_init)
    (hB_ge_init : β_init ≤ matDensity Y_curr Z_curr B)
    (hfuel_cap : 16 * β_init ≤ (1 + ε * gamma3D / 4) ^ fuel * matDensity Y_curr Z_curr B) :
    let res := cappedGoodCubeLoop fuel X Y_curr Z_curr A B ε gamma3D D α_cap β_init S
    res.X_star = X ∧ res.Y_star ⊆ Y_curr ∧ res.Z_star ⊆ Z_curr ∧
    res.Y_star.Nonempty ∧ res.Z_star.Nonempty ∧
    res.Y_prime = res.Y_star ∧
    res.A_prime = submatZeroExt X res.Y_star A ∧
    res.B_prime = submatZeroExt res.Y_star res.Z_star B ∧
    res.alpha_star = α_cap ∧
    res.steps ≤ fuel ∧
    (2 : ℝ) ^ res.S_B * (1 + ε * gamma3D / 4) ^ res.steps * matDensity Y_curr Z_curr B ≤
      matDensity res.Y_star res.Z_star B ∧
    (3⁻¹ : ℝ) * ((goodCubeStepFactor ε D) ^ res.steps)⁻¹ *
      (2 : ℝ) ^ (-(res.S_B * D : ℤ)) * ((Y_curr.card : ℝ) * (Z_curr.card : ℝ)) ≤
        (res.Y_star.card : ℝ) * (res.Z_star.card : ℝ) ∧
    (res.mode = CubeMode.bBoost ∨ res.mode = CubeMode.normal) ∧
    (res.mode = CubeMode.bBoost → 16 * β_init ≤ matDensity res.Y_star res.Z_star B) ∧
    (res.mode = CubeMode.normal →
      (matDensity res.Y_star res.Z_star B < 16 * (1 + ε * gamma3D / 4) * β_init ∧
        matDensity res.Y_star res.Z_star B < 17 * β_init) ∧
      (∀ x y, (res.slices.map (fun sl => sl.A_ell x y)).sum = submatZeroExt X res.Y_star A x y) ∧
      (res.slices.map (fun sl =>
        matDensity sl.X_ell sl.Y_ell sl.A_ell * (sl.X_ell.card : ℝ) * (sl.Y_ell.card : ℝ))).sum =
        matDensity X res.Y_star A * (X.card : ℝ) * (res.Y_star.card : ℝ) ∧
      (∀ sl ∈ res.slices,
        sl.Z_ell ⊆ res.Z_star ∧ sl.X_ell ⊆ X ∧ sl.Y_ell ⊆ res.Y_star ∧
        sl.X_ell.Nonempty ∧ sl.Y_ell.Nonempty ∧
        IsBinaryMatrix sl.X_ell sl.Y_ell sl.A_ell ∧
        (∀ x y, sl.A_ell x y = submatZeroExt sl.X_ell sl.Y_ell sl.A_ell x y) ∧
        (sl.tag = RectTag.residual →
          (sl.Z_ell.Nonempty →
            sl.Z_ell = res.Z_star ∧ matDensity sl.X_ell sl.Y_ell sl.A_ell ≤ (2 : ℝ) ^ (-(D : ℤ))) ∧
          ((2 : ℝ) ^ (-(D : ℤ)) < matDensity sl.X_ell sl.Y_ell sl.A_ell → sl.Z_ell = ∅) ∧
          (matDensity sl.X_ell sl.Y_ell sl.A_ell ≤ (2 : ℝ) ^ (-(D : ℤ)) → sl.Z_ell = res.Z_star)) ∧
        (sl.tag = RectTag.aBoosted →
          sl.Z_ell = ∅ ∧
          matDensity sl.Y_ell res.Z_star B < 2 * matDensity res.Y_star res.Z_star B ∧
          cCap3D * α_cap ≤ matDensity sl.X_ell sl.Y_ell sl.A_ell ∧
          (2 : ℝ) ^ sl.S_ell * (cLow3D * α_cap) ≤ matDensity sl.X_ell sl.Y_ell sl.A_ell ∧
          (M_rect3D ε D)⁻¹ * (2 : ℝ) ^ (-(sl.S_ell * D : ℤ)) *
            ((X.card : ℝ) * (res.Y_star.card : ℝ)) ≤ (sl.X_ell.card : ℝ) * (sl.Y_ell.card : ℝ)) ∧
        (sl.tag = RectTag.regular →
          sl.Z_ell.Nonempty ∧
          sl.S_ell ≤ 47 ∧
          (2 : ℝ) ^ (-(D : ℤ)) < matDensity sl.X_ell sl.Y_ell sl.A_ell ∧
          matDensity sl.X_ell sl.Y_ell sl.A_ell < cCap3D * α_cap ∧
          IsGridRegular sl.X_ell sl.Y_ell sl.A_ell ε 2 D ∧
          IsEpsMinDegree sl.X_ell sl.Y_ell sl.A_ell ε ∧
          (M_rect3D ε D)⁻¹ * (2 : ℝ) ^ (-(sl.S_ell * D : ℤ)) *
            ((X.card : ℝ) * (res.Y_star.card : ℝ)) ≤ (sl.X_ell.card : ℝ) * (sl.Y_ell.card : ℝ) ∧
          IsGridRegular sl.Z_ell sl.Y_ell (matTranspose B) ε 2 D ∧
          IsEpsMinDegree sl.Z_ell sl.Y_ell (matTranspose B) ε ∧
          (1 - ε * gamma3D / 2) * matDensity res.Y_star res.Z_star B ≤
            matDensity sl.Y_ell sl.Z_ell B ∧
          (2 : ℝ) ^ (-((D + 1 : ℕ) : ℤ)) < matDensity sl.Y_ell sl.Z_ell B ∧
          matDensity sl.Y_ell sl.Z_ell B < 3 * matDensity res.Y_star res.Z_star B ∧
          ((res.Z_star \ sl.Z_ell).card : ℝ) < gamma3D * (res.Z_star.card : ℝ) ∧
          ((res.Z_star \ sl.Z_ell).Nonempty →
            matDensity sl.Y_ell (res.Z_star \ sl.Z_ell) B <
              2 * matDensity res.Y_star res.Z_star B)))) := by
  classical
  have hε1 : ε < 1 := by linarith
  have hβ_pos : 0 < β_init := lt_trans (by positivity) hβ_gt
  induction fuel generalizing Y_curr Z_curr with
  | zero =>
    unfold cappedGoodCubeLoop
    dsimp only
    rw [pow_zero, one_mul] at hfuel_cap
    refine ⟨rfl, Finset.Subset.rfl, Finset.Subset.rfl, hY, hZ, rfl, rfl, rfl, rfl, le_rfl,
      ?_, ?_, Or.inl rfl, fun _ => hfuel_cap, fun h => by cases h⟩
    · simp only [pow_zero, one_mul]; exact le_rfl
    · simp only [pow_zero, inv_one, Nat.cast_zero, zero_mul, neg_zero, zpow_zero, mul_one]
      have harea : 0 ≤ (Y_curr.card : ℝ) * (Z_curr.card : ℝ) := by positivity
      linarith
  | succ k ih =>
    unfold cappedGoodCubeLoop
    dsimp only
    have harea : 0 ≤ (Y_curr.card : ℝ) * (Z_curr.card : ℝ) := by positivity
    by_cases hboost : matDensity Y_curr Z_curr B ≥ 16 * β_init
    · rw [if_pos hboost]
      dsimp only
      refine ⟨rfl, Finset.Subset.rfl, Finset.Subset.rfl, hY, hZ, rfl, rfl, rfl, rfl,
        Nat.zero_le _, ?_, ?_, Or.inl rfl, fun _ => hboost, fun h => by cases h⟩
      · simp only [pow_zero, one_mul]; exact le_rfl
      · simp only [pow_zero, inv_one, Nat.cast_zero, zero_mul, neg_zero, zpow_zero, mul_one]
        linarith
    · rw [if_neg hboost]
      push_neg at hboost
      have hεγ_pos : 0 < ε * gamma3D / 2 := by unfold gamma3D; positivity
      have hεγ_lt_1 : ε * gamma3D / 2 < 1 := by unfold gamma3D; linarith
      have hrow_B : ∀ y ∈ Y_curr, 0 ≤ rowDeg Z_curr B y :=
        fun y hy => expectSet_nonneg (fun z hz => isBinaryMatrix_nonneg hB y hy z hz)
      have hminB := lem_min_degree hY hεγ_pos hεγ_lt_1 (by norm_num) (le_rfl) hrow_B
      rcases hminB with ⟨hY'_sub, hY'_ne, hY'_third, hY'_dens, hY'_cases, hY'_tag1, hY'_tag2, _⟩
      let Y' := (minDegree Y_curr Z_curr B (ε * gamma3D / 2) (1 / 2)).1
      let tagB := (minDegree Y_curr Z_curr B (ε * gamma3D / 2) (1 / 2)).2
      have hA_Y' : IsBinaryMatrix X Y' A := isBinaryMatrix_subset Finset.Subset.rfl hY'_sub hA
      have hB_Y' : IsBinaryMatrix Y' Z_curr B := isBinaryMatrix_subset hY'_sub Finset.Subset.rfl hB
      have hB_curr_gt : (2 : ℝ) ^ (-(D : ℤ)) < matDensity Y_curr Z_curr B :=
        lt_of_lt_of_le hβ_gt hB_ge_init
      by_cases hstep1 :
          (minDegree Y_curr Z_curr B (ε * gamma3D / 2) (1 / 2)).2 = 2 ∨
            matDensity (minDegree Y_curr Z_curr B (ε * gamma3D / 2) (1 / 2)).1 Z_curr B ≥
              (1 + ε * gamma3D / 4) * matDensity Y_curr Z_curr B
      · -- Recursive Step 1
        rw [if_pos hstep1]
        have hboost1 : (1 + ε * gamma3D / 4) * matDensity Y_curr Z_curr B ≤ matDensity Y' Z_curr B := by
          rcases hstep1 with h2 | hge
          · have h2s := (hY'_tag2 h2).2.2.2.2.2.2.1
            linarith
          · exact hge
        have hB'_ge_init : β_init ≤ matDensity Y' Z_curr B :=
          hB_ge_init.trans hY'_dens
        have hfuel_next : 16 * β_init ≤ (1 + ε * gamma3D / 4) ^ k * matDensity Y' Z_curr B := by
          calc
            16 * β_init ≤ (1 + ε * gamma3D / 4) ^ (k + 1) * matDensity Y_curr Z_curr B := hfuel_cap
            _ = (1 + ε * gamma3D / 4) ^ k *
                  ((1 + ε * gamma3D / 4) * matDensity Y_curr Z_curr B) := by rw [pow_succ]; ring
            _ ≤ (1 + ε * gamma3D / 4) ^ k * matDensity Y' Z_curr B :=
                mul_le_mul_of_nonneg_left hboost1 (by unfold gamma3D; positivity)
        rcases ih hY'_ne hZ hA_Y' hB_Y' hB'_ge_init hfuel_next with
          ⟨hX_eq, hsubY, hsubZ, hneY, hneZ, hYp_eq, hAp_eq, hBp_eq, halp_eq, hsteps_le,
            hdens_ih, harea_ih, hmode_ih, hbboost_ih, hnorm_ih⟩
        dsimp only
        refine ⟨hX_eq, hsubY.trans hY'_sub, hsubZ, hneY, hneZ, hYp_eq, hAp_eq, hBp_eq, halp_eq,
          Nat.succ_le_succ hsteps_le, ?_, ?_, hmode_ih, hbboost_ih, hnorm_ih⟩
        · calc
            (2 : ℝ) ^ (cappedGoodCubeLoop k X Y' Z_curr A B ε gamma3D D α_cap β_init S).S_B *
                (1 + ε * gamma3D / 4) ^
                  ((cappedGoodCubeLoop k X Y' Z_curr A B ε gamma3D D α_cap β_init S).steps + 1) *
                matDensity Y_curr Z_curr B
              = (2 : ℝ) ^ (cappedGoodCubeLoop k X Y' Z_curr A B ε gamma3D D α_cap β_init S).S_B *
                  (1 + ε * gamma3D / 4) ^
                    (cappedGoodCubeLoop k X Y' Z_curr A B ε gamma3D D α_cap β_init S).steps *
                  ((1 + ε * gamma3D / 4) * matDensity Y_curr Z_curr B) := by rw [pow_succ]; ring
            _ ≤ (2 : ℝ) ^ (cappedGoodCubeLoop k X Y' Z_curr A B ε gamma3D D α_cap β_init S).S_B *
                  (1 + ε * gamma3D / 4) ^
                    (cappedGoodCubeLoop k X Y' Z_curr A B ε gamma3D D α_cap β_init S).steps *
                  matDensity Y' Z_curr B :=
                mul_le_mul_of_nonneg_left hboost1 (by unfold gamma3D; positivity)
            _ ≤ _ := hdens_ih
        · have hfac_ge_3 : 3 ≤ goodCubeStepFactor ε D := by
            have hinv := three_mul_inv_goodCubeStepFactor_le hε0 hε1.le D
            have hle1 : (1 / 3 : ℝ) * (2 : ℝ) ^ (- (194 * (D : ℝ) / ε)) ≤ 1 := by
              have hpos_exp : 0 ≤ 194 * (D : ℝ) / ε := by positivity
              have : (2 : ℝ) ^ (- (194 * (D : ℝ) / ε)) ≤ 1 :=
                Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
              linarith
            have h1 : 3 * (goodCubeStepFactor ε D)⁻¹ ≤ 1 := hinv.trans hle1
            have hpos := one_le_goodCubeStepFactor hε0 hε1.le D
            have hmul := mul_le_mul_of_nonneg_right h1 (by linarith : 0 ≤ goodCubeStepFactor ε D)
            rw [mul_assoc, inv_mul_cancel₀ (by linarith), mul_one, one_mul] at hmul
            exact hmul
          have hinv_le : (goodCubeStepFactor ε D)⁻¹ ≤ (1 / 3 : ℝ) := by
            rw [one_div]
            exact inv_anti₀ (by norm_num) hfac_ge_3
          have hY'_area :
              (goodCubeStepFactor ε D)⁻¹ * ((Y_curr.card : ℝ) * (Z_curr.card : ℝ)) ≤
                (Y'.card : ℝ) * (Z_curr.card : ℝ) := by
            calc
              (goodCubeStepFactor ε D)⁻¹ * ((Y_curr.card : ℝ) * (Z_curr.card : ℝ))
                ≤ (1 / 3 : ℝ) * ((Y_curr.card : ℝ) * (Z_curr.card : ℝ)) :=
                  mul_le_mul_of_nonneg_right hinv_le harea
              _ = ((1 / 3 : ℝ) * (Y_curr.card : ℝ)) * (Z_curr.card : ℝ) := by ring
              _ ≤ (Y'.card : ℝ) * (Z_curr.card : ℝ) :=
                  mul_le_mul_of_nonneg_right hY'_third (Nat.cast_nonneg _)
          calc
            (3⁻¹ : ℝ) *
                ((goodCubeStepFactor ε D) ^
                  ((cappedGoodCubeLoop k X Y' Z_curr A B ε gamma3D D α_cap β_init S).steps + 1))⁻¹ *
                (2 : ℝ) ^
                  (-((cappedGoodCubeLoop k X Y' Z_curr A B ε gamma3D D α_cap β_init S).S_B * D : ℤ)) *
                ((Y_curr.card : ℝ) * (Z_curr.card : ℝ))
              = (3⁻¹ : ℝ) *
                  ((goodCubeStepFactor ε D) ^
                    (cappedGoodCubeLoop k X Y' Z_curr A B ε gamma3D D α_cap β_init S).steps)⁻¹ *
                  (2 : ℝ) ^
                    (-((cappedGoodCubeLoop k X Y' Z_curr A B ε gamma3D D α_cap β_init S).S_B * D : ℤ)) *
                  ((goodCubeStepFactor ε D)⁻¹ * ((Y_curr.card : ℝ) * (Z_curr.card : ℝ))) := by
                rw [pow_succ, mul_inv]; ring
            _ ≤ (3⁻¹ : ℝ) *
                  ((goodCubeStepFactor ε D) ^
                    (cappedGoodCubeLoop k X Y' Z_curr A B ε gamma3D D α_cap β_init S).steps)⁻¹ *
                  (2 : ℝ) ^
                    (-((cappedGoodCubeLoop k X Y' Z_curr A B ε gamma3D D α_cap β_init S).S_B * D : ℤ)) *
                  ((Y'.card : ℝ) * (Z_curr.card : ℝ)) := by
                refine mul_le_mul_of_nonneg_left hY'_area ?_
                have := one_le_goodCubeStepFactor hε0 hε1.le D
                positivity
            _ ≤ _ := harea_ih
      · -- Step 1 passed (`tagB = 1` and `matDensity Y' Z_curr B < (1 + ε * gamma3D / 4) * matDensity Y_curr Z_curr B`)
        rw [if_neg hstep1]
        push_neg at hstep1
        have htagB_1 : tagB = 1 := by
          rcases hY'_cases with h1 | h2
          · exact h1
          · exact False.elim (hstep1.1 h2)
        have hB'_min := (hY'_tag1 htagB_1).1
        let piecesA := cappedADecomp3D X Y' A ε D (cLow3D * α_cap) (cCap3D * α_cap) S
        have hwin : cCap3D * α_cap ≤ (2 : ℝ) ^ (48 : ℕ) * (cLow3D * α_cap) := by
          have : cCap3D * α_cap = (2 : ℝ) ^ (48 : ℕ) * (cLow3D * α_cap) := by
            unfold cCap3D cLow3D
            norm_num
            ring
          linarith
        have hpiecesA_spec : ∀ P ∈ piecesA, _ :=
          fun P hP => cappedADecomp3DLoop_pieces_spec (rDecompAFuel ε D) S
            hX hY'_ne hA_Y' hε0 hε_le hD hwin hP
        have hproc := processGoodCubePieces_spec S piecesA hZ hB_Y' hε0 hε_le hD
          hB_curr_gt hY'_dens hB'_min hpiecesA_spec
        cases hproc_eq : processGoodCubePieces Y' Z_curr B ε gamma3D D S piecesA with
        | inl step =>
          rcases step with ⟨Y_next, Z_next, s_step⟩
          rw [hproc_eq] at hproc
          rcases hproc with ⟨hYn_sub, hZn_sub, hYn_ne, hZn_ne, hYn_dens, hYn_area⟩
          have hA_Yn : IsBinaryMatrix X Y_next A :=
            isBinaryMatrix_subset Finset.Subset.rfl hYn_sub hA_Y'
          have hB_Yn : IsBinaryMatrix Y_next Z_next B :=
            isBinaryMatrix_subset hYn_sub hZn_sub hB_Y'
          have h2s_ge : (1 : ℝ) ≤ (2 : ℝ) ^ s_step := one_le_pow₀ (by norm_num)
          have hboost_step :
              (1 + ε * gamma3D / 4) * matDensity Y_curr Z_curr B ≤ matDensity Y_next Z_next B := by
            have h1 :
                1 * ((1 + ε * gamma3D / 4) * matDensity Y_curr Z_curr B) ≤
                  (2 : ℝ) ^ s_step * (1 + ε * gamma3D / 4) * matDensity Y_curr Z_curr B := by
              have hpos : 0 ≤ (1 + ε * gamma3D / 4) * matDensity Y_curr Z_curr B := by
                have := lt_trans (by positivity) hB_curr_gt
                unfold gamma3D; positivity
              have := mul_le_mul_of_nonneg_right h2s_ge hpos
              linarith
            linarith
          have hBn_ge_init : β_init ≤ matDensity Y_next Z_next B := by
            have hpos : 0 < ε * gamma3D / 4 := by unfold gamma3D; positivity
            have : matDensity Y_curr Z_curr B ≤ (1 + ε * gamma3D / 4) * matDensity Y_curr Z_curr B := by
              have := lt_trans (by positivity) hB_curr_gt
              nlinarith
            exact hB_ge_init.trans (this.trans hboost_step)
          have hfuel_next : 16 * β_init ≤ (1 + ε * gamma3D / 4) ^ k * matDensity Y_next Z_next B := by
            calc
              16 * β_init ≤ (1 + ε * gamma3D / 4) ^ (k + 1) * matDensity Y_curr Z_curr B := hfuel_cap
              _ = (1 + ε * gamma3D / 4) ^ k *
                    ((1 + ε * gamma3D / 4) * matDensity Y_curr Z_curr B) := by rw [pow_succ]; ring
              _ ≤ (1 + ε * gamma3D / 4) ^ k * matDensity Y_next Z_next B :=
                  mul_le_mul_of_nonneg_left hboost_step (by unfold gamma3D; positivity)
          rcases ih hYn_ne hZn_ne hA_Yn hB_Yn hBn_ge_init hfuel_next with
            ⟨hX_eq, hsubY, hsubZ, hneY, hneZ, hYp_eq, hAp_eq, hBp_eq, halp_eq, hsteps_le,
              hdens_ih, harea_ih, hmode_ih, hbboost_ih, hnorm_ih⟩
          dsimp only
          refine ⟨hX_eq, hsubY.trans (hYn_sub.trans hY'_sub), hsubZ.trans hZn_sub,
            hneY, hneZ, hYp_eq, hAp_eq, hBp_eq, halp_eq,
            Nat.succ_le_succ hsteps_le, ?_, ?_, hmode_ih, hbboost_ih, hnorm_ih⟩
          · calc
              (2 : ℝ) ^
                  ((cappedGoodCubeLoop k X Y_next Z_next A B ε gamma3D D α_cap β_init S).S_B + s_step) *
                (1 + ε * gamma3D / 4) ^
                  ((cappedGoodCubeLoop k X Y_next Z_next A B ε gamma3D D α_cap β_init S).steps + 1) *
                matDensity Y_curr Z_curr B
                = (2 : ℝ) ^ (cappedGoodCubeLoop k X Y_next Z_next A B ε gamma3D D α_cap β_init S).S_B *
                    (1 + ε * gamma3D / 4) ^
                      (cappedGoodCubeLoop k X Y_next Z_next A B ε gamma3D D α_cap β_init S).steps *
                    ((2 : ℝ) ^ s_step * (1 + ε * gamma3D / 4) * matDensity Y_curr Z_curr B) := by
                  rw [pow_add, pow_succ]; ring
              _ ≤ (2 : ℝ) ^ (cappedGoodCubeLoop k X Y_next Z_next A B ε gamma3D D α_cap β_init S).S_B *
                    (1 + ε * gamma3D / 4) ^
                      (cappedGoodCubeLoop k X Y_next Z_next A B ε gamma3D D α_cap β_init S).steps *
                    matDensity Y_next Z_next B :=
                  mul_le_mul_of_nonneg_left hYn_dens (by unfold gamma3D; positivity)
              _ ≤ _ := hdens_ih
          · have harea_step :
                (goodCubeStepFactor ε D)⁻¹ * (2 : ℝ) ^ (-(s_step * D : ℤ)) *
                  ((Y_curr.card : ℝ) * (Z_curr.card : ℝ)) ≤
                  (Y_next.card : ℝ) * (Z_next.card : ℝ) := by
              have hY'_YZ :
                  (1 / 3 : ℝ) * ((Y_curr.card : ℝ) * (Z_curr.card : ℝ)) ≤
                    (Y'.card : ℝ) * (Z_curr.card : ℝ) := by
                have : (1 / 3 : ℝ) * ((Y_curr.card : ℝ) * (Z_curr.card : ℝ)) =
                    ((1 / 3 : ℝ) * (Y_curr.card : ℝ)) * (Z_curr.card : ℝ) := by ring
                rw [this]
                exact mul_le_mul_of_nonneg_right hY'_third (Nat.cast_nonneg _)
              have h1 :
                  (goodCubeStepFactor ε D)⁻¹ * (2 : ℝ) ^ (-(s_step * D : ℤ)) *
                    ((Y_curr.card : ℝ) * (Z_curr.card : ℝ)) =
                  (3 : ℝ) * (goodCubeStepFactor ε D)⁻¹ * (2 : ℝ) ^ (-(s_step * D : ℤ)) *
                    ((1 / 3 : ℝ) * ((Y_curr.card : ℝ) * (Z_curr.card : ℝ))) := by ring
              rw [h1]
              have h2 :
                  (3 : ℝ) * (goodCubeStepFactor ε D)⁻¹ * (2 : ℝ) ^ (-(s_step * D : ℤ)) *
                    ((1 / 3 : ℝ) * ((Y_curr.card : ℝ) * (Z_curr.card : ℝ))) ≤
                  (3 : ℝ) * (goodCubeStepFactor ε D)⁻¹ * (2 : ℝ) ^ (-(s_step * D : ℤ)) *
                    ((Y'.card : ℝ) * (Z_curr.card : ℝ)) := by
                refine mul_le_mul_of_nonneg_left hY'_YZ ?_
                have := one_le_goodCubeStepFactor hε0 hε1.le D
                positivity
              exact h2.trans hYn_area
            have hzpow_add :
                (2 : ℝ) ^
                  (-(((cappedGoodCubeLoop k X Y_next Z_next A B ε gamma3D D α_cap β_init S).S_B +
                    s_step) * D : ℤ)) =
                (2 : ℝ) ^
                  (-((cappedGoodCubeLoop k X Y_next Z_next A B ε gamma3D D α_cap β_init S).S_B * D : ℤ)) *
                  (2 : ℝ) ^ (-(s_step * D : ℤ)) := by
              have hexp :
                  (-(((cappedGoodCubeLoop k X Y_next Z_next A B ε gamma3D D α_cap β_init S).S_B +
                    s_step) * D : ℤ)) =
                  (-((cappedGoodCubeLoop k X Y_next Z_next A B ε gamma3D D α_cap β_init S).S_B * D : ℤ)) +
                    (-(s_step * D : ℤ)) := by ring
              rw [hexp, zpow_add₀ (by norm_num)]
            calc
              (3⁻¹ : ℝ) *
                  ((goodCubeStepFactor ε D) ^
                    ((cappedGoodCubeLoop k X Y_next Z_next A B ε gamma3D D α_cap β_init S).steps + 1))⁻¹ *
                  (2 : ℝ) ^
                    (-(((cappedGoodCubeLoop k X Y_next Z_next A B ε gamma3D D α_cap β_init S).S_B +
                      s_step) * D : ℤ)) *
                  ((Y_curr.card : ℝ) * (Z_curr.card : ℝ))
                = (3⁻¹ : ℝ) *
                    ((goodCubeStepFactor ε D) ^
                      (cappedGoodCubeLoop k X Y_next Z_next A B ε gamma3D D α_cap β_init S).steps)⁻¹ *
                    (2 : ℝ) ^
                      (-((cappedGoodCubeLoop k X Y_next Z_next A B ε gamma3D D α_cap β_init S).S_B * D : ℤ)) *
                    ((goodCubeStepFactor ε D)⁻¹ * (2 : ℝ) ^ (-(s_step * D : ℤ)) *
                      ((Y_curr.card : ℝ) * (Z_curr.card : ℝ))) := by
                  rw [pow_succ, mul_inv, hzpow_add]; ring
              _ ≤ (3⁻¹ : ℝ) *
                    ((goodCubeStepFactor ε D) ^
                      (cappedGoodCubeLoop k X Y_next Z_next A B ε gamma3D D α_cap β_init S).steps)⁻¹ *
                    (2 : ℝ) ^
                      (-((cappedGoodCubeLoop k X Y_next Z_next A B ε gamma3D D α_cap β_init S).S_B * D : ℤ)) *
                    ((Y_next.card : ℝ) * (Z_next.card : ℝ)) := by
                  refine mul_le_mul_of_nonneg_left harea_step ?_
                  have := one_le_goodCubeStepFactor hε0 hε1.le D
                  positivity
              _ ≤ _ := harea_ih
        | inr slices =>
          rw [hproc_eq] at hproc
          rcases hproc with ⟨hsum_A, hsum_mom, hslices_spec⟩
          have hY'_area :
              (3⁻¹ : ℝ) * ((Y_curr.card : ℝ) * (Z_curr.card : ℝ)) ≤
                (Y'.card : ℝ) * (Z_curr.card : ℝ) := by
            have : (3⁻¹ : ℝ) * ((Y_curr.card : ℝ) * (Z_curr.card : ℝ)) =
                ((1 / 3 : ℝ) * (Y_curr.card : ℝ)) * (Z_curr.card : ℝ) := by ring
            rw [this]
            exact mul_le_mul_of_nonneg_right hY'_third (Nat.cast_nonneg _)
          have hlt16 : matDensity Y' Z_curr B < 16 * (1 + ε * gamma3D / 4) * β_init := by
            have h1 := hstep1.2
            have hpos : 0 < 1 + ε * gamma3D / 4 := by unfold gamma3D; positivity
            nlinarith
          have hlt17 : matDensity Y' Z_curr B < 17 * β_init := by
            have h2 : 1 + ε * gamma3D / 4 < 17 / 16 := by unfold gamma3D; linarith
            nlinarith
          dsimp only
          refine ⟨rfl, hY'_sub, Finset.Subset.rfl, hY'_ne, hZ, rfl, rfl, rfl, rfl,
            Nat.zero_le _, ?_, ?_, Or.inr rfl, (fun h => by cases h),
            fun _ => ⟨⟨hlt16, hlt17⟩, ?_, ?_, hslices_spec⟩⟩
          · simp only [pow_zero, one_mul]; exact hY'_dens
          · simp only [pow_zero, inv_one, Nat.cast_zero, zero_mul, neg_zero, zpow_zero, mul_one]
            exact hY'_area
          · intro x y
            rw [hsum_A x y]
            exact cappedADecomp3DLoop_sum_eq (rDecompAFuel ε D) X Y' A ε D
              (cLow3D * α_cap) (cCap3D * α_cap) S x y
          · rw [hsum_mom]
            exact cappedADecomp3DLoop_first_moment_eq (rDecompAFuel ε D) hX hY'_ne A ε D
              (cLow3D * α_cap) (cCap3D * α_cap) S

/-- **Lemma 5.3 (`\label{lem:cube-step}`) (`thm_3d_decomp_part1`, §5.2 of `paper.tex`)**:
Full specification of `cappedGoodCube X Y Z A B ε gamma3D D α_cap (matDensity Y Z B) S`:
Whenever $\beta_{\text{init}} = \mathbb{E}_{Y \times Z}[B] > 2^{-D}$, `cappedGoodCube` halts in
at most `rCubeFuel ε gamma3D` steps with $S_B \le D$, area lower bound
$$|Y^*| |Z^*| \ge M_{\text{cube}}(\varepsilon, \gamma, D)^{-1} 2^{-S_B D} |Y| |Z|,$$
and:
- If `res.mode = CubeMode.bBoost`: $\mathbb{E}[B[Y^*, Z^*]] \ge \max(16, 2^{S_B}) \mathbb{E}[B]$.
- If `res.mode = CubeMode.normal`: $S_B \le 4$, $2^{S_B}\mathbb{E}[B] \le \mathbb{E}[B[Y^*, Z^*]] < 17\mathbb{E}[B]$,
  and every slice in `res.slices` satisfies the regular / `aBoosted` / residual guarantees of
  Lemma 5.3 (`\label{lem:cube-step}`). -/
theorem thm_3d_decomp_part1 [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {X : Finset α} {Y : Finset β} {Z : Finset γ}
    {A : α → β → ℝ} {B : β → γ → ℝ}
    {ε : ℝ} {D : ℕ} {α_cap : ℝ}
    (S : TwoStageSamplerOracle β ε)
    (hX : X.Nonempty) (hY : Y.Nonempty) (hZ : Z.Nonempty)
    (hA : IsBinaryMatrix X Y A) (hB : IsBinaryMatrix Y Z B)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hD : 2 ≤ D)
    (hα_nonneg : 0 ≤ α_cap)
    (hB_gt : (2 : ℝ) ^ (-(D : ℤ)) < matDensity Y Z B) :
    let res := cappedGoodCube X Y Z A B ε gamma3D D α_cap (matDensity Y Z B) S
    res.X_star = X ∧ res.Y_star ⊆ Y ∧ res.Z_star ⊆ Z ∧
    res.Y_star.Nonempty ∧ res.Z_star.Nonempty ∧
    res.steps ≤ rCubeFuel ε gamma3D ∧
    res.S_B ≤ D ∧
    (2 : ℝ) ^ res.S_B * matDensity Y Z B ≤ matDensity res.Y_star res.Z_star B ∧
    (M_cube ε gamma3D D)⁻¹ * (2 : ℝ) ^ (-(res.S_B * D : ℤ)) *
      ((Y.card : ℝ) * (Z.card : ℝ)) ≤ (res.Y_star.card : ℝ) * (res.Z_star.card : ℝ) ∧
    (res.mode = CubeMode.bBoost ∨ res.mode = CubeMode.normal) ∧
    (res.mode = CubeMode.bBoost →
      max 16 ((2 : ℝ) ^ res.S_B) * matDensity Y Z B ≤ matDensity res.Y_star res.Z_star B) ∧
    (res.mode = CubeMode.normal →
      res.S_B ≤ 4 ∧
      (matDensity res.Y_star res.Z_star B < 16 * (1 + ε * gamma3D / 4) * matDensity Y Z B ∧
        matDensity res.Y_star res.Z_star B < 17 * matDensity Y Z B) ∧
      (∀ x y, (res.slices.map (fun sl => sl.A_ell x y)).sum = submatZeroExt X res.Y_star A x y) ∧
      (∀ sl ∈ res.slices,
        sl.Z_ell ⊆ res.Z_star ∧ sl.X_ell ⊆ X ∧ sl.Y_ell ⊆ res.Y_star ∧
        sl.X_ell.Nonempty ∧ sl.Y_ell.Nonempty ∧
        IsBinaryMatrix sl.X_ell sl.Y_ell sl.A_ell ∧
        (∀ x y, sl.A_ell x y = submatZeroExt sl.X_ell sl.Y_ell sl.A_ell x y) ∧
        (sl.tag = RectTag.residual →
          (sl.Z_ell.Nonempty →
            sl.Z_ell = res.Z_star ∧ matDensity sl.X_ell sl.Y_ell sl.A_ell ≤ (2 : ℝ) ^ (-(D : ℤ))) ∧
          ((2 : ℝ) ^ (-(D : ℤ)) < matDensity sl.X_ell sl.Y_ell sl.A_ell → sl.Z_ell = ∅) ∧
          (matDensity sl.X_ell sl.Y_ell sl.A_ell ≤ (2 : ℝ) ^ (-(D : ℤ)) → sl.Z_ell = res.Z_star)) ∧
        (sl.tag = RectTag.aBoosted →
          sl.Z_ell = ∅ ∧
          matDensity sl.Y_ell res.Z_star B < 2 * matDensity res.Y_star res.Z_star B ∧
          cCap3D * α_cap ≤ matDensity sl.X_ell sl.Y_ell sl.A_ell ∧
          (2 : ℝ) ^ sl.S_ell * (cLow3D * α_cap) ≤ matDensity sl.X_ell sl.Y_ell sl.A_ell ∧
          (M_rect3D ε D)⁻¹ * (2 : ℝ) ^ (-(sl.S_ell * D : ℤ)) *
            ((X.card : ℝ) * (res.Y_star.card : ℝ)) ≤ (sl.X_ell.card : ℝ) * (sl.Y_ell.card : ℝ)) ∧
        (sl.tag = RectTag.regular →
          sl.Z_ell.Nonempty ∧
          sl.S_ell ≤ 47 ∧
          (2 : ℝ) ^ (-(D : ℤ)) < matDensity sl.X_ell sl.Y_ell sl.A_ell ∧
          matDensity sl.X_ell sl.Y_ell sl.A_ell < cCap3D * α_cap ∧
          IsGridRegular sl.X_ell sl.Y_ell sl.A_ell ε 2 D ∧
          IsEpsMinDegree sl.X_ell sl.Y_ell sl.A_ell ε ∧
          (M_rect3D ε D)⁻¹ * (2 : ℝ) ^ (-(sl.S_ell * D : ℤ)) *
            ((X.card : ℝ) * (res.Y_star.card : ℝ)) ≤ (sl.X_ell.card : ℝ) * (sl.Y_ell.card : ℝ) ∧
          IsGridRegular sl.Z_ell sl.Y_ell (matTranspose B) ε 2 D ∧
          IsEpsMinDegree sl.Z_ell sl.Y_ell (matTranspose B) ε ∧
          (1 - ε * gamma3D / 2) * matDensity res.Y_star res.Z_star B ≤
            matDensity sl.Y_ell sl.Z_ell B ∧
          (2 : ℝ) ^ (-((D + 1 : ℕ) : ℤ)) < matDensity sl.Y_ell sl.Z_ell B ∧
          matDensity sl.Y_ell sl.Z_ell B < 3 * matDensity res.Y_star res.Z_star B ∧
          ((res.Z_star \ sl.Z_ell).card : ℝ) < gamma3D * (res.Z_star.card : ℝ) ∧
          ((res.Z_star \ sl.Z_ell).Nonempty →
            matDensity sl.Y_ell (res.Z_star \ sl.Z_ell) B <
              2 * matDensity res.Y_star res.Z_star B)))) := by
  have hB_pos : 0 < matDensity Y Z B := lt_trans (by positivity) hB_gt
  have hpow16 := pow_rCubeFuel_ge hε0 gamma3D_pos
  have hfuel_cap : 16 * matDensity Y Z B ≤ (1 + ε * gamma3D / 4) ^ (rCubeFuel ε gamma3D) * matDensity Y Z B :=
    mul_le_mul_of_nonneg_right hpow16 hB_pos.le
  unfold cappedGoodCube
  rcases cappedGoodCubeLoop_spec (rCubeFuel ε gamma3D) S hX hY hZ hA hB hε0 hε_le hD
    hα_nonneg hB_gt le_rfl hfuel_cap with
    ⟨hX_eq, hsubY, hsubZ, hneY, hneZ, _hYp, _hAp, _hBp, _halp, hsteps_le,
      hdens_loop, harea_loop, hmode_or, hbboost_spec, hnorm_spec⟩
  let res := cappedGoodCubeLoop (rCubeFuel ε gamma3D) X Y Z A B ε gamma3D D α_cap (matDensity Y Z B) S
  have hpow_eps_ge : (1 : ℝ) ≤ (1 + ε * gamma3D / 4) ^ res.steps :=
    one_le_pow₀ (by unfold gamma3D; linarith)
  have hdens_scale : (2 : ℝ) ^ res.S_B * matDensity Y Z B ≤ matDensity res.Y_star res.Z_star B := by
    have h1 : (2 : ℝ) ^ res.S_B * 1 * matDensity Y Z B ≤
        (2 : ℝ) ^ res.S_B * (1 + ε * gamma3D / 4) ^ res.steps * matDensity Y Z B := by
      refine mul_le_mul_of_nonneg_right ?_ hB_pos.le
      exact mul_le_mul_of_nonneg_left hpow_eps_ge (by positivity)
    linarith
  have hB_star_le_1 : matDensity res.Y_star res.Z_star B ≤ 1 :=
    matDensity_le_one_of_isBinaryMatrix (isBinaryMatrix_subset hsubY hsubZ hB)
  have hSB_le_D : res.S_B ≤ D :=
    goodCube_scale_le_D hB_gt hdens_scale hB_star_le_1
  have hsteps_real : (res.steps : ℝ) ≤ maxGoodCubeStepsReal ε gamma3D := by
    have h1 : (res.steps : ℝ) ≤ (rCubeFuel ε gamma3D : ℝ) := by exact_mod_cast hsteps_le
    exact h1.trans (rCubeFuel_le_maxGoodCubeStepsReal hε0 hε_le gamma3D_pos
      (by unfold gamma3D; norm_num))
  have hM_bound :
      (M_cube ε gamma3D D)⁻¹ * (2 : ℝ) ^ (-(res.S_B * D : ℤ)) *
        ((Y.card : ℝ) * (Z.card : ℝ)) ≤ (res.Y_star.card : ℝ) * (res.Z_star.card : ℝ) :=
    eq_goodcube_M hε0 (by linarith) (by positivity) hsteps_real harea_loop
  refine ⟨hX_eq, hsubY, hsubZ, hneY, hneZ, hsteps_le, hSB_le_D, hdens_scale,
    hM_bound, hmode_or, ?_, ?_⟩
  · intro hbboost
    have h16 := hbboost_spec hbboost
    rcases max_choice 16 ((2 : ℝ) ^ res.S_B) with hmax | hmax <;> rw [hmax]
    · exact h16
    · exact hdens_scale
  · intro hnorm
    rcases hnorm_spec hnorm with ⟨⟨hlt16, hlt17⟩, hsum_A, _hsum_mom, hslices⟩
    have hSB_le_4 : res.S_B ≤ 4 :=
      goodCube_normal_scale_le_four hB_pos hdens_scale hlt17
    exact ⟨hSB_le_4, ⟨hlt16, hlt17⟩, hsum_A, hslices⟩

lemma submatZeroExt_eq_restrictSubrect [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (A : α → β → ℝ) :
    submatZeroExt X Y A = restrictSubrect A X Y := by
  ext x y; unfold submatZeroExt restrictSubrect; split_ifs <;> rfl

lemma dyadicSift_fst_eq_subrect_or_regular
    (X : Finset α) (Y : Finset β) (A : α → β → ℝ) (ε : ℝ) (D : ℕ) (V : α → ℝ) :
    (dyadicSift X Y A ε D V).1 = "subrect" ∨ (dyadicSift X Y A ε D V).1 = "regular" := by
  classical
  unfold dyadicSift; dsimp only
  cases (List.range D).findSome? _ with
  | some s => exact Or.inl rfl
  | none =>
    split_ifs with hwit
    · dsimp only
      cases (List.range D).findSome? _ with
      | some s => exact Or.inl rfl
      | none => exact Or.inr rfl
    · exact Or.inr rfl

/-- In-code equivalence theorem proving that `cappedGoodRect3DLoop` (`W = 2 ^ 48`) is
an instance of the unified parameterized 2D loop `goodRectLoop` from `BMMGrid/Decomp2D.lean`. -/
theorem cappedGoodRect3DLoop_eq_goodRectLoop_concrete [DecidableEq α] [DecidableEq β]
    (fuel : ℕ) (X : Finset α) (Y : Finset β) (A : α → β → ℝ) (ε : ℝ) (D : ℕ) (α_cap : ℝ)
    (S : TwoStageSamplerOracle β ε) (s_bar steps_done : ℕ) :
    let res3D := cappedGoodRect3DLoop fuel X Y A ε D α_cap S
    goodRectLoop fuel X Y A ε D α_cap (concreteOracleV S) s_bar steps_done =
      (res3D.X_ell, res3D.Y_ell, res3D.tag, s_bar + res3D.S_ell, steps_done + res3D.steps) := by
  classical
  induction fuel generalizing X Y s_bar steps_done with
  | zero => unfold goodRectLoop cappedGoodRect3DLoop; simp
  | succ k ih =>
    unfold goodRectLoop cappedGoodRect3DLoop goodRectStep; dsimp only
    by_cases hcap : matDensity X Y A ≥ α_cap
    · rw [if_pos hcap, if_pos hcap]; simp
    · rw [if_neg hcap, if_neg hcap]
      by_cases htag1 : (minDegree X Y A ε (1 / 2)).2 = 2 ∨
          matDensity (minDegree X Y A ε (1 / 2)).1 Y A ≥ (1 + ε / 2) * matDensity X Y A
      · rw [if_pos htag1, if_pos htag1]; dsimp only
        rw [ih (minDegree X Y A ε (1 / 2)).1 Y s_bar (steps_done + 1)]
        refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_)))
        dsimp only; omega
      · rw [if_neg htag1, if_neg htag1]
        by_cases hcap2 : matDensity (minDegree X Y A ε (1 / 2)).1 Y A ≥ α_cap
        · rw [if_pos hcap2, if_pos hcap2]; simp
        · rw [if_neg hcap2, if_neg hcap2]
          change (match
              if (dyadicSiftConcrete (minDegree X Y A ε (1 / 2)).1 Y A ε D S).1 = "regular" then
                Sum.inr ((minDegree X Y A ε (1 / 2)).1, Y, RectTag.regular, s_bar)
              else
                Sum.inl
                  ((dyadicSiftConcrete (minDegree X Y A ε (1 / 2)).1 Y A ε D S).2.1,
                   (dyadicSiftConcrete (minDegree X Y A ε (1 / 2)).1 Y A ε D S).2.2.1,
                   s_bar + (dyadicSiftConcrete (minDegree X Y A ε (1 / 2)).1 Y A ε D S).2.2.2,
                   (dyadicSiftConcrete (minDegree X Y A ε (1 / 2)).1 Y A ε D S).2.2.2) with
            | Sum.inr (X_out, Y_out, tag_out, s_final) =>
              (X_out, Y_out, tag_out, s_final, steps_done)
            | Sum.inl (X_next, Y_next, s_bar_next, _s_step) =>
              goodRectLoop k X_next Y_next A ε D α_cap (concreteOracleV S) s_bar_next (steps_done + 1)) = _
          rcases dyadicSift_fst_eq_subrect_or_regular
              (minDegree X Y A ε (1 / 2)).1 Y A ε D
              (concreteApproxGridNormV S (minDegree X Y A ε (1 / 2)).1 Y A D) with hsub | hreg
          · change (dyadicSiftConcrete (minDegree X Y A ε (1 / 2)).1 Y A ε D S).1 = "subrect" at hsub
            have hnot_reg :
                (dyadicSiftConcrete (minDegree X Y A ε (1 / 2)).1 Y A ε D S).1 ≠ "regular" := by
              rw [hsub]; decide
            rw [if_neg hnot_reg, if_pos hsub]; dsimp only; rw [ih]
            refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ ?_))) <;> (dsimp only; omega)
          · change (dyadicSiftConcrete (minDegree X Y A ε (1 / 2)).1 Y A ε D S).1 = "regular" at hreg
            have hnot_sub :
                (dyadicSiftConcrete (minDegree X Y A ε (1 / 2)).1 Y A ε D S).1 ≠ "subrect" := by
              rw [hreg]; decide
            rw [if_pos hreg, if_neg hnot_sub]; simp

/-- Top-level 3D-to-2D equivalence theorem proving `cappedGoodRect3D` equals `cappedGoodRectConcrete`. -/
theorem cappedGoodRect3D_eq_cappedGoodRectConcrete [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (A : α → β → ℝ) (ε : ℝ) (D : ℕ) (α_cap : ℝ)
    (S : TwoStageSamplerOracle β ε) :
    let res2D := cappedGoodRectConcrete X Y A ε D α_cap S
    cappedGoodRect3D X Y A ε D α_cap S =
      ⟨res2D.1, res2D.2.1, restrictSubrect A res2D.1 res2D.2.1,
       res2D.2.2.1, res2D.2.2.2.1, res2D.2.2.2.2⟩ := by
  dsimp only
  unfold cappedGoodRectConcrete cappedGoodRect cappedGoodRect3D
  have hfuel : rRect2DFuel ε = rRectFuel ε := rfl
  rw [hfuel, cappedGoodRect3DLoop_eq_goodRectLoop_concrete (rRectFuel ε) X Y A ε D α_cap S 0 0]
  have hsub := (cappedGoodRect3DLoop_subset (rRectFuel ε) X Y A ε D α_cap S).2.2
  cases hres : cappedGoodRect3DLoop (rRectFuel ε) X Y A ε D α_cap S
  rw [hres] at hsub
  dsimp only at hsub ⊢
  rw [hsub, submatZeroExt_eq_restrictSubrect, zero_add, zero_add]

/-- In-code equivalence theorem proving `cappedADecomp3DLoop` equals `aDecompositionLoop` with `concreteOracleV S`. -/
theorem cappedADecomp3DLoop_eq_aDecompositionLoop_concrete [DecidableEq α] [DecidableEq β]
    (fuel : ℕ) (X : Finset α) (Y : Finset β) (A_rem : α → β → ℝ)
    (ε : ℝ) (D : ℕ) (α_low α_cap : ℝ) (S : TwoStageSamplerOracle β ε)
    (acc : List (RectPiece α β)) :
    aDecompositionLoop fuel (rRect2DFuel ε) X Y A_rem ε D
      (max (((2 : ℝ) ^ D)⁻¹) α_low) α_cap (concreteOracleV S) acc =
      acc.reverse ++ cappedADecomp3DLoop fuel X Y A_rem ε D α_low α_cap S := by
  classical
  have hfuel : rRectFuel ε = rRect2DFuel ε := rfl
  have hpow : (2 : ℝ) ^ (-(D : ℤ)) = ((2 : ℝ) ^ D)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  induction fuel generalizing A_rem acc with
  | zero =>
    unfold aDecompositionLoop cappedADecomp3DLoop
    rw [submatZeroExt_eq_restrictSubrect]
  | succ k ih =>
    unfold aDecompositionLoop cappedADecomp3DLoop
    dsimp only; rw [hpow]
    by_cases hle : matDensity X Y A_rem ≤ max (((2 : ℝ) ^ D)⁻¹) α_low
    · rw [if_pos hle, if_pos hle, submatZeroExt_eq_restrictSubrect]
    · rw [if_neg hle, if_neg hle]
      rw [cappedGoodRect3DLoop_eq_goodRectLoop_concrete (rRect2DFuel ε) X Y A_rem ε D α_cap S 0 0]
      dsimp only
      rw [ih]
      have hA_ell : (cappedGoodRect3D X Y A_rem ε D α_cap S).A_ell =
          restrictSubrect A_rem (cappedGoodRect3D X Y A_rem ε D α_cap S).X_ell
            (cappedGoodRect3D X Y A_rem ε D α_cap S).Y_ell := by
        unfold cappedGoodRect3D
        rw [(cappedGoodRect3DLoop_subset (rRectFuel ε) X Y A_rem ε D α_cap S).2.2,
            submatZeroExt_eq_restrictSubrect]
      unfold cappedGoodRect3D at hA_ell ⊢
      rw [hfuel] at hA_ell ⊢
      rw [hA_ell, zero_add, List.reverse_cons, List.append_assoc, List.singleton_append]

/-- Top-level 3D-to-2D equivalence theorem proving `cappedADecomp3D` equals `cappedADecompositionConcrete`. -/
theorem cappedADecomp3D_eq_cappedADecompositionConcrete [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (A : α → β → ℝ) (ε : ℝ) (D : ℕ) (α_low α_cap : ℝ)
    (S : TwoStageSamplerOracle β ε) :
    cappedADecomp3D X Y A ε D α_low α_cap S =
      cappedADecompositionConcrete (rDecompAFuel ε D) X Y A ε D α_low α_cap S := by
  unfold cappedADecompositionConcrete cappedADecomposition cappedADecomp3D
  rw [cappedADecomp3DLoop_eq_aDecompositionLoop_concrete]
  rfl

end CappedGoodCube

#verify_standard_axioms BMMGrid.lem_dyadic_col_degree_bucketing
#verify_standard_axioms BMMGrid.cappedGoodRect3D_spec
#verify_standard_axioms BMMGrid.cappedGoodCubeTracked_snd_le
#verify_standard_axioms BMMGrid.thm_3d_decomp_part1

end BMMGrid
