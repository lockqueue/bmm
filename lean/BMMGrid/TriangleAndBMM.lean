import BMMGrid.KLMUniformity
import BMMGrid.ArithRAM
import BMMGrid.Decomp3D

/-!
# Section 6: Combinatorial Triangle Detection & Boolean Matrix Multiplication (`BMMGrid/TriangleAndBMM.lean`)

This module formalizes Section 6 (`\label{sec:bmm}`) of
`paper.tex`:
1. **Algorithm 6 (`TriangleDetection`, §6)**:
   - Case 1 sparse work bound (`min_le_two_neg_d_mul_rpow_quarter`, `tridet_case1_work_bound`,
     `\eqref{eq:tridet-case1}`, §6).
   - Subcase 2a regularity + pigeonhole triangle existence (`subcase2a_pigeonhole_has_triangle`,
     §6).
   - Subcase 2b Cauchy–Schwarz minimum-degree neighbor scan bound (`subcase2b_scan_work_bound`,
     `\eqref{eq:tridet-case2}`, §6).
   - Piece-level and list-level triangle detection `triangleDetectionOnPieces` and its bottom-up
     cost-tracked counterpart `triangleDetectionOnPiecesTracked` in `CostM`,
     together with exact correctness (`triangleDetectionOnPieces_correct`) and total scan work bound
     (`triangleDetectionOnPiecesTracked_work_bound`).
2. **Lemma 6.1 (`\label{lem:bmm-to-tridet}`, §6)**:
   - Exact integer floor fourth-root block size `blockSizeBMM` ($m = \max(1, \lfloor n^{1/4} \rfloor)$, §6), and block
     extraction `extractBlockMat`.
   - Block-triple BMM reduction `bmmFromTriDet` and its bottom-up cost-tracked counterpart
     `bmmFromTriDetTracked` in `CostM` (`bmmFromTriDetTracked_fst`), with permanent clearing
     $C(x, z) \gets \text{false}$ on every `"triangle"` block scan.
   - Strict decrease of $\operatorname{nnz}(C)$ on every `"triangle"` block scan
     (`nnz_C_strictly_decreases_on_triangle`, §6), bounding the total number of
     $O(m^3)$ exhaustive block scans by $n^2$.
   - Exact correctness (`bmmFromTriDet_correct`) and asymptotic / quantitative operation bound
     (`lem_bmm_to_tridet_time_bound`, §6).
-/

namespace BMMGrid

open scoped BigOperators

/-!
## Part 1: Algorithm 6 Helper Inequalities & Pigeonhole Principle
(`paper.tex` Section 6)
-/

section Algorithm6Helpers

variable {α β γ : Type*}

/-- **Case 1 Exponent Splitting Helper (`min_le_two_neg_d_mul_rpow_quarter`, `paper.tex` §6)**:
For all $u, v \in [0, 1]$ with $\min(u, v) \le 2^{-2d}$,
$$\min(u, v) = \min(u, v)^{1/2} \min(u, v)^{1/4} \min(u, v)^{1/4}
  \le 2^{-d} u^{1/4} v^{1/4}.$$ -/
theorem min_le_two_neg_d_mul_rpow_quarter {u v : ℝ} (hu0 : 0 ≤ u) (hv0 : 0 ≤ v)
    {d : ℕ} (hmin : min u v ≤ (2 : ℝ) ^ (- (2 * (d : ℝ)))) :
    min u v ≤ (2 : ℝ) ^ (- (d : ℝ)) * u ^ (1 / 4 : ℝ) * v ^ (1 / 4 : ℝ) := by
  set m := min u v
  have hm0 : 0 ≤ m := le_min hu0 hv0
  have hmu : m ≤ u := min_le_left u v
  have hmv : m ≤ v := min_le_right u v
  have hm_split : m = m ^ (1 / 2 : ℝ) * m ^ (1 / 4 : ℝ) * m ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add' hm0 (by norm_num), ← Real.rpow_add' hm0 (by norm_num)]
    have h_exp : (1 / 2 : ℝ) + 1 / 4 + 1 / 4 = 1 := by ring
    rw [h_exp, Real.rpow_one]
  have h1 : m ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (- (d : ℝ)) := by
    have h_rpow := Real.rpow_le_rpow hm0 hmin (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at h_rpow
    have h_exp : - (2 * (d : ℝ)) * (1 / 2 : ℝ) = - (d : ℝ) := by ring
    rwa [h_exp] at h_rpow
  have h2 : m ^ (1 / 4 : ℝ) ≤ u ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow hm0 hmu (by norm_num)
  have h3 : m ^ (1 / 4 : ℝ) ≤ v ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow hm0 hmv (by norm_num)
  rw [hm_split]
  have h12 : m ^ (1 / 2 : ℝ) * m ^ (1 / 4 : ℝ) ≤ (2 : ℝ) ^ (- (d : ℝ)) * u ^ (1 / 4 : ℝ) :=
    mul_le_mul h1 h2 (Real.rpow_nonneg hm0 _) (by positivity)
  have h_prod_nonneg : 0 ≤ m ^ (1 / 2 : ℝ) * m ^ (1 / 4 : ℝ) := by positivity
  exact mul_le_mul h12 h3 (Real.rpow_nonneg hm0 _) (by positivity)

/-- **Equation (`\eqref{eq:tridet-case1}`, `tridet_case1_work_bound`, §6)**:
In Case 1 of Algorithm 6, when $\min(\mathbb{E}[A_k], \mathbb{E}[B_k]) \le 2^{-2d}$,
$$\min(\mathbb{E}[A_k], \mathbb{E}[B_k]) |X_k| |Y_k| |Z_k|
  \le 2^{-d} (\mathbb{E}[A_k])^{1/4} (\mathbb{E}[B_k])^{1/4} |X_k| |Y_k| |Z_k|.$$ -/
theorem tridet_case1_work_bound (X_k : Finset α) (Y_k : Finset β) (Z_k : Finset γ)
    (A_k : α → β → ℝ) (B_k : β → γ → ℝ)
    (hA_nonneg : ∀ x ∈ X_k, ∀ y ∈ Y_k, 0 ≤ A_k x y)
    (hB_nonneg : ∀ y ∈ Y_k, ∀ z ∈ Z_k, 0 ≤ B_k y z)
    {d : ℕ}
    (hmin : min (matDensity X_k Y_k A_k) (matDensity Y_k Z_k B_k) ≤ (2 : ℝ) ^ (- (2 * (d : ℝ)))) :
    min (matDensity X_k Y_k A_k) (matDensity Y_k Z_k B_k) *
        (X_k.card : ℝ) * (Y_k.card : ℝ) * (Z_k.card : ℝ) ≤
      (2 : ℝ) ^ (- (d : ℝ)) *
        (matDensity X_k Y_k A_k) ^ (1 / 4 : ℝ) *
        (matDensity Y_k Z_k B_k) ^ (1 / 4 : ℝ) *
        (X_k.card : ℝ) * (Y_k.card : ℝ) * (Z_k.card : ℝ) := by
  have hA0 : 0 ≤ matDensity X_k Y_k A_k :=
    expectSet_nonneg (fun x hx => expectSet_nonneg (fun y hy => hA_nonneg x hx y hy))
  have hB0 : 0 ≤ matDensity Y_k Z_k B_k :=
    expectSet_nonneg (fun y hy => expectSet_nonneg (fun z hz => hB_nonneg y hy z hz))
  have h_base := min_le_two_neg_d_mul_rpow_quarter hA0 hB0 hmin
  have h_cards : 0 ≤ (X_k.card : ℝ) * (Y_k.card : ℝ) * (Z_k.card : ℝ) := by positivity
  have h_mul := mul_le_mul_of_nonneg_right h_base h_cards
  linarith

/-- **Subcase 2a Pigeonhole Principle (`subcase2a_pigeonhole_has_triangle`, `paper.tex` §6)**:
When $A_k, B_k^T$ are $(\varepsilon, 2, 2d)$-regular and $\varepsilon$-min-degree with
$\varepsilon \in (0, 1/160]$, $2 / \varepsilon \le d$, $\mathbb{E}[A_k] > 0$, $\mathbb{E}[B_k] > 0$,
and $|S_k| > 2^{-\varepsilon d} |X_k| |Z_k|$ where $S_k = \{(x, z) \in X_k \times Z_k : C(x, z) = \text{true}\}$,
there exists $(x, y, z) \in X_k \times Y_k \times Z_k$ with $A_k(x, y) > 0$, $B_k(y, z) > 0$, and
$C(x, z) = \text{true}$. -/
theorem subcase2a_pigeonhole_has_triangle [DecidableEq α] [DecidableEq γ]
    {X_k : Finset α} {Y_k : Finset β} {Z_k : Finset γ}
    (hX : X_k.Nonempty) (hY : Y_k.Nonempty) (hZ : Z_k.Nonempty)
    (A_k : α → β → ℝ) (B_k : β → γ → ℝ) (C : α → γ → Bool)
    (hA_nonneg : ∀ x ∈ X_k, ∀ y ∈ Y_k, 0 ≤ A_k x y)
    (hB_nonneg : ∀ y ∈ Y_k, ∀ z ∈ Z_k, 0 ≤ B_k y z)
    (hA_pos : 0 < matDensity X_k Y_k A_k)
    (hB_pos : 0 < matDensity Y_k Z_k B_k)
    {ε : ℝ} {d : ℕ} (hε_pos : 0 < ε) (hε_le : ε ≤ 1 / 160)
    (hd_ge : 2 / ε ≤ (d : ℝ))
    (hA_reg : IsGridRegular X_k Y_k A_k ε 2 (2 * d))
    (hB_reg : IsGridRegular Z_k Y_k (matTranspose B_k) ε 2 (2 * d))
    (hA_min : IsEpsMinDegree X_k Y_k A_k ε)
    (hB_min : IsEpsMinDegree Z_k Y_k (matTranspose B_k) ε)
    (hSk_dense :
      (2 : ℝ) ^ (- (ε * (d : ℝ))) * ((X_k.card : ℝ) * (Z_k.card : ℝ)) <
        (((X_k ×ˢ Z_k).filter (fun xz => C xz.1 xz.2 = true)).card : ℝ)) :
    ∃ x ∈ X_k, ∃ y ∈ Y_k, ∃ z ∈ Z_k,
      0 < A_k x y ∧ 0 < B_k y z ∧ C x z = true := by
  have hD_even : Even (2 * d) := ⟨d, by ring⟩
  have hD_ge : 4 / ε ≤ ((2 * d : ℕ) : ℝ) := by
    push_cast
    have h4 : 4 / ε = 2 * (2 / ε) := by ring
    linarith
  have h_prop := (prop_regular_matrices_uniform_product hX hY hZ A_k B_k
    hA_nonneg hB_nonneg hA_pos hB_pos hε_pos (by linarith) hD_even hD_ge
    hA_reg hB_reg hA_min hB_min).2 hε_le
  have h_exp_eq : - (ε * ((2 * d : ℕ) : ℝ) / 2) = - (ε * (d : ℝ)) := by
    push_cast
    ring
  rw [h_exp_eq] at h_prop
  classical
  let S_k := (X_k ×ˢ Z_k).filter (fun xz => C xz.1 xz.2 = true)
  let good := (X_k ×ˢ Z_k).filter (fun xz =>
    (1 / 2 : ℝ) * (matDensity X_k Y_k A_k * matDensity Y_k Z_k B_k) ≤
      normMatMul Y_k A_k B_k xz.1 xz.2)
  have h_sum_cards_real :
      ((X_k ×ˢ Z_k).card : ℝ) < (S_k.card : ℝ) + (good.card : ℝ) := by
    rw [Finset.card_product, Nat.cast_mul]
    have h_good := h_prop.2
    linarith
  have h_sum_cards_nat : (X_k ×ˢ Z_k).card < S_k.card + good.card := by
    exact_mod_cast h_sum_cards_real
  have h_union_sub : S_k ∪ good ⊆ X_k ×ˢ Z_k :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have h_union_le : (S_k ∪ good).card ≤ (X_k ×ˢ Z_k).card :=
    Finset.card_le_card h_union_sub
  have h_ie := Finset.card_union_add_card_inter S_k good
  have h_inter_pos : 0 < (S_k ∩ good).card := by omega
  obtain ⟨⟨x, z⟩, hxz_inter⟩ := Finset.card_pos.mp h_inter_pos
  have hxz_Sk : (x, z) ∈ S_k := (Finset.mem_inter.mp hxz_inter).1
  have hxz_good : (x, z) ∈ good := (Finset.mem_inter.mp hxz_inter).2
  have hx : x ∈ X_k := (Finset.mem_product.mp (Finset.mem_filter.mp hxz_Sk).1).1
  have hz : z ∈ Z_k := (Finset.mem_product.mp (Finset.mem_filter.mp hxz_Sk).1).2
  have hC : C x z = true := (Finset.mem_filter.mp hxz_Sk).2
  have h_norm_pos : 0 < normMatMul Y_k A_k B_k x z :=
    lt_of_lt_of_le h_prop.1 (Finset.mem_filter.mp hxz_good).2
  unfold normMatMul expectSet at h_norm_pos
  have hY_card_pos : (0 : ℝ) < Y_k.card := Nat.cast_pos.mpr hY.card_pos
  have h_sum_pos : 0 < ∑ y ∈ Y_k, A_k x y * B_k y z :=
    (div_pos_iff_of_pos_right hY_card_pos).mp h_norm_pos
  have h_exists_y : ∃ y ∈ Y_k, 0 < A_k x y * B_k y z := by
    by_contra! h_all_nonpos
    have h_le_zero : ∑ y ∈ Y_k, A_k x y * B_k y z ≤ 0 :=
      Finset.sum_nonpos h_all_nonpos
    linarith
  obtain ⟨y, hy, h_prod_pos⟩ := h_exists_y
  have hAy_nonneg : 0 ≤ A_k x y := hA_nonneg x hx y hy
  have hBy_nonneg : 0 ≤ B_k y z := hB_nonneg y hy z hz
  have hAy_pos : 0 < A_k x y := by
    rcases eq_or_lt_of_le hAy_nonneg with h_eq | h_lt
    · exfalso; rw [← h_eq, zero_mul] at h_prod_pos; exact lt_irrefl 0 h_prod_pos
    · exact h_lt
  have hBy_pos : 0 < B_k y z := by
    rcases eq_or_lt_of_le hBy_nonneg with h_eq | h_lt
    · exfalso; rw [← h_eq, mul_zero] at h_prod_pos; exact lt_irrefl 0 h_prod_pos
    · exact h_lt
  exact ⟨x, hx, y, hy, z, hz, hAy_pos, hBy_pos, hC⟩

/-- Elementary bound $\min(u, v) \le \sqrt{u v}$ for $u, v \ge 0$ (`paper.tex` §6). -/
lemma min_le_sqrt_mul {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    min u v ≤ Real.sqrt (u * v) := by
  have hm0 : 0 ≤ min u v := le_min hu hv
  rw [← Real.sqrt_sq hm0]
  refine Real.sqrt_le_sqrt ?_
  rw [sq]
  exact mul_le_mul (min_le_left u v) (min_le_right u v) hm0 hu

/-- Helper inequality $\sqrt{u} \le u^{1/4}$ for $u \in [0, 1]$ (`paper.tex` §6). -/
lemma sqrt_le_rpow_quarter_of_le_one {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.sqrt u ≤ u ^ (1 / 4 : ℝ) := by
  rcases eq_or_lt_of_le hu0 with rfl | hu_pos
  · simp
  · rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hu_pos hu1 (by norm_num)

/-- **Equation (`\eqref{eq:tridet-case2}`, `subcase2b_scan_work_bound`, §6)**:
In Subcase 2b of Algorithm 6, when $S_k \subseteq X_k \times Z_k$ satisfies
$|S_k| \le 2^{-\varepsilon d} |X_k| |Z_k|$ and $\mathbb{E}[A_k], \mathbb{E}[B_k] \in [0, 1]$,
$$\sum_{(x, z) \in S_k} |Y_k| \min(\deg_{A_k}(x), \deg_{B_k^T}(z))
  \le |Y_k| \sqrt{|S_k|} \sqrt{\left(\sum_{x \in X_k}\deg_{A_k}(x)\right)
      \left(\sum_{z \in Z_k}\deg_{B_k^T}(z)\right)}
  \le 2^{-\varepsilon d / 2} (\mathbb{E}[A_k])^{1/4} (\mathbb{E}[B_k])^{1/4} |X_k| |Y_k| |Z_k|.$$ -/
theorem subcase2b_scan_work_bound {X_k : Finset α} {Y_k : Finset β} {Z_k : Finset γ}
    {S_k : Finset (α × γ)} (hSk_sub : S_k ⊆ X_k ×ˢ Z_k)
    (A_k : α → β → ℝ) (B_k : β → γ → ℝ)
    (hA_nonneg : ∀ x ∈ X_k, ∀ y ∈ Y_k, 0 ≤ A_k x y)
    (hB_nonneg : ∀ y ∈ Y_k, ∀ z ∈ Z_k, 0 ≤ B_k y z)
    (hA_dens_le : matDensity X_k Y_k A_k ≤ 1)
    (hB_dens_le : matDensity Y_k Z_k B_k ≤ 1)
    {ε : ℝ} {d : ℕ}
    (hSk_sparse :
      (S_k.card : ℝ) ≤ (2 : ℝ) ^ (- (ε * (d : ℝ))) * ((X_k.card : ℝ) * (Z_k.card : ℝ))) :
    ∑ xz ∈ S_k, (Y_k.card : ℝ) * min (rowDeg Y_k A_k xz.1) (rowDeg Y_k (matTranspose B_k) xz.2) ≤
      (Y_k.card : ℝ) * Real.sqrt (S_k.card : ℝ) *
        Real.sqrt ((∑ x ∈ X_k, rowDeg Y_k A_k x) * (∑ z ∈ Z_k, rowDeg Y_k (matTranspose B_k) z)) ∧
    (Y_k.card : ℝ) * Real.sqrt (S_k.card : ℝ) *
        Real.sqrt ((∑ x ∈ X_k, rowDeg Y_k A_k x) * (∑ z ∈ Z_k, rowDeg Y_k (matTranspose B_k) z)) ≤
      (2 : ℝ) ^ (- (ε * (d : ℝ) / 2)) *
        (matDensity X_k Y_k A_k) ^ (1 / 4 : ℝ) *
        (matDensity Y_k Z_k B_k) ^ (1 / 4 : ℝ) *
        (X_k.card : ℝ) * (Y_k.card : ℝ) * (Z_k.card : ℝ) := by
  have hdegA_nonneg : ∀ x ∈ X_k, 0 ≤ rowDeg Y_k A_k x :=
    fun x hx => expectSet_nonneg (fun y hy => hA_nonneg x hx y hy)
  have hdegB_nonneg : ∀ z ∈ Z_k, 0 ≤ rowDeg Y_k (matTranspose B_k) z :=
    fun z hz => expectSet_nonneg (fun y hy => hB_nonneg y hy z hz)
  -- Step 1 (`paper.tex` §6): min(u, v) ≤ √(u v) and Cauchy–Schwarz over S_k
  have h_sum_min_le_sqrt :
      ∑ xz ∈ S_k, min (rowDeg Y_k A_k xz.1) (rowDeg Y_k (matTranspose B_k) xz.2) ≤
        ∑ xz ∈ S_k, Real.sqrt (rowDeg Y_k A_k xz.1 * rowDeg Y_k (matTranspose B_k) xz.2) := by
    refine Finset.sum_le_sum (fun xz hxz => ?_)
    rcases Finset.mem_product.mp (hSk_sub hxz) with ⟨hx, hz⟩
    exact min_le_sqrt_mul (hdegA_nonneg xz.1 hx) (hdegB_nonneg xz.2 hz)
  have h_cs := Finset.sum_mul_sq_le_sq_mul_sq S_k
    (fun _ => (1 : ℝ))
    (fun xz => Real.sqrt (rowDeg Y_k A_k xz.1 * rowDeg Y_k (matTranspose B_k) xz.2))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h_cs
  have h_sq_sum_eq :
      ∑ xz ∈ S_k, (Real.sqrt (rowDeg Y_k A_k xz.1 * rowDeg Y_k (matTranspose B_k) xz.2)) ^ 2 =
        ∑ xz ∈ S_k, rowDeg Y_k A_k xz.1 * rowDeg Y_k (matTranspose B_k) xz.2 := by
    refine Finset.sum_congr rfl (fun xz hxz => ?_)
    rcases Finset.mem_product.mp (hSk_sub hxz) with ⟨hx, hz⟩
    exact Real.sq_sqrt (mul_nonneg (hdegA_nonneg xz.1 hx) (hdegB_nonneg xz.2 hz))
  rw [h_sq_sum_eq] at h_cs
  have h_sub_prod :
      ∑ xz ∈ S_k, rowDeg Y_k A_k xz.1 * rowDeg Y_k (matTranspose B_k) xz.2 ≤
        (∑ x ∈ X_k, rowDeg Y_k A_k x) * (∑ z ∈ Z_k, rowDeg Y_k (matTranspose B_k) z) := by
    calc
      ∑ xz ∈ S_k, rowDeg Y_k A_k xz.1 * rowDeg Y_k (matTranspose B_k) xz.2
        ≤ ∑ xz ∈ X_k ×ˢ Z_k, rowDeg Y_k A_k xz.1 * rowDeg Y_k (matTranspose B_k) xz.2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hSk_sub (fun xz hxz _ => ?_)
          rcases Finset.mem_product.mp hxz with ⟨hx, hz⟩
          exact mul_nonneg (hdegA_nonneg xz.1 hx) (hdegB_nonneg xz.2 hz)
      _ = (∑ x ∈ X_k, rowDeg Y_k A_k x) * (∑ z ∈ Z_k, rowDeg Y_k (matTranspose B_k) z) := by
          rw [Finset.sum_product]
          simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  have h_cs_prod :
      (∑ xz ∈ S_k, Real.sqrt (rowDeg Y_k A_k xz.1 * rowDeg Y_k (matTranspose B_k) xz.2)) ^ 2 ≤
        (S_k.card : ℝ) *
          ((∑ x ∈ X_k, rowDeg Y_k A_k x) * (∑ z ∈ Z_k, rowDeg Y_k (matTranspose B_k) z)) :=
    le_trans h_cs (mul_le_mul_of_nonneg_left h_sub_prod (Nat.cast_nonneg _))
  have h_sqrt_cs :
      ∑ xz ∈ S_k, Real.sqrt (rowDeg Y_k A_k xz.1 * rowDeg Y_k (matTranspose B_k) xz.2) ≤
        Real.sqrt (S_k.card : ℝ) *
          Real.sqrt ((∑ x ∈ X_k, rowDeg Y_k A_k x) * (∑ z ∈ Z_k, rowDeg Y_k (matTranspose B_k) z)) := by
    have h_lhs_nonneg : 0 ≤ ∑ xz ∈ S_k,
        Real.sqrt (rowDeg Y_k A_k xz.1 * rowDeg Y_k (matTranspose B_k) xz.2) :=
      Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
    rw [← Real.sqrt_sq h_lhs_nonneg, ← Real.sqrt_mul (Nat.cast_nonneg _)]
    exact Real.sqrt_le_sqrt h_cs_prod
  have h_part1 :
      ∑ xz ∈ S_k, (Y_k.card : ℝ) * min (rowDeg Y_k A_k xz.1) (rowDeg Y_k (matTranspose B_k) xz.2) ≤
        (Y_k.card : ℝ) * Real.sqrt (S_k.card : ℝ) *
          Real.sqrt ((∑ x ∈ X_k, rowDeg Y_k A_k x) * (∑ z ∈ Z_k, rowDeg Y_k (matTranspose B_k) z)) := by
    rw [← Finset.mul_sum, mul_assoc]
    exact mul_le_mul_of_nonneg_left (le_trans h_sum_min_le_sqrt h_sqrt_cs) (Nat.cast_nonneg _)
  refine ⟨h_part1, ?_⟩
  -- Step 2 (`paper.tex` §6): Express sums via matDensity and apply |S_k| ≤ 2^{-ε d}|X_k||Z_k|
  have h_sumA_le : ∑ x ∈ X_k, rowDeg Y_k A_k x ≤ matDensity X_k Y_k A_k * (X_k.card : ℝ) := by
    unfold matDensity expectSet
    rcases Nat.eq_zero_or_pos X_k.card with h0 | hpos
    · rw [Finset.card_eq_zero.mp h0]; simp
    · have hne : (X_k.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
      rw [div_mul_cancel₀ _ hne]
  have hBT_dens_eq : matDensity Z_k Y_k (matTranspose B_k) = matDensity Y_k Z_k B_k :=
    expectSet_comm Z_k Y_k (matTranspose B_k)
  have h_sumB_le :
      ∑ z ∈ Z_k, rowDeg Y_k (matTranspose B_k) z ≤ matDensity Y_k Z_k B_k * (Z_k.card : ℝ) := by
    rw [← hBT_dens_eq]
    unfold matDensity expectSet
    rcases Nat.eq_zero_or_pos Z_k.card with h0 | hpos
    · rw [Finset.card_eq_zero.mp h0]; simp
    · have hne : (Z_k.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
      rw [div_mul_cancel₀ _ hne]
  have hA0 : 0 ≤ matDensity X_k Y_k A_k :=
    expectSet_nonneg (fun x hx => hdegA_nonneg x hx)
  have hB0 : 0 ≤ matDensity Y_k Z_k B_k :=
    expectSet_nonneg (fun y hy => expectSet_nonneg (fun z hz => hB_nonneg y hy z hz))
  have h_sqrt_Sk :
      Real.sqrt (S_k.card : ℝ) ≤
        (2 : ℝ) ^ (- (ε * (d : ℝ) / 2)) * Real.sqrt ((X_k.card : ℝ) * (Z_k.card : ℝ)) := by
    have h_pow_sq : ((2 : ℝ) ^ (- (ε * (d : ℝ) / 2))) ^ 2 = (2 : ℝ) ^ (- (ε * (d : ℝ))) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1; push_cast; ring
    rw [← Real.sqrt_sq (by positivity : 0 ≤ (2 : ℝ) ^ (- (ε * (d : ℝ) / 2))),
      ← Real.sqrt_mul (sq_nonneg _), h_pow_sq]
    exact Real.sqrt_le_sqrt hSk_sparse
  have h_sqrt_sums :
      Real.sqrt ((∑ x ∈ X_k, rowDeg Y_k A_k x) * (∑ z ∈ Z_k, rowDeg Y_k (matTranspose B_k) z)) ≤
        (matDensity X_k Y_k A_k) ^ (1 / 4 : ℝ) *
          (matDensity Y_k Z_k B_k) ^ (1 / 4 : ℝ) *
          Real.sqrt ((X_k.card : ℝ) * (Z_k.card : ℝ)) := by
    have h_prod_le :
        (∑ x ∈ X_k, rowDeg Y_k A_k x) * (∑ z ∈ Z_k, rowDeg Y_k (matTranspose B_k) z) ≤
          (matDensity X_k Y_k A_k * matDensity Y_k Z_k B_k) *
            ((X_k.card : ℝ) * (Z_k.card : ℝ)) := by
      calc
        (∑ x ∈ X_k, rowDeg Y_k A_k x) * (∑ z ∈ Z_k, rowDeg Y_k (matTranspose B_k) z)
          ≤ (matDensity X_k Y_k A_k * (X_k.card : ℝ)) *
              (matDensity Y_k Z_k B_k * (Z_k.card : ℝ)) :=
            mul_le_mul h_sumA_le h_sumB_le
              (Finset.sum_nonneg hdegB_nonneg) (by positivity)
        _ = (matDensity X_k Y_k A_k * matDensity Y_k Z_k B_k) *
              ((X_k.card : ℝ) * (Z_k.card : ℝ)) := by ring
    calc
      Real.sqrt ((∑ x ∈ X_k, rowDeg Y_k A_k x) * (∑ z ∈ Z_k, rowDeg Y_k (matTranspose B_k) z))
        ≤ Real.sqrt ((matDensity X_k Y_k A_k * matDensity Y_k Z_k B_k) *
            ((X_k.card : ℝ) * (Z_k.card : ℝ))) := Real.sqrt_le_sqrt h_prod_le
      _ = Real.sqrt (matDensity X_k Y_k A_k) * Real.sqrt (matDensity Y_k Z_k B_k) *
            Real.sqrt ((X_k.card : ℝ) * (Z_k.card : ℝ)) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hA0]
      _ ≤ (matDensity X_k Y_k A_k) ^ (1 / 4 : ℝ) *
            (matDensity Y_k Z_k B_k) ^ (1 / 4 : ℝ) *
            Real.sqrt ((X_k.card : ℝ) * (Z_k.card : ℝ)) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
          exact mul_le_mul
            (sqrt_le_rpow_quarter_of_le_one hA0 hA_dens_le)
            (sqrt_le_rpow_quarter_of_le_one hB0 hB_dens_le)
            (Real.sqrt_nonneg _) (Real.rpow_nonneg hA0 _)
  have h_mul_both := mul_le_mul h_sqrt_Sk h_sqrt_sums
    (Real.sqrt_nonneg _) (by positivity)
  have h_mul_Y := mul_le_mul_of_nonneg_left h_mul_both (Nat.cast_nonneg Y_k.card)
  have h_sq_XZ :
      Real.sqrt ((X_k.card : ℝ) * (Z_k.card : ℝ)) *
        Real.sqrt ((X_k.card : ℝ) * (Z_k.card : ℝ)) =
      (X_k.card : ℝ) * (Z_k.card : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  calc
    (Y_k.card : ℝ) * Real.sqrt (S_k.card : ℝ) *
        Real.sqrt ((∑ x ∈ X_k, rowDeg Y_k A_k x) * (∑ z ∈ Z_k, rowDeg Y_k (matTranspose B_k) z))
      = (Y_k.card : ℝ) * (Real.sqrt (S_k.card : ℝ) *
          Real.sqrt ((∑ x ∈ X_k, rowDeg Y_k A_k x) *
            (∑ z ∈ Z_k, rowDeg Y_k (matTranspose B_k) z))) := by ring
    _ ≤ (Y_k.card : ℝ) *
          (((2 : ℝ) ^ (- (ε * (d : ℝ) / 2)) * Real.sqrt ((X_k.card : ℝ) * (Z_k.card : ℝ))) *
            ((matDensity X_k Y_k A_k) ^ (1 / 4 : ℝ) *
              (matDensity Y_k Z_k B_k) ^ (1 / 4 : ℝ) *
              Real.sqrt ((X_k.card : ℝ) * (Z_k.card : ℝ)))) := h_mul_Y
    _ = (2 : ℝ) ^ (- (ε * (d : ℝ) / 2)) *
          (matDensity X_k Y_k A_k) ^ (1 / 4 : ℝ) *
          (matDensity Y_k Z_k B_k) ^ (1 / 4 : ℝ) *
          (Y_k.card : ℝ) *
          (Real.sqrt ((X_k.card : ℝ) * (Z_k.card : ℝ)) *
            Real.sqrt ((X_k.card : ℝ) * (Z_k.card : ℝ))) := by ring
    _ = (2 : ℝ) ^ (- (ε * (d : ℝ) / 2)) *
          (matDensity X_k Y_k A_k) ^ (1 / 4 : ℝ) *
          (matDensity Y_k Z_k B_k) ^ (1 / 4 : ℝ) *
          (X_k.card : ℝ) * (Y_k.card : ℝ) * (Z_k.card : ℝ) := by
        rw [h_sq_XZ]; ring

end Algorithm6Helpers

/-!
## Part 2: Algorithm 6 — Piece-Level & Decomposition-Level Triangle Detection
(`paper.tex` Section 6)
-/

section Algorithm6

/-- Mathematical predicate asserting that a 3D piece `P : CubePiece α β γ` contains a triangle
with query matrix `C` (`paper.tex` §6). -/
def pieceHasTriangle {α β γ : Type*} (C : α → γ → Bool) (P : CubePiece α β γ) : Prop :=
  ∃ x ∈ P.X_k, ∃ y ∈ P.Y_k, ∃ z ∈ P.Z_k,
    0 < P.A_k x y ∧ 0 < P.B_k y z ∧ C x z = true

/-- Real-threshold specification of Lines 5–12 (`\label{line:tri-sparse}`–`\label{line:tri-cs}`) of Algorithm 6 (`TriangleDetection`) on a single 3D
piece `P : CubePiece (Fin n) (Fin n) (Fin n)` (`paper.tex` §6). -/
noncomputable def detectOnPieceReal (n d : ℕ) (C : Fin n → Fin n → Bool)
    (P : CubePiece (Fin n) (Fin n) (Fin n)) : Bool :=
  let densA := matDensity P.X_k P.Y_k P.A_k
  let densB := matDensity P.Y_k P.Z_k P.B_k
  let suppB := (P.Y_k ×ˢ P.Z_k).filter (fun yz => decide (0 < P.B_k yz.1 yz.2))
  let suppA := (P.X_k ×ˢ P.Y_k).filter (fun xy => decide (0 < P.A_k xy.1 xy.2))
  -- Line 5 (`\label{line:tri-sparse}`): Case 1 (sparse or single-edge piece: min(E[A_k], E[B_k]) ≤ 2^{-D} or nnz(B_k) ≤ 1)
  if decide (min densA densB ≤ (2 : ℝ) ^ (- (2 * (d : ℝ)))) ||
      decide (suppB.card ≤ 1) then
    -- Lines 6–7 (`\label{line:tri-scanb}`, `\label{line:tri-scana}`): scan smaller support
    if decide (suppB.card ≤ 1) || decide (densB < densA) then
      -- Line 6 (`\label{line:tri-scanb}`): for each (y, z) ∈ supp(B_k) and x ∈ X_k
      decide (∃ yz ∈ suppB, ∃ x ∈ P.X_k, 0 < P.A_k x yz.1 ∧ C x yz.2 = true)
    else
      -- Line 7 (`\label{line:tri-scana}`): for each (x, y) ∈ supp(A_k) and z ∈ Z_k
      decide (∃ xy ∈ suppA, ∃ z ∈ P.Z_k, 0 < P.B_k xy.2 z ∧ C xy.1 z = true)
  else
    -- Lines 8–9 (`\label{line:tri-reg}`, `\label{line:tri-sk}`): Case 2 (regular piece with densA > 2^{-2d}, densB > 2^{-2d}, nnz(B_k) > 1)
    let S_k := (P.X_k ×ˢ P.Z_k).filter (fun xz => C xz.1 xz.2)
    -- Line 10 (`\label{line:tri-pigeon}`): Subcase 2a (pigeonhole threshold |S_k| > 2^{-ε d}|X_k||Z_k|, ε = 1/160)
    if decide ((2 : ℝ) ^ (- ((1 / 160 : ℝ) * (d : ℝ))) *
        ((P.X_k.card : ℝ) * (P.Z_k.card : ℝ)) < (S_k.card : ℝ)) then
      true
    else
      -- Lines 11–12 (`\label{line:tri-adj}`, `\label{line:tri-cs}`): Subcase 2b (minimum-degree neighbor scan over (x, z) ∈ S_k)
      let N_A : Fin n → Finset (Fin n) := fun x => P.Y_k.filter (fun y => decide (0 < P.A_k x y))
      let N_B : Fin n → Finset (Fin n) := fun z => P.Y_k.filter (fun y => decide (0 < P.B_k y z))
      decide (∃ xz ∈ S_k,
        if (N_A xz.1).card ≤ (N_B xz.2).card then
          ∃ y ∈ N_A xz.1, 0 < P.B_k y xz.2
        else
          ∃ y ∈ N_B xz.2, 0 < P.A_k xz.1 y)

/-- Computable integer power-and-cross-multiplication check for Algorithm 6 Line 5 (`\label{line:tri-sparse}`, `Case 1` sparse
piece test $\min(\mathbb{E}[A_k], \mathbb{E}[B_k]) \le 2^{-D}$). -/
def checkSparsePieceNatTracked (nnzA cardXY nnzB cardYZ D : ℕ) : CostM Bool :=
  CostM.bind (powNatTracked 2 D) (fun pD =>
    CostM.bind (mulNatTracked nnzA pD) (fun lhsA =>
      CostM.bind (cmpLeNatTracked lhsA cardXY) (fun cA =>
        CostM.bind (mulNatTracked nnzB pD) (fun lhsB =>
          CostM.bind (cmpLeNatTracked lhsB cardYZ) (fun cB =>
            retTracked (cA || cB))))))

@[simp]
lemma checkSparsePieceNatTracked_fst (nnzA cardXY nnzB cardYZ D : ℕ) :
    (checkSparsePieceNatTracked nnzA cardXY nnzB cardYZ D).1 =
      (decide (nnzA * 2 ^ D ≤ cardXY) || decide (nnzB * 2 ^ D ≤ cardYZ)) := rfl

theorem checkSparsePieceNatTracked_iff_min_le {nnzA cardXY nnzB cardYZ D : ℕ}
    (hXY : 0 < cardXY) (hYZ : 0 < cardYZ) :
    (checkSparsePieceNatTracked nnzA cardXY nnzB cardYZ D).1 = true ↔
      min ((nnzA : ℝ) / (cardXY : ℝ)) ((nnzB : ℝ) / (cardYZ : ℝ)) ≤ (2 : ℝ) ^ (-(D : ℝ)) := by
  rw [checkSparsePieceNatTracked_fst, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq,
    min_le_iff]
  have hXY_pos : (0 : ℝ) < (cardXY : ℝ) := Nat.cast_pos.mpr hXY
  have hYZ_pos : (0 : ℝ) < (cardYZ : ℝ) := Nat.cast_pos.mpr hYZ
  have h2D_pos : (0 : ℝ) < ((2 ^ D : ℕ) : ℝ) := by positivity
  have hrpow : (2 : ℝ) ^ (-(D : ℝ)) = 1 / ((2 ^ D : ℕ) : ℝ) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, Nat.cast_pow, Nat.cast_ofNat]
  rw [hrpow, div_le_div_iff₀ hXY_pos h2D_pos, div_le_div_iff₀ hYZ_pos h2D_pos, one_mul, one_mul]
  exact ⟨fun h => h.elim (fun h1 => Or.inl (by exact_mod_cast h1))
      (fun h2 => Or.inr (by exact_mod_cast h2)),
    fun h => h.elim (fun h1 => Or.inl (by exact_mod_cast h1))
      (fun h2 => Or.inr (by exact_mod_cast h2))⟩

/-- Exact computable integer power-and-multiplication check for Algorithm 6 Line 10 (`\label{line:tri-pigeon}`, `Subcase 2a`
dense $C_k$ test $2^{-d/160} |X_k||Z_k| < |S_k|$ for all $d \in \mathbb{N}$):
evaluates $(|X_k|\cdot |Z_k|)^{160} < |S_k|^{160} \cdot 2^d$ in `CostM Bool` with zero floating-point
or `Real.rpow` operations. -/
def checkDenseCSubcase2aExactNatTracked (cardSk cardX cardZ d : ℕ) : CostM Bool :=
  CostM.bind (powNatTracked 2 d) (fun pd =>
    CostM.bind (mulNatTracked cardX cardZ) (fun xz =>
      CostM.bind (powNatTracked xz 160) (fun lhs =>
        CostM.bind (powNatTracked cardSk 160) (fun sk160 =>
          CostM.bind (mulNatTracked sk160 pd) (fun rhs =>
            cmpLtNatTracked lhs rhs)))))

@[simp]
lemma checkDenseCSubcase2aExactNatTracked_fst (cardSk cardX cardZ d : ℕ) :
    (checkDenseCSubcase2aExactNatTracked cardSk cardX cardZ d).1 =
      decide ((cardX * cardZ) ^ 160 < cardSk ^ 160 * 2 ^ d) := rfl

/-- Exact unconditional equivalence for Algorithm 6 Line 10 (`\label{line:tri-pigeon}`):
for **every** $d \in \mathbb{N}$ (without any divisibility requirement on $d$),
`checkDenseCSubcase2aExactNatTracked cardSk cardX cardZ d` is equivalent (`↔`) to
$2^{-d/160} |X_k||Z_k| < |S_k|$. -/
theorem checkDenseCSubcase2aExactNatTracked_iff_lt (cardSk cardX cardZ d : ℕ) :
    (checkDenseCSubcase2aExactNatTracked cardSk cardX cardZ d).1 = true ↔
      (2 : ℝ) ^ (- ((1 / 160 : ℝ) * (d : ℝ))) * ((cardX : ℝ) * (cardZ : ℝ)) < (cardSk : ℝ) := by
  rw [checkDenseCSubcase2aExactNatTracked_fst, decide_eq_true_eq]
  set lhs : ℝ := (2 : ℝ) ^ (- ((1 / 160 : ℝ) * (d : ℝ))) * ((cardX : ℝ) * (cardZ : ℝ))
  set rhs : ℝ := (cardSk : ℝ)
  have hlhs_nn : 0 ≤ lhs := by dsimp [lhs]; positivity
  have hrhs_nn : 0 ≤ rhs := by dsimp [rhs]; positivity
  have hpow_iff : lhs < rhs ↔ lhs ^ (160 : ℝ) < rhs ^ (160 : ℝ) :=
    ⟨fun h => Real.rpow_lt_rpow hlhs_nn h (by norm_num),
     fun h => by
       by_contra hge
       push_neg at hge
       exact not_le_of_gt h (Real.rpow_le_rpow hrhs_nn hge (by norm_num))⟩
  have hlhs_pow :
      lhs ^ (160 : ℝ) = ((2 : ℝ) ^ (d : ℝ))⁻¹ * ((cardX : ℝ) * (cardZ : ℝ)) ^ 160 := by
    dsimp [lhs]
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by norm_num)]
    have hexp : -((1 / 160 : ℝ) * (d : ℝ)) * (160 : ℝ) = -(d : ℝ) := by ring
    rw [hexp, Real.rpow_neg (by norm_num)]
    congr 1
    exact Real.rpow_natCast ((cardX : ℝ) * (cardZ : ℝ)) 160
  have hrhs_pow : rhs ^ (160 : ℝ) = (cardSk : ℝ) ^ 160 :=
    Real.rpow_natCast (cardSk : ℝ) 160
  rw [hpow_iff, hlhs_pow, hrhs_pow, Real.rpow_natCast, inv_mul_eq_div,
    div_lt_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ d)]
  exact_mod_cast Iff.rfl

lemma sum_binary_eq_card_filter_pos {n : ℕ} (X Y : Finset (Fin n)) (M : Fin n → Fin n → ℝ)
    (h_bin : ∀ x y, M x y = 0 ∨ M x y = 1) :
    (∑ x ∈ X, ∑ y ∈ Y, M x y) =
      (((X ×ˢ Y).filter (fun xy => decide (0 < M xy.1 xy.2))).card : ℝ) := by
  rw [← Finset.sum_product', Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun xy _ => ?_)
  rcases h_bin xy.1 xy.2 with h0 | h1
  · simp [h0]
  · simp [h1]

lemma matDensity_binary_eq_card_div {n : ℕ} (X Y : Finset (Fin n)) (M : Fin n → Fin n → ℝ)
    (h_bin : ∀ x y, M x y = 0 ∨ M x y = 1) :
    matDensity X Y M =
      (((X ×ˢ Y).filter (fun xy => decide (0 < M xy.1 xy.2))).card : ℝ) /
        ((X.card * Y.card : ℕ) : ℝ) := by
  unfold matDensity rowDeg expectSet
  rw [← Finset.sum_div, div_div, mul_comm (Y.card : ℝ) (X.card : ℝ), ← Nat.cast_mul,
    sum_binary_eq_card_filter_pos X Y M h_bin]

/-- Purely integer-arithmetic cost-tracked execution of Lines 5–12 (`\label{line:tri-sparse}`–`\label{line:tri-cs}`) of Algorithm 6
(`detectOnPieceNatTracked`, `paper.tex` §6) that evaluates all three
threshold tests using `checkSparsePieceNatTracked`, `cmpRatCrossLtTracked`, and
`checkDenseCSubcase2aExactNatTracked` with zero real exponentiation or division. -/
noncomputable def detectOnPieceNatTracked (n d : ℕ) (C : Fin n → Fin n → Bool)
    (P : CubePiece (Fin n) (Fin n) (Fin n)) : CostM Bool :=
  CostM.bind (scanMatrixPairTracked P.X_k P.Y_k P.Z_k ()) (fun _ =>
    let suppB := (P.Y_k ×ˢ P.Z_k).filter (fun yz => decide (0 < P.B_k yz.1 yz.2))
    let suppA := (P.X_k ×ˢ P.Y_k).filter (fun xy => decide (0 < P.A_k xy.1 xy.2))
    let cardXY := P.X_k.card * P.Y_k.card
    let cardYZ := P.Y_k.card * P.Z_k.card
    CostM.bind
      (checkSparsePieceNatTracked suppA.card cardXY suppB.card cardYZ (2 * d))
      (fun isSparse =>
        CostM.bind (cmpLeNatTracked suppB.card 1) (fun isB1 =>
          if isSparse || isB1 then
            CostM.bind
              (cmpRatCrossLtTracked suppB.card cardYZ suppA.card cardXY)
              (fun isBLtA =>
                if isB1 || isBLtA then
                  evalSupportScanTracked suppB P.X_k
                    (fun yz x => decide (0 < P.A_k x yz.1 ∧ C x yz.2 = true))
                else
                  evalSupportScanTracked suppA P.Z_k
                    (fun xy z => decide (0 < P.B_k xy.2 z ∧ C xy.1 z = true)))
          else
            CostM.bind (scanMatrixTracked P.X_k P.Z_k ()) (fun _ =>
              let S_k := (P.X_k ×ˢ P.Z_k).filter (fun xz => C xz.1 xz.2)
              CostM.bind
                (checkDenseCSubcase2aExactNatTracked S_k.card P.X_k.card P.Z_k.card d)
                (fun c3 =>
                  if c3 then
                    retTracked true
                  else
                    let N_A : Fin n → Finset (Fin n) :=
                      fun x => P.Y_k.filter (fun y => decide (0 < P.A_k x y))
                    let N_B : Fin n → Finset (Fin n) :=
                      fun z => P.Y_k.filter (fun y => decide (0 < P.B_k y z))
                    evalMinNbrScanTracked S_k
                      (fun xz => N_A xz.1) (fun xz => N_B xz.2)
                      (fun xz y => decide (0 < P.B_k y xz.2))
                      (fun xz y => decide (0 < P.A_k xz.1 y)))))))

/-- Exact behavioral equivalence between the purely integer-arithmetic `detectOnPieceNatTracked`
and `detectOnPieceReal` for every binary piece $P \in \mathcal{S}$. -/
theorem detectOnPieceNatTracked_fst_eq_detectOnPiece (n d : ℕ) (C : Fin n → Fin n → Bool)
    (P : CubePiece (Fin n) (Fin n) (Fin n))
    (h_bin : ∀ x y z, (P.A_k x y = 0 ∨ P.A_k x y = 1) ∧ (P.B_k y z = 0 ∨ P.B_k y z = 1)) :
    (detectOnPieceNatTracked n d C P).1 = detectOnPieceReal n d C P := by
  unfold detectOnPieceNatTracked detectOnPieceReal
  simp only [CostM.bind_fst]
  set suppB := (P.Y_k ×ˢ P.Z_k).filter (fun yz => decide (0 < P.B_k yz.1 yz.2))
  set suppA := (P.X_k ×ˢ P.Y_k).filter (fun xy => decide (0 < P.A_k xy.1 xy.2))
  set cardXY := P.X_k.card * P.Y_k.card
  set cardYZ := P.Y_k.card * P.Z_k.card
  have hdensA : matDensity P.X_k P.Y_k P.A_k = (suppA.card : ℝ) / (cardXY : ℝ) :=
    matDensity_binary_eq_card_div P.X_k P.Y_k P.A_k (fun x y => (h_bin x y x).1)
  have hdensB : matDensity P.Y_k P.Z_k P.B_k = (suppB.card : ℝ) / (cardYZ : ℝ) :=
    matDensity_binary_eq_card_div P.Y_k P.Z_k P.B_k (fun y z => (h_bin y y z).2)
  have hc1_eq :
      ((checkSparsePieceNatTracked suppA.card cardXY suppB.card cardYZ (2 * d)).1 ||
        (cmpLeNatTracked suppB.card 1).1) =
      (decide (min (matDensity P.X_k P.Y_k P.A_k) (matDensity P.Y_k P.Z_k P.B_k) ≤
          (2 : ℝ) ^ (- (2 * (d : ℝ)))) ||
        decide (suppB.card ≤ 1)) := by
    apply Bool.eq_iff_iff.mpr
    rw [Bool.or_eq_true, Bool.or_eq_true, cmpLeNatTracked_fst, decide_eq_true_eq]
    by_cases hb1 : suppB.card ≤ 1
    · simp [hb1]
    · simp only [hb1, or_false]
      have hsuppB_le : suppB.card ≤ cardYZ := by
        have h1 := Finset.card_le_card (Finset.filter_subset
          (fun yz : Fin n × Fin n => decide (0 < P.B_k yz.1 yz.2)) (P.Y_k ×ˢ P.Z_k))
        rwa [Finset.card_product] at h1
      have hsuppA_le : suppA.card ≤ cardXY := by
        have h1 := Finset.card_le_card (Finset.filter_subset
          (fun xy : Fin n × Fin n => decide (0 < P.A_k xy.1 xy.2)) (P.X_k ×ˢ P.Y_k))
        rwa [Finset.card_product] at h1
      have hYZ_pos : 0 < cardYZ :=
        Nat.lt_of_lt_of_le (by omega : 0 < suppB.card) hsuppB_le
      have hdensB_nn : 0 ≤ matDensity P.Y_k P.Z_k P.B_k := by rw [hdensB]; positivity
      have h2d_nn : (0 : ℝ) ≤ (2 : ℝ) ^ (- (2 * (d : ℝ))) := by positivity
      rcases Nat.eq_zero_or_pos cardXY with hXY0 | hXY_pos
      · have hsuppA0 : suppA.card = 0 := Nat.eq_zero_of_le_zero (hsuppA_le.trans_eq hXY0)
        have hdensA0 : matDensity P.X_k P.Y_k P.A_k = 0 := by
          rw [hdensA, hXY0, Nat.cast_zero, div_zero]
        have hmin0 : min (matDensity P.X_k P.Y_k P.A_k) (matDensity P.Y_k P.Z_k P.B_k) = 0 := by
          rw [hdensA0, min_eq_left hdensB_nn]
        rw [checkSparsePieceNatTracked_fst, hsuppA0, hXY0, hmin0, Bool.or_eq_true,
          decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq, Nat.zero_mul]
        exact ⟨fun _ => h2d_nn, fun _ => Or.inl le_rfl⟩
      · rw [checkSparsePieceNatTracked_iff_min_le hXY_pos hYZ_pos, decide_eq_true_eq,
          ← hdensA, ← hdensB]
        push_cast
        rfl
  rw [hc1_eq]
  by_cases h_case1 :
      (decide (min (matDensity P.X_k P.Y_k P.A_k) (matDensity P.Y_k P.Z_k P.B_k) ≤
          (2 : ℝ) ^ (- (2 * (d : ℝ)))) ||
        decide (suppB.card ≤ 1)) = true
  · rw [if_pos h_case1, if_pos h_case1, CostM.bind_fst]
    have hc2_eq :
        ((cmpLeNatTracked suppB.card 1).1 ||
          (cmpRatCrossLtTracked suppB.card cardYZ suppA.card cardXY).1) =
        (decide (suppB.card ≤ 1) ||
          decide (matDensity P.Y_k P.Z_k P.B_k < matDensity P.X_k P.Y_k P.A_k)) := by
      apply Bool.eq_iff_iff.mpr
      rw [Bool.or_eq_true, Bool.or_eq_true, cmpLeNatTracked_fst, cmpRatCrossLtTracked_fst,
        decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq]
      by_cases hb1 : suppB.card ≤ 1
      · simp [hb1]
      · simp only [hb1, false_or]
        have hsuppB_le : suppB.card ≤ cardYZ := by
          have h1 := Finset.card_le_card (Finset.filter_subset
            (fun yz : Fin n × Fin n => decide (0 < P.B_k yz.1 yz.2)) (P.Y_k ×ˢ P.Z_k))
          rwa [Finset.card_product] at h1
        have hsuppA_le : suppA.card ≤ cardXY := by
          have h1 := Finset.card_le_card (Finset.filter_subset
            (fun xy : Fin n × Fin n => decide (0 < P.A_k xy.1 xy.2)) (P.X_k ×ˢ P.Y_k))
          rwa [Finset.card_product] at h1
        have hYZ_pos : 0 < cardYZ :=
          Nat.lt_of_lt_of_le (by omega : 0 < suppB.card) hsuppB_le
        have hdensB_pos : 0 < matDensity P.Y_k P.Z_k P.B_k := by
          rw [hdensB]; exact div_pos (by exact_mod_cast (by omega : 0 < suppB.card))
            (Nat.cast_pos.mpr hYZ_pos)
        rcases Nat.eq_zero_or_pos cardXY with hXY0 | hXY_pos
        · have hsuppA0 : suppA.card = 0 := Nat.eq_zero_of_le_zero (hsuppA_le.trans_eq hXY0)
          have hdensA0 : matDensity P.X_k P.Y_k P.A_k = 0 := by
            rw [hdensA, hXY0, Nat.cast_zero, div_zero]
          rw [hXY0, hsuppA0, hdensA0, Nat.mul_zero, Nat.zero_mul]
          exact ⟨fun h => False.elim (Nat.lt_irrefl 0 h),
            fun h => False.elim (not_lt_of_gt hdensB_pos h)⟩
        · rw [hdensB, hdensA, div_lt_div_iff₀ (Nat.cast_pos.mpr hYZ_pos) (Nat.cast_pos.mpr hXY_pos)]
          exact_mod_cast Iff.rfl
    rw [hc2_eq]
    by_cases h_sub1 :
        (decide (suppB.card ≤ 1) ||
          decide (matDensity P.Y_k P.Z_k P.B_k < matDensity P.X_k P.Y_k P.A_k)) = true
    · rw [if_pos h_sub1, if_pos h_sub1, evalSupportScanTracked_fst]
      simp [decide_eq_true_eq]
    · rw [if_neg h_sub1, if_neg h_sub1, evalSupportScanTracked_fst]
      simp [decide_eq_true_eq]
  · rw [if_neg h_case1, if_neg h_case1, CostM.bind_fst, CostM.bind_fst]
    set S_k := (P.X_k ×ˢ P.Z_k).filter (fun xz => C xz.1 xz.2)
    have hc3_eq :
        (checkDenseCSubcase2aExactNatTracked S_k.card P.X_k.card P.Z_k.card d).1 =
          decide ((2 : ℝ) ^ (- ((1 / 160 : ℝ) * (d : ℝ))) *
            ((P.X_k.card : ℝ) * (P.Z_k.card : ℝ)) < (S_k.card : ℝ)) := by
      apply Bool.eq_iff_iff.mpr
      rw [checkDenseCSubcase2aExactNatTracked_iff_lt, decide_eq_true_eq]
    rw [hc3_eq]
    by_cases h_sub2a :
        decide ((2 : ℝ) ^ (- ((1 / 160 : ℝ) * (d : ℝ))) *
          ((P.X_k.card : ℝ) * (P.Z_k.card : ℝ)) < (S_k.card : ℝ)) = true
    · rw [if_pos h_sub2a, if_pos h_sub2a, retTracked_fst]
    · rw [if_neg h_sub2a, if_neg h_sub2a, evalMinNbrScanTracked_fst]
      simp [decide_eq_true_eq]

/-- Bottom-up cost-tracked execution of Lines 5–12 (`\label{line:tri-sparse}`–`\label{line:tri-cs}`) of Algorithm 6 (`TriangleDetection`) on a single
3D piece `P : CubePiece (Fin n) (Fin n) (Fin n)` in `CostM Bool` (
`paper.tex` §6), executing all threshold comparisons via `checkSparsePieceNatTracked`,
`cmpLeNatTracked`, `cmpRatCrossLtTracked`, and `checkDenseCSubcase2aExactNatTracked` with zero
untracked `Real` threshold operations. -/
noncomputable def detectOnPieceTracked (n d : ℕ) (C : Fin n → Fin n → Bool)
    (P : CubePiece (Fin n) (Fin n) (Fin n)) : CostM Bool :=
  detectOnPieceNatTracked n d C P

/-- Untracked execution of Lines 5–12 (`\label{line:tri-sparse}`–`\label{line:tri-cs}`) of Algorithm 6 (`TriangleDetection`) on a single 3D piece
`P : CubePiece (Fin n) (Fin n) (Fin n)` (`paper.tex` §6). -/
noncomputable def detectOnPiece (n d : ℕ) (C : Fin n → Fin n → Bool)
    (P : CubePiece (Fin n) (Fin n) (Fin n)) : Bool :=
  (detectOnPieceTracked n d C P).1

/-- Projection equivalence `detectOnPieceTracked_fst`. -/
@[simp]
theorem detectOnPieceTracked_fst (n d : ℕ) (C : Fin n → Fin n → Bool)
    (P : CubePiece (Fin n) (Fin n) (Fin n)) :
    (detectOnPieceTracked n d C P).1 = detectOnPiece n d C P := rfl

theorem detectOnPiece_eq_detectOnPieceReal (n d : ℕ) (C : Fin n → Fin n → Bool)
    (P : CubePiece (Fin n) (Fin n) (Fin n))
    (h_bin : ∀ x y z, (P.A_k x y = 0 ∨ P.A_k x y = 1) ∧ (P.B_k y z = 0 ∨ P.B_k y z = 1)) :
    detectOnPiece n d C P = detectOnPieceReal n d C P :=
  detectOnPieceNatTracked_fst_eq_detectOnPiece n d C P h_bin

/-- Untracked execution of Lines 4–13 (`\label{line:tri-loop}`–`\label{line:tri-false}`) of Algorithm 6 (`TriangleDetection`) across a list of 3D
decomposition pieces `S : List (CubePiece (Fin n) (Fin n) (Fin n))` (`paper.tex` §6). -/
noncomputable def triangleDetectionOnPieces (n d : ℕ) (C : Fin n → Fin n → Bool)
    (S : List (CubePiece (Fin n) (Fin n) (Fin n))) : Bool :=
  S.foldl (fun acc P => acc || detectOnPiece n d C P) false

/-- Bottom-up cost-tracked execution of Lines 4–13 (`\label{line:tri-loop}`–`\label{line:tri-false}`) of Algorithm 6 (`TriangleDetection`) across a
list of 3D decomposition pieces in `CostM Bool` (`paper.tex` §6). -/
noncomputable def triangleDetectionOnPiecesTracked (n d : ℕ) (C : Fin n → Fin n → Bool)
    (S : List (CubePiece (Fin n) (Fin n) (Fin n))) : CostM Bool :=
  foldlListTracked
    (fun acc P =>
      CostM.bind (detectOnPieceTracked n d C P) (fun r => retTracked (acc || r)))
    false S

/-- Projection equivalence `triangleDetectionOnPiecesTracked_fst`. -/
@[simp]
theorem triangleDetectionOnPiecesTracked_fst (n d : ℕ) (C : Fin n → Fin n → Bool)
    (S : List (CubePiece (Fin n) (Fin n) (Fin n))) :
    (triangleDetectionOnPiecesTracked n d C S).1 = triangleDetectionOnPieces n d C S := by
  unfold triangleDetectionOnPiecesTracked triangleDetectionOnPieces
  rw [foldlListTracked_fst]
  simp only [CostM.bind_fst, retTracked_fst, detectOnPieceTracked_fst]

/-- Specification of a valid 3D decomposition $\mathcal{S}$ produced by `CappedABDecomposition`
(Lemmas 5.3–5.5 & 5.9 (`\label{lem:cube-step}`, `\label{lem:children-invariants}`, `\label{lem:potential}`, `\label{lem:recurrence}`) / Theorem 1.1, `paper.tex` §6) for input binary matrices $A, B$ on
$[n] \times [n]$ at parameter $d$:
1. Every piece $P \in \mathcal{S}$ has non-negative $\{0, 1\}$-valued entries (`0 ≤ A_k ≤ 1`,
   `0 ≤ B_k ≤ 1`, and non-zeros $\ge 1$).
2. For every $(x, z) \in [n]^2$, $(A \star B)(x, z) = \text{true} \iff \exists P \in \mathcal{S},
   \exists y \in P.Y_k, x \in P.X_k \wedge z \in P.Z_k \wedge 0 < P.A_k x y \wedge 0 < P.B_k y z$
   (capturing Boolean witness equivalence for `boolMatMul`; see `cappedABDecomposition_sum_eq` in `Decomp3D.lean` for the exact bilinear partition $AB = \sum_{k=1}^K A_k B_k$).
3. Every piece with $\min(\mathbb{E}[A_k], \mathbb{E}[B_k]) > 2^{-2d}$ and $\operatorname{nnz}(B_k) > 1$
   has non-empty $X_k, Y_k, Z_k$ and is $(1/160, 2, 2d)$-regular and $(1/160)$-min-degree on both
   $A_k$ and $B_k^T$ (Definition 1.1 `\label{def:pieces}`, Theorem 1.1 `\label{thm:main-decomp}`, & Lemma 5.4 `\label{lem:children-invariants}`, `paper.tex` §1.2, §5.3 & §6).
4. The $(1/4, 1/4)$-potential satisfies $C_{1/4, 1/4}(\mathcal{S}) \le 128 n^3$. -/
structure IsValid3DDecomposition (n d : ℕ) (A B : Fin n → Fin n → Bool)
    (S : List (CubePiece (Fin n) (Fin n) (Fin n))) : Prop where
  piece_entries_binary :
    ∀ P ∈ S, ∀ x y z,
      (P.A_k x y = 0 ∨ P.A_k x y = 1) ∧ (P.B_k y z = 0 ∨ P.B_k y z = 1)
  partition_boolMatMul :
    ∀ x z : Fin n,
      boolMatMul n A B x z = true ↔
        ∃ P ∈ S, x ∈ P.X_k ∧ z ∈ P.Z_k ∧ ∃ y ∈ P.Y_k, 0 < P.A_k x y ∧ 0 < P.B_k y z
  regular_pieces_spec :
    ∀ P ∈ S,
      (2 : ℝ) ^ (- (2 * (d : ℝ))) < min (matDensity P.X_k P.Y_k P.A_k) (matDensity P.Y_k P.Z_k P.B_k) →
      1 < ((P.Y_k ×ˢ P.Z_k).filter (fun yz => decide (0 < P.B_k yz.1 yz.2))).card →
      P.X_k.Nonempty ∧ P.Y_k.Nonempty ∧ P.Z_k.Nonempty ∧
      IsGridRegular P.X_k P.Y_k P.A_k (1 / 160 : ℝ) 2 (2 * d) ∧
      IsGridRegular P.Z_k P.Y_k (matTranspose P.B_k) (1 / 160 : ℝ) 2 (2 * d) ∧
      IsEpsMinDegree P.X_k P.Y_k P.A_k (1 / 160 : ℝ) ∧
      IsEpsMinDegree P.Z_k P.Y_k (matTranspose P.B_k) (1 / 160 : ℝ)
  potential_bound :
    cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ) S ≤ 128 * (n : ℝ) ^ 3

/-- Correctness of `detectOnPiece` on a single valid piece $P \in \mathcal{S}$
(`paper.tex` §6):
`detectOnPiece n d C P = true ↔ pieceHasTriangle C P`. -/
theorem detectOnPiece_eq_true_iff {n d : ℕ} (hd : 320 ≤ d) (C : Fin n → Fin n → Bool)
    {P : CubePiece (Fin n) (Fin n) (Fin n)}
    (h_bin : ∀ x y z, (P.A_k x y = 0 ∨ P.A_k x y = 1) ∧ (P.B_k y z = 0 ∨ P.B_k y z = 1))
    (h_reg :
      (2 : ℝ) ^ (- (2 * (d : ℝ))) < min (matDensity P.X_k P.Y_k P.A_k) (matDensity P.Y_k P.Z_k P.B_k) →
      1 < ((P.Y_k ×ˢ P.Z_k).filter (fun yz => decide (0 < P.B_k yz.1 yz.2))).card →
      P.X_k.Nonempty ∧ P.Y_k.Nonempty ∧ P.Z_k.Nonempty ∧
      IsGridRegular P.X_k P.Y_k P.A_k (1 / 160 : ℝ) 2 (2 * d) ∧
      IsGridRegular P.Z_k P.Y_k (matTranspose P.B_k) (1 / 160 : ℝ) 2 (2 * d) ∧
      IsEpsMinDegree P.X_k P.Y_k P.A_k (1 / 160 : ℝ) ∧
      IsEpsMinDegree P.Z_k P.Y_k (matTranspose P.B_k) (1 / 160 : ℝ)) :
    detectOnPiece n d C P = true ↔ pieceHasTriangle C P := by
  rw [detectOnPiece_eq_detectOnPieceReal n d C P h_bin]
  unfold detectOnPieceReal pieceHasTriangle
  dsimp only
  split_ifs with h_case1 h_sub1 h_sub2a
  · -- Case 1a: scan supp(B_k) × X_k
    simp only [decide_eq_true_eq, Finset.mem_filter, Finset.mem_product, Prod.exists]
    constructor
    · rintro ⟨y, z, ⟨⟨hy, hz⟩, hB⟩, x, hx, hA, hC⟩
      exact ⟨x, hx, y, hy, z, hz, hA, hB, hC⟩
    · rintro ⟨x, hx, y, hy, z, hz, hA, hB, hC⟩
      exact ⟨y, z, ⟨⟨hy, hz⟩, hB⟩, x, hx, hA, hC⟩
  · -- Case 1b: scan supp(A_k) × Z_k
    simp only [decide_eq_true_eq, Finset.mem_filter, Finset.mem_product, Prod.exists]
    constructor
    · rintro ⟨x, y, ⟨⟨hx, hy⟩, hA⟩, z, hz, hB, hC⟩
      exact ⟨x, hx, y, hy, z, hz, hA, hB, hC⟩
    · rintro ⟨x, hx, y, hy, z, hz, hA, hB, hC⟩
      exact ⟨x, y, ⟨⟨hx, hy⟩, hA⟩, z, hz, hB, hC⟩
  · -- Subcase 2a: Pigeonhole with Proposition 3.1 (`paper.tex` §6)
    simp only [true_iff]
    rcases not_or.mp (mt (Bool.or_eq_true _ _).mpr h_case1) with ⟨h_not_min, h_not_suppB⟩
    have h_min_gt :
        (2 : ℝ) ^ (- (2 * (d : ℝ))) <
          min (matDensity P.X_k P.Y_k P.A_k) (matDensity P.Y_k P.Z_k P.B_k) :=
      not_le.mp (of_decide_eq_false (Bool.eq_false_iff.mpr h_not_min))
    have h_suppB_gt :
        1 < ((P.Y_k ×ˢ P.Z_k).filter (fun yz => decide (0 < P.B_k yz.1 yz.2))).card :=
      not_le.mp (of_decide_eq_false (Bool.eq_false_iff.mpr h_not_suppB))
    obtain ⟨hX, hY, hZ, hA_reg, hB_reg, hA_min, hB_min⟩ := h_reg h_min_gt h_suppB_gt
    have hA_nonneg : ∀ x ∈ P.X_k, ∀ y ∈ P.Y_k, 0 ≤ P.A_k x y := by
      intro x _ y _
      rcases (h_bin x y x).1 with h0 | h1 <;> linarith
    have hB_nonneg : ∀ y ∈ P.Y_k, ∀ z ∈ P.Z_k, 0 ≤ P.B_k y z := by
      intro y _ z _
      rcases (h_bin y y z).2 with h0 | h1 <;> linarith
    have h_two_pos : (0 : ℝ) < (2 : ℝ) ^ (- (2 * (d : ℝ))) := by positivity
    have hA_pos : 0 < matDensity P.X_k P.Y_k P.A_k :=
      lt_of_lt_of_le (lt_trans h_two_pos h_min_gt) (min_le_left _ _)
    have hB_pos : 0 < matDensity P.Y_k P.Z_k P.B_k :=
      lt_of_lt_of_le (lt_trans h_two_pos h_min_gt) (min_le_right _ _)
    have hd_ge : 2 / (1 / 160 : ℝ) ≤ (d : ℝ) := by
      have hd_real : (320 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith
    have hSk_dense :
        (2 : ℝ) ^ (- ((1 / 160 : ℝ) * (d : ℝ))) * ((P.X_k.card : ℝ) * (P.Z_k.card : ℝ)) <
          (((P.X_k ×ˢ P.Z_k).filter (fun xz => C xz.1 xz.2 = true)).card : ℝ) :=
      of_decide_eq_true h_sub2a
    exact subcase2a_pigeonhole_has_triangle hX hY hZ P.A_k P.B_k C
      hA_nonneg hB_nonneg hA_pos hB_pos (by norm_num) (le_rfl) hd_ge
      hA_reg hB_reg hA_min hB_min hSk_dense
  · -- Subcase 2b: Minimum-degree adjacency scan over S_k (`paper.tex` §6)
    simp only [decide_eq_true_eq, Finset.mem_filter, Finset.mem_product, Prod.exists]
    constructor
    · rintro ⟨x, z, ⟨⟨hx, hz⟩, hC⟩, h_scan⟩
      split_ifs at h_scan with h_deg
      · rcases h_scan with ⟨y, ⟨hy, hA⟩, hB⟩
        exact ⟨x, hx, y, hy, z, hz, hA, hB, hC⟩
      · rcases h_scan with ⟨y, ⟨hy, hB⟩, hA⟩
        exact ⟨x, hx, y, hy, z, hz, hA, hB, hC⟩
    · rintro ⟨x, hx, y, hy, z, hz, hA, hB, hC⟩
      refine ⟨x, z, ⟨⟨hx, hz⟩, hC⟩, ?_⟩
      split_ifs with h_deg
      · exact ⟨y, ⟨hy, hA⟩, hB⟩
      · exact ⟨y, ⟨hy, hB⟩, hA⟩

/-- Helper lemma for `List.foldl (fun acc x => acc || f x)` over a list. -/
lemma foldl_or_eq_true_iff {α : Type*} (f : α → Bool) (xs : List α) (init : Bool) :
    xs.foldl (fun acc x => acc || f x) init = true ↔ init = true ∨ ∃ x ∈ xs, f x = true := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, Bool.or_eq_true, List.mem_cons, exists_eq_or_imp]
    tauto

/-- **Correctness of Algorithm 6 (`triangleDetectionOnPieces_correct`, `paper.tex` §6)**:
For any valid 3D decomposition $\mathcal{S}$ of $(A, B)$ with $d \ge 320$,
`triangleDetectionOnPieces n d C S = hasTriangle n A B C`. -/
theorem triangleDetectionOnPieces_correct {n d : ℕ} (hd : 320 ≤ d)
    (A B C : Fin n → Fin n → Bool)
    (S : List (CubePiece (Fin n) (Fin n) (Fin n)))
    (hS : IsValid3DDecomposition n d A B S) :
    triangleDetectionOnPieces n d C S = hasTriangle n A B C := by
  apply Bool.eq_iff_iff.mpr
  unfold triangleDetectionOnPieces
  rw [foldl_or_eq_true_iff, hasTriangle_eq_true_iff]
  simp only [Bool.false_eq_true, false_or]
  constructor
  · rintro ⟨P, hP_mem, hP_det⟩
    have h_tri := (detectOnPiece_eq_true_iff hd C
      (hS.piece_entries_binary P hP_mem)
      (hS.regular_pieces_spec P hP_mem)).mp hP_det
    rcases h_tri with ⟨x, hx, y, hy, z, hz, hA, hB, hC⟩
    have h_bmm : boolMatMul n A B x z = true :=
      (hS.partition_boolMatMul x z).mpr ⟨P, hP_mem, hx, hz, y, hy, hA, hB⟩
    rcases (boolMatMul_eq_true_iff n A B x z).mp h_bmm with ⟨y', hy'A, hy'B⟩
    exact ⟨x, y', z, hy'A, hy'B, hC⟩
  · rintro ⟨x, y, z, hA, hB, hC⟩
    have h_bmm : boolMatMul n A B x z = true :=
      (boolMatMul_eq_true_iff n A B x z).mpr ⟨y, hA, hB⟩
    obtain ⟨P, hP_mem, hx, hz, y', hy', hA', hB'⟩ :=
      (hS.partition_boolMatMul x z).mp h_bmm
    refine ⟨P, hP_mem, ?_⟩
    exact (detectOnPiece_eq_true_iff hd C
      (hS.piece_entries_binary P hP_mem)
      (hS.regular_pieces_spec P hP_mem)).mpr ⟨x, hx, y', hy', z, hz, hA', hB', hC⟩

/-- Helper lemma: support cardinality of a binary $\{0, 1\}$-valued matrix $M$ on $X \times Y$ is at
most $\mathbb{E}[M] |X| |Y|$. -/
lemma card_filter_pos_prod_le_matDensity {n : ℕ} (X Y : Finset (Fin n)) (M : Fin n → Fin n → ℝ)
    (h_bin : ∀ x y, M x y = 0 ∨ M x y = 1) :
    (((X ×ˢ Y).filter (fun xy => decide (0 < M xy.1 xy.2))).card : ℝ) ≤
      matDensity X Y M * ((X.card : ℝ) * (Y.card : ℝ)) := by
  let supp := (X ×ˢ Y).filter (fun xy => decide (0 < M xy.1 xy.2))
  have hM_nonneg : ∀ x y, 0 ≤ M x y := by
    intro x y; rcases h_bin x y with h0 | h1 <;> linarith
  have hM0 : 0 ≤ matDensity X Y M :=
    expectSet_nonneg (fun x _ => expectSet_nonneg (fun y _ => hM_nonneg x y))
  have h_sum_ge : (supp.card : ℝ) ≤ ∑ x ∈ X, ∑ y ∈ Y, M x y := by
    rw [← Finset.sum_product']
    calc
      (supp.card : ℝ) = ∑ _xy ∈ supp, (1 : ℝ) := by simp
      _ ≤ ∑ xy ∈ supp, M xy.1 xy.2 := by
          refine Finset.sum_le_sum (fun xy hxy => ?_)
          have h_pos : 0 < M xy.1 xy.2 := of_decide_eq_true (Finset.mem_filter.mp hxy).2
          rcases h_bin xy.1 xy.2 with h0 | h1 <;> linarith
      _ ≤ ∑ xy ∈ X ×ˢ Y, M xy.1 xy.2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun xy _ _ => hM_nonneg xy.1 xy.2)
  rcases Nat.eq_zero_or_pos (X.card * Y.card) with h0 | hpos
  · have h_empty : supp.card = 0 := by
      have h_le : supp.card ≤ (X ×ˢ Y).card := Finset.card_le_card (Finset.filter_subset _ _)
      rw [Finset.card_product] at h_le; omega
    change (supp.card : ℝ) ≤ _
    rw [h_empty, Nat.cast_zero]
    positivity
  · have hX_ne : (X.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_mul_pos_right hpos).ne'
    have hY_ne : (Y.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_mul_pos_left hpos).ne'
    have h_eq : matDensity X Y M * ((X.card : ℝ) * (Y.card : ℝ)) =
        ∑ x ∈ X, ∑ y ∈ Y, M x y := by
      unfold matDensity rowDeg expectSet
      simp only [← Finset.sum_div]
      field_simp
    change (supp.card : ℝ) ≤ _
    linarith

/-- Helper lemma: row support cardinality of a binary $\{0, 1\}$-valued matrix $M$ on $Y$ is at most
$|Y| \deg_M(x)$. -/
lemma card_filter_pos_le_card_mul_rowDeg {n : ℕ} (Y : Finset (Fin n)) (M : Fin n → Fin n → ℝ)
    (x : Fin n) (h_bin : ∀ y, M x y = 0 ∨ M x y = 1) :
    ((Y.filter (fun y => decide (0 < M x y))).card : ℝ) ≤ (Y.card : ℝ) * rowDeg Y M x := by
  let N_x := Y.filter (fun y => decide (0 < M x y))
  rcases Nat.eq_zero_or_pos Y.card with h0 | hpos
  · have h_empty : N_x.card = 0 := by
      have h_le : N_x.card ≤ Y.card :=
        Finset.card_le_card (Finset.filter_subset (fun y => decide (0 < M x y)) Y)
      omega
    change (N_x.card : ℝ) ≤ _
    simp [h_empty, h0]
  · have hY_ne : (Y.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
    unfold rowDeg expectSet
    rw [mul_div_cancel₀ _ hY_ne]
    change (N_x.card : ℝ) ≤ _
    calc
      (N_x.card : ℝ) = ∑ _y ∈ N_x, (1 : ℝ) := by simp
      _ ≤ ∑ y ∈ N_x, M x y := by
          refine Finset.sum_le_sum (fun y hy => ?_)
          have h_pos : 0 < M x y := of_decide_eq_true (Finset.mem_filter.mp hy).2
          rcases h_bin y with h0 | h1 <;> linarith
      _ ≤ ∑ y ∈ Y, M x y := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun y _ _ => ?_)
          rcases h_bin y with h0 | h1 <;> linarith

/-- Helper lemma: if `suppB.card ≤ 1` and `X_k : Finset (Fin n)`, then
`(suppB.card : ℝ) * (X_k.card : ℝ) ≤ (n : ℝ) ^ 2`. -/
lemma card_mul_le_sq_of_le_one {n : ℕ} {c : ℕ} (hc : c ≤ 1) (X_k : Finset (Fin n)) :
    (c : ℝ) * (X_k.card : ℝ) ≤ (n : ℝ) ^ 2 := by
  have hX : X_k.card ≤ n := by
    have := Finset.card_le_univ X_k
    simpa using this
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · have hX0 : X_k.card = 0 := Nat.eq_zero_of_le_zero hX
    simp [hX0]
  · have hc_n : c ≤ n := le_trans hc hn_pos
    have h_mul : c * X_k.card ≤ n * n := Nat.mul_le_mul hc_n hX
    rw [sq]
    exact_mod_cast h_mul

lemma bitLengthNat_le_of_le_pow {u n k : ℕ} (hu : u ≤ n ^ k) :
    bitLengthNat u ≤ k * n + 1 := by
  unfold bitLengthNat
  have hn : n ≤ 2 ^ n := (Nat.lt_two_pow_self).le
  have hu2 : u ≤ 2 ^ (k * n) := by
    calc
      u ≤ n ^ k := hu
      _ ≤ (2 ^ n) ^ k := Nat.pow_le_pow_left hn k
      _ = 2 ^ (n * k) := (Nat.pow_mul 2 n k).symm
      _ = 2 ^ (k * n) := by rw [Nat.mul_comm]
  have hlog : Nat.log 2 u ≤ k * n := by
    calc
      Nat.log 2 u ≤ Nat.log 2 (2 ^ (k * n)) := Nat.log_mono_right hu2
      _ = k * n := Nat.log_pow (by norm_num) (k * n)
  omega

lemma bitLengthNat_le_of_le_pow_mul_two_pow {u n k e : ℕ} (hu : u ≤ n ^ k * 2 ^ e) :
    bitLengthNat u ≤ k * n + e + 1 := by
  unfold bitLengthNat
  have hn : n ≤ 2 ^ n := (Nat.lt_two_pow_self).le
  have hu2 : u ≤ 2 ^ (k * n + e) := by
    calc
      u ≤ n ^ k * 2 ^ e := hu
      _ ≤ (2 ^ n) ^ k * 2 ^ e := Nat.mul_le_mul_right (2 ^ e) (Nat.pow_le_pow_left hn k)
      _ = 2 ^ (k * n) * 2 ^ e := by rw [← Nat.pow_mul, Nat.mul_comm n k]
      _ = 2 ^ (k * n + e) := (Nat.pow_add 2 (k * n) e).symm
  have hlog : Nat.log 2 u ≤ k * n + e := by
    calc
      Nat.log 2 u ≤ Nat.log 2 (2 ^ (k * n + e)) := Nat.log_mono_right hu2
      _ = k * n + e := Nat.log_pow (by norm_num) (k * n + e)
  omega

lemma checkSparsePieceNatTracked_snd_le {nnzA cardXY nnzB cardYZ D n : ℕ}
    (hA : nnzA ≤ n ^ 2) (hXY : cardXY ≤ n ^ 2) (hB : nnzB ≤ n ^ 2) (hYZ : cardYZ ≤ n ^ 2) :
    (checkSparsePieceNatTracked nnzA cardXY nnzB cardYZ D).2 ≤
      16 * (D + 1) ^ 3 + 32 * (n + 1) ^ 2 := by
  unfold checkSparsePieceNatTracked powNatTracked mulNatTracked cmpLeNatTracked retTracked
  dsimp only [CostM.bind_snd, CostM.bind_fst]
  have hb2 : bitLengthNat 2 = 2 := by decide
  rw [hb2]
  have hbA : bitLengthNat nnzA ≤ 2 * n + 1 := bitLengthNat_le_of_le_pow hA
  have hbXY : bitLengthNat cardXY ≤ 2 * n + 1 := bitLengthNat_le_of_le_pow hXY
  have hbB : bitLengthNat nnzB ≤ 2 * n + 1 := bitLengthNat_le_of_le_pow hB
  have hbYZ : bitLengthNat cardYZ ≤ 2 * n + 1 := bitLengthNat_le_of_le_pow hYZ
  have hb2D : bitLengthNat (2 ^ D) ≤ D + 1 := by
    simpa using bitLengthNat_le_of_le_pow_mul_two_pow (n := n) (k := 0) (e := D) (by simp)
  have hbA2D : bitLengthNat (nnzA * 2 ^ D) ≤ 2 * n + D + 1 :=
    bitLengthNat_le_of_le_pow_mul_two_pow (Nat.mul_le_mul_right (2 ^ D) hA)
  have hbB2D : bitLengthNat (nnzB * 2 ^ D) ≤ 2 * n + D + 1 :=
    bitLengthNat_le_of_le_pow_mul_two_pow (Nat.mul_le_mul_right (2 ^ D) hB)
  have hmulA : bitLengthNat nnzA * bitLengthNat (2 ^ D) ≤ (2 * n + 1) * (D + 1) :=
    Nat.mul_le_mul hbA hb2D
  have hmulB : bitLengthNat nnzB * bitLengthNat (2 ^ D) ≤ (2 * n + 1) * (D + 1) :=
    Nat.mul_le_mul hbB hb2D
  have hpD : (D + 1) * (D * 2 + 1) * (D * 2 + 1) ≤ 9 * (D + 1) ^ 3 := by
    have : (D + 1) * (D * 2 + 1) * (D * 2 + 1) = 4 * D ^ 3 + 8 * D ^ 2 + 5 * D + 1 := by ring
    have : 9 * (D + 1) ^ 3 = 9 * D ^ 3 + 27 * D ^ 2 + 27 * D + 9 := by ring
    omega
  have hm_le : (2 * n + 1) * (D + 1) ≤ 4 * (n + 1) ^ 2 + (D + 1) ^ 2 := by
    have : (2 * n + 1) * (D + 1) ≤ (2 * n + 1) ^ 2 + (D + 1) ^ 2 := by nlinarith
    have : (2 * n + 1) ^ 2 ≤ 4 * (n + 1) ^ 2 := by nlinarith
    omega
  have hd2_le_d3 : (D + 1) ^ 2 ≤ (D + 1) ^ 3 := by
    have h1 : (D + 1) ^ 2 * 1 ≤ (D + 1) ^ 2 * (D + 1) := Nat.mul_le_mul_left _ (by omega)
    have h2 : (D + 1) ^ 2 * (D + 1) = (D + 1) ^ 3 := by ring
    omega
  have hn_le : n + 1 ≤ (n + 1) ^ 2 := by clear *- ; nlinarith
  have hd_le : D + 1 ≤ (D + 1) ^ 3 := by
    have : D + 1 ≤ (D + 1) ^ 2 := by clear *- ; nlinarith
    exact this.trans hd2_le_d3
  omega

lemma cmpLeNatTracked_one_snd_le {u n : ℕ} (hu : u ≤ n ^ 2) :
    (cmpLeNatTracked u 1).2 ≤ 4 * (n + 1) ^ 2 := by
  unfold cmpLeNatTracked
  dsimp only
  have hb1 : bitLengthNat 1 = 1 := by decide
  have hbu : bitLengthNat u ≤ 2 * n + 1 := bitLengthNat_le_of_le_pow hu
  rw [hb1]
  nlinarith

lemma cmpRatCrossLtTracked_snd_le {p₁ q₁ p₂ q₂ n : ℕ}
    (hp₁ : p₁ ≤ n ^ 2) (hq₁ : q₁ ≤ n ^ 2) (hp₂ : p₂ ≤ n ^ 2) (hq₂ : q₂ ≤ n ^ 2) :
    (cmpRatCrossLtTracked p₁ q₁ p₂ q₂).2 ≤ 32 * (n + 1) ^ 2 := by
  unfold cmpRatCrossLtTracked mulNatTracked cmpLtNatTracked
  dsimp only [CostM.bind_snd, CostM.bind_fst]
  have hbp₁ : bitLengthNat p₁ ≤ 2 * n + 1 := bitLengthNat_le_of_le_pow hp₁
  have hbq₁ : bitLengthNat q₁ ≤ 2 * n + 1 := bitLengthNat_le_of_le_pow hq₁
  have hbp₂ : bitLengthNat p₂ ≤ 2 * n + 1 := bitLengthNat_le_of_le_pow hp₂
  have hbq₂' : bitLengthNat q₂ ≤ 2 * n + 1 := bitLengthNat_le_of_le_pow hq₂
  have hpq₁ : p₁ * q₂ ≤ n ^ 4 := by
    calc
      p₁ * q₂ ≤ n ^ 2 * n ^ 2 := Nat.mul_le_mul hp₁ hq₂
      _ = n ^ 4 := by ring
  have hpq₂ : p₂ * q₁ ≤ n ^ 4 := by
    calc
      p₂ * q₁ ≤ n ^ 2 * n ^ 2 := Nat.mul_le_mul hp₂ hq₁
      _ = n ^ 4 := by ring
  have hbpq₁ : bitLengthNat (p₁ * q₂) ≤ 4 * n + 1 := bitLengthNat_le_of_le_pow hpq₁
  have hbpq₂ : bitLengthNat (p₂ * q₁) ≤ 4 * n + 1 := bitLengthNat_le_of_le_pow hpq₂
  have hm₁ : bitLengthNat p₁ * bitLengthNat q₂ ≤ (2 * n + 1) * (2 * n + 1) :=
    Nat.mul_le_mul hbp₁ hbq₂'
  have hm₂ : bitLengthNat p₂ * bitLengthNat q₁ ≤ (2 * n + 1) * (2 * n + 1) :=
    Nat.mul_le_mul hbp₂ hbq₁
  have hm_sq : (2 * n + 1) * (2 * n + 1) ≤ 4 * (n + 1) ^ 2 := by clear *- ; nlinarith
  have hn_le : n + 1 ≤ (n + 1) ^ 2 := by clear *- ; nlinarith
  omega

lemma checkDenseCSubcase2aExactNatTracked_snd_le {cardSk cardX cardZ d n : ℕ}
    (hSk : cardSk ≤ n ^ 2) (hX : cardX ≤ n) (hZ : cardZ ≤ n) :
    (checkDenseCSubcase2aExactNatTracked cardSk cardX cardZ d).2 ≤
      256 * (d + 1) ^ 3 + 2 ^ 26 * (n + 1) ^ 2 := by
  unfold checkDenseCSubcase2aExactNatTracked powNatTracked mulNatTracked cmpLtNatTracked
  dsimp only [CostM.bind_snd, CostM.bind_fst]
  have hb2 : bitLengthNat 2 = 2 := by decide
  rw [hb2]
  have hXZ : cardX * cardZ ≤ n ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul hX hZ
  have hbX : bitLengthNat cardX ≤ n + 1 := by
    simpa using bitLengthNat_le_of_le_pow (k := 1) (by simpa using hX)
  have hbZ : bitLengthNat cardZ ≤ n + 1 := by
    simpa using bitLengthNat_le_of_le_pow (k := 1) (by simpa using hZ)
  have hbXZ : bitLengthNat (cardX * cardZ) ≤ 2 * n + 1 := bitLengthNat_le_of_le_pow hXZ
  have hbSk : bitLengthNat cardSk ≤ 2 * n + 1 := bitLengthNat_le_of_le_pow hSk
  have hXZ160 : (cardX * cardZ) ^ 160 ≤ n ^ 320 := by
    calc
      (cardX * cardZ) ^ 160 ≤ (n ^ 2) ^ 160 := Nat.pow_le_pow_left hXZ 160
      _ = n ^ 320 := by ring
  have hSk160 : cardSk ^ 160 ≤ n ^ 320 := by
    calc
      cardSk ^ 160 ≤ (n ^ 2) ^ 160 := Nat.pow_le_pow_left hSk 160
      _ = n ^ 320 := by ring
  have hbXZ160 : bitLengthNat ((cardX * cardZ) ^ 160) ≤ 320 * n + 1 :=
    bitLengthNat_le_of_le_pow hXZ160
  have hbSk160 : bitLengthNat (cardSk ^ 160) ≤ 320 * n + 1 :=
    bitLengthNat_le_of_le_pow hSk160
  have hb2d : bitLengthNat (2 ^ d) ≤ d + 1 := by
    simpa using bitLengthNat_le_of_le_pow_mul_two_pow (n := n) (k := 0) (e := d) (by simp)
  have hbRhs : bitLengthNat (cardSk ^ 160 * 2 ^ d) ≤ 320 * n + d + 1 :=
    bitLengthNat_le_of_le_pow_mul_two_pow (Nat.mul_le_mul_right (2 ^ d) hSk160)
  have hmXZ : bitLengthNat cardX * bitLengthNat cardZ ≤ (n + 1) * (n + 1) :=
    Nat.mul_le_mul hbX hbZ
  have hpXZ :
      (160 + 1) * (160 * bitLengthNat (cardX * cardZ) + 1) * (160 * bitLengthNat (cardX * cardZ) + 1) ≤
        161 * ((320 * n + 161) * (320 * n + 161)) := by
    have h1 : 160 * bitLengthNat (cardX * cardZ) + 1 ≤ 320 * n + 161 := by omega
    calc
      (160 + 1) * (160 * bitLengthNat (cardX * cardZ) + 1) * (160 * bitLengthNat (cardX * cardZ) + 1)
        ≤ 161 * (320 * n + 161) * (320 * n + 161) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 161 h1) h1
      _ = 161 * ((320 * n + 161) * (320 * n + 161)) := by ring
  have hpSk :
      (160 + 1) * (160 * bitLengthNat cardSk + 1) * (160 * bitLengthNat cardSk + 1) ≤
        161 * ((320 * n + 161) * (320 * n + 161)) := by
    have h1 : 160 * bitLengthNat cardSk + 1 ≤ 320 * n + 161 := by omega
    calc
      (160 + 1) * (160 * bitLengthNat cardSk + 1) * (160 * bitLengthNat cardSk + 1)
        ≤ 161 * (320 * n + 161) * (320 * n + 161) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 161 h1) h1
      _ = 161 * ((320 * n + 161) * (320 * n + 161)) := by ring
  have hmSk2d : bitLengthNat (cardSk ^ 160) * bitLengthNat (2 ^ d) ≤ (320 * n + 1) * (d + 1) :=
    Nat.mul_le_mul hbSk160 hb2d
  have hpd : (d + 1) * (d * 2 + 1) * (d * 2 + 1) ≤ 9 * (d + 1) ^ 3 := by
    have : (d + 1) * (d * 2 + 1) * (d * 2 + 1) = 4 * d ^ 3 + 8 * d ^ 2 + 5 * d + 1 := by ring
    have : 9 * (d + 1) ^ 3 = 9 * d ^ 3 + 27 * d ^ 2 + 27 * d + 9 := by ring
    omega
  have hp160 : (320 * n + 161) * (320 * n + 161) ≤ 2 ^ 17 * (n + 1) ^ 2 := by
    have : (320 * n + 161) * (320 * n + 161) = 102400 * n ^ 2 + 103040 * n + 25921 := by ring
    have : 2 ^ 17 * (n + 1) ^ 2 = 131072 * n ^ 2 + 262144 * n + 131072 := by ring
    omega
  have hm_le : (320 * n + 1) * (d + 1) ≤ 2 ^ 17 * (n + 1) ^ 2 + (d + 1) ^ 2 := by
    clear *-
    have h1 : (320 * n + 1) * (d + 1) ≤ (320 * n + 1) * (320 * n + 1) + (d + 1) ^ 2 := by nlinarith
    have h2 : (320 * n + 1) * (320 * n + 1) = 102400 * n ^ 2 + 640 * n + 1 := by ring
    have h3 : 2 ^ 17 * (n + 1) ^ 2 = 131072 * n ^ 2 + 262144 * n + 131072 := by ring
    omega
  have hd2_le_d3 : (d + 1) ^ 2 ≤ (d + 1) ^ 3 := by
    have h1 : (d + 1) ^ 2 * 1 ≤ (d + 1) ^ 2 * (d + 1) := Nat.mul_le_mul_left _ (by omega)
    have h2 : (d + 1) ^ 2 * (d + 1) = (d + 1) ^ 3 := by ring
    omega
  have hn_le : n + 1 ≤ (n + 1) ^ 2 := by clear *- ; nlinarith
  have hd_le : d + 1 ≤ (d + 1) ^ 3 := by
    have : d + 1 ≤ (d + 1) ^ 2 := by clear *- ; nlinarith
    exact this.trans hd2_le_d3
  have hn1_sq : (n + 1) * (n + 1) = (n + 1) ^ 2 := (sq (n + 1)).symm
  omega

/-- Per-piece bit-operation overhead of Algorithm 6 (`pieceOverhead n d`). -/
def pieceOverhead (n d : ℕ) : ℕ :=
  2 ^ 27 * (n + 1) ^ 2 + 512 * (d + 1) ^ 3

/-- Helper lemma unfolding `(detectOnPieceTracked n d C P).2` and rewriting the three integer-arithmetic
threshold conditions into their exact `Real` equivalents. -/
lemma detectOnPieceTracked_snd_eq_real (n d : ℕ) (C : Fin n → Fin n → Bool)
    (P : CubePiece (Fin n) (Fin n) (Fin n))
    (h_bin : ∀ x y z, (P.A_k x y = 0 ∨ P.A_k x y = 1) ∧ (P.B_k y z = 0 ∨ P.B_k y z = 1)) :
    let suppB := (P.Y_k ×ˢ P.Z_k).filter (fun yz => decide (0 < P.B_k yz.1 yz.2))
    let suppA := (P.X_k ×ˢ P.Y_k).filter (fun xy => decide (0 < P.A_k xy.1 xy.2))
    let cardXY := P.X_k.card * P.Y_k.card
    let cardYZ := P.Y_k.card * P.Z_k.card
    let S_k := (P.X_k ×ˢ P.Z_k).filter (fun xz => C xz.1 xz.2)
    let N_A : Fin n → Finset (Fin n) := fun x => P.Y_k.filter (fun y => decide (0 < P.A_k x y))
    let N_B : Fin n → Finset (Fin n) := fun z => P.Y_k.filter (fun y => decide (0 < P.B_k y z))
    (detectOnPieceTracked n d C P).2 =
      (scanMatrixPairTracked P.X_k P.Y_k P.Z_k ()).2 +
      ((checkSparsePieceNatTracked suppA.card cardXY suppB.card cardYZ (2 * d)).2 +
        ((cmpLeNatTracked suppB.card 1).2 +
          (if decide (min (matDensity P.X_k P.Y_k P.A_k) (matDensity P.Y_k P.Z_k P.B_k) ≤
                (2 : ℝ) ^ (- (2 * (d : ℝ)))) ||
              decide (suppB.card ≤ 1) then
            (cmpRatCrossLtTracked suppB.card cardYZ suppA.card cardXY).2 +
              (if decide (suppB.card ≤ 1) ||
                  decide (matDensity P.Y_k P.Z_k P.B_k < matDensity P.X_k P.Y_k P.A_k) then
                (evalSupportScanTracked suppB P.X_k
                  (fun yz x => decide (0 < P.A_k x yz.1 ∧ C x yz.2 = true))).2
              else
                (evalSupportScanTracked suppA P.Z_k
                  (fun xy z => decide (0 < P.B_k xy.2 z ∧ C xy.1 z = true))).2)
          else
            (scanMatrixTracked P.X_k P.Z_k ()).2 +
              ((checkDenseCSubcase2aExactNatTracked S_k.card P.X_k.card P.Z_k.card d).2 +
                (if decide ((2 : ℝ) ^ (- ((1 / 160 : ℝ) * (d : ℝ))) *
                      ((P.X_k.card : ℝ) * (P.Z_k.card : ℝ)) < (S_k.card : ℝ)) then
                  (retTracked true).2
                else
                  (evalMinNbrScanTracked S_k
                    (fun xz => N_A xz.1) (fun xz => N_B xz.2)
                    (fun xz y => decide (0 < P.B_k y xz.2))
                    (fun xz y => decide (0 < P.A_k xz.1 y))).2))))) := by
  intro suppB suppA cardXY cardYZ S_k N_A N_B
  unfold detectOnPieceTracked detectOnPieceNatTracked
  dsimp only [CostM.bind_snd]
  have hsuppB_le : suppB.card ≤ cardYZ := by
    have h1 := Finset.card_le_card (Finset.filter_subset
      (fun yz : Fin n × Fin n => decide (0 < P.B_k yz.1 yz.2)) (P.Y_k ×ˢ P.Z_k))
    rwa [Finset.card_product] at h1
  have hsuppA_le : suppA.card ≤ cardXY := by
    have h1 := Finset.card_le_card (Finset.filter_subset
      (fun xy : Fin n × Fin n => decide (0 < P.A_k xy.1 xy.2)) (P.X_k ×ˢ P.Y_k))
    rwa [Finset.card_product] at h1
  have hdensA : matDensity P.X_k P.Y_k P.A_k = (suppA.card : ℝ) / (cardXY : ℝ) :=
    matDensity_binary_eq_card_div P.X_k P.Y_k P.A_k (fun x y => (h_bin x y x).1)
  have hdensB : matDensity P.Y_k P.Z_k P.B_k = (suppB.card : ℝ) / (cardYZ : ℝ) :=
    matDensity_binary_eq_card_div P.Y_k P.Z_k P.B_k (fun y z => (h_bin y y z).2)
  have hc1_eq :
      ((checkSparsePieceNatTracked suppA.card cardXY suppB.card cardYZ (2 * d)).1 ||
        (cmpLeNatTracked suppB.card 1).1) =
      (decide (min (matDensity P.X_k P.Y_k P.A_k) (matDensity P.Y_k P.Z_k P.B_k) ≤
          (2 : ℝ) ^ (- (2 * (d : ℝ)))) ||
        decide (suppB.card ≤ 1)) := by
    apply Bool.eq_iff_iff.mpr
    rw [Bool.or_eq_true, Bool.or_eq_true, cmpLeNatTracked_fst, decide_eq_true_eq]
    by_cases hb1 : suppB.card ≤ 1
    · simp [hb1]
    · simp only [hb1, or_false]
      have hYZ_pos : 0 < cardYZ := Nat.lt_of_lt_of_le (by omega : 0 < suppB.card) hsuppB_le
      have hdensB_nn : 0 ≤ matDensity P.Y_k P.Z_k P.B_k := by rw [hdensB]; positivity
      have h2d_nn : (0 : ℝ) ≤ (2 : ℝ) ^ (- (2 * (d : ℝ))) := by positivity
      rcases Nat.eq_zero_or_pos cardXY with hXY0 | hXY_pos
      · have hsuppA0 : suppA.card = 0 := Nat.eq_zero_of_le_zero (hsuppA_le.trans_eq hXY0)
        have hdensA0 : matDensity P.X_k P.Y_k P.A_k = 0 := by
          rw [hdensA, hXY0, Nat.cast_zero, div_zero]
        have hmin0 : min (matDensity P.X_k P.Y_k P.A_k) (matDensity P.Y_k P.Z_k P.B_k) = 0 := by
          rw [hdensA0, min_eq_left hdensB_nn]
        rw [checkSparsePieceNatTracked_fst, hsuppA0, hXY0, hmin0, Bool.or_eq_true,
          decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq, Nat.zero_mul]
        exact ⟨fun _ => h2d_nn, fun _ => Or.inl le_rfl⟩
      · rw [checkSparsePieceNatTracked_iff_min_le hXY_pos hYZ_pos, decide_eq_true_eq,
          ← hdensA, ← hdensB]
        push_cast
        rfl
  have hc2_eq :
      ((cmpLeNatTracked suppB.card 1).1 ||
        (cmpRatCrossLtTracked suppB.card cardYZ suppA.card cardXY).1) =
      (decide (suppB.card ≤ 1) ||
        decide (matDensity P.Y_k P.Z_k P.B_k < matDensity P.X_k P.Y_k P.A_k)) := by
    apply Bool.eq_iff_iff.mpr
    rw [Bool.or_eq_true, Bool.or_eq_true, cmpLeNatTracked_fst, cmpRatCrossLtTracked_fst,
      decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq]
    by_cases hb1 : suppB.card ≤ 1
    · simp [hb1]
    · simp only [hb1, false_or]
      have hYZ_pos : 0 < cardYZ := Nat.lt_of_lt_of_le (by omega : 0 < suppB.card) hsuppB_le
      have hdensB_pos : 0 < matDensity P.Y_k P.Z_k P.B_k := by
        rw [hdensB]; exact div_pos (by exact_mod_cast (by omega : 0 < suppB.card))
          (Nat.cast_pos.mpr hYZ_pos)
      rcases Nat.eq_zero_or_pos cardXY with hXY0 | hXY_pos
      · have hsuppA0 : suppA.card = 0 := Nat.eq_zero_of_le_zero (hsuppA_le.trans_eq hXY0)
        have hdensA0 : matDensity P.X_k P.Y_k P.A_k = 0 := by
          rw [hdensA, hXY0, Nat.cast_zero, div_zero]
        rw [hXY0, hsuppA0, hdensA0, Nat.mul_zero, Nat.zero_mul]
        exact ⟨fun h => False.elim (Nat.lt_irrefl 0 h),
          fun h => False.elim (not_lt_of_gt hdensB_pos h)⟩
      · rw [hdensB, hdensA, div_lt_div_iff₀ (Nat.cast_pos.mpr hYZ_pos) (Nat.cast_pos.mpr hXY_pos)]
        exact_mod_cast Iff.rfl
  have hc3_eq :
      (checkDenseCSubcase2aExactNatTracked S_k.card P.X_k.card P.Z_k.card d).1 =
        decide ((2 : ℝ) ^ (- ((1 / 160 : ℝ) * (d : ℝ))) *
          ((P.X_k.card : ℝ) * (P.Z_k.card : ℝ)) < (S_k.card : ℝ)) := by
    apply Bool.eq_iff_iff.mpr
    rw [checkDenseCSubcase2aExactNatTracked_iff_lt, decide_eq_true_eq]
  rw [hc1_eq]
  by_cases h_case1 :
      (decide (min (matDensity P.X_k P.Y_k P.A_k) (matDensity P.Y_k P.Z_k P.B_k) ≤
          (2 : ℝ) ^ (- (2 * (d : ℝ)))) ||
        decide (suppB.card ≤ 1)) = true
  · rw [if_pos h_case1, if_pos h_case1]
    dsimp only [CostM.bind_snd]
    rw [hc2_eq]
    by_cases h_sub1 :
        (decide (suppB.card ≤ 1) ||
          decide (matDensity P.Y_k P.Z_k P.B_k < matDensity P.X_k P.Y_k P.A_k)) = true
    · rw [if_pos h_sub1, if_pos h_sub1]
    · rw [if_neg h_sub1, if_neg h_sub1]
  · rw [if_neg h_case1, if_neg h_case1]
    dsimp only [CostM.bind_snd]
    rw [hc3_eq]
    by_cases h_sub2a :
        decide ((2 : ℝ) ^ (- ((1 / 160 : ℝ) * (d : ℝ))) *
          ((P.X_k.card : ℝ) * (P.Z_k.card : ℝ)) < (S_k.card : ℝ)) = true
    · rw [if_pos h_sub2a, if_pos h_sub2a]
    · rw [if_neg h_sub2a, if_neg h_sub2a]

/-- Helper lemma bounding the per-piece preprocessing and threshold-testing overheads in `ℝ` by
`pieceOverhead n d` using purely `ℕ` arithmetic so `2 ^ 26` and `2 ^ 27` never enter `ℝ`. -/
lemma detectOnPiece_overhead_bounds_R {n d : ℕ} (C : Fin n → Fin n → Bool)
    (P : CubePiece (Fin n) (Fin n) (Fin n)) :
    let suppB := (P.Y_k ×ˢ P.Z_k).filter (fun yz => decide (0 < P.B_k yz.1 yz.2))
    let suppA := (P.X_k ×ˢ P.Y_k).filter (fun xy => decide (0 < P.A_k xy.1 xy.2))
    let cardXY := P.X_k.card * P.Y_k.card
    let cardYZ := P.Y_k.card * P.Z_k.card
    let S_k := (P.X_k ×ˢ P.Z_k).filter (fun xz => C xz.1 xz.2)
    (((P.X_k.card : ℝ) * (P.Y_k.card : ℝ) + (P.Y_k.card : ℝ) * (P.Z_k.card : ℝ) + 1) +
        ((checkSparsePieceNatTracked suppA.card cardXY suppB.card cardYZ (2 * d)).2 : ℝ) +
        ((cmpLeNatTracked suppB.card 1).2 : ℝ) +
        ((cmpRatCrossLtTracked suppB.card cardYZ suppA.card cardXY).2 : ℝ) +
        1 + (n : ℝ) ^ 2 ≤ (pieceOverhead n d : ℝ)) ∧
    (((P.X_k.card : ℝ) * (P.Y_k.card : ℝ) + (P.Y_k.card : ℝ) * (P.Z_k.card : ℝ) + 1) +
        ((checkSparsePieceNatTracked suppA.card cardXY suppB.card cardYZ (2 * d)).2 : ℝ) +
        ((cmpLeNatTracked suppB.card 1).2 : ℝ) +
        ((P.X_k.card : ℝ) * (P.Z_k.card : ℝ) + 1) +
        ((checkDenseCSubcase2aExactNatTracked S_k.card P.X_k.card P.Z_k.card d).2 : ℝ) +
        1 + (S_k.card : ℝ) ≤ (pieceOverhead n d : ℝ)) := by
  intro suppB suppA cardXY cardYZ S_k
  have hX_nat : P.X_k.card ≤ n := by
    have := Finset.card_le_univ P.X_k; rwa [Fintype.card_fin] at this
  have hY_nat : P.Y_k.card ≤ n := by
    have := Finset.card_le_univ P.Y_k; rwa [Fintype.card_fin] at this
  have hZ_nat : P.Z_k.card ≤ n := by
    have := Finset.card_le_univ P.Z_k; rwa [Fintype.card_fin] at this
  have hXY_nat : cardXY ≤ n ^ 2 := by rw [sq]; exact Nat.mul_le_mul hX_nat hY_nat
  have hYZ_nat : cardYZ ≤ n ^ 2 := by rw [sq]; exact Nat.mul_le_mul hY_nat hZ_nat
  have hXZ_nat : P.X_k.card * P.Z_k.card ≤ n ^ 2 := by rw [sq]; exact Nat.mul_le_mul hX_nat hZ_nat
  have hsuppB_le : suppB.card ≤ cardYZ := by
    have h1 := Finset.card_le_card (Finset.filter_subset
      (fun yz : Fin n × Fin n => decide (0 < P.B_k yz.1 yz.2)) (P.Y_k ×ˢ P.Z_k))
    rwa [Finset.card_product] at h1
  have hsuppA_le : suppA.card ≤ cardXY := by
    have h1 := Finset.card_le_card (Finset.filter_subset
      (fun xy : Fin n × Fin n => decide (0 < P.A_k xy.1 xy.2)) (P.X_k ×ˢ P.Y_k))
    rwa [Finset.card_product] at h1
  have hSk_nat : S_k.card ≤ n ^ 2 := by
    have h1 := Finset.card_le_card (Finset.filter_subset (fun xz : Fin n × Fin n => C xz.1 xz.2) (P.X_k ×ˢ P.Z_k))
    rw [Finset.card_product] at h1
    exact h1.trans hXZ_nat
  have hcost_sparse :
      (checkSparsePieceNatTracked suppA.card cardXY suppB.card cardYZ (2 * d)).2 ≤
        128 * (d + 1) ^ 3 + 32 * (n + 1) ^ 2 := by
    have h1 := checkSparsePieceNatTracked_snd_le (D := 2 * d)
      (hsuppA_le.trans hXY_nat) hXY_nat (hsuppB_le.trans hYZ_nat) hYZ_nat
    have h2 : 16 * (2 * d + 1) ^ 3 ≤ 128 * (d + 1) ^ 3 := by
      have : 16 * (2 * d + 1) ^ 3 = 128 * d ^ 3 + 192 * d ^ 2 + 96 * d + 16 := by ring
      have : 128 * (d + 1) ^ 3 = 128 * d ^ 3 + 384 * d ^ 2 + 384 * d + 128 := by ring
      omega
    omega
  have hcost_b1 : (cmpLeNatTracked suppB.card 1).2 ≤ 4 * (n + 1) ^ 2 :=
    cmpLeNatTracked_one_snd_le (hsuppB_le.trans hYZ_nat)
  have hcost_rat :
      (cmpRatCrossLtTracked suppB.card cardYZ suppA.card cardXY).2 ≤ 32 * (n + 1) ^ 2 :=
    cmpRatCrossLtTracked_snd_le (hsuppB_le.trans hYZ_nat) hYZ_nat (hsuppA_le.trans hXY_nat) hXY_nat
  have hcost_dense :
      (checkDenseCSubcase2aExactNatTracked S_k.card P.X_k.card P.Z_k.card d).2 ≤
        256 * (d + 1) ^ 3 + 2 ^ 26 * (n + 1) ^ 2 :=
    checkDenseCSubcase2aExactNatTracked_snd_le hSk_nat hX_nat hZ_nat
  have h_sq_expand : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
  have hovh1_nat :
      (P.X_k.card * P.Y_k.card + P.Y_k.card * P.Z_k.card + 1) +
        (checkSparsePieceNatTracked suppA.card cardXY suppB.card cardYZ (2 * d)).2 +
        (cmpLeNatTracked suppB.card 1).2 +
        (cmpRatCrossLtTracked suppB.card cardYZ suppA.card cardXY).2 +
        1 + n ^ 2 ≤ pieceOverhead n d := by
    unfold pieceOverhead
    omega
  have hovh2_nat :
      (P.X_k.card * P.Y_k.card + P.Y_k.card * P.Z_k.card + 1) +
        (checkSparsePieceNatTracked suppA.card cardXY suppB.card cardYZ (2 * d)).2 +
        (cmpLeNatTracked suppB.card 1).2 +
        (P.X_k.card * P.Z_k.card + 1) +
        (checkDenseCSubcase2aExactNatTracked S_k.card P.X_k.card P.Z_k.card d).2 +
        1 + S_k.card ≤ pieceOverhead n d := by
    unfold pieceOverhead
    omega
  exact ⟨by exact_mod_cast hovh1_nat, by exact_mod_cast hovh2_nat⟩

/-- **Runtime / Scan Work Bound for Algorithm 6 (`detectOnPieceTracked_work_bound`,
`\eqref{eq:tridet-case1}`–`\eqref{eq:tridet-case2}`, §6 of `paper.tex`)**:
For every piece $P \in \mathcal{S}$ in a valid 3D decomposition, the inner triangle-scanning work of
`detectOnPieceTracked` is bounded by
$$\text{pieceOverhead } n\, d + \big(2^{-d} + 2^{-d / 320}\big)
  (\mathbb{E}[A_k])^{1/4} (\mathbb{E}[B_k])^{1/4} |X_k| |Y_k| |Z_k|.$$ -/
theorem detectOnPieceTracked_work_bound {n d : ℕ} (C : Fin n → Fin n → Bool)
    {P : CubePiece (Fin n) (Fin n) (Fin n)}
    (h_bin : ∀ x y z, (P.A_k x y = 0 ∨ P.A_k x y = 1) ∧ (P.B_k y z = 0 ∨ P.B_k y z = 1)) :
    ((detectOnPieceTracked n d C P).2 : ℝ) ≤
      (pieceOverhead n d : ℝ) +
        ((2 : ℝ) ^ (- (d : ℝ)) + (2 : ℝ) ^ (- ((1 / 160 : ℝ) * (d : ℝ) / 2))) *
          ((matDensity P.X_k P.Y_k P.A_k) ^ (1 / 4 : ℝ) *
            (matDensity P.Y_k P.Z_k P.B_k) ^ (1 / 4 : ℝ) *
            (P.X_k.card : ℝ) * (P.Y_k.card : ℝ) * (P.Z_k.card : ℝ)) := by
  have hn2_nonneg : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg (n : ℝ)
  have hA_nonneg : ∀ x ∈ P.X_k, ∀ y ∈ P.Y_k, 0 ≤ P.A_k x y := by
    intro x _ y _; rcases (h_bin x y x).1 with h0 | h1 <;> linarith
  have hB_nonneg : ∀ y ∈ P.Y_k, ∀ z ∈ P.Z_k, 0 ≤ P.B_k y z := by
    intro y _ z _; rcases (h_bin y y z).2 with h0 | h1 <;> linarith
  have hA_le_one : ∀ x ∈ P.X_k, ∀ y ∈ P.Y_k, P.A_k x y ≤ 1 := by
    intro x _ y _; rcases (h_bin x y x).1 with h0 | h1 <;> linarith
  have hB_le_one : ∀ y ∈ P.Y_k, ∀ z ∈ P.Z_k, P.B_k y z ≤ 1 := by
    intro y _ z _; rcases (h_bin y y z).2 with h0 | h1 <;> linarith
  have hA0 : 0 ≤ matDensity P.X_k P.Y_k P.A_k :=
    expectSet_nonneg (fun x hx => expectSet_nonneg (fun y hy => hA_nonneg x hx y hy))
  have hB0 : 0 ≤ matDensity P.Y_k P.Z_k P.B_k :=
    expectSet_nonneg (fun y hy => expectSet_nonneg (fun z hz => hB_nonneg y hy z hz))
  have h_pot_nonneg :
      0 ≤ (matDensity P.X_k P.Y_k P.A_k) ^ (1 / 4 : ℝ) *
        (matDensity P.Y_k P.Z_k P.B_k) ^ (1 / 4 : ℝ) *
        (P.X_k.card : ℝ) * (P.Y_k.card : ℝ) * (P.Z_k.card : ℝ) := by positivity
  have h_extra1 : 0 ≤ (2 : ℝ) ^ (- ((1 / 160 : ℝ) * (d : ℝ) / 2)) *
      ((matDensity P.X_k P.Y_k P.A_k) ^ (1 / 4 : ℝ) *
        (matDensity P.Y_k P.Z_k P.B_k) ^ (1 / 4 : ℝ) *
        (P.X_k.card : ℝ) * (P.Y_k.card : ℝ) * (P.Z_k.card : ℝ)) :=
    mul_nonneg (by positivity) h_pot_nonneg
  have h_extra2 : 0 ≤ (2 : ℝ) ^ (- (d : ℝ)) *
      ((matDensity P.X_k P.Y_k P.A_k) ^ (1 / 4 : ℝ) *
        (matDensity P.Y_k P.Z_k P.B_k) ^ (1 / 4 : ℝ) *
        (P.X_k.card : ℝ) * (P.Y_k.card : ℝ) * (P.Z_k.card : ℝ)) :=
    mul_nonneg (by positivity) h_pot_nonneg
  have h_nonneg_rhs : 0 ≤ ((2 : ℝ) ^ (- (d : ℝ)) +
      (2 : ℝ) ^ (- ((1 / 160 : ℝ) * (d : ℝ) / 2))) *
      ((matDensity P.X_k P.Y_k P.A_k) ^ (1 / 4 : ℝ) *
        (matDensity P.Y_k P.Z_k P.B_k) ^ (1 / 4 : ℝ) *
        (P.X_k.card : ℝ) * (P.Y_k.card : ℝ) * (P.Z_k.card : ℝ)) := by linarith
  have h_suppB_le := card_filter_pos_prod_le_matDensity P.Y_k P.Z_k P.B_k
    (fun y z => (h_bin y y z).2)
  have h_suppA_le := card_filter_pos_prod_le_matDensity P.X_k P.Y_k P.A_k
    (fun x y => (h_bin x y x).1)
  set suppB := (P.Y_k ×ˢ P.Z_k).filter (fun yz => decide (0 < P.B_k yz.1 yz.2))
  set suppA := (P.X_k ×ˢ P.Y_k).filter (fun xy => decide (0 < P.A_k xy.1 xy.2))
  set cardXY := P.X_k.card * P.Y_k.card
  set cardYZ := P.Y_k.card * P.Z_k.card
  set S_k := (P.X_k ×ˢ P.Z_k).filter (fun xz => C xz.1 xz.2)
  set N_A : Fin n → Finset (Fin n) := fun x => P.Y_k.filter (fun y => decide (0 < P.A_k x y))
  set N_B : Fin n → Finset (Fin n) := fun z => P.Y_k.filter (fun y => decide (0 < P.B_k y z))
  have hSk_sub : S_k ⊆ P.X_k ×ˢ P.Z_k := Finset.filter_subset _ _
  obtain ⟨hovh1_R, hovh2_R⟩ := detectOnPiece_overhead_bounds_R C P
  have h_snd_eq := detectOnPieceTracked_snd_eq_real n d C P h_bin
  rw [h_snd_eq]
  split_ifs with h_case1 h_sub1 h_sub2a
  · -- Case 1a: suppB.card ≤ 1 or densB < densA
    rw [scanMatrixPairTracked_snd, evalSupportScanTracked_snd]
    push_cast
    rcases (Bool.or_eq_true _ _).mp h_sub1 with h_le1 | h_lt_dens
    · have h_bx : (suppB.card : ℝ) * (P.X_k.card : ℝ) ≤ (n : ℝ) ^ 2 :=
        card_mul_le_sq_of_le_one (of_decide_eq_true h_le1) P.X_k
      linarith
    · rcases (Bool.or_eq_true _ _).mp h_case1 with h_min_b | h_b1_b
      · have h_min_le : min (matDensity P.X_k P.Y_k P.A_k) (matDensity P.Y_k P.Z_k P.B_k) ≤
            (2 : ℝ) ^ (- (2 * (d : ℝ))) := of_decide_eq_true h_min_b
        have h_densB_eq : min (matDensity P.X_k P.Y_k P.A_k) (matDensity P.Y_k P.Z_k P.B_k) =
            matDensity P.Y_k P.Z_k P.B_k :=
          min_eq_right (le_of_lt (of_decide_eq_true h_lt_dens))
        have h_c1 := tridet_case1_work_bound P.X_k P.Y_k P.Z_k P.A_k P.B_k
          hA_nonneg hB_nonneg h_min_le
        rw [h_densB_eq] at h_c1
        have h_supp_mul :
            (suppB.card : ℝ) * (P.X_k.card : ℝ) ≤
              matDensity P.Y_k P.Z_k P.B_k *
                (P.X_k.card : ℝ) * (P.Y_k.card : ℝ) * (P.Z_k.card : ℝ) := by
          have := mul_le_mul_of_nonneg_right h_suppB_le (Nat.cast_nonneg P.X_k.card)
          linarith
        linarith
      · have h_bx : (suppB.card : ℝ) * (P.X_k.card : ℝ) ≤ (n : ℝ) ^ 2 :=
          card_mul_le_sq_of_le_one (of_decide_eq_true h_b1_b) P.X_k
        linarith
  · -- Case 1b: ¬(suppB.card ≤ 1) and densA ≤ densB
    rw [scanMatrixPairTracked_snd, evalSupportScanTracked_snd]
    push_cast
    rcases not_or.mp (mt (Bool.or_eq_true _ _).mpr h_sub1) with ⟨h_not_b1, h_not_lt⟩
    have h_dens_le : matDensity P.X_k P.Y_k P.A_k ≤ matDensity P.Y_k P.Z_k P.B_k :=
      not_lt.mp (of_decide_eq_false (Bool.eq_false_iff.mpr h_not_lt))
    have h_min_le : min (matDensity P.X_k P.Y_k P.A_k) (matDensity P.Y_k P.Z_k P.B_k) ≤
        (2 : ℝ) ^ (- (2 * (d : ℝ))) := by
      rcases (Bool.or_eq_true _ _).mp h_case1 with h_m | h_b1
      · exact of_decide_eq_true h_m
      · exact False.elim (h_not_b1 h_b1)
    have h_densA_eq : min (matDensity P.X_k P.Y_k P.A_k) (matDensity P.Y_k P.Z_k P.B_k) =
        matDensity P.X_k P.Y_k P.A_k := min_eq_left h_dens_le
    have h_c1 := tridet_case1_work_bound P.X_k P.Y_k P.Z_k P.A_k P.B_k
      hA_nonneg hB_nonneg h_min_le
    rw [h_densA_eq] at h_c1
    have h_supp_mul :
        (suppA.card : ℝ) * (P.Z_k.card : ℝ) ≤
          matDensity P.X_k P.Y_k P.A_k *
            (P.X_k.card : ℝ) * (P.Y_k.card : ℝ) * (P.Z_k.card : ℝ) := by
      have := mul_le_mul_of_nonneg_right h_suppA_le (Nat.cast_nonneg P.Z_k.card)
      linarith
    linarith
  · -- Subcase 2a
    rw [scanMatrixPairTracked_snd, scanMatrixTracked_snd, retTracked_snd]
    push_cast
    have hSk_nonneg : 0 ≤ (S_k.card : ℝ) := Nat.cast_nonneg S_k.card
    linarith
  · -- Subcase 2b: Apply subcase2b_scan_work_bound (`\eqref{eq:tridet-case2}`, §6 of `paper.tex`)
    rw [scanMatrixPairTracked_snd, scanMatrixTracked_snd, evalMinNbrScanTracked_snd]
    push_cast
    have hSk_sparse :
        (S_k.card : ℝ) ≤
          (2 : ℝ) ^ (- ((1 / 160 : ℝ) * (d : ℝ))) * ((P.X_k.card : ℝ) * (P.Z_k.card : ℝ)) :=
      not_lt.mp (of_decide_eq_false (Bool.eq_false_iff.mpr h_sub2a))
    have hA_dens_le : matDensity P.X_k P.Y_k P.A_k ≤ 1 := by
      rcases P.X_k.eq_empty_or_nonempty with hX_emp | hX_ne
      · simp [matDensity, hX_emp]
      · rcases P.Y_k.eq_empty_or_nonempty with hY_emp | hY_ne
        · simp [matDensity, rowDeg, expectSet, hY_emp]
        · exact expectSet_le_of_le hX_ne (fun x hx => expectSet_le_of_le hY_ne (hA_le_one x hx))
    have hB_dens_le : matDensity P.Y_k P.Z_k P.B_k ≤ 1 := by
      rcases P.Y_k.eq_empty_or_nonempty with hY_emp | hY_ne
      · simp [matDensity, hY_emp]
      · rcases P.Z_k.eq_empty_or_nonempty with hZ_emp | hZ_ne
        · simp [matDensity, rowDeg, expectSet, hZ_emp]
        · exact expectSet_le_of_le hY_ne (fun y hy => expectSet_le_of_le hZ_ne (hB_le_one y hy))
    have h_scan_sum :
        ∑ xz ∈ S_k,
            (1 + min ((N_A xz.1).card : ℝ) ((N_B xz.2).card : ℝ)) ≤
          (S_k.card : ℝ) +
            ∑ xz ∈ S_k, (P.Y_k.card : ℝ) *
              min (rowDeg P.Y_k P.A_k xz.1) (rowDeg P.Y_k (matTranspose P.B_k) xz.2) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
      refine add_le_add le_rfl (Finset.sum_le_sum (fun xz _ => ?_))
      rw [mul_min_of_nonneg _ _ (Nat.cast_nonneg _)]
      exact min_le_min
        (card_filter_pos_le_card_mul_rowDeg P.Y_k P.A_k xz.1 (fun y => (h_bin xz.1 y xz.1).1))
        (card_filter_pos_le_card_mul_rowDeg P.Y_k (matTranspose P.B_k) xz.2
          (fun y => (h_bin y y xz.2).2))
    have h_2b := subcase2b_scan_work_bound hSk_sub P.A_k P.B_k
      hA_nonneg hB_nonneg hA_dens_le hB_dens_le hSk_sparse
    have h_2b_trans := le_trans h_2b.1 h_2b.2
    linarith

/-- Helper lemma: cost of `foldlListTracked` when the step cost depends only on the list element. -/
lemma foldlListTracked_snd_eq_sum {α β : Type*} (f : β → α → CostM β) (g : α → ℕ)
    (hf : ∀ b a, (f b a).2 = g a) (init : β) (xs : List α) :
    (foldlListTracked f init xs).2 = (xs.map (fun a => g a + 1)).sum + 1 := by
  induction xs generalizing init with
  | nil => simp [foldlListTracked]
  | cons x xs ih =>
    simp only [foldlListTracked, List.map_cons, List.sum_cons]
    rw [hf init x, ih (f init x).1]
    omega

/-- **Total Work Bound of Algorithm 6 (`triangleDetectionOnPiecesTracked_work_bound`,
`paper.tex` §6)**:
Summing `detectOnPieceTracked_work_bound` over all $K = |\mathcal{S}|$ pieces in $\mathcal{S}$
bounds the total work of `triangleDetectionOnPiecesTracked` by
$$(\text{pieceOverhead } n\, d + 2) \cdot |\mathcal{S}| + 1 +
  \big(2^{-d} + 2^{-d/320}\big) C_{1/4, 1/4}(\mathcal{S}).$$ -/
theorem triangleDetectionOnPiecesTracked_work_bound {n d : ℕ} (C : Fin n → Fin n → Bool)
    (S : List (CubePiece (Fin n) (Fin n) (Fin n)))
    (h_bin : ∀ P ∈ S, ∀ x y z,
      (P.A_k x y = 0 ∨ P.A_k x y = 1) ∧ (P.B_k y z = 0 ∨ P.B_k y z = 1)) :
    ((triangleDetectionOnPiecesTracked n d C S).2 : ℝ) ≤
      ((pieceOverhead n d : ℝ) + 2) * (S.length : ℝ) + 1 +
        ((2 : ℝ) ^ (- (d : ℝ)) + (2 : ℝ) ^ (- ((1 / 160 : ℝ) * (d : ℝ) / 2))) *
          cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ) S := by
  unfold triangleDetectionOnPiecesTracked
  rw [foldlListTracked_snd_eq_sum _ (fun P => (detectOnPieceTracked n d C P).2 + 1)
    (fun _ _ => rfl)]
  induction S with
  | nil =>
    simp [cubePotential]
  | cons P S ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, cubePotential] at *
    have hP := detectOnPieceTracked_work_bound (d := d) C (h_bin P (List.mem_cons.mpr (Or.inl rfl)))
    have hS := ih (fun Q hQ => h_bin Q (List.mem_cons.mpr (Or.inr hQ)))
    push_cast at *
    linarith

/-- **Total Work Bound of Algorithm 6 on a Valid 3D Decomposition
(`triangleDetectionOnPiecesTracked_valid_work_bound`, `paper.tex` §6)**:
When $\mathcal{S}$ satisfies `IsValid3DDecomposition n d A B S` (so $C_{1/4, 1/4}(\mathcal{S}) \le 128 n^3$),
the total work of `triangleDetectionOnPiecesTracked` is at most
$$(\text{pieceOverhead } n\, d + 2) \cdot |\mathcal{S}| + 1 + 128 \cdot \big(2^{-d} + 2^{-d/320}\big) n^3.$$ -/
theorem triangleDetectionOnPiecesTracked_valid_work_bound {n d : ℕ}
    (A B C : Fin n → Fin n → Bool)
    (S : List (CubePiece (Fin n) (Fin n) (Fin n)))
    (hS : IsValid3DDecomposition n d A B S) :
    ((triangleDetectionOnPiecesTracked n d C S).2 : ℝ) ≤
      ((pieceOverhead n d : ℝ) + 2) * (S.length : ℝ) + 1 +
        128 * ((2 : ℝ) ^ (- (d : ℝ)) + (2 : ℝ) ^ (- ((1 / 160 : ℝ) * (d : ℝ) / 2))) *
          (n : ℝ) ^ 3 := by
  have h1 := triangleDetectionOnPiecesTracked_work_bound (d := d) C S hS.piece_entries_binary
  have h2 := hS.potential_bound
  have h_coeff_nonneg :
      0 ≤ (2 : ℝ) ^ (- (d : ℝ)) + (2 : ℝ) ^ (- ((1 / 160 : ℝ) * (d : ℝ) / 2)) := by positivity
  have h3 := mul_le_mul_of_nonneg_left h2 h_coeff_nonneg
  linarith

/-- **Bridge Theorem (`cappedABDecomposition_isValid3DDecomposition`, `paper.tex` §6)**:
For any $d \ge 1$ and $n \times n$ boolean matrices $A, B$, the 3D decomposition
`S := cappedABDecomposition Finset.univ Finset.univ Finset.univ (bmatToReal A) (bmatToReal B) (1 / 160 : ℝ) (2 * d)`
satisfies `IsValid3DDecomposition n d A B S` (Rule 2: inhabited structure witness). -/
theorem cappedABDecomposition_isValid3DDecomposition {n d : ℕ} (hd : 1 ≤ d)
    (S : TwoStageSamplerOracle (Fin n) (1 / 160 : ℝ))
    (A B : Fin n → Fin n → Bool) :
    IsValid3DDecomposition n d A B
      (cappedABDecomposition Finset.univ Finset.univ Finset.univ
        (bmatToReal A) (bmatToReal B) (1 / 160 : ℝ) S (2 * d)) := by
  have hA_bin : IsBinaryMatrix Finset.univ Finset.univ (bmatToReal A) :=
    isBinaryMatrix_bmatToReal Finset.univ Finset.univ A
  have hB_bin : IsBinaryMatrix Finset.univ Finset.univ (bmatToReal B) :=
    isBinaryMatrix_bmatToReal Finset.univ Finset.univ B
  have hε0 : (0 : ℝ) < 1 / 160 := by norm_num
  have hε_le : (1 / 160 : ℝ) ≤ 1 / 160 := le_rfl
  have hD : 2 ≤ 2 * d := by omega
  refine
    { piece_entries_binary := ?_
      partition_boolMatMul := fun x z =>
        cappedABDecomposition_boolMatMul_iff n A B S hε0 hε_le hD x z
      regular_pieces_spec := ?_
      potential_bound := ?_ }
  · intro P hP x y z
    have hV := cappedABDecomposition_pieces_spec Finset.univ Finset.univ Finset.univ
      (bmatToReal A) (bmatToReal B) S hA_bin hB_bin hε0 hε_le hD hP
    exact isBinary_everywhere_of_validCubePiece hV x y z
  · intro P hP hmin_gt hsuppB_gt
    have hV := cappedABDecomposition_pieces_spec Finset.univ Finset.univ Finset.univ
      (bmatToReal A) (bmatToReal B) S hA_bin hB_bin hε0 hε_le hD hP
    rcases hV with ⟨_hX, _hY, _hZ, _hPA_ext, _hPB_ext, _hPA_bin, hPB_bin, hreg_true, hreg_false⟩
    cases hflag : P.isRegularPiece
    · exfalso
      rcases hreg_false hflag with hsp | hcard_le1
      · have hcast : ((2 * d : ℕ) : ℝ) = 2 * (d : ℝ) := by push_cast; ring
        rw [hcast] at hsp
        linarith
      · have hfilt_le :
            ((P.Y_k ×ˢ P.Z_k).filter (fun yz => decide (0 < P.B_k yz.1 yz.2))).card ≤
              ((P.Y_k ×ˢ P.Z_k).filter (fun p => P.B_k p.1 p.2 = 1)).card := by
          refine Finset.card_le_card (fun p hp => ?_)
          rw [Finset.mem_filter] at hp ⊢
          rcases hp with ⟨hp_mem, hp_pos⟩
          refine ⟨hp_mem, ?_⟩
          rcases hPB_bin p.1 (Finset.mem_product.mp hp_mem).1 p.2 (Finset.mem_product.mp hp_mem).2 with
            h0 | h1
          · exfalso
            have hlt : 0 < P.B_k p.1 p.2 := of_decide_eq_true hp_pos
            linarith
          · exact h1
        omega
    · rcases hreg_true hflag with ⟨h1, h2, h3, h4, h5, h6, h7, _h8⟩
      exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  · have hpot := (cappedABDecomposition_potential_le Finset.univ Finset.univ Finset.univ
      (bmatToReal A) (bmatToReal B) S hA_bin hB_bin hε0 hε_le hD).2
    have hcard : ((Finset.univ : Finset (Fin n)).card : ℝ) = (n : ℝ) := by simp
    rw [hcard] at hpot
    linarith [show 128 * (n : ℝ) * (n : ℝ) * (n : ℝ) = 128 * (n : ℝ) ^ 3 by ring]

/-!
### Concrete $2^{O(d^2)}$ Piece-Count and Cost Bounds for `cappedABDecomposition` at $\varepsilon = 1/160$
-/

lemma bitLengthNat_le_succ (v : ℕ) : bitLengthNat v ≤ v + 1 :=
  Nat.add_le_add_right (Nat.log_le_self 2 v) 1

lemma self_le_two_pow (m : ℕ) : m ≤ 2 ^ m :=
  (Nat.lt_two_pow_self).le

lemma nat_sq_le_two_pow (n : ℕ) : n ^ 2 ≤ 2 ^ (2 * n) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    rcases k with _ | m
    · norm_num
    · have h1 : (m + 1 + 1) ^ 2 ≤ 4 * (m + 1) ^ 2 := by
        have hdiff : 4 * (m + 1) ^ 2 = (m + 1 + 1) ^ 2 + (3 * m ^ 2 + 4 * m) := by ring
        omega
      have h2 : 4 * (m + 1) ^ 2 ≤ 4 * 2 ^ (2 * (m + 1)) := Nat.mul_le_mul_left 4 ih
      have h3 : 4 * 2 ^ (2 * (m + 1)) = 2 ^ (2 * (m + 1 + 1)) := by
        have hexp : 2 * (m + 1 + 1) = 2 + 2 * (m + 1) := by ring
        rw [hexp, Nat.pow_add]
      exact (h1.trans h2).trans_eq h3

/-- Combined polynomial overhead exponent `c + 20 * k + 20` of a two-stage oblivious sampler with
leading constant `c` and polynomial degree parameter `k`. -/
def samplerOverheadExp (c k : ℕ) : ℕ :=
  c + 20 * k + 20

lemma twenty_le_samplerOverheadExp (c k : ℕ) : 20 ≤ samplerOverheadExp c k := by
  unfold samplerOverheadExp
  omega

lemma twoStageSampleSizeBound_le_two_pow (c k : ℕ) {invEps logInvDelta m : ℕ}
    (he : invEps ≤ 2 ^ m) (hd : logInvDelta ≤ 2 ^ m) :
    twoStageSampleSizeBound c k invEps logInvDelta ≤
      2 ^ (c + 1 + (4 * k + 4) * (m + 1)) := by
  unfold twoStageSampleSizeBound
  have hc : c + 1 ≤ 2 ^ (c + 1) := self_le_two_pow (c + 1)
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have he1 : invEps + 1 ≤ 2 ^ (m + 1) := by
    rw [Nat.pow_succ]; omega
  have hd1 : logInvDelta + 1 ≤ 2 ^ (m + 1) := by
    rw [Nat.pow_succ]; omega
  have hprod : (invEps + 1) * (logInvDelta + 1) ≤ 2 ^ (2 * (m + 1)) := by
    calc
      (invEps + 1) * (logInvDelta + 1) ≤ 2 ^ (m + 1) * 2 ^ (m + 1) := Nat.mul_le_mul he1 hd1
      _ = 2 ^ (2 * (m + 1)) := by rw [← Nat.pow_add]; congr 1; ring
  have hexp_le : c + 1 + 2 * (m + 1) * (k + 2) ≤ c + 1 + (4 * k + 4) * (m + 1) := by
    have hmul_eq : 2 * (m + 1) * (k + 2) = (2 * k + 4) * (m + 1) := by ring
    have hk_le : 2 * k + 4 ≤ 4 * k + 4 := by omega
    nlinarith only [hmul_eq, hk_le]
  calc
    (c + 1) * ((invEps + 1) * (logInvDelta + 1)) ^ (k + 2)
      ≤ 2 ^ (c + 1) * (2 ^ (2 * (m + 1))) ^ (k + 2) :=
        Nat.mul_le_mul hc (Nat.pow_le_pow_left hprod (k + 2))
    _ = 2 ^ (c + 1 + 2 * (m + 1) * (k + 2)) := by rw [← Nat.pow_mul, ← Nat.pow_add]
    _ ≤ 2 ^ (c + 1 + (4 * k + 4) * (m + 1)) := Nat.pow_le_pow_right (by norm_num) hexp_le

lemma twoStageFamFactor_le_two_pow (c k : ℕ) {invEps invDelta m : ℕ}
    (he : invEps ≤ 2 ^ m) (hd : invDelta ≤ 2 ^ m) :
    twoStageFamFactor c k invEps invDelta ≤
      2 ^ (c + 1 + (4 * k + 4) * (m + 1)) :=
  twoStageSampleSizeBound_le_two_pow c k he hd

lemma concreteApproxGridNormCostFactor_le_pow (c k : ℕ) {D : ℕ} (hD : 640 ≤ D) :
    concreteApproxGridNormCostFactor c k (1 / 160 : ℝ) D + 2 * D + 7 ≤
      2 ^ (4 * samplerOverheadExp c k * D ^ 2) := by
  unfold concreteApproxGridNormCostFactor
  rw [accExp_one_div_160]
  set B := twoStageSampleSizeBound c k (2 ^ (3 * D + 14)) (D * (3 * D + 14))
  set F := twoStageFamFactor c k (2 ^ (3 * D + 14)) (2 ^ (D * (3 * D + 14)))
  change (powNatTracked B (2 * D)).2 +
      F * ((B ^ D) * (2 * D + 7) + B + 85 * (D + 1) ^ 3 + 6) +
      (D + 1) ^ 3 * (85 * B + 95) + 10 * D + 16 + 2 * D + 7 ≤
    2 ^ (4 * samplerOverheadExp c k * D ^ 2)
  set E := samplerOverheadExp c k
  have hE20 : 20 ≤ E := twenty_le_samplerOverheadExp c k
  have hD2 : 640 * D ≤ D ^ 2 := by
    rw [sq]
    exact Nat.mul_le_mul_right D hD
  have he : 2 ^ (3 * D + 14) ≤ 2 ^ (3 * D + 14) := le_rfl
  have hd : D * (3 * D + 14) ≤ 2 ^ (3 * D + 14) := by
    have h1 : D * (3 * D + 14) ≤ 4 * D ^ 2 := by
      have : D * (3 * D + 14) = 3 * D ^ 2 + 14 * D := by ring
      omega
    have h2 : 4 * D ^ 2 ≤ 2 ^ 2 * 2 ^ (2 * D) := Nat.mul_le_mul_left 4 (nat_sq_le_two_pow D)
    have h3 : 2 ^ 2 * 2 ^ (2 * D) = 2 ^ (2 + 2 * D) := (Nat.pow_add 2 2 (2 * D)).symm
    have h4 : 2 ^ (2 + 2 * D) ≤ 2 ^ (3 * D + 14) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact (h1.trans (h2.trans_eq h3)).trans h4
  have hB_raw : B ≤ 2 ^ (c + 1 + (4 * k + 4) * (3 * D + 14 + 1)) :=
    twoStageSampleSizeBound_le_two_pow c k he hd
  have heF : 2 ^ (3 * D + 14) ≤ 2 ^ (4 * D ^ 2) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hdF : 2 ^ (D * (3 * D + 14)) ≤ 2 ^ (4 * D ^ 2) := by
    have : D * (3 * D + 14) = 3 * D ^ 2 + 14 * D := by ring
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hF_raw : F ≤ 2 ^ (c + 1 + (4 * k + 4) * (4 * D ^ 2 + 1)) :=
    twoStageFamFactor_le_two_pow c k heF hdF
  clear_value B F
  have hB_exp : c + 1 + (4 * k + 4) * (3 * D + 14 + 1) ≤ E * D := by
    dsimp [E, samplerOverheadExp]
    nlinarith only [hD]
  have hB_le : B ≤ 2 ^ (E * D) :=
    hB_raw.trans (Nat.pow_le_pow_right (by norm_num) hB_exp)
  have hF_exp : c + 1 + (4 * k + 4) * (4 * D ^ 2 + 1) ≤ E * D ^ 2 := by
    dsimp [E, samplerOverheadExp]
    nlinarith only [hD, hD2]
  have hF_le : F ≤ 2 ^ (E * D ^ 2) :=
    hF_raw.trans (Nat.pow_le_pow_right (by norm_num) hF_exp)
  have hD3_le : (D + 1) ^ 3 ≤ 2 ^ (6 * D) := by
    have hD1_le : D + 1 ≤ 2 ^ (2 * D) := by
      have h1 : D + 1 ≤ D ^ 2 := by omega
      exact h1.trans (nat_sq_le_two_pow D)
    calc
      (D + 1) ^ 3 ≤ (2 ^ (2 * D)) ^ 3 := Nat.pow_le_pow_left hD1_le 3
      _ = 2 ^ (6 * D) := by
        rw [← Nat.pow_mul]
        exact congrArg (2 ^ ·) (by ring)
  have hBD_inner : (B ^ D) * (2 * D + 7) + B + 85 * (D + 1) ^ 3 + 6 ≤ 2 ^ (2 * E * D ^ 2) := by
    have hBD1 : B ^ D ≤ 2 ^ (E * D ^ 2) := by
      calc
        B ^ D ≤ (2 ^ (E * D)) ^ D := Nat.pow_le_pow_left hB_le D
        _ = 2 ^ (E * D ^ 2) := by
          rw [← Nat.pow_mul]
          exact congrArg (2 ^ ·) (by ring)
    have hBD2 : 2 * D + 7 ≤ 2 ^ (2 * D ^ 2) := by
      have h1 : 2 * D + 7 ≤ D ^ 2 := by omega
      have h2 : D ^ 2 ≤ 2 ^ (2 * D) := nat_sq_le_two_pow D
      have h3 : 2 ^ (2 * D) ≤ 2 ^ (2 * D ^ 2) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      exact (h1.trans h2).trans h3
    have hprod : (B ^ D) * (2 * D + 7) ≤ 2 ^ ((E + 2) * D ^ 2) := by
      calc
        (B ^ D) * (2 * D + 7) ≤ 2 ^ (E * D ^ 2) * 2 ^ (2 * D ^ 2) :=
          Nat.mul_le_mul hBD1 hBD2
        _ = 2 ^ ((E + 2) * D ^ 2) := by
          rw [← Nat.pow_add]
          exact congrArg (2 ^ ·) (by ring)
    have hED_le : E * D ≤ (E + 2) * D ^ 2 := by
      have h1 : E * D ≤ E * D ^ 2 := by
        calc
          E * D ≤ E * (640 * D) := Nat.mul_le_mul_left E (by omega)
          _ ≤ E * D ^ 2 := Nat.mul_le_mul_left E hD2
      have h2 : E * D ^ 2 ≤ (E + 2) * D ^ 2 := Nat.mul_le_mul_right (D ^ 2) (by omega)
      exact h1.trans h2
    have hB_powE : B ≤ 2 ^ ((E + 2) * D ^ 2) :=
      hB_le.trans (Nat.pow_le_pow_right (by norm_num) hED_le)
    have h85D3 : 85 * (D + 1) ^ 3 ≤ 2 ^ ((E + 2) * D ^ 2) := by
      have h85 : 85 ≤ 2 ^ 7 := by norm_num
      calc
        85 * (D + 1) ^ 3 ≤ 2 ^ 7 * 2 ^ (6 * D) := Nat.mul_le_mul h85 hD3_le
        _ = 2 ^ (7 + 6 * D) := (Nat.pow_add 2 7 (6 * D)).symm
        _ ≤ 2 ^ ((E + 2) * D ^ 2) :=
          Nat.pow_le_pow_right (by norm_num) (by nlinarith only [hD, hD2, hE20])
    have h6 : 6 ≤ 2 ^ ((E + 2) * D ^ 2) := by
      have h6_8 : 6 ≤ 2 ^ 3 := by norm_num
      exact h6_8.trans (Nat.pow_le_pow_right (by norm_num) (by nlinarith only [hD, hE20]))
    have hsum : 4 * 2 ^ ((E + 2) * D ^ 2) ≤ 2 ^ (2 * E * D ^ 2) := by
      have h4_pow : 4 * 2 ^ ((E + 2) * D ^ 2) = 2 ^ (2 + (E + 2) * D ^ 2) := by
        have : (4 : ℕ) = 2 ^ 2 := by norm_num
        rw [this, ← Nat.pow_add]
      rw [h4_pow]
      exact Nat.pow_le_pow_right (by norm_num) (by nlinarith only [hD, hE20])
    omega
  have hFBD_le : F * ((B ^ D) * (2 * D + 7) + B + 85 * (D + 1) ^ 3 + 6) ≤ 2 ^ (3 * E * D ^ 2) := by
    calc
      F * ((B ^ D) * (2 * D + 7) + B + 85 * (D + 1) ^ 3 + 6)
        ≤ 2 ^ (E * D ^ 2) * 2 ^ (2 * E * D ^ 2) :=
          Nat.mul_le_mul hF_le hBD_inner
      _ = 2 ^ (3 * E * D ^ 2) := by
        rw [← Nat.pow_add]
        exact congrArg (2 ^ ·) (by ring)
  have hD3B_le : (D + 1) ^ 3 * (85 * B + 95) ≤ 2 ^ (2 * E * D ^ 2) := by
    have h1 : (D + 1) ^ 3 ≤ 2 ^ (E * D ^ 2) :=
      hD3_le.trans (Nat.pow_le_pow_right (by norm_num) (by nlinarith only [hD, hD2, hE20]))
    have h2 : 85 * B + 95 ≤ 2 ^ (E * D ^ 2) := by
      have hED_pos : 1 ≤ 2 ^ (E * D) := Nat.one_le_two_pow
      have h85B : 85 * B + 95 ≤ 2 ^ 8 * 2 ^ (E * D) := by omega
      have hpow_add : 2 ^ 8 * 2 ^ (E * D) = 2 ^ (8 + E * D) := (Nat.pow_add 2 8 (E * D)).symm
      have hED_le2 : 8 + E * D ≤ E * D ^ 2 := by
        have hED_640 : E * (640 * D) ≤ E * D ^ 2 := Nat.mul_le_mul_left E hD2
        nlinarith only [hD, hE20, hED_640]
      exact (h85B.trans_eq hpow_add).trans (Nat.pow_le_pow_right (by norm_num) hED_le2)
    calc
      (D + 1) ^ 3 * (85 * B + 95) ≤ 2 ^ (E * D ^ 2) * 2 ^ (E * D ^ 2) := Nat.mul_le_mul h1 h2
      _ = 2 ^ (2 * E * D ^ 2) := by
        rw [← Nat.pow_add]
        exact congrArg (2 ^ ·) (by ring)
  have hD3B_and_D : (D + 1) ^ 3 * (85 * B + 95) + 12 * D + 23 ≤ 2 ^ (3 * E * D ^ 2) := by
    have hD_le : 12 * D + 23 ≤ 2 ^ (2 * E * D ^ 2) := by
      have h1 : 12 * D + 23 ≤ D ^ 2 := by omega
      have h2 : D ^ 2 ≤ 2 ^ (2 * D) := nat_sq_le_two_pow D
      have h3 : 2 ^ (2 * D) ≤ 2 ^ (2 * E * D ^ 2) :=
        Nat.pow_le_pow_right (by norm_num) (by nlinarith only [hD, hE20])
      exact (h1.trans h2).trans h3
    have h2_pow : 2 * 2 ^ (2 * E * D ^ 2) ≤ 2 ^ (3 * E * D ^ 2) := by
      have h1 : 2 * 2 ^ (2 * E * D ^ 2) = 2 ^ (1 + 2 * E * D ^ 2) := by
        rw [← Nat.pow_succ']
        exact congrArg (2 ^ ·) (by omega)
      rw [h1]
      exact Nat.pow_le_pow_right (by norm_num) (by nlinarith only [hD, hE20])
    omega
  have hlogB : bitLengthNat B ≤ E * D + 1 := by
    unfold bitLengthNat
    have hlog : Nat.log 2 B ≤ E * D :=
      (Nat.log_mono_right hB_le).trans_eq (Nat.log_pow (by norm_num) (E * D))
    omega
  have hpow_cost : (powNatTracked B (2 * D)).2 ≤ 2 ^ (3 * E * D ^ 2) := by
    unfold powNatTracked
    dsimp only
    have hD1 : 2 * D + 1 ≤ 2 ^ (E * D ^ 2) := by
      have h1 : 2 * D + 1 ≤ D ^ 2 := by omega
      have h2 : D ^ 2 ≤ 2 ^ (2 * D) := nat_sq_le_two_pow D
      have h3 : 2 ^ (2 * D) ≤ 2 ^ (E * D ^ 2) :=
        Nat.pow_le_pow_right (by norm_num) (by nlinarith only [hD, hE20])
      exact (h1.trans h2).trans h3
    have hDB : 2 * D * bitLengthNat B + 1 ≤ 2 ^ (E * D ^ 2) := by
      have hmul_b : 2 * D * bitLengthNat B ≤ 2 * D * (E * D + 1) :=
        Nat.mul_le_mul_left (2 * D) hlogB
      have h1 : 2 * D * bitLengthNat B + 1 ≤ (E * D) ^ 2 := by
        have hED_20 : 20 * D ≤ E * D := Nat.mul_le_mul_right D hE20
        have h2D_ED : 2 * D * (E * D + 1) + 1 ≤ 20 * D * (E * D) := by
          have : 640 ≤ E * D := by omega
          nlinarith only [hD, this]
        have hED_sq : 20 * D * (E * D) ≤ (E * D) ^ 2 := by
          rw [sq]
          exact Nat.mul_le_mul_right (E * D) hED_20
        omega
      have h2 : (E * D) ^ 2 ≤ 2 ^ (2 * (E * D)) := nat_sq_le_two_pow (E * D)
      have h3 : 2 * (E * D) ≤ E * D ^ 2 := by
        calc
          2 * (E * D) = E * (2 * D) := by ring
          _ ≤ E * (640 * D) := Nat.mul_le_mul_left E (by omega)
          _ ≤ E * D ^ 2 := Nat.mul_le_mul_left E hD2
      exact (h1.trans h2).trans (Nat.pow_le_pow_right (by norm_num) h3)
    calc
      (2 * D + 1) * (2 * D * bitLengthNat B + 1) * (2 * D * bitLengthNat B + 1)
        ≤ 2 ^ (E * D ^ 2) * 2 ^ (E * D ^ 2) * 2 ^ (E * D ^ 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul hD1 hDB) hDB
      _ = 2 ^ (3 * E * D ^ 2) := by
          rw [← Nat.pow_add, ← Nat.pow_add]
          exact congrArg (2 ^ ·) (by ring)
  have h4_pow : 4 * 2 ^ (3 * E * D ^ 2) ≤ 2 ^ (4 * E * D ^ 2) := by
    have h1 : 4 * 2 ^ (3 * E * D ^ 2) = 2 ^ (2 + 3 * E * D ^ 2) := by
      have : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [this, ← Nat.pow_add]
    rw [h1]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith only [hD, hE20])
  omega

lemma rRectFuel_160_le : rRectFuel (1 / 160 : ℝ) ≤ 15520 := by
  have h := rRect2DFuel_le_div (by norm_num : (0 : ℝ) < 1 / 160) le_rfl
  have h2 : (97 : ℝ) / (1 / 160 : ℝ) = ((15520 : ℕ) : ℝ) := by norm_num
  exact_mod_cast h.trans_eq h2

lemma goodRect3DStepFactor_160_le {D : ℕ} (hD : 640 ≤ D) :
    goodRect3DStepFactor (1 / 160 : ℝ) D ≤ (2 : ℝ) ^ (5 * D) := by
  unfold goodRect3DStepFactor
  have h1 : (48 : ℝ) / (1 / 160 : ℝ) ≤ (2 : ℝ) ^ (13 : ℕ) := by norm_num
  calc
    (48 / (1 / 160 : ℝ)) * (2 : ℝ) ^ (4 * D)
      ≤ (2 : ℝ) ^ (13 : ℕ) * (2 : ℝ) ^ (4 * D) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (2 : ℝ) ^ (13 + 4 * D) := (pow_add 2 13 (4 * D)).symm
    _ ≤ (2 : ℝ) ^ (5 * D) := pow_le_pow_right₀ (by norm_num) (by omega)

lemma M_rect3D_160_le {D : ℕ} (hD : 640 ≤ D) :
    M_rect3D (1 / 160 : ℝ) D ≤ (2 : ℝ) ^ (2 ^ 17 * D) := by
  unfold M_rect3D
  have hstep := goodRect3DStepFactor_160_le hD
  have hfuel := rRectFuel_160_le
  have hbase_ge_1 : 1 ≤ goodRect3DStepFactor (1 / 160 : ℝ) D :=
    one_le_goodRect3DStepFactor (by norm_num) (by norm_num) D
  have hpow1 :
      (goodRect3DStepFactor (1 / 160 : ℝ) D) ^ (rRectFuel (1 / 160 : ℝ)) ≤
        (goodRect3DStepFactor (1 / 160 : ℝ) D) ^ 15520 :=
    pow_le_pow_right₀ hbase_ge_1 hfuel
  have hpow2 :
      (goodRect3DStepFactor (1 / 160 : ℝ) D) ^ 15520 ≤ ((2 : ℝ) ^ (5 * D)) ^ 15520 :=
    pow_le_pow_left₀ (by linarith) hstep 15520
  have h3 : (3 : ℝ) ≤ (2 : ℝ) ^ (2 : ℕ) := by norm_num
  calc
    3 * (goodRect3DStepFactor (1 / 160 : ℝ) D) ^ (rRectFuel (1 / 160 : ℝ))
      ≤ (2 : ℝ) ^ (2 : ℕ) * ((2 : ℝ) ^ (5 * D)) ^ 15520 :=
        mul_le_mul h3 (hpow1.trans hpow2) (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (2 + 5 * D * 15520) := by rw [← pow_mul, ← pow_add]
    _ ≤ (2 : ℝ) ^ (2 ^ 17 * D) := pow_le_pow_right₀ (by norm_num) (by omega)

lemma rDecompAFuel_160_le {D : ℕ} (hD : 640 ≤ D) :
    rDecompAFuel (1 / 160 : ℝ) D ≤ 2 ^ (2 ^ 18 * D ^ 2) := by
  unfold rDecompAFuel
  rw [Nat.ceil_le, Nat.cast_pow, Nat.cast_ofNat]
  have hM := M_rect3D_160_le hD
  calc
    (2 : ℝ) ^ (D + D ^ 2) * M_rect3D (1 / 160 : ℝ) D
      ≤ (2 : ℝ) ^ (D + D ^ 2) * (2 : ℝ) ^ (2 ^ 17 * D) :=
        mul_le_mul_of_nonneg_left hM (by positivity)
    _ = (2 : ℝ) ^ (D + D ^ 2 + 2 ^ 17 * D) := (pow_add 2 _ _).symm
    _ ≤ (2 : ℝ) ^ (2 ^ 18 * D ^ 2) := pow_le_pow_right₀ (by norm_num) (by nlinarith)

lemma maxGoodCubeStepsReal_160_eq :
    maxGoodCubeStepsReal (1 / 160 : ℝ) gamma3D = ((5242881 : ℕ) : ℝ) := by
  unfold maxGoodCubeStepsReal gamma3D
  norm_num

lemma rCubeFuel_160_le : rCubeFuel (1 / 160 : ℝ) gamma3D ≤ 5242881 := by
  have h := rCubeFuel_le_maxGoodCubeStepsReal (by norm_num : (0 : ℝ) < 1 / 160)
    le_rfl gamma3D_pos gamma3D_le_one
  rw [maxGoodCubeStepsReal_160_eq] at h
  exact_mod_cast h

lemma goodCubeStepFactor_160_le {D : ℕ} (hD : 640 ≤ D) :
    goodCubeStepFactor (1 / 160 : ℝ) D ≤ (2 : ℝ) ^ (32000 * D) := by
  unfold goodCubeStepFactor
  have hexp : 4 * (D : ℝ) + 194 * (D : ℝ) / (1 / 160 : ℝ) = ((31044 * D : ℕ) : ℝ) := by
    push_cast; ring
  rw [hexp, Real.rpow_natCast]
  have h1 : (144 : ℝ) / (1 / 160 : ℝ) ≤ (2 : ℝ) ^ (15 : ℕ) := by norm_num
  calc
    (144 / (1 / 160 : ℝ)) * (2 : ℝ) ^ (31044 * D)
      ≤ (2 : ℝ) ^ (15 : ℕ) * (2 : ℝ) ^ (31044 * D) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (2 : ℝ) ^ (15 + 31044 * D) := (pow_add 2 15 _).symm
    _ ≤ (2 : ℝ) ^ (32000 * D) := pow_le_pow_right₀ (by norm_num) (by omega)

lemma M_cube_160_le {D : ℕ} (hD : 640 ≤ D) :
    M_cube (1 / 160 : ℝ) gamma3D D ≤ (2 : ℝ) ^ (2 ^ 38 * D) := by
  unfold M_cube
  rw [maxGoodCubeStepsReal_160_eq, Real.rpow_natCast]
  have hstep := goodCubeStepFactor_160_le hD
  have hbase0 : 0 ≤ goodCubeStepFactor (1 / 160 : ℝ) D := by
    linarith [one_le_goodCubeStepFactor (by norm_num : (0 : ℝ) < 1 / 160) (by norm_num) D]
  have hpow :
      (goodCubeStepFactor (1 / 160 : ℝ) D) ^ 5242881 ≤ ((2 : ℝ) ^ (32000 * D)) ^ 5242881 :=
    pow_le_pow_left₀ hbase0 hstep 5242881
  have h3 : (3 : ℝ) ≤ (2 : ℝ) ^ (2 : ℕ) := by norm_num
  have hpow0 : 0 ≤ (goodCubeStepFactor (1 / 160 : ℝ) D) ^ 5242881 := pow_nonneg hbase0 5242881
  have h4_0 : (0 : ℝ) ≤ (2 : ℝ) ^ (2 : ℕ) := by norm_num
  calc
    3 * (goodCubeStepFactor (1 / 160 : ℝ) D) ^ 5242881
      ≤ (2 : ℝ) ^ (2 : ℕ) * ((2 : ℝ) ^ (32000 * D)) ^ 5242881 :=
        mul_le_mul h3 hpow hpow0 h4_0
    _ = (2 : ℝ) ^ (2 + 32000 * D * 5242881) := by rw [← pow_mul, ← pow_add]
    _ ≤ (2 : ℝ) ^ (2 ^ 38 * D) := pow_le_pow_right₀ (by norm_num) (by omega)

lemma rSStarFuel_160_le {D : ℕ} (hD : 640 ≤ D) :
    rSStarFuel (1 / 160 : ℝ) D ≤ 2 ^ (2 ^ 39 * D ^ 2) := by
  unfold rSStarFuel
  rw [Nat.ceil_le, Nat.cast_pow, Nat.cast_ofNat]
  have hM := M_cube_160_le hD
  calc
    (2 : ℝ) ^ (D + D ^ 2) * M_cube (1 / 160 : ℝ) gamma3D D
      ≤ (2 : ℝ) ^ (D + D ^ 2) * (2 : ℝ) ^ (2 ^ 38 * D) :=
        mul_le_mul_of_nonneg_left hM (by positivity)
    _ = (2 : ℝ) ^ (D + D ^ 2 + 2 ^ 38 * D) := (pow_add 2 _ _).symm
    _ ≤ (2 : ℝ) ^ (2 ^ 39 * D ^ 2) := pow_le_pow_right₀ (by norm_num) (by nlinarith)

lemma QTree3D_160_le {D : ℕ} (hD : 640 ≤ D) :
    QTree3D (1 / 160 : ℝ) D ≤ (2 : ℝ) ^ (2 ^ 39 * D) := by
  unfold QTree3D
  have hMc := M_cube_160_le hD
  have hMr := M_rect3D_160_le hD
  have hMc0 : 0 ≤ M_cube (1 / 160 : ℝ) gamma3D D :=
    (M_cube_pos (by norm_num) (by norm_num) gamma3D_pos D).le
  have hMr0 : 0 ≤ M_rect3D (1 / 160 : ℝ) D :=
    (M_rect3D_pos (by norm_num) (by norm_num) D).le
  calc
    (2 : ℝ) ^ (60 * D) * M_cube (1 / 160 : ℝ) gamma3D D * M_rect3D (1 / 160 : ℝ) D
      ≤ (2 : ℝ) ^ (60 * D) * (2 : ℝ) ^ (2 ^ 38 * D) * (2 : ℝ) ^ (2 ^ 17 * D) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hMc (by positivity)) hMr hMr0 (by positivity)
    _ = (2 : ℝ) ^ (60 * D + 2 ^ 38 * D + 2 ^ 17 * D) := by rw [← pow_add, ← pow_add]
    _ ≤ (2 : ℝ) ^ (2 ^ 39 * D) := pow_le_pow_right₀ (by norm_num) (by omega)

lemma GammaTree3D_160_le {D : ℕ} (hD : 640 ≤ D) :
    GammaTree3D (1 / 160 : ℝ) D ≤ 2 ^ 40 * D := by
  unfold GammaTree3D
  have h2D_nat : 2 * D + 4 ≤ 2 ^ (2 * D) := by
    have h1 : 2 * D + 4 ≤ D ^ 2 := by nlinarith
    exact h1.trans (nat_sq_le_two_pow D)
  have h2D : 2 * (D : ℝ) + 4 ≤ (2 : ℝ) ^ (2 * D) := by exact_mod_cast h2D_nat
  have hQ := QTree3D_160_le hD
  have hQ0 : 0 ≤ QTree3D (1 / 160 : ℝ) D := by
    unfold QTree3D
    have hMc0 := (M_cube_pos (by norm_num : (0 : ℝ) < 1 / 160) (by norm_num) gamma3D_pos D).le
    have hMr0 := (M_rect3D_pos (by norm_num : (0 : ℝ) < 1 / 160) (by norm_num) D).le
    positivity
  have hceil :
      Nat.ceil ((2 * (D : ℝ) + 4) * QTree3D (1 / 160 : ℝ) D) ≤ 2 ^ (2 * D + 2 ^ 39 * D) := by
    rw [Nat.ceil_le, Nat.cast_pow, Nat.cast_ofNat]
    calc
      (2 * (D : ℝ) + 4) * QTree3D (1 / 160 : ℝ) D
        ≤ (2 : ℝ) ^ (2 * D) * (2 : ℝ) ^ (2 ^ 39 * D) :=
          mul_le_mul h2D hQ hQ0 (by positivity)
      _ = (2 : ℝ) ^ (2 * D + 2 ^ 39 * D) := (pow_add 2 _ _).symm
  have hclog :
      Nat.clog 2 (Nat.ceil ((2 * (D : ℝ) + 4) * QTree3D (1 / 160 : ℝ) D)) ≤
        2 * D + 2 ^ 39 * D := by
    calc
      Nat.clog 2 (Nat.ceil ((2 * (D : ℝ) + 4) * QTree3D (1 / 160 : ℝ) D))
        ≤ Nat.clog 2 (2 ^ (2 * D + 2 ^ 39 * D)) := Nat.clog_mono_right 2 hceil
      _ = 2 * D + 2 ^ 39 * D := Nat.clog_pow _ _ (by norm_num)
  omega

private lemma two_pow_add_self_le {a b : ℕ} (h : a + 1 ≤ b) :
    2 ^ a + 2 ^ a ≤ 2 ^ b := by
  have h1 : 2 ^ a + 2 ^ a = 2 ^ (a + 1) := by rw [Nat.pow_succ]; ring
  rw [h1]
  exact Nat.pow_le_pow_right (by norm_num) h

lemma abDepthCostFactor_160_le (c k : ℕ) {D : ℕ} (hD : 640 ≤ D) :
    abDepthCostFactor c k (1 / 160 : ℝ) D ≤
      2 ^ ((2 ^ 40 + 4 * samplerOverheadExp c k) * D ^ 2) := by
  set E := samplerOverheadExp c k
  have hE20 : 20 ≤ E := twenty_le_samplerOverheadExp c k
  have hrA := rDecompAFuel_160_le hD
  have hrR := rRectFuel_160_le
  have hagn := concreteApproxGridNormCostFactor_le_pow c k hD
  have hrC := rCubeFuel_160_le
  have hrS := rSStarFuel_160_le hD
  have hstep_cost : goodCubeStepCostFactor c k (1 / 160 : ℝ) D ≤
      2 ^ ((2 ^ 20 + 4 * E) * D ^ 2) := by
    unfold goodCubeStepCostFactor
    have h1 : rDecompAFuel (1 / 160 : ℝ) D + 2 ≤ 2 ^ (2 ^ 18 * D ^ 2 + 2) := by
      have : 2 ≤ 2 ^ (2 ^ 18 * D ^ 2) :=
        Nat.le_self_pow (by nlinarith only [hD]) 2
      have : rDecompAFuel (1 / 160 : ℝ) D + 2 ≤ 2 * 2 ^ (2 ^ 18 * D ^ 2) := by omega
      have hpow : 2 * 2 ^ (2 ^ 18 * D ^ 2) ≤ 2 ^ (2 ^ 18 * D ^ 2 + 2) := by
        rw [Nat.pow_add]; omega
      exact this.trans hpow
    have h2 : rRectFuel (1 / 160 : ℝ) + 3 ≤ 2 ^ 14 := by omega
    calc
      (rDecompAFuel (1 / 160 : ℝ) D + 2) * (rRectFuel (1 / 160 : ℝ) + 3) *
          (concreteApproxGridNormCostFactor c k (1 / 160 : ℝ) D + 2 * D + 7)
        ≤ 2 ^ (2 ^ 18 * D ^ 2 + 2) * 2 ^ 14 * 2 ^ (4 * E * D ^ 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul h1 h2) hagn
      _ = 2 ^ (2 ^ 18 * D ^ 2 + 2 + 14 + 4 * E * D ^ 2) := by rw [← Nat.pow_add, ← Nat.pow_add]
      _ ≤ 2 ^ ((2 ^ 20 + 4 * E) * D ^ 2) :=
        Nat.pow_le_pow_right (by norm_num) (by nlinarith only [hD, hE20])
  have hiter_cost : abIterCostFactor c k (1 / 160 : ℝ) D ≤
      2 ^ ((2 ^ 22 + 4 * E) * D ^ 2) := by
    unfold abIterCostFactor
    have hc1 : rCubeFuel (1 / 160 : ℝ) gamma3D + 1 ≤ 2 ^ 23 := by omega
    have hterm1 :
        (rCubeFuel (1 / 160 : ℝ) gamma3D + 1) * goodCubeStepCostFactor c k (1 / 160 : ℝ) D ≤
          2 ^ ((2 ^ 21 + 4 * E) * D ^ 2) := by
      calc
        (rCubeFuel (1 / 160 : ℝ) gamma3D + 1) * goodCubeStepCostFactor c k (1 / 160 : ℝ) D
          ≤ 2 ^ 23 * 2 ^ ((2 ^ 20 + 4 * E) * D ^ 2) := Nat.mul_le_mul hc1 hstep_cost
        _ = 2 ^ (23 + (2 ^ 20 + 4 * E) * D ^ 2) := (Nat.pow_add 2 23 _).symm
        _ ≤ 2 ^ ((2 ^ 21 + 4 * E) * D ^ 2) :=
          Nat.pow_le_pow_right (by norm_num) (by nlinarith only [hD, hE20])
    have hD2 : D + deltaHACostFactor D + 2 ≤ 2 ^ (100 * D) := by
      unfold deltaHACostFactor
      have hsq50 : D + 2400 * (D + 1) ^ 2 + 2 ≤ (50 * D) ^ 2 := by nlinarith only [hD]
      have hpow50 : (50 * D) ^ 2 ≤ 2 ^ (2 * (50 * D)) := nat_sq_le_two_pow (50 * D)
      have h100 : 2 * (50 * D) = 100 * D := by ring
      rw [h100] at hpow50
      exact hsq50.trans hpow50
    have hrA2 : rDecompAFuel (1 / 160 : ℝ) D + 2 ≤ 2 ^ (2 ^ 18 * D ^ 2 + 2) := by
      have : 2 ≤ 2 ^ (2 ^ 18 * D ^ 2) := Nat.le_self_pow (by nlinarith only [hD]) 2
      have hle : rDecompAFuel (1 / 160 : ℝ) D + 2 ≤ 2 * 2 ^ (2 ^ 18 * D ^ 2) := by omega
      have hpow : 2 * 2 ^ (2 ^ 18 * D ^ 2) ≤ 2 ^ (2 ^ 18 * D ^ 2 + 2) := by rw [Nat.pow_add]; omega
      exact hle.trans hpow
    have hterm2 :
        (D + deltaHACostFactor D + 2) * (rDecompAFuel (1 / 160 : ℝ) D + 2) + 2404 ≤
          2 ^ ((2 ^ 21 + 4 * E) * D ^ 2) := by
      have hm :
          (D + deltaHACostFactor D + 2) * (rDecompAFuel (1 / 160 : ℝ) D + 2) ≤
            2 ^ (100 * D + (2 ^ 18 * D ^ 2 + 2)) := by
        rw [Nat.pow_add]
        exact Nat.mul_le_mul hD2 hrA2
      have hpow :
          2 ^ (100 * D + (2 ^ 18 * D ^ 2 + 2)) + 2404 ≤ 2 ^ ((2 ^ 21 + 4 * E) * D ^ 2) := by
        have h4 : 2404 ≤ 2 ^ (100 * D + (2 ^ 18 * D ^ 2 + 2)) := by
          have h2404 : 2404 ≤ 2 ^ 12 := by norm_num
          exact h2404.trans (Nat.pow_le_pow_right (by norm_num) (by nlinarith only [hD]))
        have hsum_le :
            2 ^ (100 * D + (2 ^ 18 * D ^ 2 + 2)) + 2 ^ (100 * D + (2 ^ 18 * D ^ 2 + 2)) ≤
              2 ^ ((2 ^ 21 + 4 * E) * D ^ 2) :=
          two_pow_add_self_le (by nlinarith only [hD, hE20])
        omega
      omega
    have hsum :
        2 ^ ((2 ^ 21 + 4 * E) * D ^ 2) + 2 ^ ((2 ^ 21 + 4 * E) * D ^ 2) ≤
          2 ^ ((2 ^ 22 + 4 * E) * D ^ 2) :=
      two_pow_add_self_le (by nlinarith only [hD, hE20])
    omega
  unfold abDepthCostFactor
  have hrS2 : rSStarFuel (1 / 160 : ℝ) D + 2 ≤ 2 ^ (2 ^ 39 * D ^ 2 + 2) := by
    have : 2 ≤ 2 ^ (2 ^ 39 * D ^ 2) := Nat.le_self_pow (by nlinarith only [hD]) 2
    have hle : rSStarFuel (1 / 160 : ℝ) D + 2 ≤ 2 * 2 ^ (2 ^ 39 * D ^ 2) := by omega
    have hpow : 2 * 2 ^ (2 ^ 39 * D ^ 2) ≤ 2 ^ (2 ^ 39 * D ^ 2 + 2) := by rw [Nat.pow_add]; omega
    exact hle.trans hpow
  have hprod :
      (rSStarFuel (1 / 160 : ℝ) D + 2) * abIterCostFactor c k (1 / 160 : ℝ) D ≤
        2 ^ (2 ^ 39 * D ^ 2 + 2 + (2 ^ 22 + 4 * E) * D ^ 2) := by
    rw [Nat.pow_add]
    exact Nat.mul_le_mul hrS2 hiter_cost
  have h4 : 4 ≤ 2 ^ (2 ^ 39 * D ^ 2 + 2 + (2 ^ 22 + 4 * E) * D ^ 2) := by
    change 2 ^ 2 ≤ 2 ^ (2 ^ 39 * D ^ 2 + 2 + (2 ^ 22 + 4 * E) * D ^ 2)
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith only [hD, hE20])
  have hsum :
      2 ^ (2 ^ 39 * D ^ 2 + 2 + (2 ^ 22 + 4 * E) * D ^ 2) +
        2 ^ (2 ^ 39 * D ^ 2 + 2 + (2 ^ 22 + 4 * E) * D ^ 2) ≤
        2 ^ ((2 ^ 40 + 4 * E) * D ^ 2) :=
    two_pow_add_self_le (by nlinarith only [hD, hE20])
  omega

/-- Concrete exponent coefficient $2^{44} + 16 \cdot \text{samplerOverheadExp } c\ k$ for the
$2^{O(d^2)}$ piece-count and cost bound of `cappedABDecomposition` (`decompPieceBound`). -/
def decompExpCoeff (c k : ℕ) : ℕ :=
  2 ^ 44 + 16 * samplerOverheadExp c k

/-- Exponential piece-count and cost bound $F_{c, k}(d) := 2^{\text{decompExpCoeff}(c, k) \cdot d^2}$
parameterized by the two-stage sampler constants $(c, k)$ and regularity parameter $d$.
Defined via `Nat.ceil` of a real power so the kernel never reduces `2 ^ (decompExpCoeff c k * 320 ^ 2)`
to a ground `Nat` literal when checking expressions involving `decompPieceBound c k 320`. -/
noncomputable def decompPieceBound (c k d : ℕ) : ℕ :=
  Nat.ceil ((2 : ℝ) ^ (decompExpCoeff c k * d ^ 2))

lemma decompPieceBound_eq (c k d : ℕ) :
    decompPieceBound c k d = 2 ^ (decompExpCoeff c k * d ^ 2) := by
  unfold decompPieceBound
  exact_mod_cast Nat.ceil_natCast (2 ^ (decompExpCoeff c k * d ^ 2))

lemma one_le_decompPieceBound (c k d : ℕ) : 1 ≤ decompPieceBound c k d := by
  rw [decompPieceBound_eq]
  exact Nat.one_le_pow (decompExpCoeff c k * d ^ 2) 2 (by decide)

lemma decompPieceBound_mul_pow_eq (c k d s : ℕ) :
    decompPieceBound c k d * 2 ^ s = 2 ^ (decompExpCoeff c k * d ^ 2 + s) := by
  rw [decompPieceBound_eq]
  exact (Nat.pow_add 2 (decompExpCoeff c k * d ^ 2) s).symm

/-- **Concrete $2^{O(d^2)}$ Piece-Count and Cost Bound for `cappedABDecomposition`
(`cappedABDecomposition_concrete_bounds`, `paper.tex` §6)**:
For any $d \ge 320$ and $n \times n$ boolean matrices $A, B$, at $\varepsilon = 1/160$ and $D = 2d$:
1. `pieces.length ≤ decompPieceBound S.c S.k d`, and
2. `(cappedABDecompositionTracked ...).2 ≤ (3 * n + 2) ^ 2 * decompPieceBound S.c S.k d`. -/
theorem cappedABDecomposition_concrete_bounds {n d : ℕ} (hd : 320 ≤ d)
    (S : TwoStageSamplerOracle (Fin n) (1 / 160 : ℝ))
    (A B : Fin n → Fin n → Bool) :
    let pieces := cappedABDecomposition Finset.univ Finset.univ Finset.univ
      (bmatToReal A) (bmatToReal B) (1 / 160 : ℝ) S (2 * d)
    pieces.length ≤ decompPieceBound S.c S.k d ∧
    (2 ^ 29 + 512 * (d + 1) ^ 3 + 2) * pieces.length ≤ decompPieceBound S.c S.k d ∧
    (cappedABDecompositionTracked Finset.univ Finset.univ Finset.univ
      (bmatToReal A) (bmatToReal B) (1 / 160 : ℝ) S (2 * d)).2 ≤
      (3 * n + 2) ^ 2 * decompPieceBound S.c S.k d := by
  rw [decompPieceBound_eq]
  dsimp only
  set pieces := cappedABDecomposition Finset.univ Finset.univ Finset.univ
    (bmatToReal A) (bmatToReal B) (1 / 160 : ℝ) S (2 * d)
  have hA_bin : IsBinaryMatrix Finset.univ Finset.univ (bmatToReal A) :=
    isBinaryMatrix_bmatToReal Finset.univ Finset.univ A
  have hB_bin : IsBinaryMatrix Finset.univ Finset.univ (bmatToReal B) :=
    isBinaryMatrix_bmatToReal Finset.univ Finset.univ B
  have hD : 640 ≤ 2 * d := by omega
  have hH : H3D (2 * d) ≤ 3 * d := by unfold H3D; omega
  have hGamma := GammaTree3D_160_le hD
  have hlen_real := cappedABDecomposition_length_le Finset.univ Finset.univ Finset.univ
    (bmatToReal A) (bmatToReal B) (ε := (1 / 160 : ℝ)) (D := 2 * d) S
    hA_bin hB_bin (by norm_num) le_rfl (by omega)
  have hlen_43 : pieces.length ≤ 2 ^ (2 ^ 43 * d ^ 2) := by
    have h3 : (3 : ℝ) ≤ (2 : ℝ) ^ (2 : ℕ) := by norm_num
    have hexp_le :
        2 + ((2 * d) + (2 * d) ^ 2 + GammaTree3D (1 / 160 : ℝ) (2 * d) * H3D (2 * d)) ≤
          2 ^ 43 * d ^ 2 := by
      have hG_mul :
          GammaTree3D (1 / 160 : ℝ) (2 * d) * H3D (2 * d) ≤ (2 ^ 40 * (2 * d)) * (3 * d) :=
        Nat.mul_le_mul hGamma hH
      nlinarith
    have hreal : (pieces.length : ℝ) ≤ ((2 ^ (2 ^ 43 * d ^ 2) : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Nat.cast_ofNat]
      calc
        (pieces.length : ℝ)
          ≤ 3 * (2 : ℝ) ^ ((2 * d) + (2 * d) ^ 2 +
              GammaTree3D (1 / 160 : ℝ) (2 * d) * H3D (2 * d)) := hlen_real
        _ ≤ (2 : ℝ) ^ (2 : ℕ) * (2 : ℝ) ^ ((2 * d) + (2 * d) ^ 2 +
              GammaTree3D (1 / 160 : ℝ) (2 * d) * H3D (2 * d)) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = (2 : ℝ) ^ (2 + ((2 * d) + (2 * d) ^ 2 +
              GammaTree3D (1 / 160 : ℝ) (2 * d) * H3D (2 * d))) := (pow_add 2 2 _).symm
        _ ≤ (2 : ℝ) ^ (2 ^ 43 * d ^ 2) := pow_le_pow_right₀ (by norm_num) hexp_le
    exact_mod_cast hreal
  have hlen_44 : pieces.length ≤ 2 ^ (decompExpCoeff S.c S.k * d ^ 2) := by
    unfold decompExpCoeff
    exact hlen_43.trans (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
  have hovh_44 :
      (2 ^ 29 + 512 * (d + 1) ^ 3 + 2) * pieces.length ≤
        2 ^ (decompExpCoeff S.c S.k * d ^ 2) := by
    unfold decompExpCoeff
    have hd_pow : d + 1 ≤ 2 ^ (2 * d) := by
      have : d + 1 ≤ d ^ 2 := by nlinarith
      exact this.trans (nat_sq_le_two_pow d)
    have hd3_pow : (d + 1) ^ 3 ≤ 2 ^ (6 * d) := by
      calc
        (d + 1) ^ 3 ≤ (2 ^ (2 * d)) ^ 3 := Nat.pow_le_pow_left hd_pow 3
        _ = 2 ^ (2 * d * 3) := (Nat.pow_mul 2 (2 * d) 3).symm
        _ = 2 ^ (6 * d) := by ring_nf
    have hfac_pow : 2 ^ 29 + 512 * (d + 1) ^ 3 + 2 ≤ 2 ^ (10 + 6 * d) := by
      have h512 : 512 * (d + 1) ^ 3 ≤ 2 ^ 9 * 2 ^ (6 * d) := Nat.mul_le_mul_left 512 hd3_pow
      rw [← Nat.pow_add] at h512
      have h29 : 2 ^ 29 + 2 ≤ 2 ^ (9 + 6 * d) := by
        have h30 : 2 ^ 29 + 2 ≤ 2 ^ 30 := by decide
        exact h30.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
      have hsum : 2 ^ (9 + 6 * d) + 2 ^ (9 + 6 * d) = 2 ^ (10 + 6 * d) := by
        have : 10 + 6 * d = (9 + 6 * d) + 1 := by omega
        rw [this, Nat.pow_succ]
        ring
      omega
    calc
      (2 ^ 29 + 512 * (d + 1) ^ 3 + 2) * pieces.length
        ≤ 2 ^ (10 + 6 * d) * 2 ^ (2 ^ 43 * d ^ 2) := Nat.mul_le_mul hfac_pow hlen_43
      _ = 2 ^ (10 + 6 * d + 2 ^ 43 * d ^ 2) := (Nat.pow_add 2 (10 + 6 * d) _).symm
      _ ≤ 2 ^ ((2 ^ 44 + 16 * samplerOverheadExp S.c S.k) * d ^ 2) :=
          Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  refine ⟨hlen_44, hovh_44, ?_⟩
  have hcost := cappedABDecompositionTracked_snd_le Finset.univ Finset.univ Finset.univ
    (bmatToReal A) (bmatToReal B) (1 / 160 : ℝ) S (2 * d)
  have hcards :
      (Finset.univ : Finset (Fin n)).card + (Finset.univ : Finset (Fin n)).card +
        (Finset.univ : Finset (Fin n)).card + 2 = 3 * n + 2 := by
    simp; omega
  rw [hcards] at hcost
  have hH_pow : H3D (2 * d) + 1 ≤ 2 ^ (4 * d) := by
    have h1 : H3D (2 * d) + 1 ≤ (2 * d) ^ 2 := by nlinarith
    have h2 : (2 * d) ^ 2 ≤ 2 ^ (2 * (2 * d)) := nat_sq_le_two_pow (2 * d)
    have h3 : 2 * (2 * d) = 4 * d := by ring
    rw [h3] at h2
    exact h1.trans h2
  have hab := abDepthCostFactor_160_le S.c S.k hD
  have hfac_44 :
      (H3D (2 * d) + 1) * abDepthCostFactor S.c S.k (1 / 160 : ℝ) (2 * d) * pieces.length ≤
        2 ^ (decompExpCoeff S.c S.k * d ^ 2) := by
    unfold decompExpCoeff
    calc
      (H3D (2 * d) + 1) * abDepthCostFactor S.c S.k (1 / 160 : ℝ) (2 * d) * pieces.length
        ≤ 2 ^ (4 * d) *
            2 ^ ((2 ^ 40 + 4 * samplerOverheadExp S.c S.k) * (2 * d) ^ 2) *
            2 ^ (2 ^ 43 * d ^ 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul hH_pow hab) hlen_43
      _ = 2 ^ (4 * d +
            (2 ^ 40 + 4 * samplerOverheadExp S.c S.k) * (2 * d) ^ 2 +
            2 ^ 43 * d ^ 2) := by
          rw [← Nat.pow_add, ← Nat.pow_add]
      _ ≤ 2 ^ ((2 ^ 44 + 16 * samplerOverheadExp S.c S.k) * d ^ 2) :=
          Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hcomm :
      ((H3D (2 * d) + 1) * abDepthCostFactor S.c S.k (1 / 160 : ℝ) (2 * d) * (3 * n + 2) ^ 2) * pieces.length =
        (3 * n + 2) ^ 2 *
          ((H3D (2 * d) + 1) * abDepthCostFactor S.c S.k (1 / 160 : ℝ) (2 * d) * pieces.length) := by ring
  rw [hcomm] at hcost
  exact hcost.trans (Nat.mul_le_mul_left ((3 * n + 2) ^ 2) hfac_44)

/-- **`paper.tex` Theorem 1.1 (`thm_main_3d_decomposition`, §1.2)**:
Unified end-to-end 3D regularity decomposition theorem for $n \times n$ Boolean matrices $A, B$ at
$\varepsilon = 1/160$ and $D = 2d$ ($d \ge 320$):
`cappedABDecompositionTracked` computes a valid 3D decomposition (`IsValid3DDecomposition n d A B`)
of at most $2^{\text{decompExpCoeff}(S.c, S.k) \cdot d^2}$ pieces in cost at most
$(3n + 2)^2 \cdot 2^{\text{decompExpCoeff}(S.c, S.k) \cdot d^2}$. -/
theorem thm_main_3d_decomposition {n d : ℕ} (hd : 320 ≤ d)
    (S : TwoStageSamplerOracle (Fin n) (1 / 160 : ℝ))
    (A B : Fin n → Fin n → Bool) :
    let run := cappedABDecompositionTracked Finset.univ Finset.univ Finset.univ
      (bmatToReal A) (bmatToReal B) (1 / 160 : ℝ) S (2 * d)
    run.1 = cappedABDecomposition Finset.univ Finset.univ Finset.univ
      (bmatToReal A) (bmatToReal B) (1 / 160 : ℝ) S (2 * d) ∧
    IsValid3DDecomposition n d A B run.1 ∧
    run.1.length ≤ 2 ^ (decompExpCoeff S.c S.k * d ^ 2) ∧
    run.2 ≤ (3 * n + 2) ^ 2 * 2 ^ (decompExpCoeff S.c S.k * d ^ 2) := by
  dsimp only
  have hfst := cappedABDecompositionTracked_fst Finset.univ Finset.univ Finset.univ
    (bmatToReal A) (bmatToReal B) (1 / 160 : ℝ) S (2 * d)
  have hvalid := cappedABDecomposition_isValid3DDecomposition (by omega : 1 ≤ d) S A B
  rcases cappedABDecomposition_concrete_bounds hd S A B with ⟨hlen, _, hcost⟩
  rw [decompPieceBound_eq] at hlen hcost
  rw [hfst]
  exact ⟨rfl, hvalid, hlen, hcost⟩

/-!
### Sampler-Conditional End-to-End Algorithm 6 (`computableTriangleDetection`, `paper.tex` §6)
-/

/-- Inverse constant $c_0^{-1}(c, k) = 2^{23} + 4 \cdot \text{samplerOverheadExp } c\ k$
for Algorithm 6 Line 2 (`\label{line:tri-init}`, `paper.tex` §6). -/
def triDetC0Inv (c k : ℕ) : ℕ :=
  2 ^ 23 + 4 * samplerOverheadExp c k

/-- Exponent divisor $D_{\text{tri}}(c, k) = 640 \cdot c_0^{-1}(c, k)$ for the
$2^{\Omega(\sqrt{\log n})}$ saving factor in Algorithm 6 (`paper.tex` §6). -/
def D_tri (c k : ℕ) : ℕ := 640 * triDetC0Inv c k

lemma D_tri_pos (c k : ℕ) : 0 < D_tri c k := by
  unfold D_tri triDetC0Inv
  positivity

/-- Explicit uniform constant $C_{\text{tri}}(c, k) = 43 \cdot \text{decompPieceBound } c\ k\ 320 + 256$
for Algorithm 6 (`thm_main_triangle_detection`, `paper.tex` §6). -/
noncomputable def C_tri (c k : ℕ) : ℕ := 43 * decompPieceBound c k 320 + 256

lemma C_tri_pos (c k : ℕ) : 0 < C_tri c k :=
  Nat.add_pos_right (43 * decompPieceBound c k 320) (by decide)

lemma D_tri_le_decompPieceBound (c k : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    D_tri c k ≤ decompPieceBound c k d := by
  rw [decompPieceBound_eq]
  unfold D_tri triDetC0Inv decompExpCoeff
  set E := samplerOverheadExp c k
  have hE20 : 20 ≤ E := twenty_le_samplerOverheadExp c k
  have hd2 : 1 ≤ d ^ 2 := by nlinarith
  have hE_pow : E ≤ 2 ^ E := self_le_two_pow E
  have h12 : 2560 ≤ 2 ^ 12 := by norm_num
  have h12_E : 2 ^ 12 ≤ 2 ^ (15 * E) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hterm2 : 2560 * E ≤ 2 ^ (16 * E) := by
    calc
      2560 * E ≤ 2 ^ 12 * 2 ^ E := Nat.mul_le_mul h12 hE_pow
      _ ≤ 2 ^ (15 * E) * 2 ^ E := Nat.mul_le_mul_right _ h12_E
      _ = 2 ^ (16 * E) := by rw [← Nat.pow_add]; congr 1; omega
  have hterm1 : 640 * 2 ^ 23 ≤ 2 ^ (16 * E) := by
    have h1 : 640 * 2 ^ 23 ≤ 2 ^ 33 := by norm_num
    exact h1.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hsum : 640 * (2 ^ 23 + 4 * E) ≤ 2 ^ (1 + 16 * E) := by
    have : 2 ^ (1 + 16 * E) = 2 ^ (16 * E) + 2 ^ (16 * E) := by
      rw [Nat.pow_add]; ring
    omega
  exact hsum.trans (Nat.pow_le_pow_right (by norm_num) (by nlinarith))

/-- Regularity parameter $d_{c, k}(n) := \max(320, \lfloor \sqrt{\lfloor \log_2 n \rfloor} / \text{triDetC0Inv}(c, k) \rfloor)$
(`paper.tex` Algorithm 6 Line 2, §6). -/
def triDetParamD (c k n : ℕ) : ℕ :=
  max 320 (Nat.sqrt (Nat.log 2 n) / triDetC0Inv c k)

/-- Exact floor-division identity for `triDetParamD` (`paper.tex` Algorithm 6 Line 2, §6):
for integer $m = c_0^{-1} = \text{triDetC0Inv}(c, k)$,
$\lfloor \lfloor \sqrt{\lfloor \log_2 n \rfloor} \rfloor / m \rfloor = \lfloor \sqrt{\lfloor \log_2 n \rfloor} / m \rfloor$. -/
lemma triDetParamD_eq_floor_div (c k n : ℕ) :
    triDetParamD c k n = max 320 (Nat.floor (Real.sqrt (Nat.log 2 n : ℝ) / (triDetC0Inv c k : ℝ))) := by
  unfold triDetParamD; congr 1; symm
  have hm : 0 < triDetC0Inv c k := by unfold triDetC0Inv; omega
  have hmR : (0 : ℝ) < (triDetC0Inv c k : ℝ) := by exact_mod_cast hm
  rw [Nat.floor_eq_iff (by positivity), le_div_iff₀ hmR, div_lt_iff₀ hmR]
  have hs1 : ((Nat.sqrt (Nat.log 2 n) : ℝ)) ≤ Real.sqrt (Nat.log 2 n : ℝ) := by
    rw [← Real.sqrt_sq (Nat.cast_nonneg _)]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (show (Nat.sqrt (Nat.log 2 n)) ^ 2 ≤ _ by rw [sq]; exact Nat.sqrt_le _))
  have hs2 : Real.sqrt (Nat.log 2 n : ℝ) < (Nat.sqrt (Nat.log 2 n) : ℝ) + 1 := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (Nat.sqrt (Nat.log 2 n) : ℝ) + 1)]
    exact Real.sqrt_lt_sqrt (Nat.cast_nonneg _) (by
      exact_mod_cast (show _ < (Nat.sqrt (Nat.log 2 n) + 1) ^ 2 by rw [sq]; exact Nat.lt_succ_sqrt _))
  have hd1 : ((Nat.sqrt (Nat.log 2 n) / triDetC0Inv c k * triDetC0Inv c k : ℕ) : ℝ) ≤
      (Nat.sqrt (Nat.log 2 n) : ℝ) := by exact_mod_cast Nat.div_mul_le_self _ _
  have hd2 : (Nat.sqrt (Nat.log 2 n) : ℝ) + 1 ≤
      (((Nat.sqrt (Nat.log 2 n) / triDetC0Inv c k + 1) * triDetC0Inv c k : ℕ) : ℝ) := by
    have hdiv := Nat.div_add_mod (Nat.sqrt (Nat.log 2 n)) (triDetC0Inv c k); have hmod := Nat.mod_lt (Nat.sqrt (Nat.log 2 n)) hm
    have hmul : (Nat.sqrt (Nat.log 2 n) / triDetC0Inv c k + 1) * triDetC0Inv c k =
        triDetC0Inv c k * (Nat.sqrt (Nat.log 2 n) / triDetC0Inv c k) + triDetC0Inv c k := by ring
    exact_mod_cast (by omega : Nat.sqrt (Nat.log 2 n) + 1 ≤ _)
  push_cast at hd1 hd2; exact ⟨hd1.trans hs1, hs2.trans_le hd2⟩

lemma le_320_triDetParamD (c k n : ℕ) : 320 ≤ triDetParamD c k n :=
  le_max_left 320 _

lemma one_le_triDetParamD (c k n : ℕ) : 1 ≤ triDetParamD c k n :=
  (by omega : 1 ≤ 320).trans (le_320_triDetParamD c k n)

/-- Cost-tracked evaluation of `triDetParamD c k n = max 320 (Nat.sqrt (Nat.log 2 n) / triDetC0Inv c k)`
in `CostM` (`paper.tex` Algorithm 6 Line 2 `\label{line:tri-init}`, §6). -/
def triDetParamDTracked (c k n : ℕ) : CostM ℕ :=
  CostM.bind (log2NatTracked n) (fun lg =>
    CostM.bind (sqrtNatTracked lg) (fun s =>
      CostM.bind (divNatTracked s (triDetC0Inv c k)) (fun q =>
        CostM.bind (cmpLeNatTracked 320 q) (fun b =>
          if b then retTracked q else retTracked 320))))

@[simp]
theorem triDetParamDTracked_fst (c k n : ℕ) :
    (triDetParamDTracked c k n).1 = triDetParamD c k n := by
  unfold triDetParamDTracked triDetParamD log2NatTracked sqrtNatTracked divNatTracked cmpLeNatTracked
  dsimp only [CostM.bind_fst, retTracked_fst]
  by_cases h : 320 ≤ Nat.sqrt (Nat.log 2 n) / triDetC0Inv c k
  · simp [h]
  · simp [h, max_eq_left (le_of_not_ge h)]

lemma triDetParamDTracked_cost_le (c k : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    (triDetParamDTracked c k n).2 + (mulNatTracked 2 (triDetParamD c k n)).2 + 1 ≤
      (100 + 2 * triDetC0Inv c k) * n ^ 2 := by
  unfold triDetParamDTracked log2NatTracked sqrtNatTracked divNatTracked cmpLeNatTracked mulNatTracked
  dsimp only [CostM.bind_snd]
  have hite : ∀ (b : Bool) (a₁ a₂ : ℕ), (if b then retTracked a₁ else retTracked a₂).2 = 1 := by
    intro b a₁ a₂; cases b <;> rfl
  rw [hite]
  have hbitC0 : bitLengthNat (triDetC0Inv c k) ≤ triDetC0Inv c k + 1 :=
    bitLengthNat_le_succ (triDetC0Inv c k)
  have hbit320 : bitLengthNat 320 = 9 := by decide
  have hbit2 : bitLengthNat 2 = 2 := by decide
  rw [hbit320, hbit2]
  have hlog_le : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
  have hsqrt_le : Nat.sqrt (Nat.log 2 n) ≤ n :=
    (Nat.sqrt_le_self _).trans hlog_le
  have hq_le : Nat.sqrt (Nat.log 2 n) / triDetC0Inv c k ≤ n :=
    (Nat.div_le_self _ _).trans hsqrt_le
  have hb_n : bitLengthNat n ≤ n + 1 := bitLengthNat_le_succ n
  have hb_log1 : bitLengthNat (Nat.log 2 n) + 1 ≤ n + 2 := by
    have := bitLengthNat_le_succ (Nat.log 2 n)
    omega
  have hb_log_sq :
      (bitLengthNat (Nat.log 2 n) + 1) * (bitLengthNat (Nat.log 2 n) + 1) ≤ (n + 2) * (n + 2) :=
    Nat.mul_le_mul hb_log1 hb_log1
  have hb_sqrt : bitLengthNat (Nat.sqrt (Nat.log 2 n)) ≤ n + 1 :=
    (bitLengthNat_le_succ _).trans (by omega)
  have hdiv_cost :
      bitLengthNat (Nat.sqrt (Nat.log 2 n)) * bitLengthNat (triDetC0Inv c k) ≤
        (n + 1) * (triDetC0Inv c k + 1) :=
    Nat.mul_le_mul hb_sqrt hbitC0
  have hb_q : bitLengthNat (Nat.sqrt (Nat.log 2 n) / triDetC0Inv c k) ≤ n + 1 :=
    (bitLengthNat_le_succ _).trans (by omega)
  have hb_d : bitLengthNat (triDetParamD c k n) ≤ n + 9 := by
    unfold triDetParamD
    rcases max_choice 320 (Nat.sqrt (Nat.log 2 n) / triDetC0Inv c k) with h | h
    · rw [h, hbit320]; omega
    · rw [h]; omega
  have hn2 : n ≤ n ^ 2 := by nlinarith
  nlinarith

lemma hundred_add_two_mul_triDetC0Inv_le_decompPieceBound (c k : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    100 + 2 * triDetC0Inv c k ≤ decompPieceBound c k d := by
  have h1 : 100 + 2 * triDetC0Inv c k ≤ D_tri c k := by
    unfold D_tri triDetC0Inv
    omega
  exact h1.trans (D_tri_le_decompPieceBound c k hd)

/-- **Algorithm 6 Parameterized by `TwoStageSamplerOracle` (`computableTriangleDetection_of_sampler`,
`paper.tex` §6)**:
Sampler-conditional combinatorial Triangle Detection via `cappedABDecomposition` and
`triangleDetectionOnPieces` with zero schoolbook fallback bypass. -/
noncomputable def computableTriangleDetection_of_sampler (n : ℕ)
    (S : TwoStageSamplerOracle (Fin n) (1 / 160 : ℝ))
    (A B C : Fin n → Fin n → Bool) : Bool :=
  let d := triDetParamD S.c S.k n
  let pieces := cappedABDecomposition Finset.univ Finset.univ Finset.univ
    (bmatToReal A) (bmatToReal B) (1 / 160 : ℝ) S (2 * d)
  triangleDetectionOnPieces n d C pieces

/-- **Bottom-Up Cost-Tracked Algorithm 6 Parameterized by `TwoStageSamplerOracle`
(`computableTriangleDetectionTracked_of_sampler`, `paper.tex` §6)**. -/
noncomputable def computableTriangleDetectionTracked_of_sampler (n : ℕ)
    (S : TwoStageSamplerOracle (Fin n) (1 / 160 : ℝ))
    (A B C : Fin n → Fin n → Bool) : CostM Bool :=
  CostM.bind (triDetParamDTracked S.c S.k n) (fun d =>
    CostM.bind (mulNatTracked 2 d) (fun two_d =>
      CostM.bind
        (cappedABDecompositionTracked Finset.univ Finset.univ Finset.univ
          (bmatToReal A) (bmatToReal B) (1 / 160 : ℝ) S two_d)
        (fun pieces =>
          CostM.bind
            (triangleDetectionOnPiecesTracked n d C pieces)
            (fun ans => retTracked ans))))

/-- Projection equivalence `computableTriangleDetectionTracked_of_sampler_fst`. -/
@[simp]
theorem computableTriangleDetectionTracked_of_sampler_fst (n : ℕ)
    (S : TwoStageSamplerOracle (Fin n) (1 / 160 : ℝ))
    (A B C : Fin n → Fin n → Bool) :
    (computableTriangleDetectionTracked_of_sampler n S A B C).1 =
      computableTriangleDetection_of_sampler n S A B C := by
  unfold computableTriangleDetectionTracked_of_sampler computableTriangleDetection_of_sampler
  have hmul : ∀ x : ℕ, (mulNatTracked 2 x).1 = 2 * x := fun _ => rfl
  simp only [CostM.bind_fst, retTracked_fst, triDetParamDTracked_fst, hmul,
    cappedABDecompositionTracked_fst, triangleDetectionOnPiecesTracked_fst]

/-- **Oracle-Parameterized Correctness of `computableTriangleDetection_of_sampler`
(`paper.tex` §6)**. -/
theorem computableTriangleDetection_of_sampler_correct (n : ℕ)
    (S : TwoStageSamplerOracle (Fin n) (1 / 160 : ℝ))
    (A B C : Fin n → Fin n → Bool) :
    computableTriangleDetection_of_sampler n S A B C = hasTriangle n A B C := by
  unfold computableTriangleDetection_of_sampler
  exact triangleDetectionOnPieces_correct (le_320_triDetParamD S.c S.k n) A B C _
    (cappedABDecomposition_isValid3DDecomposition (one_le_triDetParamD S.c S.k n) S A B)

/-- Key exponent absorption lemma for Algorithm 6 (`paper.tex` §6):
For every $n \ge 1$, letting $d = \text{triDetParamD } c\ k\ n$ and
$s = \lfloor \sqrt{\log_2 n} / D_{\text{tri}}(c, k) \rfloor$, we have
$$\text{decompPieceBound } c\ k\ d \cdot 2^s \le \text{decompPieceBound } c\ k\ 320 \cdot n.$$ -/
lemma triDet_overhead_mul_saving_le (c k : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    decompPieceBound c k (triDetParamD c k n) * 2 ^ (Nat.sqrt (Nat.log 2 n) / D_tri c k) ≤
      decompPieceBound c k 320 * n := by
  set d₀ := Nat.sqrt (Nat.log 2 n) / triDetC0Inv c k
  have hs_eq : Nat.sqrt (Nat.log 2 n) / D_tri c k = d₀ / 640 := by
    have hD : D_tri c k = triDetC0Inv c k * 640 := Nat.mul_comm 640 (triDetC0Inv c k)
    rw [hD, ← Nat.div_div_eq_div_mul]
  rw [hs_eq]
  by_cases hd₀ : d₀ ≤ 320
  · have hd_eq : decompPieceBound c k (triDetParamD c k n) = decompPieceBound c k 320 :=
      congrArg (decompPieceBound c k) (max_eq_left hd₀)
    have hs0 : d₀ / 640 = 0 := Nat.div_eq_of_lt (by omega)
    rw [hd_eq, hs0, Nat.pow_zero, mul_one]
    exact Nat.le_mul_of_pos_right (decompPieceBound c k 320) hn
  · push_neg at hd₀
    have hd_eq : decompPieceBound c k (triDetParamD c k n) = decompPieceBound c k d₀ :=
      congrArg (decompPieceBound c k) (max_eq_right hd₀.le)
    rw [hd_eq, decompPieceBound_mul_pow_eq]
    have hs_le : d₀ / 640 ≤ d₀ := Nat.div_le_self d₀ 640
    have hexp1 : decompExpCoeff c k * d₀ ^ 2 + d₀ / 640 ≤ (d₀ * triDetC0Inv c k) ^ 2 := by
      unfold decompExpCoeff triDetC0Inv
      set E := samplerOverheadExp c k
      have hsq : (d₀ * (2 ^ 23 + 4 * E)) ^ 2 =
          (2 ^ 46 + 2 ^ 26 * E + 16 * E ^ 2) * d₀ ^ 2 := by ring
      rw [hsq]
      nlinarith
    have hmul_le : d₀ * triDetC0Inv c k ≤ Nat.sqrt (Nat.log 2 n) :=
      Nat.div_mul_le_self (Nat.sqrt (Nat.log 2 n)) (triDetC0Inv c k)
    have hsq_le : (d₀ * triDetC0Inv c k) ^ 2 ≤ Nat.log 2 n := by
      calc
        (d₀ * triDetC0Inv c k) ^ 2
          ≤ (Nat.sqrt (Nat.log 2 n)) ^ 2 := Nat.pow_le_pow_left hmul_le 2
        _ = Nat.sqrt (Nat.log 2 n) * Nat.sqrt (Nat.log 2 n) := sq _
        _ ≤ Nat.log 2 n := Nat.sqrt_le (Nat.log 2 n)
    have hpow_n : 2 ^ (decompExpCoeff c k * d₀ ^ 2 + d₀ / 640) ≤ n := by
      calc
        2 ^ (decompExpCoeff c k * d₀ ^ 2 + d₀ / 640)
          ≤ 2 ^ (Nat.log 2 n) := Nat.pow_le_pow_right (by norm_num) (hexp1.trans hsq_le)
        _ ≤ n := Nat.pow_log_le_self 2 (by omega)
    exact hpow_n.trans (Nat.le_mul_of_pos_left n (one_le_decompPieceBound c k 320))

lemma combine_triDet_work_bounds {n decompCost scanCost pCost ovhLen K_d K_0 S_pow : ℕ}
    (hn : 1 ≤ n)
    (hpCost : pCost ≤ K_d * n ^ 2)
    (hK_d : 1 ≤ K_d)
    (hovh : ovhLen ≤ 11 * n ^ 2 * K_d)
    (hdecomp : decompCost ≤ (3 * n + 2) ^ 2 * K_d)
    (hscan : scanCost * S_pow ≤ (ovhLen + 1) * S_pow + 256 * n ^ 3)
    (hoverhead : K_d * S_pow ≤ K_0 * n) :
    (decompCost + (scanCost + pCost)) * S_pow ≤ (43 * K_0 + 256) * n ^ 3 := by
  have h3n2 : (3 * n + 2) ^ 2 ≤ 25 * n ^ 2 := by nlinarith
  have hdecomp_25 : decompCost ≤ 25 * n ^ 2 * K_d :=
    hdecomp.trans (Nat.mul_le_mul_right K_d h3n2)
  have hscan_len : ovhLen + (1 + pCost) ≤ 18 * n ^ 2 * K_d := by
    have h2 : 1 + pCost ≤ 7 * n ^ 2 * K_d := by nlinarith
    linarith
  calc
    (decompCost + (scanCost + pCost)) * S_pow
      = decompCost * S_pow + scanCost * S_pow + pCost * S_pow := by ring
    _ ≤ (25 * n ^ 2 * K_d) * S_pow + ((ovhLen + 1) * S_pow + 256 * n ^ 3) +
          pCost * S_pow :=
        Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right S_pow hdecomp_25) hscan) le_rfl
    _ = (25 * n ^ 2 * K_d + (ovhLen + (1 + pCost))) * S_pow + 256 * n ^ 3 := by
        ring
    _ ≤ (25 * n ^ 2 * K_d + 18 * n ^ 2 * K_d) * S_pow + 256 * n ^ 3 :=
        Nat.add_le_add_right (Nat.mul_le_mul_right S_pow (Nat.add_le_add_left hscan_len _)) _
    _ = 43 * n ^ 2 * (K_d * S_pow) + 256 * n ^ 3 := by ring
    _ ≤ 43 * n ^ 2 * (K_0 * n) + 256 * n ^ 3 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hoverhead) _
    _ = (43 * K_0 + 256) * n ^ 3 := by ring

/-- **Master Correctness and Subcubic Cost Specification of `computableTriangleDetectionTracked_of_sampler`
(`computableTriangleDetectionTracked_of_sampler_spec`, `paper.tex` §6)**:
For every $n \ge 1$, any `S : TwoStageSamplerOracle (Fin n) (1 / 160 : ℝ)`, and all $n \times n$
boolean matrices $A, B, C$, binding
`let run := computableTriangleDetectionTracked_of_sampler n S A B C` once:
`run.1 = hasTriangle n A B C` and
$$run.2 \cdot 2^{\lfloor \sqrt{\log_2 n} / D_{\text{tri}}(S.c, S.k) \rfloor}
  \le C_{\text{tri}}(S.c, S.k) \cdot n^3.$$ -/
theorem computableTriangleDetectionTracked_of_sampler_spec {n : ℕ} (hn : 1 ≤ n)
    (S : TwoStageSamplerOracle (Fin n) (1 / 160 : ℝ))
    (A B C : Fin n → Fin n → Bool) :
    let run := computableTriangleDetectionTracked_of_sampler n S A B C
    run.1 = hasTriangle n A B C ∧
    run.2 * 2 ^ (Nat.sqrt (Nat.log 2 n) / D_tri S.c S.k) ≤ C_tri S.c S.k * n ^ 3 := by
  dsimp only
  refine ⟨by rw [computableTriangleDetectionTracked_of_sampler_fst,
    computableTriangleDetection_of_sampler_correct], ?_⟩
  set d := triDetParamD S.c S.k n
  set s := Nat.sqrt (Nat.log 2 n) / D_tri S.c S.k
  set pieces := cappedABDecomposition Finset.univ Finset.univ Finset.univ
    (bmatToReal A) (bmatToReal B) (1 / 160 : ℝ) S (2 * d)
  have hd320 : 320 ≤ d := le_320_triDetParamD S.c S.k n
  have hd1 : 1 ≤ d := one_le_triDetParamD S.c S.k n
  have hvalid := cappedABDecomposition_isValid3DDecomposition hd1 S A B
  rcases cappedABDecomposition_concrete_bounds hd320 S A B with ⟨_hlen_le, hovh_44, hdecomp_cost⟩
  have hovh_bound :
      (pieceOverhead n d + 2) * pieces.length ≤ 11 * n ^ 2 * decompPieceBound S.c S.k d := by
    have hp_le : pieceOverhead n d + 2 ≤ n ^ 2 * (2 ^ 29 + 512 * (d + 1) ^ 3 + 2) := by
      unfold pieceOverhead
      have hn1 : (n + 1) ^ 2 ≤ 4 * n ^ 2 := by nlinarith
      have hn2 : 1 ≤ n ^ 2 := by nlinarith
      have hd_mul : 512 * (d + 1) ^ 3 + 2 ≤ n ^ 2 * (512 * (d + 1) ^ 3 + 2) :=
        Nat.le_mul_of_pos_left _ hn2
      have hdist : n ^ 2 * (2 ^ 29 + 512 * (d + 1) ^ 3 + 2) =
          2 ^ 29 * n ^ 2 + n ^ 2 * (512 * (d + 1) ^ 3 + 2) := by ring
      omega
    calc
      (pieceOverhead n d + 2) * pieces.length
        ≤ (n ^ 2 * (2 ^ 29 + 512 * (d + 1) ^ 3 + 2)) * pieces.length :=
          Nat.mul_le_mul_right pieces.length hp_le
      _ = n ^ 2 * ((2 ^ 29 + 512 * (d + 1) ^ 3 + 2) * pieces.length) := by ring
      _ ≤ n ^ 2 * decompPieceBound S.c S.k d := Nat.mul_le_mul_left (n ^ 2) hovh_44
      _ ≤ 11 * n ^ 2 * decompPieceBound S.c S.k d := by nlinarith
  have hscan_real := triangleDetectionOnPiecesTracked_valid_work_bound A B C pieces hvalid
  have hs_le_d640 : s ≤ d / 640 := by
    have hD : D_tri S.c S.k = triDetC0Inv S.c S.k * 640 := Nat.mul_comm 640 (triDetC0Inv S.c S.k)
    have hs_eq : s = (Nat.sqrt (Nat.log 2 n) / triDetC0Inv S.c S.k) / 640 := by
      unfold s; rw [hD, ← Nat.div_div_eq_div_mul]
    rw [hs_eq]
    exact Nat.div_le_div_right (le_max_right 320 _)
  have hs_mul_d : 640 * s ≤ d := by
    have := Nat.mul_div_le d 640
    linarith [Nat.mul_le_mul_left 640 hs_le_d640]
  have hs_real_d : 640 * (s : ℝ) ≤ (d : ℝ) := by exact_mod_cast hs_mul_d
  have hpow_sum_le :
      ((2 : ℝ) ^ (- (d : ℝ)) + (2 : ℝ) ^ (- ((1 / 160 : ℝ) * (d : ℝ) / 2))) * (2 : ℝ) ^ s ≤ 2 := by
    have h1 : (2 : ℝ) ^ (- (d : ℝ)) ≤ (2 : ℝ) ^ (- (s : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h2 : (2 : ℝ) ^ (- ((1 / 160 : ℝ) * (d : ℝ) / 2)) ≤ (2 : ℝ) ^ (- (s : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hcancel : (2 : ℝ) ^ (- (s : ℝ)) * (2 : ℝ) ^ s = 1 := by
      rw [← Real.rpow_natCast 2 s, ← Real.rpow_add (by norm_num), neg_add_cancel, Real.rpow_zero]
    calc
      ((2 : ℝ) ^ (- (d : ℝ)) + (2 : ℝ) ^ (- ((1 / 160 : ℝ) * (d : ℝ) / 2))) * (2 : ℝ) ^ s
        ≤ ((2 : ℝ) ^ (- (s : ℝ)) + (2 : ℝ) ^ (- (s : ℝ))) * (2 : ℝ) ^ s :=
          mul_le_mul_of_nonneg_right (add_le_add h1 h2) (by positivity)
      _ = 2 * ((2 : ℝ) ^ (- (s : ℝ)) * (2 : ℝ) ^ s) := by ring
      _ = 2 := by rw [hcancel]; ring
  have hscan_nat :
      (triangleDetectionOnPiecesTracked n d C pieces).2 * 2 ^ s ≤
        ((pieceOverhead n d + 2) * pieces.length + 1) * 2 ^ s + 256 * n ^ 3 := by
    have hmul_s := mul_le_mul_of_nonneg_right hscan_real (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ s)
    have hpot_term :
        128 * ((2 : ℝ) ^ (- (d : ℝ)) + (2 : ℝ) ^ (- ((1 / 160 : ℝ) * (d : ℝ) / 2))) *
          (n : ℝ) ^ 3 * (2 : ℝ) ^ s ≤ 256 * (n : ℝ) ^ 3 := by
      have hcomm :
          128 * ((2 : ℝ) ^ (- (d : ℝ)) + (2 : ℝ) ^ (- ((1 / 160 : ℝ) * (d : ℝ) / 2))) *
            (n : ℝ) ^ 3 * (2 : ℝ) ^ s =
          128 * (n : ℝ) ^ 3 *
            (((2 : ℝ) ^ (- (d : ℝ)) + (2 : ℝ) ^ (- ((1 / 160 : ℝ) * (d : ℝ) / 2))) *
              (2 : ℝ) ^ s) := by ring
      rw [hcomm]
      have := mul_le_mul_of_nonneg_left hpow_sum_le (by positivity : (0 : ℝ) ≤ 128 * (n : ℝ) ^ 3)
      linarith
    have hreal_bound :
        (((triangleDetectionOnPiecesTracked n d C pieces).2 * 2 ^ s : ℕ) : ℝ) ≤
          ((((pieceOverhead n d + 2) * pieces.length + 1) * 2 ^ s + 256 * n ^ 3 : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hreal_bound
  have hparam_le :
      (triDetParamDTracked S.c S.k n).2 + (mulNatTracked 2 d).2 + 1 ≤
        decompPieceBound S.c S.k d * n ^ 2 :=
    (triDetParamDTracked_cost_le S.c S.k hn).trans
      (Nat.mul_le_mul_right (n ^ 2)
        (hundred_add_two_mul_triDetC0Inv_le_decompPieceBound S.c S.k hd1))
  have htotal_cost_eq :
      (computableTriangleDetectionTracked_of_sampler n S A B C).2 =
        (cappedABDecompositionTracked Finset.univ Finset.univ Finset.univ
          (bmatToReal A) (bmatToReal B) (1 / 160 : ℝ) S (2 * d)).2 +
        ((triangleDetectionOnPiecesTracked n d C pieces).2 +
          ((triDetParamDTracked S.c S.k n).2 + (mulNatTracked 2 d).2 + 1)) := by
    unfold computableTriangleDetectionTracked_of_sampler
    have hmul : ∀ x : ℕ, (mulNatTracked 2 x).1 = 2 * x := fun _ => rfl
    simp only [CostM.bind_snd, retTracked_snd, triDetParamDTracked_fst, hmul,
      cappedABDecompositionTracked_fst]
    dsimp only [d, pieces]
    omega
  rw [htotal_cost_eq]
  exact combine_triDet_work_bounds hn hparam_le (one_le_decompPieceBound S.c S.k d)
    hovh_bound hdecomp_cost hscan_nat (triDet_overhead_mul_saving_le S.c S.k hn)

/-- **Algorithm 6 (`computableTriangleDetection`, `paper.tex` §6)**:
Sampler-conditional combinatorial Triangle Detection instantiated with the two-stage sampler
`twoStage_compose S₁ S₂ (1 / 160 : ℝ)` from `[AFKLM24, Lemma 4.4]` and `[Vadhan, Cor. 6.24]`,
with zero schoolbook fallback bypass. -/
noncomputable def computableTriangleDetection (n : ℕ)
    (S₁ : Stage1Sampler) (S₂ : Stage2Sampler)
    (A B C : Fin n → Fin n → Bool) : Bool :=
  computableTriangleDetection_of_sampler n
    (twoStage_compose S₁ S₂ (1 / 160 : ℝ) (by norm_num)) A B C

/-- **Bottom-Up Cost-Tracked Algorithm 6 (`computableTriangleDetectionTracked`,
`paper.tex` §6)**. -/
noncomputable def computableTriangleDetectionTracked (n : ℕ)
    (S₁ : Stage1Sampler) (S₂ : Stage2Sampler)
    (A B C : Fin n → Fin n → Bool) : CostM Bool :=
  computableTriangleDetectionTracked_of_sampler n
    (twoStage_compose S₁ S₂ (1 / 160 : ℝ) (by norm_num)) A B C

/-- Projection equivalence `computableTriangleDetectionTracked_fst`. -/
@[simp]
theorem computableTriangleDetectionTracked_fst (n : ℕ)
    (S₁ : Stage1Sampler) (S₂ : Stage2Sampler)
    (A B C : Fin n → Fin n → Bool) :
    (computableTriangleDetectionTracked n S₁ S₂ A B C).1 =
      computableTriangleDetection n S₁ S₂ A B C :=
  computableTriangleDetectionTracked_of_sampler_fst n
    (twoStage_compose S₁ S₂ (1 / 160 : ℝ) (by norm_num)) A B C

/-- **Sampler-Conditional Correctness of Algorithm 6 (`computableTriangleDetection_correct`,
`paper.tex` §6)**:
For every $n \in \mathbb{N}$, any `(S₁ : Stage1Sampler) (S₂ : Stage2Sampler)`, and all $n \times n$
boolean matrices $A, B, C$, `computableTriangleDetection n S₁ S₂ A B C = hasTriangle n A B C`. -/
theorem computableTriangleDetection_correct (n : ℕ)
    (S₁ : Stage1Sampler) (S₂ : Stage2Sampler)
    (A B C : Fin n → Fin n → Bool) :
    computableTriangleDetection n S₁ S₂ A B C = hasTriangle n A B C :=
  computableTriangleDetection_of_sampler_correct n
    (twoStage_compose S₁ S₂ (1 / 160 : ℝ) (by norm_num)) A B C

/-- **Master Correctness and Subcubic Cost Specification of Algorithm 6
(`computableTriangleDetectionTracked_spec`, `paper.tex` §6)**:
For every $n \ge 1$, any `(S₁ : Stage1Sampler) (S₂ : Stage2Sampler)`, and all $n \times n$ boolean
matrices $A, B, C$, binding `let run := computableTriangleDetectionTracked n S₁ S₂ A B C` once:
`run.1 = hasTriangle n A B C` and
$$run.2 \cdot 2^{\lfloor \sqrt{\log_2 n} / D_{\text{tri}}(c, k) \rfloor}
  \le C_{\text{tri}}(c, k) \cdot n^3$$
where $c = \text{twoStageConstC } S_1\ S_2$ and $k = \text{twoStageConstK } S_1\ S_2$. -/
theorem computableTriangleDetectionTracked_spec {n : ℕ} (hn : 1 ≤ n)
    (S₁ : Stage1Sampler) (S₂ : Stage2Sampler)
    (A B C : Fin n → Fin n → Bool) :
    let c := twoStageConstC S₁ S₂
    let k := twoStageConstK S₁ S₂
    let run := computableTriangleDetectionTracked n S₁ S₂ A B C
    run.1 = hasTriangle n A B C ∧
    run.2 * 2 ^ (Nat.sqrt (Nat.log 2 n) / D_tri c k) ≤ C_tri c k * n ^ 3 :=
  computableTriangleDetectionTracked_of_sampler_spec hn
    (twoStage_compose S₁ S₂ (1 / 160 : ℝ) (by norm_num)) A B C

/-- **Headline Triangle Detection Theorem (`thm_main_triangle_detection`,
`paper.tex` Section 6)**:
For any Stage 1 oblivious sampler `S₁ : Stage1Sampler` (`[AFKLM24, Lemma 4.4]` / `[GW97]`) and
Stage 2 averaging sampler `S₂ : Stage2Sampler` (`[Vadhan, Cor. 6.24]` / `[GUV09]`), there exist
uniform constants $C > 0$ and $D > 0$ (independent of $n, A, B, C_{\text{mat}}$) such that for all
$n \ge 2$ and all $n \times n$ Boolean matrices $A, B, C_{\text{mat}}$, there exists $t \in \mathbb{N}$
such that `computableTriangleDetectionTracked n S₁ S₂ A B C_mat = (hasTriangle n A B C_mat, t)` and
$$t \cdot 2^{\lfloor \sqrt{\log_2 n} / D \rfloor} \le C \cdot n^3.$$ -/
theorem thm_main_triangle_detection :
    ∀ (S₁ : Stage1Sampler) (S₂ : Stage2Sampler),
      ∃ C > 0, ∃ D > 0, ∀ n ≥ 2,
        ∀ (A B C_mat : Fin n → Fin n → Bool),
          ∃ t : ℕ,
            computableTriangleDetectionTracked n S₁ S₂ A B C_mat =
              (hasTriangle n A B C_mat, t) ∧
            t * 2 ^ (Nat.sqrt (Nat.log 2 n) / D) ≤ C * n ^ 3 := by
  intro S₁ S₂
  let c := twoStageConstC S₁ S₂
  let k := twoStageConstK S₁ S₂
  refine ⟨C_tri c k, C_tri_pos c k, D_tri c k, D_tri_pos c k, ?_⟩
  intro n hn A B C_mat
  rcases computableTriangleDetectionTracked_spec (by omega) S₁ S₂ A B C_mat with ⟨hfst, hsnd⟩
  refine ⟨(computableTriangleDetectionTracked n S₁ S₂ A B C_mat).2, ?_, hsnd⟩
  exact Prod.ext hfst rfl

/-- **Graph Triangle Detection Corollary (`thm_main_triangle_detection_graph`,
`paper.tex` Theorem 1.2 `\label{thm:main-bmm}`, §1.2 & §6)**:
Specializing `thm_main_triangle_detection` to $A = B = C_{\text{mat}} = \text{Adj}$ decides whether
an $n$-vertex graph with adjacency matrix $\text{Adj}$ contains a triangle in
$O(n^3 / 2^{\Omega(\sqrt{\log n})})$ time. -/
theorem thm_main_triangle_detection_graph :
    ∀ (S₁ : Stage1Sampler) (S₂ : Stage2Sampler),
      ∃ C > 0, ∃ D > 0, ∀ n ≥ 2,
        ∀ (Adj : Fin n → Fin n → Bool),
          ∃ t : ℕ,
            computableTriangleDetectionTracked n S₁ S₂ Adj Adj Adj =
              (hasTriangle n Adj Adj Adj, t) ∧
            t * 2 ^ (Nat.sqrt (Nat.log 2 n) / D) ≤ C * n ^ 3 := by
  intro S₁ S₂
  rcases thm_main_triangle_detection S₁ S₂ with ⟨C, hC, D, hD, hmain⟩
  exact ⟨C, hC, D, hD, fun n hn Adj => hmain n hn Adj Adj Adj⟩

/-- **Simple-Graph Triangle Witness Bridge (`hasTriangle_eq_true_iff_strictMono_of_symm_irrefl`,
`paper.tex` Theorem 1.2 `\label{thm:main-bmm}`, §1.2 & §6)**:
For any undirected, loopless graph on `Fin n` (whose adjacency matrix `Adj` is symmetric and
irreflexive), `hasTriangle n Adj Adj Adj = true` if and only if there exist three strictly ordered
vertices `i < j < k` in `Fin n` forming a triangle (`Adj i j = true ∧ Adj j k = true ∧ Adj i k = true`). -/
theorem hasTriangle_eq_true_iff_strictMono_of_symm_irrefl {n : ℕ}
    {Adj : Fin n → Fin n → Bool}
    (hsymm : ∀ u v : Fin n, Adj u v = Adj v u)
    (hirrefl : ∀ u : Fin n, Adj u u = false) :
    hasTriangle n Adj Adj Adj = true ↔
      ∃ i j k : Fin n, i < j ∧ j < k ∧
        Adj i j = true ∧ Adj j k = true ∧ Adj i k = true := by
  rw [hasTriangle_eq_true_iff]
  constructor
  · rintro ⟨a, b, c, hab, hbc, hac⟩
    have hba : Adj b a = true := by rw [hsymm]; exact hab
    have hcb : Adj c b = true := by rw [hsymm]; exact hbc
    have hca : Adj c a = true := by rw [hsymm]; exact hac
    have hab_ne : a ≠ b := by rintro rfl; rw [hirrefl] at hab; cases hab
    have hbc_ne : b ≠ c := by rintro rfl; rw [hirrefl] at hbc; cases hbc
    have hac_ne : a ≠ c := by rintro rfl; rw [hirrefl] at hac; cases hac
    rcases lt_trichotomy a b with h1 | rfl | h1
    · rcases lt_trichotomy b c with h2 | rfl | h2
      · exact ⟨a, b, c, h1, h2, hab, hbc, hac⟩
      · exact False.elim (hbc_ne rfl)
      · rcases lt_trichotomy a c with h3 | rfl | h3
        · exact ⟨a, c, b, h3, h2, hac, hcb, hab⟩
        · exact False.elim (hac_ne rfl)
        · exact ⟨c, a, b, h3, h1, hca, hab, hcb⟩
    · exact False.elim (hab_ne rfl)
    · rcases lt_trichotomy a c with h2 | rfl | h2
      · exact ⟨b, a, c, h1, h2, hba, hac, hbc⟩
      · exact False.elim (hac_ne rfl)
      · rcases lt_trichotomy b c with h3 | rfl | h3
        · exact ⟨b, c, a, h3, h2, hbc, hca, hba⟩
        · exact False.elim (hbc_ne rfl)
        · exact ⟨c, b, a, h3, h1, hcb, hba, hca⟩
  · rintro ⟨i, j, k, _, _, hij, hjk, hik⟩
    exact ⟨i, j, k, hij, hjk, hik⟩

end Algorithm6

/-!
## Part 3: Reduction from BMM to Triangle Detection (Lemma 6.1, `\label{lem:bmm-to-tridet}`, `paper.tex` §6)

We formalize Vassilevska Williams and Williams's combinatorial reduction (Lemma 6.1 `\label{lem:bmm-to-tridet}`,
`paper.tex` §6):
- Set block size $m := \max(1, \lfloor n^{1/4} \rfloor) = \max(1, \lfloor \sqrt{\lfloor \sqrt{n} \rfloor} \rfloor)$
  (without evaluating $f$; for $n < 16$, $m = 1$ directly evaluates $1 \times 1 \times 1$ block triples).
- Partition $[n]$ into $q = \lceil n / m \rceil$ blocks $I_0, \dots, I_{q-1}$ of size at most $m$.
- Initialize $C = \mathbf{1}_{n \times n}$ (all `true`).
- For each block triple $(a, b, c) \in [q]^3$:
  - While the $m \times m$ Triangle Detection algorithm reports a triangle in $(A_{a,b}, B_{b,c}, C_{a,c})$:
    - Exhaustively scan $I_a \times I_b \times I_c$ in $O(m^3)$ time to find $(x, y, z)$ with
      $A(x,y) = B(y,z) = C(x,z) = \text{true}$.
    - Set $C(x,z) \leftarrow \text{false}$ (strictly decreasing $\operatorname{nnz}(C)$ by $1$:
      `nnz_C_strictly_decreases_on_triangle`).
- Return $\mathbf{1}_{n \times n} - C$ (`fun x z => !C x z`).
-/

section Lemma61

/-- Number of blocks $q = \lceil n / m \rceil = (n + m - 1) / m$ (`paper.tex` §6). -/
def numBlocksBMM (n m : ℕ) : ℕ :=
  (n + m - 1) / m

lemma self_le_cube (m : ℕ) : m ≤ m ^ 3 := by
  rcases m with _ | k
  · simp
  · have : 1 ≤ (k + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    calc
      k + 1 = (k + 1) * 1 := (Nat.mul_one (k + 1)).symm
      _ ≤ (k + 1) * (k + 1) ^ 2 := Nat.mul_le_mul_left (k + 1) this
      _ = (k + 1) ^ 3 := by ring

/-- Triangle detection saving factor $f_{c,k}(M) := 2^{\lfloor \sqrt{\log_2 M} / D_{\text{tri}}(c,k) \rfloor}$
(`paper.tex` Lemma 6.1 `\label{lem:bmm-to-tridet}` & §6). -/
def triDetSavingFactor (c k M : ℕ) : ℕ :=
  2 ^ (Nat.sqrt (Nat.log 2 M) / D_tri c k)

lemma one_le_triDetSavingFactor (c k M : ℕ) : 1 ≤ triDetSavingFactor c k M :=
  Nat.one_le_pow _ _ (by norm_num)

lemma triDetSavingFactor_le_self (c k : ℕ) {M : ℕ} (hM : 1 ≤ M) :
    triDetSavingFactor c k M ≤ M := by
  unfold triDetSavingFactor
  have h1 : Nat.sqrt (Nat.log 2 M) / D_tri c k ≤ Nat.sqrt (Nat.log 2 M) :=
    Nat.div_le_self _ _
  have h2 : Nat.sqrt (Nat.log 2 M) ≤ Nat.log 2 M :=
    Nat.sqrt_le_self (Nat.log 2 M)
  calc
    2 ^ (Nat.sqrt (Nat.log 2 M) / D_tri c k)
      ≤ 2 ^ (Nat.log 2 M) := Nat.pow_le_pow_right (by norm_num) (h1.trans h2)
    _ ≤ M := Nat.pow_log_le_self 2 (by omega)

/-- Block size $m := \max(1, \lfloor n^{1/4} \rfloor) = \max(1, \lfloor \sqrt{\lfloor \sqrt{n} \rfloor} \rfloor)$
for Lemma 6.1 (`\label{lem:bmm-to-tridet}`, `paper.tex` §6). -/
def blockSizeBMM (n : ℕ) : ℕ :=
  max 1 (Nat.sqrt (Nat.sqrt n))

lemma one_le_blockSizeBMM (n : ℕ) : 1 ≤ blockSizeBMM n :=
  le_max_left 1 _

lemma blockSizeBMM_eq_sqrt_sqrt {n : ℕ} (hn : 1 ≤ n) :
    blockSizeBMM n = Nat.sqrt (Nat.sqrt n) := by
  unfold blockSizeBMM
  apply max_eq_right
  have h1 : 1 * 1 ≤ n := by omega
  have h2 : 1 ≤ Nat.sqrt n := (Nat.le_sqrt).mpr h1
  have h3 : 1 * 1 ≤ Nat.sqrt n := by omega
  exact (Nat.le_sqrt).mpr h3

lemma blockSizeBMM_pow_four_le {n : ℕ} (hn : 1 ≤ n) :
    (blockSizeBMM n) ^ 4 ≤ n := by
  rw [blockSizeBMM_eq_sqrt_sqrt hn]
  set s := Nat.sqrt (Nat.sqrt n)
  have hs2 : s * s ≤ Nat.sqrt n := Nat.sqrt_le (Nat.sqrt n)
  have hs4 : (s * s) * (s * s) ≤ Nat.sqrt n * Nat.sqrt n := Nat.mul_le_mul hs2 hs2
  have hsqrt_n : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
  have hpow4 : s ^ 4 = (s * s) * (s * s) := by ring
  rw [hpow4]
  exact hs4.trans hsqrt_n

lemma blockSizeBMM_le_self {n : ℕ} (hn : 1 ≤ n) :
    blockSizeBMM n ≤ n := by
  rw [blockSizeBMM_eq_sqrt_sqrt hn]
  exact (Nat.sqrt_le_self _).trans (Nat.sqrt_le_self n)

lemma blockSizeBMM_cube_mul_saving_le (c k : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    (blockSizeBMM n) ^ 3 * triDetSavingFactor c k (blockSizeBMM n) ≤ n := by
  have hm1 : 1 ≤ blockSizeBMM n := one_le_blockSizeBMM n
  have hf_le : triDetSavingFactor c k (blockSizeBMM n) ≤ blockSizeBMM n :=
    triDetSavingFactor_le_self c k hm1
  have hpow4 : (blockSizeBMM n) ^ 3 * blockSizeBMM n = (blockSizeBMM n) ^ 4 := by ring
  calc
    (blockSizeBMM n) ^ 3 * triDetSavingFactor c k (blockSizeBMM n)
      ≤ (blockSizeBMM n) ^ 3 * blockSizeBMM n := Nat.mul_le_mul_left _ hf_le
    _ = (blockSizeBMM n) ^ 4 := hpow4
    _ ≤ n := blockSizeBMM_pow_four_le hn

/-- Tracked evaluation of `blockSizeBMM n = max 1 (Nat.sqrt (Nat.sqrt n))` in `CostM`
(`paper.tex` Lemma 6.1 `\label{lem:bmm-to-tridet}`, §6). -/
def blockSizeBMMTracked (n : ℕ) : CostM ℕ :=
  CostM.bind (sqrtNatTracked n) (fun s1 =>
    CostM.bind (sqrtNatTracked s1) (fun s2 =>
      CostM.bind (cmpLeNatTracked 1 s2) (fun b =>
        if b then retTracked s2 else retTracked 1)))

@[simp]
lemma blockSizeBMMTracked_fst (n : ℕ) :
    (blockSizeBMMTracked n).1 = blockSizeBMM n := by
  unfold blockSizeBMMTracked blockSizeBMM cmpLeNatTracked retTracked
  dsimp only [CostM.bind_fst, sqrtNatTracked_fst]
  split_ifs with h
  · have hle : 1 ≤ n.sqrt.sqrt := of_decide_eq_true h; dsimp; omega
  · have hge : ¬ 1 ≤ n.sqrt.sqrt := by simpa using h
    dsimp; omega

lemma blockSizeBMMTracked_snd_le {n : ℕ} (hn : 1 ≤ n) :
    (blockSizeBMMTracked n).2 ≤ 24 * n ^ 2 := by
  unfold blockSizeBMMTracked sqrtNatTracked cmpLeNatTracked
  dsimp only [CostM.bind_snd, CostM.bind_fst]
  have hite : ∀ (b : Bool) (x y : ℕ), (if b then retTracked x else retTracked y).2 = 1 := by
    intro b x y; cases b <;> rfl
  rw [hite]
  set s1 := Nat.sqrt n
  set s2 := Nat.sqrt s1
  have hs1_le : s1 ≤ n := Nat.sqrt_le_self n
  have hs2_le : s2 ≤ n := (Nat.sqrt_le_self s1).trans hs1_le
  have hbn : bitLengthNat n + 1 ≤ n + 2 := by
    have := bitLengthNat_le_succ n; omega
  have hbs1 : bitLengthNat s1 + 1 ≤ n + 2 := by
    have := bitLengthNat_le_succ s1; omega
  have hbs2 : bitLengthNat s2 ≤ n + 1 := (bitLengthNat_le_succ s2).trans (by omega)
  have hb1 : bitLengthNat 1 = 1 := by decide
  have hmul1 : (bitLengthNat n + 1) * (bitLengthNat n + 1) ≤ (n + 2) * (n + 2) :=
    Nat.mul_le_mul hbn hbn
  have hmul2 : (bitLengthNat s1 + 1) * (bitLengthNat s1 + 1) ≤ (n + 2) * (n + 2) :=
    Nat.mul_le_mul hbs1 hbs1
  nlinarith

/-- Every index $x < n$ belongs to block $a = x / m < \text{numBlocksBMM } n\ m$ when $m \ge 1$. -/
lemma div_lt_numBlocksBMM {n m : ℕ} (hm : 1 ≤ m) (x : Fin n) :
    x.val / m < numBlocksBMM n m := by
  unfold numBlocksBMM
  have hx_lt : x.val < n := x.isLt
  have hx_le : x.val ≤ n - 1 := Nat.le_sub_one_of_lt hx_lt
  have h_div_le : x.val / m ≤ (n - 1) / m := Nat.div_le_div_right hx_le
  have h_eq : n + m - 1 = (n - 1) + m := by omega
  rw [h_eq, Nat.add_div_right (n - 1) hm]
  omega

/-- Restrict an $n \times n$ boolean matrix $M$ to an $m \times m$ block submatrix on
$I_a \times I_b$ (zero-padded if $a \cdot m + i \ge n$ or $b \cdot m + j \ge n$,
`paper.tex` §6). -/
def extractBlockMat (n m a b : ℕ) (M : Fin n → Fin n → Bool) (i j : Fin m) : Bool :=
  if h : a * m + i.val < n ∧ b * m + j.val < n then
    M ⟨a * m + i.val, h.1⟩ ⟨b * m + j.val, h.2⟩
  else
    false

/-- Clear a single entry $(x_0, z_0)$ of $C$ to `false` ($C(x_0, z_0) \leftarrow 0$,
`paper.tex` §6). -/
def clearMatEntry {n : ℕ} (C : Fin n → Fin n → Bool) (x₀ z₀ : Fin n)
    (x z : Fin n) : Bool :=
  if x = x₀ ∧ z = z₀ then false else C x z

lemma clearMatEntry_eq_false_iff {n : ℕ} (C : Fin n → Fin n → Bool) (x₀ z₀ x z : Fin n) :
    clearMatEntry C x₀ z₀ x z = false ↔ (x = x₀ ∧ z = z₀) ∨ C x z = false := by
  unfold clearMatEntry
  split_ifs with h
  · simp [h]
  · simp [h]

/-- Reformulation of `bmatNnz X Y M` as the cardinality of the filter of `true` entries on
`X ×ˢ Y`. -/
lemma bmatNnz_eq_card_filter {α β : Type*} (X : Finset α) (Y : Finset β) (M : α → β → Bool) :
    bmatNnz X Y M = ((X ×ˢ Y).filter (fun xy => M xy.1 xy.2)).card := by
  unfold bmatNnz
  rw [← Finset.sum_product', Finset.card_filter]

/-- Upper bound on the number of non-zero (`true`) entries of an $n \times n$ boolean matrix:
$\operatorname{nnz}(C) \le n^2$. -/
lemma bmatNnz_univ_le_sq (n : ℕ) (C : Fin n → Fin n → Bool) :
    bmatNnz Finset.univ Finset.univ C ≤ n * n := by
  rw [bmatNnz_eq_card_filter]
  calc
    ((Finset.univ ×ˢ Finset.univ).filter (fun xy : Fin n × Fin n => C xy.1 xy.2)).card
      ≤ (Finset.univ ×ˢ Finset.univ : Finset (Fin n × Fin n)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = n * n := by simp

/-- ** Global Amortization Invariant (`nnz_C_strictly_decreases_on_triangle`,
`paper.tex` §6)**:
Whenever $C(x_0, z_0) = \text{true}$ and the algorithm clears $C(x_0, z_0) \leftarrow \text{false}$,
the number of ones $\operatorname{nnz}(C)$ strictly decreases by exactly $1$:
$$\operatorname{nnz}(\text{clearMatEntry } C\ x_0\ z_0) + 1 = \operatorname{nnz}(C).$$ -/
theorem nnz_C_strictly_decreases_on_triangle {n : ℕ} (C : Fin n → Fin n → Bool)
    (x₀ z₀ : Fin n) (hC : C x₀ z₀ = true) :
    bmatNnz Finset.univ Finset.univ (clearMatEntry C x₀ z₀) + 1 =
      bmatNnz Finset.univ Finset.univ C := by
  rw [bmatNnz_eq_card_filter, bmatNnz_eq_card_filter]
  have h_mem : (x₀, z₀) ∈ (Finset.univ ×ˢ Finset.univ).filter (fun xy : Fin n × Fin n => C xy.1 xy.2) := by
    simp [hC]
  have h_erase :
      (Finset.univ ×ˢ Finset.univ).filter (fun xy : Fin n × Fin n => clearMatEntry C x₀ z₀ xy.1 xy.2) =
        ((Finset.univ ×ˢ Finset.univ).filter (fun xy : Fin n × Fin n => C xy.1 xy.2)).erase (x₀, z₀) := by
    ext ⟨x, z⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_erase, clearMatEntry]
    split_ifs with h
    · simp [h]
    · simp [h]
  rw [h_erase]
  exact Finset.card_erase_add_one h_mem

/-- Predicate testing whether $(x, z) \in [n]^2$ is a valid triangle witness in block triple
$(a, b, c)$, i.e., $x \in I_a$, $z \in I_c$, and there exists $y \in I_b$ with
$A_{a,b}(i, j) = B_{b,c}(j, k) = C_{a,c}(i, k) = \text{true}$ (`paper.tex` §6). -/
def isBlockTrianglePair (n m a b c : ℕ) (A B C : Fin n → Fin n → Bool)
    (xz : Fin n × Fin n) : Bool :=
  decide (∃ i j k : Fin m,
    xz.1.val = a * m + i.val ∧
    xz.2.val = c * m + k.val ∧
    extractBlockMat n m a b A i j = true ∧
    extractBlockMat n m b c B j k = true ∧
    extractBlockMat n m a c C i k = true)

/-- List of all $m^3$ local block index triples $(i, j, k) \in \text{Fin } m \times \text{Fin } m \times \text{Fin } m$
for the exhaustive $O(m^3)$ subblock triangle witness scan in Lemma 6.1 (`paper.tex` §6). -/
def blockSubTriplesList (m : ℕ) : List (Fin m × Fin m × Fin m) :=
  (List.finRange m).flatMap (fun i =>
    (List.finRange m).flatMap (fun j =>
      (List.finRange m).map (fun k => (i, j, k))))

lemma mem_blockSubTriplesList {m : ℕ} (ijk : Fin m × Fin m × Fin m) :
    ijk ∈ blockSubTriplesList m := by
  rcases ijk with ⟨i, j, k⟩
  simp [blockSubTriplesList, List.mem_flatMap, List.mem_map, List.mem_finRange]

lemma length_blockSubTriplesList (m : ℕ) :
    (blockSubTriplesList m).length = m * m * m := by
  unfold blockSubTriplesList
  have h1 : ∀ i : Fin m,
      ((List.finRange m).flatMap (fun j => (List.finRange m).map (fun k => (i, j, k)))).length =
        m * m := by
    intro i
    rw [List.length_flatMap]
    simp [List.map_const', List.sum_replicate, List.length_finRange]
  rw [List.length_flatMap]
  simp [h1, List.map_const', List.sum_replicate, List.length_finRange, Nat.mul_assoc]

/-- Check whether local subblock indices $(i, j, k) \in (\text{Fin } m)^3$ form a triangle in
$(A_{a,b}, B_{b,c}, C_{a,c})$, and if so, return the global matrix coordinates
$(x, z) = (a \cdot m + i, c \cdot m + k) \in \text{Fin } n \times \text{Fin } n$
(`paper.tex` §6). -/
def checkBlockSubTriple (n m a b c : ℕ) (A B C : Fin n → Fin n → Bool)
    (ijk : Fin m × Fin m × Fin m) : Option (Fin n × Fin n) :=
  let i := ijk.1
  let j := ijk.2.1
  let k := ijk.2.2
  if h : a * m + i.val < n ∧ c * m + k.val < n ∧
      extractBlockMat n m a b A i j = true ∧
      extractBlockMat n m b c B j k = true ∧
      extractBlockMat n m a c C i k = true then
    some (⟨a * m + i.val, h.1⟩, ⟨c * m + k.val, h.2.1⟩)
  else
    none

/-- Exhaustive $O(m^3)$ subblock scan finding a triangle witness $(x, z) \in I_a \times I_c$ when
$\mathcal{A}(A_{a,b}, B_{b,c}, C_{a,c})$ reports a triangle (`paper.tex` §6). -/
def findBlockTriangle (n m a b c : ℕ) (A B C : Fin n → Fin n → Bool) :
    Option (Fin n × Fin n) :=
  (blockSubTriplesList m).findSome? (checkBlockSubTriple n m a b c A B C)

/-- Tracked exhaustive $O(m^3)$ subblock scan in `CostM` via `findSomeListByTracked` over
`blockSubTriplesList m` (`paper.tex` §6). -/
def findBlockTriangleTracked (n m a b c : ℕ) (A B C : Fin n → Fin n → Bool) :
    CostM (Option (Fin n × Fin n)) :=
  findSomeListByTracked (checkBlockSubTriple n m a b c A B C) (blockSubTriplesList m)

@[simp]
lemma findBlockTriangleTracked_fst (n m a b c : ℕ) (A B C : Fin n → Fin n → Bool) :
    (findBlockTriangleTracked n m a b c A B C).1 = findBlockTriangle n m a b c A B C := by
  unfold findBlockTriangleTracked findBlockTriangle
  rw [findSomeListByTracked_fst]

lemma findBlockTriangleTracked_snd_le (n m a b c : ℕ) (A B C : Fin n → Fin n → Bool) :
    (findBlockTriangleTracked n m a b c A B C).2 ≤ m * m * m + 1 := by
  unfold findBlockTriangleTracked
  have h := findSomeListByTracked_snd_le
    (checkBlockSubTriple n m a b c A B C) (blockSubTriplesList m)
  rwa [length_blockSubTriplesList] at h

/-- Soundness of `isBlockTrianglePair`: any pair $(x, z)$ satisfying `isBlockTrianglePair` has
$C(x, z) = \text{true}$ and $(A \star B)(x, z) = \text{true}$. -/
lemma isBlockTrianglePair_sound {n m a b c : ℕ} {A B C : Fin n → Fin n → Bool}
    {xz : Fin n × Fin n} (h : isBlockTrianglePair n m a b c A B C xz = true) :
    C xz.1 xz.2 = true ∧ boolMatMul n A B xz.1 xz.2 = true := by
  unfold isBlockTrianglePair at h
  rcases of_decide_eq_true h with ⟨i, j, k, hx_eq, hz_eq, hA, hB, hC⟩
  unfold extractBlockMat at hA hB hC
  split_ifs at hC with h_ac
  split_ifs at hA with h_ab
  split_ifs at hB with h_bc
  have hx_fin : (⟨a * m + i.val, h_ac.1⟩ : Fin n) = xz.1 := Fin.ext hx_eq.symm
  have hz_fin : (⟨c * m + k.val, h_ac.2⟩ : Fin n) = xz.2 := Fin.ext hz_eq.symm
  rw [hx_fin, hz_fin] at hC
  rw [hx_fin] at hA
  rw [hz_fin] at hB
  refine ⟨hC, (boolMatMul_eq_true_iff n A B xz.1 xz.2).mpr ⟨⟨b * m + j.val, h_ab.2⟩, hA, hB⟩⟩

lemma checkBlockSubTriple_some_sound {n m a b c : ℕ} {A B C : Fin n → Fin n → Bool}
    {ijk : Fin m × Fin m × Fin m} {xz : Fin n × Fin n}
    (h : checkBlockSubTriple n m a b c A B C ijk = some xz) :
    C xz.1 xz.2 = true ∧ boolMatMul n A B xz.1 xz.2 = true := by
  unfold checkBlockSubTriple at h
  dsimp only at h
  split_ifs at h with hcond
  injection h with hxz
  rcases hcond with ⟨ha, hc, hA, hB, hC⟩
  have hx_eq : xz.1 = ⟨a * m + ijk.1.val, ha⟩ := by rw [← hxz]
  have hz_eq : xz.2 = ⟨c * m + ijk.2.2.val, hc⟩ := by rw [← hxz]
  have h_pair : isBlockTrianglePair n m a b c A B C xz = true := by
    unfold isBlockTrianglePair
    exact decide_eq_true ⟨ijk.1, ijk.2.1, ijk.2.2,
      by rw [hx_eq], by rw [hz_eq], hA, hB, hC⟩
  exact isBlockTrianglePair_sound h_pair

private lemma exists_of_findSome?_eq_some {α β : Type*} {xs : List α} {f : α → Option β} {y : β}
    (h : xs.findSome? f = some y) : ∃ x ∈ xs, f x = some y := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.findSome?_cons] at h
    cases hfx : f x with
    | some val =>
      rw [hfx] at h
      dsimp only at h
      exact ⟨x, List.mem_cons_self, by rw [hfx, h]⟩
    | none =>
      rw [hfx] at h
      rcases ih h with ⟨x', hx', hfx'⟩
      exact ⟨x', List.mem_cons_of_mem x hx', hfx'⟩

private lemma isSome_findSome?_of_mem {α β : Type*} {xs : List α} {f : α → Option β} {x : α}
    (hx : x ∈ xs) (hfx : (f x).isSome = true) : (xs.findSome? f).isSome = true := by
  induction xs with
  | nil => nomatch hx
  | cons a xs ih =>
    simp only [List.findSome?_cons]
    rcases List.mem_cons.mp hx with rfl | htail
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hfx
      rw [hv]; rfl
    · cases hfa : f a with
      | some v => rfl
      | none => exact ih htail

/-- Completeness of `findBlockTriangle`: whenever `hasTriangle m A_{a,b} B_{b,c} C_{a,c} = true`,
`findBlockTriangle` returns `some xz` with `C xz.1 xz.2 = true` and `boolMatMul n A B xz.1 xz.2 = true`. -/
lemma findBlockTriangle_some_of_hasTriangle {n m a b c : ℕ} {A B C : Fin n → Fin n → Bool}
    (h_tri : hasTriangle m (extractBlockMat n m a b A) (extractBlockMat n m b c B)
      (extractBlockMat n m a c C) = true) :
    ∃ xz : Fin n × Fin n,
      findBlockTriangle n m a b c A B C = some xz ∧
      C xz.1 xz.2 = true ∧
      boolMatMul n A B xz.1 xz.2 = true := by
  rcases (hasTriangle_eq_true_iff m _ _ _).mp h_tri with ⟨i, j, k, hA, hB, hC⟩
  have h_ac : a * m + i.val < n ∧ c * m + k.val < n := by
    unfold extractBlockMat at hC
    split_ifs at hC with h_cond
    exact h_cond
  have h_cond : a * m + i.val < n ∧ c * m + k.val < n ∧
      extractBlockMat n m a b A i j = true ∧
      extractBlockMat n m b c B j k = true ∧
      extractBlockMat n m a c C i k = true :=
    ⟨h_ac.1, h_ac.2, hA, hB, hC⟩
  have h_chk : (checkBlockSubTriple n m a b c A B C (i, j, k)).isSome = true := by
    unfold checkBlockSubTriple
    dsimp only
    rw [dif_pos h_cond]
    rfl
  have h_isSome : (findBlockTriangle n m a b c A B C).isSome = true :=
    isSome_findSome?_of_mem (mem_blockSubTriplesList (i, j, k)) h_chk
  obtain ⟨xz, h_eq⟩ := Option.isSome_iff_exists.mp h_isSome
  obtain ⟨ijk, _, h_ijk⟩ := exists_of_findSome?_eq_some h_eq
  obtain ⟨hC_xz, hBMM_xz⟩ := checkBlockSubTriple_some_sound h_ijk
  exact ⟨xz, h_eq, hC_xz, hBMM_xz⟩

/-- Untracked while-loop on block triple $(a, b, c)$ with fuel `fuel`
(`paper.tex` §6). -/
def processBlockTripleLoop (n m a b c : ℕ)
    (triDet : (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → Bool)
    (A B : Fin n → Fin n → Bool) :
    ℕ → (Fin n → Fin n → Bool) → (Fin n → Fin n → Bool)
  | 0, C => C
  | fuel + 1, C =>
    let A_ab := extractBlockMat n m a b A
    let B_bc := extractBlockMat n m b c B
    let C_ac := extractBlockMat n m a c C
    if triDet A_ab B_bc C_ac then
      match findBlockTriangle n m a b c A B C with
      | some xz => processBlockTripleLoop n m a b c triDet A B fuel (clearMatEntry C xz.1 xz.2)
      | none => C
    else
      C

/-- Bottom-up cost-tracked while-loop on block triple $(a, b, c)$ in `CostM`
(`processBlockTripleLoopTracked`, `paper.tex` §6). -/
def processBlockTripleLoopTracked (n m a b c : ℕ)
    (triDetTracked :
      (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → CostM Bool)
    (A B : Fin n → Fin n → Bool) :
    ℕ → (Fin n → Fin n → Bool) → CostM (Fin n → Fin n → Bool)
  | 0, C => retTracked C
  | fuel + 1, C =>
    let A_ab := extractBlockMat n m a b A
    let B_bc := extractBlockMat n m b c B
    let C_ac := extractBlockMat n m a c C
    CostM.bind (scanBlockExtractTracked m ()) (fun _ =>
      CostM.bind (triDetTracked A_ab B_bc C_ac) (fun hasTri =>
        if hasTri then
          CostM.bind (findBlockTriangleTracked n m a b c A B C) (fun scanOpt =>
            match scanOpt with
            | some xz =>
              CostM.bind (retTracked (clearMatEntry C xz.1 xz.2)) (fun C_next =>
                processBlockTripleLoopTracked n m a b c triDetTracked A B fuel C_next)
            | none =>
              retTracked C)
        else
          retTracked C))

/-- Projection equivalence `processBlockTripleLoopTracked_fst`. -/
@[simp]
theorem processBlockTripleLoopTracked_fst (n m a b c : ℕ)
    (triDet : (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → Bool)
    (triDetTracked :
      (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → CostM Bool)
    (h_fst : ∀ A' B' C', (triDetTracked A' B' C').1 = triDet A' B' C')
    (A B : Fin n → Fin n → Bool) (fuel : ℕ) (C : Fin n → Fin n → Bool) :
    (processBlockTripleLoopTracked n m a b c triDetTracked A B fuel C).1 =
      processBlockTripleLoop n m a b c triDet A B fuel C := by
  induction fuel generalizing C with
  | zero => rfl
  | succ fuel ih =>
    unfold processBlockTripleLoopTracked processBlockTripleLoop
    simp only [CostM.bind_fst, h_fst]
    split_ifs with h_td
    · rw [CostM.bind_fst, findBlockTriangleTracked_fst]
      cases findBlockTriangle n m a b c A B C with
      | none => rfl
      | some xz =>
        rw [CostM.bind_fst, retTracked_fst]
        exact ih (clearMatEntry C xz.1 xz.2)
    · rfl

/-- Soundness and completeness of `processBlockTripleLoop` on block triple $(a, b, c)$:
1. Entries that were `false` in `C` remain `false` in `C'`.
2. Any entry flipped to `false` in `C'` satisfies `boolMatMul n A B x z = true`.
3. When `bmatNnz Finset.univ Finset.univ C ≤ fuel`, `C'` has no remaining triangles in block
   triple $(a, b, c)$. -/
theorem processBlockTripleLoop_spec {n m a b c : ℕ}
    {triDet : (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → Bool}
    (h_corr : ∀ A' B' C', triDet A' B' C' = hasTriangle m A' B' C')
    (A B : Fin n → Fin n → Bool) (fuel : ℕ) (C : Fin n → Fin n → Bool) :
    let C' := processBlockTripleLoop n m a b c triDet A B fuel C
    (∀ x z, C x z = false → C' x z = false) ∧
    (∀ x z, C' x z = false → C x z = false ∨ boolMatMul n A B x z = true) ∧
    (bmatNnz Finset.univ Finset.univ C ≤ fuel →
      hasTriangle m (extractBlockMat n m a b A) (extractBlockMat n m b c B)
        (extractBlockMat n m a c C') = false) := by
  induction fuel generalizing C with
  | zero =>
    dsimp only [processBlockTripleLoop]
    refine ⟨fun _ _ h => h, fun _ _ h => Or.inl h, fun h_nnz => ?_⟩
    have h_zero : bmatNnz Finset.univ Finset.univ C = 0 := Nat.eq_zero_of_le_zero h_nnz
    rw [Bool.eq_false_iff]
    intro h_tri
    obtain ⟨xz, _, hC_xz, _⟩ := findBlockTriangle_some_of_hasTriangle h_tri
    have h_mem : xz ∈ (Finset.univ ×ˢ Finset.univ).filter (fun p : Fin n × Fin n => C p.1 p.2) := by
      simp [hC_xz]
    have h_pos : 0 < bmatNnz Finset.univ Finset.univ C := by
      rw [bmatNnz_eq_card_filter]
      exact Finset.card_pos.mpr ⟨xz, h_mem⟩
    omega
  | succ fuel ih =>
    unfold processBlockTripleLoop
    dsimp only
    split_ifs with h_td
    · have h_tri : hasTriangle m (extractBlockMat n m a b A) (extractBlockMat n m b c B)
          (extractBlockMat n m a c C) = true := by rwa [← h_corr]
      obtain ⟨xz, h_find, hC_xz, hBMM_xz⟩ := findBlockTriangle_some_of_hasTriangle h_tri
      rw [h_find]
      dsimp only
      have h_dec := nnz_C_strictly_decreases_on_triangle C xz.1 xz.2 hC_xz
      obtain ⟨ih1, ih2, ih3⟩ := ih (clearMatEntry C xz.1 xz.2)
      refine ⟨?_, ?_, ?_⟩
      · intro x z hC_false
        apply ih1
        rw [clearMatEntry_eq_false_iff]
        exact Or.inr hC_false
      · intro x z hC'_false
        rcases ih2 x z hC'_false with h_clear | h_bmm
        · rcases (clearMatEntry_eq_false_iff C xz.1 xz.2 x z).mp h_clear with ⟨rfl, rfl⟩ | hC0
          · exact Or.inr hBMM_xz
          · exact Or.inl hC0
        · exact Or.inr h_bmm
      · intro h_nnz
        apply ih3
        omega
    · rw [Bool.not_eq_true] at h_td
      rw [h_corr] at h_td
      exact ⟨fun _ _ h => h, fun _ _ h => Or.inl h, fun _ => h_td⟩

/-- Amortized cost bound for `processBlockTripleLoopTracked` on a single block triple $(a, b, c)$
(`paper.tex` §6):
Let $C' = (\text{processBlockTripleLoopTracked } \dots C).1$. Then $\operatorname{nnz}(C') \le \operatorname{nnz}(C)$
and the work is bounded by one `"no triangle"` call plus $(\operatorname{nnz}(C) - \operatorname{nnz}(C'))$
`"triangle"` calls and $O(m^3)$ scans:
$$\text{cost} \le (3 m^2 + T_{\text{tri}} + 3) +
  (\operatorname{nnz}(C) - \operatorname{nnz}(C')) \cdot (3 m^2 + T_{\text{tri}} + m^3 + 4).$$ -/
theorem processBlockTripleLoopTracked_cost_bound {n m a b c T_tri : ℕ}
    {triDetTracked :
      (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → CostM Bool}
    (h_corr : ∀ A' B' C', (triDetTracked A' B' C').1 = hasTriangle m A' B' C')
    (h_cost : ∀ A' B' C', (triDetTracked A' B' C').2 ≤ T_tri)
    (A B : Fin n → Fin n → Bool) (fuel : ℕ) (C : Fin n → Fin n → Bool) :
    let res := processBlockTripleLoopTracked n m a b c triDetTracked A B fuel C
    bmatNnz Finset.univ Finset.univ res.1 ≤ bmatNnz Finset.univ Finset.univ C ∧
    res.2 ≤ (3 * m * m + T_tri + 3) +
      (bmatNnz Finset.univ Finset.univ C - bmatNnz Finset.univ Finset.univ res.1) *
        (3 * m * m + T_tri + m * m * m + 4) := by
  induction fuel generalizing C with
  | zero =>
    unfold processBlockTripleLoopTracked
    simp only [retTracked_fst, retTracked_snd]
    refine ⟨le_rfl, ?_⟩
    omega
  | succ fuel ih =>
    unfold processBlockTripleLoopTracked
    simp only [CostM.bind_fst, CostM.bind_snd, scanBlockExtractTracked_snd]
    have h_td_cost :
        (triDetTracked (extractBlockMat n m a b A) (extractBlockMat n m b c B)
          (extractBlockMat n m a c C)).2 ≤ T_tri := h_cost _ _ _
    split_ifs with h_td
    · have h_tri : hasTriangle m (extractBlockMat n m a b A) (extractBlockMat n m b c B)
          (extractBlockMat n m a c C) = true := by rwa [← h_corr]
      obtain ⟨xz, h_find, hC_xz, _⟩ := findBlockTriangle_some_of_hasTriangle h_tri
      have h_scan_cost : (findBlockTriangleTracked n m a b c A B C).2 ≤ m * m * m + 1 :=
        findBlockTriangleTracked_snd_le n m a b c A B C
      simp only [CostM.bind_fst, CostM.bind_snd, findBlockTriangleTracked_fst, h_find,
        retTracked_fst, retTracked_snd]
      have h_dec := nnz_C_strictly_decreases_on_triangle C xz.1 xz.2 hC_xz
      obtain ⟨h_nnz_le, h_rest_cost⟩ := ih (clearMatEntry C xz.1 xz.2)
      refine ⟨by omega, ?_⟩
      have h_diff :
          bmatNnz Finset.univ Finset.univ C -
            bmatNnz Finset.univ Finset.univ
              (processBlockTripleLoopTracked n m a b c triDetTracked A B fuel
                (clearMatEntry C xz.1 xz.2)).1 =
          (bmatNnz Finset.univ Finset.univ (clearMatEntry C xz.1 xz.2) -
            bmatNnz Finset.univ Finset.univ
              (processBlockTripleLoopTracked n m a b c triDetTracked A B fuel
                (clearMatEntry C xz.1 xz.2)).1) + 1 := by omega
      rw [h_diff]
      linarith
    · simp only [retTracked_fst, retTracked_snd]
      refine ⟨le_rfl, ?_⟩
      omega

/-- List of all $q^3$ block triples $(a, b, c) \in \{0, \dots, q-1\}^3$ (`paper.tex` §6). -/
def blockTriplesList (q : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range q).flatMap (fun a =>
    (List.range q).flatMap (fun b =>
      (List.range q).map (fun c => (a, b, c))))

lemma mem_blockTriplesList {q a b c : ℕ} (ha : a < q) (hb : b < q) (hc : c < q) :
    (a, b, c) ∈ blockTriplesList q := by
  simp [blockTriplesList, List.mem_flatMap, List.mem_map, List.mem_range, ha, hb, hc]

lemma length_blockTriplesList (q : ℕ) :
    (blockTriplesList q).length = q * q * q := by
  unfold blockTriplesList
  have h1 : ∀ a : ℕ,
      ((List.range q).flatMap (fun b => (List.range q).map (fun c => (a, b, c)))).length =
        q * q := by
    intro a
    rw [List.length_flatMap]
    simp [List.map_const', List.sum_replicate, List.length_range]
  rw [List.length_flatMap]
  simp [h1, List.map_const', List.sum_replicate, List.length_range, Nat.mul_assoc]

/-- Untracked fold of `processBlockTripleLoop` over a list of block triples `triples`. -/
def foldBlockTriples (n m : ℕ)
    (triDet : (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → Bool)
    (A B : Fin n → Fin n → Bool) (triples : List (ℕ × ℕ × ℕ))
    (C : Fin n → Fin n → Bool) : (Fin n → Fin n → Bool) :=
  triples.foldl
    (fun acc abc => processBlockTripleLoop n m abc.1 abc.2.1 abc.2.2 triDet A B (n * n) acc)
    C

/-- Tracked fold of `processBlockTripleLoopTracked` over a list of block triples `triples`
in `CostM`. -/
def foldBlockTriplesTracked (n m : ℕ)
    (triDetTracked :
      (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → CostM Bool)
    (A B : Fin n → Fin n → Bool) (triples : List (ℕ × ℕ × ℕ))
    (C : Fin n → Fin n → Bool) : CostM (Fin n → Fin n → Bool) :=
  foldlListTracked
    (fun acc abc =>
      processBlockTripleLoopTracked n m abc.1 abc.2.1 abc.2.2 triDetTracked A B (n * n) acc)
    C triples

@[simp]
theorem foldBlockTriplesTracked_fst (n m : ℕ)
    (triDet : (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → Bool)
    (triDetTracked :
      (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → CostM Bool)
    (h_fst : ∀ A' B' C', (triDetTracked A' B' C').1 = triDet A' B' C')
    (A B : Fin n → Fin n → Bool) (triples : List (ℕ × ℕ × ℕ))
    (C : Fin n → Fin n → Bool) :
    (foldBlockTriplesTracked n m triDetTracked A B triples C).1 =
      foldBlockTriples n m triDet A B triples C := by
  unfold foldBlockTriplesTracked foldBlockTriples
  rw [foldlListTracked_fst]
  congr 1
  funext acc abc
  exact processBlockTripleLoopTracked_fst n m abc.1 abc.2.1 abc.2.2 triDet triDetTracked h_fst A B
    (n * n) acc

/-- If a matrix `C'` is obtained from `C` by clearing some `true` entries to `false`
(`∀ x z, C x z = false → C' x z = false`), and `hasTriangle m A_ab B_bc C_ac = false`, then
`hasTriangle m A_ab B_bc C'_ac = false`. -/
lemma hasTriangle_extractBlockMat_mono_false {n m a b c : ℕ}
    (A B C C' : Fin n → Fin n → Bool)
    (h_mono : ∀ x z, C x z = false → C' x z = false)
    (h_no_tri : hasTriangle m (extractBlockMat n m a b A) (extractBlockMat n m b c B)
      (extractBlockMat n m a c C) = false) :
    hasTriangle m (extractBlockMat n m a b A) (extractBlockMat n m b c B)
      (extractBlockMat n m a c C') = false := by
  rw [Bool.eq_false_iff] at h_no_tri ⊢
  intro h_tri'
  apply h_no_tri
  rcases (hasTriangle_eq_true_iff m _ _ _).mp h_tri' with ⟨i, j, k, hA, hB, hC'⟩
  refine (hasTriangle_eq_true_iff m _ _ _).mpr ⟨i, j, k, hA, hB, ?_⟩
  unfold extractBlockMat at hC' ⊢
  split_ifs at hC' with h_ac
  simp only [h_ac]
  by_contra h_not
  rw [Bool.not_eq_true] at h_not
  have := h_mono _ _ h_not
  rw [this] at hC'
  contradiction

/-- Invariant of `foldBlockTriples` across any list of block triples `triples`:
1. Monotonicity: `C x z = false → C_final x z = false`.
2. Soundness: `C_final x z = false → C x z = false ∨ boolMatMul n A B x z = true`.
3. Completeness: For every `(a, b, c) ∈ triples`, `C_final` has no triangles in block `(a, b, c)`. -/
theorem foldBlockTriples_spec {n m : ℕ}
    {triDet : (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → Bool}
    (h_corr : ∀ A' B' C', triDet A' B' C' = hasTriangle m A' B' C')
    (A B : Fin n → Fin n → Bool) (triples : List (ℕ × ℕ × ℕ)) (C : Fin n → Fin n → Bool) :
    let C_final := foldBlockTriples n m triDet A B triples C
    (∀ x z, C x z = false → C_final x z = false) ∧
    (∀ x z, C_final x z = false → C x z = false ∨ boolMatMul n A B x z = true) ∧
    (∀ abc ∈ triples,
      hasTriangle m (extractBlockMat n m abc.1 abc.2.1 A)
        (extractBlockMat n m abc.2.1 abc.2.2 B)
        (extractBlockMat n m abc.1 abc.2.2 C_final) = false) := by
  induction triples generalizing C with
  | nil =>
    dsimp only [foldBlockTriples, List.foldl_nil]
    exact ⟨fun _ _ h => h, fun _ _ h => Or.inl h, fun _ h => by nomatch h⟩
  | cons abc triples ih =>
    unfold foldBlockTriples
    simp only [List.foldl_cons]
    let C₁ := processBlockTripleLoop n m abc.1 abc.2.1 abc.2.2 triDet A B (n * n) C
    obtain ⟨h1_mono, h1_sound, h1_comp⟩ :=
      processBlockTripleLoop_spec h_corr A B (n * n) C
        (a := abc.1) (b := abc.2.1) (c := abc.2.2)
    have h1_no_tri :
        hasTriangle m (extractBlockMat n m abc.1 abc.2.1 A)
          (extractBlockMat n m abc.2.1 abc.2.2 B)
          (extractBlockMat n m abc.1 abc.2.2 C₁) = false :=
      h1_comp (bmatNnz_univ_le_sq n C)
    obtain ⟨ih_mono, ih_sound, ih_comp⟩ := ih C₁
    refine ⟨fun x z h => ih_mono x z (h1_mono x z h), ?_, ?_⟩
    · intro x z h_final
      rcases ih_sound x z h_final with h_c1 | h_bmm
      · exact h1_sound x z h_c1
      · exact Or.inr h_bmm
    · intro abc' habc'
      rcases List.mem_cons.mp habc' with rfl | h_tail
      · exact hasTriangle_extractBlockMat_mono_false A B C₁ _ ih_mono h1_no_tri
      · exact ih_comp abc' h_tail

/-- General telescoping cost bound for `foldlListTracked` with a non-increasing potential
`Φ : β → ℕ`. -/
lemma foldlListTracked_telescoping_bound {α β : Type*}
    (f : β → α → CostM β) (Φ : β → ℕ) (A_const B_const : ℕ)
    (hf : ∀ b a, Φ (f b a).1 ≤ Φ b ∧
      (f b a).2 ≤ A_const + (Φ b - Φ (f b a).1) * B_const)
    (init : β) (xs : List α) :
    Φ (foldlListTracked f init xs).1 ≤ Φ init ∧
    (foldlListTracked f init xs).2 ≤
      xs.length * (A_const + 1) + (Φ init - Φ (foldlListTracked f init xs).1) * B_const + 1 := by
  induction xs generalizing init with
  | nil =>
    simp [foldlListTracked]
  | cons x xs ih =>
    simp only [foldlListTracked, List.length_cons]
    obtain ⟨h_phi1, h_cost1⟩ := hf init x
    obtain ⟨h_phi2, h_cost2⟩ := ih (f init x).1
    refine ⟨le_trans h_phi2 h_phi1, ?_⟩
    have h_tele :
        Φ init - Φ (foldlListTracked f (f init x).1 xs).1 =
          (Φ init - Φ (f init x).1) +
          (Φ (f init x).1 - Φ (foldlListTracked f (f init x).1 xs).1) := by omega
    rw [h_tele]
    linarith

/-- Telescoping global cost bound for `foldBlockTriplesTracked` across any list of block triples
(`paper.tex` §6):
$$\text{cost} \le |\text{triples}| \cdot (3 m^2 + T_{\text{tri}} + 4) +
  (\operatorname{nnz}(C) - \operatorname{nnz}(C_{\text{final}})) \cdot (3 m^2 + T_{\text{tri}} + m^3 + 4) + 1.$$ -/
theorem foldBlockTriplesTracked_cost_bound {n m T_tri : ℕ}
    {triDetTracked :
      (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → CostM Bool}
    (h_corr : ∀ A' B' C', (triDetTracked A' B' C').1 = hasTriangle m A' B' C')
    (h_cost : ∀ A' B' C', (triDetTracked A' B' C').2 ≤ T_tri)
    (A B : Fin n → Fin n → Bool) (triples : List (ℕ × ℕ × ℕ)) (C : Fin n → Fin n → Bool) :
    let res := foldBlockTriplesTracked n m triDetTracked A B triples C
    bmatNnz Finset.univ Finset.univ res.1 ≤ bmatNnz Finset.univ Finset.univ C ∧
    res.2 ≤ triples.length * (3 * m * m + T_tri + 4) +
      (bmatNnz Finset.univ Finset.univ C - bmatNnz Finset.univ Finset.univ res.1) *
        (3 * m * m + T_tri + m * m * m + 4) + 1 := by
  unfold foldBlockTriplesTracked
  exact foldlListTracked_telescoping_bound
    (fun acc abc =>
      processBlockTripleLoopTracked n m abc.1 abc.2.1 abc.2.2 triDetTracked A B (n * n) acc)
    (bmatNnz Finset.univ Finset.univ)
    (3 * m * m + T_tri + 3)
    (3 * m * m + T_tri + m * m * m + 4)
    (fun acc abc => processBlockTripleLoopTracked_cost_bound h_corr h_cost A B (n * n) acc)
    C triples

/-- **Untracked BMM-to-Triangle-Detection Reduction (`bmmFromTriDet`, Lemma 6.1,
`paper.tex` §6)**:
Given $n \times n$ binary matrices $A, B$, block size $m$, and an $m \times m$ triangle-detection
oracle `triDet`:
1. Initialize $C = \mathbf{1}_{n \times n}$ (`fun _ _ => true`).
2. Iterate `processBlockTripleLoop` over all $q^3$ block triples $(a, b, c) \in [q]^3$ where
   $q = \lceil n / m \rceil = \text{numBlocksBMM } n\ m$.
3. Return $\mathbf{1}_{n \times n} - C_{\text{final}}$ (`fun x z => !C_final x z`). -/
def bmmFromTriDet (n m : ℕ)
    (triDet : (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → Bool)
    (A B : Fin n → Fin n → Bool) : Fin n → Fin n → Bool :=
  let initC : Fin n → Fin n → Bool := fun _ _ => true
  let finalC := foldBlockTriples n m triDet A B (blockTriplesList (numBlocksBMM n m)) initC
  fun x z => !finalC x z

/-- **Bottom-Up Cost-Tracked BMM-to-Triangle-Detection Reduction (`bmmFromTriDetTracked`,
Lemma 6.1, `paper.tex` §6)**. -/
def bmmFromTriDetTracked (n m : ℕ)
    (triDetTracked :
      (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → CostM Bool)
    (A B : Fin n → Fin n → Bool) : CostM (Fin n → Fin n → Bool) :=
  let U : Finset (Fin n) := Finset.univ
  CostM.bind (scanMatrixTracked U U (fun _ _ : Fin n => true)) (fun initC =>
    CostM.bind
      (foldBlockTriplesTracked n m triDetTracked A B
        (blockTriplesList (numBlocksBMM n m)) initC)
      (fun finalC =>
        scanMatrixTracked U U (fun x z => !finalC x z)))

/-- Projection equivalence `bmmFromTriDetTracked_fst`. -/
@[simp]
theorem bmmFromTriDetTracked_fst (n m : ℕ)
    (triDet : (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → Bool)
    (triDetTracked :
      (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → CostM Bool)
    (h_fst : ∀ A' B' C', (triDetTracked A' B' C').1 = triDet A' B' C')
    (A B : Fin n → Fin n → Bool) :
    (bmmFromTriDetTracked n m triDetTracked A B).1 = bmmFromTriDet n m triDet A B := by
  unfold bmmFromTriDetTracked bmmFromTriDet
  simp only [CostM.bind_fst, scanMatrixTracked_fst]
  rw [foldBlockTriplesTracked_fst n m triDet triDetTracked h_fst]

/-- **Lemma 6.1 Correctness (`bmmFromTriDet_correct`, `paper.tex` §6)**:
For any $m \ge 1$ and any correct $m \times m$ triangle-detection oracle `triDet`,
`bmmFromTriDet n m triDet A B = boolMatMul n A B`. -/
theorem bmmFromTriDet_correct {n m : ℕ} (hm : 1 ≤ m)
    {triDet : (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → Bool}
    (h_corr : ∀ A' B' C', triDet A' B' C' = hasTriangle m A' B' C')
    (A B : Fin n → Fin n → Bool) :
    bmmFromTriDet n m triDet A B = boolMatMul n A B := by
  funext x z
  unfold bmmFromTriDet
  let initC : Fin n → Fin n → Bool := fun _ _ => true
  let triples := blockTriplesList (numBlocksBMM n m)
  obtain ⟨_, h_sound, h_comp⟩ := foldBlockTriples_spec h_corr A B triples initC
  apply Bool.eq_iff_iff.mpr
  rw [Bool.not_eq_true']
  constructor
  · intro h_false
    rcases h_sound x z h_false with h_init | h_bmm
    · simp [initC] at h_init
    · exact h_bmm
  · intro h_bmm
    rcases (boolMatMul_eq_true_iff n A B x z).mp h_bmm with ⟨y, hA, hB⟩
    let a := x.val / m
    let b := y.val / m
    let c := z.val / m
    have ha : a < numBlocksBMM n m := div_lt_numBlocksBMM hm x
    have hb : b < numBlocksBMM n m := div_lt_numBlocksBMM hm y
    have hc : c < numBlocksBMM n m := div_lt_numBlocksBMM hm z
    have h_mem : (a, b, c) ∈ triples := mem_blockTriplesList ha hb hc
    have h_no_tri := h_comp (a, b, c) h_mem
    let i : Fin m := ⟨x.val % m, Nat.mod_lt x.val hm⟩
    let j : Fin m := ⟨y.val % m, Nat.mod_lt y.val hm⟩
    let k : Fin m := ⟨z.val % m, Nat.mod_lt z.val hm⟩
    have hx_eq : a * m + i.val = x.val := Nat.div_add_mod' x.val m
    have hy_eq : b * m + j.val = y.val := Nat.div_add_mod' y.val m
    have hz_eq : c * m + k.val = z.val := Nat.div_add_mod' z.val m
    have hA_blk : extractBlockMat n m a b A i j = true := by
      unfold extractBlockMat
      have h_cond : a * m + i.val < n ∧ b * m + j.val < n := by
        rw [hx_eq, hy_eq]; exact ⟨x.isLt, y.isLt⟩
      rw [dif_pos h_cond]
      have hx_fin : (⟨a * m + i.val, h_cond.1⟩ : Fin n) = x := Fin.ext hx_eq
      have hy_fin : (⟨b * m + j.val, h_cond.2⟩ : Fin n) = y := Fin.ext hy_eq
      rw [hx_fin, hy_fin]
      exact hA
    have hB_blk : extractBlockMat n m b c B j k = true := by
      unfold extractBlockMat
      have h_cond : b * m + j.val < n ∧ c * m + k.val < n := by
        rw [hy_eq, hz_eq]; exact ⟨y.isLt, z.isLt⟩
      rw [dif_pos h_cond]
      have hy_fin : (⟨b * m + j.val, h_cond.1⟩ : Fin n) = y := Fin.ext hy_eq
      have hz_fin : (⟨c * m + k.val, h_cond.2⟩ : Fin n) = z := Fin.ext hz_eq
      rw [hy_fin, hz_fin]
      exact hB
    rw [Bool.eq_false_iff]
    intro h_true
    have hC_blk : extractBlockMat n m a c (foldBlockTriples n m triDet A B triples initC) i k = true := by
      unfold extractBlockMat
      have h_cond : a * m + i.val < n ∧ c * m + k.val < n := by
        rw [hx_eq, hz_eq]; exact ⟨x.isLt, z.isLt⟩
      rw [dif_pos h_cond]
      have hx_fin : (⟨a * m + i.val, h_cond.1⟩ : Fin n) = x := Fin.ext hx_eq
      have hz_fin : (⟨c * m + k.val, h_cond.2⟩ : Fin n) = z := Fin.ext hz_eq
      rw [hx_fin, hz_fin]
      exact h_true
    have h_has_tri :
        hasTriangle m (extractBlockMat n m a b A) (extractBlockMat n m b c B)
          (extractBlockMat n m a c (foldBlockTriples n m triDet A B triples initC)) = true :=
      (hasTriangle_eq_true_iff m _ _ _).mpr ⟨i, j, k, hA_blk, hB_blk, hC_blk⟩
    rw [h_has_tri] at h_no_tri
    contradiction

/-- **Lemma 6.1 Runtime Bound (`lem_bmm_to_tridet_time_bound`, `paper.tex` §6)**:
Across the entire execution of `bmmFromTriDetTracked n m triDetTracked A B` with
$q = \text{numBlocksBMM } n\ m$:
- There are at most $q^3$ `"no triangle"` calls to `triDetTracked` (at most one per block triple
  among the $q^3$ block triples).
- Since $\operatorname{nnz}(C_0) \le n^2$ and every `"triangle"` call flips an entry of $C$ from
  `true` to `false` (`nnz_C_strictly_decreases_on_triangle`), there are at most $n^2$ `"triangle"`
  calls and $O(m^3)$ scans across all $q^3$ block triples combined.
- Thus the total work is bounded by
  $$q^3 \cdot (3 m^2 + T_{\text{tri}} + 4) + n^2 \cdot (3 m^2 + T_{\text{tri}} + m^3 + 6) + 3.$$ -/
theorem lem_bmm_to_tridet_time_bound {n m T_tri : ℕ}
    {triDetTracked :
      (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → (Fin m → Fin m → Bool) → CostM Bool}
    (h_corr : ∀ A' B' C', (triDetTracked A' B' C').1 = hasTriangle m A' B' C')
    (h_cost : ∀ A' B' C', (triDetTracked A' B' C').2 ≤ T_tri)
    (A B : Fin n → Fin n → Bool) :
    let q := numBlocksBMM n m
    (bmmFromTriDetTracked n m triDetTracked A B).2 ≤
      (q * q * q) * (3 * m * m + T_tri + 4) +
      (n * n) * (3 * m * m + T_tri + m * m * m + 6) + 3 := by
  dsimp only
  unfold bmmFromTriDetTracked
  simp only [CostM.bind_snd, scanMatrixTracked_snd, scanMatrixTracked_fst,
    Finset.card_univ, Fintype.card_fin]
  have h_fold :=
    (foldBlockTriplesTracked_cost_bound h_corr h_cost A B
      (blockTriplesList (numBlocksBMM n m)) (fun _ _ => true)).2
  rw [length_blockTriplesList] at h_fold
  have h_nnz_init : bmatNnz Finset.univ Finset.univ (fun _ _ : Fin n => true) ≤ n * n :=
    bmatNnz_univ_le_sq n (fun _ _ => true)
  have h_diff_le :
      bmatNnz Finset.univ Finset.univ (fun _ _ : Fin n => true) -
        bmatNnz Finset.univ Finset.univ
          (foldBlockTriplesTracked n m triDetTracked A B
            (blockTriplesList (numBlocksBMM n m)) (fun _ _ => true)).1 ≤
      n * n := by omega
  have h_mul_le :
      (bmatNnz Finset.univ Finset.univ (fun _ _ : Fin n => true) -
        bmatNnz Finset.univ Finset.univ
          (foldBlockTriplesTracked n m triDetTracked A B
            (blockTriplesList (numBlocksBMM n m)) (fun _ _ => true)).1) *
        (3 * m * m + T_tri + m * m * m + 4) ≤
      (n * n) * (3 * m * m + T_tri + m * m * m + 4) :=
    Nat.mul_le_mul_right _ h_diff_le
  linarith

/-!
### Sampler-Conditional End-to-End Combinatorial BMM (`computableBMM` & `thm_main_bmm`,
`paper.tex` Theorem 1.2 & Section 6, §1.2 & Appendix C & §6)
-/

/-- Exponent divisor $D_{\text{bmm}}(c, k) = 2 \cdot D_{\text{tri}}(c, k)$ for the
$2^{\Omega(\sqrt{\log n})}$ saving factor in Theorem 1.2 (`thm_main_bmm`,
`paper.tex` §6). -/
def D_bmm (c k : ℕ) : ℕ := 2 * D_tri c k

lemma D_bmm_pos (c k : ℕ) : 0 < D_bmm c k :=
  Nat.mul_pos (by decide) (D_tri_pos c k)

/-- Explicit uniform constant $C_{\text{bmm}}(c, k) = 9 \cdot C_{\text{tri}}(c, k) + 93$ for
Theorem 1.2 (`thm_main_bmm`, `paper.tex` §6). -/
noncomputable def C_bmm (c k : ℕ) : ℕ := 9 * C_tri c k + 93

lemma C_bmm_pos (c k : ℕ) : 0 < C_bmm c k :=
  Nat.add_pos_right (9 * C_tri c k) (by decide)

lemma nat_sqrt_div_two_le_sqrt_div_four (k : ℕ) :
    Nat.sqrt k / 2 ≤ Nat.sqrt (k / 4) := by
  rw [Nat.le_sqrt]
  have h1 : 2 * (Nat.sqrt k / 2) ≤ Nat.sqrt k := Nat.mul_div_le (Nat.sqrt k) 2
  have h2 : (2 * (Nat.sqrt k / 2)) * (2 * (Nat.sqrt k / 2)) ≤ Nat.sqrt k * Nat.sqrt k :=
    Nat.mul_le_mul h1 h1
  have h3 : Nat.sqrt k * Nat.sqrt k ≤ k := Nat.sqrt_le k
  have h4 : 4 * ((Nat.sqrt k / 2) * (Nat.sqrt k / 2)) ≤ k := by linarith
  omega

/-- Key saving-factor comparison for Lemma 6.1 (`\label{lem:bmm-to-tridet}`, `paper.tex` §6):
For every $n \ge 1$,
$$2^{\lfloor \sqrt{\log_2 n} / D_{\text{bmm}}(c,k) \rfloor} \le
  f_{c,k}(\text{blockSizeBMM } n).$$ -/
lemma bmm_saving_le_triDetSavingFactor_blockSizeBMM (c k : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    2 ^ (Nat.sqrt (Nat.log 2 n) / D_bmm c k) ≤ triDetSavingFactor c k (blockSizeBMM n) := by
  unfold triDetSavingFactor
  apply Nat.pow_le_pow_right (by norm_num)
  set k_log := Nat.log 2 n
  have hpow4_le_n :
      (2 ^ (k_log / 4) * 2 ^ (k_log / 4)) * (2 ^ (k_log / 4) * 2 ^ (k_log / 4)) ≤ n := by
    have hexp :
        (2 ^ (k_log / 4) * 2 ^ (k_log / 4)) * (2 ^ (k_log / 4) * 2 ^ (k_log / 4)) =
          2 ^ (4 * (k_log / 4)) := by
      rw [← Nat.pow_add, ← Nat.pow_add]
      congr 1; omega
    rw [hexp]
    exact (Nat.pow_le_pow_right (by norm_num) (Nat.mul_div_le k_log 4)).trans
      (Nat.pow_log_le_self 2 (by omega))
  have hpow2_le_sqrt : 2 ^ (k_log / 4) * 2 ^ (k_log / 4) ≤ Nat.sqrt n :=
    (Nat.le_sqrt).mpr hpow4_le_n
  have hm_ge : 2 ^ (k_log / 4) ≤ blockSizeBMM n := by
    have h1 : 2 ^ (k_log / 4) ≤ Nat.sqrt (Nat.sqrt n) := (Nat.le_sqrt).mpr hpow2_le_sqrt
    exact h1.trans (le_max_right 1 _)
  have hlog_m : k_log / 4 ≤ Nat.log 2 (blockSizeBMM n) := by
    calc
      k_log / 4 = Nat.log 2 (2 ^ (k_log / 4)) := (Nat.log_pow (by norm_num) (k_log / 4)).symm
      _ ≤ Nat.log 2 (blockSizeBMM n) := Nat.log_mono_right hm_ge
  have hsqrt_m : Nat.sqrt k_log / 2 ≤ Nat.sqrt (Nat.log 2 (blockSizeBMM n)) :=
    (nat_sqrt_div_two_le_sqrt_div_four k_log).trans (Nat.sqrt_le_sqrt hlog_m)
  have hdiv_eq : Nat.sqrt k_log / D_bmm c k = (Nat.sqrt k_log / 2) / D_tri c k := by
    unfold D_bmm
    rw [← Nat.div_div_eq_div_mul]
  rw [hdiv_eq]
  exact Nat.div_le_div_right hsqrt_m

lemma numBlocksBMM_mul_le_two_mul {n m : ℕ} (hm : m ≤ n) :
    numBlocksBMM n m * m ≤ 2 * n := by
  unfold numBlocksBMM
  have h1 : ((n + m - 1) / m) * m ≤ n + m - 1 := Nat.div_mul_le_self (n + m - 1) m
  omega

/-- **Sampler-Conditional Combinatorial BMM Algorithm (`computableBMM`,
`paper.tex` Lemma 6.1 `\label{lem:bmm-to-tridet}` & Theorem 1.2 `\label{thm:main-bmm}`,
§1.2 & §6)**:
Instantiates `bmmFromTriDet` with block size `m := blockSizeBMM n = max 1 ⌊n^{1/4}⌋` and the 3D
grid-regularity Triangle Detection oracle `computableTriangleDetection m S₁ S₂`, with zero
schoolbook or fallback bypass. -/
noncomputable def computableBMM (n : ℕ)
    (S₁ : Stage1Sampler) (S₂ : Stage2Sampler)
    (A B : Fin n → Fin n → Bool) :
    Fin n → Fin n → Bool :=
  let m := blockSizeBMM n
  bmmFromTriDet n m (computableTriangleDetection m S₁ S₂) A B

/-- **Bottom-Up Cost-Tracked Combinatorial BMM Algorithm (`computableBMMTracked`,
`paper.tex` Lemma 6.1 `\label{lem:bmm-to-tridet}` & Theorem 1.2 `\label{thm:main-bmm}`,
§1.2 & §6)**:
Directly binds `blockSizeBMMTracked n` to `bmmFromTriDetTracked n m (computableTriangleDetectionTracked m S₁ S₂) A B`
with zero fallback branches. -/
noncomputable def computableBMMTracked (n : ℕ)
    (S₁ : Stage1Sampler) (S₂ : Stage2Sampler)
    (A B : Fin n → Fin n → Bool) :
    CostM (Fin n → Fin n → Bool) :=
  CostM.bind (blockSizeBMMTracked n) (fun m =>
    bmmFromTriDetTracked n m (computableTriangleDetectionTracked m S₁ S₂) A B)

/-- Projection equivalence `computableBMMTracked_fst`. -/
@[simp]
theorem computableBMMTracked_fst (n : ℕ)
    (S₁ : Stage1Sampler) (S₂ : Stage2Sampler)
    (A B : Fin n → Fin n → Bool) :
    (computableBMMTracked n S₁ S₂ A B).1 = computableBMM n S₁ S₂ A B := by
  unfold computableBMMTracked computableBMM
  rw [CostM.bind_fst, blockSizeBMMTracked_fst]
  exact bmmFromTriDetTracked_fst n (blockSizeBMM n)
    (computableTriangleDetection (blockSizeBMM n) S₁ S₂)
    (computableTriangleDetectionTracked (blockSizeBMM n) S₁ S₂)
    (computableTriangleDetectionTracked_fst (blockSizeBMM n) S₁ S₂) A B

/-- **Sampler-Conditional Correctness of `computableBMM` (`computableBMM_correct`,
`paper.tex` Lemma 6.1 `\label{lem:bmm-to-tridet}` & Theorem 1.2 `\label{thm:main-bmm}`,
§6)**:
For every $n \in \mathbb{N}$, any `(S₁ : Stage1Sampler) (S₂ : Stage2Sampler)`, and all $n \times n$
boolean matrices $A, B$, `computableBMM n S₁ S₂ A B = boolMatMul n A B`. -/
theorem computableBMM_correct (n : ℕ)
    (S₁ : Stage1Sampler) (S₂ : Stage2Sampler)
    (A B : Fin n → Fin n → Bool) :
    computableBMM n S₁ S₂ A B = boolMatMul n A B := by
  unfold computableBMM
  exact bmmFromTriDet_correct (one_le_blockSizeBMM n)
    (computableTriangleDetection_correct (blockSizeBMM n) S₁ S₂) A B

lemma combine_bmm_work_bounds {n m q S_n T_tri C_t pCost cost : ℕ}
    (hm1 : 1 ≤ m)
    (hSn_le_m : S_n ≤ m)
    (hSn_le_n : S_n ≤ n)
    (hT_mul_Sn : T_tri * S_n ≤ C_t * m ^ 3)
    (hT_le : T_tri ≤ C_t * m ^ 3)
    (hqm_le : q * m ≤ 2 * n)
    (hm3_Sn_le_n : m ^ 3 * S_n ≤ n)
    (hpCost : pCost ≤ 24 * n ^ 2)
    (hbmm_bound : cost ≤ (q * q * q) * (3 * m * m + T_tri + 4) +
      (n * n) * (3 * m * m + T_tri + m * m * m + 6) + 3) :
    (pCost + cost) * S_n ≤ (9 * C_t + 93) * n ^ 3 := by
  have hm2_le_m3 : m * m ≤ m ^ 3 := by
    calc
      m * m = (m * m) * 1 := (Nat.mul_one (m * m)).symm
      _ ≤ (m * m) * m := Nat.mul_le_mul_left (m * m) hm1
      _ = m ^ 3 := by ring
  have h1_le_m2 : 1 ≤ m * m := by nlinarith
  have h3m2_4 : (3 * m * m + 4) * S_n ≤ 7 * m ^ 3 := by
    have h1 : 3 * m * m + 4 ≤ 7 * (m * m) := by linarith
    calc
      (3 * m * m + 4) * S_n ≤ (7 * (m * m)) * m := Nat.mul_le_mul h1 hSn_le_m
      _ = 7 * m ^ 3 := by ring
  have hinner1 : (3 * m * m + T_tri + 4) * S_n ≤ (C_t + 7) * m ^ 3 := by
    calc
      (3 * m * m + T_tri + 4) * S_n
        = (3 * m * m + 4) * S_n + T_tri * S_n := by ring
      _ ≤ 7 * m ^ 3 + C_t * m ^ 3 := Nat.add_le_add h3m2_4 hT_mul_Sn
      _ = (C_t + 7) * m ^ 3 := by ring
  have hq3m3_le : (q * q * q) * m ^ 3 ≤ 8 * n ^ 3 := by
    calc
      (q * q * q) * m ^ 3
        = (q * m) ^ 3 := by ring
      _ ≤ (2 * n) ^ 3 := Nat.pow_le_pow_left hqm_le 3
      _ = 8 * n ^ 3 := by ring
  have hterm1 :
      (q * q * q) * (3 * m * m + T_tri + 4) * S_n ≤ 8 * (C_t + 7) * n ^ 3 := by
    calc
      (q * q * q) * (3 * m * m + T_tri + 4) * S_n
        = (q * q * q) * ((3 * m * m + T_tri + 4) * S_n) := by ring
      _ ≤ (q * q * q) * ((C_t + 7) * m ^ 3) := Nat.mul_le_mul_left _ hinner1
      _ = (C_t + 7) * ((q * q * q) * m ^ 3) := by ring
      _ ≤ (C_t + 7) * (8 * n ^ 3) := Nat.mul_le_mul_left _ hq3m3_le
      _ = 8 * (C_t + 7) * n ^ 3 := by ring
  have hinner2 : 3 * m * m + T_tri + m * m * m + 6 ≤ (C_t + 10) * m ^ 3 := by
    have hm3 : m * m * m = m ^ 3 := by ring
    have h1_le_m3 : 1 ≤ m ^ 3 := h1_le_m2.trans hm2_le_m3
    linarith
  have hterm2 :
      (n * n) * (3 * m * m + T_tri + m * m * m + 6) * S_n ≤ (C_t + 10) * n ^ 3 := by
    calc
      (n * n) * (3 * m * m + T_tri + m * m * m + 6) * S_n
        ≤ (n * n) * ((C_t + 10) * m ^ 3) * S_n :=
          Nat.mul_le_mul_right S_n (Nat.mul_le_mul_left (n * n) hinner2)
      _ = (C_t + 10) * (n * n) * (m ^ 3 * S_n) := by ring
      _ ≤ (C_t + 10) * (n * n) * n := Nat.mul_le_mul_left _ hm3_Sn_le_n
      _ = (C_t + 10) * n ^ 3 := by ring
  have hterm3 : 3 * S_n ≤ 3 * n ^ 3 := by
    have hn_le_n3 : n ≤ n ^ 3 := self_le_cube n
    exact Nat.mul_le_mul_left 3 (hSn_le_n.trans hn_le_n3)
  have hterm0 : pCost * S_n ≤ 24 * n ^ 3 := by
    calc
      pCost * S_n ≤ (24 * n ^ 2) * n := Nat.mul_le_mul hpCost hSn_le_n
      _ = 24 * n ^ 3 := by ring
  calc
    (pCost + cost) * S_n
      = pCost * S_n + cost * S_n := by ring
    _ ≤ 24 * n ^ 3 +
          (((q * q * q) * (3 * m * m + T_tri + 4) +
            (n * n) * (3 * m * m + T_tri + m * m * m + 6) + 3) * S_n) :=
        Nat.add_le_add hterm0 (Nat.mul_le_mul_right S_n hbmm_bound)
    _ = 24 * n ^ 3 +
          ((q * q * q) * (3 * m * m + T_tri + 4) * S_n +
            (n * n) * (3 * m * m + T_tri + m * m * m + 6) * S_n + 3 * S_n) := by ring
    _ ≤ 24 * n ^ 3 + (8 * (C_t + 7) * n ^ 3 + (C_t + 10) * n ^ 3 + 3 * n ^ 3) :=
        Nat.add_le_add_left (Nat.add_le_add (Nat.add_le_add hterm1 hterm2) hterm3) _
    _ = (9 * C_t + 93) * n ^ 3 := by ring

/-- **Master Correctness and Subcubic Cost Specification of `computableBMMTracked`
(`computableBMMTracked_spec`, `paper.tex` Lemma 6.1 `\label{lem:bmm-to-tridet}` &
Theorem 1.2 `\label{thm:main-bmm}`, §1.2 & §6)**:
For every $n \ge 1$, any `(S₁ : Stage1Sampler) (S₂ : Stage2Sampler)`, and all $n \times n$ boolean
matrices $A, B$, binding `let run := computableBMMTracked n S₁ S₂ A B` once:
`run.1 = boolMatMul n A B` and
$$run.2 \cdot 2^{\lfloor \sqrt{\log_2 n} / D_{\text{bmm}}(c, k) \rfloor}
  \le C_{\text{bmm}}(c, k) \cdot n^3$$
where $c = \text{twoStageConstC } S_1\ S_2$ and $k = \text{twoStageConstK } S_1\ S_2$. -/
theorem computableBMMTracked_spec {n : ℕ} (hn : 1 ≤ n)
    (S₁ : Stage1Sampler) (S₂ : Stage2Sampler)
    (A B : Fin n → Fin n → Bool) :
    let c := twoStageConstC S₁ S₂
    let k := twoStageConstK S₁ S₂
    let run := computableBMMTracked n S₁ S₂ A B
    run.1 = boolMatMul n A B ∧
    run.2 * 2 ^ (Nat.sqrt (Nat.log 2 n) / D_bmm c k) ≤ C_bmm c k * n ^ 3 := by
  dsimp only
  refine ⟨by rw [computableBMMTracked_fst, computableBMM_correct], ?_⟩
  set c := twoStageConstC S₁ S₂
  set k := twoStageConstK S₁ S₂
  set m := blockSizeBMM n
  set q := numBlocksBMM n m
  set S_n := 2 ^ (Nat.sqrt (Nat.log 2 n) / D_bmm c k)
  have hm1 : 1 ≤ m := one_le_blockSizeBMM n
  have hm_le_n : m ≤ n := blockSizeBMM_le_self hn
  set T_tri := (C_tri c k * m ^ 3) / triDetSavingFactor c k m
  have htd_corr : ∀ A' B' C',
      (computableTriangleDetectionTracked m S₁ S₂ A' B' C').1 = hasTriangle m A' B' C' :=
    fun A' B' C' => (computableTriangleDetectionTracked_spec hm1 S₁ S₂ A' B' C').1
  have htd_cost : ∀ A' B' C',
      (computableTriangleDetectionTracked m S₁ S₂ A' B' C').2 ≤ T_tri := by
    intro A' B' C'
    have hspec := (computableTriangleDetectionTracked_spec hm1 S₁ S₂ A' B' C').2
    exact (Nat.le_div_iff_mul_le (one_le_triDetSavingFactor c k m)).mpr hspec
  have hbmm_bound := lem_bmm_to_tridet_time_bound htd_corr htd_cost A B
  have hSn_le_fm := bmm_saving_le_triDetSavingFactor_blockSizeBMM c k hn
  have hSn_le_m : S_n ≤ m := hSn_le_fm.trans (triDetSavingFactor_le_self c k hm1)
  have hSn_le_n : S_n ≤ n := hSn_le_m.trans hm_le_n
  have hT_mul_Sn : T_tri * S_n ≤ C_tri c k * m ^ 3 :=
    (Nat.mul_le_mul_left T_tri hSn_le_fm).trans
      (Nat.div_mul_le_self (C_tri c k * m ^ 3) (triDetSavingFactor c k m))
  have hT_le : T_tri ≤ C_tri c k * m ^ 3 :=
    Nat.div_le_self (C_tri c k * m ^ 3) (triDetSavingFactor c k m)
  have hqm_le : q * m ≤ 2 * n := numBlocksBMM_mul_le_two_mul hm_le_n
  have hm3_Sn_le_n : m ^ 3 * S_n ≤ n :=
    (Nat.mul_le_mul_left (m ^ 3) hSn_le_fm).trans
      (blockSizeBMM_cube_mul_saving_le c k hn)
  have htotal_cost_eq :
      (computableBMMTracked n S₁ S₂ A B).2 =
        (blockSizeBMMTracked n).2 +
          (bmmFromTriDetTracked n m (computableTriangleDetectionTracked m S₁ S₂) A B).2 := by
    unfold computableBMMTracked
    rw [CostM.bind_snd, blockSizeBMMTracked_fst]
  rw [htotal_cost_eq]
  exact combine_bmm_work_bounds hm1 hSn_le_m hSn_le_n hT_mul_Sn hT_le hqm_le hm3_Sn_le_n
    (blockSizeBMMTracked_snd_le hn) hbmm_bound

/-- **`paper.tex` Theorem 1.2 (`thm_main_bmm`, §1.2 & Appendix C & §6)**:
For any Stage 1 oblivious sampler `S₁ : Stage1Sampler` (`[AFKLM24, Lemma 4.4]` / `[GW97]`) and
Stage 2 averaging sampler `S₂ : Stage2Sampler` (`[Vadhan, Cor. 6.24]` / `[GUV09]`), there exist
uniform constants $C > 0$ and $D > 0$ (independent of $n, A, B$) such that for all $n \ge 2$ and
all $n \times n$ Boolean matrices $A, B$, there exists $t \in \mathbb{N}$ such that
`computableBMMTracked n S₁ S₂ A B = (boolMatMul n A B, t)` and
$$t \cdot 2^{\lfloor \sqrt{\log_2 n} / D \rfloor} \le C \cdot n^3.$$ -/
theorem thm_main_bmm :
    ∀ (S₁ : Stage1Sampler) (S₂ : Stage2Sampler),
      ∃ C > 0, ∃ D > 0, ∀ n ≥ 2,
        ∀ (A B : Fin n → Fin n → Bool),
          ∃ t : ℕ,
            computableBMMTracked n S₁ S₂ A B = (boolMatMul n A B, t) ∧
            t * 2 ^ (Nat.sqrt (Nat.log 2 n) / D) ≤ C * n ^ 3 := by
  intro S₁ S₂
  let c := twoStageConstC S₁ S₂
  let k := twoStageConstK S₁ S₂
  refine ⟨C_bmm c k, C_bmm_pos c k, D_bmm c k, D_bmm_pos c k, ?_⟩
  intro n hn A B
  rcases computableBMMTracked_spec (by omega) S₁ S₂ A B with ⟨hfst, hsnd⟩
  refine ⟨(computableBMMTracked n S₁ S₂ A B).2, ?_, hsnd⟩
  exact Prod.ext hfst rfl

/-- Address / pointer bit-length factor `bitLengthNat n + 4` per pointer/index step under the
Cook–Reckhow log-cost / pointer-machine model (`paper.tex` Appendix C (`\label{app:models}`)).
Note that multi-precision multiplications, powers, divisions, and cross-multiplications inside
`ApproxGridNorm` are bit-priced inside `CostM` (while table-contraction counter additions are
unit-charged as disclosed in `FORMALIZATION.tex` Class B), and each index step in $[n]$ uses $\le \text{bitLengthNat } n$ bits. -/
def pointerBitOverhead (n : ℕ) : ℕ :=
  bitLengthNat n + 4

/-- Absorption of the Cook–Reckhow pointer bit-length factor `pointerBitOverhead n = bitLengthNat n + 4`
into the $2^{\Omega(\sqrt{\log n})}$ saving factor by quadrupling the exponent divisor $D \ge 1$
(`paper.tex` Appendix C (`\label{app:models}`), Appendix C):
For every $n \ge 1$ and $D \ge 1$,
$$\text{pointerBitOverhead } n \cdot 2^{\lfloor \sqrt{\log_2 n} / (4 D) \rfloor}
  \le 80 D^2 \cdot 2^{\lfloor \sqrt{\log_2 n} / D \rfloor}.$$ -/
lemma pointerBitOverhead_mul_saving_le (n : ℕ) {D : ℕ} (hD : 1 ≤ D) :
    pointerBitOverhead n * 2 ^ (Nat.sqrt (Nat.log 2 n) / (4 * D)) ≤
      (80 * D ^ 2) * 2 ^ (Nat.sqrt (Nat.log 2 n) / D) := by
  set k := Nat.log 2 n
  set s := Nat.sqrt k / D
  set r := Nat.sqrt k / (4 * D)
  have hr_eq : r = s / 4 := by
    unfold r s
    rw [Nat.mul_comm 4 D, ← Nat.div_div_eq_div_mul]
  have h3r_le_s : 3 * r ≤ s := by
    have : 4 * r ≤ s := by rw [hr_eq]; exact Nat.mul_div_le s 4
    omega
  have hs_lt : s < 4 * (r + 1) := by
    rw [hr_eq]
    omega
  have hsqrt_lt : Nat.sqrt k < 4 * (r + 1) * D := by
    by_contra hge
    push_neg at hge
    have hdiv : 4 * (r + 1) ≤ Nat.sqrt k / D :=
      (Nat.le_div_iff_mul_le hD).mpr hge
    exact absurd hdiv (not_le.mpr hs_lt)
  have hsqrt_succ : Nat.sqrt k + 1 ≤ 4 * (r + 1) * D := hsqrt_lt
  have hk_lt : k < (Nat.sqrt k + 1) ^ 2 := by
    rw [sq]
    exact Nat.lt_succ_sqrt k
  have hk_le : k ≤ 16 * D ^ 2 * (r + 1) ^ 2 := by
    have hsq := Nat.pow_le_pow_left hsqrt_succ 2
    have hring : (4 * (r + 1) * D) ^ 2 = 16 * D ^ 2 * (r + 1) ^ 2 := by ring
    rw [hring] at hsq
    exact (le_of_lt hk_lt).trans hsq
  have hbit_le : pointerBitOverhead n ≤ 20 * D ^ 2 * (r + 1) ^ 2 := by
    unfold pointerBitOverhead bitLengthNat
    have hD2 : 1 ≤ D ^ 2 := by nlinarith
    have hr2 : 1 ≤ (r + 1) ^ 2 := by nlinarith
    have h1_le : 1 ≤ D ^ 2 * (r + 1) ^ 2 := Nat.mul_le_mul hD2 hr2
    change k + 1 + 4 ≤ 20 * D ^ 2 * (r + 1) ^ 2
    nlinarith
  have hr_pow : (r + 1) ^ 2 ≤ 4 * 2 ^ (2 * r) := by
    have h1 : (r + 1) ^ 2 ≤ 2 ^ (2 * (r + 1)) := nat_sq_le_two_pow (r + 1)
    have h2 : 2 ^ (2 * (r + 1)) = 4 * 2 ^ (2 * r) := by
      have : 2 * (r + 1) = 2 + 2 * r := by ring
      rw [this, Nat.pow_add]
    rwa [h2] at h1
  have hbit_pow : pointerBitOverhead n ≤ 80 * D ^ 2 * 2 ^ (2 * r) := by
    calc
      pointerBitOverhead n
        ≤ 20 * D ^ 2 * (r + 1) ^ 2 := hbit_le
      _ ≤ 20 * D ^ 2 * (4 * 2 ^ (2 * r)) := Nat.mul_le_mul_left _ hr_pow
      _ = 80 * D ^ 2 * 2 ^ (2 * r) := by ring
  calc
    pointerBitOverhead n * 2 ^ r
      ≤ (80 * D ^ 2 * 2 ^ (2 * r)) * 2 ^ r := Nat.mul_le_mul_right _ hbit_pow
    _ = (80 * D ^ 2) * (2 ^ (2 * r) * 2 ^ r) := by ring
    _ = (80 * D ^ 2) * 2 ^ (3 * r) := by
        rw [← Nat.pow_add]
        congr 2
        omega
    _ ≤ (80 * D ^ 2) * 2 ^ s :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) h3r_le_s)

/-- Quadratic 2D-indexing Cook–Reckhow log-cost absorption (`12 * (pointerBitOverhead n) ^ 2`):
For every $n \in \mathbb{N}$ and $D \ge 1$,
$$(12 \cdot (\text{pointerBitOverhead } n)^2) \cdot 2^{\lfloor \sqrt{\log_2 n} / (16 D) \rfloor}
  \le 1228800 D^4 \cdot 2^{\lfloor \sqrt{\log_2 n} / D \rfloor}.$$ -/
lemma pointerBitOverhead_sq_mul_saving_le (n : ℕ) {D : ℕ} (hD : 1 ≤ D) :
    (12 * (pointerBitOverhead n) ^ 2) * 2 ^ (Nat.sqrt (Nat.log 2 n) / (16 * D)) ≤
      (1228800 * D ^ 4) * 2 ^ (Nat.sqrt (Nat.log 2 n) / D) := by
  have h16 : 16 * D = 4 * (4 * D) := by ring
  rw [h16]
  have h1 := pointerBitOverhead_mul_saving_le n (D := 4 * D) (by omega)
  have h2 := pointerBitOverhead_mul_saving_le n (D := D) hD
  calc
    (12 * (pointerBitOverhead n) ^ 2) * 2 ^ (Nat.sqrt (Nat.log 2 n) / (4 * (4 * D)))
      = (12 * pointerBitOverhead n) *
          (pointerBitOverhead n * 2 ^ (Nat.sqrt (Nat.log 2 n) / (4 * (4 * D)))) := by ring
    _ ≤ (12 * pointerBitOverhead n) *
          ((80 * (4 * D) ^ 2) * 2 ^ (Nat.sqrt (Nat.log 2 n) / (4 * D))) :=
        Nat.mul_le_mul_left _ h1
    _ = (12 * (80 * (4 * D) ^ 2)) *
          (pointerBitOverhead n * 2 ^ (Nat.sqrt (Nat.log 2 n) / (4 * D))) := by ring
    _ ≤ (12 * (80 * (4 * D) ^ 2)) *
          ((80 * D ^ 2) * 2 ^ (Nat.sqrt (Nat.log 2 n) / D)) :=
        Nat.mul_le_mul_left _ h2
    _ = (1228800 * D ^ 4) * 2 ^ (Nat.sqrt (Nat.log 2 n) / D) := by ring

lemma pointerBitOverhead_le_twelve_sq (n : ℕ) :
    pointerBitOverhead n ≤ 12 * (pointerBitOverhead n) ^ 2 := by
  have h1 : 1 ≤ pointerBitOverhead n := by unfold pointerBitOverhead; omega
  nlinarith

/-- Exponent divisor $D_{\text{tri,log}}(c, k) = 16 \cdot D_{\text{tri}}(c, k)$ for the
Cook–Reckhow pointer-overhead scaling bound (`paper.tex` Appendix C (`\label{app:models}`), Appendix C). -/
def D_tri_log (c k : ℕ) : ℕ := 16 * D_tri c k

lemma D_tri_log_pos (c k : ℕ) : 0 < D_tri_log c k :=
  Nat.mul_pos (by decide) (D_tri_pos c k)

/-- Uniform constant $C_{\text{tri,log}}(c, k) = 1228800 \cdot D_{\text{tri}}(c, k)^4 \cdot C_{\text{tri}}(c, k)$
for the Cook–Reckhow pointer-overhead scaling bound (`paper.tex` Appendix C (`\label{app:models}`)). -/
noncomputable def C_tri_log (c k : ℕ) : ℕ := 1228800 * (D_tri c k) ^ 4 * C_tri c k

lemma C_tri_log_pos (c k : ℕ) : 0 < C_tri_log c k :=
  Nat.mul_pos (Nat.mul_pos (by decide) (Nat.pow_pos (D_tri_pos c k))) (C_tri_pos c k)

/-- **Log-Cost Absorption & `ArithRAM` Primitive Log-Cost Theorem for Triangle Detection
(`thm_main_triangle_detection_log_cost_absorption`, `paper.tex` Appendix C (`\label{app:models}`) & Section 6,
Appendix C & §6)**:
This theorem is the **log-cost absorption step** (together with per-primitive `ArithRAM` log-cost
execution witnesses for 2D matrix read/write, register addition, and loop control). It does not
compile `computableBMMTracked` / `computableTriangleDetectionTracked` into a single `ArithRAM`
program; the full algorithm runs in `CostM`. Specifically, it establishes:
1. Machine-checked `ArithRAM` log-cost execution bounds (`EvalsToInLogCostTime`) for the fundamental
   flattened-memory 2D-matrix read, triangle-triple check, register addition, and loop-control
   primitives (`ramReadMatrixEntry`, `ramCheckTriangleTriple`, `ramInitAndAdd`, `ramCountLoop`),
   showing that each 2D matrix access costs at most `12 * (pointerBitOverhead n) ^ 2` bit operations,
2. Absorption of both linear pointer-indexing overhead `t * pointerBitOverhead n` and quadratic
   2D-matrix-indexing overhead `t * (12 * (pointerBitOverhead n) ^ 2)` into the $2^{\Omega(\sqrt{\log n})}$
   saving factor of `computableTriangleDetectionTracked n S₁ S₂ A B C_mat = (hasTriangle n A B C_mat, t)`:
   $$(t \cdot (12 \cdot (\text{pointerBitOverhead } n)^2)) \cdot 2^{\lfloor \sqrt{\log_2 n} / D \rfloor}
     \le C \cdot n^3.$$ -/
theorem thm_main_triangle_detection_log_cost_absorption :
    ∀ (S₁ : Stage1Sampler) (S₂ : Stage2Sampler),
      ∃ C > 0, ∃ D > 0, ∀ n ≥ 2,
        ∀ (A B C_mat : Fin n → Fin n → Bool),
          (ArithRAM.initTriDetConfig ArithRAM.ramInitAndAdd n A B C_mat).regs
            ArithRAM.ramInitAndAdd.reg0 = n ∧
          ArithRAM.readBMatFromMem n (ArithRAM.initTriDetMem n A B C_mat) 1 = A ∧
          ArithRAM.readBMatFromMem n (ArithRAM.initTriDetMem n A B C_mat) (1 + n * n) = B ∧
          ArithRAM.readBMatFromMem n (ArithRAM.initTriDetMem n A B C_mat) (1 + 2 * (n * n)) = C_mat ∧
          (∀ i j : Fin n,
            ∃ (haltCfg : ArithRAM.Config ArithRAM.ramReadMatrixEntry) (b : ℕ),
              b ≤ 12 * (pointerBitOverhead n) ^ 2 ∧
              haltCfg.regs (5 : Fin 6) = (if A i j then 1 else 0) ∧
              ArithRAM.EvalsToInLogCostTime ArithRAM.ramReadMatrixEntry
                (ArithRAM.initReadMatrixEntryConfig n 1 i j
                  (ArithRAM.initTriDetMem n A B C_mat)) haltCfg 5 b) ∧
          (∀ i j k : Fin n,
            ∃ (haltCfg : ArithRAM.Config ArithRAM.ramCheckTriangleTriple) (b : ℕ),
              b ≤ 12 * (pointerBitOverhead n) ^ 2 ∧
              haltCfg.regs (6 : Fin 7) = (if (A i j && B j k && C_mat i k) then 1 else 0) ∧
              ArithRAM.EvalsToInLogCostTime ArithRAM.ramCheckTriangleTriple
                (ArithRAM.initCheckTriangleTripleConfig n i j k
                  (ArithRAM.initTriDetMem n A B C_mat)) haltCfg 6 b) ∧
          (∃ (haltCfg : ArithRAM.Config ArithRAM.ramInitAndAdd) (b : ℕ),
            b ≤ 3 * pointerBitOverhead n ∧
            haltCfg.regs (2 : Fin 3) = n + n ∧
            ArithRAM.EvalsToInLogCostTime ArithRAM.ramInitAndAdd
              (ArithRAM.initTriDetConfig ArithRAM.ramInitAndAdd n A B C_mat) haltCfg 3 b) ∧
          (∀ (r₁ r₂ dst : Fin 3) (regs : Fin 3 → ℕ),
            regs r₁ ≤ n → regs r₂ ≤ n →
            ArithRAM.opLogCost (.add dst r₁ r₂) regs (ArithRAM.initTriDetMem n A B C_mat) ≤
              2 * pointerBitOverhead n) ∧
          ∃ t : ℕ,
            computableTriangleDetectionTracked n S₁ S₂
              (ArithRAM.readBMatFromMem n (ArithRAM.initTriDetMem n A B C_mat) 1)
              (ArithRAM.readBMatFromMem n (ArithRAM.initTriDetMem n A B C_mat) (1 + n * n))
              (ArithRAM.readBMatFromMem n (ArithRAM.initTriDetMem n A B C_mat) (1 + 2 * (n * n))) =
              (hasTriangle n A B C_mat, t) ∧
            (∃ (haltCfg : ArithRAM.Config ArithRAM.ramCountLoop) (b : ℕ),
              b ≤ (n + 1) * (3 * pointerBitOverhead n) ∧
              haltCfg.regs (1 : Fin 4) = n ∧
              ArithRAM.EvalsToInLogCostTime ArithRAM.ramCountLoop
                (ArithRAM.initTriDetConfig ArithRAM.ramCountLoop n A B C_mat) haltCfg (2 * n + 3) b) ∧
            (t * pointerBitOverhead n) * 2 ^ (Nat.sqrt (Nat.log 2 n) / D) ≤ C * n ^ 3 ∧
            (t * (12 * (pointerBitOverhead n) ^ 2)) * 2 ^ (Nat.sqrt (Nat.log 2 n) / D) ≤ C * n ^ 3 := by
  intro S₁ S₂
  let c := twoStageConstC S₁ S₂
  let k := twoStageConstK S₁ S₂
  refine ⟨C_tri_log c k, C_tri_log_pos c k, D_tri_log c k, D_tri_log_pos c k, ?_⟩
  intro n hn A B C_mat
  have hreadA : ArithRAM.readBMatFromMem n (ArithRAM.initTriDetMem n A B C_mat) 1 = A := by
    funext i j; exact ArithRAM.readBMatFromMem_initTriDetMem_A n A B C_mat i j
  have hreadB : ArithRAM.readBMatFromMem n (ArithRAM.initTriDetMem n A B C_mat) (1 + n * n) = B := by
    funext i j; exact ArithRAM.readBMatFromMem_initTriDetMem_B n A B C_mat i j
  have hreadC :
      ArithRAM.readBMatFromMem n (ArithRAM.initTriDetMem n A B C_mat) (1 + 2 * (n * n)) = C_mat := by
    funext i j; exact ArithRAM.readBMatFromMem_initTriDetMem_C n A B C_mat i j
  refine ⟨ArithRAM.initTriDetConfig_reg0 ArithRAM.ramInitAndAdd n A B C_mat,
    hreadA, hreadB, hreadC, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    rcases ArithRAM.ramReadMatrixEntry_triDet_A n A B C_mat i j with
      ⟨haltCfg, b, hb_le, hreg5, heval⟩
    exact ⟨haltCfg, b, hb_le, hreg5, heval⟩
  · intro i j k
    exact ArithRAM.ramCheckTriangleTriple_evalsToInLogCostTime_triDet n A B C_mat i j k
  · rcases ArithRAM.ramInitAndAdd_evalsToInLogCostTime_triDet n A B C_mat with
      ⟨haltCfg, b, hb_le, hreg2, heval⟩
    refine ⟨haltCfg, b, ?_, hreg2, heval⟩
    unfold pointerBitOverhead
    omega
  · intro r₁ r₂ dst regs hr₁ hr₂
    have h1 := ArithRAM.opLogCost_add_index_le dst r₁ r₂ regs
      (ArithRAM.initTriDetMem n A B C_mat) hr₁ hr₂
    unfold pointerBitOverhead
    omega
  · rw [hreadA, hreadB, hreadC]
    rcases computableTriangleDetectionTracked_spec (by omega) S₁ S₂ A B C_mat with ⟨hfst, hsnd⟩
    set t := (computableTriangleDetectionTracked n S₁ S₂ A B C_mat).2
    have hD_pos : 1 ≤ D_tri c k := D_tri_pos c k
    have hbit_sq := pointerBitOverhead_sq_mul_saving_le n (D := D_tri c k) hD_pos
    have h_sq_bound :
        (t * (12 * (pointerBitOverhead n) ^ 2)) * 2 ^ (Nat.sqrt (Nat.log 2 n) / D_tri_log c k) ≤
          C_tri_log c k * n ^ 3 := by
      unfold C_tri_log D_tri_log
      calc
        (t * (12 * (pointerBitOverhead n) ^ 2)) * 2 ^ (Nat.sqrt (Nat.log 2 n) / (16 * D_tri c k))
          = t * ((12 * (pointerBitOverhead n) ^ 2) *
              2 ^ (Nat.sqrt (Nat.log 2 n) / (16 * D_tri c k))) := by ring
        _ ≤ t * ((1228800 * (D_tri c k) ^ 4) * 2 ^ (Nat.sqrt (Nat.log 2 n) / D_tri c k)) :=
            Nat.mul_le_mul_left t hbit_sq
        _ = (1228800 * (D_tri c k) ^ 4) * (t * 2 ^ (Nat.sqrt (Nat.log 2 n) / D_tri c k)) := by ring
        _ ≤ (1228800 * (D_tri c k) ^ 4) * (C_tri c k * n ^ 3) :=
            Nat.mul_le_mul_left _ hsnd
        _ = (1228800 * (D_tri c k) ^ 4 * C_tri c k) * n ^ 3 := by ring
    have h_lin_le_sq :
        (t * pointerBitOverhead n) * 2 ^ (Nat.sqrt (Nat.log 2 n) / D_tri_log c k) ≤
          (t * (12 * (pointerBitOverhead n) ^ 2)) * 2 ^ (Nat.sqrt (Nat.log 2 n) / D_tri_log c k) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left t (pointerBitOverhead_le_twelve_sq n))
    rcases ArithRAM.ramCountLoop_evalsToInLogCostTime_triDet n A B C_mat with
      ⟨haltCfgL, bL, hbL_le, _hr0, hr1, _hmem, hevalL⟩
    have hbL_le' : bL ≤ (n + 1) * (3 * pointerBitOverhead n) := by
      refine hbL_le.trans (Nat.mul_le_mul_left (n + 1) ?_)
      unfold pointerBitOverhead
      omega
    exact ⟨t, Prod.ext hfst rfl,
      ⟨haltCfgL, bL, hbL_le', hr1, hevalL⟩,
      h_lin_le_sq.trans h_sq_bound, h_sq_bound⟩

/-- Alias for `thm_main_triangle_detection_log_cost_absorption`. -/
abbrev thm_main_triangle_detection_log_cost := thm_main_triangle_detection_log_cost_absorption

/-- Exponent divisor $D_{\text{bmm,log}}(c, k) = 16 \cdot D_{\text{bmm}}(c, k)$ for the
Cook–Reckhow log-cost absorption BMM bound (`paper.tex` Appendix C (`\label{app:models}`) & Theorem 1.2, §1.2 & Appendix C). -/
def D_bmm_log (c k : ℕ) : ℕ := 16 * D_bmm c k

lemma D_bmm_log_pos (c k : ℕ) : 0 < D_bmm_log c k :=
  Nat.mul_pos (by decide) (D_bmm_pos c k)

/-- Uniform constant $C_{\text{bmm,log}}(c, k) = 1228800 \cdot D_{\text{bmm}}(c, k)^4 \cdot C_{\text{bmm}}(c, k)$
for the Cook–Reckhow log-cost absorption BMM bound (`paper.tex` Appendix C (`\label{app:models}`) & Theorem 1.2). -/
noncomputable def C_bmm_log (c k : ℕ) : ℕ := 1228800 * (D_bmm c k) ^ 4 * C_bmm c k

lemma C_bmm_log_pos (c k : ℕ) : 0 < C_bmm_log c k :=
  Nat.mul_pos (Nat.mul_pos (by decide) (Nat.pow_pos (D_bmm_pos c k))) (C_bmm_pos c k)

/-- **Log-Cost Absorption & `ArithRAM` Primitive Log-Cost Theorem for BMM
(`thm_main_bmm_log_cost_absorption`, `paper.tex` Theorem 1.2 & Appendix C (`\label{app:models}`), §1.2 & Appendix C & §6)**:
This theorem is the **log-cost absorption step** (together with per-primitive `ArithRAM` log-cost
execution witnesses for 2D matrix read/write, register addition, and loop control). It does not
compile `computableBMMTracked` / `computableTriangleDetectionTracked` into a single `ArithRAM`
program; the full algorithm runs in `CostM`. Specifically, it establishes:
1. Machine-checked `ArithRAM` log-cost execution bounds (`EvalsToInLogCostTime`) for the fundamental
   flattened-memory 2D-matrix read, write, entry clearing, register addition, and loop-control
   primitives (`ramReadMatrixEntry`, `ramWriteMatrixEntry`, `ramInitAndAdd`, `ramCountLoop`),
   showing that each 2D matrix access/update costs at most `12 * (pointerBitOverhead n) ^ 2` bit
   operations,
2. Absorption of both linear pointer-indexing overhead `t * pointerBitOverhead n` and quadratic
   2D-matrix-indexing overhead `t * (12 * (pointerBitOverhead n) ^ 2)` into the $2^{\Omega(\sqrt{\log n})}$
   saving factor of `computableBMMTracked n S₁ S₂ A B = (boolMatMul n A B, t)`:
   $$(t \cdot (12 \cdot (\text{pointerBitOverhead } n)^2)) \cdot 2^{\lfloor \sqrt{\log_2 n} / D \rfloor}
     \le C \cdot n^3.$$ -/
theorem thm_main_bmm_log_cost_absorption :
    ∀ (S₁ : Stage1Sampler) (S₂ : Stage2Sampler),
      ∃ C > 0, ∃ D > 0, ∀ n ≥ 2,
        ∀ (A B : Fin n → Fin n → Bool),
          (ArithRAM.initBMMConfig ArithRAM.ramInitAndAdd n A B).regs
            ArithRAM.ramInitAndAdd.reg0 = n ∧
          ArithRAM.readBMatFromMem n (ArithRAM.initBMMMem n A B) 1 = A ∧
          ArithRAM.readBMatFromMem n (ArithRAM.initBMMMem n A B) (1 + n * n) = B ∧
          (∀ i j : Fin n,
            ∃ (haltCfg : ArithRAM.Config ArithRAM.ramReadMatrixEntry) (b : ℕ),
              b ≤ 12 * (pointerBitOverhead n) ^ 2 ∧
              haltCfg.regs (5 : Fin 6) = (if A i j then 1 else 0) ∧
              ArithRAM.EvalsToInLogCostTime ArithRAM.ramReadMatrixEntry
                (ArithRAM.initReadMatrixEntryConfig n 1 i j
                  (ArithRAM.initBMMMem n A B)) haltCfg 5 b) ∧
          (∃ (haltCfg : ArithRAM.Config ArithRAM.ramInitAndAdd) (b : ℕ),
            b ≤ 3 * pointerBitOverhead n ∧
            haltCfg.regs (2 : Fin 3) = n + n ∧
            ArithRAM.EvalsToInLogCostTime ArithRAM.ramInitAndAdd
              (ArithRAM.initBMMConfig ArithRAM.ramInitAndAdd n A B) haltCfg 3 b) ∧
          (∀ (r₁ r₂ dst : Fin 3) (regs : Fin 3 → ℕ),
            regs r₁ ≤ n → regs r₂ ≤ n →
            ArithRAM.opLogCost (.add dst r₁ r₂) regs (ArithRAM.initBMMMem n A B) ≤
              2 * pointerBitOverhead n) ∧
          (∀ (i j : Fin n) (mem : ℕ → ℕ),
            ∃ (haltCfg : ArithRAM.Config ArithRAM.ramWriteMatrixEntry) (b : ℕ),
              b ≤ 12 * (pointerBitOverhead n) ^ 2 ∧
              haltCfg.mem = ArithRAM.updateMem mem (1 + 2 * (n * n) + i.val * n + j.val) 0 ∧
              ArithRAM.readBMatFromMem n haltCfg.mem (1 + 2 * (n * n)) =
                clearMatEntry (ArithRAM.readBMatFromMem n mem (1 + 2 * (n * n))) i j ∧
              ArithRAM.EvalsToInLogCostTime ArithRAM.ramWriteMatrixEntry
                (ArithRAM.initWriteMatrixEntryConfig n (1 + 2 * (n * n)) i j 0 mem) haltCfg 5 b) ∧
          (∀ (entries : List (Fin n × Fin n)) (i j : Fin n),
            let mem' := ArithRAM.clearEntriesMem n (1 + 2 * (n * n))
              (ArithRAM.initTriDetMem n A B (fun _ _ => true)) entries
            ∃ (haltCfg : ArithRAM.Config ArithRAM.ramReadMatrixEntry) (b : ℕ),
              b ≤ 12 * (pointerBitOverhead n) ^ 2 ∧
              haltCfg.regs (5 : Fin 6) =
                (if ArithRAM.readBMatFromMem n mem' (1 + 2 * (n * n)) i j then 1 else 0) ∧
              ArithRAM.EvalsToInLogCostTime ArithRAM.ramReadMatrixEntry
                (ArithRAM.initReadMatrixEntryConfig n (1 + 2 * (n * n)) i j mem') haltCfg 5 b) ∧
          (∀ (i j : Fin n) (valBit : Bool) (mem : ℕ → ℕ),
            ∃ (haltCfg : ArithRAM.Config ArithRAM.ramWriteMatrixEntry) (b : ℕ),
              b ≤ 12 * (pointerBitOverhead n) ^ 2 ∧
              ArithRAM.readBMatFromMem n haltCfg.mem (1 + 2 * (n * n)) i j = valBit ∧
              ArithRAM.EvalsToInLogCostTime ArithRAM.ramWriteMatrixEntry
                (ArithRAM.initWriteMatrixEntryConfig n (1 + 2 * (n * n)) i j
                  (if valBit then 1 else 0) mem) haltCfg 5 b) ∧
          ∃ t : ℕ,
            computableBMMTracked n S₁ S₂
              (ArithRAM.readBMatFromMem n (ArithRAM.initBMMMem n A B) 1)
              (ArithRAM.readBMatFromMem n (ArithRAM.initBMMMem n A B) (1 + n * n)) =
              (boolMatMul n A B, t) ∧
            (∃ (haltCfg : ArithRAM.Config ArithRAM.ramCountLoop) (b : ℕ),
              b ≤ (n + 1) * (3 * pointerBitOverhead n) ∧
              haltCfg.regs (1 : Fin 4) = n ∧
              ArithRAM.EvalsToInLogCostTime ArithRAM.ramCountLoop
                (ArithRAM.initBMMConfig ArithRAM.ramCountLoop n A B) haltCfg (2 * n + 3) b) ∧
            (t * pointerBitOverhead n) * 2 ^ (Nat.sqrt (Nat.log 2 n) / D) ≤ C * n ^ 3 ∧
            (t * (12 * (pointerBitOverhead n) ^ 2)) * 2 ^ (Nat.sqrt (Nat.log 2 n) / D) ≤ C * n ^ 3 := by
  intro S₁ S₂
  let c := twoStageConstC S₁ S₂
  let k := twoStageConstK S₁ S₂
  refine ⟨C_bmm_log c k, C_bmm_log_pos c k, D_bmm_log c k, D_bmm_log_pos c k, ?_⟩
  intro n hn A B
  have hreadA : ArithRAM.readBMatFromMem n (ArithRAM.initBMMMem n A B) 1 = A := by
    funext i j; exact ArithRAM.readBMatFromMem_initBMMMem_A n A B i j
  have hreadB : ArithRAM.readBMatFromMem n (ArithRAM.initBMMMem n A B) (1 + n * n) = B := by
    funext i j; exact ArithRAM.readBMatFromMem_initBMMMem_B n A B i j
  refine ⟨ArithRAM.initBMMConfig_reg0 ArithRAM.ramInitAndAdd n A B,
    hreadA, hreadB, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    rcases ArithRAM.ramReadMatrixEntry_bmm_A n A B i j with
      ⟨haltCfg, b, hb_le, hreg5, heval⟩
    exact ⟨haltCfg, b, hb_le, hreg5, heval⟩
  · rcases ArithRAM.ramInitAndAdd_evalsToInLogCostTime_bmm n A B with
      ⟨haltCfg, b, hb_le, hreg2, heval⟩
    refine ⟨haltCfg, b, ?_, hreg2, heval⟩
    unfold pointerBitOverhead
    omega
  · intro r₁ r₂ dst regs hr₁ hr₂
    have h1 := ArithRAM.opLogCost_add_index_le dst r₁ r₂ regs
      (ArithRAM.initBMMMem n A B) hr₁ hr₂
    unfold pointerBitOverhead
    omega
  · intro i j mem
    rcases ArithRAM.ramWriteMatrixEntry_evalsToInLogCostTime n (1 + 2 * (n * n)) i j 0 mem
      (by omega) (by omega) with ⟨haltCfg, b, hb_le, hmem_eq, heval⟩
    refine ⟨haltCfg, b, hb_le, hmem_eq, ?_, heval⟩
    funext x z
    rw [hmem_eq, ArithRAM.readBMatFromMem_updateMem_zero]
    rfl
  · intro entries i j
    exact ArithRAM.ramReadMatrixEntry_after_clears_evalsToInLogCostTime
      n A B (fun _ _ => true) entries i j
  · intro i j valBit mem
    have hval : (if valBit then 1 else 0) ≤ 1 := by
      split_ifs <;> omega
    rcases ArithRAM.ramWriteMatrixEntry_evalsToInLogCostTime n (1 + 2 * (n * n)) i j
      (if valBit then 1 else 0) mem
      (by omega) hval with ⟨haltCfg, b, hb_le, hmem_eq, heval⟩
    refine ⟨haltCfg, b, hb_le, ?_, heval⟩
    rw [hmem_eq, ArithRAM.readBMatFromMem_updateMem_self_bool]
  · rw [hreadA, hreadB]
    rcases computableBMMTracked_spec (by omega) S₁ S₂ A B with ⟨hfst, hsnd⟩
    set t := (computableBMMTracked n S₁ S₂ A B).2
    have hD_pos : 1 ≤ D_bmm c k := D_bmm_pos c k
    have hbit_sq := pointerBitOverhead_sq_mul_saving_le n (D := D_bmm c k) hD_pos
    have h_sq_bound :
        (t * (12 * (pointerBitOverhead n) ^ 2)) * 2 ^ (Nat.sqrt (Nat.log 2 n) / D_bmm_log c k) ≤
          C_bmm_log c k * n ^ 3 := by
      unfold C_bmm_log D_bmm_log
      calc
        (t * (12 * (pointerBitOverhead n) ^ 2)) * 2 ^ (Nat.sqrt (Nat.log 2 n) / (16 * D_bmm c k))
          = t * ((12 * (pointerBitOverhead n) ^ 2) *
              2 ^ (Nat.sqrt (Nat.log 2 n) / (16 * D_bmm c k))) := by ring
        _ ≤ t * ((1228800 * (D_bmm c k) ^ 4) * 2 ^ (Nat.sqrt (Nat.log 2 n) / D_bmm c k)) :=
            Nat.mul_le_mul_left t hbit_sq
        _ = (1228800 * (D_bmm c k) ^ 4) * (t * 2 ^ (Nat.sqrt (Nat.log 2 n) / D_bmm c k)) := by ring
        _ ≤ (1228800 * (D_bmm c k) ^ 4) * (C_bmm c k * n ^ 3) :=
            Nat.mul_le_mul_left _ hsnd
        _ = (1228800 * (D_bmm c k) ^ 4 * C_bmm c k) * n ^ 3 := by ring
    have h_lin_le_sq :
        (t * pointerBitOverhead n) * 2 ^ (Nat.sqrt (Nat.log 2 n) / D_bmm_log c k) ≤
          (t * (12 * (pointerBitOverhead n) ^ 2)) * 2 ^ (Nat.sqrt (Nat.log 2 n) / D_bmm_log c k) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left t (pointerBitOverhead_le_twelve_sq n))
    rcases ArithRAM.ramCountLoop_evalsToInLogCostTime_bmm n A B with
      ⟨haltCfgL, bL, hbL_le, _hr0, hr1, _hmem, hevalL⟩
    have hbL_le' : bL ≤ (n + 1) * (3 * pointerBitOverhead n) := by
      refine hbL_le.trans (Nat.mul_le_mul_left (n + 1) ?_)
      unfold pointerBitOverhead
      omega
    exact ⟨t, Prod.ext hfst rfl,
      ⟨haltCfgL, bL, hbL_le', hr1, hevalL⟩,
      h_lin_le_sq.trans h_sq_bound, h_sq_bound⟩

/-- Alias for `thm_main_bmm_log_cost_absorption`. -/
abbrev thm_main_bmm_log_cost := thm_main_bmm_log_cost_absorption

end Lemma61

#verify_standard_axioms BMMGrid.cappedABDecomposition_isValid3DDecomposition
#verify_standard_axioms BMMGrid.cappedABDecomposition_concrete_bounds
#verify_standard_axioms BMMGrid.thm_main_3d_decomposition
#verify_standard_axioms BMMGrid.computableTriangleDetection_correct
#verify_standard_axioms BMMGrid.computableTriangleDetectionTracked_spec
#verify_standard_axioms BMMGrid.thm_main_triangle_detection
#verify_standard_axioms BMMGrid.thm_main_triangle_detection_graph
#verify_standard_axioms BMMGrid.thm_main_triangle_detection_log_cost_absorption
#verify_standard_axioms BMMGrid.thm_main_triangle_detection_log_cost
#verify_standard_axioms BMMGrid.nnz_C_strictly_decreases_on_triangle
#verify_standard_axioms BMMGrid.bmmFromTriDet_correct
#verify_standard_axioms BMMGrid.lem_bmm_to_tridet_time_bound
#verify_standard_axioms BMMGrid.computableBMM_correct
#verify_standard_axioms BMMGrid.computableBMMTracked_spec
#verify_standard_axioms BMMGrid.thm_main_bmm
#verify_standard_axioms BMMGrid.thm_main_bmm_log_cost_absorption
#verify_standard_axioms BMMGrid.thm_main_bmm_log_cost

end BMMGrid
