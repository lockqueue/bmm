import BMMGrid.ObliviousSampler

/-!
# Section 4.1: Deterministic Grid-Norm Approximation (`BMMGrid/ApproxGridNorm.lean`)

This module formalizes Algorithm 2 (`ApproxGridNorm`) and Lemma 4.1
(`\label{lem:approx-grid-norm}`, `\eqref{eq:approx-grid-norm-err}`, §4.1) of
`paper.tex`:
1. List expectations `expectList` and product-space Fubini identities between `expectSet` and
   `expectList`.
2. Row neighborhood $Y_x = \{y \in Y : A(x, y) = 1\}$ (`rowNbr` / `realRowNbr`), the
   row-filtered matrix $A'_x(x', y) = A(x', y) A(x, y)$ (`rowFilteredMat` / `bmatRowFiltered`),
   and the exact scaling identity $\|A'_x\|_{U(1, d)} = \deg_A(x) \|A_x\|_{U(1, d)}$
   (`gridNorm1Pow_rowFilteredMat_eq` and `gridNorm1_rowFilteredMat_eq`, `paper.tex` §4.1).
3. Algorithm 2 (`approxGridNormU`, `approxGridNormV`, `approxGridNormVal`) and its Fubini identity
   (`approxGridNormU_eq_expectSet_expectList`, `paper.tex` §4.1).
4. Minkowski's reverse triangle inequality in $L_d$ (`abs_lpNormSet_sub_le`, `paper.tex` §4.1)
   derived from `lpNormSet_add_le` (`Defs.lean`), together with fractional-power subadditivity
   $(u + v)^{1/d} \le u^{1/d} + v^{1/d}$ (`rpow_inv_add_le`, `paper.tex` §4.1).
5. **Lemma 4.1 (`lem_approx_grid_norm` / `lem_approx_grid_norm_seq_real` / `lem_approx_grid_norm_tuple`, `paper.tex` §4.1)**:
   For any $(\varepsilon_{\text{samp}}, \delta_{\text{samp}})$-oblivious sampler $\mathcal{T}$ of $Y$
   with $\varepsilon_{\text{samp}} = \alpha_{\text{grid}} / 2$ and
   $\delta_{\text{samp}} = (\alpha_{\text{grid}} / 2)^d$, for every $x \in X$ with $\deg_A(x) > 0$,
   $$\left|v_x - \|A_x\|_{U(1, d)}\right| \le \frac{\alpha_{\text{grid}}}{\deg_A(x)}.$$
6. Cost-tracked implementation `approxGridNormVxRowPairTracked` in `CostM`, routing the $d$-th
   powers and the four rational-pair products through `powNatTracked` and `mulNatTracked`; the
   two table-contraction accumulators are unit-charged (`FORMALIZATION.tex` Class B).
-/

namespace BMMGrid

open scoped BigOperators Classical

/-!
## 1. Uniform Expectations over Lists (`expectList`) and Fubini Identities
-/

section ListExpectations

variable {α β γ : Type*}

/-- Uniform expectation $\mathbb{E}_{x \in L}[f(x)] = \frac{1}{|L|} \sum_{x \in L} f(x)$ over a
list `L : List α` (returning `0` if `L = []`). -/
noncomputable def expectList (L : List α) (f : α → ℝ) : ℝ :=
  (L.map f).sum / (L.length : ℝ)

lemma list_map_sum_const (L : List α) (c : ℝ) :
    (L.map (fun _ => c)).sum = (L.length : ℝ) * c := by
  induction L with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.cast_add, Nat.cast_one]
    ring

lemma expectList_const {L : List α} (hL : L ≠ []) (c : ℝ) :
    expectList L (fun _ => c) = c := by
  unfold expectList
  rw [list_map_sum_const]
  have hlen : (L.length : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (List.length_pos_iff.mpr hL).ne'
  exact mul_div_cancel_left₀ c hlen

lemma list_map_sum_nonneg {L : List α} {f : α → ℝ} (hf : ∀ x ∈ L, 0 ≤ f x) :
    0 ≤ (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_nonneg (hf a List.mem_cons_self)
      (ih (fun x hx => hf x (List.mem_cons_of_mem a hx)))

lemma expectList_nonneg {L : List α} {f : α → ℝ} (hf : ∀ x ∈ L, 0 ≤ f x) :
    0 ≤ expectList L f := by
  unfold expectList
  exact div_nonneg (list_map_sum_nonneg hf) (Nat.cast_nonneg _)

lemma list_map_sum_le_sum {L : List α} {f g : α → ℝ} (h : ∀ x ∈ L, f x ≤ g x) :
    (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a List.mem_cons_self)
      (ih (fun x hx => h x (List.mem_cons_of_mem a hx)))

lemma expectList_mono {L : List α} {f g : α → ℝ} (h : ∀ x ∈ L, f x ≤ g x) :
    expectList L f ≤ expectList L g := by
  unfold expectList
  exact div_le_div_of_nonneg_right (list_map_sum_le_sum h) (Nat.cast_nonneg _)

lemma list_map_sum_add (L : List α) (f g : α → ℝ) :
    (L.map (fun x => f x + g x)).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

lemma expectList_add (L : List α) (f g : α → ℝ) :
    expectList L (fun x => f x + g x) = expectList L f + expectList L g := by
  unfold expectList
  rw [list_map_sum_add, add_div]

/-- Correspondence between `List.sum` of a mapped list and `Finset.sum` over `Fin L.length`. -/
theorem list_map_sum_eq_sum_fin (L : List γ) (F : γ → ℝ) :
    (L.map F).sum = ∑ i : Fin L.length, F (L.get i) := by
  induction L with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Fin.sum_univ_succ,
      List.get_cons_zero, ih]
    rfl

/-- Any `expectList L F` equals `expectSet Finset.univ (fun i : Fin L.length => F (L.get i))`. -/
theorem expectList_eq_expectSet_fin (L : List γ) (F : γ → ℝ) :
    expectList L F = expectSet (Finset.univ : Finset (Fin L.length)) (fun i => F (L.get i)) := by
  unfold expectList expectSet
  rw [list_map_sum_eq_sum_fin, Finset.card_univ, Fintype.card_fin]

/-- Fubini's theorem between `expectList` and `expectSet`:
$\mathbb{E}_{T \in L} \mathbb{E}_{x \in X}[f(x, T)] = \mathbb{E}_{x \in X} \mathbb{E}_{T \in L}[f(x, T)]$. -/
theorem expectList_expectSet_comm (L : List γ) (X : Finset α) (f : α → γ → ℝ) :
    expectList L (fun T => expectSet X (fun x => f x T)) =
      expectSet X (fun x => expectList L (fun T => f x T)) := by
  rw [expectList_eq_expectSet_fin]
  simp_rw [expectList_eq_expectSet_fin]
  exact expectSet_comm (Finset.univ : Finset (Fin L.length)) X (fun i x => f x (L.get i))

/-- Product-space representation of an iterated expectation over `X : Finset α` and `L : List γ`:
$\mathbb{E}_{x \in X} \mathbb{E}_{T \in L}[F(x, T)] = \mathbb{E}_{(x, i) \in X \times \text{Fin } |L|}[F(x, L[i])]$. -/
theorem expectSet_expectList_eq_expectSet_prod (X : Finset α) (L : List γ)
    (F : α → γ → ℝ) :
    expectSet X (fun x => expectList L (fun T => F x T)) =
      expectSet (X ×ˢ (Finset.univ : Finset (Fin L.length)))
        (fun p => F p.1 (L.get p.2)) := by
  unfold expectSet
  simp_rw [expectList_eq_expectSet_fin]
  unfold expectSet
  rw [← Finset.sum_div, div_div, Finset.card_product, Finset.card_univ, Fintype.card_fin,
    Nat.cast_mul, mul_comm (L.length : ℝ) (X.card : ℝ), Finset.sum_product]

/-- Sum of an indicator `(if p x then 1 else 0)` over a list equals the length of `L.filter p`. -/
lemma list_map_ite_one_zero_sum (L : List γ) (p : γ → Bool) :
    (L.map (fun x => if p x then (1 : ℝ) else 0)).sum = ((L.filter p).length : ℝ) := by
  induction L with
  | nil => simp
  | cons a tl ih =>
    cases hp : p a <;> simp [hp, ih, add_comm]

/-- Average of an indicator `(if p x then 1 else 0)` over a non-empty list is bounded by `δ`
whenever `(L.filter p).length ≤ δ * L.length`. -/
lemma expectList_ite_le_of_filter_length_le {L : List γ} (hL : L ≠ [])
    (p : γ → Bool) {δ : ℝ} (hδ : ((L.filter p).length : ℝ) ≤ δ * (L.length : ℝ)) :
    expectList L (fun x => if p x then (1 : ℝ) else 0) ≤ δ := by
  unfold expectList
  rw [list_map_ite_one_zero_sum]
  have hlen : (0 : ℝ) < (L.length : ℝ) := Nat.cast_pos.mpr (List.length_pos_iff.mpr hL)
  exact (div_le_iff₀ hlen).mpr hδ

lemma expectSet_mul_const (S : Finset α) (f : α → ℝ) (c : ℝ) :
    expectSet S (fun x => f x * c) = expectSet S f * c := by
  have h : (fun x => f x * c) = (fun x => c * f x) := by ext x; ring
  rw [h, expectSet_smul, mul_comm]

end ListExpectations

/-!
## 2. Row-Filtered Matrix $A'_x$ and Exact Grid-Norm Scaling Identity (`paper.tex` §4.1)
-/

section RowFilteredMatrix

variable {α β : Type*}

/-- Specialized $(1, d)$-grid norm $\|M\|_{U(1, d)} = (\|M\|_{U(1, d)}^d)^{1/d}$
(`paper.tex` §4.1). -/
noncomputable def gridNorm1 (X : Finset α) (Y : Finset β) (M : α → β → ℝ) (d : ℕ) : ℝ :=
  (gridNorm1Pow X Y M d) ^ (1 / (d : ℝ))

/-- Equivalence between `gridNorm1Pow X Y M d` and `gridNormPow X Y M 1 d`. -/
theorem gridNorm1Pow_eq_gridNormPow_one (X : Finset α) (Y : Finset β) (M : α → β → ℝ) (d : ℕ) :
    gridNorm1Pow X Y M d = gridNormPow X Y M 1 d := by
  unfold gridNorm1Pow gridNormPow rowDeg
  have h := expectSet_pow_eq_piFinset X (fun x => (expectSet Y (fun y => M x y)) ^ d) 1
  rw [pow_one] at h
  rw [h]
  congr 1
  ext xs
  rw [Fin.prod_univ_one]
  congr 1
  unfold expectSet
  congr 1
  refine Finset.sum_congr rfl (fun y _ => ?_)
  dsimp only
  rw [Fin.prod_univ_one]

/-- Equivalence between `gridNorm1 X Y M d` and `gridNorm X Y M 1 d`. -/
theorem gridNorm1_eq_gridNorm_one (X : Finset α) (Y : Finset β) (M : α → β → ℝ) (d : ℕ) :
    gridNorm1 X Y M d = gridNorm X Y M 1 d := by
  unfold gridNorm1 gridNorm
  rw [gridNorm1Pow_eq_gridNormPow_one, one_mul]

/-- Predicate that a real matrix $M : \alpha \to \beta \to \mathbb{R}$ takes values in $\{0, 1\}$. -/
def IsBinaryRealMat (M : α → β → ℝ) : Prop :=
  ∀ x y, M x y = 0 ∨ M x y = 1

lemma isBinaryRealMat_bmatToReal (A : α → β → Bool) : IsBinaryRealMat (bmatToReal A) := by
  intro x y
  unfold bmatToReal boolToReal
  cases A x y <;> simp

lemma isBinaryRealMat_nonneg {M : α → β → ℝ} (hM : IsBinaryRealMat M) (x : α) (y : β) :
    0 ≤ M x y := by
  rcases hM x y with h0 | h1 <;> linarith

lemma isBinaryRealMat_le_one {M : α → β → ℝ} (hM : IsBinaryRealMat M) (x : α) (y : β) :
    M x y ≤ 1 := by
  rcases hM x y with h0 | h1 <;> linarith

/-- Row neighborhood $Y_x := \{y \in Y : A(x, y) = \text{true}\}$ of a row $x$ in a Boolean
matrix $A$ (`paper.tex` §3.3 & §4.1). -/
def rowNbr (Y : Finset β) (A : α → β → Bool) (x : α) : Finset β :=
  Y.filter (fun y => A x y = true)

/-- Row neighborhood $Y_x := \{y \in Y : M(x, y) = 1\}$ of a row $x$ in a real matrix $M$. -/
noncomputable def realRowNbr (Y : Finset β) (M : α → β → ℝ) (x : α) : Finset β :=
  Y.filter (fun y => M x y = 1)

lemma realRowNbr_bmatToReal (Y : Finset β) (A : α → β → Bool) (x : α) :
    realRowNbr Y (bmatToReal A) x = rowNbr Y A x := by
  unfold realRowNbr rowNbr bmatToReal boolToReal
  ext y
  simp only [Finset.mem_filter]
  constructor <;> intro ⟨hy, h⟩ <;> refine ⟨hy, ?_⟩
  · cases hA : A x y
    · simp [hA] at h
    · rfl
  · simp [h]

/-- Row-filtered real matrix $A'_x(x', y) := M(x', y) \cdot M(x, y)$ on the full column set $Y$
(`paper.tex` Lemma 4.1 proof, §4.1). -/
def rowFilteredMat (M : α → β → ℝ) (x : α) (x' : α) (y : β) : ℝ :=
  M x' y * M x y

/-- Row-filtered Boolean matrix $A'_x(x', y) := A(x', y) \wedge A(x, y)$. -/
def bmatRowFiltered (A : α → β → Bool) (x : α) (x' : α) (y : β) : Bool :=
  A x' y && A x y

lemma bmatToReal_bmatRowFiltered (A : α → β → Bool) (x : α) :
    bmatToReal (bmatRowFiltered A x) = rowFilteredMat (bmatToReal A) x := by
  ext x' y
  by_cases h1 : A x' y = true <;> by_cases h2 : A x y = true <;>
    simp [bmatToReal, boolToReal, bmatRowFiltered, rowFilteredMat, h1, h2]

/-- For a binary real matrix $M$, $\sum_{y \in Y} M(x, y) = |Y_x|$. -/
lemma sum_eq_card_realRowNbr (Y : Finset β) {M : α → β → ℝ} (hM : IsBinaryRealMat M) (x : α) :
    ∑ y ∈ Y, M x y = ((realRowNbr Y M x).card : ℝ) := by
  have hite : ∀ y ∈ Y, M x y = if M x y = 1 then (1 : ℝ) else 0 := by
    intro y _
    rcases hM x y with h | h <;> simp [h]
  rw [Finset.sum_congr rfl hite, Finset.sum_boole]
  rfl

/-- For a binary real matrix $M$, $\deg_M(x) = |Y_x| / |Y|$. -/
theorem rowDeg_eq_card_realRowNbr_div (Y : Finset β) {M : α → β → ℝ} (hM : IsBinaryRealMat M)
    (x : α) :
    rowDeg Y M x = ((realRowNbr Y M x).card : ℝ) / (Y.card : ℝ) := by
  unfold rowDeg expectSet
  rw [sum_eq_card_realRowNbr Y hM x]

/-- For a Boolean matrix $A$, $\deg_A(x) = |Y_x| / |Y|$. -/
theorem rowDeg_bmatToReal_eq_card_rowNbr_div (Y : Finset β) (A : α → β → Bool) (x : α) :
    rowDeg Y (bmatToReal A) x = ((rowNbr Y A x).card : ℝ) / (Y.card : ℝ) := by
  rw [rowDeg_eq_card_realRowNbr_div Y (isBinaryRealMat_bmatToReal A) x, realRowNbr_bmatToReal]

/-- For a binary real matrix $M$, $\sum_{y \in Y} A'_x(x', y) = \sum_{y \in Y_x} M(x', y)$. -/
theorem sum_rowFilteredMat_eq_sum_realRowNbr (Y : Finset β) {M : α → β → ℝ}
    (hM : IsBinaryRealMat M) (x x' : α) :
    ∑ y ∈ Y, rowFilteredMat M x x' y = ∑ y ∈ realRowNbr Y M x, M x' y := by
  unfold realRowNbr
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  unfold rowFilteredMat
  rcases hM x y with h | h <;> simp [h]

/-- Exact row-degree scaling identity:
$\deg_{A'_x, Y}(x') = \deg_{M, Y}(x) \cdot \deg_{M, Y_x}(x')$
(`paper.tex` Lemma 4.1 proof, §4.1). -/
theorem rowDeg_rowFilteredMat_eq (Y : Finset β) {M : α → β → ℝ} (hM : IsBinaryRealMat M)
    (x x' : α) :
    rowDeg Y (rowFilteredMat M x) x' =
      rowDeg Y M x * rowDeg (realRowNbr Y M x) M x' := by
  rw [rowDeg_eq_card_realRowNbr_div Y hM x]
  unfold rowDeg expectSet
  rw [sum_rowFilteredMat_eq_sum_realRowNbr Y hM x x']
  by_cases hcard : (realRowNbr Y M x).card = 0
  · have hemp : realRowNbr Y M x = ∅ := Finset.card_eq_zero.mp hcard
    simp [hemp]
  · have hcardR : ((realRowNbr Y M x).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hcard
    rw [div_mul_div_comm, mul_comm ((realRowNbr Y M x).card : ℝ),
      mul_div_mul_right _ _ hcardR]

/-- **`paper.tex` §4.1**: Exact scaling identity for the $(1, d)$-grid norm power of the
row-filtered matrix $A'_x$:
$$\|A'_x\|_{U(1, d)}^d = (\deg_M(x))^d \cdot \|M[X, Y_x]\|_{U(1, d)}^d.$$ -/
theorem gridNorm1Pow_rowFilteredMat_eq (X : Finset α) (Y : Finset β) {M : α → β → ℝ}
    (hM : IsBinaryRealMat M) (x : α) (d : ℕ) :
    gridNorm1Pow X Y (rowFilteredMat M x) d =
      (rowDeg Y M x) ^ d * gridNorm1Pow X (realRowNbr Y M x) M d := by
  unfold gridNorm1Pow
  have hfun : (fun x' => (rowDeg Y (rowFilteredMat M x) x') ^ d) =
      (fun x' => (rowDeg Y M x) ^ d * (rowDeg (realRowNbr Y M x) M x') ^ d) := by
    ext x'
    rw [rowDeg_rowFilteredMat_eq Y hM x x', mul_pow]
  rw [hfun, expectSet_smul]

lemma rowDeg_nonneg_of_nonneg (Y : Finset β) {M : α → β → ℝ}
    (hM : ∀ x y, 0 ≤ M x y) (x : α) :
    0 ≤ rowDeg Y M x :=
  expectSet_nonneg (fun y _ => hM x y)

lemma gridNorm1Pow_nonneg_of_nonneg (X : Finset α) (Y : Finset β) {M : α → β → ℝ}
    (hM : ∀ x y, 0 ≤ M x y) (d : ℕ) :
    0 ≤ gridNorm1Pow X Y M d :=
  expectSet_nonneg (fun x _ => pow_nonneg (rowDeg_nonneg_of_nonneg Y hM x) d)

lemma pow_rpow_inv_natCast {a : ℝ} (ha : 0 ≤ a) {d : ℕ} (hd : 1 ≤ d) :
    (a ^ d) ^ (1 / (d : ℝ)) = a := by
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [← Real.rpow_natCast a d, ← Real.rpow_mul ha, mul_one_div_cancel hd0, Real.rpow_one]

/-- **`paper.tex` §4.1**: Exact scaling identity for the $(1, d)$-grid norm of the row-filtered
matrix $A'_x$:
$$\|A'_x\|_{U(1, d)} = \deg_M(x) \cdot \|M[X, Y_x]\|_{U(1, d)}.$$ -/
theorem gridNorm1_rowFilteredMat_eq (X : Finset α) (Y : Finset β) {M : α → β → ℝ}
    (hM : IsBinaryRealMat M) (x : α) {d : ℕ} (hd : 1 ≤ d) :
    gridNorm1 X Y (rowFilteredMat M x) d =
      rowDeg Y M x * gridNorm1 X (realRowNbr Y M x) M d := by
  unfold gridNorm1
  rw [gridNorm1Pow_rowFilteredMat_eq X Y hM x d]
  have hdeg : 0 ≤ rowDeg Y M x := rowDeg_nonneg_of_nonneg Y (isBinaryRealMat_nonneg hM) x
  have hgn : 0 ≤ gridNorm1Pow X (realRowNbr Y M x) M d :=
    gridNorm1Pow_nonneg_of_nonneg X (realRowNbr Y M x) (isBinaryRealMat_nonneg hM) d
  rw [Real.mul_rpow (pow_nonneg hdeg d) hgn, pow_rpow_inv_natCast hdeg hd]

end RowFilteredMatrix

/-!
## 3. Algorithm 2 (`ApproxGridNorm`) Specification and Fubini Identity (`paper.tex` §4.1)
-/

section ApproxGridNormSpec

variable {α β : Type*}

/-- Line 2 of Algorithm 2 (`paper.tex` §4.1):
$u_{T, y_1, \dots, y_d} := \mathbb{E}_{x' \in X}\!\left[\prod_{j=1}^d M(x', y_j)\right]$. -/
noncomputable def approxGridNormTupleAvg (X : Finset α) (M : α → β → ℝ) (d : ℕ)
    (ys : Fin d → β) : ℝ :=
  expectSet X (fun x' => ∏ j : Fin d, M x' (ys j))

/-- Line 3 of Algorithm 2 (`paper.tex` §4.1):
$U_x := \mathbb{E}_{T \in \mathcal{T}} \mathbb{E}_{(y_1, \dots, y_d) \in T^d}\!\left[
  u_{T, y_1, \dots, y_d} \cdot \prod_{j=1}^d M(x, y_j)\right]$. -/
noncomputable def approxGridNormU (X : Finset α) (T_fam : List (Finset β))
    (M : α → β → ℝ) (d : ℕ) (x : α) : ℝ :=
  expectList T_fam (fun T =>
    expectSet (Fintype.piFinset (fun _ : Fin d => T)) (fun ys =>
      approxGridNormTupleAvg X M d ys * ∏ j : Fin d, M x (ys j)))

/-- Line 3 of Algorithm 2 (`paper.tex` §4.1):
$V_x := U_x / (\deg_M(x))^d$. -/
noncomputable def approxGridNormV (X : Finset α) (Y : Finset β) (T_fam : List (Finset β))
    (M : α → β → ℝ) (d : ℕ) (x : α) : ℝ :=
  approxGridNormU X T_fam M d x / (rowDeg Y M x) ^ d

/-- The $d$-th root $u_x := U_x^{1/d}$ (`paper.tex` §4.1). -/
noncomputable def approxGridNormURoot (X : Finset α) (T_fam : List (Finset β))
    (M : α → β → ℝ) (d : ℕ) (x : α) : ℝ :=
  (approxGridNormU X T_fam M d x) ^ (1 / (d : ℝ))

/-- The $d$-th root $v_x := V_x^{1/d}$ of Algorithm 2's output $V_x$ (`paper.tex` Lemma 4.1, §4.1). -/
noncomputable def approxGridNormVal (X : Finset α) (Y : Finset β) (T_fam : List (Finset β))
    (M : α → β → ℝ) (d : ℕ) (x : α) : ℝ :=
  (approxGridNormV X Y T_fam M d x) ^ (1 / (d : ℝ))

/-- **`paper.tex` §4.1**: Fubini's theorem for $U_x$ in Algorithm 2:
$$U_x = \mathbb{E}_{x' \in X} \mathbb{E}_{T \in \mathcal{T}}\!\left[\left(\mathbb{E}_{y \in T} A'_x(x', y)\right)^d\right].$$ -/
theorem approxGridNormU_eq_expectSet_expectList (X : Finset α) (T_fam : List (Finset β))
    (M : α → β → ℝ) (d : ℕ) (x : α) :
    approxGridNormU X T_fam M d x =
      expectSet X (fun x' =>
        expectList T_fam (fun T => (rowDeg T (rowFilteredMat M x) x') ^ d)) := by
  unfold approxGridNormU approxGridNormTupleAvg
  have hinner : ∀ T : Finset β,
      expectSet (Fintype.piFinset (fun _ : Fin d => T)) (fun ys =>
        expectSet X (fun x' => ∏ j : Fin d, M x' (ys j)) * ∏ j : Fin d, M x (ys j)) =
      expectSet X (fun x' => (rowDeg T (rowFilteredMat M x) x') ^ d) := by
    intro T
    have hmul : (fun ys : Fin d → β =>
        expectSet X (fun x' => ∏ j : Fin d, M x' (ys j)) * ∏ j : Fin d, M x (ys j)) =
        (fun ys : Fin d → β =>
          expectSet X (fun x' => ∏ j : Fin d, rowFilteredMat M x x' (ys j))) := by
      ext ys
      rw [← expectSet_mul_const]
      congr 1
      ext x'
      rw [← Finset.prod_mul_distrib]
      rfl
    rw [hmul, expectSet_comm]
    congr 1
    ext x'
    rw [expectSet_piFinset_prod T d (fun _ y => rowFilteredMat M x x' y),
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rfl
  simp_rw [hinner]
  exact expectList_expectSet_comm T_fam X _

lemma approxGridNormU_nonneg (X : Finset α) (T_fam : List (Finset β))
    {M : α → β → ℝ} (hM : ∀ x y, 0 ≤ M x y) (d : ℕ) (x : α) :
    0 ≤ approxGridNormU X T_fam M d x := by
  rw [approxGridNormU_eq_expectSet_expectList]
  refine expectSet_nonneg (fun x' _ => expectList_nonneg (fun T _ => ?_))
  refine pow_nonneg (rowDeg_nonneg_of_nonneg T ?_ x') d
  intro x₁ y₁
  exact mul_nonneg (hM x₁ y₁) (hM x y₁)

lemma approxGridNormV_nonneg (X : Finset α) (Y : Finset β) (T_fam : List (Finset β))
    {M : α → β → ℝ} (hM : ∀ x y, 0 ≤ M x y) (d : ℕ) (x : α) :
    0 ≤ approxGridNormV X Y T_fam M d x := by
  unfold approxGridNormV
  exact div_nonneg (approxGridNormU_nonneg X T_fam hM d x)
    (pow_nonneg (rowDeg_nonneg_of_nonneg Y hM x) d)

/-- Relation $v_x = u_x / \deg_M(x)$ (`paper.tex` §4.1). -/
theorem approxGridNormVal_eq_div (X : Finset α) (Y : Finset β) (T_fam : List (Finset β))
    {M : α → β → ℝ} (hM : ∀ x y, 0 ≤ M x y) {d : ℕ} (hd : 1 ≤ d) (x : α) :
    approxGridNormVal X Y T_fam M d x =
      approxGridNormURoot X T_fam M d x / rowDeg Y M x := by
  unfold approxGridNormVal approxGridNormV approxGridNormURoot
  have hU : 0 ≤ approxGridNormU X T_fam M d x := approxGridNormU_nonneg X T_fam hM d x
  have hdeg : 0 ≤ rowDeg Y M x := rowDeg_nonneg_of_nonneg Y hM x
  rw [Real.div_rpow hU (pow_nonneg hdeg d), pow_rpow_inv_natCast hdeg hd]

end ApproxGridNormSpec

/-!
## 4. Minkowski Reverse Triangle Inequality in $L_d$ and Root Subadditivity (`paper.tex` §4.1)
-/

section MinkowskiAndRoots

variable {ι : Type*}

/-- Elementary superadditivity $a^d + b^d \le (a + b)^d$ for $a, b \ge 0$ and $d \ge 1$. -/
lemma add_pow_le_pow_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {d : ℕ} (hd : 1 ≤ d) :
    a ^ d + b ^ d ≤ (a + b) ^ d := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hd
  induction m with
  | zero =>
    simp
  | succ m ih =>
    have hm1 : 1 ≤ 1 + m := by omega
    have ih' := ih hm1
    have hpow_a : 0 ≤ a ^ (1 + m) := pow_nonneg ha (1 + m)
    have hpow_b : 0 ≤ b ^ (1 + m) := pow_nonneg hb (1 + m)
    have hexp : 1 + (m + 1) = (1 + m) + 1 := by omega
    rw [hexp, pow_succ, pow_succ, pow_succ]
    nlinarith

/-- **`paper.tex` §4.1**: Subadditivity of the $d$-th root:
$$(u + v)^{1/d} \le u^{1/d} + v^{1/d}$$
for $u, v \ge 0$ and integer $d \ge 1$. -/
theorem rpow_inv_add_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) {d : ℕ} (hd : 1 ≤ d) :
    (u + v) ^ (1 / (d : ℝ)) ≤ u ^ (1 / (d : ℝ)) + v ^ (1 / (d : ℝ)) := by
  let a := u ^ (1 / (d : ℝ))
  let b := v ^ (1 / (d : ℝ))
  have ha : 0 ≤ a := Real.rpow_nonneg hu _
  have hb : 0 ≤ b := Real.rpow_nonneg hv _
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have had : a ^ d = u := by
    rw [← Real.rpow_natCast a d, ← Real.rpow_mul hu, one_div_mul_cancel hd0, Real.rpow_one]
  have hbd : b ^ d = v := by
    rw [← Real.rpow_natCast b d, ← Real.rpow_mul hv, one_div_mul_cancel hd0, Real.rpow_one]
  have huv : u + v ≤ (a + b) ^ d := by
    rw [← had, ← hbd]
    exact add_pow_le_pow_add ha hb hd
  calc
    (u + v) ^ (1 / (d : ℝ)) ≤ ((a + b) ^ d) ^ (1 / (d : ℝ)) :=
      Real.rpow_le_rpow (add_nonneg hu hv) huv (by positivity)
    _ = a + b := pow_rpow_inv_natCast (add_nonneg ha hb) hd

lemma lpNormSet_sub_comm (s : Finset ι) (d : ℕ) (f g : ι → ℝ) :
    lpNormSet s d (fun i => f i - g i) = lpNormSet s d (fun i => g i - f i) := by
  unfold lpNormSet expectSet
  congr 2
  refine Finset.sum_congr rfl (fun i _ => ?_)
  dsimp only
  rw [abs_sub_comm]

/-- **`paper.tex` §4.1**: Minkowski's reverse triangle inequality in $L_d(s)$:
$$\Big|\|a\|_{L_d(s)} - \|b\|_{L_d(s)}\Big| \le \|a - b\|_{L_d(s)}.$$ -/
theorem abs_lpNormSet_sub_le (s : Finset ι) {d : ℕ} (hd : 1 ≤ d) (a b : ι → ℝ) :
    |lpNormSet s d a - lpNormSet s d b| ≤ lpNormSet s d (fun i => a i - b i) := by
  rw [abs_sub_le_iff]
  constructor
  · have h1 := lpNormSet_add_le s hd b (fun i => a i - b i)
    have hfun : (fun i => b i + (a i - b i)) = a := by ext i; ring
    rw [hfun] at h1
    linarith
  · have h2 := lpNormSet_add_le s hd a (fun i => b i - a i)
    have hfun : (fun i => a i + (b i - a i)) = b := by ext i; ring
    rw [hfun, lpNormSet_sub_comm s d b a] at h2
    linarith

end MinkowskiAndRoots

/-!
## 5. Sampler Moment Bound and Proof of Lemma 4.1 (`lem_approx_grid_norm`, `paper.tex` §4.1)
-/

section LemmaApproxGridNorm

variable {α β : Type*}

lemma expectSet_mem_unit_interval (S : Finset β) {g : β → ℝ}
    (hg : ∀ y ∈ S, 0 ≤ g y ∧ g y ≤ 1) :
    0 ≤ expectSet S g ∧ expectSet S g ≤ 1 := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp [expectSet]
  · exact ⟨expectSet_nonneg (fun y hy => (hg y hy).1),
      expectSet_le_of_le hS (fun y hy => (hg y hy).2)⟩

lemma abs_sub_le_one_of_unit_interval {p q : ℝ}
    (hp : 0 ≤ p ∧ p ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1) :
    |p - q| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith

/-!
### Set-Sampler (`IsObliviousSampler`) Variants of Lemma 4.1 (`paper.tex` §4.1)

*Note*: The following five lemmas (`expectList_abs_sub_pow_le_of_isObliviousSampler` through
`lem_approx_grid_norm`) prove Lemma 4.1 for set-based samplers `T_fam : List (Finset β)`
(`IsObliviousSampler`). The sequence-sampler (`IsSeqSampler`, `List (List β)`) instantiation used
by `concreteApproxGridNormVTracked` in `MinDegreeAndDyadicSift.lean` and the headline theorem
pipeline (`thm_main_3d_decomposition` / `thm_main_triangle_detection` / `thm_main_bmm`) follows in
the next subsection.
-/

/-- **`paper.tex` §4.1** (Set-sampler `IsObliviousSampler` variant; see
`expectList_abs_sub_pow_le_of_isSeqSampler` below for the sequence-sampler version on the
headline path): For any $(\varepsilon_{\text{samp}}, \delta_{\text{samp}})$-oblivious
sampler `T_fam` of `Y` and any $g : \beta \to [0, 1]$,
$$\mathbb{E}_{T \in \mathcal{T}}\!\left[\left|\mathbb{E}_{y \in T}[g(y)] - \mathbb{E}_{y \in Y}[g(y)]\right|^d\right]
  \le \varepsilon_{\text{samp}}^d + \delta_{\text{samp}}.$$ -/
theorem expectList_abs_sub_pow_le_of_isObliviousSampler
    {Y : Finset β} {T_fam : List (Finset β)} {ε_samp δ_samp : ℝ}
    (hS : IsObliviousSampler Y T_fam ε_samp δ_samp) (hε : 0 ≤ ε_samp)
    (d : ℕ) (g : β → ℝ) (hg : ∀ y ∈ Y, 0 ≤ g y ∧ g y ≤ 1) :
    expectList T_fam (fun T => |expectSet T g - expectSet Y g| ^ d) ≤
      ε_samp ^ d + δ_samp := by
  let p : Finset β → Bool := fun T => decide (|expectSet T g - expectSet Y g| > ε_samp)
  have hpt : ∀ T ∈ T_fam,
      |expectSet T g - expectSet Y g| ^ d ≤
        ε_samp ^ d + (if p T then (1 : ℝ) else 0) := by
    intro T hT
    have hT_sub : T ⊆ Y := (hS.2.1 T hT).1
    have hT_unit := expectSet_mem_unit_interval T (fun y hy => hg y (hT_sub hy))
    have hY_unit := expectSet_mem_unit_interval Y hg
    have habs_le_one : |expectSet T g - expectSet Y g| ≤ 1 :=
      abs_sub_le_one_of_unit_interval hT_unit hY_unit
    by_cases hgt : |expectSet T g - expectSet Y g| > ε_samp
    · have hpT : p T = true := decide_eq_true hgt
      simp only [hpT, ↓reduceIte]
      have hpow1 : |expectSet T g - expectSet Y g| ^ d ≤ 1 := by
        calc
          |expectSet T g - expectSet Y g| ^ d ≤ (1 : ℝ) ^ d :=
            pow_le_pow_left₀ (abs_nonneg _) habs_le_one d
          _ = 1 := one_pow d
      have hε_pow : 0 ≤ ε_samp ^ d := pow_nonneg hε d
      linarith
    · have hpT : p T = false := decide_eq_false hgt
      simp only [hpT, Bool.false_eq_true, ↓reduceIte, add_zero]
      have hle : |expectSet T g - expectSet Y g| ≤ ε_samp := not_lt.mp hgt
      exact pow_le_pow_left₀ (abs_nonneg _) hle d
  have hite_le := expectList_ite_le_of_filter_length_le hS.1 p (hS.2.2 g hg)
  calc
    expectList T_fam (fun T => |expectSet T g - expectSet Y g| ^ d)
      ≤ expectList T_fam (fun T => ε_samp ^ d + (if p T then (1 : ℝ) else 0)) :=
        expectList_mono hpt
    _ = expectList T_fam (fun _ => ε_samp ^ d) +
          expectList T_fam (fun T => if p T then (1 : ℝ) else 0) :=
        expectList_add T_fam _ _
    _ = ε_samp ^ d + expectList T_fam (fun T => if p T then (1 : ℝ) else 0) := by
        rw [expectList_const hS.1]
    _ ≤ ε_samp ^ d + δ_samp := by linarith

/-- **`paper.tex` §4.1**: Unnormalized $L_d(X \times \mathcal{T})$ approximation bound
between $u_x = U_x^{1/d}$ and $\|A'_x\|_{U(1, d)}$:
$$\left|u_x - \|A'_x\|_{U(1, d)}\right| \le \varepsilon_{\text{samp}} + \delta_{\text{samp}}^{1/d}.$$ -/
theorem abs_approxGridNormURoot_sub_gridNorm1_rowFilteredMat_le
    {X : Finset α} (hX : X.Nonempty) {Y : Finset β} {T_fam : List (Finset β)}
    {ε_samp δ_samp : ℝ} (hS : IsObliviousSampler Y T_fam ε_samp δ_samp)
    (hε : 0 ≤ ε_samp) (hδ : 0 ≤ δ_samp)
    {M : α → β → ℝ} (hM : ∀ x y, 0 ≤ M x y ∧ M x y ≤ 1)
    {d : ℕ} (hd : 1 ≤ d) (x : α) :
    |approxGridNormURoot X T_fam M d x - gridNorm1 X Y (rowFilteredMat M x) d| ≤
      ε_samp + δ_samp ^ (1 / (d : ℝ)) := by
  let S := X ×ˢ (Finset.univ : Finset (Fin T_fam.length))
  let a : α × Fin T_fam.length → ℝ :=
    fun p => rowDeg (T_fam.get p.2) (rowFilteredMat M x) p.1
  let b : α × Fin T_fam.length → ℝ :=
    fun p => rowDeg Y (rowFilteredMat M x) p.1
  have hM_filt_nonneg : ∀ x' y, 0 ≤ rowFilteredMat M x x' y :=
    fun x' y => mul_nonneg (hM x' y).1 (hM x y).1
  have ha_eq : lpNormSet S d a = approxGridNormURoot X T_fam M d x := by
    unfold lpNormSet approxGridNormURoot
    congr 1
    rw [approxGridNormU_eq_expectSet_expectList,
      expectSet_expectList_eq_expectSet_prod X T_fam
        (fun x' T => (rowDeg T (rowFilteredMat M x) x') ^ d)]
    congr 1
    ext p
    have ha_nonneg : 0 ≤ a p := rowDeg_nonneg_of_nonneg (T_fam.get p.2) hM_filt_nonneg p.1
    rw [abs_of_nonneg ha_nonneg]
  have hb_eq : lpNormSet S d b = gridNorm1 X Y (rowFilteredMat M x) d := by
    unfold lpNormSet gridNorm1 gridNorm1Pow
    congr 1
    have hconst : expectSet X (fun x' => (rowDeg Y (rowFilteredMat M x) x') ^ d) =
        expectSet X (fun x' => expectList T_fam (fun _ => (rowDeg Y (rowFilteredMat M x) x') ^ d)) := by
      congr 1
      ext x'
      rw [expectList_const hS.1]
    rw [hconst, expectSet_expectList_eq_expectSet_prod X T_fam
      (fun x' _ => (rowDeg Y (rowFilteredMat M x) x') ^ d)]
    congr 1
    ext p
    have hb_nonneg : 0 ≤ b p := rowDeg_nonneg_of_nonneg Y hM_filt_nonneg p.1
    rw [abs_of_nonneg hb_nonneg]
  have hdiff_pow : expectSet S (fun p => |a p - b p| ^ d) ≤ ε_samp ^ d + δ_samp := by
    rw [← expectSet_expectList_eq_expectSet_prod X T_fam
      (fun x' T => |rowDeg T (rowFilteredMat M x) x' - rowDeg Y (rowFilteredMat M x) x'| ^ d)]
    refine expectSet_le_of_le hX (fun x' _ => ?_)
    refine expectList_abs_sub_pow_le_of_isObliviousSampler hS hε d
      (fun y => rowFilteredMat M x x' y) (fun y _ => ?_)
    refine ⟨hM_filt_nonneg x' y, ?_⟩
    unfold rowFilteredMat
    calc
      M x' y * M x y ≤ 1 * 1 :=
        mul_le_mul (hM x' y).2 (hM x y).2 (hM x y).1 zero_le_one
      _ = 1 := one_mul 1
  have hdiff_norm : lpNormSet S d (fun p => a p - b p) ≤ ε_samp + δ_samp ^ (1 / (d : ℝ)) := by
    unfold lpNormSet
    calc
      (expectSet S (fun p => |a p - b p| ^ d)) ^ (1 / (d : ℝ))
        ≤ (ε_samp ^ d + δ_samp) ^ (1 / (d : ℝ)) :=
          Real.rpow_le_rpow (expectSet_nonneg (fun _ _ => pow_nonneg (abs_nonneg _) d))
            hdiff_pow (by positivity)
      _ ≤ (ε_samp ^ d) ^ (1 / (d : ℝ)) + δ_samp ^ (1 / (d : ℝ)) :=
          rpow_inv_add_le (pow_nonneg hε d) hδ hd
      _ = ε_samp + δ_samp ^ (1 / (d : ℝ)) := by
          rw [pow_rpow_inv_natCast hε hd]
  rw [← ha_eq, ← hb_eq]
  exact (abs_lpNormSet_sub_le S hd a b).trans hdiff_norm

/-- **Lemma 4.1 (`\label{lem:approx-grid-norm}`, `\eqref{eq:approx-grid-norm-err}`, `paper.tex` §4.1)**
(general $(\varepsilon_{\text{samp}}, \delta_{\text{samp}})$ form for binary real matrices):
For every $x \in X$ with $\deg_M(x) > 0$,
$$\left|v_x - \|M[X, Y_x]\|_{U(1, d)}\right| \le \frac{\varepsilon_{\text{samp}} + \delta_{\text{samp}}^{1/d}}{\deg_M(x)}.$$ -/
theorem approxGridNormVal_sub_gridNorm1_le_of_isObliviousSampler
    {X : Finset α} (hX : X.Nonempty) {Y : Finset β} {T_fam : List (Finset β)}
    {ε_samp δ_samp : ℝ} (hS : IsObliviousSampler Y T_fam ε_samp δ_samp)
    (hε : 0 ≤ ε_samp) (hδ : 0 ≤ δ_samp)
    {M : α → β → ℝ} (hM : IsBinaryRealMat M)
    {d : ℕ} (hd : 1 ≤ d) {x : α} (hdeg : 0 < rowDeg Y M x) :
    |approxGridNormVal X Y T_fam M d x - gridNorm1 X (realRowNbr Y M x) M d| ≤
      (ε_samp + δ_samp ^ (1 / (d : ℝ))) / rowDeg Y M x := by
  have hM01 : ∀ x' y, 0 ≤ M x' y ∧ M x' y ≤ 1 :=
    fun x' y => ⟨isBinaryRealMat_nonneg hM x' y, isBinaryRealMat_le_one hM x' y⟩
  have hU_bound :=
    abs_approxGridNormURoot_sub_gridNorm1_rowFilteredMat_le hX hS hε hδ hM01 hd x
  rw [gridNorm1_rowFilteredMat_eq X Y hM x hd] at hU_bound
  rw [approxGridNormVal_eq_div X Y T_fam (isBinaryRealMat_nonneg hM) hd x]
  have hsub : approxGridNormURoot X T_fam M d x / rowDeg Y M x -
      gridNorm1 X (realRowNbr Y M x) M d =
      (approxGridNormURoot X T_fam M d x -
        rowDeg Y M x * gridNorm1 X (realRowNbr Y M x) M d) / rowDeg Y M x := by
    rw [sub_div, mul_div_cancel_left₀ _ hdeg.ne']
  rw [hsub, abs_div, abs_of_pos hdeg]
  exact div_le_div_of_nonneg_right hU_bound hdeg.le

/-- **Lemma 4.1 (`\label{lem:approx-grid-norm}`, `\eqref{eq:approx-grid-norm-err}`, `paper.tex` §4.1)**:
With $\varepsilon_{\text{samp}} = \alpha_{\text{grid}} / 2$ and
$\delta_{\text{samp}} = (\alpha_{\text{grid}} / 2)^d$ (Algorithm 2, Line 1), for every $x \in X$
with $\deg_M(x) > 0$, the output $V_x$ is non-negative and $v_x = V_x^{1/d}$ satisfies
$$\left|v_x - \|M[X, Y_x]\|_{U(1, d)}\right| \le \frac{\alpha_{\text{grid}}}{\deg_M(x)}.$$ -/
theorem lem_approx_grid_norm_real
    {X : Finset α} (hX : X.Nonempty) {Y : Finset β} {T_fam : List (Finset β)}
    {α_grid : ℝ} (hα : 0 ≤ α_grid) {d : ℕ} (hd : 1 ≤ d)
    (hS : IsObliviousSampler Y T_fam (α_grid / 2) ((α_grid / 2) ^ d))
    {M : α → β → ℝ} (hM : IsBinaryRealMat M)
    {x : α} (hdeg : 0 < rowDeg Y M x) :
    0 ≤ approxGridNormV X Y T_fam M d x ∧
    |approxGridNormVal X Y T_fam M d x - gridNorm1 X (realRowNbr Y M x) M d| ≤
      α_grid / rowDeg Y M x := by
  refine ⟨approxGridNormV_nonneg X Y T_fam (isBinaryRealMat_nonneg hM) d x, ?_⟩
  have hε : 0 ≤ α_grid / 2 := by linarith
  have hδ : 0 ≤ (α_grid / 2) ^ d := pow_nonneg hε d
  have h1 := approxGridNormVal_sub_gridNorm1_le_of_isObliviousSampler hX hS hε hδ hM hd hdeg
  have hsum : α_grid / 2 + ((α_grid / 2) ^ d) ^ (1 / (d : ℝ)) = α_grid := by
    rw [pow_rpow_inv_natCast hε hd]
    ring
  rw [hsum] at h1
  exact h1

/-- **Lemma 4.1 (`\label{lem:approx-grid-norm}`, `\eqref{eq:approx-grid-norm-err}`, `paper.tex` §4.1)**
specialized to Boolean matrices $A : \alpha \to \beta \to \text{Bool}$:
For $\varepsilon_{\text{samp}} = \alpha_{\text{grid}} / 2$ and
$\delta_{\text{samp}} = (\alpha_{\text{grid}} / 2)^d$, for every $x \in X$ with $\deg_A(x) > 0$,
$$0 \le V_x \quad\text{and}\quad
  \left|v_x - \|A_x\|_{U(1, d)}\right| \le \frac{\alpha_{\text{grid}}}{\deg_A(x)}.$$ -/
theorem lem_approx_grid_norm
    {X : Finset α} (hX : X.Nonempty) {Y : Finset β} {T_fam : List (Finset β)}
    {α_grid : ℝ} (hα : 0 ≤ α_grid) {d : ℕ} (hd : 1 ≤ d)
    (hS : IsObliviousSampler Y T_fam (α_grid / 2) ((α_grid / 2) ^ d))
    (A : α → β → Bool) {x : α} (hdeg : 0 < rowDeg Y (bmatToReal A) x) :
    0 ≤ approxGridNormV X Y T_fam (bmatToReal A) d x ∧
    |approxGridNormVal X Y T_fam (bmatToReal A) d x -
      gridNorm1 X (rowNbr Y A x) (bmatToReal A) d| ≤
      α_grid / rowDeg Y (bmatToReal A) x := by
  have h := lem_approx_grid_norm_real hX hα hd hS (isBinaryRealMat_bmatToReal A) hdeg
  rwa [realRowNbr_bmatToReal] at h

/-!
### Sequence-Sampler Instantiation of Lemma 4.1 (`IsSeqSampler`, `paper.tex` §3.3 & §4.1)
-/

/-- Sequence-sampler estimator $U_x$ for a family of sample sequences `T_fam : List (List β)`:
$U_x = \mathbb{E}_{x' \in X} \mathbb{E}_{T \in \mathcal{T}}\!\left[\left(\mathbb{E}_{y \in T} A'_x(x', y)\right)^d\right]$
(`paper.tex` §4.1). -/
noncomputable def approxGridNormUSeq (X : Finset α) (T_fam : List (List β))
    (M : α → β → ℝ) (d : ℕ) (x : α) : ℝ :=
  expectSet X (fun x' =>
    expectList T_fam (fun T => (expectSeq T (fun y => rowFilteredMat M x x' y)) ^ d))

/-- Sequence-sampler estimator $V_x := U_x / (\deg_M(x))^d$ (Algorithm 2 Line 3). -/
noncomputable def approxGridNormVSeq (X : Finset α) (Y : Finset β) (T_fam : List (List β))
    (M : α → β → ℝ) (d : ℕ) (x : α) : ℝ :=
  approxGridNormUSeq X T_fam M d x / (rowDeg Y M x) ^ d

/-- The $d$-th root $u_x := U_x^{1/d}$ of `approxGridNormUSeq`. -/
noncomputable def approxGridNormURootSeq (X : Finset α) (T_fam : List (List β))
    (M : α → β → ℝ) (d : ℕ) (x : α) : ℝ :=
  (approxGridNormUSeq X T_fam M d x) ^ (1 / (d : ℝ))

/-- The $d$-th root $v_x := V_x^{1/d}$ of `approxGridNormVSeq`. -/
noncomputable def approxGridNormValSeq (X : Finset α) (Y : Finset β) (T_fam : List (List β))
    (M : α → β → ℝ) (d : ℕ) (x : α) : ℝ :=
  (approxGridNormVSeq X Y T_fam M d x) ^ (1 / (d : ℝ))

lemma expectSeq_nonneg {T : List β} {g : β → ℝ} (hg : ∀ y ∈ T, 0 ≤ g y) :
    0 ≤ expectSeq T g := by
  unfold expectSeq
  refine div_nonneg (List.sum_nonneg ?_) (Nat.cast_nonneg _)
  intro r hr
  rcases List.mem_map.mp hr with ⟨y, hy, rfl⟩
  exact hg y hy

lemma list_map_sum_le_length {T : List β} {g : β → ℝ} (h1 : ∀ y ∈ T, g y ≤ 1) :
    (T.map g).sum ≤ (T.length : ℝ) := by
  induction T with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have ha := h1 a List.mem_cons_self
    have htl := ih (fun y hy => h1 y (List.mem_cons_of_mem a hy))
    linarith

lemma expectSeq_mem_unit_interval {Y : Finset β} {T : List β} (hT : ∀ y ∈ T, y ∈ Y)
    {g : β → ℝ} (hg : ∀ y ∈ Y, 0 ≤ g y ∧ g y ≤ 1) :
    0 ≤ expectSeq T g ∧ expectSeq T g ≤ 1 := by
  refine ⟨expectSeq_nonneg (fun y hy => (hg y (hT y hy)).1), ?_⟩
  unfold expectSeq
  cases T with
  | nil => simp
  | cons a tl =>
    have hpos : (0 : ℝ) < ((a :: tl).length : ℝ) := by simp; positivity
    rw [div_le_iff₀ hpos, one_mul]
    exact list_map_sum_le_length (fun y hy => (hg y (hT y hy)).2)

lemma approxGridNormUSeq_nonneg (X : Finset α) (T_fam : List (List β))
    {M : α → β → ℝ} (hM : ∀ x y, 0 ≤ M x y) (d : ℕ) (x : α) :
    0 ≤ approxGridNormUSeq X T_fam M d x := by
  unfold approxGridNormUSeq
  refine expectSet_nonneg (fun x' _ => expectList_nonneg (fun T _ => ?_))
  refine pow_nonneg (expectSeq_nonneg (fun y _ => ?_)) d
  exact mul_nonneg (hM x' y) (hM x y)

lemma approxGridNormVSeq_nonneg (X : Finset α) (Y : Finset β) (T_fam : List (List β))
    {M : α → β → ℝ} (hM : ∀ x y, 0 ≤ M x y) (d : ℕ) (x : α) :
    0 ≤ approxGridNormVSeq X Y T_fam M d x := by
  unfold approxGridNormVSeq
  exact div_nonneg (approxGridNormUSeq_nonneg X T_fam hM d x)
    (pow_nonneg (rowDeg_nonneg_of_nonneg Y hM x) d)

theorem approxGridNormValSeq_eq_div (X : Finset α) (Y : Finset β) (T_fam : List (List β))
    {M : α → β → ℝ} (hM : ∀ x y, 0 ≤ M x y) {d : ℕ} (hd : 1 ≤ d) (x : α) :
    approxGridNormValSeq X Y T_fam M d x =
      approxGridNormURootSeq X T_fam M d x / rowDeg Y M x := by
  unfold approxGridNormValSeq approxGridNormVSeq approxGridNormURootSeq
  have hU : 0 ≤ approxGridNormUSeq X T_fam M d x := approxGridNormUSeq_nonneg X T_fam hM d x
  have hdeg : 0 ≤ rowDeg Y M x := rowDeg_nonneg_of_nonneg Y hM x
  rw [Real.div_rpow hU (pow_nonneg hdeg d), pow_rpow_inv_natCast hdeg hd]

/-- **`paper.tex` §4.1 (Sequence-Sampler Form)**:
For any $(\varepsilon_{\text{samp}}, \delta_{\text{samp}})$-sequence sampler `T_fam : List (List β)`
of `Y` (`IsSeqSampler`) and any $g : \beta \to [0, 1]$,
$$\mathbb{E}_{T \in \mathcal{T}}\!\left[\left|\mathbb{E}_{y \in T}[g(y)] - \mathbb{E}_{y \in Y}[g(y)]\right|^d\right]
  \le \varepsilon_{\text{samp}}^d + \delta_{\text{samp}}.$$ -/
theorem expectList_abs_sub_pow_le_of_isSeqSampler
    {Y : Finset β} {T_fam : List (List β)} {ε_samp δ_samp : ℝ}
    (hS : IsSeqSampler Y T_fam ε_samp δ_samp) (hε : 0 ≤ ε_samp)
    (d : ℕ) (g : β → ℝ) (hg : ∀ y ∈ Y, 0 ≤ g y ∧ g y ≤ 1) :
    expectList T_fam (fun T => |expectSeq T g - expectSet Y g| ^ d) ≤
      ε_samp ^ d + δ_samp := by
  let p : List β → Bool := fun T => decide (|expectSeq T g - expectSet Y g| > ε_samp)
  have hpt : ∀ T ∈ T_fam,
      |expectSeq T g - expectSet Y g| ^ d ≤
        ε_samp ^ d + (if p T then (1 : ℝ) else 0) := by
    intro T hT
    have hT_sub : ∀ y ∈ T, y ∈ Y := (hS.2.1 T hT).1
    have hT_unit := expectSeq_mem_unit_interval hT_sub hg
    have hY_unit := expectSet_mem_unit_interval Y hg
    have habs_le_one : |expectSeq T g - expectSet Y g| ≤ 1 :=
      abs_sub_le_one_of_unit_interval hT_unit hY_unit
    by_cases hgt : |expectSeq T g - expectSet Y g| > ε_samp
    · have hpT : p T = true := decide_eq_true hgt
      simp only [hpT, ↓reduceIte]
      have hpow1 : |expectSeq T g - expectSet Y g| ^ d ≤ 1 := by
        calc
          |expectSeq T g - expectSet Y g| ^ d ≤ (1 : ℝ) ^ d :=
            pow_le_pow_left₀ (abs_nonneg _) habs_le_one d
          _ = 1 := one_pow d
      have hε_pow : 0 ≤ ε_samp ^ d := pow_nonneg hε d
      linarith
    · have hpT : p T = false := decide_eq_false hgt
      simp only [hpT, Bool.false_eq_true, ↓reduceIte, add_zero]
      have hle : |expectSeq T g - expectSet Y g| ≤ ε_samp := not_lt.mp hgt
      exact pow_le_pow_left₀ (abs_nonneg _) hle d
  have hite_le := expectList_ite_le_of_filter_length_le hS.1 p (hS.2.2 g hg)
  calc
    expectList T_fam (fun T => |expectSeq T g - expectSet Y g| ^ d)
      ≤ expectList T_fam (fun T => ε_samp ^ d + (if p T then (1 : ℝ) else 0)) :=
        expectList_mono hpt
    _ = expectList T_fam (fun _ => ε_samp ^ d) +
          expectList T_fam (fun T => if p T then (1 : ℝ) else 0) :=
        expectList_add T_fam _ _
    _ = ε_samp ^ d + expectList T_fam (fun T => if p T then (1 : ℝ) else 0) := by
        rw [expectList_const hS.1]
    _ ≤ ε_samp ^ d + δ_samp := by linarith

/-- **`paper.tex` §4.1 (Sequence-Sampler Form)**:
$$\left|u_x - \|A'_x\|_{U(1, d)}\right| \le \varepsilon_{\text{samp}} + \delta_{\text{samp}}^{1/d}.$$ -/
theorem abs_approxGridNormURootSeq_sub_gridNorm1_rowFilteredMat_le
    {X : Finset α} (hX : X.Nonempty) {Y : Finset β} {T_fam : List (List β)}
    {ε_samp δ_samp : ℝ} (hS : IsSeqSampler Y T_fam ε_samp δ_samp)
    (hε : 0 ≤ ε_samp) (hδ : 0 ≤ δ_samp)
    {M : α → β → ℝ} (hM : ∀ x y, 0 ≤ M x y ∧ M x y ≤ 1)
    {d : ℕ} (hd : 1 ≤ d) (x : α) :
    |approxGridNormURootSeq X T_fam M d x - gridNorm1 X Y (rowFilteredMat M x) d| ≤
      ε_samp + δ_samp ^ (1 / (d : ℝ)) := by
  let S := X ×ˢ (Finset.univ : Finset (Fin T_fam.length))
  let a : α × Fin T_fam.length → ℝ :=
    fun p => expectSeq (T_fam.get p.2) (fun y => rowFilteredMat M x p.1 y)
  let b : α × Fin T_fam.length → ℝ :=
    fun p => rowDeg Y (rowFilteredMat M x) p.1
  have hM_filt_nonneg : ∀ x' y, 0 ≤ rowFilteredMat M x x' y :=
    fun x' y => mul_nonneg (hM x' y).1 (hM x y).1
  have ha_eq : lpNormSet S d a = approxGridNormURootSeq X T_fam M d x := by
    unfold lpNormSet approxGridNormURootSeq approxGridNormUSeq
    congr 1
    rw [expectSet_expectList_eq_expectSet_prod X T_fam
      (fun x' T => (expectSeq T (fun y => rowFilteredMat M x x' y)) ^ d)]
    congr 1
    ext p
    have ha_nonneg : 0 ≤ a p := expectSeq_nonneg (fun y _ => hM_filt_nonneg p.1 y)
    rw [abs_of_nonneg ha_nonneg]
  have hb_eq : lpNormSet S d b = gridNorm1 X Y (rowFilteredMat M x) d := by
    unfold lpNormSet gridNorm1 gridNorm1Pow
    congr 1
    have hconst : expectSet X (fun x' => (rowDeg Y (rowFilteredMat M x) x') ^ d) =
        expectSet X (fun x' => expectList T_fam (fun _ => (rowDeg Y (rowFilteredMat M x) x') ^ d)) := by
      congr 1
      ext x'
      rw [expectList_const hS.1]
    rw [hconst, expectSet_expectList_eq_expectSet_prod X T_fam
      (fun x' _ => (rowDeg Y (rowFilteredMat M x) x') ^ d)]
    congr 1
    ext p
    have hb_nonneg : 0 ≤ b p := rowDeg_nonneg_of_nonneg Y hM_filt_nonneg p.1
    rw [abs_of_nonneg hb_nonneg]
  have hdiff_pow : expectSet S (fun p => |a p - b p| ^ d) ≤ ε_samp ^ d + δ_samp := by
    rw [← expectSet_expectList_eq_expectSet_prod X T_fam
      (fun x' T => |expectSeq T (fun y => rowFilteredMat M x x' y) - rowDeg Y (rowFilteredMat M x) x'| ^ d)]
    refine expectSet_le_of_le hX (fun x' _ => ?_)
    refine expectList_abs_sub_pow_le_of_isSeqSampler hS hε d
      (fun y => rowFilteredMat M x x' y) (fun y _ => ?_)
    refine ⟨hM_filt_nonneg x' y, ?_⟩
    unfold rowFilteredMat
    calc
      M x' y * M x y ≤ 1 * 1 :=
        mul_le_mul (hM x' y).2 (hM x y).2 (hM x y).1 zero_le_one
      _ = 1 := one_mul 1
  have hdiff_norm : lpNormSet S d (fun p => a p - b p) ≤ ε_samp + δ_samp ^ (1 / (d : ℝ)) := by
    unfold lpNormSet
    calc
      (expectSet S (fun p => |a p - b p| ^ d)) ^ (1 / (d : ℝ))
        ≤ (ε_samp ^ d + δ_samp) ^ (1 / (d : ℝ)) :=
          Real.rpow_le_rpow (expectSet_nonneg (fun _ _ => pow_nonneg (abs_nonneg _) d))
            hdiff_pow (by positivity)
      _ ≤ (ε_samp ^ d) ^ (1 / (d : ℝ)) + δ_samp ^ (1 / (d : ℝ)) :=
          rpow_inv_add_le (pow_nonneg hε d) hδ hd
      _ = ε_samp + δ_samp ^ (1 / (d : ℝ)) := by
          rw [pow_rpow_inv_natCast hε hd]
  rw [← ha_eq, ← hb_eq]
  exact (abs_lpNormSet_sub_le S hd a b).trans hdiff_norm

/-- **Lemma 4.1 for Sequence Oblivious Samplers (`lem_approx_grid_norm_seq_real`, `paper.tex` §4.1)**:
With $\varepsilon_{\text{samp}} = \alpha_{\text{grid}} / 2$ and
$\delta_{\text{samp}} = (\alpha_{\text{grid}} / 2)^d$, for every $x \in X$ with $\deg_M(x) > 0$,
$$0 \le V_x \quad\text{and}\quad
  \left|v_x - \|M[X, Y_x]\|_{U(1, d)}\right| \le \frac{\alpha_{\text{grid}}}{\deg_M(x)}.$$ -/
theorem lem_approx_grid_norm_seq_real
    {X : Finset α} (hX : X.Nonempty) {Y : Finset β} {T_fam : List (List β)}
    {α_grid : ℝ} (hα : 0 ≤ α_grid) {d : ℕ} (hd : 1 ≤ d)
    (hS : IsSeqSampler Y T_fam (α_grid / 2) ((α_grid / 2) ^ d))
    {M : α → β → ℝ} (hM : IsBinaryRealMat M)
    {x : α} (hdeg : 0 < rowDeg Y M x) :
    0 ≤ approxGridNormVSeq X Y T_fam M d x ∧
    |approxGridNormValSeq X Y T_fam M d x - gridNorm1 X (realRowNbr Y M x) M d| ≤
      α_grid / rowDeg Y M x := by
  refine ⟨approxGridNormVSeq_nonneg X Y T_fam (isBinaryRealMat_nonneg hM) d x, ?_⟩
  have hε : 0 ≤ α_grid / 2 := by linarith
  have hδ : 0 ≤ (α_grid / 2) ^ d := pow_nonneg hε d
  have hM01 : ∀ x' y, 0 ≤ M x' y ∧ M x' y ≤ 1 :=
    fun x' y => ⟨isBinaryRealMat_nonneg hM x' y, isBinaryRealMat_le_one hM x' y⟩
  have hU_bound :=
    abs_approxGridNormURootSeq_sub_gridNorm1_rowFilteredMat_le hX hS hε hδ hM01 hd x
  have hsum : α_grid / 2 + ((α_grid / 2) ^ d) ^ (1 / (d : ℝ)) = α_grid := by
    rw [pow_rpow_inv_natCast hε hd]
    ring
  rw [hsum, gridNorm1_rowFilteredMat_eq X Y hM x hd] at hU_bound
  rw [approxGridNormValSeq_eq_div X Y T_fam (isBinaryRealMat_nonneg hM) hd x]
  have hsub : approxGridNormURootSeq X T_fam M d x / rowDeg Y M x -
      gridNorm1 X (realRowNbr Y M x) M d =
      (approxGridNormURootSeq X T_fam M d x -
        rowDeg Y M x * gridNorm1 X (realRowNbr Y M x) M d) / rowDeg Y M x := by
    rw [sub_div, mul_div_cancel_left₀ _ hdeg.ne']
  rw [hsub, abs_div, abs_of_pos hdeg]
  exact div_le_div_of_nonneg_right hU_bound hdeg.le

/-!
### Tuple-Sampler Instantiation of Lemma 4.1 (`IsTupleObliviousSampler` & `constructChebyshevTupleSampler`)
-/

/-- Product-space identity for iterated `expectSet` over `X ×ˢ Ω`. -/
theorem expectSet_expectSet_eq_expectSet_prod {γ : Type*} (X : Finset α) (Ω : Finset γ)
    (F : α → γ → ℝ) :
    expectSet X (fun x => expectSet Ω (fun ω => F x ω)) =
      expectSet (X ×ˢ Ω) (fun p => F p.1 p.2) := by
  unfold expectSet
  rw [← Finset.sum_div, div_div, Finset.card_product, Nat.cast_mul,
    mul_comm (Ω.card : ℝ) (X.card : ℝ), Finset.sum_product]

/-- Tuple-sampler estimator $U_x$ for a $k$-tuple family $\Omega \subseteq Y^k$ (`Finset (Fin k → β)`):
$U_x = \mathbb{E}_{x' \in X} \mathbb{E}_{ys \in \Omega}\!\left[(\bar{A}'_x(x', ys))^d\right]$
(`paper.tex` §4.1). -/
noncomputable def approxGridNormUTuple (X : Finset α) (k : ℕ) (Ω : Finset (Fin k → β))
    (M : α → β → ℝ) (d : ℕ) (x : α) : ℝ :=
  expectSet X (fun x' =>
    expectSet Ω (fun ys => (tupleSampleAvg k (fun y => rowFilteredMat M x x' y) ys) ^ d))

/-- Tuple-sampler estimator $V_x := U_x / (\deg_M(x))^d$ (Algorithm 2 Line 3). -/
noncomputable def approxGridNormVTuple (X : Finset α) (Y : Finset β) (k : ℕ)
    (Ω : Finset (Fin k → β)) (M : α → β → ℝ) (d : ℕ) (x : α) : ℝ :=
  approxGridNormUTuple X k Ω M d x / (rowDeg Y M x) ^ d

/-- The $d$-th root $u_x := U_x^{1/d}$ of `approxGridNormUTuple`. -/
noncomputable def approxGridNormURootTuple (X : Finset α) (k : ℕ) (Ω : Finset (Fin k → β))
    (M : α → β → ℝ) (d : ℕ) (x : α) : ℝ :=
  (approxGridNormUTuple X k Ω M d x) ^ (1 / (d : ℝ))

/-- The $d$-th root $v_x := V_x^{1/d}$ of `approxGridNormVTuple`. -/
noncomputable def approxGridNormValTuple (X : Finset α) (Y : Finset β) (k : ℕ)
    (Ω : Finset (Fin k → β)) (M : α → β → ℝ) (d : ℕ) (x : α) : ℝ :=
  (approxGridNormVTuple X Y k Ω M d x) ^ (1 / (d : ℝ))

lemma tupleSampleAvg_mem_unit_interval {Y : Finset β} {k : ℕ} {ys : Fin k → β}
    (hys : ∀ i : Fin k, ys i ∈ Y) {g : β → ℝ} (hg : ∀ y ∈ Y, 0 ≤ g y ∧ g y ≤ 1) :
    0 ≤ tupleSampleAvg k g ys ∧ tupleSampleAvg k g ys ≤ 1 := by
  unfold tupleSampleAvg
  exact expectSet_mem_unit_interval Finset.univ (fun i _ => hg (ys i) (hys i))

lemma approxGridNormUTuple_nonneg (X : Finset α) (k : ℕ) (Ω : Finset (Fin k → β))
    {M : α → β → ℝ} (hM : ∀ x y, 0 ≤ M x y) (d : ℕ) (x : α) :
    0 ≤ approxGridNormUTuple X k Ω M d x := by
  unfold approxGridNormUTuple
  refine expectSet_nonneg (fun x' _ => expectSet_nonneg (fun ys _ => ?_))
  refine pow_nonneg ?_ d
  unfold tupleSampleAvg
  exact expectSet_nonneg (fun i _ => mul_nonneg (hM x' (ys i)) (hM x (ys i)))

lemma approxGridNormVTuple_nonneg (X : Finset α) (Y : Finset β) (k : ℕ)
    (Ω : Finset (Fin k → β)) {M : α → β → ℝ} (hM : ∀ x y, 0 ≤ M x y) (d : ℕ) (x : α) :
    0 ≤ approxGridNormVTuple X Y k Ω M d x := by
  unfold approxGridNormVTuple
  exact div_nonneg (approxGridNormUTuple_nonneg X k Ω hM d x)
    (pow_nonneg (rowDeg_nonneg_of_nonneg Y hM x) d)

theorem approxGridNormValTuple_eq_div (X : Finset α) (Y : Finset β) (k : ℕ)
    (Ω : Finset (Fin k → β)) {M : α → β → ℝ} (hM : ∀ x y, 0 ≤ M x y)
    {d : ℕ} (hd : 1 ≤ d) (x : α) :
    approxGridNormValTuple X Y k Ω M d x =
      approxGridNormURootTuple X k Ω M d x / rowDeg Y M x := by
  unfold approxGridNormValTuple approxGridNormVTuple approxGridNormURootTuple
  have hU : 0 ≤ approxGridNormUTuple X k Ω M d x := approxGridNormUTuple_nonneg X k Ω hM d x
  have hdeg : 0 ≤ rowDeg Y M x := rowDeg_nonneg_of_nonneg Y hM x
  rw [Real.div_rpow hU (pow_nonneg hdeg d), pow_rpow_inv_natCast hdeg hd]

/-- **`paper.tex` §4.1 (Tuple Sampler Form)**:
For any $(\varepsilon_{\text{samp}}, \delta_{\text{samp}})$-tuple oblivious sampler $\Omega \subseteq Y^k$
and any $g : \beta \to [0, 1]$,
$$\mathbb{E}_{ys \in \Omega}\!\left[\left|\bar{g}(ys) - \mathbb{E}_{y \in Y}[g(y)]\right|^d\right]
  \le \varepsilon_{\text{samp}}^d + \delta_{\text{samp}}.$$ -/
theorem expectSet_abs_sub_pow_le_of_isTupleObliviousSampler
    {Y : Finset β} {k : ℕ} {Ω : Finset (Fin k → β)} {ε_samp δ_samp : ℝ}
    (hS : IsTupleObliviousSampler Y k Ω ε_samp δ_samp) (hΩ : Ω.Nonempty) (hε : 0 ≤ ε_samp)
    (d : ℕ) (g : β → ℝ) (hg : ∀ y ∈ Y, 0 ≤ g y ∧ g y ≤ 1) :
    expectSet Ω (fun ys => |tupleSampleAvg k g ys - expectSet Y g| ^ d) ≤
      ε_samp ^ d + δ_samp := by
  let P : (Fin k → β) → Prop := fun ys => ε_samp ≤ |tupleSampleAvg k g ys - expectSet Y g|
  have hpt : ∀ ys ∈ Ω,
      |tupleSampleAvg k g ys - expectSet Y g| ^ d ≤
        ε_samp ^ d + (if P ys then (1 : ℝ) else 0) := by
    intro ys hys
    have hys_unit := tupleSampleAvg_mem_unit_interval (hS.2.1 ys hys) hg
    have hY_unit := expectSet_mem_unit_interval Y hg
    have habs_le_one : |tupleSampleAvg k g ys - expectSet Y g| ≤ 1 :=
      abs_sub_le_one_of_unit_interval hys_unit hY_unit
    by_cases hP : P ys
    · simp only [hP, ↓reduceIte]
      have hpow1 : |tupleSampleAvg k g ys - expectSet Y g| ^ d ≤ 1 := by
        calc
          |tupleSampleAvg k g ys - expectSet Y g| ^ d ≤ (1 : ℝ) ^ d :=
            pow_le_pow_left₀ (abs_nonneg _) habs_le_one d
          _ = 1 := one_pow d
      have hε_pow : 0 ≤ ε_samp ^ d := pow_nonneg hε d
      linarith
    · simp only [hP, ↓reduceIte, add_zero]
      have hle : |tupleSampleAvg k g ys - expectSet Y g| ≤ ε_samp := le_of_lt (not_le.mp hP)
      exact pow_le_pow_left₀ (abs_nonneg _) hle d
  have hite_eq : expectSet Ω (fun ys => if P ys then (1 : ℝ) else 0) =
      ((Ω.filter P).card : ℝ) / (Ω.card : ℝ) := by
    unfold expectSet
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hΩ_pos : (0 : ℝ) < (Ω.card : ℝ) := Nat.cast_pos.mpr hΩ.card_pos
  have hite_le : expectSet Ω (fun ys => if P ys then (1 : ℝ) else 0) ≤ δ_samp := by
    rw [hite_eq, div_le_iff₀ hΩ_pos]
    exact hS.2.2 g hg
  calc
    expectSet Ω (fun ys => |tupleSampleAvg k g ys - expectSet Y g| ^ d)
      ≤ expectSet Ω (fun ys => ε_samp ^ d + (if P ys then (1 : ℝ) else 0)) :=
        expectSet_mono hpt
    _ = expectSet Ω (fun _ => ε_samp ^ d) +
          expectSet Ω (fun ys => if P ys then (1 : ℝ) else 0) :=
        expectSet_add Ω _ _
    _ = ε_samp ^ d + expectSet Ω (fun ys => if P ys then (1 : ℝ) else 0) := by
        rw [expectSet_const hΩ]
    _ ≤ ε_samp ^ d + δ_samp := by linarith

/-- **`paper.tex` §4.1 (Tuple Sampler Form)**:
$$\left|u_x - \|A'_x\|_{U(1, d)}\right| \le \varepsilon_{\text{samp}} + \delta_{\text{samp}}^{1/d}.$$ -/
theorem abs_approxGridNormURootTuple_sub_gridNorm1_rowFilteredMat_le
    {X : Finset α} (hX : X.Nonempty) {Y : Finset β} {k : ℕ} {Ω : Finset (Fin k → β)}
    {ε_samp δ_samp : ℝ} (hS : IsTupleObliviousSampler Y k Ω ε_samp δ_samp)
    (hΩ : Ω.Nonempty) (hε : 0 ≤ ε_samp) (hδ : 0 ≤ δ_samp)
    {M : α → β → ℝ} (hM : ∀ x y, 0 ≤ M x y ∧ M x y ≤ 1)
    {d : ℕ} (hd : 1 ≤ d) (x : α) :
    |approxGridNormURootTuple X k Ω M d x - gridNorm1 X Y (rowFilteredMat M x) d| ≤
      ε_samp + δ_samp ^ (1 / (d : ℝ)) := by
  let S := X ×ˢ Ω
  let a : α × (Fin k → β) → ℝ :=
    fun p => tupleSampleAvg k (fun y => rowFilteredMat M x p.1 y) p.2
  let b : α × (Fin k → β) → ℝ :=
    fun p => rowDeg Y (rowFilteredMat M x) p.1
  have hM_filt_nonneg : ∀ x' y, 0 ≤ rowFilteredMat M x x' y :=
    fun x' y => mul_nonneg (hM x' y).1 (hM x y).1
  have ha_eq : lpNormSet S d a = approxGridNormURootTuple X k Ω M d x := by
    unfold lpNormSet approxGridNormURootTuple approxGridNormUTuple
    congr 1
    rw [expectSet_expectSet_eq_expectSet_prod X Ω
      (fun x' ys => (tupleSampleAvg k (fun y => rowFilteredMat M x x' y) ys) ^ d)]
    congr 1
    ext p
    have ha_nonneg : 0 ≤ a p :=
      expectSet_nonneg (fun i _ => hM_filt_nonneg p.1 (p.2 i))
    rw [abs_of_nonneg ha_nonneg]
  have hb_eq : lpNormSet S d b = gridNorm1 X Y (rowFilteredMat M x) d := by
    unfold lpNormSet gridNorm1 gridNorm1Pow
    congr 1
    have hconst : expectSet X (fun x' => (rowDeg Y (rowFilteredMat M x) x') ^ d) =
        expectSet X (fun x' => expectSet Ω (fun _ => (rowDeg Y (rowFilteredMat M x) x') ^ d)) := by
      congr 1
      ext x'
      rw [expectSet_const hΩ]
    rw [hconst, expectSet_expectSet_eq_expectSet_prod X Ω
      (fun x' _ => (rowDeg Y (rowFilteredMat M x) x') ^ d)]
    congr 1
    ext p
    have hb_nonneg : 0 ≤ b p := rowDeg_nonneg_of_nonneg Y hM_filt_nonneg p.1
    rw [abs_of_nonneg hb_nonneg]
  have hdiff_pow : expectSet S (fun p => |a p - b p| ^ d) ≤ ε_samp ^ d + δ_samp := by
    rw [← expectSet_expectSet_eq_expectSet_prod X Ω
      (fun x' ys => |tupleSampleAvg k (fun y => rowFilteredMat M x x' y) ys -
        rowDeg Y (rowFilteredMat M x) x'| ^ d)]
    refine expectSet_le_of_le hX (fun x' _ => ?_)
    refine expectSet_abs_sub_pow_le_of_isTupleObliviousSampler hS hΩ hε d
      (fun y => rowFilteredMat M x x' y) (fun y _ => ?_)
    refine ⟨hM_filt_nonneg x' y, ?_⟩
    unfold rowFilteredMat
    calc
      M x' y * M x y ≤ 1 * 1 :=
        mul_le_mul (hM x' y).2 (hM x y).2 (hM x y).1 zero_le_one
      _ = 1 := one_mul 1
  have hdiff_norm : lpNormSet S d (fun p => a p - b p) ≤ ε_samp + δ_samp ^ (1 / (d : ℝ)) := by
    unfold lpNormSet
    calc
      (expectSet S (fun p => |a p - b p| ^ d)) ^ (1 / (d : ℝ))
        ≤ (ε_samp ^ d + δ_samp) ^ (1 / (d : ℝ)) :=
          Real.rpow_le_rpow (expectSet_nonneg (fun _ _ => pow_nonneg (abs_nonneg _) d))
            hdiff_pow (by positivity)
      _ ≤ (ε_samp ^ d) ^ (1 / (d : ℝ)) + δ_samp ^ (1 / (d : ℝ)) :=
          rpow_inv_add_le (pow_nonneg hε d) hδ hd
      _ = ε_samp + δ_samp ^ (1 / (d : ℝ)) := by
          rw [pow_rpow_inv_natCast hε hd]
  rw [← ha_eq, ← hb_eq]
  exact (abs_lpNormSet_sub_le S hd a b).trans hdiff_norm

/-- **Lemma 4.1 Accuracy Guarantee for Tuple Oblivious Samplers (`lem_approx_grid_norm_tuple`, `paper.tex` §4.1)**:
If `IsTupleObliviousSampler Y k Ω (α_grid / 2) ((α_grid / 2) ^ d)` and `Ω.Nonempty`, then for
every $x \in X$ with $\deg_M(x) > 0$,
$$0 \le V_x \quad\text{and}\quad
  \left|v_x - \|M[X, Y_x]\|_{U(1, d)}\right| \le \frac{\alpha_{\text{grid}}}{\deg_M(x)}.$$
(This theorem states the mathematical accuracy guarantee of Lemma 4.1 for an arbitrary tuple
sampler $\Omega \subseteq Y^k$, without a running-time clause.) -/
theorem lem_approx_grid_norm_tuple
    {X : Finset α} (hX : X.Nonempty) {Y : Finset β} {k : ℕ} {Ω : Finset (Fin k → β)}
    (hΩ : Ω.Nonempty) {α_grid : ℝ} (hα : 0 ≤ α_grid) {d : ℕ} (hd : 1 ≤ d)
    (hS : IsTupleObliviousSampler Y k Ω (α_grid / 2) ((α_grid / 2) ^ d))
    {M : α → β → ℝ} (hM : IsBinaryRealMat M)
    {x : α} (hdeg : 0 < rowDeg Y M x) :
    0 ≤ approxGridNormVTuple X Y k Ω M d x ∧
    |approxGridNormValTuple X Y k Ω M d x - gridNorm1 X (realRowNbr Y M x) M d| ≤
      α_grid / rowDeg Y M x := by
  refine ⟨approxGridNormVTuple_nonneg X Y k Ω (isBinaryRealMat_nonneg hM) d x, ?_⟩
  have hε : 0 ≤ α_grid / 2 := by linarith
  have hδ : 0 ≤ (α_grid / 2) ^ d := pow_nonneg hε d
  have hM01 : ∀ x' y, 0 ≤ M x' y ∧ M x' y ≤ 1 :=
    fun x' y => ⟨isBinaryRealMat_nonneg hM x' y, isBinaryRealMat_le_one hM x' y⟩
  have hU_bound :=
    abs_approxGridNormURootTuple_sub_gridNorm1_rowFilteredMat_le hX hS hΩ hε hδ hM01 hd x
  have hsum : α_grid / 2 + ((α_grid / 2) ^ d) ^ (1 / (d : ℝ)) = α_grid := by
    rw [pow_rpow_inv_natCast hε hd]
    ring
  rw [hsum, gridNorm1_rowFilteredMat_eq X Y hM x hd] at hU_bound
  rw [approxGridNormValTuple_eq_div X Y k Ω (isBinaryRealMat_nonneg hM) hd x]
  have hsub : approxGridNormURootTuple X k Ω M d x / rowDeg Y M x -
      gridNorm1 X (realRowNbr Y M x) M d =
      (approxGridNormURootTuple X k Ω M d x -
        rowDeg Y M x * gridNorm1 X (realRowNbr Y M x) M d) / rowDeg Y M x := by
    rw [sub_div, mul_div_cancel_left₀ _ hdeg.ne']
  rw [hsub, abs_div, abs_of_pos hdeg]
  exact div_le_div_of_nonneg_right hU_bound hdeg.le

/-- **Unconditional Chebyshev Tuple-Sampler Accuracy Instantiation of Lemma 4.1 (`lem_approx_grid_norm_chebyshev_tuple`)**:
Instantiating `lem_approx_grid_norm_tuple` with `constructChebyshevTupleSampler Y invEps invDelta`
(whose sample tuple length `k = chebyshevSampleSize invEps invDelta = (invEps + 1)^2 * (invDelta + 1)`
is independent of $|Y|$, while the full product family $\Omega = Y^k$ has cardinality
$|\Omega| = |Y|^k$; mathematical accuracy statement only, with no running-time clause) yields the
accuracy bound of Lemma 4.1 unconditionally for any nonempty $X, Y$. -/
theorem lem_approx_grid_norm_chebyshev_tuple
    {X : Finset α} (hX : X.Nonempty) {Y : Finset β} (hY : Y.Nonempty)
    (invEps invDelta : ℕ) {α_grid : ℝ} (hα : 0 ≤ α_grid) {d : ℕ} (hd : 1 ≤ d)
    (hε : (1 : ℝ) / ((invEps : ℝ) + 1) ≤ α_grid / 2)
    (hδ : (1 : ℝ) / ((invDelta : ℝ) + 1) ≤ (α_grid / 2) ^ d)
    {M : α → β → ℝ} (hM : IsBinaryRealMat M)
    {x : α} (hdeg : 0 < rowDeg Y M x) :
    let k := chebyshevSampleSize invEps invDelta
    let Ω := constructChebyshevTupleSampler Y invEps invDelta
    0 ≤ approxGridNormVTuple X Y k Ω M d x ∧
    |approxGridNormValTuple X Y k Ω M d x - gridNorm1 X (realRowNbr Y M x) M d| ≤
      α_grid / rowDeg Y M x := by
  have hS := isTupleObliviousSampler_constructChebyshevTupleSampler Y invEps invDelta hε hδ
  have hΩ : (constructChebyshevTupleSampler Y invEps invDelta).Nonempty := by
    refine ⟨fun _ => hY.choose, ?_⟩
    exact Fintype.mem_piFinset.mpr (fun _ => hY.choose_spec)
  exact lem_approx_grid_norm_tuple hX hΩ hα hd hS hM hdeg

end LemmaApproxGridNorm

/-!
## 6. Cost-Tracked Common-Denominator Rational Execution of Algorithm 2
-/

section TrackedExecution

variable {α β : Type*}

/-- Embed a rational numerator/denominator pair `(num, den) : ℕ × ℕ` into `ℝ`. -/
noncomputable def ratPairToReal (q : ℕ × ℕ) : ℝ :=
  (q.1 : ℝ) / (q.2 : ℝ)

lemma sum_toList_map {γ : Type*} (s : Finset γ) (f : γ → ℕ) :
    (s.toList.map f).sum = ∑ x ∈ s, f x := by
  rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
  rfl

lemma list_map_sum_div_const {γ : Type*} (L : List γ) (f : γ → ℝ) (c : ℝ) :
    (L.map (fun x => f x / c)).sum = (L.map f).sum / c := by
  induction L with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.sum_cons, ih, add_div]

lemma list_map_nat_cast_sum {γ : Type*} (L : List γ) (f : γ → ℕ) :
    (L.map (fun x => (f x : ℝ))).sum = (((L.map f).sum : ℕ) : ℝ) := by
  induction L with
  | nil => simp
  | cons a tl ih =>
    simp [ih]

lemma list_map_sum_le_length_mul {γ : Type*} (L : List γ) (f : γ → ℕ) (B : ℕ)
    (hf : ∀ z ∈ L, f z ≤ B) :
    (L.map f).sum ≤ L.length * B := by
  induction L with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have ha : f a ≤ B := hf a List.mem_cons_self
    have htl := ih (fun z hz => hf z (List.mem_cons_of_mem a hz))
    calc
      f a + (tl.map f).sum ≤ B + tl.length * B := Nat.add_le_add ha htl
      _ = (tl.length + 1) * B := by ring

/-- List of all $d$-tuples (`List β` of length `d`) with coordinates in `T_list : List β`,
enumerating $T^d$ in `(|T_list|)^d` entries (Algorithm 2, Line 2 `\label{line:est-u}`, `paper.tex`, §4.1). -/
def piList (T_list : List β) : ℕ → List (List β)
  | 0 => [[]]
  | d + 1 =>
    let rest := piList T_list d
    T_list.flatMap (fun y => rest.map (fun ys => y :: ys))

@[simp]
lemma piList_length (T_list : List β) (d : ℕ) :
    (piList T_list d).length = T_list.length ^ d := by
  induction d with
  | zero => simp [piList]
  | succ d ih =>
    simp only [piList, List.length_flatMap, List.length_map,
      List.map_const', List.sum_replicate, smul_eq_mul, ih, pow_succ']

/-- Boolean product $\prod_{y \in ys} \mathbf{1}_{A(x, y)} \in \{0, 1\}$ for row `x` and tuple `ys`. -/
def prodTupleBool (A : α → β → Bool) (x : α) : List β → ℕ
  | [] => 1
  | y :: ys => (if A x y then 1 else 0) * prodTupleBool A x ys

/-- Cost-tracked Boolean product $\prod_{y \in ys} \mathbf{1}_{A(x, y)} \in \{0, 1\}$ in `CostM`. -/
def prodTupleBoolTracked (A : α → β → Bool) (x : α) : List β → CostM ℕ
  | [] => retTracked 1
  | y :: ys =>
    CostM.bind (prodTupleBoolTracked A x ys) (fun p =>
      retTracked (if A x y then p else 0))

@[simp]
lemma prodTupleBoolTracked_fst (A : α → β → Bool) (x : α) (ys : List β) :
    (prodTupleBoolTracked A x ys).1 = prodTupleBool A x ys := by
  induction ys with
  | nil => rfl
  | cons y tl ih =>
    cases hA : A x y <;> simp [prodTupleBoolTracked, prodTupleBool, CostM.bind, retTracked, ih, hA]

lemma list_map_sum_add_nat {γ : Type*} (L : List γ) (f g : γ → ℕ) :
    (L.map (fun z => f z + g z)).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

lemma list_map_sum_mul_left_nat {γ : Type*} (L : List γ) (c : ℕ) (f : γ → ℕ) :
    (L.map (fun z => c * f z)).sum = c * (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

lemma list_map_sum_mul_right_nat {γ : Type*} (L : List γ) (f : γ → ℕ) (c : ℕ) :
    (L.map (fun z => f z * c)).sum = (L.map f).sum * c := by
  induction L with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

lemma list_sum_map_comm_nat {γ δ : Type*} (L₁ : List γ) (L₂ : List δ) (f : γ → δ → ℕ) :
    (L₁.map (fun u => (L₂.map (fun v => f u v)).sum)).sum =
      (L₂.map (fun v => (L₁.map (fun u => f u v)).sum)).sum := by
  induction L₁ with
  | nil =>
    simp [List.map_const']
  | cons a tl ih =>
    simp only [List.map_cons, List.sum_cons, ih, ← list_map_sum_add_nat]

lemma list_sum_flatMap_map_nat {γ δ ε : Type*} (L₁ : List γ) (L₂ : List δ)
    (g : γ → δ → ε) (h : ε → ℕ) :
    ((L₁.flatMap (fun y => L₂.map (g y))).map h).sum =
      (L₁.map (fun y => (L₂.map (fun ys => h (g y ys))).sum)).sum := by
  induction L₁ with
  | nil => simp
  | cons a tl ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_map,
      Function.comp_def, List.map_cons, List.sum_cons, ih]

lemma sum_piList_prodTupleBool_mul (T_list : List β) (A : α → β → Bool) (x' x : α) (d : ℕ) :
    ((piList T_list d).map (fun ys => prodTupleBool A x' ys * prodTupleBool A x ys)).sum =
      ((T_list.map (fun y => if A x' y && A x y then 1 else 0)).sum) ^ d := by
  induction d with
  | zero => simp [piList, prodTupleBool]
  | succ d ih =>
    simp only [piList, list_sum_flatMap_map_nat, prodTupleBool, pow_succ']
    have hcongr :
        (T_list.map (fun y =>
          ((piList T_list d).map (fun ys =>
            ((if A x' y then 1 else 0) * prodTupleBool A x' ys) *
              ((if A x y then 1 else 0) * prodTupleBool A x ys))).sum)).sum =
        (T_list.map (fun y =>
          (if A x' y && A x y then 1 else 0) *
            ((piList T_list d).map (fun ys =>
              prodTupleBool A x' ys * prodTupleBool A x ys)).sum)).sum := by
      congr 1
      refine List.map_congr_left (fun y _ => ?_)
      rw [← list_map_sum_mul_left_nat]
      congr 1
      refine List.map_congr_left (fun ys _ => ?_)
      cases A x' y <;> cases A x y <;> simp
    rw [hcongr]
    simp_rw [ih]
    rw [list_map_sum_mul_right_nat]

lemma mem_piList_length (T_list : List β) (d : ℕ) {ys : List β} (hys : ys ∈ piList T_list d) :
    ys.length = d := by
  induction d generalizing ys with
  | zero =>
    simp only [piList, List.mem_singleton] at hys
    subst hys
    rfl
  | succ d ih =>
    simp only [piList, List.mem_flatMap, List.mem_map] at hys
    rcases hys with ⟨y, _, ys', hys', rfl⟩
    simp [ih hys']

@[simp]
lemma prodTupleBoolTracked_snd (A : α → β → Bool) (x : α) (ys : List β) :
    (prodTupleBoolTracked A x ys).2 = ys.length + 1 := by
  induction ys with
  | nil => rfl
  | cons y tl ih =>
    simp only [prodTupleBoolTracked, CostM.bind_snd, retTracked_snd, List.length_cons, ih]

/-- Algorithm 2, Line 2 (`\label{line:est-u}`, `paper.tex`, §4.1):
Precomputes the $d$-tuple column-intersection table `[(ys, c_{T, ys}) : ys ∈ T^d]` over `X : Finset α`
via `sumFinsetTracked` and `prodTupleBoolTracked` in exact step cost
`(|T|^d) * (|X| * (d + 1) + 3) + 1`. -/
def buildTupleTableFinsetTracked (X : Finset α) (A : α → β → Bool) (d : ℕ)
    (T_list : List β) : CostM (List (List β × ℕ)) :=
  mapListTracked (fun ys =>
    CostM.bind (sumFinsetTracked X (fun x' => prodTupleBoolTracked A x' ys)) (fun c =>
      retTracked (ys, c))) (piList T_list d)

@[simp]
lemma buildTupleTableFinsetTracked_fst (X : Finset α) (A : α → β → Bool) (d : ℕ)
    (T_list : List β) :
    (buildTupleTableFinsetTracked X A d T_list).1 =
      (piList T_list d).map (fun ys =>
        (ys, ∑ x' ∈ X, prodTupleBool A x' ys)) := by
  simp [buildTupleTableFinsetTracked, CostM.bind, retTracked]

theorem buildTupleTableFinsetTracked_snd_eq (X : Finset α) (A : α → β → Bool) (d : ℕ)
    (T_list : List β) :
    (buildTupleTableFinsetTracked X A d T_list).2 =
      (T_list.length ^ d) * (X.card * (d + 1) + 3) + 1 := by
  unfold buildTupleTableFinsetTracked
  rw [mapListTracked_snd_const _ (X.card * (d + 1) + 2) (piList T_list d), piList_length]
  intro ys hys
  simp only [CostM.bind_snd, retTracked_snd]
  have hlen : ys.length = d := mem_piList_length T_list d hys
  rw [sumFinsetTracked_snd_const X _ (d + 1)]
  intro x' _
  rw [prodTupleBoolTracked_snd, hlen]

/-- Algorithm 2, Line 3 (`\label{line:est-v}`, `paper.tex`, §4.1):
Contracts a precomputed tuple table `table : List (List β × ℕ)` against row `x ∈ X` via
`foldlListTracked` and `prodTupleBoolTracked`. -/
def contractTupleTableSimpleTracked (A : α → β → Bool) (x : α)
    (table : List (List β × ℕ)) : CostM ℕ :=
  foldlListTracked (fun acc entry =>
    CostM.bind (prodTupleBoolTracked A x entry.1) (fun px =>
      retTracked (if px = 0 then acc else acc + entry.2))) 0 table

private lemma prodTupleBool_eq_zero_or_one (A : α → β → Bool) (x : α) (ys : List β) :
    prodTupleBool A x ys = 0 ∨ prodTupleBool A x ys = 1 := by
  induction ys with
  | nil => right; rfl
  | cons y tl ih =>
    rcases ih with h0 | h1
    · left; simp [prodTupleBool, h0]
    · cases A x y <;> simp [prodTupleBool, h1]

private lemma add_ite_prodTupleBool_eq_mul (A : α → β → Bool) (x : α) (ys : List β) (acc m : ℕ) :
    (if prodTupleBool A x ys = 0 then acc else acc + m) = acc + m * prodTupleBool A x ys := by
  rcases prodTupleBool_eq_zero_or_one A x ys with h0 | h1
  · simp [h0]
  · simp [h1]

private lemma foldl_add_map_eq_sum {γ : Type*} (f : γ → ℕ) (L : List γ) (init : ℕ) :
    L.foldl (fun acc z => acc + f z) init = init + (L.map f).sum := by
  induction L generalizing init with
  | nil => simp
  | cons a tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
    omega

@[simp]
lemma contractTupleTableSimpleTracked_fst (A : α → β → Bool) (x : α)
    (table : List (List β × ℕ)) :
    (contractTupleTableSimpleTracked A x table).1 =
      (table.map (fun entry => entry.2 * prodTupleBool A x entry.1)).sum := by
  unfold contractTupleTableSimpleTracked
  rw [foldlListTracked_fst]
  simp only [CostM.bind_fst, prodTupleBoolTracked_fst, retTracked_fst,
    add_ite_prodTupleBool_eq_mul]
  rw [foldl_add_map_eq_sum (fun entry : List β × ℕ => entry.2 * prodTupleBool A x entry.1) table 0,
    Nat.zero_add]

theorem contractTupleTableSimpleTracked_buildTupleTableFinsetTracked_snd_eq
    (X : Finset α) (A : α → β → Bool) (d : ℕ) (x : α) (T_list : List β) :
    (contractTupleTableSimpleTracked A x
      (buildTupleTableFinsetTracked X A d T_list).1).2 =
      (T_list.length ^ d) * (d + 3) + 1 := by
  unfold contractTupleTableSimpleTracked
  rw [foldlListTracked_snd_const _ (d + 2) 0 (buildTupleTableFinsetTracked X A d T_list).1]
  · rw [buildTupleTableFinsetTracked_fst, List.length_map, piList_length]
  · intro acc entry hentry
    rw [buildTupleTableFinsetTracked_fst, List.mem_map] at hentry
    rcases hentry with ⟨ys, hys, rfl⟩
    simp only [CostM.bind_snd, prodTupleBoolTracked_snd, retTracked_snd,
      mem_piList_length T_list d hys]

/-- Cost-tracked contraction of a family of pre-tabulated $d$-tuple tables for a single row $x \in X$
(`paper.tex`, Section 4.1, Algorithm 2, Line 3 `\label{line:est-v}`): sums `contractTupleTableSimpleTracked A x table`
across all `table ∈ tables` via `foldlListTracked`. -/
def contractTupleTableFamilySimpleTracked (A : α → β → Bool) (x : α)
    (tables : List (List (List β × ℕ))) : CostM ℕ :=
  foldlListTracked (fun acc table =>
    CostM.bind (contractTupleTableSimpleTracked A x table) (fun v =>
      retTracked (acc + v))) 0 tables

lemma contractTupleTableFamilySimpleTracked_fst (A : α → β → Bool) (x : α)
    (tables : List (List (List β × ℕ))) :
    (contractTupleTableFamilySimpleTracked A x tables).1 =
      (tables.map (fun table => (contractTupleTableSimpleTracked A x table).1)).sum := by
  unfold contractTupleTableFamilySimpleTracked
  rw [foldlListTracked_fst]
  simp only [CostM.bind_fst, retTracked_fst]
  rw [foldl_add_map_eq_sum (fun table => (contractTupleTableSimpleTracked A x table).1) tables 0,
    Nat.zero_add]

/-- Cost-tracked per-row contraction and rational-pair assembly for $V_x = U_x / (\deg_A(x))^d$
in Algorithm 2 Line 3 (`\label{line:est-v}`, `paper.tex`, §4.1):
1. Contracts the precomputed tuple tables `tables` for row `x` via
   `contractTupleTableFamilySimpleTracked A x tables`,
2. Scans `Y` via `filterFinsetByTracked Y (fun y => A x y)` to compute `rowNbr Y A x`
   (charging `Y.card + 1`),
3. Computes `(rowNbr Y A x).card ^ d` via `powNatTracked nbrs.card d`,
4. Assembles the common-denominator rational pair
   `(totalNum * yPow, (T_fam_len * X.card * sPow) * degPow)` in `CostM` via four `mulNatTracked`
   calls. -/
def approxGridNormVxRowPairTracked (X : Finset α) (Y : Finset β)
    (T_fam_len sPow yPow : ℕ) (A : α → β → Bool) (d : ℕ)
    (tables : List (List (List β × ℕ))) (x : α) : CostM (ℕ × ℕ) :=
  CostM.bind (contractTupleTableFamilySimpleTracked A x tables) (fun totalNum =>
    CostM.bind (filterFinsetByTracked Y (fun y => A x y)) (fun nbrs =>
      CostM.bind (powNatTracked nbrs.card d) (fun degPow =>
        CostM.bind (mulNatTracked totalNum yPow) (fun num =>
          CostM.bind (mulNatTracked T_fam_len X.card) (fun den₀ =>
            CostM.bind (mulNatTracked den₀ sPow) (fun den₁ =>
              CostM.bind (mulNatTracked den₁ degPow) (fun den =>
                retTracked (num, den))))))))

@[simp]
lemma approxGridNormVxRowPairTracked_fst (X : Finset α) (Y : Finset β)
    (T_fam_len sPow yPow : ℕ) (A : α → β → Bool) (d : ℕ)
    (tables : List (List (List β × ℕ))) (x : α) :
    (approxGridNormVxRowPairTracked X Y T_fam_len sPow yPow A d tables x).1 =
      ((contractTupleTableFamilySimpleTracked A x tables).1 * yPow,
       (T_fam_len * X.card * sPow) * ((rowNbr Y A x).card ^ d)) := by
  simp [approxGridNormVxRowPairTracked, CostM.bind_fst, filterFinsetByTracked_fst,
    powNatTracked_fst, mulNatTracked_fst, retTracked_fst, rowNbr]

lemma approxGridNormVxRowPairTracked_snd_le_of_bounds
    (X : Finset α) (Y : Finset β) (T_fam_len sPow yPow : ℕ)
    (A : α → β → Bool) (d B : ℕ) (tables : List (List (List β × ℕ))) (x : α)
    (h_num : (contractTupleTableFamilySimpleTracked A x tables).1 ≤ (T_fam_len * X.card) * (B ^ d))
    (h_sPow : sPow ≤ B ^ d) (h_yPow : yPow ≤ Y.card ^ d) :
    (approxGridNormVxRowPairTracked X Y T_fam_len sPow yPow A d tables x).2 ≤
      (contractTupleTableFamilySimpleTracked A x tables).2 +
        (d + 1) ^ 3 * (85 * (T_fam_len + X.card + Y.card + B) + 107) := by
  unfold approxGridNormVxRowPairTracked
  simp only [CostM.bind_snd, filterFinsetByTracked_snd, filterFinsetByTracked_fst,
    powNatTracked_fst, mulNatTracked_fst, retTracked_snd]
  set totalNum := (contractTupleTableFamilySimpleTracked A x tables).1
  set bL := bitLengthNat T_fam_len
  set bX := bitLengthNat X.card
  set bY := bitLengthNat Y.card
  set bB := bitLengthNat B
  set S_bits := bL + bX + bY + bB + 1
  set M := (d + 1) * S_bits
  have h_nbrs_le : (Y.filter (fun y => A x y)).card ≤ Y.card := Finset.card_filter_le Y _
  have h_b_totalNum : bitLengthNat totalNum ≤ M := by
    have h1 : bitLengthNat totalNum ≤ bitLengthNat ((T_fam_len * X.card) * (B ^ d)) :=
      bitLengthNat_mono h_num
    have h2 : bitLengthNat ((T_fam_len * X.card) * (B ^ d)) ≤
        bitLengthNat (T_fam_len * X.card) + bitLengthNat (B ^ d) :=
      bitLengthNat_mul_le _ _
    have h3 : bitLengthNat (T_fam_len * X.card) ≤ bL + bX := bitLengthNat_mul_le _ _
    have h4 : bitLengthNat (B ^ d) ≤ d * bB + 1 := bitLengthNat_pow_le B d
    dsimp [M, S_bits]; nlinarith
  have h_b_yPow : bitLengthNat yPow ≤ M := by
    have h1 : bitLengthNat yPow ≤ bitLengthNat (Y.card ^ d) := bitLengthNat_mono h_yPow
    have h2 : bitLengthNat (Y.card ^ d) ≤ d * bY + 1 := bitLengthNat_pow_le Y.card d
    dsimp [M, S_bits]; nlinarith
  have h_b_L : bitLengthNat T_fam_len ≤ M := by dsimp [M, S_bits, bL]; nlinarith
  have h_b_X : bitLengthNat X.card ≤ M := by dsimp [M, S_bits, bX]; nlinarith
  have h_b_den0 : bitLengthNat (T_fam_len * X.card) ≤ M := by
    have h1 : bitLengthNat (T_fam_len * X.card) ≤ bL + bX := bitLengthNat_mul_le _ _
    dsimp [M, S_bits]; nlinarith
  have h_b_sPow : bitLengthNat sPow ≤ M := by
    have h1 : bitLengthNat sPow ≤ bitLengthNat (B ^ d) := bitLengthNat_mono h_sPow
    have h2 : bitLengthNat (B ^ d) ≤ d * bB + 1 := bitLengthNat_pow_le B d
    dsimp [M, S_bits]; nlinarith
  have h_b_den1 : bitLengthNat (T_fam_len * X.card * sPow) ≤ M := by
    have h1 : bitLengthNat (T_fam_len * X.card * sPow) ≤
        bitLengthNat (T_fam_len * X.card) + bitLengthNat sPow := bitLengthNat_mul_le _ _
    have h2 : bitLengthNat (T_fam_len * X.card) ≤ bL + bX := bitLengthNat_mul_le _ _
    have h3 : bitLengthNat sPow ≤ bitLengthNat (B ^ d) := bitLengthNat_mono h_sPow
    have h4 : bitLengthNat (B ^ d) ≤ d * bB + 1 := bitLengthNat_pow_le B d
    dsimp [M, S_bits]; nlinarith
  have h_b_degPow : bitLengthNat ((Y.filter (fun y => A x y)).card ^ d) ≤ M := by
    have h1 : bitLengthNat ((Y.filter (fun y => A x y)).card ^ d) ≤
        bitLengthNat (Y.card ^ d) := bitLengthNat_mono (Nat.pow_le_pow_left h_nbrs_le d)
    have h2 : bitLengthNat (Y.card ^ d) ≤ d * bY + 1 := bitLengthNat_pow_le Y.card d
    dsimp [M, S_bits]; nlinarith
  have h_mul1 := mulNatTracked_snd_le_of_bitLength_le h_b_totalNum h_b_yPow
  have h_mul2 := mulNatTracked_snd_le_of_bitLength_le h_b_L h_b_X
  have h_mul3 := mulNatTracked_snd_le_of_bitLength_le h_b_den0 h_b_sPow
  have h_mul4 := mulNatTracked_snd_le_of_bitLength_le h_b_den1 h_b_degPow
  have h_pow : (powNatTracked (Y.filter (fun y => A x y)).card d).2 ≤
      (d + 1) ^ 3 * (4 * Y.card + 1) :=
    (powNatTracked_snd_mono h_nbrs_le le_rfl).trans (powNatTracked_snd_le_linear Y.card d)
  have h_M2 : M ^ 2 ≤ (d + 1) ^ 3 * (20 * (T_fam_len + X.card + Y.card + B) + 25) := by
    have h_eq : M ^ 2 = (d + 1) ^ 2 * S_bits ^ 2 := by dsimp [M]; ring
    have h_S2 : S_bits ^ 2 ≤ 20 * (T_fam_len + X.card + Y.card + B) + 25 :=
      five_term_sq_bound T_fam_len X.card Y.card B
    have h_d2_d3 : (d + 1) ^ 2 ≤ (d + 1) ^ 3 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    calc
      M ^ 2 = (d + 1) ^ 2 * S_bits ^ 2 := h_eq
      _ ≤ (d + 1) ^ 3 * (20 * (T_fam_len + X.card + Y.card + B) + 25) :=
        Nat.mul_le_mul h_d2_d3 h_S2
  have hd3_pos : 1 ≤ (d + 1) ^ 3 := Nat.one_le_pow 3 (d + 1) (by omega)
  have hY6 : Y.card + 6 ≤ (d + 1) ^ 3 * (Y.card + 6) :=
    Nat.le_mul_of_pos_left (Y.card + 6) hd3_pos
  have h_comb :
      4 * ((d + 1) ^ 3 * (20 * (T_fam_len + X.card + Y.card + B) + 25)) +
          (d + 1) ^ 3 * (4 * Y.card + 1) + (d + 1) ^ 3 * (Y.card + 6) ≤
        (d + 1) ^ 3 * (85 * (T_fam_len + X.card + Y.card + B) + 107) := by
    have h_eq :
        (d + 1) ^ 3 * (85 * (T_fam_len + X.card + Y.card + B) + 107) =
          4 * ((d + 1) ^ 3 * (20 * (T_fam_len + X.card + Y.card + B) + 25)) +
            (d + 1) ^ 3 * (4 * Y.card + 1) + (d + 1) ^ 3 * (Y.card + 6) +
            5 * ((d + 1) ^ 3 * (T_fam_len + X.card + B)) := by
      ring
    omega
  omega

/-- Pure integer numerator $\sum_{x' \in X} \left(\sum_{y \in T} \mathbf{1}_{A(x', y) \wedge A(x, y)}\right)^d$
for a single sample sequence $T \in \mathcal{T}$ (`List β`) and row $x \in X$ (Algorithm 2, Lines 2–3). -/
def sampleMomentNumSeq (X : Finset α) (T : List β) (A : α → β → Bool) (d : ℕ) (x : α) : ℕ :=
  ∑ x' ∈ X, ((T.map (fun y => if A x' y && A x y then 1 else 0)).sum) ^ d

theorem contractTupleTableSimpleTracked_buildTupleTableFinsetTracked_seq_fst
    (X : Finset α) (T : List β) (A : α → β → Bool) (d : ℕ) (x : α) :
    (contractTupleTableSimpleTracked A x
      (buildTupleTableFinsetTracked X A d T).1).1 =
      sampleMomentNumSeq X T A d x := by
  simp only [contractTupleTableSimpleTracked_fst, buildTupleTableFinsetTracked_fst,
    List.map_map, Function.comp_def, sampleMomentNumSeq]
  simp_rw [← sum_toList_map X]
  simp_rw [← list_map_sum_mul_right_nat]
  rw [list_sum_map_comm_nat]
  congr 1
  refine List.map_congr_left (fun x' _ => ?_)
  exact sum_piList_prodTupleBool_mul T A x' x d

theorem contractTupleTableFamilySimpleTracked_build_seq_fst
    (X : Finset α) (T_fam : List (List β)) (A : α → β → Bool) (d : ℕ) (x : α) :
    (contractTupleTableFamilySimpleTracked A x
      (T_fam.map (fun T => (buildTupleTableFinsetTracked X A d T).1))).1 =
      (T_fam.map (fun T => sampleMomentNumSeq X T A d x)).sum := by
  rw [contractTupleTableFamilySimpleTracked_fst, List.map_map]
  congr 1
  refine List.map_congr_left (fun T _ => ?_)
  exact contractTupleTableSimpleTracked_buildTupleTableFinsetTracked_seq_fst X T A d x

theorem contractTupleTableFamilySimpleTracked_build_seq_snd_le
    (X : Finset α) (T_fam : List (List β)) (A : α → β → Bool) (d B : ℕ) (x : α)
    (hB : ∀ T ∈ T_fam, T.length ≤ B) :
    (contractTupleTableFamilySimpleTracked A x
      (T_fam.map (fun T => (buildTupleTableFinsetTracked X A d T).1))).2 ≤
      T_fam.length * ((B ^ d) * (d + 3) + 3) + 1 := by
  unfold contractTupleTableFamilySimpleTracked
  have h1 := foldlListTracked_snd_le_const
    (fun acc table =>
      CostM.bind (contractTupleTableSimpleTracked A x table) (fun v => retTracked (acc + v)))
    ((B ^ d) * (d + 3) + 2) 0
    (T_fam.map (fun T => (buildTupleTableFinsetTracked X A d T).1))
  rw [List.length_map] at h1
  apply h1
  intro acc table htable
  rw [List.mem_map] at htable
  rcases htable with ⟨T, hT, rfl⟩
  simp only [CostM.bind_snd, retTracked_snd]
  rw [contractTupleTableSimpleTracked_buildTupleTableFinsetTracked_snd_eq]
  have hpow : T.length ^ d ≤ B ^ d := Nat.pow_le_pow_left (hB T hT) d
  nlinarith

lemma list_sum_boole_le_length (T : List β) (p : β → Bool) :
    (T.map (fun y => if p y then 1 else 0)).sum ≤ T.length := by
  induction T with
  | nil => simp
  | cons y tl ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    cases p y <;> simp <;> omega

lemma sampleMomentNumSeq_le (X : Finset α) {T : List β} {sampleSize : ℕ}
    (hT : T.length ≤ sampleSize) (A : α → β → Bool) (d : ℕ) (x : α) :
    sampleMomentNumSeq X T A d x ≤ X.card * sampleSize ^ d := by
  unfold sampleMomentNumSeq
  calc
    ∑ x' ∈ X, ((T.map (fun y => if A x' y && A x y then 1 else 0)).sum) ^ d
      ≤ ∑ _x' ∈ X, sampleSize ^ d := by
        apply Finset.sum_le_sum
        intro x' _
        exact Nat.pow_le_pow_left
          (le_trans (list_sum_boole_le_length T (fun y => A x' y && A x y)) hT) d
    _ = X.card * sampleSize ^ d := by
        rw [Finset.sum_const, smul_eq_mul]

/-- **Common-Denominator Rational Pair for Sequence-Sampler $V_x = U_x / (\deg_A(x))^d$ (`paper.tex`, §4.1)**:
For a uniform-sample-length family `T_fam : List (List β)` where every sample sequence $T \in \mathcal{T}$
has length `sampleSize`, all $|\mathcal{T}|$ samples share the exact same common denominator
$|X| \cdot \text{sampleSize}^d$. -/
def approxGridNormVxSeqCommonDenomPair (X : Finset α) (Y : Finset β) (T_fam : List (List β))
    (sampleSize : ℕ) (A : α → β → Bool) (d : ℕ) (x : α) : ℕ × ℕ :=
  let totalNum := (T_fam.map (fun T => sampleMomentNumSeq X T A d x)).sum
  let deg_x := (rowNbr Y A x).card
  (totalNum * (Y.card ^ d), (T_fam.length * X.card * (sampleSize ^ d)) * (deg_x ^ d))

theorem approxGridNormVxRowPairTracked_build_seq_fst
    (X : Finset α) (Y : Finset β) (T_fam : List (List β))
    (sampleSize : ℕ) (A : α → β → Bool) (d : ℕ) (x : α) :
    (approxGridNormVxRowPairTracked X Y T_fam.length (sampleSize ^ d) (Y.card ^ d) A d
      (T_fam.map (fun T => (buildTupleTableFinsetTracked X A d T).1)) x).1 =
      approxGridNormVxSeqCommonDenomPair X Y T_fam sampleSize A d x := by
  rw [approxGridNormVxRowPairTracked_fst, contractTupleTableFamilySimpleTracked_build_seq_fst]
  rfl

theorem approxGridNormVxRowPairTracked_build_seq_snd_le
    (X : Finset α) (Y : Finset β) (T_fam : List (List β))
    (sPow yPow : ℕ) (A : α → β → Bool) (d B : ℕ) (x : α)
    (hB : ∀ T ∈ T_fam, T.length ≤ B)
    (hsPow : sPow ≤ B ^ d) (hyPow : yPow ≤ Y.card ^ d) :
    (approxGridNormVxRowPairTracked X Y T_fam.length sPow yPow A d
      (T_fam.map (fun T => (buildTupleTableFinsetTracked X A d T).1)) x).2 ≤
      T_fam.length * ((B ^ d) * (d + 3) + 3) + 1 +
        (d + 1) ^ 3 * (85 * (T_fam.length + X.card + Y.card + B) + 107) := by
  have h_num :
      (contractTupleTableFamilySimpleTracked A x
        (T_fam.map (fun T => (buildTupleTableFinsetTracked X A d T).1))).1 ≤
        (T_fam.length * X.card) * (B ^ d) := by
    rw [contractTupleTableFamilySimpleTracked_build_seq_fst]
    calc
      (T_fam.map (fun T => sampleMomentNumSeq X T A d x)).sum
        ≤ T_fam.length * (X.card * B ^ d) :=
          list_map_sum_le_length_mul T_fam _ _ (fun T hT => sampleMomentNumSeq_le X (hB T hT) A d x)
      _ = (T_fam.length * X.card) * (B ^ d) := by ring
  have h1 := approxGridNormVxRowPairTracked_snd_le_of_bounds X Y T_fam.length sPow yPow A d B
    (T_fam.map (fun T => (buildTupleTableFinsetTracked X A d T).1)) x h_num hsPow hyPow
  have h2 := contractTupleTableFamilySimpleTracked_build_seq_snd_le X T_fam A d B x hB
  omega

/-- Unconditional common-denominator equivalence for `approxGridNormVxSeqCommonDenomPair`:
whenever every sample sequence $T \in \mathcal{T}$ has uniform length `T.length = sampleSize`,
`ratPairToReal (approxGridNormVxSeqCommonDenomPair X Y T_fam sampleSize A d x)` equals
`approxGridNormVSeq X Y T_fam (bmatToReal A) d x`. -/
theorem ratPairToReal_approxGridNormVxSeqCommonDenomPair_unconditional
    (X : Finset α) (Y : Finset β)
    {T_fam : List (List β)} {sampleSize : ℕ}
    (hT_len : ∀ T ∈ T_fam, T.length = sampleSize)
    (A : α → β → Bool) (d : ℕ) (x : α) :
    ratPairToReal (approxGridNormVxSeqCommonDenomPair X Y T_fam sampleSize A d x) =
      approxGridNormVSeq X Y T_fam (bmatToReal A) d x := by
  have hsample : ∀ T ∈ T_fam,
      expectSet X (fun x' => (expectSeq T (fun y => rowFilteredMat (bmatToReal A) x x' y)) ^ d) =
        (sampleMomentNumSeq X T A d x : ℝ) / ((X.card : ℝ) * (sampleSize : ℝ) ^ d) := by
    intro T hT
    unfold expectSet sampleMomentNumSeq
    have hrow : ∀ x' : α,
        (expectSeq T (fun y => rowFilteredMat (bmatToReal A) x x' y)) ^ d =
          ((((T.map (fun y => if A x' y && A x y then 1 else 0)).sum) ^ d : ℕ) : ℝ) /
            ((sampleSize : ℝ) ^ d) := by
      intro x'
      unfold expectSeq
      have hmap_sum :
          (T.map (fun y => rowFilteredMat (bmatToReal A) x x' y)).sum =
            (((T.map (fun y => if A x' y && A x y then 1 else 0)).sum : ℕ) : ℝ) := by
        rw [← list_map_nat_cast_sum]
        congr 1
        refine List.map_congr_left (fun y _ => ?_)
        rw [← bmatToReal_bmatRowFiltered A x]
        unfold bmatToReal boolToReal bmatRowFiltered
        cases A x' y <;> cases A x y <;> simp
      rw [hmap_sum, hT_len T hT, div_pow, Nat.cast_pow]
    simp_rw [hrow, ← Finset.sum_div, div_div, mul_comm ((sampleSize : ℝ) ^ d) (X.card : ℝ)]
    push_cast
    rfl
  have hmap : T_fam.map (fun T =>
      expectSet X (fun x' => (expectSeq T (fun y => rowFilteredMat (bmatToReal A) x x' y)) ^ d)) =
    T_fam.map (fun T =>
      (sampleMomentNumSeq X T A d x : ℝ) / ((X.card : ℝ) * (sampleSize : ℝ) ^ d)) :=
    List.map_congr_left hsample
  dsimp only [approxGridNormVxSeqCommonDenomPair, ratPairToReal]
  change ((((T_fam.map (fun T => sampleMomentNumSeq X T A d x)).sum * Y.card ^ d : ℕ) : ℝ) /
      ((((T_fam.length * X.card * sampleSize ^ d) * (rowNbr Y A x).card ^ d : ℕ) : ℝ))) =
    approxGridNormVSeq X Y T_fam (bmatToReal A) d x
  unfold approxGridNormVSeq approxGridNormUSeq
  rw [← expectList_expectSet_comm, rowDeg_bmatToReal_eq_card_rowNbr_div]
  unfold expectList
  rw [hmap, list_map_sum_div_const, list_map_nat_cast_sum]
  push_cast
  rw [div_pow, div_div_eq_mul_div, div_div, mul_div_mul_comm]
  ring

end TrackedExecution

end BMMGrid
