import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Preliminaries, Matrix Notation, and Grid Norms (`BMMGrid/Defs.lean`)

This module formalizes Section 3.1 and Definition 3.1 (`\label{def:grid-norm}`) of
`paper.tex` (§3.1–§3.2):
1. Uniform expectations `expectSet` over finite sets.
2. Binary and real matrices on finite vertex sets `X, Y`, non-zeros `bmatNnz`,
   density `matDensity` ($\mathbb{E}[A]$), normalized row/column degrees `rowDeg`/`colDeg`
   ($\deg_A(x), \deg_{A^T}(y)$), and $\varepsilon$-min-degree (`IsEpsMinDegree`).
3. Standard matrix product `stdMatMul` ($AB$), Boolean matrix product `boolMatMul` ($A \star B$),
   normalized matrix product `normMatMul` ($A \circ B$), and triangle predicate `hasTriangle`.
4. Matrix uniformity (`IsUniformMatrix`, $(\alpha, \varepsilon, \delta)$-uniformity).
5. The $(k, \ell)$-grid norm `gridNorm` ($\|A\|_{U(k, \ell)}$, Definition 3.1 `\label{def:grid-norm}`,
   `\eqref{eq:grid-norm-def}`–`\eqref{eq:grid-norm-fubini}`),
   its Fubini equivalence (`gridNormPow_eq_gridNormPowCol`), and $(\varepsilon, k, \ell)$-regularity
   (`IsGridRegular`).
-/

namespace BMMGrid

open scoped BigOperators

section Expectations

variable {α β γ : Type*}

/-- Uniform expectation $\mathbb{E}_{x \in S}[f(x)] = \frac{1}{|S|} \sum_{x \in S} f(x)$ over a
finite set `S : Finset α` (returning `0` if `S = ∅`).
Section 3.1 of `paper.tex`. -/
noncomputable def expectSet (S : Finset α) (f : α → ℝ) : ℝ :=
  (∑ x ∈ S, f x) / (S.card : ℝ)

@[simp]
lemma expectSet_empty (f : α → ℝ) : expectSet (∅ : Finset α) f = 0 := by
  simp [expectSet]

lemma expectSet_const {S : Finset α} (hS : S.Nonempty) (c : ℝ) :
    expectSet S (fun _ => c) = c := by
  unfold expectSet
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hS.card_pos.ne'
  exact mul_div_cancel_left₀ c hcard

lemma expectSet_nonneg {S : Finset α} {f : α → ℝ} (hf : ∀ x ∈ S, 0 ≤ f x) :
    0 ≤ expectSet S f := by
  unfold expectSet
  exact div_nonneg (Finset.sum_nonneg hf) (Nat.cast_nonneg _)

lemma expectSet_le_of_le {S : Finset α} (hS : S.Nonempty) {f : α → ℝ} {M : ℝ}
    (hf : ∀ x ∈ S, f x ≤ M) : expectSet S f ≤ M := by
  unfold expectSet
  have hcard : (0 : ℝ) < S.card := Nat.cast_pos.mpr hS.card_pos
  rw [div_le_iff₀ hcard]
  calc
    ∑ x ∈ S, f x ≤ ∑ _x ∈ S, M := Finset.sum_le_sum hf
    _ = M * (S.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

lemma le_expectSet_of_le {S : Finset α} (hS : S.Nonempty) {f : α → ℝ} {m : ℝ}
    (hf : ∀ x ∈ S, m ≤ f x) : m ≤ expectSet S f := by
  unfold expectSet
  have hcard : (0 : ℝ) < S.card := Nat.cast_pos.mpr hS.card_pos
  rw [le_div_iff₀ hcard]
  calc
    m * (S.card : ℝ) = ∑ _x ∈ S, m := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ x ∈ S, f x := Finset.sum_le_sum hf

lemma expectSet_add (S : Finset α) (f g : α → ℝ) :
    expectSet S (fun x => f x + g x) = expectSet S f + expectSet S g := by
  unfold expectSet
  rw [Finset.sum_add_distrib, add_div]

lemma expectSet_sub (S : Finset α) (f g : α → ℝ) :
    expectSet S (fun x => f x - g x) = expectSet S f - expectSet S g := by
  unfold expectSet
  rw [Finset.sum_sub_distrib, sub_div]

lemma expectSet_smul (S : Finset α) (c : ℝ) (f : α → ℝ) :
    expectSet S (fun x => c * f x) = c * expectSet S f := by
  unfold expectSet
  rw [← Finset.mul_sum, mul_div_assoc]

lemma expectSet_mono {S : Finset α} {f g : α → ℝ} (h : ∀ x ∈ S, f x ≤ g x) :
    expectSet S f ≤ expectSet S g := by
  unfold expectSet
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum h) (Nat.cast_nonneg _)

/-- Fubini's theorem for finite expectations:
$\mathbb{E}_{x \in X}[\mathbb{E}_{y \in Y}[f(x, y)]] = \mathbb{E}_{y \in Y}[\mathbb{E}_{x \in X}[f(x, y)]]$. -/
lemma expectSet_comm (X : Finset α) (Y : Finset β) (f : α → β → ℝ) :
    expectSet X (fun x => expectSet Y (fun y => f x y)) =
      expectSet Y (fun y => expectSet X (fun x => f x y)) := by
  unfold expectSet
  simp only [ ← Finset.sum_div]
  rw [Finset.sum_comm, div_div, div_div, mul_comm (X.card : ℝ)]

/-- Positive and negative parts $t_+ = \max(t, 0)$ and $t_- = \max(-t, 0)$
(Appendix A `\label{app:klm-proof}` of `paper.tex`). -/
def posPart (t : ℝ) : ℝ := max t 0

def negPart (t : ℝ) : ℝ := max (-t) 0

lemma posPart_nonneg (t : ℝ) : 0 ≤ posPart t := le_max_right t 0

lemma negPart_nonneg (t : ℝ) : 0 ≤ negPart t := le_max_right (-t) 0

lemma posPart_sub_negPart (t : ℝ) : posPart t - negPart t = t := by
  unfold posPart negPart
  rcases le_total 0 t with ht | ht
  · have h1 : max t 0 = t := max_eq_left ht
    have h2 : max (-t) 0 = 0 := max_eq_right (neg_nonpos.mpr ht)
    linarith
  · have h1 : max t 0 = 0 := max_eq_right ht
    have h2 : max (-t) 0 = -t := max_eq_left (neg_nonneg.mpr ht)
    linarith

lemma posPart_add_negPart (t : ℝ) : posPart t + negPart t = |t| := by
  unfold posPart negPart
  rcases le_total 0 t with ht | ht
  · rw [max_eq_left ht, max_eq_right (neg_nonpos.mpr ht), abs_of_nonneg ht, add_zero]
  · rw [max_eq_right ht, max_eq_left (neg_nonneg.mpr ht), abs_of_nonpos ht, zero_add]

end Expectations

/-!
## Matrix Operations, Density, Degrees, and Products (§3.1 of `paper.tex`)
-/

section Matrices

variable {α β γ : Type*}

/-- Embed a Boolean entry `b : Bool` as `0 : ℝ` or `1 : ℝ`. -/
def boolToReal (b : Bool) : ℝ := if b then 1 else 0

/-- Embed a binary matrix `A : α → β → Bool` into a real matrix `α → β → ℝ`. -/
def bmatToReal (A : α → β → Bool) (x : α) (y : β) : ℝ :=
  boolToReal (A x y)

/-- Number of non-zero entries $\operatorname{nnz}(A[X, Y]) = |\{(x, y) \in X \times Y : A(x, y) = 1\}|$
(§3.1 of `paper.tex`). -/
def bmatNnz (X : Finset α) (Y : Finset β) (A : α → β → Bool) : ℕ :=
  ∑ x ∈ X, ∑ y ∈ Y, if A x y then 1 else 0

/-- Transpose $A^T(y, x) = A(x, y)$. -/
def matTranspose (A : α → β → ℝ) (y : β) (x : α) : ℝ := A x y

/-- Zero-extension of the submatrix $A[X', Y']$ to $\alpha \times \beta$
(§3.1 of `paper.tex`). -/
def submatZeroExt [DecidableEq α] [DecidableEq β]
    (X' : Finset α) (Y' : Finset β) (A : α → β → ℝ) (x : α) (y : β) : ℝ :=
  if x ∈ X' ∧ y ∈ Y' then A x y else 0

/-- Normalized row degree $\deg_A(x) = \mathbb{E}_{y \in Y}[A(x, y)]$
(§3.1 of `paper.tex`). -/
noncomputable def rowDeg (Y : Finset β) (A : α → β → ℝ) (x : α) : ℝ :=
  expectSet Y (fun y => A x y)

/-- Normalized column degree $\deg_{A^T}(y) = \mathbb{E}_{x \in X}[A(x, y)]$
(§3.1 of `paper.tex`). -/
noncomputable def colDeg (X : Finset α) (A : α → β → ℝ) (y : β) : ℝ :=
  expectSet X (fun x => A x y)

/-- Matrix density $\mathbb{E}[A[X, Y]] = \mathbb{E}_{x \in X} \mathbb{E}_{y \in Y}[A(x, y)]$
(§3.1 of `paper.tex`). -/
noncomputable def matDensity (X : Finset α) (Y : Finset β) (A : α → β → ℝ) : ℝ :=
  expectSet X (fun x => rowDeg Y A x)

lemma matDensity_eq_colDeg (X : Finset α) (Y : Finset β) (A : α → β → ℝ) :
    matDensity X Y A = expectSet Y (fun y => colDeg X A y) :=
  expectSet_comm X Y A

/-- $\varepsilon$-min-degree property: $\deg_A(x) \ge (1 - \varepsilon)\mathbb{E}[A]$ for all $x \in X$
(§3.1 of `paper.tex`). -/
def IsEpsMinDegree (X : Finset α) (Y : Finset β) (A : α → β → ℝ) (ε : ℝ) : Prop :=
  ∀ x ∈ X, rowDeg Y A x ≥ (1 - ε) * matDensity X Y A

/-- Standard matrix product $(AB)(x, z) = \sum_{y \in Y} A(x, y) B(y, z)$
(§3.1 of `paper.tex`). -/
def stdMatMul (Y : Finset β) (A : α → β → ℝ) (B : β → γ → ℝ) (x : α) (z : γ) : ℝ :=
  ∑ y ∈ Y, A x y * B y z

/-- Normalized matrix product $(A \circ B)(x, z) = \mathbb{E}_{y \in Y}[A(x, y) B(y, z)]$
(§3.1 of `paper.tex`). -/
noncomputable def normMatMul (Y : Finset β) (A : α → β → ℝ) (B : β → γ → ℝ) (x : α) (z : γ) : ℝ :=
  expectSet Y (fun y => A x y * B y z)

/-- Boolean matrix product $(A \star B)(x, z) = \bigvee_{y \in [n]} (A(x, y) \wedge B(y, z))$
on `Fin n × Fin n` (§3.1 & Theorem 1.2 `\label{thm:main-bmm}` of `paper.tex`). -/
def boolMatMul (n : ℕ) (A B : Fin n → Fin n → Bool) (x z : Fin n) : Bool :=
  decide (∃ y : Fin n, A x y = true ∧ B y z = true)

/-- Tripartite triangle predicate: $\exists (x, y, z) \in [n]^3, A(x, y) = B(y, z) = C(x, z) = 1$
(Algorithm 6 `\label{alg:triangle}` & Theorem 1.2 `\label{thm:main-bmm}` of `paper.tex`). -/
def hasTriangle (n : ℕ) (A B C : Fin n → Fin n → Bool) : Bool :=
  decide (∃ x y z : Fin n, A x y = true ∧ B y z = true ∧ C x z = true)

lemma hasTriangle_eq_true_iff (n : ℕ) (A B C : Fin n → Fin n → Bool) :
    hasTriangle n A B C = true ↔
      ∃ x y z : Fin n, A x y = true ∧ B y z = true ∧ C x z = true := by
  simp [hasTriangle]

lemma boolMatMul_eq_true_iff (n : ℕ) (A B : Fin n → Fin n → Bool) (x z : Fin n) :
    boolMatMul n A B x z = true ↔ ∃ y : Fin n, A x y = true ∧ B y z = true := by
  simp [boolMatMul]

/-- $(\alpha, \varepsilon, \delta)$-uniformity of a matrix $M$ on $X \times Z$:
at least a $(1 - \delta)$-fraction of pairs $(x, z) \in X \times Z$ satisfy
$(1 - \varepsilon)\alpha \le M(x, z) \le (1 + \varepsilon)\alpha$
(Section 3.1 of `paper.tex`). -/
def IsUniformMatrix (X : Finset α) (Z : Finset γ) (M : α → γ → ℝ)
    (α_val ε δ : ℝ) : Prop :=
  ((X ×ˢ Z).filter (fun xz =>
      (1 - ε) * α_val ≤ M xz.1 xz.2 ∧ M xz.1 xz.2 ≤ (1 + ε) * α_val)).card ≥
    (1 - δ) * ((X.card : ℝ) * (Z.card : ℝ))

end Matrices

/-!
## Grid Norms and $(\varepsilon, k, \ell)$-Regularity (Definition 3.1 `\label{def:grid-norm}`, §3.2 of `paper.tex`)
-/

section GridNorms

variable {α β : Type*}

/-- The $(k, \ell)$-grid norm power $\|M\|_{U(k, \ell)}^{k\ell} =
\mathbb{E}_{x_1, \dots, x_k \in X}[(\mathbb{E}_{y \in Y} \prod_{i=1}^k M(x_i, y))^\ell]$
(Definition 3.1 `\label{def:grid-norm}`, `\eqref{eq:grid-norm-fubini}`, §3.2 of `paper.tex`). -/
noncomputable def gridNormPow (X : Finset α) (Y : Finset β) (M : α → β → ℝ)
    (k ℓ : ℕ) : ℝ :=
  expectSet (Fintype.piFinset (fun _ : Fin k => X))
    (fun xs => (expectSet Y (fun y => ∏ i : Fin k, M (xs i) y)) ^ ℓ)

/-- The column-outer form of the $(k, \ell)$-grid norm power:
$\mathbb{E}_{y_1, \dots, y_\ell \in Y}[(\mathbb{E}_{x \in X} \prod_{j=1}^\ell M(x, y_j))^k]$
(Definition 3.1 `\label{def:grid-norm}`, `\eqref{eq:grid-norm-fubini}`, §3.2 of `paper.tex`). -/
noncomputable def gridNormPowCol (X : Finset α) (Y : Finset β) (M : α → β → ℝ)
    (k ℓ : ℕ) : ℝ :=
  expectSet (Fintype.piFinset (fun _ : Fin ℓ => Y))
    (fun ys => (expectSet X (fun x => ∏ j : Fin ℓ, M x (ys j))) ^ k)

/-- The $(k, \ell)$-grid norm $\|M\|_{U(k, \ell)} = (\|M\|_{U(k, \ell)}^{k\ell})^{1/(k\ell)}$
(Definition 3.1 `\label{def:grid-norm}`, `\eqref{eq:grid-norm-def}`, §3.2 of `paper.tex`). -/
noncomputable def gridNorm (X : Finset α) (Y : Finset β) (M : α → β → ℝ)
    (k ℓ : ℕ) : ℝ :=
  (gridNormPow X Y M k ℓ) ^ ((1 : ℝ) / ((k * ℓ : ℕ) : ℝ))

/-- Specialized $(1, d)$-grid norm power $\|M\|_{U(1, d)}^d =
\mathbb{E}_{x \in X}[(\mathbb{E}_{y \in Y} M(x, y))^d]$ used in `ApproxGridNorm` and `DyadicSift`
(§3.2 & §4.1 of `paper.tex`). -/
noncomputable def gridNorm1Pow (X : Finset α) (Y : Finset β) (M : α → β → ℝ) (d : ℕ) : ℝ :=
  expectSet X (fun x => (rowDeg Y M x) ^ d)

/-- Specialized $(2, d)$-grid norm power $\|M\|_{U(2, d)}^{2d} =
\mathbb{E}_{x, x' \in X}[(\mathbb{E}_{y \in Y} M(x, y) M(x', y))^d]$
(`\eqref{eq:grid-norm-fubini}` & `\eqref{eq:overview-u2d}`, §3.2 & §4.2 of `paper.tex`). -/
noncomputable def gridNorm2Pow (X : Finset α) (Y : Finset β) (M : α → β → ℝ) (d : ℕ) : ℝ :=
  expectSet X (fun x => expectSet X (fun x' => (expectSet Y (fun y => M x y * M x' y)) ^ d))

/-- $(\varepsilon, k, \ell)$-regularity of a matrix $A$ on $X \times Y$:
$\|A\|_{U(k, \ell)} \le (1 + \varepsilon)\mathbb{E}[A]$
(Definition 3.1 `\label{def:grid-norm}`, §3.2 of `paper.tex`). -/
def IsGridRegular (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (ε : ℝ) (k ℓ : ℕ) : Prop :=
  gridNorm X Y A k ℓ ≤ (1 + ε) * matDensity X Y A

/-- Power-form of $(\varepsilon, 2, d)$-regularity avoiding fractional roots:
$\|A\|_{U(2, d)}^{2d} \le ((1 + \varepsilon)\mathbb{E}[A])^{2d}$. -/
def IsGridRegular2Pow (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (ε : ℝ) (d : ℕ) : Prop :=
  gridNorm2Pow X Y A d ≤ ((1 + ε) * matDensity X Y A) ^ (2 * d)

/-- Expansion of the $m$-th power of a finite expectation into an expectation over $m$-tuples
`Fintype.piFinset (fun _ : Fin m => S)`:
$(\mathbb{E}_{x \in S}[g(x)])^m = \mathbb{E}_{xs \in S^m}[\prod_{i=1}^m g(xs_i)]$. -/
lemma expectSet_pow_eq_piFinset (S : Finset α) (g : α → ℝ) (m : ℕ) :
    (expectSet S g) ^ m =
      expectSet (Fintype.piFinset (fun _ : Fin m => S)) (fun xs => ∏ i : Fin m, g (xs i)) := by
  unfold expectSet
  rw [div_pow, Finset.sum_pow', Fintype.card_piFinset_const, Nat.cast_pow]

/-- **Fubini Identity for the $(k, \ell)$-Grid Norm Power (`\eqref{eq:grid-norm-fubini}`, §3.2 of `paper.tex`)**:
$\mathbb{E}_{x_1, \dots, x_k \in X}[(\mathbb{E}_{y \in Y} \prod_{i=1}^k M(x_i, y))^\ell] =
\mathbb{E}_{y_1, \dots, y_\ell \in Y}[(\mathbb{E}_{x \in X} \prod_{j=1}^\ell M(x, y_j))^k]$. -/
theorem gridNormPow_eq_gridNormPowCol (X : Finset α) (Y : Finset β) (M : α → β → ℝ)
    (k ℓ : ℕ) :
    gridNormPow X Y M k ℓ = gridNormPowCol X Y M k ℓ := by
  unfold gridNormPow gridNormPowCol
  simp_rw [expectSet_pow_eq_piFinset]
  rw [expectSet_comm]
  congr 1
  ext ys
  congr 1
  ext xs
  exact Finset.prod_comm

/-- Expectation of a product of independent variables factors:
$\mathbb{E}_{x \in X}[\mathbb{E}_{y \in Y}[f(x) g(y)]] = \mathbb{E}_{x \in X}[f(x)] \cdot \mathbb{E}_{y \in Y}[g(y)]$. -/
lemma expectSet_mul_independent (X : Finset α) (Y : Finset β) (f : α → ℝ) (g : β → ℝ) :
    expectSet X (fun x => expectSet Y (fun y => f x * g y)) =
      expectSet X f * expectSet Y g := by
  simp_rw [expectSet_smul]
  have h : (fun x => f x * expectSet Y g) = (fun x => expectSet Y g * f x) := by
    ext x; ring
  rw [h, expectSet_smul, mul_comm]

/-- Fubini expansion for the $(2, d)$-grid norm power:
$\|M\|_{U(2, d)}^{2d} = \mathbb{E}_{y_1, \dots, y_d \in Y}[(\mathbb{E}_{x \in X} \prod_{j=1}^d M(x, y_j))^2] \ge 0$
(Definition 3.1 `\label{def:grid-norm}`, `\eqref{eq:grid-norm-fubini}`, §3.2 & Lemma A.2 `\label{lem:decoupling-psd}`, Appendix A of `paper.tex`). -/
theorem gridNorm2Pow_eq_col_expect_sq (X : Finset α) (Y : Finset β) (M : α → β → ℝ) (d : ℕ) :
    gridNorm2Pow X Y M d =
      expectSet (Fintype.piFinset (fun _ : Fin d => Y))
        (fun ys => (expectSet X (fun x => ∏ j : Fin d, M x (ys j))) ^ 2) := by
  unfold gridNorm2Pow
  simp_rw [expectSet_pow_eq_piFinset Y _ d, Finset.prod_mul_distrib]
  have h1 :
      (fun x => expectSet X (fun x' => expectSet (Fintype.piFinset (fun _ : Fin d => Y))
        (fun ys => (∏ i : Fin d, M x (ys i)) * (∏ i : Fin d, M x' (ys i))))) =
      (fun x => expectSet (Fintype.piFinset (fun _ : Fin d => Y))
        (fun ys => expectSet X (fun x' => (∏ i : Fin d, M x (ys i)) * (∏ i : Fin d, M x' (ys i))))) := by
    ext x
    exact expectSet_comm X (Fintype.piFinset (fun _ : Fin d => Y)) _
  rw [h1, expectSet_comm X (Fintype.piFinset (fun _ : Fin d => Y))]
  congr 1
  ext ys
  rw [expectSet_mul_independent, sq]

lemma gridNorm2Pow_nonneg (X : Finset α) (Y : Finset β) (M : α → β → ℝ) (d : ℕ) :
    0 ≤ gridNorm2Pow X Y M d := by
  rw [gridNorm2Pow_eq_col_expect_sq]
  exact expectSet_nonneg (fun _ _ => sq_nonneg _)

/-!
## Shared Decomposition Piece Structures and Sampler Specification
-/

/-- $(\varepsilon_{\text{samp}}, \delta_{\text{samp}})$-oblivious sampler family `T_fam` for `Y`
(`\eqref{eq:oblivious-sampler}`, §3.3 & Appendix B `\label{app:sampler}` of `paper.tex`). -/
def IsObliviousSampler (Y : Finset β) (T_fam : List (Finset β)) (ε_samp δ_samp : ℝ) : Prop :=
  T_fam ≠ [] ∧
  (∀ T ∈ T_fam, T ⊆ Y ∧ (Y.Nonempty → T.Nonempty)) ∧
  ∀ g : β → ℝ, (∀ y ∈ Y, 0 ≤ g y ∧ g y ≤ 1) →
    (((T_fam.filter (fun T => |expectSet T g - expectSet Y g| > ε_samp)).length : ℝ) ≤
      δ_samp * (T_fam.length : ℝ))

/-- Output tag for a 2D piece in `CappedADecomposition` (Algorithm 4 (`FindRect` / `Decompose2D`) `\label{alg:2d}`, §4.3 of `paper.tex`). -/
inductive RectTag : Type
  | regular  : RectTag
  | aBoosted : RectTag
  | residual : RectTag
  deriving DecidableEq, Repr, Inhabited

/-- A single 2D submatrix piece $(X_\ell, Y_\ell, A_\ell, \text{tag}_\ell, S_\ell)$ in
`ADecomposition` or `CappedADecomposition` (Algorithms 4–5 `\label{alg:2d}`–`\label{alg:3d}`, Theorem 4.4 `\label{thm:2d-decomp}` of `paper.tex`). -/
structure RectPiece (α β : Type*) where
  X_sub : Finset α
  Y_sub : Finset β
  A_sub : α → β → ℝ
  tag   : RectTag
  scale : ℕ

/-- Output mode for `CappedGoodCube` (Algorithm 5 (`FindCube`) `\label{alg:3d}`, §5.2 of `paper.tex`). -/
inductive CubeMode : Type
  | normal : CubeMode
  | bBoost : CubeMode
  | aBoost : CubeMode
  deriving DecidableEq, Repr, Inhabited

/-- A single 3D subcube piece $(X_k, Y_k, Z_k, A_k, B_k)$ in `CappedABDecomposition`
(Algorithm 5 (`Decompose3D`) `\label{alg:3d}`, Lemmas 5.3–5.5 & 5.9 (`\label{lem:cube-step}`, `\label{lem:children-invariants}`, `\label{lem:potential}`, `\label{lem:recurrence}`) & Theorem 1.1 `\label{thm:main-decomp}` of `paper.tex`). -/
structure CubePiece (α β γ : Type*) where
  X_k : Finset α
  Y_k : Finset β
  Z_k : Finset γ
  A_k : α → β → ℝ
  B_k : β → γ → ℝ
  isRegularPiece : Bool

/-- The $(p, q)$-density-weighted cube potential
$C_{p, q}(\mathcal{S}) := \sum_{k} (\mathbb{E}[A_k])^p (\mathbb{E}[B_k])^q |X_k| |Y_k| |Z_k|$
(`\eqref{eq:main-potential}`, §1.2 & §5.1 of `paper.tex`). -/
noncomputable def cubePotential {γ : Type*} (p q : ℝ) (S : List (CubePiece α β γ)) : ℝ :=
  (S.map (fun P =>
    (matDensity P.X_k P.Y_k P.A_k) ^ p *
    (matDensity P.Y_k P.Z_k P.B_k) ^ q *
    (P.X_k.card : ℝ) * (P.Y_k.card : ℝ) * (P.Z_k.card : ℝ))).sum

/-- Normalized $L_d(s)$ seminorm $(\mathbb{E}_{i \in s}[|f(i)|^d])^{1/d}$ over a finite set `s`
(§4.1 and Appendix A of `paper.tex`). -/
noncomputable def lpNormSet {ι : Type*} (s : Finset ι) (d : ℕ) (f : ι → ℝ) : ℝ :=
  (expectSet s (fun i => |f i| ^ d)) ^ (1 / (d : ℝ))

lemma lpNormSet_eq_div {ι : Type*} (s : Finset ι) (d : ℕ) (f : ι → ℝ) :
    lpNormSet s d f =
      ((∑ i ∈ s, |f i| ^ (d : ℝ)) ^ (1 / (d : ℝ))) / ((s.card : ℝ) ^ (1 / (d : ℝ))) := by
  unfold lpNormSet expectSet
  have hsum : (∑ i ∈ s, |f i| ^ d) = ∑ i ∈ s, |f i| ^ (d : ℝ) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Real.rpow_natCast]
  rw [hsum]
  exact Real.div_rpow (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _))
    (Nat.cast_nonneg _) _

/-- **Minkowski's triangle inequality** in $L_d(s)$ for normalized expectations over `s : Finset ι`
(§4.1 and Appendix A of `paper.tex`). -/
theorem lpNormSet_add_le {ι : Type*} (s : Finset ι) {d : ℕ} (hd : 1 ≤ d) (f g : ι → ℝ) :
    lpNormSet s d (fun i => f i + g i) ≤ lpNormSet s d f + lpNormSet s d g := by
  rw [lpNormSet_eq_div, lpNormSet_eq_div, lpNormSet_eq_div, ← add_div]
  refine div_le_div_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hp : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  exact Real.Lp_add_le s f g hp

end GridNorms

end BMMGrid
