import BMMGrid.Defs

/-!
# Appendix A & Proposition 3.1: Regular Matrices Have Uniform Products (`BMMGrid/KLMUniformity.lean`)

This module formalizes Section 3.2 (Proposition 3.1) and Appendix A
(`Claim A.1`, `Lemma A.2`, and the proof of `Proposition 3.1`, Appendix A) of
`paper.tex`.
-/

namespace BMMGrid

open scoped BigOperators

/-!
## Finite $L_p$ Norms, Minkowski's Inequality, and Power-Mean Monotonicity
(Appendix A of `paper.tex`)
-/

section LpNorms

variable {α β γ : Type*}

lemma expectSet_abs_pow_nonneg (Ω : Finset α) (f : α → ℝ) (p : ℕ) :
    0 ≤ expectSet Ω (fun ω => |f ω| ^ p) :=
  expectSet_nonneg (fun _ _ => pow_nonneg (abs_nonneg _) _)

lemma lpNormSet_nonneg (Ω : Finset α) (f : α → ℝ) (p : ℕ) : 0 ≤ lpNormSet Ω p f :=
  Real.rpow_nonneg (expectSet_abs_pow_nonneg Ω f p) _

lemma lpNormSet_pow_eq (Ω : Finset α) (f : α → ℝ) {p : ℕ} (hp : 1 ≤ p) :
    (lpNormSet Ω p f) ^ p = expectSet Ω (fun ω => |f ω| ^ p) := by
  unfold lpNormSet
  have hp_ne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (expectSet_abs_pow_nonneg Ω f p),
    one_div_mul_cancel hp_ne, Real.rpow_one]

lemma lpNormSet_le_iff {Ω : Finset α} {f : α → ℝ} {p : ℕ} (hp : 1 ≤ p) {C : ℝ} (hC : 0 ≤ C) :
    lpNormSet Ω p f ≤ C ↔ expectSet Ω (fun ω => |f ω| ^ p) ≤ C ^ p := by
  rw [← lpNormSet_pow_eq Ω f hp]
  exact (pow_le_pow_iff_left₀ (lpNormSet_nonneg Ω f p) hC (by omega)).symm

lemma lt_lpNormSet_iff {Ω : Finset α} {f : α → ℝ} {p : ℕ} (hp : 1 ≤ p) {C : ℝ} (hC : 0 ≤ C) :
    C < lpNormSet Ω p f ↔ C ^ p < expectSet Ω (fun ω => |f ω| ^ p) := by
  rw [← not_le, lpNormSet_le_iff hp hC, not_le]

/-- Pointwise domination implies $L_p$ norm domination (Appendix A of `paper.tex`). -/
lemma lpNormSet_mono {Ω : Finset α} {f g : α → ℝ} (p : ℕ) (h : ∀ ω ∈ Ω, |f ω| ≤ |g ω|) :
    lpNormSet Ω p f ≤ lpNormSet Ω p g := by
  unfold lpNormSet
  refine Real.rpow_le_rpow (expectSet_abs_pow_nonneg Ω f p) ?_ (by positivity)
  exact expectSet_mono (fun ω hω => pow_le_pow_left₀ (abs_nonneg _) (h ω hω) p)

/-- $L_p \le L_\infty$ bound on a non-empty finite set (Appendix A of `paper.tex`). -/
lemma lpNormSet_le_of_bound {Ω : Finset α} (hΩ : Ω.Nonempty) {f : α → ℝ} {M : ℝ} (hM : 0 ≤ M)
    {p : ℕ} (hp : 1 ≤ p) (hf : ∀ ω ∈ Ω, |f ω| ≤ M) :
    lpNormSet Ω p f ≤ M := by
  rw [lpNormSet_le_iff hp hM]
  exact expectSet_le_of_le hΩ (fun ω hω => pow_le_pow_left₀ (abs_nonneg _) (hf ω hω) p)

/-- Lyapunov's inequality / power-mean monotonicity for finite expectations:
$(\mathbb{E}_{\omega \in \Omega}[|f(\omega)|^k])^{m/k} \le \mathbb{E}_{\omega \in \Omega}[|f(\omega)|^m]$
for $1 \le k \le m$ (Claim A.1, Appendix A & Proposition 3.1 of `paper.tex`). -/
lemma expectSet_abs_pow_mono {Ω : Finset α} (hΩ : Ω.Nonempty) (f : α → ℝ)
    {k m : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    (expectSet Ω (fun ω => |f ω| ^ k)) ^ ((m : ℝ) / (k : ℝ)) ≤
      expectSet Ω (fun ω => |f ω| ^ m) := by
  have hcard_pos : (0 : ℝ) < Ω.card := Nat.cast_pos.mpr hΩ.card_pos
  have hcard_ne : (Ω.card : ℝ) ≠ 0 := hcard_pos.ne'
  let w : α → ℝ := fun _ => (Ω.card : ℝ)⁻¹
  let z : α → ℝ := fun ω => |f ω| ^ k
  have hw : ∀ ω ∈ Ω, 0 ≤ w ω := fun _ _ => inv_nonneg.mpr hcard_pos.le
  have hw' : ∑ ω ∈ Ω, w ω = 1 := by
    simp [w, Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hcard_ne]
  have hz : ∀ ω ∈ Ω, 0 ≤ z ω := fun _ _ => pow_nonneg (abs_nonneg _) _
  have hq : (1 : ℝ) ≤ (m : ℝ) / (k : ℝ) := by
    rw [ one_le_div (by exact_mod_cast hk : (0 : ℝ) < (k : ℝ))]
    exact_mod_cast hkm
  have h_pm := Real.rpow_arith_mean_le_arith_mean_rpow Ω w z hw hw' hz hq
  have h_lhs : ∑ ω ∈ Ω, w ω * z ω = expectSet Ω (fun ω => |f ω| ^ k) := by
    unfold expectSet
    simp [w, z, div_eq_inv_mul, Finset.mul_sum]
  have h_rhs : ∑ ω ∈ Ω, w ω * (z ω) ^ ((m : ℝ) / (k : ℝ)) =
      expectSet Ω (fun ω => |f ω| ^ m) := by
    unfold expectSet
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    dsimp [w, z]
    have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h_pow : (|f ω| ^ k) ^ ((m : ℝ) / (k : ℝ)) = |f ω| ^ m := by
      rw [← Real.rpow_natCast |f ω| k, ← Real.rpow_mul (abs_nonneg _),
        mul_div_cancel₀ _ hk_ne, Real.rpow_natCast]
    rw [h_pow, inv_mul_eq_div]
  rw [h_lhs, h_rhs] at h_pm
  exact h_pm

/-- Monotonicity of $L_p$ norms on a finite probability space: $\|f\|_k \le \|f\|_m$ for $1 \le k \le m$
(Claim A.1, Appendix A & Proposition 3.1 of `paper.tex`). -/
lemma lpNormSet_mono_exponent {Ω : Finset α} (hΩ : Ω.Nonempty) (f : α → ℝ)
    {k m : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    lpNormSet Ω k f ≤ lpNormSet Ω m f := by
  have hm : 1 ≤ m := le_trans hk hkm
  rw [lpNormSet_le_iff hk (lpNormSet_nonneg Ω f m)]
  have h_pm := expectSet_abs_pow_mono hΩ f hk hkm
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h_rpow := Real.rpow_le_rpow
    (Real.rpow_nonneg (expectSet_abs_pow_nonneg Ω f k) _) h_pm
    (by positivity : (0 : ℝ) ≤ (k : ℝ) / (m : ℝ))
  have h_cancel : ((m : ℝ) / (k : ℝ)) * ((k : ℝ) / (m : ℝ)) = 1 := by
    have hm_ne : (m : ℝ) ≠ 0 := hm_pos.ne'
    have hk_ne : (k : ℝ) ≠ 0 := hk_pos.ne'
    field_simp
  rw [← Real.rpow_mul (expectSet_abs_pow_nonneg Ω f k), h_cancel, Real.rpow_one] at h_rpow
  unfold lpNormSet
  rw [← Real.rpow_natCast, ← Real.rpow_mul (expectSet_abs_pow_nonneg Ω f m), one_div_mul_eq_div]
  exact h_rpow

end LpNorms

/-!
## Claim A.1: Non-Negative Odd Moments (Appendix A of `paper.tex`)
-/

section ClaimA1

variable {α : Type*}

/-- **Helper 1 (`posPart_one_add_pow_ge_one_add_pow`, Claim A.1, Appendix A of `paper.tex`)**:
For any real $w \in \mathbb{R}$ and odd integer $p \in \mathbb{N}$,
$(\operatorname{posPart}(1 + w))^p \ge (1 + w)^p$. -/
lemma posPart_one_add_pow_ge_one_add_pow (w : ℝ) {p : ℕ} (hp : Odd p) :
    (1 + w) ^ p ≤ (posPart (1 + w)) ^ p :=
  hp.strictMono_pow.monotone (le_max_left (1 + w) 0)

/-- Extended version of Helper 1 covering both cases of Claim A.1 (Appendix A of `paper.tex`):
if $p$ is odd or $1 + w \ge 0$, then $(\operatorname{posPart}(1 + w))^p \ge (1 + w)^p$. -/
lemma posPart_one_add_pow_ge_of_odd_or_nonneg (w : ℝ) {p : ℕ} (hp : Odd p ∨ 0 ≤ 1 + w) :
    (1 + w) ^ p ≤ (posPart (1 + w)) ^ p := by
  rcases hp with hp_odd | hw_nonneg
  · exact posPart_one_add_pow_ge_one_add_pow w hp_odd
  · unfold posPart
    rw [max_eq_left hw_nonneg]

/-- The binomial moment term $t_m := \binom{p}{m} (2\eta)^m$
(Claim A.1, Appendix A of `paper.tex`). -/
noncomputable def binomMomentTerm (p : ℕ) (η : ℝ) (m : ℕ) : ℝ :=
  (p.choose m : ℝ) * (2 * η) ^ m

lemma binomMomentTerm_nonneg (p : ℕ) {η : ℝ} (hη : 0 ≤ η) (m : ℕ) :
    0 ≤ binomMomentTerm p η m := by
  unfold binomMomentTerm
  positivity

/-- Consecutive term ratio bound in Claim A.1 (Appendix A of `paper.tex`):
for $\eta \in (0, 1/4]$, $k \ge 2$, $p \ge k/\eta$, and $j < k$,
$t_{j+1} > \frac{3}{2} t_j$ where $t_m = \binom{p}{m}(2\eta)^m$. -/
lemma binom_term_ratio_gt_three_halves_step {η : ℝ} {k p j : ℕ}
    (hη_pos : 0 < η) (hη_le : η ≤ 1 / 4) (_hk : 2 ≤ k)
    (hp : (k : ℝ) / η ≤ (p : ℝ)) (hj : j < k) :
    (3 / 2 : ℝ) * binomMomentTerm p η j < binomMomentTerm p η (j + 1) := by
  have hkp : (k : ℝ) ≤ (p : ℝ) * η := (div_le_iff₀ hη_pos).mp hp
  have hj1_le_k : ((j : ℝ) + 1) ≤ (k : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hj)
  have hj1_le_pη : (j : ℝ) + 1 ≤ (p : ℝ) * η := le_trans hj1_le_k hkp
  have hjp : j < p := by
    have : (j : ℝ) + 1 < (p : ℝ) := by nlinarith
    exact_mod_cast (by linarith : (j : ℝ) < (p : ℝ))
  have hj_le_p : j ≤ p := le_of_lt hjp
  have hchoose_nat := Nat.choose_succ_right_eq p j
  have hchoose_real :
      (p.choose (j + 1) : ℝ) * ((j : ℝ) + 1) = (p.choose j : ℝ) * ((p : ℝ) - (j : ℝ)) := by
    have h1 : ((p.choose (j + 1) * (j + 1) : ℕ) : ℝ) = ((p.choose j * (p - j) : ℕ) : ℝ) :=
      congrArg Nat.cast hchoose_nat
    push_cast [Nat.cast_sub hj_le_p] at h1
    exact h1
  have h_ineq : (3 / 2 : ℝ) * ((j : ℝ) + 1) < ((p : ℝ) - (j : ℝ)) * (2 * η) := by
    nlinarith
  have h_tj_pos : 0 < binomMomentTerm p η j := by
    unfold binomMomentTerm
    have h_ch : 0 < p.choose j := Nat.choose_pos hj_le_p
    positivity
  have h_mul :
      (3 / 2 : ℝ) * binomMomentTerm p η j * ((j : ℝ) + 1) <
        binomMomentTerm p η (j + 1) * ((j : ℝ) + 1) := by
    calc
      (3 / 2 : ℝ) * binomMomentTerm p η j * ((j : ℝ) + 1)
        = binomMomentTerm p η j * ((3 / 2 : ℝ) * ((j : ℝ) + 1)) := by ring
      _ < binomMomentTerm p η j * (((p : ℝ) - (j : ℝ)) * (2 * η)) :=
        mul_lt_mul_of_pos_left h_ineq h_tj_pos
      _ = (p.choose j : ℝ) * ((p : ℝ) - (j : ℝ)) * (2 * η) ^ j * (2 * η) := by
        unfold binomMomentTerm; ring
      _ = (p.choose (j + 1) : ℝ) * ((j : ℝ) + 1) * (2 * η) ^ j * (2 * η) := by
        rw [← hchoose_real]
      _ = binomMomentTerm p η (j + 1) * ((j : ℝ) + 1) := by
        unfold binomMomentTerm; rw [pow_succ]; ring
  exact lt_of_mul_lt_mul_right h_mul (by positivity : (0 : ℝ) ≤ (j : ℝ) + 1)

/-- Auxiliary geometric tail bound for even-indexed terms satisfying $f(2r) \le \frac{4}{9} f(2r+2)$:
$\sum_{\text{even } m \le 2M} f(m) \le \frac{9}{5} f(2M)$ (`paper.tex` Appendix A). -/
lemma even_sum_le_nine_fifths_last (f : ℕ → ℝ) (M : ℕ)
    (hf0 : 0 ≤ f 0)
    (hstep : ∀ r < M, f (2 * r) ≤ (4 / 9 : ℝ) * f (2 * r + 2)) :
    ∑ m ∈ (Finset.range (2 * M + 1)).filter Even, f m ≤ (9 / 5 : ℝ) * f (2 * M) := by
  induction M with
  | zero =>
    have hfilter : (Finset.range 1).filter Even = {0} := by decide
    rw [Nat.mul_zero, hfilter, Finset.sum_singleton]
    linarith
  | succ M ih =>
    have hstep_M : ∀ r < M, f (2 * r) ≤ (4 / 9 : ℝ) * f (2 * r + 2) :=
      fun r hr => hstep r (Nat.lt_succ_of_lt hr)
    have h_ih := ih hstep_M
    have h_last := hstep M (Nat.lt_succ_self M)
    have h1 : 2 * (M + 1) + 1 = (2 * M + 1) + 1 + 1 := by omega
    rw [h1, Finset.range_add_one, Finset.filter_insert]
    have h_even2 : Even (2 * M + 1 + 1) := ⟨M + 1, by omega⟩
    rw [if_pos h_even2, Finset.sum_insert (by simp)]
    rw [Finset.range_add_one, Finset.filter_insert]
    have h_not_even1 : ¬ Even (2 * M + 1) := by
      rintro ⟨c, hc⟩
      omega
    rw [if_neg h_not_even1]
    have h_idx1 : 2 * M + 1 + 1 = 2 * M + 2 := by omega
    have h_idx2 : 2 * (M + 1) = 2 * M + 2 := by omega
    rw [h_idx1, h_idx2]
    linarith

/-- **Helper 2 (`binom_term_ratio_gt_three_halves`, Claim A.1, Appendix A of `paper.tex`)**:
For $\eta \in (0, 1/4]$, even $k \ge 2$, and $p \ge k/\eta$, we have $t_{j+1} > \frac{3}{2} t_j$
for all $1 \le j \le k - 1$, and hence $t_k \ge \frac{5}{9} \sum_{\text{even } m \le k} t_m$. -/
theorem binom_term_ratio_gt_three_halves {η : ℝ} {k p : ℕ}
    (hη_pos : 0 < η) (hη_le : η ≤ 1 / 4) (hk : 2 ≤ k) (hk_even : Even k)
    (hp : (k : ℝ) / η ≤ (p : ℝ)) :
    (∀ j, 1 ≤ j → j ≤ k - 1 → (3 / 2 : ℝ) * binomMomentTerm p η j < binomMomentTerm p η (j + 1)) ∧
      (5 / 9 : ℝ) * ∑ m ∈ (Finset.range (k + 1)).filter Even, binomMomentTerm p η m ≤
        binomMomentTerm p η k := by
  refine ⟨fun j _ hj => binom_term_ratio_gt_three_halves_step hη_pos hη_le hk hp (by omega), ?_⟩
  rcases hk_even with ⟨M, hM⟩
  have h2M : k = 2 * M := by omega
  subst h2M
  have h_le : ∑ m ∈ (Finset.range (2 * M + 1)).filter Even, binomMomentTerm p η m ≤
      (9 / 5 : ℝ) * binomMomentTerm p η (2 * M) := by
    refine even_sum_le_nine_fifths_last (binomMomentTerm p η) M
      (binomMomentTerm_nonneg p hη_pos.le 0) (fun r hr => ?_)
    have h_step1 := binom_term_ratio_gt_three_halves_step hη_pos hη_le hk hp (j := 2 * r) (by omega)
    have h_step2 := binom_term_ratio_gt_three_halves_step hη_pos hη_le hk hp (j := 2 * r + 1) (by omega)
    linarith
  linarith

/-- **Helper 3 (`even_binom_sum_eq`, Claim A.1, Appendix A of `paper.tex`)**:
$\sum_{\text{even } m \le p} \binom{p}{m}(2\eta)^m = \frac{1}{2}((1 + 2\eta)^p + (1 - 2\eta)^p)
\ge \frac{1}{2}(1 + 2\eta)^p$ for $\eta \in (0, 1/4]$. -/
theorem even_binom_sum_eq (p : ℕ) (η : ℝ) (hη_le : η ≤ 1 / 4) :
    ∑ m ∈ (Finset.range (p + 1)).filter Even, binomMomentTerm p η m =
      ((1 + 2 * η) ^ p + (1 - 2 * η) ^ p) / 2 ∧
    (1 + 2 * η) ^ p / 2 ≤
      ∑ m ∈ (Finset.range (p + 1)).filter Even, binomMomentTerm p η m := by
  have h_pos : (1 + 2 * η) ^ p =
      ∑ m ∈ Finset.range (p + 1), (p.choose m : ℝ) * (2 * η) ^ m := by
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    ring
  have h_neg : (1 - 2 * η) ^ p =
      ∑ m ∈ Finset.range (p + 1), (p.choose m : ℝ) * (- (2 * η)) ^ m := by
    have : 1 - 2 * η = (- (2 * η)) + 1 := by ring
    rw [this, add_pow]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    ring
  have h_sum : (1 + 2 * η) ^ p + (1 - 2 * η) ^ p =
      2 * ∑ m ∈ (Finset.range (p + 1)).filter Even, binomMomentTerm p η m := by
    rw [h_pos, h_neg, ← Finset.sum_add_distrib,
      ← Finset.sum_filter_add_sum_filter_not (Finset.range (p + 1)) Even]
    have h_even_part :
        ∑ m ∈ (Finset.range (p + 1)).filter Even,
          ((p.choose m : ℝ) * (2 * η) ^ m + (p.choose m : ℝ) * (-(2 * η)) ^ m) =
        2 * ∑ m ∈ (Finset.range (p + 1)).filter Even, binomMomentTerm p η m := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      have hm_even : Even m := (Finset.mem_filter.mp hm).2
      rw [hm_even.neg_pow]
      unfold binomMomentTerm
      ring
    have h_odd_part :
        ∑ m ∈ (Finset.range (p + 1)).filter (fun m => ¬ Even m),
          ((p.choose m : ℝ) * (2 * η) ^ m + (p.choose m : ℝ) * (-(2 * η)) ^ m) = 0 := by
      refine Finset.sum_eq_zero (fun m hm => ?_)
      have hm_odd : Odd m := Nat.not_even_iff_odd.mp (Finset.mem_filter.mp hm).2
      rw [hm_odd.neg_pow]
      ring
    rw [h_even_part, h_odd_part, add_zero]
  have h_eq : ∑ m ∈ (Finset.range (p + 1)).filter Even, binomMomentTerm p η m =
      ((1 + 2 * η) ^ p + (1 - 2 * η) ^ p) / 2 := by linarith
  refine ⟨h_eq, ?_⟩
  rw [h_eq]
  have h_nonneg : 0 ≤ (1 - 2 * η) ^ p := pow_nonneg (by linarith) p
  linarith

/-- Quadratic Bernoulli / binomial lower bound $(1 + x)^p \ge 1 + p x + \binom{p}{2} x^2$
for $x \ge 0$ and $p \ge 2$ (`paper.tex` Claim A.1, Appendix A). -/
lemma one_add_pow_ge_quadratic {x : ℝ} (hx : 0 ≤ x) {p : ℕ} (hp : 2 ≤ p) :
    1 + (p : ℝ) * x + (p : ℝ) * ((p : ℝ) - 1) / 2 * x ^ 2 ≤ (1 + x) ^ p := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hp
  induction m with
  | zero =>
    simp
    linarith
  | succ m ih =>
    have hp2 : 2 ≤ 2 + m := Nat.le_add_right 2 m
    have h_ih := ih hp2
    have h_mul := mul_le_mul_of_nonneg_right h_ih (by linarith : 0 ≤ 1 + x)
    have h_step :
        1 + ((2 + (m + 1) : ℕ) : ℝ) * x +
          ((2 + (m + 1) : ℕ) : ℝ) * (((2 + (m + 1) : ℕ) : ℝ) - 1) / 2 * x ^ 2 ≤
        (1 + ((2 + m : ℕ) : ℝ) * x +
          ((2 + m : ℕ) : ℝ) * (((2 + m : ℕ) : ℝ) - 1) / 2 * x ^ 2) * (1 + x) := by
      push_cast
      have h_cub : 0 ≤ (2 + (m : ℝ)) * (1 + (m : ℝ)) / 2 * x ^ 3 := by positivity
      linarith
    have h_pow : (1 + x) ^ (2 + (m + 1)) = (1 + x) ^ (2 + m) * (1 + x) := by
      rw [← add_assoc, pow_succ]
    linarith

/-- **Helper 4 (`one_add_two_eta_div_one_add_eta_pow_gt`, Claim A.1, Appendix A of `paper.tex`)**:
For $\eta \in (0, 1/4]$, $k \ge 2$, and $p \ge k/\eta$,
$$\left(\frac{1 + 2\eta}{1 + \eta}\right)^p \ge \left(1 + \frac{4}{5}\eta\right)^p
\ge 1 + p\left(\frac{4}{5}\eta\right) + \frac{p(p-1)}{2}\left(\frac{4}{5}\eta\right)^2
\ge \frac{93}{25} > \frac{18}{5},$$
and hence $\frac{5}{18}(1 + 2\eta)^p > (1 + \eta)^p$. -/
theorem one_add_two_eta_div_one_add_eta_pow_gt {η : ℝ} {k p : ℕ}
    (hη_pos : 0 < η) (hη_le : η ≤ 1 / 4) (hk : 2 ≤ k)
    (hp : (k : ℝ) / η ≤ (p : ℝ)) :
    (18 / 5 : ℝ) < ((1 + 2 * η) / (1 + η)) ^ p ∧
      (1 + η) ^ p < (5 / 18 : ℝ) * (1 + 2 * η) ^ p := by
  have hkp : (2 : ℝ) ≤ (p : ℝ) * η := by
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have := (div_le_iff₀ hη_pos).mp hp
    linarith
  have hp8_real : (8 : ℝ) ≤ (p : ℝ) := by nlinarith
  have hp2 : 2 ≤ p := by
    have : 8 ≤ p := by exact_mod_cast hp8_real
    omega
  have h_base : 1 + (4 / 5 : ℝ) * η ≤ (1 + 2 * η) / (1 + η) := by
    rw [le_div_iff₀ (by linarith : 0 < 1 + η)]
    nlinarith
  have h_pow_mono :
      (1 + (4 / 5 : ℝ) * η) ^ p ≤ ((1 + 2 * η) / (1 + η)) ^ p :=
    pow_le_pow_left₀ (by positivity) h_base p
  have h_quad := one_add_pow_ge_quadratic (x := (4 / 5 : ℝ) * η) (by positivity) hp2
  have h_p_sub : (7 / 8 : ℝ) * (p : ℝ) ≤ (p : ℝ) - 1 := by linarith
  have h_pη2 : (7 / 2 : ℝ) ≤ (p : ℝ) * ((p : ℝ) - 1) * η ^ 2 := by
    have h1 : (7 / 8 : ℝ) * (p : ℝ) * ((p : ℝ) * η ^ 2) ≤ ((p : ℝ) - 1) * ((p : ℝ) * η ^ 2) :=
      mul_le_mul_of_nonneg_right h_p_sub (by positivity)
    have h2 : (4 : ℝ) ≤ ((p : ℝ) * η) ^ 2 := by nlinarith
    nlinarith
  have h_num :
      (93 / 25 : ℝ) ≤
        1 + (p : ℝ) * ((4 / 5 : ℝ) * η) +
          (p : ℝ) * ((p : ℝ) - 1) / 2 * ((4 / 5 : ℝ) * η) ^ 2 := by
    nlinarith
  have h_gt : (18 / 5 : ℝ) < ((1 + 2 * η) / (1 + η)) ^ p := by linarith
  refine ⟨h_gt, ?_⟩
  rw [div_pow] at h_gt
  have h_denom_pos : 0 < (1 + η) ^ p := pow_pos (by linarith) p
  have h_mul := (lt_div_iff₀ h_denom_pos).mp h_gt
  linarith

/-- Finite expectation of a finite sum:
$\mathbb{E}_{u \in \Omega}[\sum_{i \in I} g(i, u)] = \sum_{i \in I} \mathbb{E}_{u \in \Omega}[g(i, u)]$. -/
lemma expectSet_finset_sum {ι : Type*} (Ω : Finset α) (I : Finset ι) (g : ι → α → ℝ) :
    expectSet Ω (fun u => ∑ i ∈ I, g i u) = ∑ i ∈ I, expectSet Ω (fun u => g i u) := by
  unfold expectSet
  rw [Finset.sum_comm, Finset.sum_div]

/-- **Claim A.1 (`clm_moments_lower_bound`, Appendix A of `paper.tex`)** (unified form covering both
odd $p$ and non-negative $1 + W$):
Let $\eta \in (0, 1/4]$, even $k \ge 2$, and $W : \alpha \to \mathbb{R}$ on a finite non-empty set
$\Omega$ satisfy $\mathbb{E}_{u \in \Omega}[W(u)^k] \ge (2\eta)^k$ and
$\mathbb{E}_{u \in \Omega}[W(u)^j] \ge 0$ for all $j \ge 1$. Then for every integer $p \ge k/\eta$
such that $p$ is odd or $1 + W(u) \ge 0$ on $\Omega$,
$$\mathbb{E}_{u \in \Omega}\Big[\big(\operatorname{posPart}(1 + W(u))\big)^p\Big] > (1 + \eta)^p
\quad\text{and}\quad \|\operatorname{posPart}(1 + W)\|_p > 1 + \eta.$$ -/
theorem clm_moments_lower_bound {Ω : Finset α} (hΩ : Ω.Nonempty) (W : α → ℝ)
    {η : ℝ} {k p : ℕ} (hη_pos : 0 < η) (hη_le : η ≤ 1 / 4)
    (hk : 2 ≤ k) (hk_even : Even k)
    (hWk : (2 * η) ^ k ≤ expectSet Ω (fun u => W u ^ k))
    (hWj : ∀ j : ℕ, 1 ≤ j → 0 ≤ expectSet Ω (fun u => W u ^ j))
    (hp : (k : ℝ) / η ≤ (p : ℝ))
    (hp_cond : Odd p ∨ ∀ u ∈ Ω, 0 ≤ 1 + W u) :
    (1 + η) ^ p < expectSet Ω (fun u => (posPart (1 + W u)) ^ p) ∧
      1 + η < lpNormSet Ω p (fun u => posPart (1 + W u)) := by
  have hkp : (k : ℝ) ≤ (p : ℝ) * η := (div_le_iff₀ hη_pos).mp hp
  have hk_le_p : k ≤ p := by
    have : (k : ℝ) ≤ (p : ℝ) := by nlinarith
    exact_mod_cast this
  have hp1 : 1 ≤ p := by omega
  -- Step 1 (Appendix A): Pointwise bound ((1 + W)_+)^p ≥ (1 + W)^p
  have h_step1 :
      expectSet Ω (fun u => (1 + W u) ^ p) ≤
        expectSet Ω (fun u => (posPart (1 + W u)) ^ p) := by
    refine expectSet_mono (fun u hu => ?_)
    rcases hp_cond with hp_odd | h_nonneg
    · exact posPart_one_add_pow_ge_one_add_pow (W u) hp_odd
    · exact posPart_one_add_pow_ge_of_odd_or_nonneg (W u) (Or.inr (h_nonneg u hu))
  -- Step 2 (Appendix A): Binomial expansion + Lyapunov lower bound on even moments m ≥ k
  have h_binom_exp :
      expectSet Ω (fun u => (1 + W u) ^ p) =
        ∑ j ∈ Finset.range (p + 1), (p.choose j : ℝ) * expectSet Ω (fun u => W u ^ j) := by
    have h_pt : (fun u => (1 + W u) ^ p) =
        (fun u => ∑ j ∈ Finset.range (p + 1), (p.choose j : ℝ) * W u ^ j) := by
      ext u
      rw [add_comm, add_pow]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [h_pt, expectSet_finset_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    exact expectSet_smul Ω (p.choose j : ℝ) (fun u => W u ^ j)
  -- For every even m ≥ k, E[W^m] ≥ (2η)^m by Lyapunov's inequality
  have h_lyap : ∀ m : ℕ, k ≤ m → Even m →
      (2 * η) ^ m ≤ expectSet Ω (fun u => W u ^ m) := by
    intro m hkm hm_even
    have h_abs_k : expectSet Ω (fun u => W u ^ k) = expectSet Ω (fun u => |W u| ^ k) := by
      congr 1; ext u; exact (hk_even.pow_abs (W u)).symm
    have h_abs_m : expectSet Ω (fun u => W u ^ m) = expectSet Ω (fun u => |W u| ^ m) := by
      congr 1; ext u; exact (hm_even.pow_abs (W u)).symm
    rw [h_abs_m]
    have h_mono := expectSet_abs_pow_mono hΩ W (by omega : 1 ≤ k) hkm
    rw [← h_abs_k] at h_mono
    have h_pow_le : ((2 * η) ^ k) ^ ((m : ℝ) / (k : ℝ)) ≤
        (expectSet Ω (fun u => W u ^ k)) ^ ((m : ℝ) / (k : ℝ)) :=
      Real.rpow_le_rpow (by positivity) hWk (by positivity)
    have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [← Real.rpow_natCast (2 * η) k, ← Real.rpow_mul (by positivity),
      mul_div_cancel₀ _ hk_ne, Real.rpow_natCast] at h_pow_le
    exact le_trans h_pow_le h_mono
  -- Restrict sum to j = 0 and even m ≥ k
  let S_even := (Finset.range (p + 1)).filter Even
  let S_high := S_even.filter (fun m => k < m)
  let S_low := (Finset.range (k + 1)).filter Even
  have h_split_even :
      ∑ m ∈ S_even, binomMomentTerm p η m =
        (∑ m ∈ S_low, binomMomentTerm p η m) + (∑ m ∈ S_high, binomMomentTerm p η m) := by
    rw [← Finset.sum_filter_add_sum_filter_not S_even (fun m => m ≤ k)]
    congr 1
    · refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext m
      simp only [S_even, S_low, Finset.mem_filter, Finset.mem_range]
      by_cases he : Even m
      · simp [he]; omega
      · simp [he]
    · refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext m
      simp only [S_even, S_high, Finset.mem_filter, not_le]
  have h_sum_ge :
      binomMomentTerm p η k + ∑ m ∈ S_high, binomMomentTerm p η m ≤
        expectSet Ω (fun u => (1 + W u) ^ p) := by
    rw [h_binom_exp]
    have h_sub : insert k S_high ⊆ Finset.range (p + 1) := by
      intro m hm
      rcases Finset.mem_insert.mp hm with rfl | hm_high
      · exact Finset.mem_range.mpr (by omega)
      · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hm_high).1).1
    have h_not_mem : k ∉ S_high := by
      simp [S_high]
    have h_sum_sub :
        ∑ m ∈ insert k S_high, (p.choose m : ℝ) * expectSet Ω (fun u => W u ^ m) ≤
          ∑ j ∈ Finset.range (p + 1), (p.choose j : ℝ) * expectSet Ω (fun u => W u ^ j) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun j hj _ => ?_)
      rcases Nat.eq_zero_or_pos j with rfl | hj_pos
      · simp [expectSet_const hΩ]
      · exact mul_nonneg (Nat.cast_nonneg _) (hWj j hj_pos)
    rw [Finset.sum_insert h_not_mem] at h_sum_sub
    have h_term_k : binomMomentTerm p η k ≤ (p.choose k : ℝ) * expectSet Ω (fun u => W u ^ k) :=
      mul_le_mul_of_nonneg_left hWk (Nat.cast_nonneg _)
    have h_terms_high :
        ∑ m ∈ S_high, binomMomentTerm p η m ≤
          ∑ m ∈ S_high, (p.choose m : ℝ) * expectSet Ω (fun u => W u ^ m) := by
      refine Finset.sum_le_sum (fun m hm => ?_)
      have hm_even : Even m := (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2
      have hm_gt : k < m := (Finset.mem_filter.mp hm).2
      exact mul_le_mul_of_nonneg_left (h_lyap m (by omega) hm_even) (Nat.cast_nonneg _)
    linarith
  -- Step 3 (Appendix A): Apply Helper 2 and Helper 3
  have h_helper2 := (binom_term_ratio_gt_three_halves hη_pos hη_le hk hk_even hp).2
  have h_high_nonneg : 0 ≤ ∑ m ∈ S_high, binomMomentTerm p η m :=
    Finset.sum_nonneg (fun m _ => binomMomentTerm_nonneg p hη_pos.le m)
  have h_helper3 := (even_binom_sum_eq p η hη_le).2
  have h_five_eighteenths :
      (5 / 18 : ℝ) * (1 + 2 * η) ^ p ≤ expectSet Ω (fun u => (posPart (1 + W u)) ^ p) := by
    change (1 + 2 * η) ^ p / 2 ≤ ∑ m ∈ S_even, binomMomentTerm p η m at h_helper3
    change (5 / 9 : ℝ) * ∑ m ∈ S_low, binomMomentTerm p η m ≤ binomMomentTerm p η k at h_helper2
    linarith
  -- Step 4 (Appendix A): Apply Helper 4
  have h_helper4 := (one_add_two_eta_div_one_add_eta_pow_gt hη_pos hη_le hk hp).2
  have h_pow_strict : (1 + η) ^ p < expectSet Ω (fun u => (posPart (1 + W u)) ^ p) :=
    lt_of_lt_of_le h_helper4 h_five_eighteenths
  refine ⟨h_pow_strict, ?_⟩
  rw [lt_lpNormSet_iff hp1 (by linarith)]
  convert h_pow_strict using 2
  ext u
  rw [abs_of_nonneg (posPart_nonneg _)]

/-- **Claim A.1 (`clm_odd_moments_lower_bound`, Appendix A of `paper.tex`)**:
If $\eta \in (0, 1/4]$, even $k \ge 2$, $\mathbb{E}_{u \in \Omega}[W(u)^k] \ge (2\eta)^k$,
$\mathbb{E}_{u \in \Omega}[W(u)^j] \ge 0$ for all $j \ge 1$, and odd $p \ge k/\eta$, then
$\mathbb{E}_{u \in \Omega}[(\operatorname{posPart}(1 + W(u)))^p] > (1 + \eta)^p$ and
$\|\operatorname{posPart}(1 + W)\|_p > 1 + \eta$. -/
theorem clm_odd_moments_lower_bound {Ω : Finset α} (hΩ : Ω.Nonempty) (W : α → ℝ)
    {η : ℝ} {k p : ℕ} (hη_pos : 0 < η) (hη_le : η ≤ 1 / 4)
    (hk : 2 ≤ k) (hk_even : Even k)
    (hWk : (2 * η) ^ k ≤ expectSet Ω (fun u => W u ^ k))
    (hWj : ∀ j : ℕ, 1 ≤ j → 0 ≤ expectSet Ω (fun u => W u ^ j))
    (hp : (k : ℝ) / η ≤ (p : ℝ)) (hp_odd : Odd p) :
    (1 + η) ^ p < expectSet Ω (fun u => (posPart (1 + W u)) ^ p) ∧
      1 + η < lpNormSet Ω p (fun u => posPart (1 + W u)) :=
  clm_moments_lower_bound hΩ W hη_pos hη_le hk hk_even hWk hWj hp (Or.inl hp_odd)

end ClaimA1

/-!
## Lemma A.2: Decoupling and Spectral Positivity (Appendix A of `paper.tex`)
-/

section LemmaA2

variable {α β γ : Type*}

/-- Cauchy–Schwarz inequality for finite expectations:
$(\mathbb{E}_{i \in s}[f(i) g(i)])^2 \le \mathbb{E}_{i \in s}[f(i)^2] \cdot \mathbb{E}_{i \in s}[g(i)^2]$
(Lemma A.2, Appendix A of `paper.tex`). -/
lemma expectSet_mul_sq_le_sq_mul_sq (s : Finset α) (f g : α → ℝ) :
    (expectSet s (fun i => f i * g i)) ^ 2 ≤
      expectSet s (fun i => f i ^ 2) * expectSet s (fun i => g i ^ 2) := by
  unfold expectSet
  rw [div_pow, div_mul_div_comm, ← sq]
  exact div_le_div_of_nonneg_right (Finset.sum_mul_sq_le_sq_mul_sq s f g) (sq_nonneg _)

/-- Fubini expansion of the $k$-th moment of an inner product over $Y^k$
(Lemma A.2, Appendix A of `paper.tex`):
$$\mathbb{E}_{x \in X, z \in Z}\!\left[\left(\mathbb{E}_{y \in Y} f(x, y) g(z, y)\right)^k\right] =
\mathbb{E}_{y_1, \dots, y_k \in Y}\!\left[\left(\mathbb{E}_{x \in X}\prod_{i=1}^k f(x, y_i)\right)
\left(\mathbb{E}_{z \in Z}\prod_{i=1}^k g(z, y_i)\right)\right].$$ -/
lemma expectSet_inner_prod_pow_eq_col_expect (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (f : α → β → ℝ) (g : γ → β → ℝ) (k : ℕ) :
    expectSet X (fun x => expectSet Z (fun z => (expectSet Y (fun y => f x y * g z y)) ^ k)) =
      expectSet (Fintype.piFinset (fun _ : Fin k => Y))
        (fun ys =>
          (expectSet X (fun x => ∏ i : Fin k, f x (ys i))) *
            (expectSet Z (fun z => ∏ i : Fin k, g z (ys i)))) := by
  simp_rw [expectSet_pow_eq_piFinset Y _ k, Finset.prod_mul_distrib]
  have h1 :
      (fun x => expectSet Z (fun z => expectSet (Fintype.piFinset (fun _ : Fin k => Y))
        (fun ys => (∏ i : Fin k, f x (ys i)) * (∏ i : Fin k, g z (ys i))))) =
      (fun x => expectSet (Fintype.piFinset (fun _ : Fin k => Y))
        (fun ys => expectSet Z (fun z => (∏ i : Fin k, f x (ys i)) * (∏ i : Fin k, g z (ys i))))) := by
    ext x
    exact expectSet_comm Z (Fintype.piFinset (fun _ : Fin k => Y)) _
  rw [h1, expectSet_comm X (Fintype.piFinset (fun _ : Fin k => Y))]
  congr 1
  ext ys
  exact expectSet_mul_independent X Z _ _

/-- **Lemma A.2 (`decoupling_inner_prod_even_moment`, Appendix A of `paper.tex`)**:
For any $f : \alpha \to \beta \to \mathbb{R}$, $g : \gamma \to \beta \to \mathbb{R}$, and $k \in \mathbb{N}$
(in particular for even $k \ge 2$),
$$\left(\mathbb{E}_{x \in X, z \in Z}\!\left[\left(\mathbb{E}_{y \in Y} f(x, y) g(z, y)\right)^k\right]\right)^2
\le \|f\|_{U(2, k)}^{2k} \|g\|_{U(2, k)}^{2k}
= \operatorname{gridNorm2Pow} X Y f k \cdot \operatorname{gridNorm2Pow} Z Y g k.$$ -/
theorem decoupling_inner_prod_even_moment (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (f : α → β → ℝ) (g : γ → β → ℝ) (k : ℕ) :
    (expectSet X (fun x => expectSet Z (fun z => (expectSet Y (fun y => f x y * g z y)) ^ k))) ^ 2 ≤
      gridNorm2Pow X Y f k * gridNorm2Pow Z Y g k := by
  rw [expectSet_inner_prod_pow_eq_col_expect, gridNorm2Pow_eq_col_expect_sq X Y f k,
    gridNorm2Pow_eq_col_expect_sq Z Y g k]
  exact expectSet_mul_sq_le_sq_mul_sq (Fintype.piFinset (fun _ : Fin k => Y))
    (fun ys => expectSet X (fun x => ∏ i : Fin k, f x (ys i)))
    (fun ys => expectSet Z (fun z => ∏ i : Fin k, g z (ys i)))

end LemmaA2

/-!
## Proposition 3.1: Regular Matrices Have Uniform Products
(Section 3.2 & Appendix A of `paper.tex`)
-/

section Proposition31

variable {α β γ : Type*}

/-- Product expectation equals iterated expectation:
$\mathbb{E}_{(x, z) \in X \times Z}[h(x, z)] = \mathbb{E}_{x \in X}[\mathbb{E}_{z \in Z}[h(x, z)]]$. -/
lemma expectSet_product (X : Finset α) (Z : Finset γ) (h : α × γ → ℝ) :
    expectSet (X ×ˢ Z) h = expectSet X (fun x => expectSet Z (fun z => h (x, z))) := by
  unfold expectSet
  rw [Finset.sum_product, Finset.card_product, Nat.cast_mul,
    mul_comm (X.card : ℝ) (Z.card : ℝ), ← div_div, Finset.sum_div]

lemma expectSet_fst (X : Finset α) {Z : Finset γ} (hZ : Z.Nonempty) (f : α → ℝ) :
    expectSet (X ×ˢ Z) (fun xz => f xz.1) = expectSet X f := by
  rw [expectSet_product]
  congr 1
  ext x
  exact expectSet_const hZ (f x)

lemma expectSet_snd {X : Finset α} (hX : X.Nonempty) (Z : Finset γ) (g : γ → ℝ) :
    expectSet (X ×ˢ Z) (fun xz => g xz.2) = expectSet Z g := by
  rw [expectSet_product, expectSet_comm]
  congr 1
  ext z
  exact expectSet_const hX (g z)

lemma lpNormSet_fst (X : Finset α) {Z : Finset γ} (hZ : Z.Nonempty) (f : α → ℝ) (p : ℕ) :
    lpNormSet (X ×ˢ Z) p (fun xz => f xz.1) = lpNormSet X p f := by
  unfold lpNormSet
  rw [expectSet_fst X hZ (fun x => |f x| ^ p)]

lemma lpNormSet_snd {X : Finset α} (hX : X.Nonempty) (Z : Finset γ) (g : γ → ℝ) (p : ℕ) :
    lpNormSet (X ×ˢ Z) p (fun xz => g xz.2) = lpNormSet Z p g := by
  unfold lpNormSet
  rw [expectSet_snd hX Z (fun z => |g z| ^ p)]

/-- **Bilinear centering decomposition (`normMatMul_sub_one_decomp`, Appendix A of `paper.tex`)**:
For any matrices $A : \alpha \to \beta \to \mathbb{R}$, $B : \beta \to \gamma \to \mathbb{R}$, and
non-empty $Y$,
$$(A \circ B)(x, z) - 1 = \langle A_x - 1, B_z^T - 1 \rangle_Y
  + (\operatorname{rowDeg} Y A x - 1) + (\operatorname{rowDeg} Y B^T z - 1).$$ -/
theorem normMatMul_sub_one_decomp {Y : Finset β} (hY : Y.Nonempty)
    (A : α → β → ℝ) (B : β → γ → ℝ) (x : α) (z : γ) :
    normMatMul Y A B x z - 1 =
      expectSet Y (fun y => (A x y - 1) * (matTranspose B z y - 1)) +
        (rowDeg Y A x - 1) + (rowDeg Y (matTranspose B) z - 1) := by
  unfold normMatMul rowDeg matTranspose
  have h1 : expectSet Y (fun _ => (1 : ℝ)) = 1 := expectSet_const hY 1
  have h_pt : (fun y => (A x y - 1) * (B y z - 1)) =
      (fun y => (A x y * B y z - A x y) - B y z + 1) := by
    ext y; ring
  rw [h_pt, expectSet_add, expectSet_sub, expectSet_sub, h1]
  ring

/-- Equivalence between `gridNormPow X Y M 2 d` and `gridNorm2Pow X Y M d`
(Definition 3.1 `\eqref{eq:grid-norm-fubini}`, §3.2 of `paper.tex`). -/
lemma gridNormPow_two_eq_gridNorm2Pow (X : Finset α) (Y : Finset β) (M : α → β → ℝ) (d : ℕ) :
    gridNormPow X Y M 2 d = gridNorm2Pow X Y M d := by
  rw [gridNormPow_eq_gridNormPowCol, gridNorm2Pow_eq_col_expect_sq]
  rfl

/-- Power-form bound from $(\varepsilon, 2, D)$-regularity when $\mathbb{E}[A] = 1$:
$\operatorname{gridNorm2Pow} X Y A D \le (1 + \varepsilon)^{2D}$
(Definition 3.1, §3.2 & Appendix A of `paper.tex`). -/
lemma gridNorm2Pow_le_of_isGridRegular_unit (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    {ε : ℝ} {D : ℕ} (_hε : 0 ≤ ε) (hD : 1 ≤ D)
    (hA_dens : matDensity X Y A = 1) (hA_reg : IsGridRegular X Y A ε 2 D) :
    gridNorm2Pow X Y A D ≤ (1 + ε) ^ (2 * D) := by
  unfold IsGridRegular gridNorm at hA_reg
  rw [hA_dens, mul_one, gridNormPow_two_eq_gridNorm2Pow] at hA_reg
  have h_nonneg : 0 ≤ gridNorm2Pow X Y A D := gridNorm2Pow_nonneg X Y A D
  have h_rpow_nonneg :
      0 ≤ (gridNorm2Pow X Y A D) ^ ((1 : ℝ) / ((2 * D : ℕ) : ℝ)) :=
    Real.rpow_nonneg h_nonneg _
  have h_pow := pow_le_pow_left₀ h_rpow_nonneg hA_reg (2 * D)
  have h2D_ne : ((2 * D : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [← Real.rpow_natCast, ← Real.rpow_mul h_nonneg,
    one_div_mul_cancel h2D_ne, Real.rpow_one] at h_pow
  exact h_pow

/-- Pointwise and $L_q$ bound on the negative part of $\operatorname{rowDeg} Y A x - 1$ from
$\varepsilon$-min-degree when $\mathbb{E}[A] = 1$:
$\operatorname{negPart}(\operatorname{rowDeg} Y A x - 1) \le \varepsilon$ and
$\|\operatorname{negPart}(a - 1)\|_q \le \varepsilon$ (Appendix A of `paper.tex`). -/
lemma negPart_rowDeg_sub_one_le_eps {X : Finset α} (hX : X.Nonempty) (Y : Finset β)
    (A : α → β → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hA_dens : matDensity X Y A = 1) (hA_min : IsEpsMinDegree X Y A ε) :
    (∀ x ∈ X, negPart (rowDeg Y A x - 1) ≤ ε) ∧
      ∀ q : ℕ, 1 ≤ q → lpNormSet X q (fun x => negPart (rowDeg Y A x - 1)) ≤ ε := by
  have h_pt : ∀ x ∈ X, negPart (rowDeg Y A x - 1) ≤ ε := by
    intro x hx
    have hdeg := hA_min x hx
    rw [hA_dens, mul_one] at hdeg
    unfold negPart
    exact max_le (by linarith) hε
  refine ⟨h_pt, fun q hq => ?_⟩
  refine lpNormSet_le_of_bound hX hε hq (fun x hx => ?_)
  rw [abs_of_nonneg (negPart_nonneg _)]
  exact h_pt x hx

/-- Jensen comparison $\|a\|_D = \|A\|_{U(1, D)} \le \|A\|_{U(2, D)} \le 1 + \varepsilon$ for a
normalized $(\varepsilon, 2, D)$-regular matrix $A \ge 0$ (Appendix A of `paper.tex`). -/
lemma lpNormSet_rowDeg_le_one_add_eps {X : Finset α} {Y : Finset β}
    (_hX : X.Nonempty) (hY : Y.Nonempty) (A : α → β → ℝ)
    (hA_nonneg : ∀ x ∈ X, ∀ y ∈ Y, 0 ≤ A x y)
    {ε : ℝ} {D : ℕ} (hε : 0 ≤ ε) (hD : 1 ≤ D)
    (hA_dens : matDensity X Y A = 1) (hA_reg : IsGridRegular X Y A ε 2 D) :
    expectSet X (fun x => (rowDeg Y A x) ^ D) ≤ (1 + ε) ^ D ∧
      lpNormSet X D (rowDeg Y A) ≤ 1 + ε := by
  let S_Y := Fintype.piFinset (fun _ : Fin D => Y)
  rcases hY with ⟨y₀, hy₀⟩
  have hSY : S_Y.Nonempty := ⟨fun _ => y₀, Fintype.mem_piFinset.mpr (fun _ => hy₀)⟩
  let g : (Fin D → β) → ℝ := fun ys => expectSet X (fun x => ∏ j : Fin D, A x (ys j))
  have h_eq_col : expectSet X (fun x => (rowDeg Y A x) ^ D) = expectSet S_Y g := by
    unfold rowDeg S_Y g
    simp_rw [expectSet_pow_eq_piFinset Y _ D]
    exact expectSet_comm X (Fintype.piFinset (fun _ : Fin D => Y)) _
  have h_cs := expectSet_mul_sq_le_sq_mul_sq S_Y (fun _ => 1) g
  simp only [one_mul, one_pow, expectSet_const hSY 1] at h_cs
  have h_gn2 : expectSet S_Y (fun ys => g ys ^ 2) = gridNorm2Pow X Y A D :=
    (gridNorm2Pow_eq_col_expect_sq X Y A D).symm
  have h_reg2 := gridNorm2Pow_le_of_isGridRegular_unit X Y A hε hD hA_dens hA_reg
  have h_sq_le : (expectSet X (fun x => (rowDeg Y A x) ^ D)) ^ 2 ≤ ((1 + ε) ^ D) ^ 2 := by
    rw [h_eq_col]
    calc
      (expectSet S_Y g) ^ 2 ≤ expectSet S_Y (fun ys => g ys ^ 2) := h_cs
      _ = gridNorm2Pow X Y A D := h_gn2
      _ ≤ (1 + ε) ^ (2 * D) := h_reg2
      _ = ((1 + ε) ^ D) ^ 2 := by rw [pow_mul']
  have h_row_nonneg : ∀ x ∈ X, 0 ≤ rowDeg Y A x :=
    fun x hx => expectSet_nonneg (fun y hy => hA_nonneg x hx y hy)
  have h_exp_nonneg : 0 ≤ expectSet X (fun x => (rowDeg Y A x) ^ D) :=
    expectSet_nonneg (fun x hx => pow_nonneg (h_row_nonneg x hx) D)
  have h_pow_le : expectSet X (fun x => (rowDeg Y A x) ^ D) ≤ (1 + ε) ^ D := by
    have h_abs := abs_le_of_sq_le_sq' h_sq_le (pow_nonneg (by linarith) D)
    exact h_abs.2
  refine ⟨h_pow_le, ?_⟩
  rw [lpNormSet_le_iff hD (by linarith)]
  have h_abs_eq : expectSet X (fun x => |rowDeg Y A x| ^ D) =
      expectSet X (fun x => (rowDeg Y A x) ^ D) := by
    unfold expectSet
    congr 1
    refine Finset.sum_congr rfl (fun x hx => ?_)
    dsimp only
    rw [abs_of_nonneg (h_row_nonneg x hx)]
  rw [h_abs_eq]
  exact h_pow_le

/-- **Row-degree $L_k$ deviation bound (`rowDeg_sub_one_Lk_bound`, Appendix A of `paper.tex`)**:
If $A \ge 0$ on $X \times Y$ has $\mathbb{E}[A] = 1$, is $(\varepsilon, 2, D)$-regular and
$\varepsilon$-min-degree with $\varepsilon \in (0, 1/80)$, and even $k \ge 2$ satisfies
$k \le 2 \varepsilon D$, then $\|\operatorname{rowDeg} Y A - 1\|_k \le 5\varepsilon$. -/
theorem rowDeg_sub_one_Lk_bound {X : Finset α} {Y : Finset β}
    (hX : X.Nonempty) (hY : Y.Nonempty) (A : α → β → ℝ)
    (hA_nonneg : ∀ x ∈ X, ∀ y ∈ Y, 0 ≤ A x y)
    {ε : ℝ} {D k : ℕ} (hε_pos : 0 < ε) (hε_lt : ε < 1 / 80)
    (hD : 1 ≤ D) (hk : 2 ≤ k) (hk_even : Even k)
    (hkD : (k : ℝ) / (2 * ε) ≤ (D : ℝ))
    (hA_dens : matDensity X Y A = 1)
    (hA_reg : IsGridRegular X Y A ε 2 D)
    (hA_min : IsEpsMinDegree X Y A ε) :
    lpNormSet X k (fun x => posPart (rowDeg Y A x - 1)) ≤ 4 * ε ∧
      lpNormSet X k (fun x => rowDeg Y A x - 1) ≤ 5 * ε := by
  have hk1 : 1 ≤ k := by omega
  have h_neg := negPart_rowDeg_sub_one_le_eps hX Y A hε_pos.le hA_dens hA_min
  have h_neg_D : lpNormSet X D (fun x => negPart (rowDeg Y A x - 1)) ≤ ε := h_neg.2 D hD
  have h_neg_k : lpNormSet X k (fun x => negPart (rowDeg Y A x - 1)) ≤ ε := h_neg.2 k hk1
  have h_row_D : lpNormSet X D (rowDeg Y A) ≤ 1 + ε :=
    (lpNormSet_rowDeg_le_one_add_eps hX hY A hA_nonneg hε_pos.le hD hA_dens hA_reg).2
  -- Minkowski bound on 1 + (a - 1)_+ = a + (a - 1)_- (Appendix A)
  have h_one_add_pos_D :
      lpNormSet X D (fun x => posPart (1 + posPart (rowDeg Y A x - 1))) ≤ 1 + 2 * ε := by
    have h_eq : (fun x => posPart (1 + posPart (rowDeg Y A x - 1))) =
        (fun x => rowDeg Y A x + negPart (rowDeg Y A x - 1)) := by
      ext x
      have h_pos_nonneg : 0 ≤ 1 + posPart (rowDeg Y A x - 1) := by
        have := posPart_nonneg (rowDeg Y A x - 1)
        linarith
      change max (1 + posPart (rowDeg Y A x - 1)) 0 = rowDeg Y A x + negPart (rowDeg Y A x - 1)
      rw [max_eq_left h_pos_nonneg]
      have h_sub := posPart_sub_negPart (rowDeg Y A x - 1)
      linarith
    rw [h_eq]
    calc
      lpNormSet X D (fun x => rowDeg Y A x + negPart (rowDeg Y A x - 1))
        ≤ lpNormSet X D (rowDeg Y A) + lpNormSet X D (fun x => negPart (rowDeg Y A x - 1)) :=
        lpNormSet_add_le X hD (rowDeg Y A) (fun x => negPart (rowDeg Y A x - 1))
      _ ≤ (1 + ε) + ε := add_le_add h_row_D h_neg_D
      _ = 1 + 2 * ε := by ring
  -- Apply Claim A.1 with η = 2ε to bound ‖(a - 1)_+‖_k ≤ 4ε (Appendix A)
  have h_pos_k : lpNormSet X k (fun x => posPart (rowDeg Y A x - 1)) ≤ 4 * ε := by
    by_contra! h_gt
    have h_pow_gt : (2 * (2 * ε)) ^ k <
        expectSet X (fun x => (posPart (rowDeg Y A x - 1)) ^ k) := by
      have h1 : (4 * ε) ^ k <
          expectSet X (fun x => |posPart (rowDeg Y A x - 1)| ^ k) :=
        (lt_lpNormSet_iff hk1 (by positivity)).mp h_gt
      have h2 : (4 * ε : ℝ) = 2 * (2 * ε) := by ring
      rw [← h2]
      convert h1 using 2
      ext x
      rw [abs_of_nonneg (posPart_nonneg _)]
    have h_clm := (clm_moments_lower_bound hX (fun x => posPart (rowDeg Y A x - 1))
      (η := 2 * ε) (k := k) (p := D)
      (by linarith) (by linarith) hk hk_even (le_of_lt h_pow_gt)
      (fun j _ => expectSet_nonneg (fun _ _ => pow_nonneg (posPart_nonneg _) j))
      hkD
      (Or.inr (fun x _ => by have := posPart_nonneg (rowDeg Y A x - 1); linarith))).2
    linarith
  refine ⟨h_pos_k, ?_⟩
  -- Combine (a - 1)_+ and (a - 1)_- via |a - 1| = (a - 1)_+ + (a - 1)_- (Appendix A)
  have h_decomp_abs :
      lpNormSet X k (fun x => rowDeg Y A x - 1) =
        lpNormSet X k (fun x => posPart (rowDeg Y A x - 1) + negPart (rowDeg Y A x - 1)) := by
    have h_fn : (fun x => |rowDeg Y A x - 1| ^ k) =
        (fun x => |posPart (rowDeg Y A x - 1) + negPart (rowDeg Y A x - 1)| ^ k) := by
      ext x
      have h_add := posPart_add_negPart (rowDeg Y A x - 1)
      have h_nonneg : 0 ≤ posPart (rowDeg Y A x - 1) + negPart (rowDeg Y A x - 1) :=
        add_nonneg (posPart_nonneg _) (negPart_nonneg _)
      rw [abs_of_nonneg h_nonneg, h_add]
    unfold lpNormSet
    rw [h_fn]
  rw [h_decomp_abs]
  calc
    lpNormSet X k (fun x => posPart (rowDeg Y A x - 1) + negPart (rowDeg Y A x - 1))
      ≤ lpNormSet X k (fun x => posPart (rowDeg Y A x - 1)) +
          lpNormSet X k (fun x => negPart (rowDeg Y A x - 1)) :=
      lpNormSet_add_le X hk1 _ _
    _ ≤ 4 * ε + ε := add_le_add h_pos_k h_neg_k
    _ = 5 * ε := by ring

/-- **`\eqref{eq:klm-triangle}`, Appendix A of `paper.tex`**:
Triangle inequality reducing $\|(A \circ B) - 1\|_k$ to $\|\langle A_x - 1, B_z^T - 1 \rangle\|_k + 10\varepsilon$. -/
theorem klm_triangle_bound {X : Finset α} {Y : Finset β} {Z : Finset γ}
    (hX : X.Nonempty) (hY : Y.Nonempty) (hZ : Z.Nonempty)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    (hA_nonneg : ∀ x ∈ X, ∀ y ∈ Y, 0 ≤ A x y)
    (hB_nonneg : ∀ z ∈ Z, ∀ y ∈ Y, 0 ≤ matTranspose B z y)
    {ε : ℝ} {D k : ℕ} (hε_pos : 0 < ε) (hε_lt : ε < 1 / 80)
    (hD : 1 ≤ D) (hk : 2 ≤ k) (hk_even : Even k)
    (hkD : (k : ℝ) / (2 * ε) ≤ (D : ℝ))
    (hA_dens : matDensity X Y A = 1)
    (hB_dens : matDensity Z Y (matTranspose B) = 1)
    (hA_reg : IsGridRegular X Y A ε 2 D)
    (hB_reg : IsGridRegular Z Y (matTranspose B) ε 2 D)
    (hA_min : IsEpsMinDegree X Y A ε)
    (hB_min : IsEpsMinDegree Z Y (matTranspose B) ε) :
    lpNormSet (X ×ˢ Z) k (fun xz => normMatMul Y A B xz.1 xz.2 - 1) ≤
      lpNormSet (X ×ˢ Z) k
        (fun xz => expectSet Y (fun y => (A xz.1 y - 1) * (matTranspose B xz.2 y - 1))) +
      10 * ε := by
  have hk1 : 1 ≤ k := by omega
  have hA_row := (rowDeg_sub_one_Lk_bound hX hY A hA_nonneg hε_pos hε_lt hD hk hk_even hkD
    hA_dens hA_reg hA_min).2
  have hB_row := (rowDeg_sub_one_Lk_bound hZ hY (matTranspose B) hB_nonneg hε_pos hε_lt hD hk
    hk_even hkD hB_dens hB_reg hB_min).2
  have h_decomp : (fun xz : α × γ => normMatMul Y A B xz.1 xz.2 - 1) =
      (fun xz : α × γ =>
        (expectSet Y (fun y => (A xz.1 y - 1) * (matTranspose B xz.2 y - 1)) +
          (rowDeg Y A xz.1 - 1)) +
        (rowDeg Y (matTranspose B) xz.2 - 1)) := by
    ext xz
    exact normMatMul_sub_one_decomp hY A B xz.1 xz.2
  rw [h_decomp]
  have h_tri1 := lpNormSet_add_le (X ×ˢ Z) hk1
    (fun xz => expectSet Y (fun y => (A xz.1 y - 1) * (matTranspose B xz.2 y - 1)) +
      (rowDeg Y A xz.1 - 1))
    (fun xz => rowDeg Y (matTranspose B) xz.2 - 1)
  have h_tri2 := lpNormSet_add_le (X ×ˢ Z) hk1
    (fun xz => expectSet Y (fun y => (A xz.1 y - 1) * (matTranspose B xz.2 y - 1)))
    (fun xz => rowDeg Y A xz.1 - 1)
  rw [lpNormSet_snd hX Z (fun z => rowDeg Y (matTranspose B) z - 1) k] at h_tri1
  rw [lpNormSet_fst X hZ (fun x => rowDeg Y A x - 1) k] at h_tri2
  linarith

/-- Pointwise non-negative upper bound on $\operatorname{posPart}(1 + M(x, x'))$ for the centered
Gram kernel $M(x, x') := \langle A_x - 1, A_{x'} - 1 \rangle_Y$
(Appendix A of `paper.tex`):
$$0 \le \operatorname{posPart}(1 + M(x, x')) \le
  \langle A_x, A_{x'} \rangle_Y + \operatorname{negPart}(a(x) - 1) + \operatorname{negPart}(a(x') - 1).$$ -/
lemma posPart_one_add_centered_gram_le {X : Finset α} {Y : Finset β} (hY : Y.Nonempty)
    (A : α → β → ℝ) (hA_nonneg : ∀ x ∈ X, ∀ y ∈ Y, 0 ≤ A x y)
    {x x' : α} (hx : x ∈ X) (hx' : x' ∈ X) :
    0 ≤ posPart (1 + expectSet Y (fun y => (A x y - 1) * (A x' y - 1))) ∧
    posPart (1 + expectSet Y (fun y => (A x y - 1) * (A x' y - 1))) ≤
      expectSet Y (fun y => A x y * A x' y) +
        negPart (rowDeg Y A x - 1) + negPart (rowDeg Y A x' - 1) := by
  refine ⟨posPart_nonneg _, ?_⟩
  have h_decomp := normMatMul_sub_one_decomp hY A (matTranspose A) x x'
  unfold normMatMul matTranspose at h_decomp
  have h_neg1 : -(rowDeg Y A x - 1) ≤ negPart (rowDeg Y A x - 1) := le_max_left _ 0
  have h_neg2 : -(rowDeg Y A x' - 1) ≤ negPart (rowDeg Y A x' - 1) := le_max_left _ 0
  have h_inner_nonneg : 0 ≤ expectSet Y (fun y => A x y * A x' y) :=
    expectSet_nonneg (fun y hy => mul_nonneg (hA_nonneg x hx y hy) (hA_nonneg x' hx' y hy))
  have h_n1_nonneg : 0 ≤ negPart (rowDeg Y A x - 1) := negPart_nonneg _
  have h_n2_nonneg : 0 ≤ negPart (rowDeg Y A x' - 1) := negPart_nonneg _
  unfold posPart
  refine max_le ?_ ?_
  · linarith
  · linarith

/-- Centered Gram self-kernel $L_k$ bound (Appendix A of `paper.tex`):
for $M(x, x') = \langle A_x - 1, A_{x'} - 1 \rangle_Y$, we have $\|M\|_k \le 10\varepsilon$, i.e.,
$\operatorname{gridNorm2Pow} X Y (A - 1) k \le (10\varepsilon)^k$. -/
lemma centered_gram_self_Lk_bound {X : Finset α} {Y : Finset β}
    (hX : X.Nonempty) (hY : Y.Nonempty) (A : α → β → ℝ)
    (hA_nonneg : ∀ x ∈ X, ∀ y ∈ Y, 0 ≤ A x y)
    {ε : ℝ} {D k : ℕ} (hε_pos : 0 < ε) (hε_lt : ε < 1 / 80)
    (hD_even : Even D) (hD_ge : 4 / ε ≤ (D : ℝ))
    (hk : 2 ≤ k) (hk_even : Even k) (hkD : (k : ℝ) ≤ ε * (D : ℝ))
    (hA_dens : matDensity X Y A = 1)
    (hA_reg : IsGridRegular X Y A ε 2 D)
    (hA_min : IsEpsMinDegree X Y A ε) :
    gridNorm2Pow X Y (fun x y => A x y - 1) k ≤ (10 * ε) ^ k ∧
      lpNormSet (X ×ˢ X) k
        (fun xx' => expectSet Y (fun y => (A xx'.1 y - 1) * (A xx'.2 y - 1))) ≤ 10 * ε := by
  have hk1 : 1 ≤ k := by omega
  have hD_real_gt : (320 : ℝ) < (D : ℝ) := by
    have := (div_le_iff₀ hε_pos).mp hD_ge
    nlinarith
  have hD_ge_320 : 320 ≤ D := by
    have : (320 : ℝ) ≤ (D : ℝ) := le_of_lt hD_real_gt
    exact_mod_cast this
  have hD1 : 1 ≤ D := by omega
  let p : ℕ := D - 1
  have hp1 : 1 ≤ p := by omega
  have hp_le_D : p ≤ D := Nat.sub_le D 1
  have hp_odd : Odd p := by
    rcases hD_even with ⟨m, hm⟩
    refine ⟨m - 1, ?_⟩
    omega
  have hp_ge_ratio : (k : ℝ) / (5 * ε) ≤ (p : ℝ) := by
    have hp_real : (p : ℝ) = (D : ℝ) - 1 := by
      dsimp [p]
      rw [Nat.cast_sub hD1, Nat.cast_one]
    have h1 : (k : ℝ) / (5 * ε) ≤ (ε * (D : ℝ)) / (5 * ε) :=
      div_le_div_of_nonneg_right hkD (by positivity)
    have h2 : (ε * (D : ℝ)) / (5 * ε) = (D : ℝ) / 5 := by
      have hε_ne : ε ≠ 0 := hε_pos.ne'
      field_simp
    linarith
  let M : α × α → ℝ := fun xx' => expectSet Y (fun y => (A xx'.1 y - 1) * (A xx'.2 y - 1))
  have hXX : (X ×ˢ X).Nonempty := hX.product hX
  have h_Mk_eq : expectSet (X ×ˢ X) (fun xx' => |M xx'| ^ k) =
      gridNorm2Pow X Y (fun x y => A x y - 1) k := by
    have h_abs : (fun xx' : α × α => |M xx'| ^ k) = (fun xx' : α × α => M xx' ^ k) := by
      ext xx'
      exact hk_even.pow_abs (M xx')
    rw [h_abs, expectSet_product]
    rfl
  -- Prove lpNormSet (X ×ˢ X) k M ≤ 10 * ε by contradiction (Appendix A)
  have h_norm_le : lpNormSet (X ×ˢ X) k M ≤ 10 * ε := by
    by_contra! h_gt
    have h_Wk : (2 * (5 * ε)) ^ k ≤ expectSet (X ×ˢ X) (fun xx' => M xx' ^ k) := by
      have h1 : (10 * ε) ^ k < expectSet (X ×ˢ X) (fun xx' => |M xx'| ^ k) :=
        (lt_lpNormSet_iff hk1 (by positivity)).mp h_gt
      have h2 : (10 * ε : ℝ) = 2 * (5 * ε) := by ring
      rw [h_Mk_eq] at h1
      rw [expectSet_product, ← h2]
      exact le_of_lt h1
    have h_Wj : ∀ j : ℕ, 1 ≤ j → 0 ≤ expectSet (X ×ˢ X) (fun xx' => M xx' ^ j) := by
      intro j _
      rw [expectSet_product]
      exact gridNorm2Pow_nonneg X Y (fun x y => A x y - 1) j
    -- Claim A.1 with η = 5ε ≤ 1/16 < 1/4 and odd p = D - 1 (Appendix A)
    have h_clm := (clm_odd_moments_lower_bound hXX M
      (η := 5 * ε) (k := k) (p := p)
      (by linarith) (by linarith) hk hk_even h_Wk h_Wj hp_ge_ratio hp_odd).2
    -- Monotonicity ‖(1 + M)_+‖_p ≤ ‖(1 + M)_+‖_D (Appendix A)
    have h_mono_exp := lpNormSet_mono_exponent hXX (fun xx' => posPart (1 + M xx')) hp1 hp_le_D
    -- Pointwise domination by ⟨A_x, A_{x'}⟩ + (a(x) - 1)_- + (a(x') - 1)_- (Appendix A)
    let U : α × α → ℝ := fun xx' =>
      (expectSet Y (fun y => A xx'.1 y * A xx'.2 y) + negPart (rowDeg Y A xx'.1 - 1)) +
        negPart (rowDeg Y A xx'.2 - 1)
    have h_mono_pt : lpNormSet (X ×ˢ X) D (fun xx' => posPart (1 + M xx')) ≤ lpNormSet (X ×ˢ X) D U := by
      refine lpNormSet_mono D (fun xx' hxx' => ?_)
      rcases Finset.mem_product.mp hxx' with ⟨hx, hx'⟩
      have h_pt := posPart_one_add_centered_gram_le hY A hA_nonneg hx hx'
      have hU_nonneg : 0 ≤ U xx' := le_trans h_pt.1 h_pt.2
      rw [abs_of_nonneg h_pt.1, abs_of_nonneg hU_nonneg]
      exact h_pt.2
    -- Minkowski's inequality on U (Appendix A)
    have h_tri1 := lpNormSet_add_le (X ×ˢ X) hD1
      (fun xx' => expectSet Y (fun y => A xx'.1 y * A xx'.2 y) + negPart (rowDeg Y A xx'.1 - 1))
      (fun xx' => negPart (rowDeg Y A xx'.2 - 1))
    have h_tri2 := lpNormSet_add_le (X ×ˢ X) hD1
      (fun xx' => expectSet Y (fun y => A xx'.1 y * A xx'.2 y))
      (fun xx' => negPart (rowDeg Y A xx'.1 - 1))
    rw [lpNormSet_snd hX X (fun x' => negPart (rowDeg Y A x' - 1)) D] at h_tri1
    rw [lpNormSet_fst X hX (fun x => negPart (rowDeg Y A x - 1)) D] at h_tri2
    have h_neg_D := (negPart_rowDeg_sub_one_le_eps hX Y A hε_pos.le hA_dens hA_min).2 D hD1
    -- Bound ‖⟨A_x, A_{x'}⟩‖_D ≤ (1 + ε)^2 from (ε, 2, D)-regularity (Appendix A)
    have h_inner_D :
        lpNormSet (X ×ˢ X) D (fun xx' => expectSet Y (fun y => A xx'.1 y * A xx'.2 y)) ≤
          (1 + ε) ^ 2 := by
      rw [lpNormSet_le_iff hD1 (by positivity)]
      have h_abs_eq :
          expectSet (X ×ˢ X) (fun xx' => |expectSet Y (fun y => A xx'.1 y * A xx'.2 y)| ^ D) =
            gridNorm2Pow X Y A D := by
        rw [expectSet_product]
        unfold gridNorm2Pow expectSet
        congr 1
        refine Finset.sum_congr rfl (fun x hx => ?_)
        dsimp only
        congr 1
        refine Finset.sum_congr rfl (fun x' hx' => ?_)
        dsimp only
        have h_nonneg : 0 ≤ (∑ y ∈ Y, A x y * A x' y) / (Y.card : ℝ) :=
          div_nonneg
            (Finset.sum_nonneg (fun y hy => mul_nonneg (hA_nonneg x hx y hy) (hA_nonneg x' hx' y hy)))
            (Nat.cast_nonneg _)
        rw [abs_of_nonneg h_nonneg]
      rw [h_abs_eq, ← pow_mul]
      exact gridNorm2Pow_le_of_isGridRegular_unit X Y A hε_pos.le hD1 hA_dens hA_reg
    -- Contradiction: 1 + 5ε < (1 + ε)^2 + 2ε = 1 + 4ε + ε^2 < 1 + 5ε (Appendix A)
    nlinarith
  refine ⟨?_, h_norm_le⟩
  rw [← h_Mk_eq, ← lpNormSet_le_iff hk1 (by positivity)]
  exact h_norm_le

/-- **Centered Gram kernel decoupling bound (`centered_gram_Lk_bound`, Appendix A of `paper.tex`)**:
For normalized $(\varepsilon, 2, D)$-regular, $\varepsilon$-min-degree matrices $A$ and $B^T$,
$\|\langle A_x - 1, B_z^T - 1 \rangle_Y\|_k \le 10\varepsilon$. -/
theorem centered_gram_Lk_bound {X : Finset α} {Y : Finset β} {Z : Finset γ}
    (hX : X.Nonempty) (hY : Y.Nonempty) (hZ : Z.Nonempty)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    (hA_nonneg : ∀ x ∈ X, ∀ y ∈ Y, 0 ≤ A x y)
    (hB_nonneg : ∀ z ∈ Z, ∀ y ∈ Y, 0 ≤ matTranspose B z y)
    {ε : ℝ} {D k : ℕ} (hε_pos : 0 < ε) (hε_lt : ε < 1 / 80)
    (hD_even : Even D) (hD_ge : 4 / ε ≤ (D : ℝ))
    (hk : 2 ≤ k) (hk_even : Even k) (hkD : (k : ℝ) ≤ ε * (D : ℝ))
    (hA_dens : matDensity X Y A = 1)
    (hB_dens : matDensity Z Y (matTranspose B) = 1)
    (hA_reg : IsGridRegular X Y A ε 2 D)
    (hB_reg : IsGridRegular Z Y (matTranspose B) ε 2 D)
    (hA_min : IsEpsMinDegree X Y A ε)
    (hB_min : IsEpsMinDegree Z Y (matTranspose B) ε) :
    lpNormSet (X ×ˢ Z) k
      (fun xz => expectSet Y (fun y => (A xz.1 y - 1) * (matTranspose B xz.2 y - 1))) ≤
        10 * ε := by
  have hk1 : 1 ≤ k := by omega
  have hA_gram := (centered_gram_self_Lk_bound hX hY A hA_nonneg hε_pos hε_lt hD_even hD_ge
    hk hk_even hkD hA_dens hA_reg hA_min).1
  have hB_gram := (centered_gram_self_Lk_bound hZ hY (matTranspose B) hB_nonneg hε_pos hε_lt
    hD_even hD_ge hk hk_even hkD hB_dens hB_reg hB_min).1
  -- Apply Lemma A.2 (decoupling_inner_prod_even_moment, Appendix A)
  have h_dec := decoupling_inner_prod_even_moment X Y Z
    (fun x y => A x y - 1) (fun z y => matTranspose B z y - 1) k
  have h_prod_le :
      gridNorm2Pow X Y (fun x y => A x y - 1) k *
        gridNorm2Pow Z Y (fun z y => matTranspose B z y - 1) k ≤
      ((10 * ε) ^ k) ^ 2 := by
    rw [sq]
    exact mul_le_mul hA_gram hB_gram
      (gridNorm2Pow_nonneg Z Y _ k) (by positivity)
  have h_sq_le := le_trans h_dec h_prod_le
  have h_exp_le :
      expectSet X (fun x => expectSet Z (fun z =>
        (expectSet Y (fun y => (A x y - 1) * (matTranspose B z y - 1))) ^ k)) ≤
        (10 * ε) ^ k :=
    (abs_le_of_sq_le_sq' h_sq_le (by positivity)).2
  rw [lpNormSet_le_iff hk1 (by positivity), expectSet_product]
  have h_even_abs :
      expectSet X (fun x => expectSet Z (fun z =>
        |expectSet Y (fun y => (A x y - 1) * (matTranspose B z y - 1))| ^ k)) =
      expectSet X (fun x => expectSet Z (fun z =>
        (expectSet Y (fun y => (A x y - 1) * (matTranspose B z y - 1))) ^ k)) := by
    congr 1; ext x; congr 1; ext z
    exact hk_even.pow_abs _
  rw [h_even_abs]
  exact h_exp_le

/-- Unit-density case of Proposition 3.1 (Appendix A of `paper.tex`):
when $\mathbb{E}[A] = \mathbb{E}[B^T] = 1$, $A \circ B$ is $(1, 80\varepsilon, 2^{-\varepsilon D / 2})$-uniform
on $X \times Z$. -/
theorem prop_regular_matrices_uniform_product_unit {X : Finset α} {Y : Finset β} {Z : Finset γ}
    (hX : X.Nonempty) (hY : Y.Nonempty) (hZ : Z.Nonempty)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    (hA_nonneg : ∀ x ∈ X, ∀ y ∈ Y, 0 ≤ A x y)
    (hB_nonneg : ∀ z ∈ Z, ∀ y ∈ Y, 0 ≤ matTranspose B z y)
    {ε : ℝ} {D : ℕ} (hε_pos : 0 < ε) (hε_lt : ε < 1 / 80)
    (hD_even : Even D) (hD_ge : 4 / ε ≤ (D : ℝ))
    (hA_dens : matDensity X Y A = 1)
    (hB_dens : matDensity Z Y (matTranspose B) = 1)
    (hA_reg : IsGridRegular X Y A ε 2 D)
    (hB_reg : IsGridRegular Z Y (matTranspose B) ε 2 D)
    (hA_min : IsEpsMinDegree X Y A ε)
    (hB_min : IsEpsMinDegree Z Y (matTranspose B) ε) :
    IsUniformMatrix X Z (normMatMul Y A B) 1 (80 * ε) ((2 : ℝ) ^ (- (ε * (D : ℝ) / 2))) := by
  -- Define k := 2 ⌊ε D / 2⌋ (Appendix A)
  let m : ℕ := Nat.floor (ε * (D : ℝ) / 2)
  let k : ℕ := 2 * m
  have hεD_ge_4 : 4 ≤ ε * (D : ℝ) := by
    have := (div_le_iff₀ hε_pos).mp hD_ge
    linarith
  have hm_ge_2 : 2 ≤ m := by
    exact Nat.le_floor (by linarith : (2 : ℝ) ≤ ε * (D : ℝ) / 2)
  have hk : 2 ≤ k := by omega
  have hk1 : 1 ≤ k := by omega
  have hk_even : Even k := ⟨m, by omega⟩
  have hk_le : (k : ℝ) ≤ ε * (D : ℝ) := by
    have hm_le : (m : ℝ) ≤ ε * (D : ℝ) / 2 := Nat.floor_le (by positivity)
    have hk_eq : (k : ℝ) = 2 * (m : ℝ) := by push_cast [k]; ring
    linarith
  have hk_ge : ε * (D : ℝ) / 2 ≤ (k : ℝ) := by
    have hm_gt : ε * (D : ℝ) / 2 - 1 < (m : ℝ) := Nat.sub_one_lt_floor (ε * (D : ℝ) / 2)
    have hk_eq : (k : ℝ) = 2 * (m : ℝ) := by push_cast [k]; ring
    linarith
  have hkD_div : (k : ℝ) / (2 * ε) ≤ (D : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hD1 : 1 ≤ D := by
    have : (320 : ℝ) < (D : ℝ) := by nlinarith
    have hD320 : 320 ≤ D := by exact_mod_cast (le_of_lt this)
    omega
  -- Combine \eqref{eq:klm-triangle} and centered Gram bound to get ‖(A ∘ B) - 1‖_k ≤ 20ε (Appendix A)
  have h_tri := klm_triangle_bound hX hY hZ A B hA_nonneg hB_nonneg hε_pos hε_lt hD1 hk hk_even
    hkD_div hA_dens hB_dens hA_reg hB_reg hA_min hB_min
  have h_gram := centered_gram_Lk_bound hX hY hZ A B hA_nonneg hB_nonneg hε_pos hε_lt hD_even
    hD_ge hk hk_even hk_le hA_dens hB_dens hA_reg hB_reg hA_min hB_min
  have h_20 : lpNormSet (X ×ˢ Z) k (fun xz => normMatMul Y A B xz.1 xz.2 - 1) ≤ 20 * ε := by
    linarith
  have h_moment_20 :
      expectSet (X ×ˢ Z) (fun xz => |normMatMul Y A B xz.1 xz.2 - 1| ^ k) ≤ (20 * ε) ^ k :=
    (lpNormSet_le_iff hk1 (by positivity)).mp h_20
  -- Markov's inequality on |A ∘ B - 1|^k (Appendix A)
  unfold IsUniformMatrix
  let P : α × γ → Prop := fun xz =>
    (1 - 80 * ε) * 1 ≤ normMatMul Y A B xz.1 xz.2 ∧
      normMatMul Y A B xz.1 xz.2 ≤ (1 + 80 * ε) * 1
  classical
  let good := (X ×ˢ Z).filter P
  let bad := (X ×ˢ Z).filter (fun xz => ¬ P xz)
  have h_card_split : (good.card : ℝ) + (bad.card : ℝ) = (X.card : ℝ) * (Z.card : ℝ) := by
    have h_nat := Finset.card_filter_add_card_filter_not P (s := X ×ˢ Z)
    rw [Finset.card_product] at h_nat
    exact_mod_cast h_nat
  have h_bad_markov :
      (bad.card : ℝ) * (80 * ε) ^ k ≤
        ∑ xz ∈ X ×ˢ Z, |normMatMul Y A B xz.1 xz.2 - 1| ^ k := by
    calc
      (bad.card : ℝ) * (80 * ε) ^ k
        = ∑ _xz ∈ bad, (80 * ε) ^ k := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ xz ∈ bad, |normMatMul Y A B xz.1 xz.2 - 1| ^ k := by
          refine Finset.sum_le_sum (fun xz hxz => ?_)
          have h_not_P : ¬ P xz := (Finset.mem_filter.mp hxz).2
          have h_abs_gt : 80 * ε ≤ |normMatMul Y A B xz.1 xz.2 - 1| := by
            by_contra! h_lt
            have h_abs := abs_lt.mp h_lt
            exact h_not_P ⟨by linarith, by linarith⟩
          exact pow_le_pow_left₀ (by positivity) h_abs_gt k
      _ ≤ ∑ xz ∈ X ×ˢ Z, |normMatMul Y A B xz.1 xz.2 - 1| ^ k := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => pow_nonneg (abs_nonneg _) k)
  have h_sum_le :
      ∑ xz ∈ X ×ˢ Z, |normMatMul Y A B xz.1 xz.2 - 1| ^ k ≤
        (20 * ε) ^ k * ((X.card : ℝ) * (Z.card : ℝ)) := by
    unfold expectSet at h_moment_20
    rw [Finset.card_product, Nat.cast_mul] at h_moment_20
    have hXZ_pos : 0 < (X.card : ℝ) * (Z.card : ℝ) :=
      mul_pos (Nat.cast_pos.mpr hX.card_pos) (Nat.cast_pos.mpr hZ.card_pos)
    exact (div_le_iff₀ hXZ_pos).mp h_moment_20
  have h_bad_frac :
      (bad.card : ℝ) ≤ (1 / 4 : ℝ) ^ k * ((X.card : ℝ) * (Z.card : ℝ)) := by
    have h80_pos : 0 < (80 * ε) ^ k := pow_pos (by positivity) k
    have h_div : (bad.card : ℝ) ≤
        ((20 * ε) ^ k / (80 * ε) ^ k) * ((X.card : ℝ) * (Z.card : ℝ)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ h80_pos]
      linarith
    have h_ratio : (20 * ε) ^ k / (80 * ε) ^ k = (1 / 4 : ℝ) ^ k := by
      rw [← div_pow]
      congr 1
      have hε_ne : ε ≠ 0 := hε_pos.ne'
      field_simp
      ring
    rwa [h_ratio] at h_div
  have h_pow_decay : (1 / 4 : ℝ) ^ k ≤ (2 : ℝ) ^ (- (ε * (D : ℝ) / 2)) := by
    calc
      (1 / 4 : ℝ) ^ k ≤ (1 / 2 : ℝ) ^ k :=
        pow_le_pow_left₀ (by norm_num) (by norm_num) k
      _ = ((2 : ℝ) ^ k)⁻¹ := by rw [one_div, inv_pow]
      _ = (2 : ℝ) ^ (- (k : ℝ)) := by
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
      _ ≤ (2 : ℝ) ^ (- (ε * (D : ℝ) / 2)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by linarith)
  have h_bad_le :
      (bad.card : ℝ) ≤ (2 : ℝ) ^ (- (ε * (D : ℝ) / 2)) * ((X.card : ℝ) * (Z.card : ℝ)) := by
    calc
      (bad.card : ℝ) ≤ (1 / 4 : ℝ) ^ k * ((X.card : ℝ) * (Z.card : ℝ)) := h_bad_frac
      _ ≤ (2 : ℝ) ^ (- (ε * (D : ℝ) / 2)) * ((X.card : ℝ) * (Z.card : ℝ)) :=
        mul_le_mul_of_nonneg_right h_pow_decay (by positivity)
  change (good.card : ℝ) ≥ (1 - (2 : ℝ) ^ (- (ε * (D : ℝ) / 2))) * ((X.card : ℝ) * (Z.card : ℝ))
  linarith

/-- Scale invariance of `matDensity` under positive scalar division (Appendix A of `paper.tex`). -/
lemma matDensity_div_self {X : Finset α} {Y : Finset β} (_hX : X.Nonempty)
    (A : α → β → ℝ) (hA_pos : 0 < matDensity X Y A) :
    matDensity X Y (fun x y => A x y / matDensity X Y A) = 1 := by
  unfold matDensity rowDeg
  have h1 : (fun x => expectSet Y (fun y => A x y / expectSet X (fun x => expectSet Y (A x)))) =
      (fun x => (expectSet X (fun x => expectSet Y (A x)))⁻¹ * expectSet Y (A x)) := by
    ext x
    simp_rw [div_eq_inv_mul]
    exact expectSet_smul Y _ _
  rw [h1, expectSet_smul]
  exact inv_mul_cancel₀ hA_pos.ne'

/-- Scale invariance of `IsEpsMinDegree` under positive scalar division (Appendix A of `paper.tex`). -/
lemma isEpsMinDegree_div_self {X : Finset α} {Y : Finset β} (hX : X.Nonempty)
    (A : α → β → ℝ) (ε : ℝ) (hA_pos : 0 < matDensity X Y A)
    (hA_min : IsEpsMinDegree X Y A ε) :
    IsEpsMinDegree X Y (fun x y => A x y / matDensity X Y A) ε := by
  intro x hx
  rw [matDensity_div_self hX A hA_pos, mul_one]
  have h_row : rowDeg Y (fun x y => A x y / matDensity X Y A) x =
      (matDensity X Y A)⁻¹ * rowDeg Y A x := by
    unfold rowDeg
    simp_rw [div_eq_inv_mul]
    exact expectSet_smul Y _ _
  rw [h_row]
  have hdeg := hA_min x hx
  have h_mul := mul_le_mul_of_nonneg_left hdeg (inv_nonneg.mpr hA_pos.le)
  rw [← mul_assoc, mul_comm (matDensity X Y A)⁻¹, mul_assoc,
    inv_mul_cancel₀ hA_pos.ne', mul_one] at h_mul
  exact h_mul

/-- Scale invariance of `IsGridRegular` under positive scalar division (Appendix A of `paper.tex`). -/
lemma isGridRegular_div_self {X : Finset α} {Y : Finset β} (hX : X.Nonempty)
    (A : α → β → ℝ) {ε : ℝ} {D : ℕ} (hD : 1 ≤ D)
    (hA_pos : 0 < matDensity X Y A) (hA_reg : IsGridRegular X Y A ε 2 D) :
    IsGridRegular X Y (fun x y => A x y / matDensity X Y A) ε 2 D := by
  unfold IsGridRegular gridNorm at *
  rw [matDensity_div_self hX A hA_pos, mul_one]
  rw [gridNormPow_two_eq_gridNorm2Pow] at *
  have h_scale :
      gridNorm2Pow X Y (fun x y => A x y / matDensity X Y A) D =
        gridNorm2Pow X Y A D / (matDensity X Y A) ^ (2 * D) := by
    unfold gridNorm2Pow
    have h_inner : ∀ x x',
        (expectSet Y (fun y => (A x y / matDensity X Y A) * (A x' y / matDensity X Y A))) ^ D =
          ((matDensity X Y A) ^ (2 * D))⁻¹ *
            (expectSet Y (fun y => A x y * A x' y)) ^ D := by
      intro x x'
      have h_eq : (fun y => (A x y / matDensity X Y A) * (A x' y / matDensity X Y A)) =
          (fun y => ((matDensity X Y A) ^ 2)⁻¹ * (A x y * A x' y)) := by
        ext y; ring
      rw [h_eq, expectSet_smul, mul_pow, inv_pow, ← pow_mul]
    simp_rw [h_inner, expectSet_smul, div_eq_inv_mul]
  rw [h_scale, Real.div_rpow (gridNorm2Pow_nonneg X Y A D) (pow_nonneg hA_pos.le _)]
  have h2D_ne : ((2 * D : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [← Real.rpow_natCast (matDensity X Y A) (2 * D), ← Real.rpow_mul hA_pos.le,
    mul_comm ((2 * D : ℕ) : ℝ), one_div_mul_cancel h2D_ne, Real.rpow_one]
  exact (div_le_iff₀ hA_pos).mpr hA_reg

/-- **Proposition 3.1 (`prop_regular_matrices_uniform_product`, Section 3.2 `\label{prop:regular-product}`
& Appendix A of `paper.tex`)**:
Let $A \in \mathbb{R}_{\ge 0}^{X \times Y}$ and $B \in \mathbb{R}_{\ge 0}^{Y \times Z}$ be non-zero
matrices on finite non-empty sets $X, Y, Z$ (so $\mathbb{E}[A] > 0$ and $\mathbb{E}[B] > 0$), let
$\varepsilon \in (0, 1/80)$, and let $D \ge 4/\varepsilon$ be an even integer. If $A$ and $B^T$ are
both $(\varepsilon, 2, D)$-regular and $\varepsilon$-min-degree, then:
1. $A \circ B$ is $(\mathbb{E}[A]\mathbb{E}[B], 80\varepsilon, 2^{-\varepsilon D / 2})$-uniform on
   $X \times Z$.
2. In particular, if $\varepsilon \le 1/160$, at least a $(1 - 2^{-\varepsilon D / 2})$-fraction of
   all pairs $(x, z) \in X \times Z$ satisfy
   $(A \circ B)(x, z) \ge \frac{1}{2}\mathbb{E}[A]\mathbb{E}[B] > 0$. -/
theorem prop_regular_matrices_uniform_product {X : Finset α} {Y : Finset β} {Z : Finset γ}
    (hX : X.Nonempty) (hY : Y.Nonempty) (hZ : Z.Nonempty)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    (hA_nonneg : ∀ x ∈ X, ∀ y ∈ Y, 0 ≤ A x y)
    (hB_nonneg : ∀ y ∈ Y, ∀ z ∈ Z, 0 ≤ B y z)
    (hA_pos : 0 < matDensity X Y A)
    (hB_pos : 0 < matDensity Y Z B)
    {ε : ℝ} {D : ℕ} (hε_pos : 0 < ε) (hε_lt : ε < 1 / 80)
    (hD_even : Even D) (hD_ge : 4 / ε ≤ (D : ℝ))
    (hA_reg : IsGridRegular X Y A ε 2 D)
    (hB_reg : IsGridRegular Z Y (matTranspose B) ε 2 D)
    (hA_min : IsEpsMinDegree X Y A ε)
    (hB_min : IsEpsMinDegree Z Y (matTranspose B) ε) :
    IsUniformMatrix X Z (normMatMul Y A B)
      (matDensity X Y A * matDensity Y Z B) (80 * ε) ((2 : ℝ) ^ (- (ε * (D : ℝ) / 2))) ∧
    (ε ≤ 1 / 160 →
      0 < (1 / 2 : ℝ) * (matDensity X Y A * matDensity Y Z B) ∧
      (((X ×ˢ Z).filter (fun xz =>
          (1 / 2 : ℝ) * (matDensity X Y A * matDensity Y Z B) ≤
            normMatMul Y A B xz.1 xz.2)).card : ℝ) ≥
        (1 - (2 : ℝ) ^ (- (ε * (D : ℝ) / 2))) * ((X.card : ℝ) * (Z.card : ℝ))) := by
  have hD1 : 1 ≤ D := by
    have : (320 : ℝ) < (D : ℝ) := by
      have := (div_le_iff₀ hε_pos).mp hD_ge
      nlinarith
    have hD320 : 320 ≤ D := by exact_mod_cast (le_of_lt this)
    omega
  have hBT_dens_eq : matDensity Z Y (matTranspose B) = matDensity Y Z B :=
    expectSet_comm Z Y (matTranspose B)
  have hBT_pos : 0 < matDensity Z Y (matTranspose B) := hBT_dens_eq.symm ▸ hB_pos
  -- Normalize A and B by their densities (Appendix A)
  let A' : α → β → ℝ := fun x y => A x y / matDensity X Y A
  let B' : β → γ → ℝ := fun y z => B y z / matDensity Y Z B
  have hBT'_eq : matTranspose B' =
      fun z y => matTranspose B z y / matDensity Z Y (matTranspose B) := by
    ext z y
    unfold B'
    rw [← hBT_dens_eq]
    rfl
  have hA'_nonneg : ∀ x ∈ X, ∀ y ∈ Y, 0 ≤ A' x y :=
    fun x hx y hy => div_nonneg (hA_nonneg x hx y hy) hA_pos.le
  have hB'_nonneg : ∀ z ∈ Z, ∀ y ∈ Y, 0 ≤ matTranspose B' z y :=
    fun z hz y hy => div_nonneg (hB_nonneg y hy z hz) hB_pos.le
  have hA'_dens : matDensity X Y A' = 1 := matDensity_div_self hX A hA_pos
  have hB'_dens : matDensity Z Y (matTranspose B') = 1 := by
    rw [hBT'_eq]
    exact matDensity_div_self hZ (matTranspose B) hBT_pos
  have hA'_reg : IsGridRegular X Y A' ε 2 D := isGridRegular_div_self hX A hD1 hA_pos hA_reg
  have hB'_reg : IsGridRegular Z Y (matTranspose B') ε 2 D := by
    rw [hBT'_eq]
    exact isGridRegular_div_self hZ (matTranspose B) hD1 hBT_pos hB_reg
  have hA'_min : IsEpsMinDegree X Y A' ε := isEpsMinDegree_div_self hX A ε hA_pos hA_min
  have hB'_min : IsEpsMinDegree Z Y (matTranspose B') ε := by
    rw [hBT'_eq]
    exact isEpsMinDegree_div_self hZ (matTranspose B) ε hBT_pos hB_min
  have h_unit := prop_regular_matrices_uniform_product_unit hX hY hZ A' B'
    hA'_nonneg hB'_nonneg hε_pos hε_lt hD_even hD_ge
    hA'_dens hB'_dens hA'_reg hB'_reg hA'_min hB'_min
  -- Rescale normMatMul Y A B = (matDensity X Y A * matDensity Y Z B) * normMatMul Y A' B'
  have h_mul_scale : ∀ x z,
      normMatMul Y A B x z =
        normMatMul Y A' B' x z * (matDensity X Y A * matDensity Y Z B) := by
    intro x z
    unfold normMatMul A' B'
    have h_pt : (fun y => A x y * B y z) =
        (fun y => (matDensity X Y A * matDensity Y Z B) *
          ((A x y / matDensity X Y A) * (B y z / matDensity Y Z B))) := by
      ext y
      have hA_ne : matDensity X Y A ≠ 0 := hA_pos.ne'
      have hB_ne : matDensity Y Z B ≠ 0 := hB_pos.ne'
      field_simp
    rw [h_pt, expectSet_smul, mul_comm]
  have h_unif :
      IsUniformMatrix X Z (normMatMul Y A B)
        (matDensity X Y A * matDensity Y Z B) (80 * ε) ((2 : ℝ) ^ (- (ε * (D : ℝ) / 2))) := by
    unfold IsUniformMatrix at h_unit ⊢
    have h_filter_eq :
        (X ×ˢ Z).filter (fun xz =>
          (1 - 80 * ε) * (matDensity X Y A * matDensity Y Z B) ≤ normMatMul Y A B xz.1 xz.2 ∧
          normMatMul Y A B xz.1 xz.2 ≤ (1 + 80 * ε) * (matDensity X Y A * matDensity Y Z B)) =
        (X ×ˢ Z).filter (fun xz =>
          (1 - 80 * ε) * 1 ≤ normMatMul Y A' B' xz.1 xz.2 ∧
          normMatMul Y A' B' xz.1 xz.2 ≤ (1 + 80 * ε) * 1) := by
      refine Finset.filter_congr (fun xz _ => ?_)
      rw [h_mul_scale xz.1 xz.2, mul_one, mul_one]
      have h_prod_pos : 0 < matDensity X Y A * matDensity Y Z B := mul_pos hA_pos hB_pos
      exact and_congr (mul_le_mul_iff_left₀ h_prod_pos) (mul_le_mul_iff_left₀ h_prod_pos)
    rw [h_filter_eq]
    exact h_unit
  refine ⟨h_unif, fun hε160 => ⟨by positivity, ?_⟩⟩
  unfold IsUniformMatrix at h_unif
  have h_sub :
      (X ×ˢ Z).filter (fun xz =>
        (1 - 80 * ε) * (matDensity X Y A * matDensity Y Z B) ≤ normMatMul Y A B xz.1 xz.2 ∧
        normMatMul Y A B xz.1 xz.2 ≤ (1 + 80 * ε) * (matDensity X Y A * matDensity Y Z B)) ⊆
      (X ×ˢ Z).filter (fun xz =>
        (1 / 2 : ℝ) * (matDensity X Y A * matDensity Y Z B) ≤ normMatMul Y A B xz.1 xz.2) := by
    intro xz hxz
    rw [Finset.mem_filter] at hxz ⊢
    refine ⟨hxz.1, ?_⟩
    have h_half : (1 / 2 : ℝ) * (matDensity X Y A * matDensity Y Z B) ≤
        (1 - 80 * ε) * (matDensity X Y A * matDensity Y Z B) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    exact le_trans h_half hxz.2.1
  have h_card_le :
      (((X ×ˢ Z).filter (fun xz =>
        (1 - 80 * ε) * (matDensity X Y A * matDensity Y Z B) ≤ normMatMul Y A B xz.1 xz.2 ∧
        normMatMul Y A B xz.1 xz.2 ≤ (1 + 80 * ε) * (matDensity X Y A * matDensity Y Z B))).card : ℝ) ≤
      (((X ×ˢ Z).filter (fun xz =>
        (1 / 2 : ℝ) * (matDensity X Y A * matDensity Y Z B) ≤ normMatMul Y A B xz.1 xz.2)).card : ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card h_sub)
  linarith

end Proposition31

end BMMGrid
