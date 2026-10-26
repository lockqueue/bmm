import BMMGrid.CitedResults
import BMMGrid.CostMonadAndLinter

/-!
# Section 3.3 & Appendix B: Two-Stage Composition of Cited Samplers (`BMMGrid/ObliviousSampler.lean`)

This module formalizes the machine-checked two-stage composition (`twoStage_compose`) of the cited
literature sampler hypotheses (`Stage1Sampler` and `Stage2Sampler` from
`BMMGrid/CitedResults.lean`) into the $(\varepsilon_{\text{samp}}, \delta_{\text{samp}})$-oblivious
sequence sampler $\mathcal{T}$ of Section 3.3 & Appendix B (`\eqref{eq:oblivious-sampler}`, §3.3,
and `\eqref{eq:two-stage-sampler}`, §3.3 & §4.1) of `paper.tex`:
1. Universe transport (`transportFam`, `transportFamTracked`, `IsSeqSampler.transport`), two-stage
   index lookup (`lookupSeq`, `lookupSeqTracked`, `composeFamilies`, `composeFamiliesTracked`,
   `composeFamilies_isSeqSampler`), parameter instantiation (`twoStage_compose_general`,
   `approxGridNorm_sampler_inst`), and the oracle constructor `twoStage_compose : TwoStageSamplerOracle`
   used on the headline theorem path (`thm_main_decomp_of_samplers`,
   `thm_main_triangle_detection`, `thm_main_bmm`).
2. Standalone auxiliary results (off the headline theorem path): first-principles Chebyshev
   $k$-tuple samplers over $Y^k$ (`constructChebyshevTupleSampler`, correctness-only reference
   model with $|\Omega| = |Y|^k$) and the small-universe exact-exhaustion inhabitant
   `smallTwoStageSamplerOracle` (`twoStageSamplerOracle_nonempty_of_le`).
-/

namespace BMMGrid

open scoped BigOperators

section ListFilterHelpers

variable {α : Type*}

/-- Monotonicity of `List.filter` length under pointwise implication on the list. -/
lemma list_length_filter_mono {xs : List α} {p q : α → Bool}
    (h : ∀ x ∈ xs, p x = true → q x = true) :
    (xs.filter p).length ≤ (xs.filter q).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    have hx := h x List.mem_cons_self
    cases hp : p x <;> cases hq : q x
    · simp [hp, hq]
      exact ih'
    · simp [hp, hq]
      omega
    · exfalso
      exact Bool.false_ne_true (hq.symm.trans (hx hp))
    · simp [hp, hq]
      omega

end ListFilterHelpers

/-!
## 1. First-Principles Chebyshev $k$-Tuple Concentration Over $Y^k$ (`paper.tex` §3.3)
-/

section ChebyshevTupleSampler

variable {β : Type*}

/-- Linearity of `expectSet` over a finite sum:
$\mathbb{E}_{x \in S}[\sum_{i \in I} F_i(x)] = \sum_{i \in I} \mathbb{E}_{x \in S}[F_i(x)]$. -/
lemma expectSet_sum {α ι : Type*} (S : Finset α) (I : Finset ι) (F : ι → α → ℝ) :
    expectSet S (fun x => ∑ i ∈ I, F i x) = ∑ i ∈ I, expectSet S (fun x => F i x) := by
  unfold expectSet
  rw [Finset.sum_comm, ← Finset.sum_div]

/-- Expectation of a product of independent coordinate functions over $Y^k$:
$\mathbb{E}_{ys \in Y^k}[\prod_{j=1}^k f_j(ys_j)] = \prod_{j=1}^k \mathbb{E}_{y \in Y}[f_j(y)]$. -/
theorem expectSet_piFinset_prod (Y : Finset β) (k : ℕ) (f : Fin k → β → ℝ) :
    expectSet (Fintype.piFinset (fun _ : Fin k => Y)) (fun ys => ∏ j : Fin k, f j (ys j)) =
      ∏ j : Fin k, expectSet Y (fun y => f j y) := by
  unfold expectSet
  rw [Finset.prod_div_distrib, Finset.sum_prod_piFinset, Fintype.card_piFinset_const,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_pow]

/-- Marginal expectation of a single coordinate $ys_i$ over $Y^k$:
$\mathbb{E}_{ys \in Y^k}[h(ys_i)] = \mathbb{E}_{y \in Y}[h(y)]$. -/
lemma expectSet_piFinset_coord {Y : Finset β} (hY : Y.Nonempty) (k : ℕ) (i : Fin k) (h : β → ℝ) :
    expectSet (Fintype.piFinset (fun _ : Fin k => Y)) (fun ys => h (ys i)) =
      expectSet Y h := by
  let f : Fin k → β → ℝ := fun j y => if j = i then h y else 1
  have hprod : (fun ys : Fin k → β => h (ys i)) = (fun ys => ∏ j : Fin k, f j (ys j)) := by
    ext ys
    simp [f]
  rw [hprod, expectSet_piFinset_prod]
  have h1 : ∀ j : Fin k, j ≠ i → expectSet Y (f j) = 1 := by
    intro j hj
    simp only [f, if_neg hj, expectSet_const hY]
  rw [Finset.prod_eq_single i (fun j _ hj => h1 j hj) (fun hi => (hi (Finset.mem_univ i)).elim)]
  simp [f]

/-- Pairwise independence of distinct coordinates $i \ne j$ over $Y^k$:
$\mathbb{E}_{ys \in Y^k}[h_1(ys_i) h_2(ys_j)] = \mathbb{E}_{y \in Y}[h_1(y)] \cdot \mathbb{E}_{y \in Y}[h_2(y)]$. -/
lemma expectSet_piFinset_pair_of_ne {Y : Finset β} (hY : Y.Nonempty) {k : ℕ}
    {i j : Fin k} (hij : i ≠ j) (h₁ h₂ : β → ℝ) :
    expectSet (Fintype.piFinset (fun _ : Fin k => Y)) (fun ys => h₁ (ys i) * h₂ (ys j)) =
      expectSet Y h₁ * expectSet Y h₂ := by
  let f : Fin k → β → ℝ := fun r y => if r = i then h₁ y else if r = j then h₂ y else 1
  have hprod : (fun ys : Fin k → β => h₁ (ys i) * h₂ (ys j)) =
      (fun ys => ∏ r : Fin k, f r (ys r)) := by
    ext ys
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase (Finset.univ.erase i) _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
    have hrest : ∏ r ∈ (Finset.univ.erase i).erase j, f r (ys r) = 1 := by
      apply Finset.prod_eq_one
      intro r hr
      rcases Finset.mem_erase.mp hr with ⟨hrj, hri'⟩
      rcases Finset.mem_erase.mp hri' with ⟨hri, _⟩
      simp [f, hri, hrj]
    rw [hrest, mul_one]
    simp [f, hij.symm]
  rw [hprod, expectSet_piFinset_prod]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase (Finset.univ.erase i) _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
  have hrest : ∏ r ∈ (Finset.univ.erase i).erase j, expectSet Y (fun y => f r y) = 1 := by
    apply Finset.prod_eq_one
    intro r hr
    rcases Finset.mem_erase.mp hr with ⟨hrj, hri'⟩
    rcases Finset.mem_erase.mp hri' with ⟨hri, _⟩
    simp [f, hri, hrj, expectSet_const hY]
  rw [hrest, mul_one]
  simp [f, hij.symm]

/-- Finite Markov inequality for `expectSet`: for any non-negative function `w : α → ℝ` and threshold
`t > 0`, $|\{x \in S : w(x) \ge t\}| \cdot t \le \mathbb{E}_{x \in S}[w(x)] \cdot |S|$. -/
theorem filter_card_mul_le_expectSet {α : Type*} (S : Finset α) (w : α → ℝ) (t : ℝ)
    (hw : ∀ x ∈ S, 0 ≤ w x) :
    (((S.filter (fun x => t ≤ w x)).card : ℝ) * t) ≤ expectSet S w * (S.card : ℝ) := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp [expectSet]
  · unfold expectSet
    have hcard : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hS.card_pos.ne'
    rw [div_mul_cancel₀ _ hcard]
    calc
      ((S.filter (fun x => t ≤ w x)).card : ℝ) * t
        = ∑ _x ∈ S.filter (fun x => t ≤ w x), t := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ S.filter (fun x => t ≤ w x), w x := by
            apply Finset.sum_le_sum
            intro x hx
            exact (Finset.mem_filter.mp hx).2
      _ ≤ ∑ x ∈ S, w x := by
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ S)
              (fun x hx _ => hw x hx)

/-- Empirical average $\frac{1}{k}\sum_{i=1}^k g(ys_i)$ of a $k$-tuple $ys \in Y^k$. -/
noncomputable def tupleSampleAvg (k : ℕ) (g : β → ℝ) (ys : Fin k → β) : ℝ :=
  expectSet Finset.univ (fun i : Fin k => g (ys i))

/-- Second-moment (variance) identity for `tupleSampleAvg` over $Y^k$:
$\mathbb{E}_{ys \in Y^k}[(\bar{g}(ys) - \mu)^2] = \frac{1}{k} \mathbb{E}_{y \in Y}[(g(y) - \mu)^2]$
(`paper.tex` Section 3.3 & Appendix B). -/
theorem expectSet_tupleSampleAvg_sub_sq_eq {Y : Finset β} (hY : Y.Nonempty)
    {k : ℕ} (hk : 0 < k) (g : β → ℝ) :
    expectSet (Fintype.piFinset (fun _ : Fin k => Y))
        (fun ys => (tupleSampleAvg k g ys - expectSet Y g) ^ 2) =
      expectSet Y (fun y => (g y - expectSet Y g) ^ 2) / (k : ℝ) := by
  let μ := expectSet Y g
  let h : β → ℝ := fun y => g y - μ
  have hh_mean : expectSet Y h = 0 := by
    change expectSet Y (fun y => g y - μ) = 0
    rw [expectSet_sub, expectSet_const hY, sub_self]
  have huniv_ne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  have hdiff : ∀ ys : Fin k → β,
      (tupleSampleAvg k g ys - μ) ^ 2 =
        ((1 / (k : ℝ)) ^ 2) * (∑ i : Fin k, ∑ j : Fin k, h (ys i) * h (ys j)) := by
    intro ys
    have h1 : tupleSampleAvg k g ys - μ = expectSet Finset.univ (fun i : Fin k => h (ys i)) := by
      unfold tupleSampleAvg h
      rw [expectSet_sub, expectSet_const huniv_ne]
    rw [h1]
    unfold expectSet
    rw [Finset.card_univ, Fintype.card_fin, div_eq_inv_mul, mul_pow, inv_eq_one_div, sq (∑ i : Fin k, h (ys i)),
      Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
  have hfun : (fun ys : Fin k → β => (tupleSampleAvg k g ys - expectSet Y g) ^ 2) =
      (fun ys : Fin k → β => ((1 / (k : ℝ)) ^ 2) * (∑ i : Fin k, ∑ j : Fin k, h (ys i) * h (ys j))) :=
    funext hdiff
  rw [hfun, expectSet_smul, expectSet_sum]
  have hinner : ∀ i : Fin k,
      expectSet (Fintype.piFinset (fun _ : Fin k => Y))
          (fun ys => ∑ j : Fin k, h (ys i) * h (ys j)) =
        expectSet Y (fun y => (h y) ^ 2) := by
    intro i
    rw [expectSet_sum]
    have hzero : ∀ j : Fin k, j ≠ i →
        expectSet (Fintype.piFinset (fun _ : Fin k => Y)) (fun ys => h (ys i) * h (ys j)) = 0 := by
      intro j hj
      rw [expectSet_piFinset_pair_of_ne hY (Ne.symm hj), hh_mean, mul_zero]
    rw [Finset.sum_eq_single i (fun j _ hj => hzero j hj) (fun hi => (hi (Finset.mem_univ i)).elim)]
    rw [expectSet_piFinset_coord hY k i (fun y => h y * h y)]
    congr 1
    ext y
    ring
  rw [Finset.sum_congr rfl (fun i _ => hinner i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  field_simp [hkR]
  rfl

/-- Variance bound $\mathbb{E}_{ys \in Y^k}[(\bar{g}(ys) - \mu)^2] \le 1 / k$ for any
$g : \beta \to [0, 1]$. -/
theorem expectSet_tupleSampleAvg_sub_sq_le {Y : Finset β} (hY : Y.Nonempty)
    {k : ℕ} (hk : 0 < k) (g : β → ℝ) (hg : ∀ y ∈ Y, 0 ≤ g y ∧ g y ≤ 1) :
    expectSet (Fintype.piFinset (fun _ : Fin k => Y))
        (fun ys => (tupleSampleAvg k g ys - expectSet Y g) ^ 2) ≤ 1 / (k : ℝ) := by
  rw [expectSet_tupleSampleAvg_sub_sq_eq hY hk g]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg k)
  apply expectSet_le_of_le hY
  intro y hy
  have hμ0 : 0 ≤ expectSet Y g := expectSet_nonneg (fun z hz => (hg z hz).1)
  have hμ1 : expectSet Y g ≤ 1 := expectSet_le_of_le hY (fun z hz => (hg z hz).2)
  have hy0 : 0 ≤ g y := (hg y hy).1
  have hy1 : g y ≤ 1 := (hg y hy).2
  nlinarith

/-- **First-Principles Chebyshev Concentration for $k$-Tuple Samplers (`\eqref{eq:oblivious-sampler}`)**:
For any $g : \beta \to [0, 1]$ and $\varepsilon_{\text{samp}} > 0$, the number of $k$-tuples
$ys \in Y^k$ with $|\bar{g}(ys) - \mathbb{E}_{y \in Y}[g(y)]| \ge \varepsilon_{\text{samp}}$ is at
most $\frac{1}{k \varepsilon_{\text{samp}}^2} |Y^k|$. -/
theorem chebyshev_tuple_sampler_bad_card_le {Y : Finset β} (hY : Y.Nonempty)
    {k : ℕ} (hk : 0 < k) (g : β → ℝ) (hg : ∀ y ∈ Y, 0 ≤ g y ∧ g y ≤ 1)
    {ε_samp : ℝ} (hε : 0 ≤ ε_samp) :
    (((Fintype.piFinset (fun _ : Fin k => Y)).filter
        (fun ys => ε_samp ≤ |tupleSampleAvg k g ys - expectSet Y g|)).card : ℝ) *
      ((k : ℝ) * ε_samp ^ 2) ≤
      ((Fintype.piFinset (fun _ : Fin k => Y)).card : ℝ) := by
  let Ω := Fintype.piFinset (fun _ : Fin k => Y)
  let w : (Fin k → β) → ℝ := fun ys => (tupleSampleAvg k g ys - expectSet Y g) ^ 2
  have hsub :
      Ω.filter (fun ys => ε_samp ≤ |tupleSampleAvg k g ys - expectSet Y g|) ⊆
        Ω.filter (fun ys => ε_samp ^ 2 ≤ w ys) := by
    intro ys hys
    rcases Finset.mem_filter.mp hys with ⟨hysΩ, hle⟩
    refine Finset.mem_filter.mpr ⟨hysΩ, ?_⟩
    unfold w
    rw [← sq_abs (tupleSampleAvg k g ys - expectSet Y g)]
    exact pow_le_pow_left₀ hε hle 2
  have hcard_le :
      ((Ω.filter (fun ys => ε_samp ≤ |tupleSampleAvg k g ys - expectSet Y g|)).card : ℝ) ≤
        ((Ω.filter (fun ys => ε_samp ^ 2 ≤ w ys)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hmarkov := filter_card_mul_le_expectSet Ω w (ε_samp ^ 2) (fun _ _ => sq_nonneg _)
  have hvar := expectSet_tupleSampleAvg_sub_sq_le hY hk g hg
  have hkR : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hΩ_nonneg : (0 : ℝ) ≤ (Ω.card : ℝ) := Nat.cast_nonneg _
  have hε2_nonneg : 0 ≤ ε_samp ^ 2 := sq_nonneg ε_samp
  have h1 :
      ((Ω.filter (fun ys => ε_samp ≤ |tupleSampleAvg k g ys - expectSet Y g|)).card : ℝ) * (ε_samp ^ 2) ≤
        (1 / (k : ℝ)) * (Ω.card : ℝ) := by
    calc
      ((Ω.filter (fun ys => ε_samp ≤ |tupleSampleAvg k g ys - expectSet Y g|)).card : ℝ) * (ε_samp ^ 2)
        ≤ ((Ω.filter (fun ys => ε_samp ^ 2 ≤ w ys)).card : ℝ) * (ε_samp ^ 2) :=
          mul_le_mul_of_nonneg_right hcard_le hε2_nonneg
      _ ≤ expectSet Ω w * (Ω.card : ℝ) := hmarkov
      _ ≤ (1 / (k : ℝ)) * (Ω.card : ℝ) := mul_le_mul_of_nonneg_right hvar hΩ_nonneg
  have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hkR)
  have hk_ne : (k : ℝ) ≠ 0 := hkR.ne'
  calc
    ((Ω.filter (fun ys => ε_samp ≤ |tupleSampleAvg k g ys - expectSet Y g|)).card : ℝ) *
        ((k : ℝ) * ε_samp ^ 2)
      = (k : ℝ) * (((Ω.filter (fun ys => ε_samp ≤ |tupleSampleAvg k g ys - expectSet Y g|)).card : ℝ) *
          (ε_samp ^ 2)) := by ring
    _ ≤ (k : ℝ) * ((1 / (k : ℝ)) * (Ω.card : ℝ)) := h2
    _ = (Ω.card : ℝ) := by field_simp [hk_ne]

/-- Sample size $k = (\text{invEps} + 1)^2 (\text{invDelta} + 1)$ for the first-principles
Chebyshev $k$-tuple oblivious sampler over $Y^k$ (`paper.tex` Section 3.3 & Appendix B). -/
def chebyshevSampleSize (invEps invDelta : ℕ) : ℕ :=
  (invEps + 1) ^ 2 * (invDelta + 1)

lemma chebyshevSampleSize_pos (invEps invDelta : ℕ) :
    0 < chebyshevSampleSize invEps invDelta := by
  unfold chebyshevSampleSize
  positivity

lemma one_le_chebyshevSampleSize (invEps invDelta : ℕ) :
    1 ≤ chebyshevSampleSize invEps invDelta :=
  Nat.succ_le_of_lt (chebyshevSampleSize_pos invEps invDelta)

/-- **Tuple Oblivious Sampler Predicate (`\eqref{eq:oblivious-sampler}`, `paper.tex` §3.3)**:
A finite collection $\Omega \subseteq Y^k$ of $k$-tuples in $Y$ (with $k > 0$) is an
$(\varepsilon_{\text{samp}}, \delta_{\text{samp}})$-tuple oblivious sampler of $Y$ if every tuple
in $\Omega$ takes values in $Y$ and, for every function $g : \beta \to [0, 1]$, at most a
$\delta_{\text{samp}}$-fraction of $ys \in \Omega$ have empirical average
$\bar{g}(ys) = \frac{1}{k}\sum_{i=1}^k g(ys_i)$ deviating from $\mathbb{E}_{y \in Y}[g(y)]$ by at
least $\varepsilon_{\text{samp}}$ (when $\Omega = \emptyset$, e.g. for $Y = \emptyset$, the
cardinality inequality holds vacuously with $0 \le 0$; non-empty sequence-family samplers used by
the algorithms are governed by `IsSeqSampler`). -/
def IsTupleObliviousSampler (Y : Finset β) (k : ℕ) (Ω : Finset (Fin k → β))
    (ε_samp δ_samp : ℝ) : Prop :=
  0 < k ∧
  (∀ ys ∈ Ω, ∀ i : Fin k, ys i ∈ Y) ∧
  ∀ g : β → ℝ, (∀ y ∈ Y, 0 ≤ g y ∧ g y ≤ 1) →
    ((Ω.filter (fun ys => ε_samp ≤ |tupleSampleAvg k g ys - expectSet Y g|)).card : ℝ) ≤
      δ_samp * (Ω.card : ℝ)

/-- Unconditional Chebyshev $k$-tuple oblivious sampler $\Omega = Y^k$ with sample size
$k = \text{chebyshevSampleSize}(\text{invEps}, \text{invDelta}) = (\text{invEps} + 1)^2 (\text{invDelta} + 1)$
completely independent of $|Y|$ (`paper.tex` Section 3.3 & Appendix B).
*Note*: This is a correctness-only reference model over the full product space $\Omega = Y^k$ of
cardinality $|\Omega| = |Y|^k$, with no running-time clause (`CostM` complexity is
proved for the polynomial-seed `TwoStageSamplerOracle` path). -/
def constructChebyshevTupleSampler (Y : Finset β) (invEps invDelta : ℕ) :
    Finset (Fin (chebyshevSampleSize invEps invDelta) → β) :=
  Fintype.piFinset (fun _ => Y)

/-- Every sample tuple in `constructChebyshevTupleSampler Y invEps invDelta` has coordinate count
$k = (\text{invEps} + 1)^2 (\text{invDelta} + 1) = \operatorname{poly}(\varepsilon_{\text{samp}}^{-1}, \delta_{\text{samp}}^{-1})$,
unconditionally and independent of $|Y|$. -/
theorem constructChebyshevTupleSampler_sample_size (invEps invDelta : ℕ) :
    Fintype.card (Fin (chebyshevSampleSize invEps invDelta)) =
      (invEps + 1) ^ 2 * (invDelta + 1) := by
  rw [Fintype.card_fin, chebyshevSampleSize]

/-- Family cardinality of `constructChebyshevTupleSampler Y invEps invDelta`:
$|\Omega| = |Y|^{(\text{invEps} + 1)^2 (\text{invDelta} + 1)}$. -/
theorem constructChebyshevTupleSampler_card (Y : Finset β) (invEps invDelta : ℕ) :
    (constructChebyshevTupleSampler Y invEps invDelta).card =
      Y.card ^ chebyshevSampleSize invEps invDelta := by
  unfold constructChebyshevTupleSampler
  rw [Fintype.card_piFinset_const]

/-- Every sample tuple `ys ∈ constructChebyshevTupleSampler Y invEps invDelta` has domain
`Fin (chebyshevSampleSize invEps invDelta)` of uniform size
`chebyshevSampleSize invEps invDelta = (invEps + 1) ^ 2 * (invDelta + 1)` completely independent
of `Y.card`, and maps every coordinate into `Y`. -/
theorem constructChebyshevTupleSampler_uniform_sample_size (Y : Finset β)
    (invEps invDelta : ℕ) :
    Fintype.card (Fin (chebyshevSampleSize invEps invDelta)) =
      chebyshevSampleSize invEps invDelta ∧
    chebyshevSampleSize invEps invDelta = (invEps + 1) ^ 2 * (invDelta + 1) ∧
    ∀ ys ∈ constructChebyshevTupleSampler Y invEps invDelta,
      ∀ i : Fin (chebyshevSampleSize invEps invDelta), ys i ∈ Y := by
  refine ⟨Fintype.card_fin _, rfl, ?_⟩
  intro ys hys i
  exact Fintype.mem_piFinset.mp hys i

/-- **Unconditional Chebyshev $k$-Tuple Oblivious Sampler Theorem (`\eqref{eq:oblivious-sampler}`)**:
For any finite set `Y : Finset β` (with **zero** `Y.card ≤ ...` hypothesis), any
`invEps invDelta : ℕ`, and any `ε_samp δ_samp : ℝ` with
$\frac{1}{\text{invEps} + 1} \le \varepsilon_{\text{samp}}$ and
$\frac{1}{\text{invDelta} + 1} \le \delta_{\text{samp}}$,
`constructChebyshevTupleSampler Y invEps invDelta` is an
$(\varepsilon_{\text{samp}}, \delta_{\text{samp}})$-tuple oblivious sampler of `Y` of sample size
$k = (\text{invEps} + 1)^2 (\text{invDelta} + 1)$ (correctness-only reference model with
$|\Omega| = |Y|^k$; no running-time clause). -/
theorem isTupleObliviousSampler_constructChebyshevTupleSampler (Y : Finset β)
    (invEps invDelta : ℕ) {ε_samp δ_samp : ℝ}
    (hε : (1 : ℝ) / ((invEps : ℝ) + 1) ≤ ε_samp)
    (hδ : (1 : ℝ) / ((invDelta : ℝ) + 1) ≤ δ_samp) :
    IsTupleObliviousSampler Y (chebyshevSampleSize invEps invDelta)
      (constructChebyshevTupleSampler Y invEps invDelta) ε_samp δ_samp := by
  set k := chebyshevSampleSize invEps invDelta
  have hk : 0 < k := chebyshevSampleSize_pos invEps invDelta
  refine ⟨hk, ?_, ?_⟩
  · intro ys hys i
    exact Fintype.mem_piFinset.mp hys i
  · intro g hg
    rcases Y.eq_empty_or_nonempty with rfl | hY
    · have hΩ_empty : constructChebyshevTupleSampler (∅ : Finset β) invEps invDelta = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro ys hys
        have hmem := Fintype.mem_piFinset.mp hys ⟨0, hk⟩
        exact Finset.notMem_empty _ hmem
      rw [hΩ_empty]
      simp
    · have hε_pos : (0 : ℝ) < (invEps : ℝ) + 1 := by positivity
      have hδ_pos : (0 : ℝ) < (invDelta : ℝ) + 1 := by positivity
      have hε0_pos : (0 : ℝ) < (1 : ℝ) / ((invEps : ℝ) + 1) := div_pos one_pos hε_pos
      have hε_nonneg : 0 ≤ ε_samp := le_trans (le_of_lt hε0_pos) hε
      have hcheb := chebyshev_tuple_sampler_bad_card_le hY hk g hg hε_nonneg
      set Ω := constructChebyshevTupleSampler Y invEps invDelta
      set bad := (Ω.filter (fun ys => ε_samp ≤ |tupleSampleAvg k g ys - expectSet Y g|)).card
      have hbad_nonneg : (0 : ℝ) ≤ (bad : ℝ) := Nat.cast_nonneg _
      have hΩ_nonneg : (0 : ℝ) ≤ (Ω.card : ℝ) := Nat.cast_nonneg _
      have hsq : ((1 : ℝ) / ((invEps : ℝ) + 1)) ^ 2 ≤ ε_samp ^ 2 :=
        pow_le_pow_left₀ (le_of_lt hε0_pos) hε 2
      have hk_eq : (k : ℝ) = ((invEps : ℝ) + 1) ^ 2 * ((invDelta : ℝ) + 1) := by
        dsimp [k, chebyshevSampleSize]
        push_cast
        rfl
      have hk_mul : (invDelta : ℝ) + 1 ≤ (k : ℝ) * ε_samp ^ 2 := by
        have h1 : (invDelta : ℝ) + 1 = (k : ℝ) * ((1 : ℝ) / ((invEps : ℝ) + 1)) ^ 2 := by
          rw [hk_eq]
          have hne : (invEps : ℝ) + 1 ≠ 0 := hε_pos.ne'
          field_simp [hne]
        rw [h1]
        exact mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg k)
      have hbad_mul : (bad : ℝ) * ((invDelta : ℝ) + 1) ≤ (Ω.card : ℝ) := by
        calc
          (bad : ℝ) * ((invDelta : ℝ) + 1)
            ≤ (bad : ℝ) * ((k : ℝ) * ε_samp ^ 2) :=
              mul_le_mul_of_nonneg_left hk_mul hbad_nonneg
          _ ≤ (Ω.card : ℝ) := hcheb
      have hbad_div : (bad : ℝ) ≤ ((1 : ℝ) / ((invDelta : ℝ) + 1)) * (Ω.card : ℝ) := by
        rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hδ_pos]
        exact hbad_mul
      exact le_trans hbad_div (mul_le_mul_of_nonneg_right hδ hΩ_nonneg)

end ChebyshevTupleSampler

/-!
## 2. Machine-Checked Two-Stage Sequence Sampler Composition (`twoStage_compose`) and
`TwoStageSamplerOracle` (`paper.tex` Section 3.3 & Appendix B, `\eqref{eq:oblivious-sampler}` &
`\eqref{eq:two-stage-sampler}`, §3.3 & §4.1)
-/

section ComputableSampler

variable {β : Type*}

/-- Sum of `L.map g` over a list `L` equals the `Finset.univ` sum over `Fin L.length`. -/
lemma list_map_sum_eq_fin_sum {γ : Type*} (L : List γ) (g : γ → ℝ) :
    (L.map g).sum = ∑ i : Fin L.length, g (L.get i) := by
  induction L with
  | nil => simp
  | cons a tl ih =>
    rw [List.map_cons, List.sum_cons, ih]
    exact (Fin.sum_univ_succ (fun i : Fin (tl.length + 1) => g ((a :: tl).get i))).symm

/-- For any `Y : Finset β` and `g : β → ℝ`, `(Y.toList.map g).sum = ∑ y ∈ Y, g y`. -/
lemma finset_toList_map_sum_eq (Y : Finset β) (g : β → ℝ) :
    (Y.toList.map g).sum = ∑ y ∈ Y, g y := by
  rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
  rfl

/-- Empirical sequence average over `Y.toList` equals the set average `expectSet Y g`. -/
lemma expectSeq_toList_eq_expectSet (Y : Finset β) (g : β → ℝ) :
    expectSeq Y.toList g = expectSet Y g := by
  unfold expectSeq expectSet
  rw [finset_toList_map_sum_eq, Finset.length_toList]

/-- Monotonicity of `IsSeqSampler` in both error parameters `ε` and `δ`. -/
theorem IsSeqSampler.mono {U : Finset β} {fam : List (List β)} {ε₁ ε₂ δ₁ δ₂ : ℝ}
    (hS : IsSeqSampler U fam ε₁ δ₁) (hε : ε₁ ≤ ε₂) (hδ : δ₁ ≤ δ₂) :
    IsSeqSampler U fam ε₂ δ₂ := by
  classical
  refine ⟨hS.1, hS.2.1, fun g hg => ?_⟩
  have hsub :
      (fam.filter (fun T => decide (|expectSeq T g - expectSet U g| > ε₂))).length ≤
        (fam.filter (fun T => decide (|expectSeq T g - expectSet U g| > ε₁))).length := by
    apply list_length_filter_mono
    intro T _ hT
    have hgt : |expectSeq T g - expectSet U g| > ε₂ := of_decide_eq_true hT
    exact decide_eq_true (lt_of_le_of_lt hε hgt)
  have hcast :
      (((fam.filter (fun T => decide (|expectSeq T g - expectSet U g| > ε₂))).length : ℕ) : ℝ) ≤
        (((fam.filter (fun T => decide (|expectSeq T g - expectSet U g| > ε₁))).length : ℕ) : ℝ) := by
    exact_mod_cast hsub
  have h1 := hS.2.2 g hg
  have hlen_nonneg : (0 : ℝ) ≤ (fam.length : ℝ) := Nat.cast_nonneg _
  exact hcast.trans (h1.trans (mul_le_mul_of_nonneg_right hδ hlen_nonneg))

/-- Zero-error sequence sampler guarantee for the singleton family `[Y.toList]`
(`expectSeq Y.toList g = expectSet Y g`). -/
theorem isSeqSampler_singleton (Y : Finset β) {ε_samp δ_samp : ℝ}
    (hε : 0 ≤ ε_samp) (hδ : 0 ≤ δ_samp) :
    IsSeqSampler Y [Y.toList] ε_samp δ_samp := by
  classical
  refine ⟨List.cons_ne_nil _ [], ?_, ?_⟩
  · intro T hT
    simp only [List.mem_singleton] at hT
    subst hT
    refine ⟨fun y hy => Finset.mem_toList.mp hy, fun hne ht => ?_⟩
    have hlen := congrArg List.length ht
    rw [Finset.length_toList, List.length_nil] at hlen
    exact hne.card_pos.ne' hlen
  · intro g _hg
    have h_not_lt : ¬(|expectSeq Y.toList g - expectSet Y g| > ε_samp) := by
      rw [expectSeq_toList_eq_expectSet, sub_self, abs_zero]
      exact not_lt.mpr hε
    have hfilt :
        ([Y.toList].filter (fun T => decide (|expectSeq T g - expectSet Y g| > ε_samp))) = [] := by
      rw [List.filter_cons_of_neg]
      · rfl
      · simpa using h_not_lt
    rw [hfilt]
    simpa using hδ

/-- Zero-error sequence sampler guarantee for `[[]]` on the empty universe `∅ : Finset β`. -/
theorem isSeqSampler_empty {ε_samp δ_samp : ℝ} (hε : 0 ≤ ε_samp) (hδ : 0 ≤ δ_samp) :
    IsSeqSampler (∅ : Finset β) [[]] ε_samp δ_samp := by
  classical
  refine ⟨List.cons_ne_nil _ [], ?_, ?_⟩
  · intro T hT
    simp only [List.mem_singleton] at hT
    subst hT
    refine ⟨?_, ?_⟩
    · intro _ hy
      cases hy
    · intro hne
      exact False.elim (Finset.not_nonempty_empty hne)
  · intro g _hg
    have h0 : expectSeq ([] : List β) g = 0 := by simp [expectSeq]
    have h1 : expectSet (∅ : Finset β) g = 0 := by simp [expectSet]
    have h_not_lt : ¬(|expectSeq ([] : List β) g - expectSet (∅ : Finset β) g| > ε_samp) := by
      rw [h0, h1, sub_self, abs_zero]
      exact not_lt.mpr hε
    have hfilt :
        ([([] : List β)].filter
          (fun T => decide (|expectSeq T g - expectSet (∅ : Finset β) g| > ε_samp))) = [] := by
      rw [List.filter_cons_of_neg]
      · rfl
      · simpa using h_not_lt
    rw [hfilt]
    simpa using hδ

/-- Canonical bijection `Fin Y.card → Y` indexing `Y : Finset β` via `Y.toList`. -/
noncomputable def indexFinset (Y : Finset β) (i : Fin Y.card) : β :=
  Y.toList.get (Fin.cast (Finset.length_toList Y).symm i)

lemma indexFinset_mem (Y : Finset β) (i : Fin Y.card) : indexFinset Y i ∈ Y := by
  unfold indexFinset
  exact Finset.mem_toList.mp (List.get_mem Y.toList _)

lemma expectSet_univ_indexFinset (Y : Finset β) (g : β → ℝ) :
    expectSet (Finset.univ : Finset (Fin Y.card)) (fun i => g (indexFinset Y i)) =
      expectSet Y g := by
  unfold expectSet indexFinset
  simp only [Finset.card_univ, Fintype.card_fin]
  congr 1
  have h1 : (∑ x ∈ Y, g x) = (Y.toList.map g).sum := (finset_toList_map_sum_eq Y g).symm
  rw [h1, list_map_sum_eq_fin_sum]
  let e : Fin Y.card ≃ Fin Y.toList.length := Fin.castOrderIso (Finset.length_toList Y).symm |>.toEquiv
  exact Equiv.sum_comp e (fun j => g (Y.toList.get j))

lemma expectSeq_map_eq {α₁ α₂ : Type*} (T : List α₁) (f : α₁ → α₂) (g : α₂ → ℝ) :
    expectSeq (T.map f) g = expectSeq T (fun x => g (f x)) := by
  unfold expectSeq
  rw [List.map_map, List.length_map]
  rfl

/-- Transport a family of index sequences `List (List (Fin Y.card))` to `List (List β)` in `Y`. -/
noncomputable def transportFam (Y : Finset β) (fam_idx : List (List (Fin Y.card))) :
    List (List β) :=
  fam_idx.map (List.map (indexFinset Y))

@[simp]
lemma transportFam_length (Y : Finset β) (fam_idx : List (List (Fin Y.card))) :
    (transportFam Y fam_idx).length = fam_idx.length :=
  List.length_map _

/-- Cost-tracked transport of a family of index sequences `List (List (Fin Y.card))` to
`List (List β)` in `Y`, mapping every sequence and element via `mapListTracked`. -/
noncomputable def transportFamTracked (Y : Finset β) (fam_idx : List (List (Fin Y.card))) :
    CostM (List (List β)) :=
  mapListTracked (fun T_idx => mapListTracked (fun i => retTracked (indexFinset Y i)) T_idx) fam_idx

@[simp]
lemma transportFamTracked_fst (Y : Finset β) (fam_idx : List (List (Fin Y.card))) :
    (transportFamTracked Y fam_idx).1 = transportFam Y fam_idx := by
  simp [transportFamTracked, transportFam]

lemma transportFamTracked_snd_le (Y : Finset β) (fam_idx : List (List (Fin Y.card)))
    (M : ℕ) (hM : ∀ T_idx ∈ fam_idx, T_idx.length ≤ M) :
    (transportFamTracked Y fam_idx).2 ≤ fam_idx.length * (2 * M + 2) + 1 := by
  unfold transportFamTracked
  refine mapListTracked_snd_le_const
    (fun T_idx => mapListTracked (fun i => retTracked (indexFinset Y i)) T_idx)
    (2 * M + 1) fam_idx ?_
  intro T_idx hT
  dsimp only
  have h1 := mapListTracked_snd_le_const (fun i => retTracked (indexFinset Y i)) 1 T_idx
    (fun _ _ => le_rfl)
  have hlen := hM T_idx hT
  omega

/-- **`IsSeqSampler.transport` (`paper.tex` Section 3.3 & Appendix B, `\eqref{eq:oblivious-sampler}`,
§3.3)**:
Transporting an $(\varepsilon, \delta)$-sequence sampler on `Fin Y.card` along `indexFinset Y`
yields an $(\varepsilon, \delta)$-sequence sampler on `Y : Finset β` with identical family size
and identical per-sequence lengths. -/
theorem IsSeqSampler.transport (Y : Finset β) {fam_idx : List (List (Fin Y.card))} {ε δ : ℝ}
    (hS : IsSeqSampler (Finset.univ : Finset (Fin Y.card)) fam_idx ε δ) :
    IsSeqSampler Y (transportFam Y fam_idx) ε δ := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro hemp
    exact hS.1 (List.map_eq_nil_iff.mp hemp)
  · intro T hT
    rcases List.mem_map.mp hT with ⟨T_idx, hT_idx, rfl⟩
    refine ⟨?_, ?_⟩
    · intro y hy
      rcases List.mem_map.mp hy with ⟨i, _, rfl⟩
      exact indexFinset_mem Y i
    · intro hY_ne
      rcases hY_ne with ⟨y₀, hy₀⟩
      have hcard_pos : 0 < Y.card := Finset.card_pos.mpr ⟨y₀, hy₀⟩
      have huniv_ne : (Finset.univ : Finset (Fin Y.card)).Nonempty :=
        ⟨⟨0, hcard_pos⟩, Finset.mem_univ _⟩
      have hT_ne := (hS.2.1 T_idx hT_idx).2 huniv_ne
      intro hmap_nil
      exact hT_ne (List.map_eq_nil_iff.mp hmap_nil)
  · intro g hg
    have hg_idx : ∀ i ∈ (Finset.univ : Finset (Fin Y.card)),
        0 ≤ g (indexFinset Y i) ∧ g (indexFinset Y i) ≤ 1 :=
      fun i _ => hg (indexFinset Y i) (indexFinset_mem Y i)
    have hbad := hS.2.2 (fun i => g (indexFinset Y i)) hg_idx
    unfold transportFam
    rw [List.filter_map, List.length_map, List.length_map]
    have hpred :
        ((fun T : List β => decide (|expectSeq T g - expectSet Y g| > ε)) ∘
          List.map (indexFinset Y)) =
        (fun T_idx : List (Fin Y.card) =>
          decide (|expectSeq T_idx (fun i => g (indexFinset Y i)) -
            expectSet (Finset.univ : Finset (Fin Y.card)) (fun i => g (indexFinset Y i))| > ε)) := by
      ext T_idx
      simp only [Function.comp_apply, expectSeq_map_eq, expectSet_univ_indexFinset]
    rw [hpred]
    exact hbad

/-- Stage-1 / Stage-2 sequence lookup: given a fallback element `y₀ : β`, a Stage-1 sequence
`T₁ : List β` of length `M`, and a Stage-2 index sequence `I₂ : List (Fin M)`, returns the
sub-sampled sequence `I₂.map (fun j => T₁.getD j.val y₀) : List β` of length `I₂.length`
(`paper.tex` Section 3.3 & Appendix B). -/
def lookupSeq {M : ℕ} (y₀ : β) (T₁ : List β) (I₂ : List (Fin M)) : List β :=
  I₂.map (fun j => T₁.getD j.val y₀)

@[simp]
lemma lookupSeq_length {M : ℕ} (y₀ : β) (T₁ : List β) (I₂ : List (Fin M)) :
    (lookupSeq y₀ T₁ I₂).length = I₂.length :=
  List.length_map _

/-- Cost-tracked Stage-1 / Stage-2 sequence lookup in `CostM`, mapping `I₂` via `mapListTracked`. -/
def lookupSeqTracked {M : ℕ} (y₀ : β) (T₁ : List β) (I₂ : List (Fin M)) : CostM (List β) :=
  mapListTracked (fun j => retTracked (T₁.getD j.val y₀)) I₂

@[simp]
lemma lookupSeqTracked_fst {M : ℕ} (y₀ : β) (T₁ : List β) (I₂ : List (Fin M)) :
    (lookupSeqTracked y₀ T₁ I₂).1 = lookupSeq y₀ T₁ I₂ := by
  simp [lookupSeqTracked, lookupSeq]

lemma lookupSeqTracked_snd_le {M : ℕ} (y₀ : β) (T₁ : List β) (I₂ : List (Fin M)) :
    (lookupSeqTracked y₀ T₁ I₂).2 ≤ 2 * I₂.length + 1 := by
  unfold lookupSeqTracked
  have h := mapListTracked_snd_le_const (fun j : Fin M => retTracked (T₁.getD j.val y₀)) 1 I₂
    (fun _ _ => le_rfl)
  omega

lemma lookupSeq_mem {M : ℕ} {y₀ : β} {Y : Finset β} (hy₀ : y₀ ∈ Y)
    {T₁ : List β} (hT₁ : ∀ y ∈ T₁, y ∈ Y) (I₂ : List (Fin M)) :
    ∀ y ∈ lookupSeq y₀ T₁ I₂, y ∈ Y := by
  intro y hy
  rcases List.mem_map.mp hy with ⟨j, _, rfl⟩
  unfold List.getD
  cases hget : T₁[j.val]? with
  | none => exact hy₀
  | some z => exact hT₁ z (List.mem_of_getElem? hget)

lemma expectSeq_lookupSeq {M : ℕ} (y₀ : β) (T₁ : List β) (I₂ : List (Fin M)) (g : β → ℝ) :
    expectSeq (lookupSeq y₀ T₁ I₂) g =
      expectSeq I₂ (fun j : Fin M => g (T₁.getD j.val y₀)) :=
  expectSeq_map_eq I₂ (fun j : Fin M => T₁.getD j.val y₀) g

lemma expectSet_univ_getD_eq_expectSeq {M : ℕ} (y₀ : β) {T₁ : List β} (hM : T₁.length = M)
    (g : β → ℝ) :
    expectSet (Finset.univ : Finset (Fin M)) (fun j : Fin M => g (T₁.getD j.val y₀)) =
      expectSeq T₁ g := by
  unfold expectSet expectSeq
  simp only [Finset.card_univ, Fintype.card_fin, hM]
  congr 1
  rw [list_map_sum_eq_fin_sum]
  let e : Fin M ≃ Fin T₁.length := Fin.castOrderIso hM.symm |>.toEquiv
  rw [← Equiv.sum_comp e (fun i : Fin T₁.length => g (T₁.get i))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hj : j.val < T₁.length := hM ▸ j.isLt
  have hgetD : T₁.getD j.val y₀ = T₁[j.val]'hj := by simp [List.getD, hj]
  rw [hgetD]
  rfl

/-- Composes a Stage-1 family `fam₁ : List (List β)` with a Stage-2 index family
`fam₂ : List (List (Fin M))` via `lookupSeq y₀`. -/
def composeFamilies {M : ℕ} (y₀ : β) (fam₁ : List (List β)) (fam₂ : List (List (Fin M))) :
    List (List β) :=
  fam₁.flatMap (fun T₁ => fam₂.map (lookupSeq y₀ T₁))

lemma composeFamilies_length {M : ℕ} (y₀ : β) (fam₁ : List (List β))
    (fam₂ : List (List (Fin M))) :
    (composeFamilies y₀ fam₁ fam₂).length = fam₁.length * fam₂.length := by
  induction fam₁ with
  | nil => simp [composeFamilies]
  | cons T₁ rest ih =>
    simp only [composeFamilies, List.flatMap_cons, List.length_append, List.length_map,
      List.length_cons] at ih ⊢
    rw [ih]
    ring

/-- Cost-tracked composition of a Stage-1 family `fam₁ : List (List β)` with a Stage-2 index
family `fam₂ : List (List (Fin M))` via `flatMapListTracked`, `mapListTracked`, and
`lookupSeqTracked`. -/
def composeFamiliesTracked {M : ℕ} (y₀ : β) (fam₁ : List (List β))
    (fam₂ : List (List (Fin M))) : CostM (List (List β)) :=
  flatMapListTracked (fun T₁ => mapListTracked (lookupSeqTracked y₀ T₁) fam₂) fam₁

@[simp]
lemma composeFamiliesTracked_fst {M : ℕ} (y₀ : β) (fam₁ : List (List β))
    (fam₂ : List (List (Fin M))) :
    (composeFamiliesTracked y₀ fam₁ fam₂).1 = composeFamilies y₀ fam₁ fam₂ := by
  simp [composeFamiliesTracked, composeFamilies]

lemma composeFamiliesTracked_snd_le {M : ℕ} (y₀ : β) (fam₁ : List (List β))
    (fam₂ : List (List (Fin M))) (L₂ : ℕ) (hL₂ : ∀ I₂ ∈ fam₂, I₂.length ≤ L₂) :
    (composeFamiliesTracked y₀ fam₁ fam₂).2 ≤
      fam₁.length * (fam₂.length * (2 * L₂ + 3) + 2) + 1 := by
  unfold composeFamiliesTracked
  have h1 := flatMapListTracked_snd_le_const
    (fun T₁ => mapListTracked (lookupSeqTracked y₀ T₁) fam₂)
    (fam₂.length * (2 * L₂ + 2) + 1) fam₂.length fam₁ ?_
  · refine h1.trans ?_
    have : fam₂.length * (2 * L₂ + 2) + 1 + fam₂.length + 1 =
        fam₂.length * (2 * L₂ + 3) + 2 := by ring
    rw [this]
  · intro T₁ _
    refine ⟨?_, by simp⟩
    refine mapListTracked_snd_le_const (lookupSeqTracked y₀ T₁) (2 * L₂ + 1) fam₂ ?_
    intro I₂ hI₂
    have hlen := hL₂ I₂ hI₂
    have hstep := lookupSeqTracked_snd_le y₀ T₁ I₂
    omega

/-- Union-bound filter inequality on a product family `L₁.flatMap (fun x₁ => L₂.map (f x₁))`. -/
lemma length_filter_flatMap_map_le {α₁ α₂ γ : Type*} (L₁ : List α₁) (L₂ : List α₂)
    (f : α₁ → α₂ → γ) (p : γ → Bool) (p₁ : α₁ → Bool) (p₂ : α₁ → α₂ → Bool)
    (h_imp : ∀ x₁ ∈ L₁, ∀ x₂ ∈ L₂, p (f x₁ x₂) = true → p₁ x₁ = true ∨ p₂ x₁ x₂ = true) :
    ((L₁.flatMap (fun x₁ => L₂.map (f x₁))).filter p).length ≤
      (L₁.filter p₁).length * L₂.length +
        (L₁.map (fun x₁ => (L₂.filter (p₂ x₁)).length)).sum := by
  induction L₁ with
  | nil => simp
  | cons x₁ xs ih =>
    have ih' := ih (fun a ha b hb hp => h_imp a (List.mem_cons_of_mem x₁ ha) b hb hp)
    rw [List.flatMap_cons, List.filter_append, List.length_append, List.map_cons,
      List.sum_cons, List.filter_cons]
    cases hp₁ : p₁ x₁
    · rw [if_neg Bool.false_ne_true]
      have hle₂ : ((L₂.map (f x₁)).filter p).length ≤ (L₂.filter (p₂ x₁)).length := by
        rw [List.filter_map, List.length_map]
        apply list_length_filter_mono
        intro x₂ hx₂ hpx
        rcases h_imp x₁ List.mem_cons_self x₂ hx₂ hpx with h1 | h2
        · exfalso; exact Bool.false_ne_true (hp₁.symm.trans h1)
        · exact h2
      omega
    · rw [if_pos rfl, List.length_cons]
      have hle₁ : ((L₂.map (f x₁)).filter p).length ≤ L₂.length := by
        calc
          ((L₂.map (f x₁)).filter p).length ≤ (L₂.map (f x₁)).length :=
            List.length_filter_le _ _
          _ = L₂.length := List.length_map _
      calc
        (List.filter p (List.map (f x₁) L₂)).length +
            (List.filter p (List.flatMap (fun x₁ => List.map (f x₁) L₂) xs)).length
          ≤ L₂.length +
              ((List.filter p₁ xs).length * L₂.length +
                (List.map (fun x₁ => (List.filter (p₂ x₁) L₂).length) xs).sum) :=
            Nat.add_le_add hle₁ ih'
        _ ≤ ((List.filter p₁ xs).length + 1) * L₂.length +
              ((List.filter (p₂ x₁) L₂).length +
                (List.map (fun x₁ => (List.filter (p₂ x₁) L₂).length) xs).sum) := by
            have : L₂.length + (List.filter p₁ xs).length * L₂.length =
                ((List.filter p₁ xs).length + 1) * L₂.length := by ring
            omega

lemma list_map_sum_le_of_le {α₁ : Type*} (L : List α₁) (f : α₁ → ℕ) (B : ℝ)
    (hB : ∀ x ∈ L, (f x : ℝ) ≤ B) :
    (((L.map f).sum : ℕ) : ℝ) ≤ (L.length : ℝ) * B := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    have hx := hB x List.mem_cons_self
    have hxs := ih (fun y hy => hB y (List.mem_cons_of_mem x hy))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

/-- **General Two-Stage Sequence Sampler Gluing Theorem (`composeFamilies_isSeqSampler`,
`paper.tex` Section 3.3 & Appendix B, `\eqref{eq:oblivious-sampler}` & `\eqref{eq:two-stage-sampler}`,
§3.3 & §4.1)**:
If `fam₁` is a Stage-1 $(\varepsilon_1, \delta_1)$-sequence sampler of `Y` with uniform sequence
length `M`, and `fam₂` is a Stage-2 $(\varepsilon_2, \delta_2)$-sequence sampler of `Fin M`, then
`composeFamilies y₀ fam₁ fam₂` is an $(\varepsilon_1 + \varepsilon_2, \delta_1 + \delta_2)$-sequence
sampler of `Y`. -/
theorem composeFamilies_isSeqSampler {M : ℕ} {Y : Finset β} {y₀ : β} (hy₀ : y₀ ∈ Y)
    {fam₁ : List (List β)} {fam₂ : List (List (Fin M))} {ε₁ ε₂ δ₁ δ₂ : ℝ}
    (hS₁ : IsSeqSampler Y fam₁ ε₁ δ₁)
    (hM : ∀ T₁ ∈ fam₁, T₁.length = M)
    (hS₂ : IsSeqSampler (Finset.univ : Finset (Fin M)) fam₂ ε₂ δ₂) :
    IsSeqSampler Y (composeFamilies y₀ fam₁ fam₂) (ε₁ + ε₂) (δ₁ + δ₂) := by
  classical
  have hY_ne : Y.Nonempty := ⟨y₀, hy₀⟩
  have hM_pos : 0 < M := by
    cases hfam₁ : fam₁ with
    | nil => exact False.elim (hS₁.1 hfam₁)
    | cons T₁ tl =>
      have hmem : T₁ ∈ fam₁ := hfam₁ ▸ List.mem_cons_self
      have hT₁_ne : T₁ ≠ [] := (hS₁.2.1 T₁ hmem).2 hY_ne
      rw [← hM T₁ hmem]
      exact List.length_pos_of_ne_nil hT₁_ne
  have hunivM_ne : (Finset.univ : Finset (Fin M)).Nonempty :=
    ⟨⟨0, hM_pos⟩, Finset.mem_univ _⟩
  refine ⟨?_, ?_, ?_⟩
  · intro hemp
    have hlen := congrArg List.length hemp
    rw [composeFamilies_length, List.length_nil, Nat.mul_eq_zero] at hlen
    rcases hlen with h1 | h2
    · exact hS₁.1 (List.length_eq_zero_iff.mp h1)
    · exact hS₂.1 (List.length_eq_zero_iff.mp h2)
  · intro T hT
    unfold composeFamilies at hT
    rcases List.mem_flatMap.mp hT with ⟨T₁, hT₁, hT₂⟩
    rcases List.mem_map.mp hT₂ with ⟨I₂, hI₂, rfl⟩
    refine ⟨lookupSeq_mem hy₀ (hS₁.2.1 T₁ hT₁).1 I₂, fun _ => ?_⟩
    have hI₂_ne : I₂ ≠ [] := (hS₂.2.1 I₂ hI₂).2 hunivM_ne
    intro hmap_nil
    exact hI₂_ne (List.map_eq_nil_iff.mp hmap_nil)
  · intro g hg
    let p : List β → Bool := fun T => decide (|expectSeq T g - expectSet Y g| > ε₁ + ε₂)
    let p₁ : List β → Bool := fun T₁ => decide (|expectSeq T₁ g - expectSet Y g| > ε₁)
    let p₂ : List β → List (Fin M) → Bool := fun T₁ I₂ =>
      decide (|expectSeq I₂ (fun j : Fin M => g (T₁.getD j.val y₀)) -
        expectSet (Finset.univ : Finset (Fin M)) (fun j : Fin M => g (T₁.getD j.val y₀))| > ε₂)
    have himp : ∀ T₁ ∈ fam₁, ∀ I₂ ∈ fam₂,
        p (lookupSeq y₀ T₁ I₂) = true → p₁ T₁ = true ∨ p₂ T₁ I₂ = true := by
      intro T₁ hT₁ I₂ _ hp_true
      have hgt : |expectSeq (lookupSeq y₀ T₁ I₂) g - expectSet Y g| > ε₁ + ε₂ :=
        of_decide_eq_true hp_true
      by_cases h1 : |expectSeq T₁ g - expectSet Y g| > ε₁
      · exact Or.inl (decide_eq_true h1)
      · right
        apply decide_eq_true
        have hle1 : |expectSeq T₁ g - expectSet Y g| ≤ ε₁ := not_lt.mp h1
        rw [expectSeq_lookupSeq] at hgt
        rw [expectSet_univ_getD_eq_expectSeq y₀ (hM T₁ hT₁) g]
        have htri :
            |expectSeq I₂ (fun j : Fin M => g (T₁.getD j.val y₀)) - expectSet Y g| ≤
              |expectSeq I₂ (fun j : Fin M => g (T₁.getD j.val y₀)) - expectSeq T₁ g| +
                |expectSeq T₁ g - expectSet Y g| := by
          have heq :
              expectSeq I₂ (fun j : Fin M => g (T₁.getD j.val y₀)) - expectSet Y g =
                (expectSeq I₂ (fun j : Fin M => g (T₁.getD j.val y₀)) - expectSeq T₁ g) +
                  (expectSeq T₁ g - expectSet Y g) := by ring
          rw [heq]
          exact abs_add_le _ _
        linarith
    have hlen_bound := length_filter_flatMap_map_le fam₁ fam₂ (lookupSeq y₀) p p₁ p₂ himp
    have hcast_bound :
        ((( (composeFamilies y₀ fam₁ fam₂).filter p ).length : ℕ) : ℝ) ≤
          ((fam₁.filter p₁).length : ℝ) * (fam₂.length : ℝ) +
            (((fam₁.map (fun T₁ => (fam₂.filter (p₂ T₁)).length)).sum : ℕ) : ℝ) := by
      unfold composeFamilies
      exact_mod_cast hlen_bound
    have hbad₁ : ((fam₁.filter p₁).length : ℝ) ≤ δ₁ * (fam₁.length : ℝ) := hS₁.2.2 g hg
    have hbad₂_each : ∀ T₁ ∈ fam₁,
        ((fam₂.filter (p₂ T₁)).length : ℝ) ≤ δ₂ * (fam₂.length : ℝ) := by
      intro T₁ hT₁
      have hg_T₁ : ∀ j ∈ (Finset.univ : Finset (Fin M)),
          0 ≤ g (T₁.getD j.val y₀) ∧ g (T₁.getD j.val y₀) ≤ 1 := by
        intro j _
        have hj_mem : T₁.getD j.val y₀ ∈ Y := by
          unfold List.getD
          cases hget : T₁[j.val]? with
          | none => exact hy₀
          | some z => exact (hS₁.2.1 T₁ hT₁).1 z (List.mem_of_getElem? hget)
        exact hg _ hj_mem
      exact hS₂.2.2 (fun j : Fin M => g (T₁.getD j.val y₀)) hg_T₁
    have hbad₂_sum := list_map_sum_le_of_le fam₁ (fun T₁ => (fam₂.filter (p₂ T₁)).length)
      (δ₂ * (fam₂.length : ℝ)) hbad₂_each
    have hbad₁_mul :
        ((fam₁.filter p₁).length : ℝ) * (fam₂.length : ℝ) ≤
          δ₁ * (fam₁.length : ℝ) * (fam₂.length : ℝ) :=
      mul_le_mul_of_nonneg_right hbad₁ (Nat.cast_nonneg _)
    rw [composeFamilies_length, Nat.cast_mul]
    linarith

/-- Polynomial sample-size bound
$(c + 1) \cdot ((\text{invEps} + 1) \cdot (\text{logInvDelta} + 1))^{k + 2}
 = \operatorname{poly}(\varepsilon_{\text{samp}}^{-1}, \log \delta_{\text{samp}}^{-1})$
from `paper.tex` `\eqref{eq:two-stage-sampler}` (§3.3). -/
def twoStageSampleSizeBound (c k invEps logInvDelta : ℕ) : ℕ :=
  (c + 1) * ((invEps + 1) * (logInvDelta + 1)) ^ (k + 2)

lemma one_le_twoStageSampleSizeBound (c k invEps logInvDelta : ℕ) :
    1 ≤ twoStageSampleSizeBound c k invEps logInvDelta := by
  unfold twoStageSampleSizeBound
  exact Nat.succ_le_of_lt (by positivity)

/-- Polynomial family-size factor
$(c + 1) \cdot ((\text{invEps} + 1) \cdot (\text{invDelta} + 1))^{k + 2}
 = \operatorname{poly}(\varepsilon_{\text{samp}}^{-1}, \delta_{\text{samp}}^{-1})$
from `paper.tex` `\eqref{eq:two-stage-sampler}` (§3.3). -/
def twoStageFamFactor (c k invEps invDelta : ℕ) : ℕ :=
  (c + 1) * ((invEps + 1) * (invDelta + 1)) ^ (k + 2)

lemma one_le_twoStageFamFactor (c k invEps invDelta : ℕ) :
    1 ≤ twoStageFamFactor c k invEps invDelta := by
  unfold twoStageFamFactor
  exact Nat.succ_le_of_lt (by positivity)

/-- Two-stage size predicate corresponding to `paper.tex` `\eqref{eq:two-stage-sampler}`
(§3.3). -/
def SatisfiesTwoStageBounds (c k : ℕ) (Y : Finset β) (T_fam : List (List β))
    (invEps invDelta logInvDelta : ℕ) : Prop :=
  T_fam.length ≤ max 1 Y.card * twoStageFamFactor c k invEps invDelta ∧
  ∀ T ∈ T_fam, T.length ≤ twoStageSampleSizeBound c k invEps logInvDelta

/-- Accuracy exponent for the `EstimateNorm` / `ApproxGridNorm` two-stage oblivious sampler
(`paper.tex` Algorithm 2 Line 1 `\label{line:est-sampler}` & §4.1):
`accExp ε d = 3 * d + 6 + ⌈log₂ ⌈1 / ε⌉⌉`, so that `2 ^ (-accExp ε d) ≤ ε * 2 ^ (-(3 * d + 6))`
for every `ε > 0`, and `accExp (1 / 160) d = 3 * d + 14`. -/
noncomputable def accExp (ε : ℝ) (d : ℕ) : ℕ :=
  3 * d + 6 + Nat.clog 2 ⌈1 / ε⌉₊

lemma three_mul_add_six_le_accExp (ε : ℝ) (d : ℕ) : 3 * d + 6 ≤ accExp ε d :=
  Nat.le_add_right _ _

@[simp]
lemma accExp_one_div_160 (d : ℕ) : accExp (1 / 160 : ℝ) d = 3 * d + 14 := by
  unfold accExp
  have hceil : ⌈(1 : ℝ) / (1 / 160 : ℝ)⌉₊ = 160 := by norm_num
  have hclog : Nat.clog 2 160 = 8 := by decide
  rw [hceil, hclog]

lemma three_mul_add_fourteen_le_accExp {ε : ℝ} (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (d : ℕ) :
    3 * d + 14 ≤ accExp ε d := by
  unfold accExp
  have h160 : (160 : ℝ) ≤ 1 / ε := by
    have := one_div_le_one_div_of_le hε0 hε_le
    linarith
  have hceil : 160 ≤ ⌈1 / ε⌉₊ := by exact_mod_cast h160.trans (Nat.le_ceil _)
  have hclog : 8 ≤ Nat.clog 2 ⌈1 / ε⌉₊ := by
    have h8 : Nat.clog 2 160 = 8 := by decide
    rw [← h8]
    exact Nat.clog_mono_right 2 hceil
  omega

/-- **Two-Stage Oblivious Sequence Sampler Oracle (`paper.tex` Section 3.3 & Appendix B,
`\eqref{eq:oblivious-sampler}` & `\eqref{eq:two-stage-sampler}`, §3.3)**:
Packages a deterministic two-stage oblivious sequence sampler construction at regularity scale `ε`
with polynomial degree/constant parameters `(c, k)`. Constructed from `(S₁ : Stage1Sampler)` and
`(S₂ : Stage2Sampler)` via `twoStage_compose` below using only Lean's three standard foundational
axioms (`propext`, `Classical.choice`, `Quot.sound`). -/
structure TwoStageSamplerOracle (β : Type*) (ε : ℝ) where
  c : ℕ
  k : ℕ
  /-- Cost-tracked two-stage sampler constructor taking `(Y : Finset β) (invEps logInvDelta : ℕ)`
      and returning `T_fam : List (List β)` in `CostM`. -/
  constructTracked : Finset β → ℕ → ℕ → CostM (List (List β))
  /-- Uniform sequence length across the family: every `T ∈ T_fam` has length equal to
      `(T_fam.headD []).length`. -/
  len_eq : ∀ (Y : Finset β) (invEps logInvDelta : ℕ),
    let T_fam := (constructTracked Y invEps logInvDelta).1
    ∀ T ∈ T_fam, T.length = (T_fam.headD []).length
  /-- Two-stage size bounds (`paper.tex` `\eqref{eq:two-stage-sampler}`, §3.3):
      For `1 ≤ invEps`, `|T_fam| ≤ max 1 |Y| * twoStageFamFactor c k invEps (2 ^ logInvDelta)` and
      `∀ T ∈ T_fam, |T| ≤ twoStageSampleSizeBound c k invEps logInvDelta`. -/
  satisfies_bounds : ∀ (Y : Finset β) (invEps logInvDelta : ℕ),
    1 ≤ invEps →
    SatisfiesTwoStageBounds c k Y (constructTracked Y invEps logInvDelta).1
      invEps (2 ^ logInvDelta) logInvDelta
  /-- Deterministic construction step cost in `CostM` (`paper.tex` `\eqref{eq:two-stage-sampler}`,
      §3.3), bounded by `(|Y| + 1) ^ 2 * twoStageFamFactor c k invEps (2 ^ logInvDelta) *
      twoStageSampleSizeBound c k invEps logInvDelta` (where `nat_log2_add_one_pow_le` relaxes
      the Stage-1 polylogarithmic factor $|Y|(\lfloor\log_2 |Y|\rfloor + 1)^{S_1.k}$ to
      $(|Y| + 1)^2$, absorbed into the $O((|X| + |Y|)^2)$ budget of Algorithm 2). -/
  cost_le : ∀ (Y : Finset β) (invEps logInvDelta : ℕ),
    (constructTracked Y invEps logInvDelta).2 ≤
      (Y.card + 1) ^ 2 * twoStageFamFactor c k invEps (2 ^ logInvDelta) *
        twoStageSampleSizeBound c k invEps logInvDelta
  /-- Oblivious sequence sampler guarantee (`paper.tex` `\eqref{eq:oblivious-sampler}` &
      Algorithm 2 Line 1 `\label{line:est-sampler}`, §3.3 & §4.1):
      For `d ≥ 1` and any target parameters `ε_samp ≥ ε / 2 ^ (3 * d + 6)` and
      `δ_samp ≥ (ε / 2 ^ (3 * d + 6)) ^ d`,
      `(constructTracked Y (2 ^ accExp ε d) (d * accExp ε d)).1` is an
      `(ε_samp, δ_samp)`-sequence sampler of `Y` (`IsSeqSampler`). -/
  is_sampler : ∀ (Y : Finset β) (d : ℕ) {ε_samp δ_samp : ℝ},
    1 ≤ d →
    ε / ((2 ^ (3 * d + 6) : ℕ) : ℝ) ≤ ε_samp →
    (ε / ((2 ^ (3 * d + 6) : ℕ) : ℝ)) ^ d ≤ δ_samp →
    IsSeqSampler Y
      (constructTracked Y (2 ^ accExp ε d) (d * accExp ε d)).1
      ε_samp δ_samp

namespace TwoStageSamplerOracle

variable {β : Type*} {ε : ℝ}

/-- Family length bound `|T_fam| ≤ (|Y| + 1) * twoStageFamFactor S.c S.k invEps (2 ^ logInvDelta)`. -/
theorem length_le (S : TwoStageSamplerOracle β ε) (Y : Finset β)
    {invEps : ℕ} (h_inv : 1 ≤ invEps) (logInvDelta : ℕ) :
    ((S.constructTracked Y invEps logInvDelta).1).length ≤
      (Y.card + 1) * twoStageFamFactor S.c S.k invEps (2 ^ logInvDelta) := by
  have h1 := (S.satisfies_bounds Y invEps logInvDelta h_inv).1
  have hmax : max 1 Y.card ≤ Y.card + 1 := max_le (by omega) (by omega)
  exact le_trans h1 (Nat.mul_le_mul_right _ hmax)

/-- Sample sequence length bound `T.length ≤ twoStageSampleSizeBound S.c S.k invEps logInvDelta`
for every `T ∈ T_fam`. -/
theorem mem_length_le (S : TwoStageSamplerOracle β ε) (Y : Finset β)
    {invEps : ℕ} (h_inv : 1 ≤ invEps) (logInvDelta : ℕ)
    {T : List β} (hT : T ∈ (S.constructTracked Y invEps logInvDelta).1) :
    T.length ≤ twoStageSampleSizeBound S.c S.k invEps logInvDelta :=
  (S.satisfies_bounds Y invEps logInvDelta h_inv).2 T hT

/-- Sample sequence length bound for `(T_fam.headD []).length`. -/
theorem headD_length_le (S : TwoStageSamplerOracle β ε) (Y : Finset β)
    {invEps : ℕ} (h_inv : 1 ≤ invEps) (logInvDelta : ℕ) :
    (((S.constructTracked Y invEps logInvDelta).1).headD []).length ≤
      twoStageSampleSizeBound S.c S.k invEps logInvDelta := by
  cases hlist : (S.constructTracked Y invEps logInvDelta).1 with
  | nil => simp
  | cons T₀ tl =>
    have hmem : T₀ ∈ (S.constructTracked Y invEps logInvDelta).1 := by
      rw [hlist]
      exact List.mem_cons_self
    simpa [List.headD] using S.mem_length_le Y h_inv logInvDelta hmem

end TwoStageSamplerOracle

/-!
### Stage-2 Reduction from `Fin (2 ^ m)` (`{0, 1}^m`) to Arbitrary `Fin M` (`stage2FinM_*`)

`[GUV09, Theorem 1.5, JACM 56(4), Art. 20, p. 4]` combined with
`[Vadhan 2012, Corollary 6.24(1), printed p. 186]` (historical context:
`[Zuckerman 1997, Theorem 3.17, p. 15]`) states averaging samplers over `{0, 1}^m` (modeled as
`Fin (2 ^ m)` in `Stage2Sampler`). Given an arbitrary Stage-1 sequence length `M ≥ 1` and accuracy
parameter `e ≥ 1`, we choose `m = stage2BitLen M e := ⌊log₂(2 M e)⌋ + 1` so that
`2 M e < 2 ^ m ≤ 4 M e + 2`, invoke `S₂` on `Fin (2 ^ m)` with accuracy parameter `2 e`, and
project `Fin (2 ^ m) → Fin M` via `x ↦ x mod M` (`modFin M hM`). Because each residue in `Fin M`
has either `⌊2^m / M⌋` or `⌊2^m / M⌋ + 1` preimages in `Fin (2 ^ m)`, the uniform expectation on
`Fin (2 ^ m)` differs from the uniform expectation on `Fin M` by at most
`(M mod 2^m) / 2^m ≤ M / 2^m ≤ 1 / (2 e)` (`expectSet_univ_modFin_sub_abs_le`), which combines with
the `1 / (2 e)` sampler accuracy on `Fin (2 ^ m)` via the triangle inequality to give `1 / e`
accuracy on `Fin M` (`isSeqSampler_modFinFam`, `stage2FinM_sampler`).
-/

/-- Modulo projection `Fin K → Fin M` mapping `x ↦ x mod M` (for `0 < M`). -/
def modFin (M : ℕ) (hM : 0 < M) {K : ℕ} (x : Fin K) : Fin M :=
  ⟨x.val % M, Nat.mod_lt x.val hM⟩

/-- Cost-tracked modulo projection `Fin K → Fin M` in `CostM`, charging
`bitLengthNat x.val * bitLengthNat M + 2` (`modNatTracked x.val M` plus `retTracked`). -/
def modFinTracked (M : ℕ) (hM : 0 < M) {K : ℕ} (x : Fin K) : CostM (Fin M) :=
  CostM.bind (modNatTracked x.val M) (fun r =>
    retTracked (if hr : r < M then ⟨r, hr⟩ else ⟨0, hM⟩))

@[simp]
lemma modFinTracked_fst (M : ℕ) (hM : 0 < M) {K : ℕ} (x : Fin K) :
    (modFinTracked M hM x).1 = modFin M hM x := by
  unfold modFinTracked modFin
  simp only [CostM.bind_fst, modNatTracked_fst, retTracked_fst]
  rw [dif_pos (Nat.mod_lt x.val hM)]

lemma modFinTracked_snd (M : ℕ) (hM : 0 < M) {K : ℕ} (x : Fin K) :
    (modFinTracked M hM x).2 = bitLengthNat x.val * bitLengthNat M + 2 := by
  unfold modFinTracked
  simp [CostM.bind_snd, modNatTracked_snd, retTracked_snd]

lemma modFinTracked_snd_le (M : ℕ) (hM : 0 < M) {K : ℕ} (x : Fin K) :
    (modFinTracked M hM x).2 ≤ (Nat.log 2 K + 2) * (Nat.log 2 M + 2) + 1 := by
  rw [modFinTracked_snd]
  unfold bitLengthNat
  have hx : Nat.log 2 x.val ≤ Nat.log 2 K := Nat.log_mono_right x.isLt.le
  have hmul : (Nat.log 2 x.val + 1) * (Nat.log 2 M + 1) ≤ (Nat.log 2 K + 1) * (Nat.log 2 M + 1) :=
    Nat.mul_le_mul_right _ (Nat.add_le_add_right hx 1)
  have h1 : (Nat.log 2 K + 1) * (Nat.log 2 M + 1) + 2 ≤ (Nat.log 2 K + 2) * (Nat.log 2 M + 2) + 1 := by
    nlinarith
  exact (Nat.add_le_add_right hmul 2).trans h1

/-- Maps a family of sample sequences over `Fin K` to `Fin M` via `modFin M hM`. -/
def modFinFam (M : ℕ) (hM : 0 < M) {K : ℕ} (fam : List (List (Fin K))) :
    List (List (Fin M)) :=
  fam.map (fun I => I.map (modFin M hM))

/-- Cost-tracked version of `modFinFam` in `CostM`, traversing every sample sequence and charging
the bit-level modular reduction cost `modFinTracked M hM x` (`O((log K) · (log M))`) per element
via `mapListTracked`. -/
def modFinFamTracked (M : ℕ) (hM : 0 < M) {K : ℕ} (fam : List (List (Fin K))) :
    CostM (List (List (Fin M))) :=
  mapListTracked (fun I => mapListTracked (modFinTracked M hM) I) fam

@[simp]
lemma modFinFamTracked_fst (M : ℕ) (hM : 0 < M) {K : ℕ} (fam : List (List (Fin K))) :
    (modFinFamTracked M hM fam).1 = modFinFam M hM fam := by
  unfold modFinFamTracked modFinFam
  rw [mapListTracked_fst]
  refine List.map_congr_left (fun I _ => ?_)
  rw [mapListTracked_fst]
  refine List.map_congr_left (fun x _ => modFinTracked_fst M hM x)

@[simp]
lemma modFinFam_length (M : ℕ) (hM : 0 < M) {K : ℕ} (fam : List (List (Fin K))) :
    (modFinFam M hM fam).length = fam.length := by
  simp [modFinFam]

lemma modFinFamTracked_snd_le (M : ℕ) (hM : 0 < M) {K : ℕ} (fam : List (List (Fin K)))
    (L : ℕ) (hL : ∀ I ∈ fam, I.length ≤ L) :
    (modFinFamTracked M hM fam).2 ≤
      fam.length * (L * ((Nat.log 2 K + 2) * (Nat.log 2 M + 2) + 2) + 2) + 1 := by
  unfold modFinFamTracked
  set B_mod := (Nat.log 2 K + 2) * (Nat.log 2 M + 2) + 1
  have hinner : ∀ I ∈ fam,
      (mapListTracked (modFinTracked M hM) I).2 ≤ L * (B_mod + 1) + 1 := by
    intro I hI
    have h1 : (mapListTracked (modFinTracked M hM) I).2 ≤ I.length * (B_mod + 1) + 1 :=
      mapListTracked_snd_le_const (modFinTracked M hM) B_mod I
        (fun x _ => modFinTracked_snd_le M hM x)
    exact h1.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (hL I hI)) 1)
  have hout := mapListTracked_snd_le_const _ (L * (B_mod + 1) + 1) fam hinner
  simpa [B_mod, Nat.add_assoc] using hout

private lemma sum_range_modFin_eq (M : ℕ) (hM : 0 < M) (g : Fin M → ℝ) :
    ∑ x ∈ Finset.range M, g ⟨x % M, Nat.mod_lt x hM⟩ = ∑ z : Fin M, g z := by
  rw [← Fin.sum_univ_eq_sum_range (fun x => g ⟨x % M, Nat.mod_lt x hM⟩) M]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  congr 1
  ext
  exact Nat.mod_eq_of_lt z.isLt

private lemma sum_range_mul_add_modFin (M : ℕ) (hM : 0 < M) (g : Fin M → ℝ) (Q R : ℕ) :
    ∑ x ∈ Finset.range (Q * M + R), g ⟨x % M, Nat.mod_lt x hM⟩ =
      (Q : ℝ) * (∑ z : Fin M, g z) +
        ∑ x ∈ Finset.range R, g ⟨x % M, Nat.mod_lt x hM⟩ := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    have h_eq : (Q + 1) * M + R = M + (Q * M + R) := by ring
    rw [h_eq, Finset.sum_range_add, sum_range_modFin_eq M hM g]
    have h_shift :
        ∑ x ∈ Finset.range (Q * M + R), g ⟨(M + x) % M, Nat.mod_lt (M + x) hM⟩ =
          ∑ x ∈ Finset.range (Q * M + R), g ⟨x % M, Nat.mod_lt x hM⟩ := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      congr 1
      ext
      exact Nat.add_mod_left M x
    rw [h_shift, ih]
    push_cast
    ring

/-- **Modulo-Projection Total-Variation Bias Bound (`expectSet_univ_modFin_sub_abs_le`)**:
For any $M, K \ge 1$ and any $g : \text{Fin } M \to [0, 1]$, the uniform expectation of
$x \mapsto g(x \bmod M)$ over $\text{Fin } K$ differs from the uniform expectation of $g$ over
$\text{Fin } M$ by at most $M / K$. -/
lemma expectSet_univ_modFin_sub_abs_le (M K : ℕ) (hM : 0 < M) (hK : 0 < K)
    (g : Fin M → ℝ) (hg : ∀ z ∈ (Finset.univ : Finset (Fin M)), 0 ≤ g z ∧ g z ≤ 1) :
    |expectSet (Finset.univ : Finset (Fin K)) (fun x => g (modFin M hM x)) -
       expectSet (Finset.univ : Finset (Fin M)) g| ≤ (M : ℝ) / (K : ℝ) := by
  have hM_ne : (Finset.univ : Finset (Fin M)).Nonempty :=
    ⟨⟨0, hM⟩, Finset.mem_univ _⟩
  have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have hK_pos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK
  set μ := expectSet (Finset.univ : Finset (Fin M)) g
  have hμ_nonneg : 0 ≤ μ := expectSet_nonneg (fun z hz => (hg z hz).1)
  have hμ_le_one : μ ≤ 1 := expectSet_le_of_le hM_ne (fun z hz => (hg z hz).2)
  have hsum_M : ∑ z : Fin M, g z = (M : ℝ) * μ := by
    dsimp [μ, expectSet]
    rw [Fintype.card_fin]
    field_simp [hM_pos.ne']
  set Q := K / M
  set R := K % M
  have hK_decomp : Q * M + R = K := by
    dsimp [Q, R]
    rw [mul_comm, Nat.div_add_mod]
  have hR_lt : R < M := Nat.mod_lt K hM
  have hsum_K :
      ∑ x : Fin K, g (modFin M hM x) =
        (Q : ℝ) * ((M : ℝ) * μ) + ∑ x ∈ Finset.range R, g ⟨x % M, Nat.mod_lt x hM⟩ := by
    dsimp [modFin]
    rw [Fin.sum_univ_eq_sum_range (fun x => g ⟨x % M, Nat.mod_lt x hM⟩) K]
    rw [← hK_decomp, sum_range_mul_add_modFin M hM g Q R, hsum_M]
  set S_R := ∑ x ∈ Finset.range R, g ⟨x % M, Nat.mod_lt x hM⟩
  have hSR_nonneg : 0 ≤ S_R :=
    Finset.sum_nonneg (fun x _ => (hg _ (Finset.mem_univ _)).1)
  have hSR_le : S_R ≤ (R : ℝ) := by
    calc
      S_R ≤ ∑ _x ∈ Finset.range R, (1 : ℝ) :=
        Finset.sum_le_sum (fun x _ => (hg _ (Finset.mem_univ _)).2)
      _ = (R : ℝ) := by simp
  have hRμ_nonneg : 0 ≤ (R : ℝ) * μ := mul_nonneg (Nat.cast_nonneg R) hμ_nonneg
  have hRμ_le : (R : ℝ) * μ ≤ (R : ℝ) := mul_le_of_le_one_right (Nat.cast_nonneg R) hμ_le_one
  have hR_le_M : (R : ℝ) ≤ (M : ℝ) := Nat.cast_le.mpr hR_lt.le
  have hK_real : (K : ℝ) = (Q : ℝ) * (M : ℝ) + (R : ℝ) := by
    have := congrArg (Nat.cast (R := ℝ)) hK_decomp.symm
    push_cast at this
    exact this
  have hexp_K :
      expectSet (Finset.univ : Finset (Fin K)) (fun x => g (modFin M hM x)) =
        ((Q : ℝ) * ((M : ℝ) * μ) + S_R) / (K : ℝ) := by
    unfold expectSet
    rw [Finset.card_univ, Fintype.card_fin, hsum_K]
  have hdiff :
      expectSet (Finset.univ : Finset (Fin K)) (fun x => g (modFin M hM x)) - μ =
        (S_R - (R : ℝ) * μ) / (K : ℝ) := by
    rw [hexp_K]
    field_simp [hK_pos.ne']
    rw [hK_real]
    ring
  rw [hdiff, abs_div, abs_of_pos hK_pos]
  refine div_le_div_of_nonneg_right ?_ hK_pos.le
  rw [abs_le]
  constructor <;> linarith

/-- **Modulo-Projection Sequence Sampler Reduction (`isSeqSampler_modFinFam`)**:
If `fam` is an `(ε₀, δ)`-sequence sampler on `Fin K` and `M / K ≤ ε₁`, then `modFinFam M hM fam`
is an `(ε₀ + ε₁, δ)`-sequence sampler on `Fin M`. -/
theorem isSeqSampler_modFinFam {M K : ℕ} (hM : 0 < M) (hK : 0 < K)
    {fam : List (List (Fin K))} {ε₀ ε₁ δ : ℝ}
    (hS : IsSeqSampler (Finset.univ : Finset (Fin K)) fam ε₀ δ)
    (hbias : (M : ℝ) / (K : ℝ) ≤ ε₁) :
    IsSeqSampler (Finset.univ : Finset (Fin M)) (modFinFam M hM fam) (ε₀ + ε₁) δ := by
  rcases hS with ⟨hne, hsupp, hconc⟩
  refine ⟨?_, ?_, ?_⟩
  · intro hemp
    exact hne (List.map_eq_nil_iff.mp hemp)
  · intro T hT
    unfold modFinFam at hT
    rcases List.mem_map.mp hT with ⟨I, hI, rfl⟩
    refine ⟨fun y _ => Finset.mem_univ y, fun _ => ?_⟩
    have hK_ne : (Finset.univ : Finset (Fin K)).Nonempty :=
      ⟨⟨0, hK⟩, Finset.mem_univ _⟩
    intro hmap_nil
    exact (hsupp I hI).2 hK_ne (List.map_eq_nil_iff.mp hmap_nil)
  · intro g hg
    let g' : Fin K → ℝ := fun x => g (modFin M hM x)
    have hg' : ∀ x ∈ (Finset.univ : Finset (Fin K)), 0 ≤ g' x ∧ g' x ≤ 1 :=
      fun x _ => hg (modFin M hM x) (Finset.mem_univ _)
    have hbad' := hconc g' hg'
    have h_univ_diff :
        |expectSet (Finset.univ : Finset (Fin K)) g' -
           expectSet (Finset.univ : Finset (Fin M)) g| ≤ ε₁ :=
      (expectSet_univ_modFin_sub_abs_le M K hM hK g hg).trans hbias
    open Classical in
    let p : List (Fin M) → Bool :=
      fun T => decide (|expectSeq T g - expectSet (Finset.univ : Finset (Fin M)) g| > ε₀ + ε₁)
    open Classical in
    let q : List (Fin K) → Bool :=
      fun I => decide (|expectSeq I g' - expectSet (Finset.univ : Finset (Fin K)) g'| > ε₀)
    have hfilter_eq :
        ((modFinFam M hM fam).filter p).length =
          (fam.filter (p ∘ List.map (modFin M hM))).length := by
      unfold modFinFam
      rw [List.filter_map, List.length_map]
    have himp : ∀ I ∈ fam, (p ∘ List.map (modFin M hM)) I = true → q I = true := by
      intro I _ hp
      simp only [Function.comp_apply, p, q, decide_eq_true_eq] at hp ⊢
      have hseq_eq : expectSeq (I.map (modFin M hM)) g = expectSeq I g' :=
        expectSeq_map_eq I (modFin M hM) g
      rw [hseq_eq] at hp
      have htri :
          |expectSeq I g' - expectSet (Finset.univ : Finset (Fin M)) g| ≤
            |expectSeq I g' - expectSet (Finset.univ : Finset (Fin K)) g'| +
              |expectSet (Finset.univ : Finset (Fin K)) g' -
                 expectSet (Finset.univ : Finset (Fin M)) g| :=
        abs_sub_le (expectSeq I g')
          (expectSet (Finset.univ : Finset (Fin K)) g')
          (expectSet (Finset.univ : Finset (Fin M)) g)
      linarith
    have hlen_le :
        (((modFinFam M hM fam).filter p).length : ℝ) ≤ ((fam.filter q).length : ℝ) := by
      rw [hfilter_eq]
      exact Nat.cast_le.mpr (list_length_filter_mono himp)
    rw [modFinFam_length]
    exact hlen_le.trans hbad'

/-- Power-of-two bit-length `m = ⌊log₂(2 M e)⌋ + 1` so that `2 M e < 2 ^ m ≤ 4 M e + 2`,
ensuring the modulo projection bias `M / 2 ^ m` is at most `1 / (2 e)`. -/
def stage2BitLen (M e : ℕ) : ℕ := Nat.log 2 (2 * M * e) + 1

/-- Pure Stage-2 family over arbitrary universe size `Fin M` derived from `S₂ : Stage2Sampler`
(which operates over `Fin (2 ^ m)` $\cong \{0,1\}^m$) via `modFinFam`. -/
def stage2FinMFam (S₂ : Stage2Sampler) (M e δ : ℕ) : List (List (Fin M)) :=
  if h : 0 < M ∧ 1 ≤ e ∧ 1 ≤ δ then
    let m := stage2BitLen M e
    modFinFam M h.1 (S₂.fam m (2 * e) δ)
  else
    [[]]

/-- Cost-tracked Stage-2 family over arbitrary universe size `Fin M` in `CostM`. -/
def stage2FinMFamTracked (S₂ : Stage2Sampler) (M e δ : ℕ) : CostM (List (List (Fin M))) :=
  if h : 0 < M ∧ 1 ≤ e ∧ 1 ≤ δ then
    let m := stage2BitLen M e
    CostM.bind (S₂.famTracked m (2 * e) δ) (fun fam_pow =>
      modFinFamTracked M h.1 fam_pow)
  else
    retTracked [[]]

/-- Uniform sample length for `stage2FinMFam S₂ M e δ`. -/
def stage2FinMLen (S₂ : Stage2Sampler) (M e δ : ℕ) : ℕ :=
  if 0 < M ∧ 1 ≤ e ∧ 1 ≤ δ then
    S₂.len (stage2BitLen M e) (2 * e) δ
  else
    0

/-- Polynomial degree `k` for `stage2FinMFam S₂`. -/
def stage2FinMK (S₂ : Stage2Sampler) : ℕ := 4 * S₂.k + 2

/-- Polynomial constant `c` for `stage2FinMFam S₂`. -/
def stage2FinMC (S₂ : Stage2Sampler) : ℕ :=
  6 * (S₂.c + 1) ^ 2 * 2304 ^ (S₂.k + 1)

@[simp]
lemma stage2FinMFamTracked_fst (S₂ : Stage2Sampler) (M e δ : ℕ) :
    (stage2FinMFamTracked S₂ M e δ).1 = stage2FinMFam S₂ M e δ := by
  unfold stage2FinMFamTracked stage2FinMFam
  split_ifs with h
  · simp [S₂.fam_eq]
  · rfl

lemma stage2FinM_len_eq (S₂ : Stage2Sampler) (M e δ : ℕ) :
    ∀ T ∈ stage2FinMFam S₂ M e δ, T.length = stage2FinMLen S₂ M e δ := by
  unfold stage2FinMFam stage2FinMLen
  split_ifs with h
  · intro T hT
    unfold modFinFam at hT
    rcases List.mem_map.mp hT with ⟨I, hI, rfl⟩
    rw [List.length_map]
    exact S₂.len_eq (stage2BitLen M e) (2 * e) δ I hI
  · intro T hT
    simp only [List.mem_singleton] at hT
    subst hT; rfl

lemma two_pow_stage2BitLen_le (M e : ℕ) :
    2 ^ stage2BitLen M e ≤ 4 * M * e + 2 := by
  unfold stage2BitLen
  rw [Nat.pow_succ]
  rcases Nat.eq_zero_or_pos (2 * M * e) with h0 | hpos
  · rw [h0]; simp
  · have hle := Nat.pow_log_le_self 2 hpos.ne'
    calc
      2 ^ Nat.log 2 (2 * M * e) * 2 ≤ (2 * M * e) * 2 := Nat.mul_le_mul_right 2 hle
      _ ≤ 4 * M * e + 2 := by ring_nf; omega

lemma stage2BitLen_add_one_le (M e : ℕ) (he : 1 ≤ e) :
    stage2BitLen M e + 1 ≤ 5 * ((Nat.log 2 M + 1) * e) := by
  unfold stage2BitLen
  have h1 : 2 ≤ 2 ^ 1 := le_rfl
  have h2 : M ≤ 2 ^ (Nat.log 2 M + 1) :=
    Nat.le_of_lt (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) M)
  have h3 : e ≤ 2 ^ e := Nat.le_of_lt Nat.lt_two_pow_self
  have hmul : 2 * M * e ≤ 2 ^ (1 + (Nat.log 2 M + 1) + e) := by
    calc
      2 * M * e ≤ 2 ^ 1 * 2 ^ (Nat.log 2 M + 1) * 2 ^ e :=
        Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
      _ = 2 ^ (1 + (Nat.log 2 M + 1) + e) := by rw [← Nat.pow_add, ← Nat.pow_add]
  have hlog : Nat.log 2 (2 * M * e) ≤ 1 + (Nat.log 2 M + 1) + e :=
    (Nat.log_mono_right hmul).trans_eq (Nat.log_pow (by norm_num) _)
  have hL_le : Nat.log 2 M + 1 ≤ (Nat.log 2 M + 1) * e :=
    Nat.le_mul_of_pos_right _ he
  have he_le : e ≤ (Nat.log 2 M + 1) * e :=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have h1_le : 1 ≤ (Nat.log 2 M + 1) * e :=
    Nat.mul_pos (Nat.succ_pos _) he
  omega

private lemma stage2FinM_raw_len_bound (S₂ : Stage2Sampler) (M e δ : ℕ) (he : 1 ≤ e) :
    S₂.len (stage2BitLen M e) (2 * e) δ ≤
      (S₂.c * 10 ^ S₂.k) * ((Nat.log 2 M + 1) * e * (Nat.log 2 δ + 1)) ^ (2 * S₂.k) := by
  set X := (Nat.log 2 M + 1) * e * (Nat.log 2 δ + 1)
  have hm_le := stage2BitLen_add_one_le M e he
  have h1 : stage2BitLen M e + 1 ≤ 5 * X := by
    calc
      stage2BitLen M e + 1 ≤ 5 * ((Nat.log 2 M + 1) * e) := hm_le
      _ ≤ 5 * ((Nat.log 2 M + 1) * e * (Nat.log 2 δ + 1)) :=
        Nat.mul_le_mul_left 5 (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  have h2 : 2 * e * (Nat.log 2 δ + 1) ≤ 2 * X := by
    dsimp [X]
    have : e * (Nat.log 2 δ + 1) ≤ (Nat.log 2 M + 1) * (e * (Nat.log 2 δ + 1)) :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    nlinarith
  have hprod : (stage2BitLen M e + 1) * (2 * e) * (Nat.log 2 δ + 1) ≤ 10 * X ^ 2 := by
    calc
      (stage2BitLen M e + 1) * (2 * e) * (Nat.log 2 δ + 1)
        = (stage2BitLen M e + 1) * (2 * e * (Nat.log 2 δ + 1)) := by ring
      _ ≤ (5 * X) * (2 * X) := Nat.mul_le_mul h1 h2
      _ = 10 * X ^ 2 := by ring
  calc
    S₂.len (stage2BitLen M e) (2 * e) δ
      ≤ S₂.c * ((stage2BitLen M e + 1) * (2 * e) * (Nat.log 2 δ + 1)) ^ S₂.k :=
        S₂.len_le _ _ _
    _ ≤ S₂.c * (10 * X ^ 2) ^ S₂.k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hprod S₂.k)
    _ = (S₂.c * 10 ^ S₂.k) * X ^ (2 * S₂.k) := by
        rw [Nat.mul_pow, ← Nat.pow_mul, ← mul_assoc]

lemma stage2FinM_len_le (S₂ : Stage2Sampler) (M e δ : ℕ) :
    stage2FinMLen S₂ M e δ ≤
      stage2FinMC S₂ * ((Nat.log 2 M + 1) * e * (Nat.log 2 δ + 1)) ^ stage2FinMK S₂ := by
  unfold stage2FinMLen
  split_ifs with h
  · set X := (Nat.log 2 M + 1) * e * (Nat.log 2 δ + 1)
    have hX_pos : 1 ≤ X :=
      Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) h.2.1) (Nat.succ_pos _)
    have hraw := stage2FinM_raw_len_bound S₂ M e δ h.2.1
    have hc_le : S₂.c * 10 ^ S₂.k ≤ stage2FinMC S₂ := by
      unfold stage2FinMC
      have h10 : 10 ^ S₂.k ≤ 2304 ^ (S₂.k + 1) :=
        (Nat.pow_le_pow_left (by norm_num) S₂.k).trans
          (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ S₂.k))
      have hc : S₂.c ≤ 6 * (S₂.c + 1) ^ 2 := by rw [sq]; nlinarith
      exact Nat.mul_le_mul hc h10
    have hk_le : X ^ (2 * S₂.k) ≤ X ^ stage2FinMK S₂ :=
      Nat.pow_le_pow_right hX_pos (by unfold stage2FinMK; omega)
    exact hraw.trans (Nat.mul_le_mul hc_le hk_le)
  · exact Nat.zero_le _

private lemma stage2FinM_pow_arg_le (M e δ : ℕ) (hM : 0 < M) (_he : 1 ≤ e) (hδ : 1 ≤ δ) :
    2 ^ stage2BitLen M e * (2 * e) * δ + 1 ≤ 13 * (M * e * δ + 1) ^ 2 := by
  set Y_arg := M * e * δ + 1
  have hY_pos : 1 ≤ Y_arg := Nat.succ_pos _
  have hMe_le : M * e ≤ M * e * δ := Nat.le_mul_of_pos_right _ hδ
  have heδ_le : e * δ ≤ M * e * δ := by
    calc
      e * δ = 1 * (e * δ) := by ring
      _ ≤ M * (e * δ) := Nat.mul_le_mul_right _ hM
      _ = M * e * δ := by ring
  have hpow := two_pow_stage2BitLen_le M e
  have h1 : 2 ^ stage2BitLen M e ≤ 6 * Y_arg := by
    calc
      2 ^ stage2BitLen M e ≤ 4 * (M * e) + 2 := by simpa [mul_assoc] using hpow
      _ ≤ 4 * (M * e * δ) + 2 := Nat.add_le_add_right (Nat.mul_le_mul_left 4 hMe_le) 2
      _ ≤ 6 * Y_arg := by dsimp [Y_arg]; omega
  have h2 : 2 * e * δ ≤ 2 * Y_arg := by
    calc
      2 * e * δ = 2 * (e * δ) := by ring
      _ ≤ 2 * (M * e * δ) := Nat.mul_le_mul_left 2 heδ_le
      _ ≤ 2 * Y_arg := by dsimp [Y_arg]; omega
  have h3 : 1 ≤ Y_arg ^ 2 := Nat.pow_pos hY_pos
  calc
    2 ^ stage2BitLen M e * (2 * e) * δ + 1
      = 2 ^ stage2BitLen M e * (2 * e * δ) + 1 := by ring
    _ ≤ (6 * Y_arg) * (2 * Y_arg) + Y_arg ^ 2 :=
      Nat.add_le_add (Nat.mul_le_mul h1 h2) h3
    _ = 13 * Y_arg ^ 2 := by ring

lemma stage2FinM_card_le (S₂ : Stage2Sampler) (M e δ : ℕ) :
    (stage2FinMFam S₂ M e δ).length ≤
      stage2FinMC S₂ * (M * e * δ + 1) ^ stage2FinMK S₂ := by
  set Y_arg := M * e * δ + 1
  have hY_pos : 1 ≤ Y_arg := Nat.succ_pos _
  unfold stage2FinMFam
  split_ifs with h
  · rw [modFinFam_length]
    set m := stage2BitLen M e
    have harg := stage2FinM_pow_arg_le M e δ h.1 h.2.1 h.2.2
    have hraw : (S₂.fam m (2 * e) δ).length ≤ (S₂.c * 13 ^ S₂.k) * Y_arg ^ (2 * S₂.k) := by
      calc
        (S₂.fam m (2 * e) δ).length
          ≤ S₂.c * (2 ^ m * (2 * e) * δ + 1) ^ S₂.k := S₂.card_le m (2 * e) δ
        _ ≤ S₂.c * (13 * Y_arg ^ 2) ^ S₂.k :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg S₂.k)
        _ = (S₂.c * 13 ^ S₂.k) * Y_arg ^ (2 * S₂.k) := by
          rw [Nat.mul_pow, ← Nat.pow_mul, ← mul_assoc]
    have hc_le : S₂.c * 13 ^ S₂.k ≤ stage2FinMC S₂ := by
      unfold stage2FinMC
      have h13 : 13 ^ S₂.k ≤ 2304 ^ (S₂.k + 1) :=
        (Nat.pow_le_pow_left (by norm_num) S₂.k).trans
          (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ S₂.k))
      have hc : S₂.c ≤ 6 * (S₂.c + 1) ^ 2 := by rw [sq]; nlinarith
      exact Nat.mul_le_mul hc h13
    have hk_le : Y_arg ^ (2 * S₂.k) ≤ Y_arg ^ stage2FinMK S₂ :=
      Nat.pow_le_pow_right hY_pos (by unfold stage2FinMK; omega)
    exact hraw.trans (Nat.mul_le_mul hc_le hk_le)
  · simp only [List.length_singleton]
    have hc_pos : 1 ≤ stage2FinMC S₂ := by
      unfold stage2FinMC
      exact Nat.mul_pos (Nat.mul_pos (by omega) (Nat.pow_pos (Nat.succ_pos _))) (by positivity)
    exact Nat.mul_pos hc_pos (Nat.one_le_pow _ _ hY_pos)

lemma stage2FinM_cost_le (S₂ : Stage2Sampler) (M e δ : ℕ) :
    (stage2FinMFamTracked S₂ M e δ).2 ≤
      stage2FinMC S₂ * (M * e * δ + 1) ^ stage2FinMK S₂ := by
  set Y_arg := M * e * δ + 1
  have hY_pos : 1 ≤ Y_arg := Nat.succ_pos _
  unfold stage2FinMFamTracked
  split_ifs with h
  · simp only [CostM.bind_snd, S₂.fam_eq]
    set m := stage2BitLen M e
    set fam_pow := S₂.fam m (2 * e) δ
    have harg := stage2FinM_pow_arg_le M e δ h.1 h.2.1 h.2.2
    have hcost_pow : (S₂.famTracked m (2 * e) δ).2 ≤ (S₂.c * 13 ^ S₂.k) * Y_arg ^ (2 * S₂.k) := by
      calc
        (S₂.famTracked m (2 * e) δ).2
          ≤ S₂.c * (2 ^ m * (2 * e) * δ + 1) ^ S₂.k := S₂.cost_le m (2 * e) δ
        _ ≤ S₂.c * (13 * Y_arg ^ 2) ^ S₂.k :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg S₂.k)
        _ = (S₂.c * 13 ^ S₂.k) * Y_arg ^ (2 * S₂.k) := by
          rw [Nat.mul_pow, ← Nat.pow_mul, ← mul_assoc]
    have hcard_pow : fam_pow.length ≤ (S₂.c * 13 ^ S₂.k) * Y_arg ^ (2 * S₂.k) := by
      calc
        fam_pow.length
          ≤ S₂.c * (2 ^ m * (2 * e) * δ + 1) ^ S₂.k := S₂.card_le m (2 * e) δ
        _ ≤ S₂.c * (13 * Y_arg ^ 2) ^ S₂.k :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg S₂.k)
        _ = (S₂.c * 13 ^ S₂.k) * Y_arg ^ (2 * S₂.k) := by
          rw [Nat.mul_pow, ← Nat.pow_mul, ← mul_assoc]
    have hX_le_4Y : (Nat.log 2 M + 1) * e * (Nat.log 2 δ + 1) ≤ 4 * Y_arg := by
      have hlogM : Nat.log 2 M + 1 ≤ 2 * M := by
        have := Nat.log_le_self 2 M; omega
      have hlogδ : Nat.log 2 δ + 1 ≤ 2 * δ := by
        have := Nat.log_le_self 2 δ; omega
      calc
        (Nat.log 2 M + 1) * e * (Nat.log 2 δ + 1)
          ≤ (2 * M) * e * (2 * δ) :=
            Nat.mul_le_mul (Nat.mul_le_mul_right e hlogM) hlogδ
        _ = 4 * (M * e * δ) := by ring
        _ ≤ 4 * Y_arg := Nat.mul_le_mul_left 4 (Nat.le_succ _)
    have hlen_pow : S₂.len m (2 * e) δ ≤ (S₂.c * 160 ^ S₂.k) * Y_arg ^ (2 * S₂.k) := by
      have hraw := stage2FinM_raw_len_bound S₂ M e δ h.2.1
      have hpow_X :
          ((Nat.log 2 M + 1) * e * (Nat.log 2 δ + 1)) ^ (2 * S₂.k) ≤
            16 ^ S₂.k * Y_arg ^ (2 * S₂.k) := by
        calc
          ((Nat.log 2 M + 1) * e * (Nat.log 2 δ + 1)) ^ (2 * S₂.k)
            ≤ (4 * Y_arg) ^ (2 * S₂.k) := Nat.pow_le_pow_left hX_le_4Y (2 * S₂.k)
          _ = (4 ^ 2) ^ S₂.k * Y_arg ^ (2 * S₂.k) := by
            rw [Nat.mul_pow, Nat.pow_mul]
          _ = 16 ^ S₂.k * Y_arg ^ (2 * S₂.k) := by norm_num
      calc
        S₂.len m (2 * e) δ
          ≤ (S₂.c * 10 ^ S₂.k) * (16 ^ S₂.k * Y_arg ^ (2 * S₂.k)) :=
            hraw.trans (Nat.mul_le_mul_left _ hpow_X)
        _ = S₂.c * (10 ^ S₂.k * 16 ^ S₂.k) * Y_arg ^ (2 * S₂.k) := by ring
        _ = (S₂.c * 160 ^ S₂.k) * Y_arg ^ (2 * S₂.k) := by
          rw [← Nat.mul_pow]
    have hmod := modFinFamTracked_snd_le M h.1 fam_pow (S₂.len m (2 * e) δ)
      (fun I hI => (S₂.len_eq m (2 * e) δ I hI).le)
    set C_base := (S₂.c + 1) ^ 2 * 2304 ^ (S₂.k + 1)
    have hC_pos : 1 ≤ C_base :=
      Nat.mul_pos (Nat.pow_pos (Nat.succ_pos _)) (by positivity)
    have h13_le : S₂.c * 13 ^ S₂.k ≤ C_base := by
      dsimp [C_base]
      have hc : S₂.c ≤ (S₂.c + 1) ^ 2 := by rw [sq]; nlinarith
      have hp : 13 ^ S₂.k ≤ 2304 ^ (S₂.k + 1) :=
        (Nat.pow_le_pow_left (by norm_num) S₂.k).trans
          (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ S₂.k))
      exact Nat.mul_le_mul hc hp
    have hmod_step : (Nat.log 2 (2 ^ m) + 2) * (Nat.log 2 M + 2) + 2 ≤ 7 * Y_arg ^ 2 := by
      have hMed_pos : 1 ≤ M * e * δ := Nat.mul_pos (Nat.mul_pos h.1 h.2.1) h.2.2
      have hMe_le : M * e ≤ M * e * δ := Nat.le_mul_of_pos_right _ h.2.2
      have hM_le : M ≤ M * e * δ := (Nat.le_mul_of_pos_right _ h.2.1).trans hMe_le
      have hlogK : Nat.log 2 (2 ^ m) + 2 ≤ 3 * Y_arg := by
        rw [Nat.log_pow (by norm_num)]
        dsimp [m, stage2BitLen, Y_arg]
        have hlog_le : Nat.log 2 (2 * M * e) ≤ 2 * (M * e * δ) := by
          calc
            Nat.log 2 (2 * M * e) ≤ 2 * M * e := Nat.log_le_self 2 (2 * M * e)
            _ = 2 * (M * e) := by ring
            _ ≤ 2 * (M * e * δ) := Nat.mul_le_mul_left 2 hMe_le
        omega
      have hlogM2 : Nat.log 2 M + 2 ≤ 2 * Y_arg := by
        dsimp [Y_arg]
        have := Nat.log_le_self 2 M
        omega
      have h2_le : 2 ≤ 1 * Y_arg ^ 2 := by
        rw [one_mul, sq]
        have : 2 ≤ Y_arg := by dsimp [Y_arg]; omega
        nlinarith
      calc
        (Nat.log 2 (2 ^ m) + 2) * (Nat.log 2 M + 2) + 2
          ≤ (3 * Y_arg) * (2 * Y_arg) + 1 * Y_arg ^ 2 :=
            Nat.add_le_add (Nat.mul_le_mul hlogK hlogM2) h2_le
        _ = 7 * Y_arg ^ 2 := by ring
    have h2len_le :
        S₂.len m (2 * e) δ * ((Nat.log 2 (2 ^ m) + 2) * (Nat.log 2 M + 2) + 2) + 2 ≤
          9 * (S₂.c + 1) * 160 ^ S₂.k * Y_arg ^ (2 * S₂.k + 2) := by
      have h1 : 1 ≤ 160 ^ S₂.k * Y_arg ^ (2 * S₂.k + 2) :=
        Nat.mul_pos (by positivity) (Nat.one_le_pow _ _ hY_pos)
      have h2 : 2 ≤ 2 * (160 ^ S₂.k * Y_arg ^ (2 * S₂.k + 2)) :=
        Nat.le_mul_of_pos_right 2 h1
      have hmul_len :
          S₂.len m (2 * e) δ * ((Nat.log 2 (2 ^ m) + 2) * (Nat.log 2 M + 2) + 2) ≤
            7 * S₂.c * 160 ^ S₂.k * Y_arg ^ (2 * S₂.k + 2) := by
        calc
          S₂.len m (2 * e) δ * ((Nat.log 2 (2 ^ m) + 2) * (Nat.log 2 M + 2) + 2)
            ≤ ((S₂.c * 160 ^ S₂.k) * Y_arg ^ (2 * S₂.k)) * (7 * Y_arg ^ 2) :=
              Nat.mul_le_mul hlen_pow hmod_step
          _ = 7 * S₂.c * 160 ^ S₂.k * (Y_arg ^ (2 * S₂.k) * Y_arg ^ 2) := by ring
          _ = 7 * S₂.c * 160 ^ S₂.k * Y_arg ^ (2 * S₂.k + 2) := by rw [← Nat.pow_add]
      calc
        S₂.len m (2 * e) δ * ((Nat.log 2 (2 ^ m) + 2) * (Nat.log 2 M + 2) + 2) + 2
          ≤ 7 * S₂.c * 160 ^ S₂.k * Y_arg ^ (2 * S₂.k + 2) +
              2 * (160 ^ S₂.k * Y_arg ^ (2 * S₂.k + 2)) :=
            Nat.add_le_add hmul_len h2
        _ ≤ 9 * (S₂.c + 1) * 160 ^ S₂.k * Y_arg ^ (2 * S₂.k + 2) := by
            have : 7 * S₂.c + 2 ≤ 9 * (S₂.c + 1) := by omega
            calc
              7 * S₂.c * 160 ^ S₂.k * Y_arg ^ (2 * S₂.k + 2) +
                  2 * (160 ^ S₂.k * Y_arg ^ (2 * S₂.k + 2))
                = (7 * S₂.c + 2) * (160 ^ S₂.k * Y_arg ^ (2 * S₂.k + 2)) := by ring
              _ ≤ 9 * (S₂.c + 1) * (160 ^ S₂.k * Y_arg ^ (2 * S₂.k + 2)) :=
                Nat.mul_le_mul_right _ this
              _ = 9 * (S₂.c + 1) * 160 ^ S₂.k * Y_arg ^ (2 * S₂.k + 2) := by ring
    have hprod_mod :
        fam_pow.length * (S₂.len m (2 * e) δ * ((Nat.log 2 (2 ^ m) + 2) * (Nat.log 2 M + 2) + 2) + 2) ≤
          4 * C_base * Y_arg ^ stage2FinMK S₂ := by
      have hcoeff :
          (S₂.c * 13 ^ S₂.k) * (9 * (S₂.c + 1) * 160 ^ S₂.k) ≤ 4 * C_base := by
        have hc : S₂.c * (S₂.c + 1) ≤ (S₂.c + 1) ^ 2 := by rw [sq]; nlinarith
        have hp : 9 * (13 ^ S₂.k * 160 ^ S₂.k) ≤ 4 * 2304 ^ (S₂.k + 1) := by
          rw [← Nat.mul_pow, Nat.pow_succ]
          have h2080 : (13 * 160) ^ S₂.k ≤ 2304 ^ S₂.k := Nat.pow_le_pow_left (by norm_num) S₂.k
          calc
            9 * (13 * 160) ^ S₂.k ≤ 9 * 2304 ^ S₂.k := Nat.mul_le_mul_left 9 h2080
            _ ≤ (4 * 2304) * 2304 ^ S₂.k := Nat.mul_le_mul_right _ (by norm_num)
            _ = 4 * (2304 ^ S₂.k * 2304) := by ring
        calc
          (S₂.c * 13 ^ S₂.k) * (9 * (S₂.c + 1) * 160 ^ S₂.k)
            = (S₂.c * (S₂.c + 1)) * (9 * (13 ^ S₂.k * 160 ^ S₂.k)) := by ring
          _ ≤ (S₂.c + 1) ^ 2 * (4 * 2304 ^ (S₂.k + 1)) :=
            Nat.mul_le_mul hc hp
          _ = 4 * C_base := by dsimp [C_base]; ring
      calc
        fam_pow.length * (S₂.len m (2 * e) δ * ((Nat.log 2 (2 ^ m) + 2) * (Nat.log 2 M + 2) + 2) + 2)
          ≤ ((S₂.c * 13 ^ S₂.k) * Y_arg ^ (2 * S₂.k)) *
              (9 * (S₂.c + 1) * 160 ^ S₂.k * Y_arg ^ (2 * S₂.k + 2)) :=
            Nat.mul_le_mul hcard_pow h2len_le
        _ = ((S₂.c * 13 ^ S₂.k) * (9 * (S₂.c + 1) * 160 ^ S₂.k)) *
              (Y_arg ^ (2 * S₂.k) * Y_arg ^ (2 * S₂.k + 2)) := by ring
        _ = ((S₂.c * 13 ^ S₂.k) * (9 * (S₂.c + 1) * 160 ^ S₂.k)) *
              Y_arg ^ stage2FinMK S₂ := by
          rw [← Nat.pow_add]
          congr 2
          unfold stage2FinMK
          omega
        _ ≤ (4 * C_base) * Y_arg ^ stage2FinMK S₂ := Nat.mul_le_mul_right _ hcoeff
    have hpow24 : Y_arg ^ (2 * S₂.k) ≤ Y_arg ^ stage2FinMK S₂ :=
      Nat.pow_le_pow_right hY_pos (by unfold stage2FinMK; omega)
    have hterm1 : (S₂.famTracked m (2 * e) δ).2 ≤ C_base * Y_arg ^ stage2FinMK S₂ :=
      hcost_pow.trans (Nat.mul_le_mul h13_le hpow24)
    have hterm2 :
        (modFinFamTracked M h.1 fam_pow).2 ≤ 5 * C_base * Y_arg ^ stage2FinMK S₂ := by
      have h1 : 1 ≤ C_base * Y_arg ^ stage2FinMK S₂ :=
        Nat.mul_pos hC_pos (Nat.one_le_pow _ _ hY_pos)
      calc
        (modFinFamTracked M h.1 fam_pow).2
          ≤ fam_pow.length * (S₂.len m (2 * e) δ * ((Nat.log 2 (2 ^ m) + 2) * (Nat.log 2 M + 2) + 2) + 2) + 1 := hmod
        _ ≤ 4 * C_base * Y_arg ^ stage2FinMK S₂ + C_base * Y_arg ^ stage2FinMK S₂ :=
          Nat.add_le_add hprod_mod h1
        _ = 5 * C_base * Y_arg ^ stage2FinMK S₂ := by ring
    calc
      (S₂.famTracked m (2 * e) δ).2 + (modFinFamTracked M h.1 fam_pow).2
        ≤ C_base * Y_arg ^ stage2FinMK S₂ + 5 * C_base * Y_arg ^ stage2FinMK S₂ :=
          Nat.add_le_add hterm1 hterm2
      _ = stage2FinMC S₂ * Y_arg ^ stage2FinMK S₂ := by
        unfold stage2FinMC; dsimp [C_base]; ring
  · rw [retTracked_snd]
    have hc_pos : 1 ≤ stage2FinMC S₂ := by
      unfold stage2FinMC
      exact Nat.mul_pos (Nat.mul_pos (by omega) (Nat.pow_pos (Nat.succ_pos _))) (by positivity)
    exact Nat.mul_pos hc_pos (Nat.one_le_pow _ _ hY_pos)

/-- **Machine-Checked Reduction from `Stage2Sampler` on `Fin (2 ^ m)` to Arbitrary `Fin M`
(`stage2FinM_sampler`)**:
For any `S₂ : Stage2Sampler` and any `M ≥ 1`, `e ≥ 1`, `δ ≥ 1`, `stage2FinMFam S₂ M e δ` is a
`(1 / e, 1 / δ)`-sequence sampler on `Fin M`. -/
theorem stage2FinM_sampler (S₂ : Stage2Sampler) (M e δ : ℕ)
    (hM : 1 ≤ M) (he : 1 ≤ e) (hδ : 1 ≤ δ) :
    IsSeqSampler (Finset.univ : Finset (Fin M)) (stage2FinMFam S₂ M e δ)
      (1 / (e : ℝ)) (1 / (δ : ℝ)) := by
  have hcond : 0 < M ∧ 1 ≤ e ∧ 1 ≤ δ := ⟨by omega, he, hδ⟩
  unfold stage2FinMFam
  rw [dif_pos hcond]
  set m := stage2BitLen M e
  have h2e : 1 ≤ 2 * e := by omega
  have hS₂ := S₂.sampler m (2 * e) δ h2e hδ
  have hpow_gt : 2 * M * e < 2 ^ m :=
    Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (2 * M * e)
  have hbias : (M : ℝ) / ((2 ^ m : ℕ) : ℝ) ≤ 1 / ((2 * e : ℕ) : ℝ) := by
    have h2e_pos : (0 : ℝ) < ((2 * e : ℕ) : ℝ) := by positivity
    have h2m_pos : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ) := by positivity
    rw [div_le_div_iff₀ h2m_pos h2e_pos, one_mul]
    have hnat : M * (2 * e) ≤ 2 ^ m := by
      rw [show M * (2 * e) = 2 * M * e by ring]
      exact hpow_gt.le
    exact_mod_cast hnat
  have hmod := isSeqSampler_modFinFam (by omega : 0 < M) (Nat.two_pow_pos m) hS₂ hbias
  have he_sum :
      (1 : ℝ) / ((2 * e : ℕ) : ℝ) + (1 : ℝ) / ((2 * e : ℕ) : ℝ) = (1 : ℝ) / (e : ℝ) := by
    have he_ne : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    push_cast
    field_simp [he_ne]
    ring
  rwa [he_sum] at hmod

/-- Combined polynomial degree `k` for the two-stage composition of `S₁ : Stage1Sampler` and
`S₂ : Stage2Sampler`. -/
def twoStageConstK (S₁ : Stage1Sampler) (S₂ : Stage2Sampler) : ℕ :=
  2 * S₁.k + (S₁.k + 2) * stage2FinMK S₂

/-- Combined polynomial constant `c` for the two-stage composition of `S₁ : Stage1Sampler` and
`S₂ : Stage2Sampler`. -/
def twoStageConstC (S₁ : Stage1Sampler) (S₂ : Stage2Sampler) : ℕ :=
  24 * ((S₁.c + 1) * (S₁.k + 1) ^ S₁.k * 4 ^ S₁.k) ^ 2 *
    (stage2FinMC S₂ + 1) * (4 * (S₁.c + 3 * S₁.k + 1) * 4 ^ (S₁.k + 1)) ^ stage2FinMK S₂

/-- Polylogarithmic absorption bound: for all $N, k \in \mathbb{N}$,
$(\lfloor \log_2 N \rfloor + 1)^k \le (k + 1)^k \cdot (N + 1)$. -/
lemma nat_log2_add_one_pow_le (N k : ℕ) :
    (Nat.log 2 N + 1) ^ k ≤ (k + 1) ^ k * (N + 1) := by
  set L := Nat.log 2 N
  set q := L / (k + 1)
  have hdiv : L + 1 ≤ (k + 1) * (q + 1) := by
    have h1 : (k + 1) * q + L % (k + 1) = L := Nat.div_add_mod L (k + 1)
    have h2 : L % (k + 1) + 1 ≤ k + 1 := Nat.succ_le_of_lt (Nat.mod_lt L (Nat.succ_pos k))
    calc
      L + 1 = (k + 1) * q + (L % (k + 1) + 1) := by omega
      _ ≤ (k + 1) * q + (k + 1) := Nat.add_le_add_left h2 _
      _ = (k + 1) * (q + 1) := by ring
  have hq : q + 1 ≤ 2 ^ q := Nat.succ_le_of_lt Nat.lt_two_pow_self
  have hL_le : L + 1 ≤ (k + 1) * 2 ^ q := hdiv.trans (Nat.mul_le_mul_left (k + 1) hq)
  have hpow := Nat.pow_le_pow_left hL_le k
  rw [Nat.mul_pow, ← Nat.pow_mul] at hpow
  have hqk : q * k ≤ L :=
    (Nat.mul_le_mul_left q (Nat.le_succ k)).trans (Nat.div_mul_le_self L (k + 1))
  have h2qk : 2 ^ (q * k) ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hqk
  have h2L : 2 ^ L ≤ N + 1 := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [L]
    · exact (Nat.pow_log_le_self 2 hN.ne').trans (Nat.le_succ N)
  exact hpow.trans (Nat.mul_le_mul_left _ (h2qk.trans h2L))

/-- For `0 < N` and `1 ≤ invEps`, the Stage-1 family `S₁.fam N (2 * invEps) (2 * 2 ^ logInvDelta)`
is non-empty, so the length of its head sequence
`((S₁.fam N (2 * invEps) (2 * 2 ^ logInvDelta)).headD []).length` equals
`S₁.len N (2 * invEps) (2 * 2 ^ logInvDelta)`. -/
lemma stage1_headD_length_eq (S₁ : Stage1Sampler) {N invEps : ℕ}
    (hN : 0 < N) (hinv : 1 ≤ invEps) (logInvDelta : ℕ) :
    ((S₁.fam N (2 * invEps) (2 * 2 ^ logInvDelta)).headD []).length =
      S₁.len N (2 * invEps) (2 * 2 ^ logInvDelta) := by
  have he₂ : 1 ≤ 2 * invEps := by omega
  have hδ₂ : 1 ≤ 2 * 2 ^ logInvDelta := Nat.mul_pos (by decide) Nat.one_le_two_pow
  have hne : S₁.fam N (2 * invEps) (2 * 2 ^ logInvDelta) ≠ [] :=
    (S₁.sampler N (2 * invEps) (2 * 2 ^ logInvDelta) hN he₂ hδ₂).1
  cases hlist : S₁.fam N (2 * invEps) (2 * 2 ^ logInvDelta) with
  | nil => exact absurd hlist hne
  | cons T₀ tl =>
    simp only [List.headD_cons]
    exact S₁.len_eq N (2 * invEps) (2 * 2 ^ logInvDelta) T₀ (hlist ▸ List.mem_cons_self)

/-- Pure two-stage composed family on `Y : Finset β` constructed from `S₁ : Stage1Sampler` and
`S₂ : Stage2Sampler` at parameters `(invEps, logInvDelta)`. -/
noncomputable def twoStageConstruct (S₁ : Stage1Sampler) (S₂ : Stage2Sampler)
    (Y : Finset β) (invEps logInvDelta : ℕ) : List (List β) :=
  if h : 0 < Y.card ∧ 1 ≤ invEps then
    let e₂ := 2 * invEps
    let δ₂ := 2 * 2 ^ logInvDelta
    let fam₁_idx := S₁.fam Y.card e₂ δ₂
    let M := (fam₁_idx.headD []).length
    let y₀ := indexFinset Y ⟨0, h.1⟩
    let fam₁ := transportFam Y fam₁_idx
    let fam₂ := stage2FinMFam S₂ M e₂ δ₂
    composeFamilies y₀ fam₁ fam₂
  else
    [[]]

/-- Cost-tracked two-stage composed family constructor in `CostM`, binding `S₁.famTracked`,
`stage2FinMFamTracked S₂` (which binds `S₂.famTracked` and `modFinFamTracked`),
`transportFamTracked`, and `composeFamiliesTracked` so that both the Stage-1/2
oracle calls and the full materialization of `modFinFam`, `transportFam`, and `composeFamilies`
are executed and charged in `CostM`. -/
noncomputable def twoStageConstructTracked (S₁ : Stage1Sampler) (S₂ : Stage2Sampler)
    (Y : Finset β) (invEps logInvDelta : ℕ) : CostM (List (List β)) :=
  if h : 0 < Y.card ∧ 1 ≤ invEps then
    let e₂ := 2 * invEps
    let δ₂ := 2 * 2 ^ logInvDelta
    let y₀ := indexFinset Y ⟨0, h.1⟩
    CostM.bind (S₁.famTracked Y.card e₂ δ₂) (fun fam₁_idx =>
      let M := (fam₁_idx.headD []).length
      CostM.bind (stage2FinMFamTracked S₂ M e₂ δ₂) (fun fam₂ =>
        CostM.bind (transportFamTracked Y fam₁_idx) (fun fam₁ =>
          composeFamiliesTracked y₀ fam₁ fam₂)))
  else
    retTracked [[]]

@[simp]
lemma twoStageConstructTracked_fst (S₁ : Stage1Sampler) (S₂ : Stage2Sampler)
    (Y : Finset β) (invEps logInvDelta : ℕ) :
    (twoStageConstructTracked S₁ S₂ Y invEps logInvDelta).1 =
      twoStageConstruct S₁ S₂ Y invEps logInvDelta := by
  unfold twoStageConstructTracked twoStageConstruct
  split_ifs with h
  · simp only [CostM.bind_fst, stage2FinMFamTracked_fst, transportFamTracked_fst,
      composeFamiliesTracked_fst]
    rw [S₁.fam_eq]
  · rfl

theorem twoStageConstruct_len_eq (S₁ : Stage1Sampler) (S₂ : Stage2Sampler)
    (Y : Finset β) (invEps logInvDelta : ℕ) :
    let T_fam := twoStageConstruct S₁ S₂ Y invEps logInvDelta
    ∀ T ∈ T_fam, T.length = (T_fam.headD []).length := by
  intro T_fam
  have hunif : ∃ L : ℕ, ∀ T ∈ T_fam, T.length = L := by
    dsimp [T_fam, twoStageConstruct]
    split_ifs with h
    · rw [stage1_headD_length_eq S₁ h.1 h.2 logInvDelta]
      refine ⟨stage2FinMLen S₂ (S₁.len Y.card (2 * invEps) (2 * 2 ^ logInvDelta))
        (2 * invEps) (2 * 2 ^ logInvDelta), ?_⟩
      intro T hT
      unfold composeFamilies at hT
      rcases List.mem_flatMap.mp hT with ⟨T₁, _, hT₂⟩
      rcases List.mem_map.mp hT₂ with ⟨I₂, hI₂, rfl⟩
      rw [lookupSeq_length, stage2FinM_len_eq S₂ _ _ _ I₂ hI₂]
    · refine ⟨0, fun T hT => ?_⟩
      simp only [List.mem_singleton] at hT
      subst hT; rfl
  rcases hunif with ⟨L, hL⟩
  intro T hT
  cases hlist : T_fam with
  | nil => rw [hlist] at hT; cases hT
  | cons T₀ tl =>
    have hT₀ : T₀ ∈ T_fam := hlist ▸ List.mem_cons_self
    simp only [List.headD_cons]
    rw [hL T hT, hL T₀ hT₀]

/-- Stage-2 sequence length bound at the composed Stage-1 buffer size
`M = S₁.len N (2 * invEps) (2 * 2 ^ logInvDelta)`. -/
lemma twoStage_S2_len_le (S₁ : Stage1Sampler) (S₂ : Stage2Sampler)
    (N invEps logInvDelta : ℕ) :
    stage2FinMLen S₂ (S₁.len N (2 * invEps) (2 * 2 ^ logInvDelta)) (2 * invEps) (2 * 2 ^ logInvDelta) ≤
      twoStageSampleSizeBound (twoStageConstC S₁ S₂) (twoStageConstK S₁ S₂)
        invEps logInvDelta := by
  set c₂ := stage2FinMC S₂
  set k₂ := stage2FinMK S₂
  set c := twoStageConstC S₁ S₂
  set k := twoStageConstK S₁ S₂
  set invDelta := 2 ^ logInvDelta
  set Q := (invEps + 1) * (logInvDelta + 1)
  have hQ_pos : 1 ≤ Q := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  set e₂ := 2 * invEps
  set δ₂ := 2 * invDelta
  set M := S₁.len N e₂ δ₂
  have heδ_pow : e₂ * δ₂ + 1 ≤ 2 ^ (invEps + logInvDelta + 3) := by
    have h1 : invEps ≤ 2 ^ invEps := Nat.le_of_lt Nat.lt_two_pow_self
    have h2 : 4 * invEps * 2 ^ logInvDelta ≤ 2 ^ 2 * 2 ^ invEps * 2 ^ logInvDelta :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 h1)
    have h3 : 2 ^ 2 * 2 ^ invEps * 2 ^ logInvDelta = 2 ^ (invEps + logInvDelta + 2) := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
    have h4 : 1 ≤ 2 ^ (invEps + logInvDelta + 2) := Nat.one_le_two_pow
    have h5 : 2 ^ (invEps + logInvDelta + 3) =
        2 ^ (invEps + logInvDelta + 2) + 2 ^ (invEps + logInvDelta + 2) := by
      rw [Nat.pow_succ]; ring
    dsimp [e₂, δ₂, invDelta]
    linarith
  have hM_pow : M ≤ 2 ^ (S₁.c + S₁.k * (invEps + logInvDelta + 3)) := by
    have h1 : S₁.c ≤ 2 ^ S₁.c := Nat.le_of_lt Nat.lt_two_pow_self
    have h2 : (e₂ * δ₂ + 1) ^ S₁.k ≤ 2 ^ (S₁.k * (invEps + logInvDelta + 3)) := by
      calc
        (e₂ * δ₂ + 1) ^ S₁.k ≤ (2 ^ (invEps + logInvDelta + 3)) ^ S₁.k :=
          Nat.pow_le_pow_left heδ_pow S₁.k
        _ = 2 ^ (S₁.k * (invEps + logInvDelta + 3)) := by
          rw [← Nat.pow_mul, mul_comm]
    calc
      M ≤ S₁.c * (e₂ * δ₂ + 1) ^ S₁.k := S₁.len_le N e₂ δ₂
      _ ≤ 2 ^ S₁.c * 2 ^ (S₁.k * (invEps + logInvDelta + 3)) := Nat.mul_le_mul h1 h2
      _ = 2 ^ (S₁.c + S₁.k * (invEps + logInvDelta + 3)) := (Nat.pow_add _ _ _).symm
  have hlogM : Nat.log 2 M + 1 ≤ (S₁.c + 3 * S₁.k + 1) * Q := by
    have h1 : Nat.log 2 M ≤ S₁.c + S₁.k * (invEps + logInvDelta + 3) :=
      (Nat.log_mono_right hM_pow).trans_eq (Nat.log_pow (by norm_num) _)
    have h2 : invEps + logInvDelta + 3 ≤ 3 * Q := by dsimp [Q]; nlinarith
    nlinarith
  have hlogδ₂ : e₂ * (Nat.log 2 δ₂ + 1) ≤ 4 * Q := by
    have hδ_eq : δ₂ = 2 ^ (logInvDelta + 1) := by
      dsimp [δ₂, invDelta]; rw [Nat.pow_succ, mul_comm]
    have hlg : Nat.log 2 δ₂ = logInvDelta + 1 := by
      rw [hδ_eq, Nat.log_pow (by norm_num)]
    rw [hlg]
    dsimp [e₂, Q]
    nlinarith
  have hprod_Q :
      (Nat.log 2 M + 1) * e₂ * (Nat.log 2 δ₂ + 1) ≤
        4 * (S₁.c + 3 * S₁.k + 1) * Q ^ 2 := by
    calc
      (Nat.log 2 M + 1) * e₂ * (Nat.log 2 δ₂ + 1)
        = (Nat.log 2 M + 1) * (e₂ * (Nat.log 2 δ₂ + 1)) := by ring
      _ ≤ ((S₁.c + 3 * S₁.k + 1) * Q) * (4 * Q) := Nat.mul_le_mul hlogM hlogδ₂
      _ = 4 * (S₁.c + 3 * S₁.k + 1) * Q ^ 2 := by ring
  have hc2_le : c₂ * (4 * (S₁.c + 3 * S₁.k + 1)) ^ k₂ ≤ c + 1 := by
    have hbase :
        4 * (S₁.c + 3 * S₁.k + 1) ≤ 4 * (S₁.c + 3 * S₁.k + 1) * 4 ^ (S₁.k + 1) :=
      Nat.le_mul_of_pos_right _ (by positivity)
    have hpow_base := Nat.pow_le_pow_left hbase k₂
    have hA₁_pos : 1 ≤ (S₁.c + 1) * (S₁.k + 1) ^ S₁.k * 4 ^ S₁.k :=
      Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.one_le_pow _ _ (Nat.succ_pos _))) (by positivity)
    have hfront : 1 ≤ 24 * ((S₁.c + 1) * (S₁.k + 1) ^ S₁.k * 4 ^ S₁.k) ^ 2 :=
      Nat.mul_pos (by omega) (Nat.pow_pos hA₁_pos)
    have hmul := Nat.mul_le_mul hfront
      (Nat.mul_le_mul (Nat.le_succ c₂) hpow_base)
    rw [one_mul] at hmul
    have heq_c :
        (24 * ((S₁.c + 1) * (S₁.k + 1) ^ S₁.k * 4 ^ S₁.k) ^ 2) *
          ((c₂ + 1) * (4 * (S₁.c + 3 * S₁.k + 1) * 4 ^ (S₁.k + 1)) ^ k₂) = c := by
      dsimp [c, twoStageConstC, c₂, k₂]; ring
    rw [heq_c] at hmul
    exact hmul.trans (Nat.le_succ c)
  have hk2_le : 2 * k₂ ≤ k + 2 := by
    dsimp [k, twoStageConstK, k₂]
    calc
      2 * k₂ ≤ (S₁.k + 2) * k₂ := Nat.mul_le_mul_right _ (by omega)
      _ ≤ 2 * S₁.k + (S₁.k + 2) * k₂ + 2 := by omega
  have hQ_pow : (Q ^ 2) ^ k₂ ≤ Q ^ (k + 2) := by
    rw [← Nat.pow_mul]
    exact Nat.pow_le_pow_right hQ_pos hk2_le
  calc
    stage2FinMLen S₂ M e₂ δ₂
      ≤ c₂ * ((Nat.log 2 M + 1) * e₂ * (Nat.log 2 δ₂ + 1)) ^ k₂ := stage2FinM_len_le S₂ M e₂ δ₂
    _ ≤ c₂ * (4 * (S₁.c + 3 * S₁.k + 1) * Q ^ 2) ^ k₂ :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hprod_Q k₂)
    _ = (c₂ * (4 * (S₁.c + 3 * S₁.k + 1)) ^ k₂) * (Q ^ 2) ^ k₂ := by
        rw [Nat.mul_pow]; ring
    _ ≤ (c + 1) * Q ^ (k + 2) := Nat.mul_le_mul hc2_le hQ_pow
    _ = twoStageSampleSizeBound c k invEps logInvDelta := rfl

theorem twoStageConstruct_satisfies_bounds (S₁ : Stage1Sampler) (S₂ : Stage2Sampler)
    (Y : Finset β) (invEps logInvDelta : ℕ) :
    SatisfiesTwoStageBounds (twoStageConstC S₁ S₂) (twoStageConstK S₁ S₂)
       Y (twoStageConstruct S₁ S₂ Y invEps logInvDelta)
       invEps (2 ^ logInvDelta) logInvDelta := by
  set c₂ := stage2FinMC S₂
  set k₂ := stage2FinMK S₂
  set c := twoStageConstC S₁ S₂
  set k := twoStageConstK S₁ S₂
  set invDelta := 2 ^ logInvDelta
  set P := (invEps + 1) * (invDelta + 1)
  have hP_pos : 1 ≤ P := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  unfold SatisfiesTwoStageBounds twoStageConstruct
  split_ifs with h
  · dsimp only
    rw [stage1_headD_length_eq S₁ h.1 h.2 logInvDelta]
    set N := Y.card
    set e₂ := 2 * invEps
    set δ₂ := 2 * invDelta
    set M := S₁.len N e₂ δ₂
    have heδ : e₂ * δ₂ + 1 ≤ 4 * P := by
      dsimp [e₂, δ₂, P]; nlinarith
    have hM_le_P : M ≤ S₁.c * 4 ^ S₁.k * P ^ S₁.k := by
      calc
        M ≤ S₁.c * (e₂ * δ₂ + 1) ^ S₁.k := S₁.len_le N e₂ δ₂
        _ ≤ S₁.c * (4 * P) ^ S₁.k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left heδ S₁.k)
        _ = S₁.c * 4 ^ S₁.k * P ^ S₁.k := by rw [Nat.mul_pow]; ring
    refine ⟨?_, ?_⟩
    · rw [composeFamilies_length, transportFam_length]
      have hcard1 : (S₁.fam N e₂ δ₂).length ≤ N * S₁.c * 4 ^ S₁.k * P ^ S₁.k := by
        calc
          (S₁.fam N e₂ δ₂).length ≤ N * S₁.c * (e₂ * δ₂ + 1) ^ S₁.k := S₁.card_le N e₂ δ₂
          _ ≤ N * S₁.c * (4 * P) ^ S₁.k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left heδ S₁.k)
          _ = N * S₁.c * 4 ^ S₁.k * P ^ S₁.k := by rw [Nat.mul_pow]; ring
      have hMeδ : M * e₂ * δ₂ + 1 ≤ (S₁.c + 1) * 4 ^ (S₁.k + 1) * P ^ (S₁.k + 1) := by
        have h1 : e₂ * δ₂ ≤ 4 * P := by dsimp [e₂, δ₂, P]; nlinarith
        have h2 : M * (e₂ * δ₂) ≤ (S₁.c * 4 ^ S₁.k * P ^ S₁.k) * (4 * P) :=
          Nat.mul_le_mul hM_le_P h1
        have h3 : (S₁.c * 4 ^ S₁.k * P ^ S₁.k) * (4 * P) + 1 ≤
            (S₁.c + 1) * 4 ^ (S₁.k + 1) * P ^ (S₁.k + 1) := by
          have hpos4P : 1 ≤ 4 ^ (S₁.k + 1) * P ^ (S₁.k + 1) :=
            Nat.mul_pos (by positivity) (Nat.one_le_pow _ _ hP_pos)
          have heqL : (S₁.c * 4 ^ S₁.k * P ^ S₁.k) * (4 * P) =
              S₁.c * (4 ^ (S₁.k + 1) * P ^ (S₁.k + 1)) := by
            rw [Nat.pow_succ 4 S₁.k, Nat.pow_succ P S₁.k]; ring
          have heqR : (S₁.c + 1) * 4 ^ (S₁.k + 1) * P ^ (S₁.k + 1) =
              S₁.c * (4 ^ (S₁.k + 1) * P ^ (S₁.k + 1)) + 4 ^ (S₁.k + 1) * P ^ (S₁.k + 1) := by
            ring
          rw [heqL, heqR]
          exact Nat.add_le_add_left hpos4P _
        calc
          M * e₂ * δ₂ + 1 = M * (e₂ * δ₂) + 1 := by ring
          _ ≤ (S₁.c * 4 ^ S₁.k * P ^ S₁.k) * (4 * P) + 1 := Nat.add_le_add_right h2 1
          _ ≤ (S₁.c + 1) * 4 ^ (S₁.k + 1) * P ^ (S₁.k + 1) := h3
      have hcard2 :
          (stage2FinMFam S₂ M e₂ δ₂).length ≤
            c₂ * ((S₁.c + 1) * 4 ^ (S₁.k + 1)) ^ k₂ * P ^ ((S₁.k + 1) * k₂) := by
        calc
          (stage2FinMFam S₂ M e₂ δ₂).length ≤ c₂ * (M * e₂ * δ₂ + 1) ^ k₂ :=
            stage2FinM_card_le S₂ M e₂ δ₂
          _ ≤ c₂ * ((S₁.c + 1) * 4 ^ (S₁.k + 1) * P ^ (S₁.k + 1)) ^ k₂ :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hMeδ k₂)
          _ = c₂ * ((S₁.c + 1) * 4 ^ (S₁.k + 1)) ^ k₂ * P ^ ((S₁.k + 1) * k₂) := by
            rw [Nat.mul_pow, ← Nat.pow_mul]; ring
      have hc_le :
          S₁.c * 4 ^ S₁.k * (c₂ * ((S₁.c + 1) * 4 ^ (S₁.k + 1)) ^ k₂) ≤ c + 1 := by
        set A₁ := (S₁.c + 1) * (S₁.k + 1) ^ S₁.k * 4 ^ S₁.k
        have hA₁_pos : 1 ≤ A₁ :=
          Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.one_le_pow _ _ (Nat.succ_pos _)))
            (by positivity)
        have hbase :
            (S₁.c + 1) * 4 ^ (S₁.k + 1) ≤ 4 * (S₁.c + 3 * S₁.k + 1) * 4 ^ (S₁.k + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        have hpow_base := Nat.pow_le_pow_left hbase k₂
        have h1 : S₁.c * 4 ^ S₁.k ≤ 24 * A₁ ^ 2 := by
          have hk_pos : 1 ≤ (S₁.k + 1) ^ S₁.k := Nat.one_le_pow _ _ (Nat.succ_pos _)
          have hleA : S₁.c * 4 ^ S₁.k ≤ A₁ := by
            dsimp [A₁]
            calc
              S₁.c * 4 ^ S₁.k = (S₁.c * 1) * 4 ^ S₁.k := by ring
              _ ≤ ((S₁.c + 1) * (S₁.k + 1) ^ S₁.k) * 4 ^ S₁.k :=
                Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.le_succ _) hk_pos)
          have hA_sq : A₁ ≤ 24 * A₁ ^ 2 := by
            rw [sq]
            calc
              A₁ = 1 * (A₁ * 1) := by ring
              _ ≤ 24 * (A₁ * A₁) :=
                Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ hA₁_pos)
          exact hleA.trans hA_sq
        have h2 : c₂ ≤ c₂ + 1 := Nat.le_succ _
        have hmul := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 hpow_base)
        have heq_c :
            (24 * A₁ ^ 2) *
              ((c₂ + 1) * (4 * (S₁.c + 3 * S₁.k + 1) * 4 ^ (S₁.k + 1)) ^ k₂) = c := by
          dsimp [c, twoStageConstC, A₁, c₂, k₂]; ring
        rw [heq_c] at hmul
        exact hmul.trans (Nat.le_succ c)
      have hk_le : S₁.k + (S₁.k + 1) * k₂ ≤ k + 2 := by
        dsimp [k, twoStageConstK, k₂]
        have : (S₁.k + 1) * stage2FinMK S₂ ≤ (S₁.k + 2) * stage2FinMK S₂ :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      have hP_pow : P ^ S₁.k * P ^ ((S₁.k + 1) * k₂) ≤ P ^ (k + 2) := by
        rw [← Nat.pow_add]
        exact Nat.pow_le_pow_right hP_pos hk_le
      have hN_max : N ≤ max 1 N := le_max_right 1 N
      calc
        (S₁.fam N e₂ δ₂).length * (stage2FinMFam S₂ M e₂ δ₂).length
          ≤ (N * S₁.c * 4 ^ S₁.k * P ^ S₁.k) *
              (c₂ * ((S₁.c + 1) * 4 ^ (S₁.k + 1)) ^ k₂ * P ^ ((S₁.k + 1) * k₂)) :=
            Nat.mul_le_mul hcard1 hcard2
        _ = N * (S₁.c * 4 ^ S₁.k * (c₂ * ((S₁.c + 1) * 4 ^ (S₁.k + 1)) ^ k₂)) *
              (P ^ S₁.k * P ^ ((S₁.k + 1) * k₂)) := by ring
        _ ≤ max 1 N * (c + 1) * P ^ (k + 2) :=
            Nat.mul_le_mul (Nat.mul_le_mul hN_max hc_le) hP_pow
        _ = max 1 N * twoStageFamFactor c k invEps invDelta := by
            unfold twoStageFamFactor; ring
    · intro T hT
      unfold composeFamilies at hT
      rcases List.mem_flatMap.mp hT with ⟨T₁, _, hT₂⟩
      rcases List.mem_map.mp hT₂ with ⟨I₂, hI₂, rfl⟩
      rw [lookupSeq_length, stage2FinM_len_eq S₂ M e₂ δ₂ I₂ hI₂]
      exact twoStage_S2_len_le S₁ S₂ N invEps logInvDelta
  · refine ⟨?_, fun T hT => ?_⟩
    · simp only [List.length_singleton]
      exact Nat.mul_pos (le_max_left 1 Y.card) (one_le_twoStageFamFactor c k invEps invDelta)
    · simp only [List.mem_singleton] at hT
      subst hT
      simp

private lemma compose_cost_linear_bound (a b B : ℕ) (hB : 1 ≤ B) :
    a * (b * (2 * B + 3) + 2) + 1 ≤ (5 * (a * b) + 2 * a + 1) * B := by
  have h1 : 2 * B + 3 ≤ 5 * B := by omega
  have h2 : b * (2 * B + 3) + 2 ≤ b * (5 * B) + 2 * B :=
    Nat.add_le_add (Nat.mul_le_mul_left _ h1) (Nat.mul_le_mul_left 2 hB)
  calc
    a * (b * (2 * B + 3) + 2) + 1
      ≤ a * (b * (5 * B) + 2 * B) + B := Nat.add_le_add (Nat.mul_le_mul_left _ h2) hB
    _ = (5 * (a * b) + 2 * a + 1) * B := by ring

private lemma transport_cost_sum_bound (x N KP : ℕ)
    (hx : x ≤ 2 * N * KP) (h1 : 1 ≤ KP) :
    x + 1 ≤ (2 * N + 1) * KP := by
  nlinarith

private lemma compose_coeff_bound (ab a N KP : ℕ)
    (hab : ab ≤ N * KP) (ha : a ≤ N * KP) (h1 : 1 ≤ KP) :
    5 * ab + 2 * a + 1 ≤ (7 * N + 1) * KP := by
  nlinarith

private lemma four_terms_sum_bound (t1 t2 t3 t4 N K P_pow B : ℕ)
    (h1 : t1 ≤ N * (N + 1) * K * P_pow * B)
    (h2 : t2 ≤ 1 * K * P_pow * B)
    (h3 : t3 ≤ (2 * N + 1) * K * P_pow * B)
    (h4 : t4 ≤ (7 * N + 1) * K * P_pow * B) :
    t1 + (t2 + (t3 + t4)) ≤ (N + 1) ^ 2 * (24 * K) * P_pow * B := by
  have hN : N * (N + 1) + 1 + (2 * N + 1) + (7 * N + 1) ≤ (N + 1) ^ 2 * 24 := by
    rw [sq]; nlinarith
  have hsum :
      t1 + (t2 + (t3 + t4)) ≤
        (N * (N + 1) + 1 + (2 * N + 1) + (7 * N + 1)) * (K * P_pow * B) := by
    nlinarith
  have hmul :
      (N * (N + 1) + 1 + (2 * N + 1) + (7 * N + 1)) * (K * P_pow * B) ≤
        ((N + 1) ^ 2 * 24) * (K * P_pow * B) :=
    Nat.mul_le_mul_right _ hN
  calc
    t1 + (t2 + (t3 + t4)) ≤ ((N + 1) ^ 2 * 24) * (K * P_pow * B) := hsum.trans hmul
    _ = (N + 1) ^ 2 * (24 * K) * P_pow * B := by ring

theorem twoStageConstructTracked_snd_le (S₁ : Stage1Sampler) (S₂ : Stage2Sampler)
    (Y : Finset β) (invEps logInvDelta : ℕ) :
    (twoStageConstructTracked S₁ S₂ Y invEps logInvDelta).2 ≤
      (Y.card + 1) ^ 2 *
        twoStageFamFactor (twoStageConstC S₁ S₂) (twoStageConstK S₁ S₂) invEps (2 ^ logInvDelta) *
        twoStageSampleSizeBound (twoStageConstC S₁ S₂) (twoStageConstK S₁ S₂) invEps logInvDelta := by
  set c₂ := stage2FinMC S₂
  set k₂ := stage2FinMK S₂
  set c := twoStageConstC S₁ S₂
  set k := twoStageConstK S₁ S₂
  set invDelta := 2 ^ logInvDelta
  set P := (invEps + 1) * (invDelta + 1)
  set B := twoStageSampleSizeBound c k invEps logInvDelta
  have hP_pos : 1 ≤ P := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  have hB_pos : 1 ≤ B := one_le_twoStageSampleSizeBound c k invEps logInvDelta
  have hF_pos : 1 ≤ twoStageFamFactor c k invEps invDelta :=
    one_le_twoStageFamFactor c k invEps invDelta
  unfold twoStageConstructTracked
  split_ifs with h
  · simp only [CostM.bind_snd, stage2FinMFamTracked_fst, transportFamTracked_fst]
    rw [S₁.fam_eq, stage1_headD_length_eq S₁ h.1 h.2 logInvDelta]
    set N := Y.card
    set e₂ := 2 * invEps
    set δ₂ := 2 * invDelta
    set M := S₁.len N e₂ δ₂
    set y₀ := indexFinset Y ⟨0, h.1⟩
    set fam₁_idx := S₁.fam N e₂ δ₂
    set fam₂ := stage2FinMFam S₂ M e₂ δ₂
    have heδ : e₂ * δ₂ + 1 ≤ 4 * P := by dsimp [e₂, δ₂, P]; nlinarith
    set A₁ := (S₁.c + 1) * (S₁.k + 1) ^ S₁.k * 4 ^ S₁.k
    set A₂ := (c₂ + 1) * ((S₁.c + 1) * 4 ^ (S₁.k + 1)) ^ k₂
    set K := A₁ ^ 2 * A₂
    have hA₁_pos : 1 ≤ A₁ :=
      Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.one_le_pow _ _ (Nat.succ_pos _)))
        (by positivity)
    have hA₂_pos : 1 ≤ A₂ :=
      Nat.mul_pos (Nat.succ_pos _)
        (Nat.one_le_pow _ _ (Nat.mul_pos (Nat.succ_pos _) (by positivity)))
    have hK_pos : 1 ≤ K := Nat.mul_pos (Nat.pow_pos hA₁_pos) hA₂_pos
    have hcost1 :
        (S₁.famTracked N e₂ δ₂).2 ≤
          N * (N + 1) * (S₁.c * (S₁.k + 1) ^ S₁.k * 4 ^ S₁.k) * P ^ S₁.k := by
      have hbase : e₂ * δ₂ * (Nat.log 2 N + 1) + 1 ≤ 4 * P * (Nat.log 2 N + 1) := by
        have h1 : 1 ≤ Nat.log 2 N + 1 := Nat.succ_pos _
        have h2 : e₂ * δ₂ * (Nat.log 2 N + 1) + 1 ≤ (e₂ * δ₂ + 1) * (Nat.log 2 N + 1) := by
          nlinarith
        exact h2.trans (Nat.mul_le_mul_right _ heδ)
      have hpow := Nat.pow_le_pow_left hbase S₁.k
      rw [Nat.mul_pow, Nat.mul_pow] at hpow
      have hlog := nat_log2_add_one_pow_le N S₁.k
      calc
        (S₁.famTracked N e₂ δ₂).2
          ≤ N * S₁.c * (e₂ * δ₂ * (Nat.log 2 N + 1) + 1) ^ S₁.k := S₁.cost_le N e₂ δ₂ h.1
        _ ≤ N * S₁.c * (4 ^ S₁.k * P ^ S₁.k * (Nat.log 2 N + 1) ^ S₁.k) :=
            Nat.mul_le_mul_left _ hpow
        _ ≤ N * S₁.c * (4 ^ S₁.k * P ^ S₁.k * ((S₁.k + 1) ^ S₁.k * (N + 1))) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hlog)
        _ = N * (N + 1) * (S₁.c * (S₁.k + 1) ^ S₁.k * 4 ^ S₁.k) * P ^ S₁.k := by ring
    have hM_le_P : M ≤ S₁.c * 4 ^ S₁.k * P ^ S₁.k := by
      calc
        M ≤ S₁.c * (e₂ * δ₂ + 1) ^ S₁.k := S₁.len_le N e₂ δ₂
        _ ≤ S₁.c * (4 * P) ^ S₁.k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left heδ S₁.k)
        _ = S₁.c * 4 ^ S₁.k * P ^ S₁.k := by rw [Nat.mul_pow]; ring
    have hcard1 : fam₁_idx.length ≤ N * A₁ * P ^ S₁.k := by
      have hc_le : S₁.c * 4 ^ S₁.k ≤ A₁ := by
        dsimp [A₁]
        have hk_pos : 1 ≤ (S₁.k + 1) ^ S₁.k := Nat.one_le_pow _ _ (Nat.succ_pos _)
        calc
          S₁.c * 4 ^ S₁.k = (S₁.c * 1) * 4 ^ S₁.k := by ring
          _ ≤ ((S₁.c + 1) * (S₁.k + 1) ^ S₁.k) * 4 ^ S₁.k :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.le_succ _) hk_pos)
      calc
        fam₁_idx.length ≤ N * S₁.c * (e₂ * δ₂ + 1) ^ S₁.k := S₁.card_le N e₂ δ₂
        _ ≤ N * S₁.c * (4 * P) ^ S₁.k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left heδ S₁.k)
        _ = N * (S₁.c * 4 ^ S₁.k) * P ^ S₁.k := by rw [Nat.mul_pow]; ring
        _ ≤ N * A₁ * P ^ S₁.k := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hc_le)
    have hMeδ : M * e₂ * δ₂ + 1 ≤ (S₁.c + 1) * 4 ^ (S₁.k + 1) * P ^ (S₁.k + 1) := by
      have h1 : e₂ * δ₂ ≤ 4 * P := by dsimp [e₂, δ₂, P]; nlinarith
      have h2 : M * (e₂ * δ₂) ≤ (S₁.c * 4 ^ S₁.k * P ^ S₁.k) * (4 * P) :=
        Nat.mul_le_mul hM_le_P h1
      have h3 : (S₁.c * 4 ^ S₁.k * P ^ S₁.k) * (4 * P) + 1 ≤
          (S₁.c + 1) * 4 ^ (S₁.k + 1) * P ^ (S₁.k + 1) := by
        have hpos4P : 1 ≤ 4 ^ (S₁.k + 1) * P ^ (S₁.k + 1) :=
          Nat.mul_pos (by positivity) (Nat.one_le_pow _ _ hP_pos)
        have heqL : (S₁.c * 4 ^ S₁.k * P ^ S₁.k) * (4 * P) =
            S₁.c * (4 ^ (S₁.k + 1) * P ^ (S₁.k + 1)) := by
          rw [Nat.pow_succ 4 S₁.k, Nat.pow_succ P S₁.k]; ring
        have heqR : (S₁.c + 1) * 4 ^ (S₁.k + 1) * P ^ (S₁.k + 1) =
            S₁.c * (4 ^ (S₁.k + 1) * P ^ (S₁.k + 1)) + 4 ^ (S₁.k + 1) * P ^ (S₁.k + 1) := by
          ring
        rw [heqL, heqR]
        exact Nat.add_le_add_left hpos4P _
      calc
        M * e₂ * δ₂ + 1 = M * (e₂ * δ₂) + 1 := by ring
        _ ≤ (S₁.c * 4 ^ S₁.k * P ^ S₁.k) * (4 * P) + 1 := Nat.add_le_add_right h2 1
        _ ≤ (S₁.c + 1) * 4 ^ (S₁.k + 1) * P ^ (S₁.k + 1) := h3
    have hc2_le_A₂ : c₂ * ((S₁.c + 1) * 4 ^ (S₁.k + 1)) ^ k₂ ≤ A₂ := by
      dsimp [A₂]
      exact Nat.mul_le_mul_right _ (Nat.le_succ _)
    have hcost2 :
        (stage2FinMFamTracked S₂ M e₂ δ₂).2 ≤ A₂ * P ^ ((S₁.k + 1) * k₂) := by
      calc
        (stage2FinMFamTracked S₂ M e₂ δ₂).2 ≤ c₂ * (M * e₂ * δ₂ + 1) ^ k₂ :=
          stage2FinM_cost_le S₂ M e₂ δ₂
        _ ≤ c₂ * ((S₁.c + 1) * 4 ^ (S₁.k + 1) * P ^ (S₁.k + 1)) ^ k₂ :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hMeδ k₂)
        _ = (c₂ * ((S₁.c + 1) * 4 ^ (S₁.k + 1)) ^ k₂) * P ^ ((S₁.k + 1) * k₂) := by
          rw [Nat.mul_pow, ← Nat.pow_mul, ← mul_assoc]
        _ ≤ A₂ * P ^ ((S₁.k + 1) * k₂) := Nat.mul_le_mul_right _ hc2_le_A₂
    have hcard2 : fam₂.length ≤ A₂ * P ^ ((S₁.k + 1) * k₂) := by
      calc
        fam₂.length ≤ c₂ * (M * e₂ * δ₂ + 1) ^ k₂ := stage2FinM_card_le S₂ M e₂ δ₂
        _ ≤ c₂ * ((S₁.c + 1) * 4 ^ (S₁.k + 1) * P ^ (S₁.k + 1)) ^ k₂ :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hMeδ k₂)
        _ = (c₂ * ((S₁.c + 1) * 4 ^ (S₁.k + 1)) ^ k₂) * P ^ ((S₁.k + 1) * k₂) := by
          rw [Nat.mul_pow, ← Nat.pow_mul, ← mul_assoc]
        _ ≤ A₂ * P ^ ((S₁.k + 1) * k₂) := Nat.mul_le_mul_right _ hc2_le_A₂
    have hP1 : P ^ S₁.k ≤ P ^ (k + 2) :=
      Nat.pow_le_pow_right hP_pos (by dsimp [k, twoStageConstK]; omega)
    have hP1_sq : P ^ S₁.k * P ^ S₁.k ≤ P ^ (k + 2) := by
      rw [← Nat.pow_add]
      exact Nat.pow_le_pow_right hP_pos (by dsimp [k, twoStageConstK]; omega)
    have hP2 : P ^ ((S₁.k + 1) * k₂) ≤ P ^ (k + 2) := by
      refine Nat.pow_le_pow_right hP_pos ?_
      dsimp [k, twoStageConstK, k₂]
      have : (S₁.k + 1) * stage2FinMK S₂ ≤ (S₁.k + 2) * stage2FinMK S₂ :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    have hP12 : P ^ S₁.k * P ^ ((S₁.k + 1) * k₂) ≤ P ^ (k + 2) := by
      rw [← Nat.pow_add]
      refine Nat.pow_le_pow_right hP_pos ?_
      dsimp [k, twoStageConstK, k₂]
      have : (S₁.k + 1) * stage2FinMK S₂ ≤ (S₁.k + 2) * stage2FinMK S₂ :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    have h1_KP : 1 ≤ K * P ^ (k + 2) :=
      Nat.mul_pos hK_pos (Nat.one_le_pow _ _ hP_pos)
    have hA₁_K : A₁ ≤ K := by
      dsimp [K]; rw [sq]
      calc
        A₁ = A₁ * 1 * 1 := by ring
        _ ≤ A₁ * A₁ * A₂ := Nat.mul_le_mul (Nat.mul_le_mul_left _ hA₁_pos) hA₂_pos
    have hc1_K : S₁.c * (S₁.k + 1) ^ S₁.k * 4 ^ S₁.k ≤ K := by
      have hleA : S₁.c * (S₁.k + 1) ^ S₁.k * 4 ^ S₁.k ≤ A₁ := by
        dsimp [A₁]
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_succ _))
      exact hleA.trans hA₁_K
    have hA₂_K : A₂ ≤ K := by
      dsimp [K]
      exact Nat.le_mul_of_pos_left _ (Nat.pow_pos hA₁_pos)
    have hA₁A₂_K : A₁ * A₂ ≤ K := by
      dsimp [K]; rw [sq]
      calc
        A₁ * A₂ = (1 * A₁) * A₂ := by ring
        _ ≤ (A₁ * A₁) * A₂ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hA₁_pos)
    have hterm1 : (S₁.famTracked N e₂ δ₂).2 ≤ N * (N + 1) * K * P ^ (k + 2) * B := by
      have h1 : (S₁.famTracked N e₂ δ₂).2 ≤ N * (N + 1) * K * P ^ (k + 2) := by
        calc
          (S₁.famTracked N e₂ δ₂).2
            ≤ N * (N + 1) * (S₁.c * (S₁.k + 1) ^ S₁.k * 4 ^ S₁.k) * P ^ S₁.k := hcost1
          _ ≤ N * (N + 1) * K * P ^ (k + 2) :=
              Nat.mul_le_mul (Nat.mul_le_mul_left _ hc1_K) hP1
      exact h1.trans (Nat.le_mul_of_pos_right _ hB_pos)
    have hterm2 : (stage2FinMFamTracked S₂ M e₂ δ₂).2 ≤ 1 * K * P ^ (k + 2) * B := by
      rw [one_mul]
      have h1 : (stage2FinMFamTracked S₂ M e₂ δ₂).2 ≤ K * P ^ (k + 2) :=
        hcost2.trans (Nat.mul_le_mul hA₂_K hP2)
      exact h1.trans (Nat.le_mul_of_pos_right _ hB_pos)
    have hterm3 :
        (transportFamTracked Y fam₁_idx).2 ≤ (2 * N + 1) * K * P ^ (k + 2) * B := by
      have htr := transportFamTracked_snd_le Y fam₁_idx M
        (fun T hT => (S₁.len_eq N e₂ δ₂ T hT).le)
      have h2M : 2 * M + 2 ≤ 2 * A₁ * P ^ S₁.k := by
        have h1 : S₁.c * 4 ^ S₁.k * P ^ S₁.k + 1 ≤ (S₁.c + 1) * 4 ^ S₁.k * P ^ S₁.k := by
          have hpos : 1 ≤ 4 ^ S₁.k * P ^ S₁.k :=
            Nat.mul_pos (by positivity) (Nat.one_le_pow _ _ hP_pos)
          nlinarith
        have h2 : (S₁.c + 1) * 4 ^ S₁.k ≤ A₁ := by
          dsimp [A₁]
          have hk_pos : 1 ≤ (S₁.k + 1) ^ S₁.k := Nat.one_le_pow _ _ (Nat.succ_pos _)
          calc
            (S₁.c + 1) * 4 ^ S₁.k = ((S₁.c + 1) * 1) * 4 ^ S₁.k := by ring
            _ ≤ ((S₁.c + 1) * (S₁.k + 1) ^ S₁.k) * 4 ^ S₁.k :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hk_pos)
        calc
          2 * M + 2 ≤ 2 * (S₁.c * 4 ^ S₁.k * P ^ S₁.k + 1) := by omega
          _ ≤ 2 * ((S₁.c + 1) * 4 ^ S₁.k * P ^ S₁.k) := Nat.mul_le_mul_left 2 h1
          _ = 2 * ((S₁.c + 1) * 4 ^ S₁.k) * P ^ S₁.k := by ring
          _ ≤ 2 * A₁ * P ^ S₁.k := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 h2)
      have hprod : fam₁_idx.length * (2 * M + 2) ≤ 2 * N * (K * P ^ (k + 2)) := by
        have hA_sq : A₁ ^ 2 ≤ K := by
          dsimp [K]
          exact Nat.le_mul_of_pos_right _ hA₂_pos
        calc
          fam₁_idx.length * (2 * M + 2)
            ≤ (N * A₁ * P ^ S₁.k) * (2 * A₁ * P ^ S₁.k) := Nat.mul_le_mul hcard1 h2M
          _ = 2 * N * A₁ ^ 2 * (P ^ S₁.k * P ^ S₁.k) := by ring
          _ ≤ 2 * N * K * P ^ (k + 2) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hA_sq) hP1_sq
          _ = 2 * N * (K * P ^ (k + 2)) := by ring
      have hsum : fam₁_idx.length * (2 * M + 2) + 1 ≤ (2 * N + 1) * K * P ^ (k + 2) := by
        have hs := transport_cost_sum_bound (fam₁_idx.length * (2 * M + 2)) N (K * P ^ (k + 2))
          hprod h1_KP
        simpa [mul_assoc] using hs
      exact (htr.trans hsum).trans (Nat.le_mul_of_pos_right _ hB_pos)
    have hterm4 :
        (composeFamiliesTracked y₀ (transportFam Y fam₁_idx) fam₂).2 ≤
          (7 * N + 1) * K * P ^ (k + 2) * B := by
      have hL₂ : ∀ I₂ ∈ fam₂, I₂.length ≤ B := by
        intro I₂ hI₂
        rw [stage2FinM_len_eq S₂ M e₂ δ₂ I₂ hI₂]
        exact twoStage_S2_len_le S₁ S₂ N invEps logInvDelta
      have hcomp := composeFamiliesTracked_snd_le y₀ (transportFam Y fam₁_idx) fam₂ B hL₂
      rw [transportFam_length] at hcomp
      have hB_lin := compose_cost_linear_bound fam₁_idx.length fam₂.length B hB_pos
      have hprod12 : fam₁_idx.length * fam₂.length ≤ N * (K * P ^ (k + 2)) := by
        calc
          fam₁_idx.length * fam₂.length
            ≤ (N * A₁ * P ^ S₁.k) * (A₂ * P ^ ((S₁.k + 1) * k₂)) :=
              Nat.mul_le_mul hcard1 hcard2
          _ = N * (A₁ * A₂) * (P ^ S₁.k * P ^ ((S₁.k + 1) * k₂)) := by ring
          _ ≤ N * K * P ^ (k + 2) :=
              Nat.mul_le_mul (Nat.mul_le_mul_left _ hA₁A₂_K) hP12
          _ = N * (K * P ^ (k + 2)) := by ring
      have h1_single : fam₁_idx.length ≤ N * (K * P ^ (k + 2)) := by
        calc
          fam₁_idx.length ≤ N * A₁ * P ^ S₁.k := hcard1
          _ ≤ N * K * P ^ (k + 2) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hA₁_K) hP1
          _ = N * (K * P ^ (k + 2)) := by ring
      have hcoeff :
          5 * (fam₁_idx.length * fam₂.length) + 2 * fam₁_idx.length + 1 ≤
            (7 * N + 1) * K * P ^ (k + 2) := by
        have hc := compose_coeff_bound (fam₁_idx.length * fam₂.length) fam₁_idx.length
          N (K * P ^ (k + 2)) hprod12 h1_single h1_KP
        simpa [mul_assoc] using hc
      exact (hcomp.trans hB_lin).trans (Nat.mul_le_mul_right B hcoeff)
    have h24K : 24 * K ≤ c + 1 := by
      have hbase :
          (S₁.c + 1) * 4 ^ (S₁.k + 1) ≤ 4 * (S₁.c + 3 * S₁.k + 1) * 4 ^ (S₁.k + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      have hpow_base := Nat.pow_le_pow_left hbase k₂
      have hmul := Nat.mul_le_mul_left (24 * A₁ ^ 2 * (c₂ + 1)) hpow_base
      have heqL : 24 * K =
          (24 * A₁ ^ 2 * (c₂ + 1)) * ((S₁.c + 1) * 4 ^ (S₁.k + 1)) ^ k₂ := by
        dsimp [K, A₂]; ring
      have heqR :
          (24 * A₁ ^ 2 * (c₂ + 1)) *
            (4 * (S₁.c + 3 * S₁.k + 1) * 4 ^ (S₁.k + 1)) ^ k₂ = c := rfl
      rw [heqL]; rw [heqR] at hmul
      exact hmul.trans (Nat.le_succ c)
    have htotal := four_terms_sum_bound
      (S₁.famTracked N e₂ δ₂).2
      (stage2FinMFamTracked S₂ M e₂ δ₂).2
      (transportFamTracked Y fam₁_idx).2
      (composeFamiliesTracked y₀ (transportFam Y fam₁_idx) fam₂).2
      N K (P ^ (k + 2)) B hterm1 hterm2 hterm3 hterm4
    have hc_step :
        (N + 1) ^ 2 * (24 * K) * P ^ (k + 2) * B ≤
          (N + 1) ^ 2 * (c + 1) * P ^ (k + 2) * B :=
      Nat.mul_le_mul_right B
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h24K))
    have hfac_eq :
        (N + 1) ^ 2 * (c + 1) * P ^ (k + 2) * B =
          (N + 1) ^ 2 * twoStageFamFactor c k invEps invDelta * B := by
      unfold twoStageFamFactor; ring
    exact (htotal.trans hc_step).trans_eq hfac_eq
  · rw [retTracked_snd]
    exact Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (Nat.succ_pos _)) hF_pos) hB_pos

/-- **General Two-Stage Composition Theorem (`twoStage_compose_general`, `paper.tex` Section 3.3 &
Appendix B, `\eqref{eq:oblivious-sampler}` & `\eqref{eq:two-stage-sampler}`, §3.3)**:
For any `S₁ : Stage1Sampler`, `S₂ : Stage2Sampler`, finite universe `Y : Finset β`, and integer
parameters `invEps logInvDelta : ℕ` with `1 ≤ invEps`, `twoStageConstruct S₁ S₂ Y invEps logInvDelta`
is a `(1 / invEps, 1 / 2 ^ logInvDelta)`-sequence sampler of `Y` (`IsSeqSampler`). -/
theorem twoStage_compose_general (S₁ : Stage1Sampler) (S₂ : Stage2Sampler)
    (Y : Finset β) {invEps : ℕ} (hinv : 1 ≤ invEps) (logInvDelta : ℕ) :
    IsSeqSampler Y (twoStageConstruct S₁ S₂ Y invEps logInvDelta)
      (1 / (invEps : ℝ)) (1 / ((2 ^ logInvDelta : ℕ) : ℝ)) := by
  unfold twoStageConstruct
  rcases Y.eq_empty_or_nonempty with rfl | hY_ne
  · have hnot : ¬(0 < (∅ : Finset β).card ∧ 1 ≤ invEps) := by simp
    rw [dif_neg hnot]
    exact isSeqSampler_empty (by positivity) (by positivity)
  · have hpos : 0 < Y.card := hY_ne.card_pos
    have hcond : 0 < Y.card ∧ 1 ≤ invEps := ⟨hpos, hinv⟩
    rw [dif_pos hcond]
    dsimp only
    rw [stage1_headD_length_eq S₁ hpos hinv logInvDelta]
    set e₂ := 2 * invEps
    set δ₂ := 2 * 2 ^ logInvDelta
    set M := S₁.len Y.card e₂ δ₂
    set y₀ := indexFinset Y ⟨0, hpos⟩
    have hy₀ : y₀ ∈ Y := indexFinset_mem Y ⟨0, hpos⟩
    have he₂_pos : 1 ≤ e₂ := by dsimp [e₂]; omega
    have hδ₂_pos : 1 ≤ δ₂ := by
      dsimp [δ₂]
      have : 1 ≤ 2 ^ logInvDelta := Nat.one_le_two_pow
      omega
    have hS₁_univ := S₁.sampler Y.card e₂ δ₂ hpos he₂_pos hδ₂_pos
    have hS₁_Y := IsSeqSampler.transport Y hS₁_univ
    have hM_unif : ∀ T₁ ∈ transportFam Y (S₁.fam Y.card e₂ δ₂), T₁.length = M := by
      intro T₁ hT₁
      rcases List.mem_map.mp hT₁ with ⟨T₁_idx, hT₁_idx, rfl⟩
      rw [List.length_map]
      exact S₁.len_eq Y.card e₂ δ₂ T₁_idx hT₁_idx
    have hM_ge_one : 1 ≤ M := by
      cases hfam₁ : S₁.fam Y.card e₂ δ₂ with
      | nil => exact False.elim (hS₁_univ.1 hfam₁)
      | cons T₀ tl =>
        have hmem : T₀ ∈ S₁.fam Y.card e₂ δ₂ := hfam₁ ▸ List.mem_cons_self
        have huniv_ne : (Finset.univ : Finset (Fin Y.card)).Nonempty :=
          ⟨⟨0, hpos⟩, Finset.mem_univ _⟩
        have hT₀_ne : T₀ ≠ [] := (hS₁_univ.2.1 T₀ hmem).2 huniv_ne
        dsimp [M]
        rw [← S₁.len_eq Y.card e₂ δ₂ T₀ hmem]
        exact List.length_pos_of_ne_nil hT₀_ne
    have hS₂_univ := stage2FinM_sampler S₂ M e₂ δ₂ hM_ge_one he₂_pos hδ₂_pos
    have hcomp := composeFamilies_isSeqSampler hy₀ hS₁_Y hM_unif hS₂_univ
    have heps_eq : (1 : ℝ) / (e₂ : ℝ) + (1 : ℝ) / (e₂ : ℝ) = (1 : ℝ) / (invEps : ℝ) := by
      have hne : (invEps : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      dsimp [e₂]
      push_cast
      field_simp [hne]
      ring
    have hdelta_eq :
        (1 : ℝ) / (δ₂ : ℝ) + (1 : ℝ) / (δ₂ : ℝ) = (1 : ℝ) / ((2 ^ logInvDelta : ℕ) : ℝ) := by
      have hne : ((2 ^ logInvDelta : ℕ) : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp Nat.one_le_two_pow)
      dsimp [δ₂]
      push_cast
      field_simp [hne]
      ring
    rwa [heps_eq, hdelta_eq] at hcomp

/-- **`approxGridNorm_sampler_inst` (`paper.tex` Algorithm 2 Line 1 `\label{line:est-sampler}` & Lemma 4.1, §4.1)**:
Specializes `twoStage_compose_general` to the `ApproxGridNorm` parameters
`invEps = 2 ^ accExp ε d` and `logInvDelta = d * accExp ε d` for any regularity parameter
$\varepsilon > 0$ (in particular $\varepsilon = 1 / 160$, where `accExp (1 / 160) d = 3 * d + 14`). -/
theorem approxGridNorm_sampler_inst (S₁ : Stage1Sampler) (S₂ : Stage2Sampler)
    {ε : ℝ} (hε0 : 0 < ε)
    (Y : Finset β) {d : ℕ} (_hd : 1 ≤ d) {ε_samp δ_samp : ℝ}
    (hε_samp : ε / ((2 ^ (3 * d + 6) : ℕ) : ℝ) ≤ ε_samp)
    (hδ_samp : (ε / ((2 ^ (3 * d + 6) : ℕ) : ℝ)) ^ d ≤ δ_samp) :
    IsSeqSampler Y
      (twoStageConstruct S₁ S₂ Y (2 ^ accExp ε d) (d * accExp ε d))
      ε_samp δ_samp := by
  have hgen := twoStage_compose_general S₁ S₂ Y
    (invEps := 2 ^ accExp ε d) Nat.one_le_two_pow (d * accExp ε d)
  have h1_le_eps :
      (1 : ℝ) / ((2 ^ accExp ε d : ℕ) : ℝ) ≤ ε / ((2 ^ (3 * d + 6) : ℕ) : ℝ) := by
    have hpow :
        ((2 ^ accExp ε d : ℕ) : ℝ) =
          ((2 ^ (3 * d + 6) : ℕ) : ℝ) * ((2 ^ Nat.clog 2 ⌈1 / ε⌉₊ : ℕ) : ℝ) := by
      unfold accExp
      push_cast
      rw [pow_add]
    have hclog_nat : ⌈1 / ε⌉₊ ≤ 2 ^ Nat.clog 2 ⌈1 / ε⌉₊ :=
      Nat.le_pow_clog (by norm_num) _
    have hclog_real : (1 : ℝ) / ε ≤ ((2 ^ Nat.clog 2 ⌈1 / ε⌉₊ : ℕ) : ℝ) :=
      (Nat.le_ceil (1 / ε)).trans (by exact_mod_cast hclog_nat)
    have hpow_pos : (0 : ℝ) < ((2 ^ Nat.clog 2 ⌈1 / ε⌉₊ : ℕ) : ℝ) := by positivity
    have hinv_le : (1 : ℝ) / ((2 ^ Nat.clog 2 ⌈1 / ε⌉₊ : ℕ) : ℝ) ≤ ε := by
      rw [div_le_iff₀ hpow_pos]
      have hmul := mul_le_mul_of_nonneg_left hclog_real hε0.le
      rwa [mul_one_div_cancel hε0.ne'] at hmul
    have hdiv_eq :
        (1 : ℝ) / (((2 ^ (3 * d + 6) : ℕ) : ℝ) * ((2 ^ Nat.clog 2 ⌈1 / ε⌉₊ : ℕ) : ℝ)) =
          ((1 : ℝ) / ((2 ^ Nat.clog 2 ⌈1 / ε⌉₊ : ℕ) : ℝ)) / ((2 ^ (3 * d + 6) : ℕ) : ℝ) := by
      ring
    rw [hpow, hdiv_eq]
    exact div_le_div_of_nonneg_right hinv_le (by positivity)
  have h1_le_delta :
      (1 : ℝ) / ((2 ^ (d * accExp ε d) : ℕ) : ℝ) ≤ (ε / ((2 ^ (3 * d + 6) : ℕ) : ℝ)) ^ d := by
    have hpow_d :
        (1 : ℝ) / ((2 ^ (d * accExp ε d) : ℕ) : ℝ) =
          ((1 : ℝ) / ((2 ^ accExp ε d : ℕ) : ℝ)) ^ d := by
      push_cast
      rw [one_div_pow, mul_comm d (accExp ε d), pow_mul]
    rw [hpow_d]
    exact pow_le_pow_left₀ (by positivity) h1_le_eps d
  exact hgen.mono (h1_le_eps.trans hε_samp) (h1_le_delta.trans hδ_samp)

/-- **Two-Stage Oblivious Sampler Oracle Constructor (`twoStage_compose`, `paper.tex` Section 3.3 &
Appendix B, `\eqref{eq:oblivious-sampler}` & `\eqref{eq:two-stage-sampler}`, §3.3)**:
Combines any Stage-1 linear-seed sampler `S₁ : Stage1Sampler` (`[AFKLM24, Lemma 4.4]`) and any
Stage-2 polynomial-family sampler `S₂ : Stage2Sampler` (`[Vadhan, Corollary 6.24]`) into a
complete `TwoStageSamplerOracle β ε` for any $\varepsilon > 0$ (in particular
$\varepsilon = 1 / 160$). -/
noncomputable def twoStage_compose (S₁ : Stage1Sampler) (S₂ : Stage2Sampler)
    (ε : ℝ) (hε0 : 0 < ε) : TwoStageSamplerOracle β ε where
  c := twoStageConstC S₁ S₂
  k := twoStageConstK S₁ S₂
  constructTracked := twoStageConstructTracked S₁ S₂
  len_eq Y invEps logInvDelta := by
    rw [twoStageConstructTracked_fst]
    exact twoStageConstruct_len_eq S₁ S₂ Y invEps logInvDelta
  satisfies_bounds Y invEps logInvDelta _hinv := by
    rw [twoStageConstructTracked_fst]
    exact twoStageConstruct_satisfies_bounds S₁ S₂ Y invEps logInvDelta
  cost_le Y invEps logInvDelta :=
    twoStageConstructTracked_snd_le S₁ S₂ Y invEps logInvDelta
  is_sampler Y d {ε_samp δ_samp} hd hε_samp hδ_samp := by
    rw [twoStageConstructTracked_fst]
    exact approxGridNorm_sampler_inst S₁ S₂ hε0 Y hd hε_samp hδ_samp

/-!
### Standalone Small-Universe Inhabitant (`smallTwoStageSamplerOracle`, Off the Headline Path)

*Note*: `constructSmallTwoStageSampler`, `smallTwoStageSamplerOracle`, and
`twoStageSamplerOracle_nonempty_of_le` provide a standalone small-universe consistency check for
`TwoStageSamplerOracle` ($n \le 5{,}566{,}362{,}550{,}596$) via exact universe exhaustion
`[Y.toList]`. They are **not** used on the headline theorem path (`thm_main_decomp_of_samplers`,
`thm_main_triangle_detection`, `thm_main_bmm`), which constructs the
oracle via `twoStage_compose S₁ S₂`.
-/

/-- Monotonicity of `twoStageSampleSizeBound 0 0` in both arguments. -/
lemma twoStageSampleSizeBound_mono {e₁ e₂ d₁ d₂ : ℕ} (he : e₁ ≤ e₂) (hd : d₁ ≤ d₂) :
    twoStageSampleSizeBound 0 0 e₁ d₁ ≤ twoStageSampleSizeBound 0 0 e₂ d₂ := by
  unfold twoStageSampleSizeBound
  rw [zero_add, one_mul, one_mul]
  exact Nat.pow_le_pow_left (Nat.mul_le_mul (by omega) (by omega)) 2

/-- Concrete deterministic sequence sampler constructor for universes bounded by
`twoStageSampleSizeBound 0 0 invEps logInvDelta`: returns the exact singleton family `[Y.toList]`
when `Y.card ≤ twoStageSampleSizeBound 0 0 invEps logInvDelta` (and `[[]]` otherwise). -/
noncomputable def constructSmallTwoStageSampler (Y : Finset β) (invEps logInvDelta : ℕ) :
    List (List β) :=
  if Y.card ≤ twoStageSampleSizeBound 0 0 invEps logInvDelta then [Y.toList] else [[]]

/-- Off-path small-universe `CostM` helper (`constructSmallTwoStageSamplerTracked`, unit-charging `1` for `[Y.toList]`). -/
noncomputable def constructSmallTwoStageSamplerTracked (Y : Finset β) (invEps logInvDelta : ℕ) :
    CostM (List (List β)) :=
  retTracked (constructSmallTwoStageSampler Y invEps logInvDelta)

@[simp]
lemma constructSmallTwoStageSamplerTracked_fst (Y : Finset β) (invEps logInvDelta : ℕ) :
    (constructSmallTwoStageSamplerTracked Y invEps logInvDelta).1 =
      constructSmallTwoStageSampler Y invEps logInvDelta := rfl

@[simp]
lemma constructSmallTwoStageSamplerTracked_snd (Y : Finset β) (invEps logInvDelta : ℕ) :
    (constructSmallTwoStageSamplerTracked Y invEps logInvDelta).2 = 1 := rfl

/-- Explicit off-path exhaustive inhabitant of `TwoStageSamplerOracle β ε` (`[Y.toList]`, `|T| = |Y|`,
`c = k = 0`) for any finite type `β` with `Fintype.card β ≤ twoStageSampleSizeBound 0 0 (2 ^ 17) 17`
(`= 5,566,362,550,596`) and `0 < ε ≤ 1 / 160`. -/
noncomputable def smallTwoStageSamplerOracle [Fintype β] (ε : ℝ)
    (hcard : Fintype.card β ≤ twoStageSampleSizeBound 0 0 (2 ^ 17) 17)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) : TwoStageSamplerOracle β ε where
  c := 0
  k := 0
  constructTracked := constructSmallTwoStageSamplerTracked
  len_eq Y invEps logInvDelta := by
    rw [constructSmallTwoStageSamplerTracked_fst]
    unfold constructSmallTwoStageSampler
    split_ifs <;> simp
  satisfies_bounds Y invEps logInvDelta _hinv := by
    rw [constructSmallTwoStageSamplerTracked_fst]
    unfold SatisfiesTwoStageBounds constructSmallTwoStageSampler
    have h1 : 1 ≤ max 1 Y.card * twoStageFamFactor 0 0 invEps (2 ^ logInvDelta) := by
      have hm : 1 ≤ max 1 Y.card := le_max_left 1 Y.card
      have hf : 1 ≤ twoStageFamFactor 0 0 invEps (2 ^ logInvDelta) :=
        one_le_twoStageFamFactor 0 0 invEps (2 ^ logInvDelta)
      exact Nat.mul_pos hm hf
    split_ifs with hle
    · refine ⟨by simpa using h1, fun T hT => ?_⟩
      simp only [List.mem_singleton] at hT
      subst hT
      simpa using hle
    · refine ⟨by simpa using h1, fun T hT => ?_⟩
      simp only [List.mem_singleton] at hT
      subst hT
      simp
  cost_le Y invEps logInvDelta := by
    rw [constructSmallTwoStageSamplerTracked_snd]
    exact Nat.mul_pos
      (Nat.mul_pos (Nat.pow_pos (Nat.succ_pos _))
        (one_le_twoStageFamFactor 0 0 invEps (2 ^ logInvDelta)))
      (one_le_twoStageSampleSizeBound 0 0 invEps logInvDelta)
  is_sampler Y d {ε_samp δ_samp} hd hε_samp hδ_samp := by
    rw [constructSmallTwoStageSamplerTracked_fst]
    unfold constructSmallTwoStageSampler
    have hexp : 3 * d + 14 ≤ accExp ε d := three_mul_add_fourteen_le_accExp hε0 hε_le d
    have he : 2 ^ 17 ≤ 2 ^ accExp ε d :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hld : 17 ≤ d * accExp ε d := by nlinarith
    have hY_le : Y.card ≤ twoStageSampleSizeBound 0 0 (2 ^ accExp ε d) (d * accExp ε d) :=
      (Finset.card_le_univ Y).trans (hcard.trans (twoStageSampleSizeBound_mono he hld))
    rw [if_pos hY_le]
    have h0_eps : 0 ≤ ε / ((2 ^ (3 * d + 6) : ℕ) : ℝ) := by positivity
    have h0_delta : 0 ≤ (ε / ((2 ^ (3 * d + 6) : ℕ) : ℝ)) ^ d := by positivity
    exact isSeqSampler_singleton Y (h0_eps.trans hε_samp) (h0_delta.trans hδ_samp)

/-- Explicit off-path exhaustive non-emptiness theorem (`[Y.toList]`, `|T| = |Y|`, `c = k = 0`) for
`TwoStageSamplerOracle (Fin n) (1 / 160 : ℝ)` for $n \le 5,566,362,550,596$. -/
theorem twoStageSamplerOracle_nonempty_of_le {n : ℕ}
    (hn : n ≤ twoStageSampleSizeBound 0 0 (2 ^ 17) 17) :
    Nonempty (TwoStageSamplerOracle (Fin n) (1 / 160 : ℝ)) :=
  ⟨smallTwoStageSamplerOracle (1 / 160 : ℝ) (by simpa using hn) (by norm_num) le_rfl⟩

end ComputableSampler

end BMMGrid
