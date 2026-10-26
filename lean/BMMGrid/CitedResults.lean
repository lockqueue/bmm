import BMMGrid.CostMonadAndLinter

/-!
# Cited External Results (`BMMGrid/CitedResults.lean`)

This module is the **single, self-contained trust boundary** for external literature theorems
cited without proof in the formalization of `paper.tex`
(Section 3.3 Lemma 3.3 `\label{lem:two-stage-sampler}`, `\eqref{eq:oblivious-sampler}`,
`\eqref{eq:two-stage-sampler}`, and Appendix B `\label{app:sampler}` of `paper.tex`).

Rather than postulating global `axiom` declarations, the two standard pseudorandomness building
blocks from the literature are packaged as explicit structure types (`Stage1Sampler` and
`Stage2Sampler`) and threaded as explicit hypotheses into the two-stage composition theorem
`twoStage_compose` in `BMMGrid/ObliviousSampler.lean` and the headline complexity theorems
`thm_main_triangle_detection` and `thm_main_bmm` in `BMMGrid/TriangleAndBMM.lean`:

1. **`Stage1Sampler` (Stage 1 — Degree-reduced expander walk / pairwise-independent sampler)**:
   - **Literature**: `[AFKLM24, arXiv:2311.09095v2, Section 4.1, Lemma 4.4, PDF p. 17]` =
     `[Goldreich–Wigderson 1997, Random Structures & Algorithms 11(4):315–343, Section 3;
     preliminary version in STOC 1994, pp. 574–583]` (see `lean/SOURCES.md` §1).
   - **Source Statement (`[AFKLM24, Lemma 4.4, PDF p. 17]`)**:
     *"Lemma 4.4 (Oblivious Sampling [41]). Let $X$ be a set and let $\delta, \varepsilon > 0$.
     There is a deterministic algorithm computing, in time
     $|X| \cdot \operatorname{poly}(\varepsilon^{-1}, \delta^{-1}, \log |X|)$, a family
     $\mathcal{S}$ of subsets $S \subseteq X$ such that
     1. $|\mathcal{S}| \le |X| \cdot \operatorname{poly}(\varepsilon^{-1}, \delta^{-1})$,
     2. $|S| \le \operatorname{poly}(\varepsilon^{-1}, \delta^{-1})$ for all $S \in \mathcal{S}$,
     3. For every function $f : X \to [0, 1]$,
     $\Pr_{S \in \mathcal{S}}[\mathbb{E}_{x \in X} f(x) = \mathbb{E}_{x \in S} f(x) \pm \varepsilon] \ge 1 - \delta$."*
   - **Lean Transcription**: Explicit sequence sampler on universe `Fin N` with accuracy $1/e$
     (`e = invEps`) and confidence $1/\delta$ (`δ = invDelta`), producing at most
     $N \cdot c_1 (e\delta + 1)^{k_1}$ sample sequences of uniform length
     $M = \text{len}(N, e, \delta) \le c_1 (e\delta + 1)^{k_1}$ (independent of $N$) in tracked
     operation count at most $N \cdot c_1 (e\delta(\lfloor\log_2 N\rfloor + 1) + 1)^{k_1}$.

2. **`Stage2Sampler` (Stage 2 — Extractor-based randomness-efficient averaging sampler)**:
   - **Literature**: `[GUV09, JACM 56(4), Art. 20, Theorem 1.5, p. 4 (p. 20:4) & Theorem 5.12]` +
     `[Vadhan, Pseudorandomness, FnT-TCS 7(1–3), 2012, Corollary 6.24, printed p. 186 (PDF p. 189)
     & Theorem 6.36]` + `[Zuckerman 1997, Random Structures & Algorithms 11(4):345–367, Lemma 2.6 &
     Proposition 2.7]` (historical context for direct oblivious samplers: `[Zuckerman 1997,
     Theorem 3.17, p. 15]`, which carries side conditions on $\alpha$ and $\varepsilon$ that
     `[GUV09, Theorem 1.5]` removes; see `lean/SOURCES.md` §§2–4).
   - **Source Statements**:
     - `[GUV09, Theorem 1.5, JACM 56(4), Art. 20, p. 4 (p. 20:4)]`:
       *"Theorem 1.5 (Main extractor result). For every constant $\alpha > 0$, and all positive
       integers $n, k$ and all $\varepsilon > 0$, there is an explicit construction of a
       $(k, \varepsilon)$ extractor $E : \{0, 1\}^n \times \{0, 1\}^d \to \{0, 1\}^m$ with
       $d \le \log n + O(\log(k/\varepsilon))$ and $m \ge (1 - \alpha)k$."*
     - `[Vadhan 2012, Corollary 6.24, printed p. 186 (PDF p. 189)]`:
       *"Corollary 6.24. Let $\mathrm{Ext} : [N] \times [D] \to [M]$ and
       $\mathrm{Samp} : [N] \to [M]^D$ be such that $\mathrm{Ext}(x, y) = \mathrm{Samp}(x)_y$.
       Then:
       (1) If $\mathrm{Ext}$ is a $(k, \varepsilon)$ extractor, then $\mathrm{Samp}$ is a
       $(K/N, \varepsilon)$ averaging sampler, where $K = 2^k$.
       (2) If $\mathrm{Samp}$ is a $(K/N, \varepsilon)$ boolean averaging sampler, then
       $\mathrm{Ext}$ is a $(k + \log(1/\varepsilon), 2\varepsilon)$ extractor.
       (3) If $\mathrm{Samp}$ is a $(\delta, \varepsilon)$ boolean averaging sampler, then
       $\mathrm{Samp}$ is a $(\delta/\varepsilon, 2\varepsilon)$ averaging sampler."*
   - **Derivation of the Lean Bounds from `[GUV09, Theorem 1.5]` + `[Vadhan 2012, Corollary 6.24(1)]`**:
     Fix $\alpha = 1/2$. For universe $\{0, 1\}^{m_0}$ ($\cong \text{Fin}(2^{m_0})$, with $m_0 = 0$
     trivial), accuracy $\varepsilon = 1/e$, and two-sided failure probability $1/\delta$ (one-sided
     failure $\delta_0 = 1/(2\delta)$), set $k = \lceil m_0 / (1 - \alpha) \rceil = 2 m_0$ and
     $n = k + \lceil\log_2(1/\delta_0)\rceil$, and truncate the extractor output of
     `[GUV09, Theorem 1.5]` to $m_0$ bits. By `[Vadhan 2012, Corollary 6.24(1)]` (cf.
     `[Zuckerman 1997, Lemma 2.6 & Proposition 2.7]`), this gives seeds
     $2^n \le 2 \cdot (2^{m_0})^{1/(1-\alpha)} / \delta_0 = 4 \cdot 2^{2 m_0} \delta \le
     c_2 (2^{m_0} e \delta + 1)^{k_2}$ (`card_le` ✓), uniform sample length
     $t = 2^d \le n \cdot \operatorname{poly}(k/\varepsilon) =
     \operatorname{poly}(m_0 + 1, e, \lfloor\log_2 \delta\rfloor + 1) \le
     c_2 ((m_0 + 1) \cdot e \cdot (\lfloor\log_2 \delta\rfloor + 1))^{k_2}$ (`len_eq` ✓,
     `len_le` ✓), and polynomial-time evaluation in tracked operation count at most
     $c_2 (2^{m_0} e \delta + 1)^{k_2}$ (`cost_le`).

## Transcription Notes (`(i)`–`(v)`)

Transcription notes:
- **(i)** `Stage1Sampler.len_eq` (uniform sequence length across all $T \in \text{fam } N\ e\ \delta$)
  is not part of `[AFKLM24, Lemma 4.4]`'s subset statement; in `paper.tex` (§8 (i) and Appendix B
  `\label{app:sampler}`), uniform length $N_1 = 2^p$ is obtained by running `[AFKLM24, Lemma 4.4]` at
  accuracy $\varepsilon / 4$ and padding each subset (and also holds directly for the underlying
  `[GW97]` walk construction), and is used by `composeFamilies_isSeqSampler`;
- **(ii)** `Stage2Sampler` is stated directly over `Fin (2 ^ m)` (representing `{0, 1}^m` as in
  `[GUV09, Theorem 1.5]` + `[Vadhan 2012, Corollary 6.24(1)]`), and its extension to an arbitrary
  Stage-1 sample length `Fin M` ($M \ge 1$, taking $m = \lfloor\log_2(2Me)\rfloor + 1$, projecting
  $x \mapsto x \bmod M$, and absorbing the $\le M / 2^m \le 1/(2e)$ total-variation bias into
  $\varepsilon$) is machine-checked in `BMMGrid/ObliviousSampler.lean`
  (`expectSet_univ_modFin_sub_abs_le`, `isSeqSampler_modFinFam`, `stage2FinM_sampler`);
- **(iii)** `cost_le` is a `CostM` transcription of the sources' RAM time bounds (assuming the
  cited constructions are implemented in `CostM` within the stated polynomial bounds, and with
  universal parameters $N \ge 1$ for `Stage1Sampler.cost_le`, $m \ge 0, e \ge 1, \delta \ge 1$ where
  $e = 1$ or $\delta = 1$ is trivial);
- **(iv)** no Lean inhabitant of `Stage1Sampler` or `Stage2Sampler` is provided (trivial exhaustive
  or product-space Chebyshev families do not satisfy the joint linear-in-$N$ family-size, $N$-free
  sample-length, and $\operatorname{poly}(\log \delta)$ sample-length bounds, so any inhabitant
  amounts to formalizing `[GW97]` / `[GUV09]`) — conditional on `(i)`–`(iii)`, `(v)` & sources;
- **(v)** Vadhan's Definition 3.29 (`[Vadhan 2012, Section 3.5.4, printed p. 71 (PDF p. 74)]`; see
  `lean/SOURCES.md` §3) is *one-sided*
  ($\Pr[\frac{1}{t}\sum_{i=1}^t f(z_i) > \mu(f) + \varepsilon] \le \delta$); the two-sided
  `IsSeqSampler` bound follows "up to a factor of 2 in the failure probability $\delta$" (Vadhan,
  p. 71, via $1 - f$), absorbed into $c_2, k_2$.

All reduction logic — transporting from `Fin |Y|` to an arbitrary finite set `Y : Finset β`,
reducing Stage 2 from `Fin (2 ^ m)` to arbitrary `Fin M` (`stage2FinM_sampler`), composing Stage 1
and Stage 2 via index lookup (`twoStage_compose`), triangle-inequality accuracy addition,
union-bound failure probability addition, and instantiation at the `EstimateNorm` (`ApproxGridNorm`)
parameters (`approxGridNorm_sampler_inst`) — is machine-checked in `BMMGrid/ObliviousSampler.lean`.
-/

namespace BMMGrid

open scoped BigOperators

/-- Empirical average of a real-valued function $g : \beta \to \mathbb{R}$ over a finite sample
sequence $T : \text{List } \beta$:
$$\mathbb{E}_{y \sim T}[g(y)] := \frac{1}{|T|} \sum_{y \in T} g(y)$$
(conventionally $0$ when $T = []$). -/
noncomputable def expectSeq {β : Type*} (T : List β) (g : β → ℝ) : ℝ :=
  (T.map g).sum / (T.length : ℝ)

/-- **$(\varepsilon, \delta)$-Oblivious Sequence Sampler (`IsSeqSampler`, `paper.tex` Lemma 3.3
`\label{lem:two-stage-sampler}`, `\eqref{eq:oblivious-sampler}`, §3.3)**:
A non-empty finite family `fam : List (List β)` of sample sequences in `U` is an
$(\varepsilon, \delta)$-sampler for `U : Finset β` if:
1. `fam ≠ []`,
2. every sequence `T ∈ fam` is supported in `U` (`∀ y ∈ T, y ∈ U`) and is non-empty whenever
   `U.Nonempty`, and
3. for every test function $g : \beta \to [0, 1]$ on $U$, the number of sequences $T \in \text{fam}$
   with $|\mathbb{E}_{y \sim T}[g(y)] - \mathbb{E}_{y \in U}[g(y)]| > \varepsilon$ is at most
   $\delta \cdot |\text{fam}|$. -/
def IsSeqSampler {β : Type*} (U : Finset β) (fam : List (List β)) (ε δ : ℝ) : Prop :=
  fam ≠ [] ∧
  (∀ T ∈ fam, (∀ y ∈ T, y ∈ U) ∧ (U.Nonempty → T ≠ [])) ∧
  ∀ g : β → ℝ, (∀ y ∈ U, 0 ≤ g y ∧ g y ≤ 1) →
    open Classical in
    (((fam.filter (fun T => |expectSeq T g - expectSet U g| > ε)).length : ℝ) ≤
      δ * (fam.length : ℝ))

/-- **Cited Theorem 1: Stage-1 Linear-Seed Sampler on `Fin N`
(`[AFKLM24, arXiv:2311.09095v2, Section 4.1, Lemma 4.4, PDF p. 17]` = `[Goldreich–Wigderson 1997,
Section 3; STOC 1994]`, `paper.tex` §3.3 Lemma 3.3 & Appendix B `\label{app:sampler}`; see
`lean/SOURCES.md` §1)**:
Source statement (`[AFKLM24, Lemma 4.4, PDF p. 17]`): *"Lemma 4.4 (Oblivious Sampling [41]). Let
$X$ be a set and let $\delta, \varepsilon > 0$. There is a deterministic algorithm computing, in
time $|X| \cdot \operatorname{poly}(\varepsilon^{-1}, \delta^{-1}, \log |X|)$, a family $\mathcal{S}$
of subsets $S \subseteq X$ such that
1. $|\mathcal{S}| \le |X| \cdot \operatorname{poly}(\varepsilon^{-1}, \delta^{-1})$,
2. $|S| \le \operatorname{poly}(\varepsilon^{-1}, \delta^{-1})$ for all $S \in \mathcal{S}$,
3. For every function $f : X \to [0, 1]$,
$\Pr_{S \in \mathcal{S}}[\mathbb{E}_{x \in X} f(x) = \mathbb{E}_{x \in S} f(x) \pm \varepsilon] \ge 1 - \delta$."*
See module header Transcription Notes `(i)`, `(iii)`, and `(iv)` for `len_eq` and `cost_le`. -/
structure Stage1Sampler where
  c : ℕ
  k : ℕ
  fam : (N invEps invDelta : ℕ) → List (List (Fin N))
  famTracked : (N invEps invDelta : ℕ) → CostM (List (List (Fin N)))
  fam_eq : ∀ N e δ, (famTracked N e δ).1 = fam N e δ
  len : (N invEps invDelta : ℕ) → ℕ
  len_eq : ∀ N e δ, ∀ T ∈ fam N e δ, T.length = len N e δ
  len_le : ∀ N e δ, len N e δ ≤ c * (e * δ + 1) ^ k
  card_le : ∀ N e δ, (fam N e δ).length ≤ N * c * (e * δ + 1) ^ k
  cost_le : ∀ N e δ, 1 ≤ N → (famTracked N e δ).2 ≤ N * c * (e * δ * (Nat.log 2 N + 1) + 1) ^ k
  sampler : ∀ N e δ, 1 ≤ N → 1 ≤ e → 1 ≤ δ →
    IsSeqSampler Finset.univ (fam N e δ) (1 / (e : ℝ)) (1 / (δ : ℝ))

/-- **Cited Theorem 2: Stage-2 Extractor-Based Sampler on `Fin (2 ^ m)` (`{0, 1}^m`)
(`[GUV09, JACM 56(4), Art. 20, Theorem 1.5, p. 4 (p. 20:4) & Theorem 5.12]` + `[Vadhan,
Pseudorandomness, 2012, Corollary 6.24, printed p. 186 (PDF p. 189)]` + `[Zuckerman 1997,
Lemma 2.6 & Proposition 2.7]`; historical context: `[Zuckerman 1997, Theorem 3.17, p. 15]`,
`paper.tex` §3.3 Lemma 3.3 & Appendix B `\label{app:sampler}`; see `lean/SOURCES.md` §§2–4)**:
Source statements:
- `[GUV09, Theorem 1.5, JACM 56(4), Art. 20, p. 4 (p. 20:4)]`: *"Theorem 1.5 (Main extractor
  result). For every constant $\alpha > 0$, and all positive integers $n, k$ and all
  $\varepsilon > 0$, there is an explicit construction of a $(k, \varepsilon)$ extractor
  $E : \{0, 1\}^n \times \{0, 1\}^d \to \{0, 1\}^m$ with $d \le \log n + O(\log(k/\varepsilon))$
  and $m \ge (1 - \alpha)k$."*
- `[Vadhan 2012, Corollary 6.24, printed p. 186 (PDF p. 189)]`: *"Corollary 6.24. Let
  $\mathrm{Ext} : [N] \times [D] \to [M]$ and $\mathrm{Samp} : [N] \to [M]^D$ be such that
  $\mathrm{Ext}(x, y) = \mathrm{Samp}(x)_y$. Then: (1) If $\mathrm{Ext}$ is a $(k, \varepsilon)$
  extractor, then $\mathrm{Samp}$ is a $(K/N, \varepsilon)$ averaging sampler, where $K = 2^k$.
  (2) If $\mathrm{Samp}$ is a $(K/N, \varepsilon)$ boolean averaging sampler, then $\mathrm{Ext}$ is
  a $(k + \log(1/\varepsilon), 2\varepsilon)$ extractor. (3) If $\mathrm{Samp}$ is a
  $(\delta, \varepsilon)$ boolean averaging sampler, then $\mathrm{Samp}$ is a
  $(\delta/\varepsilon, 2\varepsilon)$ averaging sampler."*
See the module header for the 4-line derivation of `card_le` and `len_le` from `[GUV09, Theorem 1.5]`
+ `[Vadhan 2012, Corollary 6.24(1)]` and Transcription Notes `(ii)`–`(v)` for the machine-checked
reduction from `Fin (2 ^ m)` to arbitrary `Fin M` (`stage2FinM_sampler` in
`BMMGrid/ObliviousSampler.lean`), `cost_le`, and the one-sided to two-sided factor of 2 in $\delta$. -/
structure Stage2Sampler where
  c : ℕ
  k : ℕ
  fam : (m invEps invDelta : ℕ) → List (List (Fin (2 ^ m)))
  famTracked : (m invEps invDelta : ℕ) → CostM (List (List (Fin (2 ^ m))))
  fam_eq : ∀ m e δ, (famTracked m e δ).1 = fam m e δ
  len : (m invEps invDelta : ℕ) → ℕ
  len_eq : ∀ m e δ, ∀ T ∈ fam m e δ, T.length = len m e δ
  len_le : ∀ m e δ, len m e δ ≤ c * ((m + 1) * e * (Nat.log 2 δ + 1)) ^ k
  card_le : ∀ m e δ, (fam m e δ).length ≤ c * (2 ^ m * e * δ + 1) ^ k
  cost_le : ∀ m e δ, (famTracked m e δ).2 ≤ c * (2 ^ m * e * δ + 1) ^ k
  sampler : ∀ m e δ, 1 ≤ e → 1 ≤ δ →
    IsSeqSampler Finset.univ (fam m e δ) (1 / (e : ℝ)) (1 / (δ : ℝ))

end BMMGrid
