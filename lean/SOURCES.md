# Primary Literature Sources for `BMMGrid/CitedResults.lean`

This file records the stable bibliographic locators, direct PDF fetch URLs, PDF
SHA-256 digests, text extraction command (`pdftotext -layout <file>.pdf
<file>.txt`), printed/PDF page numbers, and verbatim statements for the external
pseudorandomness results cited in `BMMGrid/CitedResults.lean` (corresponding to
Section 3.3 Lemma 3.3 `\label{lem:two-stage-sampler}`,
`\eqref{eq:oblivious-sampler}`–`\eqref{eq:two-stage-sampler}`, and Appendix B
`\label{app:sampler}` of `paper.tex`).

--------------------------------------------------------------------------------

## 1. `[AFKLM24, Lemma 4.4]` (Stage 1 — Linear-Seed Oblivious Sampler)

-   **Authors**: Amir Abboud, Nick Fischer, Zander Kelley, Shachar Lovett, and
    Raghu Meka.
-   **Title**: *New Graph Decompositions and Combinatorial Boolean Matrix
    Multiplication Algorithms* (STOC 2024, pp. 935–943; `arXiv:2311.09095v2`
    [cs.DS], 27 May 2024; citing `[41]` = Oded Goldreich and Avi Wigderson,
    *Tiny Families of Functions with Random Properties: A Quality-Size Trade-off
    for Hashing*, Random Structures & Algorithms 11(4):315–343, 1997, DOI:
    `10.1002/(SICI)1098-2418(199712)11:4<315::AID-RSA3>3.0.CO;2-1`; preliminary
    version in STOC 1994, pp. 574–583).
-   **Direct PDF URL**: `https://arxiv.org/pdf/2311.09095v2.pdf`
-   **Locator**: Section 4.1, **Lemma 4.4**, **PDF p. 17** (`pdftotext -layout`
    lines 890–903).
-   **PDF SHA-256**:
    `7665d9c5dfefbe59a42df36add2da3ad54fbe74b1b160919bc5d3c1b2d634825`
-   **Verbatim Statement**:

    > **Lemma 4.4 (Oblivious Sampling [41]).** Let $X$ be a set and let $\delta,
    > \varepsilon > 0$. There is a deterministic algorithm computing, in time
    > $|X| \cdot \mathrm{poly}(\varepsilon^{-1}, \delta^{-1}, \log |X|)$,
    > a family $\mathcal{S}$ of subsets $S \subseteq X$ such that 1.
    > $|\mathcal{S}| \le |X| \cdot \mathrm{poly}(\varepsilon^{-1},
    > \delta^{-1})$, 2. $|S| \le \mathrm{poly}(\varepsilon^{-1},
    > \delta^{-1})$ for all $S \in \mathcal{S}$, 3. For every function $f : X
    > \to [0, 1]$, $\Pr_{S \in \mathcal{S}}[\mathbb{E}_{x \in X} f(x) =
    > \mathbb{E}_{x \in S} f(x) \pm \varepsilon] \ge 1 - \delta$.

--------------------------------------------------------------------------------

## 2. `[GUV09, Theorem 1.5 & Theorem 5.12]` (Stage 2 — Unconditional Lossless-Condenser Extractor)

-   **Authors**: Venkatesan Guruswami, Christopher Umans, and Salil Vadhan.
-   **Title**: *Unbalanced Expanders and Randomness Extractors from
    Parvaresh–Vardy Codes*.
-   **Direct PDF URL**:
    `https://people.seas.harvard.edu/~salil/research/PVcondenser-jacm.pdf`
-   **Locator**: *Journal of the ACM (JACM)*, Vol. 56, No. 4, **Article 20**,
    pp. 20:1–20:34 (July 2009), DOI: `10.1145/1538902.1538904` — **Theorem
    1.5**, **p. 4 (Article p. 20:4)** (`pdftotext -layout` lines 162–164); see
    also **Theorem 5.12** (cited alongside Theorem 1.5 in Appendix B
    `\label{app:sampler}` of `paper.tex`; cf. `[Vadhan 2012, Theorem 6.36]`).
-   **PDF SHA-256**:
    `56555a9db827b8e354817f39cadc6a4ee2322ea6db55839c1857e293930d6931`
-   **Verbatim Statement (`Theorem 1.5`, p. 4 / Article p. 20:4)**:

    > **Theorem 1.5 (Main extractor result).** For every constant $\alpha > 0$,
    > and all positive integers $n, k$ and all $\varepsilon > 0$, there is an
    > explicit construction of a $(k, \varepsilon)$ extractor $E : \{0, 1\}^n
    > \times \{0, 1\}^d \to \{0, 1\}^m$ with $d \le \log n +
    > O(\log(k/\varepsilon))$ and $m \ge (1 - \alpha)k$.

--------------------------------------------------------------------------------

## 3. `[Vadhan 2012, Definition 3.29 & Corollary 6.24]` (Stage 2 — Extractor-to-Averaging-Sampler Equivalence)

-   **Author**: Salil P. Vadhan.
-   **Title**: *Pseudorandomness*.
-   **Direct PDF URL**:
    `https://people.seas.harvard.edu/~salil/pseudorandomness/pseudorandomness-published-Dec12.pdf`
-   **Locator**: *Foundations and Trends in Theoretical Computer Science*, Vol.
    7, Nos. 1–3 (2012), pp. 1–336, DOI: `10.1561/0400000010`:
    -   **Definition 3.29**: Section 3.5.4, **printed p. 71 (PDF p. 74)**
        (`pdftotext -layout` lines 2796–2822).
    -   **Corollary 6.24**: Section 6.2.4, **printed p. 186 (PDF p. 189)**
        (`pdftotext -layout` lines 7356–7364).
-   **PDF SHA-256**:
    `bf2ce542208824ebf39ce132aae2d26a3b90bc04d3496a4ec05361f27e62118c`
-   **Verbatim Statement (`Corollary 6.24`, printed p. 186 / PDF p. 189)**:

    > **Corollary 6.24.** Let $\mathrm{Ext} : [N] \times [D] \to [M]$ and
    > $\mathrm{Samp} : [N] \to [M]^D$ be such that $\mathrm{Ext}(x, y) =
    > \mathrm{Samp}(x)_y$. Then: 1. If $\mathrm{Ext}$ is a $(k, \varepsilon)$
    > extractor, then $\mathrm{Samp}$ is a $(K/N, \varepsilon)$ averaging
    > sampler, where $K = 2^k$. 2. If $\mathrm{Samp}$ is a $(K/N, \varepsilon)$
    > boolean averaging sampler, then $\mathrm{Ext}$ is a $(k +
    > \log(1/\varepsilon), 2\varepsilon)$ extractor. 3. If $\mathrm{Samp}$ is a
    > $(\delta, \varepsilon)$ boolean averaging sampler, then $\mathrm{Samp}$ is
    > a $(\delta/\varepsilon, 2\varepsilon)$ averaging sampler.

-   **Primary-Source Excerpt (`Definition 3.29` followed by the remark on two-sided error, printed p. 71 / PDF p. 74)**:

    > **Definition 3.29.** A sampler $\mathrm{Samp}$ for domain size $M$ is
    > given "coin tosses" $x \xleftarrow{R} [N]$ and outputs a sequence of
    > samples $z_1, \dots, z_t \in [M]$. We say that $\mathrm{Samp} : [N] \to
    > [M]^t$ is a $(\delta, \varepsilon)$ averaging sampler if for every
    > function $f : [M] \to [0, 1]$, we have $$\Pr_{(z_1, \dots, z_t)
    > \xleftarrow{R} \mathrm{Samp}(U_{[N]})} \left[\frac{1}{t}\sum_{i=1}^t
    > f(z_i) > \mu(f) + \varepsilon\right] \le \delta.$$ ... However, a
    > guarantee in the other direction also follows by considering the function
    > $1 - f$. Thus, up to a factor of 2 in the failure probability $\delta$,
    > the above definition is equivalent to requiring that $\Pr[|(1/t) \cdot
    > \sum_i f(z_i) - \mu(f)| > \varepsilon] \le \delta$.

--------------------------------------------------------------------------------

## 4. `[Zuckerman 1997, Lemma 2.6, Proposition 2.7 & Theorem 3.17]` (Extractor-to-Sampler Reduction & Historical Context)

-   **Author**: David Zuckerman.
-   **Title**: *Randomness-Optimal Oblivious Sampling*.
-   **Direct PDF URL**: `https://www.cs.utexas.edu/~diz/pubs/sampler.pdf`
-   **Locator**: *Random Structures & Algorithms*, Vol. 11, No. 4 (1997), pp.
    345–367 (preliminary version in STOC 1996; author preprint PDF: **Lemma 2.6
    & Proposition 2.7**, Section 2, **pp. 5–6**; **Theorem 3.17**, Section 3.4,
    **p. 15**, `pdftotext -layout` lines 730–734 between the p. 14 footer at
    line 715 and the p. 15 footer at line 767).
-   **PDF SHA-256**:
    `0e52381c327d5600ddc0a1d8ccd462de05f21d88a6eb63003b0a8ec602abbf5f`
-   **Verbatim Statement (`Theorem 3.17`, p. 15)**:

    > **Theorem 3.17.** There is a constant $c$ such that for any $\beta > 0$
    > and any parameters $\gamma = \gamma(m)$, $\varepsilon = \varepsilon(m)$,
    > and $\alpha = \alpha(m)$ with $m^{-1/2} \log^* m \le \alpha \le 1/2$ and
    > $\varepsilon \ge \exp(-\alpha^{\log^* m} m^{1-\beta})$, there exists a
    > strong $(n, m, d, \gamma, \varepsilon)$-oblivious sampler which runs in
    > $\mathrm{NC}$ and uses only $n = (1 + \alpha)(m + \log \gamma^{-1})$
    > random bits and outputs $d = ((m + \log
    > \gamma^{-1})/\varepsilon)^{c_\alpha}$ sample points, where $c_\alpha =
    > c(\log \alpha^{-1})/\alpha$.

    *(Note: Section 3.3 and Appendix B of `paper.tex` cite
    `[Zuckerman 1997, Lemma 2.6 & Proposition 2.7]` (with Appendix B also citing
    `[Vadhan 2012, Corollary 6.24]`) for the general extractor-to-sampler
    equivalence; `Theorem 3.17` is cited only as historical context in
    `BMMGrid/CitedResults.lean`, whereas the unconditional `Stage2Sampler`
    hypothesis is derived from `[GUV09, Theorem 1.5]` +
    `[Vadhan 2012, Corollary 6.24(1)]`, which have no side conditions on
    $\alpha$ or $\varepsilon$.)*
