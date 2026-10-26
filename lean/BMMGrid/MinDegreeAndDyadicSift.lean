import BMMGrid.ApproxGridNorm

/-!
# Sections 3.3 & 4.2: Minimum-Degree Pruning and Dyadic Sifting (`BMMGrid/MinDegreeAndDyadicSift.lean`)

This module formalizes:
1. Algorithm 1 (`minDegree`, `minDegreeTracked`) and Lemma 3.2 (`lem_min_degree`,
   `\label{lem:min-degree}`, §3.3).
2. Algorithm 3 (`dyadicSift`, `dyadicSiftTracked`) and Lemma 4.2 (`lem_dyadic_sift`,
   `\label{lem:dyadic-sift}`, `\eqref{eq:dyadic-sift-guarantees}`, `\eqref{eq:overview-u2d}`,
   `\eqref{eq:grid-norm-fubini}`, §4.2) of `paper.tex`.
-/

namespace BMMGrid

open scoped BigOperators

/-!
## Section 3.3: Minimum-Degree Pruning (`MinDegree`, Algorithm 1 & Lemma 3.2, §3.3)
-/

section MinDegree

variable {α β : Type*}

/-- Predicate that a real matrix `A` on `X × Y` has binary entries in `{0, 1}`. -/
def IsBinaryMatrix (X : Finset α) (Y : Finset β) (A : α → β → ℝ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, A x y = 0 ∨ A x y = 1

/-- Predicate that a real matrix `M` on `U × V` has entries in `[0, 1]`. -/
def IsUnitIntervalMatrix (U : Finset α) (V : Finset β) (M : α → β → ℝ) : Prop :=
  ∀ u ∈ U, ∀ v ∈ V, 0 ≤ M u v ∧ M u v ≤ 1

lemma IsBinaryMatrix.to_unitInterval {X : Finset α} {Y : Finset β} {A : α → β → ℝ}
    (hA : IsBinaryMatrix X Y A) : IsUnitIntervalMatrix X Y A := by
  intro x hx y hy
  rcases hA x hx y hy with h0 | h1
  · rw [h0]; exact ⟨le_rfl, zero_le_one⟩
  · rw [h1]; exact ⟨zero_le_one, le_rfl⟩

lemma isBinaryMatrix_bmatToReal (X : Finset α) (Y : Finset β) (A : α → β → Bool) :
    IsBinaryMatrix X Y (bmatToReal A) := by
  intro x _ y _
  unfold bmatToReal boolToReal
  cases A x y <;> simp

lemma IsUnitIntervalMatrix.mono {U U' : Finset α} {V V' : Finset β} {M : α → β → ℝ}
    (hM : IsUnitIntervalMatrix U V M) (hU : U' ⊆ U) (hV : V' ⊆ V) :
    IsUnitIntervalMatrix U' V' M :=
  fun u hu v hv => hM u (hU hu) v (hV hv)

lemma rowDeg_nonneg_of_unitInterval {U : Finset α} {V : Finset β} {M : α → β → ℝ}
    (hM : IsUnitIntervalMatrix U V M) {u : α} (hu : u ∈ U) :
    0 ≤ rowDeg V M u :=
  expectSet_nonneg (fun v hv => (hM u hu v hv).1)

lemma rowDeg_le_one_of_unitInterval {U : Finset α} {V : Finset β} {M : α → β → ℝ}
    (hV : V.Nonempty) (hM : IsUnitIntervalMatrix U V M) {u : α} (hu : u ∈ U) :
    rowDeg V M u ≤ 1 :=
  expectSet_le_of_le hV (fun v hv => (hM u hu v hv).2)

lemma matDensity_nonneg_of_unitInterval {U : Finset α} {V : Finset β} {M : α → β → ℝ}
    (hM : IsUnitIntervalMatrix U V M) :
    0 ≤ matDensity U V M :=
  expectSet_nonneg (fun _ hu => rowDeg_nonneg_of_unitInterval hM hu)

/-- The subset of rows in `U'` violating the $\varepsilon_0$-min-degree threshold
$\deg_{M[U', V]}(u) < (1 - \varepsilon_0)\mathbb{E}[M[U', V]]$ (`paper.tex`, Algorithm 1, Line 2, §3.3).
Note that since $V$ is fixed throughout Algorithm 1, $\deg_{M[U', V]}(u) = \text{rowDeg } V\ M\ u$
is a precomputed 1D array over $u \in U$ and $\mathbb{E}[M[U', V]] = \text{expectSet } U'\ (\text{rowDeg } V\ M)$
is its 1D average over $U'$. -/
noncomputable def minDegreeBadRows (U' : Finset α) (V : Finset β) (M : α → β → ℝ) (ε₀ : ℝ) :
    Finset α := by
  classical
  exact U'.filter (fun u => rowDeg V M u < (1 - ε₀) * matDensity U' V M)

lemma mem_minDegreeBadRows_iff {U' : Finset α} {V : Finset β} {M : α → β → ℝ} {ε₀ : ℝ} {u : α} :
    u ∈ minDegreeBadRows U' V M ε₀ ↔
      u ∈ U' ∧ rowDeg V M u < (1 - ε₀) * matDensity U' V M := by
  classical
  unfold minDegreeBadRows
  exact Finset.mem_filter

/-- Deterministic list-fold minimum-degree selector over `u₀ :: candidates` (avoiding
`Classical.choose`). -/
noncomputable def chooseMinBadRowList (u₀ : α) (candidates : List α) (deg : α → ℝ) : α :=
  letI := Classical.dec
  candidates.foldl (fun best u => if deg u < deg best then u else best) u₀

lemma chooseMinBadRowList_mem (u₀ : α) (candidates : List α) (deg : α → ℝ) :
    chooseMinBadRowList u₀ candidates deg ∈ u₀ :: candidates := by
  unfold chooseMinBadRowList
  induction candidates generalizing u₀ with
  | nil => simp
  | cons a tl ih =>
    simp only [List.foldl_cons]
    split_ifs
    · exact List.mem_cons_of_mem u₀ (ih a)
    · rcases List.mem_cons.mp (ih u₀) with heq | hmem
      · rw [heq]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem u₀ (List.mem_cons_of_mem a hmem)

lemma finset_toList_ne_nil {γ : Type*} {s : Finset γ} (hs : s.Nonempty) : s.toList ≠ [] := by
  intro h
  rcases hs with ⟨a, ha⟩
  have hmem := Finset.mem_toList.mpr ha
  rw [h] at hmem
  exact List.not_mem_nil hmem

/-- Minimum-degree vertex selection among the violating rows `minDegreeBadRows U' V M ε₀`
via deterministic list fold `chooseMinBadRowList` (`paper.tex`, Algorithm 1, Line 3, §3.3). -/
noncomputable def chooseMinBadRow (U' : Finset α) (V : Finset β) (M : α → β → ℝ) (ε₀ : ℝ)
    (hbad : (minDegreeBadRows U' V M ε₀).Nonempty) : α :=
  let cands := (minDegreeBadRows U' V M ε₀).toList
  have hne : cands ≠ [] := finset_toList_ne_nil hbad
  chooseMinBadRowList (cands.head hne) cands.tail (rowDeg V M)

lemma chooseMinBadRow_mem (U' : Finset α) (V : Finset β) (M : α → β → ℝ) (ε₀ : ℝ)
    (hbad : (minDegreeBadRows U' V M ε₀).Nonempty) :
    chooseMinBadRow U' V M ε₀ hbad ∈ minDegreeBadRows U' V M ε₀ := by
  unfold chooseMinBadRow
  dsimp only
  set cands := (minDegreeBadRows U' V M ε₀).toList
  have hne : cands ≠ [] := finset_toList_ne_nil hbad
  have hmem := chooseMinBadRowList_mem (cands.head hne) cands.tail (rowDeg V M)
  rw [List.cons_head_tail] at hmem
  exact Finset.mem_toList.mp hmem

/-- **Proof of Lemma 3.2 (`paper.tex`, §3.3)**:
When `|U'| = 1` (say `U' = {u₀}`), $\deg_{M'}(u_0) = \mathbb{E}[M'] \ge (1 - \varepsilon_0)\mathbb{E}[M']$,
so `minDegreeBadRows U' V M ε₀` is empty; hence whenever `minDegreeBadRows U' V M ε₀` is nonempty,
`|U'| ≥ 2`. -/
lemma two_le_card_of_minDegreeBadRows_nonempty {U' : Finset α} {V : Finset β} {M : α → β → ℝ}
    {ε₀ : ℝ} (hε₀ : 0 ≤ ε₀) (hM : ∀ u ∈ U', 0 ≤ rowDeg V M u)
    (hbad : (minDegreeBadRows U' V M ε₀).Nonempty) :
    2 ≤ U'.card := by
  rcases hbad with ⟨u, hu⟩
  rw [mem_minDegreeBadRows_iff] at hu
  have hpos : 1 ≤ U'.card := Finset.card_pos.mpr ⟨u, hu.1⟩
  by_contra hlt
  have hcard1 : U'.card = 1 := by omega
  rcases Finset.card_eq_one.mp hcard1 with ⟨u₀, hu₀⟩
  subst hu₀
  have hu_eq : u = u₀ := Finset.mem_singleton.mp hu.1
  subst hu_eq
  have hdens : matDensity {u} V M = rowDeg V M u := by
    unfold matDensity expectSet
    simp
  have hdeg_nonneg : 0 ≤ rowDeg V M u := hM u (Finset.mem_singleton_self u)
  have hle : (1 - ε₀) * matDensity {u} V M ≤ rowDeg V M u := by
    rw [hdens]
    nlinarith
  linarith [hu.2]

/-- **Proof of Lemma 3.2 (`paper.tex`, §3.3)**:
Removing a vertex `u ∈ U'` with $\deg_{M'}(u) < (1 - \varepsilon_0)\mathbb{E}[M'] \le \mathbb{E}[M']$
monotonically increases (or preserves) the average density $\mathbb{E}[M']$. -/
lemma matDensity_erase_ge_of_badRow [DecidableEq α] {U' : Finset α} {V : Finset β}
    {M : α → β → ℝ} {ε₀ : ℝ} (hε₀ : 0 ≤ ε₀) (hM : ∀ w ∈ U', 0 ≤ rowDeg V M w)
    {u : α} (hu : u ∈ minDegreeBadRows U' V M ε₀) :
    matDensity U' V M ≤ matDensity (U'.erase u) V M := by
  have hcard2 : 2 ≤ U'.card :=
    two_le_card_of_minDegreeBadRows_nonempty hε₀ hM ⟨u, hu⟩
  rw [mem_minDegreeBadRows_iff] at hu
  have hdens_nonneg : 0 ≤ matDensity U' V M := expectSet_nonneg hM
  have hu_le : rowDeg V M u ≤ matDensity U' V M := by nlinarith [hu.2]
  have hcard_erase : (U'.erase u).card = U'.card - 1 := Finset.card_erase_of_mem hu.1
  have hcard_pos : (0 : ℝ) < (U'.card : ℝ) := by positivity
  have hcard_erase_pos : (0 : ℝ) < ((U'.erase u).card : ℝ) := by
    rw [hcard_erase]
    have : 1 ≤ U'.card - 1 := by omega
    exact Nat.cast_pos.mpr this
  have hsum : ∑ w ∈ U', rowDeg V M w =
      rowDeg V M u + ∑ w ∈ U'.erase u, rowDeg V M w := by
    rw [add_comm, Finset.sum_erase_add _ _ hu.1]
  have hsum_dens : matDensity U' V M * (U'.card : ℝ) = ∑ w ∈ U', rowDeg V M w := by
    unfold matDensity expectSet
    exact div_mul_cancel₀ _ hcard_pos.ne'
  have hsum_erase : matDensity (U'.erase u) V M * ((U'.erase u).card : ℝ) =
      ∑ w ∈ U'.erase u, rowDeg V M w := by
    unfold matDensity expectSet
    exact div_mul_cancel₀ _ hcard_erase_pos.ne'
  have hcard_cast : ((U'.erase u).card : ℝ) = (U'.card : ℝ) - 1 := by
    rw [hcard_erase, Nat.cast_sub (by omega), Nat.cast_one]
  nlinarith

/-- While-loop body of Algorithm 1 (`MinDegree`, `paper.tex` §3.3). -/
noncomputable def minDegreeLoop [DecidableEq α]
    (U : Finset α) (V : Finset β) (M : α → β → ℝ) (ε₀ γ₀ : ℝ)
    (U' : Finset α) : Finset α × ℕ :=
  if hbad : (minDegreeBadRows U' V M ε₀).Nonempty then
    if ((U'.erase (chooseMinBadRow U' V M ε₀ hbad)).card : ℝ) ≤ (1 - γ₀) * (U.card : ℝ) then
      (U'.erase (chooseMinBadRow U' V M ε₀ hbad), 2)
    else
      minDegreeLoop U V M ε₀ γ₀ (U'.erase (chooseMinBadRow U' V M ε₀ hbad))
  else
    (U', 1)
termination_by U'.card
decreasing_by
  have hu : chooseMinBadRow U' V M ε₀ hbad ∈ U' :=
    (mem_minDegreeBadRows_iff.mp (chooseMinBadRow_mem U' V M ε₀ hbad)).1
  exact Finset.card_erase_lt_of_mem hu

/-- Cost-tracked while-loop of Algorithm 1 (`MinDegree`, `paper.tex` §3.3) in `CostM`.
After precomputing row degrees in $O(|U||V|)$ time, each peeling iteration takes $O(|U'|)$ time. -/
noncomputable def minDegreeLoopTracked [DecidableEq α]
    (U : Finset α) (V : Finset β) (M : α → β → ℝ) (ε₀ γ₀ : ℝ)
    (U' : Finset α) : CostM (Finset α × ℕ) :=
  if hbad : (minDegreeBadRows U' V M ε₀).Nonempty then
    if ((U'.erase (chooseMinBadRow U' V M ε₀ hbad)).card : ℝ) ≤ (1 - γ₀) * (U.card : ℝ) then
      scanFinsetTracked U' (U'.erase (chooseMinBadRow U' V M ε₀ hbad), 2)
    else
      CostM.bind (scanFinsetTracked U' ()) (fun _ =>
        minDegreeLoopTracked U V M ε₀ γ₀ (U'.erase (chooseMinBadRow U' V M ε₀ hbad)))
  else
    scanFinsetTracked U' (U', 1)
termination_by U'.card
decreasing_by
  have hu : chooseMinBadRow U' V M ε₀ hbad ∈ U' :=
    (mem_minDegreeBadRows_iff.mp (chooseMinBadRow_mem U' V M ε₀ hbad)).1
  exact Finset.card_erase_lt_of_mem hu

/-- **Algorithm 1 (`MinDegree`, `paper.tex` §3.3)**:
Minimum-degree pruning on $M[U, V]$ with parameters $\varepsilon_0 \in (0, 1)$ and $\gamma_0 \in (0, 1/2]$. -/
noncomputable def minDegree [DecidableEq α]
    (U : Finset α) (V : Finset β) (M : α → β → ℝ) (ε₀ γ₀ : ℝ) : Finset α × ℕ :=
  minDegreeLoop U V M ε₀ γ₀ U

/-- Cost-tracked Algorithm 1 (`minDegreeTracked`, `paper.tex` §3.3) in `CostM`:
charges $|U||V| + 1$ for initial row-degree computation plus the peeling loop work. -/
noncomputable def minDegreeTracked [DecidableEq α]
    (U : Finset α) (V : Finset β) (M : α → β → ℝ) (ε₀ γ₀ : ℝ) : CostM (Finset α × ℕ) :=
  CostM.bind (scanMatrixTracked U V ()) (fun _ =>
    minDegreeLoopTracked U V M ε₀ γ₀ U)

@[simp]
lemma minDegreeLoopTracked_fst [DecidableEq α]
    (U : Finset α) (V : Finset β) (M : α → β → ℝ) (ε₀ γ₀ : ℝ) (U' : Finset α) :
    (minDegreeLoopTracked U V M ε₀ γ₀ U').1 = minDegreeLoop U V M ε₀ γ₀ U' := by
  induction h : U'.card using Nat.strong_induction_on generalizing U' with
  | _ k ih =>
    rw [minDegreeLoopTracked, minDegreeLoop]
    split_ifs with hbad hthresh
    · rfl
    · dsimp only [CostM.bind_fst]
      have hu : chooseMinBadRow U' V M ε₀ hbad ∈ U' :=
        (mem_minDegreeBadRows_iff.mp (chooseMinBadRow_mem U' V M ε₀ hbad)).1
      exact ih (U'.erase (chooseMinBadRow U' V M ε₀ hbad)).card
        (h ▸ Finset.card_erase_lt_of_mem hu) _ rfl
    · rfl

@[simp]
theorem minDegreeTracked_fst [DecidableEq α]
    (U : Finset α) (V : Finset β) (M : α → β → ℝ) (ε₀ γ₀ : ℝ) :
    (minDegreeTracked U V M ε₀ γ₀).1 = minDegree U V M ε₀ γ₀ :=
  minDegreeLoopTracked_fst U V M ε₀ γ₀ U

lemma minDegreeLoopTracked_snd_le [DecidableEq α]
    (U : Finset α) (V : Finset β) (M : α → β → ℝ) (ε₀ γ₀ : ℝ) (U' : Finset α) :
    (minDegreeLoopTracked U V M ε₀ γ₀ U').2 ≤ (U'.card + 1) * (U'.card + 1) := by
  induction h : U'.card using Nat.strong_induction_on generalizing U' with
  | _ k ih =>
    subst h
    rw [minDegreeLoopTracked]
    split_ifs with hbad hthresh
    · simp only [scanFinsetTracked_snd]
      exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    · simp only [CostM.bind_snd, scanFinsetTracked_snd]
      set u := chooseMinBadRow U' V M ε₀ hbad
      set U'' := U'.erase u
      have hu : u ∈ U' := (mem_minDegreeBadRows_iff.mp (chooseMinBadRow_mem U' V M ε₀ hbad)).1
      have hcard_lt : U''.card < U'.card := Finset.card_erase_lt_of_mem hu
      have hcard_le : U''.card + 1 ≤ U'.card := hcard_lt
      have hrec := ih U''.card hcard_lt U'' rfl
      have hmul_le : U''.card + 1 ≤ U'.card + 1 := Nat.add_le_add_right (le_of_lt hcard_lt) 1
      calc
        (U'.card + 1) + (minDegreeLoopTracked U V M ε₀ γ₀ U'').2
          ≤ (U'.card + 1) + (U''.card + 1) * (U''.card + 1) :=
            Nat.add_le_add_left hrec _
        _ ≤ 1 * (U'.card + 1) + U'.card * (U'.card + 1) := by
            rw [Nat.one_mul]
            exact Nat.add_le_add_left (Nat.mul_le_mul hcard_le hmul_le) _
        _ = (U'.card + 1) * (U'.card + 1) := by ring
    · simp only [scanFinsetTracked_snd]
      exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)

theorem minDegreeTracked_snd_le [DecidableEq α]
    (U : Finset α) (V : Finset β) (M : α → β → ℝ) (ε₀ γ₀ : ℝ) :
    (minDegreeTracked U V M ε₀ γ₀).2 ≤ U.card * V.card + 1 + (U.card + 1) * (U.card + 1) := by
  unfold minDegreeTracked
  rw [CostM.bind_snd, scanMatrixTracked_snd]
  exact Nat.add_le_add_left (minDegreeLoopTracked_snd_le U V M ε₀ γ₀ U) _

lemma card_add_card_sdiff [DecidableEq α] {s t : Finset α} (h : s ⊆ t) :
    s.card + (t \ s).card = t.card := by
  rw [← Finset.card_union_of_disjoint Finset.disjoint_sdiff, Finset.union_sdiff_of_subset h]

/-- **Lemma 3.2 (`\label{lem:min-degree}`, `paper.tex` §3.3, Case 2 density increment calculation)**:
When $U' \subseteq U$ has $\mathbb{E}[M[U \setminus U', V]] \le (1 - \varepsilon_0)\mathbb{E}[M[U', V]]$
and $|U \setminus U'| \ge \gamma_0 |U|$, the partition identity
$\mathbb{E}[M] = \frac{|U'|}{|U|}\mathbb{E}[M'] + \frac{|U \setminus U'|}{|U|}\mathbb{E}[M[U \setminus U', V]]$
yields $\mathbb{E}[M] \le (1 - \gamma_0 \varepsilon_0)\mathbb{E}[M']$ and
$\mathbb{E}[M'] \ge (1 + \gamma_0 \varepsilon_0)\mathbb{E}[M]$. -/
lemma minDegree_case2_density_increment [DecidableEq α]
    {U U' : Finset α} {V : Finset β} {M : α → β → ℝ} {ε₀ γ₀ : ℝ}
    (hU : U.Nonempty) (hU'_sub : U' ⊆ U) (hU'_ne : U'.Nonempty)
    (hε₀ : 0 ≤ ε₀) (hγ₀_lt : γ₀ * ε₀ < 1)
    (hM_nonneg : ∀ u ∈ U, 0 ≤ rowDeg V M u)
    (h_peeled : ∀ u ∈ U \ U', rowDeg V M u ≤ (1 - ε₀) * matDensity U' V M)
    (h_card_sdiff : γ₀ * (U.card : ℝ) ≤ ((U \ U').card : ℝ)) :
    (1 - γ₀ * ε₀) * matDensity U' V M ≥ matDensity U V M ∧
    matDensity U' V M ≥ (1 / (1 - γ₀ * ε₀)) * matDensity U V M ∧
    matDensity U' V M ≥ (1 + γ₀ * ε₀) * matDensity U V M := by
  have hU_pos : (0 : ℝ) < (U.card : ℝ) := Nat.cast_pos.mpr hU.card_pos
  have hU'_pos : (0 : ℝ) < (U'.card : ℝ) := Nat.cast_pos.mpr hU'_ne.card_pos
  have hdens'_nonneg : 0 ≤ matDensity U' V M :=
    expectSet_nonneg (fun u hu => hM_nonneg u (hU'_sub hu))
  have hdens_nonneg : 0 ≤ matDensity U V M := expectSet_nonneg hM_nonneg
  have hsum_split : ∑ u ∈ U, rowDeg V M u =
      (∑ u ∈ U', rowDeg V M u) + (∑ u ∈ U \ U', rowDeg V M u) := by
    rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hU'_sub]
  have hsum_U : matDensity U V M * (U.card : ℝ) = ∑ u ∈ U, rowDeg V M u := by
    unfold matDensity expectSet
    exact div_mul_cancel₀ _ hU_pos.ne'
  have hsum_U' : matDensity U' V M * (U'.card : ℝ) = ∑ u ∈ U', rowDeg V M u := by
    unfold matDensity expectSet
    exact div_mul_cancel₀ _ hU'_pos.ne'
  have hsum_sdiff : ∑ u ∈ U \ U', rowDeg V M u ≤
      ((U \ U').card : ℝ) * ((1 - ε₀) * matDensity U' V M) := by
    calc
      ∑ u ∈ U \ U', rowDeg V M u ≤ ∑ _u ∈ U \ U', (1 - ε₀) * matDensity U' V M :=
        Finset.sum_le_sum h_peeled
      _ = ((U \ U').card : ℝ) * ((1 - ε₀) * matDensity U' V M) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hcard_add : (U'.card : ℝ) + ((U \ U').card : ℝ) = (U.card : ℝ) := by
    exact_mod_cast card_add_card_sdiff hU'_sub
  have h1 : matDensity U V M ≤ (1 - γ₀ * ε₀) * matDensity U' V M := by
    have hmul_sdiff :
        γ₀ * (U.card : ℝ) * (ε₀ * matDensity U' V M) ≤
          ((U \ U').card : ℝ) * (ε₀ * matDensity U' V M) :=
      mul_le_mul_of_nonneg_right h_card_sdiff (mul_nonneg hε₀ hdens'_nonneg)
    have h_tot : matDensity U V M * (U.card : ℝ) ≤
        (1 - γ₀ * ε₀) * matDensity U' V M * (U.card : ℝ) := by
      calc
        matDensity U V M * (U.card : ℝ) =
            (∑ u ∈ U', rowDeg V M u) + (∑ u ∈ U \ U', rowDeg V M u) := by
          rw [hsum_U, hsum_split]
        _ ≤ matDensity U' V M * (U'.card : ℝ) +
            ((U \ U').card : ℝ) * ((1 - ε₀) * matDensity U' V M) := by
          linarith [hsum_U', hsum_sdiff]
        _ = ((U'.card : ℝ) + ((U \ U').card : ℝ)) * matDensity U' V M -
            ((U \ U').card : ℝ) * (ε₀ * matDensity U' V M) := by ring
        _ = (U.card : ℝ) * matDensity U' V M -
            ((U \ U').card : ℝ) * (ε₀ * matDensity U' V M) := by rw [hcard_add]
        _ ≤ (U.card : ℝ) * matDensity U' V M -
            γ₀ * (U.card : ℝ) * (ε₀ * matDensity U' V M) := by linarith
        _ = (1 - γ₀ * ε₀) * matDensity U' V M * (U.card : ℝ) := by ring
    exact le_of_mul_le_mul_right h_tot hU_pos
  have h_one_sub_pos : 0 < 1 - γ₀ * ε₀ := by linarith
  have h2 : (1 / (1 - γ₀ * ε₀)) * matDensity U V M ≤ matDensity U' V M := by
    rw [one_div_mul_eq_div, div_le_iff₀ h_one_sub_pos, mul_comm]
    exact h1
  have h3 : (1 + γ₀ * ε₀) * matDensity U V M ≤ matDensity U' V M := by
    have hprod : (1 + γ₀ * ε₀) * (1 - γ₀ * ε₀) ≤ 1 := by
      have : 0 ≤ (γ₀ * ε₀) ^ 2 := sq_nonneg (γ₀ * ε₀)
      nlinarith
    nlinarith
  exact ⟨h1, h2, h3⟩

/-- Inductive loop invariant for `minDegreeLoop` (`paper.tex`, Lemma 3.2, §3.3). -/
theorem minDegreeLoop_spec [DecidableEq α]
    {U : Finset α} {V : Finset β} {M : α → β → ℝ} {ε₀ γ₀ : ℝ}
    (hU : U.Nonempty) (hε₀_pos : 0 < ε₀) (hε₀_lt : ε₀ < 1)
    (hγ₀_pos : 0 < γ₀) (hγ₀_le : γ₀ ≤ 1 / 2)
    (hM : ∀ u ∈ U, 0 ≤ rowDeg V M u)
    {U_curr : Finset α}
    (h_sub : U_curr ⊆ U)
    (h_ne : U_curr.Nonempty)
    (h_gt : (1 - γ₀) * (U.card : ℝ) < (U_curr.card : ℝ))
    (h_dens : matDensity U V M ≤ matDensity U_curr V M)
    (h_peeled : ∀ u ∈ U \ U_curr, rowDeg V M u < (1 - ε₀) * matDensity U_curr V M) :
    let res := minDegreeLoop U V M ε₀ γ₀ U_curr
    let U' := res.1
    let tag := res.2
    U' ⊆ U ∧
    U'.Nonempty ∧
    (1 / 3 : ℝ) * (U.card : ℝ) ≤ (U'.card : ℝ) ∧
    matDensity U V M ≤ matDensity U' V M ∧
    (tag = 1 ∨ tag = 2) ∧
    (tag = 1 →
      IsEpsMinDegree U' V M ε₀ ∧
      matDensity U V M ≤ matDensity U' V M ∧
      ((U \ U').Nonempty → matDensity (U \ U') V M < (1 - ε₀) * matDensity U' V M) ∧
      ((U \ U').card : ℝ) < γ₀ * (U.card : ℝ) ∧
      (1 - γ₀) * (U.card : ℝ) < (U'.card : ℝ) ∧
      ((U.card : ℝ) ≤ 1 / γ₀ → U' = U)) ∧
    (tag = 2 →
      2 ≤ U.card ∧
      1 ≤ U'.card ∧
      (1 / 3 : ℝ) * (U.card : ℝ) ≤ (U'.card : ℝ) ∧
      γ₀ * (U.card : ℝ) ≤ ((U \ U').card : ℝ) ∧
      (1 - γ₀ * ε₀) * matDensity U' V M ≥ matDensity U V M ∧
      matDensity U' V M ≥ (1 / (1 - γ₀ * ε₀)) * matDensity U V M ∧
      matDensity U' V M ≥ (1 + γ₀ * ε₀) * matDensity U V M ∧
      (1 - γ₀) * (U.card : ℝ) - 1 < (U'.card : ℝ) ∧
      (U'.card : ℝ) ≤ (1 - γ₀) * (U.card : ℝ)) := by
  induction hcard : U_curr.card using Nat.strong_induction_on generalizing U_curr with
  | _ k ih =>
    dsimp only
    rw [minDegreeLoop]
    split_ifs with hbad hthresh
    · -- Case 2: `hbad` and `(U''.card : ℝ) ≤ (1 - γ₀) * (U.card : ℝ)`
      set u := chooseMinBadRow U_curr V M ε₀ hbad
      set U'' := U_curr.erase u
      have hu_bad : u ∈ minDegreeBadRows U_curr V M ε₀ := chooseMinBadRow_mem U_curr V M ε₀ hbad
      have hu_mem : u ∈ U_curr := (mem_minDegreeBadRows_iff.mp hu_bad).1
      have hu_deg : rowDeg V M u < (1 - ε₀) * matDensity U_curr V M :=
        (mem_minDegreeBadRows_iff.mp hu_bad).2
      have hcard2 : 2 ≤ U_curr.card :=
        two_le_card_of_minDegreeBadRows_nonempty (le_of_lt hε₀_pos)
          (fun w hw => hM w (h_sub hw)) hbad
      have hU_card2 : 2 ≤ U.card := le_trans hcard2 (Finset.card_le_card h_sub)
      have hU''_sub : U'' ⊆ U := Finset.Subset.trans (Finset.erase_subset u U_curr) h_sub
      have hU''_card : U''.card = U_curr.card - 1 := Finset.card_erase_of_mem hu_mem
      have hU''_ne : U''.Nonempty := by
        rw [← Finset.card_pos, hU''_card]
        omega
      have hU''_dens_step : matDensity U_curr V M ≤ matDensity U'' V M :=
        matDensity_erase_ge_of_badRow (le_of_lt hε₀_pos) (fun w hw => hM w (h_sub hw)) hu_bad
      have hU''_dens : matDensity U V M ≤ matDensity U'' V M :=
        le_trans h_dens hU''_dens_step
      have h_peeled'' : ∀ w ∈ U \ U'', rowDeg V M w < (1 - ε₀) * matDensity U'' V M := by
        intro w hw
        rw [Finset.mem_sdiff] at hw
        have h1 : (1 - ε₀) * matDensity U_curr V M ≤ (1 - ε₀) * matDensity U'' V M :=
          mul_le_mul_of_nonneg_left hU''_dens_step (by linarith)
        by_cases hw_curr : w ∈ U_curr
        · have hw_eq : w = u := by
            by_contra hne
            exact hw.2 (Finset.mem_erase.mpr ⟨hne, hw_curr⟩)
          subst hw_eq
          exact lt_of_lt_of_le hu_deg h1
        · exact lt_of_lt_of_le (h_peeled w (Finset.mem_sdiff.mpr ⟨hw.1, hw_curr⟩)) h1
      have h_one_third : (1 / 3 : ℝ) * (U.card : ℝ) ≤ (U''.card : ℝ) := by
        have h_curr_gt : (1 / 2 : ℝ) * (U.card : ℝ) < (U_curr.card : ℝ) := by
          have : (0 : ℝ) < (U.card : ℝ) := Nat.cast_pos.mpr hU.card_pos
          nlinarith
        have h_nat : U.card < 2 * U_curr.card := by
          have : (U.card : ℝ) < 2 * (U_curr.card : ℝ) := by linarith
          exact_mod_cast this
        have h_nat_3 : U.card ≤ 3 * U''.card := by omega
        have h_real_3 : (U.card : ℝ) ≤ 3 * (U''.card : ℝ) := by exact_mod_cast h_nat_3
        linarith
      have h_sdiff_ge : γ₀ * (U.card : ℝ) ≤ ((U \ U'').card : ℝ) := by
        have hcard_add : (U''.card : ℝ) + ((U \ U'').card : ℝ) = (U.card : ℝ) := by
          exact_mod_cast card_add_card_sdiff hU''_sub
        linarith
      have h_inc := minDegree_case2_density_increment hU hU''_sub hU''_ne
        (le_of_lt hε₀_pos) (by nlinarith) hM
        (fun w hw => le_of_lt (h_peeled'' w hw)) h_sdiff_ge
      have h_card_gt : (1 - γ₀) * (U.card : ℝ) - 1 < (U''.card : ℝ) := by
        have h_cast : (U''.card : ℝ) + 1 = (U_curr.card : ℝ) := by
          have : U''.card + 1 = U_curr.card := by omega
          exact_mod_cast this
        linarith
      refine ⟨hU''_sub, hU''_ne, h_one_third, hU''_dens, Or.inr rfl, ?_, ?_⟩
      · intro h1; cases h1
      · intro _
        exact ⟨hU_card2, hU''_ne.card_pos, h_one_third, h_sdiff_ge,
          h_inc.1, h_inc.2.1, h_inc.2.2, h_card_gt, hthresh⟩
    · -- Recursive step: `hbad` and `¬ (U''.card : ℝ) ≤ (1 - γ₀) * (U.card : ℝ)`
      set u := chooseMinBadRow U_curr V M ε₀ hbad
      set U'' := U_curr.erase u
      have hu_bad : u ∈ minDegreeBadRows U_curr V M ε₀ := chooseMinBadRow_mem U_curr V M ε₀ hbad
      have hu_mem : u ∈ U_curr := (mem_minDegreeBadRows_iff.mp hu_bad).1
      have hu_deg : rowDeg V M u < (1 - ε₀) * matDensity U_curr V M :=
        (mem_minDegreeBadRows_iff.mp hu_bad).2
      have hcard2 : 2 ≤ U_curr.card :=
        two_le_card_of_minDegreeBadRows_nonempty (le_of_lt hε₀_pos)
          (fun w hw => hM w (h_sub hw)) hbad
      have hU''_sub : U'' ⊆ U := Finset.Subset.trans (Finset.erase_subset u U_curr) h_sub
      have hU''_card : U''.card = U_curr.card - 1 := Finset.card_erase_of_mem hu_mem
      have hU''_ne : U''.Nonempty := by
        rw [← Finset.card_pos, hU''_card]
        omega
      have hU''_dens_step : matDensity U_curr V M ≤ matDensity U'' V M :=
        matDensity_erase_ge_of_badRow (le_of_lt hε₀_pos) (fun w hw => hM w (h_sub hw)) hu_bad
      have hU''_dens : matDensity U V M ≤ matDensity U'' V M :=
        le_trans h_dens hU''_dens_step
      have h_peeled'' : ∀ w ∈ U \ U'', rowDeg V M w < (1 - ε₀) * matDensity U'' V M := by
        intro w hw
        rw [Finset.mem_sdiff] at hw
        have h1 : (1 - ε₀) * matDensity U_curr V M ≤ (1 - ε₀) * matDensity U'' V M :=
          mul_le_mul_of_nonneg_left hU''_dens_step (by linarith)
        by_cases hw_curr : w ∈ U_curr
        · have hw_eq : w = u := by
            by_contra hne
            exact hw.2 (Finset.mem_erase.mpr ⟨hne, hw_curr⟩)
          subst hw_eq
          exact lt_of_lt_of_le hu_deg h1
        · exact lt_of_lt_of_le (h_peeled w (Finset.mem_sdiff.mpr ⟨hw.1, hw_curr⟩)) h1
      have hcard_lt : U''.card < U_curr.card := Finset.card_erase_lt_of_mem hu_mem
      exact ih U''.card (hcard ▸ hcard_lt) hU''_sub hU''_ne (not_le.mp hthresh)
        hU''_dens h_peeled'' rfl
    · -- Case 1: `¬ (minDegreeBadRows U_curr V M ε₀).Nonempty`
      have h_min_deg : IsEpsMinDegree U_curr V M ε₀ := by
        intro u hu
        by_contra hlt
        exact hbad ⟨u, mem_minDegreeBadRows_iff.mpr ⟨hu, not_le.mp hlt⟩⟩
      have h_sdiff_lt : ((U \ U_curr).card : ℝ) < γ₀ * (U.card : ℝ) := by
        have hcard_add : (U_curr.card : ℝ) + ((U \ U_curr).card : ℝ) = (U.card : ℝ) := by
          exact_mod_cast card_add_card_sdiff h_sub
        linarith
      have h_one_third : (1 / 3 : ℝ) * (U.card : ℝ) ≤ (U_curr.card : ℝ) := by
        have : (0 : ℝ) < (U.card : ℝ) := Nat.cast_pos.mpr hU.card_pos
        nlinarith
      have h_sdiff_dens :
          (U \ U_curr).Nonempty → matDensity (U \ U_curr) V M < (1 - ε₀) * matDensity U_curr V M := by
        intro hsdiff
        unfold matDensity expectSet
        have hsdiff_pos : (0 : ℝ) < ((U \ U_curr).card : ℝ) := Nat.cast_pos.mpr hsdiff.card_pos
        rw [div_lt_iff₀ hsdiff_pos]
        calc
          ∑ u ∈ U \ U_curr, rowDeg V M u < ∑ _u ∈ U \ U_curr, (1 - ε₀) * matDensity U_curr V M :=
            Finset.sum_lt_sum_of_nonempty hsdiff h_peeled
          _ = ((1 - ε₀) * matDensity U_curr V M) * ((U \ U_curr).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      have h_small_U : (U.card : ℝ) ≤ 1 / γ₀ → U_curr = U := by
        intro hsmall
        have hmul : γ₀ * (U.card : ℝ) ≤ 1 := by
          rw [← le_div_iff₀' hγ₀_pos]
          exact hsmall
        have hlt1 : ((U \ U_curr).card : ℝ) < 1 := lt_of_lt_of_le h_sdiff_lt hmul
        have hlt1_nat : (U \ U_curr).card < 1 := by exact_mod_cast hlt1
        have hcard0 : (U \ U_curr).card = 0 := by omega
        have hempty : U \ U_curr = ∅ := Finset.card_eq_zero.mp hcard0
        exact Finset.Subset.antisymm h_sub (Finset.sdiff_eq_empty_iff_subset.mp hempty)
      refine ⟨h_sub, h_ne, h_one_third, h_dens, Or.inl rfl, ?_, ?_⟩
      · intro _
        exact ⟨h_min_deg, h_dens, h_sdiff_dens, h_sdiff_lt, h_gt, h_small_U⟩
      · intro h2; cases h2

/-- **Lemma 3.2 (`\label{lem:min-degree}`, `paper.tex` §3.3)**:
Minimum-degree pruning guarantees for both Case 1 ($\varepsilon_0$-min-degree certified) and
Case 2 (density increment $\mathbb{E}[M'] \ge (1 + \gamma_0 \varepsilon_0)\mathbb{E}[M]$). -/
theorem lem_min_degree [DecidableEq α]
    {U : Finset α} {V : Finset β} {M : α → β → ℝ} {ε₀ γ₀ : ℝ}
    (hU : U.Nonempty) (hε₀_pos : 0 < ε₀) (hε₀_lt : ε₀ < 1)
    (hγ₀_pos : 0 < γ₀) (hγ₀_le : γ₀ ≤ 1 / 2)
    (hM : ∀ u ∈ U, 0 ≤ rowDeg V M u) :
    let res := minDegree U V M ε₀ γ₀
    let U' := res.1
    let tag := res.2
    U' ⊆ U ∧
    U'.Nonempty ∧
    (1 / 3 : ℝ) * (U.card : ℝ) ≤ (U'.card : ℝ) ∧
    matDensity U V M ≤ matDensity U' V M ∧
    (tag = 1 ∨ tag = 2) ∧
    (tag = 1 →
      IsEpsMinDegree U' V M ε₀ ∧
      matDensity U V M ≤ matDensity U' V M ∧
      ((U \ U').Nonempty → matDensity (U \ U') V M < (1 - ε₀) * matDensity U' V M) ∧
      ((U \ U').card : ℝ) < γ₀ * (U.card : ℝ) ∧
      (1 - γ₀) * (U.card : ℝ) < (U'.card : ℝ) ∧
      ((U.card : ℝ) ≤ 1 / γ₀ → U' = U)) ∧
    (tag = 2 →
      2 ≤ U.card ∧
      1 ≤ U'.card ∧
      (1 / 3 : ℝ) * (U.card : ℝ) ≤ (U'.card : ℝ) ∧
      γ₀ * (U.card : ℝ) ≤ ((U \ U').card : ℝ) ∧
      (1 - γ₀ * ε₀) * matDensity U' V M ≥ matDensity U V M ∧
      matDensity U' V M ≥ (1 / (1 - γ₀ * ε₀)) * matDensity U V M ∧
      matDensity U' V M ≥ (1 + γ₀ * ε₀) * matDensity U V M ∧
      (1 - γ₀) * (U.card : ℝ) - 1 < (U'.card : ℝ) ∧
      (U'.card : ℝ) ≤ (1 - γ₀) * (U.card : ℝ) ∧
      U'.card = ⌊(1 - γ₀) * (U.card : ℝ)⌋₊ ∧
      (U \ U').card = ⌈γ₀ * (U.card : ℝ)⌉₊) ∧
    max 1 ⌊(1 - γ₀) * (U.card : ℝ)⌋₊ ≤ U'.card := by
  have hU_pos : (0 : ℝ) < (U.card : ℝ) := Nat.cast_pos.mpr hU.card_pos
  have h_gt : (1 - γ₀) * (U.card : ℝ) < (U.card : ℝ) := by nlinarith
  have h_peeled : ∀ u ∈ U \ U, rowDeg V M u < (1 - ε₀) * matDensity U V M := by
    intro u hu
    simp at hu
  rcases minDegreeLoop_spec hU hε₀_pos hε₀_lt hγ₀_pos hγ₀_le hM
    (Finset.Subset.refl U) hU h_gt le_rfl h_peeled with
    ⟨h_sub, h_ne, h_third, h_dens, h_cases, h_tag1, h_tag2⟩
  let res := minDegree U V M ε₀ γ₀
  let U' := res.1
  let tag := res.2
  have h0_nonneg : 0 ≤ (1 - γ₀) * (U.card : ℝ) := by nlinarith
  have h_tag2' : tag = 2 →
      2 ≤ U.card ∧
      1 ≤ U'.card ∧
      (1 / 3 : ℝ) * (U.card : ℝ) ≤ (U'.card : ℝ) ∧
      γ₀ * (U.card : ℝ) ≤ ((U \ U').card : ℝ) ∧
      (1 - γ₀ * ε₀) * matDensity U' V M ≥ matDensity U V M ∧
      matDensity U' V M ≥ (1 / (1 - γ₀ * ε₀)) * matDensity U V M ∧
      matDensity U' V M ≥ (1 + γ₀ * ε₀) * matDensity U V M ∧
      (1 - γ₀) * (U.card : ℝ) - 1 < (U'.card : ℝ) ∧
      (U'.card : ℝ) ≤ (1 - γ₀) * (U.card : ℝ) ∧
      U'.card = ⌊(1 - γ₀) * (U.card : ℝ)⌋₊ ∧
      (U \ U').card = ⌈γ₀ * (U.card : ℝ)⌉₊ := by
    intro h2
    rcases h_tag2 h2 with ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9⟩
    change γ₀ * (U.card : ℝ) ≤ ((U \ U').card : ℝ) at hc4
    change (1 - γ₀) * (U.card : ℝ) - 1 < (U'.card : ℝ) at hc8
    change (U'.card : ℝ) ≤ (1 - γ₀) * (U.card : ℝ) at hc9
    have h_ring : (1 - γ₀) * (U.card : ℝ) + γ₀ * (U.card : ℝ) = (U.card : ℝ) := by ring
    have h_le_floor : U'.card ≤ ⌊(1 - γ₀) * (U.card : ℝ)⌋₊ := Nat.le_floor hc9
    have h_floor_lt : ⌊(1 - γ₀) * (U.card : ℝ)⌋₊ < U'.card + 1 := by
      rw [Nat.floor_lt h0_nonneg]
      push_cast
      linarith
    have h_floor_eq : U'.card = ⌊(1 - γ₀) * (U.card : ℝ)⌋₊ := by omega
    have h_card_add : (U \ U').card + U'.card = U.card :=
      Finset.card_sdiff_add_card_eq_card h_sub
    have h_card_add_r : ((U \ U').card : ℝ) + (U'.card : ℝ) = (U.card : ℝ) := by
      exact_mod_cast h_card_add
    have h_ceil_le : ⌈γ₀ * (U.card : ℝ)⌉₊ ≤ (U \ U').card :=
      Nat.ceil_le.mpr hc4
    have h_sdiff_pos : 1 ≤ (U \ U').card := by
      have h_pos_r : (0 : ℝ) < ((U \ U').card : ℝ) := by nlinarith
      have h_pos_n : 0 < (U \ U').card := by exact_mod_cast h_pos_r
      omega
    have h_sdiff_le_ceil : (U \ U').card ≤ ⌈γ₀ * (U.card : ℝ)⌉₊ := by
      have h_sub1_lt_r : (((U \ U').card - 1 : ℕ) : ℝ) < (⌈γ₀ * (U.card : ℝ)⌉₊ : ℝ) := by
        rw [Nat.cast_sub h_sdiff_pos, Nat.cast_one]
        have h_le_c : γ₀ * (U.card : ℝ) ≤ (⌈γ₀ * (U.card : ℝ)⌉₊ : ℝ) :=
          Nat.le_ceil (γ₀ * (U.card : ℝ))
        linarith
      have h_sub1_lt : (U \ U').card - 1 < ⌈γ₀ * (U.card : ℝ)⌉₊ := by
        exact_mod_cast h_sub1_lt_r
      omega
    have h_ceil_eq : (U \ U').card = ⌈γ₀ * (U.card : ℝ)⌉₊ :=
      le_antisymm h_sdiff_le_ceil h_ceil_le
    exact ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, h_floor_eq, h_ceil_eq⟩
  have h_max_le : max 1 ⌊(1 - γ₀) * (U.card : ℝ)⌋₊ ≤ U'.card := by
    refine Nat.max_le.mpr ⟨h_ne.card_pos, ?_⟩
    rcases h_cases with h1 | h2
    · exact Nat.floor_le_of_le (h_tag1 h1).2.2.2.2.1.le
    · exact (h_tag2' h2).2.2.2.2.2.2.2.2.2.1.ge
  exact ⟨h_sub, h_ne, h_third, h_dens, h_cases, h_tag1, h_tag2', h_max_le⟩

end MinDegree

/-!
## Section 4.2: Dyadic Level-Set Sifting (`DyadicSift`, Algorithm 3 & Lemma 4.2, §4.2)
-/

section DyadicSift

variable {α β : Type*}

/-- Support neighborhood $N_A(x) = Y_x = \{y \in Y : A(x, y) = 1\}$ of row $x$ in a binary matrix
$A$ on $X \times Y$ (`paper.tex`, Algorithm 3 Line 6 `\label{line:sift-witness}`, §4.2). -/
noncomputable def rowSupport (Y : Finset β) (A : α → β → ℝ) (x : α) : Finset β := by
  classical
  exact Y.filter (fun y => 1 ≤ A x y)

lemma mem_rowSupport_iff {Y : Finset β} {A : α → β → ℝ} {x : α} {y : β} :
    y ∈ rowSupport Y A x ↔ y ∈ Y ∧ 1 ≤ A x y := by
  classical
  unfold rowSupport
  exact Finset.mem_filter

lemma rowSupport_subset (Y : Finset β) (A : α → β → ℝ) (x : α) :
    rowSupport Y A x ⊆ Y := by
  intro y hy
  exact (mem_rowSupport_iff.mp hy).1

lemma binary_eq_one_or_zero_of_rowSupport {X : Finset α} {Y : Finset β} {A : α → β → ℝ}
    (hA : IsBinaryMatrix X Y A) {x : α} (hx : x ∈ X) {y : β} (hy : y ∈ Y) :
    (y ∈ rowSupport Y A x → A x y = 1) ∧ (y ∉ rowSupport Y A x → A x y = 0) := by
  constructor
  · intro hmem
    have h1 := (mem_rowSupport_iff.mp hmem).2
    rcases hA x hx y hy with h0 | h1'
    · linarith
    · exact h1'
  · intro hnmem
    rcases hA x hx y hy with h0 | h1'
    · exact h0
    · exfalso
      exact hnmem (mem_rowSupport_iff.mpr ⟨hy, by linarith⟩)

lemma rowDeg_binary_eq_card_rowSupport {X : Finset α} {Y : Finset β} {A : α → β → ℝ}
    (hA : IsBinaryMatrix X Y A) {x : α} (hx : x ∈ X) :
    rowDeg Y A x = ((rowSupport Y A x).card : ℝ) / (Y.card : ℝ) := by
  classical
  unfold rowDeg expectSet
  congr 1
  have hsplit : ∑ y ∈ Y, A x y =
      (∑ y ∈ rowSupport Y A x, A x y) + (∑ y ∈ Y \ rowSupport Y A x, A x y) := by
    rw [← Finset.sum_union Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset (rowSupport_subset Y A x)]
  have h1 : ∑ y ∈ rowSupport Y A x, A x y = ((rowSupport Y A x).card : ℝ) := by
    have heq : ∀ y ∈ rowSupport Y A x, A x y = 1 := fun y hy =>
      (binary_eq_one_or_zero_of_rowSupport hA hx (rowSupport_subset Y A x hy)).1 hy
    rw [Finset.sum_congr rfl heq, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h0 : ∑ y ∈ Y \ rowSupport Y A x, A x y = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    rw [Finset.mem_sdiff] at hy
    exact (binary_eq_one_or_zero_of_rowSupport hA hx hy.1).2 hy.2
  rw [hsplit, h1, h0, add_zero]

lemma card_rowSupport_eq_rowDeg_mul_card {X : Finset α} {Y : Finset β} {A : α → β → ℝ}
    (hY : Y.Nonempty) (hA : IsBinaryMatrix X Y A) {x : α} (hx : x ∈ X) :
    ((rowSupport Y A x).card : ℝ) = rowDeg Y A x * (Y.card : ℝ) := by
  have hY_pos : (Y.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hY.card_pos.ne'
  rw [rowDeg_binary_eq_card_rowSupport hA hx, div_mul_cancel₀ _ hY_pos]

/-- Inner product of two rows of a binary matrix equals $\deg_A(x) \cdot \deg_{A_x}(x')$:
$\mathbb{E}_{y \in Y}[A(x, y) A(x', y)] = \deg_A(x) \cdot \mathbb{E}_{y \in N_A(x)}[A(x', y)]$. -/
lemma expectSet_mul_binary_eq_rowDeg_mul_rowSupport {X : Finset α} {Y : Finset β} {A : α → β → ℝ}
    (hA : IsBinaryMatrix X Y A) {x : α} (hx : x ∈ X) (x' : α) :
    expectSet Y (fun y => A x y * A x' y) =
      rowDeg Y A x * rowDeg (rowSupport Y A x) A x' := by
  classical
  by_cases hY : Y.Nonempty
  · have hY_pos : (Y.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hY.card_pos.ne'
    unfold rowDeg expectSet
    have hsplit : ∑ y ∈ Y, A x y * A x' y =
        (∑ y ∈ rowSupport Y A x, A x y * A x' y) +
        (∑ y ∈ Y \ rowSupport Y A x, A x y * A x' y) := by
      rw [← Finset.sum_union Finset.disjoint_sdiff,
        Finset.union_sdiff_of_subset (rowSupport_subset Y A x)]
    have h1 : ∑ y ∈ rowSupport Y A x, A x y * A x' y = ∑ y ∈ rowSupport Y A x, A x' y := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [(binary_eq_one_or_zero_of_rowSupport hA hx (rowSupport_subset Y A x hy)).1 hy, one_mul]
    have h0 : ∑ y ∈ Y \ rowSupport Y A x, A x y * A x' y = 0 := by
      apply Finset.sum_eq_zero
      intro y hy
      rw [Finset.mem_sdiff] at hy
      rw [(binary_eq_one_or_zero_of_rowSupport hA hx hy.1).2 hy.2, zero_mul]
    have hsum_x : ∑ y ∈ Y, A x y = ((rowSupport Y A x).card : ℝ) := by
      have hdeg := rowDeg_binary_eq_card_rowSupport hA hx
      unfold rowDeg expectSet at hdeg
      calc
        ∑ y ∈ Y, A x y = ((∑ y ∈ Y, A x y) / (Y.card : ℝ)) * (Y.card : ℝ) :=
          (div_mul_cancel₀ _ hY_pos).symm
        _ = (((rowSupport Y A x).card : ℝ) / (Y.card : ℝ)) * (Y.card : ℝ) := by rw [hdeg]
        _ = ((rowSupport Y A x).card : ℝ) := div_mul_cancel₀ _ hY_pos
    rw [hsplit, h1, h0, add_zero, hsum_x]
    by_cases hsupp : (rowSupport Y A x).Nonempty
    · have hsupp_pos : ((rowSupport Y A x).card : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr hsupp.card_pos.ne'
      rw [div_mul_div_comm, mul_comm ((rowSupport Y A x).card : ℝ),
        mul_div_mul_right _ _ hsupp_pos]
    · have hempty : rowSupport Y A x = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsupp
      simp [hempty]
  · have hempty : Y = ∅ := Finset.not_nonempty_iff_eq_empty.mp hY
    unfold rowDeg expectSet
    simp [hempty]

/-- **Grid-Norm Fubini Expansion (`\eqref{eq:overview-u2d}`, `\eqref{eq:grid-norm-fubini}`, `paper.tex` §2.3, §3.2 & §4.2)**:
For any binary matrix $A \in \{0, 1\}^{X \times Y}$ and $d \ge 1$,
$\|A\|_{U(2, d)}^{2d} = \mathbb{E}_{x \in X}[\deg_A(x)^d \|A_x\|_{U(1, d)}^d]$. -/
theorem u2d_expansion {X : Finset α} {Y : Finset β} {A : α → β → ℝ}
    (hA : IsBinaryMatrix X Y A) (d : ℕ) :
    gridNorm2Pow X Y A d =
      expectSet X (fun x => (rowDeg Y A x) ^ d * gridNorm1Pow X (rowSupport Y A x) A d) := by
  unfold gridNorm2Pow gridNorm1Pow
  change (∑ x ∈ X, expectSet X (fun x' => (expectSet Y (fun y => A x y * A x' y)) ^ d)) / (X.card : ℝ) =
    (∑ x ∈ X, (rowDeg Y A x) ^ d * expectSet X (fun x' => (rowDeg (rowSupport Y A x) A x') ^ d)) / (X.card : ℝ)
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  simp_rw [expectSet_mul_binary_eq_rowDeg_mul_rowSupport hA hx, mul_pow]
  unfold expectSet
  rw [← Finset.mul_sum, mul_div_assoc]

lemma gridNormPow_two_eq_gridNorm2Pow (X : Finset α) (Y : Finset β) (M : α → β → ℝ) (d : ℕ) :
    gridNormPow X Y M 2 d = gridNorm2Pow X Y M d := by
  rw [gridNormPow_eq_gridNormPowCol, gridNorm2Pow_eq_col_expect_sq]
  rfl

lemma gridNormPow_one_eq_gridNorm1Pow (X : Finset α) (Y : Finset β) (M : α → β → ℝ) (d : ℕ) :
    gridNormPow X Y M 1 d = gridNorm1Pow X Y M d := by
  rw [gridNormPow_eq_gridNormPowCol]
  unfold gridNormPowCol gridNorm1Pow rowDeg
  simp_rw [pow_one, expectSet_pow_eq_piFinset Y _ d]
  exact (expectSet_comm X (Fintype.piFinset (fun _ : Fin d => Y)) _).symm

lemma gridNorm1Pow_nonneg {X : Finset α} {Y : Finset β} {M : α → β → ℝ}
    (hM : ∀ x ∈ X, 0 ≤ rowDeg Y M x) (d : ℕ) :
    0 ≤ gridNorm1Pow X Y M d :=
  expectSet_nonneg (fun x hx => pow_nonneg (hM x hx) d)

lemma gridNorm1Pow_le_one {X : Finset α} {Y : Finset β} {M : α → β → ℝ}
    (hX : X.Nonempty) (hM0 : ∀ x ∈ X, 0 ≤ rowDeg Y M x) (hM1 : ∀ x ∈ X, rowDeg Y M x ≤ 1)
    (d : ℕ) :
    gridNorm1Pow X Y M d ≤ 1 :=
  expectSet_le_of_le hX (fun x hx => pow_le_one₀ (hM0 x hx) (hM1 x hx))

lemma gridNorm_one_pow_eq_gridNorm1Pow {X : Finset α} {Y : Finset β} {M : α → β → ℝ}
    (hM : ∀ x ∈ X, 0 ≤ rowDeg Y M x) {d : ℕ} (hd : 1 ≤ d) :
    (gridNorm X Y M 1 d) ^ d = gridNorm1Pow X Y M d := by
  unfold gridNorm
  rw [Nat.one_mul, gridNormPow_one_eq_gridNorm1Pow, one_div]
  exact Real.rpow_inv_natCast_pow (gridNorm1Pow_nonneg hM d) (by omega)

lemma isGridRegular_of_isGridRegular2Pow {X : Finset α} {Y : Finset β} {A : α → β → ℝ}
    {ε : ℝ} {d : ℕ} (hd : 1 ≤ d) (hε : 0 ≤ 1 + ε) (hμ : 0 ≤ matDensity X Y A)
    (hreg : IsGridRegular2Pow X Y A ε d) :
    IsGridRegular X Y A ε 2 d := by
  unfold IsGridRegular gridNorm
  rw [gridNormPow_two_eq_gridNorm2Pow, one_div]
  have h2d : (2 * d : ℕ) ≠ 0 := by omega
  have hrhs : (((1 + ε) * matDensity X Y A) ^ (2 * d)) ^ (((2 * d : ℕ) : ℝ)⁻¹) =
      (1 + ε) * matDensity X Y A :=
    Real.pow_rpow_inv_natCast (mul_nonneg hε hμ) h2d
  rw [← hrhs]
  exact Real.rpow_le_rpow (gridNorm2Pow_nonneg X Y A d) hreg (by positivity)

/-- Outer dyadic slice $X'_s := B_s := \{x \in X : 2^s \delta \le \deg_A(x) < 2^{s+1}\delta\}$
(`paper.tex`, Algorithm 3 Line 3 & Lemma 4.2 Case A, §4.2). -/
noncomputable def outerDyadicBucket (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (δ : ℝ) (s : ℕ) : Finset α := by
  classical
  exact X.filter (fun x => (2 : ℝ) ^ s * δ ≤ rowDeg Y A x ∧ rowDeg Y A x < (2 : ℝ) ^ (s + 1) * δ)

/-- High-degree candidate witness set $X_{\ge \delta^2} := \{x \in X : \deg_A(x) \ge \delta^2\}$
(`paper.tex`, Algorithm 3 Line 4, §4.2). -/
noncomputable def witnessRowCandidates (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (δ : ℝ) : Finset α := by
  classical
  exact X.filter (fun x => δ ^ 2 ≤ rowDeg Y A x)

/-- Inner dyadic slice $X'_{x^*, s} := D_s := \{x' \in X : 2^s \delta \le \deg_{A_{x^*}}(x') < 2^{s+1}\delta\}$
(`paper.tex`, Algorithm 3 Line 8 `\label{line:sift-inner-ret}` & Lemma 4.2 Case B, §4.2). -/
noncomputable def innerDyadicBucket (X : Finset α) (Y' : Finset β) (A : α → β → ℝ)
    (δ : ℝ) (s : ℕ) : Finset α := by
  classical
  exact X.filter (fun x' => (2 : ℝ) ^ s * δ ≤ rowDeg Y' A x' ∧ rowDeg Y' A x' < (2 : ℝ) ^ (s + 1) * δ)

lemma mem_outerDyadicBucket_iff {X : Finset α} {Y : Finset β} {A : α → β → ℝ}
    {δ : ℝ} {s : ℕ} {x : α} :
    x ∈ outerDyadicBucket X Y A δ s ↔
      x ∈ X ∧ ((2 : ℝ) ^ s * δ ≤ rowDeg Y A x ∧ rowDeg Y A x < (2 : ℝ) ^ (s + 1) * δ) := by
  classical
  unfold outerDyadicBucket
  exact Finset.mem_filter

lemma mem_witnessRowCandidates_iff {X : Finset α} {Y : Finset β} {A : α → β → ℝ}
    {δ : ℝ} {x : α} :
    x ∈ witnessRowCandidates X Y A δ ↔ x ∈ X ∧ δ ^ 2 ≤ rowDeg Y A x := by
  classical
  unfold witnessRowCandidates
  exact Finset.mem_filter

lemma mem_innerDyadicBucket_iff {X : Finset α} {Y' : Finset β} {A : α → β → ℝ}
    {δ : ℝ} {s : ℕ} {x' : α} :
    x' ∈ innerDyadicBucket X Y' A δ s ↔
      x' ∈ X ∧ ((2 : ℝ) ^ s * δ ≤ rowDeg Y' A x' ∧ rowDeg Y' A x' < (2 : ℝ) ^ (s + 1) * δ) := by
  classical
  unfold innerDyadicBucket
  exact Finset.mem_filter

/-- Deterministic list-fold witness-row selector over `x₀ :: candidates` maximizing `V` directly
(avoiding `Classical.choose`). -/
noncomputable def selectWitnessRowList (x₀ : α) (candidates : List α) (V : α → ℝ) : α :=
  letI := Classical.dec
  candidates.foldl (fun best x => if V best ≤ V x then x else best) x₀

lemma selectWitnessRowList_mem (x₀ : α) (candidates : List α) (V : α → ℝ) :
    selectWitnessRowList x₀ candidates V ∈ x₀ :: candidates := by
  unfold selectWitnessRowList
  induction candidates generalizing x₀ with
  | nil => simp
  | cons a tl ih =>
    simp only [List.foldl_cons]
    split_ifs
    · exact List.mem_cons_of_mem x₀ (ih a)
    · rcases List.mem_cons.mp (ih x₀) with heq | hmem
      · rw [heq]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem x₀ (List.mem_cons_of_mem a hmem)

lemma selectWitnessRowList_ge_V (x₀ : α) (candidates : List α) (V : α → ℝ) :
    ∀ x ∈ x₀ :: candidates, V x ≤ V (selectWitnessRowList x₀ candidates V) := by
  unfold selectWitnessRowList
  induction candidates generalizing x₀ with
  | nil =>
    intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact le_rfl
  | cons a tl ih =>
    simp only [List.foldl_cons]
    letI := Classical.dec
    set next := if V x₀ ≤ V a then a else x₀
    have hx₀_le_next : V x₀ ≤ V next := by
      dsimp [next]
      split_ifs with h
      · exact h
      · exact le_rfl
    have ha_le_next : V a ≤ V next := by
      dsimp [next]
      split_ifs with h
      · exact le_rfl
      · exact le_of_lt (not_le.mp h)
    have hnext_le_res :
        V next ≤ V (List.foldl (fun best x => if V best ≤ V x then x else best) next tl) :=
      ih next next List.mem_cons_self
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hxa
    · exact hx₀_le_next.trans hnext_le_res
    · rcases List.mem_cons.mp hxa with rfl | hxtl
      · exact ha_le_next.trans hnext_le_res
      · exact ih next x (List.mem_cons_of_mem next hxtl)

/-- Witness selection at Line 6 (`\label{line:sift-witness}`) of Algorithm 3 (`DyadicSift`, `paper.tex` §4.2):
selects $x^* \in X_{\ge \delta^2}$ maximizing the rational quantity $V_{x^*}$ directly
via deterministic list fold `selectWitnessRowList` (without extracting a $d$-th root or invoking
`Classical.choose`, since $z \mapsto z^{1/d}$ is strictly increasing on $[0, \infty)$). -/
noncomputable def selectWitnessRow (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (δ : ℝ) (_d : ℕ) (V : α → ℝ)
    (hwit : (witnessRowCandidates X Y A δ).Nonempty) : α :=
  let cands := (witnessRowCandidates X Y A δ).toList
  have hne : cands ≠ [] := finset_toList_ne_nil hwit
  selectWitnessRowList (cands.head hne) cands.tail V

lemma selectWitnessRow_mem (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (δ : ℝ) (d : ℕ) (V : α → ℝ)
    (hwit : (witnessRowCandidates X Y A δ).Nonempty) :
    selectWitnessRow X Y A δ d V hwit ∈ witnessRowCandidates X Y A δ := by
  unfold selectWitnessRow
  dsimp only
  set cands := (witnessRowCandidates X Y A δ).toList
  have hne : cands ≠ [] := finset_toList_ne_nil hwit
  have hmem := selectWitnessRowList_mem (cands.head hne) cands.tail V
  rw [List.cons_head_tail] at hmem
  exact Finset.mem_toList.mp hmem

lemma selectWitnessRow_ge_V (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (δ : ℝ) (d : ℕ) (V : α → ℝ)
    (hwit : (witnessRowCandidates X Y A δ).Nonempty) :
    ∀ x ∈ witnessRowCandidates X Y A δ,
      V x ≤ V (selectWitnessRow X Y A δ d V hwit) := by
  intro x hx
  unfold selectWitnessRow
  dsimp only
  set cands := (witnessRowCandidates X Y A δ).toList
  have hne : cands ≠ [] := finset_toList_ne_nil hwit
  have hx_mem : x ∈ cands.head hne :: cands.tail := by
    rw [List.cons_head_tail]
    exact Finset.mem_toList.mpr hx
  exact selectWitnessRowList_ge_V (cands.head hne) cands.tail V x hx_mem

lemma selectWitnessRow_ge (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (δ : ℝ) (d : ℕ) (V : α → ℝ)
    (hwit : (witnessRowCandidates X Y A δ).Nonempty)
    {x : α} (hx : x ∈ witnessRowCandidates X Y A δ) (hVx : 0 ≤ V x) :
    (V x) ^ ((1 : ℝ) / (d : ℝ)) ≤
      (V (selectWitnessRow X Y A δ d V hwit)) ^ ((1 : ℝ) / (d : ℝ)) :=
  Real.rpow_le_rpow hVx (selectWitnessRow_ge_V X Y A δ d V hwit x hx) (by positivity)

lemma list_range_findSome_ite_eq_none_iff {P : ℕ → Prop} [DecidablePred P] (d : ℕ) :
    ((List.range d).findSome? (fun s => if P s then some s else none) = none) ↔
      ∀ s ∈ Finset.range d, ¬ P s := by
  simp [List.findSome?_eq_none_iff]

lemma list_range_findSome_ite_eq_some {P : ℕ → Prop} [DecidablePred P] {d s : ℕ}
    (h : (List.range d).findSome? (fun s => if P s then some s else none) = some s) :
    s ∈ Finset.range d ∧ P s := by
  obtain ⟨s', hs'_mem, hs'_eq⟩ := List.exists_of_findSome?_eq_some h
  split_ifs at hs'_eq with hP
  cases hs'_eq
  exact ⟨Finset.mem_range.mpr (List.mem_range.mp hs'_mem), hP⟩

/-- **Algorithm 3 (`DyadicSift`, `paper.tex` §4.2)**:
Given $X, Y, A, \varepsilon, d$ and the vector $V : \alpha \to \mathbb{R}$ returned by
`ApproxGridNorm`, iterates over dyadic scales $s \in \{0, \dots, d-1\}$ (`List.range d`) in Step 1
and Step 3 and either returns a denser sub-rectangle `("subrect", X', Y', s)` or certifies
`("regular", X, Y, 0)`. -/
noncomputable def dyadicSift (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (ε : ℝ) (d : ℕ) (V : α → ℝ) : String × Finset α × Finset β × ℕ :=
  letI := Classical.dec
  let δ := (1 + ε / 2) * matDensity X Y A
  -- Step 1: Outer dyadic row-degree loop over `s ∈ List.range d` (§4.2)
  match (List.range d).findSome? (fun s =>
      if (ε / 16) * (((2 : ℝ) ^ ((s + 2) * d))⁻¹) * (X.card : ℝ) ≤
          ((outerDyadicBucket X Y A δ s).card : ℝ) then
        some s
      else
        none) with
  | some s =>
    ("subrect", outerDyadicBucket X Y A δ s, Y, s)
  | none =>
    -- Step 2: Deterministic witness-row selection maximizing `V` directly (§4.2)
    if hwit : (witnessRowCandidates X Y A δ).Nonempty then
      let x_star := selectWitnessRow X Y A δ d V hwit
      let Y' := rowSupport Y A x_star
      -- Step 3: Inner dyadic row-degree loop over `s ∈ List.range d` (§4.2)
      match (List.range d).findSome? (fun s =>
          if (ε / 16) * (((2 : ℝ) ^ ((s + 2) * d))⁻¹) * (X.card : ℝ) ≤
              ((innerDyadicBucket X Y' A δ s).card : ℝ) then
            some s
          else
            none) with
      | some s =>
        ("subrect", innerDyadicBucket X Y' A δ s, Y', s)
      | none =>
        ("regular", X, Y, 0)
    else
      ("regular", X, Y, 0)

/-- Cost-tracked Algorithm 3 (`dyadicSiftTracked`) in `CostM`:
executes `findSomeListTracked` across `List.range d` in Step 1, `scanFinsetTracked X` for
witness selection in Step 2, and `findSomeListTracked` across `List.range d` in Step 3. -/
noncomputable def dyadicSiftTracked (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (ε : ℝ) (d : ℕ) (V_tracked : CostM (α → ℝ)) :
    CostM (String × Finset α × Finset β × ℕ) :=
  letI := Classical.dec
  let δ := (1 + ε / 2) * matDensity X Y A
  CostM.bind V_tracked (fun V =>
    CostM.bind
      (findSomeListTracked
        (fun s =>
          scanMatrixTracked X Y
            (if (ε / 16) * (((2 : ℝ) ^ ((s + 2) * d))⁻¹) * (X.card : ℝ) ≤
                ((outerDyadicBucket X Y A δ s).card : ℝ) then
              some s
            else
              none))
        (List.range d))
      (fun outerOpt =>
        match outerOpt with
        | some s =>
          retTracked ("subrect", outerDyadicBucket X Y A δ s, Y, s)
        | none =>
          if hwit : (witnessRowCandidates X Y A δ).Nonempty then
            CostM.bind (scanFinsetTracked X (selectWitnessRow X Y A δ d V hwit)) (fun x_star =>
              let Y' := rowSupport Y A x_star
              CostM.bind
                (findSomeListTracked
                  (fun s =>
                    scanMatrixTracked X Y
                      (if (ε / 16) * (((2 : ℝ) ^ ((s + 2) * d))⁻¹) * (X.card : ℝ) ≤
                          ((innerDyadicBucket X Y' A δ s).card : ℝ) then
                        some s
                      else
                        none))
                  (List.range d))
                (fun innerOpt =>
                  match innerOpt with
                  | some s =>
                    retTracked ("subrect", innerDyadicBucket X Y' A δ s, Y', s)
                  | none =>
                    retTracked ("regular", X, Y, 0)))
          else
            retTracked ("regular", X, Y, 0)))

@[simp]
theorem dyadicSiftTracked_fst (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (ε : ℝ) (d : ℕ) (V_tracked : CostM (α → ℝ)) :
    (dyadicSiftTracked X Y A ε d V_tracked).1 = dyadicSift X Y A ε d V_tracked.1 := by
  unfold dyadicSiftTracked dyadicSift
  simp only [CostM.bind_fst, findSomeListTracked_fst, scanMatrixTracked_fst]
  cases (List.range d).findSome? _ with
  | some s => rfl
  | none =>
    dsimp only
    split_ifs with hwit
    · simp only [CostM.bind_fst, scanFinsetTracked_fst, findSomeListTracked_fst,
        scanMatrixTracked_fst]
      cases (List.range d).findSome? _ <;> rfl
    · rfl

theorem dyadicSiftTracked_snd_le (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (ε : ℝ) (d : ℕ) (V_tracked : CostM (α → ℝ)) :
    (dyadicSiftTracked X Y A ε d V_tracked).2 ≤
      V_tracked.2 + (4 * d + 4) * ((X.card + 1) * (Y.card + 1)) := by
  unfold dyadicSiftTracked
  dsimp only [CostM.bind_snd]
  set Q := (X.card + 1) * (Y.card + 1)
  have hQ_pos : 1 ≤ Q := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  have hX_le : X.card + 1 ≤ Q := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have hXY2_le : X.card * Y.card + 2 ≤ 2 * Q := by dsimp [Q]; nlinarith
  have hmul_d : (X.card * Y.card + 2) * d ≤ 2 * Q * d := Nat.mul_le_mul_right d hXY2_le
  have h_alg : (4 * d + 4) * Q = 2 * Q * d + 2 * Q * d + 4 * Q := by ring
  have houter_le :
      (findSomeListTracked
        (fun s =>
          scanMatrixTracked X Y
            (if (ε / 16) * (((2 : ℝ) ^ ((s + 2) * d))⁻¹) * (X.card : ℝ) ≤
                ((outerDyadicBucket X Y A ((1 + ε / 2) * matDensity X Y A) s).card : ℝ) then
              some s
            else
              none))
        (List.range d)).2 ≤ (X.card * Y.card + 2) * d + 1 := by
    have h := findSomeListTracked_snd_le_of_const
      (fun s =>
        scanMatrixTracked X Y
          (if (ε / 16) * (((2 : ℝ) ^ ((s + 2) * d))⁻¹) * (X.card : ℝ) ≤
              ((outerDyadicBucket X Y A ((1 + ε / 2) * matDensity X Y A) s).card : ℝ) then
            some s
          else
            none))
      (X.card * Y.card + 1) (List.range d)
      (fun s _ => by simp [scanMatrixTracked_snd])
    simpa [List.length_range] using h
  rw [findSomeListTracked_fst]
  simp only [scanMatrixTracked_fst]
  cases h_out : (List.range d).findSome? _ with
  | some s =>
    dsimp only [retTracked_snd]
    omega
  | none =>
    dsimp only
    split_ifs with hwit
    · dsimp only [CostM.bind_snd, scanFinsetTracked_fst]
      rw [scanFinsetTracked_snd]
      set x_star := selectWitnessRow X Y A ((1 + ε / 2) * matDensity X Y A) d V_tracked.1 hwit
      set Y' := rowSupport Y A x_star
      have hinner_le :
          (findSomeListTracked
            (fun s =>
              scanMatrixTracked X Y
                (if (ε / 16) * (((2 : ℝ) ^ ((s + 2) * d))⁻¹) * (X.card : ℝ) ≤
                    ((innerDyadicBucket X Y' A ((1 + ε / 2) * matDensity X Y A) s).card : ℝ) then
                  some s
                else
                  none))
            (List.range d)).2 ≤ (X.card * Y.card + 2) * d + 1 := by
        have h := findSomeListTracked_snd_le_of_const
          (fun s =>
            scanMatrixTracked X Y
              (if (ε / 16) * (((2 : ℝ) ^ ((s + 2) * d))⁻¹) * (X.card : ℝ) ≤
                  ((innerDyadicBucket X Y' A ((1 + ε / 2) * matDensity X Y A) s).card : ℝ) then
                some s
              else
                none))
          (X.card * Y.card + 1) (List.range d)
          (fun s _ => by simp [scanMatrixTracked_snd])
        simpa [List.length_range] using h
      rw [findSomeListTracked_fst]
      simp only [scanMatrixTracked_fst]
      cases (List.range d).findSome? _ <;> dsimp only [retTracked_snd] <;> omega
    · dsimp only [retTracked_snd]
      omega

/-- Bernoulli's inequality $1 + d x \le (1 + x)^d$ for $x \ge 0$ and $d \in \mathbb{N}$. -/
lemma one_add_mul_le_pow_nat {x : ℝ} (hx : 0 ≤ x) (d : ℕ) :
    1 + (d : ℝ) * x ≤ (1 + x) ^ d := by
  induction d with
  | zero => simp
  | succ n ih =>
    push_cast
    rw [pow_succ]
    have h1 : (1 + (n : ℝ) * x) * (1 + x) ≤ (1 + x) ^ n * (1 + x) :=
      mul_le_mul_of_nonneg_right ih (by linarith)
    have h2 : 0 ≤ (n : ℝ) * (x * x) := mul_nonneg (Nat.cast_nonneg n) ( mul_self_nonneg x)
    nlinarith

/-- Strict Bernoulli lower bound $(1 + x)^{2d} - (1 + x)^d > d x$ for $x > 0$ and $d \ge 1$
(`paper.tex`, Section 4.2, Case A). -/
lemma pow_two_mul_sub_pow_gt {x : ℝ} (hx : 0 < x) {d : ℕ} (hd : 1 ≤ d) :
    (d : ℝ) * x < (1 + x) ^ (2 * d) - (1 + x) ^ d := by
  have hbern : 1 + (d : ℝ) * x ≤ (1 + x) ^ d := one_add_mul_le_pow_nat (le_of_lt hx) d
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hdx_pos : 0 < (d : ℝ) * x := mul_pos hd_pos hx
  have hpow_gt_one : 1 < (1 + x) ^ d := by linarith
  have h2d : (1 + x) ^ (2 * d) = (1 + x) ^ d * (1 + x) ^ d := by
    rw [two_mul, pow_add]
  nlinarith

/-- Strict Bernoulli lower bound $(1 + x)^d - 1 > d x$ for $x > 0$ and $d \ge 2$
(`paper.tex`, Section 4.2, Case B). -/
lemma pow_sub_one_gt_of_two_le {x : ℝ} (hx : 0 < x) {d : ℕ} (hd : 2 ≤ d) :
    (d : ℝ) * x < (1 + x) ^ d - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  push_cast
  have hbern : 1 + (k : ℝ) * x ≤ (1 + x) ^ k := one_add_mul_le_pow_nat (le_of_lt hx) k
  have hpow2 : (1 + x) ^ (k + 2) = (1 + x) ^ k * (1 + 2 * x + x ^ 2) := by
    rw [pow_add]
    ring
  have hmul : (1 + (k : ℝ) * x) * (1 + 2 * x + x ^ 2) ≤ (1 + x) ^ k * (1 + 2 * x + x ^ 2) :=
    mul_le_mul_of_nonneg_right hbern (by positivity)
  have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx
  have hkx : 0 ≤ (k : ℝ) * x := mul_nonneg (Nat.cast_nonneg k) (le_of_lt hx)
  nlinarith

/-- Dyadic interval covering lemma: for $\delta > 0$ and any $r \in [\delta, 2^d \delta)$,
there exists $s \in \text{Finset.range } d$ such that $2^s \delta \le r < 2^{s+1}\delta$. -/
lemma exists_dyadic_bucket_of_mem_Ico {δ r : ℝ} (hδ : 0 < δ) :
    ∀ d : ℕ, δ ≤ r → r < (2 : ℝ) ^ d * δ →
      ∃ s ∈ Finset.range d, (2 : ℝ) ^ s * δ ≤ r ∧ r < (2 : ℝ) ^ (s + 1) * δ
  | 0, hlo, hhi => by
    simp only [pow_zero, one_mul] at hhi
    linarith
  | d + 1, hlo, hhi => by
    by_cases hlt : r < (2 : ℝ) ^ d * δ
    · obtain ⟨s, hs, h1, h2⟩ := exists_dyadic_bucket_of_mem_Ico hδ d hlo hlt
      exact ⟨s, Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hs)), h1, h2⟩
    · refine ⟨d, Finset.mem_range.mpr (Nat.lt_succ_self d), not_lt.mp hlt, hhi⟩

/-- Pointwise dyadic bound: for any $r \in [0, 1]$ and $\delta > 2^{-d}$,
either $r < \delta$ or $r \in [2^s \delta, 2^{s+1}\delta)$ for some $s < d$. -/
lemma dyadic_partition_cases {δ r : ℝ} {d : ℕ} (hδ : (2 : ℝ) ^ d * δ > 1)
    (hr1 : r ≤ 1) :
    r < δ ∨ ∃ s ∈ Finset.range d, (2 : ℝ) ^ s * δ ≤ r ∧ r < (2 : ℝ) ^ (s + 1) * δ := by
  by_cases hlt : r < δ
  · exact Or.inl hlt
  · right
    have hδ_pos : 0 < δ := by
      have : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
      nlinarith
    exact exists_dyadic_bucket_of_mem_Ico hδ_pos d (not_lt.mp hlt) (lt_of_le_of_lt hr1 hδ)

/-- Every non-empty outer dyadic bucket $B_s$ has density $\mathbb{E}[A[B_s, Y]] \ge 2^s \delta$. -/
lemma matDensity_outerDyadicBucket_ge {X : Finset α} {Y : Finset β} {A : α → β → ℝ}
    {δ : ℝ} {s : ℕ} (hne : (outerDyadicBucket X Y A δ s).Nonempty) :
    (2 : ℝ) ^ s * δ ≤ matDensity (outerDyadicBucket X Y A δ s) Y A := by
  apply le_expectSet_of_le hne
  intro x hx
  exact (mem_outerDyadicBucket_iff.mp hx).2.1

/-- Every non-empty inner dyadic bucket $D_s$ has density $\mathbb{E}[A[D_s, Y']] \ge 2^s \delta$. -/
lemma matDensity_innerDyadicBucket_ge {X : Finset α} {Y' : Finset β} {A : α → β → ℝ}
    {δ : ℝ} {s : ℕ} (hne : (innerDyadicBucket X Y' A δ s).Nonempty) :
    (2 : ℝ) ^ s * δ ≤ matDensity (innerDyadicBucket X Y' A δ s) Y' A := by
  apply le_expectSet_of_le hne
  intro x' hx'
  exact (mem_innerDyadicBucket_iff.mp hx').2.1

/-- **Lemma 4.2(1) Case A (`dyadicSift_caseA_heavy_bucket`, `paper.tex` §4.2)**:
When $\|A\|_{U(2, d)}^{2d} > ((1 + \varepsilon_0)\delta)^{2d}$ and no $x \in X_{\ge \delta^2}$ has
$\|A_x\|_{U(1, d)}^d > ((1 + \varepsilon_0)\delta)^d$, the outer dyadic bucketing $B_s$ produces
a scale $s^* \in \{0, \dots, d-1\}$ with $|B_{s^*}| \ge \frac{\varepsilon}{16} 2^{-(s^*+2)d}|X|$
and $\mathbb{E}[A[B_{s^*}, Y]] \ge 2^{s^*}(1 + \varepsilon/2)\mathbb{E}[A]$. -/
theorem dyadicSift_caseA_heavy_bucket
    {X : Finset α} {Y : Finset β} {A : α → β → ℝ} {ε : ℝ} {d : ℕ}
    (hX : X.Nonempty) (hY : Y.Nonempty) (hA : IsBinaryMatrix X Y A)
    (hε_pos : 0 < ε) (hε_lt : ε < 1) (hd : 2 ≤ d)
    (hδ_gt : 1 < (2 : ℝ) ^ d * ((1 + ε / 2) * matDensity X Y A))
    (h_irreg : (((1 + ε / 4) * ((1 + ε / 2) * matDensity X Y A)) ^ (2 * d) <
      gridNorm2Pow X Y A d))
    (h_caseA : ∀ x ∈ witnessRowCandidates X Y A ((1 + ε / 2) * matDensity X Y A),
      gridNorm1Pow X (rowSupport Y A x) A d ≤
        ((1 + ε / 4) * ((1 + ε / 2) * matDensity X Y A)) ^ d) :
    let δ := (1 + ε / 2) * matDensity X Y A
    ∃ s ∈ Finset.range d,
      (ε / 16) * (((2 : ℝ) ^ ((s + 2) * d))⁻¹) * (X.card : ℝ) ≤
        ((outerDyadicBucket X Y A δ s).card : ℝ) ∧
      (2 : ℝ) ^ s * δ ≤ matDensity (outerDyadicBucket X Y A δ s) Y A := by
  classical
  dsimp only
  set μ := matDensity X Y A
  set δ := (1 + ε / 2) * μ
  set ε₀ := ε / 4
  have hδ_def : δ = (1 + ε / 2) * μ := rfl
  have hε₀_def : ε₀ = ε / 4 := rfl
  have h2d_pos : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  have hδ_pos : 0 < δ := by nlinarith
  have hε₀_pos : 0 < ε₀ := by positivity
  have hε₀_lt_one : ε₀ < 1 := by linarith
  have hX_pos : (0 : ℝ) < (X.card : ℝ) := Nat.cast_pos.mpr hX.card_pos
  -- Pointwise bound on f(x) = rowDeg(x)^d * gridNorm1Pow(A_x, d) for x ∈ X
  let f : α → ℝ := fun x => (rowDeg Y A x) ^ d * gridNorm1Pow X (rowSupport Y A x) A d
  have hf_bound : ∀ x ∈ X,
      f x ≤ (1 + ε₀) ^ d * δ ^ (2 * d) +
        ∑ s ∈ Finset.range d,
          (if x ∈ outerDyadicBucket X Y A δ s then ((2 : ℝ) ^ ((s + 2) * d) * δ ^ (2 * d)) else 0) := by
    intro x hx
    have hdeg0 : 0 ≤ rowDeg Y A x := rowDeg_nonneg_of_unitInterval hA.to_unitInterval hx
    have hdeg1 : rowDeg Y A x ≤ 1 := rowDeg_le_one_of_unitInterval hY hA.to_unitInterval hx
    have hA_sub : IsUnitIntervalMatrix X (rowSupport Y A x) A :=
      hA.to_unitInterval.mono (Finset.Subset.refl X) (rowSupport_subset Y A x)
    have hnorm0 : 0 ≤ gridNorm1Pow X (rowSupport Y A x) A d :=
      gridNorm1Pow_nonneg (fun x' hx' => rowDeg_nonneg_of_unitInterval hA_sub hx') d
    have hsum_nonneg : 0 ≤ ∑ s ∈ Finset.range d,
        (if x ∈ outerDyadicBucket X Y A δ s then ((2 : ℝ) ^ ((s + 2) * d) * δ ^ (2 * d)) else 0) := by
      apply Finset.sum_nonneg
      intro s _
      by_cases h : x ∈ outerDyadicBucket X Y A δ s <;> simp [h]; positivity
    rcases dyadic_partition_cases hδ_gt hdeg1 with hlt_δ | ⟨s, hs, hs_lo, hs_hi⟩
    · -- Case `rowDeg Y A x < δ`: either `< δ^2` or `∈ [δ^2, δ)`
      have hterm1 : f x ≤ (1 + ε₀) ^ d * δ ^ (2 * d) := by
        by_cases hlt_sq : rowDeg Y A x < δ ^ 2
        · -- `rowDeg Y A x < δ^2`: note if `rowSupport` is empty, `gridNorm1Pow = 0`; else `≤ 1`
          have hnorm1 : gridNorm1Pow X (rowSupport Y A x) A d ≤ 1 := by
            by_cases hsupp : (rowSupport Y A x).Nonempty
            · exact gridNorm1Pow_le_one hX
                (fun x' hx' => rowDeg_nonneg_of_unitInterval hA_sub hx')
                (fun x' hx' => rowDeg_le_one_of_unitInterval hsupp hA_sub hx') d
            · have hempty : rowSupport Y A x = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsupp
              unfold gridNorm1Pow rowDeg expectSet
              simp [hempty, show d ≠ 0 by omega]
          have hpow_le : (rowDeg Y A x) ^ d ≤ (δ ^ 2) ^ d :=
            pow_le_pow_left₀ hdeg0 (le_of_lt hlt_sq) d
          have hpow_eq : (δ ^ 2) ^ d = δ ^ (2 * d) := by rw [← pow_mul]
          have hone_le : (1 : ℝ) ≤ (1 + ε₀) ^ d := one_le_pow₀ (by linarith)
          calc
            f x ≤ (δ ^ 2) ^ d * 1 := mul_le_mul hpow_le hnorm1 hnorm0 (by positivity)
            _ = 1 * δ ^ (2 * d) := by rw [hpow_eq, mul_one, one_mul]
            _ ≤ (1 + ε₀) ^ d * δ ^ (2 * d) :=
              mul_le_mul_of_nonneg_right hone_le (by positivity)
        · -- `δ^2 ≤ rowDeg Y A x < δ`: `x ∈ witnessRowCandidates`
          have hcand : x ∈ witnessRowCandidates X Y A δ :=
            mem_witnessRowCandidates_iff.mpr ⟨hx, not_lt.mp hlt_sq⟩
          have hnorm_le := h_caseA x hcand
          have hpow_le : (rowDeg Y A x) ^ d ≤ δ ^ d :=
            pow_le_pow_left₀ hdeg0 (le_of_lt hlt_δ) d
          calc
            f x ≤ δ ^ d * ((1 + ε₀) * δ) ^ d :=
              mul_le_mul hpow_le hnorm_le hnorm0 (by positivity)
            _ = (1 + ε₀) ^ d * δ ^ (2 * d) := by
              rw [mul_pow (1 + ε₀) δ d, two_mul, pow_add δ d d, mul_comm (δ ^ d), mul_assoc]
      linarith
    · -- Case `x ∈ outerDyadicBucket X Y A δ s` for some `s ∈ Finset.range d`
      have hx_mem : x ∈ outerDyadicBucket X Y A δ s :=
        mem_outerDyadicBucket_iff.mpr ⟨hx, hs_lo, hs_hi⟩
      have hδ_le_one : δ ≤ 1 := by
        have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ s := one_le_pow₀ (by norm_num)
        nlinarith
      have hcand : x ∈ witnessRowCandidates X Y A δ := by
        rw [mem_witnessRowCandidates_iff]
        refine ⟨hx, ?_⟩
        have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ s := one_le_pow₀ (by norm_num)
        have hsq : δ ^ 2 ≤ δ := by nlinarith
        nlinarith
      have hnorm_le : gridNorm1Pow X (rowSupport Y A x) A d ≤ (2 * δ) ^ d := by
        calc
          gridNorm1Pow X (rowSupport Y A x) A d ≤ ((1 + ε₀) * δ) ^ d := h_caseA x hcand
          _ ≤ (2 * δ) ^ d := by
            apply pow_le_pow_left₀ (by positivity)
            nlinarith
      have hdeg_pow : (rowDeg Y A x) ^ d ≤ ((2 : ℝ) ^ (s + 1) * δ) ^ d :=
        pow_le_pow_left₀ hdeg0 (le_of_lt hs_hi) d
      have hfx_le : f x ≤ (2 : ℝ) ^ ((s + 2) * d) * δ ^ (2 * d) := by
        calc
          f x ≤ ((2 : ℝ) ^ (s + 1) * δ) ^ d * (2 * δ) ^ d :=
            mul_le_mul hdeg_pow hnorm_le hnorm0 (by positivity)
          _ = (2 : ℝ) ^ ((s + 2) * d) * δ ^ (2 * d) := by
            rw [mul_pow ((2 : ℝ) ^ (s + 1)) δ d, mul_pow 2 δ d, ← pow_mul, two_mul d, pow_add δ d d]
            have h2 : ((2 : ℝ) ^ ((s + 1) * d)) * (2 : ℝ) ^ d = (2 : ℝ) ^ ((s + 2) * d) := by
              rw [← pow_add]
              congr 1
              ring
            calc
              (2 : ℝ) ^ ((s + 1) * d) * δ ^ d * ((2 : ℝ) ^ d * δ ^ d) =
                  ((2 : ℝ) ^ ((s + 1) * d) * (2 : ℝ) ^ d) * (δ ^ d * δ ^ d) := by
                rw [mul_assoc, mul_left_comm (δ ^ d), ← mul_assoc]
              _ = (2 : ℝ) ^ ((s + 2) * d) * (δ ^ d * δ ^ d) := by rw [h2]
      have hsingle_le : (2 : ℝ) ^ ((s + 2) * d) * δ ^ (2 * d) ≤
          ∑ s' ∈ Finset.range d,
            (if x ∈ outerDyadicBucket X Y A δ s' then ((2 : ℝ) ^ ((s' + 2) * d) * δ ^ (2 * d)) else 0) := by
        have hterm : (if x ∈ outerDyadicBucket X Y A δ s then
            ((2 : ℝ) ^ ((s + 2) * d) * δ ^ (2 * d)) else 0) =
            (2 : ℝ) ^ ((s + 2) * d) * δ ^ (2 * d) := if_pos hx_mem
        rw [← hterm]
        exact Finset.single_le_sum
          (f := fun s' => if x ∈ outerDyadicBucket X Y A δ s' then
            ((2 : ℝ) ^ ((s' + 2) * d) * δ ^ (2 * d)) else 0)
          (fun s' _ => by
            by_cases h : x ∈ outerDyadicBucket X Y A δ s' <;> simp [h]; positivity)
          hs
      have hpos1 : 0 ≤ (1 + ε₀) ^ d * δ ^ (2 * d) := by positivity
      linarith
  -- Sum / expectation over X
  have hexp_le : gridNorm2Pow X Y A d ≤
      (1 + ε₀) ^ d * δ ^ (2 * d) +
        ∑ s ∈ Finset.range d,
          (((outerDyadicBucket X Y A δ s).card : ℝ) / (X.card : ℝ)) *
            ((2 : ℝ) ^ ((s + 2) * d) * δ ^ (2 * d)) := by
    rw [u2d_expansion hA d]
    have hmono := expectSet_mono hf_bound
    rw [expectSet_add, expectSet_const hX] at hmono
    have hsum_exp : expectSet X (fun x => ∑ s ∈ Finset.range d,
        (if x ∈ outerDyadicBucket X Y A δ s then ((2 : ℝ) ^ ((s + 2) * d) * δ ^ (2 * d)) else 0)) =
        ∑ s ∈ Finset.range d,
          (((outerDyadicBucket X Y A δ s).card : ℝ) / (X.card : ℝ)) *
            ((2 : ℝ) ^ ((s + 2) * d) * δ ^ (2 * d)) := by
      unfold expectSet
      rw [Finset.sum_comm, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      have hfilter : (X.filter (fun x => x ∈ outerDyadicBucket X Y A δ s)) =
          outerDyadicBucket X Y A δ s := by
        ext x
        simp only [Finset.mem_filter, mem_outerDyadicBucket_iff, and_self_left]
      rw [hfilter, mul_div_right_comm]
    linarith
  -- Use `h_irreg` and Bernoulli inequality `(1 + ε₀)^(2d) - (1 + ε₀)^d > d * ε₀`
  have hirreg_pow : (1 + ε₀) ^ (2 * d) * δ ^ (2 * d) < gridNorm2Pow X Y A d := by
    rwa [mul_pow] at h_irreg
  have hbern := pow_two_mul_sub_pow_gt hε₀_pos (by omega : 1 ≤ d)
  have hδ2d_pos : 0 < δ ^ (2 * d) := by positivity
  have hsum_gt : (d : ℝ) * ε₀ * δ ^ (2 * d) <
      ∑ s ∈ Finset.range d,
        (((outerDyadicBucket X Y A δ s).card : ℝ) / (X.card : ℝ)) *
          ((2 : ℝ) ^ ((s + 2) * d) * δ ^ (2 * d)) := by
    nlinarith
  -- By averaging over the d terms in `Finset.range d`, some `s` exceeds `ε₀ * δ^(2d)`
  by_contra h_none
  push_neg at h_none
  have hsum_le : ∑ s ∈ Finset.range d,
      (((outerDyadicBucket X Y A δ s).card : ℝ) / (X.card : ℝ)) *
        ((2 : ℝ) ^ ((s + 2) * d) * δ ^ (2 * d)) ≤
      ∑ _s ∈ Finset.range d, ε₀ * δ ^ (2 * d) := by
    apply Finset.sum_le_sum
    intro s hs
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ ((s + 2) * d) := by positivity
    by_cases hcard_le :
        ((outerDyadicBucket X Y A δ s).card : ℝ) <
          (ε / 16) * (((2 : ℝ) ^ ((s + 2) * d))⁻¹) * (X.card : ℝ)
    · have h1 : (((outerDyadicBucket X Y A δ s).card : ℝ) / (X.card : ℝ)) *
          (2 : ℝ) ^ ((s + 2) * d) ≤ ε / 16 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hX_pos]
        have hlt := mul_lt_mul_of_pos_right hcard_le hpow_pos
        have hcancel : (ε / 16) * ((2 : ℝ) ^ ((s + 2) * d))⁻¹ * (X.card : ℝ) *
            (2 : ℝ) ^ ((s + 2) * d) = (ε / 16) * (X.card : ℝ) := by
          calc
            (ε / 16) * ((2 : ℝ) ^ ((s + 2) * d))⁻¹ * (X.card : ℝ) * (2 : ℝ) ^ ((s + 2) * d) =
                (ε / 16) * (X.card : ℝ) * (((2 : ℝ) ^ ((s + 2) * d))⁻¹ * (2 : ℝ) ^ ((s + 2) * d)) := by ring
            _ = (ε / 16) * (X.card : ℝ) := by
              rw [inv_mul_cancel₀ hpow_pos.ne', mul_one]
        linarith
      have h2 : ε / 16 ≤ ε₀ := by linarith
      calc
        (((outerDyadicBucket X Y A δ s).card : ℝ) / (X.card : ℝ)) *
            ((2 : ℝ) ^ ((s + 2) * d) * δ ^ (2 * d)) =
          ((((outerDyadicBucket X Y A δ s).card : ℝ) / (X.card : ℝ)) *
            (2 : ℝ) ^ ((s + 2) * d)) * δ ^ (2 * d) := by rw [← mul_assoc]
        _ ≤ ε₀ * δ ^ (2 * d) :=
          mul_le_mul_of_nonneg_right (le_trans h1 h2) (le_of_lt hδ2d_pos)
    · have hge := not_lt.mp hcard_le
      have hne_s : (outerDyadicBucket X Y A δ s).Nonempty := by
        rw [← Finset.card_pos]
        have : (0 : ℝ) < ((outerDyadicBucket X Y A δ s).card : ℝ) :=
          lt_of_lt_of_le (by positivity) hge
        exact Nat.cast_pos.mp this
      exfalso
      exact not_le.mpr (h_none s hs hge) (matDensity_outerDyadicBucket_ge hne_s)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum_le
  linarith

/-- **Inner heavy-bucket lemma for Case B of Lemma 4.2 (`paper.tex` §4.2)**:
Whenever a candidate row $x^* \in X_{\ge \delta^2}$ satisfies
$\|A_{x^*}\|_{U(1, d)}^d \ge ((1 + \frac{3}{4}\varepsilon_0)\delta)^d$, we have
$|Y'| = |N_A(x^*)| \ge \delta^2 |Y| > 2^{-2d}|Y|$ and there exists $s^* \in \{0, \dots, d-1\}$
with $|D_{s^*}| \ge \frac{\varepsilon}{16} 2^{-(s^*+2)d}|X|$ and
$\mathbb{E}[A[D_{s^*}, Y']] \ge 2^{s^*}(1 + \varepsilon/2)\mathbb{E}[A]$. -/
theorem dyadicSift_inner_heavy_bucket_of_norm
    {X : Finset α} {Y : Finset β} {A : α → β → ℝ} {ε : ℝ} {d : ℕ}
    (hX : X.Nonempty) (hY : Y.Nonempty) (hA : IsBinaryMatrix X Y A)
    (hε_pos : 0 < ε) (hε_lt : ε < 1) (hd : 2 ≤ d)
    (hδ_gt : 1 < (2 : ℝ) ^ d * ((1 + ε / 2) * matDensity X Y A))
    {x_star : α} (hx_star : x_star ∈ witnessRowCandidates X Y A ((1 + ε / 2) * matDensity X Y A))
    (h_norm : (((1 + (3 / 4 : ℝ) * (ε / 4)) * ((1 + ε / 2) * matDensity X Y A)) ^ d ≤
      gridNorm1Pow X (rowSupport Y A x_star) A d)) :
    let δ := (1 + ε / 2) * matDensity X Y A
    let Y' := rowSupport Y A x_star
    δ ^ 2 * (Y.card : ℝ) ≤ (Y'.card : ℝ) ∧
    (((2 : ℝ) ^ (2 * d))⁻¹) * (Y.card : ℝ) < (Y'.card : ℝ) ∧
    ∃ s ∈ Finset.range d,
      (ε / 16) * (((2 : ℝ) ^ ((s + 2) * d))⁻¹) * (X.card : ℝ) ≤
        ((innerDyadicBucket X Y' A δ s).card : ℝ) ∧
      (2 : ℝ) ^ s * δ ≤ matDensity (innerDyadicBucket X Y' A δ s) Y' A := by
  classical
  dsimp only
  set μ := matDensity X Y A
  set δ := (1 + ε / 2) * μ
  set ε₀ := ε / 4
  set Y' := rowSupport Y A x_star
  have hδ_def : δ = (1 + ε / 2) * μ := rfl
  have hε₀_def : ε₀ = ε / 4 := rfl
  have h2d_pos : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  have hδ_pos : 0 < δ := by nlinarith
  have hY_pos : (0 : ℝ) < (Y.card : ℝ) := Nat.cast_pos.mpr hY.card_pos
  have hX_pos : (0 : ℝ) < (X.card : ℝ) := Nat.cast_pos.mpr hX.card_pos
  have hx_mem : x_star ∈ X ∧ δ ^ 2 ≤ rowDeg Y A x_star :=
    mem_witnessRowCandidates_iff.mp hx_star
  -- Bound on |Y'| = deg_A(x_star) * |Y| ≥ δ^2 |Y| > 2^{-2d} |Y|
  have hY'_card : (Y'.card : ℝ) = rowDeg Y A x_star * (Y.card : ℝ) :=
    card_rowSupport_eq_rowDeg_mul_card hY hA hx_mem.1
  have hY'_ge : δ ^ 2 * (Y.card : ℝ) ≤ (Y'.card : ℝ) := by
    rw [hY'_card]
    exact mul_le_mul_of_nonneg_right hx_mem.2 (le_of_lt hY_pos)
  have hδ_gt_inv : ((2 : ℝ) ^ d)⁻¹ < δ := by
    rw [inv_lt_iff_one_lt_mul₀ h2d_pos, mul_comm]
    exact hδ_gt
  have hδ2_gt : (((2 : ℝ) ^ (2 * d))⁻¹) < δ ^ 2 := by
    have hsq : (((2 : ℝ) ^ d)⁻¹) ^ 2 < δ ^ 2 :=
      pow_lt_pow_left₀ hδ_gt_inv (by positivity) (by norm_num)
    have hpow_eq : (((2 : ℝ) ^ d)⁻¹) ^ 2 = ((2 : ℝ) ^ (2 * d))⁻¹ := by
      rw [inv_pow, ← pow_mul, mul_comm d 2]
    rwa [← hpow_eq]
  have hY'_gt : (((2 : ℝ) ^ (2 * d))⁻¹) * (Y.card : ℝ) < (Y'.card : ℝ) :=
    lt_of_lt_of_le (mul_lt_mul_of_pos_right hδ2_gt hY_pos) hY'_ge
  have hY'_ne : Y'.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < (Y'.card : ℝ) := lt_trans (by positivity) hY'_gt
    exact Nat.cast_pos.mp this
  refine ⟨hY'_ge, hY'_gt, ?_⟩
  -- Pointwise bound on rowDeg Y' A x' ^ d for x' ∈ X
  have hA_sub : IsUnitIntervalMatrix X Y' A :=
    hA.to_unitInterval.mono (Finset.Subset.refl X) (rowSupport_subset Y A x_star)
  have hf_bound : ∀ x' ∈ X,
      (rowDeg Y' A x') ^ d ≤ δ ^ d +
        ∑ s ∈ Finset.range d,
          (if x' ∈ innerDyadicBucket X Y' A δ s then ((2 : ℝ) ^ ((s + 1) * d) * δ ^ d) else 0) := by
    intro x' hx'
    have hdeg0 : 0 ≤ rowDeg Y' A x' := rowDeg_nonneg_of_unitInterval hA_sub hx'
    have hdeg1 : rowDeg Y' A x' ≤ 1 := rowDeg_le_one_of_unitInterval hY'_ne hA_sub hx'
    have hsum_nonneg : 0 ≤ ∑ s ∈ Finset.range d,
        (if x' ∈ innerDyadicBucket X Y' A δ s then ((2 : ℝ) ^ ((s + 1) * d) * δ ^ d) else 0) := by
      apply Finset.sum_nonneg
      intro s _
      by_cases h : x' ∈ innerDyadicBucket X Y' A δ s <;> simp [h]; positivity
    rcases dyadic_partition_cases hδ_gt hdeg1 with hlt_δ | ⟨s, hs, hs_lo, hs_hi⟩
    · have hpow_le : (rowDeg Y' A x') ^ d ≤ δ ^ d :=
        pow_le_pow_left₀ hdeg0 (le_of_lt hlt_δ) d
      linarith
    · have hx'_mem : x' ∈ innerDyadicBucket X Y' A δ s :=
        mem_innerDyadicBucket_iff.mpr ⟨hx', hs_lo, hs_hi⟩
      have hpow_le : (rowDeg Y' A x') ^ d ≤ (2 : ℝ) ^ ((s + 1) * d) * δ ^ d := by
        calc
          (rowDeg Y' A x') ^ d ≤ ((2 : ℝ) ^ (s + 1) * δ) ^ d :=
            pow_le_pow_left₀ hdeg0 (le_of_lt hs_hi) d
          _ = (2 : ℝ) ^ ((s + 1) * d) * δ ^ d := by rw [mul_pow ((2 : ℝ) ^ (s + 1)) δ d, ← pow_mul]
      have hsingle_le : (2 : ℝ) ^ ((s + 1) * d) * δ ^ d ≤
          ∑ s' ∈ Finset.range d,
            (if x' ∈ innerDyadicBucket X Y' A δ s' then ((2 : ℝ) ^ ((s' + 1) * d) * δ ^ d) else 0) := by
        have hterm : (if x' ∈ innerDyadicBucket X Y' A δ s then
            ((2 : ℝ) ^ ((s + 1) * d) * δ ^ d) else 0) =
            (2 : ℝ) ^ ((s + 1) * d) * δ ^ d := if_pos hx'_mem
        rw [← hterm]
        exact Finset.single_le_sum
          (f := fun s' => if x' ∈ innerDyadicBucket X Y' A δ s' then
            ((2 : ℝ) ^ ((s' + 1) * d) * δ ^ d) else 0)
          (fun s' _ => by
            by_cases h : x' ∈ innerDyadicBucket X Y' A δ s' <;> simp [h]; positivity)
          hs
      have hδd_nonneg : 0 ≤ δ ^ d := by positivity
      linarith
  have hexp_le : gridNorm1Pow X Y' A d ≤
      δ ^ d +
        ∑ s ∈ Finset.range d,
          (((innerDyadicBucket X Y' A δ s).card : ℝ) / (X.card : ℝ)) *
            ((2 : ℝ) ^ ((s + 1) * d) * δ ^ d) := by
    unfold gridNorm1Pow
    have hmono := expectSet_mono hf_bound
    rw [expectSet_add, expectSet_const hX] at hmono
    have hsum_exp : expectSet X (fun x' => ∑ s ∈ Finset.range d,
        (if x' ∈ innerDyadicBucket X Y' A δ s then ((2 : ℝ) ^ ((s + 1) * d) * δ ^ d) else 0)) =
        ∑ s ∈ Finset.range d,
          (((innerDyadicBucket X Y' A δ s).card : ℝ) / (X.card : ℝ)) *
            ((2 : ℝ) ^ ((s + 1) * d) * δ ^ d) := by
      unfold expectSet
      rw [Finset.sum_comm, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      have hfilter : (X.filter (fun x' => x' ∈ innerDyadicBucket X Y' A δ s)) =
          innerDyadicBucket X Y' A δ s := by
        ext x'
        simp only [Finset.mem_filter, mem_innerDyadicBucket_iff, and_self_left]
      rw [hfilter, mul_div_right_comm]
    linarith
  have hbern := pow_sub_one_gt_of_two_le (by positivity : (0 : ℝ) < (3 / 4 : ℝ) * ε₀) hd
  have hnorm_mul : (1 + (3 / 4 : ℝ) * ε₀) ^ d * δ ^ d ≤ gridNorm1Pow X Y' A d := by
    rwa [mul_pow] at h_norm
  have hδd_pos : 0 < δ ^ d := by positivity
  have hsum_gt : (d : ℝ) * ((3 / 4 : ℝ) * ε₀) * δ ^ d <
      ∑ s ∈ Finset.range d,
        (((innerDyadicBucket X Y' A δ s).card : ℝ) / (X.card : ℝ)) *
          ((2 : ℝ) ^ ((s + 1) * d) * δ ^ d) := by
    nlinarith
  by_contra h_none
  push_neg at h_none
  have hsum_le : ∑ s ∈ Finset.range d,
      (((innerDyadicBucket X Y' A δ s).card : ℝ) / (X.card : ℝ)) *
        ((2 : ℝ) ^ ((s + 1) * d) * δ ^ d) ≤
      ∑ _s ∈ Finset.range d, ((3 / 4 : ℝ) * ε₀) * δ ^ d := by
    apply Finset.sum_le_sum
    intro s hs
    have hpow1_pos : (0 : ℝ) < (2 : ℝ) ^ ((s + 1) * d) := by positivity
    have hpow2_pos : (0 : ℝ) < (2 : ℝ) ^ ((s + 2) * d) := by positivity
    have hpow_le : (2 : ℝ) ^ ((s + 1) * d) ≤ (2 : ℝ) ^ ((s + 2) * d) := by
      apply pow_le_pow_right₀ (by norm_num)
      nlinarith
    have hinv_le : ((2 : ℝ) ^ ((s + 2) * d))⁻¹ ≤ ((2 : ℝ) ^ ((s + 1) * d))⁻¹ :=
      inv_anti₀ hpow1_pos hpow_le
    by_cases hcard_le :
        ((innerDyadicBucket X Y' A δ s).card : ℝ) <
          (ε / 16) * (((2 : ℝ) ^ ((s + 2) * d))⁻¹) * (X.card : ℝ)
    · have hcard_lt1 :
          ((innerDyadicBucket X Y' A δ s).card : ℝ) <
            (ε / 16) * (((2 : ℝ) ^ ((s + 1) * d))⁻¹) * (X.card : ℝ) := by
        have : (ε / 16) * (((2 : ℝ) ^ ((s + 2) * d))⁻¹) * (X.card : ℝ) ≤
            (ε / 16) * (((2 : ℝ) ^ ((s + 1) * d))⁻¹) * (X.card : ℝ) := by
          have : 0 ≤ (ε / 16) * (X.card : ℝ) := by positivity
          nlinarith
        linarith
      have h1 : (((innerDyadicBucket X Y' A δ s).card : ℝ) / (X.card : ℝ)) *
          (2 : ℝ) ^ ((s + 1) * d) ≤ ε / 16 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hX_pos]
        have hlt := mul_lt_mul_of_pos_right hcard_lt1 hpow1_pos
        have hcancel : (ε / 16) * ((2 : ℝ) ^ ((s + 1) * d))⁻¹ * (X.card : ℝ) *
            (2 : ℝ) ^ ((s + 1) * d) = (ε / 16) * (X.card : ℝ) := by
          calc
            (ε / 16) * ((2 : ℝ) ^ ((s + 1) * d))⁻¹ * (X.card : ℝ) * (2 : ℝ) ^ ((s + 1) * d) =
                (ε / 16) * (X.card : ℝ) * (((2 : ℝ) ^ ((s + 1) * d))⁻¹ * (2 : ℝ) ^ ((s + 1) * d)) := by ring
            _ = (ε / 16) * (X.card : ℝ) := by
              rw [inv_mul_cancel₀ hpow1_pos.ne', mul_one]
        linarith
      have h2 : ε / 16 ≤ (3 / 4 : ℝ) * ε₀ := by linarith
      calc
        (((innerDyadicBucket X Y' A δ s).card : ℝ) / (X.card : ℝ)) *
            ((2 : ℝ) ^ ((s + 1) * d) * δ ^ d) =
          ((((innerDyadicBucket X Y' A δ s).card : ℝ) / (X.card : ℝ)) *
            (2 : ℝ) ^ ((s + 1) * d)) * δ ^ d := by rw [← mul_assoc]
        _ ≤ ((3 / 4 : ℝ) * ε₀) * δ ^ d :=
          mul_le_mul_of_nonneg_right (le_trans h1 h2) (le_of_lt hδd_pos)
    · have hge := not_lt.mp hcard_le
      have hne_s : (innerDyadicBucket X Y' A δ s).Nonempty := by
        rw [← Finset.card_pos]
        have : (0 : ℝ) < ((innerDyadicBucket X Y' A δ s).card : ℝ) :=
          lt_of_lt_of_le (by positivity) hge
        exact Nat.cast_pos.mp this
      exfalso
      exact not_le.mpr (h_none s hs hge) (matDensity_innerDyadicBucket_ge hne_s)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum_le
  linarith

/-- **Lemma 4.2(2) (`dyadicSift_certified_regular`, `paper.tex` §4.2)**:
When `dyadicSift X Y A ε d V` returns `"regular"` (i.e. `.1 = "regular"`), $A$ is
$(\varepsilon, 2, d)$-regular (`IsGridRegular2Pow X Y A ε d` and `IsGridRegular X Y A ε 2 d`). -/
theorem dyadicSift_certified_regular
    {X : Finset α} {Y : Finset β} {A : α → β → ℝ} {ε : ℝ} {d : ℕ} {V : α → ℝ}
    (hX : X.Nonempty) (hY : Y.Nonempty) (hA : IsBinaryMatrix X Y A)
    (hε_pos : 0 < ε) (hε_lt : ε < 1) (hd : 2 ≤ d)
    (hδ_gt : 1 < (2 : ℝ) ^ d * ((1 + ε / 2) * matDensity X Y A))
    (hV_approx : ∀ x ∈ X, 0 < rowDeg Y A x →
      0 ≤ V x ∧
      |(V x) ^ ((1 : ℝ) / (d : ℝ)) - gridNorm X (rowSupport Y A x) A 1 d| ≤
        (ε * ((1 + ε / 2) * matDensity X Y A) ^ 3 / 32) / rowDeg Y A x)
    (h_reg_out : (dyadicSift X Y A ε d V).1 = "regular") :
    IsGridRegular2Pow X Y A ε d ∧ IsGridRegular X Y A ε 2 d := by
  set μ := matDensity X Y A
  set δ := (1 + ε / 2) * μ
  set ε₀ := ε / 4
  have hδ_def : δ = (1 + ε / 2) * μ := rfl
  have hε₀_def : ε₀ = ε / 4 := rfl
  have h2d_pos : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  have hδ_pos : 0 < δ := by nlinarith
  have hμ_pos : 0 < μ := by
    have : 0 < 1 + ε / 2 := by linarith
    nlinarith
  -- First show `(1 + ε₀) * δ ≤ (1 + ε) * μ`
  have h_eps_delta : (1 + ε₀) * δ ≤ (1 + ε) * μ := by
    rw [hε₀_def, hδ_def]
    have : ε ^ 2 ≤ ε := by nlinarith
    nlinarith
  have hpow_2d : IsGridRegular2Pow X Y A ε d := by
    unfold IsGridRegular2Pow
    by_contra h_not_reg
    push_neg at h_not_reg
    have h_irreg : ((1 + ε₀) * δ) ^ (2 * d) < gridNorm2Pow X Y A d := by
      have hle : ((1 + ε₀) * δ) ^ (2 * d) ≤ ((1 + ε) * μ) ^ (2 * d) :=
        pow_le_pow_left₀ (by positivity) h_eps_delta (2 * d)
      exact lt_of_le_of_lt hle h_not_reg
    -- Unpack `dyadicSift` definition to see that neither Step 1 nor Step 3 triggered
    unfold dyadicSift at h_reg_out
    dsimp only at h_reg_out
    cases h_outer_opt : (List.range d).findSome? (fun s =>
        if (ε / 16) * (((2 : ℝ) ^ ((s + 2) * d))⁻¹) * (X.card : ℝ) ≤
            ((outerDyadicBucket X Y A δ s).card : ℝ) then
          some s
        else
          none) with
    | some s =>
      rw [h_outer_opt] at h_reg_out
      dsimp only at h_reg_out; revert h_reg_out; decide
    | none =>
      rw [h_outer_opt] at h_reg_out
      dsimp only at h_reg_out
      have h_outer := (list_range_findSome_ite_eq_none_iff d).mp h_outer_opt
      split_ifs at h_reg_out with hwit
      · let x_star := selectWitnessRow X Y A δ d V hwit
        let Y' := rowSupport Y A x_star
        cases h_inner_opt : (List.range d).findSome? (fun s =>
            if (ε / 16) * (((2 : ℝ) ^ ((s + 2) * d))⁻¹) * (X.card : ℝ) ≤
                ((innerDyadicBucket X Y' A δ s).card : ℝ) then
              some s
            else
              none) with
        | some s =>
          change (match (List.range d).findSome? (fun s =>
              if (ε / 16) * (((2 : ℝ) ^ ((s + 2) * d))⁻¹) * (X.card : ℝ) ≤
                  ((innerDyadicBucket X Y' A δ s).card : ℝ) then
                some s
              else
                none) with
            | some s => ("subrect", innerDyadicBucket X Y' A δ s, Y', s)
            | none => ("regular", X, Y, 0)).1 = "regular" at h_reg_out
          rw [h_inner_opt] at h_reg_out
          dsimp only at h_reg_out; revert h_reg_out; decide
        | none =>
          have h_inner := (list_range_findSome_ite_eq_none_iff d).mp h_inner_opt
          by_cases h_all_small : ∀ x ∈ witnessRowCandidates X Y A δ,
              gridNorm1Pow X (rowSupport Y A x) A d ≤ ((1 + ε₀) * δ) ^ d
          · obtain ⟨s, hs, hge, _⟩ :=
              dyadicSift_caseA_heavy_bucket hX hY hA hε_pos hε_lt hd hδ_gt h_irreg h_all_small
            exact h_outer s hs hge
          · push_neg at h_all_small
            rcases h_all_small with ⟨x_wit, hx_wit, h_wit_gt⟩
            have hx_star_mem : x_star ∈ witnessRowCandidates X Y A δ :=
              selectWitnessRow_mem X Y A δ d V hwit
            have hx_wit_X : x_wit ∈ X ∧ δ ^ 2 ≤ rowDeg Y A x_wit :=
              mem_witnessRowCandidates_iff.mp hx_wit
            have hx_star_X : x_star ∈ X ∧ δ ^ 2 ≤ rowDeg Y A x_star :=
              mem_witnessRowCandidates_iff.mp hx_star_mem
            have herr_wit_both := hV_approx x_wit hx_wit_X.1 (lt_of_lt_of_le (by positivity) hx_wit_X.2)
            have herr_star_both := hV_approx x_star hx_star_X.1 (lt_of_lt_of_le (by positivity) hx_star_X.2)
            have herr_wit := herr_wit_both.2
            have herr_star := herr_star_both.2
            have hv_star_ge : (V x_wit) ^ ((1 : ℝ) / (d : ℝ)) ≤ (V x_star) ^ ((1 : ℝ) / (d : ℝ)) :=
              selectWitnessRow_ge X Y A δ d V hwit hx_wit herr_wit_both.1
            have h_eq_err : ε * δ ^ 3 / 32 = ε₀ * δ / 8 * δ ^ 2 := by
              rw [hε₀_def]; ring
            have herr_wit_le : (ε * δ ^ 3 / 32) / rowDeg Y A x_wit ≤ ε₀ * δ / 8 := by
              rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hx_wit_X.2), h_eq_err]
              exact mul_le_mul_of_nonneg_left hx_wit_X.2 (by positivity)
            have herr_star_le : (ε * δ ^ 3 / 32) / rowDeg Y A x_star ≤ ε₀ * δ / 8 := by
              rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hx_star_X.2), h_eq_err]
              exact mul_le_mul_of_nonneg_left hx_star_X.2 (by positivity)
            have hnorm_wit_ge : (1 + ε₀) * δ ≤ gridNorm X (rowSupport Y A x_wit) A 1 d := by
              have hA_wit : IsUnitIntervalMatrix X (rowSupport Y A x_wit) A :=
                hA.to_unitInterval.mono (Finset.Subset.refl X) (rowSupport_subset Y A x_wit)
              have h1 : (((1 + ε₀) * δ) ^ d) ^ ((d : ℝ)⁻¹) = (1 + ε₀) * δ :=
                Real.pow_rpow_inv_natCast (by positivity) (by omega)
              unfold gridNorm
              rw [Nat.one_mul, gridNormPow_one_eq_gridNorm1Pow, one_div, ← h1]
              exact Real.rpow_le_rpow (by positivity) (le_of_lt h_wit_gt) (by positivity)
            have hnorm_star_ge :
                (1 + (3 / 4 : ℝ) * ε₀) * δ ≤ gridNorm X (rowSupport Y A x_star) A 1 d := by
              have habs_wit := (abs_le.mp herr_wit).1
              have habs_star := (abs_le.mp herr_star).2
              have h_alg : (1 + (3 / 4 : ℝ) * ε₀) * δ = (1 + ε₀) * δ - ε₀ * δ / 8 - ε₀ * δ / 8 := by
                ring
              linarith
            have hA_star : IsUnitIntervalMatrix X (rowSupport Y A x_star) A :=
              hA.to_unitInterval.mono (Finset.Subset.refl X) (rowSupport_subset Y A x_star)
            have hnorm_star_pow :
                ((1 + (3 / 4 : ℝ) * ε₀) * δ) ^ d ≤ gridNorm1Pow X (rowSupport Y A x_star) A d := by
              rw [← gridNorm_one_pow_eq_gridNorm1Pow
                (fun x' hx' => rowDeg_nonneg_of_unitInterval hA_star hx') (by omega)]
              exact pow_le_pow_left₀ (by positivity) hnorm_star_ge d
            obtain ⟨_, _, s, hs, hge, _⟩ :=
              dyadicSift_inner_heavy_bucket_of_norm hX hY hA hε_pos hε_lt hd hδ_gt
                hx_star_mem hnorm_star_pow
            exact h_inner s hs hge
      · -- Step 1 did not trigger, and `witnessRowCandidates` is empty!
        have h_all_small : ∀ x ∈ witnessRowCandidates X Y A δ,
            gridNorm1Pow X (rowSupport Y A x) A d ≤ ((1 + ε₀) * δ) ^ d := by
          intro x hx
          exfalso
          exact hwit ⟨x, hx⟩
        obtain ⟨s, hs, hge, _⟩ :=
          dyadicSift_caseA_heavy_bucket hX hY hA hε_pos hε_lt hd hδ_gt h_irreg h_all_small
        exact h_outer s hs hge
  exact ⟨hpow_2d, isGridRegular_of_isGridRegular2Pow (by omega) (by linarith) (le_of_lt hμ_pos) hpow_2d⟩

/-- **Lemma 4.2 (`\label{lem:dyadic-sift}`, `\eqref{eq:dyadic-sift-guarantees}`, `paper.tex` §4.2)**:
Full specification of `dyadicSift`:
1. Either it returns `("subrect", X', Y', s)` with $s < d$, $X' \subseteq X$, $Y' \subseteq Y$,
   $\mathbb{E}[A[X', Y']] \ge 2^s(1 + \varepsilon/2)\mathbb{E}[A]$,
   $|X'| \ge \frac{\varepsilon}{16} 2^{-(s+2)d}|X|$, and
   $|Y'| \ge (1 + \varepsilon/2)^2 \mathbb{E}[A]^2 |Y| > 2^{-2d}|Y|$;
2. Or it returns `("regular", X, Y, 0)` and $A$ is $(\varepsilon, 2, d)$-regular. -/
theorem lem_dyadic_sift
    {X : Finset α} {Y : Finset β} {A : α → β → ℝ} {ε : ℝ} {d : ℕ} {V : α → ℝ}
    (hX : X.Nonempty) (hY : Y.Nonempty) (hA : IsBinaryMatrix X Y A)
    (hε_pos : 0 < ε) (hε_lt : ε < 1) (hd : 2 ≤ d)
    (hδ_gt : 1 < (2 : ℝ) ^ d * ((1 + ε / 2) * matDensity X Y A))
    (hV_approx : ∀ x ∈ X, 0 < rowDeg Y A x →
      0 ≤ V x ∧
      |(V x) ^ ((1 : ℝ) / (d : ℝ)) - gridNorm X (rowSupport Y A x) A 1 d| ≤
        (ε * ((1 + ε / 2) * matDensity X Y A) ^ 3 / 32) / rowDeg Y A x) :
    let res := dyadicSift X Y A ε d V
    let tag := res.1
    let X' := res.2.1
    let Y' := res.2.2.1
    let s := res.2.2.2
    (tag = "subrect" ∨ tag = "regular") ∧
    (tag = "subrect" →
      s < d ∧
      X' ⊆ X ∧
      Y' ⊆ Y ∧
      X'.Nonempty ∧
      Y'.Nonempty ∧
      (2 : ℝ) ^ s * (1 + ε / 2) * matDensity X Y A ≤ matDensity X' Y' A ∧
      (ε / 16) * (((2 : ℝ) ^ ((s + 2) * d))⁻¹) * (X.card : ℝ) ≤ (X'.card : ℝ) ∧
      ((1 + ε / 2) * matDensity X Y A) ^ 2 * (Y.card : ℝ) ≤ (Y'.card : ℝ) ∧
      (((2 : ℝ) ^ (2 * d))⁻¹) * (Y.card : ℝ) < (Y'.card : ℝ)) ∧
    (tag = "regular" →
      X' = X ∧ Y' = Y ∧ s = 0 ∧
      IsGridRegular2Pow X Y A ε d ∧ IsGridRegular X Y A ε 2 d) := by
  classical
  set δ := (1 + ε / 2) * matDensity X Y A
  have h2d_pos : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  have hδ_pos : 0 < δ := by nlinarith
  have hY_pos : (0 : ℝ) < (Y.card : ℝ) := Nat.cast_pos.mpr hY.card_pos
  have hX_pos : (0 : ℝ) < (X.card : ℝ) := Nat.cast_pos.mpr hX.card_pos
  have hδ_gt_inv : ((2 : ℝ) ^ d)⁻¹ < δ := by
    rw [inv_lt_iff_one_lt_mul₀ h2d_pos, mul_comm]
    exact hδ_gt
  have hδ2_gt : (((2 : ℝ) ^ (2 * d))⁻¹) < δ ^ 2 := by
    have hsq : (((2 : ℝ) ^ d)⁻¹) ^ 2 < δ ^ 2 :=
      pow_lt_pow_left₀ hδ_gt_inv (by positivity) (by norm_num)
    have hpow_eq : (((2 : ℝ) ^ d)⁻¹) ^ 2 = ((2 : ℝ) ^ (2 * d))⁻¹ := by
      rw [inv_pow, ← pow_mul, mul_comm d 2]
    rwa [← hpow_eq]
  have hreg_thm := dyadicSift_certified_regular hX hY hA hε_pos hε_lt hd hδ_gt hV_approx
  dsimp only
  unfold dyadicSift
  dsimp only
  cases h_outer : (List.range d).findSome? (fun s =>
      if (ε / 16) * (((2 : ℝ) ^ ((s + 2) * d))⁻¹) * (X.card : ℝ) ≤
          ((outerDyadicBucket X Y A δ s).card : ℝ) then
        some s
      else
        none) with
  | some s =>
    dsimp only
    have hs_spec := list_range_findSome_ite_eq_some h_outer
    have hs_lt : s < d := Finset.mem_range.mp hs_spec.1
    have hB_card : (ε / 16) * (((2 : ℝ) ^ ((s + 2) * d))⁻¹) * (X.card : ℝ) ≤
        ((outerDyadicBucket X Y A δ s).card : ℝ) := hs_spec.2
    have hB_sub : outerDyadicBucket X Y A δ s ⊆ X :=
      fun x hx => (mem_outerDyadicBucket_iff.mp hx).1
    have hB_ne : (outerDyadicBucket X Y A δ s).Nonempty := by
      rw [← Finset.card_pos]
      have : (0 : ℝ) < ((outerDyadicBucket X Y A δ s).card : ℝ) :=
        lt_of_lt_of_le (by positivity) hB_card
      exact Nat.cast_pos.mp this
    have hB_dens : (2 : ℝ) ^ s * (1 + ε / 2) * matDensity X Y A ≤
        matDensity (outerDyadicBucket X Y A δ s) Y A := by
      rw [mul_assoc]
      exact matDensity_outerDyadicBucket_ge hB_ne
    rcases hB_ne with ⟨x₀, hx₀⟩
    have hx₀_mem := mem_outerDyadicBucket_iff.mp hx₀
    have hdeg_le_one : rowDeg Y A x₀ ≤ 1 :=
      rowDeg_le_one_of_unitInterval hY hA.to_unitInterval hx₀_mem.1
    have h1_le_2s : (1 : ℝ) ≤ (2 : ℝ) ^ s := one_le_pow₀ (by norm_num)
    have hδ_le_one : δ ≤ 1 := by nlinarith [hx₀_mem.2.1]
    have hδ2_le_one : δ ^ 2 ≤ 1 := by nlinarith
    have hY_ge_δ2 : δ ^ 2 * (Y.card : ℝ) ≤ (Y.card : ℝ) := by nlinarith
    have hY_gt_2d : (((2 : ℝ) ^ (2 * d))⁻¹) * (Y.card : ℝ) < (Y.card : ℝ) :=
      lt_of_lt_of_le (mul_lt_mul_of_pos_right hδ2_gt hY_pos) hY_ge_δ2
    refine ⟨Or.inl rfl, ?_, ?_⟩
    · intro _
      exact ⟨hs_lt, hB_sub, Finset.Subset.refl Y, ⟨x₀, hx₀⟩, hY,
        hB_dens, hB_card, hY_ge_δ2, hY_gt_2d⟩
    · intro h; exfalso; revert h; decide
  | none =>
    dsimp only
    split_ifs with hwit
    · set x_star := selectWitnessRow X Y A δ d V hwit
      set Y' := rowSupport Y A x_star
      cases h_inner : (List.range d).findSome? (fun s =>
          if (ε / 16) * (((2 : ℝ) ^ ((s + 2) * d))⁻¹) * (X.card : ℝ) ≤
              ((innerDyadicBucket X Y' A δ s).card : ℝ) then
            some s
          else
            none) with
      | some s =>
        dsimp only
        have hs_spec := list_range_findSome_ite_eq_some h_inner
        have hs_lt : s < d := Finset.mem_range.mp hs_spec.1
        have hD_card : (ε / 16) * (((2 : ℝ) ^ ((s + 2) * d))⁻¹) * (X.card : ℝ) ≤
            ((innerDyadicBucket X Y' A δ s).card : ℝ) := hs_spec.2
        have hD_sub : innerDyadicBucket X Y' A δ s ⊆ X :=
          fun x' hx' => (mem_innerDyadicBucket_iff.mp hx').1
        have hY'_sub : Y' ⊆ Y := rowSupport_subset Y A x_star
        have hD_ne : (innerDyadicBucket X Y' A δ s).Nonempty := by
          rw [← Finset.card_pos]
          have : (0 : ℝ) < ((innerDyadicBucket X Y' A δ s).card : ℝ) :=
            lt_of_lt_of_le (by positivity) hD_card
          exact Nat.cast_pos.mp this
        have hD_dens : (2 : ℝ) ^ s * (1 + ε / 2) * matDensity X Y A ≤
            matDensity (innerDyadicBucket X Y' A δ s) Y' A := by
          rw [mul_assoc]
          exact matDensity_innerDyadicBucket_ge hD_ne
        have hx_star_mem := mem_witnessRowCandidates_iff.mp (selectWitnessRow_mem X Y A δ d V hwit)
        have hY'_card_eq : (Y'.card : ℝ) = rowDeg Y A x_star * (Y.card : ℝ) :=
          card_rowSupport_eq_rowDeg_mul_card hY hA hx_star_mem.1
        have hY'_ge_δ2 : δ ^ 2 * (Y.card : ℝ) ≤ (Y'.card : ℝ) := by
          rw [hY'_card_eq]
          exact mul_le_mul_of_nonneg_right hx_star_mem.2 (le_of_lt hY_pos)
        have hY'_gt_2d : (((2 : ℝ) ^ (2 * d))⁻¹) * (Y.card : ℝ) < (Y'.card : ℝ) :=
          lt_of_lt_of_le (mul_lt_mul_of_pos_right hδ2_gt hY_pos) hY'_ge_δ2
        have hY'_ne : Y'.Nonempty := by
          rw [← Finset.card_pos]
          have : (0 : ℝ) < (Y'.card : ℝ) := lt_trans (by positivity) hY'_gt_2d
          exact Nat.cast_pos.mp this
        refine ⟨Or.inl rfl, ?_, ?_⟩
        · intro _
          exact ⟨hs_lt, hD_sub, hY'_sub, hD_ne, hY'_ne,
            hD_dens, hD_card, hY'_ge_δ2, hY'_gt_2d⟩
        · intro h; exfalso; revert h; decide
      | none =>
        dsimp only
        have h_out : (dyadicSift X Y A ε d V).1 = "regular" := by
          unfold dyadicSift
          dsimp only
          rw [h_outer]
          dsimp only
          rw [dif_pos hwit]
          change (match (List.range d).findSome? (fun s =>
              if (ε / 16) * (((2 : ℝ) ^ ((s + 2) * d))⁻¹) * (X.card : ℝ) ≤
                  ((innerDyadicBucket X Y' A δ s).card : ℝ) then
                some s
              else
                none) with
            | some s => ("subrect", innerDyadicBucket X Y' A δ s, Y', s)
            | none => ("regular", X, Y, 0)).1 = "regular"
          rw [h_inner]
        have hreg := hreg_thm h_out
        refine ⟨Or.inr rfl, ?_, ?_⟩
        · intro h; exfalso; revert h; decide
        · intro _
          exact ⟨rfl, rfl, rfl, hreg.1, hreg.2⟩
    · dsimp only
      have h_out : (dyadicSift X Y A ε d V).1 = "regular" := by
        unfold dyadicSift
        dsimp only
        rw [h_outer]
        dsimp only
        rw [dif_neg hwit]
      have hreg := hreg_thm h_out
      refine ⟨Or.inr rfl, ?_, ?_⟩
      · intro h; exfalso; revert h; decide
      · intro _
        exact ⟨rfl, rfl, rfl, hreg.1, hreg.2⟩

/-!
### Concrete Instantiation of `ApproxGridNorm` in `DyadicSift` (Algorithm 3 Line 5 `\label{line:sift-est}`)
-/

/-- Restrict a real matrix $A : \alpha \to \beta \to \mathbb{R}$ to a globally binary
$\{0, 1\}$-matrix on $X \times Y$. -/
noncomputable def restrictBinaryMat (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (x : α) (y : β) : ℝ :=
  letI := Classical.dec
  if x ∈ X ∧ y ∈ Y ∧ 1 ≤ A x y then 1 else 0

lemma isBinaryRealMat_restrictBinaryMat (X : Finset α) (Y : Finset β) (A : α → β → ℝ) :
    IsBinaryRealMat (restrictBinaryMat X Y A) := by
  classical
  intro x y
  unfold restrictBinaryMat
  split_ifs <;> simp

lemma restrictBinaryMat_eq_of_mem {X : Finset α} {Y : Finset β} {A : α → β → ℝ}
    (hA : IsBinaryMatrix X Y A) {x : α} (hx : x ∈ X) {y : β} (hy : y ∈ Y) :
    restrictBinaryMat X Y A x y = A x y := by
  classical
  unfold restrictBinaryMat
  rcases hA x hx y hy with h0 | h1
  · simp [hx, hy, h0]
  · simp [hx, hy, h1]

lemma rowDeg_restrictBinaryMat_eq {X : Finset α} {Y Y' : Finset β} {A : α → β → ℝ}
    (hA : IsBinaryMatrix X Y A) (hY' : Y' ⊆ Y) {x : α} (hx : x ∈ X) :
    rowDeg Y' (restrictBinaryMat X Y A) x = rowDeg Y' A x := by
  unfold rowDeg expectSet
  congr 1
  refine Finset.sum_congr rfl (fun y hy => ?_)
  exact restrictBinaryMat_eq_of_mem hA hx (hY' hy)

lemma realRowNbr_restrictBinaryMat_eq_rowSupport {X : Finset α} {Y : Finset β} {A : α → β → ℝ}
    (hA : IsBinaryMatrix X Y A) {x : α} (hx : x ∈ X) :
    realRowNbr Y (restrictBinaryMat X Y A) x = rowSupport Y A x := by
  classical
  ext y
  simp only [realRowNbr, rowSupport, Finset.mem_filter]
  constructor <;> intro ⟨hy, h⟩ <;> refine ⟨hy, ?_⟩
  · rw [restrictBinaryMat_eq_of_mem hA hx hy] at h
    linarith
  · rw [restrictBinaryMat_eq_of_mem hA hx hy]
    rcases hA x hx y hy with h0 | h1 <;> linarith

lemma gridNorm1_restrictBinaryMat_eq_gridNorm {X : Finset α} {Y Y' : Finset β} {A : α → β → ℝ}
    (hA : IsBinaryMatrix X Y A) (hY' : Y' ⊆ Y) (d : ℕ) :
    gridNorm1 X Y' (restrictBinaryMat X Y A) d = gridNorm X Y' A 1 d := by
  rw [← gridNorm1_eq_gridNorm_one]
  unfold gridNorm1 gridNorm1Pow expectSet
  congr 2
  refine Finset.sum_congr rfl (fun x' hx' => ?_)
  dsimp only
  rw [rowDeg_restrictBinaryMat_eq hA hY' hx']

/-- Restrict a real matrix $A : \alpha \to \beta \to \mathbb{R}$ to a Boolean matrix
$\alpha \to \beta \to \text{Bool}$ on $X \times Y$. -/
noncomputable def restrictBoolMat (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (x : α) (y : β) : Bool :=
  letI := Classical.dec
  decide (x ∈ X ∧ y ∈ Y ∧ 1 ≤ A x y)

theorem bmatToReal_restrictBoolMat (X : Finset α) (Y : Finset β) (A : α → β → ℝ) :
    bmatToReal (restrictBoolMat X Y A) = restrictBinaryMat X Y A := by
  classical
  ext x y
  unfold bmatToReal boolToReal restrictBoolMat restrictBinaryMat
  by_cases h : x ∈ X ∧ y ∈ Y ∧ 1 ≤ A x y <;> simp [h]

/-- Concrete Algorithm 2 (`ApproxGridNorm`, `paper.tex` §4.1 & §4.2) vector $V : \alpha \to \mathbb{R}$
instantiated with the two-stage oblivious sequence sampler oracle `S : TwoStageSamplerOracle β ε` on
`Y` at parameters `(2 ^ accExp ε d, d * accExp ε d)` and `restrictBinaryMat X Y A`. -/
noncomputable def concreteApproxGridNormV {ε : ℝ} (S : TwoStageSamplerOracle β ε)
    (X : Finset α) (Y : Finset β) (A : α → β → ℝ) (d : ℕ) : α → ℝ :=
  fun x => approxGridNormVSeq X Y
    (S.constructTracked Y (2 ^ accExp ε d) (d * accExp ε d)).1
    (restrictBinaryMat X Y A) d x

/-- Cost-tracked Algorithm 2 (`concreteApproxGridNormVTracked`) in `CostM`: builds the two-stage
oblivious sequence sampler family `T_fam` via `S.constructTracked`, evaluates `powNatTracked` on the
uniform sample sequence length `(T_fam.headD []).length` raised to power $d$ and
`powNatTracked Y.card d`, precomputes the $d$-tuple column-intersection table over $X$ for every
sample sequence $T \in \mathcal{T}$ via `mapListTracked` and `buildTupleTableFinsetTracked`
(Algorithm 2 Line 2 `\label{line:est-u}`), and tabulates across every row $x \in X$ via `tabulateFinsetTracked` and
`approxGridNormVxRowPairTracked` (Algorithm 2 Line 3 `\label{line:est-v}`, `paper.tex` §4.1). -/
noncomputable def concreteApproxGridNormVTracked {ε : ℝ} (S : TwoStageSamplerOracle β ε)
    (X : Finset α) (Y : Finset β) (A : α → β → ℝ) (d : ℕ) : CostM (α → ℝ) :=
  let A_bool := restrictBoolMat X Y A
  CostM.bind (S.constructTracked Y (2 ^ accExp ε d) (d * accExp ε d)) (fun T_fam =>
    CostM.bind (powNatTracked (T_fam.headD []).length d) (fun sPow =>
      CostM.bind (powNatTracked Y.card d) (fun yPow =>
        CostM.bind
          (mapListTracked (fun T => buildTupleTableFinsetTracked X A_bool d T) T_fam)
          (fun tables =>
            tabulateFinsetTracked X (fun x =>
              CostM.bind
                (approxGridNormVxRowPairTracked X Y tables.length sPow yPow A_bool d tables x)
                (fun q => retTracked (ratPairToReal q)))))))

@[simp]
theorem concreteApproxGridNormVTracked_fst {ε : ℝ} (S : TwoStageSamplerOracle β ε)
    (X : Finset α) (Y : Finset β) (A : α → β → ℝ) (d : ℕ) :
    (concreteApproxGridNormVTracked S X Y A d).1 = concreteApproxGridNormV S X Y A d := by
  unfold concreteApproxGridNormVTracked concreteApproxGridNormV
  simp only [CostM.bind_fst, powNatTracked_fst, mapListTracked_fst,
    tabulateFinsetTracked_fst, retTracked_fst, List.length_map]
  ext x
  rw [approxGridNormVxRowPairTracked_build_seq_fst,
    ratPairToReal_approxGridNormVxSeqCommonDenomPair_unconditional X Y
      (S.len_eq Y (2 ^ accExp ε d) (d * accExp ε d))
      (restrictBoolMat X Y A) d x,
    bmatToReal_restrictBoolMat]

/-- Explicit cost factor for `concreteApproxGridNormVTracked` depending on $(c, k, \varepsilon, d)$. -/
noncomputable def concreteApproxGridNormCostFactor (c k : ℕ) (ε : ℝ) (d : ℕ) : ℕ :=
  let B := twoStageSampleSizeBound c k (2 ^ accExp ε d) (d * accExp ε d)
  let F := twoStageFamFactor c k (2 ^ accExp ε d) (2 ^ (d * accExp ε d))
  (powNatTracked B (2 * d)).2 +
    F * ((B ^ d) * (2 * d + 7) + B + 85 * (d + 1) ^ 3 + 6) +
    (d + 1) ^ 3 * (85 * B + 95) + 10 * d + 16

lemma concreteApproxGridNormVTracked_snd_le_arith
    {Xc Yc d D3 L B Bd F P c_S c_pow c_yPow c_build c_tab : ℕ}
    (hS_cost : c_S ≤ (Yc + 1) ^ 2 * F * B)
    (hpow_le : c_pow ≤ P)
    (hyPow_le : c_yPow ≤ D3 * (4 * Yc + 1))
    (hmap_build : c_build ≤ L * (Bd * (Xc * (d + 1) + 3) + 2) + 1)
    (htab_contract :
      c_tab ≤ Xc * (L * (Bd * (d + 3) + 3) + 3 + D3 * (85 * (L + Xc + Yc + B) + 107)) + 1)
    (hlen_le : L ≤ (Yc + 1) * F) :
    (c_S + (c_pow + (c_yPow + (c_build + c_tab)))) + (4 * d + 4) * ((Xc + 1) * (Yc + 1)) ≤
      (Xc + Yc + 2) ^ 2 *
        (P + F * (Bd * (2 * d + 7) + B + 85 * D3 + 6) +
          D3 * (85 * B + 95) + 10 * d + 16) := by
  set Q := (Xc + 1) * (Yc + 1)
  set R := (Xc + Yc + 2) ^ 2
  have hQ_le_R : Q ≤ R := by dsimp [Q, R]; rw [sq]; nlinarith only
  have hY2_le_R : (Yc + 1) ^ 2 ≤ R := by dsimp [R]; rw [sq, sq]; nlinarith only
  have h1 : 1 ≤ R := by dsimp [R]; rw [sq]; nlinarith only
  have hX : Xc + 1 ≤ R := by dsimp [R]; rw [sq]; nlinarith only
  have hY_le_R : Yc + 1 ≤ R := by dsimp [R]; rw [sq]; nlinarith only
  have hXXY_1 : 85 * Xc * (Xc + Yc) + 107 * Xc ≤ 85 * R := by
    dsimp [R]; rw [sq]; nlinarith only
  clear_value R
  have hcomb :
      L * (Bd * (Xc * (d + 1) + 3) + 2) +
          Xc * (L * (Bd * (d + 3) + 3) + 1) ≤
        R * (F * (Bd * (2 * d + 7) + 5)) + Xc := by
    have halg :
        L * (Bd * (Xc * (d + 1) + 3) + 2) +
            Xc * (L * (Bd * (d + 3) + 3) + 1) =
          L * (Bd * (Xc * (2 * d + 4) + 3) + (3 * Xc + 2)) + Xc := by
      ring
    rw [halg]
    have hinner :
        Bd * (Xc * (2 * d + 4) + 3) + (3 * Xc + 2) ≤
          (Xc + 1) * (Bd * (2 * d + 7) + 5) := by
      have hXd : Xc * (2 * d + 4) + 3 ≤ (Xc + 1) * (2 * d + 7) := by nlinarith only
      have hmul1 : Bd * (Xc * (2 * d + 4) + 3) ≤
          Bd * ((Xc + 1) * (2 * d + 7)) :=
        Nat.mul_le_mul_left Bd hXd
      have hmul_eq : Bd * ((Xc + 1) * (2 * d + 7)) + (3 * Xc + 2) ≤
          (Xc + 1) * (Bd * (2 * d + 7) + 5) := by
        have : Bd * ((Xc + 1) * (2 * d + 7)) + 5 * (Xc + 1) =
            (Xc + 1) * (Bd * (2 * d + 7) + 5) := by ring
        omega
      omega
    have hprod :
        L * (Bd * (Xc * (2 * d + 4) + 3) + (3 * Xc + 2)) ≤
          ((Yc + 1) * F) * ((Xc + 1) * (Bd * (2 * d + 7) + 5)) :=
      Nat.mul_le_mul hlen_le hinner
    have hQ_eq :
        ((Yc + 1) * F) * ((Xc + 1) * (Bd * (2 * d + 7) + 5)) =
          Q * (F * (Bd * (2 * d + 7) + 5)) := by
      dsimp [Q]; ring
    have hQR :
        Q * (F * (Bd * (2 * d + 7) + 5)) ≤
          R * (F * (Bd * (2 * d + 7) + 5)) :=
      Nat.mul_le_mul_right _ hQ_le_R
    linarith
  have hXY_Q : Xc * (Yc + 1) ≤ Q := Nat.mul_le_mul_right (Yc + 1) (Nat.le_succ Xc)
  clear_value Q
  have hY_FB : (Yc + 1) ^ 2 * F * B ≤ R * (F * B) := by
    have hY_F : (Yc + 1) ^ 2 * F ≤ R * F := Nat.mul_le_mul_right F hY2_le_R
    calc
      (Yc + 1) ^ 2 * F * B ≤ (R * F) * B := Nat.mul_le_mul_right B hY_F
      _ = R * (F * B) := by ring
  have hyPow_R : c_yPow ≤ R * (4 * D3) := by
    have h4Y : 4 * Yc + 1 ≤ 4 * R := by omega
    have hmul : D3 * (4 * Yc + 1) ≤ D3 * (4 * R) := Nat.mul_le_mul_left D3 h4Y
    have heq : D3 * (4 * R) = R * (4 * D3) := by ring
    exact hyPow_le.trans (hmul.trans_eq heq)
  have hX_extra :
      Xc * (L * (Bd * (d + 3) + 3) + 3 + D3 * (85 * (L + Xc + Yc + B) + 107)) =
        Xc * (L * (Bd * (d + 3) + 3) + 1) + 2 * Xc +
          D3 * 85 * (Xc * L) + D3 * (85 * Xc * (Xc + Yc) + 107 * Xc) +
          Xc * (D3 * (85 * B)) := by
    ring
  have hXL_le : D3 * 85 * (Xc * L) ≤ R * (F * (85 * D3)) := by
    have h1 : Xc * L ≤ Xc * ((Yc + 1) * F) := Nat.mul_le_mul_left Xc hlen_le
    have h2 : Xc * ((Yc + 1) * F) ≤ Q * F := by
      calc
        Xc * ((Yc + 1) * F) = (Xc * (Yc + 1)) * F := by ring
        _ ≤ Q * F := Nat.mul_le_mul_right F hXY_Q
    have h3 : Q * F ≤ R * F := Nat.mul_le_mul_right F hQ_le_R
    have h4 : D3 * 85 * (Xc * L) ≤ D3 * 85 * (R * F) :=
      Nat.mul_le_mul_left (D3 * 85) ((h1.trans h2).trans h3)
    have h5 : D3 * 85 * (R * F) = R * (F * (85 * D3)) := by ring
    exact h4.trans_eq h5
  have hXXY_le : D3 * (85 * Xc * (Xc + Yc) + 107 * Xc) ≤ R * (85 * D3) := by
    have h2 : D3 * (85 * Xc * (Xc + Yc) + 107 * Xc) ≤ D3 * (85 * R) :=
      Nat.mul_le_mul_left D3 hXXY_1
    have h3 : D3 * (85 * R) = R * (85 * D3) := by ring
    exact h2.trans_eq h3
  have hXB_le : Xc * (D3 * (85 * B)) ≤ R * (D3 * (85 * B)) :=
    Nat.mul_le_mul_right (D3 * (85 * B)) (by omega)
  have h4d_Q : (4 * d + 4) * Q ≤ R * (4 * d + 4) := by
    rw [mul_comm (4 * d + 4) Q]
    exact Nat.mul_le_mul_right (4 * d + 4) hQ_le_R
  have hP_le : c_pow ≤ R * P := hpow_le.trans (Nat.le_mul_of_pos_left P (by omega))
  have hS_FB : c_S ≤ R * (F * B) := hS_cost.trans hY_FB
  have hrhs_expand :
      R * (P + F * (Bd * (2 * d + 7) + B + 85 * D3 + 6) +
          D3 * (85 * B + 95) + 10 * d + 16) =
        R * P + R * (F * (Bd * (2 * d + 7) + 5)) + R * (F * B) +
          R * (F * (85 * D3)) + R * (4 * D3) + R * (85 * D3) +
          R * (D3 * (85 * B)) + R * (4 * d + 4) + 12 * R +
          (R * F + R * (6 * d) + R * (6 * D3)) := by
    ring
  rw [hrhs_expand]
  omega

theorem concreteApproxGridNormVTracked_snd_le {ε : ℝ} (S : TwoStageSamplerOracle β ε)
    (X : Finset α) (Y : Finset β) (A : α → β → ℝ) (d : ℕ) :
    (concreteApproxGridNormVTracked S X Y A d).2 + (4 * d + 4) * ((X.card + 1) * (Y.card + 1)) ≤
      (X.card + Y.card + 2) ^ 2 * concreteApproxGridNormCostFactor S.c S.k ε d := by
  unfold concreteApproxGridNormVTracked concreteApproxGridNormCostFactor
  simp only [CostM.bind_snd, powNatTracked_fst]
  set invEps := 2 ^ accExp ε d
  set logInvDelta := d * accExp ε d
  set B := twoStageSampleSizeBound S.c S.k invEps logInvDelta
  set F := twoStageFamFactor S.c S.k invEps (2 ^ logInvDelta)
  set A_bool := restrictBoolMat X Y A
  set T_fam := (S.constructTracked Y invEps logInvDelta).1
  have hinvEps_pos : 1 ≤ invEps := Nat.one_le_two_pow
  have hS_cost :
      (S.constructTracked Y invEps logInvDelta).2 ≤
        (Y.card + 1) ^ 2 * F * B :=
    S.cost_le Y invEps logInvDelta
  have hhead_le : (T_fam.headD []).length ≤ B :=
    S.headD_length_le Y hinvEps_pos logInvDelta
  have hpow_le : (powNatTracked (T_fam.headD []).length d).2 ≤ (powNatTracked B (2 * d)).2 :=
    powNatTracked_snd_mono hhead_le (by omega)
  have hyPow_le : (powNatTracked Y.card d).2 ≤ (d + 1) ^ 3 * (4 * Y.card + 1) :=
    powNatTracked_snd_le_linear Y.card d
  have hmap_build :
      (mapListTracked (fun T : List β => buildTupleTableFinsetTracked X A_bool d T) T_fam).2 ≤
        T_fam.length * ((B ^ d) * (X.card * (d + 1) + 3) + 2) + 1 := by
    apply mapListTracked_snd_le_const
    intro T hT
    rw [buildTupleTableFinsetTracked_snd_eq]
    have hT_le : T.length ^ d ≤ B ^ d :=
      Nat.pow_le_pow_left (S.mem_length_le Y hinvEps_pos logInvDelta hT) d
    have hmul : T.length ^ d * (X.card * (d + 1) + 3) ≤ B ^ d * (X.card * (d + 1) + 3) :=
      Nat.mul_le_mul_right _ hT_le
    omega
  have htab_contract :
      (tabulateFinsetTracked X (fun x =>
        CostM.bind
          (approxGridNormVxRowPairTracked X Y
            ((mapListTracked (fun T : List β =>
              buildTupleTableFinsetTracked X A_bool d T) T_fam).1).length
            ((T_fam.headD []).length ^ d) (Y.card ^ d) A_bool d
            (mapListTracked (fun T : List β =>
              buildTupleTableFinsetTracked X A_bool d T) T_fam).1 x)
          (fun q => retTracked (ratPairToReal q)))).2 ≤
        X.card * (T_fam.length * ((B ^ d) * (d + 3) + 3) + 3 +
          (d + 1) ^ 3 * (85 * (T_fam.length + X.card + Y.card + B) + 107)) + 1 := by
    rw [mapListTracked_fst, List.length_map]
    apply tabulateFinsetTracked_snd_le_const
    intro x _
    simp only [CostM.bind_snd, retTracked_snd]
    have h1 := approxGridNormVxRowPairTracked_build_seq_snd_le X Y T_fam
      ((T_fam.headD []).length ^ d) (Y.card ^ d) A_bool d B x
      (fun T hT => S.mem_length_le Y hinvEps_pos logInvDelta hT)
      (Nat.pow_le_pow_left hhead_le d) le_rfl
    omega
  have hlen_le : T_fam.length ≤ (Y.card + 1) * F :=
    S.length_le Y hinvEps_pos logInvDelta
  exact concreteApproxGridNormVTracked_snd_le_arith hS_cost hpow_le hyPow_le hmap_build htab_contract hlen_le

/-- **Lemma 4.1 guarantee for `concreteApproxGridNormV` (`paper.tex` §4.1 & §4.2)**:
For any binary matrix $A$ on $X \times Y$, $\varepsilon \ge 0$, $d \ge 1$, density threshold
$2^d (1 + \varepsilon / 2) \mathbb{E}[A] > 1$, and $x \in X$ with $\deg_A(x) > 0$,
`concreteApproxGridNormV S X Y A d` satisfies the non-negativity and approximation bounds
required by Algorithm 3 (`DyadicSift`). -/
theorem concreteApproxGridNormV_approx
    {X : Finset α} {Y : Finset β} {A : α → β → ℝ} {ε : ℝ} {d : ℕ}
    (S : TwoStageSamplerOracle β ε)
    (hX : X.Nonempty) (hA : IsBinaryMatrix X Y A)
    (hε : 0 ≤ ε) (hd : 1 ≤ d)
    (hδ_gt : 1 < (2 : ℝ) ^ d * ((1 + ε / 2) * matDensity X Y A)) :
    ∀ x ∈ X, 0 < rowDeg Y A x →
      0 ≤ concreteApproxGridNormV S X Y A d x ∧
      |(concreteApproxGridNormV S X Y A d x) ^ ((1 : ℝ) / (d : ℝ)) -
        gridNorm X (rowSupport Y A x) A 1 d| ≤
        (ε * ((1 + ε / 2) * matDensity X Y A) ^ 3 / 32) / rowDeg Y A x := by
  intro x hx hdeg
  set δ := (1 + ε / 2) * matDensity X Y A
  set α_grid := ε * δ ^ 3 / 32
  have hμ_nonneg : 0 ≤ matDensity X Y A := matDensity_nonneg_of_unitInterval hA.to_unitInterval
  have hδ_nonneg : 0 ≤ δ := by positivity
  have hα_nonneg : 0 ≤ α_grid := by positivity
  have h2d_pos : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  have h2_3d6_pos : (0 : ℝ) < ((2 ^ (3 * d + 6) : ℕ) : ℝ) := by positivity
  have h1_le_cubed : (1 : ℝ) ≤ ((2 : ℝ) ^ d * δ) ^ 3 :=
    one_le_pow₀ (le_of_lt hδ_gt)
  have hpow_3d : ((2 : ℝ) ^ d * δ) ^ 3 = (2 : ℝ) ^ (3 * d) * δ ^ 3 := by
    rw [mul_pow, ← pow_mul, mul_comm d 3]
  have h2_3d6_eq : ((2 ^ (3 * d + 6) : ℕ) : ℝ) = (2 : ℝ) ^ (3 * d) * 64 := by
    push_cast
    rw [pow_add]
    norm_num
  have h_eps_samp : ε / ((2 ^ (3 * d + 6) : ℕ) : ℝ) ≤ α_grid / 2 := by
    rw [div_le_iff₀ h2_3d6_pos, h2_3d6_eq]
    have hmul : ε ≤ ε * ((2 : ℝ) ^ (3 * d) * δ ^ 3) := by
      rw [← hpow_3d]
      exact le_mul_of_one_le_right hε h1_le_cubed
    dsimp [α_grid]
    linarith
  have h_delta_samp : (ε / ((2 ^ (3 * d + 6) : ℕ) : ℝ)) ^ d ≤ (α_grid / 2) ^ d :=
    pow_le_pow_left₀ (by positivity) h_eps_samp d
  have hS : IsSeqSampler Y
      (S.constructTracked Y (2 ^ accExp ε d) (d * accExp ε d)).1
      (α_grid / 2) ((α_grid / 2) ^ d) :=
    S.is_sampler Y d hd h_eps_samp h_delta_samp
  have hM : IsBinaryRealMat (restrictBinaryMat X Y A) :=
    isBinaryRealMat_restrictBinaryMat X Y A
  have hdegM : 0 < rowDeg Y (restrictBinaryMat X Y A) x := by
    rwa [rowDeg_restrictBinaryMat_eq hA (Finset.Subset.refl Y) hx]
  have hlem := lem_approx_grid_norm_seq_real hX hα_nonneg hd hS hM hdegM
  rw [rowDeg_restrictBinaryMat_eq hA (Finset.Subset.refl Y) hx,
    realRowNbr_restrictBinaryMat_eq_rowSupport hA hx,
    gridNorm1_restrictBinaryMat_eq_gridNorm hA (rowSupport_subset Y A x) d] at hlem
  exact hlem

/-- Concrete Algorithm 3 (`dyadicSiftConcrete`, `paper.tex` §4.2) with `ApproxGridNorm`
instantiated via `concreteApproxGridNormV S`. -/
noncomputable def dyadicSiftConcrete (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (ε : ℝ) (d : ℕ) (S : TwoStageSamplerOracle β ε) : String × Finset α × Finset β × ℕ :=
  dyadicSift X Y A ε d (concreteApproxGridNormV S X Y A d)

/-- Cost-tracked Concrete Algorithm 3 (`dyadicSiftConcreteTracked`) in `CostM`. -/
noncomputable def dyadicSiftConcreteTracked (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (ε : ℝ) (d : ℕ) (S : TwoStageSamplerOracle β ε) :
    CostM (String × Finset α × Finset β × ℕ) :=
  dyadicSiftTracked X Y A ε d (concreteApproxGridNormVTracked S X Y A d)

@[simp]
theorem dyadicSiftConcreteTracked_fst (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (ε : ℝ) (d : ℕ) (S : TwoStageSamplerOracle β ε) :
    (dyadicSiftConcreteTracked X Y A ε d S).1 = dyadicSiftConcrete X Y A ε d S := by
  unfold dyadicSiftConcreteTracked dyadicSiftConcrete
  rw [dyadicSiftTracked_fst, concreteApproxGridNormVTracked_fst]

theorem dyadicSiftConcreteTracked_snd_le (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (ε : ℝ) (d : ℕ) (S : TwoStageSamplerOracle β ε) :
    (dyadicSiftConcreteTracked X Y A ε d S).2 ≤
      (X.card + Y.card + 2) ^ 2 * (concreteApproxGridNormCostFactor S.c S.k ε d + 2 * (d + 1)) := by
  unfold dyadicSiftConcreteTracked
  have h1 := dyadicSiftTracked_snd_le X Y A ε d (concreteApproxGridNormVTracked S X Y A d)
  have hV := concreteApproxGridNormVTracked_snd_le S X Y A d
  exact (h1.trans hV).trans (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))

/-- **Lemma 4.2 (`lem_dyadic_sift_concrete`, `paper.tex` §4.2)**:
Full specification of `dyadicSiftConcrete` parameterized by `S : TwoStageSamplerOracle β ε`. -/
theorem lem_dyadic_sift_concrete
    {X : Finset α} {Y : Finset β} {A : α → β → ℝ} {ε : ℝ} {d : ℕ}
    (S : TwoStageSamplerOracle β ε)
    (hX : X.Nonempty) (hY : Y.Nonempty) (hA : IsBinaryMatrix X Y A)
    (hε_pos : 0 < ε) (hε_lt : ε < 1) (hd : 2 ≤ d)
    (hδ_gt : 1 < (2 : ℝ) ^ d * ((1 + ε / 2) * matDensity X Y A)) :
    let res := dyadicSiftConcrete X Y A ε d S
    let tag := res.1
    let X' := res.2.1
    let Y' := res.2.2.1
    let s := res.2.2.2
    (tag = "subrect" ∨ tag = "regular") ∧
    (tag = "subrect" →
      s < d ∧
      X' ⊆ X ∧
      Y' ⊆ Y ∧
      X'.Nonempty ∧
      Y'.Nonempty ∧
      (2 : ℝ) ^ s * (1 + ε / 2) * matDensity X Y A ≤ matDensity X' Y' A ∧
      (ε / 16) * (((2 : ℝ) ^ ((s + 2) * d))⁻¹) * (X.card : ℝ) ≤ (X'.card : ℝ) ∧
      ((1 + ε / 2) * matDensity X Y A) ^ 2 * (Y.card : ℝ) ≤ (Y'.card : ℝ) ∧
      (((2 : ℝ) ^ (2 * d))⁻¹) * (Y.card : ℝ) < (Y'.card : ℝ)) ∧
    (tag = "regular" →
      X' = X ∧ Y' = Y ∧ s = 0 ∧
      IsGridRegular2Pow X Y A ε d ∧ IsGridRegular X Y A ε 2 d) := by
  exact lem_dyadic_sift hX hY hA hε_pos hε_lt hd hδ_gt
    (concreteApproxGridNormV_approx S hX hA (le_of_lt hε_pos) (by omega) hδ_gt)

/-- Concrete Algorithm 2 (`ApproxGridNorm`) vector $V : \alpha \to \mathbb{R}$ instantiated with
the Chebyshev $k$-tuple oblivious sampler `constructChebyshevTupleSampler Y invEps invDelta`
(whose sample tuple size `chebyshevSampleSize invEps invDelta = (invEps + 1)^2 * (invDelta + 1)`
is independent of $|Y|$, while its family size is $|\Omega| = |Y|^k$; correctness-only reference
instantiation with no running-time clause). -/
noncomputable def concreteApproxGridNormVChebyshev (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (invEps invDelta d : ℕ) : α → ℝ :=
  fun x => approxGridNormVTuple X Y
    (chebyshevSampleSize invEps invDelta)
    (constructChebyshevTupleSampler Y invEps invDelta)
    (restrictBinaryMat X Y A) d x

/-- **Chebyshev Tuple-Sampler Accuracy Guarantee for `concreteApproxGridNormVChebyshev`
(correctness only; $|\Omega| = |Y|^k$; no running-time clause)**:
For any binary matrix $A$ on $X \times Y$, $\varepsilon \ge 0$, $d \ge 1$, and integer inverse
error bounds `invEps invDelta : ℕ` satisfying
$\frac{1}{\text{invEps} + 1} \le \frac{\alpha_{\text{grid}}}{2}$ and
$\frac{1}{\text{invDelta} + 1} \le \left(\frac{\alpha_{\text{grid}}}{2}\right)^d$
(where $\alpha_{\text{grid}} = \varepsilon \delta^3 / 32$ and $\delta = (1 + \varepsilon / 2) \mu$),
`concreteApproxGridNormVChebyshev X Y A invEps invDelta d` satisfies the non-negativity and
approximation bounds required by Algorithm 3 (`DyadicSift`). -/
theorem concreteApproxGridNormVChebyshev_approx
    {X : Finset α} {Y : Finset β} {A : α → β → ℝ} {ε : ℝ} {invEps invDelta d : ℕ}
    (hX : X.Nonempty) (hY : Y.Nonempty) (hA : IsBinaryMatrix X Y A)
    (hε : 0 ≤ ε) (hd : 1 ≤ d)
    (h_invEps : (1 : ℝ) / ((invEps : ℝ) + 1) ≤
      (ε * ((1 + ε / 2) * matDensity X Y A) ^ 3 / 32) / 2)
    (h_invDelta : (1 : ℝ) / ((invDelta : ℝ) + 1) ≤
      ((ε * ((1 + ε / 2) * matDensity X Y A) ^ 3 / 32) / 2) ^ d) :
    ∀ x ∈ X, 0 < rowDeg Y A x →
      0 ≤ concreteApproxGridNormVChebyshev X Y A invEps invDelta d x ∧
      |(concreteApproxGridNormVChebyshev X Y A invEps invDelta d x) ^ ((1 : ℝ) / (d : ℝ)) -
        gridNorm X (rowSupport Y A x) A 1 d| ≤
        (ε * ((1 + ε / 2) * matDensity X Y A) ^ 3 / 32) / rowDeg Y A x := by
  intro x hx hdeg
  set δ := (1 + ε / 2) * matDensity X Y A
  set α_grid := ε * δ ^ 3 / 32
  have hμ_nonneg : 0 ≤ matDensity X Y A := matDensity_nonneg_of_unitInterval hA.to_unitInterval
  have hδ_nonneg : 0 ≤ δ := by positivity
  have hα_nonneg : 0 ≤ α_grid := by positivity
  have hM : IsBinaryRealMat (restrictBinaryMat X Y A) :=
    isBinaryRealMat_restrictBinaryMat X Y A
  have hdegM : 0 < rowDeg Y (restrictBinaryMat X Y A) x := by
    rwa [rowDeg_restrictBinaryMat_eq hA (Finset.Subset.refl Y) hx]
  have hlem := lem_approx_grid_norm_chebyshev_tuple hX hY invEps invDelta hα_nonneg hd
    h_invEps h_invDelta hM hdegM
  rw [rowDeg_restrictBinaryMat_eq hA (Finset.Subset.refl Y) hx,
    realRowNbr_restrictBinaryMat_eq_rowSupport hA hx,
    gridNorm1_restrictBinaryMat_eq_gridNorm hA (rowSupport_subset Y A x) d] at hlem
  exact hlem

/-- Concrete Algorithm 3 (`dyadicSiftChebyshev`, `paper.tex` §4.2) with `ApproxGridNorm`
instantiated via the Chebyshev $k$-tuple oblivious sampler `concreteApproxGridNormVChebyshev`
(correctness-only reference instantiation; $|\Omega| = |Y|^k$; no running-time clause). -/
noncomputable def dyadicSiftChebyshev (X : Finset α) (Y : Finset β) (A : α → β → ℝ)
    (ε : ℝ) (invEps invDelta d : ℕ) : String × Finset α × Finset β × ℕ :=
  dyadicSift X Y A ε d (concreteApproxGridNormVChebyshev X Y A invEps invDelta d)

/-- **Lemma 4.2 Correctness Instantiation via Chebyshev $k$-Tuple Sampler (`lem_dyadic_sift_chebyshev`,
correctness only; $|\Omega| = |Y|^k$; no running-time clause)**:
Full correctness specification of `dyadicSiftChebyshev` using `constructChebyshevTupleSampler`
(where sample tuple size `chebyshevSampleSize invEps invDelta = (invEps + 1)^2 * (invDelta + 1)` is
independent of $|Y|$, while the exhaustive family has $|\Omega| = |Y|^k$ tuples; the linear-in-$|Y|$
two-stage sampler with `CostM` running-time bound is given by `lem_dyadic_sift_concrete`). -/
theorem lem_dyadic_sift_chebyshev
    {X : Finset α} {Y : Finset β} {A : α → β → ℝ} {ε : ℝ} {invEps invDelta d : ℕ}
    (hX : X.Nonempty) (hY : Y.Nonempty) (hA : IsBinaryMatrix X Y A)
    (hε_pos : 0 < ε) (hε_lt : ε < 1) (hd : 2 ≤ d)
    (hδ_gt : 1 < (2 : ℝ) ^ d * ((1 + ε / 2) * matDensity X Y A))
    (h_invEps : (1 : ℝ) / ((invEps : ℝ) + 1) ≤
      (ε * ((1 + ε / 2) * matDensity X Y A) ^ 3 / 32) / 2)
    (h_invDelta : (1 : ℝ) / ((invDelta : ℝ) + 1) ≤
      ((ε * ((1 + ε / 2) * matDensity X Y A) ^ 3 / 32) / 2) ^ d) :
    let res := dyadicSiftChebyshev X Y A ε invEps invDelta d
    let tag := res.1
    let X' := res.2.1
    let Y' := res.2.2.1
    let s := res.2.2.2
    (tag = "subrect" ∨ tag = "regular") ∧
    (tag = "subrect" →
      s < d ∧
      X' ⊆ X ∧
      Y' ⊆ Y ∧
      X'.Nonempty ∧
      Y'.Nonempty ∧
      (2 : ℝ) ^ s * (1 + ε / 2) * matDensity X Y A ≤ matDensity X' Y' A ∧
      (ε / 16) * (((2 : ℝ) ^ ((s + 2) * d))⁻¹) * (X.card : ℝ) ≤ (X'.card : ℝ) ∧
      ((1 + ε / 2) * matDensity X Y A) ^ 2 * (Y.card : ℝ) ≤ (Y'.card : ℝ) ∧
      (((2 : ℝ) ^ (2 * d))⁻¹) * (Y.card : ℝ) < (Y'.card : ℝ)) ∧
    (tag = "regular" →
      X' = X ∧ Y' = Y ∧ s = 0 ∧
      IsGridRegular2Pow X Y A ε d ∧ IsGridRegular X Y A ε 2 d) := by
  exact lem_dyadic_sift hX hY hA hε_pos hε_lt hd hδ_gt
    (concreteApproxGridNormVChebyshev_approx hX hY hA (le_of_lt hε_pos) (by omega)
      h_invEps h_invDelta)

end DyadicSift

end BMMGrid
