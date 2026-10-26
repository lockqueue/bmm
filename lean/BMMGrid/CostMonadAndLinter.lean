import BMMGrid.Defs
import Lean

/-!
# Intrinsic Cost Monad (`CostM`) & Compile-Time AST / Axiom Auditors (`BMMGrid/CostMonadAndLinter.lean`)

This module implements:
1. The bottom-up cost-accounting monad `CostM α := α × ℕ`.
2. Bit-length and multi-precision integer / rational cross-multiplication primitives
   (`bitLengthNat`, `addNatTracked`, `subNatTracked`, `mulNatTracked`, `divNatTracked`,
   `modNatTracked`, `cmpLeNatTracked`, `cmpLtNatTracked`, `powNatTracked`, `log2NatTracked`,
   `sqrtNatTracked`, `cmpRatCrossLeTracked`, `cmpRatCrossLtTracked`) where every operation
   charges its Cook–Reckhow (1973) logarithmic bit-operation cost (which strictly dominates
   Unit-Cost Word RAM steps `1 ≤ bitLengthNat`).
3. Tracked list and finite-set iteration combinators (`foldlListTracked`, `filterListByTracked`,
   `retTracked`, `findSomeListTracked`, `findSomeListByTracked`, `appendListTracked`,
   `mapListTracked`, `flatMapListTracked`, `repeatStepsTracked`, `repeatGridStepsTracked`,
   `scanFinsetTracked`, `scanMatrixTracked`, `scanMatrixPairTracked`, `scanBlockExtractTracked`,
   `sumFinsetTracked`, `tabulateFinsetTracked`, `filterFinsetByTracked`,
   `evalSupportScanTracked`, `evalMinNbrScanTracked`).
4. Compile-time metaprogramming verification commands:
   - `#verify_standard_axioms <decl>`,
   - `#verify_no_escape_hatches`,
   - `#verify_tracked_declarations_ast_audit`,
   - `#verify_headline_cone_excludes`,
   - `#verify_no_unused_decls`.
-/

namespace BMMGrid

/-- Bottom-up cost-accounting monad `CostM α := α × ℕ`.
The first projection `.1` is the pure mathematical value, and `.2` is the accumulated
bottom-up operation / Cook–Reckhow bit-complexity count. -/
abbrev CostM (α : Type*) := α × ℕ

namespace CostM

variable {α β : Type*}

@[inline]
def pure (x : α) : CostM α := (x, 0)

@[inline]
def tick (c : ℕ) : CostM PUnit := (PUnit.unit, c)

@[inline]
def withCost (x : α) (c : ℕ) : CostM α := (x, c)

@[inline]
def bind (m : CostM α) (f : α → CostM β) : CostM β :=
  let r := f m.1
  (r.1, m.2 + r.2)

@[simp]
lemma bind_fst (m : CostM α) (f : α → CostM β) : (bind m f).1 = (f m.1).1 := rfl

@[simp]
lemma bind_snd (m : CostM α) (f : α → CostM β) : (bind m f).2 = m.2 + (f m.1).2 := rfl

end CostM

/-!
## Logarithmic Bit-Length & Multi-Precision Arithmetic Primitives
-/

/-- Cook–Reckhow (1973) logarithmic bit-length of a natural number:
$\operatorname{bitlen}(v) = \lfloor \log_2(\max(1, v)) \rfloor + 1 \ge 1$. -/
def bitLengthNat (v : ℕ) : ℕ :=
  Nat.log 2 v + 1

lemma one_le_bitLengthNat (v : ℕ) : 1 ≤ bitLengthNat v :=
  Nat.succ_le_succ (Nat.zero_le _)

lemma bitLengthNat_mono {u v : ℕ} (h : u ≤ v) : bitLengthNat u ≤ bitLengthNat v :=
  Nat.add_le_add_right (Nat.log_mono_right h) 1

/-- Tracked natural-number addition charging $\operatorname{bitlen}(a) + \operatorname{bitlen}(b) + 1$
bit operations. -/
def addNatTracked (a b : ℕ) : CostM ℕ :=
  (a + b, bitLengthNat a + bitLengthNat b + 1)

lemma addNatTracked_fst (a b : ℕ) : (addNatTracked a b).1 = a + b := rfl

lemma addNatTracked_snd (a b : ℕ) :
    (addNatTracked a b).2 = bitLengthNat a + bitLengthNat b + 1 := rfl

/-- Tracked natural-number subtraction charging $\operatorname{bitlen}(a) + \operatorname{bitlen}(b) + 1$
bit operations. -/
def subNatTracked (a b : ℕ) : CostM ℕ :=
  (a - b, bitLengthNat a + bitLengthNat b + 1)

lemma subNatTracked_fst (a b : ℕ) : (subNatTracked a b).1 = a - b := rfl

lemma subNatTracked_snd (a b : ℕ) :
    (subNatTracked a b).2 = bitLengthNat a + bitLengthNat b + 1 := rfl

/-- Tracked natural-number multiplication charging $\operatorname{bitlen}(a) \cdot \operatorname{bitlen}(b) + 1$
bit operations (schoolbook / restoring word-level log-cost bound). -/
def mulNatTracked (a b : ℕ) : CostM ℕ :=
  (a * b, bitLengthNat a * bitLengthNat b + 1)

lemma mulNatTracked_fst (a b : ℕ) : (mulNatTracked a b).1 = a * b := rfl

lemma mulNatTracked_snd (a b : ℕ) :
    (mulNatTracked a b).2 = bitLengthNat a * bitLengthNat b + 1 := rfl

/-- Tracked natural-number division charging $\operatorname{bitlen}(a) \cdot \operatorname{bitlen}(b) + 1$
bit operations. -/
def divNatTracked (a b : ℕ) : CostM ℕ :=
  (a / b, bitLengthNat a * bitLengthNat b + 1)

lemma divNatTracked_fst (a b : ℕ) : (divNatTracked a b).1 = a / b := rfl

lemma divNatTracked_snd (a b : ℕ) :
    (divNatTracked a b).2 = bitLengthNat a * bitLengthNat b + 1 := rfl

/-- Tracked natural-number modulo `a % b` charging $\operatorname{bitlen}(a) \cdot \operatorname{bitlen}(b) + 1$
bit operations. -/
def modNatTracked (a b : ℕ) : CostM ℕ :=
  (a % b, bitLengthNat a * bitLengthNat b + 1)

@[simp]
lemma modNatTracked_fst (a b : ℕ) : (modNatTracked a b).1 = a % b := rfl

lemma modNatTracked_snd (a b : ℕ) :
    (modNatTracked a b).2 = bitLengthNat a * bitLengthNat b + 1 := rfl

/-- Tracked natural-number comparison `a ≤ b` charging $\operatorname{bitlen}(a) + \operatorname{bitlen}(b) + 1$
bit operations. -/
def cmpLeNatTracked (a b : ℕ) : CostM Bool :=
  (decide (a ≤ b), bitLengthNat a + bitLengthNat b + 1)

lemma cmpLeNatTracked_fst (a b : ℕ) : (cmpLeNatTracked a b).1 = decide (a ≤ b) := rfl

lemma cmpLeNatTracked_snd (a b : ℕ) :
    (cmpLeNatTracked a b).2 = bitLengthNat a + bitLengthNat b + 1 := rfl

/-- Tracked natural-number strict comparison `a < b` charging
$\operatorname{bitlen}(a) + \operatorname{bitlen}(b) + 1$ bit operations. -/
def cmpLtNatTracked (a b : ℕ) : CostM Bool :=
  (decide (a < b), bitLengthNat a + bitLengthNat b + 1)

lemma cmpLtNatTracked_fst (a b : ℕ) : (cmpLtNatTracked a b).1 = decide (a < b) := rfl

lemma cmpLtNatTracked_snd (a b : ℕ) :
    (cmpLtNatTracked a b).2 = bitLengthNat a + bitLengthNat b + 1 := rfl

/-- Tracked exact integer power `a ^ d` charging $(d + 1) \cdot (d \cdot \operatorname{bitlen}(a) + 1)^2$
bit operations (covering $d$-fold multiplication of $O(d \log a)$-bit integers in `ApproxGridNorm`). -/
def powNatTracked (a d : ℕ) : CostM ℕ :=
  (a ^ d, (d + 1) * (d * bitLengthNat a + 1) * (d * bitLengthNat a + 1))

lemma powNatTracked_fst (a d : ℕ) : (powNatTracked a d).1 = a ^ d := rfl

lemma powNatTracked_snd (a d : ℕ) :
    (powNatTracked a d).2 = (d + 1) * (d * bitLengthNat a + 1) * (d * bitLengthNat a + 1) := rfl

lemma powNatTracked_snd_mono {a₁ a₂ d₁ d₂ : ℕ} (ha : a₁ ≤ a₂) (hd : d₁ ≤ d₂) :
    (powNatTracked a₁ d₁).2 ≤ (powNatTracked a₂ d₂).2 := by
  dsimp [powNatTracked]
  have hb : bitLengthNat a₁ ≤ bitLengthNat a₂ := bitLengthNat_mono ha
  have h1 : d₁ * bitLengthNat a₁ + 1 ≤ d₂ * bitLengthNat a₂ + 1 :=
    Nat.add_le_add_right (Nat.mul_le_mul hd hb) 1
  exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.add_le_add_right hd 1) h1) h1

private lemma nat_add_one_sq_le_four_mul_two_pow : ∀ k : ℕ, (k + 1) ^ 2 ≤ 4 * 2 ^ k
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | m + 3 => by
    have ih := nat_add_one_sq_le_four_mul_two_pow (m + 2)
    have hsq : 2 * (m + 2 + 1) ^ 2 = (m + 3 + 1) ^ 2 + (m ^ 2 + 4 * m + 2) := by ring
    have hpow : 4 * 2 ^ (m + 3) = 2 * (4 * 2 ^ (m + 2)) := by
      rw [Nat.pow_succ]; ring
    omega

lemma bitLengthNat_sq_le (v : ℕ) : bitLengthNat v ^ 2 ≤ 4 * v + 1 := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · decide
  · have h1 := nat_add_one_sq_le_four_mul_two_pow (Nat.log 2 v)
    have h2 : 2 ^ Nat.log 2 v ≤ v := Nat.pow_log_le_self 2 hv.ne'
    have h3 : bitLengthNat v ^ 2 = (Nat.log 2 v + 1) ^ 2 := rfl
    omega

lemma powNatTracked_snd_le_linear (a d : ℕ) :
    (powNatTracked a d).2 ≤ (d + 1) ^ 3 * (4 * a + 1) := by
  have hb1 : 1 ≤ bitLengthNat a := one_le_bitLengthNat a
  have h1 : d * bitLengthNat a + 1 ≤ (d + 1) * bitLengthNat a := by nlinarith
  have hsq :
      (d * bitLengthNat a + 1) * (d * bitLengthNat a + 1) ≤
        (d + 1) ^ 2 * bitLengthNat a ^ 2 := by
    calc
      (d * bitLengthNat a + 1) * (d * bitLengthNat a + 1)
        ≤ ((d + 1) * bitLengthNat a) * ((d + 1) * bitLengthNat a) := Nat.mul_le_mul h1 h1
      _ = (d + 1) ^ 2 * bitLengthNat a ^ 2 := by ring
  calc
    (powNatTracked a d).2
      = (d + 1) * ((d * bitLengthNat a + 1) * (d * bitLengthNat a + 1)) := by
          dsimp [powNatTracked]; ring
    _ ≤ (d + 1) * ((d + 1) ^ 2 * bitLengthNat a ^ 2) := Nat.mul_le_mul_left _ hsq
    _ = (d + 1) ^ 3 * bitLengthNat a ^ 2 := by ring
    _ ≤ (d + 1) ^ 3 * (4 * a + 1) := Nat.mul_le_mul_left _ (bitLengthNat_sq_le a)

lemma bitLengthNat_mul_le (a b : ℕ) :
    bitLengthNat (a * b) ≤ bitLengthNat a + bitLengthNat b := by
  have h0 : bitLengthNat 0 = 1 := by decide
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have hb : 1 ≤ bitLengthNat b := one_le_bitLengthNat b
    simp only [zero_mul, h0]
    omega
  · rcases Nat.eq_zero_or_pos b with rfl | hb
    · have ha1 : 1 ≤ bitLengthNat a := one_le_bitLengthNat a
      simp only [mul_zero, h0]
      omega
    · have ha_lt : a < 2 ^ bitLengthNat a :=
        Nat.lt_pow_succ_log_self (by norm_num) a
      have hb_lt : b < 2 ^ bitLengthNat b :=
        Nat.lt_pow_succ_log_self (by norm_num) b
      have hab_lt : a * b < 2 ^ (bitLengthNat a + bitLengthNat b) := by
        rw [Nat.pow_add]
        exact Nat.mul_lt_mul'' ha_lt hb_lt
      have hlog_lt : Nat.log 2 (a * b) < bitLengthNat a + bitLengthNat b :=
        (Nat.log_lt_iff_lt_pow (by norm_num) (Nat.mul_pos ha hb).ne').mpr hab_lt
      change Nat.log 2 (a * b) + 1 ≤ bitLengthNat a + bitLengthNat b
      omega

lemma bitLengthNat_pow_le (a d : ℕ) :
    bitLengthNat (a ^ d) ≤ d * bitLengthNat a + 1 := by
  induction d with
  | zero =>
    simp [bitLengthNat]
  | succ k ih =>
    rw [Nat.pow_succ]
    calc
      bitLengthNat (a ^ k * a)
        ≤ bitLengthNat (a ^ k) + bitLengthNat a := bitLengthNat_mul_le (a ^ k) a
      _ ≤ (k * bitLengthNat a + 1) + bitLengthNat a := Nat.add_le_add_right ih _
      _ = (k + 1) * bitLengthNat a + 1 := by ring

lemma mulNatTracked_snd_le_of_bitLength_le {u v M : ℕ}
    (hu : bitLengthNat u ≤ M) (hv : bitLengthNat v ≤ M) :
    (mulNatTracked u v).2 ≤ M ^ 2 + 1 := by
  unfold mulNatTracked
  rw [sq]
  exact Nat.add_le_add_right (Nat.mul_le_mul hu hv) 1

lemma five_term_sq_bound (L Xc Yc B : ℕ) :
    (bitLengthNat L + bitLengthNat Xc + bitLengthNat Yc + bitLengthNat B + 1) ^ 2 ≤
      20 * (L + Xc + Yc + B) + 25 := by
  have h5 : ∀ a b c e : ℕ,
      (a + b + c + e + 1) ^ 2 ≤ 5 * (a ^ 2 + b ^ 2 + c ^ 2 + e ^ 2 + 1) := by
    intro a b c e
    zify
    nlinarith [sq_nonneg ((a : ℤ) - b), sq_nonneg ((a : ℤ) - c), sq_nonneg ((a : ℤ) - e),
      sq_nonneg ((a : ℤ) - 1), sq_nonneg ((b : ℤ) - c), sq_nonneg ((b : ℤ) - e),
      sq_nonneg ((b : ℤ) - 1), sq_nonneg ((c : ℤ) - e), sq_nonneg ((c : ℤ) - 1),
      sq_nonneg ((e : ℤ) - 1)]
  have hL := bitLengthNat_sq_le L
  have hX := bitLengthNat_sq_le Xc
  have hY := bitLengthNat_sq_le Yc
  have hB := bitLengthNat_sq_le B
  have hstep := h5 (bitLengthNat L) (bitLengthNat Xc) (bitLengthNat Yc) (bitLengthNat B)
  omega

/-- Tracked integer base-2 logarithm $\lfloor \log_2 a \rfloor$ charging $\operatorname{bitlen}(a) + 1$
bit operations. -/
def log2NatTracked (a : ℕ) : CostM ℕ :=
  (Nat.log 2 a, bitLengthNat a + 1)

@[simp]
lemma log2NatTracked_fst (a : ℕ) : (log2NatTracked a).1 = Nat.log 2 a := rfl

@[simp]
lemma log2NatTracked_snd (a : ℕ) : (log2NatTracked a).2 = bitLengthNat a + 1 := rfl

/-- Tracked integer square root $\lfloor \sqrt{a} \rfloor$ charging $(\operatorname{bitlen}(a) + 1)^2$
bit operations. -/
def sqrtNatTracked (a : ℕ) : CostM ℕ :=
  (Nat.sqrt a, (bitLengthNat a + 1) * (bitLengthNat a + 1))

@[simp]
lemma sqrtNatTracked_fst (a : ℕ) : (sqrtNatTracked a).1 = Nat.sqrt a := rfl

@[simp]
lemma sqrtNatTracked_snd (a : ℕ) :
    (sqrtNatTracked a).2 = (bitLengthNat a + 1) * (bitLengthNat a + 1) := rfl

/-- Tracked exact cross-multiplied rational comparison $p_1 / q_1 \le p_2 / q_2$
(for $q_1, q_2 > 0$) via $p_1 \cdot q_2 \le p_2 \cdot q_1$, avoiding dynamic `ℚ` GCD/LCM reduction. -/
def cmpRatCrossLeTracked (p₁ q₁ p₂ q₂ : ℕ) : CostM Bool :=
  CostM.bind (mulNatTracked p₁ q₂) (fun lhs =>
    CostM.bind (mulNatTracked p₂ q₁) (fun rhs =>
      cmpLeNatTracked lhs rhs))

/-- Tracked exact cross-multiplied strict rational comparison $p_1 / q_1 < p_2 / q_2$
(for $q_1, q_2 > 0$) via $p_1 \cdot q_2 < p_2 \cdot q_1$. -/
def cmpRatCrossLtTracked (p₁ q₁ p₂ q₂ : ℕ) : CostM Bool :=
  CostM.bind (mulNatTracked p₁ q₂) (fun lhs =>
    CostM.bind (mulNatTracked p₂ q₁) (fun rhs =>
      cmpLtNatTracked lhs rhs))

@[simp]
lemma cmpRatCrossLeTracked_fst (p₁ q₁ p₂ q₂ : ℕ) :
    (cmpRatCrossLeTracked p₁ q₁ p₂ q₂).1 = decide (p₁ * q₂ ≤ p₂ * q₁) := rfl

lemma cmpRatCrossLeTracked_snd (p₁ q₁ p₂ q₂ : ℕ) :
    (cmpRatCrossLeTracked p₁ q₁ p₂ q₂).2 =
      (mulNatTracked p₁ q₂).2 + ((mulNatTracked p₂ q₁).2 + (cmpLeNatTracked (p₁ * q₂) (p₂ * q₁)).2) := rfl

@[simp]
lemma cmpRatCrossLtTracked_fst (p₁ q₁ p₂ q₂ : ℕ) :
    (cmpRatCrossLtTracked p₁ q₁ p₂ q₂).1 = decide (p₁ * q₂ < p₂ * q₁) := rfl

lemma cmpRatCrossLtTracked_snd (p₁ q₁ p₂ q₂ : ℕ) :
    (cmpRatCrossLtTracked p₁ q₁ p₂ q₂).2 =
      (mulNatTracked p₁ q₂).2 + ((mulNatTracked p₂ q₁).2 + (cmpLtNatTracked (p₁ * q₂) (p₂ * q₁)).2) := rfl

/-!
## Tracked Iteration Combinators
-/

/-- Tracked fold over a list `xs : List α`, charging `1` step per cons cell plus the step cost of
`f` plus `1` on the empty list (`xs.length * (c + 1) + 1` when each step costs `c`). -/
def foldlListTracked {α β : Type*} (f : β → α → CostM β) (init : β) : List α → CostM β
  | [] => (init, 1)
  | x :: xs =>
    let step := f init x
    let rest := foldlListTracked f step.1 xs
    (rest.1, step.2 + rest.2 + 1)

@[simp]
lemma foldlListTracked_fst {α β : Type*} (f : β → α → CostM β) (init : β) (xs : List α) :
    (foldlListTracked f init xs).1 = xs.foldl (fun acc x => (f acc x).1) init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simp only [foldlListTracked, List.foldl_cons]
    exact ih (f init x).1

lemma foldlListTracked_snd_const {α β : Type*} (f : β → α → CostM β) (c : ℕ) (init : β)
    (xs : List α) (hf : ∀ acc, ∀ x ∈ xs, (f acc x).2 = c) :
    (foldlListTracked f init xs).2 = xs.length * (c + 1) + 1 := by
  induction xs generalizing init with
  | nil => simp [foldlListTracked]
  | cons x xs ih =>
    simp only [foldlListTracked, List.length_cons]
    rw [hf init x List.mem_cons_self,
      ih (f init x).1 (fun acc y hy => hf acc y (List.mem_cons_of_mem x hy))]
    ring

lemma foldlListTracked_snd_le_const {α β : Type*} (f : β → α → CostM β) (c : ℕ) (init : β)
    (xs : List α) (hf : ∀ acc, ∀ x ∈ xs, (f acc x).2 ≤ c) :
    (foldlListTracked f init xs).2 ≤ xs.length * (c + 1) + 1 := by
  induction xs generalizing init with
  | nil => simp [foldlListTracked]
  | cons x xs ih =>
    simp only [foldlListTracked, List.length_cons]
    have h1 : (f init x).2 ≤ c := hf init x List.mem_cons_self
    have h2 := ih (f init x).1 (fun acc y hy => hf acc y (List.mem_cons_of_mem x hy))
    calc
      (f init x).2 + (foldlListTracked f (f init x).1 xs).2 + 1
        ≤ c + (xs.length * (c + 1) + 1) + 1 := by omega
      _ = (xs.length + 1) * (c + 1) + 1 := by ring

/-- Tracked filter over a list `xs : List α` by a predicate `p : α → Bool`, charging `1` step per
cons cell plus `1` on the empty list (`xs.length + 1`). -/
def filterListByTracked {α : Type*} (p : α → Bool) : List α → CostM (List α)
  | [] => ([], 1)
  | x :: xs =>
    let rest := filterListByTracked p xs
    (if p x then x :: rest.1 else rest.1, rest.2 + 1)

@[simp]
lemma filterListByTracked_fst {α : Type*} (p : α → Bool) (xs : List α) :
    (filterListByTracked p xs).1 = xs.filter p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [filterListByTracked, List.filter_cons, ih]

@[simp]
lemma filterListByTracked_snd {α : Type*} (p : α → Bool) (xs : List α) :
    (filterListByTracked p xs).2 = xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [filterListByTracked, List.length_cons, ih]

/-- Tracked unit-cost return step `(x, 1)` in `CostM`. -/
@[inline]
def retTracked {α : Type*} (x : α) : CostM α :=
  (x, 1)

@[simp]
lemma retTracked_fst {α : Type*} (x : α) : (retTracked x).1 = x := rfl

@[simp]
lemma retTracked_snd {α : Type*} (x : α) : (retTracked x).2 = 1 := rfl

/-- Tracked `findSome?` over a list `xs : List α`, charging `1` step per element examined plus
`f x` (and `1` on `[]`, so at most `(c + 1) * xs.length + 1` when `(f x).2 ≤ c`). -/
def findSomeListTracked {α β : Type*} (f : α → CostM (Option β)) : List α → CostM (Option β)
  | [] => (none, 1)
  | x :: xs =>
    let fx := f x
    match fx.1 with
    | some b => (some b, fx.2 + 1)
    | none =>
      let rest := findSomeListTracked f xs
      (rest.1, fx.2 + rest.2 + 1)

@[simp]
lemma findSomeListTracked_fst {α β : Type*} (f : α → CostM (Option β)) (xs : List α) :
    (findSomeListTracked f xs).1 = xs.findSome? (fun x => (f x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [findSomeListTracked, List.findSome?_cons]
    cases h : (f x).1 <;> simp [ih]

lemma findSomeListTracked_snd_le_of_const {α β : Type*}
    (f : α → CostM (Option β)) (c : ℕ) (xs : List α)
    (hc : ∀ x ∈ xs, (f x).2 ≤ c) :
    (findSomeListTracked f xs).2 ≤ (c + 1) * xs.length + 1 := by
  induction xs with
  | nil => simp [findSomeListTracked]
  | cons x xs ih =>
    simp only [findSomeListTracked, List.length_cons]
    have hx : (f x).2 ≤ c := hc x List.mem_cons_self
    have hxs : ∀ y ∈ xs, (f y).2 ≤ c := fun y hy => hc y (List.mem_cons_of_mem x hy)
    cases h : (f x).1 with
    | some b =>
      dsimp only
      calc
        (f x).2 + 1 ≤ c + 1 := Nat.add_le_add_right hx 1
        _ ≤ (c + 1) * (xs.length + 1) + 1 := by
          rw [Nat.mul_add, Nat.mul_one]
          omega
    | none =>
      dsimp only
      have hrec := ih hxs
      calc
        (f x).2 + (findSomeListTracked f xs).2 + 1
          ≤ c + ((c + 1) * xs.length + 1) + 1 := by omega
        _ = (c + 1) * (xs.length + 1) + 1 := by ring

/-- Tracked `findSome?` over a list `xs : List α` by `f : α → Option β`, charging `1` step per
element examined (and `1` on `[]`, so at most `xs.length + 1`). -/
def findSomeListByTracked {α β : Type*} (f : α → Option β) : List α → CostM (Option β)
  | [] => (none, 1)
  | x :: xs =>
    match f x with
    | some b => (some b, 1)
    | none =>
      let rest := findSomeListByTracked f xs
      (rest.1, rest.2 + 1)

@[simp]
lemma findSomeListByTracked_fst {α β : Type*} (f : α → Option β) (xs : List α) :
    (findSomeListByTracked f xs).1 = xs.findSome? f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [findSomeListByTracked, List.findSome?_cons]
    cases h : f x <;> simp [ih]

lemma findSomeListByTracked_snd_le {α β : Type*} (f : α → Option β) (xs : List α) :
    (findSomeListByTracked f xs).2 ≤ xs.length + 1 := by
  induction xs with
  | nil => simp [findSomeListByTracked]
  | cons x xs ih =>
    simp only [findSomeListByTracked, List.length_cons]
    cases h : f x with
    | some b =>
      dsimp only
      omega
    | none =>
      dsimp only
      omega

/-- Tracked list append `xs ++ ys`, iterating through `xs` and charging `1` per cons cell plus `1`
on the empty list (`xs.length + 1`). -/
def appendListTracked {α : Type*} : List α → List α → CostM (List α)
  | [], ys => (ys, 1)
  | x :: xs, ys =>
    let rest := appendListTracked xs ys
    (x :: rest.1, rest.2 + 1)

@[simp]
lemma appendListTracked_fst {α : Type*} (xs ys : List α) :
    (appendListTracked xs ys).1 = xs ++ ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [appendListTracked, List.cons_append, ih]

@[simp]
lemma appendListTracked_snd {α : Type*} (xs ys : List α) :
    (appendListTracked xs ys).2 = xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [appendListTracked, List.length_cons, ih]

/-- Cost-tracked list map in `CostM`, preserving list order and charging `xs.length * (c + 1) + 1`
when each element callback costs `c`. -/
def mapListTracked {γ δ : Type*} (f : γ → CostM δ) : List γ → CostM (List δ)
  | [] => retTracked []
  | x :: xs =>
    CostM.bind (f x) (fun y =>
      CostM.bind (mapListTracked f xs) (fun ys =>
        retTracked (y :: ys)))

@[simp]
lemma mapListTracked_fst {γ δ : Type*} (f : γ → CostM δ) (xs : List γ) :
    (mapListTracked f xs).1 = xs.map (fun x => (f x).1) := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    simp [mapListTracked, CostM.bind, retTracked, ih]

lemma mapListTracked_snd_const {γ δ : Type*} (f : γ → CostM δ) (c : ℕ) (xs : List γ)
    (hf : ∀ x ∈ xs, (f x).2 = c) :
    (mapListTracked f xs).2 = xs.length * (c + 1) + 1 := by
  induction xs with
  | nil => simp [mapListTracked]
  | cons x tl ih =>
    simp only [mapListTracked, CostM.bind_snd, retTracked_snd, List.length_cons]
    rw [hf x List.mem_cons_self, ih (fun y hy => hf y (List.mem_cons_of_mem x hy))]
    ring

lemma mapListTracked_snd_le_const {γ δ : Type*} (f : γ → CostM δ) (c : ℕ) (xs : List γ)
    (hf : ∀ x ∈ xs, (f x).2 ≤ c) :
    (mapListTracked f xs).2 ≤ xs.length * (c + 1) + 1 := by
  induction xs with
  | nil => simp [mapListTracked]
  | cons x tl ih =>
    simp only [mapListTracked, CostM.bind_snd, retTracked_snd, List.length_cons]
    have hx := hf x List.mem_cons_self
    have htl := ih (fun y hy => hf y (List.mem_cons_of_mem x hy))
    nlinarith

/-- Cost-tracked list `flatMap` in `CostM`, mapping `f` over `xs` and concatenating via
`appendListTracked` (charging at most `xs.length * (c + m + 1) + 1` when `(f x).2 ≤ c` and
`((f x).1).length ≤ m`). -/
def flatMapListTracked {γ δ : Type*} (f : γ → CostM (List δ)) : List γ → CostM (List δ)
  | [] => retTracked []
  | x :: xs =>
    CostM.bind (f x) (fun ys =>
      CostM.bind (flatMapListTracked f xs) (fun rest =>
        appendListTracked ys rest))

@[simp]
lemma flatMapListTracked_fst {γ δ : Type*} (f : γ → CostM (List δ)) (xs : List γ) :
    (flatMapListTracked f xs).1 = xs.flatMap (fun x => (f x).1) := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    simp [flatMapListTracked, CostM.bind, appendListTracked_fst, ih]

lemma flatMapListTracked_snd_le_const {γ δ : Type*} (f : γ → CostM (List δ))
    (c m : ℕ) (xs : List γ)
    (hf : ∀ x ∈ xs, (f x).2 ≤ c ∧ ((f x).1).length ≤ m) :
    (flatMapListTracked f xs).2 ≤ xs.length * (c + m + 1) + 1 := by
  induction xs with
  | nil => simp [flatMapListTracked]
  | cons x tl ih =>
    simp only [flatMapListTracked, CostM.bind_snd, appendListTracked_snd, List.length_cons]
    have hx := hf x List.mem_cons_self
    have htl := ih (fun y hy => hf y (List.mem_cons_of_mem x hy))
    nlinarith

/-- Bottom-up single-step counter iterating `k` times and adding `1` per step. -/
def repeatStepsTracked : ℕ → ℕ
  | 0 => 0
  | k + 1 => repeatStepsTracked k + 1

@[simp]
lemma repeatStepsTracked_eq (k : ℕ) : repeatStepsTracked k = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [repeatStepsTracked, ih]

/-- Bottom-up 2D nested loop counter iterating `m` outer steps of `n` inner steps. -/
def repeatGridStepsTracked : ℕ → ℕ → ℕ
  | 0, _ => 0
  | m + 1, n => repeatGridStepsTracked m n + repeatStepsTracked n

@[simp]
lemma repeatGridStepsTracked_eq (m n : ℕ) : repeatGridStepsTracked m n = m * n := by
  induction m with
  | zero => simp [repeatGridStepsTracked]
  | succ m ih =>
    simp only [repeatGridStepsTracked, ih, repeatStepsTracked_eq]
    ring

/-- Tracked 1D scan over a finite set `U : Finset α`, iterating over `u ∈ U` and charging `1` per
element plus `1` (`U.card + 1`). -/
def scanFinsetTracked {α β : Type*} (U : Finset α) (val : β) : CostM β :=
  (val, (∑ _u ∈ U, 1) + 1)

@[simp]
lemma scanFinsetTracked_fst {α β : Type*} (U : Finset α) (val : β) :
    (scanFinsetTracked U val).1 = val := rfl

@[simp]
lemma scanFinsetTracked_snd {α β : Type*} (U : Finset α) (val : β) :
    (scanFinsetTracked U val).2 = U.card + 1 := by
  simp [scanFinsetTracked]

/-- Tracked 2D matrix scan over `U × V`, iterating over `u ∈ U` and `v ∈ V` and charging `1` per
pair plus `1` (`U.card * V.card + 1`). -/
def scanMatrixTracked {α β γ : Type*} (U : Finset α) (V : Finset β) (val : γ) : CostM γ :=
  (val, (∑ _u ∈ U, ∑ _v ∈ V, 1) + 1)

@[simp]
lemma scanMatrixTracked_fst {α β γ : Type*} (U : Finset α) (V : Finset β) (val : γ) :
    (scanMatrixTracked U V val).1 = val := rfl

@[simp]
lemma scanMatrixTracked_snd {α β γ : Type*} (U : Finset α) (V : Finset β) (val : γ) :
    (scanMatrixTracked U V val).2 = U.card * V.card + 1 := by
  simp [scanMatrixTracked]

/-- Tracked 3D bipartite matrix-pair scan over `X × Y` and `Y × Z`, charging
`X.card * Y.card + Y.card * Z.card + 1`. -/
def scanMatrixPairTracked {α β γ δ : Type*} (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (val : δ) : CostM δ :=
  (val, (∑ _x ∈ X, ∑ _y ∈ Y, 1) + (∑ _y ∈ Y, ∑ _z ∈ Z, 1) + 1)

@[simp]
lemma scanMatrixPairTracked_fst {α β γ δ : Type*} (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (val : δ) :
    (scanMatrixPairTracked X Y Z val).1 = val := rfl

@[simp]
lemma scanMatrixPairTracked_snd {α β γ δ : Type*} (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (val : δ) :
    (scanMatrixPairTracked X Y Z val).2 = X.card * Y.card + Y.card * Z.card + 1 := by
  simp [scanMatrixPairTracked]

/-- Tracked sub-block extraction scan for three `m × m` blocks `A_{a,b}, B_{b,c}, C_{a,c}`,
charging `3 * m * m + 1`. -/
def scanBlockExtractTracked {α : Type*} (m : ℕ) (val : α) : CostM α :=
  (val, repeatGridStepsTracked (3 * m) m + 1)

@[simp]
lemma scanBlockExtractTracked_fst {α : Type*} (m : ℕ) (val : α) :
    (scanBlockExtractTracked m val).1 = val := rfl

@[simp]
lemma scanBlockExtractTracked_snd {α : Type*} (m : ℕ) (val : α) :
    (scanBlockExtractTracked m val).2 = 3 * m * m + 1 := by
  simp [scanBlockExtractTracked, mul_assoc]

/-- Tracked commutative sum over a finite set `S : Finset α`, evaluating `f x : CostM ℕ` at each
element `x ∈ S` and accumulating both the value and step cost across all elements of `S` plus `1`
(`(∑ x ∈ S, (f x).2) + 1`). -/
def sumFinsetTracked {α : Type*} (S : Finset α) (f : α → CostM ℕ) : CostM ℕ :=
  (∑ x ∈ S, (f x).1, (∑ x ∈ S, (f x).2) + 1)

@[simp]
lemma sumFinsetTracked_fst {α : Type*} (S : Finset α) (f : α → CostM ℕ) :
    (sumFinsetTracked S f).1 = ∑ x ∈ S, (f x).1 := rfl

@[simp]
lemma sumFinsetTracked_snd {α : Type*} (S : Finset α) (f : α → CostM ℕ) :
    (sumFinsetTracked S f).2 = (∑ x ∈ S, (f x).2) + 1 := rfl

lemma sumFinsetTracked_snd_const {α : Type*} (S : Finset α) (f : α → CostM ℕ) (c : ℕ)
    (hf : ∀ x ∈ S, (f x).2 = c) :
    (sumFinsetTracked S f).2 = S.card * c + 1 := by
  rw [sumFinsetTracked_snd, Finset.sum_congr rfl hf, Finset.sum_const, smul_eq_mul]

/-- Tracked tabulation of `f : α → CostM γ` over a finite domain `S : Finset α`, evaluating `f x`
at each element `x ∈ S` and accumulating the step cost `(∑ x ∈ S, (f x).2) + 1` while returning
the tabulated function `fun x => (f x).1`. -/
def tabulateFinsetTracked {α γ : Type*} (S : Finset α) (f : α → CostM γ) : CostM (α → γ) :=
  ((fun x => (f x).1), (∑ x ∈ S, (f x).2) + 1)

@[simp]
lemma tabulateFinsetTracked_fst {α γ : Type*} (S : Finset α) (f : α → CostM γ) :
    (tabulateFinsetTracked S f).1 = fun x => (f x).1 := rfl

@[simp]
lemma tabulateFinsetTracked_snd {α γ : Type*} (S : Finset α) (f : α → CostM γ) :
    (tabulateFinsetTracked S f).2 = (∑ x ∈ S, (f x).2) + 1 := rfl

lemma tabulateFinsetTracked_snd_le_const {α γ : Type*} (S : Finset α) (f : α → CostM γ) (c : ℕ)
    (hf : ∀ x ∈ S, (f x).2 ≤ c) :
    (tabulateFinsetTracked S f).2 ≤ S.card * c + 1 := by
  rw [tabulateFinsetTracked_snd]
  have h1 : (∑ x ∈ S, (f x).2) ≤ ∑ _x ∈ S, c := Finset.sum_le_sum hf
  rw [Finset.sum_const, smul_eq_mul] at h1
  exact Nat.add_le_add_right h1 1

/-- Tracked per-element filter over a finite set `S : Finset α`, evaluating `p x : Bool` at each
element `x ∈ S` and charging `1` per element examined plus `1` (`S.card + 1`). -/
def filterFinsetByTracked {α : Type*} (S : Finset α) (p : α → Bool) : CostM (Finset α) :=
  (S.filter (fun x => p x = true), (∑ _x ∈ S, 1) + 1)

@[simp]
lemma filterFinsetByTracked_fst {α : Type*} (S : Finset α) (p : α → Bool) :
    (filterFinsetByTracked S p).1 = S.filter (fun x => p x = true) := rfl

@[simp]
lemma filterFinsetByTracked_snd {α : Type*} (S : Finset α) (p : α → Bool) :
    (filterFinsetByTracked S p).2 = S.card + 1 := by
  simp [filterFinsetByTracked]

/-- Tracked 2D support-pair scan over `U × V` evaluating a per-element Boolean predicate
`p : α → β → Bool` (`decide (∃ u ∈ U, ∃ v ∈ V, p u v = true)`), iterating over every `(u, v) ∈ U × V`
via `sumFinsetTracked` and charging `U.card * V.card + 1` (Algorithm 6 Case 1). -/
def evalSupportScanTracked {α β : Type*} (U : Finset α) (V : Finset β)
    (p : α → β → Bool) : CostM Bool :=
  let rowSums : CostM ℕ :=
    sumFinsetTracked U (fun u =>
      (∑ v ∈ V, if p u v then 1 else 0, ∑ _v ∈ V, 1))
  (decide (0 < rowSums.1), rowSums.2)

@[simp]
lemma evalSupportScanTracked_fst {α β : Type*} (U : Finset α) (V : Finset β)
    (p : α → β → Bool) :
    (evalSupportScanTracked U V p).1 = decide (∃ u ∈ U, ∃ v ∈ V, p u v = true) := by
  simp only [evalSupportScanTracked, sumFinsetTracked_fst, decide_eq_decide]
  simp only [Nat.pos_iff_ne_zero, Ne, Finset.sum_eq_zero_iff, not_forall, exists_prop,
    ite_eq_right_iff, one_ne_zero, imp_false, Bool.not_eq_true, Bool.not_eq_false]

@[simp]
lemma evalSupportScanTracked_snd {α β : Type*} (U : Finset α) (V : Finset β)
    (p : α → β → Bool) :
    (evalSupportScanTracked U V p).2 = U.card * V.card + 1 := by
  simp [evalSupportScanTracked, sumFinsetTracked_snd]

/-- Tracked minimum-degree neighbor intersection scan over `xz ∈ S` evaluating per-neighbor
Boolean predicates `p₁ p₂ : γ → α → Bool` element-by-element over the smaller neighborhood via
`sumFinsetTracked`, charging `(∑ xz ∈ S, (1 + min (N₁ xz).card (N₂ xz).card)) + 1`
(Algorithm 6 Case 2b). -/
def evalMinNbrScanTracked {α γ : Type*} (S : Finset γ)
    (N₁ N₂ : γ → Finset α) (p₁ p₂ : γ → α → Bool) : CostM Bool :=
  let pairSums : CostM ℕ :=
    sumFinsetTracked S (fun xz =>
      if (N₁ xz).card ≤ (N₂ xz).card then
        (∑ y ∈ N₁ xz, if p₁ xz y then 1 else 0, 1 + ∑ _y ∈ N₁ xz, 1)
      else
        (∑ y ∈ N₂ xz, if p₂ xz y then 1 else 0, 1 + ∑ _y ∈ N₂ xz, 1))
  (decide (0 < pairSums.1), pairSums.2)

@[simp]
lemma evalMinNbrScanTracked_fst {α γ : Type*} (S : Finset γ)
    (N₁ N₂ : γ → Finset α) (p₁ p₂ : γ → α → Bool) :
    (evalMinNbrScanTracked S N₁ N₂ p₁ p₂).1 =
      decide (∃ xz ∈ S,
        if (N₁ xz).card ≤ (N₂ xz).card then
          ∃ y ∈ N₁ xz, p₁ xz y = true
        else
          ∃ y ∈ N₂ xz, p₂ xz y = true) := by
  simp only [evalMinNbrScanTracked, sumFinsetTracked_fst, decide_eq_decide]
  simp only [Nat.pos_iff_ne_zero, Ne, Finset.sum_eq_zero_iff, not_forall, exists_prop]
  constructor
  · rintro ⟨xz, hxz, hne⟩
    refine ⟨xz, hxz, ?_⟩
    split_ifs at hne ⊢ with hle
    · simp only [Finset.sum_eq_zero_iff, not_forall, exists_prop, ite_eq_right_iff,
        one_ne_zero, imp_false, Bool.not_eq_true, Bool.not_eq_false] at hne
      exact hne
    · simp only [Finset.sum_eq_zero_iff, not_forall, exists_prop, ite_eq_right_iff,
        one_ne_zero, imp_false, Bool.not_eq_true, Bool.not_eq_false] at hne
      exact hne
  · rintro ⟨xz, hxz, hex⟩
    refine ⟨xz, hxz, ?_⟩
    split_ifs at hex ⊢ with hle
    · simp only [Finset.sum_eq_zero_iff, not_forall, exists_prop, ite_eq_right_iff,
        one_ne_zero, imp_false, Bool.not_eq_true, Bool.not_eq_false]
      exact hex
    · simp only [Finset.sum_eq_zero_iff, not_forall, exists_prop, ite_eq_right_iff,
        one_ne_zero, imp_false, Bool.not_eq_true, Bool.not_eq_false]
      exact hex

@[simp]
lemma evalMinNbrScanTracked_snd {α γ : Type*} (S : Finset γ)
    (N₁ N₂ : γ → Finset α) (p₁ p₂ : γ → α → Bool) :
    (evalMinNbrScanTracked S N₁ N₂ p₁ p₂).2 =
      (∑ xz ∈ S, (1 + min (N₁ xz).card (N₂ xz).card)) + 1 := by
  simp only [evalMinNbrScanTracked, sumFinsetTracked_snd, add_left_inj]
  refine Finset.sum_congr rfl (fun xz _ => ?_)
  split_ifs with hle
  · simp [hle]
  · simp [le_of_lt (not_le.mp hle)]

/-!
## Compile-Time Metaprogramming Auditors
-/

open Lean Elab Command Meta

/-- Standard Lean 4 axioms allowed in the transitive closure of any theorem or definition. -/
def allowedStandardAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- Compile-time command verifying that a declaration depends only on
`[propext, Classical.choice, Quot.sound]`. Fails compilation otherwise. -/
elab "#verify_standard_axioms " id:ident : command => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axioms ← collectAxioms declName
  for ax in axioms do
    if !allowedStandardAxioms.contains ax then
      throwError "Axiom hygiene failure in `{declName}`: forbidden axiom `{ax}` detected!"
  logInfo m!"[Axiom Gate Verified] `{declName}` depends only on standard axioms: {axioms.toList}"

/-- Strips any `_private.<module>.0.` prefix from `n` so `private` declarations inside
`namespace BMMGrid` are audited and traversed identically to public `BMMGrid.*` declarations. -/
def toUserBMMName (n : Name) : Name :=
  (Lean.privateToUserName? n).getD n

/-- Returns `true` when `s` starts with `pre` followed by one or more ASCII digits or `'_'`. -/
def hasDigitSuffix (s pre : String) : Bool :=
  s.startsWith pre &&
    let chars := s.toList.drop pre.length
    !chars.isEmpty && chars.all (fun c => c.isDigit || c == '_')

/-- Returns `true` for Lean elaborator/compiler auxiliary declarations (`_unary`, `_mutual`,
`_unsafe_rec`, `_sunfold`, `_brecOn`, `_below`, `_ibelow`, `eq_<n>`, `match_<n>`, `proof_<n>`,
`omega_<n>`, `_cstage<n>`, `_closed_<n>`). Does not match arbitrary user names starting with `_`. -/
def isAuxDeclName : Name → Bool
  | Name.str p s =>
    s == "_unary" || s == "_mutual" || s == "_unsafe_rec" || s == "_sunfold" ||
    s == "_brecOn" || s == "_below" || s == "_ibelow" ||
    hasDigitSuffix s "eq_" || hasDigitSuffix s "match_" || hasDigitSuffix s "proof_" ||
    hasDigitSuffix s "omega_" || hasDigitSuffix s "_cstage" || hasDigitSuffix s "_closed_" ||
    isAuxDeclName p
  | Name.num _ _ => true
  | Name.anonymous => false

/-- Compile-time command verifying that no public or `private` `BMMGrid.*` declaration in the
environment is an `axiom`, `opaque`, or `unsafe` definition, and that every `BMMGrid.*` theorem
and definition depends only on `allowedStandardAxioms` (`[propext, Classical.choice, Quot.sound]`).
(`@[implemented_by]` and `@[extern]` attributes are checked across all 14 `.lean` files by
`make -C lean audit`.) -/
elab "#verify_no_escape_hatches" : command => do
  let env ← getEnv
  let mut checkedNames : Array Name := #[]
  for (name, cinfo) in env.constants do
    let uname := toUserBMMName name
    if (`BMMGrid).isPrefixOf uname then
      match cinfo with
      | ConstantInfo.axiomInfo _ =>
        throwError "[Escape-Hatch Audit Failure] Forbidden `axiom` declaration `{name}` in `BMMGrid`!"
      | ConstantInfo.opaqueInfo _ =>
        throwError "[Escape-Hatch Audit Failure] Forbidden `opaque` declaration `{name}` in `BMMGrid`!"
      | _ =>
        if cinfo.isUnsafe then
          throwError "[Escape-Hatch Audit Failure] Forbidden `unsafe` declaration `{name}` in `BMMGrid`!"
        if !isAuxDeclName uname then
          match cinfo with
          | ConstantInfo.thmInfo _ | ConstantInfo.defnInfo _ =>
            checkedNames := checkedNames.push name
          | _ => pure ()
  let (_, s) := ((checkedNames.forM Lean.CollectAxioms.collect).run env).run {}
  for ax in s.axioms do
    if !allowedStandardAxioms.contains ax then
      for name in checkedNames do
        let axioms ← collectAxioms name
        if axioms.contains ax then
          throwError "[Escape-Hatch Audit Failure] Declaration `{name}` depends on non-standard axiom `{ax}`!"
      throwError "[Escape-Hatch Audit Failure] Non-standard axiom `{ax}` found in `BMMGrid`!"
  logInfo m!"[Escape-Hatch Audit Verified] Zero `axiom`, `opaque`, or `unsafe` declarations in `BMMGrid`; all {checkedNames.size} `BMMGrid.*` theorems and definitions depend only on standard axioms."

/-- Closed-form complexity bound names, unpriced moment/norm formulas, and exact grid-norm /
regularity predicates that are checked by the static AST lint `#verify_tracked_declarations_ast_audit`
against direct references inside `*Tracked` definitions. -/
def forbiddenFormulaNamesInTracked : List Name :=
  [`BMMGrid.samplerOverheadExp, `BMMGrid.decompExpCoeff, `BMMGrid.decompPieceBound,
   `BMMGrid.C_tri, `BMMGrid.D_tri, `BMMGrid.C_bmm, `BMMGrid.D_bmm,
   `BMMGrid.C_tri_log, `BMMGrid.D_tri_log, `BMMGrid.C_bmm_log, `BMMGrid.D_bmm_log,
   `BMMGrid.triDetParamD, `BMMGrid.blockSizeBMM, `BMMGrid.triDetSavingFactor,
   `BMMGrid.concreteApproxGridNormCostFactor, `BMMGrid.goodRectStepCostFactor,
   `BMMGrid.goodCubeStepCostFactor, `BMMGrid.deltaHACostFactor,
   `BMMGrid.abIterCostFactor, `BMMGrid.abDepthCostFactor,
   `BMMGrid.rawDeltaHB, `BMMGrid.rawDeltaHA,
   `BMMGrid.M_rect3D, `BMMGrid.M_cube, `BMMGrid.QTree3D, `BMMGrid.GammaTree3D,
   `BMMGrid.gridNorm, `BMMGrid.gridNormPow, `BMMGrid.gridNormPowCol,
   `BMMGrid.gridNorm1, `BMMGrid.gridNorm1Pow, `BMMGrid.gridNorm2Pow, `BMMGrid.lpNormSet,
   `BMMGrid.IsGridRegular, `BMMGrid.IsGridRegular2Pow, `BMMGrid.IsEpsMinDegree,
   `BMMGrid.sampleMomentNumSeq,
   `BMMGrid.approxGridNormVxSeqCommonDenomPair,
   `BMMGrid.approxGridNormV, `BMMGrid.approxGridNormU,
   `BMMGrid.approxGridNormVSeq, `BMMGrid.approxGridNormUSeq,
   `BMMGrid.approxGridNormVTuple, `BMMGrid.approxGridNormUTuple,
   `BMMGrid.transportFam, `BMMGrid.lookupSeq, `BMMGrid.composeFamilies,
   `BMMGrid.modFinFam, `BMMGrid.stage2FinMFam]

/-- Primitive `CostM` combinators defined in `BMMGrid/CostMonadAndLinter.lean`.
Checked by `#verify_tracked_declarations_ast_audit` as the foundational combinator layer. -/
def primitiveCostMCombinators : List Name :=
  [`BMMGrid.addNatTracked, `BMMGrid.subNatTracked, `BMMGrid.mulNatTracked,
   `BMMGrid.divNatTracked, `BMMGrid.modNatTracked,
   `BMMGrid.cmpLeNatTracked, `BMMGrid.cmpLtNatTracked,
   `BMMGrid.powNatTracked, `BMMGrid.log2NatTracked, `BMMGrid.sqrtNatTracked,
   `BMMGrid.cmpRatCrossLeTracked, `BMMGrid.cmpRatCrossLtTracked,
   `BMMGrid.foldlListTracked, `BMMGrid.filterListByTracked,
   `BMMGrid.retTracked, `BMMGrid.findSomeListTracked, `BMMGrid.findSomeListByTracked,
   `BMMGrid.appendListTracked, `BMMGrid.mapListTracked, `BMMGrid.flatMapListTracked,
   `BMMGrid.repeatStepsTracked, `BMMGrid.repeatGridStepsTracked,
   `BMMGrid.scanFinsetTracked, `BMMGrid.scanMatrixTracked,
   `BMMGrid.scanMatrixPairTracked, `BMMGrid.scanBlockExtractTracked,
   `BMMGrid.sumFinsetTracked, `BMMGrid.tabulateFinsetTracked, `BMMGrid.filterFinsetByTracked,
   `BMMGrid.evalSupportScanTracked, `BMMGrid.evalMinNbrScanTracked]

/-- Exact grid-norm, $L_p$-norm, regularity predicates, unpriced moment formulas, untracked sampler
accessors, and closed-form time/piece bound names that are checked transitively across `BMMGrid.*`
`ConstantInfo.defnInfo` helper definitions by `#verify_tracked_declarations_ast_audit` and
`#verify_headline_cone_excludes`. -/
def forbiddenOracleNamesInHelpers : List Name :=
  [`BMMGrid.decompExpCoeff, `BMMGrid.decompPieceBound,
   `BMMGrid.C_tri, `BMMGrid.D_tri, `BMMGrid.C_bmm, `BMMGrid.D_bmm,
   `BMMGrid.C_tri_log, `BMMGrid.D_tri_log, `BMMGrid.C_bmm_log, `BMMGrid.D_bmm_log,
   `BMMGrid.triDetParamD, `BMMGrid.blockSizeBMM, `BMMGrid.triDetSavingFactor,
   `BMMGrid.concreteApproxGridNormCostFactor, `BMMGrid.goodRectStepCostFactor,
   `BMMGrid.goodCubeStepCostFactor, `BMMGrid.deltaHACostFactor,
   `BMMGrid.abIterCostFactor, `BMMGrid.abDepthCostFactor,
   `BMMGrid.rawDeltaHB, `BMMGrid.rawDeltaHA,
   `BMMGrid.gridNorm, `BMMGrid.gridNormPow, `BMMGrid.gridNormPowCol,
   `BMMGrid.gridNorm1, `BMMGrid.gridNorm1Pow, `BMMGrid.gridNorm2Pow, `BMMGrid.lpNormSet,
   `BMMGrid.IsGridRegular, `BMMGrid.IsGridRegular2Pow, `BMMGrid.IsEpsMinDegree,
   `BMMGrid.sampleMomentNumSeq,
   `BMMGrid.approxGridNormVxSeqCommonDenomPair,
   `BMMGrid.approxGridNormV, `BMMGrid.approxGridNormU,
   `BMMGrid.approxGridNormVSeq, `BMMGrid.approxGridNormUSeq,
   `BMMGrid.approxGridNormVTuple, `BMMGrid.approxGridNormUTuple,
   `BMMGrid.Stage1Sampler.fam, `BMMGrid.Stage2Sampler.fam,
   `BMMGrid.Stage1Sampler.len, `BMMGrid.Stage2Sampler.len,
   `BMMGrid.transportFam, `BMMGrid.lookupSeq, `BMMGrid.composeFamilies,
   `BMMGrid.modFinFam, `BMMGrid.stage2FinMFam]

/-- Concrete complexity constants, discrete parameter functions, and combinatorial reduction
components in `BMMGrid` that must exist in the environment and be strictly computable
(`!Lean.isNoncomputable`). -/
def computableComplexityConstants : List Name :=
  [`BMMGrid.twoStageSampleSizeBound, `BMMGrid.twoStageFamFactor,
   `BMMGrid.twoStageConstK, `BMMGrid.twoStageConstC,
   `BMMGrid.stage2BitLen, `BMMGrid.stage2FinMK, `BMMGrid.stage2FinMC,
   `BMMGrid.modFin, `BMMGrid.modFinTracked, `BMMGrid.modFinFamTracked,
   `BMMGrid.mapListTracked, `BMMGrid.flatMapListTracked,
   `BMMGrid.lookupSeqTracked, `BMMGrid.composeFamiliesTracked,
   `BMMGrid.samplerOverheadExp, `BMMGrid.decompExpCoeff,
   `BMMGrid.deltaHACostFactor,
   `BMMGrid.triDetC0Inv, `BMMGrid.D_tri, `BMMGrid.D_bmm, `BMMGrid.D_tri_log, `BMMGrid.D_bmm_log,
   `BMMGrid.triDetParamD, `BMMGrid.numBlocksBMM, `BMMGrid.triDetSavingFactor,
   `BMMGrid.blockSizeBMM, `BMMGrid.extractBlockMat, `BMMGrid.findBlockTriangle,
   `BMMGrid.processBlockTripleLoop, `BMMGrid.foldBlockTriples, `BMMGrid.bmmFromTriDet,
   `BMMGrid.tabulateFinsetTracked,
   `BMMGrid.approxGridNormVxRowPairTracked,
   `BMMGrid.buildTupleTableFinsetTracked, `BMMGrid.contractTupleTableSimpleTracked,
   `BMMGrid.contractTupleTableFamilySimpleTracked,
   `BMMGrid.checkSparsePieceNatTracked,
   `BMMGrid.checkDenseCSubcase2aExactNatTracked,
   `BMMGrid.rawDeltaHBNat, `BMMGrid.rawDeltaHANat,
   `BMMGrid.rawDeltaHBNatTracked, `BMMGrid.rawDeltaHANatTracked,
   `BMMGrid.clampDeltaHBTracked, `BMMGrid.clampDeltaHATracked]

/-- `ℝ`-specification types and bridges whose presence in a `*Tracked` declaration's type or body is
the sole permitted reason for `noncomputable`. Any `BMMGrid.*Tracked` declaration that
does not bridge `Real`, `CubePiece`, `RectPiece`, or `computableTriangleDetectionTracked` must be
strictly computable (`!Lean.isNoncomputable`). -/
def realSpecBridgeNames : List Name :=
  [`Real, `BMMGrid.CubePiece, `BMMGrid.RectPiece, `BMMGrid.computableTriangleDetectionTracked,
   `BMMGrid.computableTriangleDetectionTracked_of_sampler,
   `BMMGrid.Stage1Sampler, `BMMGrid.Stage2Sampler,
   `BMMGrid.indexFinset, `BMMGrid.constructSmallTwoStageSampler, `Finset.toList]

/-- Returns `true` when peeling all outer `Expr.forallE` binders from `ty` leaves an application
whose syntactic head constant is `BMMGrid.CostM` (does not unfold `Prod α ℕ` aliases). -/
def returnsCostM : Expr → Bool
  | Expr.forallE _ _ body _ => returnsCostM body
  | e => e.getAppFn.isConstOf ``CostM

/-- Recursively checks (up to AST depth `fuel`) that an expression `e` inside a `*Tracked`
declaration `declName` contains no `CostM.bind` call whose syntactic `Expr.lam` (`fun`)
continuation discards a non-`Unit` / non-`PUnit` bound variable. -/
def verifyNoDiscardedBind : Nat → Name → Expr → CommandElabM Unit
  | 0, _, _ => pure ()
  | fuel + 1, declName, e => do
    if e.getAppFn.isConstOf ``CostM.bind && e.getAppNumArgs >= 4 then
      let args := e.getAppArgs
      let alpha := args[0]!
      let f := args[3]!
      let isUnitType := alpha.isConstOf ``Unit || alpha.isConstOf ``PUnit
      if let Expr.lam binderName _ body _ := f then
        if !isUnitType && !body.hasLooseBVar 0 then
          throwError "[Value-Provenance Lint Failure] Tracked declaration `{declName}` contains a decoy `CostM.bind` whose non-Unit result (`{binderName}`) is discarded!"
    match e with
    | Expr.app fn arg =>
      verifyNoDiscardedBind fuel declName fn
      verifyNoDiscardedBind fuel declName arg
    | Expr.lam _ ty body _ =>
      verifyNoDiscardedBind fuel declName ty
      verifyNoDiscardedBind fuel declName body
    | Expr.forallE _ ty body _ =>
      verifyNoDiscardedBind fuel declName ty
      verifyNoDiscardedBind fuel declName body
    | Expr.letE _ ty val body _ =>
      verifyNoDiscardedBind fuel declName ty
      verifyNoDiscardedBind fuel declName val
      verifyNoDiscardedBind fuel declName body
    | Expr.mdata _ inner =>
      verifyNoDiscardedBind fuel declName inner
    | Expr.proj _ _ inner =>
      verifyNoDiscardedBind fuel declName inner
    | _ => pure ()

/-- Recursively checks tail return positions of a non-primitive `CostM` expression `e` inside
`declName` (descending through lambdas, `let`-bindings, metadata wrappers, `ite`/`dite` branches,
and `CostM.bind` arguments/continuations) to reject direct `Prod.mk` tuple construction in `CostM`
return positions (`CostM.withCost` / combinators must be used instead). -/
def verifyNoRawCostMTuple : Nat → Name → Expr → CommandElabM Unit
  | 0, _, _ => pure ()
  | fuel + 1, declName, e => do
    if e.getAppFn.isConstOf ``Prod.mk then
      throwError "[AST Hygiene Lint Failure] Non-primitive `CostM` declaration `{declName}` returns a raw `Prod.mk` tuple directly instead of invoking a tracked combinator!"
    if e.getAppFn.isConstOf ``CostM.bind && e.getAppNumArgs >= 4 then
      let args := e.getAppArgs
      verifyNoRawCostMTuple fuel declName args[2]!
      verifyNoRawCostMTuple fuel declName args[3]!
    else if (e.getAppFn.isConstOf ``ite || e.getAppFn.isConstOf ``dite) && e.getAppNumArgs >= 5 then
      let args := e.getAppArgs
      verifyNoRawCostMTuple fuel declName args[3]!
      verifyNoRawCostMTuple fuel declName args[4]!
    else
      match e with
      | Expr.lam _ _ body _ => verifyNoRawCostMTuple fuel declName body
      | Expr.letE _ _ _ body _ => verifyNoRawCostMTuple fuel declName body
      | Expr.mdata _ inner => verifyNoRawCostMTuple fuel declName inner
      | _ => pure ()

/-- Compile-time heuristic AST, computability, and value-provenance hygiene lint (for defense in
depth rather than a soundness guard; cost accounting relies on manual review of the 107 combinator
call sites in `FORMALIZATION.tex`) checking that:
1. Every `BMMGrid.*Tracked` definition (and every non-auxiliary `BMMGrid.*` definition whose
   syntactic return head is `CostM`) does not directly reference any name in
   `forbiddenFormulaNamesInTracked`, and no `BMMGrid.*` `ConstantInfo.defnInfo` helper in its
   transitive `BMMGrid.*` definition cone references any name in `forbiddenOracleNamesInHelpers`,
2. Outside `primitiveCostMCombinators`, does not reference `CostM.withCost`, `CostM.tick`, or
   `CostM.pure` directly and does not return a raw `Prod.mk` tuple at any `CostM` tail position
   (`verifyNoRawCostMTuple`),
3. Every `CostM.bind` with a syntactic `Expr.lam` continuation uses its bound variable whenever its
   return type is non-`Unit` (`verifyNoDiscardedBind`), and `concreteApproxGridNormVTracked`
   directly invokes `buildTupleTableFinsetTracked`, `approxGridNormVxRowPairTracked`, and
   `tabulateFinsetTracked`,
4. Every discrete/combinatorial/rational `BMMGrid.*Tracked` declaration (not referencing
   `realSpecBridgeNames`), every `BMMGrid.ArithRAM.*` definition, and every constant in
   `computableComplexityConstants` exists in the environment and is computable
   (`!Lean.isNoncomputable env name`). -/
elab "#verify_tracked_declarations_ast_audit" : command => do
  let env ← getEnv
  let mut auditedCount := 0
  let mut computableTrackedCount := 0
  for c in forbiddenFormulaNamesInTracked do
    if !env.contains c then
      throwError "[AST Lint Failure] Listed constant `{c}` in `forbiddenFormulaNamesInTracked` does not exist in the environment!"
  for c in forbiddenOracleNamesInHelpers do
    if !env.contains c then
      throwError "[AST Lint Failure] Listed constant `{c}` in `forbiddenOracleNamesInHelpers` does not exist in the environment!"
  for c in computableComplexityConstants do
    if !env.contains c then
      throwError "[Computability Lint Failure] Listed constant `{c}` in `computableComplexityConstants` does not exist in the environment!"
    if Lean.isNoncomputable env c then
      throwError "[Computability Lint Failure] Concrete complexity/algorithmic constant `{c}` is marked `noncomputable`!"
  for (name, cinfo) in env.constants do
    let uname := toUserBMMName name
    if (`BMMGrid.ArithRAM).isPrefixOf uname && !isAuxDeclName uname then
      match cinfo with
      | ConstantInfo.defnInfo _ =>
        if Lean.isNoncomputable env name then
          throwError "[Computability Lint Failure] `ArithRAM` definition `{name}` is `noncomputable`!"
      | _ => pure ()
    let isTrackedByName :=
      (`BMMGrid).isPrefixOf uname && uname.toString.endsWith "Tracked" && !isAuxDeclName uname
    let isCostMDefn :=
      (`BMMGrid).isPrefixOf uname &&
      !(`BMMGrid.CostM).isPrefixOf uname &&
      !isAuxDeclName uname &&
      match cinfo with
      | ConstantInfo.defnInfo _ => returnsCostM cinfo.type
      | _ => false
    if isTrackedByName || isCostMDefn then
      match cinfo.value? with
      | some val =>
        auditedCount := auditedCount + 1
        verifyNoDiscardedBind 10000 name val
        if !primitiveCostMCombinators.contains uname && returnsCostM cinfo.type then
          verifyNoRawCostMTuple 10000 name val
        let usedConsts := val.getUsedConstants
        if uname == `BMMGrid.concreteApproxGridNormVTracked then
          for req in [`BMMGrid.buildTupleTableFinsetTracked,
                      `BMMGrid.approxGridNormVxRowPairTracked,
                      `BMMGrid.tabulateFinsetTracked] do
            if !usedConsts.contains req then
              throwError "[Value-Provenance Lint Failure] `concreteApproxGridNormVTracked` must directly invoke `{req}`!"
        let typeConsts := cinfo.type.getUsedConstants
        let bridgesRealSpec :=
          usedConsts.any (fun u => realSpecBridgeNames.contains u) ||
          typeConsts.any (fun u => realSpecBridgeNames.contains u)
        if !bridgesRealSpec && Lean.isNoncomputable env name then
          throwError "[Computability Lint Failure] Discrete/combinatorial tracked declaration `{name}` is `noncomputable` without bridging `Real`!"
        if !Lean.isNoncomputable env name then
          computableTrackedCount := computableTrackedCount + 1
        let mut hVisited : NameSet := {}
        let mut hQueue : Array Name := #[]
        for u in usedConsts do
          let uUser := toUserBMMName u
          if forbiddenFormulaNamesInTracked.contains uUser then
            throwError "[AST Lint Failure] Tracked declaration `{name}` references forbidden formula `{u}`!"
          if !primitiveCostMCombinators.contains uname &&
              (u == ``CostM.withCost || u == ``CostM.tick || u == ``CostM.pure) then
            throwError "[AST Lint Failure] Non-primitive tracked declaration `{name}` calls `{u}` directly instead of composing tracked combinators!"
          if (`BMMGrid).isPrefixOf uUser then
            if let some (ConstantInfo.defnInfo _) := env.find? u then
              hQueue := hQueue.push u
        let mut hIdx := 0
        while hIdx < hQueue.size do
          let curr := hQueue[hIdx]!
          hIdx := hIdx + 1
          if !hVisited.contains curr then
            hVisited := hVisited.insert curr
            if let some (ConstantInfo.defnInfo hdef) := env.find? curr then
              for hu in hdef.value.getUsedConstants do
                let huUser := toUserBMMName hu
                if forbiddenOracleNamesInHelpers.contains huUser then
                  throwError "[Transitive AST Lint Failure] Tracked declaration `{name}` transitively reaches helper `{curr}` which references forbidden oracle/formula `{hu}`!"
                if (`BMMGrid).isPrefixOf huUser && !hVisited.contains hu then
                  if let some (ConstantInfo.defnInfo _) := env.find? hu then
                    hQueue := hQueue.push hu
      | none =>
        throwError "[AST Lint Failure] Tracked declaration `{name}` has no definition body!"
  logInfo m!"[AST & Computability Lint Verified] Audited {auditedCount} `BMMGrid.*Tracked` / `CostM` declarations ({computableTrackedCount} strictly computable discrete/rational combinators)."

/-- Root tracked definitions for the headline algorithmic cone exclusion check
(`#verify_headline_cone_excludes`). -/
def headlineConeRoots : List Name :=
  [`BMMGrid.computableBMMTracked,
   `BMMGrid.computableTriangleDetectionTracked,
   `BMMGrid.cappedABDecompositionTracked,
   `BMMGrid.cappedADecompositionConcreteTracked,
   `BMMGrid.twoStage_compose]

/-- Specification predicates, naive matrix multiplication, and closed-form bounds/oracles that must
never appear in any `BMMGrid.*` `ConstantInfo.defnInfo` definition in the transitive cone of
`headlineConeRoots`. -/
def forbiddenHeadlineConeTargets : List Name :=
  [`BMMGrid.boolMatMul, `BMMGrid.hasTriangle, `BMMGrid.stdMatMul] ++
  forbiddenOracleNamesInHelpers

/-- Unbounded-depth transitive `BMMGrid.*` `ConstantInfo.defnInfo` cone exclusion lint checking
that every reachable `BMMGrid.*` definition in the cone from `headlineConeRoots`:
1. Never references `boolMatMul`, `hasTriangle`, `stdMatMul`, or any symbol in
   `forbiddenOracleNamesInHelpers`, and
2. Whenever the reachable definition is a `*Tracked` or `CostM`-returning definition, never
   references any symbol in `forbiddenFormulaNamesInTracked`. -/
elab "#verify_headline_cone_excludes" : command => do
  let env ← getEnv
  for root in headlineConeRoots do
    match env.find? root with
    | some (ConstantInfo.defnInfo _) => pure ()
    | some (ConstantInfo.thmInfo _) => pure ()
    | _ =>
      throwError "[Headline Cone Audit Failure] Root `{root}` not found in environment!"
  let mut visited : NameSet := {}
  let mut queue : Array Name := headlineConeRoots.toArray
  let mut idx := 0
  while idx < queue.size do
    let curr := queue[idx]!
    idx := idx + 1
    if !visited.contains curr then
      visited := visited.insert curr
      if let some cinfo := env.find? curr then
        if let some val := cinfo.value? then
          let currUser := toUserBMMName curr
          let isTrackedOrCostM :=
            currUser.toString.endsWith "Tracked" || returnsCostM cinfo.type
          for u in val.getUsedConstants do
            let uUser := toUserBMMName u
            if cinfo matches ConstantInfo.defnInfo _ then
              if forbiddenHeadlineConeTargets.contains uUser then
                throwError "[Headline Cone Audit Failure] Reachable definition `{curr}` in headline cone references forbidden target `{u}`!"
              if isTrackedOrCostM && forbiddenFormulaNamesInTracked.contains uUser then
                throwError "[Headline Cone Audit Failure] Reachable CostM/Tracked definition `{curr}` in headline cone references forbidden formula `{u}`!"
            if (`BMMGrid).isPrefixOf uUser && !visited.contains u then
              if let some (ConstantInfo.defnInfo _) := env.find? u then
                queue := queue.push u
  logInfo m!"[Headline Cone Verified] Unbounded-depth BFS from {headlineConeRoots} visited {visited.size} `BMMGrid.*` roots/definitions with zero references to `boolMatMul`, `hasTriangle`, `stdMatMul`, or forbidden oracle/bound symbols."

/-- Headline theorem roots gated by `#verify_standard_axioms` in `BMMGrid.lean`. -/
def headlineTheoremRoots : List Name :=
  [`BMMGrid.prop_regular_matrices_uniform_product,
   `BMMGrid.twoStage_compose,
   `BMMGrid.lem_approx_grid_norm,
   `BMMGrid.thm_2d_decomp,
   `BMMGrid.thm_2d_decomp_concrete,
   `BMMGrid.thm_2d_decomp_uncapped,
   `BMMGrid.thm_2d_decomp_uncapped_concrete,
   `BMMGrid.thm_main_decomp,
   `BMMGrid.thm_main_decomp_of_samplers,
   `BMMGrid.thm_main_3d_decomposition,
   `BMMGrid.thm_main_triangle_detection,
   `BMMGrid.thm_main_triangle_detection_graph,
   `BMMGrid.thm_main_triangle_detection_log_cost_absorption,
   `BMMGrid.thm_main_bmm,
   `BMMGrid.thm_main_bmm_log_cost_absorption]

/-- Documented auxiliary roots kept intentionally outside the headline theorem cone. -/
def auxiliaryRoots : List Name :=
  [ -- Paper §4.4 Proposition 4.7 single-step and multi-block sifting tightness witnesses:
    `BMMGrid.rem_obstacles_single_step_tightness,
    `BMMGrid.rem_obstacles_multiblock_sift_tightness,
    -- Paper §4.1 Lemma 4.1 unconditional tuple and Chebyshev instantiations:
    `BMMGrid.lem_approx_grid_norm_tuple,
    `BMMGrid.lem_approx_grid_norm_chebyshev_tuple,
    `BMMGrid.concreteApproxGridNormVChebyshev_approx,
    -- Paper §4.2 Lemma 4.2 unconditional Chebyshev dyadic-sift instantiation:
    `BMMGrid.lem_dyadic_sift_chebyshev,
    -- Chebyshev tuple-sampler cardinality and uniform sample-size properties:
    `BMMGrid.constructChebyshevTupleSampler_card,
    `BMMGrid.constructChebyshevTupleSampler_sample_size,
    `BMMGrid.constructChebyshevTupleSampler_uniform_sample_size,
    `BMMGrid.one_le_chebyshevSampleSize,
    -- Small-universe oracle inhabitation witness and cost bound:
    `BMMGrid.twoStageSamplerOracle_nonempty_of_le,
    `BMMGrid.constructSmallTwoStageSamplerTracked_fst,
    `BMMGrid.constructSmallTwoStageSamplerTracked_snd,
    -- Concrete Lemma 4.2 correctness wrapper for dyadicSiftConcrete cited in FORMALIZATION.tex:
    `BMMGrid.lem_dyadic_sift_concrete,
    -- Concrete Lemma 4.3 cost projection cited in FORMALIZATION.tex and its companion .1 projection:
    `BMMGrid.cappedGoodRectConcreteTracked_fst,
    `BMMGrid.cappedGoodRectConcreteTracked_snd_le,
    -- 3D-to-2D specialization bridges cited in FORMALIZATION.tex and their companion loop-equivalence lemmas:
    `BMMGrid.cappedGoodRect3D_eq_cappedGoodRectConcrete,
    `BMMGrid.cappedADecomp3D_eq_cappedADecompositionConcrete,
    `BMMGrid.cappedGoodRect3DLoop_eq_goodRectLoop_concrete,
    `BMMGrid.cappedADecomp3DLoop_eq_aDecompositionLoop_concrete,
    -- Paper §4.3 Theorem 4.4 width comparison helper cited in FORMALIZATION.tex:
    `BMMGrid.rRect2DFuel_width_le_paper,
    -- Paper §4.1/§4.2 & §8(iv) uniform EstimateNorm accuracy bound cited in FORMALIZATION.tex §4:
    `BMMGrid.three_mul_add_six_le_accExp,
    -- Paper §6 Algorithm 6 floor-division parameter identity cited in FORMALIZATION.tex:
    `BMMGrid.triDetParamD_eq_floor_div,
    -- Paper §1.2 Theorem 1.2 simple-graph strict-monotonicity bridge cited in FORMALIZATION.tex:
    `BMMGrid.hasTriangle_eq_true_iff_strictMono_of_symm_irrefl,
    -- Short aliases for the log-cost absorption corollaries cited in FORMALIZATION.tex:
    `BMMGrid.thm_main_triangle_detection_log_cost,
    `BMMGrid.thm_main_bmm_log_cost,
    -- Tracked .1 projection lemmas whose rfl proofs are reduced definitionally by simp only:
    `BMMGrid.clampDeltaHATracked_fst,
    `BMMGrid.clampDeltaHBTracked_fst,
    `BMMGrid.detectOnPieceTracked_fst ]

/-- Foundational `CostM` primitive interface and linter configuration declarations in
`CostMonadAndLinter.lean`. -/
def linterHelperRoots : List Name :=
  [`BMMGrid.CostM.pure, `BMMGrid.CostM.tick, `BMMGrid.CostM.withCost, `BMMGrid.CostM.bind,
   `BMMGrid.CostM.bind_fst, `BMMGrid.CostM.bind_snd,
   `BMMGrid.addNatTracked_fst, `BMMGrid.addNatTracked_snd,
   `BMMGrid.subNatTracked_fst, `BMMGrid.subNatTracked_snd,
   `BMMGrid.mulNatTracked_fst, `BMMGrid.mulNatTracked_snd,
   `BMMGrid.divNatTracked_fst, `BMMGrid.divNatTracked_snd,
   `BMMGrid.modNatTracked_fst, `BMMGrid.modNatTracked_snd,
   `BMMGrid.cmpLeNatTracked_fst, `BMMGrid.cmpLeNatTracked_snd,
   `BMMGrid.cmpLtNatTracked_fst, `BMMGrid.cmpLtNatTracked_snd,
   `BMMGrid.powNatTracked_fst, `BMMGrid.powNatTracked_snd,
   `BMMGrid.log2NatTracked_fst, `BMMGrid.log2NatTracked_snd,
   `BMMGrid.sqrtNatTracked_fst, `BMMGrid.sqrtNatTracked_snd,
   `BMMGrid.scanFinsetTracked_fst, `BMMGrid.scanMatrixTracked_fst,
   `BMMGrid.sumFinsetTracked_fst, `BMMGrid.tabulateFinsetTracked_fst,
   `BMMGrid.filterFinsetByTracked_fst,
   `BMMGrid.scanBlockExtractTracked_fst, `BMMGrid.scanBlockExtractTracked_snd,
   `BMMGrid.cmpRatCrossLeTracked_fst, `BMMGrid.cmpRatCrossLeTracked_snd,
   `BMMGrid.cmpRatCrossLtTracked_fst, `BMMGrid.cmpRatCrossLtTracked_snd,
   `BMMGrid.allowedStandardAxioms,
   `BMMGrid.forbiddenFormulaNamesInTracked,
   `BMMGrid.primitiveCostMCombinators,
   `BMMGrid.forbiddenOracleNamesInHelpers,
   `BMMGrid.computableComplexityConstants,
   `BMMGrid.realSpecBridgeNames,
   `BMMGrid.returnsCostM,
   `BMMGrid.hasDigitSuffix,
   `BMMGrid.toUserBMMName,
   `BMMGrid.isAuxDeclName,
   `BMMGrid.verifyNoDiscardedBind, `BMMGrid.verifyNoRawCostMTuple,
   `BMMGrid.headlineConeRoots,
   `BMMGrid.forbiddenHeadlineConeTargets,
   `BMMGrid.headlineTheoremRoots,
   `BMMGrid.auxiliaryRoots,
   `BMMGrid.linterHelperRoots]

/-- Heuristic filter returning `true` for compiler/elaborator-generated auxiliary declarations,
inductive constructors/recursors/eliminators (`Lean.isAuxRecursor`, `Lean.isNoConfusion`), structure
projections (`Lean.getStructureInfo?`), and derived typeclass/enumerator helpers (`inst*`, `_aux_*`,
`decEq`, `enumList*`, `proxyType*`, etc.). -/
def isCompilerOrInductAux (env : Environment) (uname : Name) (cinfo : ConstantInfo) : Bool :=
  if isAuxDeclName uname || Lean.isAuxRecursor env uname || Lean.isNoConfusion env uname then true
  else
    match cinfo with
    | ConstantInfo.ctorInfo _ => true
    | ConstantInfo.recInfo _ => true
    | _ =>
      match uname with
      | Name.str p s =>
        if s == "eq_def" || s == "eq_unfold" || s == "_unfold" || s == "_eq_def" ||
           s == "ctorIdx" || s == "toCtorIdx" || s == "ofNat" || s == "inj" || s == "injEq" ||
           s == "elim" || s == "ctorElim" || s == "ctorElimType" || s == "ofNat_ctorIdx" ||
           s == "_flat_ctor" || s == "congr_simp" ||
           s == "sizeOf_spec" || s == "_sizeOf_inst" || s == "_autoParam" ||
           s == "decEq" || s == "default" || s == "repr" ||
           s == "noConfusionType" || s == "brecOn" || s == "below" || s == "ibelow" ||
           s == "enumList" || s == "enumList_getElem?_ctorIdx_eq" || s == "enumList_nodup" ||
           s == "proxyType" || s == "proxyTypeEquiv" ||
           s.startsWith "inst" || s.startsWith "command#verify_" || s.startsWith "_aux_" ||
           hasDigitSuffix s "_proof_" || hasDigitSuffix s "_match_" ||
           hasDigitSuffix s "_eq_" || hasDigitSuffix s "_sizeOf_" ||
           hasDigitSuffix s "_simp_" || hasDigitSuffix s "_sparseCasesOn_" then
          true
        else
          match env.find? p with
          | some (ConstantInfo.ctorInfo _) | some (ConstantInfo.recInfo _) => true
          | _ =>
            match Lean.getStructureInfo? env p with
            | some sinfo => sinfo.fieldNames.contains (Name.mkSimple s)
            | none => false
      | _ => false

/-- Compile-time unused-declaration hygiene lint checking that every `BMMGrid.*` declaration not
filtered by `isCompilerOrInductAux` (instances, inductive eliminators/projections, and compiler
auxiliaries) is reachable in the environment-level dependency closure of
`headlineTheoremRoots ++ auxiliaryRoots ++ linterHelperRoots`. -/
elab "#verify_no_unused_decls" : command => do
  let env ← getEnv
  let allRoots :=
    headlineTheoremRoots ++ auxiliaryRoots ++ linterHelperRoots ++
    [`BMMGrid.isCompilerOrInductAux]
  for r in allRoots do
    if !env.contains r then
      throwError "[Unused-Declaration Lint Failure] Root `{r}` not found in environment!"
  let mut visited : NameSet := {}
  let mut visitedUser : NameSet := {}
  let mut queue : Array Name := #[]
  for r in allRoots do
    visited := visited.insert r
    visitedUser := visitedUser.insert (toUserBMMName r)
    queue := queue.push r
  let mut idx := 0
  while idx < queue.size do
    let curr := queue[idx]!
    idx := idx + 1
    if let some cinfo := env.find? curr then
      let mut deps : Array Name := cinfo.type.getUsedConstants
      if let some v := cinfo.value? then
        deps := deps ++ v.getUsedConstants
      if let ConstantInfo.inductInfo iinfo := cinfo then
        for ctor in iinfo.ctors do
          deps := deps.push ctor
        if let some sinfo := Lean.getStructureInfo? env curr then
          for finfo in sinfo.fieldInfo do
            deps := deps.push finfo.projFn
      for u in deps do
        let uUser := toUserBMMName u
        if (`BMMGrid).isPrefixOf uUser && !visited.contains u then
          visited := visited.insert u
          visitedUser := visitedUser.insert uUser
          queue := queue.push u
  let mut checkedUser : NameSet := {}
  let mut unused : Array Name := #[]
  for (name, cinfo) in env.constants do
    let uname := toUserBMMName name
    if (`BMMGrid).isPrefixOf uname && !isCompilerOrInductAux env uname cinfo then
      checkedUser := checkedUser.insert uname
      if !visitedUser.contains uname then
        if !unused.contains uname then
          unused := unused.push uname
  let unusedSorted := unused.qsort (fun a b => a.toString < b.toString)
  if !unusedSorted.isEmpty then
    throwError m!"[Unused-Declaration Lint Failure] Found {unusedSorted.size} unreachable `BMMGrid.*` declarations: {unusedSorted.toList}"
  logInfo m!"[Unused-Declaration Lint Verified] All {checkedUser.size} non-exempt `BMMGrid.*` declarations (excluding instances, projections, and compiler/inductive helpers in `isCompilerOrInductAux`; {visitedUser.size} reachable `BMMGrid.*` symbols) are reachable from `headlineTheoremRoots`, `auxiliaryRoots`, or `linterHelperRoots`."

end BMMGrid
