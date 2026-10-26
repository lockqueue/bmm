import BMMGrid.CostMonadAndLinter

/-!
# Bitwise-Free Arithmetic Random-Access Machine (`BMMGrid/ArithRAM.lean`)

This module formalizes the concrete **Bitwise-Free Arithmetic RAM (`ArithRAM`)** model
specified in Section 3.1 and Appendix C (`\label{app:models}`) of `paper.tex`:
- **Instruction Set (`ArithStmt` / `ArithOp`)**: First-order inductive types over a finite control
  label type `Λ` (`[Fintype Λ]`) and finite register type `Reg` (`[Fintype Reg]`), supporting
  **only** small immediate constant load (`0, 1, 2`), register copy, indirect 1D memory load/store,
  $+, -, \times, \div, \bmod$, and control flow (`op`, `branchLt`, `branchEq`, `halt`).
- **Zero Bitwise Instructions & Zero Oracle Payloads**:
  `ArithStmt` / `ArithOp` have **no** bitwise instructions (`AND`, `OR`, `XOR`, shifts), **no**
  lookup-table oracles, and **no** function-valued payloads (`f : State → ℕ`).
- **Coupled Step-Count & Cook–Reckhow (1973) Log-Cost RAM Semantics**:
  - `ArithRAM.StepsInTimeAndLogCost M initCfg haltCfg t b` tracks exact transition steps `t` and
    cumulative logarithmic bit-operation cost `b` (`stepLogCost` / `opLogCost`).
  - `ArithRAM.EvalsToInLogCostTime M initCfg haltCfg t b` asserts `haltCfg.pc = none` together with
    `StepsInTimeAndLogCost M initCfg haltCfg t b`.
-/

namespace BMMGrid

/-- Small immediate constants `{0, 1, 2}` allowed in `ArithOp`. -/
inductive ImmConst : Type
  | zero : ImmConst
  | one  : ImmConst
  | two  : ImmConst
  deriving DecidableEq, Repr, Fintype

/-- Value of an `ImmConst`. -/
def ImmConst.toNat : ImmConst → ℕ
  | .zero => 0
  | .one  => 1
  | .two  => 2

/-- Elementary bitwise-free register/memory operation over a finite register set `Reg`.
Notice that this is a purely first-order datatype with **zero** function payloads and **zero**
bitwise operations (`AND`/`OR`/`XOR`/shifts), matching Appendix C (`\label{app:models}`). -/
inductive ArithOp (Reg : Type) : Type
  | loadImm  (dst : Reg) (c : ImmConst)
  | copy     (dst src : Reg)
  | loadInd  (dst addr : Reg)
  | storeInd (addr src : Reg)
  | add      (dst r₁ r₂ : Reg)
  | sub      (dst r₁ r₂ : Reg)
  | mul      (dst r₁ r₂ : Reg)
  | div      (dst r₁ r₂ : Reg)
  | mod      (dst r₁ r₂ : Reg)
  deriving DecidableEq, Repr

/-- Control-flow statement for a single label of an `ArithRAM` machine. -/
inductive ArithStmt (Λ Reg : Type) : Type
  | op       (o : ArithOp Reg) (next : Λ)
  | branchLt (r₁ r₂ : Reg) (targetTrue targetFalse : Λ)
  | branchEq (r₁ r₂ : Reg) (targetTrue targetFalse : Λ)
  | halt
  deriving DecidableEq, Repr

/-- A concrete Bitwise-Free Arithmetic RAM (`ArithRAM`) with finite control label set `Λ`,
finite register set `Reg`, entry label `initLabel`, primary input dimension register `reg0`, and
program `prog : Λ → ArithStmt Λ Reg`. -/
structure ArithRAM where
  Λ : Type
  Reg : Type
  [fintypeΛ : Fintype Λ]
  [fintypeReg : Fintype Reg]
  [decEqΛ : DecidableEq Λ]
  [decEqReg : DecidableEq Reg]
  initLabel : Λ
  reg0 : Reg
  prog : Λ → ArithStmt Λ Reg

attribute [instance] ArithRAM.fintypeΛ ArithRAM.fintypeReg ArithRAM.decEqΛ ArithRAM.decEqReg

namespace ArithRAM

/-- Configuration of an `ArithRAM` machine:
- `pc : Option M.Λ` (`none` when halted, `some lbl` when active),
- `regs : M.Reg → ℕ` (finite register file),
- `mem : ℕ → ℕ` (flat random-access memory). -/
structure Config (M : ArithRAM) where
  pc   : Option M.Λ
  regs : M.Reg → ℕ
  mem  : ℕ → ℕ

/-- Update a single register `r` in `regs : Reg → ℕ`. -/
def updateReg {Reg : Type} [DecidableEq Reg] (regs : Reg → ℕ) (r : Reg) (v : ℕ) (r' : Reg) : ℕ :=
  if r' = r then v else regs r'

/-- Update a single memory address `addr` in `mem : ℕ → ℕ`. -/
def updateMem (mem : ℕ → ℕ) (addr v : ℕ) (a : ℕ) : ℕ :=
  if a = addr then v else mem a

@[simp]
lemma updateReg_self {Reg : Type} [DecidableEq Reg] (regs : Reg → ℕ) (r : Reg) (v : ℕ) :
    updateReg regs r v r = v := by
  simp [updateReg]

@[simp]
lemma updateMem_self (mem : ℕ → ℕ) (addr v : ℕ) :
    updateMem mem addr v addr = v := by
  simp [updateMem]

/-- Execute a single elementary `ArithOp` on `(regs, mem)`. -/
def execOp {Reg : Type} [DecidableEq Reg] (o : ArithOp Reg)
    (regs : Reg → ℕ) (mem : ℕ → ℕ) : (Reg → ℕ) × (ℕ → ℕ) :=
  match o with
  | .loadImm dst c   => (updateReg regs dst c.toNat, mem)
  | .copy dst src    => (updateReg regs dst (regs src), mem)
  | .loadInd dst a   => (updateReg regs dst (mem (regs a)), mem)
  | .storeInd a src  => (regs, updateMem mem (regs a) (regs src))
  | .add dst r₁ r₂   => (updateReg regs dst (regs r₁ + regs r₂), mem)
  | .sub dst r₁ r₂   => (updateReg regs dst (regs r₁ - regs r₂), mem)
  | .mul dst r₁ r₂   => (updateReg regs dst (regs r₁ * regs r₂), mem)
  | .div dst r₁ r₂   => (updateReg regs dst (regs r₁ / regs r₂), mem)
  | .mod dst r₁ r₂   => (updateReg regs dst (regs r₁ % regs r₂), mem)

/-- Cook–Reckhow (1973) logarithmic bit-operation cost of a single `ArithOp`:
charges `bitLengthNat c.toNat` for `.loadImm`, `bitLengthNat (regs src) + 1` for `.copy`,
address plus value bit-lengths plus `1` for `.loadInd` / `.storeInd`, additive bit-lengths plus `1`
for `.add` / `.sub`, and multiplicative bit-lengths plus `1` for `.mul` / `.div` / `.mod`. -/
def opLogCost {Reg : Type} (o : ArithOp Reg) (regs : Reg → ℕ) (mem : ℕ → ℕ) : ℕ :=
  match o with
  | .loadImm _ c    => bitLengthNat c.toNat
  | .copy _ src     => bitLengthNat (regs src) + 1
  | .loadInd _ a    => bitLengthNat (regs a) + bitLengthNat (mem (regs a)) + 1
  | .storeInd a src => bitLengthNat (regs a) + bitLengthNat (regs src) + 1
  | .add _ r₁ r₂    => bitLengthNat (regs r₁) + bitLengthNat (regs r₂) + 1
  | .sub _ r₁ r₂    => bitLengthNat (regs r₁) + bitLengthNat (regs r₂) + 1
  | .mul _ r₁ r₂    => bitLengthNat (regs r₁) * bitLengthNat (regs r₂) + 1
  | .div _ r₁ r₂    => bitLengthNat (regs r₁) * bitLengthNat (regs r₂) + 1
  | .mod _ r₁ r₂    => bitLengthNat (regs r₁) * bitLengthNat (regs r₂) + 1

/-- Single-step transition function `M.step : Config M → Option (Config M)` used by
`StepsInTimeAndLogCost`. Returns `none` when `cfg.pc = none` (or transitions to `pc = none` on `halt`). -/
def step (M : ArithRAM) (cfg : Config M) : Option (Config M) :=
  match cfg.pc with
  | none => none
  | some lbl =>
    match M.prog lbl with
    | .op o next =>
      let (regs', mem') := execOp o cfg.regs cfg.mem
      some ⟨some next, regs', mem'⟩
    | .branchLt r₁ r₂ tTrue tFalse =>
      let next := if cfg.regs r₁ < cfg.regs r₂ then tTrue else tFalse
      some ⟨some next, cfg.regs, cfg.mem⟩
    | .branchEq r₁ r₂ tTrue tFalse =>
      let next := if cfg.regs r₁ = cfg.regs r₂ then tTrue else tFalse
      some ⟨some next, cfg.regs, cfg.mem⟩
    | .halt =>
      some ⟨none, cfg.regs, cfg.mem⟩

/-- Cook–Reckhow (1973) logarithmic bit-operation cost of a single transition step from `cfg`. -/
def stepLogCost (M : ArithRAM) (cfg : Config M) : ℕ :=
  match cfg.pc with
  | none => 0
  | some lbl =>
    match M.prog lbl with
    | .op o _ => opLogCost o cfg.regs cfg.mem
    | .branchLt r₁ r₂ _ _ => bitLengthNat (cfg.regs r₁) + bitLengthNat (cfg.regs r₂) + 1
    | .branchEq r₁ r₂ _ _ => bitLengthNat (cfg.regs r₁) + bitLengthNat (cfg.regs r₂) + 1
    | .halt => 1

/-- Coupled inductive relation `StepsInTimeAndLogCost M cfg haltCfg t b` asserting that `M`
transitions from `cfg` to `haltCfg` in `t` Unit-Cost Word RAM steps and `b`
Cook–Reckhow Log-Cost RAM bit operations. -/
inductive StepsInTimeAndLogCost (M : ArithRAM) : Config M → Config M → ℕ → ℕ → Prop
  | refl (cfg : Config M) :
      StepsInTimeAndLogCost M cfg cfg 0 0
  | step {cfg mid haltCfg : Config M} {t b : ℕ}
      (hstep : M.step cfg = some mid)
      (hrest : StepsInTimeAndLogCost M mid haltCfg t b) :
      StepsInTimeAndLogCost M cfg haltCfg (t + 1) (b + M.stepLogCost cfg)

/-- Halted evaluation relation `EvalsToInLogCostTime M initCfg haltCfg t b`:
`M` transitions from `initCfg` to a halted configuration `haltCfg` (`haltCfg.pc = none`) in
`t` Unit-Cost Word RAM steps and `b` Cook–Reckhow Log-Cost RAM bit operations. -/
def EvalsToInLogCostTime (M : ArithRAM) (initCfg haltCfg : Config M) (t b : ℕ) : Prop :=
  haltCfg.pc = none ∧ StepsInTimeAndLogCost M initCfg haltCfg t b

/-!
## Canonical Initial & Halted Memory Layouts for Triangle Detection and BMM
-/

private lemma pos_of_lt_mul_self {a n : ℕ} (h : a < n * n) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp at h
  · exact hn

/-- Encode three $n \times n$ binary matrices $A, B, C$ into flat RAM memory:
- `mem[0] = n`,
- `mem[1 + i*n + j] = if A i j then 1 else 0` for $0 \le i, j < n$,
- `mem[1 + n^2 + i*n + j] = if B i j then 1 else 0` for $0 \le i, j < n$,
- `mem[1 + 2*n^2 + i*n + j] = if C i j then 1 else 0` for $0 \le i, j < n$,
- `0` everywhere else (zero pre-populated tables or schedules). -/
def initTriDetMem (n : ℕ) (A B C : Fin n → Fin n → Bool) (addr : ℕ) : ℕ :=
  if addr = 0 then n
  else if hA : addr - 1 < n * n then
    have hn : 0 < n := pos_of_lt_mul_self hA
    let i : Fin n := ⟨(addr - 1) / n, Nat.div_lt_of_lt_mul hA⟩
    let j : Fin n := ⟨(addr - 1) % n, Nat.mod_lt _ hn⟩
    if A i j then 1 else 0
  else if hB : addr - 1 - n * n < n * n then
    have hn : 0 < n := pos_of_lt_mul_self hB
    let offset := addr - 1 - n * n
    let i : Fin n := ⟨offset / n, Nat.div_lt_of_lt_mul hB⟩
    let j : Fin n := ⟨offset % n, Nat.mod_lt _ hn⟩
    if B i j then 1 else 0
  else if hC : addr - 1 - 2 * (n * n) < n * n then
    have hn : 0 < n := pos_of_lt_mul_self hC
    let offset := addr - 1 - 2 * (n * n)
    let i : Fin n := ⟨offset / n, Nat.div_lt_of_lt_mul hC⟩
    let j : Fin n := ⟨offset % n, Nat.mod_lt _ hn⟩
    if C i j then 1 else 0
  else 0

/-- Encode two $n \times n$ binary matrices $A, B$ into flat RAM memory:
- `mem[0] = n`,
- `mem[1 + i*n + j] = if A i j then 1 else 0` for $0 \le i, j < n$,
- `mem[1 + n^2 + i*n + j] = if B i j then 1 else 0` for $0 \le i, j < n$,
- `0` everywhere else. -/
def initBMMMem (n : ℕ) (A B : Fin n → Fin n → Bool) (addr : ℕ) : ℕ :=
  if addr = 0 then n
  else if hA : addr - 1 < n * n then
    have hn : 0 < n := pos_of_lt_mul_self hA
    let i : Fin n := ⟨(addr - 1) / n, Nat.div_lt_of_lt_mul hA⟩
    let j : Fin n := ⟨(addr - 1) % n, Nat.mod_lt _ hn⟩
    if A i j then 1 else 0
  else if hB : addr - 1 - n * n < n * n then
    have hn : 0 < n := pos_of_lt_mul_self hB
    let offset := addr - 1 - n * n
    let i : Fin n := ⟨offset / n, Nat.div_lt_of_lt_mul hB⟩
    let j : Fin n := ⟨offset % n, Nat.mod_lt _ hn⟩
    if B i j then 1 else 0
  else 0

/-- Initial configuration of `M : ArithRAM` for Triangle Detection:
sets `regs M.reg0 = n`, `0` in all other registers, and `initTriDetMem n A B C` in memory. -/
def initTriDetConfig (M : ArithRAM) (n : ℕ) (A B C : Fin n → Fin n → Bool) : Config M :=
  { pc   := some M.initLabel
    regs := fun r => if r = M.reg0 then n else 0
    mem  := initTriDetMem n A B C }

/-- Initial configuration of `M : ArithRAM` for Boolean Matrix Multiplication:
sets `regs M.reg0 = n`, `0` in all other registers, and `initBMMMem n A B` in memory. -/
def initBMMConfig (M : ArithRAM) (n : ℕ) (A B : Fin n → Fin n → Bool) : Config M :=
  { pc   := some M.initLabel
    regs := fun r => if r = M.reg0 then n else 0
    mem  := initBMMMem n A B }

@[simp]
lemma initTriDetConfig_reg0 (M : ArithRAM) (n : ℕ) (A B C : Fin n → Fin n → Bool) :
    (initTriDetConfig M n A B C).regs M.reg0 = n := by
  simp [initTriDetConfig]

@[simp]
lemma initBMMConfig_reg0 (M : ArithRAM) (n : ℕ) (A B : Fin n → Fin n → Bool) :
    (initBMMConfig M n A B).regs M.reg0 = n := by
  simp [initBMMConfig]

theorem opLogCost_add_index_le {Reg : Type} (dst r₁ r₂ : Reg)
    (regs : Reg → ℕ) (mem : ℕ → ℕ) {n : ℕ}
    (hr₁ : regs r₁ ≤ n) (hr₂ : regs r₂ ≤ n) :
    opLogCost (.add dst r₁ r₂) regs mem ≤ 2 * bitLengthNat n + 3 := by
  dsimp only [opLogCost]
  have h1 := bitLengthNat_mono hr₁
  have h2 := bitLengthNat_mono hr₂
  omega

/-- Extract the Boolean matrix stored at base address `baseAddr` in `mem : ℕ → ℕ`. -/
def readBMatFromMem (n : ℕ) (mem : ℕ → ℕ) (baseAddr : ℕ) (i j : Fin n) : Bool :=
  decide (mem (baseAddr + i.val * n + j.val) ≠ 0)

private lemma fin_mul_add_lt {n : ℕ} (i j : Fin n) : i.val * n + j.val < n * n := by
  have hi : i.val + 1 ≤ n := i.isLt
  have hj : j.val < n := j.isLt
  have hmul : (i.val + 1) * n ≤ n * n := Nat.mul_le_mul_right n hi
  nlinarith

private lemma fin_mul_add_div {n : ℕ} (i j : Fin n) : (i.val * n + j.val) / n = i.val := by
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  rw [Nat.add_comm, Nat.add_mul_div_right j.val i.val hn, Nat.div_eq_of_lt j.isLt, Nat.zero_add]

private lemma fin_mul_add_mod {n : ℕ} (i j : Fin n) : (i.val * n + j.val) % n = j.val := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.isLt]

theorem initTriDetMem_A_eq (n : ℕ) (A B C : Fin n → Fin n → Bool) (i j : Fin n) :
    initTriDetMem n A B C (1 + i.val * n + j.val) = if A i j then 1 else 0 := by
  unfold initTriDetMem
  have hne0 : 1 + i.val * n + j.val ≠ 0 := by omega
  have hsub : 1 + i.val * n + j.val - 1 = i.val * n + j.val := by omega
  have hA : 1 + i.val * n + j.val - 1 < n * n := by
    rw [hsub]
    exact fin_mul_add_lt i j
  rw [if_neg hne0, dif_pos hA]
  dsimp only
  have hi_eq : (⟨(1 + i.val * n + j.val - 1) / n, Nat.div_lt_of_lt_mul hA⟩ : Fin n) = i := by
    ext
    dsimp only
    rw [hsub, fin_mul_add_div]
  have hj_eq : (⟨(1 + i.val * n + j.val - 1) % n,
      Nat.mod_lt _ (pos_of_lt_mul_self hA)⟩ : Fin n) = j := by
    ext
    dsimp only
    rw [hsub, fin_mul_add_mod]
  rw [hi_eq, hj_eq]

theorem initTriDetMem_B_eq (n : ℕ) (A B C : Fin n → Fin n → Bool) (i j : Fin n) :
    initTriDetMem n A B C (1 + n * n + i.val * n + j.val) = if B i j then 1 else 0 := by
  unfold initTriDetMem
  have hlt := fin_mul_add_lt i j
  have hne0 : 1 + n * n + i.val * n + j.val ≠ 0 := by omega
  have hnotA : ¬ (1 + n * n + i.val * n + j.val - 1 < n * n) := by omega
  have hsubB : 1 + n * n + i.val * n + j.val - 1 - n * n = i.val * n + j.val := by omega
  have hB : 1 + n * n + i.val * n + j.val - 1 - n * n < n * n := by
    rw [hsubB]
    exact hlt
  rw [if_neg hne0, dif_neg hnotA, dif_pos hB]
  dsimp only
  have hi_eq :
      (⟨(1 + n * n + i.val * n + j.val - 1 - n * n) / n, Nat.div_lt_of_lt_mul hB⟩ : Fin n) = i := by
    ext
    dsimp only
    rw [hsubB, fin_mul_add_div]
  have hj_eq :
      (⟨(1 + n * n + i.val * n + j.val - 1 - n * n) % n,
        Nat.mod_lt _ (pos_of_lt_mul_self hB)⟩ : Fin n) = j := by
    ext
    dsimp only
    rw [hsubB, fin_mul_add_mod]
  rw [hi_eq, hj_eq]

theorem initTriDetMem_C_eq (n : ℕ) (A B C : Fin n → Fin n → Bool) (i j : Fin n) :
    initTriDetMem n A B C (1 + 2 * (n * n) + i.val * n + j.val) = if C i j then 1 else 0 := by
  unfold initTriDetMem
  have hlt := fin_mul_add_lt i j
  have hne0 : 1 + 2 * (n * n) + i.val * n + j.val ≠ 0 := by omega
  have hnotA : ¬ (1 + 2 * (n * n) + i.val * n + j.val - 1 < n * n) := by omega
  have hnotB : ¬ (1 + 2 * (n * n) + i.val * n + j.val - 1 - n * n < n * n) := by omega
  have hsubC : 1 + 2 * (n * n) + i.val * n + j.val - 1 - 2 * (n * n) = i.val * n + j.val := by
    omega
  have hC : 1 + 2 * (n * n) + i.val * n + j.val - 1 - 2 * (n * n) < n * n := by
    rw [hsubC]
    exact hlt
  rw [if_neg hne0, dif_neg hnotA, dif_neg hnotB, dif_pos hC]
  dsimp only
  have hi_eq :
      (⟨(1 + 2 * (n * n) + i.val * n + j.val - 1 - 2 * (n * n)) / n,
        Nat.div_lt_of_lt_mul hC⟩ : Fin n) = i := by
    ext
    dsimp only
    rw [hsubC, fin_mul_add_div]
  have hj_eq :
      (⟨(1 + 2 * (n * n) + i.val * n + j.val - 1 - 2 * (n * n)) % n,
        Nat.mod_lt _ (pos_of_lt_mul_self hC)⟩ : Fin n) = j := by
    ext
    dsimp only
    rw [hsubC, fin_mul_add_mod]
  rw [hi_eq, hj_eq]

theorem initBMMMem_A_eq (n : ℕ) (A B : Fin n → Fin n → Bool) (i j : Fin n) :
    initBMMMem n A B (1 + i.val * n + j.val) = if A i j then 1 else 0 := by
  unfold initBMMMem
  have hne0 : 1 + i.val * n + j.val ≠ 0 := by omega
  have hsub : 1 + i.val * n + j.val - 1 = i.val * n + j.val := by omega
  have hA : 1 + i.val * n + j.val - 1 < n * n := by
    rw [hsub]
    exact fin_mul_add_lt i j
  rw [if_neg hne0, dif_pos hA]
  dsimp only
  have hi_eq : (⟨(1 + i.val * n + j.val - 1) / n, Nat.div_lt_of_lt_mul hA⟩ : Fin n) = i := by
    ext
    dsimp only
    rw [hsub, fin_mul_add_div]
  have hj_eq : (⟨(1 + i.val * n + j.val - 1) % n,
      Nat.mod_lt _ (pos_of_lt_mul_self hA)⟩ : Fin n) = j := by
    ext
    dsimp only
    rw [hsub, fin_mul_add_mod]
  rw [hi_eq, hj_eq]

theorem initBMMMem_B_eq (n : ℕ) (A B : Fin n → Fin n → Bool) (i j : Fin n) :
    initBMMMem n A B (1 + n * n + i.val * n + j.val) = if B i j then 1 else 0 := by
  unfold initBMMMem
  have hlt := fin_mul_add_lt i j
  have hne0 : 1 + n * n + i.val * n + j.val ≠ 0 := by omega
  have hnotA : ¬ (1 + n * n + i.val * n + j.val - 1 < n * n) := by omega
  have hsubB : 1 + n * n + i.val * n + j.val - 1 - n * n = i.val * n + j.val := by omega
  have hB : 1 + n * n + i.val * n + j.val - 1 - n * n < n * n := by
    rw [hsubB]
    exact hlt
  rw [if_neg hne0, dif_neg hnotA, dif_pos hB]
  dsimp only
  have hi_eq :
      (⟨(1 + n * n + i.val * n + j.val - 1 - n * n) / n, Nat.div_lt_of_lt_mul hB⟩ : Fin n) = i := by
    ext
    dsimp only
    rw [hsubB, fin_mul_add_div]
  have hj_eq :
      (⟨(1 + n * n + i.val * n + j.val - 1 - n * n) % n,
        Nat.mod_lt _ (pos_of_lt_mul_self hB)⟩ : Fin n) = j := by
    ext
    dsimp only
    rw [hsubB, fin_mul_add_mod]
  rw [hi_eq, hj_eq]

private lemma decide_ite_one_zero_ne_zero (b : Bool) :
    decide ((if b then (1 : ℕ) else 0) ≠ 0) = b := by
  cases b <;> rfl

@[simp]
theorem readBMatFromMem_initTriDetMem_A (n : ℕ) (A B C : Fin n → Fin n → Bool) (i j : Fin n) :
    readBMatFromMem n (initTriDetMem n A B C) 1 i j = A i j := by
  unfold readBMatFromMem
  rw [initTriDetMem_A_eq, decide_ite_one_zero_ne_zero]

@[simp]
theorem readBMatFromMem_initTriDetMem_B (n : ℕ) (A B C : Fin n → Fin n → Bool) (i j : Fin n) :
    readBMatFromMem n (initTriDetMem n A B C) (1 + n * n) i j = B i j := by
  unfold readBMatFromMem
  rw [initTriDetMem_B_eq, decide_ite_one_zero_ne_zero]

@[simp]
theorem readBMatFromMem_initTriDetMem_C (n : ℕ) (A B C : Fin n → Fin n → Bool) (i j : Fin n) :
    readBMatFromMem n (initTriDetMem n A B C) (1 + 2 * (n * n)) i j = C i j := by
  unfold readBMatFromMem
  rw [initTriDetMem_C_eq, decide_ite_one_zero_ne_zero]

@[simp]
theorem readBMatFromMem_initBMMMem_A (n : ℕ) (A B : Fin n → Fin n → Bool) (i j : Fin n) :
    readBMatFromMem n (initBMMMem n A B) 1 i j = A i j := by
  unfold readBMatFromMem
  rw [initBMMMem_A_eq, decide_ite_one_zero_ne_zero]

@[simp]
theorem readBMatFromMem_initBMMMem_B (n : ℕ) (A B : Fin n → Fin n → Bool) (i j : Fin n) :
    readBMatFromMem n (initBMMMem n A B) (1 + n * n) i j = B i j := by
  unfold readBMatFromMem
  rw [initBMMMem_B_eq, decide_ite_one_zero_ne_zero]

/-!
## Concrete `ArithRAM` Micro-Kernels
-/

/-- Concrete 3-label, 3-register `ArithRAM` executing an indirect memory load `.loadInd`
from `mem[0]` into register `1`, adding registers `0` and `1` into register `2`, and halting. -/
@[reducible]
def ramInitAndAdd : ArithRAM where
  Λ := Fin 3
  Reg := Fin 3
  initLabel := (0 : Fin 3)
  reg0 := (0 : Fin 3)
  prog := fun l =>
    if l = (0 : Fin 3) then .op (.loadInd (1 : Fin 3) (2 : Fin 3)) (1 : Fin 3)
    else if l = (1 : Fin 3) then .op (.add (2 : Fin 3) (0 : Fin 3) (1 : Fin 3)) (2 : Fin 3)
    else .halt

theorem ramInitAndAdd_evalsToInLogCostTime_of_mem (n : ℕ) (mem : ℕ → ℕ) (hmem0 : mem 0 = n) :
    let r0 : Fin 3 → ℕ := fun r => if r = (0 : Fin 3) then n else 0
    let initCfg : Config ramInitAndAdd := ⟨some (0 : Fin 3), r0, mem⟩
    ∃ (haltCfg : Config ramInitAndAdd) (b : ℕ),
      b ≤ 3 * bitLengthNat n + 4 ∧
      haltCfg.regs (2 : Fin 3) = n + n ∧
      EvalsToInLogCostTime ramInitAndAdd initCfg haltCfg 3 b := by
  dsimp only
  let r0 : Fin 3 → ℕ := fun r => if r = (0 : Fin 3) then n else 0
  let r1 : Fin 3 → ℕ := updateReg r0 (1 : Fin 3) (mem 0)
  let r2 : Fin 3 → ℕ := updateReg r1 (2 : Fin 3) (n + mem 0)
  have hstep1 : ramInitAndAdd.step ⟨some (0 : Fin 3), r0, mem⟩ =
      some ⟨some (1 : Fin 3), r1, mem⟩ := rfl
  have hstep2 : ramInitAndAdd.step ⟨some (1 : Fin 3), r1, mem⟩ =
      some ⟨some (2 : Fin 3), r2, mem⟩ := rfl
  have hstep3 : ramInitAndAdd.step ⟨some (2 : Fin 3), r2, mem⟩ =
      some ⟨none, r2, mem⟩ := rfl
  have htr0 := StepsInTimeAndLogCost.refl (M := ramInitAndAdd) ⟨none, r2, mem⟩
  have htr1 := StepsInTimeAndLogCost.step hstep3 htr0
  have htr2 := StepsInTimeAndLogCost.step hstep2 htr1
  have htr3 := StepsInTimeAndLogCost.step hstep1 htr2
  refine ⟨⟨none, r2, mem⟩, _, ?_, ?_, ⟨rfl, htr3⟩⟩
  · change 0 + 1 + (bitLengthNat n + bitLengthNat (mem 0) + 1) +
        (bitLengthNat 0 + bitLengthNat (mem 0) + 1) ≤
      3 * bitLengthNat n + 4
    have hb0 : bitLengthNat 0 = 1 := rfl
    rw [hb0, hmem0]
    omega
  · change updateReg r1 (2 : Fin 3) (n + mem 0) (2 : Fin 3) = n + n
    rw [updateReg_self, hmem0]

theorem ramInitAndAdd_evalsToInLogCostTime_triDet (n : ℕ) (A B C : Fin n → Fin n → Bool) :
    ∃ (haltCfg : Config ramInitAndAdd) (b : ℕ),
      b ≤ 3 * bitLengthNat n + 4 ∧
      haltCfg.regs (2 : Fin 3) = n + n ∧
      EvalsToInLogCostTime ramInitAndAdd
        (initTriDetConfig ramInitAndAdd n A B C) haltCfg 3 b :=
  ramInitAndAdd_evalsToInLogCostTime_of_mem n (initTriDetMem n A B C) rfl

theorem ramInitAndAdd_evalsToInLogCostTime_bmm (n : ℕ) (A B : Fin n → Fin n → Bool) :
    ∃ (haltCfg : Config ramInitAndAdd) (b : ℕ),
      b ≤ 3 * bitLengthNat n + 4 ∧
      haltCfg.regs (2 : Fin 3) = n + n ∧
      EvalsToInLogCostTime ramInitAndAdd
        (initBMMConfig ramInitAndAdd n A B) haltCfg 3 b :=
  ramInitAndAdd_evalsToInLogCostTime_of_mem n (initBMMMem n A B) rfl

/-- Concrete 5-label, 6-register `ArithRAM` computing the flat 2D matrix address
`baseAddr + i * n + j` (from `reg 0 = n`, `reg 1 = baseAddr`, `reg 2 = i`, `reg 3 = j` into
`reg 4`) via `.mul`, `.add`, `.add`, loading `mem[reg 4]` into `reg 5` via `.loadInd`, and halting. -/
@[reducible]
def ramReadMatrixEntry : ArithRAM where
  Λ := Fin 5
  Reg := Fin 6
  initLabel := (0 : Fin 5)
  reg0 := (0 : Fin 6)
  prog := fun l =>
    if l = (0 : Fin 5) then .op (.mul (4 : Fin 6) (2 : Fin 6) (0 : Fin 6)) (1 : Fin 5)
    else if l = (1 : Fin 5) then .op (.add (4 : Fin 6) (4 : Fin 6) (3 : Fin 6)) (2 : Fin 5)
    else if l = (2 : Fin 5) then .op (.add (4 : Fin 6) (1 : Fin 6) (4 : Fin 6)) (3 : Fin 5)
    else if l = (3 : Fin 5) then .op (.loadInd (5 : Fin 6) (4 : Fin 6)) (4 : Fin 5)
    else .halt

lemma bitLengthNat_le_of_le_four_mul_sq {x n : ℕ} (hx : x ≤ 4 * (n * n)) :
    bitLengthNat x ≤ 2 * bitLengthNat n + 3 := by
  unfold bitLengthNat
  have hn_lt : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hx_le : x ≤ 2 ^ ((Nat.log 2 n + 1) + (Nat.log 2 n + 1) + 2) := by
    have hpow : 2 ^ ((Nat.log 2 n + 1) + (Nat.log 2 n + 1) + 2) =
        4 * (2 ^ (Nat.log 2 n + 1) * 2 ^ (Nat.log 2 n + 1)) := by
      rw [Nat.pow_add, Nat.pow_add]
      ring
    rw [hpow]
    have hmul : n * n ≤ 2 ^ (Nat.log 2 n + 1) * 2 ^ (Nat.log 2 n + 1) :=
      Nat.mul_le_mul (le_of_lt hn_lt) (le_of_lt hn_lt)
    omega
  have hlog : Nat.log 2 x ≤ (Nat.log 2 n + 1) + (Nat.log 2 n + 1) + 2 :=
    (Nat.log_mono_right hx_le).trans_eq (Nat.log_pow (by norm_num) _)
  omega

/-- Initial configuration of `ramReadMatrixEntry` for reading `(i, j)` at `baseAddr` in `mem`. -/
def initReadMatrixEntryConfig (n baseAddr : ℕ) (i j : Fin n) (mem : ℕ → ℕ) :
    Config ramReadMatrixEntry :=
  { pc   := some (0 : Fin 5)
    regs := fun r =>
      if r = (0 : Fin 6) then n
      else if r = (1 : Fin 6) then baseAddr
      else if r = (2 : Fin 6) then i.val
      else if r = (3 : Fin 6) then j.val
      else 0
    mem  := mem }

theorem ramReadMatrixEntry_evalsToInLogCostTime (n baseAddr : ℕ) (i j : Fin n) (mem : ℕ → ℕ)
    (hbase : baseAddr ≤ 2 * (n * n) + 1)
    (hmem : mem (baseAddr + i.val * n + j.val) ≤ 1) :
    ∃ (haltCfg : Config ramReadMatrixEntry) (b : ℕ),
      b ≤ 12 * (bitLengthNat n + 4) ^ 2 ∧
      haltCfg.regs (5 : Fin 6) = mem (baseAddr + i.val * n + j.val) ∧
      EvalsToInLogCostTime ramReadMatrixEntry
        (initReadMatrixEntryConfig n baseAddr i j mem) haltCfg 5 b := by
  let r0 : Fin 6 → ℕ := (initReadMatrixEntryConfig n baseAddr i j mem).regs
  let r1 : Fin 6 → ℕ := updateReg r0 (4 : Fin 6) (i.val * n)
  let r2 : Fin 6 → ℕ := updateReg r1 (4 : Fin 6) (i.val * n + j.val)
  let r3 : Fin 6 → ℕ := updateReg r2 (4 : Fin 6) (baseAddr + (i.val * n + j.val))
  let r4 : Fin 6 → ℕ := updateReg r3 (5 : Fin 6) (mem (baseAddr + (i.val * n + j.val)))
  have hstep1 : ramReadMatrixEntry.step ⟨some (0 : Fin 5), r0, mem⟩ =
      some ⟨some (1 : Fin 5), r1, mem⟩ := rfl
  have hstep2 : ramReadMatrixEntry.step ⟨some (1 : Fin 5), r1, mem⟩ =
      some ⟨some (2 : Fin 5), r2, mem⟩ := rfl
  have hstep3 : ramReadMatrixEntry.step ⟨some (2 : Fin 5), r2, mem⟩ =
      some ⟨some (3 : Fin 5), r3, mem⟩ := rfl
  have hstep4 : ramReadMatrixEntry.step ⟨some (3 : Fin 5), r3, mem⟩ =
      some ⟨some (4 : Fin 5), r4, mem⟩ := rfl
  have hstep5 : ramReadMatrixEntry.step ⟨some (4 : Fin 5), r4, mem⟩ =
      some ⟨none, r4, mem⟩ := rfl
  have htr0 := StepsInTimeAndLogCost.refl (M := ramReadMatrixEntry) ⟨none, r4, mem⟩
  have htr1 := StepsInTimeAndLogCost.step hstep5 htr0
  have htr2 := StepsInTimeAndLogCost.step hstep4 htr1
  have htr3 := StepsInTimeAndLogCost.step hstep3 htr2
  have htr4 := StepsInTimeAndLogCost.step hstep2 htr3
  have htr5 := StepsInTimeAndLogCost.step hstep1 htr4
  have haddr_eq : baseAddr + (i.val * n + j.val) = baseAddr + i.val * n + j.val := by omega
  refine ⟨⟨none, r4, mem⟩, _, ?_, ?_, ⟨rfl, htr5⟩⟩
  · change 0 + 1 +
        (bitLengthNat (baseAddr + (i.val * n + j.val)) +
          bitLengthNat (mem (baseAddr + (i.val * n + j.val))) + 1) +
        (bitLengthNat baseAddr + bitLengthNat (i.val * n + j.val) + 1) +
        (bitLengthNat (i.val * n) + bitLengthNat j.val + 1) +
        (bitLengthNat i.val * bitLengthNat n + 1) ≤
      12 * (bitLengthNat n + 4) ^ 2
    have hlt := fin_mul_add_lt i j
    have hi_le : i.val ≤ n := le_of_lt i.isLt
    have hbi : bitLengthNat i.val ≤ bitLengthNat n := bitLengthNat_mono hi_le
    have hbi_mul : bitLengthNat i.val * bitLengthNat n ≤ bitLengthNat n * bitLengthNat n :=
      Nat.mul_le_mul_right _ hbi
    have hbj : bitLengthNat j.val ≤ 2 * bitLengthNat n + 3 :=
      bitLengthNat_le_of_le_four_mul_sq (by omega)
    have hbin : bitLengthNat (i.val * n) ≤ 2 * bitLengthNat n + 3 :=
      bitLengthNat_le_of_le_four_mul_sq (by omega)
    have hbinj : bitLengthNat (i.val * n + j.val) ≤ 2 * bitLengthNat n + 3 :=
      bitLengthNat_le_of_le_four_mul_sq (by omega)
    have hbb : bitLengthNat baseAddr ≤ 2 * bitLengthNat n + 3 :=
      bitLengthNat_le_of_le_four_mul_sq (by omega)
    have hbaddr : bitLengthNat (baseAddr + (i.val * n + j.val)) ≤ 2 * bitLengthNat n + 3 :=
      bitLengthNat_le_of_le_four_mul_sq (by omega)
    have hbmem : bitLengthNat (mem (baseAddr + (i.val * n + j.val))) ≤ 2 * bitLengthNat n + 3 := by
      rw [haddr_eq]
      exact bitLengthNat_le_of_le_four_mul_sq (by omega)
    nlinarith
  · change updateReg r3 (5 : Fin 6) (mem (baseAddr + (i.val * n + j.val))) (5 : Fin 6) =
      mem (baseAddr + i.val * n + j.val)
    rw [updateReg_self, haddr_eq]

theorem ramReadMatrixEntry_triDet_A (n : ℕ) (A B C : Fin n → Fin n → Bool) (i j : Fin n) :
    ∃ (haltCfg : Config ramReadMatrixEntry) (b : ℕ),
      b ≤ 12 * (bitLengthNat n + 4) ^ 2 ∧
      haltCfg.regs (5 : Fin 6) = (if A i j then 1 else 0) ∧
      EvalsToInLogCostTime ramReadMatrixEntry
        (initReadMatrixEntryConfig n 1 i j (initTriDetMem n A B C)) haltCfg 5 b := by
  have hmem_eq := initTriDetMem_A_eq n A B C i j
  have hmem_le : initTriDetMem n A B C (1 + i.val * n + j.val) ≤ 1 := by
    rw [hmem_eq]; split_ifs <;> omega
  rcases ramReadMatrixEntry_evalsToInLogCostTime n 1 i j (initTriDetMem n A B C)
    (by omega) hmem_le with ⟨haltCfg, b, hb, hreg5, heval⟩
  rw [hmem_eq] at hreg5
  exact ⟨haltCfg, b, hb, hreg5, heval⟩

theorem ramReadMatrixEntry_bmm_A (n : ℕ) (A B : Fin n → Fin n → Bool) (i j : Fin n) :
    ∃ (haltCfg : Config ramReadMatrixEntry) (b : ℕ),
      b ≤ 12 * (bitLengthNat n + 4) ^ 2 ∧
      haltCfg.regs (5 : Fin 6) = (if A i j then 1 else 0) ∧
      EvalsToInLogCostTime ramReadMatrixEntry
        (initReadMatrixEntryConfig n 1 i j (initBMMMem n A B)) haltCfg 5 b := by
  have hmem_eq := initBMMMem_A_eq n A B i j
  have hmem_le : initBMMMem n A B (1 + i.val * n + j.val) ≤ 1 := by
    rw [hmem_eq]; split_ifs <;> omega
  rcases ramReadMatrixEntry_evalsToInLogCostTime n 1 i j (initBMMMem n A B)
    (by omega) hmem_le with ⟨haltCfg, b, hb, hreg5, heval⟩
  rw [hmem_eq] at hreg5
  exact ⟨haltCfg, b, hb, hreg5, heval⟩

/-- Concrete 5-label, 6-register `ArithRAM` computing the flat 2D matrix address
`baseAddr + i * n + j` (from `reg 0 = n`, `reg 1 = baseAddr`, `reg 2 = i`, `reg 3 = j` into
`reg 4`) via `.mul`, `.add`, `.add`, storing `reg 5` (`val`) into `mem[reg 4]` via `.storeInd`, and
halting. -/
@[reducible]
def ramWriteMatrixEntry : ArithRAM where
  Λ := Fin 5
  Reg := Fin 6
  initLabel := (0 : Fin 5)
  reg0 := (0 : Fin 6)
  prog := fun l =>
    if l = (0 : Fin 5) then .op (.mul (4 : Fin 6) (2 : Fin 6) (0 : Fin 6)) (1 : Fin 5)
    else if l = (1 : Fin 5) then .op (.add (4 : Fin 6) (4 : Fin 6) (3 : Fin 6)) (2 : Fin 5)
    else if l = (2 : Fin 5) then .op (.add (4 : Fin 6) (1 : Fin 6) (4 : Fin 6)) (3 : Fin 5)
    else if l = (3 : Fin 5) then .op (.storeInd (4 : Fin 6) (5 : Fin 6)) (4 : Fin 5)
    else .halt

/-- Initial configuration of `ramWriteMatrixEntry` for writing `val` to `(i, j)` at `baseAddr` in `mem`. -/
def initWriteMatrixEntryConfig (n baseAddr : ℕ) (i j : Fin n) (val : ℕ) (mem : ℕ → ℕ) :
    Config ramWriteMatrixEntry :=
  { pc   := some (0 : Fin 5)
    regs := fun r =>
      if r = (0 : Fin 6) then n
      else if r = (1 : Fin 6) then baseAddr
      else if r = (2 : Fin 6) then i.val
      else if r = (3 : Fin 6) then j.val
      else if r = (5 : Fin 6) then val
      else 0
    mem  := mem }

theorem ramWriteMatrixEntry_evalsToInLogCostTime (n baseAddr : ℕ) (i j : Fin n) (val : ℕ)
    (mem : ℕ → ℕ)
    (hbase : baseAddr ≤ 2 * (n * n) + 1)
    (hval : val ≤ 1) :
    ∃ (haltCfg : Config ramWriteMatrixEntry) (b : ℕ),
      b ≤ 12 * (bitLengthNat n + 4) ^ 2 ∧
      haltCfg.mem = updateMem mem (baseAddr + i.val * n + j.val) val ∧
      EvalsToInLogCostTime ramWriteMatrixEntry
        (initWriteMatrixEntryConfig n baseAddr i j val mem) haltCfg 5 b := by
  let r0 : Fin 6 → ℕ := (initWriteMatrixEntryConfig n baseAddr i j val mem).regs
  let r1 : Fin 6 → ℕ := updateReg r0 (4 : Fin 6) (i.val * n)
  let r2 : Fin 6 → ℕ := updateReg r1 (4 : Fin 6) (i.val * n + j.val)
  let r3 : Fin 6 → ℕ := updateReg r2 (4 : Fin 6) (baseAddr + (i.val * n + j.val))
  let mem4 : ℕ → ℕ := updateMem mem (baseAddr + (i.val * n + j.val)) val
  have hstep1 : ramWriteMatrixEntry.step ⟨some (0 : Fin 5), r0, mem⟩ =
      some ⟨some (1 : Fin 5), r1, mem⟩ := rfl
  have hstep2 : ramWriteMatrixEntry.step ⟨some (1 : Fin 5), r1, mem⟩ =
      some ⟨some (2 : Fin 5), r2, mem⟩ := rfl
  have hstep3 : ramWriteMatrixEntry.step ⟨some (2 : Fin 5), r2, mem⟩ =
      some ⟨some (3 : Fin 5), r3, mem⟩ := rfl
  have hstep4 : ramWriteMatrixEntry.step ⟨some (3 : Fin 5), r3, mem⟩ =
      some ⟨some (4 : Fin 5), r3, mem4⟩ := rfl
  have hstep5 : ramWriteMatrixEntry.step ⟨some (4 : Fin 5), r3, mem4⟩ =
      some ⟨none, r3, mem4⟩ := rfl
  have htr0 := StepsInTimeAndLogCost.refl (M := ramWriteMatrixEntry) ⟨none, r3, mem4⟩
  have htr1 := StepsInTimeAndLogCost.step hstep5 htr0
  have htr2 := StepsInTimeAndLogCost.step hstep4 htr1
  have htr3 := StepsInTimeAndLogCost.step hstep3 htr2
  have htr4 := StepsInTimeAndLogCost.step hstep2 htr3
  have htr5 := StepsInTimeAndLogCost.step hstep1 htr4
  have haddr_eq : baseAddr + (i.val * n + j.val) = baseAddr + i.val * n + j.val := by omega
  refine ⟨⟨none, r3, mem4⟩, _, ?_, ?_, ⟨rfl, htr5⟩⟩
  · change 0 + 1 +
        (bitLengthNat (baseAddr + (i.val * n + j.val)) + bitLengthNat val + 1) +
        (bitLengthNat baseAddr + bitLengthNat (i.val * n + j.val) + 1) +
        (bitLengthNat (i.val * n) + bitLengthNat j.val + 1) +
        (bitLengthNat i.val * bitLengthNat n + 1) ≤
      12 * (bitLengthNat n + 4) ^ 2
    have hlt := fin_mul_add_lt i j
    have hi_le : i.val ≤ n := le_of_lt i.isLt
    have hbi : bitLengthNat i.val ≤ bitLengthNat n := bitLengthNat_mono hi_le
    have hbi_mul : bitLengthNat i.val * bitLengthNat n ≤ bitLengthNat n * bitLengthNat n :=
      Nat.mul_le_mul_right _ hbi
    have hbj : bitLengthNat j.val ≤ 2 * bitLengthNat n + 3 :=
      bitLengthNat_le_of_le_four_mul_sq (by omega)
    have hbin : bitLengthNat (i.val * n) ≤ 2 * bitLengthNat n + 3 :=
      bitLengthNat_le_of_le_four_mul_sq (by omega)
    have hbinj : bitLengthNat (i.val * n + j.val) ≤ 2 * bitLengthNat n + 3 :=
      bitLengthNat_le_of_le_four_mul_sq (by omega)
    have hbb : bitLengthNat baseAddr ≤ 2 * bitLengthNat n + 3 :=
      bitLengthNat_le_of_le_four_mul_sq (by omega)
    have hbaddr : bitLengthNat (baseAddr + (i.val * n + j.val)) ≤ 2 * bitLengthNat n + 3 :=
      bitLengthNat_le_of_le_four_mul_sq (by omega)
    have hbval : bitLengthNat val ≤ 2 * bitLengthNat n + 3 :=
      bitLengthNat_le_of_le_four_mul_sq (by omega)
    nlinarith
  · dsimp only [mem4]
    rw [haddr_eq]

theorem readBMatFromMem_updateMem_zero (n baseAddr : ℕ) (mem : ℕ → ℕ) (i₀ j₀ i j : Fin n) :
    readBMatFromMem n (updateMem mem (baseAddr + i₀.val * n + j₀.val) 0) baseAddr i j =
      (if i = i₀ ∧ j = j₀ then false else readBMatFromMem n mem baseAddr i j) := by
  unfold readBMatFromMem updateMem
  by_cases h : i = i₀ ∧ j = j₀
  · rcases h with ⟨rfl, rfl⟩
    simp
  · have hne : baseAddr + i.val * n + j.val ≠ baseAddr + i₀.val * n + j₀.val := by
      intro heq
      have h1 : i.val * n + j.val = i₀.val * n + j₀.val := by omega
      have hi : i.val = i₀.val := by
        rw [← fin_mul_add_div i j, h1, fin_mul_add_div i₀ j₀]
      have hj : j.val = j₀.val := by
        rw [← fin_mul_add_mod i j, h1, fin_mul_add_mod i₀ j₀]
      exact h ⟨Fin.ext hi, Fin.ext hj⟩
    simp [h, hne]

@[simp]
theorem readBMatFromMem_updateMem_self_bool (n baseAddr : ℕ) (mem : ℕ → ℕ)
    (i j : Fin n) (b : Bool) :
    readBMatFromMem n (updateMem mem (baseAddr + i.val * n + j.val) (if b then 1 else 0))
      baseAddr i j = b := by
  unfold readBMatFromMem
  rw [updateMem_self, decide_ite_one_zero_ne_zero]

/-- Clear a single matrix entry `(p.1, p.2)` at `baseAddr` in 1D RAM memory `mem : ℕ → ℕ`. -/
def clearEntryMem (n baseAddr : ℕ) (mem : ℕ → ℕ) (p : Fin n × Fin n) : ℕ → ℕ :=
  updateMem mem (baseAddr + p.1.val * n + p.2.val) 0

/-- Sequentially clear a list of matrix entries `entries : List (Fin n × Fin n)` in 1D RAM memory. -/
def clearEntriesMem (n baseAddr : ℕ) (mem : ℕ → ℕ) (entries : List (Fin n × Fin n)) : ℕ → ℕ :=
  entries.foldl (clearEntryMem n baseAddr) mem

lemma clearEntriesMem_le_of_le (n baseAddr : ℕ) (mem : ℕ → ℕ)
    (entries : List (Fin n × Fin n)) {addr : ℕ} (hmem : mem addr ≤ 1) :
    clearEntriesMem n baseAddr mem entries addr ≤ 1 := by
  unfold clearEntriesMem
  induction entries generalizing mem with
  | nil => exact hmem
  | cons p tl ih =>
    simp only [List.foldl_cons]
    refine ih (clearEntryMem n baseAddr mem p) ?_
    unfold clearEntryMem updateMem
    split_ifs <;> omega

/-- Reading from `clearEntriesMem` after clearing any number $K$ of entries in 1D RAM memory
via `ramReadMatrixEntry` still executes in **5 `ArithRAM` steps and at most
`12 * (bitLengthNat n + 4) ^ 2` Cook–Reckhow bit operations**, independent of $K$. -/
theorem ramReadMatrixEntry_after_clears_evalsToInLogCostTime
    (n : ℕ) (A B C : Fin n → Fin n → Bool)
    (entries : List (Fin n × Fin n)) (i j : Fin n) :
    let mem' := clearEntriesMem n (1 + 2 * (n * n)) (initTriDetMem n A B C) entries
    ∃ (haltCfg : Config ramReadMatrixEntry) (b : ℕ),
      b ≤ 12 * (bitLengthNat n + 4) ^ 2 ∧
      haltCfg.regs (5 : Fin 6) =
        (if readBMatFromMem n mem' (1 + 2 * (n * n)) i j then 1 else 0) ∧
      EvalsToInLogCostTime ramReadMatrixEntry
        (initReadMatrixEntryConfig n (1 + 2 * (n * n)) i j mem') haltCfg 5 b := by
  dsimp only
  set baseAddr := 1 + 2 * (n * n)
  set mem₀ := initTriDetMem n A B C
  set mem' := clearEntriesMem n baseAddr mem₀ entries
  have hmem₀_eq : mem₀ (baseAddr + i.val * n + j.val) = if C i j then 1 else 0 :=
    initTriDetMem_C_eq n A B C i j
  have hmem₀_le : mem₀ (baseAddr + i.val * n + j.val) ≤ 1 := by
    rw [hmem₀_eq]; split_ifs <;> omega
  have hmem'_le : mem' (baseAddr + i.val * n + j.val) ≤ 1 :=
    clearEntriesMem_le_of_le n baseAddr mem₀ entries hmem₀_le
  rcases ramReadMatrixEntry_evalsToInLogCostTime n baseAddr i j mem'
    (by omega) hmem'_le with ⟨haltCfg, b, hb, hreg5, heval⟩
  refine ⟨haltCfg, b, hb, ?_, heval⟩
  rw [hreg5]
  unfold readBMatFromMem
  have h01 : mem' (baseAddr + i.val * n + j.val) = 0 ∨
      mem' (baseAddr + i.val * n + j.val) = 1 := by omega
  rcases h01 with h | h <;> simp [h]

/-- Concrete 6-label, 7-register `ArithRAM` that loads `mem[reg 0]`, `mem[reg 1]`, and
`mem[reg 2]` (holding the 1D addresses of $A[i, j]$, $B[j, k]$, and $C[i, k]$) into registers
`3, 4, 5` via `.loadInd`, multiplies them via `.mul` into `reg 6`, and halts. -/
@[reducible]
def ramCheckTriangleTriple : ArithRAM where
  Λ := Fin 6
  Reg := Fin 7
  initLabel := (0 : Fin 6)
  reg0 := (0 : Fin 7)
  prog := fun l =>
    if l = (0 : Fin 6) then .op (.loadInd (3 : Fin 7) (0 : Fin 7)) (1 : Fin 6)
    else if l = (1 : Fin 6) then .op (.loadInd (4 : Fin 7) (1 : Fin 7)) (2 : Fin 6)
    else if l = (2 : Fin 6) then .op (.loadInd (5 : Fin 7) (2 : Fin 7)) (3 : Fin 6)
    else if l = (3 : Fin 6) then .op (.mul (6 : Fin 7) (3 : Fin 7) (4 : Fin 7)) (4 : Fin 6)
    else if l = (4 : Fin 6) then .op (.mul (6 : Fin 7) (6 : Fin 7) (5 : Fin 7)) (5 : Fin 6)
    else .halt

/-- Initial configuration of `ramCheckTriangleTriple` for testing triple `(i, j, k)` in `mem`. -/
def initCheckTriangleTripleConfig (n : ℕ) (i j k : Fin n) (mem : ℕ → ℕ) :
    Config ramCheckTriangleTriple :=
  { pc   := some (0 : Fin 6)
    regs := fun r =>
      if r = (0 : Fin 7) then 1 + i.val * n + j.val
      else if r = (1 : Fin 7) then 1 + n * n + j.val * n + k.val
      else if r = (2 : Fin 7) then 1 + 2 * (n * n) + i.val * n + k.val
      else 0
    mem  := mem }

theorem ramCheckTriangleTriple_evalsToInLogCostTime_triDet
    (n : ℕ) (A B C : Fin n → Fin n → Bool) (i j k : Fin n) :
    let mem := initTriDetMem n A B C
    ∃ (haltCfg : Config ramCheckTriangleTriple) (b : ℕ),
      b ≤ 12 * (bitLengthNat n + 4) ^ 2 ∧
      haltCfg.regs (6 : Fin 7) = (if (A i j && B j k && C i k) then 1 else 0) ∧
      EvalsToInLogCostTime ramCheckTriangleTriple
        (initCheckTriangleTripleConfig n i j k mem) haltCfg 6 b := by
  dsimp only
  set mem := initTriDetMem n A B C
  set addrA := 1 + i.val * n + j.val
  set addrB := 1 + n * n + j.val * n + k.val
  set addrC := 1 + 2 * (n * n) + i.val * n + k.val
  let r0 : Fin 7 → ℕ := (initCheckTriangleTripleConfig n i j k mem).regs
  let r1 : Fin 7 → ℕ := updateReg r0 (3 : Fin 7) (mem addrA)
  let r2 : Fin 7 → ℕ := updateReg r1 (4 : Fin 7) (mem addrB)
  let r3 : Fin 7 → ℕ := updateReg r2 (5 : Fin 7) (mem addrC)
  let r4 : Fin 7 → ℕ := updateReg r3 (6 : Fin 7) (mem addrA * mem addrB)
  let r5 : Fin 7 → ℕ := updateReg r4 (6 : Fin 7) ((mem addrA * mem addrB) * mem addrC)
  have hstep1 : ramCheckTriangleTriple.step ⟨some (0 : Fin 6), r0, mem⟩ =
      some ⟨some (1 : Fin 6), r1, mem⟩ := rfl
  have hstep2 : ramCheckTriangleTriple.step ⟨some (1 : Fin 6), r1, mem⟩ =
      some ⟨some (2 : Fin 6), r2, mem⟩ := rfl
  have hstep3 : ramCheckTriangleTriple.step ⟨some (2 : Fin 6), r2, mem⟩ =
      some ⟨some (3 : Fin 6), r3, mem⟩ := rfl
  have hstep4 : ramCheckTriangleTriple.step ⟨some (3 : Fin 6), r3, mem⟩ =
      some ⟨some (4 : Fin 6), r4, mem⟩ := rfl
  have hstep5 : ramCheckTriangleTriple.step ⟨some (4 : Fin 6), r4, mem⟩ =
      some ⟨some (5 : Fin 6), r5, mem⟩ := rfl
  have hstep6 : ramCheckTriangleTriple.step ⟨some (5 : Fin 6), r5, mem⟩ =
      some ⟨none, r5, mem⟩ := rfl
  have htr0 := StepsInTimeAndLogCost.refl (M := ramCheckTriangleTriple) ⟨none, r5, mem⟩
  have htr1 := StepsInTimeAndLogCost.step hstep6 htr0
  have htr2 := StepsInTimeAndLogCost.step hstep5 htr1
  have htr3 := StepsInTimeAndLogCost.step hstep4 htr2
  have htr4 := StepsInTimeAndLogCost.step hstep3 htr3
  have htr5 := StepsInTimeAndLogCost.step hstep2 htr4
  have htr6 := StepsInTimeAndLogCost.step hstep1 htr5
  have hmemA : mem addrA = if A i j then 1 else 0 := initTriDetMem_A_eq n A B C i j
  have hmemB : mem addrB = if B j k then 1 else 0 := initTriDetMem_B_eq n A B C j k
  have hmemC : mem addrC = if C i k then 1 else 0 := initTriDetMem_C_eq n A B C i k
  refine ⟨⟨none, r5, mem⟩, _, ?_, ?_, ⟨rfl, htr6⟩⟩
  · change 0 + 1 +
        (bitLengthNat (mem addrA * mem addrB) * bitLengthNat (mem addrC) + 1) +
        (bitLengthNat (mem addrA) * bitLengthNat (mem addrB) + 1) +
        (bitLengthNat addrC + bitLengthNat (mem addrC) + 1) +
        (bitLengthNat addrB + bitLengthNat (mem addrB) + 1) +
        (bitLengthNat addrA + bitLengthNat (mem addrA) + 1) ≤
      12 * (bitLengthNat n + 4) ^ 2
    have hlt_ij := fin_mul_add_lt i j
    have hlt_jk := fin_mul_add_lt j k
    have hlt_ik := fin_mul_add_lt i k
    have hb_addrA : bitLengthNat addrA ≤ 2 * bitLengthNat n + 3 :=
      bitLengthNat_le_of_le_four_mul_sq (by omega)
    have hb_addrB : bitLengthNat addrB ≤ 2 * bitLengthNat n + 3 :=
      bitLengthNat_le_of_le_four_mul_sq (by omega)
    have hb_addrC : bitLengthNat addrC ≤ 2 * bitLengthNat n + 3 :=
      bitLengthNat_le_of_le_four_mul_sq (by omega)
    have hb_mA : bitLengthNat (mem addrA) = 1 := by
      rw [hmemA]; cases A i j <;> rfl
    have hb_mB : bitLengthNat (mem addrB) = 1 := by
      rw [hmemB]; cases B j k <;> rfl
    have hb_mC : bitLengthNat (mem addrC) = 1 := by
      rw [hmemC]; cases C i k <;> rfl
    have hb_mAB : bitLengthNat (mem addrA * mem addrB) = 1 := by
      rw [hmemA, hmemB]; cases A i j <;> cases B j k <;> rfl
    rw [hb_mA, hb_mB, hb_mC, hb_mAB]
    nlinarith
  · change updateReg r4 (6 : Fin 7) ((mem addrA * mem addrB) * mem addrC) (6 : Fin 7) =
      if (A i j && B j k && C i k) then 1 else 0
    rw [updateReg_self, hmemA, hmemB, hmemC]
    cases A i j <;> cases B j k <;> cases C i k <;> rfl

/-- Transitive composition of `StepsInTimeAndLogCost` traces: if `M` transitions from
`cfg₁` to `cfg₂` in `t₁` steps and `b₁` log-cost bit operations, and from `cfg₂` to `cfg₃` in
`t₂` steps and `b₂` log-cost bit operations, then `M` transitions from `cfg₁` to `cfg₃` in
`t₁ + t₂` steps and `b₁ + b₂` log-cost bit operations. -/
theorem StepsInTimeAndLogCost.trans {M : ArithRAM}
    {cfg₁ cfg₂ cfg₃ : Config M} {t₁ b₁ t₂ b₂ : ℕ}
    (h₁ : StepsInTimeAndLogCost M cfg₁ cfg₂ t₁ b₁)
    (h₂ : StepsInTimeAndLogCost M cfg₂ cfg₃ t₂ b₂) :
    StepsInTimeAndLogCost M cfg₁ cfg₃ (t₁ + t₂) (b₁ + b₂) := by
  induction h₁ with
  | refl _ =>
    simpa only [Nat.zero_add] using h₂
  | @step cfg mid haltCfg t b hstep _ ih =>
    have hstep' := StepsInTimeAndLogCost.step hstep (ih h₂)
    have ht : t + t₂ + 1 = t + 1 + t₂ := by omega
    have hb : b + b₂ + M.stepLogCost cfg = b + M.stepLogCost cfg + b₂ := by omega
    rwa [ht, hb] at hstep'

@[simp]
lemma updateReg_idem {Reg : Type} [DecidableEq Reg] (regs : Reg → ℕ) (r : Reg) (v₁ v₂ : ℕ) :
    updateReg (updateReg regs r v₁) r v₂ = updateReg regs r v₂ := by
  funext r'
  unfold updateReg
  split_ifs <;> rfl

/-- Concrete 4-label, 4-register `ArithRAM` loop machine
that starts from the canonical initial configuration (`regs 0 = n`, all other registers `0`) and
executes an `n`-iteration loop (`reg 1 < reg 0`) while preserving `reg 0 = n` and memory `mem`:
- Label `0`: `.op (.loadImm (2 : Fin 4) .one) (1 : Fin 4)` (`reg 2 := 1`)
- Label `1`: `.branchLt (1 : Fin 4) (0 : Fin 4) (2 : Fin 4) (3 : Fin 4)`
- Label `2`: `.op (.add (1 : Fin 4) (1 : Fin 4) (2 : Fin 4)) (1 : Fin 4)` (`reg 1 := reg 1 + reg 2`)
- Label `3`: `.halt` -/
@[reducible]
def ramCountLoop : ArithRAM where
  Λ := Fin 4
  Reg := Fin 4
  initLabel := (0 : Fin 4)
  reg0 := (0 : Fin 4)
  prog := fun l =>
    if l = (0 : Fin 4) then .op (.loadImm (2 : Fin 4) .one) (1 : Fin 4)
    else if l = (1 : Fin 4) then .branchLt (1 : Fin 4) (0 : Fin 4) (2 : Fin 4) (3 : Fin 4)
    else if l = (2 : Fin 4) then .op (.add (1 : Fin 4) (1 : Fin 4) (2 : Fin 4)) (1 : Fin 4)
    else .halt

/-- Base register file for `ramCountLoop` after Label `0` loads `1` into `reg 2`. -/
def countLoopBaseRegs (n : ℕ) (r : Fin 4) : ℕ :=
  if r = (0 : Fin 4) then n
  else if r = (1 : Fin 4) then 0
  else if r = (2 : Fin 4) then 1
  else 0

/-- Configuration of `ramCountLoop` at loop header Label `1` with loop counter `c` in `reg 1`. -/
def countLoopCfgAt (n : ℕ) (mem : ℕ → ℕ) (c : ℕ) : Config ramCountLoop :=
  ⟨some (1 : Fin 4), updateReg (countLoopBaseRegs n) (1 : Fin 4) c, mem⟩

/-- Single loop iteration of `ramCountLoop` (`c ↦ c + 1` when `c < n`): executes 2 instructions
(`.branchLt` and `.add`) in `2` steps and at most `3 * bitLengthNat n + 3` Cook–Reckhow bit
operations. -/
theorem ramCountLoop_one_iter (n : ℕ) (mem : ℕ → ℕ) {c : ℕ} (hc : c < n) :
    ∃ b : ℕ,
      b ≤ 3 * bitLengthNat n + 3 ∧
      StepsInTimeAndLogCost ramCountLoop
        (countLoopCfgAt n mem c)
        (countLoopCfgAt n mem (c + 1)) 2 b := by
  have h0 : updateReg (countLoopBaseRegs n) (1 : Fin 4) c (0 : Fin 4) = n := rfl
  have h1 : updateReg (countLoopBaseRegs n) (1 : Fin 4) c (1 : Fin 4) = c := rfl
  have h2 : updateReg (countLoopBaseRegs n) (1 : Fin 4) c (2 : Fin 4) = 1 := rfl
  have hstep1 : ramCountLoop.step (countLoopCfgAt n mem c) =
      some ⟨some (2 : Fin 4), updateReg (countLoopBaseRegs n) (1 : Fin 4) c, mem⟩ := by
    change some (⟨some (if updateReg (countLoopBaseRegs n) (1 : Fin 4) c (1 : Fin 4) <
        updateReg (countLoopBaseRegs n) (1 : Fin 4) c (0 : Fin 4)
      then (2 : Fin 4) else (3 : Fin 4)),
      updateReg (countLoopBaseRegs n) (1 : Fin 4) c, mem⟩ : Config ramCountLoop) = _
    rw [h1, h0, if_pos hc]
  have hstep2 : ramCountLoop.step
      ⟨some (2 : Fin 4), updateReg (countLoopBaseRegs n) (1 : Fin 4) c, mem⟩ =
      some (countLoopCfgAt n mem (c + 1)) := by
    change some (⟨some (1 : Fin 4),
      updateReg (updateReg (countLoopBaseRegs n) (1 : Fin 4) c) (1 : Fin 4)
        (updateReg (countLoopBaseRegs n) (1 : Fin 4) c (1 : Fin 4) +
          updateReg (countLoopBaseRegs n) (1 : Fin 4) c (2 : Fin 4)), mem⟩ : Config ramCountLoop) = _
    rw [h1, h2, updateReg_idem]
    rfl
  have htr0 := StepsInTimeAndLogCost.refl (M := ramCountLoop) (countLoopCfgAt n mem (c + 1))
  have htr1 := StepsInTimeAndLogCost.step hstep2 htr0
  have htr2 := StepsInTimeAndLogCost.step hstep1 htr1
  refine ⟨_, ?_, htr2⟩
  change 0 + (bitLengthNat c + bitLengthNat 1 + 1) + (bitLengthNat c + bitLengthNat n + 1) ≤
    3 * bitLengthNat n + 3
  have hb1 : bitLengthNat 1 = 1 := rfl
  have hbc : bitLengthNat c ≤ bitLengthNat n := bitLengthNat_mono (le_of_lt hc)
  omega

/-- Multi-step loop execution theorem for `ramCountLoop` (`c ↦ c + k` when `c + k ≤ n`):
executes `2 * k` RAM steps and at most `k * (3 * bitLengthNat n + 3)` Cook–Reckhow bit operations. -/
theorem ramCountLoop_loop_steps (n : ℕ) (mem : ℕ → ℕ) (c k : ℕ) (hck : c + k ≤ n) :
    ∃ b : ℕ,
      b ≤ k * (3 * bitLengthNat n + 3) ∧
      StepsInTimeAndLogCost ramCountLoop
        (countLoopCfgAt n mem c)
        (countLoopCfgAt n mem (c + k)) (2 * k) b := by
  induction k generalizing c with
  | zero =>
    refine ⟨0, by simp, ?_⟩
    simpa only [Nat.add_zero, Nat.mul_zero] using
      StepsInTimeAndLogCost.refl (M := ramCountLoop) (countLoopCfgAt n mem c)
  | succ k ih =>
    have hc_lt : c < n := by omega
    have hck' : (c + 1) + k ≤ n := by omega
    rcases ramCountLoop_one_iter n mem hc_lt with ⟨b₁, hb₁, htr₁⟩
    rcases ih (c + 1) hck' with ⟨b₂, hb₂, htr₂⟩
    have htr := htr₁.trans htr₂
    have h_add : c + 1 + k = c + (k + 1) := by omega
    have h_steps : 2 + 2 * k = 2 * (k + 1) := by ring
    rw [h_add, h_steps] at htr
    refine ⟨b₁ + b₂, ?_, htr⟩
    calc
      b₁ + b₂ ≤ (3 * bitLengthNat n + 3) + k * (3 * bitLengthNat n + 3) :=
        Nat.add_le_add hb₁ hb₂
      _ = (k + 1) * (3 * bitLengthNat n + 3) := by ring

/-- Full halted execution of `ramCountLoop` from any canonical initial configuration where
`regs 0 = n` and all other registers are `0`:
halts in `2 * n + 3` Unit-Cost Word RAM steps and `b ≤ (n + 1) * (3 * bitLengthNat n + 4)`
Cook–Reckhow bit operations, with `haltCfg.regs 0 = n`, `haltCfg.regs 1 = n`, and
`haltCfg.mem = mem`. -/
theorem ramCountLoop_evalsToInLogCostTime_of_mem (n : ℕ) (mem : ℕ → ℕ) :
    let initCfg : Config ramCountLoop :=
      { pc   := some (0 : Fin 4)
        regs := fun r => if r = (0 : Fin 4) then n else 0
        mem  := mem }
    ∃ (haltCfg : Config ramCountLoop) (b : ℕ),
      b ≤ (n + 1) * (3 * bitLengthNat n + 4) ∧
      haltCfg.regs (0 : Fin 4) = n ∧
      haltCfg.regs (1 : Fin 4) = n ∧
      haltCfg.mem = mem ∧
      EvalsToInLogCostTime ramCountLoop initCfg haltCfg (2 * n + 3) b := by
  dsimp only
  let initCfg : Config ramCountLoop :=
    { pc   := some (0 : Fin 4)
      regs := fun r => if r = (0 : Fin 4) then n else 0
      mem  := mem }
  have hregs0 :
      updateReg initCfg.regs (2 : Fin 4) 1 =
        updateReg (countLoopBaseRegs n) (1 : Fin 4) 0 := by
    funext r
    fin_cases r <;> rfl
  have hstep0 : ramCountLoop.step initCfg = some (countLoopCfgAt n mem 0) := by
    change some (⟨some (1 : Fin 4),
      updateReg initCfg.regs (2 : Fin 4) 1, mem⟩ : Config ramCountLoop) = _
    rw [hregs0]
    rfl
  rcases ramCountLoop_loop_steps n mem 0 n (by omega) with ⟨b_loop, hb_loop, htr_loop⟩
  rw [Nat.zero_add] at htr_loop
  have h0 : updateReg (countLoopBaseRegs n) (1 : Fin 4) n (0 : Fin 4) = n := rfl
  have h1 : updateReg (countLoopBaseRegs n) (1 : Fin 4) n (1 : Fin 4) = n := rfl
  have hstep_exit : ramCountLoop.step (countLoopCfgAt n mem n) =
      some ⟨some (3 : Fin 4), updateReg (countLoopBaseRegs n) (1 : Fin 4) n, mem⟩ := by
    change some (⟨some (if updateReg (countLoopBaseRegs n) (1 : Fin 4) n (1 : Fin 4) <
        updateReg (countLoopBaseRegs n) (1 : Fin 4) n (0 : Fin 4)
      then (2 : Fin 4) else (3 : Fin 4)),
      updateReg (countLoopBaseRegs n) (1 : Fin 4) n, mem⟩ : Config ramCountLoop) = _
    rw [h1, h0, if_neg (Nat.lt_irrefl n)]
  have hstep_halt : ramCountLoop.step
      ⟨some (3 : Fin 4), updateReg (countLoopBaseRegs n) (1 : Fin 4) n, mem⟩ =
      some ⟨none, updateReg (countLoopBaseRegs n) (1 : Fin 4) n, mem⟩ := rfl
  let haltCfg : Config ramCountLoop :=
    ⟨none, updateReg (countLoopBaseRegs n) (1 : Fin 4) n, mem⟩
  have htr_halt := StepsInTimeAndLogCost.step hstep_exit
    (StepsInTimeAndLogCost.step hstep_halt (StepsInTimeAndLogCost.refl haltCfg))
  have htr_from_1 := htr_loop.trans htr_halt
  have htr_all := StepsInTimeAndLogCost.step hstep0 htr_from_1
  have h_steps : 2 * n + (0 + 1 + 1) + 1 = 2 * n + 3 := by omega
  rw [h_steps] at htr_all
  refine ⟨haltCfg, _, ?_, rfl, rfl, rfl, ⟨rfl, htr_all⟩⟩
  change b_loop + (0 + 1 + (bitLengthNat n + bitLengthNat n + 1)) + bitLengthNat 1 ≤
    (n + 1) * (3 * bitLengthNat n + 4)
  have hb1 : bitLengthNat 1 = 1 := rfl
  rw [hb1]
  nlinarith

theorem ramCountLoop_evalsToInLogCostTime_triDet (n : ℕ) (A B C : Fin n → Fin n → Bool) :
    ∃ (haltCfg : Config ramCountLoop) (b : ℕ),
      b ≤ (n + 1) * (3 * bitLengthNat n + 4) ∧
      haltCfg.regs (0 : Fin 4) = n ∧
      haltCfg.regs (1 : Fin 4) = n ∧
      haltCfg.mem = initTriDetMem n A B C ∧
      EvalsToInLogCostTime ramCountLoop
        (initTriDetConfig ramCountLoop n A B C) haltCfg (2 * n + 3) b :=
  ramCountLoop_evalsToInLogCostTime_of_mem n (initTriDetMem n A B C)

theorem ramCountLoop_evalsToInLogCostTime_bmm (n : ℕ) (A B : Fin n → Fin n → Bool) :
    ∃ (haltCfg : Config ramCountLoop) (b : ℕ),
      b ≤ (n + 1) * (3 * bitLengthNat n + 4) ∧
      haltCfg.regs (0 : Fin 4) = n ∧
      haltCfg.regs (1 : Fin 4) = n ∧
      haltCfg.mem = initBMMMem n A B ∧
      EvalsToInLogCostTime ramCountLoop
        (initBMMConfig ramCountLoop n A B) haltCfg (2 * n + 3) b :=
  ramCountLoop_evalsToInLogCostTime_of_mem n (initBMMMem n A B)

end ArithRAM

end BMMGrid
