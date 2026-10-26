import BMMGrid.Decomp3DPotential
/-!
# Sections 5.2–5.6: 3D Regularity Decomposition (`BMMGrid/Decomp3D.lean`)

This module formalizes Algorithm 5 (`Decompose3D`, `\label{alg:3d}`, `sStarLoop`,
`cappedABDecompAux`, `cappedABDecomposition`), Lemmas 5.4, 5.5, and 5.9
(`\label{lem:children-invariants}`, `\label{lem:potential}`, `\label{lem:recurrence}`), and
Theorem 1.1 (`\label{thm:main-decomp}`, `thm_main_decomp`, `thm_main_decomp_of_samplers`) of
`paper.tex` (§1.2 & §5.2–§5.6).
-/
namespace BMMGrid
section CappedABDecomposition
variable {α β γ : Type*}

open Classical in
/-- Boolean indicator of Base Case 1 sparsity ($\min(\mathbb{E}[A], \mathbb{E}[B]) \le 2^{-D}$,
`paper.tex` Algorithm 5 (`Decompose3D`) §5.2). -/
noncomputable def isSparse3DPiece (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ) (D : ℕ) : Bool :=
  decide (min (matDensity X Y A) (matDensity Y Z B) ≤ (2 : ℝ) ^ (- (D : ℝ)))

lemma two_rpow_neg_nat_eq_zpow (D : ℕ) :
    (2 : ℝ) ^ (- (D : ℝ)) = (2 : ℝ) ^ (-(D : ℤ)) := by
  rw [← Real.rpow_intCast 2 (-(D : ℤ))]
  push_cast
  rfl

lemma of_isSparse3DPiece_eq_false {X : Finset α} {Y : Finset β} {Z : Finset γ}
    {A : α → β → ℝ} {B : β → γ → ℝ} {D : ℕ}
    (h : isSparse3DPiece X Y Z A B D = false) :
    X.Nonempty ∧ Y.Nonempty ∧ Z.Nonempty ∧
    (2 : ℝ) ^ (-(D : ℤ)) < matDensity X Y A ∧
    (2 : ℝ) ^ (-(D : ℤ)) < matDensity Y Z B := by
  unfold isSparse3DPiece at h
  rw [decide_eq_false_iff_not, not_le, two_rpow_neg_nat_eq_zpow, lt_min_iff] at h
  rcases h with ⟨hA_gt, hB_gt⟩
  have hposA : 0 < matDensity X Y A := lt_trans (by positivity) hA_gt
  have hposB : 0 < matDensity Y Z B := lt_trans (by positivity) hB_gt
  have hX : X.Nonempty := by
    rcases X.eq_empty_or_nonempty with rfl | hne
    · simp [matDensity] at hposA
    · exact hne
  have hY : Y.Nonempty := by
    rcases Y.eq_empty_or_nonempty with rfl | hne
    · simp [matDensity, rowDeg] at hposA
    · exact hne
  have hZ : Z.Nonempty := by
    rcases Z.eq_empty_or_nonempty with rfl | hne
    · simp [matDensity, rowDeg] at hposB
    · exact hne
  exact ⟨hX, hY, hZ, hA_gt, hB_gt⟩

lemma isBinaryMatrix_submatZeroExt [DecidableEq α] [DecidableEq β]
    {X X' : Finset α} {Y Y' : Finset β} {A : α → β → ℝ}
    (hX : X' ⊆ X) (hY : Y' ⊆ Y) (hA : IsBinaryMatrix X Y A) :
    IsBinaryMatrix X' Y' (submatZeroExt X' Y' A) := by
  intro x hx y hy
  simp only [submatZeroExt, hx, hy, and_self, ↓reduceIte]
  exact hA x (hX hx) y (hY hy)

/-- Base Case 1 sparse piece `(X, Y, Z, A[X, Y], B[Y, Z])` with `isRegularPiece = false`
(`paper.tex` Algorithm 5 (`Decompose3D` `\label{line:3d-base1}`), §5.2). -/
def baseCase1Piece [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ) (_ε : ℝ) (_D : ℕ) : CubePiece α β γ where
  X_k := X
  Y_k := Y
  Z_k := Z
  A_k := submatZeroExt X Y A
  B_k := submatZeroExt Y Z B
  isRegularPiece := false

/-- Direct slice piece `(sl.X_ell, sl.Y_ell, sl.Z_ell, sl.A_ell, B[sl.Y_ell, sl.Z_ell])`
in $\mathcal{S}_{\text{direct}}$ (`paper.tex` Algorithm 5 (`Decompose3D` `\label{line:3d-direct}`), §5.2). -/
noncomputable def directSlicePiece [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (B : β → γ → ℝ) (D : ℕ) (sl : GoodCubeSlice α β γ) : CubePiece α β γ where
  X_k := sl.X_ell
  Y_k := sl.Y_ell
  Z_k := sl.Z_ell
  A_k := sl.A_ell
  B_k := submatZeroExt sl.Y_ell sl.Z_ell B
  isRegularPiece := open Classical in
    decide (sl.tag = RectTag.regular ∧
      (2 : ℝ) ^ (- (D : ℝ)) <
        min (matDensity sl.X_ell sl.Y_ell sl.A_ell)
          (matDensity sl.Y_ell sl.Z_ell (submatZeroExt sl.Y_ell sl.Z_ell B)))

/-- Maximum number of $\mathcal{S}^*$ tail-recursive iterations at a single tree node
$R_{\mathcal{S}^*}(\varepsilon, D) := \lceil 2^{D + D^2} M_{\text{cube}}(\varepsilon, \gamma_{3D}, D) \rceil$
(`paper.tex` §5.5). -/
noncomputable def rSStarFuel (ε : ℝ) (D : ℕ) : ℕ :=
  Nat.ceil ((2 : ℝ) ^ (D + D ^ 2) * M_cube ε gamma3D D)

lemma processGoodCubePiece_inr_sub [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {X : Finset α} {Y' : Finset β} {Z_curr : Finset γ} {B : β → γ → ℝ} {ε : ℝ}
    {S : TwoStageSamplerOracle β ε} {γ_val : ℝ} {D : ℕ}
    {P : RectPiece α β} {sl : GoodCubeSlice α β γ}
    (hPX : P.X_sub ⊆ X) (hPY : P.Y_sub ⊆ Y')
    (hinr : processGoodCubePiece Y' Z_curr B ε γ_val D S P = Sum.inr sl) :
    sl.X_ell ⊆ X ∧ sl.Y_ell ⊆ Y' ∧ sl.Z_ell ⊆ Z_curr := by
  classical
  unfold processGoodCubePiece at hinr
  cases htag : P.tag <;> rw [htag] at hinr
  · dsimp only at hinr
    split_ifs at hinr with h4a h4c h4d
    cases hinr
    dsimp only
    exact ⟨hPX, hPY, minDegree_fst_subset Z_curr P.Y_sub (matTranspose B) ε γ_val⟩
  · dsimp only at hinr
    split_ifs at hinr with h4a
    cases hinr
    dsimp only
    exact ⟨hPX, hPY, Finset.empty_subset _⟩
  · cases hinr
    dsimp only
    refine ⟨hPX, hPY, ?_⟩
    split_ifs
    · exact Finset.Subset.rfl
    · exact Finset.empty_subset _

lemma processGoodCubePieces_inr_sub [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {X : Finset α} {Y' : Finset β} {Z_curr : Finset γ} {B : β → γ → ℝ} {ε : ℝ}
    {S : TwoStageSamplerOracle β ε} {γ_val : ℝ} {D : ℕ}
    {L : List (RectPiece α β)} {slices : List (GoodCubeSlice α β γ)}
    (hL : ∀ P ∈ L, P.X_sub ⊆ X ∧ P.Y_sub ⊆ Y')
    (hinr : processGoodCubePieces Y' Z_curr B ε γ_val D S L = Sum.inr slices) :
    slices.length = L.length ∧
    ∀ sl ∈ slices, sl.X_ell ⊆ X ∧ sl.Y_ell ⊆ Y' ∧ sl.Z_ell ⊆ Z_curr := by
  induction L generalizing slices with
  | nil =>
    unfold processGoodCubePieces at hinr
    cases hinr
    exact ⟨rfl, fun _ h => by cases h⟩
  | cons P rest ih =>
    unfold processGoodCubePieces at hinr
    cases hP : processGoodCubePiece Y' Z_curr B ε γ_val D S P with
    | inl step => rw [hP] at hinr; cases hinr
    | inr sl =>
      rw [hP] at hinr
      cases hrest : processGoodCubePieces Y' Z_curr B ε γ_val D S rest with
      | inl step => rw [hrest] at hinr; cases hinr
      | inr sls =>
        rw [hrest] at hinr
        cases hinr
        rcases hL P List.mem_cons_self with ⟨hPX, hPY⟩
        have hsl_sub := processGoodCubePiece_inr_sub hPX hPY hP
        rcases ih (fun Q hQ => hL Q (List.mem_cons_of_mem P hQ)) hrest with ⟨hlen, hmem⟩
        refine ⟨by simp [hlen], fun s hs => ?_⟩
        simp only [List.mem_cons] at hs
        rcases hs with rfl | hs_tail
        · exact hsl_sub
        · exact hmem s hs_tail

lemma cappedGoodCubeLoop_sub_and_slices_len [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (fuel : ℕ) (X : Finset α) (Y_curr : Finset β) (Z_curr : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    (ε : ℝ) (S : TwoStageSamplerOracle β ε) (γ_val : ℝ) (D : ℕ) (α_cap β_init : ℝ) :
    let res := cappedGoodCubeLoop fuel X Y_curr Z_curr A B ε γ_val D α_cap β_init S
    res.Y_star ⊆ Y_curr ∧ res.Z_star ⊆ Z_curr ∧
    res.slices.length ≤ rDecompAFuel ε D + 1 ∧
    ∀ sl ∈ res.slices, sl.X_ell ⊆ X ∧ sl.Y_ell ⊆ res.Y_star ∧ sl.Z_ell ⊆ res.Z_star := by
  classical
  induction fuel generalizing Y_curr Z_curr with
  | zero =>
    unfold cappedGoodCubeLoop
    exact ⟨Finset.Subset.rfl, Finset.Subset.rfl, by simp, fun _ h => by cases h⟩
  | succ k ih =>
    unfold cappedGoodCubeLoop
    dsimp only
    by_cases hboost : matDensity Y_curr Z_curr B ≥ 16 * β_init
    · rw [if_pos hboost]
      exact ⟨Finset.Subset.rfl, Finset.Subset.rfl, by simp, fun _ h => by cases h⟩
    · rw [if_neg hboost]
      set Y' := (minDegree Y_curr Z_curr B (ε * γ_val / 2) (1 / 2)).1
      have hY'_sub : Y' ⊆ Y_curr := minDegree_fst_subset Y_curr Z_curr B (ε * γ_val / 2) (1 / 2)
      by_cases hstep1 :
          (minDegree Y_curr Z_curr B (ε * γ_val / 2) (1 / 2)).2 = 2 ∨
            matDensity Y' Z_curr B ≥ (1 + ε * γ_val / 4) * matDensity Y_curr Z_curr B
      · rw [if_pos hstep1]
        rcases ih Y' Z_curr with ⟨hY, hZ, hlen, hsl⟩
        exact ⟨hY.trans hY'_sub, hZ, hlen, hsl⟩
      · rw [if_neg hstep1]
        set piecesA := cappedADecomp3D X Y' A ε D (cLow3D * α_cap) (cCap3D * α_cap) S
        have hpieces_sub : ∀ P ∈ piecesA, P.X_sub ⊆ X ∧ P.Y_sub ⊆ Y' :=
          fun P hP => cappedADecomp3DLoop_mem_subset_raw
            (rDecompAFuel ε D) X Y' A ε D (cLow3D * α_cap) (cCap3D * α_cap) S hP
        cases hproc : processGoodCubePieces Y' Z_curr B ε γ_val D S piecesA with
        | inl step =>
          rcases step with ⟨Y_next, Z_next, s_step⟩
          dsimp only
          have hnext_sub := processGoodCubePieces_inl_subset
            (fun P hP => (hpieces_sub P hP).2) hproc
          rcases ih Y_next Z_next with ⟨hY, hZ, hlen, hsl⟩
          exact ⟨hY.trans (hnext_sub.1.trans hY'_sub), hZ.trans hnext_sub.2, hlen, hsl⟩
        | inr slices =>
          dsimp only
          rcases processGoodCubePieces_inr_sub hpieces_sub hproc with ⟨hlen_eq, hsl_sub⟩
          have hlen_le : slices.length ≤ rDecompAFuel ε D + 1 := by
            rw [hlen_eq]
            exact cappedADecomp3DLoop_length_le (rDecompAFuel ε D) X Y' A ε D
              (cLow3D * α_cap) (cCap3D * α_cap) S
          exact ⟨hY'_sub, Finset.Subset.rfl, hlen_le, hsl_sub⟩

lemma cappedGoodCube_sub_and_slices_len [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    (ε : ℝ) (S : TwoStageSamplerOracle β ε) (γ_val : ℝ) (D : ℕ) (α_cap β_init : ℝ) :
    let res := cappedGoodCube X Y Z A B ε γ_val D α_cap β_init S
    res.Y_star ⊆ Y ∧ res.Z_star ⊆ Z ∧
    res.slices.length ≤ rDecompAFuel ε D + 1 ∧
    ∀ sl ∈ res.slices, sl.X_ell ⊆ X ∧ sl.Y_ell ⊆ res.Y_star ∧ sl.Z_ell ⊆ res.Z_star :=
  cappedGoodCubeLoop_sub_and_slices_len (rCubeFuel ε γ_val) X Y Z A B ε S γ_val D α_cap β_init

/-- **Algorithm 5 (`Decompose3D`) $\mathcal{S}^*$ Tail-Recursion Loop (`sStarLoop`, `paper.tex` §5.2)**:
Executes the recursive step of `cappedABDecomposition'` at remaining depth `remDepth = H - h ≥ 1`,
carrying the exact integer numerator/denominator pair `(capNum, capDen)` of `α_cap` and
parameterized by the depth-advancing recursive call `recDepth`. -/
noncomputable def sStarLoop [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (sStarFuel : ℕ) (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    (ε : ℝ) (S : TwoStageSamplerOracle β ε) (D : ℕ) (α_cap : ℝ) (capNum capDen remDepth : ℕ)
    (recDepth : ℕ → Finset α → Finset β → Finset γ →
      (α → β → ℝ) → (β → γ → ℝ) → ℝ → ℕ → ℕ → List (CubePiece α β γ)) :
    List (CubePiece α β γ) :=
  match sStarFuel with
  | 0 => [baseCase1Piece X Y Z A B ε D]
  | fuel + 1 =>
    if isSparse3DPiece X Y Z A B D then
      [baseCase1Piece X Y Z A B ε D]
    else
      let cubeRes := cappedGoodCube X Y Z A B ε gamma3D D α_cap (matDensity Y Z B) S
      let B_rem := zeroOutSubrect B cubeRes.Y_star cubeRes.Z_star
      let S_star := sStarLoop fuel X Y Z A B_rem ε S D α_cap capNum capDen remDepth recDepth
      if cubeRes.mode = CubeMode.bBoost then
        let Δ := min remDepth
          (rawDeltaHBNat
            (supportCountRealNat cubeRes.Y_star cubeRes.Z_star B)
            (cubeRes.Y_star.card * cubeRes.Z_star.card)
            (supportCountRealNat Y Z B)
            (Y.card * Z.card))
        let S_boost := recDepth Δ X cubeRes.Y_star cubeRes.Z_star
          (submatZeroExt X cubeRes.Y_star A)
          (submatZeroExt cubeRes.Y_star cubeRes.Z_star B) α_cap capNum capDen
        S_star ++ S_boost
      else
        let S_direct :=
          (cubeRes.slices.filter (fun sl => decide sl.Z_ell.Nonempty)).map (directSlicePiece B D)
        let activeSlices :=
          cubeRes.slices.filter (fun sl => decide (cubeRes.Z_star \ sl.Z_ell).Nonempty)
        let S_rec := activeSlices.flatMap (fun sl =>
          let Z_rem := cubeRes.Z_star \ sl.Z_ell
          let α_ell := matDensity sl.X_ell sl.Y_ell sl.A_ell
          let p_ell := supportCountRealNat sl.X_ell sl.Y_ell sl.A_ell
          let q_ell := sl.X_ell.card * sl.Y_ell.card
          let Δ := min remDepth (rawDeltaHANat p_ell q_ell capNum capDen)
          bucketedRec sl.X_ell sl.Y_ell Z_rem sl.A_ell
            (submatZeroExt sl.Y_ell Z_rem B) α_ell D
            (fun X' Y'_j Z' A'_j B'_j α'_j j =>
              recDepth Δ X' Y'_j Z' A'_j B'_j α'_j (2 ^ j * p_ell) q_ell))
        S_direct ++ S_star ++ S_rec

/-- Bottom-up cost-tracked implementation of `sStarLoop` in `CostM`. -/
noncomputable def sStarLoopTracked [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (sStarFuel : ℕ) (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    (ε : ℝ) (S : TwoStageSamplerOracle β ε) (D : ℕ) (α_cap : ℝ) (capNum capDen remDepth : ℕ)
    (recDepthTracked : ℕ → Finset α → Finset β → Finset γ →
      (α → β → ℝ) → (β → γ → ℝ) → ℝ → ℕ → ℕ → CostM (List (CubePiece α β γ))) :
    CostM (List (CubePiece α β γ)) :=
  match sStarFuel with
  | 0 =>
    scanMatrixPairTracked X Y Z [baseCase1Piece X Y Z A B ε D]
  | fuel + 1 =>
    CostM.bind (scanMatrixPairTracked X Y Z (isSparse3DPiece X Y Z A B D)) (fun isSparse =>
      if isSparse then
        scanMatrixPairTracked X Y Z [baseCase1Piece X Y Z A B ε D]
      else
        CostM.bind
          (cappedGoodCubeTracked X Y Z A B ε gamma3D D α_cap (matDensity Y Z B) S)
          (fun cubeRes =>
            let B_rem := zeroOutSubrect B cubeRes.Y_star cubeRes.Z_star
            CostM.bind
              (sStarLoopTracked fuel X Y Z A B_rem ε S D α_cap capNum capDen remDepth recDepthTracked)
              (fun S_star =>
                if cubeRes.mode = CubeMode.bBoost then
                  CostM.bind
                    (scanMatrixTracked cubeRes.Y_star cubeRes.Z_star
                      (supportCountRealNat cubeRes.Y_star cubeRes.Z_star B))
                    (fun p_star =>
                      CostM.bind
                        (scanMatrixTracked Y Z (supportCountRealNat Y Z B))
                        (fun p_init =>
                          CostM.bind
                            (clampDeltaHBTracked remDepth
                              p_star
                              (cubeRes.Y_star.card * cubeRes.Z_star.card)
                              p_init
                              (Y.card * Z.card))
                            (fun Δ =>
                              CostM.bind
                                (recDepthTracked Δ X cubeRes.Y_star cubeRes.Z_star
                                  (submatZeroExt X cubeRes.Y_star A)
                                  (submatZeroExt cubeRes.Y_star cubeRes.Z_star B) α_cap capNum capDen)
                                (fun S_boost =>
                                  CostM.bind (appendListTracked S_star S_boost) (fun S_out =>
                                    scanMatrixPairTracked X Y Z S_out)))))
                else
                  CostM.bind
                    (filterListByTracked (fun sl => decide sl.Z_ell.Nonempty) cubeRes.slices)
                    (fun directSlices =>
                      CostM.bind
                        (mapListTracked
                          (fun sl => scanMatrixTracked sl.Y_ell sl.Z_ell (directSlicePiece B D sl))
                          directSlices)
                        (fun S_direct =>
                          CostM.bind
                            (filterListByTracked
                              (fun sl => decide (cubeRes.Z_star \ sl.Z_ell).Nonempty)
                              cubeRes.slices)
                            (fun activeSlices =>
                              CostM.bind
                                (flatMapListTracked
                                  (fun sl =>
                                    let Z_rem := cubeRes.Z_star \ sl.Z_ell
                                    let α_ell := matDensity sl.X_ell sl.Y_ell sl.A_ell
                                    let q_ell := sl.X_ell.card * sl.Y_ell.card
                                    CostM.bind
                                      (scanMatrixTracked sl.X_ell sl.Y_ell
                                        (supportCountRealNat sl.X_ell sl.Y_ell sl.A_ell))
                                      (fun p_ell =>
                                        CostM.bind
                                          (clampDeltaHATracked remDepth p_ell q_ell capNum capDen)
                                          (fun Δ =>
                                            bucketedRecTracked sl.X_ell sl.Y_ell Z_rem sl.A_ell
                                              (submatZeroExt sl.Y_ell Z_rem B) α_ell D
                                              (fun X' Y'_j Z' A'_j B'_j α'_j j =>
                                                recDepthTracked Δ X' Y'_j Z' A'_j B'_j α'_j
                                                  (2 ^ j * p_ell) q_ell))))
                                  activeSlices)
                                (fun S_rec =>
                                  CostM.bind (appendListTracked S_direct S_star) (fun S_ds =>
                                    CostM.bind (appendListTracked S_ds S_rec) (fun S_out =>
                                      scanMatrixPairTracked X Y Z S_out)))))))))

@[simp]
theorem clampDeltaHBTracked_fst (remDepth p_star q_star p_init q_init : ℕ) :
    (clampDeltaHBTracked remDepth p_star q_star p_init q_init).1 =
      min remDepth (rawDeltaHBNat p_star q_star p_init q_init) :=
  rfl

@[simp]
theorem sStarLoopTracked_fst [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (sStarFuel : ℕ) (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    (ε : ℝ) (S : TwoStageSamplerOracle β ε) (D : ℕ) (α_cap : ℝ) (capNum capDen remDepth : ℕ)
    (recDepthTracked : ℕ → Finset α → Finset β → Finset γ →
      (α → β → ℝ) → (β → γ → ℝ) → ℝ → ℕ → ℕ → CostM (List (CubePiece α β γ))) :
    (sStarLoopTracked sStarFuel X Y Z A B ε S D α_cap capNum capDen remDepth recDepthTracked).1 =
      sStarLoop sStarFuel X Y Z A B ε S D α_cap capNum capDen remDepth
        (fun Δ X' Y' Z' A' B' α' p' q' => (recDepthTracked Δ X' Y' Z' A' B' α' p' q').1) := by
  induction sStarFuel generalizing B with
  | zero => rfl
  | succ fuel ih =>
    unfold sStarLoopTracked sStarLoop
    simp only [CostM.bind_fst, scanMatrixPairTracked_fst]
    by_cases hbase : isSparse3DPiece X Y Z A B D = true
    · rw [if_pos hbase, if_pos hbase]
      rfl
    · rw [if_neg hbase, if_neg hbase]
      simp only [CostM.bind_fst, cappedGoodCubeTracked_fst, ih]
      split_ifs with hmode
      · simp only [CostM.bind_fst, scanMatrixTracked_fst, clampDeltaHBTracked_fst,
          appendListTracked_fst, scanMatrixPairTracked_fst]
      · simp only [CostM.bind_fst, filterListByTracked_fst, mapListTracked_fst,
          scanMatrixTracked_fst, appendListTracked_fst, scanMatrixPairTracked_fst,
          flatMapListTracked_fst]
        congr 1
        refine List.flatMap_congr (fun sl _ => ?_)
        simp only [clampDeltaHATracked_fst]
        exact bucketedRecTracked_fst _ _ _ _ _ _ _ _

lemma sStarLoop_length_pos [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (sStarFuel : ℕ) (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    (ε : ℝ) (S : TwoStageSamplerOracle β ε) (D : ℕ) (α_cap : ℝ) (capNum capDen remDepth : ℕ)
    (recDepth : ℕ → Finset α → Finset β → Finset γ →
      (α → β → ℝ) → (β → γ → ℝ) → ℝ → ℕ → ℕ → List (CubePiece α β γ)) :
    1 ≤ (sStarLoop sStarFuel X Y Z A B ε S D α_cap capNum capDen remDepth recDepth).length := by
  induction sStarFuel generalizing B with
  | zero => simp [sStarLoop]
  | succ fuel ih =>
    unfold sStarLoop
    dsimp only
    by_cases hbase : isSparse3DPiece X Y Z A B D = true
    · rw [if_pos hbase]
      simp
    · rw [if_neg hbase]
      have hstar := ih (zeroOutSubrect B
        (cappedGoodCube X Y Z A B ε gamma3D D α_cap (matDensity Y Z B) S).Y_star
        (cappedGoodCube X Y Z A B ε gamma3D D α_cap (matDensity Y Z B) S).Z_star)
      split_ifs
      · simp only [List.length_append]; omega
      · simp only [List.length_append]; omega

/-- Auxiliary recursion on remaining depth `remDepth = H - h` for Algorithm 5 (`Decompose3D`)
(`cappedABDecomposition'`, `paper.tex` §5.2). -/
noncomputable def cappedABDecompAux [DecidableEq α] [DecidableEq β] [DecidableEq γ] :
    ℕ → Finset α → Finset β → Finset γ →
    (α → β → ℝ) → (β → γ → ℝ) → (ε : ℝ) → TwoStageSamplerOracle β ε → ℕ → ℝ → ℕ → ℕ →
    List (CubePiece α β γ)
  | 0, X, Y, Z, A, B, ε, _S, D, _α_cap, _capNum, _capDen =>
    if isSparse3DPiece X Y Z A B D then
      [baseCase1Piece X Y Z A B ε D]
    else
      baseCase2Decomposition X Y Z A B D
  | rem + 1, X, Y, Z, A, B, ε, S, D, α_cap, capNum, capDen =>
    sStarLoop (rSStarFuel ε D) X Y Z A B ε S D α_cap capNum capDen (rem + 1)
      (fun Δ X' Y' Z' A' B' α' capNum' capDen' =>
        cappedABDecompAux (rem - (Δ - 1)) X' Y' Z' A' B' ε S D α' capNum' capDen')
termination_by remDepth => remDepth
decreasing_by omega

/-- Bottom-up cost-tracked implementation of `cappedABDecompAux` in `CostM`. -/
noncomputable def cappedABDecompAuxTracked [DecidableEq α] [DecidableEq β] [DecidableEq γ] :
    ℕ → Finset α → Finset β → Finset γ →
    (α → β → ℝ) → (β → γ → ℝ) → (ε : ℝ) → TwoStageSamplerOracle β ε → ℕ → ℝ → ℕ → ℕ →
    CostM (List (CubePiece α β γ))
  | 0, X, Y, Z, A, B, ε, _S, D, _α_cap, _capNum, _capDen =>
    CostM.bind (scanMatrixPairTracked X Y Z (isSparse3DPiece X Y Z A B D)) (fun isSparse =>
      if isSparse then
        scanMatrixPairTracked X Y Z [baseCase1Piece X Y Z A B ε D]
      else
        baseCase2DecompositionTracked X Y Z A B D)
  | rem + 1, X, Y, Z, A, B, ε, S, D, α_cap, capNum, capDen =>
    sStarLoopTracked (rSStarFuel ε D) X Y Z A B ε S D α_cap capNum capDen (rem + 1)
      (fun Δ X' Y' Z' A' B' α' capNum' capDen' =>
        cappedABDecompAuxTracked (rem - (Δ - 1)) X' Y' Z' A' B' ε S D α' capNum' capDen')
termination_by remDepth => remDepth
decreasing_by omega

@[simp]
theorem cappedABDecompAuxTracked_fst [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (remDepth : ℕ) (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    (ε : ℝ) (S : TwoStageSamplerOracle β ε) (D : ℕ) (α_cap : ℝ) (capNum capDen : ℕ) :
    (cappedABDecompAuxTracked remDepth X Y Z A B ε S D α_cap capNum capDen).1 =
      cappedABDecompAux remDepth X Y Z A B ε S D α_cap capNum capDen := by
  induction' remDepth using Nat.strong_induction_on with remDepth ih
    generalizing X Y Z A B α_cap capNum capDen
  rcases remDepth with _ | rem
  · rw [cappedABDecompAuxTracked, cappedABDecompAux, CostM.bind_fst, scanMatrixPairTracked_fst]
    split_ifs <;> simp
  · rw [cappedABDecompAuxTracked, cappedABDecompAux, sStarLoopTracked_fst]
    refine congrArg (sStarLoop (rSStarFuel ε D) X Y Z A B ε S D α_cap capNum capDen (rem + 1)) ?_
    funext Δ X' Y' Z' A' B' α' capNum' capDen'
    exact ih (rem - (Δ - 1)) (by omega) X' Y' Z' A' B' α' capNum' capDen'

/-- **Algorithm 5 (`Decompose3D`) (`cappedABDecomposition'`, §5.2 of `paper.tex`)**:
Recursive 3D regularity decomposition at depth $h \le H$. -/
noncomputable def cappedABDecomposition' [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    (ε : ℝ) (S : TwoStageSamplerOracle β ε) (D : ℕ) (α_cap : ℝ) (capNum capDen h H : ℕ) :
    List (CubePiece α β γ) :=
  cappedABDecompAux (H - h) X Y Z A B ε S D α_cap capNum capDen

/-- **Algorithm 5 (`Decompose3D`) Root Entry (`cappedABDecomposition`, `paper.tex` §5.2)**:
Invokes `cappedABDecomposition'` at $\alpha_{\text{cap}} = 1 = 1 / 1$ and root depth $h = 0$ with
maximum depth $H = \text{H3D } D$. -/
noncomputable def cappedABDecomposition [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    (ε : ℝ) (S : TwoStageSamplerOracle β ε) (D : ℕ) : List (CubePiece α β γ) :=
  cappedABDecomposition' X Y Z A B ε S D 1 1 1 0 (H3D D)

/-- Tracked `CostM` implementation of `cappedABDecomposition'`. -/
noncomputable def cappedABDecomposition'Tracked [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    (ε : ℝ) (S : TwoStageSamplerOracle β ε) (D : ℕ) (α_cap : ℝ) (capNum capDen h H : ℕ) :
    CostM (List (CubePiece α β γ)) :=
  cappedABDecompAuxTracked (H - h) X Y Z A B ε S D α_cap capNum capDen

@[simp]
theorem cappedABDecomposition'Tracked_fst [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    (ε : ℝ) (S : TwoStageSamplerOracle β ε) (D : ℕ) (α_cap : ℝ) (capNum capDen h H : ℕ) :
    (cappedABDecomposition'Tracked X Y Z A B ε S D α_cap capNum capDen h H).1 =
      cappedABDecomposition' X Y Z A B ε S D α_cap capNum capDen h H :=
  cappedABDecompAuxTracked_fst (H - h) X Y Z A B ε S D α_cap capNum capDen

/-- Tracked `CostM` implementation of Algorithm 5 (`Decompose3D`) (`cappedABDecompositionTracked`). -/
noncomputable def cappedABDecompositionTracked [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    (ε : ℝ) (S : TwoStageSamplerOracle β ε) (D : ℕ) : CostM (List (CubePiece α β γ)) :=
  cappedABDecomposition'Tracked X Y Z A B ε S D 1 1 1 0 (H3D D)

@[simp]
theorem cappedABDecompositionTracked_fst [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    (ε : ℝ) (S : TwoStageSamplerOracle β ε) (D : ℕ) :
    (cappedABDecompositionTracked X Y Z A B ε S D).1 =
      cappedABDecomposition X Y Z A B ε S D :=
  cappedABDecomposition'Tracked_fst X Y Z A B ε S D 1 1 1 0 (H3D D)

/-- Per-iteration cost factor of `sStarLoopTracked`. -/
noncomputable def abIterCostFactor (c k : ℕ) (ε : ℝ) (D : ℕ) : ℕ :=
  (rCubeFuel ε gamma3D + 1) * goodCubeStepCostFactor c k ε D +
    (D + deltaHACostFactor D + 2) * (rDecompAFuel ε D + 2) + 2404

/-- Per-depth-level cost factor of `cappedABDecompAuxTracked`. -/
noncomputable def abDepthCostFactor (c k : ℕ) (ε : ℝ) (D : ℕ) : ℕ :=
  (rSStarFuel ε D + 2) * abIterCostFactor c k ε D + 4

lemma bucketedRecTracked_snd_le [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X' : Finset α) (Y' : Finset β) (Z' : Finset γ)
    (A' : α → β → ℝ) (B' : β → γ → ℝ) (μ : ℝ) (D K : ℕ)
    (recCallTracked : Finset α → Finset β → Finset γ →
      (α → β → ℝ) → (β → γ → ℝ) → ℝ → ℕ → CostM (List (CubePiece α β γ)))
    (hrec : ∀ j < D, (dyadicColBucket X' Y' A' μ j).Nonempty →
      let Y'_j := dyadicColBucket X' Y' A' μ j
      (recCallTracked X' Y'_j Z'
        (submatZeroExt X' Y'_j A') (submatZeroExt Y'_j Z' B') (dyadicColAlpha μ j) j).2 ≤
      K * (recCallTracked X' Y'_j Z'
        (submatZeroExt X' Y'_j A') (submatZeroExt Y'_j Z' B') (dyadicColAlpha μ j) j).1.length) :
    (bucketedRecTracked X' Y' Z' A' B' μ D recCallTracked).2 ≤
      (K + 1) * (bucketedRecTracked X' Y' Z' A' B' μ D recCallTracked).1.length +
        (D + 1) * (X'.card + Y'.card + Z'.card + 2) ^ 2 := by
  unfold bucketedRecTracked
  simp only [CostM.bind_snd, dyadicColBucketingTracked_snd, dyadicColBucketingTracked_fst,
    filterListByTracked_snd, filterListByTracked_fst, scanMatrixTracked_snd,
    CostM.bind_fst, scanMatrixTracked_fst]
  have hlen_buck : (dyadicColBucketing X' Y' A' μ D).length = D := by
    simp [dyadicColBucketing]
  set active := (dyadicColBucketing X' Y' A' μ D).filter (fun b : ℕ × Finset β => decide b.2.Nonempty)
  have hflat := flatMapListTracked_snd_le_linear
    (fun b : ℕ × Finset β =>
      recCallTracked X' b.2 Z'
        (submatZeroExt X' b.2 A')
        (submatZeroExt b.2 Z' B') (dyadicColAlpha μ b.1) b.1)
    active K 0
    (fun b hb => by
      rw [List.mem_filter, decide_eq_true_eq] at hb
      rcases hb with ⟨hb_mem, hb_ne⟩
      unfold dyadicColBucketing at hb_mem
      rw [List.mem_map] at hb_mem
      rcases hb_mem with ⟨j, hj_range, rfl⟩
      rw [List.mem_range] at hj_range
      simpa using hrec j hj_range hb_ne)
  rw [zero_add, one_mul] at hflat
  have hlen_active : active.length ≤ D :=
    (List.length_filter_le _ _).trans hlen_buck.le
  have hsq : (X'.card + Y'.card + Z'.card + 2) ^ 2 =
      (X'.card + Y'.card + Z'.card + 2) * (X'.card + Y'.card + Z'.card + 2) := sq _
  have hquad1 : X'.card * Y'.card + 4 ≤ (X'.card + Y'.card + Z'.card + 2) ^ 2 := by
    rw [hsq]; nlinarith
  have hquad2 : Y'.card * Z'.card + 4 ≤ (X'.card + Y'.card + Z'.card + 2) ^ 2 := by
    rw [hsq]; nlinarith
  have hD_quad :
      (D * (X'.card * Y'.card + 2) + 1) +
        ((dyadicColBucketing X' Y' A' μ D).length + 1) + active.length + 1 +
        (Y'.card * Z'.card + 1) ≤
        (D + 1) * (X'.card + Y'.card + Z'.card + 2) ^ 2 := by
    calc
      (D * (X'.card * Y'.card + 2) + 1) +
          ((dyadicColBucketing X' Y' A' μ D).length + 1) + active.length + 1 +
          (Y'.card * Z'.card + 1)
        ≤ (D * (X'.card * Y'.card + 2) + 1) + (D + 1) + D + 1 + (Y'.card * Z'.card + 1) := by omega
      _ = D * (X'.card * Y'.card + 4) + (Y'.card * Z'.card + 4) := by ring
      _ ≤ D * (X'.card + Y'.card + Z'.card + 2) ^ 2 + (X'.card + Y'.card + Z'.card + 2) ^ 2 :=
          Nat.add_le_add (Nat.mul_le_mul_left D hquad1) hquad2
      _ = (D + 1) * (X'.card + Y'.card + Z'.card + 2) ^ 2 := by ring
  omega

set_option maxHeartbeats 800000 in
lemma sStarLoopTracked_snd_le [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (sStarFuel : ℕ) (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    (ε : ℝ) (S : TwoStageSamplerOracle β ε) (D : ℕ) (α_cap : ℝ)
    (capNum capDen remDepth K S_bound : ℕ)
    (hXYZ_bound : X.card + Y.card + Z.card + 2 ≤ S_bound)
    (hcapNum : capNum ≤ 2 ^ D * S_bound ^ 2)
    (hcapDen : capDen ≤ S_bound ^ 2)
    (recDepthTracked : ℕ → Finset α → Finset β → Finset γ →
      (α → β → ℝ) → (β → γ → ℝ) → ℝ → ℕ → ℕ → CostM (List (CubePiece α β γ)))
    (hrec : ∀ Δ X' Y' Z' A' B' α' capNum' capDen',
      X'.card + Y'.card + Z'.card + 2 ≤ S_bound →
      capNum' ≤ 2 ^ D * S_bound ^ 2 →
      capDen' ≤ S_bound ^ 2 →
      (recDepthTracked Δ X' Y' Z' A' B' α' capNum' capDen').2 ≤
        K * (recDepthTracked Δ X' Y' Z' A' B' α' capNum' capDen').1.length) :
    (sStarLoopTracked sStarFuel X Y Z A B ε S D α_cap capNum capDen remDepth recDepthTracked).2 ≤
      (K + 2 + (sStarFuel + 1) * (abIterCostFactor S.c S.k ε D * S_bound ^ 2)) *
        (sStarLoopTracked sStarFuel X Y Z A B ε S D α_cap capNum capDen remDepth
          recDepthTracked).1.length := by
  set Q := S_bound ^ 2
  set I := abIterCostFactor S.c S.k ε D * Q
  have hS_ge_2 : 2 ≤ S_bound := by omega
  have hQ_sub : (X.card + Y.card + Z.card + 2) ^ 2 ≤ Q :=
    Nat.pow_le_pow_left hXYZ_bound 2
  have hbase_Q : X.card * Y.card + Y.card * Z.card + 1 ≤ Q := by
    have : X.card * Y.card + Y.card * Z.card + 1 ≤ (X.card + Y.card + Z.card + 2) ^ 2 := by
      rw [sq]; nlinarith
    exact this.trans hQ_sub
  have hQ_ge_4 : 4 ≤ Q := by
    change 4 ≤ S_bound ^ 2
    rw [sq]; nlinarith
  have hiter_ge_4 : 4 ≤ abIterCostFactor S.c S.k ε D := by unfold abIterCostFactor; omega
  have hI_ge_4Q : 4 * Q ≤ I := Nat.mul_le_mul_right Q hiter_ge_4
  induction sStarFuel generalizing B with
  | zero =>
    unfold sStarLoopTracked
    simp only [scanMatrixPairTracked_snd, scanMatrixPairTracked_fst, List.length_singleton,
      mul_one, zero_add, one_mul]
    omega
  | succ fuel ih =>
    unfold sStarLoopTracked
    rw [CostM.bind_snd, CostM.bind_fst, scanMatrixPairTracked_snd, scanMatrixPairTracked_fst]
    by_cases hbase : isSparse3DPiece X Y Z A B D = true
    · rw [if_pos hbase]
      simp only [scanMatrixPairTracked_snd, scanMatrixPairTracked_fst, List.length_singleton, mul_one]
      have h2 : I ≤ (fuel + 1 + 1) * I := Nat.le_mul_of_pos_left _ (by omega)
      omega
    · rw [if_neg hbase, CostM.bind_snd, CostM.bind_fst,
        cappedGoodCubeTracked_fst, CostM.bind_snd, CostM.bind_fst]
      set cubeRes := cappedGoodCube X Y Z A B ε gamma3D D α_cap (matDensity Y Z B) S
      set B_rem := zeroOutSubrect B cubeRes.Y_star cubeRes.Z_star
      set starRun :=
        sStarLoopTracked fuel X Y Z A B_rem ε S D α_cap capNum capDen remDepth recDepthTracked
      have hstar_len : 1 ≤ starRun.1.length := by
        dsimp only [starRun]
        rw [sStarLoopTracked_fst]
        exact sStarLoop_length_pos _ _ _ _ _ _ _ _ _ _ _ _ _ _
      have hcube_cost :
          (cappedGoodCubeTracked X Y Z A B ε gamma3D D α_cap (matDensity Y Z B) S).2 ≤
            ((rCubeFuel ε gamma3D + 1) * goodCubeStepCostFactor S.c S.k ε D) * Q := by
        have h := cappedGoodCubeTracked_snd_le X Y Z A B ε gamma3D D α_cap (matDensity Y Z B) S
        have h1 :
            (rCubeFuel ε gamma3D + 1) *
                ((X.card + Y.card + Z.card + 2) ^ 2 * goodCubeStepCostFactor S.c S.k ε D) ≤
              (rCubeFuel ε gamma3D + 1) * (Q * goodCubeStepCostFactor S.c S.k ε D) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hQ_sub)
        have hring :
            (rCubeFuel ε gamma3D + 1) * (Q * goodCubeStepCostFactor S.c S.k ε D) =
              ((rCubeFuel ε gamma3D + 1) * goodCubeStepCostFactor S.c S.k ε D) * Q := by ring
        exact (h.trans h1).trans_eq hring
      rcases cappedGoodCube_sub_and_slices_len X Y Z A B ε S gamma3D D α_cap (matDensity Y Z B) with
        ⟨hY_sub, hZ_sub, hslices_len, hslices_sub⟩
      change cubeRes.Y_star ⊆ Y at hY_sub
      change cubeRes.Z_star ⊆ Z at hZ_sub
      change cubeRes.slices.length ≤ rDecompAFuel ε D + 1 at hslices_len
      have hih : starRun.2 ≤ (K + 2 + (fuel + 1) * I) * starRun.1.length := ih B_rem
      have hsucc : (fuel + 1 + 1) * I = (fuel + 1) * I + I := Nat.succ_mul (fuel + 1) I
      set scanCost := X.card * Y.card + Y.card * Z.card + 1
      by_cases hmode : cubeRes.mode = CubeMode.bBoost
      · rw [if_pos hmode]
        simp only [CostM.bind_snd, CostM.bind_fst, scanMatrixTracked_snd, scanMatrixTracked_fst,
          clampDeltaHBTracked_fst, appendListTracked_snd, appendListTracked_fst,
          scanMatrixPairTracked_snd, scanMatrixPairTracked_fst, List.length_append]
        set Δ := min remDepth
          (rawDeltaHBNat
            (supportCountRealNat cubeRes.Y_star cubeRes.Z_star B)
            (cubeRes.Y_star.card * cubeRes.Z_star.card)
            (supportCountRealNat Y Z B)
            (Y.card * Z.card))
        set boostRun := recDepthTracked Δ X cubeRes.Y_star cubeRes.Z_star
          (submatZeroExt X cubeRes.Y_star A)
          (submatZeroExt cubeRes.Y_star cubeRes.Z_star B) α_cap capNum capDen
        have hYstar_le : cubeRes.Y_star.card ≤ Y.card := Finset.card_le_card hY_sub
        have hZstar_le : cubeRes.Z_star.card ≤ Z.card := Finset.card_le_card hZ_sub
        have hboost : boostRun.2 ≤ K * boostRun.1.length :=
          hrec Δ X cubeRes.Y_star cubeRes.Z_star
            (submatZeroExt X cubeRes.Y_star A)
            (submatZeroExt cubeRes.Y_star cubeRes.Z_star B) α_cap capNum capDen
            (by omega) hcapNum hcapDen
        have hboost2 : boostRun.2 ≤ (K + 2 + (fuel + 1 + 1) * I) * boostRun.1.length :=
          hboost.trans (Nat.mul_le_mul_right _ (by omega))
        set deltaHBRun := clampDeltaHBTracked remDepth
          (supportCountRealNat cubeRes.Y_star cubeRes.Z_star B)
          (cubeRes.Y_star.card * cubeRes.Z_star.card)
          (supportCountRealNat Y Z B)
          (Y.card * Z.card)
        have hYZstar_mul_le : cubeRes.Y_star.card * cubeRes.Z_star.card ≤ Y.card * Z.card :=
          Nat.mul_le_mul hYstar_le hZstar_le
        have hYZstar_Q : cubeRes.Y_star.card * cubeRes.Z_star.card + 1 ≤ Q := by omega
        have hYZ_Q : Y.card * Z.card + 1 ≤ Q := by omega
        have hdeltaHB_le :
            (cubeRes.Y_star.card * cubeRes.Z_star.card + 1) +
              (Y.card * Z.card + 1) + deltaHBRun.2 ≤ 2400 * Q := by
          have hYZstar_le : cubeRes.Y_star.card * cubeRes.Z_star.card ≤ Q := by omega
          have hYZ_le : Y.card * Z.card ≤ Q := by omega
          have hd := clampDeltaHBTracked_snd_le (S := S_bound) (remDepth := remDepth) hS_ge_2
            ((supportCountRealNat_le_card_mul cubeRes.Y_star cubeRes.Z_star B).trans hYZstar_le)
            hYZstar_le
            ((supportCountRealNat_le_card_mul Y Z B).trans hYZ_le)
            hYZ_le
          change deltaHBRun.2 + 2 * Q ≤ 2400 * Q at hd
          omega
        set boostScanCost :=
          (cubeRes.Y_star.card * cubeRes.Z_star.card + 1) + (Y.card * Z.card + 1) + deltaHBRun.2
        have hstep_I :
            scanCost + (cappedGoodCubeTracked X Y Z A B ε gamma3D D α_cap (matDensity Y Z B) S).2 +
              boostScanCost + 1 + scanCost + 1 ≤ I := by
          have hfac :
              (rCubeFuel ε gamma3D + 1) * goodCubeStepCostFactor S.c S.k ε D + 2403 ≤
                abIterCostFactor S.c S.k ε D := by
            unfold abIterCostFactor; omega
          calc
            scanCost + (cappedGoodCubeTracked X Y Z A B ε gamma3D D α_cap (matDensity Y Z B) S).2 +
                boostScanCost + 1 + scanCost + 1
              ≤ ((rCubeFuel ε gamma3D + 1) * goodCubeStepCostFactor S.c S.k ε D) * Q + 2403 * Q := by omega
            _ = ((rCubeFuel ε gamma3D + 1) * goodCubeStepCostFactor S.c S.k ε D + 2403) * Q := by ring
            _ ≤ abIterCostFactor S.c S.k ε D * Q := Nat.mul_le_mul_right Q hfac
        have hstep_star :
            (scanCost + (cappedGoodCubeTracked X Y Z A B ε gamma3D D α_cap (matDensity Y Z B) S).2 +
              boostScanCost + 1 + scanCost) + starRun.1.length ≤
              I * starRun.1.length := by
          have hmul := Nat.mul_le_mul_right starRun.1.length hstep_I
          have h1 :
              scanCost + (cappedGoodCubeTracked X Y Z A B ε gamma3D D α_cap (matDensity Y Z B) S).2 +
                boostScanCost + 1 + scanCost ≤
              (scanCost + (cappedGoodCubeTracked X Y Z A B ε gamma3D D α_cap (matDensity Y Z B) S).2 +
                boostScanCost + 1 + scanCost) * starRun.1.length :=
            Nat.le_mul_of_pos_right _ hstar_len
          linarith
        rw [Nat.mul_add (K + 2 + (fuel + 1 + 1) * I), hsucc]
        have hstar_comb :
            starRun.2 + ((scanCost + (cappedGoodCubeTracked X Y Z A B ε gamma3D D α_cap (matDensity Y Z B) S).2 +
              boostScanCost + 1 + scanCost) + starRun.1.length) ≤
            (K + 2 + ((fuel + 1) * I + I)) * starRun.1.length := by
          linarith
        dsimp only [scanCost, boostScanCost] at hstar_comb ⊢
        linarith
      · rw [if_neg hmode]
        simp only [CostM.bind_snd, CostM.bind_fst, filterListByTracked_snd, filterListByTracked_fst,
          mapListTracked_fst, scanMatrixTracked_fst,
          appendListTracked_snd, appendListTracked_fst,
          scanMatrixPairTracked_snd, scanMatrixPairTracked_fst, List.length_append, List.length_map]
        set directSlices := cubeRes.slices.filter (fun sl => decide sl.Z_ell.Nonempty)
        set activeSlices := cubeRes.slices.filter (fun sl => decide (cubeRes.Z_star \ sl.Z_ell).Nonempty)
        set dirRun := mapListTracked
          (fun sl => scanMatrixTracked sl.Y_ell sl.Z_ell (directSlicePiece B D sl))
          directSlices
        have hdir_len : directSlices.length ≤ rDecompAFuel ε D + 1 :=
          (List.length_filter_le _ _).trans hslices_len
        have hdir : dirRun.2 ≤ (Q + 1) * directSlices.length + 1 := by
          have h := mapListTracked_snd_le_const
            (fun sl => scanMatrixTracked sl.Y_ell sl.Z_ell (directSlicePiece B D sl))
            Q directSlices
            (fun sl hsl => by
              have hsl_mem : sl ∈ cubeRes.slices := (List.mem_filter.mp hsl).1
              rcases hslices_sub sl hsl_mem with ⟨_hslX, hslY, hslZ⟩
              have hY_ell : sl.Y_ell.card ≤ Y.card :=
                (Finset.card_le_card hslY).trans (Finset.card_le_card hY_sub)
              have hZ_ell : sl.Z_ell.card ≤ Z.card :=
                (Finset.card_le_card hslZ).trans (Finset.card_le_card hZ_sub)
              have hYZ_ell : sl.Y_ell.card * sl.Z_ell.card ≤ Y.card * Z.card :=
                Nat.mul_le_mul hY_ell hZ_ell
              simp only [scanMatrixTracked_snd]
              omega)
          dsimp only [dirRun]
          linarith
        set f_rec : GoodCubeSlice α β γ → CostM (List (CubePiece α β γ)) := fun sl =>
          let Z_rem := cubeRes.Z_star \ sl.Z_ell
          let α_ell := matDensity sl.X_ell sl.Y_ell sl.A_ell
          let q_ell := sl.X_ell.card * sl.Y_ell.card
          CostM.bind
            (scanMatrixTracked sl.X_ell sl.Y_ell
              (supportCountRealNat sl.X_ell sl.Y_ell sl.A_ell))
            (fun p_ell =>
              CostM.bind
                (clampDeltaHATracked remDepth p_ell q_ell capNum capDen)
                (fun Δ =>
                  bucketedRecTracked sl.X_ell sl.Y_ell Z_rem sl.A_ell
                    (submatZeroExt sl.Y_ell Z_rem B) α_ell D
                    (fun X' Y'_j Z' A'_j B'_j α'_j j =>
                      recDepthTracked Δ X' Y'_j Z' A'_j B'_j α'_j (2 ^ j * p_ell) q_ell)))
        set recRun := flatMapListTracked f_rec activeSlices
        have hactive_len : activeSlices.length ≤ rDecompAFuel ε D + 1 :=
          (List.length_filter_le _ _).trans hslices_len
        have hflat :
            recRun.2 ≤ (K + 2) * recRun.1.length +
              (((D + deltaHACostFactor D) * Q + 1) * activeSlices.length + 1) :=
          flatMapListTracked_snd_le_linear f_rec
            activeSlices (K + 1) ((D + deltaHACostFactor D) * Q)
            (fun sl hsl => by
              have hsl_mem : sl ∈ cubeRes.slices := (List.mem_filter.mp hsl).1
              rcases hslices_sub sl hsl_mem with ⟨hslX, hslY, _hslZ⟩
              have hZrem_sub : cubeRes.Z_star \ sl.Z_ell ⊆ Z :=
                Finset.sdiff_subset.trans hZ_sub
              have h1 : sl.X_ell.card ≤ X.card := Finset.card_le_card hslX
              have h2 : sl.Y_ell.card ≤ Y.card := (Finset.card_le_card hslY).trans (Finset.card_le_card hY_sub)
              have h3 : (cubeRes.Z_star \ sl.Z_ell).card ≤ Z.card := Finset.card_le_card hZrem_sub
              have hsl_S_bound :
                  sl.X_ell.card + sl.Y_ell.card + (cubeRes.Z_star \ sl.Z_ell).card + 2 ≤ S_bound := by
                omega
              have hcard_le :
                  (sl.X_ell.card + sl.Y_ell.card + (cubeRes.Z_star \ sl.Z_ell).card + 2) ^ 2 ≤ Q :=
                Nat.pow_le_pow_left hsl_S_bound 2
              have hXY_ell_mul : sl.X_ell.card * sl.Y_ell.card ≤ X.card * Y.card := Nat.mul_le_mul h1 h2
              have hXY_ell_Q : sl.X_ell.card * sl.Y_ell.card + 1 ≤ Q := by omega
              have hXY_ell_le : sl.X_ell.card * sl.Y_ell.card ≤ Q := by omega
              have hp_ell_le : supportCountRealNat sl.X_ell sl.Y_ell sl.A_ell ≤ Q :=
                (supportCountRealNat_le_card_mul _ _ _).trans hXY_ell_le
              have hdeltaHA_le :
                  (clampDeltaHATracked remDepth
                    (supportCountRealNat sl.X_ell sl.Y_ell sl.A_ell)
                    (sl.X_ell.card * sl.Y_ell.card)
                    capNum capDen).2 + 2 * Q ≤ deltaHACostFactor D * Q :=
                clampDeltaHATracked_snd_le (D := D) (S := S_bound) hS_ge_2
                  hp_ell_le hXY_ell_le hcapNum hcapDen
              have hb := bucketedRecTracked_snd_le sl.X_ell sl.Y_ell (cubeRes.Z_star \ sl.Z_ell)
                sl.A_ell (submatZeroExt sl.Y_ell (cubeRes.Z_star \ sl.Z_ell) B)
                (matDensity sl.X_ell sl.Y_ell sl.A_ell) D K
                (fun X' Y'_j Z' A'_j B'_j α'_j j =>
                  recDepthTracked
                    (min remDepth
                      (rawDeltaHANat
                        (supportCountRealNat sl.X_ell sl.Y_ell sl.A_ell)
                        (sl.X_ell.card * sl.Y_ell.card) capNum capDen))
                    X' Y'_j Z' A'_j B'_j α'_j
                    (2 ^ j * supportCountRealNat sl.X_ell sl.Y_ell sl.A_ell)
                    (sl.X_ell.card * sl.Y_ell.card))
                (fun j hj _ => by
                  have hbuck_card :
                      (dyadicColBucket sl.X_ell sl.Y_ell sl.A_ell
                        (matDensity sl.X_ell sl.Y_ell sl.A_ell) j).card ≤ sl.Y_ell.card :=
                    Finset.card_le_card (dyadicColBucket_subset _ _ _ _ _)
                  have h2j : 2 ^ j ≤ 2 ^ D := Nat.pow_le_pow_right (by norm_num) (by omega)
                  have hcapNum' :
                      2 ^ j * supportCountRealNat sl.X_ell sl.Y_ell sl.A_ell ≤ 2 ^ D * Q :=
                    Nat.mul_le_mul h2j hp_ell_le
                  exact hrec _ _ _ _ _ _ _ _ _ (by omega) hcapNum' hXY_ell_le)
              have hb2 := hb.trans (Nat.add_le_add_left (Nat.mul_le_mul_left (D + 1) hcard_le) _)
              dsimp only [f_rec]
              simp only [CostM.bind_snd, CostM.bind_fst,
                scanMatrixTracked_snd, scanMatrixTracked_fst, clampDeltaHATracked_fst]
              linarith)
        set stepFixed :=
          scanCost + (cappedGoodCubeTracked X Y Z A B ε gamma3D D α_cap (matDensity Y Z B) S).2 +
            2 * (cubeRes.slices.length + 1) + dirRun.2 +
            (((D + deltaHACostFactor D) * Q + 1) * activeSlices.length + 1) + 2 + scanCost
        have hstep_I : stepFixed + 1 ≤ I := by
          have hdir_split :
              dirRun.2 ≤ (rDecompAFuel ε D + 1) * Q + (rDecompAFuel ε D + 1) + 1 := by
            calc
              dirRun.2 ≤ (Q + 1) * directSlices.length + 1 := hdir
              _ ≤ (Q + 1) * (rDecompAFuel ε D + 1) + 1 :=
                  Nat.add_le_add_right (Nat.mul_le_mul_left _ hdir_len) 1
              _ = (rDecompAFuel ε D + 1) * Q + (rDecompAFuel ε D + 1) + 1 := by ring
          have hact_split :
              ((D + deltaHACostFactor D) * Q + 1) * activeSlices.length ≤
                ((D + deltaHACostFactor D) * (rDecompAFuel ε D + 1)) * Q +
                  (rDecompAFuel ε D + 1) := by
            calc
              ((D + deltaHACostFactor D) * Q + 1) * activeSlices.length
                ≤ ((D + deltaHACostFactor D) * Q + 1) * (rDecompAFuel ε D + 1) :=
                    Nat.mul_le_mul_left _ hactive_len
              _ = ((D + deltaHACostFactor D) * (rDecompAFuel ε D + 1)) * Q +
                    (rDecompAFuel ε D + 1) := by ring
          have hslices_Q :
              2 * (cubeRes.slices.length + 1) + 2 * (rDecompAFuel ε D + 1) + 2 ≤
                (rDecompAFuel ε D + 2) * Q := by
            have h1 :
                2 * (cubeRes.slices.length + 1) + 2 * (rDecompAFuel ε D + 1) + 2 ≤
                  (rDecompAFuel ε D + 2) * 4 := by omega
            exact h1.trans (Nat.mul_le_mul_left _ hQ_ge_4)
          have hsum_A :
              ((D + deltaHACostFactor D) * (rDecompAFuel ε D + 1)) * Q +
                (rDecompAFuel ε D + 1) * Q +
                (rDecompAFuel ε D + 2) * Q ≤
                ((D + deltaHACostFactor D + 2) * (rDecompAFuel ε D + 2)) * Q := by
            rw [← Nat.add_mul, ← Nat.add_mul]
            exact Nat.mul_le_mul_right Q (by nlinarith)
          have hfac_le :
              (rCubeFuel ε gamma3D + 1) * goodCubeStepCostFactor S.c S.k ε D +
                (D + deltaHACostFactor D + 2) * (rDecompAFuel ε D + 2) + 4 ≤
                  abIterCostFactor S.c S.k ε D := by
            unfold abIterCostFactor
            omega
          calc
            stepFixed + 1
              ≤ ((rCubeFuel ε gamma3D + 1) * goodCubeStepCostFactor S.c S.k ε D) * Q +
                  (((D + deltaHACostFactor D) * (rDecompAFuel ε D + 1)) * Q +
                    (rDecompAFuel ε D + 1) * Q +
                    (rDecompAFuel ε D + 2) * Q) +
                  4 * Q := by
                dsimp only [stepFixed]
                linarith
            _ ≤ ((rCubeFuel ε gamma3D + 1) * goodCubeStepCostFactor S.c S.k ε D) * Q +
                  ((D + deltaHACostFactor D + 2) * (rDecompAFuel ε D + 2)) * Q + 4 * Q := by linarith
            _ = (((rCubeFuel ε gamma3D + 1) * goodCubeStepCostFactor S.c S.k ε D) +
                  (D + deltaHACostFactor D + 2) * (rDecompAFuel ε D + 2) + 4) * Q := by ring
            _ ≤ abIterCostFactor S.c S.k ε D * Q := Nat.mul_le_mul_right Q hfac_le
        have hstep_star :
            stepFixed + starRun.1.length ≤ I * starRun.1.length := by
          have hmul := Nat.mul_le_mul_right starRun.1.length hstep_I
          have h1 : stepFixed ≤ stepFixed * starRun.1.length :=
            Nat.le_mul_of_pos_right _ hstar_len
          linarith
        have hdir_le :
            2 * directSlices.length ≤ (K + 2 + (fuel + 1 + 1) * I) * directSlices.length :=
          Nat.mul_le_mul_right _ (by omega)
        have hrec_le :
            (K + 2) * recRun.1.length ≤ (K + 2 + (fuel + 1 + 1) * I) * recRun.1.length :=
          Nat.mul_le_mul_right _ (by omega)
        rw [Nat.mul_add (K + 2 + (fuel + 1 + 1) * I),
          Nat.mul_add (K + 2 + (fuel + 1 + 1) * I)]
        have hstar_comb :
            starRun.2 + (stepFixed + starRun.1.length) ≤
              (K + 2 + (fuel + 1 + 1) * I) * starRun.1.length := by
          rw [hsucc]
          linarith
        dsimp only [stepFixed, scanCost] at hstar_comb ⊢
        linarith

/-- Total operation bound for `cappedABDecompAuxTracked` (Lemmas 5.4, 5.5 & 5.9 (`\label{lem:children-invariants}`, `\label{lem:potential}`, `\label{lem:recurrence}`)). -/
theorem cappedABDecompAuxTracked_snd_le [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (remDepth : ℕ) (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    (ε : ℝ) (S : TwoStageSamplerOracle β ε) (D : ℕ) (α_cap : ℝ)
    (capNum capDen S_bound : ℕ)
    (hXYZ_bound : X.card + Y.card + Z.card + 2 ≤ S_bound)
    (hcapNum : capNum ≤ 2 ^ D * S_bound ^ 2)
    (hcapDen : capDen ≤ S_bound ^ 2) :
    (cappedABDecompAuxTracked remDepth X Y Z A B ε S D α_cap capNum capDen).2 ≤
      ((remDepth + 1) * abDepthCostFactor S.c S.k ε D * S_bound ^ 2) *
        (cappedABDecompAuxTracked remDepth X Y Z A B ε S D α_cap capNum capDen).1.length := by
  induction' remDepth using Nat.strong_induction_on with remDepth ih
    generalizing X Y Z A B α_cap capNum capDen
  set Q := S_bound ^ 2
  have hQ_sub : (X.card + Y.card + Z.card + 2) ^ 2 ≤ Q :=
    Nat.pow_le_pow_left hXYZ_bound 2
  have hbase_Q : X.card * Y.card + Y.card * Z.card + 1 ≤ Q := by
    have : X.card * Y.card + Y.card * Z.card + 1 ≤ (X.card + Y.card + Z.card + 2) ^ 2 := by
      rw [sq]; nlinarith
    exact this.trans hQ_sub
  have hbase_Q2 : X.card * Y.card + Y.card * Z.card + 2 ≤ Q := by
    have : X.card * Y.card + Y.card * Z.card + 2 ≤ (X.card + Y.card + Z.card + 2) ^ 2 := by
      rw [sq]; nlinarith
    exact this.trans hQ_sub
  have hQ_ge_4 : 4 ≤ Q := by
    have : 2 ≤ S_bound := by omega
    change 4 ≤ S_bound ^ 2
    rw [sq]; nlinarith
  have hdepth_ge_4 : 4 ≤ abDepthCostFactor S.c S.k ε D := by unfold abDepthCostFactor; omega
  rcases remDepth with _ | rem
  · rw [cappedABDecompAuxTracked, CostM.bind_snd, CostM.bind_fst,
      scanMatrixPairTracked_snd, scanMatrixPairTracked_fst]
    split_ifs with hbase
    · simp only [scanMatrixPairTracked_snd, scanMatrixPairTracked_fst, List.length_singleton,
        mul_one, zero_add, one_mul]
      have : 4 * Q ≤ abDepthCostFactor S.c S.k ε D * Q := Nat.mul_le_mul_right Q hdepth_ge_4
      omega
    · rw [baseCase2DecompositionTracked_fst]
      have hbc2 := baseCase2DecompositionTracked_snd_le X Y Z A B D
      set pieces := baseCase2Decomposition X Y Z A B D
      have hlen2 : 1 ≤ pieces.length :=
        (baseCase2Decomposition_length_bounds X Y Z A B D).1
      have hmul1 :
          pieces.length * (X.card * Y.card + Y.card * Z.card + 2) ≤
            pieces.length * Q :=
        Nat.mul_le_mul_left _ hbase_Q2
      have hmul2 :
          (X.card * Y.card + Y.card * Z.card + 1) + (pieces.length * Q + 1) ≤
            (4 * Q) * pieces.length := by
        nlinarith
      have hmul3 :
          (4 * Q) * pieces.length ≤
            ((0 + 1) * abDepthCostFactor S.c S.k ε D * Q) * pieces.length := by
        rw [zero_add, one_mul]
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right Q hdepth_ge_4)
      linarith
  · rw [cappedABDecompAuxTracked]
    set K := (rem + 1) * abDepthCostFactor S.c S.k ε D * Q
    have hsstar := sStarLoopTracked_snd_le (rSStarFuel ε D) X Y Z A B ε S D α_cap
      capNum capDen (rem + 1) K S_bound hXYZ_bound hcapNum hcapDen
      (fun Δ X' Y' Z' A' B' α' capNum' capDen' =>
        cappedABDecompAuxTracked (rem - (Δ - 1)) X' Y' Z' A' B' ε S D α' capNum' capDen')
      (fun Δ X' Y' Z' A' B' α' capNum' capDen' hXYZ' hcapNum' hcapDen' => by
        have hlt : rem - (Δ - 1) < rem + 1 := by omega
        have hih := ih (rem - (Δ - 1)) hlt X' Y' Z' A' B' α' capNum' capDen'
          hXYZ' hcapNum' hcapDen'
        have hrem_le : rem - (Δ - 1) + 1 ≤ rem + 1 := by omega
        have hK_le :
            (rem - (Δ - 1) + 1) * abDepthCostFactor S.c S.k ε D * Q ≤ K := by
          unfold K
          exact Nat.mul_le_mul_right Q (Nat.mul_le_mul_right _ hrem_le)
        exact hih.trans (Nat.mul_le_mul_right _ hK_le))
    refine hsstar.trans (Nat.mul_le_mul_right _ ?_)
    change K + 2 + (rSStarFuel ε D + 1) * (abIterCostFactor S.c S.k ε D * Q) ≤
      (rem + 1 + 1) * abDepthCostFactor S.c S.k ε D * Q
    have hfactor :
        (rem + 1 + 1) * abDepthCostFactor S.c S.k ε D * Q =
          K + abDepthCostFactor S.c S.k ε D * Q := by
      unfold K
      ring
    rw [hfactor]
    have h2 :
        2 + (rSStarFuel ε D + 1) * (abIterCostFactor S.c S.k ε D * Q) ≤
          abDepthCostFactor S.c S.k ε D * Q := by
      calc
        2 + (rSStarFuel ε D + 1) * (abIterCostFactor S.c S.k ε D * Q)
          ≤ 2 * Q + ((rSStarFuel ε D + 1) * abIterCostFactor S.c S.k ε D) * Q := by
            rw [← Nat.mul_assoc]
            omega
        _ = ((rSStarFuel ε D + 1) * abIterCostFactor S.c S.k ε D + 2) * Q := by ring
        _ ≤ abDepthCostFactor S.c S.k ε D * Q :=
            Nat.mul_le_mul_right Q (by unfold abDepthCostFactor; nlinarith)
    linarith

/-- Total operation bound for `cappedABDecompositionTracked` at the root. -/
theorem cappedABDecompositionTracked_snd_le [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    (ε : ℝ) (S : TwoStageSamplerOracle β ε) (D : ℕ) :
    (cappedABDecompositionTracked X Y Z A B ε S D).2 ≤
      ((H3D D + 1) * abDepthCostFactor S.c S.k ε D * (X.card + Y.card + Z.card + 2) ^ 2) *
        (cappedABDecomposition X Y Z A B ε S D).length := by
  unfold cappedABDecompositionTracked cappedABDecomposition
    cappedABDecomposition'Tracked cappedABDecomposition'
  simp only [Nat.sub_zero, ← cappedABDecompAuxTracked_fst]
  have hQ_ge_1 : 1 ≤ (X.card + Y.card + Z.card + 2) ^ 2 := by rw [sq]; nlinarith
  have hcapNum : 1 ≤ 2 ^ D * (X.card + Y.card + Z.card + 2) ^ 2 := by
    have : 1 ≤ 2 ^ D := Nat.one_le_two_pow
    nlinarith
  exact cappedABDecompAuxTracked_snd_le (H3D D) X Y Z A B ε S D 1 1 1
    (X.card + Y.card + Z.card + 2) le_rfl hcapNum hQ_ge_1


/-- **Fuel & Scale-Drop Step for `cappedGoodCube` (`goodCube_fuel_step`, `paper.tex` §5.5)**:
Whenever $(X, Y, Z, A, B)$ is non-empty with binary $A, B$ and $\mathbb{E}_{Y \times Z}[B] > 2^{-D}$,
letting `res := cappedGoodCube X Y Z A B ε S gamma3D D α_cap (matDensity Y Z B)` and
`B_rem := zeroOutSubrect B res.Y_star res.Z_star`:
1. $2^{-S_B D} \le 2^D M_{\text{cube}}(\varepsilon, \gamma_{3D}, D) (\mathbb{E}[B] - \mathbb{E}[B_{\text{rem}}])$,
2. $1 \le (\mathbb{E}[B] - \mathbb{E}[B_{\text{rem}}]) \cdot 2^{D + D^2} M_{\text{cube}}(\varepsilon, \gamma_{3D}, D)$. -/
lemma goodCube_fuel_step [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {X : Finset α} {Y : Finset β} {Z : Finset γ}
    {A : α → β → ℝ} {B : β → γ → ℝ}
    {ε : ℝ} (S : TwoStageSamplerOracle β ε) {D : ℕ} {α_cap : ℝ}
    (hX : X.Nonempty) (hY : Y.Nonempty) (hZ : Z.Nonempty)
    (hA : IsBinaryMatrix X Y A) (hB : IsBinaryMatrix Y Z B)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hD : 2 ≤ D)
    (hα0 : 0 ≤ α_cap)
    (hB_gt : (2 : ℝ) ^ (-(D : ℤ)) < matDensity Y Z B) :
    let res := cappedGoodCube X Y Z A B ε gamma3D D α_cap (matDensity Y Z B) S
    let B_rem := zeroOutSubrect B res.Y_star res.Z_star
    (2 : ℝ) ^ (-(res.S_B * D : ℤ)) ≤
      (2 : ℝ) ^ D * M_cube ε gamma3D D * (matDensity Y Z B - matDensity Y Z B_rem) ∧
    1 ≤ (matDensity Y Z B - matDensity Y Z B_rem) *
      ((2 : ℝ) ^ (D + D ^ 2) * M_cube ε gamma3D D) := by
  rcases thm_3d_decomp_part1 S hX hY hZ hA hB hε0 hε_le hD hα0 hB_gt with
    ⟨_hX_eq, hsubY, hsubZ, _hneY, _hneZ, _hsteps, hSB_D, hdens_scale, hM_bound, _⟩
  set res := cappedGoodCube X Y Z A B ε gamma3D D α_cap (matDensity Y Z B) S
  set B_rem := zeroOutSubrect B res.Y_star res.Z_star
  have hY_pos : (0 : ℝ) < (Y.card : ℝ) := Nat.cast_pos.mpr hY.card_pos
  have hZ_pos : (0 : ℝ) < (Z.card : ℝ) := Nat.cast_pos.mpr hZ.card_pos
  have hYZ_pos : (0 : ℝ) < (Y.card : ℝ) * (Z.card : ℝ) := mul_pos hY_pos hZ_pos
  have hYZ_ne : (Y.card : ℝ) * (Z.card : ℝ) ≠ 0 := hYZ_pos.ne'
  have hε1 : ε < 1 := by linarith
  have hM_pos : 0 < M_cube ε gamma3D D := by
    have := three_le_M_cube hε0 hε1.le gamma3D_pos D
    linarith
  have h1_le_2s : (1 : ℝ) ≤ (2 : ℝ) ^ res.S_B := one_le_pow₀ (by norm_num)
  have hstar_gt : (2 : ℝ) ^ (-(D : ℤ)) < matDensity res.Y_star res.Z_star B := by
    have hpos : 0 < matDensity Y Z B := lt_trans (by positivity) hB_gt
    have : 1 * matDensity Y Z B ≤ (2 : ℝ) ^ res.S_B * matDensity Y Z B :=
      mul_le_mul_of_nonneg_right h1_le_2s hpos.le
    linarith
  have hzero := matDensity_zeroOutSubrect_eq B hY hZ hsubY hsubZ
  have hdrop_ge :
      (2 : ℝ) ^ (-(D : ℤ)) * (M_cube ε gamma3D D)⁻¹ * (2 : ℝ) ^ (-(res.S_B * D : ℤ)) ≤
        matDensity Y Z B - matDensity Y Z B_rem := by
    have h1 :
        ((M_cube ε gamma3D D)⁻¹ * (2 : ℝ) ^ (-(res.S_B * D : ℤ)) * ((Y.card : ℝ) * (Z.card : ℝ))) *
          (2 : ℝ) ^ (-(D : ℤ)) ≤
        ((res.Y_star.card : ℝ) * (res.Z_star.card : ℝ)) * matDensity res.Y_star res.Z_star B :=
      mul_le_mul hM_bound hstar_gt.le (by positivity) (by positivity)
    have h2 := div_le_div_of_nonneg_right h1 hYZ_pos.le
    have hlhs :
        (((M_cube ε gamma3D D)⁻¹ * (2 : ℝ) ^ (-(res.S_B * D : ℤ)) * ((Y.card : ℝ) * (Z.card : ℝ))) *
          (2 : ℝ) ^ (-(D : ℤ))) / ((Y.card : ℝ) * (Z.card : ℝ)) =
        (2 : ℝ) ^ (-(D : ℤ)) * (M_cube ε gamma3D D)⁻¹ * (2 : ℝ) ^ (-(res.S_B * D : ℤ)) := by
      field_simp [hYZ_ne]
    have hrhs :
        (((res.Y_star.card : ℝ) * (res.Z_star.card : ℝ)) * matDensity res.Y_star res.Z_star B) /
          ((Y.card : ℝ) * (Z.card : ℝ)) =
        matDensity Y Z B - matDensity Y Z B_rem := by
      change _ = matDensity Y Z B - matDensity Y Z (zeroOutSubrect B res.Y_star res.Z_star)
      rw [hzero]
      field_simp [hYZ_ne]
      ring
    rwa [hlhs, hrhs] at h2
  have hscale_step :
      (2 : ℝ) ^ (-(res.S_B * D : ℤ)) ≤
        (2 : ℝ) ^ D * M_cube ε gamma3D D * (matDensity Y Z B - matDensity Y Z B_rem) := by
    have hmul := mul_le_mul_of_nonneg_left hdrop_ge
      (by positivity : 0 ≤ (2 : ℝ) ^ D * M_cube ε gamma3D D)
    have hid :
        (2 : ℝ) ^ D * M_cube ε gamma3D D *
          ((2 : ℝ) ^ (-(D : ℤ)) * (M_cube ε gamma3D D)⁻¹ * (2 : ℝ) ^ (-(res.S_B * D : ℤ))) =
        (2 : ℝ) ^ (-(res.S_B * D : ℤ)) := by
      have h2D : (2 : ℝ) ^ D * (2 : ℝ) ^ (-(D : ℤ)) = 1 := by
        rw [← zpow_natCast 2 D, ← zpow_add₀ (by norm_num), add_neg_cancel, zpow_zero]
      have hM : M_cube ε gamma3D D * (M_cube ε gamma3D D)⁻¹ = 1 := mul_inv_cancel₀ hM_pos.ne'
      calc
        (2 : ℝ) ^ D * M_cube ε gamma3D D *
            ((2 : ℝ) ^ (-(D : ℤ)) * (M_cube ε gamma3D D)⁻¹ * (2 : ℝ) ^ (-(res.S_B * D : ℤ)))
          = ((2 : ℝ) ^ D * (2 : ℝ) ^ (-(D : ℤ))) * (M_cube ε gamma3D D * (M_cube ε gamma3D D)⁻¹) *
              (2 : ℝ) ^ (-(res.S_B * D : ℤ)) := by ring
        _ = (2 : ℝ) ^ (-(res.S_B * D : ℤ)) := by rw [h2D, hM]; ring
    rwa [hid] at hmul
  refine ⟨hscale_step, ?_⟩
  have hSD_le : res.S_B * D ≤ D ^ 2 := by
    rw [sq]
    exact Nat.mul_le_mul_right D hSB_D
  have hzpow_ge : (1 : ℝ) ≤ (2 : ℝ) ^ (D ^ 2) * (2 : ℝ) ^ (-(res.S_B * D : ℤ)) := by
    have h1 : (2 : ℝ) ^ (res.S_B * D) ≤ (2 : ℝ) ^ (D ^ 2) :=
      pow_le_pow_right₀ (by norm_num) hSD_le
    have h2 : (2 : ℝ) ^ (res.S_B * D) * (2 : ℝ) ^ (-(res.S_B * D : ℤ)) = 1 := by
      have hcast : (-(res.S_B * D : ℤ)) = -((res.S_B * D : ℕ) : ℤ) := by push_cast; ring
      rw [hcast, ← zpow_natCast 2 (res.S_B * D), ← zpow_add₀ (by norm_num),
        add_neg_cancel, zpow_zero]
    have h3 := mul_le_mul_of_nonneg_right h1
      (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (-(res.S_B * D : ℤ)))
    linarith
  have hmul := mul_le_mul_of_nonneg_left hscale_step (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (D ^ 2))
  have hrhs :
      (2 : ℝ) ^ (D ^ 2) *
        ((2 : ℝ) ^ D * M_cube ε gamma3D D * (matDensity Y Z B - matDensity Y Z B_rem)) =
      (matDensity Y Z B - matDensity Y Z B_rem) *
        ((2 : ℝ) ^ (D + D ^ 2) * M_cube ε gamma3D D) := by
    rw [pow_add]
    ring
  linarith

lemma rSStarFuel_ge_of_isBinaryMatrix {Y : Finset β} {Z : Finset γ} {B : β → γ → ℝ}
    {ε : ℝ} {D : ℕ}
    (hB : IsBinaryMatrix Y Z B) (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) :
    matDensity Y Z B * ((2 : ℝ) ^ (D + D ^ 2) * M_cube ε gamma3D D) ≤ (rSStarFuel ε D : ℝ) := by
  have hB1 : matDensity Y Z B ≤ 1 := matDensity_le_one_of_isBinaryMatrix hB
  have hε1 : ε < 1 := by linarith
  have hM_pos : 0 < M_cube ε gamma3D D := by
    have := three_le_M_cube hε0 hε1.le gamma3D_pos D
    linarith
  have h1 :
      matDensity Y Z B * ((2 : ℝ) ^ (D + D ^ 2) * M_cube ε gamma3D D) ≤
        1 * ((2 : ℝ) ^ (D + D ^ 2) * M_cube ε gamma3D D) :=
    mul_le_mul_of_nonneg_right hB1 (by positivity)
  rw [one_mul] at h1
  exact h1.trans (Nat.le_ceil _)

lemma stdMatMul_submatZeroExt_eq [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ) (x : α) (z : γ) :
    stdMatMul Y (submatZeroExt X Y A) (submatZeroExt Y Z B) x z =
      if x ∈ X ∧ z ∈ Z then stdMatMul Y A B x z else 0 := by
  unfold stdMatMul submatZeroExt
  by_cases hx : x ∈ X <;> by_cases hz : z ∈ Z
  · simp only [hx, hz, and_self, ↓reduceIte]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    simp [hy]
  · simp [hx, hz]
  · simp [hx, hz]
  · simp [hx, hz]

lemma stdMatMul_submatZeroExt_split_B [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) {Y Y_star : Finset β} {Z Z_star : Finset γ}
    (A : α → β → ℝ) (B : β → γ → ℝ)
    (hY_sub : Y_star ⊆ Y) (hZ_sub : Z_star ⊆ Z) (x : α) (z : γ) :
    stdMatMul Y (submatZeroExt X Y A)
        (submatZeroExt Y Z (zeroOutSubrect B Y_star Z_star)) x z +
      stdMatMul Y_star (submatZeroExt X Y_star A)
        (submatZeroExt Y_star Z_star B) x z =
      stdMatMul Y (submatZeroExt X Y A) (submatZeroExt Y Z B) x z := by
  have hstar_ext :
      stdMatMul Y_star (submatZeroExt X Y_star A) (submatZeroExt Y_star Z_star B) x z =
        ∑ y ∈ Y, submatZeroExt X Y A x y * submatZeroExt Y_star Z_star B y z := by
    unfold stdMatMul
    refine (Finset.sum_congr rfl (fun y hy => ?_)).trans
      (Finset.sum_subset hY_sub (fun y _ hy_not => ?_))
    · have hyY : y ∈ Y := hY_sub hy
      simp [submatZeroExt, hy, hyY]
    · simp [submatZeroExt, hy_not]
  rw [hstar_ext]
  unfold stdMatMul
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun y hy => ?_)
  rw [← mul_add]
  congr 1
  unfold submatZeroExt zeroOutSubrect
  by_cases hy_s : y ∈ Y_star <;> by_cases hz_s : z ∈ Z_star
  · have hz : z ∈ Z := hZ_sub hz_s
    simp [hy, hz, hy_s, hz_s]
  · by_cases hz : z ∈ Z <;> simp [hy, hz, hy_s, hz_s]
  · by_cases hz : z ∈ Z <;> simp [hy, hz, hy_s, hz_s]
  · by_cases hz : z ∈ Z <;> simp [hy, hz, hy_s, hz_s]

lemma stdMatMul_slice_split_Z [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {X_ell : Finset α} {Y_ell Y_star : Finset β} {Z_ell Z_star : Finset γ}
    {A_ell : α → β → ℝ} (B : β → γ → ℝ)
    (hY_sub : Y_ell ⊆ Y_star) (hZ_sub : Z_ell ⊆ Z_star)
    (hA_ext : ∀ x y, A_ell x y = submatZeroExt X_ell Y_ell A_ell x y)
    (x : α) (z : γ) :
    stdMatMul Y_ell A_ell (submatZeroExt Y_ell Z_ell B) x z +
      stdMatMul Y_ell A_ell (submatZeroExt Y_ell (Z_star \ Z_ell) B) x z =
      stdMatMul Y_star A_ell (submatZeroExt Y_star Z_star B) x z := by
  have hlhs :
      stdMatMul Y_ell A_ell (submatZeroExt Y_ell Z_ell B) x z +
        stdMatMul Y_ell A_ell (submatZeroExt Y_ell (Z_star \ Z_ell) B) x z =
        stdMatMul Y_ell A_ell (submatZeroExt Y_ell Z_star B) x z := by
    unfold stdMatMul
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    rw [← mul_add]
    congr 1
    unfold submatZeroExt
    by_cases hz_ell : z ∈ Z_ell
    · have hz_star : z ∈ Z_star := hZ_sub hz_ell
      simp [hy, hz_ell, hz_star]
    · by_cases hz_star : z ∈ Z_star <;> simp [hy, hz_ell, hz_star]
  rw [hlhs]
  unfold stdMatMul
  refine (Finset.sum_congr rfl (fun y hy => ?_)).trans
    (Finset.sum_subset hY_sub (fun y _ hy_not => ?_))
  · have hy_star : y ∈ Y_star := hY_sub hy
    by_cases hz : z ∈ Z_star <;> simp [submatZeroExt, hy, hy_star, hz]
  · have hA0 : A_ell x y = 0 := by
      rw [hA_ext x y]
      simp [submatZeroExt, hy_not]
    simp [hA0]

lemma bucketedRec_sum_eq_all [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X' : Finset α) (Y' : Finset β) (Z' : Finset γ)
    (A' : α → β → ℝ) (B' : β → γ → ℝ) {μ : ℝ} {D : ℕ}
    (hD : 1 ≤ D) (hμ : 0 < μ) (hμD : 1 ≤ (2 : ℝ) ^ D * μ)
    (hcol_le_one : ∀ y ∈ Y', colDeg X' A' y ≤ 1)
    (recCall : Finset α → Finset β → Finset γ →
      (α → β → ℝ) → (β → γ → ℝ) → ℝ → ℕ → List (CubePiece α β γ))
    (x : α) (z : γ)
    (hrec_sum : ∀ j < D, (dyadicColBucket X' Y' A' μ j).Nonempty →
      let Y'_j := dyadicColBucket X' Y' A' μ j
      ((recCall X' Y'_j Z'
          (submatZeroExt X' Y'_j A') (submatZeroExt Y'_j Z' B') (dyadicColAlpha μ j) j).map
        (fun P => stdMatMul P.Y_k P.A_k P.B_k x z)).sum =
        stdMatMul Y'_j (submatZeroExt X' Y'_j A') (submatZeroExt Y'_j Z' B') x z) :
    ((bucketedRec X' Y' Z' A' B' μ D recCall).map
      (fun P => stdMatMul P.Y_k P.A_k P.B_k x z)).sum =
      stdMatMul Y' (submatZeroExt X' Y' A') (submatZeroExt Y' Z' B') x z := by
  by_cases hxz : x ∈ X' ∧ z ∈ Z'
  · rw [stdMatMul_submatZeroExt_eq, if_pos hxz]
    exact bucketedRec_sum_eq X' Y' Z' A' B' hD hμ hμD hcol_le_one recCall hxz.1 hxz.2 hrec_sum
  · rw [stdMatMul_submatZeroExt_eq, if_neg hxz]
    unfold bucketedRec
    rw [list_flatMap_map_sum]
    suffices h0 :
        ∀ j ∈ (List.range D).filter (fun j => decide (dyadicColBucket X' Y' A' μ j).Nonempty),
          let Y'_j := dyadicColBucket X' Y' A' μ j
          ((recCall X' Y'_j Z'
              (submatZeroExt X' Y'_j A') (submatZeroExt Y'_j Z' B') (dyadicColAlpha μ j) j).map
            (fun P => stdMatMul P.Y_k P.A_k P.B_k x z)).sum = 0 by
      have hmap0 :
          (((List.range D).filter (fun j => decide (dyadicColBucket X' Y' A' μ j).Nonempty)).map
            (fun j =>
              let Y'_j := dyadicColBucket X' Y' A' μ j
              ((recCall X' Y'_j Z'
                  (submatZeroExt X' Y'_j A') (submatZeroExt Y'_j Z' B') (dyadicColAlpha μ j) j).map
                (fun P => stdMatMul P.Y_k P.A_k P.B_k x z)).sum)) =
          ((List.range D).filter (fun j => decide (dyadicColBucket X' Y' A' μ j).Nonempty)).map
            (fun _ => (0 : ℝ)) :=
        List.map_congr_left h0
      rw [hmap0]
      simp
    intro j hj
    have hj_mem : j < D ∧ (dyadicColBucket X' Y' A' μ j).Nonempty := by
      simpa using hj
    dsimp only
    rw [hrec_sum j hj_mem.1 hj_mem.2, stdMatMul_submatZeroExt_eq, if_neg hxz]

@[simp]
lemma submatZeroExt_idem [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (A : α → β → ℝ) :
    submatZeroExt X Y (submatZeroExt X Y A) = submatZeroExt X Y A := by
  ext x y
  by_cases h : x ∈ X ∧ y ∈ Y <;> simp [submatZeroExt, h]

/-- **Exact Bilinear Sum Conservation for `sStarLoop` (`sStarLoop_sum_eq`,
`paper.tex` Lemma 5.4 `\label{lem:children-invariants}` & Theorem 1.1 Clause 1, §5.3)**:
Whenever the fuel bound `matDensity Y Z B * (2^(D + D^2) * M_cube ε gamma3D D) ≤ sStarFuel`
holds and every recursive call `recDepth` preserves the bilinear sum, `sStarLoop` preserves
`stdMatMul Y (submatZeroExt X Y A) (submatZeroExt Y Z B) x z` for all $x, z$. -/
theorem sStarLoop_sum_eq [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (sStarFuel : ℕ) (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    {ε : ℝ} (S : TwoStageSamplerOracle β ε) {D : ℕ} (α_cap : ℝ) (capNum capDen : ℕ) (remDepth : ℕ)
    (hA : IsBinaryMatrix X Y A) (hB : IsBinaryMatrix Y Z B)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hD : 2 ≤ D) (hα0 : 0 ≤ α_cap)
    (hfuel : matDensity Y Z B * ((2 : ℝ) ^ (D + D ^ 2) * M_cube ε gamma3D D) ≤ (sStarFuel : ℝ))
    (recDepth : ℕ → Finset α → Finset β → Finset γ →
      (α → β → ℝ) → (β → γ → ℝ) → ℝ → ℕ → ℕ → List (CubePiece α β γ))
    (hrec_sum : ∀ Δ X' Y' Z' A' B' α' capNum' capDen',
      IsBinaryMatrix X' Y' A' → IsBinaryMatrix Y' Z' B' → 0 ≤ α' →
      ∀ x z,
        ((recDepth Δ X' Y' Z' A' B' α' capNum' capDen').map
          (fun P => stdMatMul P.Y_k P.A_k P.B_k x z)).sum =
          stdMatMul Y' (submatZeroExt X' Y' A') (submatZeroExt Y' Z' B') x z)
    (x : α) (z : γ) :
    ((sStarLoop sStarFuel X Y Z A B ε S D α_cap capNum capDen remDepth recDepth).map
      (fun P => stdMatMul P.Y_k P.A_k P.B_k x z)).sum =
      stdMatMul Y (submatZeroExt X Y A) (submatZeroExt Y Z B) x z := by
  induction sStarFuel generalizing B with
  | zero =>
    unfold sStarLoop
    simp [baseCase1Piece]
  | succ fuel ih =>
    unfold sStarLoop
    dsimp only
    by_cases hbase : isSparse3DPiece X Y Z A B D = true
    · rw [if_pos hbase]
      simp [baseCase1Piece]
    · rw [if_neg hbase]
      have hnot_sp : isSparse3DPiece X Y Z A B D = false := Bool.eq_false_iff.mpr hbase
      rcases of_isSparse3DPiece_eq_false hnot_sp with ⟨hX, hY, hZ, _hA_gt, hB_gt⟩
      rcases thm_3d_decomp_part1 S hX hY hZ hA hB hε0 hε_le hD hα0 hB_gt with
        ⟨_hX_eq, hsubY, hsubZ, _hneY, _hneZ, _hsteps, _hSB_D, _hdens_scale, _hM_bound,
          hmode_or, _hbboost_spec, hnorm_spec⟩
      set cubeRes := cappedGoodCube X Y Z A B ε gamma3D D α_cap (matDensity Y Z B) S
      set B_rem := zeroOutSubrect B cubeRes.Y_star cubeRes.Z_star
      have hB_rem_bin : IsBinaryMatrix Y Z B_rem := isBinaryMatrix_zeroOutSubrect _ _ hB
      have hstep_fuel := (goodCube_fuel_step S hX hY hZ hA hB hε0 hε_le hD hα0 hB_gt).2
      have hfuel_rem :
          matDensity Y Z B_rem * ((2 : ℝ) ^ (D + D ^ 2) * M_cube ε gamma3D D) ≤ (fuel : ℝ) := by
        push_cast at hfuel
        linarith
      have hih := ih B_rem hB_rem_bin hfuel_rem
      have hsplit_B := stdMatMul_submatZeroExt_split_B X A B hsubY hsubZ x z
      by_cases hmode : cubeRes.mode = CubeMode.bBoost
      · -- Branch A (`bBoost`)
        rw [if_pos hmode, List.map_append, List.sum_append, hih]
        have hA_star : IsBinaryMatrix X cubeRes.Y_star (submatZeroExt X cubeRes.Y_star A) :=
          isBinaryMatrix_submatZeroExt Finset.Subset.rfl hsubY hA
        have hB_star :
            IsBinaryMatrix cubeRes.Y_star cubeRes.Z_star
              (submatZeroExt cubeRes.Y_star cubeRes.Z_star B) :=
          isBinaryMatrix_submatZeroExt hsubY hsubZ hB
        rw [hrec_sum _ _ _ _ _ _ _ _ _ hA_star hB_star hα0 x z]
        have hsubA_idem :
            submatZeroExt X cubeRes.Y_star (submatZeroExt X cubeRes.Y_star A) =
              submatZeroExt X cubeRes.Y_star A := by
          ext x' y'; by_cases h : x' ∈ X ∧ y' ∈ cubeRes.Y_star <;> simp [submatZeroExt, h]
        have hsubB_idem :
            submatZeroExt cubeRes.Y_star cubeRes.Z_star
              (submatZeroExt cubeRes.Y_star cubeRes.Z_star B) =
              submatZeroExt cubeRes.Y_star cubeRes.Z_star B := by
          ext y' z'; by_cases h : y' ∈ cubeRes.Y_star ∧ z' ∈ cubeRes.Z_star <;> simp [submatZeroExt, h]
        rw [hsubA_idem, hsubB_idem]
        exact hsplit_B
      · -- Branch B (`normal`)
        rw [if_neg hmode]
        have hmode_norm : cubeRes.mode = CubeMode.normal := by
          rcases hmode_or with h1 | h2
          · exact False.elim (hmode h1)
          · exact h2
        rcases hnorm_spec hmode_norm with ⟨_hSB4, _hlt17, hsum_A, hslices⟩
        rcases cappedGoodCube_normal_extra_spec S hX hY hZ hA hB hε0 hε_le hD hα0 hB_gt hmode_norm with
          ⟨_hmom, _hrpow, _hres1, _hscale, _hlen, hsl_extra⟩
        rw [List.map_append, List.map_append, List.sum_append, List.sum_append, hih]
        -- Direct pieces sum
        have hdirect_sum :
            ((((cubeRes.slices.filter (fun sl => decide sl.Z_ell.Nonempty)).map
              (directSlicePiece B D)).map (fun P => stdMatMul P.Y_k P.A_k P.B_k x z)).sum) =
            (cubeRes.slices.map (fun sl =>
              stdMatMul sl.Y_ell sl.A_ell (submatZeroExt sl.Y_ell sl.Z_ell B) x z)).sum := by
          rw [List.map_map]
          refine list_filter_map_sum_eq_of_false_zero cubeRes.slices _ _ (fun sl _ hnot => ?_)
          have hemp : sl.Z_ell = ∅ :=
            Finset.not_nonempty_iff_eq_empty.mp (of_decide_eq_false hnot)
          dsimp only [Function.comp_apply, directSlicePiece]
          rw [hemp]
          unfold stdMatMul submatZeroExt
          simp
        -- Recursive pieces sum
        have hrec_slices_sum :
            ((((cubeRes.slices.filter (fun sl => decide (cubeRes.Z_star \ sl.Z_ell).Nonempty)).flatMap
              (fun sl =>
                let Z_rem := cubeRes.Z_star \ sl.Z_ell
                let α_ell := matDensity sl.X_ell sl.Y_ell sl.A_ell
                let p_ell := supportCountRealNat sl.X_ell sl.Y_ell sl.A_ell
                let q_ell := sl.X_ell.card * sl.Y_ell.card
                let Δ := min remDepth (rawDeltaHANat p_ell q_ell capNum capDen)
                bucketedRec sl.X_ell sl.Y_ell Z_rem sl.A_ell
                  (submatZeroExt sl.Y_ell Z_rem B) α_ell D
                  (fun X' Y'_j Z' A' B' α' j =>
                    recDepth Δ X' Y'_j Z' A' B' α' (2 ^ j * p_ell) q_ell))).map
              (fun P => stdMatMul P.Y_k P.A_k P.B_k x z)).sum) =
            (cubeRes.slices.map (fun sl =>
              stdMatMul sl.Y_ell sl.A_ell
                (submatZeroExt sl.Y_ell (cubeRes.Z_star \ sl.Z_ell) B) x z)).sum := by
          rw [list_flatMap_map_sum]
          set active := cubeRes.slices.filter (fun sl => decide (cubeRes.Z_star \ sl.Z_ell).Nonempty)
          have hactive_congr :
              active.map (fun sl =>
                let Z_rem := cubeRes.Z_star \ sl.Z_ell
                let α_ell := matDensity sl.X_ell sl.Y_ell sl.A_ell
                let p_ell := supportCountRealNat sl.X_ell sl.Y_ell sl.A_ell
                let q_ell := sl.X_ell.card * sl.Y_ell.card
                let Δ := min remDepth (rawDeltaHANat p_ell q_ell capNum capDen)
                ((bucketedRec sl.X_ell sl.Y_ell Z_rem sl.A_ell
                    (submatZeroExt sl.Y_ell Z_rem B) α_ell D
                    (fun X' Y'_j Z' A' B' α' j =>
                      recDepth Δ X' Y'_j Z' A' B' α' (2 ^ j * p_ell) q_ell)).map
                  (fun P => stdMatMul P.Y_k P.A_k P.B_k x z)).sum) =
              active.map (fun sl =>
                stdMatMul sl.Y_ell sl.A_ell
                  (submatZeroExt sl.Y_ell (cubeRes.Z_star \ sl.Z_ell) B) x z) := by
            refine List.map_congr_left (fun sl hsl => ?_)
            have hsl_mem : sl ∈ cubeRes.slices := (List.mem_filter.mp hsl).1
            have hZrem_ne : (cubeRes.Z_star \ sl.Z_ell).Nonempty :=
              of_decide_eq_true (List.mem_filter.mp hsl).2
            rcases hslices sl hsl_mem with
              ⟨hslZ, hslX, hslY, _hneX, _hneY, hsl_bin, hsl_ext, _hsl_res, _hsl_ab, _hsl_reg⟩
            rcases hsl_extra sl hsl_mem with ⟨_hsl_S, hsl_nonres, hsl_res_extra⟩
            have hα_gt : (2 : ℝ) ^ (-(D : ℤ)) < matDensity sl.X_ell sl.Y_ell sl.A_ell := by
              by_cases htag : sl.tag = RectTag.residual
              · rcases hsl_res_extra htag with ⟨_, _, _, hZ_if⟩
                by_contra hle
                push_neg at hle
                rw [if_pos hle] at hZ_if
                rw [hZ_if, Finset.sdiff_self] at hZrem_ne
                exact Finset.not_nonempty_empty hZrem_ne
              · exact hsl_nonres htag
            have hα_pos : 0 < matDensity sl.X_ell sl.Y_ell sl.A_ell :=
              lt_trans (by positivity) hα_gt
            have hαD : 1 ≤ (2 : ℝ) ^ D * matDensity sl.X_ell sl.Y_ell sl.A_ell := by
              have h1 : (2 : ℝ) ^ D * (2 : ℝ) ^ (-(D : ℤ)) = 1 := by
                rw [← zpow_natCast 2 D, ← zpow_add₀ (by norm_num), add_neg_cancel, zpow_zero]
              have h2 := mul_le_mul_of_nonneg_left hα_gt.le (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ D)
              linarith
            have hcol1 : ∀ y ∈ sl.Y_ell, colDeg sl.X_ell sl.A_ell y ≤ 1 := by
              intro y hy
              rcases sl.X_ell.eq_empty_or_nonempty with hemp | hne
              · rw [hemp]; simp [colDeg, expectSet]
              · exact expectSet_le_of_le hne (fun x' hx' => isBinaryMatrix_le_one hsl_bin x' hx' y hy)
            dsimp only
            rw [bucketedRec_sum_eq_all sl.X_ell sl.Y_ell (cubeRes.Z_star \ sl.Z_ell)
              sl.A_ell (submatZeroExt sl.Y_ell (cubeRes.Z_star \ sl.Z_ell) B)
              (by omega) hα_pos hαD hcol1 _ x z
              (fun j _ _ => by
                dsimp only
                set Y'_j := dyadicColBucket sl.X_ell sl.Y_ell sl.A_ell
                  (matDensity sl.X_ell sl.Y_ell sl.A_ell) j
                have hY'j_sub : Y'_j ⊆ sl.Y_ell := dyadicColBucket_subset _ _ _ _ _
                have hAj_bin :
                    IsBinaryMatrix sl.X_ell Y'_j (submatZeroExt sl.X_ell Y'_j sl.A_ell) :=
                  isBinaryMatrix_submatZeroExt Finset.Subset.rfl hY'j_sub hsl_bin
                have hBj_bin :
                    IsBinaryMatrix Y'_j (cubeRes.Z_star \ sl.Z_ell)
                      (submatZeroExt Y'_j (cubeRes.Z_star \ sl.Z_ell)
                        (submatZeroExt sl.Y_ell (cubeRes.Z_star \ sl.Z_ell) B)) :=
                  isBinaryMatrix_submatZeroExt hY'j_sub Finset.Subset.rfl
                    (isBinaryMatrix_submatZeroExt (hslY.trans hsubY)
                      (Finset.sdiff_subset.trans hsubZ) hB)
                have hαj_0 : 0 ≤ dyadicColAlpha (matDensity sl.X_ell sl.Y_ell sl.A_ell) j := by
                  unfold dyadicColAlpha; positivity
                have hrec_j := hrec_sum
                  (min remDepth
                    (rawDeltaHANat (supportCountRealNat sl.X_ell sl.Y_ell sl.A_ell)
                      (sl.X_ell.card * sl.Y_ell.card) capNum capDen))
                  _ _ _ _ _ _
                  (2 ^ j * supportCountRealNat sl.X_ell sl.Y_ell sl.A_ell)
                  (sl.X_ell.card * sl.Y_ell.card)
                  hAj_bin hBj_bin hαj_0 x z
                rwa [submatZeroExt_idem, submatZeroExt_idem] at hrec_j)]
            have hA_eq : submatZeroExt sl.X_ell sl.Y_ell sl.A_ell = sl.A_ell := by
              ext x' y'; exact (hsl_ext x' y').symm
            have hB_eq := submatZeroExt_idem sl.Y_ell (cubeRes.Z_star \ sl.Z_ell) B
            rw [hA_eq, hB_eq]
          rw [hactive_congr]
          refine list_filter_map_sum_eq_of_false_zero cubeRes.slices _ _ (fun sl _ hnot => ?_)
          have hemp : cubeRes.Z_star \ sl.Z_ell = ∅ :=
            Finset.not_nonempty_iff_eq_empty.mp (of_decide_eq_false hnot)
          rw [hemp]
          unfold stdMatMul submatZeroExt
          simp
        rw [hdirect_sum, hrec_slices_sum]
        have hcomb_slices :
            (cubeRes.slices.map (fun sl =>
              stdMatMul sl.Y_ell sl.A_ell (submatZeroExt sl.Y_ell sl.Z_ell B) x z)).sum +
            (cubeRes.slices.map (fun sl =>
              stdMatMul sl.Y_ell sl.A_ell
                (submatZeroExt sl.Y_ell (cubeRes.Z_star \ sl.Z_ell) B) x z)).sum =
            stdMatMul cubeRes.Y_star (submatZeroExt X cubeRes.Y_star A)
              (submatZeroExt cubeRes.Y_star cubeRes.Z_star B) x z := by
          have hadd_map :
               (cubeRes.slices.map (fun sl =>
                stdMatMul sl.Y_ell sl.A_ell (submatZeroExt sl.Y_ell sl.Z_ell B) x z)).sum +
              (cubeRes.slices.map (fun sl =>
                stdMatMul sl.Y_ell sl.A_ell
                  (submatZeroExt sl.Y_ell (cubeRes.Z_star \ sl.Z_ell) B) x z)).sum =
              (cubeRes.slices.map (fun sl =>
                stdMatMul sl.Y_ell sl.A_ell (submatZeroExt sl.Y_ell sl.Z_ell B) x z +
                  stdMatMul sl.Y_ell sl.A_ell
                    (submatZeroExt sl.Y_ell (cubeRes.Z_star \ sl.Z_ell) B) x z)).sum := by
            generalize cubeRes.slices = L
            induction L with
            | nil => simp
            | cons a l ih => simp only [List.map_cons, List.sum_cons, ← ih]; ring
          rw [hadd_map]
          have hcongr :
              cubeRes.slices.map (fun sl =>
                stdMatMul sl.Y_ell sl.A_ell (submatZeroExt sl.Y_ell sl.Z_ell B) x z +
                  stdMatMul sl.Y_ell sl.A_ell
                    (submatZeroExt sl.Y_ell (cubeRes.Z_star \ sl.Z_ell) B) x z) =
              cubeRes.slices.map (fun sl =>
                stdMatMul cubeRes.Y_star sl.A_ell
                  (submatZeroExt cubeRes.Y_star cubeRes.Z_star B) x z) := by
            refine List.map_congr_left (fun sl hsl => ?_)
            rcases hslices sl hsl with ⟨hslZ, _hslX, hslY, _hneX, _hneY, _hsl_bin, hsl_ext, _⟩
            exact stdMatMul_slice_split_Z B hslY hslZ hsl_ext x z
          rw [hcongr]
          unfold stdMatMul
          have hcomm :
              ∀ (L : List (GoodCubeSlice α β γ)),
                (L.map (fun sl =>
                  ∑ y ∈ cubeRes.Y_star,
                    sl.A_ell x y * submatZeroExt cubeRes.Y_star cubeRes.Z_star B y z)).sum =
                ∑ y ∈ cubeRes.Y_star,
                  (L.map (fun sl => sl.A_ell x y)).sum *
                    submatZeroExt cubeRes.Y_star cubeRes.Z_star B y z := by
            intro L
            induction L with
            | nil => simp
            | cons a l ih_l =>
              simp only [List.map_cons, List.sum_cons, ih_l, ← Finset.sum_add_distrib, add_mul]
          rw [hcomm cubeRes.slices]
          refine Finset.sum_congr rfl (fun y _ => ?_)
          rw [hsum_A x y]
        linarith [hcomb_slices, hsplit_B]

/-- **Exact Bilinear Sum Conservation for `cappedABDecompAux` (`cappedABDecompAux_sum_eq`,
`paper.tex` Lemma 5.4 `\label{lem:children-invariants}` & Theorem 1.1 Clause 1, §5.3 & §5.6)**. -/
theorem cappedABDecompAux_sum_eq [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (remDepth : ℕ) (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    {ε : ℝ} (S : TwoStageSamplerOracle β ε) {D : ℕ} (α_cap : ℝ) (capNum capDen : ℕ)
    (hA : IsBinaryMatrix X Y A) (hB : IsBinaryMatrix Y Z B)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hD : 2 ≤ D) (hα0 : 0 ≤ α_cap)
    (x : α) (z : γ) :
    ((cappedABDecompAux remDepth X Y Z A B ε S D α_cap capNum capDen).map
      (fun P => stdMatMul P.Y_k P.A_k P.B_k x z)).sum =
      stdMatMul Y (submatZeroExt X Y A) (submatZeroExt Y Z B) x z := by
  induction' remDepth using Nat.strong_induction_on with remDepth ih
    generalizing X Y Z A B α_cap capNum capDen x z
  rcases remDepth with _ | rem
  · rw [cappedABDecompAux]
    split_ifs with hbase
    · simp [baseCase1Piece]
    · by_cases hxz : x ∈ X ∧ z ∈ Z
      · rw [stdMatMul_submatZeroExt_eq, if_pos hxz]
        exact baseCase2Decomposition_sum_eq X Y Z A B D hB hxz.1 hxz.2
      · rw [stdMatMul_submatZeroExt_eq, if_neg hxz]
        suffices h0 :
            ∀ P ∈ baseCase2Decomposition X Y Z A B D,
              stdMatMul P.Y_k P.A_k P.B_k x z = 0 by
          have hmap0 :
              (baseCase2Decomposition X Y Z A B D).map
                (fun P => stdMatMul P.Y_k P.A_k P.B_k x z) =
              (baseCase2Decomposition X Y Z A B D).map (fun _ => (0 : ℝ)) :=
            List.map_congr_left h0
          rw [hmap0]
          simp
        intro P hP
        rcases baseCase2Decomposition_pieces_spec X Y Z A B D hB hP with
          ⟨hPX, _hPY, hPZ, _hPA, hPA_ext, hPB_ext, _⟩
        unfold stdMatMul
        refine Finset.sum_eq_zero (fun y _ => ?_)
        rw [hPA_ext x y, hPB_ext y z]
        unfold submatZeroExt
        by_cases hx : x ∈ P.X_k <;> by_cases hz : z ∈ P.Z_k
        · exact False.elim (hxz ⟨hPX hx, hPZ hz⟩)
        · simp [hx, hz]
        · simp [hx, hz]
        · simp [hx, hz]
  · rw [cappedABDecompAux]
    exact sStarLoop_sum_eq (rSStarFuel ε D) X Y Z A B S α_cap capNum capDen (rem + 1)
      hA hB hε0 hε_le hD hα0
      (rSStarFuel_ge_of_isBinaryMatrix hB hε0 hε_le)
      (fun Δ X' Y' Z' A' B' α' capNum' capDen' =>
        cappedABDecompAux (rem - (Δ - 1)) X' Y' Z' A' B' ε S D α' capNum' capDen')
      (fun Δ X' Y' Z' A' B' α' capNum' capDen' hA' hB' hα' x' z' =>
        ih (rem - (Δ - 1)) (by omega) X' Y' Z' A' B' α' capNum' capDen' hA' hB' hα' x' z')
      x z

/-- **Exact Bilinear Matrix Product Decomposition (`cappedABDecomposition'_sum_eq`,
`paper.tex` Lemma 5.4 `\label{lem:children-invariants}` & Theorem 1.1 Clause 1, §5.3 & §5.6)**:
For all $x \in X$ and $z \in Z$,
$$(AB)(x, z) = \sum_{P \in \text{cappedABDecomposition'}} (P.A_k \, P.B_k)(x, z).$$ -/
theorem cappedABDecomposition'_sum_eq [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    {ε : ℝ} (S : TwoStageSamplerOracle β ε) {D : ℕ} (α_cap : ℝ) (capNum capDen : ℕ) (h H : ℕ)
    (hA : IsBinaryMatrix X Y A) (hB : IsBinaryMatrix Y Z B)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hD : 2 ≤ D) (hα0 : 0 ≤ α_cap)
    {x : α} {z : γ} (hx : x ∈ X) (hz : z ∈ Z) :
    ((cappedABDecomposition' X Y Z A B ε S D α_cap capNum capDen h H).map
      (fun P => stdMatMul P.Y_k P.A_k P.B_k x z)).sum = stdMatMul Y A B x z := by
  unfold cappedABDecomposition'
  rw [cappedABDecompAux_sum_eq (H - h) X Y Z A B S α_cap capNum capDen hA hB hε0 hε_le hD hα0 x z,
    stdMatMul_submatZeroExt_eq, if_pos ⟨hx, hz⟩]

/-- **Root Exact Bilinear Matrix Product Decomposition (`cappedABDecomposition_sum_eq`,
`paper.tex` Theorem 1.1 Clause 1 `\label{thm:main-decomp}`, §1.2 & §5.6)**. -/
theorem cappedABDecomposition_sum_eq [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    {ε : ℝ} (S : TwoStageSamplerOracle β ε) {D : ℕ}
    (hA : IsBinaryMatrix X Y A) (hB : IsBinaryMatrix Y Z B)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hD : 2 ≤ D)
    {x : α} {z : γ} (hx : x ∈ X) (hz : z ∈ Z) :
    ((cappedABDecomposition X Y Z A B ε S D).map
      (fun P => stdMatMul P.Y_k P.A_k P.B_k x z)).sum = stdMatMul Y A B x z :=
  cappedABDecomposition'_sum_eq X Y Z A B S 1 1 1 0 (H3D D) hA hB hε0 hε_le hD (by norm_num) hx hz

/-- Structural specification of a single 3D piece `P : CubePiece α β γ` relative to $(X, Y, Z)$
at parameters $(\varepsilon, D)$ (Definition 1.1 `\label{def:pieces}`, Theorem 1.1 Clause 2, & Lemma 5.4 `\label{lem:children-invariants}`, §1.2 & §5.3). -/
def ValidCubePiece [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ) (ε : ℝ) (D : ℕ)
    (P : CubePiece α β γ) : Prop :=
  P.X_k ⊆ X ∧ P.Y_k ⊆ Y ∧ P.Z_k ⊆ Z ∧
  (∀ x y, P.A_k x y = submatZeroExt P.X_k P.Y_k P.A_k x y) ∧
  (∀ y z, P.B_k y z = submatZeroExt P.Y_k P.Z_k P.B_k y z) ∧
  IsBinaryMatrix P.X_k P.Y_k P.A_k ∧
  IsBinaryMatrix P.Y_k P.Z_k P.B_k ∧
  (P.isRegularPiece = true →
    P.X_k.Nonempty ∧ P.Y_k.Nonempty ∧ P.Z_k.Nonempty ∧
    IsGridRegular P.X_k P.Y_k P.A_k ε 2 D ∧
    IsGridRegular P.Z_k P.Y_k (matTranspose P.B_k) ε 2 D ∧
    IsEpsMinDegree P.X_k P.Y_k P.A_k ε ∧
    IsEpsMinDegree P.Z_k P.Y_k (matTranspose P.B_k) ε ∧
    (2 : ℝ) ^ (- (D : ℝ)) < min (matDensity P.X_k P.Y_k P.A_k) (matDensity P.Y_k P.Z_k P.B_k)) ∧
  (P.isRegularPiece = false →
    open Classical in
    (min (matDensity P.X_k P.Y_k P.A_k) (matDensity P.Y_k P.Z_k P.B_k) ≤ (2 : ℝ) ^ (- (D : ℝ)) ∨
    ((P.Y_k ×ˢ P.Z_k).filter (fun p => P.B_k p.1 p.2 = 1)).card ≤ 1))

lemma validCubePiece_mono [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {X X' : Finset α} {Y Y' : Finset β} {Z Z' : Finset γ} {ε : ℝ} {D : ℕ}
    {P : CubePiece α β γ}
    (hX : X' ⊆ X) (hY : Y' ⊆ Y) (hZ : Z' ⊆ Z)
    (hP : ValidCubePiece X' Y' Z' ε D P) :
    ValidCubePiece X Y Z ε D P := by
  rcases hP with ⟨hPX, hPY, hPZ, hrest⟩
  exact ⟨hPX.trans hX, hPY.trans hY, hPZ.trans hZ, hrest⟩

lemma validCubePiece_baseCase1Piece [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {X : Finset α} {Y : Finset β} {Z : Finset γ}
    {A : α → β → ℝ} {B : β → γ → ℝ} {ε : ℝ} {D : ℕ}
    (hA : IsBinaryMatrix X Y A) (hB : IsBinaryMatrix Y Z B)
    (hbase : isSparse3DPiece X Y Z A B D = true ∨
      matDensity Y Z B ≤ (2 : ℝ) ^ (- (D : ℝ))) :
    ValidCubePiece X Y Z ε D (baseCase1Piece X Y Z A B ε D) := by
  classical
  dsimp only [ValidCubePiece, baseCase1Piece]
  refine ⟨Finset.Subset.rfl, Finset.Subset.rfl, Finset.Subset.rfl, ?_, ?_,
    isBinaryMatrix_submatZeroExt Finset.Subset.rfl Finset.Subset.rfl hA,
    isBinaryMatrix_submatZeroExt Finset.Subset.rfl Finset.Subset.rfl hB, ?_, ?_⟩
  · intro x y; by_cases h : x ∈ X ∧ y ∈ Y <;> simp [submatZeroExt, h]
  · intro y z; by_cases h : y ∈ Y ∧ z ∈ Z <;> simp [submatZeroExt, h]
  · intro hreg
    cases hreg
  · intro _
    left
    rw [matDensity_submatZeroExt_eq X Y A, matDensity_submatZeroExt_eq Y Z B]
    rcases hbase with hsp | hB_le
    · unfold isSparse3DPiece at hsp
      exact of_decide_eq_true hsp
    · exact (min_le_right _ _).trans hB_le

/-- **Piece Specification for `sStarLoop` (`sStarLoop_pieces_spec`,
`paper.tex` Lemma 5.4 `\label{lem:children-invariants}` & Theorem 1.1 Clause 2, §5.3)**. -/
theorem sStarLoop_pieces_spec [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (sStarFuel : ℕ) (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    {ε : ℝ} (S : TwoStageSamplerOracle β ε) {D : ℕ} (α_cap : ℝ) (capNum capDen : ℕ) (remDepth : ℕ)
    (hA : IsBinaryMatrix X Y A) (hB : IsBinaryMatrix Y Z B)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hD : 2 ≤ D) (hα0 : 0 ≤ α_cap)
    (hfuel : matDensity Y Z B * ((2 : ℝ) ^ (D + D ^ 2) * M_cube ε gamma3D D) ≤ (sStarFuel : ℝ))
    (recDepth : ℕ → Finset α → Finset β → Finset γ →
      (α → β → ℝ) → (β → γ → ℝ) → ℝ → ℕ → ℕ → List (CubePiece α β γ))
    (hrec_spec : ∀ Δ X' Y' Z' A' B' α' capNum' capDen',
      IsBinaryMatrix X' Y' A' → IsBinaryMatrix Y' Z' B' → 0 ≤ α' →
      ∀ P ∈ recDepth Δ X' Y' Z' A' B' α' capNum' capDen', ValidCubePiece X' Y' Z' ε D P)
    {P : CubePiece α β γ}
    (hP : P ∈ sStarLoop sStarFuel X Y Z A B ε S D α_cap capNum capDen remDepth recDepth) :
    ValidCubePiece X Y Z ε D P := by
  induction sStarFuel generalizing B with
  | zero =>
    unfold sStarLoop at hP
    simp only [List.mem_singleton] at hP
    subst hP
    have hε1 : ε < 1 := by linarith
    have hM_pos : 0 < (2 : ℝ) ^ (D + D ^ 2) * M_cube ε gamma3D D := by
      have := three_le_M_cube hε0 hε1.le gamma3D_pos D
      positivity
    have hB_le_0 : matDensity Y Z B ≤ 0 := by
      simp only [Nat.cast_zero] at hfuel
      nlinarith
    have hB_le : matDensity Y Z B ≤ (2 : ℝ) ^ (- (D : ℝ)) :=
      hB_le_0.trans (by positivity)
    exact validCubePiece_baseCase1Piece hA hB (Or.inr hB_le)
  | succ fuel ih =>
    unfold sStarLoop at hP
    dsimp only at hP
    by_cases hbase : isSparse3DPiece X Y Z A B D = true
    · rw [if_pos hbase] at hP
      simp only [List.mem_singleton] at hP
      subst hP
      exact validCubePiece_baseCase1Piece hA hB (Or.inl hbase)
    · rw [if_neg hbase] at hP
      have hnot_sp : isSparse3DPiece X Y Z A B D = false := Bool.eq_false_iff.mpr hbase
      rcases of_isSparse3DPiece_eq_false hnot_sp with ⟨hX, hY, hZ, _hA_gt, hB_gt⟩
      rcases thm_3d_decomp_part1 S hX hY hZ hA hB hε0 hε_le hD hα0 hB_gt with
        ⟨_hX_eq, hsubY, hsubZ, _hneY, _hneZ, _hsteps, _hSB_D, _hdens_scale, _hM_bound,
          hmode_or, _hbboost_spec, hnorm_spec⟩
      set cubeRes := cappedGoodCube X Y Z A B ε gamma3D D α_cap (matDensity Y Z B) S
      set B_rem := zeroOutSubrect B cubeRes.Y_star cubeRes.Z_star
      have hB_rem_bin : IsBinaryMatrix Y Z B_rem := isBinaryMatrix_zeroOutSubrect _ _ hB
      have hstep_fuel := (goodCube_fuel_step S hX hY hZ hA hB hε0 hε_le hD hα0 hB_gt).2
      have hfuel_rem :
          matDensity Y Z B_rem * ((2 : ℝ) ^ (D + D ^ 2) * M_cube ε gamma3D D) ≤ (fuel : ℝ) := by
        push_cast at hfuel
        linarith
      by_cases hmode : cubeRes.mode = CubeMode.bBoost
      · rw [if_pos hmode, List.mem_append] at hP
        rcases hP with hP_star | hP_boost
        · exact ih B_rem hB_rem_bin hfuel_rem hP_star
        · have hA_star : IsBinaryMatrix X cubeRes.Y_star (submatZeroExt X cubeRes.Y_star A) :=
            isBinaryMatrix_submatZeroExt Finset.Subset.rfl hsubY hA
          have hB_star :
              IsBinaryMatrix cubeRes.Y_star cubeRes.Z_star
                (submatZeroExt cubeRes.Y_star cubeRes.Z_star B) :=
            isBinaryMatrix_submatZeroExt hsubY hsubZ hB
          exact validCubePiece_mono Finset.Subset.rfl hsubY hsubZ
            (hrec_spec _ _ _ _ _ _ _ _ _ hA_star hB_star hα0 P hP_boost)
      · rw [if_neg hmode] at hP
        have hmode_norm : cubeRes.mode = CubeMode.normal := by
          rcases hmode_or with h1 | h2
          · exact False.elim (hmode h1)
          · exact h2
        rcases hnorm_spec hmode_norm with ⟨_hSB4, _hlt17, _hsum_A, hslices⟩
        rw [List.mem_append, List.mem_append] at hP
        rcases hP with (hP_dir | hP_star) | hP_rec
        · -- Direct piece in `S_direct`
          rw [List.mem_map] at hP_dir
          rcases hP_dir with ⟨sl, hsl_filt, rfl⟩
          have hsl_mem : sl ∈ cubeRes.slices := (List.mem_filter.mp hsl_filt).1
          have hsl_Zne : sl.Z_ell.Nonempty := of_decide_eq_true (List.mem_filter.mp hsl_filt).2
          rcases hslices sl hsl_mem with
            ⟨hslZ, hslX, hslY, hneX, hneY, hsl_bin, hsl_ext, hsl_res, hsl_ab, hsl_reg⟩
          dsimp only [ValidCubePiece, directSlicePiece]
          refine ⟨hslX, hslY.trans hsubY, hslZ.trans hsubZ, hsl_ext, ?_, hsl_bin,
            isBinaryMatrix_submatZeroExt (hslY.trans hsubY) (hslZ.trans hsubZ) hB, ?_, ?_⟩
          · intro y z; by_cases h : y ∈ sl.Y_ell ∧ z ∈ sl.Z_ell <;> simp [submatZeroExt, h]
          · intro hreg
            rcases of_decide_eq_true hreg with ⟨htag_reg, hmin_gt⟩
            rcases hsl_reg htag_reg with
              ⟨hneZ, _hS47, _hA_gt, _hA_lt, hregA, hminA, _hM, hregB, hminB, _⟩
            refine ⟨hneX, hneY, hneZ, hregA, ?_, hminA, ?_, hmin_gt⟩
            · refine isGridRegular_of_eq_on (fun z hz y hy => ?_) hregB
              simp [matTranspose, submatZeroExt, hy, hz]
            · refine isEpsMinDegree_of_eq_on (fun z hz y hy => ?_) hminB
              simp [matTranspose, submatZeroExt, hy, hz]
          · intro hnotreg
            have hnot_and := of_decide_eq_false hnotreg
            left
            by_cases htag_reg : sl.tag = RectTag.regular
            ·exact le_of_not_gt (fun hlt => hnot_and ⟨htag_reg, hlt⟩)
            · cases htag : sl.tag
              · exact False.elim (htag_reg htag)
              · have hemp := (hsl_ab htag).1
                rw [hemp] at hsl_Zne
                exact False.elim (Finset.not_nonempty_empty hsl_Zne)
              · have hdens_le := ((hsl_res htag).1 hsl_Zne).2
                rw [← two_rpow_neg_nat_eq_zpow] at hdens_le
                exact (min_le_left _ _).trans hdens_le
        · -- Tail-recursive piece in `S_star`
          exact ih B_rem hB_rem_bin hfuel_rem hP_star
        · -- Bucketed recursive piece in `S_rec`
          rw [List.mem_flatMap] at hP_rec
          rcases hP_rec with ⟨sl, hsl_filt, hP_buck⟩
          have hsl_mem : sl ∈ cubeRes.slices := (List.mem_filter.mp hsl_filt).1
          rcases hslices sl hsl_mem with
            ⟨_hslZ, hslX, hslY, _hneX, _hneY, hsl_bin, _hsl_ext, _⟩
          rw [mem_bucketedRec_iff] at hP_buck
          rcases hP_buck with ⟨j, _hj, _hnej, hP_call⟩
          set Y'_j := dyadicColBucket sl.X_ell sl.Y_ell sl.A_ell
            (matDensity sl.X_ell sl.Y_ell sl.A_ell) j
          have hY'j_sub : Y'_j ⊆ sl.Y_ell := dyadicColBucket_subset _ _ _ _ _
          have hAj_bin :
              IsBinaryMatrix sl.X_ell Y'_j (submatZeroExt sl.X_ell Y'_j sl.A_ell) :=
            isBinaryMatrix_submatZeroExt Finset.Subset.rfl hY'j_sub hsl_bin
          have hBj_bin :
              IsBinaryMatrix Y'_j (cubeRes.Z_star \ sl.Z_ell)
                (submatZeroExt Y'_j (cubeRes.Z_star \ sl.Z_ell)
                  (submatZeroExt sl.Y_ell (cubeRes.Z_star \ sl.Z_ell) B)) :=
            isBinaryMatrix_submatZeroExt hY'j_sub Finset.Subset.rfl
              (isBinaryMatrix_submatZeroExt (hslY.trans hsubY)
                (Finset.sdiff_subset.trans hsubZ) hB)
          have hα_nonneg : 0 ≤ matDensity sl.X_ell sl.Y_ell sl.A_ell :=
            matDensity_nonneg (isBinaryMatrix_nonneg hsl_bin)
          have hαj_0 : 0 ≤ dyadicColAlpha (matDensity sl.X_ell sl.Y_ell sl.A_ell) j := by
            unfold dyadicColAlpha; positivity
          exact validCubePiece_mono hslX (hY'j_sub.trans (hslY.trans hsubY))
            (Finset.sdiff_subset.trans hsubZ)
            (hrec_spec _ _ _ _ _ _ _ _ _ hAj_bin hBj_bin hαj_0 P hP_call)

/-- **Piece Specification for `cappedABDecompAux` (`cappedABDecompAux_pieces_spec`,
`paper.tex` Lemma 5.4 `\label{lem:children-invariants}` & Theorem 1.1 Clause 2, §5.3 & §5.6)**. -/
theorem cappedABDecompAux_pieces_spec [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (remDepth : ℕ) (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    {ε : ℝ} (S : TwoStageSamplerOracle β ε) {D : ℕ} (α_cap : ℝ) (capNum capDen : ℕ)
    (hA : IsBinaryMatrix X Y A) (hB : IsBinaryMatrix Y Z B)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hD : 2 ≤ D) (hα0 : 0 ≤ α_cap)
    {P : CubePiece α β γ}
    (hP : P ∈ cappedABDecompAux remDepth X Y Z A B ε S D α_cap capNum capDen) :
    ValidCubePiece X Y Z ε D P := by
  induction' remDepth using Nat.strong_induction_on with remDepth ih
    generalizing X Y Z A B α_cap capNum capDen P
  rcases remDepth with _ | rem
  · rw [cappedABDecompAux] at hP
    split_ifs at hP with hbase
    · simp only [List.mem_singleton] at hP
      subst hP
      exact validCubePiece_baseCase1Piece hA hB (Or.inl hbase)
    · rcases baseCase2Decomposition_pieces_spec X Y Z A B D hB hP with
        ⟨hPX, hPY, hPZ, hPA_eq, hPA_ext, hPB_ext, hPB_or, hreg_false, hsparse_or⟩
      dsimp only [ValidCubePiece]
      have hPA_bin : IsBinaryMatrix P.X_k P.Y_k P.A_k := by
        rw [hPA_eq]
        exact isBinaryMatrix_submatZeroExt hPX hPY hA
      have hPB_bin : IsBinaryMatrix P.Y_k P.Z_k P.B_k := by
        intro y hy z hz
        rcases hPB_or y hy z hz with h0 | heq
        · exact Or.inl h0
        · rw [heq]; exact hB y (hPY hy) z (hPZ hz)
      refine ⟨hPX, hPY, hPZ, hPA_ext, hPB_ext, hPA_bin, hPB_bin, ?_, fun _ => hsparse_or⟩
      rw [hreg_false]
      intro hf; cases hf
  · rw [cappedABDecompAux] at hP
    exact sStarLoop_pieces_spec (rSStarFuel ε D) X Y Z A B S α_cap capNum capDen (rem + 1)
      hA hB hε0 hε_le hD hα0
      (rSStarFuel_ge_of_isBinaryMatrix hB hε0 hε_le)
      (fun Δ X' Y' Z' A' B' α' capNum' capDen' =>
        cappedABDecompAux (rem - (Δ - 1)) X' Y' Z' A' B' ε S D α' capNum' capDen')
      (fun Δ X' Y' Z' A' B' α' capNum' capDen' hA' hB' hα' Q hQ =>
        ih (rem - (Δ - 1)) (by omega) X' Y' Z' A' B' α' capNum' capDen' hA' hB' hα' hQ)
      hP

/-- Subgrid containment and regularity / sparsity / single-edge properties of every piece
$P \in \text{cappedABDecomposition'}$ (`paper.tex` Lemma 5.4 `\label{lem:children-invariants}` & Theorem 1.1 Clause 2, §5.3 & §5.6). -/
theorem cappedABDecomposition'_pieces_spec [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    {ε : ℝ} (S : TwoStageSamplerOracle β ε) {D : ℕ} (α_cap : ℝ) (capNum capDen : ℕ) (h H : ℕ)
    (hA : IsBinaryMatrix X Y A) (hB : IsBinaryMatrix Y Z B)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hD : 2 ≤ D) (hα0 : 0 ≤ α_cap)
    {P : CubePiece α β γ}
    (hP : P ∈ cappedABDecomposition' X Y Z A B ε S D α_cap capNum capDen h H) :
    ValidCubePiece X Y Z ε D P :=
  cappedABDecompAux_pieces_spec (H - h) X Y Z A B S α_cap capNum capDen hA hB hε0 hε_le hD hα0 hP

/-- Root piece specification for `cappedABDecomposition` (Theorem 1.1 Clause 2, §1.2 & §5.6). -/
theorem cappedABDecomposition_pieces_spec [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    {ε : ℝ} (S : TwoStageSamplerOracle β ε) {D : ℕ}
    (hA : IsBinaryMatrix X Y A) (hB : IsBinaryMatrix Y Z B)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hD : 2 ≤ D)
    {P : CubePiece α β γ} (hP : P ∈ cappedABDecomposition X Y Z A B ε S D) :
    ValidCubePiece X Y Z ε D P :=
  cappedABDecomposition'_pieces_spec X Y Z A B S 1 1 1 0 (H3D D) hA hB hε0 hε_le hD (by norm_num) hP

lemma submatZeroExt_mono_on [DecidableEq α] [DecidableEq β]
    {U X' : Finset α} {V Y' : Finset β} {M₁ M₂ : α → β → ℝ}
    (hU : U ⊆ X') (hV : V ⊆ Y') (hle : ∀ x ∈ X', ∀ y ∈ Y', M₁ x y ≤ M₂ x y)
    (x : α) (y : β) :
    submatZeroExt U V M₁ x y ≤ submatZeroExt U V M₂ x y := by
  unfold submatZeroExt
  split_ifs with hxy
  · exact hle x (hU hxy.1) y (hV hxy.2)
  · exact le_rfl

lemma submatZeroExt_le_on [DecidableEq α] [DecidableEq β]
    (X' : Finset α) (Y' : Finset β) (M : α → β → ℝ) :
    ∀ x ∈ X', ∀ y ∈ Y', submatZeroExt X' Y' M x y ≤ M x y := by
  intro x hx y hy
  simp [submatZeroExt, hx, hy]

lemma zeroOutSubrect_le_on [DecidableEq α] [DecidableEq β]
    {X' : Finset α} {Y' : Finset β} {M : α → β → ℝ}
    (hM : IsBinaryMatrix X' Y' M) (U : Finset α) (V : Finset β) :
    ∀ x ∈ X', ∀ y ∈ Y', zeroOutSubrect M U V x y ≤ M x y := by
  intro x hx y hy
  unfold zeroOutSubrect
  split_ifs
  · exact isBinaryMatrix_nonneg hM x hx y hy
  · exact le_rfl

/-- **Entrywise Submatrix Dominance for `sStarLoop` (`sStarLoop_dominance`,
`paper.tex` Theorem 1.1 `\label{thm:main-decomp}` & Lemma 5.4 `\label{lem:children-invariants}`, §1.2, §5.3 & §5.6)**:
Every piece $P$ emitted by `sStarLoop` satisfies $P.X_k \subseteq X$, $P.Y_k \subseteq Y$,
$P.Z_k \subseteq Z$, $P.A_k(x, y) \le A[P.X_k, P.Y_k](x, y)$, and
$P.B_k(y, z) \le B[P.Y_k, P.Z_k](y, z)$. -/
theorem sStarLoop_dominance [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (sStarFuel : ℕ) (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    {ε : ℝ} (S : TwoStageSamplerOracle β ε) {D : ℕ} (α_cap : ℝ) (capNum capDen : ℕ) (remDepth : ℕ)
    (hA : IsBinaryMatrix X Y A) (hB : IsBinaryMatrix Y Z B)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hD : 2 ≤ D) (hα0 : 0 ≤ α_cap)
    (recDepth : ℕ → Finset α → Finset β → Finset γ →
      (α → β → ℝ) → (β → γ → ℝ) → ℝ → ℕ → ℕ → List (CubePiece α β γ))
    (hrec_dom : ∀ Δ X' Y' Z' A' B' α' capNum' capDen',
      IsBinaryMatrix X' Y' A' → IsBinaryMatrix Y' Z' B' → 0 ≤ α' →
      ∀ P ∈ recDepth Δ X' Y' Z' A' B' α' capNum' capDen',
        P.X_k ⊆ X' ∧ P.Y_k ⊆ Y' ∧ P.Z_k ⊆ Z' ∧
        (∀ x y, P.A_k x y ≤ submatZeroExt P.X_k P.Y_k A' x y) ∧
        (∀ y z, P.B_k y z ≤ submatZeroExt P.Y_k P.Z_k B' y z))
    {P : CubePiece α β γ}
    (hP : P ∈ sStarLoop sStarFuel X Y Z A B ε S D α_cap capNum capDen remDepth recDepth) :
    P.X_k ⊆ X ∧ P.Y_k ⊆ Y ∧ P.Z_k ⊆ Z ∧
    (∀ x y, P.A_k x y ≤ submatZeroExt P.X_k P.Y_k A x y) ∧
    (∀ y z, P.B_k y z ≤ submatZeroExt P.Y_k P.Z_k B y z) := by
  induction sStarFuel generalizing B with
  | zero =>
    unfold sStarLoop at hP
    simp only [List.mem_singleton] at hP
    subst hP
    exact ⟨Finset.Subset.rfl, Finset.Subset.rfl, Finset.Subset.rfl,
      fun _ _ => le_rfl, fun _ _ => le_rfl⟩
  | succ fuel ih =>
    unfold sStarLoop at hP
    dsimp only at hP
    by_cases hbase : isSparse3DPiece X Y Z A B D = true
    · rw [if_pos hbase] at hP
      simp only [List.mem_singleton] at hP
      subst hP
      exact ⟨Finset.Subset.rfl, Finset.Subset.rfl, Finset.Subset.rfl,
        fun _ _ => le_rfl, fun _ _ => le_rfl⟩
    · rw [if_neg hbase] at hP
      have hnot_sp : isSparse3DPiece X Y Z A B D = false := Bool.eq_false_iff.mpr hbase
      rcases of_isSparse3DPiece_eq_false hnot_sp with ⟨hX, hY, hZ, _hA_gt, hB_gt⟩
      rcases thm_3d_decomp_part1 S hX hY hZ hA hB hε0 hε_le hD hα0 hB_gt with
        ⟨_hX_eq, hsubY, hsubZ, _hneY, _hneZ, _hsteps, _hSB_D, _hdens_scale, _hM_bound,
          hmode_or, _hbboost_spec, hnorm_spec⟩
      set cubeRes := cappedGoodCube X Y Z A B ε gamma3D D α_cap (matDensity Y Z B) S
      set B_rem := zeroOutSubrect B cubeRes.Y_star cubeRes.Z_star
      have hB_rem_bin : IsBinaryMatrix Y Z B_rem := isBinaryMatrix_zeroOutSubrect _ _ hB
      by_cases hmode : cubeRes.mode = CubeMode.bBoost
      · rw [if_pos hmode, List.mem_append] at hP
        rcases hP with hP_star | hP_boost
        · rcases ih B_rem hB_rem_bin hP_star with ⟨hPX, hPY, hPZ, hPA, hPB⟩
          refine ⟨hPX, hPY, hPZ, hPA, fun y z => (hPB y z).trans ?_⟩
          exact submatZeroExt_mono_on hPY hPZ (zeroOutSubrect_le_on hB _ _) y z
        · have hA_star : IsBinaryMatrix X cubeRes.Y_star (submatZeroExt X cubeRes.Y_star A) :=
            isBinaryMatrix_submatZeroExt Finset.Subset.rfl hsubY hA
          have hB_star :
              IsBinaryMatrix cubeRes.Y_star cubeRes.Z_star
                (submatZeroExt cubeRes.Y_star cubeRes.Z_star B) :=
            isBinaryMatrix_submatZeroExt hsubY hsubZ hB
          rcases hrec_dom _ _ _ _ _ _ _ _ _ hA_star hB_star hα0 P hP_boost with
            ⟨hPX, hPY, hPZ, hPA, hPB⟩
          refine ⟨hPX, hPY.trans hsubY, hPZ.trans hsubZ,
            fun x y => (hPA x y).trans
              (submatZeroExt_mono_on hPX hPY (submatZeroExt_le_on _ _ A) x y),
            fun y z => (hPB y z).trans
              (submatZeroExt_mono_on hPY hPZ (submatZeroExt_le_on _ _ B) y z)⟩
      · rw [if_neg hmode] at hP
        have hmode_norm : cubeRes.mode = CubeMode.normal := by
          rcases hmode_or with h1 | h2
          · exact False.elim (hmode h1)
          · exact h2
        rcases hnorm_spec hmode_norm with ⟨_hSB4, _hlt17, hsum_A, hslices⟩
        have hsl_le_A : ∀ sl ∈ cubeRes.slices, ∀ x ∈ sl.X_ell, ∀ y ∈ sl.Y_ell, sl.A_ell x y ≤ A x y := by
          intro sl hsl x hx y hy
          rcases hslices sl hsl with ⟨_, hslX, hslY, _, _, _, _⟩
          have hnonneg_map :
              ∀ v ∈ cubeRes.slices.map (fun sl' => sl'.A_ell x y), 0 ≤ v := by
            intro v hv
            rw [List.mem_map] at hv
            rcases hv with ⟨sl', hsl', rfl⟩
            rcases hslices sl' hsl' with ⟨_, _, _, _, _, hsl'_bin, hsl'_ext, _⟩
            rw [hsl'_ext x y]
            unfold submatZeroExt
            split_ifs with hxy'
            · exact isBinaryMatrix_nonneg hsl'_bin x hxy'.1 y hxy'.2
            · exact le_rfl
          have hle_sum : sl.A_ell x y ≤ (cubeRes.slices.map (fun sl' => sl'.A_ell x y)).sum :=
            List.single_le_sum hnonneg_map (sl.A_ell x y)
              (List.mem_map_of_mem (f := fun sl' => sl'.A_ell x y) hsl)
          rw [hsum_A x y] at hle_sum
          have hxy_star : x ∈ X ∧ y ∈ cubeRes.Y_star := ⟨hslX hx, hslY hy⟩
          simpa [submatZeroExt, hxy_star] using hle_sum
        rw [List.mem_append, List.mem_append] at hP
        rcases hP with (hP_dir | hP_star) | hP_rec
        · rw [List.mem_map] at hP_dir
          rcases hP_dir with ⟨sl, hsl_filt, rfl⟩
          have hsl_mem : sl ∈ cubeRes.slices := (List.mem_filter.mp hsl_filt).1
          rcases hslices sl hsl_mem with
            ⟨hslZ, hslX, hslY, _hneX, _hneY, _hsl_bin, hsl_ext, _⟩
          dsimp only [directSlicePiece]
          refine ⟨hslX, hslY.trans hsubY, hslZ.trans hsubZ,
            fun x y => ?_, fun _ _ => le_rfl⟩
          rw [hsl_ext x y]
          exact submatZeroExt_mono_on Finset.Subset.rfl Finset.Subset.rfl
            (hsl_le_A sl hsl_mem) x y
        · rcases ih B_rem hB_rem_bin hP_star with ⟨hPX, hPY, hPZ, hPA, hPB⟩
          refine ⟨hPX, hPY, hPZ, hPA, fun y z => (hPB y z).trans ?_⟩
          exact submatZeroExt_mono_on hPY hPZ (zeroOutSubrect_le_on hB _ _) y z
        · rw [List.mem_flatMap] at hP_rec
          rcases hP_rec with ⟨sl, hsl_filt, hP_buck⟩
          have hsl_mem : sl ∈ cubeRes.slices := (List.mem_filter.mp hsl_filt).1
          rcases hslices sl hsl_mem with
            ⟨_hslZ, hslX, hslY, _hneX, _hneY, hsl_bin, _hsl_ext, _⟩
          rw [mem_bucketedRec_iff] at hP_buck
          rcases hP_buck with ⟨j, _hj, _hnej, hP_call⟩
          set Y'_j := dyadicColBucket sl.X_ell sl.Y_ell sl.A_ell
            (matDensity sl.X_ell sl.Y_ell sl.A_ell) j
          have hY'j_sub : Y'_j ⊆ sl.Y_ell := dyadicColBucket_subset _ _ _ _ _
          have hAj_bin :
              IsBinaryMatrix sl.X_ell Y'_j (submatZeroExt sl.X_ell Y'_j sl.A_ell) :=
            isBinaryMatrix_submatZeroExt Finset.Subset.rfl hY'j_sub hsl_bin
          have hBj_bin :
              IsBinaryMatrix Y'_j (cubeRes.Z_star \ sl.Z_ell)
                (submatZeroExt Y'_j (cubeRes.Z_star \ sl.Z_ell)
                  (submatZeroExt sl.Y_ell (cubeRes.Z_star \ sl.Z_ell) B)) :=
            isBinaryMatrix_submatZeroExt hY'j_sub Finset.Subset.rfl
              (isBinaryMatrix_submatZeroExt (hslY.trans hsubY)
                (Finset.sdiff_subset.trans hsubZ) hB)
          have hαj_0 : 0 ≤ dyadicColAlpha (matDensity sl.X_ell sl.Y_ell sl.A_ell) j := by
            unfold dyadicColAlpha
            have : 0 ≤ matDensity sl.X_ell sl.Y_ell sl.A_ell :=
              matDensity_nonneg (isBinaryMatrix_nonneg hsl_bin)
            positivity
          rcases hrec_dom _ _ _ _ _ _ _ _ _ hAj_bin hBj_bin hαj_0 P hP_call with
            ⟨hPX, hPY, hPZ, hPA, hPB⟩
          refine ⟨hPX.trans hslX, hPY.trans (hY'j_sub.trans (hslY.trans hsubY)),
            hPZ.trans (Finset.sdiff_subset.trans hsubZ),
            fun x y => (hPA x y).trans ?_, fun y z => (hPB y z).trans ?_⟩
          · refine submatZeroExt_mono_on hPX hPY (fun x' hx' y' hy' => ?_) x y
            have hy'_sl : y' ∈ sl.Y_ell := hY'j_sub hy'
            simpa [submatZeroExt, hx', hy'] using hsl_le_A sl hsl_mem x' hx' y' hy'_sl
          · refine submatZeroExt_mono_on hPY hPZ (fun y' hy' z' hz' => ?_) y z
            have hy'_sl : y' ∈ sl.Y_ell := hY'j_sub hy'
            simp [submatZeroExt, hy', hz', hy'_sl]

/-- **Entrywise Submatrix Dominance for `cappedABDecompAux` (`cappedABDecompAux_dominance`,
`paper.tex` Theorem 1.1 `\label{thm:main-decomp}` & Lemma 5.4 `\label{lem:children-invariants}`, §1.2, §5.3 & §5.6)**. -/
theorem cappedABDecompAux_dominance [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (remDepth : ℕ) (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    {ε : ℝ} (S : TwoStageSamplerOracle β ε) {D : ℕ} (α_cap : ℝ) (capNum capDen : ℕ)
    (hA : IsBinaryMatrix X Y A) (hB : IsBinaryMatrix Y Z B)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hD : 2 ≤ D) (hα0 : 0 ≤ α_cap)
    {P : CubePiece α β γ}
    (hP : P ∈ cappedABDecompAux remDepth X Y Z A B ε S D α_cap capNum capDen) :
    P.X_k ⊆ X ∧ P.Y_k ⊆ Y ∧ P.Z_k ⊆ Z ∧
    (∀ x y, P.A_k x y ≤ submatZeroExt P.X_k P.Y_k A x y) ∧
    (∀ y z, P.B_k y z ≤ submatZeroExt P.Y_k P.Z_k B y z) := by
  induction' remDepth using Nat.strong_induction_on with remDepth ih
    generalizing X Y Z A B α_cap capNum capDen P
  rcases remDepth with _ | rem
  · rw [cappedABDecompAux] at hP
    split_ifs at hP with hbase
    · simp only [List.mem_singleton] at hP
      subst hP
      exact ⟨Finset.Subset.rfl, Finset.Subset.rfl, Finset.Subset.rfl,
        fun _ _ => le_rfl, fun _ _ => le_rfl⟩
    · rcases baseCase2Decomposition_pieces_spec X Y Z A B D hB hP with
        ⟨hPX, hPY, hPZ, hPA_eq, hPA_ext, hPB_ext, hPB_or, _hreg_false, _hsparse_or⟩
      refine ⟨hPX, hPY, hPZ, fun x y => ?_, fun y z => ?_⟩
      · rw [hPA_eq]
        -- P.A_k = submatZeroExt P.X_k P.Y_k A by baseCase2Decomposition_pieces_spec
      · rw [hPB_ext y z]
        refine submatZeroExt_mono_on Finset.Subset.rfl Finset.Subset.rfl
          (fun y' hy' z' hz' => ?_) y z
        rcases hPB_or y' hy' z' hz' with h0 | heq
        · rw [h0]
          exact isBinaryMatrix_nonneg hB y' (hPY hy') z' (hPZ hz')
        · rw [heq]
  · rw [cappedABDecompAux] at hP
    exact sStarLoop_dominance (rSStarFuel ε D) X Y Z A B S α_cap capNum capDen (rem + 1)
      hA hB hε0 hε_le hD hα0
      (fun Δ X' Y' Z' A' B' α' capNum' capDen' =>
        cappedABDecompAux (rem - (Δ - 1)) X' Y' Z' A' B' ε S D α' capNum' capDen')
      (fun Δ X' Y' Z' A' B' α' capNum' capDen' hA' hB' hα' Q hQ =>
        ih (rem - (Δ - 1)) (by omega) X' Y' Z' A' B' α' capNum' capDen' hA' hB' hα' hQ)
      hP

/-- **Root Entrywise Submatrix Dominance for `cappedABDecomposition` (`cappedABDecomposition_dominance`,
`paper.tex` Theorem 1.1 `\label{thm:main-decomp}`, §1.2 & §5.6)**:
Every piece $P \in \text{cappedABDecomposition } X\ Y\ Z\ A\ B\ \varepsilon\ S\ D$ satisfies
$P.A_k(x, y) \le A[P.X_k, P.Y_k](x, y)$ and $P.B_k(y, z) \le B[P.Y_k, P.Z_k](y, z)$ entrywise. -/
theorem cappedABDecomposition_dominance [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    {ε : ℝ} (S : TwoStageSamplerOracle β ε) {D : ℕ}
    (hA : IsBinaryMatrix X Y A) (hB : IsBinaryMatrix Y Z B)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hD : 2 ≤ D)
    {P : CubePiece α β γ} (hP : P ∈ cappedABDecomposition X Y Z A B ε S D) :
    (∀ x y, P.A_k x y ≤ submatZeroExt P.X_k P.Y_k A x y) ∧
    (∀ y z, P.B_k y z ≤ submatZeroExt P.Y_k P.Z_k B y z) := by
  rcases cappedABDecompAux_dominance (H3D D - 0) X Y Z A B S 1 1 1
    hA hB hε0 hε_le hD (by norm_num) hP with ⟨_, _, _, hPA, hPB⟩
  exact ⟨hPA, hPB⟩

lemma isBinary_everywhere_of_validCubePiece [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {X : Finset α} {Y : Finset β} {Z : Finset γ} {ε : ℝ} {D : ℕ}
    {P : CubePiece α β γ} (hP : ValidCubePiece X Y Z ε D P) (x : α) (y : β) (z : γ) :
    (P.A_k x y = 0 ∨ P.A_k x y = 1) ∧ (P.B_k y z = 0 ∨ P.B_k y z = 1) := by
  rcases hP with ⟨_hX, _hY, _hZ, hPA_ext, hPB_ext, hPA_bin, hPB_bin, _⟩
  constructor
  · rw [hPA_ext x y]
    unfold submatZeroExt
    split_ifs with hxy
    · exact hPA_bin x hxy.1 y hxy.2
    · exact Or.inl rfl
  · rw [hPB_ext y z]
    unfold submatZeroExt
    split_ifs with hyz
    · exact hPB_bin y hyz.1 z hyz.2
    · exact Or.inl rfl

lemma list_sum_pos_iff_exists_pos {L : List ℝ} (hnonneg : ∀ u ∈ L, 0 ≤ u) :
    0 < L.sum ↔ ∃ u ∈ L, 0 < u := by
  induction L with
  | nil => simp
  | cons a l ih =>
    have ha : 0 ≤ a := hnonneg a List.mem_cons_self
    have hl : ∀ u ∈ l, 0 ≤ u := fun u hu => hnonneg u (List.mem_cons_of_mem a hu)
    have hl_sum : 0 ≤ l.sum := List.sum_nonneg hl
    simp only [List.sum_cons, List.mem_cons, exists_eq_or_imp, ← ih hl]
    constructor
    · intro hpos
      by_cases ha_pos : 0 < a
      · exact Or.inl ha_pos
      · right
        linarith
    · rintro (ha_pos | hl_pos) <;> linarith

/-- Witness equivalence for Boolean matrix multiplication on `Fin n`:
for any $A, B : \text{Fin } n \to \text{Fin } n \to \text{Bool}$, `boolMatMul n A B x z = true`
holds if and only if at least one piece of `cappedABDecomposition` contains a common 2-path witness
$y \in P.Y_k$ with $P.A_k(x, y) > 0$ and $P.B_k(y, z) > 0$. -/
theorem cappedABDecomposition_boolMatMul_iff (n : ℕ) (A B : Fin n → Fin n → Bool)
    {ε : ℝ} (S : TwoStageSamplerOracle (Fin n) ε) {D : ℕ}
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hD : 2 ≤ D) (x z : Fin n) :
    let pieces := cappedABDecomposition Finset.univ Finset.univ Finset.univ
      (bmatToReal A) (bmatToReal B) ε S D
    boolMatMul n A B x z = true ↔
      ∃ P ∈ pieces, x ∈ P.X_k ∧ z ∈ P.Z_k ∧ ∃ y ∈ P.Y_k, 0 < P.A_k x y ∧ 0 < P.B_k y z := by
  dsimp only
  set pieces := cappedABDecomposition Finset.univ Finset.univ Finset.univ
    (bmatToReal A) (bmatToReal B) ε S D
  have hA_bin : IsBinaryMatrix Finset.univ Finset.univ (bmatToReal A) :=
    isBinaryMatrix_bmatToReal Finset.univ Finset.univ A
  have hB_bin : IsBinaryMatrix Finset.univ Finset.univ (bmatToReal B) :=
    isBinaryMatrix_bmatToReal Finset.univ Finset.univ B
  have hsum := cappedABDecomposition_sum_eq Finset.univ Finset.univ Finset.univ
    (bmatToReal A) (bmatToReal B) S hA_bin hB_bin hε0 hε_le hD
    (Finset.mem_univ x) (Finset.mem_univ z)
  have hpiece_nonneg : ∀ P ∈ pieces, 0 ≤ stdMatMul P.Y_k P.A_k P.B_k x z := by
    intro P hP
    have hV := cappedABDecomposition_pieces_spec Finset.univ Finset.univ Finset.univ
      (bmatToReal A) (bmatToReal B) S hA_bin hB_bin hε0 hε_le hD hP
    unfold stdMatMul
    refine Finset.sum_nonneg (fun y _ => ?_)
    rcases isBinary_everywhere_of_validCubePiece hV x y z with ⟨hPA, hPB⟩
    have h1 : 0 ≤ P.A_k x y := by rcases hPA with h | h <;> linarith
    have h2 : 0 ≤ P.B_k y z := by rcases hPB with h | h <;> linarith
    exact mul_nonneg h1 h2
  have hpiece_pos_iff : ∀ P ∈ pieces,
      0 < stdMatMul P.Y_k P.A_k P.B_k x z ↔
        x ∈ P.X_k ∧ z ∈ P.Z_k ∧ ∃ y ∈ P.Y_k, 0 < P.A_k x y ∧ 0 < P.B_k y z := by
    intro P hP
    have hV := cappedABDecomposition_pieces_spec Finset.univ Finset.univ Finset.univ
      (bmatToReal A) (bmatToReal B) S hA_bin hB_bin hε0 hε_le hD hP
    rcases hV with ⟨_hX, _hY, _hZ, hPA_ext, hPB_ext, hPA_bin, hPB_bin, _⟩
    unfold stdMatMul
    constructor
    · intro hpos
      have hex : ∃ y ∈ P.Y_k, 0 < P.A_k x y * P.B_k y z := by
        by_contra! hall
        have := Finset.sum_nonpos hall
        linarith
      rcases hex with ⟨y, hy, hprod⟩
      rw [hPA_ext x y, hPB_ext y z] at hprod
      unfold submatZeroExt at hprod
      by_cases hx : x ∈ P.X_k <;> by_cases hz : z ∈ P.Z_k
      · simp only [hx, hy, hz, and_self, ↓reduceIte] at hprod
        have hA0 : 0 ≤ P.A_k x y := isBinaryMatrix_nonneg hPA_bin x hx y hy
        have hB0 : 0 ≤ P.B_k y z := isBinaryMatrix_nonneg hPB_bin y hy z hz
        have hA_pos : 0 < P.A_k x y := by
          rcases eq_or_lt_of_le hA0 with h0 | hlt
          · rw [← h0, zero_mul] at hprod; exact False.elim (lt_irrefl 0 hprod)
          · exact hlt
        have hB_pos : 0 < P.B_k y z := by
          rcases eq_or_lt_of_le hB0 with h0 | hlt
          · rw [← h0, mul_zero] at hprod; exact False.elim (lt_irrefl 0 hprod)
          · exact hlt
        exact ⟨hx, hz, y, hy, hA_pos, hB_pos⟩
      · simp [hx, hy, hz] at hprod
      · simp [hx, hy, hz] at hprod
      · simp [hx, hy, hz] at hprod
    · rintro ⟨_hx, _hz, y, hy, hA_pos, hB_pos⟩
      have hterm_pos : 0 < P.A_k x y * P.B_k y z := mul_pos hA_pos hB_pos
      have hnonneg_terms : ∀ y' ∈ P.Y_k, 0 ≤ P.A_k x y' * P.B_k y' z := by
        intro y' _
        rw [hPA_ext x y', hPB_ext y' z]
        unfold submatZeroExt
        split_ifs with h1 h2
        · exact mul_nonneg (isBinaryMatrix_nonneg hPA_bin x h1.1 y' h1.2)
            (isBinaryMatrix_nonneg hPB_bin y' h2.1 z h2.2)
        · simp
        · simp
        · simp
      have hle := Finset.single_le_sum hnonneg_terms hy
      linarith
  have hbmm_pos :
      boolMatMul n A B x z = true ↔
        0 < stdMatMul Finset.univ (bmatToReal A) (bmatToReal B) x z := by
    rw [boolMatMul_eq_true_iff]
    unfold stdMatMul
    have hnonneg_univ : ∀ y ∈ (Finset.univ : Finset (Fin n)),
        0 ≤ bmatToReal A x y * bmatToReal B y z := by
      intro y _
      have h1 : 0 ≤ bmatToReal A x y := by unfold bmatToReal boolToReal; cases A x y <;> norm_num
      have h2 : 0 ≤ bmatToReal B y z := by unfold bmatToReal boolToReal; cases B y z <;> norm_num
      exact mul_nonneg h1 h2
    constructor
    · rintro ⟨y, hAy, hBy⟩
      have hpos : 0 < bmatToReal A x y * bmatToReal B y z := by
        simp [bmatToReal, boolToReal, hAy, hBy]
      have hle := Finset.single_le_sum hnonneg_univ (Finset.mem_univ y)
      linarith
    · intro hpos
      have hex : ∃ y ∈ (Finset.univ : Finset (Fin n)), 0 < bmatToReal A x y * bmatToReal B y z := by
        by_contra! hall
        have := Finset.sum_nonpos hall
        linarith
      rcases hex with ⟨y, _, hprod⟩
      refine ⟨y, ?_, ?_⟩
      · cases h : A x y <;> simp_all [bmatToReal, boolToReal]
      · cases h : B y z <;> simp_all [bmatToReal, boolToReal]
  rw [hbmm_pos, ← hsum]
  have hlist_nonneg : ∀ u ∈ pieces.map (fun P => stdMatMul P.Y_k P.A_k P.B_k x z), 0 ≤ u := by
    intro u hu
    rw [List.mem_map] at hu
    rcases hu with ⟨P, hP, rfl⟩
    exact hpiece_nonneg P hP
  rw [list_sum_pos_iff_exists_pos hlist_nonneg]
  simp only [List.mem_map]
  constructor
  · rintro ⟨u, ⟨P, hP, rfl⟩, hu_pos⟩
    exact ⟨P, hP, (hpiece_pos_iff P hP).mp hu_pos⟩
  · rintro ⟨P, hP, hP_wit⟩
    exact ⟨stdMatMul P.Y_k P.A_k P.B_k x z, ⟨P, hP, rfl⟩, (hpiece_pos_iff P hP).mpr hP_wit⟩

/-!
### Part 5.2: Piece Count Bound $T(h) \le 3 \cdot 2^{D + D^2 + \Gamma(H - h)}$
(`paper.tex` Lemma 5.9 `\label{lem:recurrence}`, Eq. `\eqref{eq:th-inductive}`, §5.5)
-/

lemma list_flatMap_length_le_mul {ι κ : Type*} (L : List ι) (f : ι → List κ) (M : ℝ)
    (hf : ∀ x ∈ L, ((f x).length : ℝ) ≤ M) :
    ((L.flatMap f).length : ℝ) ≤ (L.length : ℝ) * M := by
  induction L with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.cast_add, Nat.cast_one]
    have ha := hf a List.mem_cons_self
    have hl := ih (fun x hx => hf x (List.mem_cons_of_mem a hx))
    linarith

lemma bucketedRec_length_le [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X' : Finset α) (Y' : Finset β) (Z' : Finset γ)
    (A' : α → β → ℝ) (B' : β → γ → ℝ) (μ : ℝ) (D : ℕ)
    (recCall : Finset α → Finset β → Finset γ →
      (α → β → ℝ) → (β → γ → ℝ) → ℝ → ℕ → List (CubePiece α β γ))
    {M : ℝ} (hM0 : 0 ≤ M)
    (hrec : ∀ j < D, (dyadicColBucket X' Y' A' μ j).Nonempty →
      let Y'_j := dyadicColBucket X' Y' A' μ j
      ((recCall X' Y'_j Z'
          (submatZeroExt X' Y'_j A') (submatZeroExt Y'_j Z' B') (dyadicColAlpha μ j) j).length : ℝ) ≤ M) :
    ((bucketedRec X' Y' Z' A' B' μ D recCall).length : ℝ) ≤ (D : ℝ) * M := by
  unfold bucketedRec
  have h1 := list_flatMap_length_le_mul
    ((List.range D).filter (fun j => decide (dyadicColBucket X' Y' A' μ j).Nonempty))
    (fun j =>
      let Y'_j := dyadicColBucket X' Y' A' μ j
      recCall X' Y'_j Z'
        (submatZeroExt X' Y'_j A') (submatZeroExt Y'_j Z' B') (dyadicColAlpha μ j) j)
    M
    (fun j hj => by
      rw [List.mem_filter, List.mem_range, decide_eq_true_eq] at hj
      exact hrec j hj.1 hj.2)
  have hlen :
      (((List.range D).filter (fun j => decide (dyadicColBucket X' Y' A' μ j).Nonempty)).length : ℝ) ≤
        (D : ℝ) := by
    have := List.length_filter_le (fun j => decide (dyadicColBucket X' Y' A' μ j).Nonempty) (List.range D)
    simpa using (Nat.cast_le.mpr this)
  exact h1.trans (mul_le_mul_of_nonneg_right hlen hM0)

lemma isBinaryMatrix_mono {U U' : Finset α} {V V' : Finset β} {M : α → β → ℝ}
    (hU : U' ⊆ U) (hV : V' ⊆ V) (hM : IsBinaryMatrix U V M) :
    IsBinaryMatrix U' V' M :=
  fun x hx y hy => hM x (hU hx) y (hV hy)

lemma T3DTree_le_three_mul_pow (ε : ℝ) (D k : ℕ) :
    T3DTree ε D k ≤ 3 * (2 : ℝ) ^ (D + D ^ 2 + GammaTree3D ε D * k) := by
  unfold T3DTree
  split_ifs with h0
  · subst h0
    have hexp : D ≤ D + D ^ 2 + GammaTree3D ε D * 0 := by omega
    have hpow : (2 : ℝ) ^ D ≤ (2 : ℝ) ^ (D + D ^ 2 + GammaTree3D ε D * 0) :=
      pow_le_pow_right₀ (by norm_num) hexp
    linarith
  · exact le_rfl

lemma one_le_pow_fifty_D_mul_zpow {s D : ℕ} (hs : s ≤ 47) :
    1 ≤ (2 : ℝ) ^ (50 * D) * (2 : ℝ) ^ (-(s * D : ℤ)) := by
  have hle : s * D ≤ 50 * D := Nat.mul_le_mul_right D (by omega)
  have hpow : (2 : ℝ) ^ (s * D) ≤ (2 : ℝ) ^ (50 * D) := pow_le_pow_right₀ (by norm_num) hle
  have hz : (2 : ℝ) ^ (s * D) * (2 : ℝ) ^ (-(s * D : ℤ)) = 1 := by
    have hcast : (-(s * D : ℤ)) = -((s * D : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, ← zpow_natCast 2 (s * D), ← zpow_add₀ (by norm_num), add_neg_cancel, zpow_zero]
  have hmul := mul_le_mul_of_nonneg_right hpow (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (-(s * D : ℤ)))
  linarith

lemma list_map_add_sum {σ : Type*} (L : List σ) (f g : σ → ℝ) :
    (L.map (fun x => f x + g x)).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma list_map_const_mul_sum {σ : Type*} (L : List σ) (c : ℝ) (f : σ → ℝ) :
    (L.map (fun x => c * f x)).sum = c * (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma list_filter_length_le_map_sum {σ : Type*} (L : List σ) (p : σ → Bool) (w : σ → ℝ)
    (hw0 : ∀ x ∈ L, 0 ≤ w x) (hw1 : ∀ x ∈ L, p x = true → 1 ≤ w x) :
    ((L.filter p).length : ℝ) ≤ (L.map w).sum := by
  induction L with
  | nil => simp
  | cons a l ih =>
    have ha0 := hw0 a List.mem_cons_self
    have hl0 : ∀ x ∈ l, 0 ≤ w x := fun x hx => hw0 x (List.mem_cons_of_mem a hx)
    have hl1 : ∀ x ∈ l, p x = true → 1 ≤ w x :=
      fun x hx hp => hw1 x (List.mem_cons_of_mem a hx) hp
    have hih := ih hl0 hl1
    rw [List.filter_cons, List.map_cons, List.sum_cons]
    cases hp : p a
    · simp only [Bool.false_eq_true, ↓reduceIte]; linarith
    · simp only [↓reduceIte, List.length_cons, Nat.cast_add, Nat.cast_one]
      have ha1 := hw1 a List.mem_cons_self hp
      linarith

lemma list_flatMap_filter_length_le_map_sum {σ τ : Type*} (L : List σ) (p : σ → Bool)
    (f : σ → List τ) (w : σ → ℝ)
    (hw0 : ∀ x ∈ L, 0 ≤ w x)
    (hf : ∀ x ∈ L, p x = true → ((f x).length : ℝ) ≤ w x) :
    (((L.filter p).flatMap f).length : ℝ) ≤ (L.map w).sum := by
  induction L with
  | nil => simp
  | cons a l ih =>
    have ha0 := hw0 a List.mem_cons_self
    have hl0 : ∀ x ∈ l, 0 ≤ w x := fun x hx => hw0 x (List.mem_cons_of_mem a hx)
    have hl1 : ∀ x ∈ l, p x = true → ((f x).length : ℝ) ≤ w x :=
      fun x hx hp => hf x (List.mem_cons_of_mem a hx) hp
    have hih := ih hl0 hl1
    rw [List.filter_cons, List.map_cons, List.sum_cons]
    cases hp : p a
    · simp only [Bool.false_eq_true, ↓reduceIte]; linarith
    · simp only [↓reduceIte, List.flatMap_cons, List.length_append, Nat.cast_add]
      have ha1 := hf a List.mem_cons_self hp
      linarith

/-- **Piece Count Recurrence Across `sStarLoop` (`sStarLoop_length_le`,
`paper.tex` Eq. `\eqref{eq:th-inductive}`, §5.5)**. -/
theorem sStarLoop_length_le [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (sStarFuel : ℕ) (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    {ε : ℝ} (S : TwoStageSamplerOracle β ε) {D k : ℕ} (α_cap : ℝ) (capNum capDen : ℕ)
    (hA : IsBinaryMatrix X Y A) (hB : IsBinaryMatrix Y Z B)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hD : 2 ≤ D) (hα_pos : 0 < α_cap)
    (hcap : α_cap = (capNum : ℝ) / (capDen : ℝ))
    (recDepth : ℕ → Finset α → Finset β → Finset γ →
      (α → β → ℝ) → (β → γ → ℝ) → ℝ → ℕ → ℕ → List (CubePiece α β γ))
    (hrec_len : ∀ Δ X' Y' Z' A' B' (α' : ℝ) (capNum' capDen' : ℕ),
      1 ≤ Δ → Δ ≤ k + 1 →
      IsBinaryMatrix X' Y' A' → IsBinaryMatrix Y' Z' B' → 0 < α' →
      α' = (capNum' : ℝ) / (capDen' : ℝ) →
      ((recDepth Δ X' Y' Z' A' B' α' capNum' capDen').length : ℝ) ≤ T3DTree ε D (k + 1 - Δ)) :
    ((sStarLoop sStarFuel X Y Z A B ε S D α_cap capNum capDen (k + 1) recDepth).length : ℝ) ≤
      1 + (2 * (D : ℝ) + 3) * QTree3D ε D *
        (3 * (2 : ℝ) ^ (D + D ^ 2 + GammaTree3D ε D * k)) * matDensity Y Z B := by
  set P_k := 3 * (2 : ℝ) ^ (D + D ^ 2 + GammaTree3D ε D * k)
  have hPk_ge_3 : 3 ≤ P_k := by
    unfold P_k
    have : (1 : ℝ) ≤ (2 : ℝ) ^ (D + D ^ 2 + GammaTree3D ε D * k) := one_le_pow₀ (by norm_num)
    linarith
  have hPk_pos : 0 < P_k := by linarith
  have hε1 : ε < 1 := by linarith
  have hMc_ge_3 : 3 ≤ M_cube ε gamma3D D := three_le_M_cube hε0 hε1.le gamma3D_pos D
  have hMr_ge_1 : 1 ≤ M_rect3D ε D := by
    unfold M_rect3D
    have := one_le_goodRect3DStepFactor hε0 hε1.le D
    have : (1 : ℝ) ≤ (goodRect3DStepFactor ε D) ^ (rRectFuel ε) := one_le_pow₀ this
    linarith
  have hQ_pos : 0 < QTree3D ε D := by unfold QTree3D; positivity
  induction sStarFuel generalizing B with
  | zero =>
    unfold sStarLoop
    simp only [List.length_singleton, Nat.cast_one]
    have hB0 : 0 ≤ matDensity Y Z B := matDensity_nonneg (isBinaryMatrix_nonneg hB)
    have : 0 ≤ (2 * (D : ℝ) + 3) * QTree3D ε D * P_k * matDensity Y Z B := by positivity
    linarith
  | succ fuel ih =>
    unfold sStarLoop
    dsimp only
    have hB0 : 0 ≤ matDensity Y Z B := matDensity_nonneg (isBinaryMatrix_nonneg hB)
    by_cases hbase : isSparse3DPiece X Y Z A B D = true
    · rw [if_pos hbase]
      simp only [List.length_singleton, Nat.cast_one]
      have : 0 ≤ (2 * (D : ℝ) + 3) * QTree3D ε D * P_k * matDensity Y Z B := by positivity
      linarith
    · rw [if_neg hbase]
      have hnot_sp : isSparse3DPiece X Y Z A B D = false := Bool.eq_false_iff.mpr hbase
      rcases of_isSparse3DPiece_eq_false hnot_sp with ⟨hX, hY, hZ, _hA_gt, hB_gt⟩
      have hpart1 := thm_3d_decomp_part1 S hX hY hZ hA hB hε0 hε_le hD hα_pos.le hB_gt
      have hstep_B := (goodCube_fuel_step S hX hY hZ hA hB hε0 hε_le hD hα_pos.le hB_gt).1
      have hextra :=
        cappedGoodCube_normal_extra_spec S hX hY hZ hA hB hε0 hε_le hD hα_pos.le hB_gt
      dsimp only at hpart1 hstep_B hextra ⊢
      generalize cappedGoodCube X Y Z A B ε gamma3D D α_cap (matDensity Y Z B) S = cubeRes
        at hpart1 hstep_B hextra ⊢
      rcases hpart1 with
        ⟨_hX_eq, hsubY, hsubZ, _hneY, _hneZ, _hsteps, hSB_D, hdens_scale, _hM_bound,
          hmode_or, _hbboost_spec, hnorm_spec⟩
      set B_rem := zeroOutSubrect B cubeRes.Y_star cubeRes.Z_star
      have hB_rem_bin : IsBinaryMatrix Y Z B_rem := isBinaryMatrix_zeroOutSubrect _ _ hB
      have hih := ih B_rem hB_rem_bin
      have hB_pos : 0 < matDensity Y Z B := lt_trans (by positivity) hB_gt
      have hdrop_nonneg : 0 ≤ matDensity Y Z B - matDensity Y Z B_rem := by
        have h1 : 0 < (2 : ℝ) ^ (-(cubeRes.S_B * D : ℤ)) := by positivity
        have h2 : 0 < (2 : ℝ) ^ D * M_cube ε gamma3D D := by positivity
        by_contra! hlt
        have hneg : (2 : ℝ) ^ D * M_cube ε gamma3D D * (matDensity Y Z B - matDensity Y Z B_rem) < 0 :=
          mul_neg_of_pos_of_neg h2 hlt
        linarith [hstep_B]
      by_cases hmode : cubeRes.mode = CubeMode.bBoost
      · -- Branch A (`bBoost`)
        rw [if_pos hmode, List.length_append, Nat.cast_add]
        have hraw_B_eq :
            rawDeltaHBNat (supportCountRealNat cubeRes.Y_star cubeRes.Z_star B)
              (cubeRes.Y_star.card * cubeRes.Z_star.card)
              (supportCountRealNat Y Z B) (Y.card * Z.card) =
            rawDeltaHB (matDensity cubeRes.Y_star cubeRes.Z_star B) (matDensity Y Z B) :=
          rawDeltaHBNat_supportCount_eq (isBinaryMatrix_mono hsubY hsubZ hB) hB
        rw [hraw_B_eq]
        set Δ_raw := rawDeltaHB (matDensity cubeRes.Y_star cubeRes.Z_star B) (matDensity Y Z B)
        set Δ := min (k + 1) Δ_raw
        have hΔ1 : 1 ≤ Δ := le_min (by omega) (one_le_rawDeltaHB _ _)
        have hΔ_le : Δ ≤ k + 1 := min_le_left _ _
        have hA_star : IsBinaryMatrix X cubeRes.Y_star (submatZeroExt X cubeRes.Y_star A) :=
          isBinaryMatrix_submatZeroExt Finset.Subset.rfl hsubY hA
        have hB_star :
            IsBinaryMatrix cubeRes.Y_star cubeRes.Z_star
              (submatZeroExt cubeRes.Y_star cubeRes.Z_star B) :=
          isBinaryMatrix_submatZeroExt hsubY hsubZ hB
        have hboost_len := hrec_len Δ X cubeRes.Y_star cubeRes.Z_star
          (submatZeroExt X cubeRes.Y_star A) (submatZeroExt cubeRes.Y_star cubeRes.Z_star B)
          α_cap capNum capDen hΔ1 hΔ_le hA_star hB_star hα_pos hcap
        have h50_B : cubeRes.S_B ≤ 50 * Δ_raw :=
          scale_le_fifty_mul_rawDeltaHB hB_pos hdens_scale
        have hjump := T3DTree_jump_le ε D k hSB_D (one_le_rawDeltaHB _ _) h50_B
        have hboost_step :
            ((recDepth Δ X cubeRes.Y_star cubeRes.Z_star
              (submatZeroExt X cubeRes.Y_star A)
              (submatZeroExt cubeRes.Y_star cubeRes.Z_star B) α_cap capNum capDen).length : ℝ) ≤
            (2 * (D : ℝ) + 3) * QTree3D ε D * P_k * (matDensity Y Z B - matDensity Y Z B_rem) := by
          have h1 := hboost_len.trans hjump
          have h2 := mul_le_mul_of_nonneg_right hstep_B
            (by positivity : 0 ≤ (2 : ℝ) ^ (50 * D) * P_k)
          have h51_le_60 : (2 : ℝ) ^ D * (2 : ℝ) ^ (50 * D) ≤ (2 : ℝ) ^ (60 * D) := by
            rw [← pow_add]
            exact pow_le_pow_right₀ (by norm_num) (by omega)
          have hQ_dom :
              (2 : ℝ) ^ D * M_cube ε gamma3D D * (2 : ℝ) ^ (50 * D) ≤
                (2 * (D : ℝ) + 3) * QTree3D ε D := by
            have hA0 :
                (2 : ℝ) ^ D * M_cube ε gamma3D D * (2 : ℝ) ^ (50 * D) =
                  ((2 : ℝ) ^ D * (2 : ℝ) ^ (50 * D)) * M_cube ε gamma3D D * 1 := by ring
            have hA1 :
                ((2 : ℝ) ^ D * (2 : ℝ) ^ (50 * D)) * M_cube ε gamma3D D * 1 ≤
                  (2 : ℝ) ^ (60 * D) * M_cube ε gamma3D D * M_rect3D ε D :=
              mul_le_mul (mul_le_mul_of_nonneg_right h51_le_60 (by linarith))
                hMr_ge_1 (by norm_num) (by positivity)
            have hA2 : (1 : ℝ) * QTree3D ε D ≤ (2 * (D : ℝ) + 3) * QTree3D ε D :=
              mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) D]) hQ_pos.le
            unfold QTree3D at hA2 ⊢
            linarith
          have h3 := mul_le_mul_of_nonneg_right hQ_dom
            (mul_nonneg hPk_pos.le hdrop_nonneg)
          calc
            ((recDepth Δ X cubeRes.Y_star cubeRes.Z_star
                (submatZeroExt X cubeRes.Y_star A)
                (submatZeroExt cubeRes.Y_star cubeRes.Z_star B) α_cap capNum capDen).length : ℝ)
              ≤ (2 : ℝ) ^ (-(cubeRes.S_B * D : ℤ)) * ((2 : ℝ) ^ (50 * D) * P_k) := by linarith
            _ ≤ ((2 : ℝ) ^ D * M_cube ε gamma3D D * (matDensity Y Z B - matDensity Y Z B_rem)) *
                  ((2 : ℝ) ^ (50 * D) * P_k) := h2
            _ = ((2 : ℝ) ^ D * M_cube ε gamma3D D * (2 : ℝ) ^ (50 * D)) *
                  (P_k * (matDensity Y Z B - matDensity Y Z B_rem)) := by ring
            _ ≤ ((2 * (D : ℝ) + 3) * QTree3D ε D) *
                  (P_k * (matDensity Y Z B - matDensity Y Z B_rem)) := h3
            _ = (2 * (D : ℝ) + 3) * QTree3D ε D * P_k *
                  (matDensity Y Z B - matDensity Y Z B_rem) := by ring
        linarith
      · -- Branch B (`normal`)
        rw [if_neg hmode, List.length_append, List.length_append, Nat.cast_add, Nat.cast_add]
        have hmode_norm : cubeRes.mode = CubeMode.normal := by
          rcases hmode_or with h1 | h2
          · exact False.elim (hmode h1)
          · exact h2
        rcases hnorm_spec hmode_norm with ⟨hSB4, _hlt17, _hsum_A, hslices⟩
        rcases hextra hmode_norm with
          ⟨_hmom, _hrpow, hres1, hscale_sum, _hlen_sl, hsl_extra⟩
        have h1_le_drop :
            1 ≤ (2 : ℝ) ^ (5 * D) * M_cube ε gamma3D D *
              (matDensity Y Z B - matDensity Y Z B_rem) := by
          have hle4 : cubeRes.S_B * D ≤ 4 * D := Nat.mul_le_mul_right D hSB4
          have hpow4 : (2 : ℝ) ^ (cubeRes.S_B * D) ≤ (2 : ℝ) ^ (4 * D) :=
            pow_le_pow_right₀ (by norm_num) hle4
          have hz : (2 : ℝ) ^ (cubeRes.S_B * D) * (2 : ℝ) ^ (-(cubeRes.S_B * D : ℤ)) = 1 := by
            have hcast : (-(cubeRes.S_B * D : ℤ)) = -((cubeRes.S_B * D : ℕ) : ℤ) := by push_cast; ring
            rw [hcast, ← zpow_natCast 2 (cubeRes.S_B * D), ← zpow_add₀ (by norm_num),
              add_neg_cancel, zpow_zero]
          have h1 : 1 ≤ (2 : ℝ) ^ (4 * D) * (2 : ℝ) ^ (-(cubeRes.S_B * D : ℤ)) := by
            have := mul_le_mul_of_nonneg_right hpow4
              (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (-(cubeRes.S_B * D : ℤ)))
            linarith
          have h2 := mul_le_mul_of_nonneg_left hstep_B (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (4 * D))
          have h5D : (2 : ℝ) ^ (4 * D) * (2 : ℝ) ^ D = (2 : ℝ) ^ (5 * D) := by
            rw [← pow_add]
            congr 1
            omega
          calc
            (1 : ℝ) ≤ (2 : ℝ) ^ (4 * D) * (2 : ℝ) ^ (-(cubeRes.S_B * D : ℤ)) := h1
            _ ≤ (2 : ℝ) ^ (4 * D) *
                  ((2 : ℝ) ^ D * M_cube ε gamma3D D * (matDensity Y Z B - matDensity Y Z B_rem)) := h2
            _ = ((2 : ℝ) ^ (4 * D) * (2 : ℝ) ^ D) * M_cube ε gamma3D D *
                  (matDensity Y Z B - matDensity Y Z B_rem) := by ring
            _ = (2 : ℝ) ^ (5 * D) * M_cube ε gamma3D D *
                  (matDensity Y Z B - matDensity Y Z B_rem) := by rw [h5D]
        let w : GoodCubeSlice α β γ → ℝ := fun sl =>
          (if sl.tag = RectTag.residual then (1 : ℝ) else 0) +
            (2 : ℝ) ^ (50 * D) *
              (if sl.tag ≠ RectTag.residual then (2 : ℝ) ^ (-(sl.S_ell * D : ℤ)) else 0)
        have hw0 : ∀ sl ∈ cubeRes.slices, 0 ≤ w sl := by
          intro sl _
          dsimp only [w]
          have h1 : 0 ≤ (if sl.tag = RectTag.residual then (1 : ℝ) else 0) := by split_ifs <;> norm_num
          have h2 : 0 ≤ (if sl.tag ≠ RectTag.residual then (2 : ℝ) ^ (-(sl.S_ell * D : ℤ)) else 0) := by
            split_ifs <;> positivity
          positivity
        have hw_sum :
            (cubeRes.slices.map w).sum ≤ 2 * (2 : ℝ) ^ (51 * D) * M_rect3D ε D := by
          dsimp only [w]
          rw [list_map_add_sum, hres1, list_map_const_mul_sum,
            ← list_filter_decide_map_sum_eq cubeRes.slices (fun sl => sl.tag ≠ RectTag.residual)]
          have h1 := mul_le_mul_of_nonneg_left hscale_sum (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (50 * D))
          have h51 : (2 : ℝ) ^ (50 * D) * ((2 : ℝ) ^ D * M_rect3D ε D) =
              (2 : ℝ) ^ (51 * D) * M_rect3D ε D := by
            have hp : (2 : ℝ) ^ (50 * D) * (2 : ℝ) ^ D = (2 : ℝ) ^ (51 * D) := by
              rw [← pow_add]; congr 1; omega
            rw [← mul_assoc, hp]
          rw [h51] at h1
          have hpow_ge_1 : (1 : ℝ) ≤ (2 : ℝ) ^ (51 * D) * M_rect3D ε D := by
            have hp1 : (1 : ℝ) ≤ (2 : ℝ) ^ (51 * D) := one_le_pow₀ (by norm_num)
            have := mul_le_mul hp1 hMr_ge_1 (by norm_num) (by positivity)
            linarith
          linarith
        have hdir_le :
            (((cubeRes.slices.filter (fun sl => decide sl.Z_ell.Nonempty)).map
              (directSlicePiece B D)).length : ℝ) ≤
            P_k * (cubeRes.slices.map w).sum := by
          rw [List.length_map]
          have h1 :
              ((cubeRes.slices.filter (fun sl => decide sl.Z_ell.Nonempty)).length : ℝ) ≤
                (cubeRes.slices.map w).sum := by
            refine list_filter_length_le_map_sum cubeRes.slices _ w hw0 (fun sl hsl hZne => ?_)
            have hne : sl.Z_ell.Nonempty := of_decide_eq_true hZne
            rcases hslices sl hsl with ⟨_, _, _, _, _, _, _, _, hsl_ab, hsl_reg⟩
            dsimp only [w]
            cases htag : sl.tag
            · -- `regular`
              rcases hsl_reg htag with ⟨_, hS47, _⟩
              have h50 := one_le_pow_fifty_D_mul_zpow (D := D) hS47
              simp only [reduceCtorEq, ↓reduceIte, ne_eq, not_false_eq_true, zero_add]
              exact h50
            · -- `aBoosted`
              have hemp := (hsl_ab htag).1
              rw [hemp] at hne
              exact False.elim (Finset.not_nonempty_empty hne)
            · -- `residual`
              simp only [↓reduceIte, ne_eq, not_true_eq_false, mul_zero, add_zero]
              exact le_rfl
          have hw_sum0 : 0 ≤ (cubeRes.slices.map w).sum := List.sum_nonneg (by
            intro v hv; rw [List.mem_map] at hv; rcases hv with ⟨sl, hsl, rfl⟩; exact hw0 sl hsl)
          have h2 : 1 * (cubeRes.slices.map w).sum ≤ P_k * (cubeRes.slices.map w).sum :=
            mul_le_mul_of_nonneg_right (by linarith [hPk_ge_3]) hw_sum0
          linarith
        have hrec_slices_le :
            ((((cubeRes.slices.filter (fun sl => decide (cubeRes.Z_star \ sl.Z_ell).Nonempty)).flatMap
              (fun sl =>
                let Z_rem := cubeRes.Z_star \ sl.Z_ell
                let α_ell := matDensity sl.X_ell sl.Y_ell sl.A_ell
                let p_ell := supportCountRealNat sl.X_ell sl.Y_ell sl.A_ell
                let q_ell := sl.X_ell.card * sl.Y_ell.card
                let Δ := min (k + 1) (rawDeltaHANat p_ell q_ell capNum capDen)
                bucketedRec sl.X_ell sl.Y_ell Z_rem sl.A_ell
                  (submatZeroExt sl.Y_ell Z_rem B) α_ell D
                  (fun X' Y'_j Z' A' B' α' j =>
                    recDepth Δ X' Y'_j Z' A' B' α' (2 ^ j * p_ell) q_ell))).length : ℝ)) ≤
            (D : ℝ) * P_k * (cubeRes.slices.map w).sum := by
          have h1 := list_flatMap_filter_length_le_map_sum cubeRes.slices
            (fun sl => decide (cubeRes.Z_star \ sl.Z_ell).Nonempty)
            (fun sl =>
              let Z_rem := cubeRes.Z_star \ sl.Z_ell
              let α_ell := matDensity sl.X_ell sl.Y_ell sl.A_ell
              let p_ell := supportCountRealNat sl.X_ell sl.Y_ell sl.A_ell
              let q_ell := sl.X_ell.card * sl.Y_ell.card
              let Δ := min (k + 1) (rawDeltaHANat p_ell q_ell capNum capDen)
              bucketedRec sl.X_ell sl.Y_ell Z_rem sl.A_ell
                (submatZeroExt sl.Y_ell Z_rem B) α_ell D
                (fun X' Y'_j Z' A' B' α' j =>
                  recDepth Δ X' Y'_j Z' A' B' α' (2 ^ j * p_ell) q_ell))
            (fun sl => ((D : ℝ) * P_k) * w sl)
            (fun sl hsl => mul_nonneg (by positivity) (hw0 sl hsl))
            (fun sl hsl hZrem => by
              have hZrem_ne : (cubeRes.Z_star \ sl.Z_ell).Nonempty := of_decide_eq_true hZrem
              rcases hslices sl hsl with ⟨_hslZ, _hslX, hslY, _hneX, _hneY, hsl_bin, _hsl_ext, _hsl_res, hsl_ab, hsl_reg⟩
              rcases hsl_extra sl hsl with ⟨hsl_S, hsl_nonres, hsl_res_extra⟩
              have hα_gt : (2 : ℝ) ^ (-(D : ℤ)) < matDensity sl.X_ell sl.Y_ell sl.A_ell := by
                by_cases htag : sl.tag = RectTag.residual
                · rcases hsl_res_extra htag with ⟨_, _, _, hZ_if⟩
                  by_contra hle; push_neg at hle
                  rw [if_pos hle] at hZ_if
                  rw [hZ_if, Finset.sdiff_self] at hZrem_ne
                  exact Finset.not_nonempty_empty hZrem_ne
                · exact hsl_nonres htag
              have hα_ell_pos : 0 < matDensity sl.X_ell sl.Y_ell sl.A_ell :=
                lt_trans (by positivity) hα_gt
              set α_ell := matDensity sl.X_ell sl.Y_ell sl.A_ell
              dsimp only
              have hraw_A_eq :
                  rawDeltaHANat (supportCountRealNat sl.X_ell sl.Y_ell sl.A_ell)
                    (sl.X_ell.card * sl.Y_ell.card) capNum capDen =
                  rawDeltaHA α_ell α_cap :=
                rawDeltaHANat_supportCount_eq hsl_bin hcap
              rw [hraw_A_eq]
              set Δ := min (k + 1) (rawDeltaHA α_ell α_cap)
              have hΔ1 : 1 ≤ Δ := le_min (by omega) (one_le_rawDeltaHA _ _)
              have hΔ_le : Δ ≤ k + 1 := min_le_left _ _
              have hT_nonneg : 0 ≤ T3DTree ε D (k + 1 - Δ) := by
                have := three_le_T3DTree ε D (k + 1 - Δ)
                linarith
              have hbuck := bucketedRec_length_le sl.X_ell sl.Y_ell (cubeRes.Z_star \ sl.Z_ell)
                sl.A_ell (submatZeroExt sl.Y_ell (cubeRes.Z_star \ sl.Z_ell) B) α_ell D
                (fun X' Y'_j Z' A' B' α' j =>
                  recDepth Δ X' Y'_j Z' A' B' α'
                    (2 ^ j * supportCountRealNat sl.X_ell sl.Y_ell sl.A_ell)
                    (sl.X_ell.card * sl.Y_ell.card))
                hT_nonneg
                (fun j _ _ => by
                  set Y'_j := dyadicColBucket sl.X_ell sl.Y_ell sl.A_ell α_ell j
                  have hY'j_sub : Y'_j ⊆ sl.Y_ell := dyadicColBucket_subset _ _ _ _ _
                  have hAj : IsBinaryMatrix sl.X_ell Y'_j (submatZeroExt sl.X_ell Y'_j sl.A_ell) :=
                    isBinaryMatrix_submatZeroExt Finset.Subset.rfl hY'j_sub hsl_bin
                  have hBj :
                      IsBinaryMatrix Y'_j (cubeRes.Z_star \ sl.Z_ell)
                        (submatZeroExt Y'_j (cubeRes.Z_star \ sl.Z_ell)
                          (submatZeroExt sl.Y_ell (cubeRes.Z_star \ sl.Z_ell) B)) :=
                    isBinaryMatrix_submatZeroExt hY'j_sub Finset.Subset.rfl
                      (isBinaryMatrix_submatZeroExt (hslY.trans hsubY)
                        (Finset.sdiff_subset.trans hsubZ) hB)
                  have hαj_pos : 0 < dyadicColAlpha α_ell j := by unfold dyadicColAlpha; positivity
                  have hcap_j :
                      dyadicColAlpha α_ell j =
                        ((2 ^ j * supportCountRealNat sl.X_ell sl.Y_ell sl.A_ell : ℕ) : ℝ) /
                          ((sl.X_ell.card * sl.Y_ell.card : ℕ) : ℝ) :=
                    dyadicColAlpha_eq_mul_supportCount_div hsl_bin j
                  exact hrec_len Δ sl.X_ell Y'_j (cubeRes.Z_star \ sl.Z_ell) _ _ _ _ _
                    hΔ1 hΔ_le hAj hBj hαj_pos hcap_j)
              have hT_le_Pk_w : T3DTree ε D (k + 1 - Δ) ≤ P_k * w sl := by
                have hT_le_Pk : T3DTree ε D (k + 1 - Δ) ≤ P_k :=
                  (T3DTree_mono (by omega : k + 1 - Δ ≤ k)).trans (T3DTree_le_three_mul_pow ε D k)
                dsimp only [w]
                cases htag : sl.tag
                · -- `regular`
                  rcases hsl_reg htag with ⟨_, hS47, _⟩
                  have h50 := one_le_pow_fifty_D_mul_zpow (D := D) hS47
                  simp only [reduceCtorEq, ↓reduceIte, ne_eq, not_false_eq_true, zero_add]
                  have hmul := mul_le_mul_of_nonneg_left h50 hPk_pos.le
                  linarith
                · -- `aBoosted`
                  rcases hsl_ab htag with ⟨_, _, _, hscale_A, _⟩
                  have h50_A : sl.S_ell ≤ 50 * rawDeltaHA α_ell α_cap :=
                    scale_le_fifty_mul_rawDeltaHA hα_pos hscale_A
                  have hjump := T3DTree_jump_le ε D k hsl_S (one_le_rawDeltaHA _ _) h50_A
                  simp only [reduceCtorEq, ↓reduceIte, ne_eq, not_false_eq_true, zero_add]
                  linarith
                · -- `residual`
                  simp only [↓reduceIte, ne_eq, not_true_eq_false, mul_zero, add_zero, mul_one]
                  exact hT_le_Pk
              calc
                ((bucketedRec sl.X_ell sl.Y_ell (cubeRes.Z_star \ sl.Z_ell)
                    sl.A_ell (submatZeroExt sl.Y_ell (cubeRes.Z_star \ sl.Z_ell) B)
                    α_ell D
                    (fun X' Y'_j Z' A' B' α' j =>
                      recDepth Δ X' Y'_j Z' A' B' α'
                        (2 ^ j * supportCountRealNat sl.X_ell sl.Y_ell sl.A_ell)
                        (sl.X_ell.card * sl.Y_ell.card))).length : ℝ)
                  ≤ (D : ℝ) * T3DTree ε D (k + 1 - Δ) := hbuck
                _ ≤ (D : ℝ) * (P_k * w sl) := mul_le_mul_of_nonneg_left hT_le_Pk_w (Nat.cast_nonneg D)
                _ = ((D : ℝ) * P_k) * w sl := by ring)
          rw [list_map_const_mul_sum] at h1
          exact h1
        have htot_step :
            (((cubeRes.slices.filter (fun sl => decide sl.Z_ell.Nonempty)).map
              (directSlicePiece B D)).length : ℝ) +
            ((((cubeRes.slices.filter (fun sl => decide (cubeRes.Z_star \ sl.Z_ell).Nonempty)).flatMap
              (fun sl =>
                let Z_rem := cubeRes.Z_star \ sl.Z_ell
                let α_ell := matDensity sl.X_ell sl.Y_ell sl.A_ell
                let p_ell := supportCountRealNat sl.X_ell sl.Y_ell sl.A_ell
                let q_ell := sl.X_ell.card * sl.Y_ell.card
                let Δ := min (k + 1) (rawDeltaHANat p_ell q_ell capNum capDen)
                bucketedRec sl.X_ell sl.Y_ell Z_rem sl.A_ell
                  (submatZeroExt sl.Y_ell Z_rem B) α_ell D
                  (fun X' Y'_j Z' A' B' α' j =>
                    recDepth Δ X' Y'_j Z' A' B' α' (2 ^ j * p_ell) q_ell))).length : ℝ)) ≤
            (2 * (D : ℝ) + 3) * QTree3D ε D * P_k * (matDensity Y Z B - matDensity Y Z B_rem) := by
          have hsum_dir_rec :
              P_k * (cubeRes.slices.map w).sum + (D : ℝ) * P_k * (cubeRes.slices.map w).sum ≤
                (2 * (D : ℝ) + 2) * (2 : ℝ) ^ (51 * D) * M_rect3D ε D * P_k := by
            have h1 := mul_le_mul_of_nonneg_left hw_sum
              (by positivity : 0 ≤ ((D : ℝ) + 1) * P_k)
            linarith
          have hmul_drop := mul_le_mul_of_nonneg_left h1_le_drop
            (by positivity : 0 ≤ (2 * (D : ℝ) + 2) * (2 : ℝ) ^ (51 * D) * M_rect3D ε D * P_k)
          have h56_le_60 : (2 : ℝ) ^ (51 * D) * (2 : ℝ) ^ (5 * D) ≤ (2 : ℝ) ^ (60 * D) := by
            rw [← pow_add]
            exact pow_le_pow_right₀ (by norm_num) (by omega)
          have hQ_bound :
              (2 * (D : ℝ) + 2) * (2 : ℝ) ^ (51 * D) * M_rect3D ε D *
                ((2 : ℝ) ^ (5 * D) * M_cube ε gamma3D D) ≤
                (2 * (D : ℝ) + 3) * QTree3D ε D := by
            have h1 :
                (2 : ℝ) ^ (51 * D) * (2 : ℝ) ^ (5 * D) * (M_cube ε gamma3D D * M_rect3D ε D) ≤
                  (2 : ℝ) ^ (60 * D) * M_cube ε gamma3D D * M_rect3D ε D := by
              have := mul_le_mul_of_nonneg_right h56_le_60
                (by positivity : 0 ≤ M_cube ε gamma3D D * M_rect3D ε D)
              linarith
            have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * (D : ℝ) + 2)
            have h3 : (2 * (D : ℝ) + 2) * QTree3D ε D ≤ (2 * (D : ℝ) + 3) * QTree3D ε D :=
              mul_le_mul_of_nonneg_right (by linarith) hQ_pos.le
            unfold QTree3D at h3 ⊢
            linarith
          have hmul_Q := mul_le_mul_of_nonneg_right hQ_bound
            (mul_nonneg hPk_pos.le hdrop_nonneg)
          linarith
        linarith

/-- **Inductive Piece Count Bound for `cappedABDecompAux` (`cappedABDecompAux_length_le`,
`paper.tex` Eq. `\eqref{eq:th-inductive}`, §5.5)**:
For every `remDepth = H - h`,
$$|\text{cappedABDecompAux } \text{remDepth } X \, Y \, Z \, A \, B \, \varepsilon \, D \, \alpha_{\text{cap}}| \le T(\text{remDepth}).$$ -/
theorem cappedABDecompAux_length_le [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (remDepth : ℕ) (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    {ε : ℝ} (S : TwoStageSamplerOracle β ε) {D : ℕ} (α_cap : ℝ) (capNum capDen : ℕ)
    (hA : IsBinaryMatrix X Y A) (hB : IsBinaryMatrix Y Z B)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hD : 2 ≤ D) (hα_pos : 0 < α_cap)
    (hcap : α_cap = (capNum : ℝ) / (capDen : ℝ)) :
    ((cappedABDecompAux remDepth X Y Z A B ε S D α_cap capNum capDen).length : ℝ) ≤
      T3DTree ε D remDepth := by
  induction' remDepth using Nat.strong_induction_on with remDepth ih
    generalizing X Y Z A B α_cap capNum capDen
  rcases remDepth with _ | k
  · rw [cappedABDecompAux, T3DTree_zero]
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ D := one_le_pow₀ (by norm_num)
    split_ifs
    · simp only [List.length_singleton, Nat.cast_one]
      linarith
    · have h2 := (baseCase2Decomposition_length_bounds X Y Z A B D).2
      exact_mod_cast h2
  · rw [cappedABDecompAux]
    have hsstar := sStarLoop_length_le (rSStarFuel ε D) X Y Z A B S α_cap capNum capDen
      hA hB hε0 hε_le hD hα_pos hcap
      (fun Δ X' Y' Z' A' B' α' capNum' capDen' =>
        cappedABDecompAux (k - (Δ - 1)) X' Y' Z' A' B' ε S D α' capNum' capDen')
      (fun Δ X' Y' Z' A' B' α' capNum' capDen' hΔ1 hΔ_le hA' hB' hα' hcap' => by
        have heq : k - (Δ - 1) = k + 1 - Δ := by omega
        rw [← heq]
        exact ih (k - (Δ - 1)) (by omega) X' Y' Z' A' B' α' capNum' capDen' hA' hB' hα' hcap')
    have hB_le_1 : matDensity Y Z B ≤ 1 := matDensity_le_one_of_isBinaryMatrix hB
    have hε1 : ε < 1 := by linarith
    have hMc_ge_3 : 3 ≤ M_cube ε gamma3D D := three_le_M_cube hε0 hε1.le gamma3D_pos D
    have hMr_pos : 0 < M_rect3D ε D := by
      unfold M_rect3D
      have := one_le_goodRect3DStepFactor hε0 hε1.le D
      positivity
    have hQ_pos : 0 < QTree3D ε D := by unfold QTree3D; positivity
    have hfac_nonneg :
        0 ≤ (2 * (D : ℝ) + 3) * QTree3D ε D *
          (3 * (2 : ℝ) ^ (D + D ^ 2 + GammaTree3D ε D * k)) := by positivity
    have hmul_1 := mul_le_mul_of_nonneg_left hB_le_1 hfac_nonneg
    have hclose := step_T3DTree_close (D := D) (k := k) hε0 hε_le
    linarith

/-- Piece count bound for `cappedABDecomposition'` (`paper.tex` Eq. `\eqref{eq:th-inductive}`, §5.5). -/
theorem cappedABDecomposition'_length_le [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    {ε : ℝ} (S : TwoStageSamplerOracle β ε) {D : ℕ} (α_cap : ℝ) (capNum capDen : ℕ) (h H : ℕ)
    (hA : IsBinaryMatrix X Y A) (hB : IsBinaryMatrix Y Z B)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hD : 2 ≤ D) (hα_pos : 0 < α_cap)
    (hcap : α_cap = (capNum : ℝ) / (capDen : ℝ)) :
    ((cappedABDecomposition' X Y Z A B ε S D α_cap capNum capDen h H).length : ℝ) ≤
      T3DTree ε D (H - h) :=
  cappedABDecompAux_length_le (H - h) X Y Z A B S α_cap capNum capDen hA hB hε0 hε_le hD hα_pos hcap

/-- Root piece count bound for `cappedABDecomposition` (`K ≤ 3 * 2^(D + D^2 + GammaTree3D ε D * H3D D)`,
`paper.tex` §5.5 & Theorem 1.1). -/
theorem cappedABDecomposition_length_le [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    {ε : ℝ} (S : TwoStageSamplerOracle β ε) {D : ℕ}
    (hA : IsBinaryMatrix X Y A) (hB : IsBinaryMatrix Y Z B)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hD : 2 ≤ D) :
    ((cappedABDecomposition X Y Z A B ε S D).length : ℝ) ≤
      3 * (2 : ℝ) ^ (D + D ^ 2 + GammaTree3D ε D * H3D D) := by
  have h1 := cappedABDecomposition'_length_le X Y Z A B S 1 1 1 0 (H3D D)
    hA hB hε0 hε_le hD (by norm_num) (by norm_num)
  rw [Nat.sub_zero] at h1
  exact h1.trans (T3DTree_le_three_mul_pow ε D (H3D D))

/-!
### Part 5.3: Inductive Potential Bound $C_{1/4, 1/4}(\mathcal{S}) \le \Lambda_h \alpha^{1/4} \beta^{1/4} |X||Y||Z|$
(`paper.tex` Lemma 5.5 `\label{lem:potential}`, Eqs. `\eqref{eq:inductive-potential}`–`\eqref{eq:bucketed-rec-bound}` & Table 6 (`\label{tab:potential-budget}`), §5.4)
-/

lemma matDensity_le_of_colDeg_le' {X : Finset α} {Y : Finset β} {A : α → β → ℝ} {c : ℝ}
    (hc0 : 0 ≤ c) (hcol : ∀ y ∈ Y, colDeg X A y ≤ c) :
    matDensity X Y A ≤ c := by
  rcases Y.eq_empty_or_nonempty with rfl | hY
  · simp [matDensity, rowDeg, expectSet, hc0]
  · rw [matDensity_eq_colDeg]
    exact expectSet_le_of_le hY hcol

lemma colDeg_submatZeroExt_eq' [DecidableEq α] [DecidableEq β]
    (X : Finset α) {Y' : Finset β} (A : α → β → ℝ) {y : β} (hy : y ∈ Y') :
    colDeg X (submatZeroExt X Y' A) y = colDeg X A y := by
  unfold colDeg expectSet submatZeroExt
  congr 1
  refine Finset.sum_congr rfl (fun x hx => ?_)
  simp [hx, hy]

lemma Lambda3D_sub_sub_eq {H k Δ : ℕ} (hkH : k + 1 ≤ H) (hΔ : Δ ≤ k + 1) :
    Lambda3D ((H - (k + 1 - Δ) : ℕ) : ℝ) =
      (2 : ℝ) ^ (Δ : ℝ) * Lambda3D ((H - (k + 1) : ℕ) : ℝ) := by
  have heq : H - (k + 1 - Δ) = (H - (k + 1)) + Δ := by omega
  rw [heq]
  push_cast
  unfold Lambda3D
  rw [Real.rpow_add (by norm_num)]
  ring

lemma cubePotential_baseCase1Piece_le [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ) (ε : ℝ) (D h : ℕ) {α_cap : ℝ}
    (hA : IsBinaryMatrix X Y A) (hB : IsBinaryMatrix Y Z B)
    (hα0 : 0 ≤ α_cap) (hcol : ∀ y ∈ Y, colDeg X A y ≤ 2 * α_cap) :
    cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ) [baseCase1Piece X Y Z A B ε D] ≤
      Lambda3D (h : ℝ) * α_cap ^ ((1 : ℝ) / 4) *
        (matDensity Y Z B) ^ ((1 : ℝ) / 4) *
        (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ) := by
  unfold cubePotential baseCase1Piece
  simp only [List.map_singleton, List.sum_singleton,
    matDensity_submatZeroExt_eq X Y A, matDensity_submatZeroExt_eq Y Z B]
  have hA0 : 0 ≤ matDensity X Y A := matDensity_nonneg (isBinaryMatrix_nonneg hA)
  have hB0 : 0 ≤ matDensity Y Z B := matDensity_nonneg (isBinaryMatrix_nonneg hB)
  have hA_le : matDensity X Y A ≤ 2 * α_cap :=
    matDensity_le_of_colDeg_le' (by linarith) hcol
  have hα_rpow : (matDensity X Y A) ^ ((1 : ℝ) / 4) ≤ 2 * α_cap ^ ((1 : ℝ) / 4) := by
    calc
      (matDensity X Y A) ^ ((1 : ℝ) / 4) ≤ (2 * α_cap) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow hA0 hA_le (by norm_num)
      _ = (2 : ℝ) ^ ((1 : ℝ) / 4) * α_cap ^ ((1 : ℝ) / 4) :=
        Real.mul_rpow (by norm_num) hα0
      _ ≤ 2 * α_cap ^ ((1 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right two_rpow_quarter_le_two (Real.rpow_nonneg hα0 _)
  have hΛ : 128 ≤ Lambda3D (h : ℝ) := Lambda3D_ge_128 (Nat.cast_nonneg h)
  have hle_Λ : (matDensity X Y A) ^ ((1 : ℝ) / 4) ≤ Lambda3D (h : ℝ) * α_cap ^ ((1 : ℝ) / 4) := by
    have : 0 ≤ α_cap ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hα0 _
    nlinarith
  have hrest :
      0 ≤ (matDensity Y Z B) ^ ((1 : ℝ) / 4) * (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ) := by
    have : 0 ≤ (matDensity Y Z B) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hB0 _
    positivity
  have hmul := mul_le_mul_of_nonneg_right hle_Λ hrest
  linarith

lemma cubePotential_filter_map_le_sum {σ : Type*} (p q : ℝ) (L : List σ) (pred : σ → Bool)
    (g : σ → CubePiece α β γ) (w : σ → ℝ)
    (hw0 : ∀ x ∈ L, 0 ≤ w x)
    (hg : ∀ x ∈ L, pred x = true →
      (matDensity (g x).X_k (g x).Y_k (g x).A_k) ^ p *
        (matDensity (g x).Y_k (g x).Z_k (g x).B_k) ^ q *
        ((g x).X_k.card : ℝ) * ((g x).Y_k.card : ℝ) * ((g x).Z_k.card : ℝ) ≤ w x) :
    cubePotential p q ((L.filter pred).map g) ≤ (L.map w).sum := by
  unfold cubePotential
  induction L with
  | nil => simp
  | cons a l ih =>
    have ha0 := hw0 a List.mem_cons_self
    have hl0 : ∀ x ∈ l, 0 ≤ w x := fun x hx => hw0 x (List.mem_cons_of_mem a hx)
    have hl1 : ∀ x ∈ l, pred x = true → _ ≤ w x :=
      fun x hx hp => hg x (List.mem_cons_of_mem a hx) hp
    have hih := ih hl0 hl1
    rw [List.filter_cons, List.map_cons, List.sum_cons]
    cases hp : pred a
    · simp only [Bool.false_eq_true, ↓reduceIte]; linarith
    · simp only [↓reduceIte, List.map_cons, List.sum_cons]
      have ha1 := hg a List.mem_cons_self hp
      linarith

lemma cubePotential_filter_flatMap_le_sum {σ : Type*} (p q : ℝ) (L : List σ) (pred : σ → Bool)
    (f : σ → List (CubePiece α β γ)) (w : σ → ℝ)
    (hw0 : ∀ x ∈ L, 0 ≤ w x)
    (hf : ∀ x ∈ L, pred x = true → cubePotential p q (f x) ≤ w x) :
    cubePotential p q ((L.filter pred).flatMap f) ≤ (L.map w).sum := by
  induction L with
  | nil => simp [cubePotential]
  | cons a l ih =>
    have ha0 := hw0 a List.mem_cons_self
    have hl0 : ∀ x ∈ l, 0 ≤ w x := fun x hx => hw0 x (List.mem_cons_of_mem a hx)
    have hl1 : ∀ x ∈ l, pred x = true → cubePotential p q (f x) ≤ w x :=
      fun x hx hp => hf x (List.mem_cons_of_mem a hx) hp
    have hih := ih hl0 hl1
    rw [List.filter_cons, List.map_cons, List.sum_cons]
    cases hp : pred a
    · simp only [Bool.false_eq_true, ↓reduceIte]; linarith
    · simp only [↓reduceIte, List.flatMap_cons, cubePotential_append]
      have ha1 := hf a List.mem_cons_self hp
      linarith

lemma cLow3D_mul_rpow_quarter {α_cap : ℝ} (hα0 : 0 ≤ α_cap) :
    (cLow3D * α_cap) ^ ((1 : ℝ) / 4) = (1 / 256 : ℝ) * α_cap ^ ((1 : ℝ) / 4) := by
  rw [Real.mul_rpow (by unfold cLow3D; norm_num) hα0]
  have hc : cLow3D ^ ((1 : ℝ) / 4) = (1 / 256 : ℝ) := by
    have h1 : cLow3D = ((1 / 256 : ℝ) ^ (4 : ℕ)) := by unfold cLow3D; norm_num
    rw [h1, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [hc]

set_option maxHeartbeats 1000000 in
/-- **Inductive Potential Conservation Across `sStarLoop` (`sStarLoop_potential_le`,
`paper.tex` Lemma 5.5 `\label{lem:potential}`, Eqs. `\eqref{eq:concavity-drop}`–`\eqref{eq:bucketed-rec-bound}` & Table 6 (`\label{tab:potential-budget}`),
§5.4)**. -/
theorem sStarLoop_potential_le [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (sStarFuel : ℕ) (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    {ε : ℝ} (S : TwoStageSamplerOracle β ε) {D k H : ℕ} (α_cap : ℝ) (capNum capDen : ℕ)
    (hA : IsBinaryMatrix X Y A) (hB : IsBinaryMatrix Y Z B)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hD : 2 ≤ D) (hα_pos : 0 < α_cap)
    (hcap : α_cap = (capNum : ℝ) / (capDen : ℝ))
    (hcol_le : ∀ y ∈ Y, colDeg X A y ≤ 2 * α_cap)
    (hkH : k + 1 ≤ H)
    (hfuel : matDensity Y Z B * ((2 : ℝ) ^ (D + D ^ 2) * M_cube ε gamma3D D) ≤ (sStarFuel : ℝ))
    (recDepth : ℕ → Finset α → Finset β → Finset γ →
      (α → β → ℝ) → (β → γ → ℝ) → ℝ → ℕ → ℕ → List (CubePiece α β γ))
    (hrec_pot : ∀ Δ X' Y' Z' A' B' (α' : ℝ) (capNum' capDen' : ℕ),
      1 ≤ Δ → Δ ≤ k + 1 →
      IsBinaryMatrix X' Y' A' → IsBinaryMatrix Y' Z' B' → 0 < α' →
      α' = (capNum' : ℝ) / (capDen' : ℝ) →
      (∀ y ∈ Y', colDeg X' A' y ≤ 2 * α') →
      cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ) (recDepth Δ X' Y' Z' A' B' α' capNum' capDen') ≤
        Lambda3D ((H - (k + 1 - Δ) : ℕ) : ℝ) * α' ^ ((1 : ℝ) / 4) *
          (matDensity Y' Z' B') ^ ((1 : ℝ) / 4) *
          (X'.card : ℝ) * (Y'.card : ℝ) * (Z'.card : ℝ)) :
    cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ)
      (sStarLoop sStarFuel X Y Z A B ε S D α_cap capNum capDen (k + 1) recDepth) ≤
      Lambda3D ((H - (k + 1) : ℕ) : ℝ) * α_cap ^ ((1 : ℝ) / 4) *
        (matDensity Y Z B) ^ ((1 : ℝ) / 4) *
        (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ) := by
  set h := H - (k + 1)
  have hΛ_ge : 128 ≤ Lambda3D (h : ℝ) := Lambda3D_ge_128 (Nat.cast_nonneg h)
  have hΛ_pos : 0 < Lambda3D (h : ℝ) := by linarith
  induction sStarFuel generalizing B with
  | zero =>
    unfold sStarLoop
    exact cubePotential_baseCase1Piece_le X Y Z A B ε D h hA hB hα_pos.le hcol_le
  | succ fuel ih =>
    unfold sStarLoop
    dsimp only
    by_cases hbase : isSparse3DPiece X Y Z A B D = true
    · rw [if_pos hbase]
      exact cubePotential_baseCase1Piece_le X Y Z A B ε D h hA hB hα_pos.le hcol_le
    · rw [if_neg hbase]
      have hnot_sp : isSparse3DPiece X Y Z A B D = false := Bool.eq_false_iff.mpr hbase
      rcases of_isSparse3DPiece_eq_false hnot_sp with ⟨hX, hY, hZ, _hA_gt, hB_gt⟩
      have hpart1 := thm_3d_decomp_part1 S hX hY hZ hA hB hε0 hε_le hD hα_pos.le hB_gt
      have hstep_fuel := (goodCube_fuel_step S hX hY hZ hA hB hε0 hε_le hD hα_pos.le hB_gt).2
      dsimp only at hpart1 hstep_fuel ⊢
      generalize hcube : cappedGoodCube X Y Z A B ε gamma3D D α_cap (matDensity Y Z B) S = cubeRes
        at hpart1 hstep_fuel ⊢
      rcases hpart1 with
        ⟨_hX_eq, hsubY, hsubZ, _hneY, _hneZ, _hsteps, _hSB_D, hdens_scale, _hM_bound,
          hmode_or, hbboost_spec, hnorm_spec⟩
      set B_rem := zeroOutSubrect B cubeRes.Y_star cubeRes.Z_star
      have hB_rem_bin : IsBinaryMatrix Y Z B_rem := isBinaryMatrix_zeroOutSubrect _ _ hB
      have hfuel_rem :
          matDensity Y Z B_rem * ((2 : ℝ) ^ (D + D ^ 2) * M_cube ε gamma3D D) ≤ (fuel : ℝ) := by
        push_cast at hfuel
        linarith
      have hih := ih B_rem hB_rem_bin hfuel_rem
      set β_cur := matDensity Y Z B
      set β_star := matDensity cubeRes.Y_star cubeRes.Z_star B
      set β_rem := matDensity Y Z B_rem
      have hβ_pos : 0 < β_cur := lt_trans (by positivity) hB_gt
      have h1_le_2s : (1 : ℝ) ≤ (2 : ℝ) ^ cubeRes.S_B := one_le_pow₀ (by norm_num)
      have hβ_le_star : β_cur ≤ β_star := by
        have : 1 * β_cur ≤ (2 : ℝ) ^ cubeRes.S_B * β_cur := mul_le_mul_of_nonneg_right h1_le_2s hβ_pos.le
        linarith [hdens_scale]
      have hstar_pos : 0 < β_star := lt_of_lt_of_le hβ_pos hβ_le_star
      have hrem0 : 0 ≤ β_rem := matDensity_nonneg (isBinaryMatrix_nonneg hB_rem_bin)
      have hY_pos : (0 : ℝ) < (Y.card : ℝ) := Nat.cast_pos.mpr hY.card_pos
      have hZ_pos : (0 : ℝ) < (Z.card : ℝ) := Nat.cast_pos.mpr hZ.card_pos
      have hYZ_pos : (0 : ℝ) < (Y.card : ℝ) * (Z.card : ℝ) := mul_pos hY_pos hZ_pos
      have hYZ_ne : (Y.card : ℝ) * (Z.card : ℝ) ≠ 0 := hYZ_pos.ne'
      set q := ((cubeRes.Y_star.card : ℝ) * (cubeRes.Z_star.card : ℝ)) /
        ((Y.card : ℝ) * (Z.card : ℝ))
      have hq0 : 0 ≤ q := by unfold q; positivity
      have hzero_B := matDensity_zeroOutSubrect_eq B hY hZ hsubY hsubZ
      have hrem_eq : β_rem = β_cur - q * β_star := by
        unfold q β_rem B_rem β_cur β_star
        have hdiv := congrArg (fun u => u / ((Y.card : ℝ) * (Z.card : ℝ))) hzero_B
        dsimp only at hdiv
        field_simp [hYZ_ne] at hdiv ⊢
        linarith
      rcases concavity_drop_beta_rem hβ_pos hrem0 hq0 hstar_pos.le hrem_eq with ⟨hconc1, hconc2⟩
      have hcol_Ystar : ∀ y ∈ cubeRes.Y_star,
          colDeg X (submatZeroExt X cubeRes.Y_star A) y ≤ 2 * α_cap := by
        intro y hy
        rw [colDeg_submatZeroExt_eq' X A hy]
        exact hcol_le y (hsubY hy)
      have hA_Ystar_le : matDensity X cubeRes.Y_star A ≤ 2 * α_cap := by
        have h1 : matDensity X cubeRes.Y_star (submatZeroExt X cubeRes.Y_star A) ≤ 2 * α_cap :=
          matDensity_le_of_colDeg_le' (by linarith) hcol_Ystar
        rwa [matDensity_submatZeroExt_eq] at h1
      set W := α_cap ^ ((1 : ℝ) / 4) * β_cur ^ ((1 : ℝ) / 4) *
        (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ)
      set W_star := Lambda3D (h : ℝ) * α_cap ^ ((1 : ℝ) / 4) * β_star ^ ((1 : ℝ) / 4) *
        (X.card : ℝ) * (cubeRes.Y_star.card : ℝ) * (cubeRes.Z_star.card : ℝ)
      have hW_star_nonneg : 0 ≤ W_star := by
        unfold W_star
        have : 0 ≤ α_cap ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hα_pos.le _
        have : 0 ≤ β_star ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hstar_pos.le _
        positivity
      have hq_Wstar :
          Lambda3D (h : ℝ) * α_cap ^ ((1 : ℝ) / 4) *
            (q * β_star ^ ((1 : ℝ) / 4)) *
            (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ) = W_star := by
        unfold q W_star
        field_simp [hYZ_ne]
      by_cases hmode : cubeRes.mode = CubeMode.bBoost
      · -- Case A: Branch A (`bBoost`, `paper.tex` §5.4 Claim 5.7 `\label{clm:pot-boost}`)
        clear hcube
        rw [if_pos hmode, cubePotential_append]
        have hraw_B_eq :
            rawDeltaHBNat (supportCountRealNat cubeRes.Y_star cubeRes.Z_star B)
              (cubeRes.Y_star.card * cubeRes.Z_star.card)
              (supportCountRealNat Y Z B) (Y.card * Z.card) =
            rawDeltaHB β_star β_cur :=
          rawDeltaHBNat_supportCount_eq (isBinaryMatrix_mono hsubY hsubZ hB) hB
        rw [hraw_B_eq]
        have hboost16 : 16 * β_cur ≤ β_star :=
          (mul_le_mul_of_nonneg_right (le_max_left 16 _) hβ_pos.le).trans (hbboost_spec hmode)
        set Δ := min (k + 1) (rawDeltaHB β_star β_cur)
        have hΔ1 : 1 ≤ Δ := le_min (by omega) (one_le_rawDeltaHB _ _)
        have hΔ_le : Δ ≤ k + 1 := min_le_left _ _
        have hA_star : IsBinaryMatrix X cubeRes.Y_star (submatZeroExt X cubeRes.Y_star A) :=
          isBinaryMatrix_submatZeroExt Finset.Subset.rfl hsubY hA
        have hB_star :
            IsBinaryMatrix cubeRes.Y_star cubeRes.Z_star
              (submatZeroExt cubeRes.Y_star cubeRes.Z_star B) :=
          isBinaryMatrix_submatZeroExt hsubY hsubZ hB
        have hboost_pot := hrec_pot Δ X cubeRes.Y_star cubeRes.Z_star
          (submatZeroExt X cubeRes.Y_star A) (submatZeroExt cubeRes.Y_star cubeRes.Z_star B)
          α_cap capNum capDen hΔ1 hΔ_le hA_star hB_star hα_pos hcap hcol_Ystar
        rw [matDensity_submatZeroExt_eq, Lambda3D_sub_sub_eq hkH hΔ_le] at hboost_pot
        have hpow_Δ := two_pow_min_rawDeltaHB_le (k + 1) hβ_pos hboost16
        have hboost_Wstar :
            cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ)
              (recDepth Δ X cubeRes.Y_star cubeRes.Z_star
                (submatZeroExt X cubeRes.Y_star A)
                (submatZeroExt cubeRes.Y_star cubeRes.Z_star B) α_cap capNum capDen) ≤
            (1 / 4 : ℝ) * (β_star / β_cur) ^ ((3 : ℝ) / 4) * W_star := by
          have hmul := mul_le_mul_of_nonneg_right hpow_Δ hW_star_nonneg
          calc
            cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ)
                (recDepth Δ X cubeRes.Y_star cubeRes.Z_star
                  (submatZeroExt X cubeRes.Y_star A)
                  (submatZeroExt cubeRes.Y_star cubeRes.Z_star B) α_cap capNum capDen)
              ≤ (2 : ℝ) ^ (Δ : ℝ) * W_star := hboost_pot.trans_eq (by unfold W_star; ring)
            _ ≤ (1 / 4 : ℝ) * (β_star / β_cur) ^ ((3 : ℝ) / 4) * W_star := hmul
        have hstar_Wstar :
            cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ)
              (sStarLoop fuel X Y Z A B_rem ε S D α_cap capNum capDen (k + 1) recDepth) ≤
            Lambda3D (h : ℝ) * W - (1 / 4 : ℝ) * (β_star / β_cur) ^ ((3 : ℝ) / 4) * W_star := by
          have hfac0 :
              0 ≤ Lambda3D (h : ℝ) * α_cap ^ ((1 : ℝ) / 4) *
                (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ) := by
            have : 0 ≤ α_cap ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hα_pos.le _
            positivity
          have hmul := mul_le_mul_of_nonneg_left hconc1 hfac0
          calc
            cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ)
                (sStarLoop fuel X Y Z A B_rem ε S D α_cap capNum capDen (k + 1) recDepth)
              ≤ (Lambda3D (h : ℝ) * α_cap ^ ((1 : ℝ) / 4) *
                  (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ)) * β_rem ^ ((1 : ℝ) / 4) := by
                exact hih.trans_eq (by unfold β_rem; ring)
            _ ≤ (Lambda3D (h : ℝ) * α_cap ^ ((1 : ℝ) / 4) *
                  (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ)) *
                  (β_cur ^ ((1 : ℝ) / 4) -
                    (1 / 4 : ℝ) * (β_star / β_cur) ^ ((3 : ℝ) / 4) * q * β_star ^ ((1 : ℝ) / 4)) := hmul
            _ = Lambda3D (h : ℝ) * W -
                  (1 / 4 : ℝ) * (β_star / β_cur) ^ ((3 : ℝ) / 4) *
                    (Lambda3D (h : ℝ) * α_cap ^ ((1 : ℝ) / 4) *
                      (q * β_star ^ ((1 : ℝ) / 4)) *
                      (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ)) := by
                unfold W; ring
            _ = Lambda3D (h : ℝ) * W -
                  (1 / 4 : ℝ) * (β_star / β_cur) ^ ((3 : ℝ) / 4) * W_star := by
                rw [hq_Wstar]
        unfold W at hstar_Wstar
        linarith
      · -- Case B: Branch B (`normal`, `paper.tex` §5.4 Claim 5.8 `\label{clm:pot-normal}` & Table 6 (`\label{tab:potential-budget}`))
        rw [if_neg hmode, cubePotential_append, cubePotential_append]
        have hmode_norm : cubeRes.mode = CubeMode.normal := by
          rcases hmode_or with h1 | h2
          · exact False.elim (hmode h1)
          · exact h2
        rcases hnorm_spec hmode_norm with ⟨_hSB4, _hlt17, _hsum_A, hslices⟩
        have hextra := cappedGoodCube_normal_extra_spec S hX hY hZ hA hB hε0 hε_le hD hα_pos.le hB_gt
          (by rw [hcube]; exact hmode_norm)
        dsimp only at hextra
        rw [hcube] at hextra
        clear hcube
        rcases hextra with
          ⟨hmom, hrpow, hres1, _hscale_sum, _hlen_sl, hsl_extra⟩
        clear _hSB4 _hlt17 _hsum_A _hscale_sum _hlen_sl hnorm_spec hbboost_spec
        -- Term 5: Residual call `S_star` (`paper.tex` §5.4)
        have hterm5 :
            cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ)
              (sStarLoop fuel X Y Z A B_rem ε S D α_cap capNum capDen (k + 1) recDepth) ≤
            Lambda3D (h : ℝ) * W - (1 / 4 : ℝ) * W_star := by
          have hfac0 :
              0 ≤ Lambda3D (h : ℝ) * α_cap ^ ((1 : ℝ) / 4) *
                (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ) := by
            have : 0 ≤ α_cap ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hα_pos.le _
            positivity
          have hmul := mul_le_mul_of_nonneg_left (hconc2 hβ_le_star) hfac0
          calc
            cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ)
                (sStarLoop fuel X Y Z A B_rem ε S D α_cap capNum capDen (k + 1) recDepth)
              ≤ (Lambda3D (h : ℝ) * α_cap ^ ((1 : ℝ) / 4) *
                  (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ)) * β_rem ^ ((1 : ℝ) / 4) := by
                exact hih.trans_eq (by unfold β_rem; ring)
            _ ≤ (Lambda3D (h : ℝ) * α_cap ^ ((1 : ℝ) / 4) *
                  (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ)) *
                  (β_cur ^ ((1 : ℝ) / 4) - (1 / 4 : ℝ) * q * β_star ^ ((1 : ℝ) / 4)) := hmul
            _ = Lambda3D (h : ℝ) * W -
                  (1 / 4 : ℝ) *
                    (Lambda3D (h : ℝ) * α_cap ^ ((1 : ℝ) / 4) *
                      (q * β_star ^ ((1 : ℝ) / 4)) *
                      (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ)) := by
                unfold W; ring
            _ = Lambda3D (h : ℝ) * W - (1 / 4 : ℝ) * W_star := by rw [hq_Wstar]
        -- Term 1: Direct pieces `S_direct` (`paper.tex` §5.4)
        have hterm1 :
            cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ)
              ((cubeRes.slices.filter (fun sl => decide sl.Z_ell.Nonempty)).map (directSlicePiece B D)) ≤
            (14 / 256 : ℝ) * W_star := by
          let w_dir : GoodCubeSlice α β γ → ℝ := fun sl =>
            ((3 * β_star) ^ ((1 : ℝ) / 4) * (cubeRes.Z_star.card : ℝ)) *
              ((matDensity sl.X_ell sl.Y_ell sl.A_ell) ^ ((1 : ℝ) / 4) *
                (sl.X_ell.card : ℝ) * (sl.Y_ell.card : ℝ))
          have hw_dir0 : ∀ sl ∈ cubeRes.slices, 0 ≤ w_dir sl := by
            intro sl hsl
            dsimp only [w_dir]
            have hsl_bin := (hslices sl hsl).2.2.2.2.2.1
            have hA0 := matDensity_nonneg (isBinaryMatrix_nonneg hsl_bin)
            have : 0 ≤ (matDensity sl.X_ell sl.Y_ell sl.A_ell) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hA0 _
            have : 0 ≤ (3 * β_star) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
            positivity
          have h1 := cubePotential_filter_map_le_sum (1 / 4 : ℝ) (1 / 4 : ℝ)
            cubeRes.slices (fun sl => decide sl.Z_ell.Nonempty) (directSlicePiece B D) w_dir hw_dir0
            (fun sl hsl hZne => by
              have hne : sl.Z_ell.Nonempty := of_decide_eq_true hZne
              rcases hslices sl hsl with ⟨hslZ, _hslX, _hslY, _hneX, _hneY, hsl_bin, _hsl_ext, hsl_res, hsl_ab, hsl_reg⟩
              rcases hsl_extra sl hsl with ⟨_hsl_S, _hsl_nonres, hsl_res_extra⟩
              dsimp only [directSlicePiece, w_dir]
              rw [matDensity_submatZeroExt_eq]
              have hB_sl0 : 0 ≤ matDensity sl.Y_ell sl.Z_ell B :=
                matDensity_nonneg (fun y hy z hz =>
                  isBinaryMatrix_nonneg hB y (hsubY ((hslices sl hsl).2.2.1 hy)) z (hsubZ (hslZ hz)))
              have hB_sl_le : matDensity sl.Y_ell sl.Z_ell B ≤ 3 * β_star := by
                cases htag : sl.tag
                · exact (hsl_reg htag).2.2.2.2.2.2.2.2.2.2.2.1.le
                · have hemp := (hsl_ab htag).1
                  rw [hemp] at hne
                  exact False.elim (Finset.not_nonempty_empty hne)
                · rcases hsl_res_extra htag with ⟨_, hY_eq, _⟩
                  rcases (hsl_res htag).1 hne with ⟨hZ_eq, _⟩
                  rw [hY_eq, hZ_eq]
                  linarith
              have hBrpow :
                  (matDensity sl.Y_ell sl.Z_ell B) ^ ((1 : ℝ) / 4) ≤ (3 * β_star) ^ ((1 : ℝ) / 4) :=
                Real.rpow_le_rpow hB_sl0 hB_sl_le (by norm_num)
              have hZ_le : (sl.Z_ell.card : ℝ) ≤ (cubeRes.Z_star.card : ℝ) :=
                Nat.cast_le.mpr (Finset.card_le_card hslZ)
              have hA0 := matDensity_nonneg (isBinaryMatrix_nonneg hsl_bin)
              have hArpow0 : 0 ≤ (matDensity sl.X_ell sl.Y_ell sl.A_ell) ^ ((1 : ℝ) / 4) :=
                Real.rpow_nonneg hA0 _
              have hprod :
                  (matDensity sl.Y_ell sl.Z_ell B) ^ ((1 : ℝ) / 4) * (sl.Z_ell.card : ℝ) ≤
                    (3 * β_star) ^ ((1 : ℝ) / 4) * (cubeRes.Z_star.card : ℝ) :=
                mul_le_mul hBrpow hZ_le (Nat.cast_nonneg _) (Real.rpow_nonneg (by positivity) _)
              have hXY0 : 0 ≤ (matDensity sl.X_ell sl.Y_ell sl.A_ell) ^ ((1 : ℝ) / 4) *
                  (sl.X_ell.card : ℝ) * (sl.Y_ell.card : ℝ) := by positivity
              have hmul := mul_le_mul_of_nonneg_right hprod hXY0
              exact (by ring : _ = _).trans_le hmul)
          rw [list_map_const_mul_sum] at h1
          have h2 := mul_le_mul_of_nonneg_left hrpow
            (by positivity : 0 ≤ (3 * β_star) ^ ((1 : ℝ) / 4) * (cubeRes.Z_star.card : ℝ))
          have hA_Ystar0 : 0 ≤ matDensity X cubeRes.Y_star A :=
            matDensity_nonneg (fun x hx y hy => isBinaryMatrix_nonneg hA x hx y (hsubY hy))
          have hArpow_le :
              (matDensity X cubeRes.Y_star A) ^ ((1 : ℝ) / 4) ≤ (2 * α_cap) ^ ((1 : ℝ) / 4) :=
            Real.rpow_le_rpow hA_Ystar0 hA_Ystar_le (by norm_num)
          have h46 :
              4 * (3 * β_star) ^ ((1 : ℝ) / 4) * (2 * α_cap) ^ ((1 : ℝ) / 4) ≤
                7 * α_cap ^ ((1 : ℝ) / 4) * β_star ^ ((1 : ℝ) / 4) := by
            have heq6 :
                4 * (3 * β_star) ^ ((1 : ℝ) / 4) * (2 * α_cap) ^ ((1 : ℝ) / 4) =
                  (4 * (6 : ℝ) ^ ((1 : ℝ) / 4)) *
                    (α_cap ^ ((1 : ℝ) / 4) * β_star ^ ((1 : ℝ) / 4)) := by
              rw [Real.mul_rpow (by norm_num) hstar_pos.le,
                Real.mul_rpow (by norm_num) hα_pos.le]
              have h32 : (3 : ℝ) ^ ((1 : ℝ) / 4) * (2 : ℝ) ^ ((1 : ℝ) / 4) = (6 : ℝ) ^ ((1 : ℝ) / 4) := by
                rw [← Real.mul_rpow (by norm_num) (by norm_num)]
                norm_num
              calc
                4 * ((3 : ℝ) ^ ((1 : ℝ) / 4) * β_star ^ ((1 : ℝ) / 4)) *
                    ((2 : ℝ) ^ ((1 : ℝ) / 4) * α_cap ^ ((1 : ℝ) / 4))
                  = 4 * ((3 : ℝ) ^ ((1 : ℝ) / 4) * (2 : ℝ) ^ ((1 : ℝ) / 4)) *
                      (α_cap ^ ((1 : ℝ) / 4) * β_star ^ ((1 : ℝ) / 4)) := by ring
                _ = (4 * (6 : ℝ) ^ ((1 : ℝ) / 4)) *
                      (α_cap ^ ((1 : ℝ) / 4) * β_star ^ ((1 : ℝ) / 4)) := by rw [h32]
            rw [heq6]
            have hαβ0 : 0 ≤ α_cap ^ ((1 : ℝ) / 4) * β_star ^ ((1 : ℝ) / 4) :=
              mul_nonneg (Real.rpow_nonneg hα_pos.le _) (Real.rpow_nonneg hstar_pos.le _)
            exact (mul_le_mul_of_nonneg_right four_mul_six_rpow_quarter_le_seven hαβ0).trans_eq (by ring)
          have hXYZ0 : 0 ≤ (X.card : ℝ) * (cubeRes.Y_star.card : ℝ) * (cubeRes.Z_star.card : ℝ) := by
            positivity
          have h3 :
              ((3 * β_star) ^ ((1 : ℝ) / 4) * (cubeRes.Z_star.card : ℝ)) *
                (4 * (matDensity X cubeRes.Y_star A) ^ ((1 : ℝ) / 4) *
                  (X.card : ℝ) * (cubeRes.Y_star.card : ℝ)) ≤
              7 * α_cap ^ ((1 : ℝ) / 4) * β_star ^ ((1 : ℝ) / 4) *
                (X.card : ℝ) * (cubeRes.Y_star.card : ℝ) * (cubeRes.Z_star.card : ℝ) := by
            have hstepA :
                (4 * (3 * β_star) ^ ((1 : ℝ) / 4) * (matDensity X cubeRes.Y_star A) ^ ((1 : ℝ) / 4)) *
                  ((X.card : ℝ) * (cubeRes.Y_star.card : ℝ) * (cubeRes.Z_star.card : ℝ)) ≤
                (7 * α_cap ^ ((1 : ℝ) / 4) * β_star ^ ((1 : ℝ) / 4)) *
                  ((X.card : ℝ) * (cubeRes.Y_star.card : ℝ) * (cubeRes.Z_star.card : ℝ)) := by
              refine mul_le_mul_of_nonneg_right ?_ hXYZ0
              have := mul_le_mul_of_nonneg_left hArpow_le
                (by positivity : 0 ≤ 4 * (3 * β_star) ^ ((1 : ℝ) / 4))
              exact this.trans h46
            exact (by ring : _ = _).trans_le (hstepA.trans_eq (by ring))
          have h4 :
              7 * α_cap ^ ((1 : ℝ) / 4) * β_star ^ ((1 : ℝ) / 4) *
                (X.card : ℝ) * (cubeRes.Y_star.card : ℝ) * (cubeRes.Z_star.card : ℝ) ≤
              (14 / 256 : ℝ) * W_star := by
            unfold W_star
            have hαβ_XYZ0 :
                0 ≤ α_cap ^ ((1 : ℝ) / 4) * β_star ^ ((1 : ℝ) / 4) *
                  (X.card : ℝ) * (cubeRes.Y_star.card : ℝ) * (cubeRes.Z_star.card : ℝ) := by
              have : 0 ≤ α_cap ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hα_pos.le _
              have : 0 ≤ β_star ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hstar_pos.le _
              positivity
            have hΛ_step := mul_le_mul_of_nonneg_right
              (by linarith [hΛ_ge] : (7 : ℝ) ≤ (14 / 256 : ℝ) * Lambda3D (h : ℝ)) hαβ_XYZ0
            exact (by ring : _ = _).trans_le (hΛ_step.trans_eq (by ring))
          exact h1.trans (h2.trans (h3.trans h4))
        -- Terms 2, 3, 4: Bucketed recursive pieces `S_rec` (`paper.tex` §5.4)
        let w2 : GoodCubeSlice α β γ → ℝ := fun sl =>
          ((7 / 256 : ℝ) * W_star) * (if sl.tag = RectTag.residual then (1 : ℝ) else 0)
        let w3 : GoodCubeSlice α β γ → ℝ := fun sl =>
          ((7 / 2048 : ℝ) * Lambda3D (h : ℝ) * α_cap ^ (- (3 : ℝ) / 4) *
            β_star ^ ((1 : ℝ) / 4) * (cubeRes.Z_star.card : ℝ)) *
            (matDensity sl.X_ell sl.Y_ell sl.A_ell * (sl.X_ell.card : ℝ) * (sl.Y_ell.card : ℝ))
        let w4 : GoodCubeSlice α β γ → ℝ := fun sl =>
          ((7 / 2048 : ℝ) * Lambda3D (h : ℝ) * (2 * β_star) ^ ((1 : ℝ) / 4) *
            (cubeRes.Z_star.card : ℝ)) *
            ((matDensity sl.X_ell sl.Y_ell sl.A_ell) ^ ((1 : ℝ) / 4) *
              (sl.X_ell.card : ℝ) * (sl.Y_ell.card : ℝ))
        have hw2_0 : ∀ sl ∈ cubeRes.slices, 0 ≤ w2 sl := by
          intro sl _; dsimp only [w2]; split_ifs <;> positivity
        have hw3_0 : ∀ sl ∈ cubeRes.slices, 0 ≤ w3 sl := by
          intro sl hsl
          dsimp only [w3]
          have hsl_bin := (hslices sl hsl).2.2.2.2.2.1
          have hA0 := matDensity_nonneg (isBinaryMatrix_nonneg hsl_bin)
          have : 0 ≤ α_cap ^ (- (3 : ℝ) / 4) := Real.rpow_nonneg hα_pos.le _
          have : 0 ≤ β_star ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hstar_pos.le _
          positivity
        have hw4_0 : ∀ sl ∈ cubeRes.slices, 0 ≤ w4 sl := by
          intro sl hsl
          dsimp only [w4]
          have hsl_bin := (hslices sl hsl).2.2.2.2.2.1
          have hA0 := matDensity_nonneg (isBinaryMatrix_nonneg hsl_bin)
          have : 0 ≤ (matDensity sl.X_ell sl.Y_ell sl.A_ell) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hA0 _
          have : 0 ≤ (2 * β_star) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
          positivity
        have hrec_slices_le :
            cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ)
              ((cubeRes.slices.filter (fun sl => decide (cubeRes.Z_star \ sl.Z_ell).Nonempty)).flatMap
                (fun sl =>
                  let Z_rem := cubeRes.Z_star \ sl.Z_ell
                  let α_ell := matDensity sl.X_ell sl.Y_ell sl.A_ell
                  let p_ell := supportCountRealNat sl.X_ell sl.Y_ell sl.A_ell
                  let q_ell := sl.X_ell.card * sl.Y_ell.card
                  let Δ := min (k + 1) (rawDeltaHANat p_ell q_ell capNum capDen)
                  bucketedRec sl.X_ell sl.Y_ell Z_rem sl.A_ell
                    (submatZeroExt sl.Y_ell Z_rem B) α_ell D
                    (fun X' Y'_j Z' A' B' α' j =>
                      recDepth Δ X' Y'_j Z' A' B' α' (2 ^ j * p_ell) q_ell))) ≤
            (cubeRes.slices.map (fun sl => w2 sl + w3 sl + w4 sl)).sum := by
          refine cubePotential_filter_flatMap_le_sum (1 / 4 : ℝ) (1 / 4 : ℝ)
            cubeRes.slices (fun sl => decide (cubeRes.Z_star \ sl.Z_ell).Nonempty) _
            (fun sl => w2 sl + w3 sl + w4 sl)
            (fun sl hsl => add_nonneg (add_nonneg (hw2_0 sl hsl) (hw3_0 sl hsl)) (hw4_0 sl hsl))
            (fun sl hsl hZrem => ?_)
          have hZrem_ne : (cubeRes.Z_star \ sl.Z_ell).Nonempty := of_decide_eq_true hZrem
          rcases hslices sl hsl with ⟨_hslZ, _hslX, hslY, _hneX, _hneY, hsl_bin, _hsl_ext, hsl_res, hsl_ab, hsl_reg⟩
          rcases hsl_extra sl hsl with ⟨_hsl_S, hsl_nonres, hsl_res_extra⟩
          have hα_gt : (2 : ℝ) ^ (-(D : ℤ)) < matDensity sl.X_ell sl.Y_ell sl.A_ell := by
            by_cases htag : sl.tag = RectTag.residual
            · rcases hsl_res_extra htag with ⟨_, _, _, hZ_if⟩
              by_contra hle; push_neg at hle
              rw [if_pos hle] at hZ_if
              rw [hZ_if, Finset.sdiff_self] at hZrem_ne
              exact Finset.not_nonempty_empty hZrem_ne
            · exact hsl_nonres htag
          set Z_rem := cubeRes.Z_star \ sl.Z_ell
          set α_ell := matDensity sl.X_ell sl.Y_ell sl.A_ell
          have hα_ell_pos : 0 < α_ell := lt_trans (by positivity) hα_gt
          dsimp only
          have hraw_A_eq :
              rawDeltaHANat (supportCountRealNat sl.X_ell sl.Y_ell sl.A_ell)
                (sl.X_ell.card * sl.Y_ell.card) capNum capDen =
              rawDeltaHA α_ell α_cap :=
            rawDeltaHANat_supportCount_eq hsl_bin hcap
          rw [hraw_A_eq]
          set Δ := min (k + 1) (rawDeltaHA α_ell α_cap)
          have hΔ1 : 1 ≤ Δ := le_min (by omega) (one_le_rawDeltaHA _ _)
          have hΔ_le : Δ ≤ k + 1 := min_le_left _ _
          have hΛ_child_eq :
              Lambda3D ((H - (k + 1 - Δ) : ℕ) : ℝ) = (2 : ℝ) ^ (Δ : ℝ) * Lambda3D (h : ℝ) :=
            Lambda3D_sub_sub_eq hkH hΔ_le
          have hA_nonneg_sl : ∀ x ∈ sl.X_ell, ∀ y ∈ sl.Y_ell, 0 ≤ sl.A_ell x y :=
            isBinaryMatrix_nonneg hsl_bin
          have hB_rem_bin_sl :
              IsBinaryMatrix sl.Y_ell Z_rem (submatZeroExt sl.Y_ell Z_rem B) :=
            isBinaryMatrix_submatZeroExt (hslY.trans hsubY) (Finset.sdiff_subset.trans hsubZ) hB
          have hB_nonneg_sl : ∀ y ∈ sl.Y_ell, ∀ z ∈ Z_rem, 0 ≤ submatZeroExt sl.Y_ell Z_rem B y z :=
            isBinaryMatrix_nonneg hB_rem_bin_sl
          have hbuck_pot := bucketedRec_potential_bound sl.X_ell sl.Y_ell Z_rem
            sl.A_ell (submatZeroExt sl.Y_ell Z_rem B)
            (Λ := (2 : ℝ) ^ (Δ : ℝ) * Lambda3D (h : ℝ)) D
            hα_ell_pos (by positivity) hA_nonneg_sl hB_nonneg_sl le_rfl
            (fun X' Y'_j Z' A' B' α' j =>
              recDepth Δ X' Y'_j Z' A' B' α'
                (2 ^ j * supportCountRealNat sl.X_ell sl.Y_ell sl.A_ell)
                (sl.X_ell.card * sl.Y_ell.card))
            (fun j _ _ => by
              set Y'_j := dyadicColBucket sl.X_ell sl.Y_ell sl.A_ell α_ell j
              have hY'j_sub : Y'_j ⊆ sl.Y_ell := dyadicColBucket_subset _ _ _ _ _
              have hAj : IsBinaryMatrix sl.X_ell Y'_j (submatZeroExt sl.X_ell Y'_j sl.A_ell) :=
                isBinaryMatrix_submatZeroExt Finset.Subset.rfl hY'j_sub hsl_bin
              have hBj :
                  IsBinaryMatrix Y'_j Z_rem
                    (submatZeroExt Y'_j Z_rem (submatZeroExt sl.Y_ell Z_rem B)) :=
                isBinaryMatrix_submatZeroExt hY'j_sub Finset.Subset.rfl hB_rem_bin_sl
              have hαj_pos : 0 < dyadicColAlpha α_ell j := by unfold dyadicColAlpha; positivity
              have hcap_j :
                  dyadicColAlpha α_ell j =
                    ((2 ^ j * supportCountRealNat sl.X_ell sl.Y_ell sl.A_ell : ℕ) : ℝ) /
                      ((sl.X_ell.card * sl.Y_ell.card : ℕ) : ℝ) :=
                dyadicColAlpha_eq_mul_supportCount_div hsl_bin j
              have hcol_j : ∀ y ∈ Y'_j,
                  colDeg sl.X_ell (submatZeroExt sl.X_ell Y'_j sl.A_ell) y ≤
                    2 * dyadicColAlpha α_ell j := by
                intro y hy
                rw [colDeg_submatZeroExt_eq' sl.X_ell sl.A_ell hy]
                exact (eq_col_bucketing sl.X_ell sl.Y_ell sl.A_ell α_ell j hy).1
              have hpot_j := hrec_pot Δ sl.X_ell Y'_j Z_rem _ _ _ _ _
                hΔ1 hΔ_le hAj hBj hαj_pos hcap_j hcol_j
              rwa [matDensity_submatZeroExt_eq, hΛ_child_eq] at hpot_j)
          rw [matDensity_submatZeroExt_eq] at hbuck_pot
          have hw2_sl0 := hw2_0 sl hsl
          have hw3_sl0 := hw3_0 sl hsl
          have hw4_sl0 := hw4_0 sl hsl
          have hB_Zrem0 : 0 ≤ matDensity sl.Y_ell Z_rem B :=
            matDensity_nonneg (fun y hy z hz =>
              isBinaryMatrix_nonneg hB y (hsubY (hslY hy)) z (hsubZ (Finset.sdiff_subset hz)))
          cases htag : sl.tag
          · -- `regular` slice → bounded by `w4 sl` (`paper.tex` §5.4)
            rcases hsl_reg htag with ⟨_, _, _, hα_lt_cap, _, _, _, _, _, _, _, _, hZrem_lt, hB_Zrem_lt⟩
            have hraw1 : rawDeltaHA α_ell α_cap = 1 :=
              rawDeltaHA_eq_one_of_lt hα_ell_pos.le hα_pos hα_lt_cap
            have hΔ_eq1 : Δ = 1 := by unfold Δ; rw [hraw1]; omega
            have h2Δ : (2 : ℝ) ^ (Δ : ℝ) = 2 := by rw [hΔ_eq1]; norm_num
            have hBrpow :
                (matDensity sl.Y_ell Z_rem B) ^ ((1 : ℝ) / 4) ≤ (2 * β_star) ^ ((1 : ℝ) / 4) :=
              Real.rpow_le_rpow hB_Zrem0 (hB_Zrem_lt hZrem_ne).le (by norm_num)
            have hZrem_le : (Z_rem.card : ℝ) ≤ (1 / 2048 : ℝ) * (cubeRes.Z_star.card : ℝ) := by
              unfold gamma3D at hZrem_lt
              linarith
            have hprod :
                (matDensity sl.Y_ell Z_rem B) ^ ((1 : ℝ) / 4) * (Z_rem.card : ℝ) ≤
                  (2 * β_star) ^ ((1 : ℝ) / 4) * ((1 / 2048 : ℝ) * (cubeRes.Z_star.card : ℝ)) :=
              mul_le_mul hBrpow hZrem_le (Nat.cast_nonneg _) (Real.rpow_nonneg (by positivity) _)
            have hfac_pos :
                0 ≤ (7 / 2 : ℝ) * (2 * Lambda3D (h : ℝ)) * α_ell ^ ((1 : ℝ) / 4) *
                  (sl.X_ell.card : ℝ) * (sl.Y_ell.card : ℝ) := by
              have : 0 ≤ α_ell ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hα_ell_pos.le _
              positivity
            have hmul := mul_le_mul_of_nonneg_left hprod hfac_pos
            have hle_w4 :
                cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ)
                  (bucketedRec sl.X_ell sl.Y_ell Z_rem sl.A_ell
                    (submatZeroExt sl.Y_ell Z_rem B) α_ell D
                    (fun X' Y'_j Z' A' B' α' j =>
                      recDepth Δ X' Y'_j Z' A' B' α'
                        (2 ^ j * supportCountRealNat sl.X_ell sl.Y_ell sl.A_ell)
                        (sl.X_ell.card * sl.Y_ell.card))) ≤ w4 sl := by
              dsimp only [w4]
              rw [h2Δ] at hbuck_pot
              exact hbuck_pot.trans ((by ring : _ = _).trans_le (hmul.trans_eq (by ring)))
            exact hle_w4.trans (le_add_of_nonneg_left (add_nonneg hw2_sl0 hw3_sl0))
          · -- `aBoosted` slice → bounded by `w3 sl` (`paper.tex` §5.4)
            rcases hsl_ab htag with ⟨hZ_emp, hB_lt2, hcap_le_α, _⟩
            have hZrem_eq : Z_rem = cubeRes.Z_star := by unfold Z_rem; rw [hZ_emp, Finset.sdiff_empty]
            have hpow_A := two_pow_min_rawDeltaHA_mul_rpow_le (k + 1) hα_pos hcap_le_α
            have h2_neg11 : (2 : ℝ) ^ (- (11 : ℝ)) = (1 / 2048 : ℝ) := by norm_num
            rw [h2_neg11] at hpow_A
            have hBrpow :
                (matDensity sl.Y_ell Z_rem B) ^ ((1 : ℝ) / 4) ≤ 2 * β_star ^ ((1 : ℝ) / 4) := by
              rw [hZrem_eq]
              calc
                (matDensity sl.Y_ell cubeRes.Z_star B) ^ ((1 : ℝ) / 4)
                  ≤ (2 * β_star) ^ ((1 : ℝ) / 4) :=
                    Real.rpow_le_rpow (by rw [← hZrem_eq]; exact hB_Zrem0) hB_lt2.le (by norm_num)
                _ = (2 : ℝ) ^ ((1 : ℝ) / 4) * β_star ^ ((1 : ℝ) / 4) :=
                    Real.mul_rpow (by norm_num) hstar_pos.le
                _ ≤ 2 * β_star ^ ((1 : ℝ) / 4) :=
                    mul_le_mul_of_nonneg_right two_rpow_quarter_le_two
                      (Real.rpow_nonneg hstar_pos.le _)
            have hprod :
                ((2 : ℝ) ^ (Δ : ℝ) * α_ell ^ ((1 : ℝ) / 4)) *
                  (matDensity sl.Y_ell Z_rem B) ^ ((1 : ℝ) / 4) ≤
                ((1 / 2048 : ℝ) * α_cap ^ (- (3 : ℝ) / 4) * α_ell) *
                  (2 * β_star ^ ((1 : ℝ) / 4)) := by
              refine mul_le_mul hpow_A hBrpow (Real.rpow_nonneg hB_Zrem0 _) ?_
              have : 0 ≤ α_cap ^ (- (3 : ℝ) / 4) := Real.rpow_nonneg hα_pos.le _
              positivity
            have hfac_pos :
                0 ≤ (7 / 2 : ℝ) * Lambda3D (h : ℝ) *
                  (sl.X_ell.card : ℝ) * (sl.Y_ell.card : ℝ) * (Z_rem.card : ℝ) := by positivity
            have hmul := mul_le_mul_of_nonneg_left hprod hfac_pos
            have hle_w3 :
                cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ)
                  (bucketedRec sl.X_ell sl.Y_ell Z_rem sl.A_ell
                    (submatZeroExt sl.Y_ell Z_rem B) α_ell D
                    (fun X' Y'_j Z' A' B' α' j =>
                      recDepth Δ X' Y'_j Z' A' B' α'
                        (2 ^ j * supportCountRealNat sl.X_ell sl.Y_ell sl.A_ell)
                        (sl.X_ell.card * sl.Y_ell.card))) ≤ w3 sl := by
              dsimp only [w3]
              rw [hZrem_eq] at hbuck_pot hmul ⊢
              calc
                cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ)
                    (bucketedRec sl.X_ell sl.Y_ell cubeRes.Z_star sl.A_ell
                      (submatZeroExt sl.Y_ell cubeRes.Z_star B) α_ell D
                      (fun X' Y'_j Z' A' B' α' j =>
                        recDepth Δ X' Y'_j Z' A' B' α'
                          (2 ^ j * supportCountRealNat sl.X_ell sl.Y_ell sl.A_ell)
                          (sl.X_ell.card * sl.Y_ell.card)))
                  ≤ (7 / 2 : ℝ) * ((2 : ℝ) ^ (Δ : ℝ) * Lambda3D (h : ℝ)) * α_ell ^ ((1 : ℝ) / 4) *
                      (matDensity sl.Y_ell cubeRes.Z_star B) ^ ((1 : ℝ) / 4) *
                      (sl.X_ell.card : ℝ) * (sl.Y_ell.card : ℝ) * (cubeRes.Z_star.card : ℝ) := hbuck_pot
                _ = (7 / 2 : ℝ) * Lambda3D (h : ℝ) *
                      (sl.X_ell.card : ℝ) * (sl.Y_ell.card : ℝ) * (cubeRes.Z_star.card : ℝ) *
                      (((2 : ℝ) ^ (Δ : ℝ) * α_ell ^ ((1 : ℝ) / 4)) *
                        (matDensity sl.Y_ell cubeRes.Z_star B) ^ ((1 : ℝ) / 4)) := by ring
                _ ≤ (7 / 2 : ℝ) * Lambda3D (h : ℝ) *
                      (sl.X_ell.card : ℝ) * (sl.Y_ell.card : ℝ) * (cubeRes.Z_star.card : ℝ) *
                      (((1 / 2048 : ℝ) * α_cap ^ (- (3 : ℝ) / 4) * α_ell) *
                        (2 * β_star ^ ((1 : ℝ) / 4))) := hmul
                _ = ((7 / 2048 : ℝ) * Lambda3D (h : ℝ) * α_cap ^ (- (3 : ℝ) / 4) *
                      β_star ^ ((1 : ℝ) / 4) * (cubeRes.Z_star.card : ℝ)) *
                      (matDensity sl.X_ell sl.Y_ell sl.A_ell *
                        (sl.X_ell.card : ℝ) * (sl.Y_ell.card : ℝ)) := by
                    unfold α_ell; ring
            exact hle_w3.trans (le_add_of_le_of_nonneg (le_add_of_nonneg_left hw2_sl0) hw4_sl0)
          · -- `residual` slice → bounded by `w2 sl` (`paper.tex` §5.4)
            rcases hsl_res_extra htag with ⟨hX_eq, hY_eq, hα_max, hZ_if⟩
            have hZ_emp : sl.Z_ell = ∅ := (hsl_res htag).2.1 hα_gt
            have hZrem_eq : Z_rem = cubeRes.Z_star := by unfold Z_rem; rw [hZ_emp, Finset.sdiff_empty]
            have hα_le_low : α_ell ≤ cLow3D * α_cap := by
              rcases le_max_iff.mp hα_max with h1 | h2
              · linarith [hα_gt]
              · exact h2
            have hα_lt_cap : α_ell < cCap3D * α_cap := by
              have : cLow3D * α_cap < cCap3D * α_cap :=
                mul_lt_mul_of_pos_right (by unfold cLow3D cCap3D; norm_num) hα_pos
              linarith
            have hraw1 : rawDeltaHA α_ell α_cap = 1 :=
              rawDeltaHA_eq_one_of_lt hα_ell_pos.le hα_pos hα_lt_cap
            have hΔ_eq1 : Δ = 1 := by unfold Δ; rw [hraw1]; omega
            have h2Δ : (2 : ℝ) ^ (Δ : ℝ) = 2 := by rw [hΔ_eq1]; norm_num
            have hα_rpow_le : α_ell ^ ((1 : ℝ) / 4) ≤ (1 / 256 : ℝ) * α_cap ^ ((1 : ℝ) / 4) := by
              rw [← cLow3D_mul_rpow_quarter hα_pos.le]
              exact Real.rpow_le_rpow hα_ell_pos.le hα_le_low (by norm_num)
            have hB_eq_star : matDensity sl.Y_ell Z_rem B = β_star := by
              rw [hY_eq, hZrem_eq]
            have hfac_pos :
                0 ≤ (7 / 2 : ℝ) * (2 * Lambda3D (h : ℝ)) * β_star ^ ((1 : ℝ) / 4) *
                  (X.card : ℝ) * (cubeRes.Y_star.card : ℝ) * (cubeRes.Z_star.card : ℝ) :=
              mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
                (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hΛ_pos.le))
                (Real.rpow_nonneg hstar_pos.le _))
                (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
            have hmul := mul_le_mul_of_nonneg_left hα_rpow_le hfac_pos
            have hle_w2 :
                cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ)
                  (bucketedRec sl.X_ell sl.Y_ell Z_rem sl.A_ell
                    (submatZeroExt sl.Y_ell Z_rem B) α_ell D
                    (fun X' Y'_j Z' A' B' α' j =>
                      recDepth Δ X' Y'_j Z' A' B' α'
                        (2 ^ j * supportCountRealNat sl.X_ell sl.Y_ell sl.A_ell)
                        (sl.X_ell.card * sl.Y_ell.card))) ≤ w2 sl := by
              dsimp only [w2]
              rw [htag, if_pos rfl]
              rw [h2Δ, hB_eq_star] at hbuck_pot
              rw [hX_eq, hY_eq, hZrem_eq] at hbuck_pot ⊢
              unfold W_star
              calc
                cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ)
                    (bucketedRec X cubeRes.Y_star cubeRes.Z_star sl.A_ell
                      (submatZeroExt cubeRes.Y_star cubeRes.Z_star B) α_ell D
                      (fun X' Y'_j Z' A' B' α' j =>
                        recDepth Δ X' Y'_j Z' A' B' α'
                          (2 ^ j * supportCountRealNat X cubeRes.Y_star sl.A_ell)
                          (X.card * cubeRes.Y_star.card)))
                  ≤ (7 / 2 : ℝ) * (2 * Lambda3D (h : ℝ)) * α_ell ^ ((1 : ℝ) / 4) *
                      β_star ^ ((1 : ℝ) / 4) *
                      (X.card : ℝ) * (cubeRes.Y_star.card : ℝ) * (cubeRes.Z_star.card : ℝ) := hbuck_pot
                _ = (7 / 2 : ℝ) * (2 * Lambda3D (h : ℝ)) * β_star ^ ((1 : ℝ) / 4) *
                      (X.card : ℝ) * (cubeRes.Y_star.card : ℝ) * (cubeRes.Z_star.card : ℝ) *
                      α_ell ^ ((1 : ℝ) / 4) := by ring
                _ ≤ (7 / 2 : ℝ) * (2 * Lambda3D (h : ℝ)) * β_star ^ ((1 : ℝ) / 4) *
                      (X.card : ℝ) * (cubeRes.Y_star.card : ℝ) * (cubeRes.Z_star.card : ℝ) *
                      ((1 / 256 : ℝ) * α_cap ^ ((1 : ℝ) / 4)) := hmul
                _ = (7 / 256 : ℝ) *
                      (Lambda3D (h : ℝ) * α_cap ^ ((1 : ℝ) / 4) * β_star ^ ((1 : ℝ) / 4) *
                        (X.card : ℝ) * (cubeRes.Y_star.card : ℝ) * (cubeRes.Z_star.card : ℝ)) * 1 := by
                    ring
            exact hle_w2.trans (le_add_of_le_of_nonneg (le_add_of_nonneg_right hw3_sl0) hw4_sl0)
        have hsum_w2 : (cubeRes.slices.map w2).sum = (7 / 256 : ℝ) * W_star := by
          dsimp only [w2]
          rw [list_map_const_mul_sum, hres1, mul_one]
        have hsum_w3 : (cubeRes.slices.map w3).sum ≤ (2 / 256 : ℝ) * W_star := by
          dsimp only [w3]
          rw [list_map_const_mul_sum, hmom]
          have hfac0 :
              0 ≤ (7 / 2048 : ℝ) * Lambda3D (h : ℝ) * α_cap ^ (- (3 : ℝ) / 4) *
                β_star ^ ((1 : ℝ) / 4) * (cubeRes.Z_star.card : ℝ) *
                ((X.card : ℝ) * (cubeRes.Y_star.card : ℝ)) := by
            have : 0 ≤ α_cap ^ (- (3 : ℝ) / 4) := Real.rpow_nonneg hα_pos.le _
            have : 0 ≤ β_star ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hstar_pos.le _
            positivity
          have hmul := mul_le_mul_of_nonneg_left hA_Ystar_le hfac0
          have hα_comb : α_cap ^ (- (3 : ℝ) / 4) * α_cap = α_cap ^ ((1 : ℝ) / 4) := by
            rw [← Real.rpow_add_one hα_pos.ne' (- (3 : ℝ) / 4)]
            congr 1
            ring
          have hrhs_eq :
              ((7 / 2048 : ℝ) * Lambda3D (h : ℝ) * α_cap ^ (- (3 : ℝ) / 4) *
                β_star ^ ((1 : ℝ) / 4) * (cubeRes.Z_star.card : ℝ) *
                ((X.card : ℝ) * (cubeRes.Y_star.card : ℝ))) * (2 * α_cap) =
              (14 / 2048 : ℝ) * W_star := by
            unfold W_star
            calc
              ((7 / 2048 : ℝ) * Lambda3D (h : ℝ) * α_cap ^ (- (3 : ℝ) / 4) *
                  β_star ^ ((1 : ℝ) / 4) * (cubeRes.Z_star.card : ℝ) *
                  ((X.card : ℝ) * (cubeRes.Y_star.card : ℝ))) * (2 * α_cap)
                = (14 / 2048 : ℝ) * Lambda3D (h : ℝ) * (α_cap ^ (- (3 : ℝ) / 4) * α_cap) *
                    β_star ^ ((1 : ℝ) / 4) * (X.card : ℝ) *
                    (cubeRes.Y_star.card : ℝ) * (cubeRes.Z_star.card : ℝ) := by ring
              _ = (14 / 2048 : ℝ) * (Lambda3D (h : ℝ) * α_cap ^ ((1 : ℝ) / 4) *
                    β_star ^ ((1 : ℝ) / 4) * (X.card : ℝ) *
                    (cubeRes.Y_star.card : ℝ) * (cubeRes.Z_star.card : ℝ)) := by
                  rw [hα_comb]; ring
          exact ((by ring : _ = _).trans_le (hmul.trans_eq hrhs_eq)).trans
            (by linarith [hW_star_nonneg])
        have hsum_w4 : (cubeRes.slices.map w4).sum ≤ (5 / 256 : ℝ) * W_star := by
          dsimp only [w4]
          rw [list_map_const_mul_sum]
          have h1 := mul_le_mul_of_nonneg_left hrpow
            (by positivity : 0 ≤ (7 / 2048 : ℝ) * Lambda3D (h : ℝ) *
              (2 * β_star) ^ ((1 : ℝ) / 4) * (cubeRes.Z_star.card : ℝ))
          have hA_Ystar0 : 0 ≤ matDensity X cubeRes.Y_star A :=
            matDensity_nonneg (fun x hx y hy => isBinaryMatrix_nonneg hA x hx y (hsubY hy))
          have hArpow_le :
              (matDensity X cubeRes.Y_star A) ^ ((1 : ℝ) / 4) ≤ (2 * α_cap) ^ ((1 : ℝ) / 4) :=
            Real.rpow_le_rpow hA_Ystar0 hA_Ystar_le (by norm_num)
          have h28_40 :
              28 * (2 * β_star) ^ ((1 : ℝ) / 4) * (2 * α_cap) ^ ((1 : ℝ) / 4) ≤
                40 * α_cap ^ ((1 : ℝ) / 4) * β_star ^ ((1 : ℝ) / 4) := by
            have heq2 :
                28 * (2 * β_star) ^ ((1 : ℝ) / 4) * (2 * α_cap) ^ ((1 : ℝ) / 4) =
                  (28 * (2 : ℝ) ^ ((1 : ℝ) / 2)) *
                    (α_cap ^ ((1 : ℝ) / 4) * β_star ^ ((1 : ℝ) / 4)) := by
              rw [Real.mul_rpow (by norm_num) hstar_pos.le,
                Real.mul_rpow (by norm_num) hα_pos.le]
              have h22 : (2 : ℝ) ^ ((1 : ℝ) / 4) * (2 : ℝ) ^ ((1 : ℝ) / 4) = (2 : ℝ) ^ ((1 : ℝ) / 2) := by
                rw [← Real.rpow_add (by norm_num)]
                norm_num
              calc
                28 * ((2 : ℝ) ^ ((1 : ℝ) / 4) * β_star ^ ((1 : ℝ) / 4)) *
                    ((2 : ℝ) ^ ((1 : ℝ) / 4) * α_cap ^ ((1 : ℝ) / 4))
                  = 28 * ((2 : ℝ) ^ ((1 : ℝ) / 4) * (2 : ℝ) ^ ((1 : ℝ) / 4)) *
                      (α_cap ^ ((1 : ℝ) / 4) * β_star ^ ((1 : ℝ) / 4)) := by ring
                _ = (28 * (2 : ℝ) ^ ((1 : ℝ) / 2)) *
                      (α_cap ^ ((1 : ℝ) / 4) * β_star ^ ((1 : ℝ) / 4)) := by rw [h22]
            rw [heq2]
            have hαβ0 : 0 ≤ α_cap ^ ((1 : ℝ) / 4) * β_star ^ ((1 : ℝ) / 4) :=
              mul_nonneg (Real.rpow_nonneg hα_pos.le _) (Real.rpow_nonneg hstar_pos.le _)
            exact (mul_le_mul_of_nonneg_right twentyeight_mul_two_rpow_half_le_forty hαβ0).trans_eq (by ring)
          have h2 :
              ((7 / 2048 : ℝ) * Lambda3D (h : ℝ) * (2 * β_star) ^ ((1 : ℝ) / 4) *
                (cubeRes.Z_star.card : ℝ)) *
                (4 * (matDensity X cubeRes.Y_star A) ^ ((1 : ℝ) / 4) *
                  (X.card : ℝ) * (cubeRes.Y_star.card : ℝ)) ≤
              (5 / 256 : ℝ) * W_star := by
            unfold W_star
            have hfac_XYZ0 :
                0 ≤ (1 / 2048 : ℝ) * Lambda3D (h : ℝ) *
                  (X.card : ℝ) * (cubeRes.Y_star.card : ℝ) * (cubeRes.Z_star.card : ℝ) := by
              positivity
            have hstepA := mul_le_mul_of_nonneg_left hArpow_le
              (by positivity : 0 ≤ 28 * (2 * β_star) ^ ((1 : ℝ) / 4))
            have hstepB := mul_le_mul_of_nonneg_right (hstepA.trans h28_40) hfac_XYZ0
            exact (by ring : _ = _).trans_le (hstepB.trans_eq (by ring))
          exact h1.trans h2
        have hrec_tot :
            cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ)
              ((cubeRes.slices.filter (fun sl => decide (cubeRes.Z_star \ sl.Z_ell).Nonempty)).flatMap
                (fun sl =>
                  let Z_rem := cubeRes.Z_star \ sl.Z_ell
                  let α_ell := matDensity sl.X_ell sl.Y_ell sl.A_ell
                  let p_ell := supportCountRealNat sl.X_ell sl.Y_ell sl.A_ell
                  let q_ell := sl.X_ell.card * sl.Y_ell.card
                  let Δ := min (k + 1) (rawDeltaHANat p_ell q_ell capNum capDen)
                  bucketedRec sl.X_ell sl.Y_ell Z_rem sl.A_ell
                    (submatZeroExt sl.Y_ell Z_rem B) α_ell D
                    (fun X' Y'_j Z' A' B' α' j =>
                      recDepth Δ X' Y'_j Z' A' B' α' (2 ^ j * p_ell) q_ell))) ≤
            (7 / 256 : ℝ) * W_star + (2 / 256 : ℝ) * W_star + (5 / 256 : ℝ) * W_star := by
          rw [list_map_add_sum, list_map_add_sum] at hrec_slices_le
          linarith
        have hcinco := table1_budget_cinco_sum_le (Λ_h_W := Lambda3D (h : ℝ) * W) hW_star_nonneg
        unfold W at hcinco hterm5
        linarith

/-- **Inductive Potential Bound for `cappedABDecompAux` (`cappedABDecompAux_potential_le`,
`paper.tex` Lemma 5.5 `\label{lem:potential}`, Eq. `\eqref{eq:inductive-potential}`, §5.4)**. -/
theorem cappedABDecompAux_potential_le [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (remDepth : ℕ) (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    {ε : ℝ} (S : TwoStageSamplerOracle β ε) {D H : ℕ} (α_cap : ℝ) (capNum capDen : ℕ)
    (hA : IsBinaryMatrix X Y A) (hB : IsBinaryMatrix Y Z B)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hD : 2 ≤ D) (hα_pos : 0 < α_cap)
    (hcap : α_cap = (capNum : ℝ) / (capDen : ℝ))
    (hcol_le : ∀ y ∈ Y, colDeg X A y ≤ 2 * α_cap)
    (hremH : remDepth ≤ H) (hDH : 3 * D ≤ 4 * H) :
    cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ)
      (cappedABDecompAux remDepth X Y Z A B ε S D α_cap capNum capDen) ≤
      Lambda3D ((H - remDepth : ℕ) : ℝ) * α_cap ^ ((1 : ℝ) / 4) *
        (matDensity Y Z B) ^ ((1 : ℝ) / 4) *
        (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ) := by
  induction' remDepth using Nat.strong_induction_on with remDepth ih
    generalizing X Y Z A B α_cap capNum capDen
  rcases remDepth with _ | k
  · rw [cappedABDecompAux, Nat.sub_zero]
    split_ifs with hbase
    · exact cubePotential_baseCase1Piece_le X Y Z A B ε D H hA hB hα_pos.le hcol_le
    · exact baseCase2Decomposition_potential_le X Y Z A B
        (isBinaryMatrix_nonneg hA) hB
        hα_pos.le (matDensity_le_of_colDeg_le' (by linarith) hcol_le) hDH
  · rw [cappedABDecompAux]
    exact sStarLoop_potential_le (rSStarFuel ε D) X Y Z A B S α_cap capNum capDen
      hA hB hε0 hε_le hD hα_pos hcap hcol_le hremH
      (rSStarFuel_ge_of_isBinaryMatrix hB hε0 hε_le)
      (fun Δ X' Y' Z' A' B' α' capNum' capDen' =>
        cappedABDecompAux (k - (Δ - 1)) X' Y' Z' A' B' ε S D α' capNum' capDen')
      (fun Δ X' Y' Z' A' B' α' capNum' capDen' hΔ1 hΔ_le hA' hB' hα' hcap' hcol' => by
        have heq : k - (Δ - 1) = k + 1 - Δ := by omega
        rw [← heq]
        exact ih (k - (Δ - 1)) (by omega) X' Y' Z' A' B' α' capNum' capDen'
          hA' hB' hα' hcap' hcol' (by omega))

/-- **Inductive Potential Bound for `cappedABDecomposition'` (`cappedABDecomposition'_potential_le`,
`paper.tex` Lemma 5.5 `\label{lem:potential}`, Eq. `\eqref{eq:inductive-potential}`, §5.4)**. -/
theorem cappedABDecomposition'_potential_le [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    {ε : ℝ} (S : TwoStageSamplerOracle β ε) {D h H : ℕ} (α_cap : ℝ) (capNum capDen : ℕ)
    (hA : IsBinaryMatrix X Y A) (hB : IsBinaryMatrix Y Z B)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hD : 2 ≤ D) (hα_pos : 0 < α_cap)
    (hcap : α_cap = (capNum : ℝ) / (capDen : ℝ))
    (hcol_le : ∀ y ∈ Y, colDeg X A y ≤ 2 * α_cap)
    (hhH : h ≤ H) (hDH : 3 * D ≤ 4 * H) :
    cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ)
      (cappedABDecomposition' X Y Z A B ε S D α_cap capNum capDen h H) ≤
      Lambda3D (h : ℝ) * α_cap ^ ((1 : ℝ) / 4) *
        (matDensity Y Z B) ^ ((1 : ℝ) / 4) *
        (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ) := by
  unfold cappedABDecomposition'
  have h1 := cappedABDecompAux_potential_le (H - h) X Y Z A B S α_cap capNum capDen
    hA hB hε0 hε_le hD hα_pos hcap hcol_le (Nat.sub_le H h) hDH
  have heq : H - (H - h) = h := Nat.sub_sub_self hhH
  rwa [heq] at h1

/-- **Root Potential Bound for `cappedABDecomposition` (`cappedABDecomposition_potential_le`,
`paper.tex` Theorem 1.1 Clause 3 `\eqref{eq:main-potential}`, §1.2, §5.4 & §5.6)**:
At the root $(h = 0, \alpha_{\text{cap}} = 1, H = \text{H3D } D)$,
$$C_{1/4, 1/4}(\text{cappedABDecomposition } X \, Y \, Z \, A \, B \, \varepsilon \, S \, D)
  \le 128 (\mathbb{E}_{Y \times Z}[B])^{1/4} |X||Y||Z| \le 128 |X||Y||Z|.$$ -/
theorem cappedABDecomposition_potential_le [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    {ε : ℝ} (S : TwoStageSamplerOracle β ε) {D : ℕ}
    (hA : IsBinaryMatrix X Y A) (hB : IsBinaryMatrix Y Z B)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hD : 2 ≤ D) :
    let pieces := cappedABDecomposition X Y Z A B ε S D
    cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ) pieces ≤
      128 * (matDensity Y Z B) ^ ((1 : ℝ) / 4) * (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ) ∧
    cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ) pieces ≤
      128 * (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ) := by
  dsimp only
  have hcol1 : ∀ y ∈ Y, colDeg X A y ≤ 2 * (1 : ℝ) := by
    intro y hy
    rcases X.eq_empty_or_nonempty with rfl | hX
    · simp [colDeg, expectSet]
    · have hle1 : colDeg X A y ≤ 1 :=
        expectSet_le_of_le hX (fun x hx => isBinaryMatrix_le_one hA x hx y hy)
      linarith
  have hDH : 3 * D ≤ 4 * H3D D := by unfold H3D; omega
  have h1 := cappedABDecomposition'_potential_le X Y Z A B S (1 : ℝ) 1 1
    hA hB hε0 hε_le hD (by norm_num) (by norm_num) hcol1 (Nat.zero_le _) hDH
  simp only [Nat.cast_zero, Lambda3D_zero, Real.one_rpow, mul_one] at h1
  refine ⟨h1, h1.trans ?_⟩
  have hB0 : 0 ≤ matDensity Y Z B := matDensity_nonneg (isBinaryMatrix_nonneg hB)
  have hB1 : matDensity Y Z B ≤ 1 := matDensity_le_one_of_isBinaryMatrix hB
  have hBrpow : (matDensity Y Z B) ^ ((1 : ℝ) / 4) ≤ 1 := by
    calc
      (matDensity Y Z B) ^ ((1 : ℝ) / 4) ≤ (1 : ℝ) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow hB0 hB1 (by norm_num)
      _ = 1 := Real.one_rpow _
  have hfac0 : 0 ≤ 128 * (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hBrpow hfac0
  linarith

/-- **`paper.tex` Lemmas 5.3–5.5 & 5.9 (`\label{lem:cube-step}`, `\label{lem:children-invariants}`, `\label{lem:potential}`, `\label{lem:recurrence}`) (`thm_3d_decomp_part2`, §5.2–§5.6)** and
**`paper.tex` Theorem 1.1 (`thm_main_decomp`, §1.2)**:
Combined master specification of `cappedABDecomposition` and `cappedABDecompositionTracked`:
1. Coupled `CostM` projection (`(cappedABDecompositionTracked ...).1 = cappedABDecomposition ...`)
   and worst-case operation count bound,
2. Exact bilinear matrix product conservation $AB = \sum_{P \in \mathcal{S}} P.A_k P.B_k$,
3. Piece structural specification (`ValidCubePiece X Y Z ε D P` for every $P \in \mathcal{S}$) and
   entrywise submatrix dominance $P.A_k \le A[P.X_k, P.Y_k], P.B_k \le B[P.Y_k, P.Z_k]$,
4. Piece count bound $|\mathcal{S}| \le 3 \cdot 2^{D + D^2 + \Gamma H}$, and
5. Joint $(1/4, 1/4)$-potential bound $C_{1/4, 1/4}(\mathcal{S}) \le 128 (\mathbb{E}[B])^{1/4} |X||Y||Z| \le 128 |X||Y||Z|$. -/
theorem thm_3d_decomp_part2 [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    {ε : ℝ} (S : TwoStageSamplerOracle β ε) {D : ℕ}
    (hA : IsBinaryMatrix X Y A) (hB : IsBinaryMatrix Y Z B)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hD : 2 ≤ D) :
    let pieces := cappedABDecomposition X Y Z A B ε S D
    (cappedABDecompositionTracked X Y Z A B ε S D).1 = pieces ∧
    (cappedABDecompositionTracked X Y Z A B ε S D).2 ≤
      ((H3D D + 1) * abDepthCostFactor S.c S.k ε D * (X.card + Y.card + Z.card + 2) ^ 2) *
        pieces.length ∧
    (∀ x ∈ X, ∀ z ∈ Z,
      (pieces.map (fun P => stdMatMul P.Y_k P.A_k P.B_k x z)).sum = stdMatMul Y A B x z) ∧
    (∀ P ∈ pieces, ValidCubePiece X Y Z ε D P) ∧
    (∀ P ∈ pieces,
      (∀ x y, P.A_k x y ≤ submatZeroExt P.X_k P.Y_k A x y) ∧
      (∀ y z, P.B_k y z ≤ submatZeroExt P.Y_k P.Z_k B y z)) ∧
    (pieces.length : ℝ) ≤ 3 * (2 : ℝ) ^ (D + D ^ 2 + GammaTree3D ε D * H3D D) ∧
    cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ) pieces ≤
      128 * (matDensity Y Z B) ^ ((1 : ℝ) / 4) * (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ) ∧
    cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ) pieces ≤
      128 * (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ) := by
  dsimp only
  rcases cappedABDecomposition_potential_le X Y Z A B S hA hB hε0 hε_le hD with ⟨hpot1, hpot2⟩
  exact ⟨cappedABDecompositionTracked_fst X Y Z A B ε S D,
    cappedABDecompositionTracked_snd_le X Y Z A B ε S D,
    fun x hx z hz => cappedABDecomposition_sum_eq X Y Z A B S hA hB hε0 hε_le hD hx hz,
    fun P hP => cappedABDecomposition_pieces_spec X Y Z A B S hA hB hε0 hε_le hD hP,
    fun P hP => cappedABDecomposition_dominance X Y Z A B S hA hB hε0 hε_le hD hP,
    cappedABDecomposition_length_le X Y Z A B S hA hB hε0 hε_le hD,
    hpot1, hpot2⟩

/-- **`paper.tex` Theorem 1.1 (`thm_main_decomp`, §1.2)**:
2-Path Regularity Decomposition with $\exp(O(d^2 / \varepsilon^2))$ Pieces at $D = 2d$. -/
theorem thm_main_decomp [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    {ε : ℝ} (S : TwoStageSamplerOracle β ε) {d : ℕ}
    (hA : IsBinaryMatrix X Y A) (hB : IsBinaryMatrix Y Z B)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hd : 1 ≤ d) :
    let pieces := cappedABDecomposition X Y Z A B ε S (2 * d)
    (cappedABDecompositionTracked X Y Z A B ε S (2 * d)).1 = pieces ∧
    (cappedABDecompositionTracked X Y Z A B ε S (2 * d)).2 ≤
      ((H3D (2 * d) + 1) * abDepthCostFactor S.c S.k ε (2 * d) *
        (X.card + Y.card + Z.card + 2) ^ 2) * pieces.length ∧
    (∀ x ∈ X, ∀ z ∈ Z,
      (pieces.map (fun P => stdMatMul P.Y_k P.A_k P.B_k x z)).sum = stdMatMul Y A B x z) ∧
    (∀ P ∈ pieces, ValidCubePiece X Y Z ε (2 * d) P) ∧
    (∀ P ∈ pieces,
      (∀ x y, P.A_k x y ≤ submatZeroExt P.X_k P.Y_k A x y) ∧
      (∀ y z, P.B_k y z ≤ submatZeroExt P.Y_k P.Z_k B y z)) ∧
    (pieces.length : ℝ) ≤
      3 * (2 : ℝ) ^ ((2 * d) + (2 * d) ^ 2 + GammaTree3D ε (2 * d) * H3D (2 * d)) ∧
    cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ) pieces ≤
      128 * (matDensity Y Z B) ^ ((1 : ℝ) / 4) * (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ) ∧
    cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ) pieces ≤
      128 * (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ) :=
  thm_3d_decomp_part2 X Y Z A B S hA hB hε0 hε_le (by omega)

/-- **`paper.tex` Theorem 1.1 from Cited Samplers (`thm_main_decomp_of_samplers`, §1.2)**:
Instantiates `thm_main_decomp` directly with `twoStage_compose S₁ S₂ ε hε0` for every
`0 < ε ≤ 1 / 160` and `1 ≤ d`. -/
theorem thm_main_decomp_of_samplers [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (A : α → β → ℝ) (B : β → γ → ℝ)
    (S₁ : Stage1Sampler) (S₂ : Stage2Sampler) {ε : ℝ} {d : ℕ}
    (hA : IsBinaryMatrix X Y A) (hB : IsBinaryMatrix Y Z B)
    (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 160) (hd : 1 ≤ d) :
    let S := twoStage_compose S₁ S₂ ε hε0
    let pieces := cappedABDecomposition X Y Z A B ε S (2 * d)
    (cappedABDecompositionTracked X Y Z A B ε S (2 * d)).1 = pieces ∧
    (cappedABDecompositionTracked X Y Z A B ε S (2 * d)).2 ≤
      ((H3D (2 * d) + 1) * abDepthCostFactor S.c S.k ε (2 * d) *
        (X.card + Y.card + Z.card + 2) ^ 2) * pieces.length ∧
    (∀ x ∈ X, ∀ z ∈ Z,
      (pieces.map (fun P => stdMatMul P.Y_k P.A_k P.B_k x z)).sum = stdMatMul Y A B x z) ∧
    (∀ P ∈ pieces, ValidCubePiece X Y Z ε (2 * d) P) ∧
    (∀ P ∈ pieces,
      (∀ x y, P.A_k x y ≤ submatZeroExt P.X_k P.Y_k A x y) ∧
      (∀ y z, P.B_k y z ≤ submatZeroExt P.Y_k P.Z_k B y z)) ∧
    (pieces.length : ℝ) ≤
      3 * (2 : ℝ) ^ ((2 * d) + (2 * d) ^ 2 + GammaTree3D ε (2 * d) * H3D (2 * d)) ∧
    cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ) pieces ≤
      128 * (matDensity Y Z B) ^ ((1 : ℝ) / 4) * (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ) ∧
    cubePotential (1 / 4 : ℝ) (1 / 4 : ℝ) pieces ≤
      128 * (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ) :=
  thm_main_decomp X Y Z A B (twoStage_compose S₁ S₂ ε hε0) hA hB hε0 hε_le hd

end CappedABDecomposition

#verify_standard_axioms BMMGrid.one_sub_rpow_quarter_le
#verify_standard_axioms BMMGrid.bucketedRec_potential_bound
#verify_standard_axioms BMMGrid.table1_budget_cinco_sum_le
#verify_standard_axioms BMMGrid.cappedABDecomposition_sum_eq
#verify_standard_axioms BMMGrid.cappedABDecomposition_pieces_spec
#verify_standard_axioms BMMGrid.cappedABDecomposition_dominance
#verify_standard_axioms BMMGrid.cappedABDecomposition_boolMatMul_iff
#verify_standard_axioms BMMGrid.cappedABDecomposition_length_le
#verify_standard_axioms BMMGrid.cappedABDecomposition_potential_le
#verify_standard_axioms BMMGrid.thm_3d_decomp_part2
#verify_standard_axioms BMMGrid.thm_main_decomp
#verify_standard_axioms BMMGrid.thm_main_decomp_of_samplers

end BMMGrid
