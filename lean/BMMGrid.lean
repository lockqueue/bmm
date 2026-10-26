import BMMGrid.Defs
import BMMGrid.CostMonadAndLinter
import BMMGrid.ArithRAM
import BMMGrid.KLMUniformity
import BMMGrid.CitedResults
import BMMGrid.ObliviousSampler
import BMMGrid.ApproxGridNorm
import BMMGrid.MinDegreeAndDyadicSift
import BMMGrid.Decomp2D
import BMMGrid.DyadicBucketingAndGoodCube
import BMMGrid.Decomp3DPotential
import BMMGrid.Decomp3D
import BMMGrid.TriangleAndBMM
/-! # Improved Grid-Regularity Decompositions & Combinatorial BMM (`BMMGrid.lean`)
Top-level trust boundary (< 60 LoC) for `paper.tex`. -/
namespace BMMGrid
/-- Self-contained specification checks: `hasTriangle` & `boolMatMul` by `rfl`. -/
example (n : ℕ) (A B C : Fin n → Fin n → Bool) :
    hasTriangle n A B C = decide (∃ i j k : Fin n, A i j = true ∧ B j k = true ∧ C i k = true) := rfl
example (n : ℕ) (A B : Fin n → Fin n → Bool) (i j : Fin n) :
    boolMatMul n A B i j = decide (∃ k : Fin n, A i k = true ∧ B k j = true) := rfl
/-- Conditional $n = 2$ sanity checks of the headline functions; the sampler structures remain parameters, so these examples do not establish that `Stage1Sampler` / `Stage2Sampler` is inhabited. -/
example (S₁ : Stage1Sampler) (S₂ : Stage2Sampler) : ∃ t : ℕ,
    computableTriangleDetectionTracked 2 S₁ S₂ (fun i j => i == j) (fun i j => i == j) (fun i j => i == j) =
      (hasTriangle 2 (fun i j => i == j) (fun i j => i == j) (fun i j => i == j), t) := by
  obtain ⟨_, _, _, _, h⟩ := thm_main_triangle_detection_graph S₁ S₂
  obtain ⟨t, ht, _⟩ := h 2 (by decide) (fun i j => i == j); exact ⟨t, ht⟩
example (S₁ : Stage1Sampler) (S₂ : Stage2Sampler) : ∃ t : ℕ,
    computableBMMTracked 2 S₁ S₂ (fun i j => i == j) (fun i j => i == j) =
      (boolMatMul 2 (fun i j => i == j) (fun i j => i == j), t) := by
  obtain ⟨_, _, _, _, h⟩ := thm_main_bmm S₁ S₂
  obtain ⟨t, ht, _⟩ := h 2 (by decide) (fun i j => i == j) (fun i j => i == j); exact ⟨t, ht⟩
#verify_no_escape_hatches
#verify_tracked_declarations_ast_audit
#verify_headline_cone_excludes
#verify_no_unused_decls
#verify_standard_axioms BMMGrid.prop_regular_matrices_uniform_product
#verify_standard_axioms BMMGrid.twoStage_compose
#verify_standard_axioms BMMGrid.lem_approx_grid_norm
#verify_standard_axioms BMMGrid.thm_2d_decomp
#verify_standard_axioms BMMGrid.thm_2d_decomp_concrete
#verify_standard_axioms BMMGrid.thm_2d_decomp_uncapped
#verify_standard_axioms BMMGrid.thm_2d_decomp_uncapped_concrete
#verify_standard_axioms BMMGrid.thm_main_decomp
#verify_standard_axioms BMMGrid.thm_main_decomp_of_samplers
#verify_standard_axioms BMMGrid.thm_main_3d_decomposition
#verify_standard_axioms BMMGrid.thm_main_triangle_detection
#verify_standard_axioms BMMGrid.thm_main_triangle_detection_graph
#verify_standard_axioms BMMGrid.thm_main_triangle_detection_log_cost_absorption
#verify_standard_axioms BMMGrid.thm_main_bmm
#verify_standard_axioms BMMGrid.thm_main_bmm_log_cost_absorption
end BMMGrid
