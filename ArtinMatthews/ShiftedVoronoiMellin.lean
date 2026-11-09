module

public import Mathlib.Analysis.MellinTransform


set_option backward.privateInPublic true
@[expose] public section

/-!
# Mellin reflection for the shifted Voronoi argument

The reciprocal change of variables in a weight-`k` modular transformation sends
the Mellin parameter `s` to `k - s`.  These lemmas prove that change of variables
for arbitrary complex `k`, keeping the scalar and positive real scale explicit.

The positive-axis transformation is a hypothesis of the second lemma; it is not
a proof of modularity or of a Voronoi summation formula.  As for Mathlib's Mellin
change-of-variables lemmas, these equalities concern the totalized integral.
Convergence must be proved separately when using them as analytic transforms.
-/

noncomputable section

open MeasureTheory Set

namespace ArtinMatthews

/-- Mellin reflection under `v ↦ (Q * v)⁻¹`, with arbitrary complex weight. -/
theorem mellin_weight_reflection (g : ℝ → ℂ) (A k s : ℂ)
    (Q : ℝ) (hQ : 0 < Q) :
    mellin (fun v : ℝ ↦ A * ((v : ℂ) ^ (-k) * g ((Q * v)⁻¹))) s =
      A * (Q : ℂ) ^ (k - s) * mellin g (k - s) := by
  have he : (fun v : ℝ ↦ A * ((v : ℂ) ^ (-k) * g ((Q * v)⁻¹))) =
      (fun v : ℝ ↦ A • ((v : ℂ) ^ (-k) • g ((Q * v)⁻¹))) := by
    funext v
    simp only [smul_eq_mul]
  have hm := mellin_comp_mul_left (fun v : ℝ ↦ g v⁻¹) (s + -k) hQ
  rw [mellin_comp_inv] at hm
  rw [he, mellin_const_smul, mellin_cpow_smul, hm]
  simp only [smul_eq_mul, ← sub_eq_add_neg, neg_sub, mul_assoc]

/-- A transformation known on the positive axis suffices for Mellin reflection. -/
theorem mellin_weight_reflection_of_identity (f g : ℝ → ℂ) (A k s : ℂ)
    (Q : ℝ) (hQ : 0 < Q)
    (hfg : ∀ v : ℝ, 0 < v →
      f v = A * ((v : ℂ) ^ (-k) * g ((Q * v)⁻¹))) :
    mellin f s = A * (Q : ℂ) ^ (k - s) * mellin g (k - s) := by
  rw [← mellin_weight_reflection g A k s Q hQ]
  unfold mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  exact congrArg (fun z : ℂ ↦ (v : ℂ) ^ (s - 1) • z) (hfg v hv)

end ArtinMatthews
