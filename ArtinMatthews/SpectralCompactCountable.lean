module

public import Mathlib


set_option backward.privateInPublic true
@[expose] public section

/-! Independent orthonormal countability proof copied verbatim from
OAI/Analysis/CoulombIonization/FormDomain/CompactEigenbasis.lean. -/

noncomputable section
namespace ArtinMatthews.SpectralCompact
open scoped Topology

universe u v
lemma orthonormal_countable {H : Type u} {ι : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [TopologicalSpace.SeparableSpace H]
    {v : ι → H} (hv : Orthonormal ℂ v) : Countable ι := by
  have hd : Pairwise (fun i j => Disjoint (Metric.ball (v i) (1/2 : ℝ)) (Metric.ball (v j) (1/2 : ℝ))) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    have hs : ‖v i-v j‖^2 = 2 := by
      rw [norm_sub_sq (𝕜 := ℂ),hv.norm_eq_one,hv.norm_eq_one,hv.inner_eq_zero hij]
      norm_num
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (v i-v j)]
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun _ => Metric.nonempty_ball.mpr (by norm_num))

end ArtinMatthews.SpectralCompact
