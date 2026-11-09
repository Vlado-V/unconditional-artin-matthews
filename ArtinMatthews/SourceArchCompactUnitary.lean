module

public import ArtinMatthews.SourceArchSphericalUnitary
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Topology.Algebra.Star.Unitary


set_option backward.privateInPublic true
@[expose] public section

/-! Compactness of the literal U(2) fixing subgroup. -/
namespace ArtinMatthews.SourceArchJacquet

open Matrix
noncomputable section

theorem sourceArchUnitary_isCompact :
    IsCompact (Matrix.unitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
  apply (isCompact_closedBall (0 : ℂ) 1).matrix.of_isClosed_subset isClosed_unitary
  intro U hU
  change ∀ i j, U i j ∈ Metric.closedBall (0 : ℂ) 1
  intro i j
  rw [Metric.mem_closedBall, dist_zero_right]
  exact entry_norm_bound_of_unitary hU i j

end
end ArtinMatthews.SourceArchJacquet
