module

public import ArtinMatthews.NativeLocalNorm


set_option backward.privateInPublic true
@[expose] public section

/-! Analytic topological conditions derived from the actual native local
norm, rather than added to the comparison statement. -/

namespace ArtinMatthews.QuadraticWeil

open LocalFieldTheory
open scoped Topology Classical ValuativeRel

theorem ultrametric_nonarchimedean (K : Type) [NormedField K] [IsUltrametricDist K] :
    NonarchimedeanAddGroup K where
  toIsTopologicalAddGroup := inferInstance
  is_nonarchimedean := by
    intro s hs
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hs
    refine ⟨IsUltrametricDist.closedBall_openAddSubgroup K (half_pos hε), ?_⟩
    intro x hx
    apply hsub
    change dist x 0 < ε
    rw [dist_zero_right]
    change x ∈ Metric.closedBall 0 (ε / 2) at hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    exact hx.trans_lt (half_lt_self hε)

theorem nontrivialNorm_not_discrete (K : Type) [NontriviallyNormedField K] :
    ¬ DiscreteTopology K := by
  intro hd
  let : DiscreteTopology K := hd
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp (isOpen_discrete ({0} : Set K)) 0 (by simp)
  obtain ⟨x, hx, hxε⟩ := NormedField.exists_norm_lt K hε
  have hx0 : x = 0 := hsub (by simpa only [Metric.mem_ball, dist_zero_right] using hxε)
  simp only [hx0, norm_zero, lt_self_iff_false] at hx

noncomputable section

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

theorem nativeLocalNorm_nonarchimedean :
    letI : NontriviallyNormedField K := localFieldNontriviallyNormedField K
    NonarchimedeanAddGroup K := by
  let : NontriviallyNormedField K := localFieldNontriviallyNormedField K
  let : IsUltrametricDist K := nativeLocalNorm_ultrametric K
  exact ultrametric_nonarchimedean K

theorem nativeLocalNorm_not_discrete :
    letI : NontriviallyNormedField K := localFieldNontriviallyNormedField K
    ¬ DiscreteTopology K := by
  let : NontriviallyNormedField K := localFieldNontriviallyNormedField K
  exact nontrivialNorm_not_discrete K

end

end ArtinMatthews.QuadraticWeil
