module

public import ArtinMatthews.SpectralEisensteinProfileLocalFinite
public import ArtinMatthews.SpectralBoundedExponential


set_option backward.privateInPublic true
@[expose] public section

/-! The actual locally finite source-height cutoff is entire in s at every
point. Its finite index set is chosen independently of s. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups
namespace ArtinMatthews

theorem cuspEisensteinCutoffTerm_analyticAt (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (v : Gamma0CuspEisensteinRows N r a) (z : UpperHalfPlane) (s : ℂ) :
    AnalyticAt ℂ (fun w => cuspEisensteinCutoffTerm N r a w v z) s := by
  have hn : (cuspEisensteinNormalizedHeight N r a v z:ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (cuspEisensteinNormalizedHeight_pos N r a v z).ne'
  have he : (fun w => cuspEisensteinCutoffTerm N r a w v z)=
      (fun w : ℂ => (eisensteinHeightCutoff (cuspEisensteinNormalizedHeight N r a v z):ℂ)*
        Complex.exp (Complex.log (cuspEisensteinNormalizedHeight N r a v z:ℂ)*w)) := by
    funext w
    rw [cuspEisensteinCutoffTerm,Complex.cpow_def_of_ne_zero hn]
  rw [he]
  exact analyticAt_const.mul ((analyticAt_const.mul analyticAt_id).cexp')

theorem gamma0CuspEisensteinCutoff_parameter_finite (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (z : UpperHalfPlane) : ∃ T : Finset (Gamma0CuspEisensteinRows N 1 a),
      ∀ s : ℂ, gamma0CuspEisensteinCutoff N a s z=
        (1/2:ℂ)*∑ v ∈ T, cuspEisensteinCutoffTerm N 1 a s v z := by
  classical
  have hf := cuspEisensteinHeight_compact_finite N 1 a (by norm_num : (0:ℝ)<1)
    (isCompact_singleton : IsCompact ({z}:Set UpperHalfPlane))
  refine ⟨hf.toFinset,?_⟩
  intro s
  unfold gamma0CuspEisensteinCutoff
  congr 1
  apply tsum_eq_sum
  intro v hv
  by_contra hn
  have hc : eisensteinHeightCutoff (cuspEisensteinNormalizedHeight N 1 a v z) ≠ 0 := by
    intro h
    exact hn (by simp only [cuspEisensteinCutoffTerm,h,Complex.ofReal_zero,zero_mul])
  exact hv (hf.mem_toFinset.mpr ⟨z,mem_singleton z,(eisensteinHeightCutoff_nonzero hc).le⟩)

theorem gamma0CuspEisensteinCutoff_analyticAt (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (z : UpperHalfPlane) (s : ℂ) :
    AnalyticAt ℂ (fun w => gamma0CuspEisensteinCutoff N a w z) s := by
  obtain ⟨T,hT⟩ := gamma0CuspEisensteinCutoff_parameter_finite N a z
  have he : (fun w => gamma0CuspEisensteinCutoff N a w z)=
      (fun w => (1/2:ℂ)*∑ v ∈ T, cuspEisensteinCutoffTerm N 1 a w v z) := funext hT
  rw [he]
  exact analyticAt_const.mul (T.analyticAt_fun_sum (fun v _ => cuspEisensteinCutoffTerm_analyticAt N 1 a v z s))

end ArtinMatthews
