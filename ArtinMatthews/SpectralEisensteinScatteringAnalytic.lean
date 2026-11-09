module

public import ArtinMatthews.SpectralEisensteinConstantMode
public import ArtinMatthews.SpectralCuspEulerCoefficient


set_option backward.privateInPublic true
@[expose] public section

/-! A holomorphic all-cusp coefficient extracted from the actual continued
ambient remainder. Its literal decaying-mode identity is proved first;
identification with the original scattering series is a separate theorem. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped MatrixGroups
namespace ArtinMatthews

def gamma0CuspEisensteinContinuedCoefficient (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (s : ℂ) : ℂ :=
  let Y : ℝ := 2*(gamma0CuspTrueWidth N r:ℝ)
  cuspEulerCoefficientExtract (Nat.cast_pos.mpr (NeZero.pos N))
    (by dsimp [Y];exact mul_pos (by norm_num) (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r))) s
    (gamma0CuspConstantTerm N r Y (by dsimp [Y];exact mul_pos (by norm_num) (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)))
      (gamma0CuspEisensteinContinuedRemainder N a s))

theorem gamma0CuspEisensteinContinuedCoefficient_mode (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (s : ℂ) (hs : s ∈ gamma0EisensteinContinuationDomain) :
    gamma0GlobalCuspConstantTerm N r (gamma0CuspEisensteinContinuedRemainder N a s)
      =ᵐ[volume.restrict (Ioi (2*(gamma0CuspTrueWidth N r:ℝ)))]
        fun y => gamma0CuspEisensteinContinuedCoefficient N r a s*(y:ℂ)^(1-s) := by
  let Y : ℝ := 2*(gamma0CuspTrueWidth N r:ℝ)
  have hY : 0<Y := by dsimp [Y];exact mul_pos (by norm_num) (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r))
  have hw : 0<(N:ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  obtain ⟨B,hB⟩ := gamma0CuspEisensteinContinuedRemainder_constant_mode N r a s hs Y hY le_rfl
  have he : gamma0GlobalCuspConstantTerm N r (gamma0CuspEisensteinContinuedRemainder N a s)
      =ᵐ[volume.restrict (Ioi Y)]
        (gamma0CuspConstantTerm N r Y hY (gamma0CuspEisensteinContinuedRemainder N a s)) :=
    (spectralCuspVerticalL2_ae_iff hw hY).mp
    (gamma0GlobalCuspConstantTerm_ae N r (gamma0CuspEisensteinContinuedRemainder N a s) Y hY)
  have hU := (spectralCuspVerticalL2_ae_iff hw hY).mpr (he.symm.trans hB)
  have hc : gamma0CuspEisensteinContinuedCoefficient N r a s=B :=
    cuspEulerCoefficientExtract_power hw hY s B hs.1 _ hU
  simpa only [hc] using hB

theorem cuspPositivePower_parameter_analyticAt (y : ℝ) (hy : 0<y) (s : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => (y:ℂ)^(w+1)) s := by
  have he : (fun w : ℂ => (y:ℂ)^(w+1))=
      (fun w : ℂ => Complex.exp (Complex.log (y:ℂ)*(w+1))) := by
    funext w
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne')]
  rw [he]
  exact (analyticAt_const.mul (analyticAt_id.add analyticAt_const)).cexp'

theorem gamma0CuspEisensteinContinuedCoefficient_analyticAt (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (s : ℂ) (hs : s ∈ gamma0EisensteinContinuationDomain) :
    AnalyticAt ℂ (gamma0CuspEisensteinContinuedCoefficient N r a) s := by
  let Y : ℝ := 2*(gamma0CuspTrueWidth N r:ℝ)
  have hY : 0<Y := by dsimp [Y];exact mul_pos (by norm_num) (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r))
  let T := (cuspEulerCoefficientTest (Nat.cast_pos.mpr (NeZero.pos N)) hY).comp
    (gamma0CuspConstantTerm N r Y hY)
  have hT : AnalyticAt ℂ (fun w => T (gamma0CuspEisensteinContinuedRemainder N a w)) s :=
    (T.analyticAt _).comp (gamma0CuspEisensteinContinuedRemainder_analyticAt N a s hs)
  have hp : AnalyticAt ℂ (fun w : ℂ => (w+1)*(Y:ℂ)^(w+1)/(N:ℂ)) s :=
    ((analyticAt_id.add analyticAt_const).mul
      (cuspPositivePower_parameter_analyticAt Y hY s)).div_const
  exact hp.mul hT

def gamma0CuspScatteringContinued (N : ℕ) [NeZero N] (r a : SL(2,ℤ)) (s : ℂ) : ℂ :=
  (gamma0CuspTrueWidth N r:ℂ)^(1-s)*gamma0CuspEisensteinContinuedCoefficient N r a s

theorem gamma0CuspScatteringContinued_analyticAt (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (s : ℂ) (hs : s ∈ gamma0EisensteinContinuationDomain) :
    AnalyticAt ℂ (gamma0CuspScatteringContinued N r a) s := by
  have hne : (gamma0CuspTrueWidth N r:ℂ)≠0 := by exact_mod_cast (gamma0CuspTrueWidth_pos N r).ne'
  have he : (fun w : ℂ => (gamma0CuspTrueWidth N r:ℂ)^(1-w))=
      (fun w : ℂ => Complex.exp (Complex.log (gamma0CuspTrueWidth N r:ℂ)*(1-w))) := by
    funext w
    rw [Complex.cpow_def_of_ne_zero hne]
  have hp : AnalyticAt ℂ (fun w : ℂ => (gamma0CuspTrueWidth N r:ℂ)^(1-w)) s := by
    rw [he]
    exact (analyticAt_const.mul (analyticAt_const.sub analyticAt_id)).cexp'
  exact hp.mul (gamma0CuspEisensteinContinuedCoefficient_analyticAt N r a s hs)

end ArtinMatthews
