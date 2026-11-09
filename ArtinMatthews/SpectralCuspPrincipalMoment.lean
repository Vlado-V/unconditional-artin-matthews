module

public import ArtinMatthews.SpectralCuspTrueWidthPhysicalMoment
public import ArtinMatthews.SpectralKFrameCompactProfiles
public import ArtinMatthews.SpectralGamma0PoincareKL


set_option backward.privateInPublic true
@[expose] public section

/-! The true-width compact principal moment in finite spectral windows. -/
noncomputable section
open scoped MatrixGroups BigOperators
namespace ArtinMatthews

def gamma0CuspUnitAmplitude (N : ℕ) [NeZero N] (i : Gamma0AllHeightSpectralIndex N)
    (b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) : ℂ :=
  (Real.sqrt (gamma0CuspTrueWidth N b : ℝ) : ℂ)*
    gamma0CuspBesselAmplitude N i b Y hY ((gamma0CuspFrequencyStep N b : ℤ)*n)
      (gamma0CuspFrequencyStep_mul_ne_zero N b hn)

def gamma0CuspPrincipalParameter (N : ℕ) [NeZero N] (i : Gamma0AllHeightSpectralIndex N) : ℝ :=
  Real.sqrt (gamma0AllHeightGradientSpectralValue N i-1/4)

def gamma0CuspPrincipalMoment (N : ℕ) [NeZero N]
    (u : Finset (Gamma0AllHeightSpectralIndex N)) (b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (n : ℤ) (hn : n ≠ 0) : ℝ :=
  u.sum fun i : Gamma0AllHeightSpectralIndex N =>
    ‖gamma0CuspUnitAmplitude N i b Y hY n hn‖^2 / Real.cosh (Real.pi*gamma0CuspPrincipalParameter N i)

theorem gamma0CuspPhysicalBesselMoment_principal_eq (N : ℕ) [NeZero N]
    (u : Finset (Gamma0AllHeightSpectralIndex N)) (b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (n : ℤ) (hn : n ≠ 0) (F : ℝ → ℝ)
    (hprincipal : ∀ i ∈ u, 1/4 ≤ gamma0AllHeightGradientSpectralValue N i) :
    gamma0CuspPhysicalBesselMoment N u b Y hY n hn F =
      u.sum fun i : Gamma0AllHeightSpectralIndex N =>
        ‖gamma0CuspUnitAmplitude N i b Y hY n hn‖^2*
          ‖spectralCompactRealKTransform F (gamma0CuspPrincipalParameter N i)‖^2 := by
  unfold gamma0CuspPhysicalBesselMoment
  dsimp only
  apply Finset.sum_congr rfl
  intro i hi
  rw [spectralComplexSqrt_quarter_sub_real _ (hprincipal i hi)]
  exact mul_comm _ _

theorem spectral_principal_orbit_growth_le {C T q N : ℝ} (hC : 0 ≤ C)
    (hT : 0 < T) (hN : 0 < N) :
    C*T^2*(6*(1+2*q/(N*(T/16)))) ≤ 192*C*(T^2+q*T/N) := by
  calc
    _ = (6*C)*(T^2+32*(q*T/N)) := by
      field_simp [hN.ne',hT.ne']
      ring
    _ ≤ (6*C)*(32*(T^2+q*T/N)) :=
      mul_le_mul_of_nonneg_left (by linarith only [sq_nonneg T]) (by positivity)
    _ = _ := by ring

end ArtinMatthews
