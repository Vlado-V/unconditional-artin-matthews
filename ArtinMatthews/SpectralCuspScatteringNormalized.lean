module

public import ArtinMatthews.SpectralCuspEisensteinConstantTerm
public import ArtinMatthews.SpectralCuspEisensteinDoubleCosets
public import ArtinMatthews.SpectralTrueWidthNormalizedMatrices


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine scattering coefficient uses precisely the same normalized
modulus and actual finite double cosets as the geometric Bessel packet. -/
noncomputable section
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0CuspScatteringCount_eq_trueWidth (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (c : ℕ) [NeZero c] :
    gamma0CuspScatteringCount N r a c=Fintype.card (gamma0TrueWidthReducedMatrix N r a c) :=
  (Fintype.card_congr (cuspEisensteinReducedMatrixRowEquiv N r a c)).symm

theorem cuspScattering_sqrt_power (s : ℂ) (u : ℝ) (hu : 0 < u) :
    (Real.sqrt u:ℂ)^(-2*s)=(u:ℂ)^(-s) := by
  have hp := Complex.cpow_mul_ofReal_nonneg (Real.sqrt_nonneg u) 2 (-s)
  have he : -2*s=(2:ℂ)*(-s) := by ring
  rw [he]
  simpa [Real.rpow_two,Real.sq_sqrt hu.le] using hp

theorem cuspScattering_normalized_width_power (s : ℂ) (u v c : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hc : 0 < c) :
    (v:ℂ)^(-s)*(u:ℂ)^(-s)*(c:ℂ)^(-2*s)=
      ((c*Real.sqrt u*Real.sqrt v:ℝ):ℂ)^(-2*s) := by
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg
    (mul_nonneg hc.le (Real.sqrt_nonneg u)) (Real.sqrt_nonneg v),
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hc.le (Real.sqrt_nonneg u),
    cuspScattering_sqrt_power s u hu,cuspScattering_sqrt_power s v hv]
  ring

theorem gamma0CuspScattering_normalized_modulus (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) :
    gamma0CuspScattering N r a s=
      ((Real.sqrt Real.pi:ℂ)*Complex.Gamma (s-1/2)/Complex.Gamma s)*
        ∑' c : {c : ℕ // 0 < c},
          (gamma0CuspScatteringCount N r a c.val:ℂ)*
            (gamma0TrueWidthModulus N r a (c.val:ℝ):ℂ)^(-2*s) := by
  unfold gamma0CuspScattering gamma0CuspScatteringDirichlet
  have he : (∑' c : {c : ℕ // 0 < c},
      (gamma0CuspScatteringCount N r a c.val:ℂ)*
        (gamma0TrueWidthModulus N r a (c.val:ℝ):ℂ)^(-2*s))=
      ((gamma0CuspTrueWidth N a:ℂ)^(-s)*(gamma0CuspTrueWidth N r:ℂ)^(-s))*
        ∑' c : {c : ℕ // 0 < c}, (gamma0CuspScatteringCount N r a c.val:ℂ)*(c.val:ℂ)^(-2*s) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro c
    have hp := cuspScattering_normalized_width_power s (gamma0CuspTrueWidth N r:ℝ)
      (gamma0CuspTrueWidth N a:ℝ) (c.val:ℝ)
      (by exact_mod_cast gamma0CuspTrueWidth_pos N r)
      (by exact_mod_cast gamma0CuspTrueWidth_pos N a) (by exact_mod_cast c.property)
    have hp' : (gamma0CuspTrueWidth N a:ℂ)^(-s)*(gamma0CuspTrueWidth N r:ℂ)^(-s)*
        (c.val:ℂ)^(-2*s)=(gamma0TrueWidthModulus N r a (c.val:ℝ):ℂ)^(-2*s) := by
      simpa only [Complex.ofReal_natCast,gamma0TrueWidthModulus] using hp
    rw [← hp']
    ring
  rw [he]
  ring

end ArtinMatthews
