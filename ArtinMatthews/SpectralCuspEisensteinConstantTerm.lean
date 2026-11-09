module

public import ArtinMatthews.SpectralCuspEisensteinEquivalentWidths
public import ArtinMatthews.SpectralCuspEisensteinPositiveIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! The actual all-cusp constant-term matrix on Re(s)>1. Both source and
target widths, the original half-row normalization and the zero sector have
been derived from actual matrices and actual absolutely convergent sums. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace ArtinMatthews

def gamma0CuspScattering (N : ℕ) [NeZero N] (r a : SL(2,ℤ)) (s : ℂ) : ℂ :=
  (gamma0CuspTrueWidth N a:ℂ)^(-s)*(gamma0CuspTrueWidth N r:ℂ)^(-s)*
    ((Real.sqrt Real.pi:ℂ)*Complex.Gamma (s-1/2)/Complex.Gamma s)*
      gamma0CuspScatteringDirichlet N r a s

theorem gamma0CuspEisenstein_all_cusp_constant_term (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) (y : ℝ) (hy : 0 < y) :
    (∫ x in (0:ℝ)..1, gamma0CuspEisenstein N a s
      (gamma0TrueCuspScaling N r • gamma0EisensteinHorizontalPoint y hy x))=
      gamma0CuspEisensteinIndicator N r a*(y:ℂ)^s+(y:ℂ)^(1-s)*gamma0CuspScattering N r a s := by
  rw [gamma0CuspEisenstein_constant_integral_rows N r a s hs y hy,
    cuspEisenstein_signed_tsum N r a _ (cuspEisensteinRowIntegral_summable N r a s hs y hy)
      (fun v => by unfold cuspEisensteinRowIntegral; simp only [cuspEisensteinRowTerm_neg])]
  calc
    _=(gamma0CuspTrueWidth N a:ℂ)^(-s)*(1/2:ℂ)*
        (∑' v : CuspEisensteinZeroRows N r a, cuspEisensteinRowIntegral N r a s y hy v.val)+
      (gamma0CuspTrueWidth N a:ℂ)^(-s)*
        (∑' v : CuspEisensteinPositiveRows N r a, cuspEisensteinRowIntegral N r a s y hy v.val) := by ring
    _=gamma0CuspEisensteinIndicator N r a*(y:ℂ)^s+
        (gamma0CuspTrueWidth N a:ℂ)^(-s)*
          ((gamma0CuspTrueWidth N r:ℂ)^(-s)*(y:ℂ)^(1-s)*
            ((Real.sqrt Real.pi:ℂ)*Complex.Gamma (s-1/2)/Complex.Gamma s)*
              gamma0CuspScatteringDirichlet N r a s) := by
      rw [gamma0CuspEisenstein_leading_constant,cuspEisensteinPositiveIntegral_dirichlet N r a s hs y hy]
    _=_ := by unfold gamma0CuspScattering; ring

theorem gamma0CuspEisenstein_all_cusp_constant_term_explicit (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (s : ℂ) (hs : 1 < s.re) (y : ℝ) (hy : 0 < y) :
    (∫ x in (0:ℝ)..1, gamma0CuspEisenstein N a s
      (gamma0TrueCuspScaling N r • gamma0EisensteinHorizontalPoint y hy x))=
      gamma0CuspEisensteinIndicator N r a*(y:ℂ)^s+
        (y:ℂ)^(1-s)*(gamma0CuspTrueWidth N a:ℂ)^(-s)*(gamma0CuspTrueWidth N r:ℂ)^(-s)*
          ((Real.sqrt Real.pi:ℂ)*Complex.Gamma (s-1/2)/Complex.Gamma s)*
            ∑' c : {c : ℕ // 0 < c},
              (gamma0CuspScatteringCount N r a c.val:ℂ)*(c.val:ℂ)^(-2*s) := by
  rw [gamma0CuspEisenstein_all_cusp_constant_term N r a s hs y hy]
  unfold gamma0CuspScattering gamma0CuspScatteringDirichlet
  ring

end ArtinMatthews
