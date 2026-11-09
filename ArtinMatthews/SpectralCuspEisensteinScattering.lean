module

public import ArtinMatthews.SpectralCuspEisensteinParabolic
public import ArtinMatthews.SpectralCuspScatteringNormalized
public import ArtinMatthews.SpectralCuspEisensteinInfinity
public import ArtinMatthews.SpectralCuspEisensteinWidthFormula


set_option backward.privateInPublic true
@[expose] public section

/-! Public actual all-cusp scattering checkpoint. This is a theorem about the
convergent automorphic Eisenstein family, not a stipulated expansion or a
continuation of a formal coefficient. -/
noncomputable section
open scoped MatrixGroups
namespace ArtinMatthews

local instance cuspScattering_positive_neZero (c : {c : ℕ // 0 < c}) : NeZero c.val :=
  ⟨c.property.ne'⟩

theorem gamma0CuspScattering_double_coset_formula (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (s : ℂ) :
    gamma0CuspScattering N r a s=
      ((Real.sqrt Real.pi:ℂ)*Complex.Gamma (s-1/2)/Complex.Gamma s)*
        ∑' c : {c : ℕ // 0 < c}, (Fintype.card (gamma0TrueWidthReducedMatrix N r a c.val):ℂ)*
          (gamma0TrueWidthModulus N r a (c.val:ℝ):ℂ)^(-2*s) := by
  rw [gamma0CuspScattering_normalized_modulus]
  congr 1
  apply tsum_congr
  intro c
  rw [gamma0CuspScatteringCount_eq_trueWidth]

theorem gamma0CuspEisenstein_normalized_constant_matrix (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (s : ℂ) (hs : 1 < s.re) (y : ℝ) (hy : 0 < y) :
    (∫ x in (0:ℝ)..1, gamma0CuspEisenstein N a s
      (gamma0TrueCuspScaling N r • gamma0EisensteinHorizontalPoint y hy x))=
      gamma0CuspEisensteinIndicator N r a*(y:ℂ)^s+
        (y:ℂ)^(1-s)*((Real.sqrt Real.pi:ℂ)*Complex.Gamma (s-1/2)/Complex.Gamma s)*
          ∑' c : {c : ℕ // 0 < c}, (Fintype.card (gamma0TrueWidthReducedMatrix N r a c.val):ℂ)*
            (gamma0TrueWidthModulus N r a (c.val:ℝ):ℂ)^(-2*s) := by
  rw [gamma0CuspEisenstein_all_cusp_constant_term N r a s hs y hy,
    gamma0CuspScattering_double_coset_formula]
  ring

end ArtinMatthews
