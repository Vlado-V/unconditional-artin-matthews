module

public import ArtinMatthews.SpectralEisensteinRemainderPDE


set_option backward.privateInPublic true
@[expose] public section

/-! Actual automorphy of the cutoff, remainder and compact forcing. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0CuspHeightProfile_automorphy (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (f : ℝ → ℂ) (g : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    gamma0CuspHeightProfile N a f (g.val • z)=gamma0CuspHeightProfile N a f z := by
  unfold gamma0CuspHeightProfile
  congr 1
  have h := finsum_comp_equiv
    (f := fun v : Gamma0CuspEisensteinRows N 1 a =>
      f (cuspEisensteinRowHeight N 1 a v z/(gamma0CuspTrueWidth N a:ℝ)))
    (cuspEisensteinAutomorphyEquiv N a g)
  simpa only [cuspEisensteinRowHeight_automorphy] using h

theorem gamma0CuspEisensteinCutoff_automorphy (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (g : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    gamma0CuspEisensteinCutoff N a s (g.val • z)=gamma0CuspEisensteinCutoff N a s z := by
  rw [gamma0CuspEisensteinCutoff_eq_profile,gamma0CuspEisensteinCutoff_eq_profile]
  exact gamma0CuspHeightProfile_automorphy N a _ g z

theorem gamma0CuspEisensteinRemainder_automorphy (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (g : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    gamma0CuspEisensteinRemainder N a s (g.val • z)=gamma0CuspEisensteinRemainder N a s z := by
  rw [gamma0CuspEisensteinRemainder,gamma0CuspEisensteinRemainder,
    gamma0CuspEisenstein_automorphy,gamma0CuspEisensteinCutoff_automorphy]

theorem gamma0CuspEisensteinCompactForcing_automorphy (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (g : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    gamma0CuspEisensteinCompactForcing N a s (g.val • z)=gamma0CuspEisensteinCompactForcing N a s z :=
  gamma0CuspHeightProfile_automorphy N a _ g z

theorem gamma0CuspEisensteinCompactForcing_continuous (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) : Continuous (gamma0CuspEisensteinCompactForcing N a s) := by
  have he : gamma0CuspEisensteinCompactForcing N a s=
      (1/2:ℂ) • gamma0PoincareSeed N
        (cuspHeightProfileSeed N a (eisensteinVerticalCutoffError s)
          (eisensteinVerticalCutoffError_smooth s) (eisensteinVerticalCutoffError_compact s)
          (eisensteinVerticalCutoffError_positive_support s)).val :=
    funext (gamma0CuspEisensteinCompactForcing_eq_poincare N a s)
  rw [he]
  exact continuous_const.smul (gamma0PoincareSeed N _).continuous

end ArtinMatthews
