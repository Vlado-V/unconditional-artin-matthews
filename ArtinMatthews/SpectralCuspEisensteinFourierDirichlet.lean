module

public import ArtinMatthews.SpectralCuspEisensteinFourierCoordinates
public import ArtinMatthews.SpectralCuspScatteringNormalized


set_option backward.privateInPublic true
@[expose] public section

/-! Absolutely convergent nonzero Fourier Dirichlet coefficients over
the genuine reduced matrices and the literal true-width modulus. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups

namespace ArtinMatthews

local instance cuspFourierDirichlet_neZero (c : {c : ℕ // 0 < c}) : NeZero c.val :=
  ⟨c.property.ne'⟩

def gamma0CuspFourierDirichletRaw (N : ℕ) [NeZero N] (r a : SL(2, ℤ)) (n : ℤ) (s : ℂ) : ℂ :=
  ∑' c : {c : ℕ // 0 < c}, gamma0TrueWidthKloostermanSum N r a c.val n 0*(c.val : ℂ)^(-2*s)

def gamma0CuspFourierDirichlet (N : ℕ) [NeZero N] (r a : SL(2, ℤ)) (n : ℤ) (s : ℂ) : ℂ :=
  ∑' c : {c : ℕ // 0 < c}, gamma0TrueWidthKloostermanSum N r a c.val n 0*
    (gamma0TrueWidthModulus N r a (c.val : ℝ) : ℂ)^(-2*s)

theorem gamma0CuspFourierDirichletRaw_summable_norm (N : ℕ) [NeZero N]
    (r a : SL(2, ℤ)) (n : ℤ) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun c : {c : ℕ // 0 < c} =>
      ‖gamma0TrueWidthKloostermanSum N r a c.val n 0*(c.val : ℂ)^(-2*s)‖) := by
  apply (gamma0CuspScatteringDirichlet_summable_norm N r a s hs).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro c
  rw [norm_mul,norm_mul,Complex.norm_natCast,gamma0CuspScatteringCount_eq_trueWidth]
  exact mul_le_mul_of_nonneg_right (gamma0TrueWidthKloostermanSum_trivial_bound N r a c.val n 0)
    (norm_nonneg _)

theorem gamma0CuspFourierDirichletRaw_summable (N : ℕ) [NeZero N]
    (r a : SL(2, ℤ)) (n : ℤ) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun c : {c : ℕ // 0 < c} =>
      gamma0TrueWidthKloostermanSum N r a c.val n 0*(c.val : ℂ)^(-2*s)) :=
  (gamma0CuspFourierDirichletRaw_summable_norm N r a n s hs).of_norm

theorem gamma0CuspFourierDirichlet_normalized (N : ℕ) [NeZero N]
    (r a : SL(2, ℤ)) (n : ℤ) (s : ℂ) :
    gamma0CuspFourierDirichlet N r a n s =
      ((gamma0CuspTrueWidth N a : ℂ)^(-s)*(gamma0CuspTrueWidth N r : ℂ)^(-s))*
        gamma0CuspFourierDirichletRaw N r a n s := by
  unfold gamma0CuspFourierDirichlet gamma0CuspFourierDirichletRaw
  rw [← tsum_mul_left]
  apply tsum_congr
  intro c
  have h := cuspScattering_normalized_width_power s (gamma0CuspTrueWidth N r : ℝ)
    (gamma0CuspTrueWidth N a : ℝ) (c.val : ℝ)
    (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r))
    (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N a)) (Nat.cast_pos.mpr c.property)
  have hp : (gamma0CuspTrueWidth N a : ℂ)^(-s)*(gamma0CuspTrueWidth N r : ℂ)^(-s)*
      (c.val : ℂ)^(-2*s) = (gamma0TrueWidthModulus N r a (c.val : ℝ) : ℂ)^(-2*s) := by
    simpa only [Complex.ofReal_natCast,gamma0TrueWidthModulus] using h
  rw [← hp]
  ring

theorem gamma0CuspFourierDirichlet_summable (N : ℕ) [NeZero N]
    (r a : SL(2, ℤ)) (n : ℤ) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun c : {c : ℕ // 0 < c} => gamma0TrueWidthKloostermanSum N r a c.val n 0*
      (gamma0TrueWidthModulus N r a (c.val : ℝ) : ℂ)^(-2*s)) := by
  let z : ℂ := (gamma0CuspTrueWidth N a : ℂ)^(-s)*(gamma0CuspTrueWidth N r : ℂ)^(-s)
  have hi := (gamma0CuspFourierDirichletRaw_summable N r a n s hs).mul_left z
  apply hi.congr
  intro c
  have h := cuspScattering_normalized_width_power s (gamma0CuspTrueWidth N r : ℝ)
    (gamma0CuspTrueWidth N a : ℝ) (c.val : ℝ)
    (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r))
    (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N a)) (Nat.cast_pos.mpr c.property)
  have hp : z*(c.val : ℂ)^(-2*s) =
      (gamma0TrueWidthModulus N r a (c.val : ℝ) : ℂ)^(-2*s) := by
    simpa only [z,Complex.ofReal_natCast,gamma0TrueWidthModulus] using h
  rw [← hp]
  ring


theorem gamma0CuspFourierDirichlet_summable_norm (N : ℕ) [NeZero N]
    (r a : SL(2, ℤ)) (n : ℤ) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun c : {c : ℕ // 0 < c} => ‖gamma0TrueWidthKloostermanSum N r a c.val n 0*
      (gamma0TrueWidthModulus N r a (c.val : ℝ) : ℂ)^(-2*s)‖) := by
  let z : ℂ := (gamma0CuspTrueWidth N a : ℂ)^(-s)*(gamma0CuspTrueWidth N r : ℂ)^(-s)
  have hi := (gamma0CuspFourierDirichletRaw_summable_norm N r a n s hs).mul_left ‖z‖
  apply hi.congr
  intro c
  have h := cuspScattering_normalized_width_power s (gamma0CuspTrueWidth N r : ℝ)
    (gamma0CuspTrueWidth N a : ℝ) (c.val : ℝ)
    (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r))
    (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N a)) (Nat.cast_pos.mpr c.property)
  have hp : z*(c.val : ℂ)^(-2*s) =
      (gamma0TrueWidthModulus N r a (c.val : ℝ) : ℂ)^(-2*s) := by
    simpa only [z,Complex.ofReal_natCast,gamma0TrueWidthModulus] using h
  have he : z*(gamma0TrueWidthKloostermanSum N r a c.val n 0*(c.val : ℂ)^(-2*s)) =
      gamma0TrueWidthKloostermanSum N r a c.val n 0*
        (gamma0TrueWidthModulus N r a (c.val : ℝ) : ℂ)^(-2*s) := by
    rw [← hp]
    ring
  exact (norm_mul z _).symm.trans (congrArg norm he)

end ArtinMatthews

