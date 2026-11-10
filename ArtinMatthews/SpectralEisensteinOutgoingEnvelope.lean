module

public import ArtinMatthews.SpectralEisensteinCompactProfile
public import ArtinMatthews.SpectralEisensteinOutgoingApproximation
public import ArtinMatthews.SpectralEisensteinHighProfiles
public import ArtinMatthews.SpectralEisensteinOutgoingDerivative
public import ArtinMatthews.SpectralEisensteinOutgoingGerms
public import ArtinMatthews.SpectralEisensteinProfileMajorants
public import ArtinMatthews.SpectralModularPowerTailL2
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! A single genuine ambient-L² majorant for the literal outgoing mode and
its actual compact approximants. Its tail is a width-scaled height power. -/
noncomputable section
open Set Filter Topology MeasureTheory
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

def eisensteinOutgoingProfile (q : ℂ) (n : ℕ) : ℝ → ℂ :=
  eisensteinOutgoingApprox q (((n+1:ℕ):ℝ)⁻¹)

theorem eisensteinOutgoingProfile_smooth (q : ℂ) (n : ℕ) :
    ContDiff ℝ ∞ (eisensteinOutgoingProfile q n) :=
  eisensteinOutgoingApprox_smooth q _

theorem eisensteinOutgoingProfile_compact (q : ℂ) (n : ℕ) :
    HasCompactSupport (eisensteinOutgoingProfile q n) :=
  eisensteinOutgoingApprox_compact q (by positivity)

theorem eisensteinOutgoingProfile_positive_support (q : ℂ) (n : ℕ) :
    tsupport (eisensteinOutgoingProfile q n) ⊆ Ioi (0:ℝ) :=
  eisensteinOutgoingApprox_positive_support q (by positivity)

def gamma0CuspOutgoingEnvelope (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (q : ℂ)
    (z : UpperHalfPlane) : ℝ :=
  ‖gamma0CuspHeightProfile N a (fun t => (eisensteinOutgoingEnvelopeProfile q t:ℂ)) z‖

theorem gamma0CuspOutgoingEnvelope_nonneg (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (q : ℂ)
    (z : UpperHalfPlane) : 0≤gamma0CuspOutgoingEnvelope N a q z := norm_nonneg _

theorem gamma0CuspOutgoingEnvelope_continuous (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (q : ℂ) : Continuous (gamma0CuspOutgoingEnvelope N a q) :=
  (gamma0CuspHeightProfile_continuous_of_zero_low N a _
    (Complex.continuous_ofReal.comp (eisensteinOutgoingEnvelopeProfile_continuous q))
    zero_lt_one (fun t ht => by simp only [Function.comp_apply,eisensteinOutgoingEnvelopeProfile_zero q ht,
      Complex.ofReal_zero])).norm

theorem gamma0CuspOutgoingEnvelope_memLp (N : ℕ) [NeZero N] (a r : SL(2,ℤ))
    (q : ℂ) (hq : q.re<1/2) :
    MemLp (fun z : UpperHalfPlane => gamma0CuspOutgoingEnvelope N a q (r⁻¹ • z)) 2
      (volume.restrict ModularGroup.fd) := by
  let w : ℝ := gamma0CuspTrueWidth N r
  have hw : 0<w := by dsimp [w];exact_mod_cast gamma0CuspTrueWidth_pos N r
  apply continuous_memLp_modular_of_power_tail _ (gamma0CuspOutgoingEnvelope_continuous N a q) r
    (2*w) (w^q.re)⁻¹ (by positivity) (by positivity) q hq
  intro z _ hz
  have hz1 : w≤z.im := by linarith
  have hz2 : 2<z.im/w := (lt_div_iff₀ hw).mpr hz
  unfold gamma0CuspOutgoingEnvelope
  rw [gamma0CuspHeightProfile_raw_high N r a _ (fun t ht => by
    simp only [eisensteinOutgoingEnvelopeProfile_zero q ht,Complex.ofReal_zero]) z hz1]
  change ‖‖gamma0CuspEisensteinIndicator N r a*(eisensteinOutgoingEnvelopeProfile q (z.im/w):ℂ)‖‖≤_
  rw [eisensteinOutgoingEnvelopeProfile_high q hz2,Real.norm_of_nonneg (norm_nonneg _)]
  by_cases h : gamma0EisensteinCuspsEquivalent N r a
  · rw [gamma0CuspEisensteinIndicator,ite_eq_left h,one_mul,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _),
      Complex.norm_cpow_eq_rpow_re_of_pos (div_pos z.im_pos hw),
      Complex.norm_cpow_eq_rpow_re_of_pos z.im_pos,Real.div_rpow z.im_pos.le hw.le,div_eq_mul_inv,mul_comm]
  · rw [gamma0CuspEisensteinIndicator,ite_eq_right h,zero_mul,norm_zero]
    positivity

theorem gamma0CuspOutgoingApprox_norm_le (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (q : ℂ) (n : ℕ) (z : UpperHalfPlane) :
    ‖gamma0CuspHeightProfile N a (eisensteinOutgoingProfile q n) z‖ ≤
      gamma0CuspOutgoingEnvelope N a q z :=
  gamma0CuspHeightProfile_norm_le_of_majorant N a _ _
    (eisensteinOutgoingEnvelopeProfile_nonneg q) zero_lt_one
    (fun _ ht => eisensteinOutgoingApprox_zero_low q _ ht)
    (fun _ ht => eisensteinOutgoingEnvelopeProfile_zero q ht)
    (fun t _ => eisensteinOutgoingApprox_norm_le_envelope q _ t) z

theorem gamma0CuspOutgoingApprox_gradient_norm_le (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (q : ℂ) (n : ℕ) {M : ℝ} (hM : 0≤M)
    (hb : ∀ t : ℝ, |t*deriv eisensteinHeightCutoff t|≤M) (z : UpperHalfPlane) :
    ‖h2SectionGradient (gamma0CuspHeightProfile N a (eisensteinOutgoingProfile q n)) z‖ ≤
      (1+M+‖q‖)*gamma0CuspOutgoingEnvelope N a q z :=
  gamma0CuspHeightProfile_gradient_norm_le_of_majorant N a _ (eisensteinOutgoingProfile_smooth q n) _
    (eisensteinOutgoingEnvelopeProfile_nonneg q) zero_lt_one
    (fun _ ht => eisensteinOutgoingApprox_zero_low q _ ht)
    (fun _ ht => eisensteinOutgoingEnvelopeProfile_zero q ht)
    (fun t ht => eisensteinOutgoingApprox_weighted_deriv_le q _ t M hM hb ht) z

theorem gamma0CuspOutgoingCutoff_norm_le (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (q : ℂ) (z : UpperHalfPlane) :
    ‖gamma0CuspEisensteinCutoff N a q z‖≤gamma0CuspOutgoingEnvelope N a q z := by
  obtain ⟨n,hn⟩ := (gamma0CuspOutgoingApprox_eventually_value N a q z).exists
  rw [← hn]
  exact gamma0CuspOutgoingApprox_norm_le N a q n z

theorem gamma0CuspOutgoingCutoff_gradient_norm_le (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (q : ℂ) {M : ℝ} (hM : 0≤M)
    (hb : ∀ t : ℝ, |t*deriv eisensteinHeightCutoff t|≤M) (z : UpperHalfPlane) :
    ‖h2SectionGradient (gamma0CuspEisensteinCutoff N a q) z‖≤
      (1+M+‖q‖)*gamma0CuspOutgoingEnvelope N a q z := by
  obtain ⟨n,hn⟩ := (gamma0CuspOutgoingApprox_eventually_gradient N a q z).exists
  rw [← hn]
  exact gamma0CuspOutgoingApprox_gradient_norm_le N a q n hM hb z

end ArtinMatthews
