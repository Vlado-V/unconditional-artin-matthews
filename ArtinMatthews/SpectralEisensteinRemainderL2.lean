module

public import ArtinMatthews.SpectralCuspEisensteinConstantTerm
public import ArtinMatthews.SpectralEisensteinHeightCutoff
public import ArtinMatthews.SpectralGamma0Core
public import ArtinMatthews.SpectralCuspBruhatKernel
public import ArtinMatthews.SpectralCuspEisensteinParabolic
public import ArtinMatthews.SpectralEisensteinCutoffAtCusps
public import ArtinMatthews.SpectralEisensteinCutoffRegularity
public import ArtinMatthews.SpectralModularTailBoundedL2
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual truncated Eisenstein remainder belongs to the full ambient
mass space on every translated modular region. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace ArtinMatthews

theorem cuspWidthDilation_re_inv_smul (w : ℝ) (hw : 0 < w) (z : UpperHalfPlane) :
    ((cuspWidthDilation w hw)⁻¹ • z).re=z.re/w := by
  have h := cuspWidthDilation_re_smul w hw ((cuspWidthDilation w hw)⁻¹ • z)
  rw [smul_inv_smul] at h
  apply (eq_div_iff hw.ne').mpr
  rw [mul_comm]
  exact h.symm

theorem gamma0CuspEisensteinRemainder_modular_tail_bound (N : ℕ) [NeZero N]
    (a r : SL(2,ℤ)) (s : ℂ) (hs : 1 < s.re) (z : UpperHalfPlane)
    (hz : z ∈ ModularGroup.fd) (hhigh : 2*(gamma0CuspTrueWidth N r:ℝ) ≤ z.im) :
    ‖gamma0CuspEisensteinRemainder N a s (r⁻¹ • z)‖ ≤
      9^s.re*‖gamma0CuspScattering N r a (s.re:ℂ)‖ := by
  let w : ℝ := gamma0CuspTrueWidth N r
  have hw1 : 1 ≤ w := by
    dsimp [w]
    exact_mod_cast (show (1:ℕ) ≤ gamma0CuspTrueWidth N r from gamma0CuspTrueWidth_pos N r)
  have hw : 0 < w := lt_of_lt_of_le zero_lt_one hw1
  let p : UpperHalfPlane := (cuspWidthDilation w hw)⁻¹ • z
  have him : p.im=z.im/w := cuspWidthDilation_im_inv_smul w hw z
  have hre : p.re=z.re/w := cuspWidthDilation_re_inv_smul w hw z
  have hp2 : 2 ≤ p.im := by rw [him]; exact (le_div_iff₀ hw).mpr hhigh
  have hpx : |p.re| ≤ 1 := by
    rw [hre,abs_div,abs_of_pos hw]
    apply (div_le_one hw).mpr
    exact hz.2.trans (by linarith)
  have he : gamma0TrueCuspScaling N r • p=r⁻¹ • z := by
    dsimp [p,w]
    rw [gamma0TrueCuspScaling,mul_smul,smul_inv_smul,← map_inv]
    exact atkinRealMap_smul r⁻¹ z
  have hp : gamma0EisensteinHorizontalPoint p.im p.im_pos p.re=p := by
    apply UpperHalfPlane.ext
    apply Complex.ext <;> rfl
  have heq := gamma0CuspEisensteinRemainder_high_cusp N r a s hs p.re p.im hp2
  rw [hp,he] at heq
  rw [heq]
  have hd := gamma0CuspEisensteinPositivePart_decay N r a s hs p.re p.im (by linarith) hpx
  have hpow : p.im^(1-s.re) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  apply hd.trans
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow (show 0 ≤ 9^s.re by positivity))
    (norm_nonneg (gamma0CuspScattering N r a (s.re:ℂ)))
  simpa only [mul_one] using h

theorem gamma0CuspEisensteinRemainder_memLp_modularRegion (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (hs : 1 < s.re) (r : SL(2,ℤ)) :
    MemLp (fun z : UpperHalfPlane => gamma0CuspEisensteinRemainder N a s (r⁻¹ • z)) 2
      (volume.restrict ModularGroup.fd) :=
  continuous_memLp_modular_of_tail_bound _ (gamma0CuspEisensteinRemainder_continuous N a s hs)
    r (2*(gamma0CuspTrueWidth N r:ℝ)) (9^s.re*‖gamma0CuspScattering N r a (s.re:ℂ)‖)
    (fun z hz hhigh => gamma0CuspEisensteinRemainder_modular_tail_bound N a r s hs z hz hhigh)

def gamma0CuspEisensteinRemainderMass (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) : Gamma0RegionL2 N :=
  WithLp.toLp 2 (fun q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N =>
    (gamma0CuspEisensteinRemainder_memLp_modularRegion N a s hs q.out).toLp _)

theorem gamma0CuspEisensteinRemainderMass_ae (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) (q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    (gamma0CuspEisensteinRemainderMass N a s hs q : UpperHalfPlane → ℂ)=ᵐ[volume.restrict ModularGroup.fd]
      (fun z => gamma0CuspEisensteinRemainder N a s (q.out⁻¹ • z)) :=
  (gamma0CuspEisensteinRemainder_memLp_modularRegion N a s hs q.out).coeFn_toLp

end ArtinMatthews
