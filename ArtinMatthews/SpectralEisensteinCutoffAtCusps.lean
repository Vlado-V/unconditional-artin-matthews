module

public import ArtinMatthews.SpectralEisensteinPositiveDecay
public import ArtinMatthews.SpectralEisensteinHeightCutoff
public import ArtinMatthews.SpectralCuspBruhatKernel
public import ArtinMatthews.SpectralCuspEisensteinAutomorphy
public import ArtinMatthews.SpectralEisensteinCutoffCuspHeight
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual target-cusp expansion of the cutoff and actual decay of the
truncated Eisenstein remainder. No resolvent agreement is assumed. -/
noncomputable section
open Set Matrix
open scoped MatrixGroups
namespace ArtinMatthews

theorem cuspEisensteinNormalizedHeight_reindex (N : ℕ) [NeZero N] (r t a : SL(2,ℤ))
    (v : Gamma0CuspEisensteinRows N r a) (z : UpperHalfPlane) :
    cuspEisensteinNormalizedHeight N t a (gamma0CuspEisensteinRowReindexEquiv N r t a v) z=
      cuspEisensteinNormalizedHeight N r a v ((r*t⁻¹:SL(2,ℤ)) • z) := by
  unfold cuspEisensteinNormalizedHeight
  rw [cuspEisensteinRowHeight_reindex]

theorem cuspEisensteinCutoffTerm_reindex (N : ℕ) [NeZero N] (r t a : SL(2,ℤ))
    (s : ℂ) (v : Gamma0CuspEisensteinRows N r a) (z : UpperHalfPlane) :
    cuspEisensteinCutoffTerm N t a s (gamma0CuspEisensteinRowReindexEquiv N r t a v) z=
      cuspEisensteinCutoffTerm N r a s v ((r*t⁻¹:SL(2,ℤ)) • z) := by
  unfold cuspEisensteinCutoffTerm
  rw [cuspEisensteinNormalizedHeight_reindex]

theorem gamma0CuspEisensteinCutoff_target (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (z : UpperHalfPlane) :
    gamma0CuspEisensteinCutoff N a s (gamma0TrueCuspScaling N r • z)=
      (1/2:ℂ)*∑' v : Gamma0CuspEisensteinRows N r a,
        cuspEisensteinCutoffTerm N r a s v
          (cuspWidthDilation (gamma0CuspTrueWidth N r:ℝ)
            (by exact_mod_cast gamma0CuspTrueWidth_pos N r) • z) := by
  unfold gamma0CuspEisensteinCutoff gamma0TrueCuspScaling
  rw [mul_smul,← map_inv,atkinRealMap_smul]
  congr 1
  have he := (gamma0CuspEisensteinRowReindexEquiv N 1 r a).tsum_eq
    (fun v => cuspEisensteinCutoffTerm N r a s v
      (cuspWidthDilation (gamma0CuspTrueWidth N r:ℝ)
        (by exact_mod_cast gamma0CuspTrueWidth_pos N r) • z))
  simpa only [cuspEisensteinCutoffTerm_reindex,one_mul] using he

theorem cuspEisensteinNormalizedHeight_neg (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (v : Gamma0CuspEisensteinRows N r a) (z : UpperHalfPlane) :
    cuspEisensteinNormalizedHeight N r a (gamma0CuspEisensteinNegRow N r a v) z=
      cuspEisensteinNormalizedHeight N r a v z := by
  simp only [cuspEisensteinNormalizedHeight,cuspEisensteinRowHeight_row,
    gamma0CuspEisensteinNegRow,Pi.neg_apply,Int.cast_neg,neg_mul,← neg_add,norm_neg]

theorem gamma0CuspEisensteinCutoff_high_cusp (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) (x y : ℝ) (hy : 2 ≤ y) :
    gamma0CuspEisensteinCutoff N a s
      (gamma0TrueCuspScaling N r • gamma0EisensteinHorizontalPoint y
        (lt_of_lt_of_le (by norm_num : (0:ℝ)<2) hy) x)=
      gamma0CuspEisensteinIndicator N r a*(y:ℂ)^s := by
  classical
  let py := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) hy
  rw [gamma0CuspEisensteinCutoff_target]
  change (1/2:ℂ)*(∑' v : Gamma0CuspEisensteinRows N r a,
    cuspEisensteinCutoffTerm N r a s v (cuspEisensteinTargetPoint N r y py x))=_
  rw [cuspEisenstein_signed_tsum N r a _
    (cuspEisensteinCutoffTerm_summable_norm N r a s hs _).of_norm
    (fun v => by simp only [cuspEisensteinCutoffTerm,cuspEisensteinNormalizedHeight_neg])]
  have hp : (∑' v : CuspEisensteinPositiveRows N r a,
      cuspEisensteinCutoffTerm N r a s v.val (cuspEisensteinTargetPoint N r y py x))=0 := by
    have hf (v : CuspEisensteinPositiveRows N r a) :
        cuspEisensteinCutoffTerm N r a s v.val (cuspEisensteinTargetPoint N r y py x)=0 :=
      cuspEisensteinCutoffTerm_nonzero_row_zero N r a s v.val v.property.ne' x y (by linarith)
    simp only [hf,tsum_zero]
  rw [hp,mul_zero,add_zero]
  simp_rw [cuspEisensteinCutoffTerm_zero_row N r a s _ x y hy]
  rw [tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,cuspEisensteinZeroRows_card]
  by_cases h : gamma0EisensteinCuspsEquivalent N r a <;>
    simp [h,gamma0CuspEisensteinIndicator]

theorem cuspEisensteinZeroRow_point_eq_integral (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (v : CuspEisensteinZeroRows N r a) (x y : ℝ) (hy : 0 < y) :
    cuspEisensteinRowTerm N r a s v.val (cuspEisensteinTargetPoint N r y hy x)=
      cuspEisensteinRowIntegral N r a s y hy v.val := by
  rw [cuspEisensteinRowTerm_zero,cuspEisensteinRowIntegral_zero]
  have him : (cuspEisensteinTargetPoint N r y hy x).im=(gamma0CuspTrueWidth N r:ℝ)*y :=
    cuspWidthDilation_im_smul _ _ _
  rw [him,Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by positivity) hy.le]
  rfl

theorem gamma0CuspEisenstein_pointwise_positive_part (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) (x y : ℝ) (hy : 0 < y) :
    gamma0CuspEisenstein N a s (gamma0TrueCuspScaling N r • gamma0EisensteinHorizontalPoint y hy x)=
      gamma0CuspEisensteinIndicator N r a*(y:ℂ)^s+gamma0CuspEisensteinPositivePart N r a s y hy x := by
  rw [gamma0CuspEisenstein_target_scaling]
  unfold cuspEisensteinRowSum
  change (gamma0CuspTrueWidth N a:ℂ)^(-s)*((1/2:ℂ)*
    ∑' v : Gamma0CuspEisensteinRows N r a, cuspEisensteinRowTerm N r a s v
      (cuspEisensteinTargetPoint N r y hy x))=_
  rw [cuspEisenstein_signed_tsum N r a _ (cuspEisensteinRowTerm_summable N r a s hs _)
    (fun v => cuspEisensteinRowTerm_neg N r a s v _)]
  simp_rw [cuspEisensteinZeroRow_point_eq_integral N r a s _ x y hy]
  calc
    _=(gamma0CuspTrueWidth N a:ℂ)^(-s)*(1/2:ℂ)*
        (∑' v : CuspEisensteinZeroRows N r a,cuspEisensteinRowIntegral N r a s y hy v.val)+
      gamma0CuspEisensteinPositivePart N r a s y hy x := by
      unfold gamma0CuspEisensteinPositivePart
      ring
    _=_ := by rw [gamma0CuspEisenstein_leading_constant]

theorem gamma0CuspEisensteinRemainder_high_cusp (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) (x y : ℝ) (hy : 2 ≤ y) :
    gamma0CuspEisensteinRemainder N a s
      (gamma0TrueCuspScaling N r • gamma0EisensteinHorizontalPoint y
        (lt_of_lt_of_le (by norm_num : (0:ℝ)<2) hy) x)=
      gamma0CuspEisensteinPositivePart N r a s y
        (lt_of_lt_of_le (by norm_num : (0:ℝ)<2) hy) x := by
  unfold gamma0CuspEisensteinRemainder
  rw [gamma0CuspEisenstein_pointwise_positive_part N r a s hs,
    gamma0CuspEisensteinCutoff_high_cusp N r a s hs x y hy,add_sub_cancel_left]

end ArtinMatthews
