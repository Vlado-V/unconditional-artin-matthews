module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The exact positive-horizontal-coordinate to second-height substitution.
This is the square-root Jacobian in the two-height orbital kernel. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

def weylSecondHeight (c y x : ℝ) : ℝ := y/(c^2*(x^2+y^2))

def weylHeightRoot (c y v : ℝ) : ℝ := Real.sqrt (y/(c^2*v)-y^2)

def weylHeightJacobian (c y v : ℝ) : ℝ := y/(2*c^2*v^2*weylHeightRoot c y v)

theorem weylHeightRoot_radicand_pos {c y v : ℝ} (hc : c ≠ 0) (hy : 0 < y)
    (hv : v ∈ Ioo 0 (1/(c^2*y))) : 0 < y/(c^2*v)-y^2 := by
  have hc2 : 0 < c^2 := sq_pos_of_ne_zero hc
  have hp : 0 < c^2*y := mul_pos hc2 hy
  have hlt : v*(c^2*y) < 1 := (lt_div_iff₀ hp).mp hv.2
  have hd : 0 < c^2*v := mul_pos hc2 hv.1
  have he : y^2*(c^2*v) < y := by nlinarith [mul_lt_mul_of_pos_left hlt hy]
  exact sub_pos.mpr ((lt_div_iff₀ hd).mpr he)

theorem weylHeightRoot_pos {c y v : ℝ} (hc : c ≠ 0) (hy : 0 < y)
    (hv : v ∈ Ioo 0 (1/(c^2*y))) : 0 < weylHeightRoot c y v :=
  Real.sqrt_pos.mpr (weylHeightRoot_radicand_pos hc hy hv)

theorem weylSecondHeight_mem {c y x : ℝ} (hc : c ≠ 0) (hy : 0 < y) (hx : 0 < x) :
    weylSecondHeight c y x ∈ Ioo 0 (1/(c^2*y)) := by
  have hc2 : 0 < c^2 := sq_pos_of_ne_zero hc
  have hd : 0 < c^2*(x^2+y^2) := mul_pos hc2 (by positivity)
  constructor
  · exact div_pos hy hd
  · unfold weylSecondHeight
    apply (div_lt_div_iff₀ hd (mul_pos hc2 hy)).mpr
    nlinarith [mul_pos hc2 (sq_pos_of_pos hx)]

theorem weylSecondHeight_heightRoot {c y v : ℝ} (hc : c ≠ 0) (hy : 0 < y)
    (hv : v ∈ Ioo 0 (1/(c^2*y))) :
    weylSecondHeight c y (weylHeightRoot c y v) = v := by
  have hr := Real.sq_sqrt (weylHeightRoot_radicand_pos hc hy hv).le
  have hv0 := hv.1.ne'
  unfold weylSecondHeight weylHeightRoot
  rw [hr]
  field_simp [hc,hv0]
  ring

theorem weylHeightRoot_secondHeight {c y x : ℝ} (hc : c ≠ 0) (hy : 0 < y) (hx : 0 < x) :
    weylHeightRoot c y (weylSecondHeight c y x) = x := by
  have hy0 := hy.ne'
  have hd : x^2+y^2 ≠ 0 := (show 0 < x^2+y^2 by positivity).ne'
  unfold weylSecondHeight weylHeightRoot
  have he : y/(c^2*(y/(c^2*(x^2+y^2))))-y^2 = x^2 := by
    field_simp [hc,hy0,hd]
    ring
  rw [he,Real.sqrt_sq hx.le]

theorem weylHeightRoot_image {c y : ℝ} (hc : c ≠ 0) (hy : 0 < y) :
    weylHeightRoot c y '' Ioo 0 (1/(c^2*y)) = Ioi 0 := by
  ext x
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact weylHeightRoot_pos hc hy hv
  · intro hx
    exact ⟨weylSecondHeight c y x,weylSecondHeight_mem hc hy hx,
      weylHeightRoot_secondHeight hc hy hx⟩

theorem weylHeightRoot_injOn {c y : ℝ} (hc : c ≠ 0) (hy : 0 < y) :
    InjOn (weylHeightRoot c y) (Ioo 0 (1/(c^2*y))) := by
  intro v hv w hw he
  have h := congrArg (weylSecondHeight c y) he
  rwa [weylSecondHeight_heightRoot hc hy hv,weylSecondHeight_heightRoot hc hy hw] at h

theorem weylHeightRoot_hasDerivAt {c y v : ℝ} (hc : c ≠ 0) (hy : 0 < y)
    (hv : v ∈ Ioo 0 (1/(c^2*y))) :
    HasDerivAt (weylHeightRoot c y) (-weylHeightJacobian c y v) v := by
  have harg := weylHeightRoot_radicand_pos hc hy hv
  have hv0 := hv.1.ne'
  have hr0 := (weylHeightRoot_pos hc hy hv).ne'
  have hd := ((hasDerivAt_const v y).div
    ((hasDerivAt_id v).const_mul (c^2)) (mul_ne_zero (pow_ne_zero 2 hc) hv0)).sub_const (y^2)
  have hs := (Real.hasDerivAt_sqrt harg.ne').comp v hd
  simp only [id_eq] at hs
  convert hs using 1
  · unfold weylHeightRoot
    rfl
  · unfold weylHeightJacobian weylHeightRoot at *
    field_simp [hc,hv0,hr0]
    ring

theorem weylHeightJacobian_pos {c y v : ℝ} (hc : c ≠ 0) (hy : 0 < y)
    (hv : v ∈ Ioo 0 (1/(c^2*y))) : 0 < weylHeightJacobian c y v := by
  unfold weylHeightJacobian
  exact div_pos hy (mul_pos (mul_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero hc))
    (sq_pos_of_pos hv.1)) (weylHeightRoot_pos hc hy hv))

theorem weylHeight_integral_substitution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c y : ℝ} (hc : c ≠ 0) (hy : 0 < y) (F : ℝ → E) :
    (∫ x in Ioi (0 : ℝ), F x) =
      ∫ v in Ioo 0 (1/(c^2*y)), weylHeightJacobian c y v • F (weylHeightRoot c y v) := by
  rw [← weylHeightRoot_image hc hy]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun v hv => (weylHeightRoot_hasDerivAt hc hy hv).hasDerivWithinAt)
    (weylHeightRoot_injOn hc hy)]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro v hv
  dsimp only
  rw [abs_neg,abs_of_pos (weylHeightJacobian_pos hc hy hv)]

theorem weylHeight_integrable_substitution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c y : ℝ} (hc : c ≠ 0) (hy : 0 < y) (F : ℝ → E) :
    IntegrableOn F (Ioi (0 : ℝ)) ↔
      IntegrableOn (fun v => weylHeightJacobian c y v • F (weylHeightRoot c y v))
        (Ioo 0 (1/(c^2*y))) := by
  rw [← weylHeightRoot_image hc hy]
  rw [integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun v hv => (weylHeightRoot_hasDerivAt hc hy hv).hasDerivWithinAt)
    (weylHeightRoot_injOn hc hy)]
  apply integrableOn_congr_fun
  · intro v hv
    dsimp only
    rw [abs_neg,abs_of_pos (weylHeightJacobian_pos hc hy hv)]
  · exact measurableSet_Ioo

end ArtinMatthews
