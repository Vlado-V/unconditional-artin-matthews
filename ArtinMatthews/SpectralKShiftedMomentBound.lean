module

public import ArtinMatthews.SpectralKShiftedMoment
public import ArtinMatthews.SpectralKSquareMellinMoment
public import ArtinMatthews.SpectralKShiftedMomentRatio
public import ArtinMatthews.SpectralKSquareMomentRecurrence
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
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

/-! Polynomial spectral growth of the actual shifted K square moments,
with the exact hyperbolic-cosine normalization. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

theorem spectralKSquareMoment_nonneg (k : ℕ) (t : ℝ) : 0 ≤ spectralKSquareMoment k t := by
  unfold spectralKSquareMoment
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change (0 : ℝ) ≤ x^(2*k)*(spectralKLRealKernel t x)^2
  exact mul_nonneg (pow_nonneg hx.le _) (sq_nonneg _)

theorem spectralKSquareMoment_succ_bound (k : ℕ) (t : ℝ) :
    spectralKSquareMoment (k+1) t ≤
      ((k : ℝ)+1)^2*(1+t^2)*spectralKSquareMoment k t := by
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hd : 0 < (2*(k : ℝ)+1)*(2*(k : ℝ)+2) := by positivity
  have hr : 4*((k : ℝ)+1/2)^2/((2*(k : ℝ)+1)*(2*(k : ℝ)+2)) ≤ 1 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith
  have hp : ((k : ℝ)+1/2)^2+t^2 ≤ ((k : ℝ)+1)^2*(1+t^2) := by
    have h1 : 1 ≤ ((k : ℝ)+1)^2 := by nlinarith
    have ht := mul_le_mul_of_nonneg_right h1 (sq_nonneg t)
    nlinarith
  rw [spectralKSquareMoment_succ]
  apply mul_le_mul_of_nonneg_right _ (spectralKSquareMoment_nonneg k t)
  calc
    _ = (4*((k : ℝ)+1/2)^2/((2*(k : ℝ)+1)*(2*(k : ℝ)+2)))*(((k : ℝ)+1/2)^2+t^2) := by ring
    _ ≤ ((k : ℝ)+1/2)^2+t^2 := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hr (by positivity : 0 ≤ ((k : ℝ)+1/2)^2+t^2)
    _ ≤ _ := hp

theorem spectralKSquareMoment_polynomial_bound (k : ℕ) (t : ℝ) :
    spectralKSquareMoment k t ≤
      (k.factorial : ℝ)^2*(1+t^2)^k*spectralKSquareMoment 0 t := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      _ ≤ ((k : ℝ)+1)^2*(1+t^2)*spectralKSquareMoment k t := spectralKSquareMoment_succ_bound k t
      _ ≤ ((k : ℝ)+1)^2*(1+t^2)*((k.factorial : ℝ)^2*(1+t^2)^k*spectralKSquareMoment 0 t) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ = _ := by rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ];ring

theorem spectralKShiftedMoment_uniform_bound (k : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hBk : B < (k : ℝ)+1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ t : ℝ, |δ| ≤ B →
      spectralKShiftedMoment k δ t ≤ C*(1+t^2)^k/Real.cosh (Real.pi*t) := by
  obtain ⟨R,hR,hbound⟩ := spectralKShiftedMomentRatio_bound k B hB hBk
  refine ⟨R*(k.factorial : ℝ)^2*Real.pi^2/4,by positivity,?_⟩
  intro δ t hδ
  rw [spectralKShiftedMoment_eq_ratio k δ t (hδ.trans_lt hBk)]
  calc
    _ ≤ R*spectralKSquareMoment k t :=
      mul_le_mul_of_nonneg_right (hbound δ hδ) (spectralKSquareMoment_nonneg k t)
    _ ≤ R*((k.factorial : ℝ)^2*(1+t^2)^k*spectralKSquareMoment 0 t) :=
      mul_le_mul_of_nonneg_left (spectralKSquareMoment_polynomial_bound k t) hR.le
    _ = _ := by rw [spectralKSquareMoment_zero];ring

end ArtinMatthews
