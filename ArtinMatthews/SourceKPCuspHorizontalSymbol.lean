module

public import ArtinMatthews.SourceKPCuspTraceFunctional
public import ArtinMatthews.SourceWeightedSquareAMGM
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Product-formula coercivity of the genuine horizontal Fourier symbol. -/
namespace ArtinMatthews
open NumberField Module Module.Free
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] (d : 𝓞 K)

def sourceKPCuspFrequencyFloor : ℝ :=
  1 / (|(NumberField.discr K : ℝ)| * (Ideal.absNorm (Ideal.span {d}) : ℝ))

theorem sourceKPCuspFrequencyFloor_pos (hd : d ≠ 0) : 0 < sourceKPCuspFrequencyFloor K d := by
  have hD : 0 < |(NumberField.discr K : ℝ)| := abs_pos.mpr (by
    exact_mod_cast NumberField.discr_ne_zero K)
  have hM : (Ideal.span {d} : Ideal (𝓞 K)) ≠ ⊥ := by simpa using hd
  have hN : 0 < (Ideal.absNorm (Ideal.span {d}) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hM)
  exact one_div_pos.mpr (mul_pos hD hN)

variable [IsTotallyComplex K]

def sourceKPCuspHorizontalSymbol (ξ : K) (y : InfinitePlace K → ℝ) : ℝ :=
  ∑ v, y v ^ 2 * ∑ k : Fin 2,
    ‖(2 * (Real.pi : ℂ) * Complex.I) *
      (sourceKPCuspTraceFunctional K ξ (sourceKPCuspHorizontalDirection K v k) : ℂ)‖ ^ 2

theorem sourceKPCuspHorizontalSymbol_place (ξ : K) (v : InfinitePlace K) :
    (∑ k : Fin 2, ‖(2 * (Real.pi : ℂ) * Complex.I) *
      (sourceKPCuspTraceFunctional K ξ (sourceKPCuspHorizontalDirection K v k) : ℂ)‖ ^ 2) =
      (4 * Real.pi) ^ 2 * ‖v.embedding ξ‖ ^ 2 := by
  rw [Fin.sum_univ_two, sourceKPCuspTraceFunctional_horizontal_zero,
    sourceKPCuspTraceFunctional_horizontal_one]
  simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
    abs_of_pos Real.pi_pos, mul_one, mul_pow, sq_abs, neg_sq]
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem sourceKPCuspHorizontalSymbol_eq (ξ : K) (y : InfinitePlace K → ℝ) :
    sourceKPCuspHorizontalSymbol K ξ y =
      (4 * Real.pi) ^ 2 * ∑ v, (y v * ‖v.embedding ξ‖) ^ 2 := by
  simp only [sourceKPCuspHorizontalSymbol, sourceKPCuspHorizontalSymbol_place,
    Finset.mul_sum, mul_pow]
  apply Finset.sum_congr rfl
  intro v _
  ring

def sourceKPCuspHorizontalGap (y : InfinitePlace K → ℝ) : ℝ :=
  (4 * Real.pi) ^ 2 * (Fintype.card (InfinitePlace K) : ℝ) *
    ((∏ v, y v ^ 2) * sourceKPCuspFrequencyFloor K d) ^
      (1 / (Fintype.card (InfinitePlace K) : ℝ))

def sourceKPCuspHorizontalGapConstant : ℝ :=
  (4 * Real.pi) ^ 2 * (Fintype.card (InfinitePlace K) : ℝ) *
    (sourceKPCuspFrequencyFloor K d) ^ (1 / (Fintype.card (InfinitePlace K) : ℝ))

omit [IsTotallyComplex K] in
theorem sourceKPCuspHorizontalGapConstant_pos (hd : d ≠ 0) :
    0 < sourceKPCuspHorizontalGapConstant K d := by
  unfold sourceKPCuspHorizontalGapConstant
  exact mul_pos (mul_pos (sq_pos_of_pos (by positivity))
    (by exact_mod_cast Fintype.card_pos))
    (Real.rpow_pos_of_pos (sourceKPCuspFrequencyFloor_pos K d hd) _)

theorem sourceKPCuspHorizontalGap_height (y : InfinitePlace K → ℝ) :
    sourceKPCuspHorizontalGap K d y = sourceKPCuspHorizontalGapConstant K d *
      (∏ v, y v ^ 2) ^ (1 / (InfinitePlace.nrComplexPlaces K : ℝ)) := by
  have hc : Fintype.card (InfinitePlace K) = InfinitePlace.nrComplexPlaces K := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  have hN : 0 ≤ sourceKPCuspFrequencyFloor K d := by
    unfold sourceKPCuspFrequencyFloor
    positivity
  rw [sourceKPCuspHorizontalGap, Real.mul_rpow
    (Finset.prod_nonneg (fun v _ => sq_nonneg (y v))) hN]
  simp only [sourceKPCuspHorizontalGapConstant, hc]
  ring

theorem sourceKPCuspHorizontalSymbol_lower (hd : d ≠ 0)
    (y : InfinitePlace K → ℝ) (hy : ∀ v, 0 < y v)
    {n : ChooseBasisIndex ℤ (𝓞 K) → ℤ} (hn : n ≠ 0) :
    sourceKPCuspHorizontalGap K d y ≤
      sourceKPCuspHorizontalSymbol K (sourceKPCuspTraceFrequency K d n) y := by
  have h := sourceFinite_weighted_square_amgm y
    (fun v => ‖v.embedding (sourceKPCuspTraceFrequency K d n)‖)
    (sourceKPCuspFrequencyFloor K d) hy (fun _ => norm_nonneg _)
    (sourceKPCuspFrequencyFloor_pos K d hd)
    (sourceKPCuspTraceFrequency_product_lower K d hd hn)
  rw [sourceKPCuspHorizontalSymbol_eq]
  simpa only [sourceKPCuspHorizontalGap, mul_assoc] using
    mul_le_mul_of_nonneg_left h (sq_nonneg (4 * Real.pi))

end
end ArtinMatthews
