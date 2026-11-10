module

public import ArtinMatthews.SourceQuadraticB2Base
public import ArtinMatthews.SourceQuadraticHeckeSymbols
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The literal annular row cutoff, its finite support, and the exact
full-minus-small parity decomposition used before Poisson summation. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "χ" => sourceReflectionQuadraticSymbol F S₀ hζ

theorem sourceQuadraticBlock_symbol_mask (d g : E) :
    ((‖χ d g‖ ^ 2 : ℝ) : ℂ) =
      if Disjoint d.support g.support then 1 else 0 := by
  by_cases hd : Disjoint d.support g.support
  · rw [ite_eq_left hd]
    have hnorm : ‖χ d g‖ = 1 := sourceReflectionQuadraticSymbol_norm_eq_one F S₀ hζ d g hd
    rw [hnorm]
    norm_num
  · rw [ite_eq_right hd]
    have hz : χ d g = 0 := by
      by_contra hn
      exact hd ((sourceReflectionQuadraticSymbol_ne_zero_iff F S₀ hζ d g).mp hn)
    rw [hz, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), Complex.ofReal_zero]

theorem sourceQuadraticB2RowWeight_support {M : ℝ} (hM : 0 < M) (d : E)
    (hd : sourceQuadraticB2RowWeight F S₀ M d ≠ 0) :
    M/2 ≤ (q d : ℝ) ∧ (q d : ℝ) ≤ 5*M/2 := by
  have hs : (q d : ℝ)/M ∈ tsupport sourceQuadraticB2Bump :=
    subset_closure (show (q d : ℝ)/M ∈ Function.support sourceQuadraticB2Bump from hd)
  have hh := sourceQuadraticB2Bump_tsupport hs
  constructor
  · have h := (le_div_iff₀ hM).mp hh.1
    linarith
  · have h := (div_le_iff₀ hM).mp hh.2
    linarith

theorem sourceQuadraticB2RowWeight_zero_of_not_mem {M K : ℝ} (hM : 0 < M)
    (d : E) (hpar : K < (q (sourceReflectionParity d) : ℝ))
    (hd : d ∉ sourceQuadraticB2Rows F S₀ M K) :
    sourceQuadraticB2RowWeight F S₀ M d = 0 := by
  by_contra hw
  have hs := sourceQuadraticB2RowWeight_support F S₀ hM d hw
  exact hd ((sourceQuadratic_mem_B2Rows F S₀ hM.le d).mpr ⟨hs.2,hs.1,hpar⟩)

/-- Multiplication by the actual bump has finite support for any coefficient. -/
theorem sourceQuadraticB2RowWeight_summable {M : ℝ} (hM : 0 < M) (f : E → ℂ) :
    Summable (fun d => (sourceQuadraticB2RowWeight F S₀ M d : ℂ)*f d) := by
  apply summable_of_ne_finset_zero (s := sourceReflectionBoundedExponents F S₀ (5*M/2))
  intro d hd
  have hw : sourceQuadraticB2RowWeight F S₀ M d = 0 := by
    by_contra hn
    have hs := sourceQuadraticB2RowWeight_support F S₀ hM d hn
    exact hd ((sourceReflection_mem_boundedExponents F S₀ (by positivity) d).mpr hs.2)
  rw [hw, Complex.ofReal_zero, zero_mul]

/-- Extend the finite row sum without changing its original parity cutoff. -/
theorem sourceQuadraticB2Rows_sum_eq_tsum {M K : ℝ} (hM : 0 < M) (f : E → ℂ) :
    (∑ d ∈ sourceQuadraticB2Rows F S₀ M K,
      (sourceQuadraticB2RowWeight F S₀ M d : ℂ)*f d) =
      ∑' d : E, if K < (q (sourceReflectionParity d) : ℝ) then
        (sourceQuadraticB2RowWeight F S₀ M d : ℂ)*f d else 0 := by
  rw [tsum_eq_sum (s := sourceQuadraticB2Rows F S₀ M K) (fun d hd => ?_)]
  · apply Finset.sum_congr rfl
    intro d hd
    rw [ite_eq_left ((sourceQuadratic_mem_B2Rows F S₀ hM.le d).mp hd).2.2]
  · by_cases hp : K < (q (sourceReflectionParity d) : ℝ)
    · rw [ite_eq_left hp, sourceQuadraticB2RowWeight_zero_of_not_mem F S₀ hM d hp hd,
        Complex.ofReal_zero, zero_mul]
    · rw [ite_eq_right hp]

/-- The retained rows are exactly the full compactly supported sum minus
its original small-squarefree-part cutoff. -/
theorem sourceQuadraticB2Rows_sum_eq_full_sub_small {M K : ℝ}
    (hM : 0 < M) (f : E → ℂ) :
    (∑ d ∈ sourceQuadraticB2Rows F S₀ M K,
      (sourceQuadraticB2RowWeight F S₀ M d : ℂ)*f d) =
      (∑' d : E, (sourceQuadraticB2RowWeight F S₀ M d : ℂ)*f d) -
        ∑' d : E, if (q (sourceReflectionParity d) : ℝ) ≤ K then
          (sourceQuadraticB2RowWeight F S₀ M d : ℂ)*f d else 0 := by
  have hfull := sourceQuadraticB2RowWeight_summable F S₀ hM f
  have hsmall : Summable (fun d : E => if (q (sourceReflectionParity d) : ℝ) ≤ K then
      (sourceQuadraticB2RowWeight F S₀ M d : ℂ)*f d else 0) := by
    exact hfull.indicator {d | (q (sourceReflectionParity d) : ℝ) ≤ K}
  rw [sourceQuadraticB2Rows_sum_eq_tsum F S₀ hM f, ← hfull.tsum_sub hsmall]
  apply tsum_congr
  intro d
  by_cases hp : (q (sourceReflectionParity d) : ℝ) ≤ K
  · simp [hp]
  · simp [hp]

def sourceQuadraticBlockRowKernel (rows : Finset E) (w : E → ℝ) (g e : E) : ℂ :=
  ∑ d ∈ rows, if Disjoint d.support g.support then (w d : ℂ)*χ d e else 0

theorem sourceQuadraticBlockRowKernel_eq_full_sub_small {M K : ℝ} (hM : 0 < M)
    (g e : E) :
    sourceQuadraticBlockRowKernel F S₀ hζ (sourceQuadraticB2Rows F S₀ M K)
        (sourceQuadraticB2RowWeight F S₀ M) g e =
      (∑' d : E, if Disjoint d.support g.support then
        (sourceQuadraticB2RowWeight F S₀ M d : ℂ)*χ d e else 0) -
      ∑' d : E, if Disjoint d.support g.support ∧ (q (sourceReflectionParity d) : ℝ) ≤ K then
        (sourceQuadraticB2RowWeight F S₀ M d : ℂ)*χ d e else 0 := by
  have h := sourceQuadraticB2Rows_sum_eq_full_sub_small F S₀ (K := K) hM
    (fun d => if Disjoint d.support g.support then χ d e else 0)
  simp only [mul_ite, mul_zero] at h
  have hcomm (d : E) :
      (if (q (sourceReflectionParity d) : ℝ) ≤ K then
        (if Disjoint d.support g.support then
          (sourceQuadraticB2RowWeight F S₀ M d : ℂ)*χ d e else 0) else 0) =
      (if Disjoint d.support g.support ∧ (q (sourceReflectionParity d) : ℝ) ≤ K then
        (sourceQuadraticB2RowWeight F S₀ M d : ℂ)*χ d e else 0) := by
    by_cases hp : (q (sourceReflectionParity d) : ℝ) ≤ K <;>
      by_cases hd : Disjoint d.support g.support <;> simp [hp, hd]
  simp_rw [hcomm] at h
  exact h

end
end ArtinMatthews.SourceEulerAssembly
