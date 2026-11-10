module

public import ArtinMatthews.SpectralEisensteinCutoffSmooth
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
public import ArtinMatthews.SpectralEisensteinPowerBounds
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Genuine compact row majorants for the first two spatial derivatives, still for Re(s)>1. -/
noncomputable section
open Set
open scoped ContDiff MatrixGroups
namespace ArtinMatthews


def cuspEisensteinRowPlaneSum (N : ℕ) (r₀ a₀ : SL(2,ℤ)) (s : ℂ) (p : ℝ×ℝ) : ℂ :=
  (1/2:ℂ)*∑' v : Gamma0CuspEisensteinRows N r₀ a₀, cuspEisensteinRowPlaneTerm N r₀ a₀ s v p

theorem cuspEisensteinRowPlaneTerm_contDiffOn (N : ℕ) (r₀ a₀ : SL(2,ℤ)) (s : ℂ)
    (v : Gamma0CuspEisensteinRows N r₀ a₀) :
    ContDiffOn ℝ ∞ (cuspEisensteinRowPlaneTerm N r₀ a₀ s v) {p : ℝ×ℝ | 0 < p.2} :=
  eisensteinRowPower_contDiffOn s _ _ (cuspEisensteinRow_coefficients_ne_zero N r₀ a₀ v)

def cuspEisensteinRowMajorant (N : ℕ) (r₀ a₀ : SL(2,ℤ)) (s : ℂ) (A a b : ℝ) (ha : 0<a)
    (v : Gamma0CuspEisensteinRows N r₀ a₀) : ℝ :=
  (b^s.re*(EisensteinSeries.r ⟨⟨A,a⟩,ha⟩)^(-(2*s.re)))*‖v.val‖^(-(2*s.re))

theorem cuspEisensteinRowMajorant_summable (N : ℕ) (r₀ a₀ : SL(2,ℤ)) (s : ℂ) (hs : 1<s.re)
    (A a b : ℝ) (ha : 0<a) : Summable (cuspEisensteinRowMajorant N r₀ a₀ s A a b ha) :=
  ((EisensteinSeries.summable_one_div_norm_rpow (show 2<2*s.re by linarith)).subtype
    (fun v => v ∈ Set.range (gamma0CuspEisensteinRow N r₀ a₀))).mul_left _

theorem cuspEisensteinRowPlaneTerm_majorant (N : ℕ) (r₀ a₀ : SL(2,ℤ)) (s : ℂ) (hs : 1<s.re)
    (A a b : ℝ) (ha : 0<a) (hab : a≤b) (v : Gamma0CuspEisensteinRows N r₀ a₀)
    (p : ℝ × ℝ) (hp : |p.1|≤A ∧ a≤p.2 ∧ p.2≤b) :
    ‖cuspEisensteinRowPlaneTerm N r₀ a₀ s v p‖ ≤ cuspEisensteinRowMajorant N r₀ a₀ s A a b ha v := by
  have hpy : 0<p.2 := ha.trans_le hp.2.1
  let z : UpperHalfPlane := ⟨⟨p.1,p.2⟩,hpy⟩
  have hz : z ∈ UpperHalfPlane.verticalStrip A a := ⟨hp.1,hp.2.1⟩
  rw [cuspEisensteinRowPlaneTerm_eq N r₀ a₀ s v p hpy,cuspEisensteinRowTerm_norm]
  have hd := EisensteinSeries.summand_bound_of_mem_verticalStrip
    (show 0≤2*s.re by linarith) v.val ha hz
  have hy : p.2^s.re ≤ b^s.re := Real.rpow_le_rpow hpy.le hp.2.2 (by linarith)
  exact (mul_le_mul hy hd (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (ha.trans_le hab).le _)).trans_eq
    (mul_assoc _ _ _).symm

theorem cuspEisensteinRowPlaneTerm_derivative_majorants (N : ℕ) (r₀ a₀ : SL(2,ℤ)) (s : ℂ) (hs : 1<s.re)
    (A a b : ℝ) (ha : 0<a) (hab : a≤b) (v : Gamma0CuspEisensteinRows N r₀ a₀)
    (p : ℝ × ℝ) (hp : |p.1|≤A ∧ a≤p.2 ∧ p.2≤b) :
    ‖fderiv ℝ (cuspEisensteinRowPlaneTerm N r₀ a₀ s v) p‖ ≤
        (5*‖s‖/a)*cuspEisensteinRowMajorant N r₀ a₀ s A a b ha v ∧
    ‖fderiv ℝ (fderiv ℝ (cuspEisensteinRowPlaneTerm N r₀ a₀ s v)) p‖ ≤
        ((50*‖s‖^2+42*‖s‖)/a^2)*cuspEisensteinRowMajorant N r₀ a₀ s A a b ha v := by
  have hpy : 0<p.2 := ha.trans_le hp.2.1
  have hf := cuspEisensteinRowPlaneTerm_majorant N r₀ a₀ s hs A a b ha hab v p hp
  have hcd := cuspEisensteinRow_coefficients_ne_zero N r₀ a₀ v
  have h1 := eisensteinRowPower_fderiv_bound s (v.val 0) (v.val 1) hcd p hpy
  have h2 := eisensteinRowPower_second_bound s (v.val 0) (v.val 1) hcd p hpy
  have hden1 : 5*‖s‖/p.2 ≤ 5*‖s‖/a := div_le_div_of_nonneg_left (by positivity) ha hp.2.1
  have hden2 : (50*‖s‖^2+42*‖s‖)/p.2^2 ≤ (50*‖s‖^2+42*‖s‖)/a^2 :=
    div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos ha) (pow_le_pow_left₀ ha.le hp.2.1 2)
  constructor
  · exact h1.trans (mul_le_mul hden1 hf (norm_nonneg _) (by positivity))
  · exact h2.trans (mul_le_mul hden2 hf (norm_nonneg _) (by positivity))

end ArtinMatthews
