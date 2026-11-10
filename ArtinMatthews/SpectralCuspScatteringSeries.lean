module

public import ArtinMatthews.SpectralCuspEisensteinResidueRows
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.PSeries
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual convergent all-cusp scattering Dirichlet coefficients count
parabolic orbits of actual matrices. No scattering identity is stipulated. -/
noncomputable section
open scoped MatrixGroups
namespace ArtinMatthews

def gamma0CuspScatteringCount (N : ℕ) [NeZero N] (r a : SL(2,ℤ)) (c : ℕ) : ℕ :=
  Fintype.card (CuspEisensteinRowResidues N r a c)

theorem gamma0CuspScatteringCount_le (N : ℕ) [NeZero N] (r a : SL(2,ℤ)) (c : ℕ) :
    gamma0CuspScatteringCount N r a c ≤ gamma0CuspTrueWidth N r*c := by
  have h := Fintype.card_le_of_injective
    (fun d : CuspEisensteinRowResidues N r a c => d.val) Subtype.coe_injective
  simpa only [gamma0CuspScatteringCount,Fintype.card_fin] using h

def gamma0CuspScatteringDirichlet (N : ℕ) [NeZero N] (r a : SL(2,ℤ)) (s : ℂ) : ℂ :=
  ∑' c : {c : ℕ // 0 < c}, (gamma0CuspScatteringCount N r a c.val:ℂ)*(c.val:ℂ)^(-2*s)

theorem gamma0CuspScatteringTerm_norm_bound (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (c : {c : ℕ // 0 < c}) :
    ‖(gamma0CuspScatteringCount N r a c.val:ℂ)*(c.val:ℂ)^(-2*s)‖ ≤
      (gamma0CuspTrueWidth N r:ℝ)*(c.val:ℝ)^(1-2*s.re) := by
  have hc : 0 < (c.val:ℝ) := by exact_mod_cast c.property
  rw [norm_mul,Complex.norm_natCast,Complex.norm_natCast_cpow_of_pos c.property]
  have hre : (-2*s).re= -2*s.re := by simp
  rw [hre]
  calc
    _ ≤ ((gamma0CuspTrueWidth N r:ℝ)*c.val)*(c.val:ℝ)^(-2*s.re) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast gamma0CuspScatteringCount_le N r a c.val)
        (Real.rpow_nonneg hc.le _)
    _ = (gamma0CuspTrueWidth N r:ℝ)*((c.val:ℝ)^(1:ℝ)*(c.val:ℝ)^(-2*s.re)) := by
      rw [Real.rpow_one,mul_assoc]
    _ = _ := by rw [← Real.rpow_add hc]; congr 2; ring

theorem gamma0CuspScatteringDirichlet_summable_norm (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun c : {c : ℕ // 0 < c} =>
      ‖(gamma0CuspScatteringCount N r a c.val:ℂ)*(c.val:ℂ)^(-2*s)‖) :=
  (((Real.summable_nat_rpow.mpr (by linarith : 1-2*s.re < -1)).subtype
    (fun c : ℕ => 0 < c)).mul_left (gamma0CuspTrueWidth N r:ℝ)).of_nonneg_of_le
      (fun _ => norm_nonneg _) (gamma0CuspScatteringTerm_norm_bound N r a s)

theorem gamma0CuspScatteringDirichlet_summable (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun c : {c : ℕ // 0 < c} =>
      (gamma0CuspScatteringCount N r a c.val:ℂ)*(c.val:ℂ)^(-2*s)) :=
  (gamma0CuspScatteringDirichlet_summable_norm N r a s hs).of_norm

end ArtinMatthews
