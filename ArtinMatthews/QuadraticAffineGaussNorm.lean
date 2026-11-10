module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Analysis.Complex.Norm
public import ArtinMatthews.TameQuadraticGauss
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.RingTheory.Henselian
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

/-! Genuine quadratic cancellation, including an arbitrary linear coefficient. -/
noncomputable section
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.FiniteFourier
namespace ArtinMatthews.PrimePowerWeil

variable {F : Type*} [Field F] [Fintype F]

theorem quadraticGauss_norm (hF : ringChar F≠2) (ψ : AddChar F ℂ) (hψ : ψ≠1)
    {a : F} (ha : a≠0) :
    ‖∑ x : F, ψ (a*x^2)‖=Real.sqrt (Fintype.card F) := by
  have hχ : ‖QuadraticGauss.residueCharacter F a‖=1 := by
    have h := congrArg norm (QuadraticGauss.residueCharacter_sq ha)
    simp only [norm_pow,norm_one] at h
    nlinarith [norm_nonneg (QuadraticGauss.residueCharacter F a)]
  have hq : 0<(Fintype.card F:ℝ) := by exact_mod_cast Fintype.card_pos (α := F)
  have hG := QuadraticGauss.residueIndex_norm hF ψ hψ
  unfold QuadraticGauss.residueIndex ProbeGauss.normalizedGauss at hG
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] at hG
  have hg := (div_eq_one_iff_eq (Real.sqrt_ne_zero'.mpr hq)).mp hG
  rw [QuadraticGauss.square_sum_scaled hF ψ hψ ha,norm_mul,hχ,hg,one_mul]

theorem quadraticAffineGauss_norm (hF : ringChar F≠2) (h2 : (2:F)≠0)
    (ψ : AddChar F ℂ) (hψ : ψ≠1) {a : F} (ha : a≠0) (b : F) :
    ‖∑ x : F, ψ (a*x^2+b*x)‖=Real.sqrt (Fintype.card F) := by
  classical
  let c := b/(2*a)
  have hc : 2*a*c=b := by dsimp [c]; field_simp
  have hpoly (x : F) : a*(x+c)^2=(a*x^2+b*x)+a*c^2 := by
    linear_combination x*hc
  have he : (∑ x : F, ψ (a*x^2))=(∑ x : F, ψ (a*x^2+b*x))*ψ (a*c^2) := by
    rw [← Equiv.sum_comp (Equiv.addRight c) (fun x : F => ψ (a*x^2))]
    change (∑ x : F, ψ (a*(x+c)^2))=_
    simp_rw [hpoly,AddChar.map_add_eq_mul]
    rw [Finset.sum_mul]
  have hn := congrArg norm he
  rw [norm_mul,AddChar.norm_apply,mul_one] at hn
  exact hn.symm.trans (quadraticGauss_norm hF ψ hψ ha)

end ArtinMatthews.PrimePowerWeil
