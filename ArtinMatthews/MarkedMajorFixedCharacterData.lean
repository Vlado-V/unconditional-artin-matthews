module

public import ArtinMatthews.MarkedMajorMellinLabelEnergyData
public import ArtinMatthews.HeckeDirichletProduct
public import ArtinMatthews.MarkedTypeIIFourier
public import ArtinMatthews.MarkedMajorCharacterSource
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual fixed-character rational-arc data. The fixed modulus costs
one eventual logarithmic exponent, and no analytic field is added. -/
namespace ArtinMatthews
open Finset Filter
noncomputable section

def markedMajorFixedCharacterConfig (cfg : MarkedMajorLabelEnergyConfig) : MarkedMajorLabelEnergyConfig :=
  { cfg with a := cfg.a+1,ha := by linarith [cfg.ha] }

theorem markedMajor_fixed_product_modulus {L a : ℝ} (hL : 0<L) (M q : ℕ)
    (hM : (M:ℝ) ≤ L) (hq : (q:ℝ) ≤ L^a) : (M*q:ℕ) ≤ L^(a+1) := by
  have hh := mul_le_mul hM hq (Nat.cast_nonneg q) hL.le
  simpa only [Nat.cast_mul,Real.rpow_add hL,Real.rpow_one,mul_comm] using hh

namespace MarkedMajorLabelEnergyData
variable {J : Type} {cfg : MarkedMajorLabelEnergyConfig} {L X : ℝ}

def fixedCharacterLeft (z : MarkedMajorLabelEnergyData J cfg L X)
    {M : ℕ} [NeZero M] (ξ : DirichletCharacter ℂ M)
    (hL : 0<L) (hM : (M:ℝ) ≤ L) (q : ℕ) [NeZero q]
    (χ : AddChar (MarkedUnitTuple q) ℂ) (θ : ℝ)
    (hq : (q:ℝ) ≤ L^cfg.a) (hθ : |θ| ≤ cfg.Kθ*L^cfg.A₀) :
    MarkedMajorLabelEnergyData J (markedMajorFixedCharacterConfig cfg) L X where
  P₀ := z.P₀
  bands := z.bands
  first_prime := z.first_prime
  bands_prime := z.bands_prime
  first_disjoint := z.first_disjoint
  bands_disjoint := z.bands_disjoint
  first_mass := z.first_mass
  bands_mass := z.bands_mass
  first_lower := z.first_lower
  first_upper := z.first_upper
  Y := z.Y
  θ := θ
  H := z.H
  u := z.u
  v := z.v
  U := z.U
  l := z.l
  r := z.r
  β := fun n => ξ n*(z.β n*markedCoordinateDirichlet q χ 3 n)
  Y_pos := z.Y_pos
  theta_bound := hθ
  H_lower := z.H_lower
  H_le_u := z.H_le_u
  u_le_v := z.u_le_v
  v_le_two_H := z.v_le_two_H
  v_upper := z.v_upper
  U_lower := z.U_lower
  U_le_l := z.U_le_l
  r_le_two_U := z.r_le_two_U
  product_eq := z.product_eq
  coefficient_bound := fun n hn => by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (ξ.norm_le_one n)).trans
      (markedMajor_character_twisted_coefficient_bound z.β _ n (z.coefficient_bound n hn))
  q := M*q
  k := q
  q_ne_zero := Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne q)
  χ := heckeDirichletProduct ξ (markedCoordinateDirichlet q χ 2)
  χb := markedCoordinateDirichlet q χ 1
  modulation := z.modulation
  modulus_bound := markedMajor_fixed_product_modulus hL M q hM hq
  modulation_bound := z.modulation_bound

def fixedCharacterRight (z : MarkedMajorLabelEnergyData J cfg L X)
    {M : ℕ} [NeZero M] (ξ : DirichletCharacter ℂ M)
    (hL : 0<L) (hM : (M:ℝ) ≤ L) (q : ℕ) [NeZero q]
    (χ : AddChar (MarkedUnitTuple q) ℂ) (θ : ℝ)
    (hq : (q:ℝ) ≤ L^cfg.a) (hθ : |θ| ≤ cfg.Kθ*L^cfg.A₀) :
    MarkedMajorLabelEnergyData J (markedMajorFixedCharacterConfig cfg) L X where
  P₀ := z.P₀
  bands := z.bands
  first_prime := z.first_prime
  bands_prime := z.bands_prime
  first_disjoint := z.first_disjoint
  bands_disjoint := z.bands_disjoint
  first_mass := z.first_mass
  bands_mass := z.bands_mass
  first_lower := z.first_lower
  first_upper := z.first_upper
  Y := z.Y
  θ := -θ
  H := z.H
  u := z.u
  v := z.v
  U := z.U
  l := z.l
  r := z.r
  β := fun n => ξ n*(z.β n*markedCoordinateDirichlet q χ 5 n)
  Y_pos := z.Y_pos
  theta_bound := by
    change |-θ| ≤ cfg.Kθ*L^cfg.A₀
    simpa only [abs_neg] using hθ
  H_lower := z.H_lower
  H_le_u := z.H_le_u
  u_le_v := z.u_le_v
  v_le_two_H := z.v_le_two_H
  v_upper := z.v_upper
  U_lower := z.U_lower
  U_le_l := z.U_le_l
  r_le_two_U := z.r_le_two_U
  product_eq := z.product_eq
  coefficient_bound := fun n hn => by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (ξ.norm_le_one n)).trans
      (markedMajor_character_twisted_coefficient_bound z.β _ n (z.coefficient_bound n hn))
  q := M*q
  k := q
  q_ne_zero := Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne q)
  χ := heckeDirichletProduct ξ (markedCoordinateDirichlet q χ 4)
  χb := markedCoordinateDirichlet q χ 0
  modulation := z.modulation
  modulus_bound := markedMajor_fixed_product_modulus hL M q hM hq
  modulation_bound := z.modulation_bound

theorem fixedCharacterLeft_allBands (z : MarkedMajorLabelEnergyData J cfg L X)
    {M : ℕ} [NeZero M] (ξ : DirichletCharacter ℂ M)
    (hL : 0<L) (hM : (M:ℝ) ≤ L) (q : ℕ) [NeZero q]
    (χ : AddChar (MarkedUnitTuple q) ℂ) (θ : ℝ)
    (hq : (q:ℝ) ≤ L^cfg.a) (hθ : |θ| ≤ cfg.Kθ*L^cfg.A₀) :
    (z.fixedCharacterLeft ξ hL hM q χ θ hq hθ).allBands=z.allBands := rfl

theorem fixedCharacterRight_allBands (z : MarkedMajorLabelEnergyData J cfg L X)
    {M : ℕ} [NeZero M] (ξ : DirichletCharacter ℂ M)
    (hL : 0<L) (hM : (M:ℝ) ≤ L) (q : ℕ) [NeZero q]
    (χ : AddChar (MarkedUnitTuple q) ℂ) (θ : ℝ)
    (hq : (q:ℝ) ≤ L^cfg.a) (hθ : |θ| ≤ cfg.Kθ*L^cfg.A₀) :
    (z.fixedCharacterRight ξ hL hM q χ θ hq hθ).allBands=z.allBands := rfl

end MarkedMajorLabelEnergyData
end
end ArtinMatthews
