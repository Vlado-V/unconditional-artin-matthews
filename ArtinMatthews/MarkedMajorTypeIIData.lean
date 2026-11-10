module

public import ArtinMatthews.MarkedMajorTypeIIParameters
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual arithmetic endpoint data for the prescribed prime bands. The
pointwise scalar β bound is exactly the bound stated in PD03 Type II. -/
namespace ArtinMatthews
open Finset
noncomputable section

 def markedMajorTypeIIData {J : Type} [Fintype J]
    (δ C A : ℝ) (hδ : 0 < δ) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (e : Option J → ℝ) (L H U u v Y modulation : ℝ) (l r : ℕ) (β : ℕ → ℂ)
    (hL : 1 ≤ L)
    (hdis : Pairwise (fun i j => Disjoint (markedLogPowerBand (e i) (Real.exp L)) (markedLogPowerBand (e j) (Real.exp L))))
    (hprime : ∀ i p,p ∈ markedLogPowerBand (e i) (Real.exp L) → p.Prime ∧
      L^(1/(10:ℝ)) ≤ Real.log p ∧ Real.log p ≤ 2*L^(1/(5:ℝ)))
    (hmass : ∀ i,Real.log 2/2 ≤ bandReciprocalMass (markedLogPowerBand (e i) (Real.exp L)))
    (hY : 0 < Y) (hH : Real.exp ((δ/2)*L) ≤ H) (hU : Real.exp ((δ/2)*L) ≤ U)
    (hHu : H ≤ u) (huv : u ≤ v) (hvH : v ≤ 2*H) (hvhi : v ≤ Real.exp (2*L))
    (hl : U ≤ (l:ℝ)) (hr : (r:ℝ) ≤ 2*U)
    (hβ : ∀ n ∈ Icc l r,‖β n‖ ≤ L^C) (hmod : |modulation| ≤ L^C) :
    MarkedMajorLabelEnergyData J (markedMajorTypeIIConfig δ C A hδ hC hA) L (H*U) where
  P₀ := markedLogPowerBand (e none) (Real.exp L)
  bands := fun j => markedLogPowerBand (e (some j)) (Real.exp L)
  first_prime := fun p hp => (hprime none p hp).1
  bands_prime := fun j p hp => (hprime (some j) p hp).1
  first_disjoint := fun _ => hdis (by simp)
  bands_disjoint := fun i j hij => hdis (by simpa only [ne_eq,Option.some.injEq] using hij)
  first_mass := hmass none
  bands_mass := fun j => (half_pos (Real.log_pos (by norm_num : (1:ℝ)<2))).trans_le (hmass (some j))
  first_lower := fun p hp => by simpa only [markedMajorTypeIIConfig,one_mul] using (hprime none p hp).2.1
  first_upper := fun p hp => (hprime none p hp).2.2
  Y := Y
  θ := 0
  H := H
  u := u
  v := v
  U := U
  l := l
  r := r
  β := β
  Y_pos := hY
  theta_bound := by
    change |(0:ℝ)| ≤ 2*L^A
    rw [abs_zero]
    positivity
  H_lower := hH
  H_le_u := hHu
  u_le_v := huv
  v_le_two_H := hvH
  v_upper := hvhi
  U_lower := hU
  U_le_l := hl
  r_le_two_U := hr
  product_eq := rfl
  coefficient_bound := hβ
  q := 1
  k := 1
  q_ne_zero := one_ne_zero
  χ := 1
  χb := 1
  modulation := modulation
  modulus_bound := by simpa only [markedMajorTypeIIConfig,Nat.cast_one] using Real.one_le_rpow hL hA
  modulation_bound := hmod

 theorem markedMajorTypeIIData_allBands {J : Type} [Fintype J]
    (δ C A : ℝ) (hδ : 0 < δ) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (e : Option J → ℝ) (L H U u v Y modulation : ℝ) (l r : ℕ) (β : ℕ → ℂ)
    (hL : 1 ≤ L)
    (hdis : Pairwise (fun i j => Disjoint (markedLogPowerBand (e i) (Real.exp L)) (markedLogPowerBand (e j) (Real.exp L))))
    (hprime : ∀ i p,p ∈ markedLogPowerBand (e i) (Real.exp L) → p.Prime ∧
      L^(1/(10:ℝ)) ≤ Real.log p ∧ Real.log p ≤ 2*L^(1/(5:ℝ)))
    (hmass : ∀ i,Real.log 2/2 ≤ bandReciprocalMass (markedLogPowerBand (e i) (Real.exp L)))
    (hY : 0 < Y) (hH : Real.exp ((δ/2)*L) ≤ H) (hU : Real.exp ((δ/2)*L) ≤ U)
    (hHu : H ≤ u) (huv : u ≤ v) (hvH : v ≤ 2*H) (hvhi : v ≤ Real.exp (2*L))
    (hl : U ≤ (l:ℝ)) (hr : (r:ℝ) ≤ 2*U)
    (hβ : ∀ n ∈ Icc l r,‖β n‖ ≤ L^C) (hmod : |modulation| ≤ L^C) :
    (markedMajorTypeIIData δ C A hδ hC hA e L H U u v Y modulation l r β hL
      hdis hprime hmass hY hH hU hHu huv hvH hvhi hl hr hβ hmod).allBands =
      fun j => markedLogPowerBand (e j) (Real.exp L) := by
  funext j
  cases j <;> rfl

end
end ArtinMatthews
