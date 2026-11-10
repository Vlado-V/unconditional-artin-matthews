module

public import ArtinMatthews.DoubleVoronoiResidueWeight
public import ArtinMatthews.KloostermanWeightedStationary
public import ArtinMatthews.DoubleVoronoiIntegralRestriction
public import ArtinMatthews.ShiftedVoronoiNumerators
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


set_option backward.privateInPublic true
@[expose] public section

/-! Exact elimination of the residual d-congruence from the complete
Kloosterman sum. The result has the full D=d*r congruence from the paper. -/
namespace ArtinMatthews
open OAI.Erdos970.ErdosKloosterman
open OAI.Erdos970.ErdosKloosterman.PrimePower
noncomputable section
attribute [local instance] Classical.decEq

/-- Complete finite sum identity underlying (5.9). Its only arithmetic
factorization data are D=d*r, m3-m4=r*A0 and gcd(d,m3*A0)=1. -/
theorem doubleVoronoi_weighted_complete_sum {q d r : ℕ} [NeZero q]
    (hq : 0<q) (hQ : (d*r)^2∣q) (hr : r≠0)
    (m₃ m₄ k₁ k₂ A₀ : ℤ)
    (hfactor : m₃-m₄=(r : ℤ)*A₀) (hcop : IsCoprime (d : ℤ) (m₃*A₀))
    (v₃ v₄ : (ZMod q)ˣ)
    (h₃ : (v₃ : ZMod q)=(m₃ : ZMod q))
    (h₄ : (v₄ : ZMod q)=(m₄ : ZMod q)) :
    let hDq : d*r∣q := (dvd_pow_self (d*r) (by decide : 2≠0)).trans hQ
    let hdq : d∣q := (dvd_mul_right d r).trans hDq
    weightedKloosterman ZMod.stdAddChar
      (doubleVoronoiResidueWeight (ZMod.castHom hdq (ZMod d)) (m₄ : ZMod q) k₁)
      ((v₃ : ZMod q)-(v₄ : ZMod q))
      ((↑(v₃*v₄)⁻¹ : ZMod q)*((v₄ : ZMod q)*k₂-(v₃ : ZMod q)*k₁)) =
    (if Int.ModEq ((d : ℤ)*(r : ℤ)) (m₃^2*k₁) (m₄^2*k₂) then 1 else 0) *
      sum ZMod.stdAddChar ((v₃ : ZMod q)-(v₄ : ZMod q))
        ((↑(v₃*v₄)⁻¹ : ZMod q)*((v₄ : ZMod q)*k₂-(v₃ : ZMod q)*k₁)) := by
  intro hDq hdq
  have hD : 0<d*r := Nat.pos_of_dvd_of_pos hDq hq
  have hquotD : d*r∣q/(d*r) :=
    (Nat.dvd_div_iff_mul_dvd hDq).mpr (by simpa only [pow_two] using hQ)
  have hquot : d∣q/(d*r) := (dvd_mul_right d r).trans hquotD
  have hnil : (((q/(d*r) : ℕ) : ZMod q))^2=0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    exact div_square_dvd_of_square_dvd hD hQ
  apply weightedKloosterman_eq_scalar _ (ZMod.isPrimitive_stdAddChar q) _ _ _ _ hnil
  · intro u z
    exact doubleVoronoiResidueWeight_quotient_shift hdq hquot _ _ u z _
  · intro u hu
    exact doubleVoronoi_weight_on_stationary hq hdq hDq hr m₃ m₄ k₁ k₂ A₀
      hfactor hcop v₃ v₄ u h₃ h₄ hu

end
end ArtinMatthews
