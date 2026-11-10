module

public import ArtinMatthews.DoubleVoronoiResidueWeight
public import OAI.NumberTheory.Jacobsthal.Harmonic.StationaryPhase
public import ArtinMatthews.DoubleVoronoiStationaryPhase
public import ArtinMatthews.KloostermanStationaryCongruence
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


set_option backward.privateInPublic true
@[expose] public section

/-! The stationary square-residue weight is the exact D-congruence
indicator, with integer source coefficients retained. -/
namespace ArtinMatthews
open OAI.Erdos970.ErdosKloosterman.PrimePower
noncomputable section
attribute [local instance] Classical.decEq

/-- Integral form of the actual finite-ring stationary equation. -/
theorem doubleVoronoi_stationary_int {q D : ℕ} [NeZero q]
    (hq : 0<q) (hDq : D∣q) (m₃ m₄ k₁ k₂ a : ℤ)
    (v₃ v₄ u : (ZMod q)ˣ)
    (h₃ : (v₃ : ZMod q)=(m₃ : ZMod q))
    (h₄ : (v₄ : ZMod q)=(m₄ : ZMod q))
    (hu : (u : ZMod q)=(a : ZMod q))
    (hs : u ∈ stationaryUnits ((q/D : ℕ) : ZMod q)
      ((v₃ : ZMod q)-(v₄ : ZMod q))
      ((↑(v₃*v₄)⁻¹ : ZMod q)*((v₄ : ZMod q)*k₂-(v₃ : ZMod q)*k₁))) :
    Int.ModEq (D : ℤ) ((m₃-m₄)*m₃*m₄*a^2) (m₄*k₂-m₃*k₁) := by
  have h := (doubleVoronoi_stationary_support hq hDq v₃ v₄ u
    (k₁ : ZMod q) (k₂ : ZMod q)).mp hs
  dsimp only at h
  rw [h₃, h₄, hu] at h
  simp only [map_intCast] at h
  apply (ZMod.intCast_eq_intCast_iff _ _ D).mp
  simpa only [Int.cast_sub, Int.cast_mul, Int.cast_pow] using h

/-- On the actual stationary support, the d-residue restriction equals
 the D=d*r restriction on the dual Fourier coefficients. -/
theorem doubleVoronoi_weight_on_stationary {q d r : ℕ} [NeZero q]
    (hq : 0<q) (hdq : d∣q) (hDq : d*r∣q) (hr : r≠0)
    (m₃ m₄ k₁ k₂ A₀ : ℤ)
    (hfactor : m₃-m₄=(r : ℤ)*A₀) (hcop : IsCoprime (d : ℤ) (m₃*A₀))
    (v₃ v₄ u : (ZMod q)ˣ)
    (h₃ : (v₃ : ZMod q)=(m₃ : ZMod q))
    (h₄ : (v₄ : ZMod q)=(m₄ : ZMod q))
    (hs : u ∈ stationaryUnits ((q/(d*r) : ℕ) : ZMod q)
      ((v₃ : ZMod q)-(v₄ : ZMod q))
      ((↑(v₃*v₄)⁻¹ : ZMod q)*((v₄ : ZMod q)*k₂-(v₃ : ZMod q)*k₁))) :
    doubleVoronoiResidueWeight (ZMod.castHom hdq (ZMod d)) (m₄ : ZMod q) k₁ u =
      if Int.ModEq ((d : ℤ)*(r : ℤ)) (m₃^2*k₁) (m₄^2*k₂) then 1 else 0 := by
  let a : ℤ := (u : ZMod q).val
  have hu : (u : ZMod q)=(a : ZMod q) := by
    simp only [a, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hstat := doubleVoronoi_stationary_int hq hDq m₃ m₄ k₁ k₂ a v₃ v₄ u h₃ h₄ hu hs
  have heq := doubleVoronoi_stationary_congruence (d : ℤ) (r : ℤ) m₃ m₄ k₁ k₂ a A₀
    (by exact_mod_cast hr) hfactor hcop (by simpa only [Nat.cast_mul] using hstat)
  have hres : (ZMod.castHom hdq (ZMod d)) (k₁ : ZMod q) =
      ((ZMod.castHom hdq (ZMod d)) (m₄ : ZMod q)*
        (ZMod.castHom hdq (ZMod d)) (u : ZMod q))^2 ↔
      Int.ModEq (d : ℤ) k₁ (m₄^2*a^2) := by
    rw [hu]
    simp only [map_intCast]
    rw [← ZMod.intCast_eq_intCast_iff k₁ (m₄^2*a^2) d]
    simp only [Int.cast_mul, Int.cast_pow, mul_pow]
  unfold doubleVoronoiResidueWeight
  simp only [hres, ← heq]

end
end ArtinMatthews
