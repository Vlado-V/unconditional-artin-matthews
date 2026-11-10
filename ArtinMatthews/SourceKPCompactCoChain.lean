module

public import ArtinMatthews.SourceKPIntegralGroup
public import ArtinMatthews.SourceKubotaCoordinates
public import ArtinMatthews.SourceKubotaBottomRows
public import ArtinMatthews.SourceKubotaDefect
public import ArtinMatthews.SourceKubotaFullScalars
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The explicit compact cochain for the determinant-modified rank-two
multiplier. The lower-right entry is divided by the determinant; this
is necessary for the diagonal and scalar generators of GL2. -/

namespace ArtinMatthews
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups Classical
noncomputable section
variable {F Γ A : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ] [CommGroup A]
    (ν : Valuation F Γ) (B : Fˣ →* (Fˣ →* A))

theorem sourceKPVal_eq_one_ne_zero {x : F} (h : ν x = 1) : x ≠ 0 := by
  intro hx
  rw [hx, map_zero] at h
  exact zero_ne_one h

theorem sourceKPVal_unit_div (a b : Fˣ) (ha : ν (a : F) = 1) (hb : ν (b : F) = 1) :
    ν (((a / b : Fˣ)) : F) = 1 := by
  rw [Units.val_div_eq_div_val, map_div₀, ha, hb, div_one]

def sourceKPCompactPhase (g : GL (Fin 2) F) : A :=
  if h : g 1 0 ≠ 0 ∧ ν (g 1 0) < 1 ∧ g 1 1 ≠ 0 then
    B (sourceKubotaX g) (Units.mk0 (g 1 1) h.2.2 / GeneralLinearGroup.det g)
  else 1

theorem sourceKPCompactPhase_zero_left (g : GL (Fin 2) F) (h : g 1 0 = 0) :
    sourceKPCompactPhase ν B g = 1 := by
  simp [sourceKPCompactPhase, h]

theorem sourceKPCompactPhase_unit_left (g : GL (Fin 2) F) (h : ν (g 1 0) = 1) :
    sourceKPCompactPhase ν B g = 1 := by
  simp [sourceKPCompactPhase, h]

theorem sourceKPCompactPhase_nonunit_left (g : GL (Fin 2) F)
    (hc : g 1 0 ≠ 0) (hv : ν (g 1 0) < 1) (hd : g 1 1 ≠ 0) :
    sourceKPCompactPhase ν B g =
      B (sourceKubotaX g) (Units.mk0 (g 1 1) hd / GeneralLinearGroup.det g) := by
  rw [sourceKPCompactPhase, dite_eq_left ⟨hc, hv, hd⟩]

theorem sourceKPCompactSymbol_scale
    (hdiag : ∀ x, B x x = 1)
    (hunit : ∀ a b : Fˣ, ν (a : F) = 1 → ν (b : F) = 1 → B a b = 1)
    (x u d : Fˣ) (hu : ν (u : F) = 1) (hd : ν (d : F) = 1) :
    B (x * u) (d / u) = B x d * B u x := by
  rw [map_mul, MonoidHom.mul_apply, hunit u _ hu (sourceKPVal_unit_div ν d u hd hu),
    mul_one, map_div, div_eq_mul_inv, sourceKubotaSymbol_skew B hdiag u x, inv_inv]

theorem sourceKP2Multiplier_right_upper (g : GL (Fin 2) F) (x : F) :
    sourceKP2Multiplier B g (sourceGL2Upper x) = 1 := by
  simp [sourceKP2Multiplier, sourceKubotaX_right_upper, sourceGL2Upper_det]

theorem sourceKP2Multiplier_compact_right_diagonal
    (hdiag : ∀ x, B x x = 1)
    (hunit : ∀ a b : Fˣ, ν (a : F) = 1 → ν (b : F) = 1 → B a b = 1)
    (g : GL (Fin 2) F) (hg : SourceKPIntegralMatrix ν g)
    (u : Fˣ) (hu : ν (u : F) = 1) :
    sourceKP2Multiplier B g (sourceGL2Diagonal u) =
      if g 1 0 = 0 then 1 else B u (sourceKubotaX g) := by
  have hD := hunit (GeneralLinearGroup.det g) u hg.det_unit hu
  rw [sourceKP2Multiplier, sourceKubotaX_right_diagonal, sourceKubotaX_diagonal,
    sourceGL2Diagonal_det, hD, one_pow, mul_one, one_mul]
  by_cases hc : g 1 0 = 0
  · rw [ite_eq_left hc, ite_eq_left hc, div_self', map_one, MonoidHom.one_apply]
  · have hx : (sourceKubotaX g * u) / sourceKubotaX g = u := by rw [mul_comm, mul_div_cancel_right]
    rw [ite_eq_right hc, ite_eq_right hc, hx, map_div, map_mul, hdiag, mul_one,
      hunit u (GeneralLinearGroup.det g) hu hg.det_unit, div_one]

theorem sourceKP2Multiplier_compact_right_scalar
    (hdiag : ∀ x, B x x = 1) (hcube : ∀ x y, B x y ^ 3 = 1)
    (hunit : ∀ a b : Fˣ, ν (a : F) = 1 → ν (b : F) = 1 → B a b = 1)
    (g : GL (Fin 2) F) (hg : SourceKPIntegralMatrix ν g)
    (u : Fˣ) (hu : ν (u : F) = 1) :
    sourceKP2Multiplier B g (GeneralLinearGroup.scalar (Fin 2) u) = B u (sourceKubotaX g) := by
  rw [sourceKP2Multiplier_scalar_right B hdiag hcube, map_mul,
    hunit u (GeneralLinearGroup.det g) hu hg.det_unit, mul_one]

end
end ArtinMatthews
