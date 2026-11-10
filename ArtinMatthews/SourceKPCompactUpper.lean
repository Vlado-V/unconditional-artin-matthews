module

public import ArtinMatthews.SourceKPCompactCoChain
public import ArtinMatthews.SourceKPIntegralGeneration
public import ArtinMatthews.SourceKubotaBottomRows
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Exact compact cochain law on integral upper root elements.
The actual shift of the lower-right entry is a principal unit,
so the source phase is preserved. -/

namespace ArtinMatthews
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups Classical
noncomputable section
variable {F Γ A : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ] [CommGroup A]
    (ν : Valuation F Γ) (B : Fˣ →* (Fˣ →* A))

theorem sourceKPCompactPhase_right_upper
    (hprincipal : ∀ a b : Fˣ, ν ((b : F) - 1) < 1 → B a b = 1)
    (g : GL (Fin 2) F) (hg : SourceKPIntegralMatrix ν g) (x : F) (hx : ν x ≤ 1) :
    sourceKPCompactPhase ν B (g * sourceGL2Upper x) =
      sourceKPCompactPhase ν B g * sourceKPCompactPhase ν B (sourceGL2Upper x) *
        sourceKP2Multiplier B g (sourceGL2Upper x) := by
  rw [sourceKPCompactPhase_zero_left ν B (sourceGL2Upper x) (by simp [sourceGL2Upper]),
    sourceKP2Multiplier_right_upper B, mul_one, mul_one]
  let g' := g * sourceGL2Upper x
  have hC : g' 1 0 = g 1 0 := sourceGL2_right_upper_bottom_left g x
  by_cases hc : g 1 0 = 0
  · rw [sourceKPCompactPhase_zero_left ν B g hc, sourceKPCompactPhase_zero_left ν B g' (hC.trans hc)]
  by_cases hcu : ν (g 1 0) = 1
  · rw [sourceKPCompactPhase_unit_left ν B g hcu,
      sourceKPCompactPhase_unit_left ν B g' (congrArg ν hC |>.trans hcu)]
  have hcv : ν (g 1 0) < 1 := lt_of_le_of_ne (hg.entries 1 0) hcu
  have hg' : SourceKPIntegralMatrix ν g' :=
    sourceKPIntegralMatrix_mul ν hg (sourceKPIntegralMatrix_upper ν x hx)
  have hd := (sourceKPIntegralMatrix_bottom_unit ν hg).resolve_left hcu
  have hd' := (sourceKPIntegralMatrix_bottom_unit ν hg').resolve_left (by rwa [hC])
  have hd0 := sourceKPVal_eq_one_ne_zero ν hd
  have hd0' := sourceKPVal_eq_one_ne_zero ν hd'
  let d := Units.mk0 (g 1 1) hd0
  let d' := Units.mk0 (g' 1 1) hd0'
  have hr : ((d' : F) / (d : F)) - 1 = (g 1 0 * x) / (d : F) := by
    change (g * sourceGL2Upper x) 1 1 / g 1 1 - 1 = (g 1 0 * x) / g 1 1
    rw [sourceGL2_right_upper_bottom_right, add_div, div_self hd0]
    ring
  have hv : ν ((((d' / d : Fˣ)) : F) - 1) < 1 := by
    rw [Units.val_div_eq_div_val, hr, map_div₀, map_mul, show ν (d : F) = 1 from hd, div_one]
    exact (mul_le_mul_of_nonneg_left hx zero_le).trans_lt (by simpa only [mul_one] using hcv)
  have hD := hprincipal (sourceKubotaX g) (d' / d) hv
  rw [map_div] at hD
  have hval := div_eq_one.mp hD
  have hdet : GeneralLinearGroup.det g' = GeneralLinearGroup.det g := by
    change GeneralLinearGroup.det (g * sourceGL2Upper x) = GeneralLinearGroup.det g
    rw [map_mul, sourceGL2Upper_det, mul_one]
  rw [sourceKPCompactPhase_nonunit_left ν B g' (hC.symm ▸ hc) ((congrArg ν hC).symm ▸ hcv) hd0',
    sourceKPCompactPhase_nonunit_left ν B g hc hcv hd0]
  change B (sourceKubotaX g') (d' / GeneralLinearGroup.det g') =
    B (sourceKubotaX g) (d / GeneralLinearGroup.det g)
  have hx' : sourceKubotaX g' = sourceKubotaX g := sourceKubotaX_right_upper g x
  rw [hx', hdet, map_div, map_div, hval]

end
end ArtinMatthews
