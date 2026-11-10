module

public import ArtinMatthews.SourceKPCompactCoChain
public import ArtinMatthews.SourceKubotaBottomRows
public import ArtinMatthews.SourceKubotaDefect
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

/-! Exact compact cochain law on the Weyl generator. It swaps the
two bottom entries. The nonunit cases retain the determinant and use
the actual skew law before simplifying the cochain. -/

namespace ArtinMatthews
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups Classical
noncomputable section
variable {F Γ A : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ] [CommGroup A]
    (ν : Valuation F Γ) (B : Fˣ →* (Fˣ →* A))

theorem sourceKP2Multiplier_right_weyl_formula
    (hminus : ∀ x, B x (sourceMinusOneUnit F) = 1) (g : GL (Fin 2) F) :
    sourceKP2Multiplier B g sourceGL2Weyl =
      B (sourceKubotaX (g * sourceGL2Weyl) / sourceKubotaX g)
        (sourceKubotaX (g * sourceGL2Weyl) / GeneralLinearGroup.det g) := by
  rw [sourceKP2Multiplier, sourceKubotaX_weyl, sourceGL2Weyl_det, hminus, one_pow, mul_one, one_mul]

private theorem sourceKPCompact_weyl_symbol_right
    (hdiag : ∀ x, B x x = 1)
    (hunit : ∀ a b : Fˣ, ν (a : F) = 1 → ν (b : F) = 1 → B a b = 1)
    (a b d : Fˣ) (ha : ν (a : F) = 1) (hd : ν (d : F) = 1) :
    B (b / a) (b / d) = B b (a / d) := by
  simp only [map_div, MonoidHom.div_apply, hdiag, hunit a d ha hd, div_one, one_div]
  rw [sourceKubotaSymbol_skew B hdiag b a]
  simp only [div_eq_mul_inv, inv_inv]

theorem sourceKPCompactPhase_right_weyl
    (hdiag : ∀ x, B x x = 1)
    (hminus : ∀ x, B x (sourceMinusOneUnit F) = 1)
    (hunit : ∀ a b : Fˣ, ν (a : F) = 1 → ν (b : F) = 1 → B a b = 1)
    (g : GL (Fin 2) F) (hg : SourceKPIntegralMatrix ν g) :
    sourceKPCompactPhase ν B (g * sourceGL2Weyl) =
      sourceKPCompactPhase ν B g * sourceKPCompactPhase ν B sourceGL2Weyl *
        sourceKP2Multiplier B g sourceGL2Weyl := by
  rw [sourceKPCompactPhase_unit_left ν B (sourceGL2Weyl : GL (Fin 2) F) (by simp [sourceGL2Weyl]),
    mul_one, sourceKP2Multiplier_right_weyl_formula B hminus]
  let g' := g * (sourceGL2Weyl : GL (Fin 2) F)
  have hC : g' 1 0 = g 1 1 := sourceGL2_right_weyl_bottom_left g
  have hD : g' 1 1 = g 1 0 := sourceGL2_right_weyl_bottom_right g
  let a := sourceKubotaX g
  let b := sourceKubotaX g'
  let D := GeneralLinearGroup.det g
  change sourceKPCompactPhase ν B g' = sourceKPCompactPhase ν B g * B (b / a) (b / D)
  by_cases hc0 : g 1 0 = 0
  · have hd := (sourceKPIntegralMatrix_bottom_unit ν hg).resolve_left (by
      rw [hc0, map_zero]
      exact zero_ne_one)
    have hba : b = a := Units.ext ((sourceKubotaX_right_weyl_of_nonzero g
      (sourceKPVal_eq_one_ne_zero ν hd)).trans (sourceKubotaX_val_right g hc0).symm)
    rw [sourceKPCompactPhase_unit_left ν B g' ((congrArg ν hC).trans hd),
      sourceKPCompactPhase_zero_left ν B g hc0, hba, div_self', map_one, MonoidHom.one_apply, mul_one]
  by_cases hd0 : g 1 1 = 0
  · have hc := (sourceKPIntegralMatrix_bottom_unit ν hg).resolve_right (by
      rw [hd0, map_zero]
      exact zero_ne_one)
    have hba : b = a := Units.ext ((sourceKubotaX_right_weyl_of_zero g hd0).trans
      (sourceKubotaX_val_left g hc0).symm)
    rw [sourceKPCompactPhase_zero_left ν B g' (hC.trans hd0), sourceKPCompactPhase_unit_left ν B g hc,
      hba, div_self', map_one, MonoidHom.one_apply, mul_one]
  have hav : (a : F) = g 1 0 := sourceKubotaX_val_left g hc0
  have hbv : (b : F) = g 1 1 := sourceKubotaX_right_weyl_of_nonzero g hd0
  by_cases hc : ν (g 1 0) = 1
  · have ha : ν (a : F) = 1 := (congrArg ν hav).trans hc
    by_cases hd : ν (g 1 1) = 1
    · have hb : ν (b : F) = 1 := (congrArg ν hbv).trans hd
      rw [sourceKPCompactPhase_unit_left ν B g' ((congrArg ν hC).trans hd),
        sourceKPCompactPhase_unit_left ν B g hc,
        hunit (b / a) (b / D) (sourceKPVal_unit_div ν b a hb ha)
          (sourceKPVal_unit_div ν b D hb hg.det_unit), mul_one]
    · have hdlt : ν (g 1 1) < 1 := lt_of_le_of_ne (hg.entries 1 1) hd
      have hgd0 : g' 1 1 ≠ 0 := hD.symm ▸ hc0
      have hu : Units.mk0 (g' 1 1) hgd0 = a := Units.ext (hD.trans hav.symm)
      have hdet : GeneralLinearGroup.det g' = D * sourceMinusOneUnit F := by
        change GeneralLinearGroup.det (g * (sourceGL2Weyl : GL (Fin 2) F)) = _
        rw [map_mul, sourceGL2Weyl_det]
      have hs : B b (a / (D * sourceMinusOneUnit F)) = B b (a / D) := by
        rw [map_div, map_mul, hminus, mul_one, ← map_div]
      rw [sourceKPCompactPhase_nonunit_left ν B g' (hC.symm ▸ hd0) ((congrArg ν hC).symm ▸ hdlt) hgd0,
        sourceKPCompactPhase_unit_left ν B g hc, one_mul, hu, hdet, hs,
        sourceKPCompact_weyl_symbol_right ν B hdiag hunit a b D ha hg.det_unit]
  · have hd := (sourceKPIntegralMatrix_bottom_unit ν hg).resolve_left hc
    have hc' : ν (g 1 0) < 1 := lt_of_le_of_ne (hg.entries 1 0) hc
    have hb : ν (b : F) = 1 := (congrArg ν hbv).trans hd
    have he : Units.mk0 (g 1 1) hd0 = b := Units.ext hbv.symm
    have hsym : B (b / a) (b / D) = (B a (b / D))⁻¹ := by
      rw [map_div B, MonoidHom.div_apply, hunit b (b / D) hb (sourceKPVal_unit_div ν b D hb hg.det_unit),
        one_div]
    rw [sourceKPCompactPhase_unit_left ν B g' ((congrArg ν hC).trans hd),
      sourceKPCompactPhase_nonunit_left ν B g hc0 hc' hd0, he, hsym, mul_inv_cancel]

end
end ArtinMatthews
