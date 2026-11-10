module

public import ArtinMatthews.SourceKubotaCoordinates
public import ArtinMatthews.SourceKubotaBottomRows
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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

/-! The actual Kubota ratios commute with a field embedding, including
the zero/nonzero choice of the bottom coordinate. -/

namespace ArtinMatthews
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section
variable {F L : Type*} [Field F] [Field L]

theorem sourceKubotaX_map (f : F →+* L) (g : GL (Fin 2) F) :
    sourceKubotaX (GeneralLinearGroup.map f g) = Units.map f.toMonoidHom (sourceKubotaX g) := by
  apply Units.ext
  have hl := GeneralLinearGroup.map_apply f 1 0 g
  have hr := GeneralLinearGroup.map_apply f 1 1 g
  by_cases hg : g 1 0 = 0
  · have h : GeneralLinearGroup.map f g 1 0 = 0 := by rw [hl, hg, map_zero]
    rw [sourceKubotaX_val_right _ h, hr]
    change f (g 1 1) = f (sourceKubotaX g : F)
    rw [sourceKubotaX_val_right g hg]
  · have h : GeneralLinearGroup.map f g 1 0 ≠ 0 := by rw [hl]; exact (map_ne_zero f).mpr hg
    rw [sourceKubotaX_val_left _ h, hl]
    change f (g 1 0) = f (sourceKubotaX g : F)
    rw [sourceKubotaX_val_left g hg]

def sourceKubotaRatioLeft (g h : GL (Fin 2) F) : Fˣ :=
  sourceKubotaX (g * h) / sourceKubotaX g

def sourceKubotaRatioRight (g h : GL (Fin 2) F) : Fˣ :=
  sourceKubotaX (g * h) / (sourceKubotaX h * GeneralLinearGroup.det g)

theorem sourceKubotaRatioLeft_map (f : F →+* L) (g h : GL (Fin 2) F) :
    sourceKubotaRatioLeft (GeneralLinearGroup.map f g) (GeneralLinearGroup.map f h) =
      Units.map f.toMonoidHom (sourceKubotaRatioLeft g h) := by
  unfold sourceKubotaRatioLeft
  rw [← GeneralLinearGroup.map_mul, sourceKubotaX_map, sourceKubotaX_map, map_div]

theorem sourceKubotaRatioRight_map (f : F →+* L) (g h : GL (Fin 2) F) :
    sourceKubotaRatioRight (GeneralLinearGroup.map f g) (GeneralLinearGroup.map f h) =
      Units.map f.toMonoidHom (sourceKubotaRatioRight g h) := by
  unfold sourceKubotaRatioRight
  rw [← GeneralLinearGroup.map_mul, sourceKubotaX_map, sourceKubotaX_map, GeneralLinearGroup.map_det,
    map_div, map_mul]
  rfl

end
end ArtinMatthews
