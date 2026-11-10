module

public import ArtinMatthews.SourceKubotaDefect
public import ArtinMatthews.SourceKubotaBottomRows
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! The Weyl defect for the actual Kubota multiplier. The bottom-row
determinant identity gives a Steinberg pair when all selected entries
are nonzero. The zero-entry cases give either a diagonal pair or the
minus-one unit. -/

namespace ArtinMatthews
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups Classical
noncomputable section
variable {F : Type*} [Field F] {A : Type*} [CommGroup A]
    (B : Fˣ →* (Fˣ →* A))

theorem sourceKubotaSymbol_steinberg_sub
    (hminus : ∀ x, B x (sourceMinusOneUnit F) = 1)
    (hsteinberg : ∀ x : Fˣ, ∀ hx : 1 - (x : F) ≠ 0, B x (Units.mk0 _ hx) = 1)
    (t z : Fˣ) (hz : (z : F) = (t : F) - 1) : B t z = 1 := by
  let u := sourceMinusOneUnit F * z
  have hu : (u : F) = 1 - (t : F) := by
    change -1 * (z : F) = 1 - (t : F)
    rw [hz]
    ring
  have hn : 1 - (t : F) ≠ 0 := hu ▸ Units.ne_zero u
  have he : Units.mk0 _ hn = u := Units.ext hu.symm
  have h := hsteinberg t hn
  rw [he] at h
  simpa only [u, map_mul, hminus, one_mul] using h

private theorem sourceKubotaWeylRow_cases
    (a e b c u v : Fˣ) (p q r s : F)
    (hb : (b : F) = if p = 0 then q else p)
    (hu : (u : F) = if q = 0 then p else q)
    (hc : (c : F) = if r = 0 then s else r)
    (hv : (v : F) = if s = 0 then r else s)
    (hdet : (a : F) * (e : F) = r * q - s * p) :
    let t : F := (c : F) * u / ((b : F) * v)
    let z : F := (a : F) * e / ((b : F) * v)
    z = t ∨ z = -1 ∨ z = t - 1 := by
  dsimp only
  have hn := mul_ne_zero (Units.ne_zero a) (Units.ne_zero e)
  have hneg (he : (a : F) * (e : F) = -(s * p)) (hp : p ≠ 0) (hs : s ≠ 0)
      (hbp : (b : F) = p) (hvs : (v : F) = s) :
      (a : F) * e / ((b : F) * v) = -1 := by
    rw [he, hbp, hvs, mul_comm p s, neg_div, div_self (mul_ne_zero hs hp)]
  by_cases hp : p = 0
  · rw [hp, mul_zero, sub_zero] at hdet
    have hq : q ≠ 0 := fun hq => hn (by rw [hdet, hq, mul_zero])
    have hr : r ≠ 0 := fun hr => hn (by rw [hdet, hr, zero_mul])
    left
    rw [hdet, hc, hu, ite_eq_right hr, ite_eq_right hq]
  · have hbp : (b : F) = p := hb.trans (ite_eq_right hp)
    by_cases hq : q = 0
    · rw [hq, mul_zero, zero_sub] at hdet
      have hs : s ≠ 0 := fun hs => hn (by rw [hdet, hs, zero_mul, neg_zero])
      exact Or.inr (Or.inl (hneg hdet hp hs hbp (hv.trans (ite_eq_right hs))))
    · by_cases hr : r = 0
      · rw [hr, zero_mul, zero_sub] at hdet
        have hs : s ≠ 0 := fun hs => hn (by rw [hdet, hs, zero_mul, neg_zero])
        exact Or.inr (Or.inl (hneg hdet hp hs hbp (hv.trans (ite_eq_right hs))))
      · by_cases hs : s = 0
        · rw [hs, zero_mul, sub_zero] at hdet
          left
          rw [hdet, hc, hu, ite_eq_right hr, ite_eq_right hq]
        · right
          right
          rw [hdet, hbp, hc, hu, hv, ite_eq_right hr, ite_eq_right hq, ite_eq_right hs]
          field_simp [hp, hs]

theorem sourceKP2Defect_left_triangular (hdiag : ∀ x, B x x = 1)
    (g h k : GL (Fin 2) F) (hg : g 1 0 = 0) : sourceKP2Defect B g h k = 1 := by
  rw [sourceKP2Defect_formula B hdiag, sourceKubotaX_mul_left_triangular g h hg,
    mul_assoc g h k, sourceKubotaX_mul_left_triangular g (h * k) hg]
  have he : (sourceKubotaX g * sourceKubotaX h * sourceKubotaX (h * k)) /
      (sourceKubotaX h * (sourceKubotaX g * sourceKubotaX (h * k))) = 1 :=
    div_eq_one.mpr (by ac_rfl)
  rw [he, map_one, MonoidHom.one_apply]

theorem sourceKP2Defect_right_weyl (hdiag : ∀ x, B x x = 1)
    (hminus : ∀ x, B x (sourceMinusOneUnit F) = 1)
    (hsteinberg : ∀ x : Fˣ, ∀ hx : 1 - (x : F) ≠ 0, B x (Units.mk0 _ hx) = 1)
    (g h : GL (Fin 2) F) : sourceKP2Defect B g h sourceGL2Weyl = 1 := by
  by_cases hg : g 1 0 = 0
  · exact sourceKP2Defect_left_triangular B hdiag g h _ hg
  rw [sourceKP2Defect_formula B hdiag, sourceKubotaX_weyl, mul_one]
  let a := sourceKubotaX g
  let e := GeneralLinearGroup.det h
  let b := sourceKubotaX h
  let c := sourceKubotaX (g * h)
  let u := sourceKubotaX (h * sourceGL2Weyl)
  let v := sourceKubotaX (g * h * sourceGL2Weyl)
  let t := (c * u) / (b * v)
  let z := (a * e) / (b * v)
  change B t z = 1
  have hb : (b : F) = if h 1 0 = 0 then h 1 1 else h 1 0 := rfl
  have hc : (c : F) = if (g * h) 1 0 = 0 then (g * h) 1 1 else (g * h) 1 0 := rfl
  have hu : (u : F) = if h 1 1 = 0 then h 1 0 else h 1 1 := by
    by_cases hh : h 1 1 = 0
    · exact (sourceKubotaX_right_weyl_of_zero h hh).trans (ite_eq_left hh).symm
    · exact (sourceKubotaX_right_weyl_of_nonzero h hh).trans (ite_eq_right hh).symm
  have hv : (v : F) = if (g * h) 1 1 = 0 then (g * h) 1 0 else (g * h) 1 1 := by
    by_cases hh : (g * h) 1 1 = 0
    · exact (sourceKubotaX_right_weyl_of_zero (g * h) hh).trans (ite_eq_left hh).symm
    · exact (sourceKubotaX_right_weyl_of_nonzero (g * h) hh).trans (ite_eq_right hh).symm
  have hdet : (a : F) * (e : F) = (g * h) 1 0 * h 1 1 - (g * h) 1 1 * h 1 0 := by
    rw [sourceKubotaX_val_left g hg, sourceKubota_det_cross]
  have hh : (z : F) = (t : F) ∨ (z : F) = -1 ∨ (z : F) = (t : F) - 1 := by
    simpa only [z, t, Units.val_div_eq_div_val, Units.val_mul] using
      sourceKubotaWeylRow_cases a e b c u v _ _ _ _ hb hu hc hv hdet
  rcases hh with he | he | he
  · rw [Units.ext he, hdiag]
  · have he' : z = sourceMinusOneUnit F := Units.ext he
    rw [he', hminus]
  · exact sourceKubotaSymbol_steinberg_sub B hminus hsteinberg t z he

end
end ArtinMatthews
