module

public import ArtinMatthews.SourceSLocalSheetComplex
public import ArtinMatthews.SourceSLocalSheetNorm
public import ArtinMatthews.SourceSLocalSheetTopology
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

/-! The norm-one S-local sheet, with the other infinite units and every
finite S unit unchanged and the chosen complex phase retained. -/

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain
open scoped NumberField
noncomputable section

variable {K : Type} [Field K] [NumberField K] {v : InfinitePlace K} (hv : IsComplex v)
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

def sourceSNormOneToSheet (x : SNormOne K S) : Circle × SNormOneOtherUnits S v :=
  (sourceSheetComplexPhase hv (x.val.1 v), sourceSheetOther S v x.val)

def sourceSNormOneFromSheet (y : Circle × SNormOneOtherUnits S v) : SNormOne K S :=
  ⟨sourceSheetFill S v
    (sourceSheetComplexUnit hv y.1 (sourceSheetRadius S v y.2) (sourceSheetRadius_pos S v y.2)) y.2, by
    change sLocalNorm K S (sourceSheetFill S v _ y.2) = 1
    rw [sourceSheetWholeNorm_split S v, hv.mult_eq_two, sourceSheetFill_chosen,
      sourceSheetOther_fill, sourceSheetComplexUnit_norm, sourceSheetRadius_sq,
      inv_mul_cancel₀ (sourceSheetOtherNorm_pos S v y.2).ne']⟩

@[simp] theorem sourceSNormOneFromSheet_chosen_image (y : Circle × SNormOneOtherUnits S v) :
    ringEquivComplexOfIsComplex hv ((sourceSNormOneFromSheet hv S y).val.1 v : v.Completion) =
      (y.1 : ℂ) * (sourceSheetRadius S v y.2 : ℂ) := by
  change ringEquivComplexOfIsComplex hv ((sourceSheetFill S v _ y.2).1 v : v.Completion) = _
  rw [sourceSheetFill_chosen, sourceSheetComplexUnit_image]

@[simp] theorem sourceSNormOneFromSheet_chosen_norm (y : Circle × SNormOneOtherUnits S v) :
    ‖((sourceSNormOneFromSheet hv S y).val.1 v : v.Completion)‖ =
      sourceSheetRadius S v y.2 := by
  rw [← sourceSheetComplex_norm hv, sourceSNormOneFromSheet_chosen_image, norm_mul,
    Circle.norm_coe, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sourceSheetRadius_pos S v y.2), one_mul]

@[simp] theorem sourceSNormOneFromSheet_other (y : Circle × SNormOneOtherUnits S v)
    (w : {w : InfinitePlace K // w ≠ v}) :
    (sourceSNormOneFromSheet hv S y).val.1 w.val = y.2.1 w :=
  sourceSheetFill_other S v _ y.2 w

@[simp] theorem sourceSNormOneFromSheet_finite (y : Circle × SNormOneOtherUnits S v) :
    (sourceSNormOneFromSheet hv S y).val.2 = y.2.2 := rfl

def sourceSNormOneSheetMulEquiv : SNormOne K S ≃* Circle × SNormOneOtherUnits S v where
  toFun := sourceSNormOneToSheet hv S
  invFun := sourceSNormOneFromSheet hv S
  left_inv x := by
    apply Subtype.ext
    let y := sourceSheetOther S v x.val
    let r := sourceSheetRadius S v y
    have hu :
        sourceSheetComplexUnit hv (sourceSheetComplexPhase hv (x.val.1 v)) r
          (sourceSheetRadius_pos S v y) = x.val.1 v := by
      apply Units.ext
      apply (ringEquivComplexOfIsComplex hv).injective
      rw [sourceSheetComplexUnit_image, show r = ‖(x.val.1 v : v.Completion)‖ from
        sourceSheetRadius_normOne S v hv x, sourceSheetComplexPhase_coe,
        div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (x.val.1 v).ne_zero))]
    change sourceSheetFill S v
      (sourceSheetComplexUnit hv (sourceSheetComplexPhase hv (x.val.1 v)) r
        (sourceSheetRadius_pos S v y)) y = x.val
    rw [hu]
    exact sourceSheetFill_reconstruct S v x.val
  right_inv y := by
    simp only [sourceSNormOneToSheet, sourceSNormOneFromSheet, sourceSheetFill_chosen,
      sourceSheetComplexUnit_phase, sourceSheetOther_fill]
  map_mul' x y :=
    Prod.ext (sourceSheetComplexPhase_mul hv (x.val.1 v) (y.val.1 v))
      (sourceSheetOther_mul S v x.val y.val)

theorem continuous_sourceSNormOneToSheet : Continuous (sourceSNormOneToSheet hv S) := by
  have hu : Continuous (fun x : SNormOne K S => x.val.1 v) :=
    (continuous_apply v).comp (continuous_fst.comp continuous_subtype_val)
  exact ((continuous_sourceSheetComplexPhase hv).comp hu).prodMk
    ((continuous_sourceSheetOther S v).comp continuous_subtype_val)

theorem continuous_sourceSNormOneFromSheet : Continuous (sourceSNormOneFromSheet hv S) := by
  refine Continuous.subtype_mk ?_ _
  have hu := continuous_sourceSheetComplexUnit hv
    (continuous_fst : Continuous (Prod.fst : Circle × SNormOneOtherUnits S v → Circle))
    ((continuous_sourceSheetRadius S v).comp continuous_snd)
    (fun y : Circle × SNormOneOtherUnits S v => sourceSheetRadius_pos S v y.2)
  exact continuous_sourceSheetFill S v hu continuous_snd

def sourceSNormOneSheetContinuousMulEquiv : SNormOne K S ≃ₜ* Circle × SNormOneOtherUnits S v where
  __ := sourceSNormOneSheetMulEquiv hv S
  continuous_toFun := continuous_sourceSNormOneToSheet hv S
  continuous_invFun := continuous_sourceSNormOneFromSheet hv S

end
end ArtinMatthews.SourcePhysical
