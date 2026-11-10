module

public import ArtinMatthews.PrincipalAngularGaussian
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact exponent comparison for section 06 of the source manuscript.

The conclusion concerns the actual corrected principal signal. The physical
probe estimate and its comparison with that signal are explicit obligations;
this file does not assert either analytic estimate or the Poisson identity.
-/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Filter Asymptotics
open scoped Topology
noncomputable section

def sourceContourExponent (xi w z : ℝ) : ℝ :=
  9 / 20 + xi - 1 + (1 / 10) * z + (133 / 1000) * (w - 1)

theorem sourceContourExponent_principal (xi : ℝ) :
    sourceContourExponent xi 1 (1 / 6) = xi - 8 / 15 := by
  unfold sourceContourExponent
  ring

theorem sourceContourExponent_w_remainder :
    sourceContourExponent (1 + 1 / 10000000) (95 / 100) (1 / 6 + 1 / 10000000)
      < 7 / 15 - 1 / 2000 := by
  norm_num [sourceContourExponent]

theorem sourceContourExponent_z_remainder :
    sourceContourExponent (1 + 1 / 10000000) 1 (16 / 100)
      < 7 / 15 - 1 / 2000 := by
  norm_num [sourceContourExponent]

theorem sourceContourExponent_good_rows :
    sourceContourExponent (998 / 1000) (3 / 1000) (4 / 10) +
      (10001 / 100000) * (11 / 10) + 1 / 10000
        < 7 / 15 - 1 / 2500 := by
  norm_num [sourceContourExponent]

theorem sourceContourExponent_far_rows :
    sourceContourExponent 4 4 350000 + (10001 / 100000) * (1 - 350000)
      + 1 / 10000 < 7 / 15 - 1 / 2500 := by
  norm_num [sourceContourExponent]

private theorem rpow_bigO_of_le {a b : ℝ} (hab : a ≤ b) :
    (fun x : ℝ => x ^ a) =O[atTop] (fun x : ℝ => x ^ b) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _), one_mul]
  exact Real.rpow_le_rpow_of_exponent_le hx hab

variable {K : Type*} [Field K] [NumberField K] {ζ : K} {M : Ideal (𝓞 K)}

/-- The exact final comparison, with the reflection loss `10⁻⁵` and the
nonprincipal error saving `.0004`, gives the manuscript's safe saving. -/
theorem principalAngularGaussianSignal_bound_of_probe_comparison
    (hζ : IsPrimitiveRoot ζ 12) (η : EvenIdealRayCharacter K M)
    (S : Finset (ArtinMatthews.ProbePrime K)) (P : ℝ → ℂ) (c : ℂ) (hc : c ≠ 0)
    (hprobe : P =O[atTop] (fun x : ℝ => x ^ (933 / 2000 + 1 / 100000 : ℝ)))
    (hcomparison : (fun x => P x - c * principalAngularGaussianSignal hζ η S x)
      =O[atTop] (fun x : ℝ => x ^ (7 / 15 - 1 / 2500 : ℝ))) :
    principalAngularGaussianSignal hζ η S =O[atTop]
      (fun x : ℝ => x ^ (7 / 15 - 1 / 20000 : ℝ)) := by
  have hp := hprobe.trans (rpow_bigO_of_le
    (show (933 / 2000 + 1 / 100000 : ℝ) ≤ 7 / 15 - 1 / 20000 by norm_num))
  have hr := hcomparison.trans (rpow_bigO_of_le
    (show (7 / 15 - 1 / 2500 : ℝ) ≤ 7 / 15 - 1 / 20000 by norm_num))
  have h := (hp.sub hr).const_mul_left c⁻¹
  apply h.congr_left
  intro x
  simp only [sub_sub_cancel, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- The two principal contour remainders and the full nonprincipal row sum
may be checked separately, without altering the actual principal signal. -/
theorem principalAngularGaussianSignal_bound_of_three_remainders
    (hζ : IsPrimitiveRoot ζ 12) (η : EvenIdealRayCharacter K M)
    (S : Finset (ArtinMatthews.ProbePrime K))
    (P Rw Rz Rnp : ℝ → ℂ) (c : ℂ) (hc : c ≠ 0)
    (hidentity : ∀ᶠ x in atTop, P x = c * principalAngularGaussianSignal hζ η S x +
      Rw x + Rz x + Rnp x)
    (hprobe : P =O[atTop] (fun x : ℝ => x ^ (933 / 2000 + 1 / 100000 : ℝ)))
    (hw : Rw =O[atTop] (fun x : ℝ => x ^ (7 / 15 - 1 / 2000 : ℝ)))
    (hz : Rz =O[atTop] (fun x : ℝ => x ^ (7 / 15 - 1 / 2000 : ℝ)))
    (hnp : Rnp =O[atTop] (fun x : ℝ => x ^ (7 / 15 - 1 / 2500 : ℝ))) :
    principalAngularGaussianSignal hζ η S =O[atTop]
      (fun x : ℝ => x ^ (7 / 15 - 1 / 20000 : ℝ)) := by
  apply principalAngularGaussianSignal_bound_of_probe_comparison hζ η S P c hc hprobe
  have hm := rpow_bigO_of_le
    (show (7 / 15 - 1 / 2000 : ℝ) ≤ 7 / 15 - 1 / 2500 by norm_num)
  apply (((hw.trans hm).add (hz.trans hm)).add hnp).congr'
  · filter_upwards [hidentity] with x hx
    rw [hx]
    ring
  · exact Filter.Eventually.of_forall (fun _ => rfl)

end
end ArtinMatthews.VaryingKummerAnalytic
