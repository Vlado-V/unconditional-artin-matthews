module

public import ArtinMatthews.QuadraticHeckeRayDualTail
public import ArtinMatthews.QuadraticHeckeRayDualCutoff
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

namespace ArtinMatthews
open NumberField Set VaryingKummerAnalytic Filter
open scoped NumberField Classical ContDiff Topology
noncomputable section

variable (F : Type) [Field F] [NumberField F]
local notation "NZ" => {J : Ideal (𝓞 F) // J ≠ ⊥}

/-- The actual finite outer family converges to the full dual ideal sum. -/
theorem quadraticHeckeRayDual_finite_cutoff_tendsto {ι : Type*} (s : Finset ι)
    (m : ι → Ideal (𝓞 F)) (ψ : ∀ i, EvenIdealRayCharacter F (m i))
    (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0) (hs : ContDiff ℝ ∞ w)
    (c : ι → ℝ) (hc' : ∀ i ∈ s, 0 < c i) (a : ι → ℂ) :
    Tendsto (fun H : ℝ => ∑ i ∈ s, a i *
      ∑ J ∈ quadraticHeckeIdealNormBall F H, quadraticHeckeRayDualTerm F (ψ i) A r w (c i) J)
      atTop (𝓝 (∑' J : NZ, ∑ i ∈ s, a i * quadraticHeckeRayDualTerm F (ψ i) A r w (c i) J)) := by
  rw [← quadraticHeckeRayDual_finite_interchange F s m ψ A r w hc hp hs c hc' a]
  obtain ⟨C, _, hb⟩ := quadraticHeckeRayDual_finite_cutoff_error F A r w hc hp hs
    (u := 2) (σ := 3) (by norm_num) (by norm_num)
  let B := C * ∑ i ∈ s, ‖a i‖ * (c i) ^ (-(3 : ℝ))
  have hlim : Tendsto (fun H : ℝ => B * H ^ (-(1 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1)).const_mul B
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
  rw [norm_sub_rev]
  have h := hb s m ψ c hc' a H hH
  apply h.trans_eq
  change C * H ^ (2 - 3 : ℝ) * (∑ i ∈ s, ‖a i‖ * (c i) ^ (-(3 : ℝ))) =
    (C * ∑ i ∈ s, ‖a i‖ * (c i) ^ (-(3 : ℝ))) * H ^ (-(1 : ℝ))
  norm_num only
  ring

end
end ArtinMatthews
