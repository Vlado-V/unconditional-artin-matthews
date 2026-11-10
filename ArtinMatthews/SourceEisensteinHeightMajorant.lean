module

public import ArtinMatthews.SourceKPAdelicEisensteinHolomorphic
public import ArtinMatthews.SourceKPAdelicEisensteinConvergence
public import ArtinMatthews.SourceKPAdelicSectionBound
public import ArtinMatthews.SourceKPRationalHeightComplex
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

/-! Explicit height majorants for the genuine initial Eisenstein series. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicCompactEisenstein_height_majorant {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1)
    (q : SourceKPAdelicProjective K hζ) (g : GL (Fin 2) 𝔸[K])
    (hq : sourceKPAdelicProjectiveProjection K hζ q = ProjGenLinGroup.mk g) :
    ‖sourceKPAdelicCompactEisenstein K hζ s q‖ ≤
      sourceKPAdelicHeight K hζ g ^ (s.re + 1 / 2) +
        sourceKPAdelicHeightConstant K hζ g ^ (s.re + 1 / 2) *
          ∑' x : K, Height.mulHeight₁ x ^ (-(2 * s.re + 1)) := by
  let F : K → ℂ := fun x => sourceKPAdelicCompactScalar K hζ s
    (sourceKPAdelicProjectiveWeyl K hζ * sourceKPAdelicUpperLift K hζ (algebraMap K 𝔸[K] x) * q)
  have hM := (sourceKPRationalHeight_rpow_summable K hs).mul_left
    (sourceKPAdelicHeightConstant K hζ g ^ (s.re + 1 / 2))
  have hbound (x : K) := sourceKPAdelicCompact_openCell_bound K hζ hs q g hq x
  have hnorm : Summable (fun x => ‖F x‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hM
  have he : sourceKPAdelicCompactEisenstein K hζ s q =
      sourceKPAdelicCompactScalar K hζ s q + ∑' x, F x :=
    sourceKPAdelicEisensteinSum_bruhat K hζ s (sourceKPAdelicCompactSection K hζ s) q
      (sourceKPAdelicCompactEisenstein_converges K hζ hs q)
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add (sourceKPAdelicCompactScalar_height_bound K hζ s q g hq)
  calc
    _ ≤ ∑' x, ‖F x‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' x : K, sourceKPAdelicHeightConstant K hζ g ^ (s.re + 1 / 2) *
        Height.mulHeight₁ x ^ (-(2 * s.re + 1)) := hnorm.tsum_le_tsum hbound hM
    _ = _ := tsum_mul_left

theorem sourceKPAdelicCompactEisenstein_uniform_height_majorant {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1)
    (q : SourceKPAdelicProjective K hζ) (g : GL (Fin 2) 𝔸[K])
    (hq : sourceKPAdelicProjectiveProjection K hζ q = ProjGenLinGroup.mk g)
    (B : ℝ) (hH : sourceKPAdelicHeight K hζ g ≤ B)
    (hC : sourceKPAdelicHeightConstant K hζ g ≤ B) :
    ‖sourceKPAdelicCompactEisenstein K hζ s q‖ ≤
      B ^ (s.re + 1 / 2) * (1 + ∑' x : K, Height.mulHeight₁ x ^ (-(2 * s.re + 1))) := by
  have ha : 0 ≤ s.re + 1 / 2 := by
    have hnonneg : 0 ≤ ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hsum : 0 ≤ ∑' x : K, Height.mulHeight₁ x ^ (-(2 * s.re + 1)) :=
    tsum_nonneg (fun x => Real.rpow_nonneg (Height.mulHeight₁_nonneg x) _)
  apply (sourceKPAdelicCompactEisenstein_height_majorant K hζ hs q g hq).trans
  calc
    _ ≤ B ^ (s.re + 1 / 2) +
        B ^ (s.re + 1 / 2) * ∑' x : K, Height.mulHeight₁ x ^ (-(2 * s.re + 1)) := by
      apply add_le_add
      · exact Real.rpow_le_rpow (sourceKPAdelicHeight_pos K hζ g).le hH ha
      · exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (sourceKPAdelicHeightConstant_pos K hζ g).le hC ha) hsum
    _ = _ := by ring

end
end ArtinMatthews
