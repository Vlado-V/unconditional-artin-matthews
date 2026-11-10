module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Order.CompletePartialOrder
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

/-! Join the two frequency estimates over the actual arc window. The
endpoints in the high-frequency bound may be included. -/
namespace ArtinMatthews

open Filter MeasureTheory Set
noncomputable section

theorem giantComparison_arcEnergy_join (f : ℝ → ℂ) (hf : Continuous f)
    {R T a b : ℝ}
    (hlow : (∫ t in Icc (-R) R, ‖f t‖ ^ 2) ≤ a)
    (hhigh : (∫ t in {t : ℝ | R ≤ |t| ∧ |t| ≤ T}, ‖f t‖ ^ 2) ≤ b) :
    (∫ t in Icc (-T) T, ‖f t‖ ^ 2) ≤ a + b := by
  let W := Icc (-T) T
  let S := Icc (-R) R
  let V : Set ℝ := {t : ℝ | R ≤ |t| ∧ |t| ≤ T}
  let g (t : ℝ) := ‖f t‖ ^ 2
  have hg : Continuous g := hf.norm.pow 2
  have hnonneg (s : Set ℝ) : 0 ≤ᵐ[volume.restrict s] g :=
    Eventually.of_forall fun t => sq_nonneg ‖f t‖
  have hV : V ⊆ W := fun _ ht => abs_le.mp ht.2
  have hWV : W \ S ⊆ V := by
    intro t ht
    exact ⟨le_of_lt (not_le.mp fun h => ht.2 (abs_le.mp h)), abs_le.mpr ht.1⟩
  have hWg : IntegrableOn g W := hg.integrableOn_Icc
  have hSg : IntegrableOn g S := hg.integrableOn_Icc
  have hVg : IntegrableOn g V := hWg.mono_set hV
  have hlow' : (∫ t in W ∩ S, g t) ≤ a :=
    (setIntegral_mono_set hSg (hnonneg S) inter_subset_right.eventuallyLE).trans hlow
  have hhigh' : (∫ t in W \ S, g t) ≤ b :=
    (setIntegral_mono_set hVg (hnonneg V) hWV.eventuallyLE).trans hhigh
  have hpartition : (W ∩ S) ∪ (W \ S) = W := by
    ext t
    constructor
    · rintro (ht | ht) <;> exact ht.1
    · intro ht
      by_cases hs : t ∈ S
      · exact Or.inl ⟨ht, hs⟩
      · exact Or.inr ⟨ht, hs⟩
  have hdis : Disjoint (W ∩ S) (W \ S) :=
    Set.disjoint_left.mpr fun _ hi hd => hd.2 hi.2
  change (∫ t in W, g t) ≤ a + b
  rw [← hpartition, setIntegral_union hdis (measurableSet_Icc.diff measurableSet_Icc)
    (hWg.mono_set inter_subset_left) (hWg.mono_set sdiff_subset)]
  exact add_le_add hlow' hhigh'

theorem giantComparison_arcEnergy_log_join (f : ℝ → ℂ) (hf : Continuous f)
    {L R T A : ℝ} (hL : 2 ≤ L)
    (hlow : (∫ t in Icc (-R) R, ‖f t‖ ^ 2) ≤ L ^ (-A-1))
    (hhigh : (∫ t in {t : ℝ | R ≤ |t| ∧ |t| ≤ T}, ‖f t‖ ^ 2) ≤ L ^ (-A-1)) :
    (∫ t in Icc (-T) T, ‖f t‖ ^ 2) ≤ L ^ (-A) := by
  have hL₀ : 0 < L := (by norm_num : (0 : ℝ) < 2).trans_le hL
  have htwo : 2 * L⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv]
    exact (div_le_one hL₀).mpr hL
  calc
    _ ≤ L ^ (-A-1) + L ^ (-A-1) := giantComparison_arcEnergy_join f hf hlow hhigh
    _ = (2 * L⁻¹) * L ^ (-A) := by
      rw [sub_eq_add_neg, Real.rpow_add hL₀, Real.rpow_neg_one]
      ring
    _ ≤ 1 * L ^ (-A) := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hL₀.le _)
    _ = _ := one_mul _

end
end ArtinMatthews
