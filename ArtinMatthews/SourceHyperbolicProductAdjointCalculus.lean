module

public import ArtinMatthews.SourceHyperbolicProductGreen
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
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
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

namespace ArtinMatthews.SourceHyperbolicGreen
open OAI.CubicEisenstein MeasureTheory Filter
open scoped Topology ContDiff BigOperators Classical
noncomputable section

variable {ι : Type*} [Fintype ι]

theorem productWeightedPartial_support {φ : ProductSpace ι → ℂ} (i : ι) (j : Fin 3) :
    tsupport (productWeightedPartial φ i j) ⊆ tsupport φ := by
  unfold productWeightedPartial
  simp only [div_eq_mul_inv]
  exact tsupport_mul_subset_left.trans
    (tsupport_mul_subset_right.trans (product_test_partial_support i j))

theorem productWeightedPartial_compact {φ : ProductSpace ι → ℂ}
    (hc : HasCompactSupport φ) (i : ι) (j : Fin 3) :
    HasCompactSupport (productWeightedPartial φ i j) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (productWeightedPartial_support i j)

theorem productWeightedPartial_contDiff {φ : ProductSpace ι → ℂ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : tsupport φ ⊆ productUpper ι) (i : ι) (j : Fin 3) :
    ContDiff ℝ 1 (productWeightedPartial φ i j) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p ∈ productUpper ι
  · exact productWeightedPartial_contDiffAt hφ.contDiffAt hp i j
  · have hn : p ∉ tsupport (productWeightedPartial φ i j) :=
      fun h => hp (hsupp (productWeightedPartial_support i j h))
    exact (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : ProductSpace ι => (0 : ℂ)) p).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hn)

theorem productWeightedPartial_second_continuous {φ : ProductSpace ι → ℂ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : tsupport φ ⊆ productUpper ι) (i : ι) (j : Fin 3) :
    Continuous (productPartial (productWeightedPartial φ i j) i j) :=
  (((productWeightedPartial_contDiff hφ hsupp i j).fderiv_right (m := 0) (by norm_num)).clm_apply
    contDiff_const).continuous

theorem productWeightedPartial_second_support {φ : ProductSpace ι → ℂ} (i : ι) (j : Fin 3) :
    tsupport (productPartial (productWeightedPartial φ i j) i j) ⊆ tsupport φ :=
  (product_test_partial_support i j).trans (productWeightedPartial_support i j)

theorem productLaplacian_zero_notMem_tsupport {φ : ProductSpace ι → ℂ} {p : ProductSpace ι}
    (hp : p ∉ tsupport φ) : productLaplacian φ p = 0 := by
  have hfirst (i : ι) (j : Fin 3) : productPartial φ i j p = 0 := by
    rw [productPartial,fderiv_of_notMem_tsupport ℝ hp]
    rfl
  have hsecond (i : ι) (j : Fin 3) : productPartial (productPartial φ i j) i j p = 0 := by
    rw [productPartial,fderiv_of_notMem_tsupport ℝ (fun h => hp (product_test_partial_support i j h))]
    rfl
  simp only [productLaplacian,blockLaplacian,hfirst,hsecond,Finset.sum_const_zero,mul_zero,add_zero]

theorem otherWeight_star (p : ProductSpace ι) (i : ι) : star (otherWeight i p) = otherWeight i p := by
  simp [otherWeight]

theorem productWeightedPartial_star_pair (φ f : ProductSpace ι → ℂ)
    (p : ProductSpace ι) (i : ι) (j : Fin 3) :
    star (productWeightedPartial φ i j p) * productPartial f i j p =
      star (productPartial φ i j p) * productWeightedPartial f i j p := by
  have hy : star (p i 2 : ℂ) = (p i 2 : ℂ) := by simp
  simp only [productWeightedPartial,star_div₀,star_mul,otherWeight_star,hy]
  ring

theorem product_adjoint_green_direction {φ f : ProductSpace ι → ℂ}
    (hf : ∀ p ∈ productUpper ι, ContDiffAt ℝ 2 f p)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) (i : ι) (j : Fin 3) :
    (∫ p, star (productWeightedPartial φ i j p) * productPartial f i j p) =
      -(∫ p, star (productPartial (productWeightedPartial φ i j) i j p) * f p) := by
  have hW := productWeightedPartial_contDiff hφ hsupp i j
  have hcW := productWeightedPartial_compact hc i j
  have h₁ : Integrable (fun p => star (productPartial (productWeightedPartial φ i j) i j p) * f p) volume := by
    apply product_compact_star_mul_integrable (productWeightedPartial_second_continuous hφ hsupp i j)
      (product_test_partial_compact hcW i j)
    intro p hp
    exact (hf p (hsupp (productWeightedPartial_second_support i j hp))).continuousAt
  have h₂ : Integrable (fun p => star (productWeightedPartial φ i j p) * productPartial f i j p) volume := by
    apply product_compact_star_mul_integrable hW.continuous hcW
    intro p hp
    exact (productPartial_contDiffAt (hf p (hsupp (productWeightedPartial_support i j hp))) i j).continuousAt
  have h₃ : Integrable (fun p => star (productWeightedPartial φ i j p) * f p) volume := by
    apply product_compact_star_mul_integrable hW.continuous hcW
    intro p hp
    exact (hf p (hsupp (productWeightedPartial_support i j hp))).continuousAt
  exact integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (μ := volume) (B := complexHermitianBilin) (f := productWeightedPartial φ i j) (g := f)
    (v := productDirection i j) h₁ h₂ h₃
    (fun _ _ => hW.contDiffAt.differentiableAt (by norm_num))
    (fun p hp => (hf p (hsupp (productWeightedPartial_support i j hp))).differentiableAt (by norm_num))

end
end ArtinMatthews.SourceHyperbolicGreen
