module

public import ArtinMatthews.SourceKPCompactCoreLocalization
public import ArtinMatthews.SourceHyperbolicH1Measure
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

namespace ArtinMatthews.SourceHyperbolicGreen
open MeasureTheory Filter
open scoped Topology ContDiff InnerProductSpace
noncomputable section

variable {ι : Type*} [Fintype ι]

theorem h1TestMass_norm_sq {n : ℕ∞ω} (f : h1Tests ι n) :
    ‖h1TestMass f‖^2 = ∫ x, ‖f.val x‖^2 ∂productVolume ι := by
  have h : inner ℂ (h1TestMass f) (h1TestMass f) =
      (∫ x, ‖f.val x‖^2 ∂productVolume ι : ℝ) := by
    rw [L2.inner_def,← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [h1TestMass_coe f] with x hx
    rw [hx,inner_self_eq_norm_sq_to_K,RCLike.ofReal_eq_complex_ofReal,← Complex.ofReal_pow]
  rw [inner_self_eq_norm_sq_to_K,RCLike.ofReal_eq_complex_ofReal,← Complex.ofReal_pow] at h
  exact Complex.ofReal_injective h

theorem h1LocalTest_mass_norm_sq (U : Set (ProductSpace ι)) (f : h1LocalTests U) :
    ‖h1TestMass f.val‖^2 = ∫ x in U, ‖f.val.val x‖^2 ∂productVolume ι := by
  rw [h1TestMass_norm_sq]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun h => hx (f.prop h)),norm_zero,zero_pow (by decide)]

end
end ArtinMatthews.SourceHyperbolicGreen

namespace ArtinMatthews
open MeasureTheory Filter SourceHyperbolicGreen
open scoped Topology ContDiff
noncomputable section

variable {ι : Type*} [Fintype ι]

theorem h1LocalTestMul_mass_norm_sq_le
    (U : Set (ProductSpace ι)) (hU : IsOpen U) (hUupper : U ⊆ productUpper ι)
    (η : h1LocalTests U) (F : ProductSpace ι → ℂ) (hF : ContDiffOn ℝ 2 F U)
    (M : ℝ) (hη : ∀ x ∈ U, ‖η.val.val x‖ ≤ M)
    (hMassInt : IntegrableOn (fun x => ‖F x‖^2) U (productVolume ι)) :
    ‖h1TestMass (h1LocalTestMul U hU hUupper η F hF).val‖^2 ≤
      M^2*(∫ x in U, ‖F x‖^2 ∂productVolume ι) := by
  let g := h1LocalTestMul U hU hUupper η F hF
  have hg : Integrable (fun x => ‖g.val.val x‖^2) (productVolume ι) :=
    (memLp_two_iff_integrable_sq_norm g.val.prop.1.continuous.aestronglyMeasurable).mp
      (h1_compact_memLp g.val.prop.1.continuous g.val.prop.2.1 g.val.prop.2.2 2)
  calc
    _ = ∫ x in U, ‖g.val.val x‖^2 ∂productVolume ι := h1LocalTest_mass_norm_sq U g
    _ ≤ ∫ x in U, M^2*‖F x‖^2 ∂productVolume ι := by
      apply integral_mono_ae hg.integrableOn (hMassInt.const_mul (M^2))
      filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
      change ‖η.val.val x*F x‖^2 ≤ _
      rw [norm_mul,mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hη x hx) 2) (sq_nonneg _)
    _ = _ := by rw [integral_const_mul]

end
end ArtinMatthews
