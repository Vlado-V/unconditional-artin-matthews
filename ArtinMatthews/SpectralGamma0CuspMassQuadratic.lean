module

public import ArtinMatthews.SpectralGamma0CuspMassRestriction
public import ArtinMatthews.SpectralGamma0CompactMass
public import ArtinMatthews.SpectralGamma0CosetCharts
public import ArtinMatthews.SpectralModularDensity
public import ArtinMatthews.SpectralModularStripCount
public import ArtinMatthews.SpectralPoincareUnfoldingNonnegative
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Actual quadratic mass growth near height zero.  The proof uses genuine
Tonelli unfolding and the proved finite modular strip multiplicity bound. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ENNReal

namespace ArtinMatthews

theorem gamma0_cusp_positive_height_mass_quadratic (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (hY1 : Y ≤ 1) :
    (∫ z in hyperbolicCuspStrip (N : ℝ) Y,
      ‖gamma0CuspSection N ψ r z‖ ^ 2) ≤
        (25 * ((N : ℝ) + 1) / Y ^ 2) * ‖gamma0SmoothSeedMass N ψ‖ ^ 2 := by
  classical
  let : Countable (Matrix (Fin 2) (Fin 2) ℤ) :=
    inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  let : Countable (SL(2, ℤ)) :=
    (show Function.Injective (fun g : SL(2, ℤ) => g.val) from Subtype.val_injective).countable
  let F := gamma0PoincareSeed N ψ.val
  let S := hyperbolicCuspStrip (N : ℝ) Y
  let C : ℝ := 25 * ((N : ℝ) + 1) / Y ^ 2
  let W : UpperHalfPlane → ℝ≥0∞ := fun z => ENNReal.ofReal (‖F (r⁻¹ • z)‖ ^ 2)
  let J := S.indicator W
  let G : UpperHalfPlane → ℝ := fun z =>
    ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, ‖F (q.out⁻¹ • z)‖ ^ 2
  have hC : 0 ≤ C := by positivity
  have hS : MeasurableSet S :=
    (measurableSet_Ioc.preimage UpperHalfPlane.continuous_re.measurable).inter
      (measurableSet_Ioi.preimage UpperHalfPlane.continuous_im.measurable)
  have hW : Measurable W :=
    (ENNReal.continuous_ofReal.comp ((F.continuous.comp
      (continuous_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ r⁻¹))).norm.pow 2)).measurable
  have hJ : Measurable J := hW.indicator hS
  have hG : Measurable (fun z => ENNReal.ofReal (G z)) := by
    apply ENNReal.measurable_ofReal.comp
    exact Finset.measurable_sum Finset.univ fun q _ =>
      ((F.continuous.comp (continuous_const_smul
        (Matrix.SpecialLinearGroup.mapGL ℝ q.out⁻¹))).norm.pow 2).measurable
  have hGi : IntegrableOn G ModularGroup.fd :=
    integrable_finsetSum Finset.univ fun q _ =>
      (gamma0PoincareSeed_memLp_modularRegion N ψ.val q.out⁻¹).integrable_norm_pow (by norm_num)
  have hG0 : ∀ z, 0 ≤ G z := fun z => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hGn : (∫ z in ModularGroup.fd, G z) = ‖gamma0SmoothSeedMass N ψ‖ ^ 2 := by
    rw [gamma0SmoothSeedMass_norm_sq]
    exact integral_finsetSum Finset.univ fun q _ =>
      (gamma0PoincareSeed_memLp_modularRegion N ψ.val q.out⁻¹).integrable_norm_pow (by norm_num)
  have hpoint (z : UpperHalfPlane) (hz : z ∈ ModularGroup.fd) :
      (∑' δ : SL(2, ℤ), J (δ⁻¹ • z)) ≤ ENNReal.ofReal C * ENNReal.ofReal (G z) := by
    let hf := spectralModular_inverse_strip_finite N Y hY hY1 z hz
    let s := hf.toFinset
    have hcard : (s.card : ℝ) ≤ C := by
      have hc := spectralModular_inverse_strip_ncard_le N Y hY hY1 z hz
      rw [Set.ncard_eq_toFinset_card _ hf] at hc
      exact hc
    have hcard' : (s.card : ℝ≥0∞) ≤ ENNReal.ofReal C := by
      simpa using ENNReal.ofReal_le_ofReal hcard
    have ht : (∑' δ : SL(2, ℤ), J (δ⁻¹ • z)) = ∑ δ ∈ s, J (δ⁻¹ • z) := by
      apply tsum_eq_sum
      intro δ hδ
      change S.indicator W (δ⁻¹ • z) = 0
      apply indicator_of_notMem
      exact fun h => hδ (hf.mem_toFinset.mpr h)
    rw [ht]
    calc
      _ ≤ ∑ _δ ∈ s, ENNReal.ofReal (G z) := by
        apply Finset.sum_le_sum
        intro δ hδ
        change S.indicator W (δ⁻¹ • z) ≤ _
        rw [indicator_of_mem (show δ⁻¹ • z ∈ S from hf.mem_toFinset.mp hδ)]
        apply ENNReal.ofReal_le_ofReal
        have he := gamma0_inverse_chart_representative N F
          (gamma0PoincareSeed_invariant N ψ.val) (δ * r) z
        change ‖F (r⁻¹ • (δ⁻¹ • z))‖ ^ 2 ≤ G z
        rw [← mul_smul, ← mul_inv_rev, he]
        apply Finset.single_le_sum (s := Finset.univ)
          (a := (QuotientGroup.mk (δ * r) : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N))
          (f := fun q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N => ‖F (q.out⁻¹ • z)‖ ^ 2)
        · exact fun _ _ => sq_nonneg _
        · exact Finset.mem_univ _
      _ = (s.card : ℝ≥0∞) * ENNReal.ofReal (G z) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul hcard' le_rfl (by positivity) (by positivity)
  have hton := modular_lintegral_tsum_eq_two_lintegral J hJ
  rw [lintegral_indicator hS] at hton
  have hbound : (∫⁻ z in S, W z) ≤ ENNReal.ofReal C * ENNReal.ofReal (‖gamma0SmoothSeedMass N ψ‖ ^ 2) := by
    calc
      _ ≤ 2 * ∫⁻ z in S, W z := by
        simpa only [one_mul] using mul_le_mul
          (by norm_num : (1 : ℝ≥0∞) ≤ 2) (le_rfl : (∫⁻ z in S, W z) ≤ ∫⁻ z in S, W z)
          (by positivity) (by positivity)
      _ = ∑' δ : SL(2, ℤ), ∫⁻ z in ModularGroup.fd, J (δ⁻¹ • z) := hton.symm
      _ = ∫⁻ z in ModularGroup.fd, ∑' δ : SL(2, ℤ), J (δ⁻¹ • z) :=
        (lintegral_tsum fun δ =>
          (hJ.comp (h2_integer_measurePreserving δ⁻¹).measurable).aemeasurable).symm
      _ ≤ ∫⁻ z in ModularGroup.fd, ENNReal.ofReal C * ENNReal.ofReal (G z) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
        exact hpoint z hz
      _ = ENNReal.ofReal C * ∫⁻ z in ModularGroup.fd, ENNReal.ofReal (G z) :=
        lintegral_const_mul _ hG
      _ = _ := by rw [← ofReal_integral_eq_lintegral_ofReal hGi (Eventually.of_forall hG0), hGn]
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (sq_nonneg _))).mp
  rw [ENNReal.ofReal_mul hC]
  rw [ofReal_integral_eq_lintegral_ofReal
    ((gamma0CuspSection_memLp_positive_height N ψ r Y hY).integrable_norm_pow (by norm_num))
    (Eventually.of_forall (fun _ => sq_nonneg _))]
  exact hbound

theorem gamma0CuspMassRestriction_norm_sq_quadratic (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (hY1 : Y ≤ 1) (f : Gamma0RegionL2 N) :
    ‖gamma0CuspMassRestriction N r Y hY f‖ ^ 2 ≤
      (25 * ((N : ℝ) + 1) / Y ^ 2) * ‖f‖ ^ 2 := by
  apply isClosed_property (gamma0SmoothSeedMass_denseRange N)
    (isClosed_le ((gamma0CuspMassRestriction N r Y hY).continuous.norm.pow 2)
      (continuous_const.mul (continuous_norm.pow 2)))
  intro ψ
  change ‖gamma0CuspMassRestriction N r Y hY (gamma0SmoothSeedMass N ψ)‖ ^ 2 ≤
    (25 * ((N : ℝ) + 1) / Y ^ 2) * ‖gamma0SmoothSeedMass N ψ‖ ^ 2
  rw [gamma0CuspMassRestriction_apply]
  change ‖(gamma0CuspSection_memLp_positive_height N ψ r Y hY).toLp
    (gamma0CuspSection N ψ r)‖ ^ 2 ≤ _
  rw [spectral_cusp_toLp_norm_square]
  exact gamma0_cusp_positive_height_mass_quadratic N ψ r Y hY hY1

end ArtinMatthews
