module

public import ArtinMatthews.SpectralCuspMass
public import ArtinMatthews.SpectralGamma0Core
public import ArtinMatthews.SpectralCompactChartCover
public import ArtinMatthews.SpectralCuspModularCover
public import ArtinMatthews.SpectralFiniteCoverIntegral
public import ArtinMatthews.SpectralGamma0CompactMass
public import ArtinMatthews.SpectralGamma0CosetCharts
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! Actual cusp-strip restriction bounds in the full mass norm.  These bounds
do not use the derivative part of the completed energy norm. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0Seed_chart_mass_le (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (δ : SL(2, ℤ)) :
    (∫ z in ModularGroup.fd, ‖gamma0PoincareSeed N ψ.val (δ⁻¹ • z)‖ ^ 2) ≤
      ‖gamma0SmoothSeedMass N ψ‖ ^ 2 := by
  rw [gamma0SmoothSeedMass_norm_sq]
  have he : (fun z : UpperHalfPlane => ‖gamma0PoincareSeed N ψ.val (δ⁻¹ • z)‖ ^ 2) =
      fun z => ‖gamma0PoincareSeed N ψ.val
        ((QuotientGroup.mk δ : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N).out⁻¹ • z)‖ ^ 2 := by
    funext z
    rw [gamma0_inverse_chart_representative N _ (gamma0PoincareSeed_invariant N ψ.val)]
  rw [he]
  apply Finset.single_le_sum (s := Finset.univ)
    (a := (QuotientGroup.mk δ : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N))
    (f := fun q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N =>
      ∫ z in ModularGroup.fd, ‖gamma0PoincareSeed N ψ.val (q.out⁻¹ • z)‖ ^ 2)
  · exact fun _ _ => integral_nonneg (fun _ => sq_nonneg _)
  · exact Finset.mem_univ _

private theorem modular_embedding (δ : SL(2, ℤ)) :
    MeasurableEmbedding (fun z : UpperHalfPlane => δ • z) := by
  change MeasurableEmbedding
    (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ δ • z)
  exact measurableEmbedding_const_smul _

private theorem gamma0_finite_cover_mass_bound (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) (K : Set UpperHalfPlane)
    (hK : MeasurableSet K) (s : Finset SL(2, ℤ))
    (hs : K ⊆ ⋃ δ ∈ s, (fun z : UpperHalfPlane => δ • z) ⁻¹' ModularGroup.fd) :
    IntegrableOn (fun z => ‖gamma0PoincareSeed N ψ.val (r⁻¹ • z)‖ ^ 2) K ∧
    (∫ z in K, ‖gamma0PoincareSeed N ψ.val (r⁻¹ • z)‖ ^ 2) ≤
      (s.card : ℝ) * ‖gamma0SmoothSeedMass N ψ‖ ^ 2 := by
  let f : UpperHalfPlane → ℝ := fun z => ‖gamma0PoincareSeed N ψ.val (r⁻¹ • z)‖ ^ 2
  have hc : Continuous f := ((gamma0PoincareSeed N ψ.val).continuous.comp
    (continuous_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ r⁻¹))).norm.pow 2
  have hfd (δ : SL(2, ℤ)) : IntegrableOn (fun z => f (δ⁻¹ • z)) ModularGroup.fd := by
    simpa only [f, mul_inv_rev, mul_smul, IntegrableOn] using
      (gamma0PoincareSeed_memLp_modularRegion N ψ.val (δ * r)⁻¹).integrable_norm_pow
        (by norm_num)
  have hi (δ : SL(2, ℤ)) : IntegrableOn f
      ((fun z : UpperHalfPlane => δ • z) ⁻¹' ModularGroup.fd) := by
    have he := ((h2_integer_measurePreserving δ).restrict_preimage_emb
      (modular_embedding δ) ModularGroup.fd).integrable_comp_emb (modular_embedding δ)
      (g := fun z => f (δ⁻¹ • z))
    simpa only [Function.comp_def, IntegrableOn, inv_smul_smul] using he.mpr (hfd δ)
  have hb (δ : SL(2, ℤ)) :
      (∫ z in (fun z : UpperHalfPlane => δ • z) ⁻¹' ModularGroup.fd, f z) ≤
        ‖gamma0SmoothSeedMass N ψ‖ ^ 2 := by
    have he := (h2_integer_measurePreserving δ).setIntegral_preimage_emb
      (modular_embedding δ) (fun z => f (δ⁻¹ • z)) ModularGroup.fd
    simp only [inv_smul_smul] at he
    rw [he]
    simpa only [f, mul_inv_rev, mul_smul] using gamma0Seed_chart_mass_le N ψ (δ * r)
  have hcov := finite_cover_integrable_integral_le_sum volume s
    (fun δ : SL(2, ℤ) => (fun z : UpperHalfPlane => δ • z) ⁻¹' ModularGroup.fd)
    hK (fun δ _ => ModularGroup.isClosed_fd.measurableSet.preimage
      (h2_integer_measurePreserving δ).measurable) hs f (fun _ => sq_nonneg _)
      hc.aestronglyMeasurable (fun δ _ => hi δ)
  refine ⟨hcov.1, hcov.2.trans ?_⟩
  calc
    _ ≤ ∑ _δ ∈ s, ‖gamma0SmoothSeedMass N ψ‖ ^ 2 :=
      Finset.sum_le_sum (fun δ _ => hb δ)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

theorem compact_chart_gamma0_cusp_mass_bound {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ C > 0, ∀ (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)),
      (∫ z in K, ‖gamma0PoincareSeed N ψ.val (r⁻¹ • z)‖ ^ 2) ≤
        C * ‖gamma0SmoothSeedMass N ψ‖ ^ 2 := by
  obtain ⟨s, hs⟩ := compact_modular_region_cover hK
  refine ⟨(s.card : ℝ) + 1, by positivity, fun N _ ψ r => ?_⟩
  have hb := (gamma0_finite_cover_mass_bound N ψ r K hK.measurableSet s hs).2
  exact hb.trans (by nlinarith [sq_nonneg ‖gamma0SmoothSeedMass N ψ‖])

theorem gamma0_cusp_strip_mass_bound (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) :
    IntegrableOn (fun z => ‖gamma0PoincareSeed N ψ.val (r⁻¹ • z)‖ ^ 2)
      (hyperbolicCuspStrip (N : ℝ) 1) ∧
    (∫ z in hyperbolicCuspStrip (N : ℝ) 1,
      ‖gamma0PoincareSeed N ψ.val (r⁻¹ • z)‖ ^ 2) ≤
        ((N : ℝ) + 1) * ‖gamma0SmoothSeedMass N ψ‖ ^ 2 := by
  have hS : MeasurableSet (hyperbolicCuspStrip (N : ℝ) 1) :=
    (measurableSet_Ioc.preimage UpperHalfPlane.continuous_re.measurable).inter
      (measurableSet_Ioi.preimage UpperHalfPlane.continuous_im.measurable)
  have hb := gamma0_finite_cover_mass_bound N ψ r _ hS
    (Finset.image (fun k : ℤ => ModularGroup.T ^ (-k)) (Finset.Icc 0 (N : ℤ))) (by
      intro z hz
      obtain ⟨k, hk, hg⟩ := mem_iUnion₂.mp (cusp_strip_modular_cover N hz)
      exact mem_iUnion₂.mpr ⟨_, Finset.mem_image.mpr ⟨k, hk, rfl⟩, hg⟩)
  refine ⟨hb.1, hb.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hcard : (Finset.Icc (0 : ℤ) (N : ℤ)).card = N + 1 := by
    rw [Int.card_Icc]
    omega
  have hc := Finset.card_image_le (s := Finset.Icc (0 : ℤ) (N : ℤ))
    (f := fun k : ℤ => ModularGroup.T ^ (-k))
  exact_mod_cast hc.trans_eq hcard

end ArtinMatthews
