module

public import ArtinMatthews.SpectralGamma0CompactMass
public import ArtinMatthews.SpectralCutoffMassBound
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Exact global mass remainder and its actual modular-tail bound. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups

namespace ArtinMatthews

variable (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ}
  (ha : 0 < a) (hab : a ≤ b) (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b)

theorem gamma0CompactMassMap_seed_remainder_norm_sq (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) :
    ‖gamma0EnergyInclusion N (gamma0EnergyTest N ψ)-
        gamma0CompactMassMap φ ha hab hφ N (gamma0EnergyTest N ψ)‖^2 =
      ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
        ∫ z in ModularGroup.fd,
          ‖(1-φ ((q.out⁻¹ • z).re,(q.out⁻¹ • z).im))*gamma0PoincareSeed N ψ.val (q.out⁻¹ • z)‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro q _
  change ‖gamma0EnergyInclusion N (gamma0EnergyTest N ψ) q-
    gamma0CompactMassMap φ ha hab hφ N (gamma0EnergyTest N ψ) q‖^2 = _
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [gamma0SeedMass_coeFn N ψ.val q,
    gamma0CompactMassMap_seed_ae φ ha hab hφ N ψ q,
    Lp.coeFn_sub (gamma0EnergyInclusion N (gamma0EnergyTest N ψ) q)
      (gamma0CompactMassMap φ ha hab hφ N (gamma0EnergyTest N ψ) q)] with z hm hc hd
  rw [real_inner_self_eq_norm_sq,hd]
  change ‖(gamma0SeedMass N ψ.val q) z-
    (gamma0CompactMassMap φ ha hab hφ N (gamma0EnergyTest N ψ) q) z‖^2 = _
  rw [hm,hc,sub_mul,one_mul]

theorem gamma0CompactMassMap_seed_remainder_tail_le (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (Y : ℝ)
    (hplateau : ∀ (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane),
      z ∈ ModularGroup.fd → z.im ≤ Y → φ ((q.out⁻¹ • z).re,(q.out⁻¹ • z).im) = 1)
    (hres : ∀ p, ‖1-φ p‖ ≤ 1) :
    ‖gamma0EnergyInclusion N (gamma0EnergyTest N ψ)-
        gamma0CompactMassMap φ ha hab hφ N (gamma0EnergyTest N ψ)‖^2 ≤
      ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
        ∫ z in {z : UpperHalfPlane | z ∈ ModularGroup.fd ∧ Y < z.im},
          ‖gamma0PoincareSeed N ψ.val (q.out⁻¹ • z)‖^2 := by
  rw [gamma0CompactMassMap_seed_remainder_norm_sq]
  apply Finset.sum_le_sum
  intro q _
  have hmem := gamma0PoincareSeed_memLp_modularRegion N ψ.val q.out⁻¹
  have hact : Continuous (fun z : UpperHalfPlane => q.out⁻¹ • z) := by
    change Continuous (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ q.out⁻¹ • z)
    exact continuous_const_smul _
  have hc : Continuous (fun z : UpperHalfPlane => φ ((q.out⁻¹ • z).re,(q.out⁻¹ • z).im)) :=
    φ.continuous.comp ((UpperHalfPlane.continuous_re.comp hact).prodMk
      (UpperHalfPlane.continuous_im.comp hact))
  have hT : MeasurableSet {z : UpperHalfPlane | Y < z.im} :=
    measurableSet_Ioi.preimage UpperHalfPlane.continuous_im.measurable
  have h := (cutoff_residual_mass_le (volume.restrict ModularGroup.fd)
    (fun z : UpperHalfPlane => gamma0PoincareSeed N ψ.val (q.out⁻¹ • z))
    (fun z => φ ((q.out⁻¹ • z).re,(q.out⁻¹ • z).im)) hT
    (hmem.integrable_norm_pow (by norm_num)) hmem.aestronglyMeasurable hc.aestronglyMeasurable
    (fun z => hres _) (by
      filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
      intro hnot
      exact hplateau q z hz (le_of_not_gt hnot))).2
  rw [Measure.restrict_restrict hT] at h
  simpa only [inter_comm,inter_def,mem_ofPred_eq] using h

end ArtinMatthews
