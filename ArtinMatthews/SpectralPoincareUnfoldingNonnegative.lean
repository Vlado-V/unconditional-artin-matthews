module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.NumberTheory.Modular
public import ArtinMatthews.SpectralGamma0CompactMass
public import ArtinMatthews.SpectralModularBoundary
public import ArtinMatthews.SpectralModularPartition
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine Tonelli unfolding for nonnegative functions, without compact
support.  The modular covering has its proved central multiplicity two. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ENNReal

namespace ArtinMatthews

theorem modular_fdo_indicator_tsum_ennreal (F : UpperHalfPlane → ℝ≥0∞)
    {z : UpperHalfPlane} (hz : ∃ g : SL(2, ℤ), g • z ∈ ModularGroup.fdo) :
    (∑' g : SL(2, ℤ), ((fun w : UpperHalfPlane => g • w) ⁻¹' ModularGroup.fdo).indicator F z) =
      2 * F z := by
  classical
  obtain ⟨g, hg⟩ := hz
  have hne : g ≠ -g := by
    intro h
    have he := congrArg (fun a : SL(2, ℤ) => a * g⁻¹) h
    have hs : (1 : SL(2, ℤ)) = -1 := by simpa only [neg_mul, mul_inv_cancel] using he
    have he' := congrArg (fun a : SL(2, ℤ) => a 0 0) hs
    norm_num at he'
  have hs (δ : SL(2, ℤ)) (hδ : δ ∉ ({g, -g} : Finset SL(2, ℤ))) :
      ((fun w : UpperHalfPlane => δ • w) ⁻¹' ModularGroup.fdo).indicator F z = 0 := by
    have hnot : δ • z ∉ ModularGroup.fdo := by
      intro hdz
      have hc := modular_interior_overlap_central hg (ModularGroup.fdo_subset_fd hdz)
      apply hδ
      rcases hc with hc | hc
      · have he := congrArg (fun a : SL(2, ℤ) => a * g) hc
        have hd : δ = g := by simpa only [mul_assoc, inv_mul_cancel, mul_one, one_mul] using he
        exact Finset.mem_insert.mpr (Or.inl hd)
      · have he := congrArg (fun a : SL(2, ℤ) => a * g) hc
        have hd : δ = -g := by simpa only [mul_assoc, inv_mul_cancel, mul_one, neg_one_mul] using he
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hd))
    exact indicator_of_notMem
      (show z ∉ (fun w : UpperHalfPlane => δ • w) ⁻¹' ModularGroup.fdo from hnot) F
  rw [tsum_eq_sum hs, Finset.sum_pair hne]
  have hng : (-g) • z ∈ ModularGroup.fdo := by
    rw [ModularGroup.SL_neg_smul]
    exact hg
  rw [indicator_of_mem
    (show z ∈ (fun w : UpperHalfPlane => g • w) ⁻¹' ModularGroup.fdo from hg),
    indicator_of_mem
    (show z ∈ (fun w : UpperHalfPlane => (-g) • w) ⁻¹' ModularGroup.fdo from hng), two_mul]

theorem modular_lintegral_tsum_eq_two_lintegral (F : UpperHalfPlane → ℝ≥0∞)
    (hF : Measurable F) :
    (∑' g : SL(2, ℤ), ∫⁻ z in ModularGroup.fd, F (g⁻¹ • z)) = 2 * ∫⁻ z, F z := by
  let : Countable (Matrix (Fin 2) (Fin 2) ℤ) :=
    inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  let : Countable (SL(2, ℤ)) :=
    (show Function.Injective (fun g : SL(2, ℤ) => g.val) from Subtype.val_injective).countable
  let D (g : SL(2, ℤ)) := (fun z : UpperHalfPlane => g • z) ⁻¹' ModularGroup.fdo
  have hD (g : SL(2, ℤ)) : MeasurableSet (D g) :=
    ModularGroup.isOpen_fdo.measurableSet.preimage (h2_integer_measurePreserving g).measurable
  have hchange (g : SL(2, ℤ)) :
      (∫⁻ z, (D g).indicator F z) = ∫⁻ z in ModularGroup.fd, F (g⁻¹ • z) := by
    rw [lintegral_indicator (hD g), modular_restrict_fd_eq_fdo]
    have hme : MeasurableEmbedding (fun z : UpperHalfPlane => g • z) := by
      change MeasurableEmbedding
        (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ g • z)
      exact measurableEmbedding_const_smul _
    simpa only [inv_smul_smul, D] using
      (h2_integer_measurePreserving g).setLIntegral_comp_preimage_emb hme
        (fun z : UpperHalfPlane => F (g⁻¹ • z)) ModularGroup.fdo
  calc
    _ = ∑' g : SL(2, ℤ), ∫⁻ z, (D g).indicator F z := tsum_congr fun g => (hchange g).symm
    _ = ∫⁻ z, ∑' g : SL(2, ℤ), (D g).indicator F z :=
      (lintegral_tsum fun g => (hF.indicator (hD g)).aemeasurable).symm
    _ = ∫⁻ z, 2 * F z := by
      apply lintegral_congr_ae
      filter_upwards [modular_exists_smul_mem_fdo_ae] with z hz
      exact modular_fdo_indicator_tsum_ennreal F hz
    _ = 2 * ∫⁻ z, F z := lintegral_const_mul 2 hF

end ArtinMatthews
