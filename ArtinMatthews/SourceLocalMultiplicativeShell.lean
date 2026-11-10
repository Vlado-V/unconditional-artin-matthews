module

public import ArtinMatthews.SourceLocalMultiplicativeMeasure
public import ArtinMatthews.StandardLocalConductor
public import Mathlib.Order.CompletePartialOrder
public import ArtinMatthews.StandardLocalBallDilation
public import ArtinMatthews.StandardLocalHaarScaling
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Topology.Algebra.IsOpenUnits
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact valuation shells on the multiplicative group. Their mass is
independent of the radius, with the actual self-dual normalization. -/

namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain MeasureTheory Set Topology Function
open scoped NumberField ENNReal NNReal
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (P : HeightOneSpectrum (𝓞 K))

local notation "k" => P.adicCompletion K
local notation "q" => (Ideal.absNorm P.asIdeal : ℝ)

def sourceLocalMulBall (n : ℤ) : Set kˣ := Units.val ⁻¹' sourceLocalBall K P n

def sourceLocalMulShell (n : ℤ) : Set kˣ :=
  Units.val ⁻¹' (sourceLocalBall K P n \ sourceLocalBall K P (n - 1))

theorem sourceLocalMulBall_measurable (n : ℤ) : MeasurableSet (sourceLocalMulBall K P n) :=
  (sourceLocalBall_isOpen K P n).measurableSet.preimage (sourceLocalUnits_measurableEmbedding K P).measurable

theorem sourceLocalMulShell_measurable (n : ℤ) : MeasurableSet (sourceLocalMulShell K P n) :=
  ((sourceLocalBall_isOpen K P n).measurableSet.diff
    (sourceLocalBall_isOpen K P (n - 1)).measurableSet).preimage
      (sourceLocalUnits_measurableEmbedding K P).measurable

theorem sourceLocalBall_sdiff_ne_zero (n : ℤ) {x : k}
    (hx : x ∈ sourceLocalBall K P n \ sourceLocalBall K P (n - 1)) : x ≠ 0 := by
  intro h
  apply hx.2
  simp [sourceLocalBall, h]

theorem sourceLocalBall_sdiff_log (n : ℤ) {x : k}
    (hx : x ∈ sourceLocalBall K P n \ sourceLocalBall K P (n - 1)) :
    WithZero.log (sourceLocalValuation K P x) = n := by
  have hv : sourceLocalValuation K P x ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (sourceLocalBall_sdiff_ne_zero K P n hx)
  have h1 : WithZero.log (sourceLocalValuation K P x) ≤ n :=
    (WithZero.log_le_iff_le_exp hv).mpr hx.1
  have h2 : ¬ WithZero.log (sourceLocalValuation K P x) ≤ n - 1 :=
    fun h => hx.2 ((WithZero.log_le_iff_le_exp hv).mp h)
  omega

theorem sourceLocalMulShell_log_iff (n : ℤ) (u : kˣ) :
    u ∈ sourceLocalMulShell K P n ↔ WithZero.log (sourceLocalValuation K P (u : k)) = n := by
  constructor
  · exact sourceLocalBall_sdiff_log K P n
  · intro hn
    have hv : sourceLocalValuation K P (u : k) ≠ 0 := (Valuation.ne_zero_iff _).mpr u.ne_zero
    refine ⟨(WithZero.log_le_iff_le_exp hv).mp hn.le, ?_⟩
    intro h
    have h' := (WithZero.log_le_iff_le_exp hv).mpr
      (show sourceLocalValuation K P (u : k) ≤ WithZero.exp (n - 1) from h)
    omega

theorem sourceLocalMulShell_norm (n : ℤ) {u : kˣ} (hu : u ∈ sourceLocalMulShell K P n) :
    ‖(u : k)‖ = q ^ n := by
  rw [sourceLocalNorm_eq_zpow K P (u : k) u.ne_zero, (sourceLocalMulShell_log_iff K P n u).mp hu]

theorem sourceLocalMulShell_image (n : ℤ) :
    (Units.val : kˣ → k) '' sourceLocalMulShell K P n =
      sourceLocalBall K P n \ sourceLocalBall K P (n - 1) := by
  rw [sourceLocalMulShell, image_preimage_eq_inter_range, sourceLocalUnits_range,
    inter_eq_self_of_subset_left]
  exact fun x hx => sourceLocalBall_sdiff_ne_zero K P n hx

theorem sourceLocalMulShell_isCompact (n : ℤ) : IsCompact (sourceLocalMulShell K P n) := by
  rw [(IsOpenUnits.isOpenEmbedding_unitsVal (M := k)).isEmbedding.isCompact_iff,
    sourceLocalMulShell_image]
  exact (sourceLocalBall_isCompact K P n).diff (sourceLocalBall_isOpen K P (n - 1))

theorem sourceLocalMulShell_mass (n : ℤ) :
    (sourceLocalMulMeasure K P).real (sourceLocalMulShell K P n) =
      (sourceLocalSelfDual K P).real (sourceLocalBall K P 0) * (1 - q⁻¹) := by
  let μ := sourceLocalSelfDual K P
  let c := μ.real (sourceLocalBall K P 0)
  let : μ.IsAddHaarMeasure := sourceLocalSelfDual_isHaar K P
  let B := sourceLocalBall K P n \ sourceLocalBall K P (n - 1)
  have hB : MeasurableSet B := (sourceLocalBall_isOpen K P n).measurableSet.diff
    (sourceLocalBall_isOpen K P (n - 1)).measurableSet
  have hd : (∫⁻ x in B, sourceLocalMulDensity K P x ∂μ) =
      ∫⁻ _ in B, ENNReal.ofReal ((q ^ n)⁻¹) ∂μ := by
    apply setLIntegral_congr_fun hB
    intro x hx
    rw [sourceLocalMulDensity_eq,
      sourceLocalNorm_eq_zpow K P x (sourceLocalBall_sdiff_ne_zero K P n hx),
      sourceLocalBall_sdiff_log K P n hx]
  have hq := sourceLocalNorm_pos K P
  have hsub : sourceLocalBall K P (n - 1) ⊆ sourceLocalBall K P n := by
    intro x hx
    exact le_trans hx (WithZero.exp_le_exp.mpr (by omega))
  rw [measureReal_def, sourceLocalMulMeasure_apply K P _ (sourceLocalMulShell_measurable K P n),
    sourceLocalMulShell_image, hd, setLIntegral_const, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (zpow_nonneg hq.le n)), ← measureReal_def]
  change (q ^ n)⁻¹ * μ.real (sourceLocalBall K P n \ sourceLocalBall K P (n - 1)) =
    c * (1 - q⁻¹)
  rw [measureReal_sdiff hsub (sourceLocalBall_isOpen K P (n - 1)).measurableSet
    (sourceLocalBall_isCompact K P n).measure_ne_top,
    sourceLocalBall_volume_scaling K P μ n, sourceLocalBall_volume_scaling K P μ (n - 1),
    zpow_sub₀ hq.ne', zpow_one, div_eq_mul_inv]
  change (q ^ n)⁻¹ * (q ^ n * c - q ^ n * q⁻¹ * c) = c * (1 - q⁻¹)
  rw [show q ^ n * c - q ^ n * q⁻¹ * c = q ^ n * (c * (1 - q⁻¹)) by ring,
    inv_mul_cancel_left₀ (zpow_ne_zero _ hq.ne')]

theorem sourceLocalMulBall_iUnion (n : ℤ) :
    sourceLocalMulBall K P n = ⋃ m : ℕ, sourceLocalMulShell K P (n - (m : ℤ)) := by
  ext u
  rw [mem_iUnion]
  change sourceLocalValuation K P (u : k) ≤ WithZero.exp n ↔ _
  have hv : sourceLocalValuation K P (u : k) ≠ 0 := (Valuation.ne_zero_iff _).mpr u.ne_zero
  simp only [← WithZero.log_le_iff_le_exp hv, sourceLocalMulShell_log_iff K P]
  constructor
  · intro h
    exact ⟨(n - WithZero.log (sourceLocalValuation K P (u : k))).toNat, by omega⟩
  · rintro ⟨m, hm⟩
    omega

theorem sourceLocalMulBall_shells_disjoint (n : ℤ) :
    Pairwise (Disjoint on fun m : ℕ => sourceLocalMulShell K P (n - (m : ℤ))) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro u hua hub
  have ha := (sourceLocalMulShell_log_iff K P _ u).mp hua
  have hb := (sourceLocalMulShell_log_iff K P _ u).mp hub
  exact hab (by omega)

end
end ArtinMatthews.SourcePhysical
