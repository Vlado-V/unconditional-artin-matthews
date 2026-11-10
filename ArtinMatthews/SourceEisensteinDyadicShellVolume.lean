module

public import ArtinMatthews.L2DyadicOpenShells
public import ArtinMatthews.SourceAdelicOrbitHeightTopology
public import ArtinMatthews.SourceKPArchHaar
public import ArtinMatthews.SourceKPAutomorphicMeasure
public import ArtinMatthews.SourceEisensteinHighOutgoingL2
public import ArtinMatthews.SourceKPArithmeticDiscreteness
public import ArtinMatthews.SourceKPAutomorphicHeightCompact
public import ArtinMatthews.SourceKPAutomorphicMeasureRegularity
public import ArtinMatthews.SourceKPHighCuspRadialShellMeasure
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

/-! Exact dyadic volume transport on the actual automorphic high cusp. -/
namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory Set
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "X" => SourceKPAutomorphicLevel K hζ
local instance sourceEisensteinShellVolumeMeasurable : MeasurableSpace X := borel X
local instance sourceEisensteinShellVolumeBorel : BorelSpace X := ⟨rfl⟩
local notation "μ" => sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ)
local notation "H" => sourceKPAutomorphicOrbitHeight K hζ

theorem sourceKPDyadicOpenShell_measurable (T : ℝ) (n : ℕ) :
    MeasurableSet (dyadicL2OpenShell H T n) :=
  (sourceKPHighCuspAutomorphic_isOpen K hζ (T*2^n)).measurableSet.inter
    (sourceKPAutomorphicOrbitHeight_sublevel_closed K hζ (T*2^(n+1))).measurableSet

theorem sourceKPDyadicOpenShell_measure_lt_top (T : ℝ) (n : ℕ) :
    μ (dyadicL2OpenShell H T n) < ∞ :=
  lt_of_le_of_lt (measure_mono fun _ hx => hx.2)
    (sourceKPAutomorphicOrbitHeight_sublevel_isCompact K hζ (T*2^(n+1))).measure_lt_top

theorem sourceKPDyadicOpenShell_real_volume (T : ℝ) (hT : 1 < T) (n : ℕ) :
    (2 : ℝ)^n * (μ).real (dyadicL2OpenShell H T n) = (μ).real (dyadicL2OpenShell H T 0) := by
  let t := sourceKPDyadicRadialTime K n
  let c := sourceKPRadialHeightScale K t
  have hc : 0 < c := sourceKPRadialHeightScale_pos K t
  have hcs : c = (2 : ℝ)^n := sourceKPDyadicRadialTime_scale K n
  have hc₁ : 1 ≤ c := by
    rw [hcs]
    exact one_le_pow₀ (by norm_num)
  have hT₀ : 0 < T := zero_lt_one.trans hT
  have hTc : T ≤ c*T := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc₁ hT₀.le
  let ν := (sourceKPHighCuspMeasure K hζ T).restrict {x | H x.val ≤ T*2}
  let V := sourceKPHighCuspRadialValue K hζ t T hT
  have hV : Measurable V :=
    ((sourceKPHighCuspRadialValue_continuous K hζ T hT).comp
      (continuous_const.prodMk continuous_id)).measurable
  have hm := sourceKPHighCuspRadialValue_shell_map K hζ t T (T*2) hT (hT.trans_le hTc)
  have hlo : c*T = T*2^n := hcs ▸ mul_comm _ _
  have hhi : c*(T*2) = T*2^(n+1) := by rw [hcs,pow_succ]; ring
  change Measure.map V ν = ENNReal.ofReal c •
    (μ).restrict {x | c*T < H x ∧ H x ≤ c*(T*2)} at hm
  rw [hlo,hhi] at hm
  change Measure.map V ν = ENNReal.ofReal c • (μ).restrict (dyadicL2OpenShell H T n) at hm
  have hb := sourceKPHighCuspMeasure_map_val_restrict K hζ T (T*2)
  have hz : dyadicL2OpenShell H T 0 = {x | T < H x ∧ H x ≤ T*2} := by
    simp only [dyadicL2OpenShell,pow_zero,mul_one,Nat.zero_add,pow_one]
  change Measure.map Subtype.val ν = (μ).restrict {x | T < H x ∧ H x ≤ T*2} at hb
  rw [← hz] at hb
  have hv := congrArg (fun m : Measure X => m.real Set.univ) hm
  have hb' := congrArg (fun m : Measure X => m.real Set.univ) hb
  change (Measure.map V ν).real Set.univ = _ at hv
  change (Measure.map Subtype.val ν).real Set.univ = _ at hb'
  rw [map_measureReal_apply hV MeasurableSet.univ,preimage_univ,
    measureReal_ennreal_smul_apply,ENNReal.toReal_ofReal hc.le] at hv
  rw [map_measureReal_apply measurable_subtype_coe MeasurableSet.univ,preimage_univ] at hb'
  have he : c * (μ).real (dyadicL2OpenShell H T n) = (μ).real (dyadicL2OpenShell H T 0) := by
    simpa only [measureReal_restrict_apply_univ] using hv.symm.trans hb'
  exact hcs ▸ he

theorem sourceKPDyadicOpenShell_real_volume_le (T : ℝ) (hT : 1 < T) (n : ℕ) :
    (μ).real (dyadicL2OpenShell H T n) ≤ (μ).real (dyadicL2OpenShell H T 0) := by
  rw [← sourceKPDyadicOpenShell_real_volume K hζ T hT n]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := n))
    (measureReal_nonneg : 0 ≤ (μ).real (dyadicL2OpenShell H T n))

end
end ArtinMatthews
