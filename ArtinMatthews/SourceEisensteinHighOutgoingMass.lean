module

public import ArtinMatthews.SourceEisensteinHighOutgoingLocal
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

/-! Exact outgoing squared-mass scaling under the genuine high-cusp measure. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Topology MeasureTheory Set
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "X" => SourceKPAutomorphicLevel K hζ
local instance sourceHighOutgoingMassMeasurable : MeasurableSpace X := borel X
local instance sourceHighOutgoingMassBorel : BorelSpace X := ⟨rfl⟩
local notation "μ" => sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ)

theorem sourceKPRadialHeightScale_one_le {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ sourceKPRadialHeightScale K t := by
  apply Real.one_le_exp_iff.mpr
  exact mul_nonneg (by positivity) ht

theorem sourceKPHighOutgoingExtension_norm_radial {s : ℂ} (hs : 0 < s.re)
    (t : ℝ) (ht : 0 ≤ t) (T : ℝ) (hT : 1 < T)
    (x : SourceKPHighCuspAutomorphic K hζ T) :
    ‖sourceKPHighOutgoingExtension K hζ s T hT (sourceKPHighCuspRadialValue K hζ t T hT x)‖ =
      sourceKPRadialHeightScale K t ^ (1 / 2 - s.re) *
        ‖sourceKPHighOutgoingExtension K hζ s T hT x.val‖ := by
  have hTU : T ≤ sourceKPRadialHeightScale K t*T := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (sourceKPRadialHeightScale_one_le K ht) (zero_lt_one.trans hT).le
  have htT : 1 < sourceKPRadialHeightScale K t*T := hT.trans_le hTU
  let y := sourceKPHighCuspRadialHomeomorph K hζ t T hT htT x
  have hy : T < sourceKPAutomorphicOrbitHeight K hζ y.val := hTU.trans_lt y.property
  rw [← sourceKPHighCuspRadialHomeomorph_value K hζ t T hT htT x]
  have he := sourceKPHighOutgoingExtension_apply K hζ s T hT ⟨y.val,hy⟩
  change sourceKPHighOutgoingExtension K hζ s T hT y.val = _ at he
  rw [he,sourceKPHighOutgoingExtension_apply]
  rw [sourceKPHighCuspOutgoingEisenstein_include K hζ s hT htT hTU y]
  exact sourceKPHighCuspOutgoingEisenstein_norm_radial K hζ hs t T hT htT x

theorem sourceKPHighOutgoingExtension_shell_mass_scale {s : ℂ} (hs : 0 < s.re)
    (t : ℝ) (ht : 0 ≤ t) (T U : ℝ) (hT : 1 < T) :
    (∫ x in {x | sourceKPRadialHeightScale K t*T < sourceKPAutomorphicOrbitHeight K hζ x ∧
      sourceKPAutomorphicOrbitHeight K hζ x ≤ sourceKPRadialHeightScale K t*U},
      ‖sourceKPHighOutgoingExtension K hζ s T hT x‖ ^ 2 ∂μ) =
    sourceKPRadialHeightScale K t ^ (-2*s.re) *
      (∫ x in {x | T < sourceKPAutomorphicOrbitHeight K hζ x ∧
        sourceKPAutomorphicOrbitHeight K hζ x ≤ U},
        ‖sourceKPHighOutgoingExtension K hζ s T hT x‖ ^ 2 ∂μ) := by
  let c := sourceKPRadialHeightScale K t
  have hc : 0 < c := sourceKPRadialHeightScale_pos K t
  have hTU : T ≤ c*T := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (sourceKPRadialHeightScale_one_le K ht) (zero_lt_one.trans hT).le
  have htT : 1 < c*T := hT.trans_le hTU
  let ν := (sourceKPHighCuspMeasure K hζ T).restrict
    {x | sourceKPAutomorphicOrbitHeight K hζ x.val ≤ U}
  let V := sourceKPHighCuspRadialValue K hζ t T hT
  let F : X → ℝ := fun x => ‖sourceKPHighOutgoingExtension K hζ s T hT x‖ ^ 2
  have hF : Measurable F := (sourceKPHighOutgoingExtension_measurable K hζ hs T hT).norm.pow_const 2
  have hV : Measurable V :=
    ((sourceKPHighCuspRadialValue_continuous K hζ T hT).comp
      (continuous_const.prodMk continuous_id)).measurable
  have hmap := sourceKPHighCuspRadialValue_shell_map K hζ t T U hT htT
  have hI : (∫ x, F x ∂Measure.map V ν) = ∫ q, F (V q) ∂ν :=
    integral_map hV.aemeasurable hF.aestronglyMeasurable
  change Measure.map V ν = ENNReal.ofReal c • (μ).restrict
    {x | c*T < sourceKPAutomorphicOrbitHeight K hζ x ∧
      sourceKPAutomorphicOrbitHeight K hζ x ≤ c*U} at hmap
  rw [hmap,integral_smul_measure,ENNReal.toReal_ofReal hc.le,smul_eq_mul] at hI
  have hbase : (∫ q, F q.val ∂ν) =
      ∫ x in {x | T < sourceKPAutomorphicOrbitHeight K hζ x ∧
        sourceKPAutomorphicOrbitHeight K hζ x ≤ U}, F x ∂μ := by
    calc
      _ = ∫ x, F x ∂Measure.map Subtype.val ν :=
        (integral_map measurable_subtype_coe.aemeasurable hF.aestronglyMeasurable).symm
      _ = _ := by rw [sourceKPHighCuspMeasure_map_val_restrict]
  have hright : (∫ q, F (V q) ∂ν) = (c ^ (1/2-s.re)) ^ 2 * ∫ q, F q.val ∂ν := by
    calc
      _ = ∫ q, (c ^ (1/2-s.re)) ^ 2 * F q.val ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun q => by
          dsimp only [F,V,c]
          rw [sourceKPHighOutgoingExtension_norm_radial K hζ hs t ht T hT q,mul_pow]
      _ = _ := integral_const_mul _ _
  rw [hright,hbase] at hI
  have hp : (c ^ (1/2-s.re)) ^ 2 = c * c ^ (-2*s.re) := by
    calc
      _ = c ^ ((1/2-s.re)*(2 : ℝ)) := (Real.rpow_mul_natCast hc.le _ 2).symm
      _ = c ^ (1+(-2*s.re)) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hc,Real.rpow_one]
  apply mul_left_cancel₀ hc.ne'
  rw [hI,hp]
  ring

end
end ArtinMatthews
