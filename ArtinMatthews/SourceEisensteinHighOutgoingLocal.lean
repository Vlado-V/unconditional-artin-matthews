module

public import ArtinMatthews.SourceEisensteinHighOutgoing
public import ArtinMatthews.SourceKPArchHaar
public import ArtinMatthews.SourceKPAutomorphicMeasure
public import ArtinMatthews.SourceEisensteinHighOutgoingBound
public import ArtinMatthews.SourceKPArithmeticDiscreteness
public import ArtinMatthews.SourceKPAutomorphicHeightCompact
public import ArtinMatthews.SourceKPAutomorphicMeasureRegularity
public import ArtinMatthews.SourceKPHighCuspMeasure
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

/-! The genuine high-cusp outgoing function, extended by zero, is measurable
and locally square-integrable on every literal bounded height shell. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Topology MeasureTheory Set
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "X" => SourceKPAutomorphicLevel K hζ
local instance sourceHighOutgoingLocalMeasurable : MeasurableSpace X := borel X
local instance sourceHighOutgoingLocalBorel : BorelSpace X := ⟨rfl⟩
local notation "μ" => sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ)

def sourceKPHighOutgoingExtension (s : ℂ) (T : ℝ) (hT : 1 < T) : X → ℂ :=
  Function.extend Subtype.val (sourceKPHighCuspOutgoingEisenstein K hζ s T hT) (fun _ => 0)

theorem sourceKPHighOutgoingExtension_apply (s : ℂ) (T : ℝ) (hT : 1 < T)
    (x : SourceKPHighCuspAutomorphic K hζ T) :
    sourceKPHighOutgoingExtension K hζ s T hT x.val =
      sourceKPHighCuspOutgoingEisenstein K hζ s T hT x :=
  Subtype.val_injective.extend_apply _ _ x

theorem sourceKPHighOutgoingExtension_zero (s : ℂ) (T : ℝ) (hT : 1 < T)
    (x : X) (hx : sourceKPAutomorphicOrbitHeight K hζ x ≤ T) :
    sourceKPHighOutgoingExtension K hζ s T hT x = 0 := by
  apply Function.extend_apply'
  rintro ⟨a,rfl⟩
  exact (not_lt_of_ge hx) a.property

theorem sourceKPHighOutgoingExtension_measurable {s : ℂ} (hs : 0 < s.re)
    (T : ℝ) (hT : 1 < T) : Measurable (sourceKPHighOutgoingExtension K hζ s T hT) :=
  (MeasurableEmbedding.subtype_coe (sourceKPHighCuspAutomorphic_isOpen K hζ T).measurableSet).measurable_extend
    (sourceKPHighCuspOutgoingEisenstein_continuous K hζ hs T hT).measurable measurable_const

theorem sourceKPHighOutgoingExtension_shell_memLp {s : ℂ} (hs : 0 < s.re)
    (T U : ℝ) (hT : 1 < T) :
    MemLp (sourceKPHighOutgoingExtension K hζ s T hT) 2
      ((μ).restrict {x | T < sourceKPAutomorphicOrbitHeight K hζ x ∧
        sourceKPAutomorphicOrbitHeight K hζ x ≤ U}) := by
  let S : Set X := {x | T < sourceKPAutomorphicOrbitHeight K hζ x ∧
    sourceKPAutomorphicOrbitHeight K hζ x ≤ U}
  have hS : MeasurableSet S :=
    (sourceKPHighCuspAutomorphic_isOpen K hζ T).measurableSet.inter
      (sourceKPAutomorphicOrbitHeight_sublevel_closed K hζ U).measurableSet
  have hfinite : μ S < ∞ := lt_of_le_of_lt (measure_mono fun _ hx => hx.2)
    (sourceKPAutomorphicOrbitHeight_sublevel_isCompact K hζ U).measure_lt_top
  letI : IsFiniteMeasure ((μ).restrict S) := ⟨by simpa only [Measure.restrict_apply_univ] using hfinite⟩
  obtain ⟨C,_hC,hbound⟩ := sourceKPHighCuspOutgoingEisenstein_band_bound K hζ hs T U hT
  apply MemLp.of_bound (sourceKPHighOutgoingExtension_measurable K hζ hs T hT).aestronglyMeasurable.restrict C
  filter_upwards [ae_restrict_mem hS] with x hx
  have he := sourceKPHighOutgoingExtension_apply K hζ s T hT ⟨x,hx.1⟩
  change sourceKPHighOutgoingExtension K hζ s T hT x = _ at he
  rw [he]
  exact hbound ⟨x,hx.1⟩ hx.2

end
end ArtinMatthews
