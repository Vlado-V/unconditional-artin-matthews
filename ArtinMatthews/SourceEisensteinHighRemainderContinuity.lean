module

public import ArtinMatthews.SourceEisensteinHighRemainder
public import ArtinMatthews.SourceKPAdelicSectionParameterContinuity
public import ArtinMatthews.SourceKPCompactEisensteinContinuity
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

/-! The actual Eisenstein nonconstant term is continuous on the high-cusp
quotient, and its extension by zero to the full framed quotient is measurable. -/
namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicCompactEisenstein_arch_continuous {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (qf : SourceKPFiniteAdeleProjective K hζ) :
    Continuous (fun a : PGL(2, InfiniteAdeleRing K) => sourceKPAdelicCompactEisenstein K hζ s (a,qf)) := by
  have hc := (sourceKPAutomorphicCompactEisenstein_continuous K hζ hs).comp
    ((sourceKPAutomorphicCompactMk_isOpenQuotientMap K hζ).continuous.comp
      (sourceKPArchComponentPoint_continuous K hζ (QuotientGroup.mk qf)))
  refine hc.congr fun a => ?_
  exact sourceKPAutomorphicCompactEisenstein_adelic K hζ s (a,qf)

theorem sourceKPAdelicNonconstantEisenstein_arch_continuous {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (qf : SourceKPFiniteAdeleProjective K hζ) :
    Continuous (fun a : PGL(2, InfiniteAdeleRing K) => sourceKPAdelicNonconstantEisenstein K hζ s (a,qf)) := by
  have hs₀ : 0 < s.re := by
    push_cast at hs
    have hn : 0 ≤ (Module.finrank ℚ K : ℝ) := Nat.cast_nonneg _
    linarith
  exact (sourceKPAdelicCompactEisenstein_arch_continuous K hζ hs qf).sub
    ((sourceKPAdelicCompactScalar_arch_continuous K hζ s qf).add
      (sourceKPAdelicTraceIntertwiner_arch_continuous K hζ hs₀ qf))

theorem sourceKPFiniteLevelNonconstantEisenstein_continuous {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1) :
    Continuous (sourceKPFiniteLevelNonconstantEisenstein K hζ s) :=
  sourceKPFiniteLevelDescend_continuous K hζ _ _
    (sourceKPAdelicNonconstantEisenstein_arch_continuous K hζ hs)

theorem sourceKPHighCuspNonconstantEisenstein_continuous {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (T : ℝ) (hT : 1 < T) : Continuous (sourceKPHighCuspNonconstantEisenstein K hζ s T hT) :=
  (((sourceKPFiniteLevelNonconstantEisenstein_continuous K hζ hs).comp
    continuous_subtype_val).quotient_lift _).comp
      (sourceKPHighCuspHomeomorph K hζ T hT).symm.continuous

local notation "X" => SourceKPAutomorphicLevel K hζ
local instance sourceHighRemainderMeasurable : MeasurableSpace X := borel X
local instance sourceHighRemainderBorel : BorelSpace X := ⟨rfl⟩

def sourceKPHighRemainderExtension (s : ℂ) (T : ℝ) (hT : 1 < T) : X → ℂ :=
  Function.extend Subtype.val (sourceKPHighCuspNonconstantEisenstein K hζ s T hT) (fun _ => 0)

theorem sourceKPHighRemainderExtension_apply (s : ℂ) (T : ℝ) (hT : 1 < T)
    (x : SourceKPHighCuspAutomorphic K hζ T) :
    sourceKPHighRemainderExtension K hζ s T hT x.val =
      sourceKPHighCuspNonconstantEisenstein K hζ s T hT x :=
  Subtype.val_injective.extend_apply _ _ x

theorem sourceKPHighRemainderExtension_zero (s : ℂ) (T : ℝ) (hT : 1 < T)
    (x : X) (hx : sourceKPAutomorphicOrbitHeight K hζ x ≤ T) :
    sourceKPHighRemainderExtension K hζ s T hT x = 0 := by
  apply Function.extend_apply'
  rintro ⟨a,rfl⟩
  exact (not_lt_of_ge hx) a.property

theorem sourceKPHighRemainderExtension_measurable {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (T : ℝ) (hT : 1 < T) : Measurable (sourceKPHighRemainderExtension K hζ s T hT) :=
  (MeasurableEmbedding.subtype_coe (sourceKPHighCuspAutomorphic_isOpen K hζ T).measurableSet).measurable_extend
    (sourceKPHighCuspNonconstantEisenstein_continuous K hζ hs T hT).measurable measurable_const

end
end ArtinMatthews
