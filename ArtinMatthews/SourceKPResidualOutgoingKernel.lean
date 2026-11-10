module

public import ArtinMatthews.SourceKPResidualTraceCombination
public import ArtinMatthews.SourceKPResidualOutgoingRelation
public import ArtinMatthews.SourceKPCuspResidualFourierValue
public import ArtinMatthews.SourceKPResidualTranslateInjective
public import ArtinMatthews.SourceKPCuspResidualFourierRelation
public import ArtinMatthews.SourceKPResidualTranslateKernel
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

/-! Relations among actual exceptional outgoing sections descend to
the genuine residual Hilbert translates, and hence to their Fourier
coefficients at every finite fibre. -/
namespace ArtinMatthews
open NumberField MeasureTheory StandardAdelic SourcePhysical
open scoped NumberField MatrixGroups AdeleRing Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "μA" => sourceKPArchHaar K hζ
local notation "μD" => Measure.restrict (sourceKPAdelicTraceProduct K) (sourceKPAdelicFundamentalDomain K)
local instance sourceResidualOutgoingAdelicMeasurable : MeasurableSpace 𝔸[K] := borel _

variable {I : Type} [Fintype I]

theorem sourceKPResidualTraceOrbit_outgoing_combination_ae
    (t : I → Gf) (c : I → ℂ) (hrel : SourceKPResidualOutgoingRelation K hζ t c)
    (qf : Gf) {T : ℝ} (hT : 1 ≤ T) :
    SourceKPResidualTraceCombinationAEZero K hζ hT (fun i => qf*t i) c :=
  sourceKPResidualTraceCombinationAEZero_of_scattering K hζ hT (fun i => qf*t i) c
    (fun i => sourceKPAdelicOutgoingScatteringWindow K hζ (qf*t i))
    (fun i => sourceKPAdelicOutgoingScatteringWindow_matches K hζ (qf*t i))
    (sourceKPResidualOutgoingRelation_scattering_zero K hζ t c hrel qf)

theorem sourceKPResidualTranslateCombination_eq_zero_of_outgoing_relation
    (t : I → Gf) (c : I → ℂ) (hrel : SourceKPResidualOutgoingRelation K hζ t c)
    (F : Finset Gf)
    (ht : ∀ i, sourceKPFiniteTranslateLevel K hζ F ≤ sourceKPFiniteLevelConjugate K hζ (t i))
    {T : ℝ} (hT : 2 < T) :
    sourceKPResidualTranslateCombination K hζ F t ht c hT = 0 := by
  have h (qf : Gf) := sourceKPResidualTraceOrbit_outgoing_combination_ae K hζ t c hrel qf
    (one_le_two.trans hT.le)
  simp only [SourceKPResidualTraceCombinationAEZero,sourceKPResidualTraceCombination] at h
  exact sourceKPResidualTranslateCombination_eq_zero_of_archMean_zero K hζ F t ht c hT h

theorem sourceKPCuspResidualFourierValue_sum_eq_zero_of_outgoing_relation
    (t : I → Gf) (c : I → ℂ) (hrel : SourceKPResidualOutgoingRelation K hζ t c)
    {T : ℝ} (hT : 2 < T) (m : Kˣ) (qf : Gf) :
    (∑ i : I, c i * sourceKPCuspResidualFourierValue K hζ m (one_le_two.trans hT.le) (qf*t i)) = 0 := by
  classical
  let F := Finset.univ.image t
  have ht (i : I) : sourceKPFiniteTranslateLevel K hζ F ≤ sourceKPFiniteLevelConjugate K hζ (t i) :=
    sourceKPFiniteTranslateLevel_le_conjugate K hζ F (Finset.mem_image_of_mem t (Finset.mem_univ i))
  exact sourceKPCuspResidualFourierValue_sum_eq_zero_of_translateCombination K hζ F t ht c hT
    (sourceKPResidualTranslateCombination_eq_zero_of_outgoing_relation K hζ t c hrel F ht hT) m qf

end
end ArtinMatthews
