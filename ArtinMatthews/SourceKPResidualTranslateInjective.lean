module

public import ArtinMatthews.SourceKPAutomorphicSpectralContinuation
public import ArtinMatthews.SourceKPDefectHighMean
public import ArtinMatthews.SourceKPTranslateH1Gram
public import ArtinMatthews.SourceKPResidualHighMeanOrthogonal
public import ArtinMatthews.SourceKPTranslateGramSpectral
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

/-! A finite relation among actual translated residual vectors vanishes
once the adjoint traces have zero high unipotent mean. -/
namespace ArtinMatthews
open NumberField MeasureTheory HilbertResolvent
open scoped NumberField MatrixGroups AdeleRing InnerProductSpace BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (F : Finset (SourceKPFiniteAdeleProjective K hζ))
variable {ι : Type*} [Fintype ι]
variable (t : ι → SourceKPFiniteAdeleProjective K hζ)
variable (ht : ∀ i, sourceKPFiniteTranslateLevel K hζ F ≤ sourceKPFiniteLevelConjugate K hζ (t i))
variable (c : ι → ℂ)
local notation "V" => SourceKPCompactGenuineH1 K hζ
local notation "H" => SourceKPGenuineAutomorphicL2 K hζ
local notation "j" => sourceKPCompactGenuineH1Mass K hζ
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "μF" => sourceKPTranslateCompactHaar K hζ F
local notation "P[" i "]" => sourceKPTranslateGenuinePullbackL2 K hζ F (t i) (ht i)

def sourceKPResidualTranslateCombination {T : ℝ} (hT : 2 < T) : Lp ℂ 2 μF :=
  ∑ i, c i • P[i] (sourceKPAutomorphicExceptionalResidue K hζ (by linarith : 1 ≤ T))

def sourceKPResidualTranslateTestVector {T : ℝ} (hT : 2 < T) (i : ι) : V :=
  ∑ k, c k • sourceKPTranslateGenuineGramH1 K hζ F (t i) (ht i) (t k) (ht k)
    (sourceKPAutomorphicExceptionalFormResidue K hζ (by linarith : 1 ≤ T))

theorem sourceKPResidualTranslateTestVector_mass {T : ℝ} (hT : 2 < T) (i : ι) :
    j (sourceKPResidualTranslateTestVector K hζ F t ht c hT i) =
      (P[i]).adjoint (sourceKPResidualTranslateCombination K hζ F t ht c hT) := by
  simp only [sourceKPResidualTranslateTestVector,sourceKPResidualTranslateCombination,
    map_sum,map_smul,sourceKPTranslateGenuineGramH1_mass,
    sourceKPAutomorphicExceptionalFormResidue_mass,sourceKPTranslateGenuineGramL2,
    ContinuousLinearMap.comp_apply]

theorem sourceKPResidualTranslateTestVector_mem_null {T : ℝ} (hT : 2 < T) (i : ι) :
    sourceKPResidualTranslateTestVector K hζ F t ht c hT i ∈
      nullSpace ((j).adjoint.comp j) (exceptionalCenter (InfinitePlace.nrComplexPlaces K : ℝ)) := by
  let N := nullSpace ((j).adjoint.comp j) (exceptionalCenter (InfinitePlace.nrComplexPlaces K : ℝ))
  apply N.sum_mem
  intro k _
  apply N.smul_mem
  exact sourceKPTranslateGenuineGramH1_mem_nullSpace K hζ F (t i) (ht i) (t k) (ht k) _
    (sourceKPAutomorphicExceptionalFormResidue_mem_null K hζ (by linarith : 1 ≤ T))

theorem sourceKPResidualTranslateCombination_eq_zero_of_highMean_zero
    {T : ℝ} (hT : 2 < T)
    (hmean : ∀ i, ∀ᵐ x ∂(sourceKPHighRepresentativeHaar K hζ (T/2)).restrict
        (sourceKPCuspBandHighSection K hζ (T/2)),
      sourceKPCompactHighUnipotentMean K hζ (T/2)
        ((j (sourceKPResidualTranslateTestVector K hζ F t ht c hT i)).val : Y → ℂ) x = 0) :
    sourceKPResidualTranslateCombination K hζ F t ht c hT = 0 := by
  let w := sourceKPResidualTranslateCombination K hζ F t ht c hT
  let R := sourceKPAutomorphicExceptionalResidue K hζ (by linarith : 1 ≤ T)
  have hi (i : ι) : inner ℂ (P[i] R) w = 0 := by
    have ho := sourceKPExceptionalResidue_inner_eq_zero_of_highMean_zero K hζ hT
      (sourceKPResidualTranslateTestVector K hζ F t ht c hT i)
      (sourceKPResidualTranslateTestVector_mem_null K hζ F t ht c hT i) (hmean i)
    rw [sourceKPResidualTranslateTestVector_mass K hζ F t ht c hT i] at ho
    have hrev : inner ℂ R ((P[i]).adjoint w) = 0 :=
      (inner_eq_zero_symm (𝕜 := ℂ) (E := H) (x := (P[i]).adjoint w) (y := R)).mp ho
    rw [(P[i]).adjoint_inner_right R w] at hrev
    exact hrev
  apply (inner_self_eq_zero (𝕜 := ℂ) (x := w)).mp
  change inner ℂ (∑ i, c i • P[i] R) w = 0
  rw [sum_inner]
  apply Finset.sum_eq_zero
  intro i _
  rw [inner_smul_left,hi,mul_zero]

end
end ArtinMatthews
