module

public import ArtinMatthews.SourceFiniteFiberScattering
public import ArtinMatthews.SourceKPAutomorphicSpectralFamily
public import ArtinMatthews.SourceKPResidualArchMean
public import ArtinMatthews.SourceKPResidualArchConstantTerm
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

/-! The constant term of a finite combination at arbitrary finite fibres,
using the original normalized trace measure. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical
open scoped NumberField MatrixGroups AdeleRing Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "μA" => sourceKPArchHaar K hζ
local notation "μD" => Measure.restrict (sourceKPAdelicTraceProduct K) (sourceKPAdelicFundamentalDomain K)
local instance sourceResidualCombinationAdelicMeasurable : MeasurableSpace 𝔸[K] := borel _

variable {T : ℝ} (hT : 1 ≤ T)
variable {I : Type} [Fintype I]

def sourceKPResidualTraceCombination (q : I → Gf) (c : I → ℂ)
    (a : PGL(2, InfiniteAdeleRing K)) (z : 𝔸[K]) : ℂ :=
  ∑ i : I, c i * sourceKPCompactTraceOrbit K hζ
    (sourceKPAutomorphicExceptionalResidue K hζ hT).val a (q i) z

def SourceKPResidualTraceCombinationAEZero (q : I → Gf) (c : I → ℂ) : Prop :=
  ∀ᵐ a : PGL(2, InfiniteAdeleRing K) ∂μA, Integrable (sourceKPResidualTraceCombination K hζ hT q c a) μD ∧
    (∫ z : 𝔸[K], sourceKPResidualTraceCombination K hζ hT q c a z ∂μD) = 0

theorem sourceKPResidualTraceCombinationAEZero_of_scattering
    (q : I → Gf) (c : I → ℂ)
    (S : I → Finset (HeightOneSpectrum (𝓞 K)))
    (hM : ∀ (i : I) (s : ℂ), ((3*(Module.finrank ℚ K+1):ℕ):ℝ) ≤ 2*s.re+1 →
      sourceKPAdelicTraceIntertwiner K hζ s (1,q i) =
        sourceKPFiniteFiberScatteringContinuation K hζ (q i) (S i) s)
    (hzero : (∑ i : I, c i * sourceKPFiniteFiberScatteringResidue K hζ (q i) (S i)) = 0) :
    SourceKPResidualTraceCombinationAEZero K hζ hT q c := by
  let R := (sourceKPAutomorphicExceptionalResidue K hζ hT).val
  let C (i : I) := sourceKPFiniteFiberScatteringResidue K hζ (q i) (S i)
  have hi := ae_all_iff.mpr fun i : I => sourceKPResidualTraceOrbit_integrable_ae K hζ hT (q i)
  have hm := ae_all_iff.mpr fun i : I =>
    sourceKPResidualTraceMean_ae_eq_scattering K hζ hT (q i) (S i) (hM i)
  unfold SourceKPResidualTraceCombinationAEZero
  filter_upwards [hi,hm] with a ha hma
  let V (i : I) := sourceKPCompactTraceOrbit K hζ R a (q i)
  let H₀ : ℂ := (sourceKPCuspArchHeight K (sourceKPCuspRepresentativeHeight K hζ a) ^ (1/3:ℝ) : ℝ)
  have hV (i : I) : Integrable (fun z => c i * V i z) μD := (ha i).const_mul _
  have hC (i : I) : (∫ z, V i z ∂μD) = C i * H₀ := hma i
  refine ⟨integrable_finsetSum _ (fun i _ => hV i), ?_⟩
  change (∫ z, ∑ i, c i * V i z ∂μD) = 0
  rw [integral_finsetSum _ (fun i _ => hV i)]
  simp_rw [integral_const_mul, hC, ← mul_assoc]
  rw [← Finset.sum_mul]
  change (∑ i, c i * sourceKPFiniteFiberScatteringResidue K hζ (q i) (S i))*H₀ = 0
  rw [hzero,zero_mul]

end
end ArtinMatthews
