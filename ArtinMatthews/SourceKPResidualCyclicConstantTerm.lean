module

public import ArtinMatthews.SourceKPAdeleLocalCover
public import ArtinMatthews.SourceKPAutomorphicSpectralFamily
public import ArtinMatthews.SourceKPLocalNegativeCyclicRelation
public import ArtinMatthews.SourceKPResidualArchMean
public import ArtinMatthews.SourceKPFiniteCyclicResidue
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

/-! Every genuine negative cyclic relation has zero constant term as an
actual combination of residual translates, on almost every arch frame. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical
open scoped NumberField AdeleRing MatrixGroups Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "G₀" => SourceFiniteKP2Projective K hζ P.val
local notation "μA" => sourceKPArchHaar K hζ
local notation "μD" => Measure.restrict (sourceKPAdelicTraceProduct K) (sourceKPAdelicFundamentalDomain K)
local notation "ι₀" => sourceKPAdelicLocalProjective K hζ P.val
local instance sourceResidualCyclicCTAdelicMeasurable : MeasurableSpace 𝔸[K] := borel _

theorem sourceKPResidualTraceOrbit_cyclic_combination_ae
    (hP : P.val ∉ traceBadPlaces K) (qf : Gf) {I : Type*} [Fintype I]
    (g : I → G₀) (c : I → ℂ) (hrel : SourceKPLocalNegativeCyclicRelation K hζ S₀ P g c)
    {T : ℝ} (hT : 1 ≤ T) :
    ∀ᵐ a ∂μA,
      Integrable (fun z : 𝔸[K] => ∑ i, c i * sourceKPCompactTraceOrbit K hζ
        (sourceKPAutomorphicExceptionalResidue K hζ hT).val a (qf*(ι₀ (g i)).2) z) μD ∧
      (∫ z, ∑ i, c i * sourceKPCompactTraceOrbit K hζ
        (sourceKPAutomorphicExceptionalResidue K hζ hT).val a (qf*(ι₀ (g i)).2) z ∂μD) = 0 := by
  obtain ⟨S,_,_,_,_,hmatch,hzero⟩ :=
    sourceKPFiniteFiberScatteringResidue_cyclic_relation_common_window K hζ S₀ P hP qf g c hrel
  let R := (sourceKPAutomorphicExceptionalResidue K hζ hT).val
  let q (i : I) := qf*(ι₀ (g i)).2
  let H := sourceKPCuspRepresentativeHeight K hζ
  let C (i : I) := sourceKPFiniteFiberScatteringResidue K hζ (q i) S
  have hi := ae_all_iff.mpr fun i : I => sourceKPResidualTraceOrbit_integrable_ae K hζ hT (q i)
  have hm := ae_all_iff.mpr fun i : I =>
    sourceKPResidualTraceMean_ae_eq_scattering K hζ hT (q i) S (hmatch i)
  filter_upwards [hi,hm] with a ha hma
  let V (i : I) := sourceKPCompactTraceOrbit K hζ R a (q i)
  let H₀ : ℂ := (sourceKPCuspArchHeight K (H a) ^ (1/3:ℝ) : ℝ)
  have hV (i : I) : Integrable (fun z => c i * V i z) μD := (ha i).const_mul _
  have hC (i : I) : (∫ z, V i z ∂μD) = C i * H₀ := hma i
  refine ⟨integrable_finsetSum _ (fun i _ => hV i), ?_⟩
  change (∫ z, ∑ i, c i * V i z ∂μD) = 0
  rw [integral_finsetSum _ (fun i _ => hV i)]
  simp_rw [integral_const_mul, hC, ← mul_assoc]
  rw [← Finset.sum_mul]
  change (∑ i, c i * sourceKPFiniteFiberScatteringResidue K hζ (q i) S)*H₀ = 0
  rw [hzero, zero_mul]

end
end ArtinMatthews
