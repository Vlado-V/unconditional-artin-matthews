module

public import ArtinMatthews.SourceKPCuspResidualGeneralFourier
public import ArtinMatthews.SourceKPCuspPrincipalFrequency
public import ArtinMatthews.SourceKPCuspResidualPeriodIndependence
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

/-! The normalized compact residue test gives one canonical coefficient at
each finite argument and each nonzero rational frequency. -/
namespace ArtinMatthews

open NumberField Matrix MeasureTheory Module.Free SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing BigOperators NNReal ENNReal

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "E[" d ", " hd "]" => sourceKPCuspProductCoordinates K hζ d hd

private def residualFourierValueSpec (m : Kˣ) {T : ℝ} (hT : 1 ≤ T) (qf : Gf) (a : ℂ) : Prop :=
  ∀ (d : 𝓞 K) (hd : d ≠ 0) (c : ℝ≥0), 0 < c →
    (∀ t ∈ sourceKPCuspFiniteIdeal K d, ∃ k : sourceKPFiniteDeepMatrixGroup K,
      (1,qf)⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t) * (1,qf) =
        sourceKPFiniteDeepCoverLift K hζ k) →
    (∃ r : 𝓞 K, (m:K) * (d:K) = (r:K)) →
    Measure.map (E[d, hd]).symm (productVolume (InfinitePlace K)) =
      (c:ℝ≥0∞) • (volume : Measure (I → ℝ)).prod (sourceKPCuspProductHeightMeasure K) →
    a = sourceKPCuspResidualCoefficient K hζ d hd qf m c hT

private theorem exists_residualFourierValue (m : Kˣ) {T : ℝ} (hT : 1 ≤ T) (qf : Gf) :
    ∃ a : ℂ, residualFourierValueSpec K hζ m hT qf a := by
  obtain ⟨d,hd,hm,hp⟩ := sourceKPAdelicCuspFrequencyPeriod K hζ (m:K) (1,qf)
  obtain ⟨c,hc,hmap⟩ := sourceKPCuspProductCoordinates_map_productVolume K hζ d hd
  refine ⟨sourceKPCuspResidualCoefficient K hζ d hd qf m c hT, ?_⟩
  intro e he ce hce hpe hme hmape
  exact sourceKPCuspResidualCoefficient_period_independent K hζ d e hd he qf m
    hp hpe hm hme c ce hc hce hmap hmape hT

def sourceKPCuspResidualFourierValue (m : Kˣ) {T : ℝ} (hT : 1 ≤ T) (qf : Gf) : ℂ :=
  Classical.choose (exists_residualFourierValue K hζ m hT qf)

theorem sourceKPCuspResidualFourierValue_eq_coefficient
    (m : Kˣ) {T : ℝ} (hT : 1 ≤ T) (qf : Gf)
    (d : 𝓞 K) (hd : d ≠ 0) (c : ℝ≥0) (hc : 0 < c)
    (hp : ∀ t ∈ sourceKPCuspFiniteIdeal K d, ∃ k : sourceKPFiniteDeepMatrixGroup K,
      (1,qf)⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t) * (1,qf) =
        sourceKPFiniteDeepCoverLift K hζ k)
    (hm : ∃ r : 𝓞 K, (m:K) * (d:K) = (r:K))
    (hmap : Measure.map (E[d, hd]).symm (productVolume (InfinitePlace K)) =
      (c:ℝ≥0∞) • (volume : Measure (I → ℝ)).prod (sourceKPCuspProductHeightMeasure K)) :
    sourceKPCuspResidualFourierValue K hζ m hT qf =
      sourceKPCuspResidualCoefficient K hζ d hd qf m c hT :=
  Classical.choose_spec (exists_residualFourierValue K hζ m hT qf) d hd c hc hp hm hmap

theorem sourceKPAdelicCuspFrequencyPeriod_common
    {ι : Type*} [Fintype ι] (m : K) (g : ι → SourceKPAdelicProjective K hζ) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ (∃ r : 𝓞 K, m * (d:K) = (r:K)) ∧
      ∀ i, ∀ t ∈ sourceKPCuspFiniteIdeal K d, ∃ k : sourceKPFiniteDeepMatrixGroup K,
        (g i)⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t) * g i =
          sourceKPFiniteDeepCoverLift K hζ k := by
  classical
  choose a ha _ hpa using fun i => sourceKPAdelicCuspFrequencyPeriod K hζ m (g i)
  obtain ⟨e,he,⟨r,hr⟩,_⟩ := sourceKPAdelicCuspFrequencyPeriod K hζ m 1
  let b := ∏ i, a i
  refine ⟨e*b, mul_ne_zero he (Finset.prod_ne_zero_iff.mpr fun i _ => ha i),
    ⟨r*b,?_⟩, ?_⟩
  · change m * algebraMap (𝓞 K) K (e*b) = algebraMap (𝓞 K) K (r*b)
    rw [map_mul, map_mul, ← mul_assoc, hr]
  · intro i t ht
    have hdiv : a i ∣ e*b := dvd_mul_of_dvd_right
      (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) e
    obtain ⟨v,hv⟩ := hdiv
    have hmem : t ∈ sourceKPCuspFiniteIdeal K (a i*v) := hv ▸ ht
    exact hpa i t (sourceKPCuspFiniteIdeal_mul_subset K (a i) v hmem)

end
end ArtinMatthews
