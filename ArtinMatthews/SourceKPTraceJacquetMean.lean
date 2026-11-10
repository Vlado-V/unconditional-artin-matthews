module

public import ArtinMatthews.SourceKPTraceJacquetCharacter
public import ArtinMatthews.SourceAdelicTraceHaar
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The nonzero-frequency trace character has zero integral over the
actual additive fundamental domain, with the prescribed trace Haar
measure. Translation preserves the integral by rational periodicity. -/

namespace ArtinMatthews
open NumberField MeasureTheory
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField AdeleRing ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance sourceKPTraceJacquetMeanMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance sourceKPTraceJacquetMeanBorel : BorelSpace 𝔸[K] := ⟨rfl⟩

include hζ in
theorem sourceKPTraceJacquetCharacter_integrableOn (m : Kˣ) :
    IntegrableOn (sourceKPTraceJacquetCharacter K m) (sourceKPAdelicFundamentalDomain K)
      (sourceKPAdelicTraceProduct K) := by
  let D := sourceKPAdelicFundamentalDomain K
  let μ := sourceKPAdelicTraceProduct K
  have hD : μ D ≠ ∞ := by
    change sourceKPAdelicTraceProduct K (sourceKPAdelicFundamentalDomain K) ≠ _
    rw [sourceKPAdelicTraceProduct_fundamentalDomain_of_primitiveRoot K hζ]
    exact ENNReal.one_ne_top
  have h : IntegrableOn (fun _ : 𝔸[K] => (1 : ℂ)) D μ := integrableOn_const hD
  have hb := h.bdd_mul (sourceKPTraceJacquetCharacter_continuous K m).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => (sourceKPTraceJacquetCharacter_norm K m y).le)
  change Integrable (sourceKPTraceJacquetCharacter K m) (μ.restrict D)
  simpa only [mul_one] using hb

include hζ in
theorem sourceKPTraceJacquetCharacter_integral_zero (m : Kˣ) :
    (∫ y in sourceKPAdelicFundamentalDomain K, sourceKPTraceJacquetCharacter K m y
      ∂sourceKPAdelicTraceProduct K) = 0 := by
  let μ := sourceKPAdelicTraceProduct K
  let D := sourceKPAdelicFundamentalDomain K
  let c := sourceKPTraceJacquetCharacter K m
  letI : μ.IsAddHaarMeasure := by
    change (sourceKPAdelicTraceProduct K).IsAddHaarMeasure
    rw [sourceKPAdelicTraceProduct_eq_standard_of_primitiveRoot K hζ]
    infer_instance
  obtain ⟨a,ha⟩ := sourceKPTraceJacquetCharacter_nontrivial K m
  let e := Equiv.addLeft a
  have hm : MeasurePreserving e μ μ := measurePreserving_add_left μ a
  have hm' : MeasurePreserving e.symm μ μ := measurePreserving_add_left μ (-a)
  have hme : MeasurableEmbedding e := (MeasurableEquiv.addLeft a).measurableEmbedding
  have hD : IsAddFundamentalDomain (sourceKPAdelicRationals K) D μ :=
    sourceKPAdelicFundamentalDomain_isFundamental K μ
  have hDe : IsAddFundamentalDomain (sourceKPAdelicRationals K) (e '' D) μ := by
    apply hD.image_of_equiv e hm'.quasiMeasurePreserving (Equiv.refl _)
    intro q y
    change a+((q : 𝔸[K])+y) = (q : 𝔸[K])+(a+y)
    abel
  have hperiod (q : sourceKPAdelicRationals K) (y : 𝔸[K]) : c (q +ᵥ y) = c y := by
    obtain ⟨x,rfl⟩ := (sourceKPRationalAdeleEquiv K).surjective q
    change c (algebraMap K 𝔸[K] x+y) = c y
    rw [add_comm]
    exact sourceKPTraceJacquetCharacter_rational_add K m x y
  have hscale : (∫ y in D, c y ∂μ) = c a * ∫ y in D, c y ∂μ := by
    calc
      _ = ∫ y in e '' D, c y ∂μ := hD.setIntegral_eq hDe hperiod
      _ = ∫ y in D, c (e y) ∂μ := hm.setIntegral_image_emb hme c D
      _ = _ := by
        change (∫ y in D, sourceKPTraceJacquetCharacter K m (a+y) ∂μ) = _
        simp_rw [sourceKPTraceJacquetCharacter_add K m a]
        rw [integral_const_mul]
  have hz : (1-c a) * (∫ y in D, c y ∂μ) = 0 := by
    rw [sub_mul,one_mul]
    exact sub_eq_zero.mpr hscale
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr ha.symm)

end
end ArtinMatthews
