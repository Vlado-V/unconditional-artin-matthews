module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Hecke.RadialDilation.PrimeChart
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart


set_option backward.privateInPublic true
@[expose] public section

/-! # Prime Pairing -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.PrimePairing.Realization

noncomputable section

/-! Orthogonal splitting of the complete finite-adelic Heisenberg pairing at one prime. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable (q : ℕ) [Fact q.Prime] {ι : Type*} [Fintype ι]

theorem fullPrime_pairing_local (p : ι → ℚ_[q]) (x : ι → Theta.PoissonAutomorphyNormalizationData.AQf) :
    PrimeChart.Realization.fullPrimeInclusion q p ⬝ᵥ x = FiniteSchur.Realization.finitePadicInclusion q (p ⬝ᵥ PrimeChart.Realization.fullPrimeProjection q x) := by
  change (∑ i, FiniteSchur.Realization.finitePadicInclusion q (p i) * x i) =
    FiniteSchur.Realization.finitePadicInclusion q (∑ i, p i * FiniteSchur.Realization.finitePadicProjection q (x i))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact FiniteBlockChart.Realization.finitePadicInclusion_mul q (p i) (x i)

theorem fullPrime_pairing_away (p : ι → ℚ_[q]) (y : PrimeChart.Realization.FullPrimeAwayPosition q (ι := ι)) :
    PrimeChart.Realization.fullPrimeInclusion q p ⬝ᵥ y.val = 0 := by
  rw [fullPrime_pairing_local, show PrimeChart.Realization.fullPrimeProjection q y.val = 0 from y.property]
  simp

theorem fullPrime_pairing_split (p x : ι → Theta.PoissonAutomorphyNormalizationData.AQf) :
    p ⬝ᵥ x = FiniteSchur.Realization.finitePadicInclusion q (PrimeChart.Realization.fullPrimeProjection q p ⬝ᵥ PrimeChart.Realization.fullPrimeProjection q x) +
      (PrimeChart.Realization.fullPrimeAway q p).val ⬝ᵥ (PrimeChart.Realization.fullPrimeAway q x).val := by
  have hc : (PrimeChart.Realization.fullPrimeAway q p).val ⬝ᵥ PrimeChart.Realization.fullPrimeInclusion q (PrimeChart.Realization.fullPrimeProjection q x) = 0 := by
    rw [dotProduct_comm]
    exact fullPrime_pairing_away q _ _
  calc
    p ⬝ᵥ x =
        (PrimeChart.Realization.fullPrimeInclusion q (PrimeChart.Realization.fullPrimeProjection q p) + (PrimeChart.Realization.fullPrimeAway q p).val) ⬝ᵥ
          (PrimeChart.Realization.fullPrimeInclusion q (PrimeChart.Realization.fullPrimeProjection q x) + (PrimeChart.Realization.fullPrimeAway q x).val) := by
      rw [PrimeChart.Realization.fullPrime_decomposition, PrimeChart.Realization.fullPrime_decomposition]
    _ = _ := by
      rw [add_dotProduct, dotProduct_add, dotProduct_add,
        fullPrime_pairing_away, fullPrime_pairing_local, PrimeChart.Realization.fullPrimeProjection_inclusion, hc]
      simp

theorem fullPrime_midpoint_pairing (p s x : ι → Theta.PoissonAutomorphyNormalizationData.AQf) :
    p ⬝ᵥ (x - (1 / 2 : ℚ) • s) =
      FiniteSchur.Realization.finitePadicInclusion q (PrimeChart.Realization.fullPrimeProjection q p ⬝ᵥ
        (PrimeChart.Realization.fullPrimeProjection q x - (1 / 2 : ℚ) • PrimeChart.Realization.fullPrimeProjection q s)) +
      (PrimeChart.Realization.fullPrimeAway q p).val ⬝ᵥ ((PrimeChart.Realization.fullPrimeAway q x).val - (1 / 2 : ℚ) • (PrimeChart.Realization.fullPrimeAway q s).val) := by
  rw [fullPrime_pairing_split q, map_sub, map_smul, map_sub, map_smul]
  rfl

end

end OAI.RepresentationTheory.Hecke.RadialDilation.PrimePairing.Realization
