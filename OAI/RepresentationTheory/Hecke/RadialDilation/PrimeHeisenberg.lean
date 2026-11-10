module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic
public import OAI.RepresentationTheory.Hecke.RadialDilation.PrimeChart
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import OAI.RepresentationTheory.Hecke.RadialDilation.PrimePairing


set_option backward.privateInPublic true
@[expose] public section

/-! # Prime Heisenberg -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.PrimeHeisenberg.Realization

noncomputable section

/-! The full finite Heisenberg action separates into a local action and an away action. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable (q : ℕ) [Fact q.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

def awayHeisenbergFunction (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (p s : PrimeChart.Realization.FullPrimeAwayPosition q (ι := ι))
    (f : PrimeChart.Realization.FullPrimeAwayPosition q (ι := ι) → ℂ) (y : PrimeChart.Realization.FullPrimeAwayPosition q (ι := ι)) : ℂ :=
  D.finiteCharacter (p.val ⬝ᵥ (y.val - (1 / 2 : ℚ) • s.val)) * f (y - s)

theorem fullPrime_heisenberg_function (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (p s x : ι → Theta.PoissonAutomorphyNormalizationData.AQf) (f : (ι → ℚ_[q]) → ℂ) (h : PrimeChart.Realization.FullPrimeAwayPosition q (ι := ι) → ℂ) :
    Theta.PoissonAutomorphyNormalizationData.heisenberg D.finiteCharacter p s
      (fun z => f (PrimeChart.Realization.fullPrimeProjection q z) * h (PrimeChart.Realization.fullPrimeAway q z)) x =
      Theta.PoissonAutomorphyNormalizationData.heisenberg (FiniteSchur.Realization.finiteLocalCharacter q D) (PrimeChart.Realization.fullPrimeProjection q p) (PrimeChart.Realization.fullPrimeProjection q s)
        f (PrimeChart.Realization.fullPrimeProjection q x) *
      awayHeisenbergFunction q D (PrimeChart.Realization.fullPrimeAway q p) (PrimeChart.Realization.fullPrimeAway q s) h (PrimeChart.Realization.fullPrimeAway q x) := by
  have hrat (u t : ι → Theta.PoissonAutomorphyNormalizationData.AQf) :
      (fun i => u i - algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * t i) = u - (1 / 2 : ℚ) • t := by
    funext i
    rw [Algebra.smul_def]
    rfl
  have hlocal (u t : ι → ℚ_[q]) :
      (fun i => u i - algebraMap ℚ ℚ_[q] (1 / 2) * t i) = u - (1 / 2 : ℚ) • t := by
    funext i
    rw [Algebra.smul_def]
    rfl
  unfold Theta.PoissonAutomorphyNormalizationData.heisenberg awayHeisenbergFunction
  change D.finiteCharacter (p ⬝ᵥ (fun i => x i - algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * s i)) *
    (f (PrimeChart.Realization.fullPrimeProjection q (x - s)) * h (PrimeChart.Realization.fullPrimeAway q (x - s))) =
    (FiniteSchur.Realization.finiteLocalCharacter q D (PrimeChart.Realization.fullPrimeProjection q p ⬝ᵥ
      (fun i => PrimeChart.Realization.fullPrimeProjection q x i - algebraMap ℚ ℚ_[q] (1 / 2) * PrimeChart.Realization.fullPrimeProjection q s i)) *
      f (PrimeChart.Realization.fullPrimeProjection q x - PrimeChart.Realization.fullPrimeProjection q s)) *
    (D.finiteCharacter ((PrimeChart.Realization.fullPrimeAway q p).val ⬝ᵥ
      ((PrimeChart.Realization.fullPrimeAway q x).val - (1 / 2 : ℚ) • (PrimeChart.Realization.fullPrimeAway q s).val)) *
      h (PrimeChart.Realization.fullPrimeAway q x - PrimeChart.Realization.fullPrimeAway q s))
  rw [hrat, hlocal, PrimePairing.Realization.fullPrime_midpoint_pairing q, D.finiteCharacter.map_add_eq_mul, map_sub, map_sub]
  change (FiniteSchur.Realization.finiteLocalCharacter q D _ * D.finiteCharacter _) * (_ * _) = _
  ring

theorem padic_heisenberg_coordinate_convention (n : ℕ) (ψ : AddChar ℚ_[q] ℂ)
    (p s : Fin n → ℚ_[q]) (f : (Fin n → ℚ_[q]) → ℂ) :
    Theta.PoissonAutomorphyNormalizationData.heisenberg ψ p s f = Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (Sum.elim s p) f := by
  funext x
  unfold Theta.PoissonAutomorphyNormalizationData.heisenberg Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  simp only [Sum.elim_inr, Sum.elim_inl, map_div₀, map_one, map_ofNat]
  ring

end

end OAI.RepresentationTheory.Hecke.RadialDilation.PrimeHeisenberg.Realization
