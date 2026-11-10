module

public import ArtinMatthews.SpectralMixedPacketTerms
public import ArtinMatthews.SpectralBareSpectrumLimit
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Finite linear combination of the actual native source pairings,
with the positive-frequency measure and every residual coefficient retained. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups BigOperators
namespace ArtinMatthews

def gamma0MixedPacketSpectralSide {ι : Type*} (N : ℕ) [NeZero N]
    (h : SpectralEnergyTest) (b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (v : Finset ι) (α : ι → ℂ) (m : ι → ℤ) (hm : ∀ j, m j ≠ 0) : ℂ :=
  (∑' i, gamma0MixedPacketCuspidalTerm N h b Y hY n hn v α m hm i) +
    ((∫ t, gamma0MixedPacketContinuousIntegrand N h b Y hY n hn v α m hm t
      ∂gamma0EisensteinSpectralMeasure) +
      ∑ l ∈ gamma0ResidualEnergyWindow N, ∑ j,
        gamma0MixedPacketResidualTerm N h b n hn v α m hm l j)

theorem gamma0MixedPacketSpectralSide_eq_sum {ι : Type*} (N : ℕ) [NeZero N]
    (h : SpectralEnergyTest) (b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (v : Finset ι) (α : ι → ℂ) (m : ι → ℤ) (hm : ∀ j, m j ≠ 0)
    (hS : ∀ j ∈ v, Summable (gamma0BareCuspidalTerm N h b 1 Y hY n (m j) hn (hm j)))
    (hI : ∀ j ∈ v, IntegrableOn (gamma0BareContinuousRhoIntegrand N h b 1 Y hY n (m j) hn (hm j))
      (Ioi (0 : ℝ))) :
    Summable (gamma0MixedPacketCuspidalTerm N h b Y hY n hn v α m hm) ∧
      Integrable (gamma0MixedPacketContinuousIntegrand N h b Y hY n hn v α m hm)
        gamma0EisensteinSpectralMeasure ∧
      gamma0MixedPacketSpectralSide N h b Y hY n hn v α m hm =
        ∑ j ∈ v, α j*gamma0BareSourceSpectralSide N h b 1 Y hY n (m j) hn (hm j) := by
  let F (j : ι) := gamma0BareCuspidalTerm N h b 1 Y hY n (m j) hn (hm j)
  let G (j : ι) := gamma0BareContinuousRhoIntegrand N h b 1 Y hY n (m j) hn (hm j)
  let C := gamma0MixedPacketCuspidalTerm N h b Y hY n hn v α m hm
  let I := gamma0MixedPacketContinuousIntegrand N h b Y hY n hn v α m hm
  let E (j : ι) := gamma0BareResidualRhoTerm N h b 1 n (m j) hn (hm j)
  let μ := gamma0EisensteinSpectralMeasure
  have hF (j : ι) (hj : j ∈ v) : Summable (fun i => α j*F j i) := (hS j hj).mul_left _
  have hG (j : ι) (hj : j ∈ v) : IntegrableOn (fun t => α j*G j t) (Ioi (0 : ℝ)) :=
    (hI j hj).const_mul _
  have hC : C = fun i => ∑ j ∈ v, α j*F j i :=
    funext (gamma0MixedPacketCuspidalTerm_eq_sum N h b Y hY n hn v α m hm)
  have hπ : ((2*Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hIeq : I = fun t => ((2*Real.pi : ℝ) : ℂ)*(∑ j ∈ v, α j*G j t) := by
    funext t
    have he := gamma0MixedPacketContinuousIntegrand_eq_sum N h b Y hY n hn v α m hm t
    exact ((div_eq_iff hπ).mp he).trans (mul_comm _ _)
  have hIG : IntegrableOn (fun t => ∑ j ∈ v, α j*G j t) (Ioi (0 : ℝ)) :=
    integrable_finsetSum v hG
  refine ⟨?_, ?_,?_⟩
  · change Summable C
    rw [hC]
    exact summable_sum hF
  · change Integrable I μ
    rw [hIeq]
    exact ((hIG.const_mul ((2*Real.pi : ℝ) : ℂ)).smul_measure ENNReal.ofReal_ne_top)
  have hT : (∑' i, C i) = ∑ j ∈ v, α j*(∑' i, F j i) := by
    rw [hC,Summable.tsum_finsetSum hF]
    simp only [tsum_mul_left]
  have hInt : (∫ t, I t ∂μ) = ∑ j ∈ v, α j*(∫ t in Ioi (0 : ℝ), G j t) := by
    dsimp only [μ]
    rw [gamma0EisensteinSpectralMeasure,integral_smul_measure,ENNReal.toReal_ofReal (by positivity),
      hIeq,integral_const_mul,Complex.real_smul,Complex.ofReal_inv]
    rw [← mul_assoc,inv_mul_cancel₀ hπ,one_mul,integral_finsetSum v hG]
    simp only [integral_const_mul]
  have hR :
      (∑ l ∈ gamma0ResidualEnergyWindow N, ∑ k,
        gamma0MixedPacketResidualTerm N h b n hn v α m hm l k) =
      ∑ j ∈ v, α j*(∑ l ∈ gamma0ResidualEnergyWindow N, ∑ k, E j l k) := by
    simp_rw [gamma0MixedPacketResidualTerm_eq_sum,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
  change (∑' i, C i) + ((∫ t, I t ∂μ) +
      ∑ l ∈ gamma0ResidualEnergyWindow N, ∑ k, gamma0MixedPacketResidualTerm N h b n hn v α m hm l k) = _
  rw [hT,hInt,hR,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold gamma0BareSourceSpectralSide gamma0BareResidualRhoSum
  dsimp only [F,G,E]
  ring

end ArtinMatthews
