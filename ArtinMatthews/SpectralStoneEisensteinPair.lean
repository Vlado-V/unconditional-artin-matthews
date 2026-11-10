module

public import ArtinMatthews.SpectralStoneFrequency
public import ArtinMatthews.SpectralEisensteinWeakForcing
public import ArtinMatthews.SpectralStoneCompactPlancherel
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
public import Mathlib.RingTheory.PiTensorProduct
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

/-! Actual native compact Eisenstein amplitudes and absolutely integrable
off-diagonal products with the positive critical measure. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

theorem gamma0EisensteinCutoffCompactTest_add_seed (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (ψ ξ : h2SmoothCompactSeeds) (s : ℂ) :
    gamma0EisensteinCutoffCompactTest N a (ψ+ξ) s=
      gamma0EisensteinCutoffCompactTest N a ψ s+gamma0EisensteinCutoffCompactTest N a ξ s := by
  let f := gamma0CuspEisensteinCutoff N a s
  have hf := gamma0CuspOutgoingCutoff_continuous N a s
  have h (z : UpperHalfPlane) : inner ℂ ((ψ+ξ).val z) (f z)=
      inner ℂ (ψ.val z) (f z)+inner ℂ (ξ.val z) (f z) :=
    inner_add_left (𝕜:=ℂ) (ψ.val z) (ξ.val z) (f z)
  simp only [gamma0EisensteinCutoffCompactTest,← show f=gamma0CuspEisensteinCutoff N a s from rfl]
  simp_rw [h]
  exact integral_add (h2CompactInner_integrable ψ f hf) (h2CompactInner_integrable ξ f hf)

theorem gamma0EisensteinCutoffCompactTest_smul_seed (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (c : ℂ) (ψ : h2SmoothCompactSeeds) (s : ℂ) :
    gamma0EisensteinCutoffCompactTest N a (c • ψ) s=
      (starRingEnd ℂ) c*gamma0EisensteinCutoffCompactTest N a ψ s := by
  let f := gamma0CuspEisensteinCutoff N a s
  have h (z : UpperHalfPlane) : inner ℂ ((c • ψ).val z) (f z)=
      (starRingEnd ℂ) c*inner ℂ (ψ.val z) (f z) :=
    inner_smul_left (𝕜:=ℂ) (ψ.val z) (f z) c
  change (∫ z : UpperHalfPlane,inner ℂ ((c • ψ).val z) (f z))=
    (starRingEnd ℂ) c*(∫ z : UpperHalfPlane,inner ℂ (ψ.val z) (f z))
  simp_rw [h]
  exact integral_const_mul _ _

theorem gamma0CuspEisensteinMeromorphicTest_add_seed (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (ψ ξ : h2SmoothCompactSeeds) (s : ℂ) :
    gamma0CuspEisensteinMeromorphicTest N a (ψ+ξ) s=
      gamma0CuspEisensteinMeromorphicTest N a ψ s+gamma0CuspEisensteinMeromorphicTest N a ξ s := by
  simp only [gamma0CuspEisensteinMeromorphicTest,gamma0EisensteinCutoffCompactTest_add_seed,map_add,
    inner_add_left,mul_add,Finset.sum_add_distrib]
  ring

theorem gamma0CuspEisensteinMeromorphicTest_smul_seed (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (c : ℂ) (ψ : h2SmoothCompactSeeds) (s : ℂ) :
    gamma0CuspEisensteinMeromorphicTest N a (c • ψ) s=
      (starRingEnd ℂ) c*gamma0CuspEisensteinMeromorphicTest N a ψ s := by
  let b := starRingEnd ℂ c
  have h (j : Gamma0EisensteinCuspClasses N) :
      gamma0EisensteinMatchedCoefficient N a s j*
        (2*(b*gamma0EisensteinCutoffCompactTest N (gamma0EisensteinCuspClassRepresentative N j) ψ (1-s)))=
      b*(gamma0EisensteinMatchedCoefficient N a s j*
        (2*gamma0EisensteinCutoffCompactTest N (gamma0EisensteinCuspClassRepresentative N j) ψ (1-s))) := by ring
  simp only [gamma0CuspEisensteinMeromorphicTest,gamma0EisensteinCutoffCompactTest_smul_seed,map_smul,
    inner_smul_left,← show b=starRingEnd ℂ c from rfl,h,← Finset.mul_sum]
  ring

def gamma0StoneEisensteinAmplitude (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (i : Gamma0EisensteinCuspClasses N) (t : ℝ) : ℂ :=
  gamma0CuspEisensteinMeromorphicTest N (gamma0EisensteinCuspClassRepresentative N i) ψ
    (eisensteinCriticalPoint t)

theorem gamma0StoneEisensteinAmplitude_measurable (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (i : Gamma0EisensteinCuspClasses N) :
    Measurable (gamma0StoneEisensteinAmplitude N ψ i) := by
  have h : Measurable eisensteinCriticalPoint := by unfold eisensteinCriticalPoint; fun_prop
  exact (gamma0CuspEisensteinMeromorphicTest_meromorphic N
    (gamma0EisensteinCuspClassRepresentative N i) ψ).measurable.comp h

def gamma0StoneEisensteinPairIntegrand (N : ℕ) [NeZero N] (ψ ξ : h2SmoothCompactSeeds) (t : ℝ) : ℂ :=
  (∑ i,gamma0StoneEisensteinAmplitude N ψ i t*(starRingEnd ℂ) (gamma0StoneEisensteinAmplitude N ξ i t))/
    ((2*Real.pi:ℝ):ℂ)

theorem gamma0StoneEisensteinPairIntegrand_diagonal (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) (t : ℝ) :
    gamma0StoneEisensteinPairIntegrand N ψ ψ t=(gamma0StoneFrequencyDensity N ψ t:ℂ) := by
  have h (a : ℂ) : a*(starRingEnd ℂ) a=(‖a‖^2:ℝ) := by
    rw [mul_comm,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
  simp only [gamma0StoneEisensteinPairIntegrand,h,gamma0StoneFrequencyDensity,Complex.ofReal_div,
    Complex.ofReal_sum,gamma0StoneEisensteinAmplitude]

theorem gamma0StoneEisensteinPairIntegrand_norm_le (N : ℕ) [NeZero N]
    (ψ ξ : h2SmoothCompactSeeds) (t : ℝ) :
    ‖gamma0StoneEisensteinPairIntegrand N ψ ξ t‖≤
      (gamma0StoneFrequencyDensity N ψ t+gamma0StoneFrequencyDensity N ξ t)/2 := by
  let a (i : Gamma0EisensteinCuspClasses N) := gamma0StoneEisensteinAmplitude N ψ i t
  let b (i : Gamma0EisensteinCuspClasses N) := gamma0StoneEisensteinAmplitude N ξ i t
  have hπ : 0<2*Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hs : ‖∑ i,a i*(starRingEnd ℂ) (b i)‖≤((∑ i,‖a i‖^2)+(∑ i,‖b i‖^2))/2 := by
    rw [← Finset.sum_add_distrib,Finset.sum_div]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul,Complex.norm_conj]
    nlinarith [sq_nonneg (‖a i‖-‖b i‖)]
  unfold gamma0StoneEisensteinPairIntegrand
  rw [norm_div,Complex.norm_real,Real.norm_of_nonneg hπ.le]
  refine (div_le_div_of_nonneg_right hs hπ.le).trans_eq ?_
  change (((∑ i,‖a i‖^2)+(∑ i,‖b i‖^2))/2)/(2*Real.pi)=
    (((∑ i,‖a i‖^2)/(2*Real.pi))+((∑ i,‖b i‖^2)/(2*Real.pi)))/2
  ring

theorem gamma0StoneEisensteinPairIntegrand_integrableOn (N : ℕ) [NeZero N]
    (ψ ξ : h2SmoothCompactSeeds) :
    IntegrableOn (gamma0StoneEisensteinPairIntegrand N ψ ξ) (Ioi 0) := by
  have hmeas : Measurable (gamma0StoneEisensteinPairIntegrand N ψ ξ) := by
    have hsum : Measurable (fun t => ∑ i,gamma0StoneEisensteinAmplitude N ψ i t*
        (starRingEnd ℂ) (gamma0StoneEisensteinAmplitude N ξ i t)) :=
      Finset.measurable_sum _ (fun i _ => (gamma0StoneEisensteinAmplitude_measurable N ψ i).mul
        (Complex.continuous_conj.measurable.comp (gamma0StoneEisensteinAmplitude_measurable N ξ i)))
    exact hsum.div_const _
  have hψ := gamma0StoneFrequencyDensity_integrableOn N ψ (gamma0CompactResolventCutoff N ψ)
  have hξ := gamma0StoneFrequencyDensity_integrableOn N ξ (gamma0CompactResolventCutoff N ξ)
  have hb : IntegrableOn (fun t => (gamma0StoneFrequencyDensity N ψ t+
      gamma0StoneFrequencyDensity N ξ t)/2) (Ioi 0) := (hψ.add hξ).div_const _
  exact hb.mono' hmeas.aestronglyMeasurable (ae_of_all _ (gamma0StoneEisensteinPairIntegrand_norm_le N ψ ξ))

end ArtinMatthews
