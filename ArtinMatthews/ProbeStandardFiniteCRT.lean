module

public import ArtinMatthews.ProbeStandardFinitePoisson
public import ArtinMatthews.ProbeStandardCRTPhase
public import ArtinMatthews.ProbeIdealPoissonCRT
public import ArtinMatthews.ProbeIdealPoissonCRTHelpers
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

/-! Finite CRT factorization of the literal global trace F(s,A,h), for
actual integral denominators away from the different. Shared prime powers
of s and A remain inside each local congruence sum. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain
open scoped NumberField BigOperators Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def probeCRTResidueWeight (P : ι → HeightOneSpectrum (𝓞 K)) (k : ι → ℕ)
    (W : ∀ i, ((𝓞 K) ⧸ (P i).asIdeal ^ k i) → ℂ) (x : 𝓞 K) : ℂ :=
  ∏ i, W i (Ideal.Quotient.mk _ x)

omit [NumberField K] [DecidableEq ι] in
theorem probeCRTModulus_add_eq (P : ι → HeightOneSpectrum (𝓞 K)) (k t : ι → ℕ)
    (s A : 𝓞 K) (hS : probeIdealCRTModulus K P k = Ideal.span {s})
    (hA : probeIdealCRTModulus K P t = Ideal.span {A}) :
    probeIdealCRTModulus K P (fun i => k i + t i) = Ideal.span {s * A} := by
  have he : probeIdealCRTModulus K P (fun i => k i + t i) =
      probeIdealCRTModulus K P k * probeIdealCRTModulus K P t := by
    simp only [probeIdealCRTModulus, pow_add, Finset.prod_mul_distrib]
  rw [he, hS, hA, Ideal.span_singleton_mul_span_singleton]

omit [DecidableEq ι] in
theorem probeStandardFiniteSum_eq_CRT (P : ι → HeightOneSpectrum (𝓞 K)) (k t : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j) (s A h : 𝓞 K) (hSA : s * A ≠ 0)
    (hcop : IsCoprime (differentIdeal ℤ (𝓞 K)) (Ideal.span {s * A}))
    (hN : probeIdealCRTModulus K P (fun i => k i + t i) = Ideal.span {s * A})
    (W : ∀ i, ((𝓞 K) ⧸ (P i).asIdeal ^ k i) → ℂ)
    (V : ∀ i, ((𝓞 K) ⧸ (P i).asIdeal ^ t i) → ℂ) :
    probeStandardFiniteSum K (probeIdealCRTModulus K P k) (probeIdealCRTModulus K P t)
        s A h (probeCRTResidueWeight K P k W) (probeCRTResidueWeight K P t V) =
      probeIdealPoissonGlobalSum K P k t hP
        (probeStandardCRTPhase K P (fun i => k i + t i) (s * A) hSA hcop hN)
        A h W V := by
  unfold probeStandardFiniteSum probeIdealPoissonGlobalSum
  apply tsum_congr
  intro d
  apply tsum_congr
  intro v
  have hw : probeCRTResidueWeight K P k W (Quotient.out d) =
      ∏ i, W i (probeIdealCRTEquiv K P k hP d i) := by
    apply Finset.prod_congr rfl
    intro i _
    exact congrArg (W i) (probeIdealCRT_out_component K P k hP d i)
  have hv : probeCRTResidueWeight K P t V (Quotient.out v) =
      ∏ i, V i (probeIdealCRTEquiv K P t hP v i) := by
    apply Finset.prod_congr rfl
    intro i _
    exact congrArg (V i) (probeIdealCRT_out_component K P t hP v i)
  by_cases hh : h - A * Quotient.out d ∈ probeIdealCRTModulus K P k
  · rw [ite_eq_left hh, ite_eq_left hh]
    rw [hw, hv]
    rw [probeStandardCRTPhase_mk]
    simp only [probeFieldTraceExponential, map_mul]
  · rw [ite_eq_right hh, ite_eq_right hh]

theorem probeStandardFiniteF_factor (P : ι → HeightOneSpectrum (𝓞 K)) (k t : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j) (s A h : 𝓞 K) (hs : s ≠ 0) (hA : A ≠ 0)
    (hcop : IsCoprime (differentIdeal ℤ (𝓞 K)) (Ideal.span {s * A}))
    (hS : probeIdealCRTModulus K P k = Ideal.span {s})
    (hT : probeIdealCRTModulus K P t = Ideal.span {A})
    (W : ∀ i, ((𝓞 K) ⧸ (P i).asIdeal ^ k i) → ℂ)
    (V : ∀ i, ((𝓞 K) ⧸ (P i).asIdeal ^ t i) → ℂ) :
    probeStandardFiniteF K s A h (probeCRTResidueWeight K P k W) (probeCRTResidueWeight K P t V) =
      ∏ i, probeIdealPoissonLocalSum K P k t hP
        (probeStandardCRTPhase K P (fun i => k i + t i) (s * A) (mul_ne_zero hs hA) hcop
          (probeCRTModulus_add_eq K P k t s A hS hT)) A h W V i := by
  let Ψ := probeStandardCRTPhase K P (fun i => k i + t i) (s * A) (mul_ne_zero hs hA) hcop
    (probeCRTModulus_add_eq K P k t s A hS hT)
  have ha : A ∈ probeIdealCRTModulus K P t := by
    rw [hT]
    exact Ideal.mem_span_singleton_self A
  calc
    _ = probeStandardFiniteSum K (probeIdealCRTModulus K P k) (probeIdealCRTModulus K P t)
        s A h (probeCRTResidueWeight K P k W) (probeCRTResidueWeight K P t V) := by
      unfold probeStandardFiniteF
      exact congrArg₂ (fun I J => probeStandardFiniteSum K I J s A h
        (probeCRTResidueWeight K P k W) (probeCRTResidueWeight K P t V)) hS.symm hT.symm
    _ = probeIdealPoissonGlobalSum K P k t hP Ψ A h W V :=
      probeStandardFiniteSum_eq_CRT K P k t hP s A h (mul_ne_zero hs hA) hcop _ W V
    _ = _ := probeIdealPoissonGlobalSum_factor K P k t hP Ψ A h ha W V

end
end ArtinMatthews.VaryingKummerAnalytic
