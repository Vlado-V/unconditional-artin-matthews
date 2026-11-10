module

public import ArtinMatthews.ProbeIdealCRTTrace
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

/-! Finite CRT and representative identities for the actual congruence kernel. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain
open scoped NumberField BigOperators Classical
noncomputable section

variable {R : Type*} [CommRing R]

theorem probeIdealPoisson_phase_congr_le (I J M : Ideal R) (hIJ : I * J ≤ M)
    (a h x x' y y' : R) (ha : a ∈ J) (hx : x - x' ∈ I) (hy : y - y' ∈ J)
    (hh : h - a * x ∈ I) (ψ : AddChar (R ⧸ M) ℂ) :
    ψ (Ideal.Quotient.mk _ ((h - a * x) * y)) =
      ψ (Ideal.Quotient.mk _ ((h - a * x') * y')) := by
  apply congrArg ψ
  apply Ideal.Quotient.eq.mpr
  apply hIJ
  have hfirst := Ideal.mul_mem_mul hh hy
  have hsecond : a * (x - x') * y' ∈ I * J :=
    (I * J).mul_mem_right y' (Ideal.mul_mem_mul_rev hx ha)
  convert (I * J).sub_mem hfirst hsecond using 1; ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem probe_product_indicator (g : ι → Prop) [DecidablePred g] (F : ι → ℂ) :
    (if ∀ i, g i then ∏ i, F i else 0) = ∏ i, if g i then F i else 0 := by
  by_cases h : ∀ i, g i
  · simp only [ite_eq_left h, ite_eq_left (h _)]
  · rw [ite_eq_right h]
    symm
    obtain ⟨i, hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

theorem probe_two_pi_sum {A B : ι → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (F : ∀ i, A i → B i → ℂ) :
    (∑ x : ∀ i, A i, ∑ y : ∀ i, B i, ∏ i, F i (x i) (y i)) =
      ∏ i, ∑ x : A i, ∑ y : B i, F i x y := by
  calc
    _ = ∑ x : ∀ i, A i, ∏ i, ∑ y : B i, F i (x i) y := by
      apply Finset.sum_congr rfl
      intro x _
      exact (Fintype.prod_sum (fun i y => F i (x i) y)).symm
    _ = _ := (Fintype.prod_sum (fun i x => ∑ y : B i, F i x y)).symm

variable (K : Type*) [Field K] [NumberField K]

omit [DecidableEq ι] in
theorem probeIdealCRT_mem_iff (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j) (x : 𝓞 K) :
    x ∈ probeIdealCRTModulus K P n ↔ ∀ i, x ∈ (P i).asIdeal ^ n i := by
  constructor
  · intro hx i
    have hz : Ideal.Quotient.mk (probeIdealCRTModulus K P n) x = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hx
    have hi := congrArg (fun z => probeIdealCRTEquiv K P n hP z i) hz
    rw [probeIdealCRTEquiv_mk, map_zero, Pi.zero_apply] at hi
    exact Ideal.Quotient.eq_zero_iff_mem.mp hi
  · intro hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (probeIdealCRTEquiv K P n hP).injective
    ext i
    rw [probeIdealCRTEquiv_mk, map_zero, Pi.zero_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hx i)

omit [DecidableEq ι] in
theorem probeIdealCRT_out_component (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j)
    (x : (𝓞 K) ⧸ probeIdealCRTModulus K P n) (i : ι) :
    Ideal.Quotient.mk ((P i).asIdeal ^ n i) (Quotient.out x) =
      probeIdealCRTEquiv K P n hP x i := by
  rw [← probeIdealCRTEquiv_mk K P n hP, Ideal.Quotient.mk_out]

omit [DecidableEq ι] in
theorem probeIdealCRT_out_difference (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j)
    (x : (𝓞 K) ⧸ probeIdealCRTModulus K P n) (i : ι) :
    Quotient.out x - Quotient.out (probeIdealCRTEquiv K P n hP x i) ∈
      (P i).asIdeal ^ n i := by
  apply Ideal.Quotient.eq.mp
  rw [probeIdealCRT_out_component, Ideal.Quotient.mk_out]

end
end ArtinMatthews.VaryingKummerAnalytic
