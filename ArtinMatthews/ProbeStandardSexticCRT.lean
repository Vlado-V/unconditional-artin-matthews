module

public import ArtinMatthews.ProbeStandardFiniteCRT
public import ArtinMatthews.ProbeIdealPrimeGauss
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
public import Mathlib.RingTheory.Henselian
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

/-! The source's exact absent-modulus and positive-modulus character weights
in the standard finite CRT factorization. Coherent local phases are compared
through genuine units; no assertion that these units equal one is made. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain
open scoped NumberField BigOperators Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def probePowerResidueWeight (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ) (x : (𝓞 K) ⧸ P.asIdeal ^ n) : ℂ :=
  if hn : 0 < n then (χ ^ n) (probeIdealResidueReduction K P n hn x) else 1

omit [NumberField K] in
theorem probePowerResidueWeight_zero (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (x : (𝓞 K) ⧸ P.asIdeal ^ 0) :
    probePowerResidueWeight K P χ 0 x = 1 := rfl

omit [NumberField K] in
theorem probePowerResidueWeight_succ_mk (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ) (x : 𝓞 K) :
    probePowerResidueWeight K P χ (n + 1) (Ideal.Quotient.mk _ x) =
      (χ (Ideal.Quotient.mk P.asIdeal x)) ^ (n + 1) := by
  rw [probePowerResidueWeight, dite_eq_left (Nat.succ_pos n), probeIdealResidueReduction_mk,
    χ.pow_apply' (Nat.succ_ne_zero n)]

theorem probePowerResidueWeight_succ_zero (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ) (x : 𝓞 K) (hx : x ∈ P.asIdeal) :
    probePowerResidueWeight K P χ (n + 1) (Ideal.Quotient.mk _ x) = 0 := by
  let : Field ((𝓞 K) ⧸ P.asIdeal) := Ideal.Quotient.field _
  rw [probePowerResidueWeight_succ_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hx,
    MulChar.map_zero, zero_pow (Nat.succ_ne_zero n)]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem probeStandardSexticFiniteF_factor (P : ι → HeightOneSpectrum (𝓞 K)) (k t : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j) (s A h : 𝓞 K) (hs : s ≠ 0) (hA : A ≠ 0)
    (hcop : IsCoprime (differentIdeal ℤ (𝓞 K)) (Ideal.span {s * A}))
    (hS : probeIdealCRTModulus K P k = Ideal.span {s})
    (hT : probeIdealCRTModulus K P t = Ideal.span {A})
    (χ : ∀ i, MulChar ((𝓞 K) ⧸ (P i).asIdeal) ℂ) :
    probeStandardFiniteF K s A h
      (probeCRTResidueWeight K P k (fun i => probePowerResidueWeight K (P i) (χ i) (k i)))
      (probeCRTResidueWeight K P t (fun i => probePowerResidueWeight K (P i) (χ i) (t i))) =
      ∏ i, probeIdealPoissonLocalSum K P k t hP
        (probeStandardCRTPhase K P (fun i => k i + t i) (s * A) (mul_ne_zero hs hA) hcop
          (probeCRTModulus_add_eq K P k t s A hS hT)) A h
        (fun i => probePowerResidueWeight K (P i) (χ i) (k i))
        (fun i => probePowerResidueWeight K (P i) (χ i) (t i)) i :=
  probeStandardFiniteF_factor K P k t hP s A h hs hA hcop hS hT _ _

theorem probeStandardSexticFiniteF_factor_coherent
    (P : ι → HeightOneSpectrum (𝓞 K)) (k t : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j) (s A h : 𝓞 K) (hs : s ≠ 0) (hA : A ≠ 0)
    (hcop : IsCoprime (differentIdeal ℤ (𝓞 K)) (Ideal.span {s * A}))
    (hS : probeIdealCRTModulus K P k = Ideal.span {s})
    (hT : probeIdealCRTModulus K P t = Ideal.span {A})
    (χ : ∀ i, MulChar ((𝓞 K) ⧸ (P i).asIdeal) ℂ) :
    ∃ u : ∀ i, ((𝓞 K) ⧸ (P i).asIdeal ^ (k i + t i))ˣ,
    probeStandardFiniteF K s A h
      (probeCRTResidueWeight K P k (fun i => probePowerResidueWeight K (P i) (χ i) (k i)))
      (probeCRTResidueWeight K P t (fun i => probePowerResidueWeight K (P i) (χ i) (t i))) =
      ∏ i, ∑' d : (𝓞 K) ⧸ (P i).asIdeal ^ k i,
        ∑' v : (𝓞 K) ⧸ (P i).asIdeal ^ t i,
          if h - A * Quotient.out d ∈ (P i).asIdeal ^ k i then
            probePowerResidueWeight K (P i) (χ i) (k i) d *
              probePowerResidueWeight K (P i) (χ i) (t i) v *
              probeIdealPhase K (P i) (k i + t i)
                ((u i : (𝓞 K) ⧸ (P i).asIdeal ^ (k i + t i)) *
                  Ideal.Quotient.mk _ ((h - A * Quotient.out d) * Quotient.out v)) else 0 := by
  let hN := probeCRTModulus_add_eq K P k t s A hS hT
  let Ψ := probeStandardCRTPhase K P (fun i => k i + t i) (s * A)
    (mul_ne_zero hs hA) hcop hN
  have hu := fun i => probeStandardCRTPhase_component_unit K P (fun i => k i + t i) hP
    (s * A) (mul_ne_zero hs hA) hcop hN i
  choose u hu using hu
  refine ⟨u, ?_⟩
  rw [probeStandardSexticFiniteF_factor K P k t hP s A h hs hA hcop hS hT χ]
  apply Finset.prod_congr rfl
  intro i _
  unfold probeIdealPoissonLocalSum
  apply tsum_congr
  intro d
  apply tsum_congr
  intro v
  split_ifs
  · have he := congrArg (fun ψ : AddChar ((𝓞 K) ⧸ (P i).asIdeal ^ (k i + t i)) ℂ =>
      ψ (Ideal.Quotient.mk _ ((h - A * Quotient.out d) * Quotient.out v))) (hu i)
    exact congrArg (fun z => probePowerResidueWeight K (P i) (χ i) (k i) d *
      probePowerResidueWeight K (P i) (χ i) (t i) v * z) he.symm
  · rfl

end
end ArtinMatthews.VaryingKummerAnalytic
