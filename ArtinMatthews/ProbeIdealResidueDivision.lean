module

public import ArtinMatthews.ProbeIdealPowerQuotients
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
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


set_option backward.privateInPublic true
@[expose] public section

/-! Exact division by a local uniformizer in a prime-power quotient.
The input need only lie in P^k; global divisibility by pi^k is not assumed. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open IsDedekindDomain
noncomputable section

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

def probeIdealDivideResidue (P : HeightOneSpectrum R) (n k : ℕ)
    (h : R) (hh : h ∈ P.asIdeal ^ k) : R ⧸ P.asIdeal ^ n :=
  Ideal.Quotient.mk (P.asIdeal ^ n) (probeIdealUniformizer_approx P n k h hh).choose

theorem probeIdealDivideResidue_spec (P : HeightOneSpectrum R) (n k : ℕ)
    (h : R) (hh : h ∈ P.asIdeal ^ k) :
    probePrimePowerScale P n k (probeIdealDivideResidue P n k h hh) =
      Ideal.Quotient.mk (P.asIdeal ^ (n + k)) h := by
  unfold probeIdealDivideResidue
  rw [probePrimePowerScale_mk, Ideal.Quotient.eq]
  simpa only [neg_sub] using
    (P.asIdeal ^ (n + k)).neg_mem (probeIdealUniformizer_approx P n k h hh).choose_spec

theorem probeIdealDivideResidue_unique (P : HeightOneSpectrum R) (n k : ℕ)
    (h : R) (hh : h ∈ P.asIdeal ^ k) (q : R ⧸ P.asIdeal ^ n)
    (hq : probePrimePowerScale P n k q = Ideal.Quotient.mk (P.asIdeal ^ (n + k)) h) :
    probeIdealDivideResidue P n k h hh = q := by
  apply probePrimePowerScale_injective P n k
  rw [probeIdealDivideResidue_spec, hq]

theorem probeIdealDivideResidue_uniformizer_mul (P : HeightOneSpectrum R) (n k : ℕ)
    (x : R) (hx : probeIdealUniformizer P ^ k * x ∈ P.asIdeal ^ k) :
    probeIdealDivideResidue P n k (probeIdealUniformizer P ^ k * x) hx =
      Ideal.Quotient.mk (P.asIdeal ^ n) x := by
  apply probeIdealDivideResidue_unique
  exact probePrimePowerScale_mk P n k x

theorem probeIdealDivideResidue_congr (P : HeightOneSpectrum R) (n k : ℕ)
    (h h' : R) (hh : h ∈ P.asIdeal ^ k) (hh' : h' ∈ P.asIdeal ^ k)
    (he : h - h' ∈ P.asIdeal ^ (n + k)) :
    probeIdealDivideResidue P n k h hh = probeIdealDivideResidue P n k h' hh' := by
  apply probePrimePowerScale_injective P n k
  rw [probeIdealDivideResidue_spec, probeIdealDivideResidue_spec, Ideal.Quotient.eq]
  exact he

theorem probeIdealDivideResidue_add (P : HeightOneSpectrum R) (n k : ℕ)
    (a b : R) (ha : a ∈ P.asIdeal ^ k) (hb : b ∈ P.asIdeal ^ k) :
    probeIdealDivideResidue P n k (a + b) ((P.asIdeal ^ k).add_mem ha hb) =
      probeIdealDivideResidue P n k a ha + probeIdealDivideResidue P n k b hb := by
  apply probePrimePowerScale_injective P n k
  rw [map_add, probeIdealDivideResidue_spec, probeIdealDivideResidue_spec,
    probeIdealDivideResidue_spec, map_add]

end

end ArtinMatthews.VaryingKummerAnalytic
