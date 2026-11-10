module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset


set_option backward.privateInPublic true
@[expose] public section

/-! The explicit finite-level Euler denominator and its genuine nonvanishing. -/
noncomputable section
namespace ArtinMatthews

def gamma0EisensteinLevelEulerDenominator (N : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ N.primeFactors, (1-(p:ℂ)^(-2*s))

theorem gamma0EisensteinLevelEulerDenominator_one (s : ℂ) :
    gamma0EisensteinLevelEulerDenominator 1 s=1 := by simp [gamma0EisensteinLevelEulerDenominator]

theorem gamma0EisensteinLevelEulerDenominator_existing (N p : ℕ) (hN : 0<N)
    (hp : p.Prime) (hpN : p∣N) (s : ℂ) :
    gamma0EisensteinLevelEulerDenominator (p*N) s=gamma0EisensteinLevelEulerDenominator N s := by
  have hm : p∈N.primeFactors := hp.mem_primeFactors hpN hN.ne'
  unfold gamma0EisensteinLevelEulerDenominator
  rw [Nat.primeFactors_mul hp.ne_zero hN.ne',hp.primeFactors,Finset.singleton_union,Finset.insert_eq_of_mem hm]

theorem gamma0EisensteinLevelEulerDenominator_new (N p : ℕ) (hN : 0<N)
    (hp : p.Prime) (hpN : ¬p∣N) (s : ℂ) :
    gamma0EisensteinLevelEulerDenominator (p*N) s=
      (1-(p:ℂ)^(-2*s))*gamma0EisensteinLevelEulerDenominator N s := by
  have hm : p∉N.primeFactors := fun h => hpN (Nat.dvd_of_mem_primeFactors h)
  unfold gamma0EisensteinLevelEulerDenominator
  rw [Nat.primeFactors_mul hp.ne_zero hN.ne',hp.primeFactors,Finset.singleton_union,Finset.prod_insert hm]

theorem gamma0EisensteinPrimeFactor_norm_lt_one (p : ℕ) (hp : p.Prime) (s : ℂ) (hs : 1<s.re) :
    ‖(p:ℂ)^(-2*s)‖<1 := by
  rw [Complex.norm_natCast_cpow_of_pos hp.pos]
  have hre : (-2*s).re= -2*s.re := by simp
  rw [hre]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)

theorem gamma0EisensteinLevelEulerDenominator_ne_zero (N : ℕ) (s : ℂ) (hs : 1<s.re) :
    gamma0EisensteinLevelEulerDenominator N s≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  have h := gamma0EisensteinPrimeFactor_norm_lt_one p (Nat.prime_of_mem_primeFactors hp) s hs
  intro he
  have hv : (p:ℂ)^(-2*s)=1 := (sub_eq_zero.mp he).symm
  rw [hv,norm_one] at h
  exact lt_irrefl _ h

end ArtinMatthews
