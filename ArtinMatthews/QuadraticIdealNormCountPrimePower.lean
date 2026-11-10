module

public import OAI.NumberTheory.PrimePackets.IdealCoefficients
public import ArtinMatthews.QuadraticIdealNormCountAbstract
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

/-! The sharp quadratic ideal norm count at prime powers. -/

noncomputable section
open scoped NumberField
namespace ArtinMatthews
open OAI.PrimeDegreePackets UniqueFactorizationMonoid

/-- In degree two, the norm-`p^r` fiber has at most `r+1` ideals. The proof
uses the actual prime ideal factors; inert and ramified primes are included. -/
theorem quadraticIdealCoefficient_prime_pow_le
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℤ (𝓞 K) = 2) {p : ℕ} (hp : p.Prime) (r : ℕ) :
    idealCoefficient K (p ^ r) ≤ r + 1 := by
  classical
  rw [idealCoefficient_pos K _ (pow_ne_zero _ hp.ne_zero)]
  let A := {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ r}
  let f : A → Multiset (Ideal (𝓞 K)) := fun I => normalizedFactors I.val
  let S := idealsOverPrime K p
  have hzero (I : A) : I.val ≠ ⊥ := by
    intro h
    have hz : (0 : ℕ) = p ^ r := by simpa [h] using I.property
    exact (pow_ne_zero r hp.ne_zero) hz.symm
  have hf : Function.Injective f := by
    intro I J h
    apply Subtype.ext
    have hh := congrArg Multiset.prod h
    simpa only [f, Ideal.prod_normalizedFactors_eq_self (hzero I),
      Ideal.prod_normalizedFactors_eq_self (hzero J)] using hh
  have hS : S.card ≤ 2 :=
    (idealsOverPrime_card_le K hp).trans_eq hdegree
  have hs : ∀ I : A, ∀ P, P ∈ f I → P ∈ S := by
    intro I P hP
    exact ideal_factor_mem_over K hp I.property hP
  have hnorm : ∀ P ∈ S, 2 ≤ Ideal.absNorm P := by
    intro P hP
    have hfac : P ∈ normalizedFactors (Ideal.span {(p : 𝓞 K)}) := by
      simpa only [S, idealsOverPrime, Multiset.mem_toFinset] using hP
    exact hp.two_le.trans
      (ideal_factor_prime_power K hp (Ideal.absNorm_span_natCast p) hfac).2
  have hprod : ∀ I : A, ((f I).map Ideal.absNorm).prod = p ^ r := by
    intro I
    change ((normalizedFactors I.val).map Ideal.absNorm).prod = p ^ r
    rw [← map_multiset_prod, Ideal.prod_normalizedFactors_eq_self (hzero I)]
    exact I.property
  exact two_support_multiset_norm_fiber_card_le f hf S hS hs Ideal.absNorm hnorm
    (p ^ r) r hprod (fun I => ideal_factor_count_le K hp I.property)

end ArtinMatthews
