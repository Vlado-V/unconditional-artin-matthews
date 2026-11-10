module

public import ArtinMatthews.SourcePrimeIdealFactorization
public import ArtinMatthews.ReflectionCoefficientRow
public import ArtinMatthews.SourceReflectionPowerful
public import ArtinMatthews.SourceReflectionExteriorRows
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
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

/-! An unramified rational prime supplies one exterior squarefree ideal.
Its norm is the rational prime to the field degree. Distinct rational
primes supply tags with disjoint actual prime-ideal supports. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField Ideal IsDedekindDomain UniqueFactorizationMonoid VaryingKummerAnalytic
open SIntegerPrincipalization
open scoped BigOperators Classical NumberField

noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

local notation "P" => SourceExteriorPrime F S₀
local notation "I" => Ideal (𝓞 F)
local notation "q" => sourcePrimeExponentNorm F S₀

def sourceQuadraticRationalCutoff : ℕ :=
  (NumberField.discr F).natAbs + ∑ Q ∈ sourceHilbertSet F S₀, Q.asIdeal.absNorm

def sourceQuadraticRationalIdeal (p : ℕ) : I := Ideal.span {(p : 𝓞 F)}

private theorem sourceQuadraticRationalIdeal_ne_bot {p : ℕ} (hp : p.Prime) :
    sourceQuadraticRationalIdeal F p ≠ ⊥ :=
  Ideal.span_singleton_eq_bot.not.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)

omit [NumberField F] in
private theorem sourceQuadraticRationalMap (p : ℕ) :
    (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 F)) =
      sourceQuadraticRationalIdeal F p := by
  simp only [Ideal.map_span, Set.image_singleton, map_natCast, sourceQuadraticRationalIdeal]

private theorem sourceQuadraticRational_liesOver {p : ℕ} (hp : p.Prime)
    (Q : I) [Q.IsPrime] (hQ : Q ∣ sourceQuadraticRationalIdeal F p) :
    Q.LiesOver (Ideal.span {(p : ℤ)}) := by
  let : Fact p.Prime := ⟨hp⟩
  have hpb : Ideal.span {(p : ℤ)} ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hmem : Q ∈ normalizedFactors (sourceQuadraticRationalIdeal F p) :=
    (Ideal.mem_normalizedFactors_iff (sourceQuadraticRationalIdeal_ne_bot F hp)).mpr
      ⟨inferInstance, Ideal.dvd_iff_le.mp hQ⟩
  have h := (Ideal.mem_primesOver_iff_mem_normalizedFactors (𝓞 F) hpb).mpr
    (show Q ∈ normalizedFactors ((Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 F))) from
      (sourceQuadraticRationalMap F p).symm ▸ hmem)
  exact h.2

omit [NumberField F] in
private theorem sourceQuadraticRational_dvd_of_mem {p n : ℕ}
    (Q : I) [Q.LiesOver (Ideal.span {(p : ℤ)})] (hn : (n : 𝓞 F) ∈ Q) :
    p ∣ n := by
  have hz : (n : ℤ) ∈ Ideal.span {(p : ℤ)} :=
    (Q.mem_of_liesOver (Ideal.span {(p : ℤ)}) (n : ℤ)).mpr (by
      simpa only [map_natCast] using hn)
  exact Int.natCast_dvd_natCast.mp (Ideal.mem_span_singleton.mp hz)

theorem sourceQuadraticRationalIdeal_squarefree {p : ℕ} (hp : p.Prime)
    (hbig : (NumberField.discr F).natAbs < p) :
    Squarefree (sourceQuadraticRationalIdeal F p) := by
  rw [squarefree_iff_nodup_normalizedFactors (sourceQuadraticRationalIdeal_ne_bot F hp),
    Multiset.nodup_iff_count_le_one]
  intro Q
  by_cases hQ : Q ∈ normalizedFactors (sourceQuadraticRationalIdeal F p)
  · have h := (Ideal.mem_normalizedFactors_iff (sourceQuadraticRationalIdeal_ne_bot F hp)).mp hQ
    let : Q.IsPrime := h.1
    let : Q.LiesOver (Ideal.span {(p : ℤ)}) :=
      sourceQuadraticRational_liesOver F hp Q (Ideal.dvd_iff_le.mpr h.2)
    have hnd : ¬ Q ∣ differentIdeal ℤ (𝓞 F) := by
      intro hdiv
      have hn : ((NumberField.discr F).natAbs : 𝓞 F) ∈ Q := by
        rw [← NumberField.absNorm_differentIdeal F (𝓞 F)]
        exact (Ideal.dvd_iff_le.mp hdiv) (Ideal.absNorm_mem _)
      have hdp := sourceQuadraticRational_dvd_of_mem F (p := p) Q hn
      exact (not_le_of_gt hbig) (Nat.le_of_dvd (Int.natAbs_pos.mpr (NumberField.discr_ne_zero F)) hdp)
    let : Algebra.IsUnramifiedAt ℤ Q := not_dvd_differentIdeal_iff.mp hnd
    have he := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := ℤ) (p := Q)
    have hmap0 : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 F)) ≠ ⊥ := by
      rw [sourceQuadraticRationalMap F p]
      exact sourceQuadraticRationalIdeal_ne_bot F hp
    have hcount := IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
      (Ideal.span {(p : ℤ)}) Q hmap0
    rw [sourceQuadraticRationalMap F p, he] at hcount
    exact hcount.ge
  · rw [Multiset.count_eq_zero.mpr hQ]
    exact Nat.zero_le 1

theorem sourceQuadraticRationalIdeal_exterior {p : ℕ} (hp : p.Prime)
    (hbig : sourceQuadraticRationalCutoff F S₀ < p) :
    sourceQuadraticRationalIdeal F p ∈ exteriorIdeals
      (principalizingDenominator (sourceHilbertSeed F S₀)) := by
  apply (exteriorIdeals_mem_iff (sourceHilbertSeed F S₀) _).mpr
  refine ⟨sourceQuadraticRationalIdeal_ne_bot F hp, ?_⟩
  intro Q hQ hdiv
  let : Q.asIdeal.IsPrime := Q.isPrime
  let : Q.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
    sourceQuadraticRational_liesOver F hp Q.asIdeal hdiv
  have hdp := sourceQuadraticRational_dvd_of_mem F (p := p) Q.asIdeal (Ideal.absNorm_mem Q.asIdeal)
  have hlow := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr Q.ne_bot)) hdp
  have hhigh : Q.asIdeal.absNorm ≤ sourceQuadraticRationalCutoff F S₀ := by
    apply le_trans (Finset.single_le_sum (fun Q _ => Nat.zero_le Q.asIdeal.absNorm)
      (show Q ∈ sourceHilbertSet F S₀ from hQ))
    exact Nat.le_add_left _ _
  exact (not_le_of_gt hbig) (hlow.trans hhigh)

def sourceQuadraticRationalTag (p : ℕ) (hp : p.Prime)
    (hbig : sourceQuadraticRationalCutoff F S₀ < p) : ReflectionSquarefreeExponents F S₀ := by
  let I₀ : exteriorIdeals (principalizingDenominator (sourceHilbertSeed F S₀)) :=
    ⟨sourceQuadraticRationalIdeal F p,
    sourceQuadraticRationalIdeal_exterior F S₀ hp hbig⟩
  let e := sourceExteriorIdealExponents F S₀ I₀
  refine ⟨e, (sourceReflectionExteriorIdeal_squarefree F S₀ e).mp ?_⟩
  rw [sourceExteriorIdealExponents_recover F S₀ I₀]
  exact sourceQuadraticRationalIdeal_squarefree F hp ((Nat.le_add_right _ _).trans_lt hbig)

theorem sourceQuadraticRationalTag_ideal {p : ℕ} (hp : p.Prime)
    (hbig : sourceQuadraticRationalCutoff F S₀ < p) :
    sourcePrimeExponentIdeal F S₀ (sourceQuadraticRationalTag F S₀ p hp hbig).val =
      sourceQuadraticRationalIdeal F p :=
  sourceExteriorIdealExponents_recover F S₀
    ⟨sourceQuadraticRationalIdeal F p, sourceQuadraticRationalIdeal_exterior F S₀ hp hbig⟩

theorem sourceQuadraticRationalTag_norm {p : ℕ} (hp : p.Prime)
    (hbig : sourceQuadraticRationalCutoff F S₀ < p) :
    q (sourceQuadraticRationalTag F S₀ p hp hbig).val = p ^ Module.finrank ℚ F := by
  rw [← sourcePrimeExponentIdeal_norm, sourceQuadraticRationalTag_ideal, sourceQuadraticRationalIdeal,
    Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank]

private theorem sourceQuadraticRationalTag_support_dvd {p : ℕ} (hp : p.Prime)
    (hbig : sourceQuadraticRationalCutoff F S₀ < p)
    {Q : P} (hQ : Q ∈ (sourceQuadraticRationalTag F S₀ p hp hbig).val.support) :
    Q.val.asIdeal ∣ sourceQuadraticRationalIdeal F p := by
  let e := (sourceQuadraticRationalTag F S₀ p hp hbig).val
  have hn : e Q ≠ 0 := Finsupp.mem_support_iff.mp hQ
  rw [← sourceQuadraticRationalTag_ideal F S₀ hp hbig]
  change Q.val.asIdeal ∣ ∏ R ∈ e.support, R.val.asIdeal ^ e R
  exact (dvd_pow_self _ hn).trans (Finset.dvd_prod_of_mem (fun R : P => R.val.asIdeal ^ e R) hQ)

theorem sourceQuadraticRationalTag_support_disjoint {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hp' : sourceQuadraticRationalCutoff F S₀ < p)
    (hr' : sourceQuadraticRationalCutoff F S₀ < r) (hne : p ≠ r) :
    Disjoint (sourceQuadraticRationalTag F S₀ p hp hp').val.support
      (sourceQuadraticRationalTag F S₀ r hr hr').val.support := by
  apply Finset.disjoint_left.mpr
  intro Q hQ hR
  let : Q.val.asIdeal.IsPrime := Q.val.isPrime
  let : Q.val.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
    sourceQuadraticRational_liesOver F hp Q.val.asIdeal
      (sourceQuadraticRationalTag_support_dvd F S₀ hp hp' hQ)
  have hdiv := sourceQuadraticRationalTag_support_dvd F S₀ hr hr' hR
  have hmem : (r : 𝓞 F) ∈ Q.val.asIdeal :=
    (Ideal.dvd_iff_le.mp hdiv) (Ideal.subset_span (Set.mem_singleton _))
  have hpr := sourceQuadraticRational_dvd_of_mem F (p := p) Q.val.asIdeal hmem
  exact hne ((Nat.prime_dvd_prime_iff_eq hp hr).mp hpr)

end
end ArtinMatthews.SourceEulerAssembly
