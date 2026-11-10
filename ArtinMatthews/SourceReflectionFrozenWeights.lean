module

public import ArtinMatthews.SourceReflectionFrozenLocal
public import ArtinMatthews.SourcePrimeExponents
public import ArtinMatthews.SourceReflectionPowerful
public import ArtinMatthews.FinitePiSeries
public import ArtinMatthews.FiniteSupportEulerPrefix
public import ArtinMatthews.SourceReflectionExteriorRows
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The active choices and frozen numerator weights of the reflected
expansion, in the actual exterior-prime coordinates. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

local notation "Prime" => SourceExteriorPrime F S₀
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
def sourceReflectionPrimeNorm (P : Prime) : ℝ := (P.val.asIdeal.absNorm : ℝ)

local notation "qp" => sourceReflectionPrimeNorm F S₀

def sourceReflectionActiveChoices (h : E) : Finset (Finset Prime) :=
  h.support.powerset.filter (fun f => ∀ P ∈ h.support, h P % 6 ≠ 0 → P ∈ f)

def sourceReflectionActiveExponents (f : Finset Prime) : E :=
  Finsupp.onFinset f (fun P => if P ∈ f then 1 else 0)
    (fun _ hp => by by_contra hn; exact hp (ite_eq_right hn))

theorem sourceReflectionActiveExponents_support (f : Finset Prime) :
    (sourceReflectionActiveExponents F S₀ f).support = f := by
  ext P
  simp only [sourceReflectionActiveExponents, Finsupp.mem_support_iff, Finsupp.onFinset_apply]
  by_cases hp : P ∈ f <;> simp [hp]

theorem sourceReflectionActiveExponents_squarefree (f : Finset Prime) :
    sourceReflectionIsSquarefree (sourceReflectionActiveExponents F S₀ f) := by
  intro P
  simp only [sourceReflectionActiveExponents, Finsupp.onFinset_apply]
  split <;> omega

theorem sourceReflectionActiveChoice_sq_le {h : E} (hh : sourceReflectionIsPowerful h)
    {f : Finset Prime} (hf : f ∈ sourceReflectionActiveChoices F S₀ h) :
    (q (sourceReflectionActiveExponents F S₀ f) : ℝ) ^ 2 ≤ (q h : ℝ) := by
  apply sourceReflectionActiveNorm_sq_le F S₀ hh (sourceReflectionActiveExponents_squarefree F S₀ f)
  rw [sourceReflectionActiveExponents_support]
  exact Finset.mem_powerset.mp (Finset.mem_filter.mp hf).1

abbrev SourceReflectionFrozenNumerator (f : Finset Prime) :=
  {a : E // a.support ⊆ f}

def sourceReflectionFrozenWeight (f : Finset Prime) (a : E) : ℝ :=
  ∏ P ∈ f, sourceReflectionFrozenLocalWeight (qp P) (a P)

def sourceReflectionFrozenFactors (f : Finset Prime) (σ : ℝ) : ℝ :=
  ∏ P ∈ f, sourceReflectionFrozenLocalFactor (qp P) σ

theorem sourceReflection_primeNorm_two_le (P : Prime) : (2 : ℝ) ≤ qp P := by
  change (2 : ℝ) ≤ (P.val.asIdeal.absNorm : ℝ)
  exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm P.val)

theorem sourceReflectionFrozenWeight_nonneg (f : Finset Prime) (a : E) :
    0 ≤ sourceReflectionFrozenWeight F S₀ f a := by
  apply Finset.prod_nonneg
  intro P _
  have hp : 0 ≤ qp P := (by norm_num : (0 : ℝ) ≤ 2).trans (sourceReflection_primeNorm_two_le F S₀ P)
  simpa only [sourceReflectionFrozenLocalTerm, neg_zero, zero_mul, Real.rpow_zero, mul_one] using
    sourceReflectionFrozenLocalTerm_nonneg hp 0 (a P)

theorem sourceReflectionFrozenFactors_nonneg (f : Finset Prime) {σ : ℝ} (hσ : 0 ≤ σ) :
    0 ≤ sourceReflectionFrozenFactors F S₀ f σ :=
  Finset.prod_nonneg (fun P _ => sourceReflectionFrozenLocalFactor_nonneg
    (sourceReflection_primeNorm_two_le F S₀ P) hσ)

theorem sourceReflectionFrozenWeight_mul_rpow (f : Finset Prime)
    (a : SourceReflectionFrozenNumerator F S₀ f) (σ : ℝ) :
    sourceReflectionFrozenWeight F S₀ f a.val * (q a.val : ℝ) ^ (-σ) =
      ∏ P ∈ f, sourceReflectionFrozenLocalTerm (qp P) σ (a.val P) := by
  have hq : (q a.val : ℝ) = ∏ P ∈ f, (qp P) ^ a.val P := by
    simp only [sourcePrimeExponentNorm]
    rw [Finsupp.prod_of_support_subset a.val a.property _ (fun _ _ => pow_zero _),
      Nat.cast_prod]
    simp only [Nat.cast_pow, sourceReflectionPrimeNorm]
  have hp (P : Prime) : 0 ≤ qp P := (by norm_num : (0 : ℝ) ≤ 2).trans
    (sourceReflection_primeNorm_two_le F S₀ P)
  rw [hq, ← Real.finsetProd_rpow f (fun P => (qp P) ^ a.val P)
    (fun P _ => pow_nonneg (hp P) _) (-σ), sourceReflectionFrozenWeight,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P _
  rw [sourceReflectionFrozenLocalTerm, ← Real.rpow_natCast_mul (hp P),
    mul_comm (a.val P : ℝ)]

theorem sourceReflectionFrozenDirichlet (f : Finset Prime) {σ : ℝ} (hσ : 0 ≤ σ) :
    HasSum (fun a : SourceReflectionFrozenNumerator F S₀ f =>
      sourceReflectionFrozenWeight F S₀ f a.val * (q a.val : ℝ) ^ (-σ))
      (sourceReflectionFrozenFactors F S₀ f σ) := by
  let w (P : f) (n : ℕ) := sourceReflectionFrozenLocalTerm (qp P.val) σ n
  have hn (P : f) (n : ℕ) : 0 ≤ w P n := sourceReflectionFrozenLocalTerm_nonneg
    ((by norm_num : (0 : ℝ) ≤ 2).trans (sourceReflection_primeNorm_two_le F S₀ P.val)) σ n
  have hw (P : f) := sourceReflectionFrozenLocal_hasSum (sourceReflection_primeNorm_two_le F S₀ P.val) hσ
  have hcomplex (P : f) : Summable (fun n => ‖(w P n : ℂ)‖) := by
    exact (hw P).summable.congr (fun n => by rw [Complex.norm_real, Real.norm_of_nonneg (hn P n)])
  obtain ⟨hs, ht⟩ := SourceEuler.finitePiSeries f ℕ (fun P n => (w P n : ℂ)) hcomplex
  have hsr : Summable (fun a : f → ℕ => ∏ P : f, w P (a P)) := by
    apply hs.congr
    intro a
    rw [norm_prod]
    exact Finset.prod_congr rfl (fun P _ => by rw [Complex.norm_real, Real.norm_of_nonneg (hn P _)])
  have htr : (∑' a : f → ℕ, ∏ P : f, w P (a P)) = sourceReflectionFrozenFactors F S₀ f σ := by
    have hc (P : f) : (∑' n, (w P n : ℂ)) = (sourceReflectionFrozenLocalFactor (qp P.val) σ : ℂ) := by
      rw [← Complex.ofReal_tsum]
      exact congrArg Complex.ofReal (hw P).tsum_eq
    simp_rw [hc] at ht
    apply Complex.ofReal_injective
    rw [Complex.ofReal_tsum, sourceReflectionFrozenFactors, Complex.ofReal_prod, ← Finset.prod_coe_sort]
    simpa only [Complex.ofReal_prod] using ht
  let e := SourceEuler.primeChoicePrefixEquiv (X := ℕ) f
  have hprod (a : SourceReflectionFrozenNumerator F S₀ f) :
      sourceReflectionFrozenWeight F S₀ f a.val * (q a.val : ℝ) ^ (-σ) =
        ∏ P : f, w P (e a P) := by
    rw [sourceReflectionFrozenWeight_mul_rpow, ← Finset.prod_coe_sort]
    rfl
  have hs' : Summable (fun a : SourceReflectionFrozenNumerator F S₀ f =>
      sourceReflectionFrozenWeight F S₀ f a.val * (q a.val : ℝ) ^ (-σ)) :=
    (e.summable_iff.mpr hsr).congr (fun a => (hprod a).symm)
  exact hs'.hasSum_iff.mpr ((tsum_congr hprod).trans ((e.tsum_eq _).trans htr))

end
end ArtinMatthews.SourceEulerAssembly
