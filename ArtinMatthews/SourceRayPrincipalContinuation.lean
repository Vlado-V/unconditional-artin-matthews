module

public import ArtinMatthews.PrincipalAngularResidue
public import ArtinMatthews.SourceFullIdealFactorization
public import ArtinMatthews.VaryingKummerAnalyticRayIdealConductorOne
public import ArtinMatthews.SourceFullIdealEuler
public import ArtinMatthews.SourceLocalCorrectionFactorization
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! A principal finite-order ideal ray character has precisely the
Dedekind series with its actual conductor primes deleted, with the
regularized simple pole retained. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain UniqueFactorizationMonoid VaryingKummerAnalytic
open scoped NumberField Classical BigOperators nonZeroDivisors
noncomputable section
variable (F : Type) [Field F] [NumberField F]

def sourceRayModulusPrimeSet (M : Ideal (𝓞 F)) : Finset (ProbePrime F) :=
  (sourceFullIdealExponents F M).support

theorem sourceRayModulusPrimeSet_mem {M : Ideal (𝓞 F)} (hM : M ≠ ⊥) (P : ProbePrime F) :
    P ∈ sourceRayModulusPrimeSet F M ↔ P.asIdeal ∣ M := by
  let e := sourceFullIdealExponents F M
  let emb := sourceFullPrimeEmbedding F
  calc
    _ ↔ P.asIdeal ∈ (e.embDomain emb).support := by
      rw [Finsupp.support_embDomain, Finset.mem_map]
      constructor
      · intro h
        exact ⟨P, h, rfl⟩
      · rintro ⟨Q, hQ, hEq⟩
        have h := emb.injective (show emb Q = emb P from hEq)
        exact h ▸ hQ
    _ ↔ _ := by
      rw [sourceFullIdealExponents_embDomain, support_factorization, Multiset.mem_toFinset,
        Ideal.mem_normalizedFactors_iff hM, Ideal.dvd_iff_le]
      exact ⟨And.right, fun h => ⟨P.isPrime, h⟩⟩

theorem sourcePrime_coprime_iff_not_dvd (P : ProbePrime F) (M : Ideal (𝓞 F)) :
    IsCoprime P.asIdeal M ↔ ¬ P.asIdeal ∣ M := by
  rw [Ideal.dvd_iff_le]
  constructor
  · intro h hle
    have H := Ideal.isCoprime_iff_sup_eq.mp h
    rw [sup_eq_left.mpr hle] at H
    exact P.isPrime.ne_top H
  · exact principalAngular_prime_coprime_of_not_le P M

theorem sourceRayPrincipalPrimeValues {M : Ideal (𝓞 F)} (ψ : EvenIdealRayCharacter F M)
    (hM : M ≠ ⊥) (hψ : ¬ ψ.IsNonprincipal) (P : ProbePrime F) :
    ψ.allCoefficient P.asIdeal = if P ∈ sourceRayModulusPrimeSet F M then 0 else 1 := by
  by_cases hP : P ∈ sourceRayModulusPrimeSet F M
  · rw [ite_eq_left hP]
    exact ψ.allCoefficient_eq_zero_of_not_coprime P.asIdeal (fun h =>
      (sourcePrime_coprime_iff_not_dvd F P M).mp h ((sourceRayModulusPrimeSet_mem F hM P).mp hP))
  · have hc := (sourcePrime_coprime_iff_not_dvd F P M).mpr
      (fun hd => hP ((sourceRayModulusPrimeSet_mem F hM P).mpr hd))
    have hOne : ψ.idealHom (integralIdealFractionalUnit P.asIdeal P.ne_bot) = 1 := by
      by_contra hn
      exact hψ ⟨P.asIdeal, P.ne_bot, hc, hn⟩
    rw [ite_eq_right hP, EvenIdealRayCharacter.allCoefficient,
      dite_eq_left P.ne_bot, ite_eq_left hc, hOne, Units.val_one]

theorem sourceRayPrincipal_dirichlet_eq_exteriorZeta {M : Ideal (𝓞 F)}
    (ψ : EvenIdealRayCharacter F M) (hM : M ≠ ⊥) (hψ : ¬ ψ.IsNonprincipal)
    (s : ℂ) (hs : 1 < s.re) :
    ψ.dirichlet s = principalExteriorZeta (sourceRayModulusPrimeSet F M) s := by
  let S := sourceRayModulusPrimeSet F M
  let v (P : ProbePrime F) := 1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)
  let B := ∏ P ∈ S, v P
  have hRay : HasProd (fun P : ProbePrime F => if P ∈ S then 1 else (v P)⁻¹) (ψ.dirichlet s) := by
    apply (sourceFullRayEuler_hasProd F ψ s hs).congr_fun
    intro P
    rw [sourcePrimeEulerRatio, sourceRayPrincipalPrimeValues F ψ hM hψ P]
    change (if P ∈ S then 1 else (v P)⁻¹) =
      (1 - (if P ∈ S then 0 else 1) * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))⁻¹
    split_ifs <;> simp only [zero_mul, sub_zero, inv_one, one_mul, v]
  let f (P : ProbePrime F) := if P ∈ S then (v P)⁻¹ else 1
  have hFin : HasProd f B⁻¹ := by
    have H : HasProd f (∏ P ∈ S, f P) :=
      hasProd_prod_of_ne_finset_one (s := S) (fun _ h => ite_eq_right h)
    have h : (∏ P ∈ S, f P) = B⁻¹ := by
      rw [show B = ∏ P ∈ S, v P from rfl, ← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl (fun _ hP => ite_eq_left hP)
    rw [h] at H
    exact H
  have hZ : HasProd (fun P : ProbePrime F => (v P)⁻¹) (ψ.dirichlet s * B⁻¹) := by
    apply (hRay.mul hFin).congr_fun
    intro P
    dsimp only [f]
    split_ifs <;> simp only [one_mul, mul_one]
  have hDedekind := sourceFullDedekindEuler_hasProd F s hs
  simp only [sourcePrimeEulerRatio, one_mul] at hDedekind
  have h := hZ.unique hDedekind
  have hB : B ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun P _ => by
    apply sourceOneSub_ne_zero_of_norm_lt_one
    have hV := sourcePrimeEulerRatio_norm_le_half F P 1 s (by simp) hs.le
    simpa only [sourcePrimeEulerRatio, one_mul] using hV.trans_lt (by norm_num : (1 / 2 : ℝ) < 1))
  unfold principalExteriorZeta principalZetaEulerFactor
  rw [mixedDedekindZeta_eq F hs, ← h]
  change _ = ψ.dirichlet s * B⁻¹ * B
  rw [mul_assoc, inv_mul_cancel₀ hB, mul_one]

end
end ArtinMatthews.SourceEulerAssembly
