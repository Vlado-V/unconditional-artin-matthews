module

public import ArtinMatthews.VaryingKummerAnalyticHeckeFiniteEulerBounds
public import ArtinMatthews.VaryingKummerAnalyticRayIdealEuler
public import ArtinMatthews.VaryingKummerAnalyticRayIdealPrimitiveContinuation
public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusConvolution
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
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The literal old-ideal Euler deletion is exactly the Dirichlet series
whose coefficients vanish at ideals not coprime to the old modulus. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex UniqueFactorizationMonoid
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
namespace HeckeIdealMobius
variable (K : Type*) [Field K] [NumberField K]

theorem prime_product_eq_moebius_sum (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (a : Ideal (𝓞 K) →*₀ ℂ) :
    (∏ P ∈ primeSupport K M, (1-a P)) = ∑ J ∈ divisors K M, (moebius J : ℂ)*a J := by
  have hf : (∑ J ∈ divisors K M, (moebius J : ℂ)*a J) =
      ∑ J ∈ (divisors K M).filter Squarefree, (moebius J : ℂ)*a J := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro J hJ hn
    have hns : ¬ Squarefree J := by simpa [hJ] using hn
    rw [moebius_of_not_squarefree hns,Int.cast_zero,zero_mul]
  rw [hf,squarefree_divisors_eq_image K M hM,Finset.sum_image]
  · have H := Finset.prod_one_add (f := fun P : Ideal (𝓞 K) => -a P) (primeSupport K M)
    rw [show (∏ P ∈ primeSupport K M, (1-a P)) =
      ∏ P ∈ primeSupport K M, (1+ -a P) by simp only [sub_eq_add_neg],H]
    apply Finset.sum_congr rfl
    intro S hS
    rw [moebius_support_product K (Finset.mem_powerset.mp hS),map_prod,Finset.prod_neg]
  · intro S hS T hT hST
    exact support_product_injective K (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT) hST

theorem common_divisor_moebius_sum (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    (∑ J ∈ (divisors K I).filter (fun J => J ∣ M), (moebius J : ℂ)) =
      if IsCoprime I M then 1 else 0 := by
  have hg : gcd I M ≠ ⊥ := gcd_ne_zero_of_left hI
  have he : (divisors K I).filter (fun J => J ∣ M) = divisors K (gcd I M) := by
    ext J
    simp only [Finset.mem_filter,mem_divisors K hI,mem_divisors K hg,dvd_gcd_iff]
  rw [he,sum_moebius_divisors K (gcd I M) hg]
  simp only [← Ideal.isCoprime_iff_gcd]

theorem coprime_mask_hasSum (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (a : Ideal (𝓞 K) →*₀ ℂ) (ha : Summable a) :
    HasSum (fun I : Ideal (𝓞 K) => if IsCoprime I M then a I else 0)
      ((∏ P ∈ primeSupport K M, (1-a P)) * ∑' I : Ideal (𝓞 K), a I) := by
  let b : Ideal (𝓞 K) → ℂ := fun J => if J ∈ divisors K M then (moebius J : ℂ)*a J else 0
  have hb : Summable b := summable_of_ne_finset_zero (s := divisors K M) (fun J hJ => by simp [b,hJ])
  have hbs : (∑' J, b J) = ∏ P ∈ primeSupport K M, (1-a P) := by
    rw [tsum_eq_sum (s := divisors K M) (fun J hJ => by simp [b,hJ])]
    rw [prime_product_eq_moebius_sum K M hM a]
    exact Finset.sum_congr rfl (fun J hJ => by simp [b,hJ])
  have hp := summable_mul_of_summable_norm hb.norm ha.norm
  have hfiber (I : Ideal (𝓞 K)) :
      (∑' p : MulFiber K I, b p.val.1*a p.val.2) = if IsCoprime I M then a I else 0 := by
    have he (p : MulFiber K I) : b p.val.1*a p.val.2 =
        (if p.val.1 ∣ M then (moebius p.val.1 : ℂ) else 0)*a I := by
      dsimp only [b]
      simp only [mem_divisors K hM]
      split_ifs
      · rw [mul_assoc,← map_mul,p.property]
      · simp
    simp_rw [he]
    by_cases hI : I=0
    · subst I
      simp only [map_zero,mul_zero,tsum_zero,ite_self]
    · rw [tsum_mul_right]
      have hpart : (∑' p : MulFiber K I, if p.val.1 ∣ M then (moebius p.val.1 : ℂ) else 0) =
          ∑ J ∈ (divisors K I).filter (fun J => J ∣ M), (moebius J : ℂ) := by
        have H := (mulFiberDivisorEquiv K I hI).tsum_eq
          (fun J => if J.val ∣ M then (moebius J.val : ℂ) else 0)
        change (∑' p : MulFiber K I, if p.val.1 ∣ M then (moebius p.val.1 : ℂ) else 0) =
          ∑' J : {J : Ideal (𝓞 K) // J ∈ divisors K I},
            if J.val ∣ M then (moebius J.val : ℂ) else 0 at H
        rw [H,tsum_fintype]
        rw [← Finset.sum_subtype (divisors K I) (fun J => Iff.rfl)
          (fun J => if J ∣ M then (moebius J : ℂ) else 0)]
        exact (Finset.sum_filter (s := divisors K I) (fun J => J ∣ M) (fun J => (moebius J : ℂ))).symm
      rw [hpart,common_divisor_moebius_sum K I M hI]
      split_ifs <;> simp
  have hg := hp.hasSum.tsum_fiberwise (fun p : Ideal (𝓞 K) × Ideal (𝓞 K) => p.1*p.2)
  change HasSum (fun I : Ideal (𝓞 K) => ∑' p : MulFiber K I, b p.val.1*a p.val.2)
    (∑' p : Ideal (𝓞 K) × Ideal (𝓞 K), b p.1*a p.2) at hg
  simp_rw [hfiber] at hg
  rw [← tsum_mul_tsum_of_summable_norm hb.norm ha.norm,hbs] at hg
  exact hg

end HeckeIdealMobius

namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {f : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K f)

theorem idealEulerDeletion_eq_moebius (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    {s : ℂ} (hs : 1 < s.re) :
    ψ.idealEulerDeletion M s =
      ∑ J ∈ HeckeIdealMobius.divisors K M, (moebius J : ℂ)*ψ.idealTerm hs J := by
  have H := HeckeIdealMobius.prime_product_eq_moebius_sum K M hM (ψ.idealTerm hs)
  simpa only [idealEulerDeletion,ψ.idealTerm_apply hs] using H

theorem idealCoprimeDirichlet_hasSum (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : Ideal (𝓞 K) => if IsCoprime I M then
      ψ.allCoefficient I*(Ideal.absNorm I : ℂ)^(-s) else 0)
      (ψ.idealEulerDeletion M s*ψ.dirichlet s) := by
  have H := HeckeIdealMobius.coprime_mask_hasSum K M hM (ψ.idealTerm hs) (ψ.idealTerm_summable hs)
  have he : (∏ P ∈ HeckeIdealMobius.primeSupport K M, (1-ψ.idealTerm hs P)) =
      ψ.idealEulerDeletion M s := by simp only [idealEulerDeletion,ψ.idealTerm_apply hs]
  rw [he,← ψ.dirichlet_eq_ideal_tsum hs] at H
  simpa only [ψ.idealTerm_apply hs] using H

theorem idealCoprimeDirichlet_primitive_hasSum (hf : f ≠ ⊥)
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
    (hnp : ψ.IsNonprincipal) (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : Ideal (𝓞 K) => if IsCoprime I M then
      ψ.allCoefficient I*(Ideal.absNorm I : ℂ)^(-s) else 0)
      (ψ.primitiveContinued hf hprim s*ψ.idealEulerDeletion M s) := by
  rw [ψ.primitiveContinued_eq_dirichlet hf hprim hnp hs,mul_comm]
  exact ψ.idealCoprimeDirichlet_hasSum M hM hs

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
