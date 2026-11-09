module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealEulerCorrection
public import ArtinMatthews.VaryingKummerAnalyticRayPrimitiveNonprincipal


set_option backward.privateInPublic true
@[expose] public section

/-! The original rational-modulus series is exactly its primitive
ideal-conductor series times the finite old-prime deletion factors. -/
namespace ArtinMatthews.VaryingKummerAnalytic
noncomputable section
open NumberField RayClass IsDedekindDomain FractionalIdeal Set Module Filter Topology
open OAI.PrimeDegreePackets
open scoped BigOperators NumberField nonZeroDivisors Classical
namespace EvenRayCharacter
variable {K : Type*} [Field K] [NumberField K] {N : ℕ} [NeZero N]
variable (ψ : EvenRayCharacter K N) (f : Ideal (𝓞 K))
variable (hMf : rationalModulusIdeal (𝓞 K) N ≤ f) (Ψ : EvenIdealRayCharacter K f)
variable (hagree : ∀ I : primeToModulusIdeals (rationalIdealRayModulus K N),
  Ψ.idealHom (I:FractionalIdealGroup K) = ψ.idealHom (I:FractionalIdealGroup K))
include hMf hagree

theorem allCoefficient_eq_primitive_of_coprime (I : Ideal (𝓞 K))
    (hI : I ≠ ⊥) (hcop : IsCoprime I (rationalModulusIdeal (𝓞 K) N)) :
    ψ.allCoefficient I = Ψ.allCoefficient I := by
  have hcopf : IsCoprime I f :=
    hcop.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hMf)
  have H := hagree (integralIdealPrimeToIdeal (rationalModulusIdeal (𝓞 K) N)
    (rationalModulusIdeal_ne_bot N) I hI hcop)
  change Ψ.idealHom (integralIdealFractionalUnit I hI) =
    ψ.idealHom (integralIdealFractionalUnit I hI) at H
  simp only [allCoefficient,EvenIdealRayCharacter.allCoefficient,
    dite_eq_left hI,ite_eq_left hcop,ite_eq_left hcopf]
  exact congrArg Units.val H.symm

theorem local_euler_eq_primitive_correction (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    (∏ P : idealsOverPrime K (p:ℕ), (1 - ψ.idealTerm hs P.val)⁻¹) =
      (Ψ.primeEulerCorrection p s)⁻¹ *
        (if p ∈ badPrimes N then Ψ.primeEulerCorrection p s else 1) := by
  by_cases hb : p ∈ badPrimes N
  · rw [ite_eq_left hb, inv_mul_cancel₀ (Ψ.primeEulerCorrection_ne_zero p (by linarith))]
    apply Finset.prod_eq_one
    intro P _
    apply ψ.local_factor_eq_one_of_not_coprime hs
    rw [coprime_idealOverPrime_iff p.property P]
    exact not_not.mpr ((mem_badPrimes p).mp hb)
  · rw [ite_eq_right hb,mul_one,← Ψ.primeEulerCorrection_inv p hs]
    apply Finset.prod_congr rfl
    intro P _
    have hc : IsCoprime P.val (rationalModulusIdeal (𝓞 K) N) := by
      rw [coprime_idealOverPrime_iff p.property P]
      exact (mem_badPrimes p).not.mp hb
    have hp0 : P.val ≠ ⊥ := (idealsOverPrime_prime K P.property).ne_zero
    rw [idealTerm_apply,EvenIdealRayCharacter.idealTerm_apply,
      ψ.allCoefficient_eq_primitive_of_coprime f hMf Ψ hagree P.val hp0 hc]

theorem dirichlet_eq_primitive_correction {s : ℂ} (hs : 1 < s.re) :
    ψ.dirichlet s = Ψ.dirichlet s * Ψ.rationalBadEulerCorrection N s := by
  have HF := Ψ.dirichlet_hasProd hs
  simp_rw [Ψ.primeEulerCorrection_inv _ hs] at HF
  have HB : HasProd (fun p : Nat.Primes =>
      if p ∈ badPrimes N then Ψ.primeEulerCorrection p s else 1)
      (Ψ.rationalBadEulerCorrection N s) := by
    have HT := hasProd_prod_of_ne_finset_one (s := badPrimes N)
      (f := fun p : Nat.Primes => if p ∈ badPrimes N then Ψ.primeEulerCorrection p s else 1)
      (L := SummationFilter.unconditional _) (fun p hp => ite_eq_right hp)
    simpa only [EvenIdealRayCharacter.rationalBadEulerCorrection,Finset.prod_ite_mem,
      Finset.inter_self] using HT
  have H := HF.mul HB
  have HR := ψ.dirichlet_hasProd hs
  simp_rw [ψ.local_euler_eq_primitive_correction f hMf Ψ hagree _ hs] at HR
  exact HR.unique H

end EvenRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
