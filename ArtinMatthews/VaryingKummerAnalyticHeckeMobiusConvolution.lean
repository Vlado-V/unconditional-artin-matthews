module

public import ArtinMatthews.VaryingKummerAnalyticHeckeIdealMobius
public import ArtinMatthews.VaryingKummerAnalyticRayIdealPrimitiveContinuation


set_option backward.privateInPublic true
@[expose] public section

/-! Exact actual-ideal convolution of the finite Möbius inverse with a
multiplicative summable series, then with the genuine primitive Hecke L
series. The unit coefficient and the support of the remaining tail are
proved from the actual ideal Möbius identity. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField UniqueFactorizationMonoid
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
namespace HeckeIdealMobius
variable (K : Type*) [Field K] [NumberField K]

def normCutoff (D : ℝ) : Finset (Ideal (𝓞 K)) :=
  (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) (Nat.floor D)).toFinset

theorem mem_normCutoff {D : ℝ} (hD : 0 ≤ D) (I : Ideal (𝓞 K)) :
    I ∈ normCutoff K D ↔ (Ideal.absNorm I : ℝ) ≤ D := by
  simp only [normCutoff,Set.Finite.mem_toFinset,Set.mem_ofPred_eq]
  exact Nat.le_floor_iff hD

abbrev MulFiber (I : Ideal (𝓞 K)) := {p : Ideal (𝓞 K) × Ideal (𝓞 K) // p.1*p.2=I}

def mulFiberDivisorEquiv (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    MulFiber K I ≃ {J : Ideal (𝓞 K) // J ∈ divisors K I} := by
  let f : MulFiber K I → {J : Ideal (𝓞 K) // J ∈ divisors K I} :=
    fun p => ⟨p.val.1,(mem_divisors K hI).mpr ⟨p.val.2,p.property.symm⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q hpq
    have hfst : p.val.1=q.val.1 := congrArg Subtype.val hpq
    apply Subtype.ext
    apply Prod.ext hfst
    have hn : p.val.1 ≠ 0 := by
      intro hz
      have he := p.property
      rw [hz,zero_mul] at he
      exact hI he.symm
    apply mul_left_cancel₀ hn
    rw [p.property,hfst,q.property]
  · intro J
    obtain ⟨L,hL⟩ := (mem_divisors K hI).mp J.property
    exact ⟨⟨(J.val,L),hL.symm⟩,rfl⟩

theorem truncated_eq_mulFiber_sum (D : ℝ) (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    truncated K D I = ∑' p : MulFiber K I,
      (if (Ideal.absNorm p.val.1 : ℝ) ≤ D then (moebius p.val.1 : ℂ) else 0) := by
  rw [truncated,ite_eq_right hI]
  have he := (mulFiberDivisorEquiv K I hI).tsum_eq
    (fun J => if (Ideal.absNorm J.val : ℝ) ≤ D then (moebius J.val : ℂ) else 0)
  change (∑' p : MulFiber K I,
    if (Ideal.absNorm p.val.1 : ℝ) ≤ D then (moebius p.val.1 : ℂ) else 0) =
    (∑' J : {J : Ideal (𝓞 K) // J ∈ divisors K I},
      if (Ideal.absNorm J.val : ℝ) ≤ D then (moebius J.val : ℂ) else 0) at he
  rw [he]
  rw [tsum_fintype]
  rw [← Finset.sum_subtype (divisors K I) (fun J => Iff.rfl)
    (fun J => if (Ideal.absNorm J : ℝ) ≤ D then (moebius J : ℂ) else 0)]
  exact (Finset.sum_filter (s := divisors K I)
    (fun J : Ideal (𝓞 K) => (Ideal.absNorm J : ℝ) ≤ D)
    (fun J => (moebius J : ℂ)))

def finiteInverse (D : ℝ) (a : Ideal (𝓞 K) →*₀ ℂ) : ℂ :=
  ∑ I ∈ normCutoff K D, (moebius I : ℂ)*a I

theorem convolution_hasSum {D : ℝ} (hD : 0 ≤ D)
    (a : Ideal (𝓞 K) →*₀ ℂ) (ha : Summable a) :
    HasSum (fun I : Ideal (𝓞 K) => truncated K D I*a I)
      (finiteInverse K D a * ∑' I : Ideal (𝓞 K), a I) := by
  let b : Ideal (𝓞 K) → ℂ := fun I =>
    if I ∈ normCutoff K D then (moebius I : ℂ)*a I else 0
  have hb : Summable b := summable_of_ne_finset_zero
    (s := normCutoff K D) (fun I hI => by simp [b,hI])
  have hbs : (∑' I, b I) = finiteInverse K D a := by
    rw [tsum_eq_sum (s := normCutoff K D) (fun I hI => by simp [b,hI])]
    unfold finiteInverse
    exact Finset.sum_congr rfl (fun I hI => by simp [b,hI])
  have hp := summable_mul_of_summable_norm hb.norm ha.norm
  have hfiber (I : Ideal (𝓞 K)) :
      (∑' p : MulFiber K I, b p.val.1*a p.val.2) = truncated K D I*a I := by
    have he (p : MulFiber K I) : b p.val.1*a p.val.2 =
        (if (Ideal.absNorm p.val.1 : ℝ) ≤ D then (moebius p.val.1 : ℂ) else 0)*a I := by
      dsimp [b]
      simp only [mem_normCutoff K hD]
      split_ifs
      · rw [mul_assoc,← map_mul,p.property]
      · simp
    simp_rw [he]
    by_cases hI : I = 0
    · subst I
      simp only [map_zero,mul_zero,tsum_zero]
    · rw [tsum_mul_right,← truncated_eq_mulFiber_sum K D I hI]
  have hg := hp.hasSum.tsum_fiberwise (fun p : Ideal (𝓞 K) × Ideal (𝓞 K) => p.1*p.2)
  change HasSum (fun I : Ideal (𝓞 K) => ∑' p : MulFiber K I, b p.val.1*a p.val.2)
    (∑' p : Ideal (𝓞 K) × Ideal (𝓞 K), b p.1*a p.2) at hg
  simp_rw [hfiber] at hg
  rw [← tsum_mul_tsum_of_summable_norm hb.norm ha.norm,hbs] at hg
  exact hg

theorem convolution_unit_tail {D : ℝ} (hD : 1 ≤ D)
    (a : Ideal (𝓞 K) →*₀ ℂ) (ha : Summable a) :
    finiteInverse K D a * (∑' I : Ideal (𝓞 K), a I) = 1 +
      ∑' I : Ideal (𝓞 K), if D < (Ideal.absNorm I : ℝ) then truncated K D I*a I else 0 := by
  have hconv := convolution_hasSum K (zero_le_one.trans hD) a ha
  have hpoint (I : Ideal (𝓞 K)) :
      (if D < (Ideal.absNorm I : ℝ) then truncated K D I*a I else 0) =
        truncated K D I*a I - if I=1 then 1 else 0 := by
    by_cases hI : I=1
    · subst I
      rw [truncated_one K hD,map_one]
      simp only [map_one,Nat.cast_one,ite_true,mul_one,sub_self]
      exact ite_eq_right (not_lt.mpr hD)
    · by_cases hN : D < (Ideal.absNorm I : ℝ)
      · simp only [hI,hN,ite_true,ite_false,sub_zero]
      · rw [ite_eq_right hN,ite_eq_right hI,truncated_vanishes K hI (le_of_not_gt hN)]
        simp only [zero_mul,sub_zero]
  simp_rw [hpoint]
  rw [hconv.summable.tsum_sub (hasSum_ite_eq (1 : Ideal (𝓞 K)) (1 : ℂ)).summable,
    hconv.tsum_eq,tsum_ite_eq]
  ring

end HeckeIdealMobius

namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M)

def mobiusTruncation (D : ℝ) (s : ℂ) : ℂ :=
  ∑ I ∈ HeckeIdealMobius.normCutoff K D,
    (moebius I : ℂ)*ψ.allCoefficient I*(Ideal.absNorm I : ℂ)^(-s)

theorem mobiusTruncation_eq_finiteInverse (D : ℝ) {s : ℂ} (hs : 1 < s.re) :
    ψ.mobiusTruncation D s = HeckeIdealMobius.finiteInverse K D (ψ.idealTerm hs) := by
  unfold mobiusTruncation HeckeIdealMobius.finiteInverse
  apply Finset.sum_congr rfl
  intro I _
  rw [ψ.idealTerm_apply hs]
  ring

theorem mobiusTruncation_mul_primitive_unit_tail (hM : M ≠ ⊥)
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
    (hnp : ψ.IsNonprincipal) {D : ℝ} (hD : 1 ≤ D) {s : ℂ} (hs : 1 < s.re) :
    ψ.mobiusTruncation D s * ψ.primitiveContinued hM hprim s = 1 +
      ∑' I : Ideal (𝓞 K), if D < (Ideal.absNorm I : ℝ) then
        HeckeIdealMobius.truncated K D I *
          (ψ.allCoefficient I*(Ideal.absNorm I : ℂ)^(-s)) else 0 := by
  rw [ψ.mobiusTruncation_eq_finiteInverse D hs,
    ψ.primitiveContinued_eq_dirichlet hM hprim hnp hs,ψ.dirichlet_eq_ideal_tsum hs]
  exact HeckeIdealMobius.convolution_unit_tail K hD (ψ.idealTerm hs) (ψ.idealTerm_summable hs)

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
