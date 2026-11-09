module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealEuler
public import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius
public import Mathlib.Algebra.BigOperators.Ring.Finset


set_option backward.privateInPublic true
@[expose] public section

/-! Actual ideal Möbius coefficients for an arbitrary number field.
The divisor and prime-support arguments are the algebraic part of the
pinned ideal Möbius proof, with no principal-ideal or fixed-field assumption. -/
namespace ArtinMatthews.VaryingKummerAnalytic.HeckeIdealMobius
open NumberField UniqueFactorizationMonoid Filter
open scoped NumberField nonZeroDivisors Classical BigOperators Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def divisors (I : Ideal (𝓞 K)) : Finset (Ideal (𝓞 K)) :=
  (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) (Ideal.absNorm I)).toFinset.filter (fun J => J ∣ I)

theorem mem_divisors {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    J ∈ divisors K I ↔ J ∣ I := by
  simp only [divisors,Finset.mem_filter,Set.Finite.mem_toFinset,Set.mem_ofPred_eq]
  constructor
  · exact And.right
  · intro hJI
    have hn : 0 < Ideal.absNorm I := Nat.pos_iff_ne_zero.mpr
      (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
    exact ⟨Nat.le_of_dvd hn (map_dvd Ideal.absNorm hJI),hJI⟩

def primeSupport (I : Ideal (𝓞 K)) : Finset (Ideal (𝓞 K)) := (normalizedFactors I).toFinset

theorem support_prime {I P : Ideal (𝓞 K)} (hP : P ∈ primeSupport K I) : Prime P :=
  prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)

theorem support_product_ne_zero {I : Ideal (𝓞 K)} {S : Finset (Ideal (𝓞 K))}
    (hS : S ⊆ primeSupport K I) : (∏ P ∈ S, P) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun _ hP => (support_prime K (hS hP)).ne_zero)

theorem factors_support_product {I : Ideal (𝓞 K)} {S : Finset (Ideal (𝓞 K))}
    (hS : S ⊆ primeSupport K I) : normalizedFactors (∏ P ∈ S, P) = S.val := by
  have hp : ∀ P ∈ S.val, Prime P := fun _ hP => support_prime K (hS hP)
  simpa using normalizedFactors_prod_of_prime hp

theorem squarefree_support_product {I : Ideal (𝓞 K)} {S : Finset (Ideal (𝓞 K))}
    (hS : S ⊆ primeSupport K I) : Squarefree (∏ P ∈ S, P) := by
  apply (squarefree_iff_nodup_normalizedFactors (support_product_ne_zero K hS)).mpr
  rw [factors_support_product K hS]
  exact S.nodup

theorem support_product_dvd {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    {S : Finset (Ideal (𝓞 K))} (hS : S ⊆ primeSupport K I) : (∏ P ∈ S, P) ∣ I := by
  apply (dvd_iff_normalizedFactors_le_normalizedFactors (support_product_ne_zero K hS) hI).mpr
  rw [factors_support_product K hS]
  apply (Multiset.le_iff_subset S.nodup).mpr
  intro P hP
  exact Multiset.mem_toFinset.mp (hS hP)

theorem moebius_support_product {I : Ideal (𝓞 K)} {S : Finset (Ideal (𝓞 K))}
    (hS : S ⊆ primeSupport K I) : (moebius (∏ P ∈ S, P) : ℂ) = (-1 : ℂ)^S.card := by
  rw [(squarefree_support_product K hS).moebius_eq,factors_eq_normalizedFactors,
    factors_support_product K hS]
  simp

theorem support_product_injective {I : Ideal (𝓞 K)} {S T : Finset (Ideal (𝓞 K))}
    (hS : S ⊆ primeSupport K I) (hT : T ⊆ primeSupport K I)
    (h : (∏ P ∈ S, P) = ∏ P ∈ T, P) : S = T := by
  have hf := congrArg normalizedFactors h
  rw [factors_support_product K hS,factors_support_product K hT] at hf
  exact Finset.val_inj.mp hf

theorem squarefree_divisor_support {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (hJ : Squarefree J) (hJI : J ∣ I) : primeSupport K J ⊆ primeSupport K I := by
  have hf := (dvd_iff_normalizedFactors_le_normalizedFactors hJ.ne_zero hI).mp hJI
  intro P hP
  exact Multiset.mem_toFinset.mpr (Multiset.mem_of_le hf (Multiset.mem_toFinset.mp hP))

theorem squarefree_support_product_self {J : Ideal (𝓞 K)} (hJ : Squarefree J) :
    (∏ P ∈ primeSupport K J, P) = J := by
  have hn : (normalizedFactors J).Nodup := (squarefree_iff_nodup_normalizedFactors hJ.ne_zero).mp hJ
  have hv : (primeSupport K J).val = normalizedFactors J := by
    simpa only [primeSupport,Multiset.toFinset_val] using hn.dedup
  calc
    _ = (primeSupport K J).val.prod := (Finset.prod_val _).symm
    _ = (normalizedFactors J).prod := by rw [hv]
    _ = J := Ideal.prod_normalizedFactors_eq_self hJ.ne_zero

theorem squarefree_divisors_eq_image (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    (divisors K I).filter Squarefree =
      (primeSupport K I).powerset.image (fun S => ∏ P ∈ S, P) := by
  ext J
  simp only [Finset.mem_filter,mem_divisors K hI,Finset.mem_image,Finset.mem_powerset]
  constructor
  · rintro ⟨hJI,hJ⟩
    exact ⟨primeSupport K J,squarefree_divisor_support K hI hJ hJI,
      squarefree_support_product_self K hJ⟩
  · rintro ⟨S,hS,rfl⟩
    exact ⟨support_product_dvd K hI hS,squarefree_support_product K hS⟩

theorem primeSupport_empty_iff (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    primeSupport K I = ∅ ↔ I = 1 := by
  constructor
  · intro h
    have hz : normalizedFactors I = 0 := Multiset.toFinset_eq_empty.mp h
    have hp := Ideal.prod_normalizedFactors_eq_self hI
    rw [hz,Multiset.prod_zero] at hp
    exact hp.symm
  · rintro rfl
    change (normalizedFactors (1 : Ideal (𝓞 K))).toFinset = ∅
    rw [normalizedFactors_one]
    rfl

omit [NumberField K] in
theorem sum_subset_sign (S : Finset (Ideal (𝓞 K))) :
    (∑ T ∈ S.powerset, (-1 : ℂ)^T.card) = if S = ∅ then 1 else 0 := by
  have H := Finset.prod_one_add (f := fun _ : Ideal (𝓞 K) => (-1 : ℂ)) S
  simp only [Finset.prod_const] at H
  rw [← H]
  by_cases hS : S = ∅
  · simp [hS]
  · simp [hS,Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hS)]

theorem sum_moebius_divisors (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    (∑ J ∈ divisors K I, (moebius J : ℂ)) = if I = 1 then 1 else 0 := by
  have hf : (∑ J ∈ divisors K I, (moebius J : ℂ)) =
      ∑ J ∈ (divisors K I).filter Squarefree, (moebius J : ℂ) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro J hJ hn
    have hns : ¬ Squarefree J := by simpa [hJ] using hn
    rw [moebius_of_not_squarefree hns,Int.cast_zero]
  rw [hf,squarefree_divisors_eq_image K I hI,Finset.sum_image]
  · have he : (∑ S ∈ (primeSupport K I).powerset, (moebius (∏ P ∈ S, P) : ℂ)) =
        ∑ S ∈ (primeSupport K I).powerset, (-1 : ℂ)^S.card :=
      Finset.sum_congr rfl (fun S hS => moebius_support_product K (Finset.mem_powerset.mp hS))
    rw [he,sum_subset_sign K]
    simp only [primeSupport_empty_iff K I hI]
  · intro S hS T hT hST
    exact support_product_injective K (Finset.mem_powerset.mp hS)
      (Finset.mem_powerset.mp hT) hST

theorem norm_moebius_le_one (I : Ideal (𝓞 K)) : ‖(moebius I : ℂ)‖ ≤ 1 := by
  by_cases hI : Squarefree I
  · simp [hI.moebius_eq]
  · simp [moebius_of_not_squarefree hI]

def truncated (D : ℝ) (I : Ideal (𝓞 K)) : ℂ :=
  if I = 0 then 0 else ∑ J ∈ (divisors K I).filter (fun J => (Ideal.absNorm J : ℝ) ≤ D),
    (moebius J : ℂ)

theorem truncated_zero (D : ℝ) : truncated K D 0 = 0 := by simp [truncated]

theorem truncated_eq_unit_of_norm_le {D : ℝ} (I : Ideal (𝓞 K))
    (hI : (Ideal.absNorm I : ℝ) ≤ D) :
    truncated K D I = if I = 1 then 1 else 0 := by
  by_cases hI0 : I = 0
  · simp [truncated,hI0]
  rw [truncated,ite_eq_right hI0]
  have he : (divisors K I).filter (fun J => (Ideal.absNorm J : ℝ) ≤ D) = divisors K I := by
    apply Finset.filter_eq_self.mpr
    intro J hJ
    have hdiv := (mem_divisors K hI0).mp hJ
    have hp : 0 < Ideal.absNorm I := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI0)
    exact (show (Ideal.absNorm J : ℝ) ≤ Ideal.absNorm I from by
      exact_mod_cast Nat.le_of_dvd hp (map_dvd Ideal.absNorm hdiv)).trans hI
  rw [he,sum_moebius_divisors K I hI0]

theorem truncated_one {D : ℝ} (hD : 1 ≤ D) : truncated K D 1 = 1 := by
  simpa using truncated_eq_unit_of_norm_le K (1 : Ideal (𝓞 K)) (by simpa using hD)

theorem truncated_vanishes {D : ℝ} {I : Ideal (𝓞 K)}
    (hI : I ≠ 1) (hID : (Ideal.absNorm I : ℝ) ≤ D) : truncated K D I = 0 := by
  rw [truncated_eq_unit_of_norm_le K I hID,ite_eq_right hI]

end
end ArtinMatthews.VaryingKummerAnalytic.HeckeIdealMobius
