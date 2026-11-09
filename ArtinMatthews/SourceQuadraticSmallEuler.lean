module

public import ArtinMatthews.QuadraticHeckeCoprimeContourRemainder
public import ArtinMatthews.SourceRayAbsoluteBounds


set_option backward.privateInPublic true
@[expose] public section

/-! The complete finite Möbius factor on the positive Small contour. -/
namespace ArtinMatthews
open NumberField Complex MeasureTheory Set VaryingKummerAnalytic UniqueFactorizationMonoid
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]

def quadraticSmallEuler (J : Ideal (𝓞 F)) (s : ℂ) : ℂ :=
  ∏ P ∈ HeckeIdealMobius.primeSupport F J, (1 - (Ideal.absNorm P : ℂ) ^ (-s))

theorem quadraticSmallEuler_eq_moebius (J : Ideal (𝓞 F)) (hJ : J ≠ ⊥)
    (s : ℂ) (hs : s ≠ 0) :
    quadraticSmallEuler F J s = ∑ d ∈ HeckeIdealMobius.divisors F J,
      (moebius d : ℂ) * (Ideal.absNorm d : ℂ) ^ (-s) := by
  let A : Ideal (𝓞 F) →*₀ ℂ := (riemannZetaSummandHom (s := s) hs).comp Ideal.absNorm
  exact HeckeIdealMobius.prime_product_eq_moebius_sum F J hJ A

theorem quadraticSmallEuler_mul {J L : Ideal (𝓞 F)} (hJ : J ≠ ⊥) (hL : L ≠ ⊥)
    (hJL : IsCoprime J L) (s : ℂ) :
    quadraticSmallEuler F (J * L) s = quadraticSmallEuler F J s * quadraticSmallEuler F L s := by
  have hsupp : HeckeIdealMobius.primeSupport F (J * L) =
      HeckeIdealMobius.primeSupport F J ∪ HeckeIdealMobius.primeSupport F L := by
    ext P
    simp only [HeckeIdealMobius.primeSupport, normalizedFactors_mul hJ hL,
      Multiset.mem_toFinset, Finset.mem_union, Multiset.mem_add]
  have hdis : Disjoint (HeckeIdealMobius.primeSupport F J) (HeckeIdealMobius.primeSupport F L) := by
    apply Finset.disjoint_left.mpr
    intro P hp hq
    exact (HeckeIdealMobius.support_prime F hp).not_isUnit
      (hJL.isUnit_of_dvd' (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hp))
        (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hq)))
  unfold quadraticSmallEuler
  rw [hsupp, Finset.prod_union hdis]

theorem quadraticSmallEuler_norm_le (J : Ideal (𝓞 F)) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖quadraticSmallEuler F J s‖ ≤ (2 : ℝ) ^ (HeckeIdealMobius.primeSupport F J).card := by
  rw [quadraticSmallEuler, norm_prod]
  calc
    _ ≤ ∏ _P ∈ HeckeIdealMobius.primeSupport F J, (2 : ℝ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro P hp
      have hN : 1 ≤ (Ideal.absNorm P : ℝ) := by
        have h := ideal_prime_support_norm_ge_two F hp
        exact_mod_cast (show 1 ≤ Ideal.absNorm P by omega)
      have hpow : ‖(Ideal.absNorm P : ℂ) ^ (-s)‖ ≤ 1 := by
        rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos
          (zero_lt_one.trans_le hN), Complex.neg_re]
        exact Real.rpow_le_one_of_one_le_of_nonpos hN (neg_nonpos.mpr hs)
      exact (norm_sub_le (1 : ℂ) _).trans (by rw [norm_one]; linarith)
    _ = _ := by simp

theorem quadraticSmallEuler_subpower (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ J : Ideal (𝓞 F), J ≠ ⊥ → ∀ s : ℂ, 0 ≤ s.re →
      ‖quadraticSmallEuler F J s‖ ≤ C * (Ideal.absNorm J : ℝ) ^ η := by
  obtain ⟨C, hC, hb⟩ := HeckeIdealMobius.prime_support_subsets_bound F η hη
  exact ⟨C, hC, fun J hJ s hs => (quadraticSmallEuler_norm_le F J hs).trans (hb J hJ)⟩

theorem quadraticSmallEuler_continuous (J : Ideal (𝓞 F)) : Continuous (quadraticSmallEuler F J) := by
  unfold quadraticSmallEuler
  apply continuous_finsetProd
  intro P hp
  have hP : (Ideal.absNorm P : ℂ) ≠ 0 := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) (ideal_prime_support_norm_ge_two F hp)).ne'
  apply continuous_const.sub
  simp only [Complex.cpow_def_of_ne_zero hP]
  fun_prop

end
end ArtinMatthews
