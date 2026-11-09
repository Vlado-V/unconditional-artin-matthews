module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealLog
public import ArtinMatthews.VaryingKummerAnalyticHeckeFiniteEulerBounds


set_option backward.privateInPublic true
@[expose] public section

/-! Bounds from the actual absolutely convergent ray Euler log and from
its finite old-modulus factors. The right-hand bound is independent of
the conductor, and the positive-half-plane deletion costs a subpower. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField VaryingKummerAnalytic
open scoped NumberField Classical BigOperators nonZeroDivisors
noncomputable section
variable (F : Type) [Field F] [NumberField F]

def sourceRayAbsoluteEulerBound (a : ℝ) : ℝ :=
  Real.exp (∑' p : Nat.Primes, dedekindEulerLogMajorant F a p)

theorem sourceRayAbsoluteEulerBound_pos (a : ℝ) : 0 < sourceRayAbsoluteEulerBound F a :=
  Real.exp_pos _

theorem sourceRayEulerLog_norm_le {M : Ideal (𝓞 F)} (ψ : EvenIdealRayCharacter F M)
    {a : ℝ} (ha : 1 < a) {s : ℂ} (hs : a ≤ s.re) :
    ‖ψ.eulerLog s‖ ≤ ∑' p : Nat.Primes, dedekindEulerLogMajorant F a p := by
  have hM := dedekindEulerLogMajorant_summable F ha
  have h := hM.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => ψ.eulerLocalLog_norm_le p ha.le hs)
  exact (norm_tsum_le_tsum_norm h).trans
    (h.tsum_le_tsum (fun p => ψ.eulerLocalLog_norm_le p ha.le hs) hM)

theorem sourceRayDirichlet_norm_bounds {M : Ideal (𝓞 F)} (ψ : EvenIdealRayCharacter F M)
    {a : ℝ} (ha : 1 < a) {s : ℂ} (hs : a ≤ s.re) :
    ‖ψ.dirichlet s‖ ≤ sourceRayAbsoluteEulerBound F a ∧
      ‖(ψ.dirichlet s)⁻¹‖ ≤ sourceRayAbsoluteEulerBound F a := by
  have h := sourceRayEulerLog_norm_le F ψ ha hs
  rw [← ψ.exp_eulerLog_eq_dirichlet (ha.trans_le hs), ← Complex.exp_neg]
  simp only [sourceRayAbsoluteEulerBound, Complex.norm_exp]
  refine ⟨Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans h), ?_⟩
  exact Real.exp_le_exp.mpr ((Complex.re_le_norm (-ψ.eulerLog s)).trans (by simpa using h))

theorem sourceIdealEulerDeletion_norm_le_two_pow {f : Ideal (𝓞 F)} (ψ : EvenIdealRayCharacter F f)
    (M : Ideal (𝓞 F)) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖ψ.idealEulerDeletion M s‖ ≤ (2 : ℝ)^(HeckeIdealMobius.primeSupport F M).card := by
  rw [EvenIdealRayCharacter.idealEulerDeletion, norm_prod]
  calc
    _ ≤ ∏ _P ∈ HeckeIdealMobius.primeSupport F M, (2 : ℝ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro P hP
      have hN : 1 ≤ (Ideal.absNorm P : ℝ) := by
        have h := ideal_prime_support_norm_ge_two F hP
        exact_mod_cast (show 1 ≤ Ideal.absNorm P by omega)
      have hpow : ‖(Ideal.absNorm P : ℂ)^(-s)‖ ≤ 1 := by
        rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), Complex.neg_re]
        exact Real.rpow_le_one_of_one_le_of_nonpos hN (neg_nonpos.mpr hs)
      have hm : ‖ψ.allCoefficient P*(Ideal.absNorm P : ℂ)^(-s)‖ ≤ 1 := by
        rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (ψ.allCoefficient_norm_le_one P)).trans hpow
      exact (norm_sub_le (1 : ℂ) _).trans (by rw [norm_one]; linarith)
    _ = _ := by simp

theorem exists_sourceIdealEulerDeletion_norm_le_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {f : Ideal (𝓞 F)} (ψ : EvenIdealRayCharacter F f)
      (M : Ideal (𝓞 F)), M ≠ ⊥ → ∀ s : ℂ, 0 ≤ s.re →
        ‖ψ.idealEulerDeletion M s‖ ≤ C*(Ideal.absNorm M : ℝ)^ε := by
  obtain ⟨C, hC, hbound⟩ := HeckeIdealMobius.prime_support_subsets_bound F ε hε
  exact ⟨C, hC, fun ψ M hM _ hs => (sourceIdealEulerDeletion_norm_le_two_pow F ψ M hs).trans (hbound M hM)⟩

end
end ArtinMatthews.SourceEulerAssembly
