module

public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusConvolution
public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusMass


set_option backward.privateInPublic true
@[expose] public section

/-! Entirety and a concrete conductor-independent norm bound for the actual
finite Möbius inverse on Re(s)>=1/2. The loss D^(1/2+epsilon) is obtained from
the positive ideal norm series, with no bound on the truncation supplied. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M)

theorem mobiusTruncation_entire (D : ℝ) : Differentiable ℂ (ψ.mobiusTruncation D) := by
  unfold mobiusTruncation
  apply Differentiable.fun_sum
  intro I _
  by_cases hI : I=0
  · subst I
    simp only [allCoefficient_zero,mul_zero,zero_mul]
    exact differentiable_const _
  · apply Differentiable.const_mul
    exact (differentiable_id.neg).const_cpow (Or.inl (by
      exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hI))

end EvenIdealRayCharacter

theorem exists_mobiusTruncation_norm_bound (K : Type*) [Field K] [NumberField K]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {M : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K M)
      (D : ℝ), 1 ≤ D → ∀ s : ℂ, (1/2 : ℝ) ≤ s.re →
      ‖ψ.mobiusTruncation D s‖ ≤ C*D^(1/2+ε) := by
  let F : Ideal (𝓞 K) → ℝ := fun I => if I=0 then 0 else (Ideal.absNorm I : ℝ)^(-(1+ε))
  have hF : Summable F := by
    have hsub : Summable (fun I : {I : Ideal (𝓞 K) // I ≠ 0} => F I.val) := by
      apply (HeckeIdealMobius.normSeries_summable K hε).congr
      intro I
      have hn : I.val ≠ 0 := I.property
      simp only [F,ite_eq_right hn]
    exact (hasSum_subtype_iff_of_support_subset (s := {I : Ideal (𝓞 K) | I ≠ 0})
      (f := F) (by
        intro I hI hi
        subst I
        exact hI (by simp [F]))).mp hsub.hasSum |>.summable
  have hsum : (∑' I : Ideal (𝓞 K), F I) = HeckeIdealMobius.normSeries K ε := by
    have H := tsum_subtype_eq_of_support_subset (s := {I : Ideal (𝓞 K) | I ≠ 0})
      (f := F) (by
        intro I hI hi
        subst I
        exact hI (by simp [F]))
    apply H.symm.trans
    apply tsum_congr
    intro I
    have hn : I.val ≠ 0 := I.property
    simp only [F,ite_eq_right hn]
  refine ⟨HeckeIdealMobius.normSeries K ε+1,by linarith [HeckeIdealMobius.normSeries_nonneg K ε],?_⟩
  intro M ψ D hD s hs
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hterm (I : Ideal (𝓞 K)) (hI : I ∈ HeckeIdealMobius.normCutoff K D) :
      ‖(UniqueFactorizationMonoid.moebius I : ℂ)*ψ.allCoefficient I*(Ideal.absNorm I : ℂ)^(-s)‖ ≤
        D^(1/2+ε)*F I := by
    by_cases hI0 : I=0
    · subst I
      simp [F]
    · have hN : 0 < (Ideal.absNorm I : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI0)
      have hN1 : 1 ≤ (Ideal.absNorm I : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI0)
      have hND := (HeckeIdealMobius.mem_normCutoff K hD0.le I).mp hI
      rw [norm_mul,norm_mul,← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos hN,neg_re]
      dsimp only [F]
      rw [ite_eq_right hI0]
      calc
        _ ≤ (Ideal.absNorm I : ℝ)^(-s.re) := by
          have hcoeff := mul_le_mul (HeckeIdealMobius.norm_moebius_le_one K I)
            (ψ.allCoefficient_norm_le_one I) (norm_nonneg _) zero_le_one
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hN.le (-s.re))
        _ ≤ (Ideal.absNorm I : ℝ)^(-(1/2)) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
        _ = (Ideal.absNorm I : ℝ)^(1/2+ε)*(Ideal.absNorm I : ℝ)^(-(1+ε)) := by
          rw [← Real.rpow_add hN]
          congr 1
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hN.le hND (by linarith : (0 : ℝ) ≤ 1/2+ε)) (Real.rpow_nonneg hN.le _)
  unfold EvenIdealRayCharacter.mobiusTruncation
  calc
    _ ≤ ∑ I ∈ HeckeIdealMobius.normCutoff K D,
        ‖(UniqueFactorizationMonoid.moebius I : ℂ)*ψ.allCoefficient I*(Ideal.absNorm I : ℂ)^(-s)‖ := norm_sum_le _ _
    _ ≤ ∑ I ∈ HeckeIdealMobius.normCutoff K D, D^(1/2+ε)*F I := Finset.sum_le_sum hterm
    _ = D^(1/2+ε)*∑ I ∈ HeckeIdealMobius.normCutoff K D, F I := by rw [Finset.mul_sum]
    _ ≤ D^(1/2+ε)*HeckeIdealMobius.normSeries K ε := by
      rw [← hsum]
      exact mul_le_mul_of_nonneg_left (hF.sum_le_tsum _ (fun I _ => by dsimp [F]; split_ifs <;> positivity))
        (Real.rpow_nonneg hD0.le _)
    _ ≤ _ := by nlinarith [Real.rpow_nonneg hD0.le (1/2+ε)]

end
end ArtinMatthews.VaryingKummerAnalytic
