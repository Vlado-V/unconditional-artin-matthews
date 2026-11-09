module

public import ArtinMatthews.VaryingKummerAnalyticDedekindSeriesPartialComplex


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine complex ideal series and its finite ideal-class decomposition
for arbitrary number fields, with exact Mathlib Dedekind-zeta identification. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal Set
open OAI.PrimeDegreePackets
open scoped NumberField nonZeroDivisors Classical BigOperators ENNReal
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def classRepresentative (c : ClassGroup (𝓞 K)) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Classical.choose (show ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ClassGroup.mk K I = c from
    ClassGroup.induction K (fun I => ⟨I, rfl⟩) c)

theorem classRepresentative_spec (c : ClassGroup (𝓞 K)) :
    ClassGroup.mk K (classRepresentative K c) = c :=
  Classical.choose_spec
    (show ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ClassGroup.mk K I = c from
      ClassGroup.induction K (fun I => ⟨I, rfl⟩) c)

/-- Exact class partition; the inverse convention matches the actual partial
series and its relative principal-element construction. -/
def idealClassPartitionEquiv :
    (Σ c : ClassGroup (𝓞 K), integralIdealClassFiber (classRepresentative K c)) ≃
      integralFractionalIdeals K where
  toFun x := ⟨x.2.1, x.2.2.1⟩
  invFun J := ⟨(ClassGroup.mk K J.1)⁻¹,
    ⟨J.1, J.2, by rw [classRepresentative_spec, inv_inv]⟩⟩
  left_inv := by
    rintro ⟨c, J⟩
    have h : (ClassGroup.mk K J.1)⁻¹ = c := by
      rw [J.2.2, classRepresentative_spec, inv_inv]
    apply Sigma.ext h
    exact (Subtype.heq_iff_coe_eq (fun x => by
      change (x.val ≤ 1 ∧ ClassGroup.mk K x =
        (ClassGroup.mk K (classRepresentative K ((ClassGroup.mk K J.val)⁻¹)))⁻¹) ↔ _
      rw [h])).mpr rfl
  right_inv _ := rfl

/-- The actual unweighted complex series over all nonzero integral ideals. -/
def integralDedekindDirichlet (s : ℂ) : ℂ :=
  ∑' J : integralFractionalIdeals K,
    ((FractionalIdeal.absNorm J.1.val : ℝ) : ℂ) ^ (-s)

theorem integralDedekindDirichlet_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun J : integralFractionalIdeals K =>
      ((FractionalIdeal.absNorm J.1.val : ℝ) : ℂ) ^ (-s)) := by
  apply Summable.of_norm_bounded (integralFractionalIdeals_norm_summable (K := K) hs)
  intro J
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (fractionalIdeal_absNorm_pos J.val),
    Complex.neg_re]

/-- The complex ideal series is exactly the actual Mathlib Dedekind zeta
function throughout the half-plane of absolute convergence. -/
theorem integralDedekindDirichlet_eq_dedekindZeta {s : ℂ} (hs : 1 < s.re) :
    integralDedekindDirichlet K s = NumberField.dedekindZeta K s := by
  classical
  let F : integralFractionalIdeals K → ℂ := fun J =>
    ((FractionalIdeal.absNorm J.1.val : ℝ) : ℂ) ^ (-s)
  let G : {I : Ideal (𝓞 K) // I ≠ ⊥} → ℂ :=
    fun I => (Ideal.absNorm I.val : ℂ) ^ (-s)
  have heq : F ∘ integralFractionalIdealsEquiv K = G := by
    funext I
    change ((FractionalIdeal.absNorm (I.val : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ (-s) = _
    rw [FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast, Complex.ofReal_natCast]
  have hF : Summable F := integralDedekindDirichlet_summable K hs
  have hG : Summable (F ∘ integralFractionalIdealsEquiv K) :=
    hF.comp_injective (integralFractionalIdealsEquiv K).injective
  rw [heq] at hG
  have ht : integralDedekindDirichlet K s = ∑' I, G I := by
    have h := (integralFractionalIdealsEquiv K).tsum_eq F
    change (∑' I, (F ∘ integralFractionalIdealsEquiv K) I) = integralDedekindDirichlet K s at h
    rw [heq] at h
    exact h.symm
  rw [ht]
  have hgroup := (hG.hasSum.tsum_fiberwise (fun I => Ideal.absNorm I.val)).tsum_eq
  rw [← hgroup, ← idealCoefficient_LSeries_eq K s]
  unfold LSeries
  apply tsum_congr
  intro m
  change (∑' I : {I : {J : Ideal (𝓞 K) // J ≠ ⊥} // Ideal.absNorm I.1 = m},
    (Ideal.absNorm I.1.1 : ℂ) ^ (-s)) = _
  have hf : (fun I : {I : {J : Ideal (𝓞 K) // J ≠ ⊥} // Ideal.absNorm I.1 = m} =>
      (Ideal.absNorm I.1.1 : ℂ) ^ (-s)) = fun _ => (m : ℂ) ^ (-s) := by
    funext I
    rw [I.2]
  rw [hf]
  by_cases hm : m = 0
  · subst m
    have : IsEmpty {I : {J : Ideal (𝓞 K) // J ≠ ⊥} // Ideal.absNorm I.1 = 0} :=
      ⟨fun I => I.1.2 (Ideal.absNorm_eq_zero_iff.mp I.2)⟩
    simp [LSeries.term]
  · rw [← (nonzeroIdealNormFiberEquiv (K := K) m hm).symm.tsum_eq]
    have : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = m} :=
      (Ideal.finite_setOfPred_absNorm_eq m).to_subtype
    let : Fintype {I : Ideal (𝓞 K) // Ideal.absNorm I = m} := Fintype.ofFinite _
    simp [LSeries.term_of_ne_zero hm, idealCoefficientReal, idealCoefficient_pos K m hm,
      Nat.card_eq_fintype_card, Complex.cpow_neg, div_eq_mul_inv]

/-- The full complex ideal series is the finite sum of the actual partial
series associated to genuine ideal-class representatives. -/
theorem integralDedekindDirichlet_partition {s : ℂ} (hs : 1 < s.re) :
    integralDedekindDirichlet K s =
      ∑ c : ClassGroup (𝓞 K), mixedPartialDedekindDirichlet K (classRepresentative K c) s := by
  classical
  let F : integralFractionalIdeals K → ℂ := fun J =>
    ((FractionalIdeal.absNorm J.1.val : ℝ) : ℂ) ^ (-s)
  have h := ((idealClassPartitionEquiv K).summable_iff.mpr
    (integralDedekindDirichlet_summable K hs)).tsum_sigma
  change (∑' x, F (idealClassPartitionEquiv K x)) = _ at h
  rw [(idealClassPartitionEquiv K).tsum_eq F] at h
  simp only [tsum_fintype] at h
  exact h

/-- The exact class sum needed to pass from the partial completed functions
to the actual Dedekind zeta function of any signature. -/
theorem dedekindZeta_eq_partial_class_sum {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta K s =
      ∑ c : ClassGroup (𝓞 K), mixedPartialDedekindDirichlet K (classRepresentative K c) s :=
  (integralDedekindDirichlet_eq_dedekindZeta K hs).symm.trans
    (integralDedekindDirichlet_partition K hs)

end
end ArtinMatthews.VaryingKummerAnalytic
