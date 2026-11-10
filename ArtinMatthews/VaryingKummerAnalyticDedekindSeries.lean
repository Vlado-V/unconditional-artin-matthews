module

public import ArtinMatthews.VaryingKummerAnalyticIdealOrbits
public import OAI.NumberTheory.PrimePackets.IdealCoefficients
public import Mathlib.NumberTheory.LSeries.Deriv
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Analysis.CStarAlgebra.Classes


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine general-field ideal norm series and the Mathlib Dedekind zeta function.
The norm-fiber and integral-fractional-ideal equivalences are general OpenAI
PrimePackets extracts; none uses a signature or degree-parity hypothesis. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal MeasureTheory Set Filter
open OAI.PrimeDegreePackets
open scoped NumberField nonZeroDivisors Classical BigOperators ENNReal
noncomputable section

private lemma fractional_absNorm_pos {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    0 < (FractionalIdeal.absNorm I.val : ℝ) := by
  exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg I.val)
    (fun h => I.ne_zero (FractionalIdeal.absNorm_eq_zero_iff.mp h.symm))

/-- Genuine nonzero integral fractional ideals in an arbitrary number field. -/
def integralFractionalIdeals (K : Type*) [Field K] [NumberField K] :=
  {J : (FractionalIdeal (𝓞 K)⁰ K)ˣ // (J : FractionalIdeal (𝓞 K)⁰ K) ≤ 1}

/-- The literal equivalence with nonzero ordinary integral ideals. -/
def integralFractionalIdealsEquiv (K : Type*) [Field K] [NumberField K] :
    {J : Ideal (𝓞 K) // J ≠ ⊥} ≃ integralFractionalIdeals K :=
  Equiv.ofBijective (fun J =>
    ⟨Units.mk0 (J.1 : FractionalIdeal (𝓞 K)⁰ K) (by simpa using J.2),
      FractionalIdeal.coeIdeal_le_one⟩)
    ⟨by
      intro J L h
      apply Subtype.ext
      apply FractionalIdeal.coeIdeal_injective (K := K)
      exact congrArg (fun a : integralFractionalIdeals K => a.1.val) h,
    by
      rintro ⟨J, hJ⟩
      obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hJ
      have hI0 : I ≠ ⊥ := by
        intro he
        subst I
        simp only [FractionalIdeal.coeIdeal_bot] at hI
        exact J.ne_zero hI.symm
      refine ⟨⟨I, hI0⟩, ?_⟩
      apply Subtype.ext
      apply Units.ext
      exact hI⟩

theorem tsum_integralFractionalIdeals (K : Type*) [Field K] [NumberField K]
    (F : FractionalIdeal (𝓞 K)⁰ K → ℝ≥0∞) :
    (∑' J : integralFractionalIdeals K, F J.1) =
      ∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥}, F J.1 :=
  ((integralFractionalIdealsEquiv K).tsum_eq (fun J => F J.1)).symm

def nonzeroIdealNormFiberEquiv {K : Type*} [Field K] [NumberField K]
    (m : ℕ) (hm : m ≠ 0) :
    {I : {J : Ideal (𝓞 K) // J ≠ ⊥} // Ideal.absNorm I.1 = m} ≃
      {I : Ideal (𝓞 K) // Ideal.absNorm I = m} where
  toFun I := ⟨I.1.1, I.2⟩
  invFun I := ⟨⟨I.1, fun hz => hm (by simpa [hz] using I.2.symm)⟩, I.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact grouping of the actual ideal norm fibers, with the zero ideal
excluded rather than assigned an artificial Dirichlet weight. -/
theorem integralIdeal_norm_tsum {K : Type*} [Field K] [NumberField K]
    (F : ℕ → ℝ≥0∞) :
    (∑' I : {J : Ideal (𝓞 K) // J ≠ ⊥}, F (Ideal.absNorm I.1)) =
      ∑' m : ℕ, (idealCoefficient K m : ℝ≥0∞) * F m := by
  classical
  rw [← ENNReal.tsum_fiberwise
    (fun I : {J : Ideal (𝓞 K) // J ≠ ⊥} => F (Ideal.absNorm I.1))
    (fun I => Ideal.absNorm I.1)]
  apply tsum_congr
  intro m
  change (∑' I : {I : {J : Ideal (𝓞 K) // J ≠ ⊥} // Ideal.absNorm I.1 = m},
    F (Ideal.absNorm I.1.1)) = _
  have hf : (fun I : {I : {J : Ideal (𝓞 K) // J ≠ ⊥} // Ideal.absNorm I.1 = m} =>
    F (Ideal.absNorm I.1.1)) = fun _ => F m := by funext I; rw [I.2]
  rw [hf]
  by_cases hm : m = 0
  · subst m
    have : IsEmpty {I : {J : Ideal (𝓞 K) // J ≠ ⊥} // Ideal.absNorm I.1 = 0} :=
      ⟨fun I => I.1.2 (Ideal.absNorm_eq_zero_iff.mp I.2)⟩
    simp
  · rw [← (nonzeroIdealNormFiberEquiv (K := K) m hm).symm.tsum_eq]
    have : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = m} :=
      (Ideal.finite_setOfPred_absNorm_eq m).to_subtype
    let : Fintype {I : Ideal (𝓞 K) // Ideal.absNorm I = m} := Fintype.ofFinite _
    rw [tsum_fintype, Finset.sum_const, nsmul_eq_mul, idealCoefficient_pos K m hm,
      Nat.card_eq_fintype_card]
    rfl

/-- The actual positive ideal series equals the actual Mathlib Dedekind zeta
function in its half-plane of convergence. -/
theorem integralFractionalIdeals_norm_tsum {K : Type*} [Field K] [NumberField K]
    {s : ℝ} (hs : 1 < s) :
    (∑' J : integralFractionalIdeals K,
      ENNReal.ofReal ((FractionalIdeal.absNorm J.1.val : ℝ) ^ (-s))) =
      ENNReal.ofReal ((NumberField.dedekindZeta K s).re) := by
  rw [tsum_integralFractionalIdeals K (fun J =>
    ENNReal.ofReal ((FractionalIdeal.absNorm J : ℝ) ^ (-s)))]
  simp only [FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast]
  rw [integralIdeal_norm_tsum (fun m => ENNReal.ofReal ((m : ℝ) ^ (-s)))]
  have he (m : ℕ) :
      (idealCoefficient K m : ℝ≥0∞) * ENNReal.ofReal ((m : ℝ) ^ (-s)) =
        ENNReal.ofReal (realDirichletTerm (idealCoefficientReal K) s m) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1
    simp [realDirichletTerm, idealCoefficientReal, Real.rpow_neg, div_eq_mul_inv]
  simp_rw [he]
  have hnonneg (m : ℕ) : 0 ≤ realDirichletTerm (idealCoefficientReal K) s m :=
    div_nonneg (idealCoefficientReal_nonneg K m) (Real.rpow_nonneg (Nat.cast_nonneg m) s)
  have hz : (NumberField.dedekindZeta K s).re =
      ∑' m, realDirichletTerm (idealCoefficientReal K) s m := by
    simpa only [Complex.ofReal_re] using
      (congrArg Complex.re (idealDirichlet_eq_dedekindZeta K s)).symm
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg (idealCoefficient_real_summable K hs), ← hz]

theorem integralFractionalIdeals_norm_summable {K : Type*} [Field K] [NumberField K]
    {s : ℝ} (hs : 1 < s) :
    Summable (fun J : integralFractionalIdeals K =>
      (FractionalIdeal.absNorm J.1.val : ℝ) ^ (-s)) := by
  have h := ENNReal.summable_toReal (show
    (∑' J : integralFractionalIdeals K,
      ENNReal.ofReal ((FractionalIdeal.absNorm J.1.val : ℝ) ^ (-s))) ≠ ⊤ from by
    rw [integralFractionalIdeals_norm_tsum hs]
    exact ENNReal.ofReal_ne_top)
  simpa only [ENNReal.toReal_ofReal (Real.rpow_nonneg (fractional_absNorm_pos _).le _)] using h

/-- Holomorphy of the actual Mathlib Dedekind zeta function for every number
field on `Re(s)>1`. -/
theorem dedekindZeta_analyticOnNhd (K : Type*) [Field K] [NumberField K] :
    AnalyticOnNhd ℂ (NumberField.dedekindZeta K) {s : ℂ | 1 < s.re} := by
  let f : ℕ → ℂ := fun m => (idealCoefficientReal K m : ℂ)
  have habs : LSeries.abscissaOfAbsConv f ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (fun y hy =>
      idealCoefficient_LSeriesSummable K (by simpa using hy))
  have heq : NumberField.dedekindZeta K = LSeries f := by
    funext s
    exact (idealCoefficient_LSeries_eq K s).symm
  rw [heq]
  apply (LSeries_analyticOnNhd f).mono
  intro s hs
  exact lt_of_le_of_lt habs (by exact_mod_cast hs)

theorem dedekindZeta_differentiableOn (K : Type*) [Field K] [NumberField K] :
    DifferentiableOn ℂ (NumberField.dedekindZeta K) {s : ℂ | 1 < s.re} :=
  (dedekindZeta_analyticOnNhd K).differentiableOn

end
end ArtinMatthews.VaryingKummerAnalytic
