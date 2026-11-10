module

public import ArtinMatthews.VaryingKummerAnalyticMixedLogCoordinates
public import ArtinMatthews.VaryingKummerAnalyticUnitUnfolding


set_option backward.privateInPublic true
@[expose] public section

/-! Complex full-unit unfolding for arbitrary signature. Generic proof extracted
from OpenAI PrimePackets/IdealThetaFlow, with a finite coordinate type replacing Fin d. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField MeasureTheory
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField nonZeroDivisors Classical BigOperators ENNReal
noncomputable section
lemma complex_tsum_comp_surjective_addHom {A B : Type*} [AddGroup A] [AddGroup B]
    (hom : A →+ B) (hφ : Function.Surjective hom) [Finite hom.ker]
    (f : B → ℂ) (hs : Summable (fun a => f (hom a))) :
    (∑' a, f (hom a)) = (Nat.card hom.ker : ℂ) * ∑' b, f b := by
  classical
  have H := ((Equiv.sigmaFiberEquiv hom).summable_iff.mpr hs).tsum_sigma
  simp only [Function.comp_apply] at H
  rw [(Equiv.sigmaFiberEquiv hom).tsum_eq (fun a => f (hom a))] at H
  rw [H, ← tsum_mul_left]
  apply tsum_congr
  intro b
  let e1 : {a // hom a = b} ≃ (hom ⁻¹' {b}) :=
    Equiv.subtypeEquivRight (fun a => by simp)
  let e := e1.trans (AddMonoidHom.fiberEquivKerOfSurjective hφ b)
  let := Fintype.ofFinite hom.ker
  let := Fintype.ofEquiv hom.ker e.symm
  calc
    (∑' a : {a // hom a = b}, f (hom a)) = ∑' _a : {a // hom a = b}, f b := by
      apply tsum_congr
      intro a
      rw [a.property]
    _ = (Nat.card hom.ker : ℂ) * f b := by
      rw [tsum_fintype,Finset.sum_const,nsmul_eq_mul,Finset.card_univ,
        ← Nat.card_eq_fintype_card,Nat.card_congr e]

 

theorem integral_tsum_addHom_fundamentalDomain_complex {ι : Type*} [Fintype ι] {A : Type*}
    [AddGroup A] [Countable A] (L : Submodule ℤ (ι → ℝ)) [Countable L]
    (hom : A →+ L) (hφ : Function.Surjective hom) [Finite hom.ker]
    {D : Set (ι → ℝ)} (hD : IsAddFundamentalDomain L D volume)
    (f : (ι → ℝ) → ℂ) (hfM : Measurable f) (hf : Integrable f) :
    (∫ u in D, ∑' a, f ((hom a : ι → ℝ)+u)) =
      (Nat.card hom.ker : ℂ) * ∫ u, f u := by
  have : VAddInvariantMeasure L (ι → ℝ) volume :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup (ι → ℝ) volume)
  have HI (a : A) : IntegrableOn (fun u => f ((hom a : ι → ℝ)+u)) D :=
    (hf.comp_add_left _).restrict
  have HN : (∑' a : A, ∫⁻ u in D, ‖f ((hom a : ι → ℝ)+u)‖ₑ) ≠ ⊤ := by
    have HM (a : A) : AEMeasurable (fun u : ι → ℝ =>
        ‖f ((hom a : ι → ℝ)+u)‖ₑ) (volume.restrict D) :=
      ((hfM.comp (measurable_const.add measurable_id)).enorm).aemeasurable
    rw [← lintegral_tsum HM]
    have HU := lintegral_tsum_addHom_fundamentalDomain L hom hφ hD
      (fun u => ‖f u‖ₑ) hfM.enorm
    rw [HU]
    exact ENNReal.mul_ne_top (by simp) hf.hasFiniteIntegral.ne
  have HS : Summable (fun a : A => ∫ u in D, f ((hom a : ι → ℝ)+u)) := by
    apply (ENNReal.summable_toReal HN).of_norm_bounded
    intro a
    rw [← integral_norm_eq_lintegral_enorm (HI a).aestronglyMeasurable]
    exact norm_integral_le_integral_norm _
  rw [integral_tsum (fun a => (HI a).aestronglyMeasurable) HN,
    complex_tsum_comp_surjective_addHom hom hφ
      (fun p => ∫ u in D, f ((p : ι → ℝ)+u)) HS]
  congr 1
  exact (hD.integral_eq_tsum'' f hf).symm


variable (K : Type*) [Field K] [NumberField K]

theorem mixedUnitLog_unfold_complex (f : logSpace K → ℂ)
    (hfM : Measurable f) (hf : Integrable f) :
    (∫ u in mixedUnitLogDomain K, ∑' z : (𝓞 K)ˣ,
      f (logEmbedding K (Additive.ofMul z) + u)) =
      (torsionOrder K : ℂ) * ∫ u, f u := by
  let : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let : Countable (𝓞 K) := NumberField.RingOfIntegers.coe_injective.countable
  let : Countable (𝓞 K)ˣ := Units.val_injective.countable
  let : Countable (Additive ((𝓞 K)ˣ)) := by change Countable ((𝓞 K)ˣ); infer_instance
  let : Countable (unitLattice K) := (mixedUnitLogOnto_surjective K).countable
  have h := integral_tsum_addHom_fundamentalDomain_complex (unitLattice K)
    (mixedUnitLogOnto K) (mixedUnitLogOnto_surjective K)
    (mixedUnitLogDomain_fundamental K) f hfM hf
  rw [mixedUnitLogOnto_kernel_card K] at h
  exact h

end
end ArtinMatthews.VaryingKummerAnalytic
