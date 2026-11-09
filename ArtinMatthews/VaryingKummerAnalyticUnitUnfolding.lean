module

public import ArtinMatthews.VaryingKummerAnalyticMixedLogCoordinates
public import Mathlib.MeasureTheory.Group.FundamentalDomain


set_option backward.privateInPublic true
@[expose] public section

/-! Positive unit-orbit integration for the actual Dirichlet logarithm of an
arbitrary number field. The finite kernel is the full roots-of-unity group;
its order is not replaced by the totally-real value two. The generic unfolding
argument is extracted from OpenAI PrimePackets/ZetaResidues.lean with arbitrary
finite coordinate type in place of `Fin d`. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField MeasureTheory
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField nonZeroDivisors Classical BigOperators ENNReal
noncomputable section

theorem tsum_comp_surjective_addHom {A B : Type*} [AddGroup A] [AddGroup B]
    (additiveMap : A →+ B) (hφ : Function.Surjective additiveMap) [Finite additiveMap.ker]
    (f : B → ℝ≥0∞) :
    (∑' a, f (additiveMap a)) = (Nat.card additiveMap.ker : ℝ≥0∞) * ∑' b, f b := by
  rw [← ENNReal.tsum_fiberwise (fun a => f (additiveMap a)) additiveMap,← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro b
  let e := AddMonoidHom.fiberEquivKerOfSurjective hφ b
  let := Fintype.ofFinite additiveMap.ker
  let := Fintype.ofEquiv additiveMap.ker e.symm
  calc
    (∑' a : additiveMap ⁻¹' {b}, f (additiveMap a)) = ∑' _a : additiveMap ⁻¹' {b}, f b := by
      apply tsum_congr
      intro a
      rw [show additiveMap a = b from a.property]
    _ = (Nat.card additiveMap.ker : ℝ≥0∞) * f b := by
      rw [tsum_fintype,Finset.sum_const,nsmul_eq_mul,Finset.card_univ,
        ← Nat.card_eq_fintype_card,Nat.card_congr e]

 

theorem lintegral_tsum_addHom_fundamentalDomain {ι : Type*} [Fintype ι] {A : Type*} [AddGroup A]
    (L : Submodule ℤ (ι → ℝ)) [Countable L]
    (additiveMap : A →+ L) (hφ : Function.Surjective additiveMap) [Finite additiveMap.ker]
    {t : Set (ι → ℝ)} (ht : IsAddFundamentalDomain L t volume)
    (f : (ι → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ u in t, ∑' a, f ((additiveMap a : ι → ℝ)+u)) =
      (Nat.card additiveMap.ker : ℝ≥0∞) * ∫⁻ v, f v := by
  have he (u : ι → ℝ) : (∑' a, f ((additiveMap a : ι → ℝ)+u)) =
      (Nat.card additiveMap.ker : ℝ≥0∞) * ∑' p : L, f ((p : ι → ℝ)+u) :=
    tsum_comp_surjective_addHom additiveMap hφ (fun p => f ((p : ι → ℝ)+u))
  have : VAddInvariantMeasure L (ι → ℝ) volume :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup (ι → ℝ) volume)
  simp_rw [he]
  rw [lintegral_const_mul _ (by fun_prop)]
  congr 1
  rw [ht.lintegral_eq_tsum'' f]
  exact lintegral_tsum (fun p => (hf.comp (measurable_const.add measurable_id)).aemeasurable)

variable (K : Type*) [Field K] [NumberField K]

def mixedUnitLogOnto : Additive ((𝓞 K)ˣ) →+ unitLattice K where
  toFun z := ⟨logEmbedding K z, ⟨z, Submodule.mem_top, rfl⟩⟩
  map_zero' := by apply Subtype.ext; exact map_zero (logEmbedding K)
  map_add' x y := by apply Subtype.ext; exact map_add (logEmbedding K) x y

theorem mixedUnitLogOnto_surjective : Function.Surjective (mixedUnitLogOnto K) := by
  rintro ⟨u, hu⟩
  obtain ⟨z, _, hz⟩ := hu
  exact ⟨z, Subtype.ext hz⟩

def mixedUnitLogKernelEquiv : (mixedUnitLogOnto K).ker ≃ torsion K where
  toFun z := ⟨z.1.toMul, (logEmbedding_eq_zero_iff).mp (congrArg Subtype.val z.2)⟩
  invFun z := ⟨Additive.ofMul z.1, Subtype.ext ((logEmbedding_eq_zero_iff).mpr z.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Finite (mixedUnitLogOnto K).ker :=
  Finite.of_equiv (torsion K) (mixedUnitLogKernelEquiv K).symm

theorem mixedUnitLogOnto_kernel_card : Nat.card (mixedUnitLogOnto K).ker = torsionOrder K :=
  Nat.card_congr (mixedUnitLogKernelEquiv K)

theorem mixedUnitLogDomain_fundamental :
    IsAddFundamentalDomain (unitLattice K) (mixedUnitLogDomain K) volume :=
  ZLattice.isAddFundamentalDomain (basisUnitLattice K) volume

theorem mixedUnitLog_unfold (f : logSpace K → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ u in mixedUnitLogDomain K, ∑' z : (𝓞 K)ˣ,
      f (logEmbedding K (Additive.ofMul z) + u)) =
      (torsionOrder K : ℝ≥0∞) * ∫⁻ u, f u := by
  have h := lintegral_tsum_addHom_fundamentalDomain (unitLattice K)
    (mixedUnitLogOnto K) (mixedUnitLogOnto_surjective K)
    (mixedUnitLogDomain_fundamental K) f hf
  rw [mixedUnitLogOnto_kernel_card K] at h
  exact h

end
end ArtinMatthews.VaryingKummerAnalytic
