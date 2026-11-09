module

public import ArtinMatthews.VaryingKummerAnalyticIdealCharacterTheta
public import ArtinMatthews.VaryingKummerAnalyticIdealModuleResidueCoordinates
public import ArtinMatthews.VaryingKummerAnalyticUnitUnfoldingComplex


set_option backward.privateInPublic true
@[expose] public section

/-! Actual periodic weights for an arbitrary ideal conductor. The modulus
norm annihilates its residue quotient, and the genuine module coordinate
map is surjective without any coprimality between I and the conductor. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Module MeasureTheory
open ArtinMatthews.ReusedTheta
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {d : Type*} [Fintype d]

theorem idealResidue_absNorm_nsmul (M : Ideal (𝓞 K)) (x : (𝓞 K) ⧸ M) : M.absNorm • x = 0 := by
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_nsmul,Ideal.Quotient.eq_zero_iff_mem]
  rw [nsmul_eq_mul]
  change (M.absNorm:𝓞 K)*a ∈ M
  exact M.mul_mem_right a (Ideal.absNorm_mem M)

def idealModuleModNormReduction (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥) :
    ModN I M.absNorm →+ (𝓞 K) ⧸ M :=
  ModN.liftEquiv.symm ⟨(idealResidueCoordinate I M hI hM).toAddMonoidHom,
    fun _ => idealResidue_absNorm_nsmul M _⟩

theorem idealModuleModNormReduction_mk (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥) (a : I) :
    idealModuleModNormReduction I M hI hM (ModN.mkQ M.absNorm a) =
      idealResidueCoordinate I M hI hM a := rfl

theorem idealModuleModNormReduction_surjective (I M : Ideal (𝓞 K))
    (hI : I ≠ ⊥) (hM : M ≠ ⊥) : Function.Surjective (idealModuleModNormReduction I M hI hM) := by
  intro x
  obtain ⟨a,ha⟩ := idealResidueCoordinate_surjective I M hI hM x
  exact ⟨ModN.mkQ M.absNorm a,ha⟩

def idealModuleCharacterWeight (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)
    (bI : Basis d ℤ I) [NeZero M.absNorm] (χ : MulChar ((𝓞 K) ⧸ M) ℂ) : (d → Fin M.absNorm) → ℂ :=
  fun r => χ (idealModuleModNormReduction I M hI hM (moduleResidueEquiv bI M.absNorm r))

theorem idealModuleCharacterWeight_coordinates (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)
    (bI : Basis d ℤ I) [NeZero M.absNorm] (χ : MulChar ((𝓞 K) ⧸ M) ℂ) (z : d → ℤ) :
    periodicPrimalWeight M.absNorm (idealModuleCharacterWeight I M hI hM bI χ) z =
      χ (idealResidueCoordinate I M hI hM (bI.equivFun.symm z)) := by
  simp only [periodicPrimalWeight,idealModuleCharacterWeight,moduleResidueEquiv_coordinates,
    idealModuleModNormReduction_mk]

theorem idealModuleCharacterWeight_zero (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)
    (bI : Basis d ℤ I) [NeZero M.absNorm] (χ : MulChar ((𝓞 K) ⧸ M) ℂ) (hχ : χ ≠ 1) :
    periodicPrimalWeight M.absNorm (idealModuleCharacterWeight I M hI hM bI χ) 0 = 0 := by
  let : Nontrivial ((𝓞 K) ⧸ M) := mulChar_nontrivial_domain χ hχ
  simp only [periodicPrimalWeight,integerCongruenceEquiv_zero,idealModuleCharacterWeight,
    moduleResidueEquiv_zero,map_zero,MulChar.map_zero]

theorem idealModuleCharacterWeight_sum_zero (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)
    (bI : Basis d ℤ I) [NeZero M.absNorm] (χ : MulChar ((𝓞 K) ⧸ M) ℂ) (hχ : χ ≠ 1) :
    ∑ r, idealModuleCharacterWeight I M hI hM bI χ r = 0 := by
  let : Fintype (ModN I M.absNorm) := Fintype.ofEquiv (d → Fin M.absNorm) (moduleResidueEquiv bI M.absNorm)
  let : Finite ((𝓞 K) ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient hM
  let : Fintype ((𝓞 K) ⧸ M) := Fintype.ofFinite _
  have H := complex_tsum_comp_surjective_addHom (idealModuleModNormReduction I M hI hM)
    (idealModuleModNormReduction_surjective I M hI hM) (fun x => χ x) (Summable.of_finite)
  simp only [tsum_fintype] at H
  unfold idealModuleCharacterWeight
  rw [show (∑ r, χ (idealModuleModNormReduction I M hI hM
      (moduleResidueEquiv bI M.absNorm r))) =
      ∑ a, χ (idealModuleModNormReduction I M hI hM a) from
    (moduleResidueEquiv bI M.absNorm).sum_comp
      (fun a => χ (idealModuleModNormReduction I M hI hM a))]
  rw [H,MulChar.sum_eq_zero_of_ne_one hχ,mul_zero]

end
end ArtinMatthews.VaryingKummerAnalytic
