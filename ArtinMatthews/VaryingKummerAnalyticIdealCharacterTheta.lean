module

public import ArtinMatthews.VaryingKummerAnalyticPeriodicThetaAverages


set_option backward.privateInPublic true
@[expose] public section

/-! Generic integral-ideal residue-weighted theta proof from OpenAI
PrimePackets/GaussianMellin.lean, namespace/import routing only. -/
namespace ArtinMatthews.ReusedTheta
noncomputable section
open MeasureTheory Module WithLp Set
open scoped Classical BigOperators nonZeroDivisors

variable {d R : Type*} [Fintype d] [CommRing R]
local instance gaussianMellinDecidableEq : DecidableEq d := Classical.decEq d

lemma moduleResidueEquiv_coordinates {M : Type*} [AddCommGroup M]
    (b : Basis d ℤ M) (N : ℕ) [NeZero N] (z : d → ℤ) :
    moduleResidueEquiv b N (integerCongruenceEquiv N z).1 =
      ModN.mkQ N (b.equivFun.symm z) := by
  have hz : (Equiv.piCongrRight fun _ : d => (ZMod.finEquiv N).toEquiv)
      (integerCongruenceEquiv N z).1 = fun i => (z i : ZMod N) := by
    funext i
    exact finEquiv_divMod N (z i)
  simp only [moduleResidueEquiv,Equiv.trans_apply,hz,LinearEquiv.coe_toEquiv,
    Basis.equivFun_symm_apply,_root_.map_sum,map_zsmul,ModN.basis_apply_eq_mkQ,
    Int.cast_smul_eq_zsmul]

lemma idealCharacterWeight_coordinates (I : Ideal R) (bI : Basis d ℤ I)
    (N : ℕ) [NeZero N] (χ : MulChar (R ⧸ rationalModulusIdeal R N) ℂ) (z : d → ℤ) :
    periodicPrimalWeight N (idealCharacterWeight I bI N χ) z =
      χ (Ideal.Quotient.mk (rationalModulusIdeal R N) (bI.equivFun.symm z : R)) := by
  simp only [periodicPrimalWeight,idealCharacterWeight,moduleResidueEquiv_coordinates,
    idealModNReduction_mk]

 
def idealCharacterTheta (I : Ideal R) (bI : Basis d ℤ I)
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) (N : ℕ)
    (χ : MulChar (R ⧸ rationalModulusIdeal R N) ℂ) (t : ℝ) : ℂ :=
  ∑' a : I, χ (Ideal.Quotient.mk (rationalModulusIdeal R N) (a:R)) *
    Complex.exp (-((Real.pi*t : ℝ):ℂ)*‖B (euclideanInteger (bI.equivFun a))‖^2)

lemma idealCharacterTheta_eq_periodic (I : Ideal R) (bI : Basis d ℤ I)
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) (N : ℕ) [NeZero N]
    (χ : MulChar (R ⧸ rationalModulusIdeal R N) ℂ) (t : ℝ) :
    idealCharacterTheta I bI B N χ t =
      normalizedPeriodicTheta (modulusScaledBasis B N) N (idealCharacterWeight I bI N χ) t := by
  unfold idealCharacterTheta normalizedPeriodicTheta periodicLatticeTheta
  rw [← bI.equivFun.symm.toEquiv.tsum_eq]
  apply tsum_congr
  intro z
  simp only [LinearEquiv.coe_toEquiv,LinearEquiv.apply_symm_apply,modulusScaledBasis_cancel]
  rw [← idealCharacterWeight_coordinates I bI N χ z]
  rfl

lemma idealCharacterTheta_mellin_entire (I : Ideal R) (bI : Basis d ℤ I) (bR : Basis d ℤ R)
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) (N : ℕ) [NeZero N]
    (hI : IsCoprime I (rationalModulusIdeal R N))
    (χ : MulChar (R ⧸ rationalModulusIdeal R N) ℂ) (hχ : χ ≠ 1) :
    Differentiable ℂ (mellin (idealCharacterTheta I bI B N χ)) := by
  have H : idealCharacterTheta I bI B N χ =
      normalizedPeriodicTheta (modulusScaledBasis B N) N (idealCharacterWeight I bI N χ) :=
    funext (idealCharacterTheta_eq_periodic I bI B N χ)
  rw [H]
  exact normalizedPeriodicTheta_mellin_entire _ N _
    (idealCharacterWeight_zero I bI N χ hχ) (idealCharacterWeight_sum_zero I bI bR N hI χ hχ)


end
end ArtinMatthews.ReusedTheta
