module

public import ArtinMatthews.PrincipalAngularCorrection


set_option backward.privateInPublic true
@[expose] public section

/-! The actual angular principal correction is the product of the
literal normalized j=0 source series. No sixth-order hypothesis on the
finite ray character is used: its sixth power stays in the third phase. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain Set Filter AngularLambda
open scoped NumberField Classical BigOperators Topology
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {ζ : K} {M : Ideal (𝓞 K)}

def principalAngularResidueCharacter (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (ArtinMatthews.ProbePrime K)) (hS : principalAngularCutoff K M ⊆ S)
    (P : ArtinMatthews.ProbeGoodPrime K S) : MulChar ((𝓞 K) ⧸ P.val.asIdeal) ℂ :=
  cyclotomicAngularResidueCharacter hζ P.val
    (principalAngularCutoff_six_not_mem P.val (fun h => P.property (hS h)))

def principalAngularLocalSource (hζ : IsPrimitiveRoot ζ 12) (η : EvenIdealRayCharacter K M)
    (S : Finset (ArtinMatthews.ProbePrime K)) (hS : principalAngularCutoff K M ⊆ S)
    (P : ArtinMatthews.ProbeGoodPrime K S) (s : ℂ) : ℂ :=
  let Q : ℝ := Ideal.absNorm P.val.asIdeal
  let χ := principalAngularResidueCharacter hζ S hS P
  (1 - ArtinMatthews.probeLocalV Q (1 / 6)) * (1 - ArtinMatthews.probeLocalW Q 1 1) /
    (1 - ArtinMatthews.probeLocalD Q (η.allCoefficient P.val.asIdeal) s) *
    probeIdealSourceSeries K P.val χ 0 (probeIdealGaussGamma K P.val χ 2)
      (probeIdealGaussLocalVartheta K P.val χ (η.allCoefficient P.val.asIdeal)) 1 s 1 (1 / 6)

theorem principalAngular_vartheta_sixth (hζ : IsPrimitiveRoot ζ 12) (η : EvenIdealRayCharacter K M)
    (S : Finset (ArtinMatthews.ProbePrime K)) (hS : principalAngularCutoff K M ⊆ S)
    (P : ArtinMatthews.ProbeGoodPrime K S) :
    probeIdealGaussLocalVartheta K P.val (principalAngularResidueCharacter hζ S hS P)
      (η.allCoefficient P.val.asIdeal) ^ 6 = principalAngularThirdPhase hζ η P.val := by
  let hsix := principalAngularCutoff_six_not_mem P.val (fun h => P.property (hS h))
  have hχ := cyclotomicAngularResidueCharacter_order hζ P.val hsix
  rw [principalAngularResidueCharacter, probeIdealGauss_vartheta_sixth K P.val _ hχ
    (probeIdealCharacter_minus_one_of_twelve hζ P.val _ hχ)
    (probeIdealResidue_char_ne_two P.val hsix),
    cyclotomicAngularResidueCharacter_localLambda hζ P.val hsix]
  rfl

theorem principalAngular_local_parameters (P : ArtinMatthews.ProbePrime K)
    (c : ℂ) (hc : ‖c‖ ≤ 1) {s : ℂ} (hs : 1 / 2 < s.re) :
    ‖ArtinMatthews.probeLocalV (Ideal.absNorm P.asIdeal) (1 / 6)‖ < 1 ∧
      ‖ArtinMatthews.probeLocalW (Ideal.absNorm P.asIdeal) 1 1‖ < 1 ∧
      ‖ArtinMatthews.probeLocalE (Ideal.absNorm P.asIdeal) c s (1 / 6)‖ < 1 := by
  have hQ := probeIdealPrime_norm_gt_one K P
  have hQ0 := lt_trans zero_lt_one hQ
  refine ⟨?_, ?_, ?_⟩
  · rw [ArtinMatthews.probeLocalV_norm _ hQ0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by norm_num)
  · exact (ArtinMatthews.probeLocalW_norm_le _ hQ0 1 1 (by simp)).trans_lt
      (Real.rpow_lt_one_of_one_lt_of_neg hQ (by norm_num))
  · exact (ArtinMatthews.probeLocalE_norm_le _ hQ0 c s (1 / 6) hc).trans_lt
      (Real.rpow_lt_one_of_one_lt_of_neg hQ (by norm_num; linarith))

theorem principalAngularLocalSource_eq_factor (hζ : IsPrimitiveRoot ζ 12)
    (η : EvenIdealRayCharacter K M) (S : Finset (ArtinMatthews.ProbePrime K))
    (hS : principalAngularCutoff K M ⊆ S) (P : ArtinMatthews.ProbeGoodPrime K S)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    principalAngularLocalSource hζ η S hS P s =
      ArtinMatthews.probeGoodPrimeCorrection (Ideal.absNorm P.val.asIdeal) 1
        (η.allCoefficient P.val.asIdeal) (principalAngularThirdPhase hζ η P.val) s 1 (1 / 6) := by
  let hsix := principalAngularCutoff_six_not_mem P.val (fun h => P.property (hS h))
  let χ := principalAngularResidueCharacter hζ S hS P
  have hχ : orderOf χ = 6 := cyclotomicAngularResidueCharacter_order hζ P.val hsix
  have hv := principalAngular_vartheta_sixth hζ η S hS P
  change probeIdealGaussLocalVartheta K P.val χ (η.allCoefficient P.val.asIdeal) ^ 6 = _ at hv
  obtain ⟨hV, hW, hE⟩ := principalAngular_local_parameters P.val
    (principalAngularThirdPhase hζ η P.val) (principalAngularThirdPhase_norm_le_one hζ η P.val) hs
  have H := probeIdealGoodSourceSeries_correction K P.val χ hχ
    (probeIdealCharacter_minus_one_of_twelve hζ P.val χ hχ)
    (probeIdealResidue_char_ne_two P.val hsix)
    (η.allCoefficient P.val.asIdeal) 1 s 1 (1 / 6) (by norm_num)
  dsimp only at H
  rw [hv] at H
  simpa only [principalAngularLocalSource, inv_one, mul_one] using H hV hW hE

theorem principalAngularCorrection_hasProd_source (hζ : IsPrimitiveRoot ζ 12)
    (η : EvenIdealRayCharacter K M) (S : Finset (ArtinMatthews.ProbePrime K))
    (hS : principalAngularCutoff K M ⊆ S) {s : ℂ} (hs : 99799 / 100000 ≤ s.re) :
    HasProd (fun P : ArtinMatthews.ProbeGoodPrime K S => principalAngularLocalSource hζ η S hS P s)
      (principalAngularCorrection hζ η S s) := by
  have hcut := probePrimeCutoff_subset_principalAngularCutoff.trans hS
  have hp := principalAngular_point_region hs
  have H := ArtinMatthews.probeEulerProduct_hasProd K S hcut
    (fun _ => 1) (fun P => η.allCoefficient P.asIdeal) (principalAngularThirdPhase hζ η)
    (by simp) (fun P => η.allCoefficient_norm_le_one P.asIdeal)
    (fun P => principalAngularThirdPhase_norm_le_one hζ η P) hp
  rw [← ArtinMatthews.probeEulerProduct_eq_exp K S hcut _ _ _ (by simp)
    (fun P => η.allCoefficient_norm_le_one P.asIdeal)
    (fun P => principalAngularThirdPhase_norm_le_one hζ η P) hp] at H
  apply H.congr_fun
  intro P
  exact principalAngularLocalSource_eq_factor hζ η S hS P (by linarith : 1 / 2 < s.re)

theorem principalAngularCorrection_eq_tprod_source (hζ : IsPrimitiveRoot ζ 12)
    (η : EvenIdealRayCharacter K M) (S : Finset (ArtinMatthews.ProbePrime K))
    (hS : principalAngularCutoff K M ⊆ S) {s : ℂ} (hs : 99799 / 100000 ≤ s.re) :
    principalAngularCorrection hζ η S s =
      ∏' P : ArtinMatthews.ProbeGoodPrime K S, principalAngularLocalSource hζ η S hS P s :=
  (principalAngularCorrection_hasProd_source hζ η S hS hs).tprod_eq.symm

end
end ArtinMatthews.VaryingKummerAnalytic
