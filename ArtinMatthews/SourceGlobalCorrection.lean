module

public import ArtinMatthews.SourceLocalCorrectionFactorization
public import ArtinMatthews.ProbeEulerHolomorphy


set_option backward.privateInPublic true
@[expose] public section

/-! The analytic correction from the actual source coefficients is the
convergent rational good-prime product times exactly the finite factors
at primes dividing u. The principal specialization is the existing
angular correction used in the Gaussian Mellin signal. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M)
variable (u : sourceRing F S₀) (hu : u ≠ 0)

local notation "S" => sourceHilbertSet F S₀
local notation "A" => sourcePrimeRowCharacter F hζ S₀ u hu
local notation "B" => sourcePrimeRowTwist F hζ S₀ u hu η
local notation "C" => sourcePrimeRowThirdPhase F hζ S₀ u hu η

def sourceExteriorValues (f : SourceExteriorPrime F S₀ → ℂ) (P : ProbePrime F) : ℂ :=
  if hp : P ∉ S then f ⟨P, hp⟩ else 0

theorem sourceExteriorValues_apply (f : SourceExteriorPrime F S₀ → ℂ)
    (P : SourceExteriorPrime F S₀) : sourceExteriorValues F S₀ f P.val = f P :=
  dite_eq_left P.property

theorem sourceExteriorValues_norm_le_one (f : SourceExteriorPrime F S₀ → ℂ)
    (hf : ∀ P, ‖f P‖ ≤ 1) (P : ProbePrime F) : ‖sourceExteriorValues F S₀ f P‖ ≤ 1 := by
  by_cases h : P ∉ S
  · rw [sourceExteriorValues, dite_eq_left h]
    exact hf ⟨P, h⟩
  · rw [sourceExteriorValues, dite_eq_right h, norm_zero]
    exact zero_le_one

def sourceGlobalCorrection (q : ProbeCoordinates) : ℂ :=
  probeEulerProduct F S (sourceExteriorValues F S₀ A) (sourceExteriorValues F S₀ B)
    (sourceExteriorValues F S₀ C) q *
      ∏ P ∈ (sourceElementExponents F S₀ u hu).support, sourcePrimeBadCorrection F hζ S₀ η u hu P q

theorem sourceGoodPrimeCorrection_zero_params (P : ProbePrime F) (q : ProbeCoordinates)
    (hq : q ∈ probeEulerDomain) :
    probeGoodPrimeCorrection (Ideal.absNorm P.asIdeal) 0 0 0 q.1 q.2.1 q.2.2 = 1 := by
  obtain ⟨hV, _, _, _⟩ := sourceLocalParameters_norm_lt_one F P 0 0 0
    (by simp) (by simp) (by simp) q.1 q.2.1 q.2.2 hq
  have hV0 := sourceOneSub_ne_zero_of_norm_lt_one hV
  simp only [probeGoodPrimeCorrection, probeGoodLocalCorrection, probeGoodLocalFactor,
    probeLocalW, probeLocalD, probeLocalE, zero_mul, sub_zero, mul_one, div_one, zero_div,
    add_zero, mul_zero]
  rw [div_eq_mul_inv, one_mul, mul_inv_cancel₀ hV0]

theorem sourcePrimeRowCorrection_split (P : SourceExteriorPrime F S₀) (q : ProbeCoordinates)
    (hq : q ∈ probeEulerDomain) :
    sourcePrimeRowCorrection F hζ S₀ η u hu P q =
      probeGoodPrimeCorrection (Ideal.absNorm P.val.asIdeal) (A P) (B P) (C P) q.1 q.2.1 q.2.2 *
        (if P ∈ (sourceElementExponents F S₀ u hu).support then
          sourcePrimeBadCorrection F hζ S₀ η u hu P q else 1) := by
  by_cases hP : P ∈ (sourceElementExponents F S₀ u hu).support
  · have hj : sourceElementExponents F S₀ u hu P ≠ 0 := Finsupp.mem_support_iff.mp hP
    have ha : A P = 0 := ite_eq_right hj
    have hb : B P = 0 := by rw [sourcePrimeRowTwist, ha, star_zero, mul_zero]
    have hc : C P = 0 := ite_eq_right hj
    rw [sourcePrimeRowCorrection, ite_eq_right hj, ite_eq_left hP, ha, hb, hc,
      sourceGoodPrimeCorrection_zero_params F P.val q hq, one_mul]
  · have hj : sourceElementExponents F S₀ u hu P = 0 := Finsupp.notMem_support_iff.mp hP
    rw [sourcePrimeRowCorrection, ite_eq_left hj, ite_eq_right hP, mul_one]

theorem sourceGlobalCorrection_hasProd (hcut : probePrimeCutoff F ⊆ S)
    (q : ProbeCoordinates) (hq : q ∈ probeEulerDomain) :
    HasProd (fun P : SourceExteriorPrime F S₀ => sourcePrimeRowCorrection F hζ S₀ η u hu P q)
      (sourceGlobalCorrection F hζ S₀ η u hu q) := by
  let a := sourceExteriorValues F S₀ A
  let b := sourceExteriorValues F S₀ B
  let c := sourceExteriorValues F S₀ C
  have ha := sourceExteriorValues_norm_le_one F S₀ A (sourcePrimeRowCharacter_norm_le_one F hζ S₀ u hu)
  have hb := sourceExteriorValues_norm_le_one F S₀ B (sourcePrimeRowTwist_norm_le_one F hζ S₀ u hu η)
  have hc := sourceExteriorValues_norm_le_one F S₀ C (sourcePrimeRowThirdPhase_norm_le_one F hζ S₀ u hu η)
  have hG := probeEulerProduct_hasProd F S hcut a b c ha hb hc hq
  rw [← probeEulerProduct_eq_exp F S hcut a b c ha hb hc hq] at hG
  let T := (sourceElementExponents F S₀ u hu).support
  let d (P : SourceExteriorPrime F S₀) := if P ∈ T then sourcePrimeBadCorrection F hζ S₀ η u hu P q else 1
  have hB : HasProd d (∏ P ∈ T, sourcePrimeBadCorrection F hζ S₀ η u hu P q) := by
    have H : HasProd d (∏ P ∈ T, d P) :=
      hasProd_prod_of_ne_finset_one (s := T) (fun _ h => ite_eq_right h)
    have he : (∏ P ∈ T, d P) = ∏ P ∈ T, sourcePrimeBadCorrection F hζ S₀ η u hu P q :=
      Finset.prod_congr rfl (fun _ h => ite_eq_left h)
    rw [he] at H
    exact H
  apply (hG.mul hB).congr_fun
  intro P
  change sourcePrimeRowCorrection F hζ S₀ η u hu P q =
    probePrimeCorrection F a b c P.val q * d P
  unfold probePrimeCorrection
  dsimp only [a, b, c, d, T]
  rw [sourceExteriorValues_apply, sourceExteriorValues_apply, sourceExteriorValues_apply]
  exact sourcePrimeRowCorrection_split F hζ S₀ η u hu P q hq

theorem sourceGlobalCorrection_one_specialize (s : ℂ) :
    sourceGlobalCorrection F hζ S₀ η 1 one_ne_zero (s, 1, 1 / 6) =
      principalAngularCorrection hζ η S s := by
  rw [sourceGlobalCorrection, sourceElementExponents_one, Finsupp.support_zero, Finset.prod_empty, mul_one]
  unfold principalAngularCorrection probeEulerProduct
  apply tprod_congr
  intro P
  unfold probePrimeCorrection
  rw [sourceExteriorValues_apply, sourceExteriorValues_apply, sourceExteriorValues_apply,
    sourcePrimeRowTwist, sourcePrimeRowCharacter_one, star_one, mul_one, sourcePrimeRowThirdPhase,
    sourceElementExponents_one, Finsupp.zero_apply, ite_eq_left rfl]

end
end ArtinMatthews.SourceEulerAssembly
