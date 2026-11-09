module

public import ArtinMatthews.SourceKPRetainedThetaDepth
public import ArtinMatthews.SourceKPRetainedSeedAtDepth
public import ArtinMatthews.SourceReflectionSUnitCharacter


set_option backward.privateInPublic true
@[expose] public section

/-! On the shifted positive support the actual theta and row characters
evaluate to their principal factors. The row character uses the literal
local sixth roots of the cutoff. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain SourcePhysical SourceReflection StandardAdelic
open RayClass QuadraticWeil VaryingKummerAnalytic SourceEulerAssembly
open scoped NumberField SourcePhysical Classical BigOperators

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "S[" S₀ "]" => sourceHilbertSet K S₀

theorem sourceKPRetainedThetaShift_at (S : Finset Pr) (a : Kˣ)
    (x : SWholeUnits K S) (P : S) :
    (sWholeDiagonal K S a*x).2 P =
      sourceKPRetainedUnitAt K P.val (FiniteAdeleRing.unitEmbedding (𝓞 K) K a)*x.2 P := by
  change Units.map (algebraMap K (P.val.adicCompletion K)).toMonoidHom a*x.2 P = _
  rw [sourceKPRetainedUnitAt_rational]

theorem sourceKPRetainedThetaRowMultiplier_eq_principal
    (S₀ : Finset Pr) (hS : standardWeilBadPlaces K ⊆ S[S₀])
    {J : Ideal (𝓞 K)} (hJ : J ≠ ⊥) (η : EvenIdealRayCharacter K J)
    (u : exteriorUnitSubgroup S[S₀]) (U : ∀ P : S[S₀], SourceThetaFiniteCutoff K P.val)
    (hU : ∀ (P : S[S₀]) (t : (P.val.adicCompletion K)ˣ), t ∈ (U P).region →
      ((t : P.val.adicCompletion K)-1) ∈ sourceLocalBall K P.val
        (-(sourceKPRetainedModulusDepth K S[S₀] (sourceReflectionThetaModulus K S₀ hJ) P : ℤ)) ∧
        ∃ w, w^6 = t)
    (a : Kˣ) (x : SWholeUnits K S[S₀])
    (hx : ∀ P : S[S₀], (sWholeDiagonal K S[S₀] a*x).2 P ∈ (U P).region) :
    letI : IsTotallyComplex K := source_isTotallyComplex K hζ
    let ϑ := sourceReflectionLocalThetaCharacter K S₀ hJ hζ hS η
    let ρ := sourceReflectionSUnitCharacter K hζ S₀ u
    let d := sWholeDiagonal K S[S₀] a
    (ϑ x.2 * ρ x)⁻¹ = ϑ d.2 * ρ d := by
  letI : IsTotallyComplex K := source_isTotallyComplex K hζ
  let S := S[S₀]
  let ϑ := sourceReflectionLocalThetaCharacter K S₀ hJ hζ hS η
  let ρ := sourceReflectionSUnitCharacter K hζ S₀ u
  let d := sWholeDiagonal K S a
  let w := d*x
  have hθ : ϑ w.2 = 1 :=
    sourceKPRetainedThetaFactor_eq_one K hζ S₀ hS hJ η w.2 (fun P => (hU P (w.2 P) (hx P)).1)
  choose z hz using fun P : S => (hU P (w.2 P) (hx P)).2
  have he : w.2 = (1:SWholeUnits K S).2*z^6 := by
    funext P
    change w.2 P = (1 : (P.val.adicCompletion K)ˣ)*(z P)^6
    rw [one_mul,hz]
  have hρ : ρ w = 1 :=
    (sourceReflectionSUnitCharacter_eq_of_finite_sixth_mul K hζ S₀ u (x := w) (y := 1) z he).trans
      (map_one ρ)
  have hprod : (ϑ d.2*ρ d)*(ϑ x.2*ρ x) = 1 := calc
    _ = (ϑ d.2*ϑ x.2)*(ρ d*ρ x) := by ac_rfl
    _ = ϑ w.2*ρ w := by
      change _ = ϑ (d.2*x.2)*ρ (d*x)
      rw [ϑ.map_mul,ρ.map_mul]
    _ = 1 := by rw [hθ,hρ,mul_one]
  change (ϑ x.2*ρ x)⁻¹ = ϑ d.2*ρ d
  calc
    _ = ((ϑ d.2*ρ d)*(ϑ x.2*ρ x))*(ϑ x.2*ρ x)⁻¹ := by rw [hprod,one_mul]
    _ = _ := by rw [mul_assoc,mul_inv_cancel,mul_one]

theorem sourceKPRetainedThetaRowMultiplier_factor_product
    (S₀ : Finset Pr) (hS : standardWeilBadPlaces K ⊆ S[S₀])
    {J : Ideal (𝓞 K)} (hJ : J ≠ ⊥) (η : EvenIdealRayCharacter K J)
    (u : exteriorUnitSubgroup S[S₀]) (U : ∀ P : S[S₀], SourceThetaFiniteCutoff K P.val)
    (hU : ∀ (P : S[S₀]) (t : (P.val.adicCompletion K)ˣ), t ∈ (U P).region →
      ((t : P.val.adicCompletion K)-1) ∈ sourceLocalBall K P.val
        (-(sourceKPRetainedModulusDepth K S[S₀] (sourceReflectionThetaModulus K S₀ hJ) P : ℤ)) ∧
        ∃ w, w^6 = t)
    (a : Kˣ) (x : SWholeUnits K S[S₀]) :
    letI : IsTotallyComplex K := source_isTotallyComplex K hζ
    let ϑ := sourceReflectionLocalThetaCharacter K S₀ hJ hζ hS η
    let ρ := sourceReflectionSUnitCharacter K hζ S₀ u
    let d := sWholeDiagonal K S[S₀] a
    let cut := ∏ P : S[S₀], (U P).factor ((d*x).2 P)
    (((ϑ x.2*ρ x)⁻¹ : ℂˣ):ℂ)*cut = ((ϑ d.2*ρ d : ℂˣ):ℂ)*cut := by
  letI : IsTotallyComplex K := source_isTotallyComplex K hζ
  let ϑ := sourceReflectionLocalThetaCharacter K S₀ hJ hζ hS η
  let ρ := sourceReflectionSUnitCharacter K hζ S₀ u
  let d := sWholeDiagonal K S[S₀] a
  let cut := ∏ P : S[S₀], (U P).factor ((d*x).2 P)
  change (((ϑ x.2*ρ x)⁻¹ : ℂˣ):ℂ)*cut = ((ϑ d.2*ρ d : ℂˣ):ℂ)*cut
  by_cases hx : ∀ P : S[S₀], (d*x).2 P ∈ (U P).region
  · have he : (ϑ x.2*ρ x)⁻¹ = ϑ d.2*ρ d :=
      sourceKPRetainedThetaRowMultiplier_eq_principal K hζ S₀ hS hJ η u U hU a x hx
    rw [he]
  · obtain ⟨P,hP⟩ := not_forall.mp hx
    have hzero : cut = 0 := Finset.prod_eq_zero (Finset.mem_univ P) (Set.indicator_of_notMem hP _)
    rw [hzero,mul_zero,mul_zero]

end
end ArtinMatthews
