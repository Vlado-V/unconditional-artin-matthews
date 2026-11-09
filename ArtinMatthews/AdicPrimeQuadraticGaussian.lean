module

public import ArtinMatthews.AdicPrimeResidueCharacter
public import ArtinMatthews.FiniteQuadraticGaussPhase
public import ArtinMatthews.AdicAnalyticWeil
public import ArtinMatthews.AnalyticWeilSquareClasses


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine Haar/Abel quadratic Gaussian for an arbitrary actual
uniformizer, with the exact volume/cardinality constant and no replacement
of its residue additive character by a chosen phase. -/

namespace ArtinMatthews.QuadraticWeil

open MeasureTheory NumberField IsDedekindDomain LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField ArtinMatthews.QuadraticGauss
open OAI.RepresentationTheory.Weil.Local
open scoped NumberField ValuativeRel Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local instance primeGaussianRelation : ValuativeRel (v.adicCompletion F) := adicRelation F v
local instance primeGaussianLocalField : IsNonarchimedeanLocalField (v.adicCompletion F) := adicLocalField F v
local instance primeGaussianCharZero : CharZero (v.adicCompletion F) :=
  charZero_of_injective_ringHom (algebraMap F (v.adicCompletion F)).injective
local instance primeGaussianMeasurable : MeasurableSpace (v.adicCompletion F) := borel (v.adicCompletion F)
local instance primeGaussianBorel : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
local instance primeGaussianResidueFintype : Fintype 𝓀[v.adicCompletion F] := Fintype.ofFinite _

theorem adic_integer_norm (x : v.adicCompletion F) :
    x ∈ (ValuativeRel.valuation (v.adicCompletion F)).integer ↔ ‖x‖ ≤ 1 := by
  rw [adic_mem_integer_iff F v]
  change (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) x ≤ 1 ↔ ‖x‖ ≤ 1
  exact (Valued.toNormedField.norm_le_one_iff).symm

theorem adic_canonical_two_unit
    (h2 : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) 2 = 1) :
    ValuativeRel.valuation (v.adicCompletion F) (2 : v.adicCompletion F) = 1 := by
  let ν : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  let : ν.Compatible := Valuation.Compatible.ofValuation ν
  have hrel : (2 : v.adicCompletion F) =ᵥ (1 : v.adicCompletion F) :=
    (Valuation.veq_iff_eq ν).mpr (by simpa only [map_one] using h2)
  simpa only [map_one] using (Valuation.veq_iff_eq (ValuativeRel.valuation (v.adicCompletion F))).mp hrel

variable (ψ : AddChar (v.adicCompletion F) ℂ) (hψ : adicConductorZero F v ψ)
  (u : v.adicCompletion F)
  (hu : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) u = WithZero.exp (-1 : ℤ))
  (hunit : ∀ x, ‖ψ x‖ = 1) (hc : Continuous ψ)
  (h2 : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) 2 = 1)

include hunit hc h2 in
theorem adicPrime_gaussianIntegral :
    FunctionsMetaplectic.Construction.gaussianIntegral (v.adicCompletion F) ψ (2 * u⁻¹) =
      (((Measure.addHaar : Measure (v.adicCompletion F)).real
          (integerOpenSubgroup (v.adicCompletion F) : Set (v.adicCompletion F)) : ℂ) *
        ∑ z : 𝓀[v.adicCompletion F], adicPrimeResidueChar F v ψ hψ u hu (z ^ 2)) /
      Fintype.card 𝓀[v.adicCompletion F] := by
  let C := v.adicCompletion F
  let ν : Valuation C (WithZero (Multiplicative ℤ)) := Valued.v
  let : NontriviallyNormedField C := Valued.toNontriviallyNormedField C (WithZero (Multiplicative ℤ))
  have hu0 : u ≠ 0 := by
    intro he
    have h := hu
    rw [he, map_zero] at h
    exact WithZero.exp_ne_zero h.symm
  have hcoef : (2 : C) * u⁻¹ ≠ 0 := mul_ne_zero (by norm_num) (inv_ne_zero hu0)
  have hi : ((2 : C) * u⁻¹)⁻¹ ∈ (ValuativeRel.valuation C).integer := by
    apply (adic_mem_integer_iff F v _).mpr
    change ν (((2 : C) * u⁻¹)⁻¹) ≤ 1
    rw [map_inv₀, map_mul, h2, one_mul, map_inv₀, inv_inv, hu]
    decide
  rw [gaussianIntegral_eq_integer_integral C (adic_integer_norm F v)
    (nontrivialNorm_not_discrete C) ψ hψ hunit hc (adic_canonical_two_unit F v h2) _ hcoef hi]
  calc
    _ = ∫ x in (integerOpenSubgroup C : Set C), ψ (u⁻¹ * x ^ 2) ∂(Measure.addHaar : Measure C) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => congrArg ψ (by ring))
    _ = _ := by
      apply compact_finite_integral (Measure.addHaar : Measure C) (integerOpenSubgroup C)
        (integerOpenSubgroup_compact C) (integerReduction C) (integerReduction_surjective C)
      · exact hc.comp (by fun_prop)
      · intro x
        exact (adicPrimeResidueChar_quadratic F v ψ hψ u hu ⟨(x : C), x.property⟩).symm

include hunit hc h2 in
theorem adicPrime_normalizedWeil_eq_residueIndex :
    analyticNormalizedWeil ψ (Units.mk0 u (by
      intro he
      have h := hu
      rw [he, map_zero] at h
      exact WithZero.exp_ne_zero h.symm))⁻¹ =
      residueIndex 𝓀[v.adicCompletion F] (adicPrimeResidueChar F v ψ hψ u hu) := by
  let C := v.adicCompletion F
  let : NontriviallyNormedField C := Valued.toNontriviallyNormedField C (WithZero (Multiplicative ℤ))
  have htwo := adic_canonical_two_unit F v h2
  rw [analyticNormalizedWeil, analyticIndex_two C (adic_integer_norm F v) ψ hψ hunit hc htwo, div_one,
    FunctionsMetaplectic.Construction.gaussianIndex]
  simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
  rw [adicPrime_gaussianIntegral F v ψ hψ u hu hunit hc h2]
  let A : ℝ := (Measure.addHaar : Measure C).real (integerOpenSubgroup C : Set C)
  let q : ℝ := Fintype.card 𝓀[C]
  let T : ℂ := ∑ z : 𝓀[C], adicPrimeResidueChar F v ψ hψ u hu (z ^ 2)
  have hA : 0 < A := NonarchimedeanFourier.Construction.compact_open_subgroup_real_pos
    Measure.addHaar (integerOpenSubgroup C) (integerOpenSubgroup_compact C)
  have hq : 0 < q := Nat.cast_pos.mpr Fintype.card_pos
  change FunctionsMetaplectic.Construction.phase (((A : ℂ) * T) / Fintype.card 𝓀[C]) = _
  have he : ((A : ℂ) * T) / Fintype.card 𝓀[C] = ((A / q : ℝ) : ℂ) * T := by
    dsimp only [q]
    rw [Complex.ofReal_div, Complex.ofReal_natCast]
    ring
  rw [he, Gaussian.Construction.phase_positive_mul (A / q) (div_pos hA hq)]
  exact finite_quadratic_phase 𝓀[C] (tameResidue_char_ne_two C htwo)
    (adicPrimeResidueChar F v ψ hψ u hu) (adicPrimeResidueChar_nontrivial F v ψ hψ u hu)

end

end ArtinMatthews.QuadraticWeil
