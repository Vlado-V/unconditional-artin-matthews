module

public import ArtinMatthews.StandardLocalBallFourier
public import ArtinMatthews.IdealPrimeWeilSquareSum
public import ArtinMatthews.CompactFiniteAverage


set_option backward.privateInPublic true
@[expose] public section

/-! The actual prime ball has one residue class, out of exactly the
ideal norm many classes. Haar translation therefore gives its precise
volume, independently of the starting additive Haar normalization. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain MeasureTheory QuadraticWeil
open scoped NumberField Classical ValuativeRel
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (P : HeightOneSpectrum (𝓞 K))

theorem sourceLocalPrimeBall_iff (x : P.adicCompletion K) :
    x ∈ sourceLocalBall K P (-1) ↔ sourceLocalValuation K P x < 1 := by
  let v := sourceLocalValuation K P
  change v x ≤ WithZero.exp (-1 : ℤ) ↔ v x < 1
  by_cases h : v x = 0
  · simp [h]
  · rw [← WithZero.exp_log h, WithZero.exp_le_exp, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega

theorem sourceLocalPrimeBall_subset_integer : sourceLocalBall K P (-1) ⊆ sourceLocalBall K P 0 := by
  intro x hx
  change sourceLocalValuation K P x ≤ WithZero.exp (0 : ℤ)
  rw [WithZero.exp_zero]
  exact ((sourceLocalPrimeBall_iff K P x).mp hx).le

theorem sourceLocalIntegerReduction_eq_zero (x : integerOpenSubgroup (P.adicCompletion K)) :
    integerReduction (P.adicCompletion K) x = 0 ↔ (x : P.adicCompletion K) ∈ sourceLocalBall K P (-1) := by
  let C := P.adicCompletion K
  let v : Valuation C (WithZero (Multiplicative ℤ)) := Valued.v
  let : v.Compatible := Valuation.Compatible.ofValuation v
  rw [integerReduction_apply, adic_residue_eq_zero_iff, sourceLocalPrimeBall_iff]
  exact (Valuation.vlt_one_iff (ValuativeRel.valuation C)).symm.trans (Valuation.vlt_one_iff v)

local instance sourceLocalResidueFintype : Fintype 𝓀[P.adicCompletion K] := Fintype.ofFinite _

theorem sourceLocalPrimeBall_volume (μ : Measure (P.adicCompletion K)) [μ.IsAddHaarMeasure] :
    μ.real (sourceLocalBall K P (-1)) = μ.real (sourceLocalBall K P 0) / Ideal.absNorm P.asIdeal := by
  let C := P.adicCompletion K
  let U := integerOpenSubgroup C
  let f := sourceLocalBallIndicator K P (-1)
  let g (z : 𝓀[C]) : ℂ := if z = 0 then 1 else 0
  have hfac (x : U) : f x = g (integerReduction C x) := by
    have h : integerReduction C x = 0 ↔ (x : C) ∈ sourceLocalBall K P (-1) :=
      sourceLocalIntegerReduction_eq_zero K P x
    by_cases hx : (x : C) ∈ sourceLocalBall K P (-1)
    · simp only [f, sourceLocalBallIndicator, Set.indicator_of_mem hx, g, h.mpr hx, ite_true]
    · have hn : integerReduction C x ≠ 0 := fun he => hx (h.mp he)
      simp only [f, sourceLocalBallIndicator, Set.indicator_of_notMem hx, g, hn, ite_false]
  have hU : (U : Set C) = sourceLocalBall K P 0 := (sourceLocalBall_zero_eq_integerOpen K P).symm
  have hi : (∫ x in (U : Set C), f x ∂μ) = (μ.real (sourceLocalBall K P (-1)) : ℂ) := by
    rw [hU]
    change (∫ x in sourceLocalBall K P 0, (sourceLocalBall K P (-1)).indicator (fun _ => (1 : ℂ)) x ∂μ) = _
    rw [setIntegral_indicator (sourceLocalBall_isOpen K P (-1)).measurableSet,
      Set.inter_eq_right.mpr (sourceLocalPrimeBall_subset_integer K P)]
    simp only [integral_const, Measure.restrict_apply_univ, Complex.real_smul, Measure.real, mul_one]
  have h := compact_finite_integral μ U (integerOpenSubgroup_compact C)
    (integerReduction C) (integerReduction_surjective C) g f
    (sourceLocalBallIndicator_locallyConstant K P (-1)).continuous hfac
  have hs : (∑ z : 𝓀[C], g z) = 1 := by simp [g]
  rw [hi, hs, mul_one, hU, completedResidue_card_eq_norm K P] at h
  exact_mod_cast h

end
end ArtinMatthews.SourcePhysical
