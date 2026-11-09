module

public import ArtinMatthews.IntegerConductorDual
public import ArtinMatthews.IntegerOpenSubgroup
public import OAI.RepresentationTheory.Weil.Local.GaussianCompact


set_option backward.privateInPublic true
@[expose] public section

/-! Derive an actual compact domain for the analytic Abel Gaussian from the
conductor-zero condition.  The domain and its annihilator are not supplied as
hypotheses. -/

namespace ArtinMatthews.QuadraticWeil

open MeasureTheory LocalFieldTheory ArtinMatthews.QuadraticGauss Filter
open OAI.RepresentationTheory.Weil.Local
open scoped ValuativeRel Classical Topology

noncomputable section

variable (K : Type) [NormedField K] [ValuativeRel K] [IsNonarchimedeanLocalField K]

def inverseCoefficientDomain (c : K) : OpenAddSubgroup K :=
  (integerOpenSubgroup K).comap
    { toFun := fun x => c * x
      map_zero' := mul_zero c
      map_add' := mul_add c }
    (continuous_const.mul continuous_id)

theorem inverseCoefficientDomain_compact (c : K) (hc : c ≠ 0) :
    IsCompact (inverseCoefficientDomain K c : Set K) := by
  change IsCompact ((fun x : K => c * x) ⁻¹' (integerOpenSubgroup K : Set K))
  exact (Homeomorph.mulLeft₀ c hc).isCompact_preimage.mpr (integerOpenSubgroup_compact K)

theorem inverseCoefficientDomain_le (c : K) (hc : c ≠ 0)
    (hi : c⁻¹ ∈ (ValuativeRel.valuation K).integer) :
    inverseCoefficientDomain K c ≤ integerOpenSubgroup K := by
  intro t ht
  change c * t ∈ (ValuativeRel.valuation K).integer at ht
  have h := (ValuativeRel.valuation K).integer.mul_mem hi ht
  rw [inv_mul_cancel_left₀ hc] at h
  exact h

theorem inverseCoefficientDomain_dual (ψ : AddChar K ℂ) (hψ : ConductorZero K ψ)
    (c : K) (hc : c ≠ 0) (y : K) :
    y ∈ integerOpenSubgroup K ↔ c * y ∈
      QuadraticFourier.Construction.scalarAnnihilator ψ (inverseCoefficientDomain K c).toAddSubgroup := by
  constructor
  · intro hy t ht
    change c * t ∈ (ValuativeRel.valuation K).integer at ht
    have h := hψ.integer (⟨y, hy⟩ * ⟨c * t, ht⟩)
    change ψ (y * (c * t)) = 1 at h
    simpa only [mul_left_comm, mul_assoc] using h
  · intro hy
    apply (conductorZero_dual_integer K ψ hψ y).mp
    intro b
    have ht : c⁻¹ * (b : K) ∈ inverseCoefficientDomain K c := by
      change c * (c⁻¹ * (b : K)) ∈ (ValuativeRel.valuation K).integer
      rw [mul_inv_cancel_left₀ hc]
      exact b.property
    have h := hy (c⁻¹ * (b : K)) ht
    have heq : (c * y) * (c⁻¹ * (b : K)) = y * (b : K) := by
      field_simp
    rwa [heq] at h

theorem inverseCoefficientDomain_phase (ψ : AddChar K ℂ) (hψ : ConductorZero K ψ)
    (h2 : ValuativeRel.valuation K (2 : K) = 1)
    (c : K) (hc : c ≠ 0) (hi : c⁻¹ ∈ (ValuativeRel.valuation K).integer)
    (t : K) (ht : t ∈ inverseCoefficientDomain K c) : ψ (c * t ^ 2 / 2) = 1 := by
  have htt := inverseCoefficientDomain_le K c hc hi ht
  have hct : c * t ∈ (ValuativeRel.valuation K).integer := ht
  have hhalf : (2 : K)⁻¹ ∈ (ValuativeRel.valuation K).integer := by
    change ValuativeRel.valuation K (2 : K)⁻¹ ≤ 1
    rw [map_inv₀, h2, inv_one]
  have h := hψ.integer (⟨c * t, hct⟩ * ⟨t, htt⟩ * ⟨(2 : K)⁻¹, hhalf⟩)
  simpa only [Subring.coe_mul, div_eq_mul_inv, pow_two, mul_assoc] using h

variable [IsUltrametricDist K]

theorem inverseCoefficientDomain_radial
    (hnorm : ∀ x : K, x ∈ (ValuativeRel.valuation K).integer ↔ ‖x‖ ≤ 1)
    (c : K) (hc : c ≠ 0) (hi : c⁻¹ ∈ (ValuativeRel.valuation K).integer)
    (t : K) (ht : t ∈ inverseCoefficientDomain K c) (y : K)
    (hy : y ∉ integerOpenSubgroup K) : ‖y + t‖ = ‖y‖ := by
  have ht' : ‖t‖ ≤ 1 := (hnorm t).mp (inverseCoefficientDomain_le K c hc hi ht)
  have hy' : 1 < ‖y‖ := lt_of_not_ge (fun h => hy ((hnorm y).mpr h))
  have hlt : ‖t‖ < ‖y‖ := ht'.trans_lt hy'
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le]

variable [CharZero K] [MeasurableSpace K] [BorelSpace K]

theorem gaussianIntegral_eq_integer_integral
    (hnorm : ∀ x : K, x ∈ (ValuativeRel.valuation K).integer ↔ ‖x‖ ≤ 1)
    (hnd : ¬ DiscreteTopology K) (ψ : AddChar K ℂ) (hψ : ConductorZero K ψ)
    (hu : ∀ x : K, ‖ψ x‖ = 1) (hcont : Continuous (fun x => ψ x))
    (h2 : ValuativeRel.valuation K (2 : K) = 1)
    (c : K) (hc : c ≠ 0) (hi : c⁻¹ ∈ (ValuativeRel.valuation K).integer) :
    FunctionsMetaplectic.Construction.gaussianIntegral K ψ c =
      ∫ x in (integerOpenSubgroup K : Set K), ψ (c * x ^ 2 / 2)
        ∂(Measure.addHaar : Measure K) := by
  exact (GaussianCompact.Construction.regularizedGaussian_tendsto_compact_of_domain
    hnd ψ hu hcont c (integerOpenSubgroup K) (inverseCoefficientDomain K c)
    (integerOpenSubgroup_compact K) (inverseCoefficientDomain_compact K c hc)
    (inverseCoefficientDomain_le K c hc hi)
    (inverseCoefficientDomain_phase K ψ hψ h2 c hc hi)
    (inverseCoefficientDomain_dual K ψ hψ c hc)
    (inverseCoefficientDomain_radial K hnorm c hc hi)).limUnder_eq

end

end ArtinMatthews.QuadraticWeil
