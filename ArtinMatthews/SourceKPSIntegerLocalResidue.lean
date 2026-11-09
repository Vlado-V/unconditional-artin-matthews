module

public import ArtinMatthews.SourceKPLocalUnitResidue
public import ArtinMatthews.SourcePrimeExponentValuation


set_option backward.privateInPublic true
@[expose] public section

/-! The residue of a completed exterior unit agrees with the actual
quotient of the constructed S-integer ring. Integral representatives
come from the localization quotient equivalence. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization SIntegerQuotient QuadraticWeil
open scoped NumberField
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "R" => PrincipalIntegerRing (sourceHilbertSeed K S₀)
local notation "L" => P.val.adicCompletion K
local notation "T₀" => sourceHilbertSeed K S₀
local notation "ν₀" => sourceKPFiniteVal K P.val
local notation "p₀" => (sourceAllowedPrimeGenerator K hζ S₀ P : R)
local notation "hp₀" => sourceAllowedPrimeGenerator_ideal K hζ S₀ P
local notation "r₀" => generatorResidueEquiv T₀ P.val P.property p₀ hp₀

theorem sourceKPLocalUnitResidue_eq_sInteger (x : R) (u : Lˣ)
    (hu : ν₀ (u : L) = 1) (hux : (u : L) = algebraMap K L (x : K)) :
    sourceKPLocalUnitResidue K P.val u hu = r₀ (Ideal.Quotient.mk _ x) := by
  obtain ⟨y, hy⟩ := principal_quotient_coverage T₀ P.val.asIdeal
    (by simpa only [pow_one] using principalPrimePower_coprime T₀ P.val P.property 1) x
  have hv := (principalInteger_power_mem_iff_valuation T₀ P.val P.property 1
    (x - algebraMap (𝓞 K) R y)).mp (by simpa only [pow_one] using hy)
  have hd : ν₀ ((u : L) - algebraMap K L (y : K)) < 1 := by
    rw [hux, ← map_sub]
    change Valued.v ((x - algebraMap (𝓞 K) R y : R) : L) < 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hv.trans_lt (WithZero.exp_lt_one_iff.mpr (by decide))
  have hres := (sourceJacquetReduction_eq_iff K P.val
      (sourceKPLocalUnitInteger K P.val u hu) (sourceKPCompletedIntegral K P.val y)).mpr
    (Valued.toNormedField.norm_lt_one_iff.mpr (by
      change ν₀ ((u : L) - (sourceKPCompletedIntegral K P.val y : L)) < 1
      rw [sourceKPCompletedIntegral_val]
      exact hd))
  have hyq : Ideal.Quotient.mk (Ideal.span {p₀}) x =
      Ideal.Quotient.mk (Ideal.span {p₀}) (algebraMap (𝓞 K) R y) := by
    have hmem : x - algebraMap (𝓞 K) R y ∈ Ideal.span {p₀} := hp₀ ▸ hy
    exact Ideal.Quotient.eq.mpr hmem
  change sourceJacquetReduction K P.val (sourceKPLocalUnitInteger K P.val u hu) = _
  rw [hres, sourceKPCompletedIntegral_residue]
  exact (generatorResidueEquiv_mk T₀ P.val P.property p₀ hp₀ y).symm.trans
    (congrArg r₀ hyq.symm)

end
end ArtinMatthews
