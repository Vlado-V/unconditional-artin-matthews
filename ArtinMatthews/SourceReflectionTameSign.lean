module

public import ArtinMatthews.SourceKPExteriorWhittakerAllowed
public import ArtinMatthews.SLocalHilbertAlternating


set_option backward.privateInPublic true
@[expose] public section

/-! The actual tame spherical Whittaker value is unchanged by the
sign of its diagonal argument. The sign is a sixth power of a completed
unit, so the checked local sixth-power invariance applies directly. -/

namespace ArtinMatthews

open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic StandardAdelic QuadraticWeil
open scoped NumberField Classical MatrixGroups

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "ν₀" => sourceKPFiniteVal K P.val
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P.val
local notation "W₀" => sourceKPTameCyclicWhittakerValue K hζ S₀ P hS

theorem sourceKPTameCyclicWhittakerValue_diagonal_neg (a : Lˣ) :
    W₀ (l₀ (sourceGL2Diagonal (-a))) = W₀ (l₀ (sourceGL2Diagonal a)) := by
  obtain ⟨z, hz⟩ := neg_one_is_sixth_power_of_primitive_twelve K hζ
  let j : Kˣ →* Lˣ := Units.map (algebraMap K L).toMonoidHom
  let u : Lˣ := j z
  have hu6 : u ^ (6 : ℕ) = -1 := by
    rw [show u = j z from rfl, ← map_pow, hz]
    exact Units.map_neg_one (algebraMap K L)
  have hminus : ν₀ ((-1 : Lˣ) : L) = 1 := by
    rw [Units.val_neg, Units.val_one, Valuation.map_neg, map_one]
  have ho := sourceKPValuationOrder_of_unit ν₀ (-1 : Lˣ) hminus
  have hpow : sourceKPValuationOrder ν₀ (u ^ (6 : ℕ)) = ((6 : ℕ) : ℤ) * sourceKPValuationOrder ν₀ u := by
    simpa only [zpow_natCast] using sourceKPValuationOrder_zpow ν₀ u ((6 : ℕ) : ℤ)
  rw [hu6, ho] at hpow
  have huOrder : sourceKPValuationOrder ν₀ u = 0 := by omega
  have hu : ν₀ (u : L) = 1 := by
    rw [sourceKPValuationOrder_spec, huOrder, neg_zero, WithZero.exp_zero]
  have hsign : a * u ^ (6 : ℕ) = -a := by rw [hu6, mul_neg_one]
  simpa only [hsign] using sourceKPTameCyclicWhittakerValue_diagonal_mul_sixth K hζ S₀ hS P a u hu

theorem sourceKPTameExteriorWhittakerDiagonal_neg (a : Kˣ) :
    sourceKPTameExteriorWhittakerDiagonal K hζ S₀ P hS (-a) =
      sourceKPTameExteriorWhittakerDiagonal K hζ S₀ P hS a := by
  unfold sourceKPTameExteriorWhittakerDiagonal
  have he : Units.map (algebraMap K L).toMonoidHom (-a) =
      -(Units.map (algebraMap K L).toMonoidHom a) := by
    apply Units.ext
    change algebraMap K L (-(a : K)) = -(algebraMap K L (a : K))
    exact map_neg _ _
  rw [he, sourceKPTameCyclicWhittakerValue_diagonal_neg]

end
end ArtinMatthews
