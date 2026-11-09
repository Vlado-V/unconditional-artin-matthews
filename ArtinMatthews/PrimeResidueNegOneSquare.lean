module

public import ArtinMatthews.AdicIntegerResidueEquiv
public import ArtinMatthews.SLocalHilbertAlternating


set_option backward.privateInPublic true
@[expose] public section

/-! A primitive twelfth root supplies a genuine square root of -1 in
every completed and ideal residue field, with integrality derived from
the valuation of its square. -/

namespace ArtinMatthews.QuadraticWeil

open NumberField IsDedekindDomain LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open scoped NumberField ValuativeRel Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local instance negOnePrimeRelation : ValuativeRel (v.adicCompletion F) := adicRelation F v
local instance negOnePrimeLocalField : IsNonarchimedeanLocalField (v.adicCompletion F) := adicLocalField F v

theorem completedResidue_neg_one_square (h : IsSquare (-1 : v.adicCompletion F)) :
    IsSquare (-1 : 𝓀[v.adicCompletion F]) := by
  let C := v.adicCompletion F
  obtain ⟨r, hr⟩ := h
  have hr2 : r ^ 2 = -1 := by simpa only [pow_two] using hr.symm
  have hv : (ValuativeRel.valuation C r) ^ 2 = 1 := by
    rw [← map_pow, hr2, Valuation.map_neg, map_one]
  have hi : ValuativeRel.valuation C r ≤ 1 :=
    (pow_le_one_iff_of_nonneg zero_le (by decide : (2 : ℕ) ≠ 0)).mp hv.le
  let rO : 𝒪[C] := ⟨r, hi⟩
  have hro : rO ^ 2 = (-1 : 𝒪[C]) := Subtype.ext hr2
  have hres : IsLocalRing.residue 𝒪[C] rO ^ 2 = (-1 : 𝓀[C]) := by
    rw [← map_pow, hro, map_neg, map_one]
  refine ⟨IsLocalRing.residue 𝒪[C] rO, ?_⟩
  simpa only [pow_two] using hres.symm

theorem idealResidue_neg_one_square_of_twelve {ζ : F} (hζ : IsPrimitiveRoot ζ 12) :
    IsSquare (-1 : 𝓞 F ⧸ v.asIdeal) := by
  obtain ⟨r, hr⟩ := neg_one_is_square_of_primitive_twelve F hζ
  have hrF : (r : F) ^ 2 = -1 := congrArg Units.val hr
  have hC : IsSquare (-1 : v.adicCompletion F) := by
    refine ⟨algebraMap F (v.adicCompletion F) (r : F), ?_⟩
    have hm := congrArg (algebraMap F (v.adicCompletion F)) hrF
    simpa only [map_neg, map_one, pow_two, map_mul] using hm.symm
  have hR := completedResidue_neg_one_square F v hC
  simpa only [map_neg, map_one] using hR.map (adicIntegerResidueEquiv F v).symm.toRingHom

end

end ArtinMatthews.QuadraticWeil
