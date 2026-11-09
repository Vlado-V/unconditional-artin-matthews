module

public import ArtinMatthews.SourceFiniteKPHilbert
public import ArtinMatthews.SixthLocalHensel
public import ArtinMatthews.AdicPrimeQuadraticGaussian
public import ClassFieldTheory.LocalClassFieldTheory.Kummer.PowerResidueTameFormula


set_option backward.privateInPublic true
@[expose] public section

/-! The actual tame unit laws needed for the compact section of the
cubic cover. Unit-unit triviality follows from the genuine tame norm
criterion. Principal units are genuine sixth powers by Hensel lifting,
hence cubes. No chosen normalizing cochain is assumed. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain ClassFieldTheory LocalFieldTheory QuadraticWeil
open LocalFieldTheory.IsNonarchimedeanLocalField LocalClassFieldTheory.Kummer
open scoped NumberField ValuativeRel Classical
noncomputable section

private theorem sourceKPIntegerUnit_exists (C : Type) [Field C] [ValuativeRel C]
    (x : Cˣ) (hx : ValuativeRel.valuation C (x : C) = 1) :
    ∃ u : 𝒪[C]ˣ, integerUnitsToFieldUnits C u = x := by
  let u : 𝒪[C]ˣ :=
    { val := ⟨(x : C), by simp [valuation_integer_membership, hx]⟩
      inv := ⟨((x⁻¹ : Cˣ) : C), by simp [valuation_integer_membership, Units.val_inv_eq_inv_val, hx]⟩
      val_inv := by
        apply Subtype.ext
        change (x : C) * ((x⁻¹ : Cˣ) : C) = 1
        simp [Units.val_inv_eq_inv_val, Units.ne_zero x]
      inv_val := by
        apply Subtype.ext
        change ((x⁻¹ : Cˣ) : C) * (x : C) = 1
        simp [Units.val_inv_eq_inv_val, Units.ne_zero x] }
  exact ⟨u, Units.ext (integerUnitsToFieldUnits_apply C u)⟩

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

abbrev sourceKPFiniteVal : Valuation (P.adicCompletion K) (WithZero (Multiplicative ℤ)) := Valued.v

local instance sourceKPTameRelation : ValuativeRel (P.adicCompletion K) := adicRelation K P
local instance sourceKPTameLocal : IsNonarchimedeanLocalField (P.adicCompletion K) := adicLocalField K P

private theorem sourceKPFiniteVal_to_rel_one (x : P.adicCompletion K)
    (hx : sourceKPFiniteVal K P x = 1) : ValuativeRel.valuation (P.adicCompletion K) x = 1 := by
  let C := P.adicCompletion K
  let ν := sourceKPFiniteVal K P
  let : ν.Compatible := Valuation.Compatible.ofValuation ν
  have hr : x =ᵥ (1 : C) := (Valuation.veq_iff_eq ν).mpr (by simpa only [map_one] using hx)
  simpa only [map_one] using (Valuation.veq_iff_eq (ValuativeRel.valuation C)).mp hr

theorem sourceKPFiniteVal_three (h6 : (6 : 𝓞 K) ∉ P.asIdeal) : sourceKPFiniteVal K P 3 = 1 := by
  have h3 : (3 : 𝓞 K) ∉ P.asIdeal := by
    intro h
    apply h6
    simpa only [show (2 : 𝓞 K) * 3 = 6 by norm_num] using P.asIdeal.mul_mem_left 2 h
  have h := (P.valuation_eq_one_iff_notMem (K := K) (r := (3 : 𝓞 K))).mpr h3
  have hc : Valued.v (algebraMap K (P.adicCompletion K) (3 : K)) = 1 := by
    change Valued.v ((3 : K) : P.adicCompletion K) = 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    simpa only [map_ofNat] using h
  simpa only [map_ofNat] using hc

theorem sourceFiniteKPHilbert_units (h6 : (6 : 𝓞 K) ∉ P.asIdeal)
    (a b : (P.adicCompletion K)ˣ)
    (ha : sourceKPFiniteVal K P (a : P.adicCompletion K) = 1)
    (hb : sourceKPFiniteVal K P (b : P.adicCompletion K) = 1) :
    sourceFiniteKPHilbert K hζ P a b = 1 := by
  let C := P.adicCompletion K
  have h3 : ValuativeRel.valuation C (((3 : ℕ+) : ℕ) : C) = 1 :=
    sourceKPFiniteVal_to_rel_one K P 3 (sourceKPFiniteVal_three K P h6)
  have hmu : (primitiveRoots 3 C).Nonempty :=
    ⟨algebraMap K C (((sourceHilbertRootThree K hζ : Kˣ) : K)),
      (mem_primitiveRoots (by decide : 0 < 3)).mpr
        ((IsPrimitiveRoot.coe_units_iff.mpr (sourceHilbertRootThree_isPrimitive K hζ)).map_of_injective
          (algebraMap K C).injective)⟩
  obtain ⟨u, hu⟩ := sourceKPIntegerUnit_exists C a (sourceKPFiniteVal_to_rel_one K P a ha)
  obtain ⟨v, hv⟩ := sourceKPIntegerUnit_exists C b (sourceKPFiniteVal_to_rel_one K P b hb)
  have h := LocalClassFieldTheory.Kummer.localHilbertSymbol_integerUnit_integerUnit_eq_one C 3 h3 hmu u v
  rw [hu, hv] at h
  have hn : ClassFieldTheory.localHilbertSymbol C 3 (natCast_ne_zero_of_valuation_eq_one C 3 h3)
      hmu a b = 1 := by
    unfold ClassFieldTheory.localHilbertSymbol
    rw [h, map_one]
  rw [sourceFiniteKPHilbert_apply]
  apply ((finitePlaceAdicHilbertPairingFamily_isLocallyHilbert K 3
    (sLocalPrimitiveRoots K 3 (sourceHilbertRootThree_isPrimitive K hζ)) P).2.2.2 a b).mpr
  exact (ClassFieldTheory.localHilbertSymbol_eq_one_iff_isKummerNorm C 3 _ hmu a b).mp hn

theorem sourceFiniteKPHilbert_principalUnit (h6 : (6 : 𝓞 K) ∉ P.asIdeal)
    (a b : (P.adicCompletion K)ˣ)
    (hb : sourceKPFiniteVal K P ((b : P.adicCompletion K) - 1) < 1) :
    sourceFiniteKPHilbert K hζ P a b = 1 := by
  let C := P.adicCompletion K
  let O := P.adicCompletionIntegers K
  let ν := sourceKPFiniteVal K P
  have hval : ν (b : C) = 1 := by
    have hh := ν.map_one_add_of_lt hb
    rwa [add_sub_cancel] at hh
  let x : O := ⟨(b : C), (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K P).mpr hval.le⟩
  have hx : IsUnit x := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hval
  let u := hx.unit
  have hu : (u : O) = x := hx.unit_spec
  have hm : (u : O) - 1 ∈ IsLocalRing.maximalIdeal O := by
    rw [hu]
    exact (Valuation.mem_maximalIdeal_iff C ν).mpr hb
  obtain ⟨w, hw⟩ := sixthLocal_exists_root_of_not_mem P h6 u hm
  let f : Oˣ →* Cˣ := Units.map (algebraMap O C).toMonoidHom
  have hfu : f u = b := by
    apply Units.ext
    change ((u : O) : C) = (b : C)
    rw [hu]
  have hfw : (f w ^ 2) ^ 3 = b := by
    rw [← pow_mul, show 2 * 3 = 6 by decide, ← map_pow, hw, hfu]
  rw [← hfw, sourceFiniteKPHilbert_cube_right]

end
end ArtinMatthews
