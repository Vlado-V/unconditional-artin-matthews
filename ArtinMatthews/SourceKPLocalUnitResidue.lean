module

public import ArtinMatthews.SourceJacquetHaar
public import ArtinMatthews.SourceFiniteKPTameUnits


set_option backward.privateInPublic true
@[expose] public section

/-! Every actual completed unit has an integral representative of its
residue class. The quotient by that representative is a principal
unit, with the exact valuation inequality. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain LocalFieldTheory QuadraticWeil
open LocalFieldTheory.IsNonarchimedeanLocalField
open GlobalClassFieldTheory.Reciprocity
open scoped NumberField ValuativeRel Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))

def sourceKPCompletedIntegral (x : 𝓞 K) : sourceJacquetIntegers K P :=
  let a := adicIntegralOfInteger K P x
  ⟨(a : P.adicCompletion K), a.property⟩

theorem sourceKPCompletedIntegral_val (x : 𝓞 K) :
    (sourceKPCompletedIntegral K P x : P.adicCompletion K) =
      algebraMap K (P.adicCompletion K) (x : K) :=
  IsScalarTower.algebraMap_apply (𝓞 K) K (P.adicCompletion K) x

theorem sourceKPCompletedIntegral_residue (x : 𝓞 K) :
    sourceJacquetReduction K P (sourceKPCompletedIntegral K P x) = Ideal.Quotient.mk P.asIdeal x := by
  calc
    _ = (adicIntegerResidueEquiv K P).symm (adicResidueOfInteger K P x) := rfl
    _ = _ := by rw [← adicIntegerResidueEquiv_mk, RingEquiv.symm_apply_apply]

def sourceKPLocalUnitInteger (u : (P.adicCompletion K)ˣ)
    (hu : sourceKPFiniteVal K P (u : P.adicCompletion K) = 1) : sourceJacquetIntegers K P :=
  ⟨(u : P.adicCompletion K), (adic_mem_integer_iff K P _).mpr
    ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K P).mpr hu.le)⟩

def sourceKPLocalUnitResidue (u : (P.adicCompletion K)ˣ)
    (hu : sourceKPFiniteVal K P (u : P.adicCompletion K) = 1) : (𝓞 K) ⧸ P.asIdeal :=
  sourceJacquetReduction K P (sourceKPLocalUnitInteger K P u hu)

theorem sourceKPLocalUnitResidue_ne_zero (u : (P.adicCompletion K)ˣ)
    (hu : sourceKPFiniteVal K P (u : P.adicCompletion K) = 1) :
    sourceKPLocalUnitResidue K P u hu ≠ 0 := by
  intro h
  have he : sourceJacquetReduction K P (sourceKPLocalUnitInteger K P u hu) =
      sourceJacquetReduction K P (0 : sourceJacquetIntegers K P) := h.trans (map_zero _).symm
  have hnorm := (sourceJacquetReduction_eq_iff K P (sourceKPLocalUnitInteger K P u hu) 0).mp he
  have hv := Valued.toNormedField.norm_lt_one_iff.mp hnorm
  change sourceKPFiniteVal K P ((u : P.adicCompletion K) - 0) < 1 at hv
  rw [sub_zero, hu] at hv
  exact (lt_irrefl 1) hv

theorem sourceKPLocalUnitResidue_representative (u : (P.adicCompletion K)ˣ)
    (hu : sourceKPFiniteVal K P (u : P.adicCompletion K) = 1) :
    ∃ x : 𝓞 K, x ∉ P.asIdeal ∧ Ideal.Quotient.mk P.asIdeal x = sourceKPLocalUnitResidue K P u hu ∧
      sourceKPFiniteVal K P ((u : P.adicCompletion K) - algebraMap K (P.adicCompletion K) (x : K)) < 1 := by
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (sourceKPLocalUnitResidue K P u hu)
  have hx0 : x ∉ P.asIdeal := by
    intro h
    exact sourceKPLocalUnitResidue_ne_zero K P u hu (hx.symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr h))
  refine ⟨x, hx0, hx, ?_⟩
  have he : sourceJacquetReduction K P (sourceKPLocalUnitInteger K P u hu) =
      sourceJacquetReduction K P (sourceKPCompletedIntegral K P x) :=
    hx.symm.trans (sourceKPCompletedIntegral_residue K P x).symm
  have hn := (sourceJacquetReduction_eq_iff K P (sourceKPLocalUnitInteger K P u hu)
    (sourceKPCompletedIntegral K P x)).mp he
  have hv := Valued.toNormedField.norm_lt_one_iff.mp hn
  rw [sourceKPCompletedIntegral_val K P x] at hv
  exact hv

theorem sourceKPIntegralUnit_completion_valuation (x : 𝓞 K) (hx : x ∉ P.asIdeal) :
    sourceKPFiniteVal K P ((Units.map (algebraMap K (P.adicCompletion K)).toMonoidHom
      (primeAvoidingIntegralFieldUnit K P x hx) : (P.adicCompletion K)ˣ) : P.adicCompletion K) = 1 := by
  change Valued.v ((x : K) : P.adicCompletion K) = 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact (P.valuation_eq_one_iff_notMem (K := K) (r := x)).mpr hx

theorem sourceKPFiniteUnitRatio_principal (u v : (P.adicCompletion K)ˣ)
    (hv : sourceKPFiniteVal K P (v : P.adicCompletion K) = 1)
    (h : sourceKPFiniteVal K P ((u : P.adicCompletion K) - (v : P.adicCompletion K)) < 1) :
    sourceKPFiniteVal K P ((((u / v : (P.adicCompletion K)ˣ)) : P.adicCompletion K) - 1) < 1 := by
  let C := P.adicCompletion K
  have he : (u : C) / (v : C) - 1 = ((u : C) - (v : C)) / (v : C) := by
    rw [sub_div, div_self (Units.ne_zero v)]
  rw [Units.val_div_eq_div_val, he, map_div₀, hv, div_one]
  exact h

end
end ArtinMatthews
