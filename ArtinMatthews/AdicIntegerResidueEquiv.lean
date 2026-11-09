module

public import ArtinMatthews.AdicIntegralResidueMap
public import Mathlib.RingTheory.Ideal.Quotient.Operations


set_option backward.privateInPublic true
@[expose] public section

/-! Density of actual number-field integers gives all completed residue
classes. Together with the derived kernel=P this constructs the genuine
O/P to completed-residue ring equivalence. -/

namespace ArtinMatthews.QuadraticWeil

open NumberField IsDedekindDomain LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open scoped NumberField ValuativeRel Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local instance residueEquivRelation : ValuativeRel (v.adicCompletion F) := adicRelation F v
local instance residueEquivLocalField : IsNonarchimedeanLocalField (v.adicCompletion F) := adicLocalField F v

theorem adicResidueOfInteger_surjective : Function.Surjective (adicResidueOfInteger F v) := by
  let C := v.adicCompletion F
  let ν : Valuation C (WithZero (Multiplicative ℤ)) := Valued.v
  let : ν.Compatible := Valuation.Compatible.ofValuation ν
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  let xA : v.adicCompletionIntegers F := ⟨(x : C), (adic_mem_integer_iff F v x).mp x.property⟩
  let U : Set (v.adicCompletionIntegers F) := {y | ‖(y : C) - (x : C)‖ < 1}
  have hU : IsOpen U := by
    apply isOpen_lt
    · fun_prop
    · fun_prop
  have hxU : xA ∈ U := by
    change ‖(x : C) - (x : C)‖ < 1
    norm_num
  obtain ⟨a, ha⟩ := (StandardAdelic.integer_dense_local F v).exists_mem_open hU ⟨xA, hxU⟩
  change ‖((algebraMap (𝓞 F) (v.adicCompletionIntegers F) a : v.adicCompletionIntegers F) : C) - (x : C)‖ < 1 at ha
  have hcast : ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) a : v.adicCompletionIntegers F) : C) =
      algebraMap (𝓞 F) C a := by
    calc
      _ = (algebraMap (𝓞 F) F a : v.adicCompletion F) :=
        HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply (R := 𝓞 F) (K := F) (v := v) a
      _ = _ := (IsScalarTower.algebraMap_apply (𝓞 F) F C a).symm
  rw [hcast] at ha
  let y := adicIntegralOfInteger F v a
  have hynorm : ‖(y : C) - (x : C)‖ < 1 := by
    change ‖algebraMap (𝓞 F) C a - (x : C)‖ < 1
    exact ha
  have hν : ν ((y : C) - (x : C)) < 1 := Valued.toNormedField.norm_lt_one_iff.mp hynorm
  have hcanonical : ValuativeRel.valuation C (((y - x : 𝒪[C]) : C)) < 1 :=
    (Valuation.vlt_one_iff (ValuativeRel.valuation C)).mp ((Valuation.vlt_one_iff ν).mpr hν)
  have hzero : IsLocalRing.residue 𝒪[C] (y - x) = 0 :=
    (adic_residue_eq_zero_iff F v (y - x)).mpr hcanonical
  have he : IsLocalRing.residue 𝒪[C] y = IsLocalRing.residue 𝒪[C] x :=
    sub_eq_zero.mp ((map_sub (IsLocalRing.residue 𝒪[C]) y x).symm.trans hzero)
  exact ⟨a, he⟩

def adicIntegerResidueEquiv : (𝓞 F ⧸ v.asIdeal) ≃+* 𝓀[v.adicCompletion F] :=
  (Ideal.quotEquivOfEq (adicResidueOfInteger_ker F v).symm).trans
    ((adicResidueOfInteger F v).quotientKerEquivOfSurjective (adicResidueOfInteger_surjective F v))

theorem adicIntegerResidueEquiv_mk (x : 𝓞 F) :
    adicIntegerResidueEquiv F v (Ideal.Quotient.mk v.asIdeal x) = adicResidueOfInteger F v x := by
  rw [adicIntegerResidueEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

end

end ArtinMatthews.QuadraticWeil
