module

public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveThetaRootNumber
public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveThetaPoisson


set_option backward.privateInPublic true
@[expose] public section

/-! Actual ray-character theta transform with a single root number for all
ideal classes. The sum is over genuine nonzero trace-dual ideal elements,
with the exact inverse ideal-character coefficient and conductor mask. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal Module
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
set_option maxHeartbeats 1000000
variable (K : Type*) [Field K] [NumberField K]
variable (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)

def mixedPrimitiveRayDualTheta (ψ : EvenIdealRayCharacter K M) (u : logSpace K) (t : ℝ) : ℂ :=
  ∑' a : nonzeroIdealElements (mixedTraceDualIdeal K (mixedConductorIdeal K I M hI hM)),
    ψ.inverse.coefficient ⟨relativeElementIdeal
      (mixedTraceDualIdeal K (mixedConductorIdeal K I M hI hM)) a.val,
      (relativeElementIdeal_le_one_iff _ _).mpr a.property⟩ *
      Complex.exp (-((Real.pi * t : ℝ) : ℂ) *
        ((∑ w : InfinitePlace K, ((w.mult : ℝ) * mixedPlaceWeight K u w * w (a.val : K))^2 : ℝ) : ℂ))

theorem mixedPrimitiveRayDualTheta_eq_subtype (ψ : EvenIdealRayCharacter K M)
    (u : logSpace K) (t : ℝ) :
    mixedPrimitiveRayDualTheta K I M hI hM ψ u t =
      ∑' β : {β : (mixedPrimitiveDualFractionalIdeal K I M).val // (β : K) ≠ 0},
        ψ.inverse.coefficient (mixedPrimitiveDualRelativeIdeal K I M hI hM β.val β.property) *
          Complex.exp (-((Real.pi * t : ℝ) : ℂ) *
            ((∑ w : InfinitePlace K, ((w.mult : ℝ) * mixedPlaceWeight K u w * w (β.val : K))^2 : ℝ) : ℂ)) := by
  exact ((nonzeroIdealElementEquiv (mixedTraceDualIdeal K (mixedConductorIdeal K I M hI hM))).tsum_eq
    (fun a : nonzeroIdealElements (mixedTraceDualIdeal K (mixedConductorIdeal K I M hI hM)) =>
      ψ.inverse.coefficient ⟨relativeElementIdeal
        (mixedTraceDualIdeal K (mixedConductorIdeal K I M hI hM)) a.val,
        (relativeElementIdeal_le_one_iff _ _).mpr a.property⟩ *
        Complex.exp (-((Real.pi * t : ℝ) : ℂ) *
          ((∑ w : InfinitePlace K, ((w.mult : ℝ) * mixedPlaceWeight K u w * w (a.val : K))^2 : ℝ) : ℂ)))).symm

def mixedPrimitivePoissonScale (t : ℝ) : ℂ :=
  (((((FractionalIdeal.absNorm (mixedConductorIdeal K I M hI hM).val : ℝ) *
    (2⁻¹ : ℝ)^InfinitePlace.nrComplexPlaces K * Real.sqrt |(discr K : ℝ)|)⁻¹) : ℝ) : ℂ) *
    (t : ℂ)^(-(((Module.finrank ℚ K : ℕ) : ℂ)/2))

variable [NeZero M]

/-- Literal ray-weighted Poisson, with one common normalized root factor
and the full inverse-ray coefficient at every nonzero dual lattice point. -/
theorem mixedPrimitiveRayTheta_poisson (ψ : EvenIdealRayCharacter K M)
    (hMt : M ≠ ⊤) (hψ : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue) :
    ∃ W : ℂ, ‖W‖ = 1 ∧ ∀ (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
      (G : Ideal (𝓞 K)) (hG : G ≠ ⊥) (_hGM : IsCoprime G M)
      (_hprod : Ideal.span {idealModuleGenerator I M hI hM} = I*G)
      (u : logSpace K) (t : ℝ) (_ht : 0 < t),
      (ψ.idealHom (integralIdealFractionalUnit G hG) : ℂ) *
        mixedPrimitiveTheta K I M hI hM ψ.residue u t =
      mixedPrimitivePoissonScale K I M hI hM t *
        (Real.sqrt (Ideal.absNorm M : ℝ) : ℂ) * W *
          mixedPrimitiveRayDualTheta K I M hI hM ψ (-u) t⁻¹ := by
  let : Nontrivial ((𝓞 K) ⧸ M) := Ideal.Quotient.nontrivial_iff.mpr hMt
  obtain ⟨W,hW,HW⟩ := mixedPrimitiveTheta_common_rootNumber K M ψ hMt hψ
  refine ⟨W,hW,fun I hI G hG hGM hprod u t ht => ?_⟩
  let F := mixedPrimitiveDualFractionalIdeal K I M
  let E : F.val → ℂ := fun β => Complex.exp (-((Real.pi * t⁻¹ : ℝ) : ℂ) *
    ((∑ w : InfinitePlace K, ((w.mult : ℝ) * mixedPlaceWeight K (-u) w * w (β : K))^2 : ℝ) : ℂ))
  let f : F.val → ℂ := fun β => E β *
    (ψ.residue⁻¹ (idealModuleDualResidue K I M hI hM β β.property) * idealTraceGaussSum K M ψ.residue)
  have hsupport : Function.support f ⊆ {β : F.val | (β : K) ≠ 0} := by
    intro β hβ hz
    have hb : β = 0 := Subtype.ext hz
    subst β
    have hlabel : idealModuleDualResidue K I M hI hM (0 : F.val) (0 : F.val).property = 0 :=
      map_zero (idealModuleDualResidueLinear K I M hI hM)
    simp only [f,hlabel,MulChar.map_zero,zero_mul,mul_zero,Function.mem_support,ne_eq,not_true_eq_false] at hβ
  rw [mixedPrimitiveTheta_poisson K I M hI hM ψ.residue hψ u ht]
  change (ψ.idealHom (integralIdealFractionalUnit G hG) : ℂ) *
    (mixedPrimitivePoissonScale K I M hI hM t * ∑' β : F.val, f β) = _
  rw [← tsum_subtype_eq_of_support_subset hsupport]
  change (ψ.idealHom (integralIdealFractionalUnit G hG) : ℂ) *
    (mixedPrimitivePoissonScale K I M hI hM t *
      ∑' β : {β : F.val // (β : K) ≠ 0}, f β.val) = _
  calc
    _ = mixedPrimitivePoissonScale K I M hI hM t *
        ∑' β : {β : F.val // (β : K) ≠ 0},
          (ψ.idealHom (integralIdealFractionalUnit G hG) : ℂ) * f β.val := by
      rw [tsum_mul_left]
      ring
    _ = mixedPrimitivePoissonScale K I M hI hM t *
        ∑' β : {β : F.val // (β : K) ≠ 0},
          ((Real.sqrt (Ideal.absNorm M : ℝ) : ℂ) * W) *
            (ψ.inverse.coefficient (mixedPrimitiveDualRelativeIdeal K I M hI hM β.val β.property) * E β.val) := by
      congr 1
      apply tsum_congr
      intro β
      have H := HW I hI G hG hGM hprod β.val β.property
      change _ * (E β.val * (_ * _)) = _
      calc
        _ = E β.val * ((ψ.idealHom (integralIdealFractionalUnit G hG) : ℂ) *
          (ψ.residue⁻¹ (idealModuleDualResidue K I M hI hM β.val β.val.property) *
            idealTraceGaussSum K M ψ.residue)) := by ring
        _ = _ := by rw [H]; ring
    _ = _ := by
      rw [tsum_mul_left,mixedPrimitiveRayDualTheta_eq_subtype]
      ring

end
end ArtinMatthews.VaryingKummerAnalytic
