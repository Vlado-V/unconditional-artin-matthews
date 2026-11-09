module

public import ArtinMatthews.CompactSupportL2Map
public import ArtinMatthews.ContinuousMapDerivative


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set
noncomputable section

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (S : Set X) [CompactSpace S]

def compactSupportRestriction (f : X → ℂ) (hf : Continuous f) : C(S, ℂ) :=
  ⟨fun x => f x, hf.comp continuous_subtype_val⟩

theorem compactContinuousZeroExtension_restriction (f : X → ℂ) (hf : Continuous f)
    (hsupport : Function.support f ⊆ S) :
    compactContinuousZeroExtension S (compactSupportRestriction S f hf) = f := by
  funext x
  by_cases hx : x ∈ S
  · exact compactContinuousZeroExtension_mem S _ x hx
  · rw [compactContinuousZeroExtension_notMem S _ x hx]
    have hzero : f x = 0 := by
      by_contra hne
      exact hx (hsupport hne)
    exact hzero.symm

theorem compactSupport_memLp (hs : MeasurableSet S) (μ : Measure X) (hμS : μ S ≠ ⊤)
    (f : X → ℂ) (hf : Continuous f) (hsupport : Function.support f ⊆ S) :
    MemLp f 2 μ := by
  have hm := compactContinuousZeroExtension_memLp S hs μ hμS (compactSupportRestriction S f hf)
  rwa [compactContinuousZeroExtension_restriction S f hf hsupport] at hm

theorem compactContinuousToL2L_restriction (hs : MeasurableSet S) (μ : Measure X)
    (hμS : μ S ≠ ⊤) (f : X → ℂ) (hf : Continuous f) (hsupport : Function.support f ⊆ S)
    (hm : MemLp f 2 μ) :
    compactContinuousToL2L S hs μ hμS (compactSupportRestriction S f hf) = hm.toLp f := by
  change (compactContinuousZeroExtension_memLp S hs μ hμS _).toLp _ = hm.toLp f
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall (congrFun (compactContinuousZeroExtension_restriction S f hf hsupport))

theorem hasDerivAt_toLp_of_fixed_compact_support
    (hs : MeasurableSet S) (μ : Measure X) (hμS : μ S ≠ ⊤)
    (F G : ℂ → X → ℂ)
    (hF : Continuous (fun p : ℂ × X => F p.1 p.2))
    (hG : Continuous (fun p : ℂ × X => G p.1 p.2))
    (hFs : ∀ z, Function.support (F z) ⊆ S)
    (hGs : ∀ z, Function.support (G z) ⊆ S)
    (hderiv : ∀ z x, HasDerivAt (fun w => F w x) (G z x) z)
    (hFm : ∀ z, MemLp (F z) 2 μ) (hGm : ∀ z, MemLp (G z) 2 μ) (z : ℂ) :
    HasDerivAt (fun w => (hFm w).toLp (F w)) ((hGm z).toLp (G z)) z := by
  have hFz (w : ℂ) : Continuous (F w) := hF.comp (continuous_const.prodMk continuous_id)
  have hGz (w : ℂ) : Continuous (G w) := hG.comp (continuous_const.prodMk continuous_id)
  let Fr : ℂ → C(S, ℂ) := fun w => compactSupportRestriction S (F w) (hFz w)
  let Gr : ℂ → C(S, ℂ) := fun w => compactSupportRestriction S (G w) (hGz w)
  have hGr : Continuous Gr := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact hG.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hFr : HasDerivAt Fr (Gr z) z :=
    hasDerivAt_continuousMap_of_pointwise Fr Gr hGr (fun w x => hderiv w x.val) z
  let L := compactContinuousToL2L S hs μ hμS
  have hcomp : HasDerivAt (fun w => L (Fr w)) (L (Gr z)) z :=
    L.hasFDerivAt.comp_hasDerivAt z hFr
  have hfeq : (fun w => L (Fr w)) = (fun w => (hFm w).toLp (F w)) := by
    funext w
    exact compactContinuousToL2L_restriction S hs μ hμS (F w) (hFz w) (hFs w) (hFm w)
  have hgeq : L (Gr z) = (hGm z).toLp (G z) :=
    compactContinuousToL2L_restriction S hs μ hμS (G z) (hGz z) (hGs z) (hGm z)
  rwa [hfeq,hgeq] at hcomp


theorem compactSupportFamily_memLp
    (hs : MeasurableSet S) (μ : Measure X) (hμS : μ S ≠ ⊤)
    (F : ℂ → X → ℂ) (hF : Continuous (fun p : ℂ × X => F p.1 p.2))
    (hFs : ∀ z, Function.support (F z) ⊆ S) (z : ℂ) : MemLp (F z) 2 μ :=
  compactSupport_memLp S hs μ hμS (F z)
    (hF.comp (continuous_const.prodMk continuous_id)) (hFs z)

theorem hasDerivAt_compactSupportFamily_toLp
    (hs : MeasurableSet S) (μ : Measure X) (hμS : μ S ≠ ⊤)
    (F G : ℂ → X → ℂ)
    (hF : Continuous (fun p : ℂ × X => F p.1 p.2))
    (hG : Continuous (fun p : ℂ × X => G p.1 p.2))
    (hFs : ∀ z, Function.support (F z) ⊆ S)
    (hGs : ∀ z, Function.support (G z) ⊆ S)
    (hderiv : ∀ z x, HasDerivAt (fun w => F w x) (G z x) z) (z : ℂ) :
    HasDerivAt
      (fun w => (compactSupportFamily_memLp S hs μ hμS F hF hFs w).toLp (F w))
      ((compactSupportFamily_memLp S hs μ hμS G hG hGs z).toLp (G z)) z :=
  hasDerivAt_toLp_of_fixed_compact_support S hs μ hμS F G hF hG hFs hGs hderiv
    (compactSupportFamily_memLp S hs μ hμS F hF hFs)
    (compactSupportFamily_memLp S hs μ hμS G hG hGs) z

end
end ArtinMatthews
