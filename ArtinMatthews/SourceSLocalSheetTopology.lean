module

public import ArtinMatthews.SourceSLocalSheetNorm


set_option backward.privateInPublic true
@[expose] public section

/-! Continuity of the literal retained coordinates, their product norm,
and the positive radius of the deleted complex coordinate. -/

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain
open scoped NumberField BigOperators Classical
noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (v : InfinitePlace K)

theorem continuous_sourceSheetOther : Continuous (sourceSheetOther S v) :=
  (continuous_pi fun w : {w : InfinitePlace K // w ≠ v} =>
    (continuous_apply w.val).comp continuous_fst).prodMk continuous_snd

theorem continuous_sourceSheetFill {X : Type*} [TopologicalSpace X]
    {u : X → v.Completionˣ} {y : X → SNormOneOtherUnits S v}
    (hu : Continuous u) (hy : Continuous y) :
    Continuous (fun x => sourceSheetFill S v (u x) (y x)) := by
  change Continuous (fun x => ((sourceSheetFill S v (u x) (y x)).1,(y x).2))
  refine (continuous_pi fun w => ?_).prodMk (continuous_snd.comp hy)
  by_cases hw : w = v
  · subst w
    exact hu.congr (fun x => (sourceSheetFill_chosen S v (u x) (y x)).symm)
  · let w' : {w : InfinitePlace K // w ≠ v} := ⟨w,hw⟩
    exact ((continuous_apply w').comp (continuous_fst.comp hy)).congr
      (fun x => (sourceSheetFill_other S v (u x) (y x) w').symm)

theorem continuous_sourceSheetOtherNorm : Continuous (sourceSheetOtherNorm S v) := by
  unfold sourceSheetOtherNorm
  apply Continuous.mul
  · apply continuous_finsetProd
    intro w _
    exact (Units.continuous_val.comp ((continuous_apply w).comp continuous_fst)).norm.pow _
  · apply continuous_finsetProd
    intro p _
    exact (Units.continuous_val.comp ((continuous_apply p).comp continuous_snd)).norm

theorem continuous_sourceSheetRadius : Continuous (sourceSheetRadius S v) := by
  have h := (continuous_sourceSheetOtherNorm S v).inv₀
    (fun y => (sourceSheetOtherNorm_pos S v y).ne')
  exact (Real.continuous_sqrt.comp h).congr (fun _ => rfl)

end
end ArtinMatthews.SourcePhysical
