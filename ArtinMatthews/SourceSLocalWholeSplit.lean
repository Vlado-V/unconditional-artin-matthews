module

public import ArtinMatthews.SourceSLocalSheetTopology


set_option backward.privateInPublic true
@[expose] public section

/-! Extract the chosen infinite unit from the whole product. All
remaining infinite units and finite S units keep their original coordinates. -/

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain
open scoped NumberField
noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (v : InfinitePlace K)

def sourceSWholeToSheet (x : SWholeUnits K S) : v.Completionˣ × SNormOneOtherUnits S v :=
  (x.1 v, sourceSheetOther S v x)

def sourceSWholeSheetSplit : SWholeUnits K S ≃ₜ* v.Completionˣ × SNormOneOtherUnits S v where
  toFun := sourceSWholeToSheet S v
  invFun y := sourceSheetFill S v y.1 y.2
  left_inv := sourceSheetFill_reconstruct S v
  right_inv y := Prod.ext (sourceSheetFill_chosen S v y.1 y.2) (sourceSheetOther_fill S v y.1 y.2)
  map_mul' x y := Prod.ext rfl (sourceSheetOther_mul S v x y)
  continuous_toFun := ((continuous_apply v).comp continuous_fst).prodMk (continuous_sourceSheetOther S v)
  continuous_invFun := continuous_sourceSheetFill S v continuous_fst continuous_snd

@[simp] theorem sourceSWholeSheetSplit_apply (x : SWholeUnits K S) :
    sourceSWholeSheetSplit S v x = (x.1 v, sourceSheetOther S v x) := rfl

@[simp] theorem sourceSWholeSheetSplit_symm_apply (y : v.Completionˣ × SNormOneOtherUnits S v) :
    (sourceSWholeSheetSplit S v).symm y = sourceSheetFill S v y.1 y.2 := rfl

end
end ArtinMatthews.SourcePhysical
