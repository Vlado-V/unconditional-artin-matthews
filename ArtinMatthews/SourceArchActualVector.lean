module

public import ArtinMatthews.SourceArchCompletedJacquet
public import ArtinMatthews.SourceArchBorelInduction
public import ArtinMatthews.SourceArchAdelicEmbedding
public import ArtinMatthews.SourceSLocalOtherTensor
public import ArtinMatthews.SourceThetaBesselSchlafli
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The nonzero actual archimedean Jacquet vector and its injection
into the existing adelic projective group. -/
namespace ArtinMatthews.SourceArchJacquet

open NumberField NumberField.InfinitePlace Matrix
open ArtinMatthews.SourceReflection
open scoped MatrixGroups
noncomputable section

theorem sourceArchBorel_eq_map :
    sourceArchBorel = (sourceGL2NormalizedBorel ℂ).map ProjGenLinGroup.mk := by
  ext g
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b.val, b.property, hb⟩
  · rintro ⟨b, hb, he⟩
    exact ⟨⟨b, hb⟩, he⟩

theorem sourceArchSphericalWhittaker_ne_zero (y : ℂˣ) :
    sourceArchSphericalWhittaker y ≠ 0 := by
  intro h
  have hp := sourceThetaBesselProfile_pos
    (by positivity : 0 < 4 * Real.pi) (sq_pos_of_pos (norm_pos_iff.mpr y.ne_zero))
  rw [sourceThetaBesselProfile_eq_weightedWhittaker, h, mul_zero, zero_div, Complex.zero_re] at hp
  exact lt_irrefl _ hp

variable (F : Type) [Field F] [NumberField F]

def sourceArchComplexToAdelic {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (v : InfinitePlace F) (hv : IsComplex v) : PGL(2, ℂ) →* SourceKPAdelicProjective F hζ :=
  (sourceArchLocalToAdelic F hζ v).comp
    (ProjGenLinGroup.map (sourceArchCompletionEquiv F v hv).symm.toRingHom)

theorem sourceArchComplexToAdelic_injective {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (v : InfinitePlace F) (hv : IsComplex v) :
    Function.Injective (sourceArchComplexToAdelic F hζ v hv) := by
  apply (sourceArchLocalToAdelic_injective F hζ v).comp
  apply Function.LeftInverse.injective
    (g := ProjGenLinGroup.map (sourceArchCompletionEquiv F v hv).toRingHom)
  intro g
  rw [← MonoidHom.comp_apply, ← ProjGenLinGroup.map_comp,
    RingEquiv.toRingHom_comp_symm_toRingHom, ProjGenLinGroup.map_id]
  rfl

theorem sourceArchCompletedWhittaker_ne_zero (v : InfinitePlace F) (hv : IsComplex v)
    (y : v.Completionˣ) : sourceArchCompletedWhittaker F v hv y ≠ 0 := by
  rw [sourceArchCompletedWhittaker_eq]
  exact sourceArchSphericalWhittaker_ne_zero _

theorem sourceArchCompletedWhittaker_sourceNorm (v : InfinitePlace F) (hv : IsComplex v)
    (y : v.Completionˣ) :
    sourceThetaBesselProfile (4 * Real.pi) (SourcePhysical.sourceSheetArchNorm v y) =
      (Real.sqrt (SourcePhysical.sourceSheetArchNorm v y) : ℂ) *
        sourceArchCompletedWhittaker F v hv y / (sourceArchJacquetConstant : ℂ) :=
  sourceArchCompletedWhittaker_sourceProfile F v hv y

end
end ArtinMatthews.SourceArchJacquet
