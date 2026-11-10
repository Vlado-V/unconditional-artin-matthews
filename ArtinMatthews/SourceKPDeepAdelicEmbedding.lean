module

public import ArtinMatthews.SourceKPDeepLowerSupport
public import ArtinMatthews.SourceKPAdelicCompactSplit
public import ArtinMatthews.SourceKPAdeleLocalCover
public import ArtinMatthews.SourceKPDeepPhase
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

/-! A genuine one-place deep matrix belongs to the constructed
global compact subgroup, with exactly the prescribed covering lift. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))

local notation "O" => P.adicCompletionIntegers K
local notation "L" => P.adicCompletion K
local notation "D₀" => sourceKPDeepIntegralGroup K P

def sourceKPFullSingleMatrix : GL (Fin 2) L →* GL (Fin 2) 𝔸[K] :=
  (sourceKPGL2ProductEquiv K).symm.toMonoidHom.comp
    ((1 : GL (Fin 2) L →* GL (Fin 2) (InfiniteAdeleRing K)).prod (sourceKPAdeleSingleMatrix K P))

theorem sourceKPFullSingleMatrix_components (g : GL (Fin 2) L) :
    sourceKPGL2ProductEquiv K (sourceKPFullSingleMatrix K P g) =
      (1, sourceKPAdeleSingleMatrix K P g) :=
  (sourceKPGL2ProductEquiv K).apply_symm_apply _

theorem sourceKPFullSingleMatrix_same (g : GL (Fin 2) L) :
    sourceKPAdelicBaseFiniteAt K P (sourceKPFullSingleMatrix K P g) = g := by
  change sourceKPAdeleMatrixAt K P ((sourceKPGL2ProductEquiv K (sourceKPFullSingleMatrix K P g)).2) = g
  rw [sourceKPFullSingleMatrix_components, sourceKPAdeleSingleMatrix_same]

theorem sourceKPFullSingleMatrix_other (Q : HeightOneSpectrum (𝓞 K)) (hQP : Q ≠ P)
    (g : GL (Fin 2) L) :
    sourceKPAdelicBaseFiniteAt K Q (sourceKPFullSingleMatrix K P g) = 1 := by
  change sourceKPAdeleMatrixAt K Q ((sourceKPGL2ProductEquiv K (sourceKPFullSingleMatrix K P g)).2) = 1
  rw [sourceKPFullSingleMatrix_components, sourceKPAdeleSingleMatrix_other K P Q hQP]

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPFullSingleMatrix_complex (v : InfinitePlace K) (g : GL (Fin 2) L) :
    sourceKPAdelicBaseComplexAt K hζ v (sourceKPFullSingleMatrix K P g) = 1 := by
  change sourceKPArchMatrixComplexEquiv K hζ v
    (sourceArchGLPiEquiv K (sourceKPGL2ProductEquiv K (sourceKPFullSingleMatrix K P g)).1 v) = 1
  rw [sourceKPFullSingleMatrix_components, map_one]
  exact map_one _

theorem sourceKPDeepLocalBase_integral (g : D₀) :
    SourceKPIntegralMatrix (sourceKPFiniteVal K P) (sourceKPDeepLocalBase K P g) := by
  refine ⟨?_, ?_⟩
  · intro i j
    exact (g.val i j).property
  · change sourceKPFiniteVal K P
      ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap O L) g.val) : Lˣ) : L) = 1
    rw [GeneralLinearGroup.map_det]
    exact Valuation.Integers.one_of_isUnit' (v := sourceKPFiniteVal K P)
      (Units.isUnit (GeneralLinearGroup.det g.val)) (fun x : O => x.property)

def sourceKPDeepAdelicMatrix (g : D₀) : sourceKPAdelicDeepCompactMatrix K hζ :=
  ⟨sourceKPFullSingleMatrix K P (sourceKPDeepLocalBase K P g), by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro Q
      by_cases hQP : Q = P
      · subst Q
        rw [sourceKPFullSingleMatrix_same]
        exact sourceKPDeepLocalBase_integral K P g
      · rw [sourceKPFullSingleMatrix_other K P Q hQP]
        exact sourceKPIntegralMatrix_one _
    · intro v
      rw [sourceKPFullSingleMatrix_complex]
      exact sourceArchUnitaryGL.range.one_mem
    · intro Q _
      by_cases hQP : Q = P
      · subst Q
        rw [sourceKPFullSingleMatrix_same]
        exact ⟨g, rfl⟩
      · rw [sourceKPFullSingleMatrix_other K P Q hQP]
        exact (sourceKPDeepLocalBase K Q).range.one_mem⟩

theorem sourceKPDeepAdelicMatrix_lift (g : D₀) :
    sourceKPAdelicDeepCompactLift K hζ (sourceKPDeepAdelicMatrix K P hζ g) =
      sourceKPAdelicLocalProjective K hζ P (sourceKPDeepProjectiveSection K P hζ g) := by
  change (ProjGenLinGroup.mk (sourceKPGL2ProductEquiv K
      (sourceKPFullSingleMatrix K P (sourceKPDeepLocalBase K P g))).1,
    sourceKPFiniteAdeleProjectiveLift K hζ (sourceKPGL2ProductEquiv K
      (sourceKPFullSingleMatrix K P (sourceKPDeepLocalBase K P g))).2) = _
  rw [sourceKPFullSingleMatrix_components]
  apply Prod.ext
  · exact map_one _
  · change sourceKPFiniteAdeleProjectiveMk K hζ
      ⟨1, sourceKPAdeleSingleMatrix K P (sourceKPDeepLocalBase K P g)⟩ =
      sourceKPFiniteAdeleProjectiveMk K hζ
        (sourceKPAdeleLocalCover K hζ P (sourceKPDeepLocalSection K P hζ g))
    apply congrArg (sourceKPFiniteAdeleProjectiveMk K hζ)
    apply SourceKPFiniteAdeleCover.ext
    · change 1 = (sourceKPRootsTransport K hζ P).symm
        (1 / sourceKPFinitePhase K hζ P (sourceKPDeepLocalBase K P g))
      rw [sourceKPFinitePhase_deep K hζ P _ (sourceKPDeepLocalBase_cubeData K P g),
        div_one, map_one]
    · rfl

theorem sourceKPDeepAdelicMatrix_mem (g : D₀) :
    sourceKPAdelicLocalProjective K hζ P (sourceKPDeepProjectiveSection K P hζ g) ∈
      sourceKPAdelicDeepCompact K hζ :=
  ⟨sourceKPDeepAdelicMatrix K P hζ g, sourceKPDeepAdelicMatrix_lift K P hζ g⟩

end
end ArtinMatthews
