module

public import ArtinMatthews.SourceAdelicIwasawa
public import ArtinMatthews.SourceArchMatrixHeight
public import ArtinMatthews.SourceKPAdelicCompactIntersection
public import ArtinMatthews.SourceKPFiniteMatrixTopology
public import ArtinMatthews.SourceKPIntegralMatrixValuation
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
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Continuity of the actual local right-translation constants. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain Topology Matrix SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

section NormedField
variable {F : Type*} [NormedField F]

lemma sourceKPEntryBound_continuous : Continuous (sourceKPEntryBound (F := F)) := by
  have he (i j : Fin 2) : Continuous (fun g : GL (Fin 2) F => ‖g i j‖) :=
    (Units.continuous_val.matrix_elem i j).norm
  exact continuous_const.max (((he 0 0).max (he 0 1)).max ((he 1 0).max (he 1 1)))

lemma sourceKPMatrixHeightRaw_continuous :
    Continuous (fun g : GL (Fin 2) F =>
      max 1 (4 * ‖(GeneralLinearGroup.det g : F)‖ * sourceKPEntryBound g⁻¹ ^ 2)) := by
  have hd : Continuous (fun g : GL (Fin 2) F => ‖(GeneralLinearGroup.det g : F)‖) :=
    (Units.continuous_val.comp GeneralLinearGroup.continuous_det).norm
  exact continuous_const.max ((continuous_const.mul hd).mul
    ((sourceKPEntryBound_continuous.comp continuous_inv).pow 2))

end NormedField

variable (K : Type) [Field K] [NumberField K]

lemma sourceKPFiniteMatrixHeightConstant_continuous (P : HeightOneSpectrum (𝓞 K)) :
    Continuous (sourceKPFiniteMatrixHeightConstant K P) := by
  classical
  have hcl : IsClopen {g : GL (Fin 2) (P.adicCompletion K) |
      SourceKPIntegralMatrix (sourceKPFiniteVal K P) g} := by
    change IsClopen (sourceKPIntegralGroup (sourceKPFiniteVal K P) : Set (GL (Fin 2) (P.adicCompletion K)))
    rw [← sourceKPIntegralMatrixMap_range_eq]
    exact ⟨(sourceKPIntegralMatrixGroup_isCompact K P).isClosed, sourceKPIntegralMatrixGroup_isOpen K P⟩
  unfold sourceKPFiniteMatrixHeightConstant
  apply Continuous.if ?_ continuous_const sourceKPMatrixHeightRaw_continuous
  intro g hg
  rw [hcl.frontier_eq] at hg
  exact False.elim hg

lemma sourceArchMatrixHeightConstant_continuous : Continuous sourceArchMatrixHeightConstant :=
  sourceKPMatrixHeightRaw_continuous

lemma sourceKPAdelicFiniteMatrix_continuous :
    Continuous (fun g : GL (Fin 2) 𝔸[K] => (sourceKPGL2ProductEquiv K g).2) := by
  change Continuous (GeneralLinearGroup.map (RingHom.snd (InfiniteAdeleRing K) 𝔸ᶠ[K]))
  exact continuous_snd.generalLinearGroup_map

lemma sourceKPAdelicBaseFiniteAt_continuous (P : HeightOneSpectrum (𝓞 K)) :
    Continuous (sourceKPAdelicBaseFiniteAt K P) :=
  (sourceKPAdeleMatrixAt_continuous K P).comp (sourceKPAdelicFiniteMatrix_continuous K)

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

lemma sourceKPArchComplexEquiv_continuous (v : InfinitePlace K) :
    Continuous (sourceKPArchComplexEquiv K hζ v) :=
  (AddMonoidHomClass.isometry_of_norm (sourceKPArchComplexEquiv K hζ v)
    (sourceKPArchComplexEquiv_norm K hζ v)).continuous

lemma sourceKPAdelicBaseComplexAt_continuous (v : InfinitePlace K) :
    Continuous (sourceKPAdelicBaseComplexAt K hζ v) := by
  let φ : 𝔸[K] →+* ℂ := (sourceKPArchComplexEquiv K hζ v).toRingHom.comp
    ((sourceArchAdeleEval K v).comp (sourceKPAdeleInfiniteProjection K))
  have hφ : Continuous φ := by
    change Continuous (fun x : 𝔸[K] => sourceKPArchComplexEquiv K hζ v (x.1 v))
    exact (sourceKPArchComplexEquiv_continuous K hζ v).comp
      ((continuous_apply v).comp continuous_fst)
  have he (g : GL (Fin 2) 𝔸[K]) :
      sourceKPAdelicBaseComplexAt K hζ v g = GeneralLinearGroup.map φ g := by
    apply GeneralLinearGroup.ext
    intro i j
    rfl
  exact hφ.generalLinearGroup_map.congr (fun g => (he g).symm)

end
end ArtinMatthews
