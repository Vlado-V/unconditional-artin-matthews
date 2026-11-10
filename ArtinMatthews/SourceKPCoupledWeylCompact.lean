module

public import ArtinMatthews.SourceKPCoupledWeylProductLift
public import ArtinMatthews.SourceKPAdelicCompactSplit
public import ArtinMatthews.SourceKPAdelicWeyl
public import ArtinMatthews.SourceArchIntertwinerProduct
public import ArtinMatthews.SourceKPIntegralGeneration
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

/-! The actual global Weyl lift times the finite wild Weyl word is
the phase-one deep compact lift. Every wild matrix component is identity. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup SourceArchJacquet
open scoped NumberField AdeleRing MatrixGroups Classical
noncomputable section

theorem sourceKPCoupledArchWeyl_unitary :
    (sourceGL2Weyl : GL (Fin 2) ℂ) ∈ sourceArchUnitaryGL.range := by
  let w : GL (Fin 2) ℂ := sourceGL2Weyl
  let a : Matrix (Fin 2) (Fin 2) ℂ := w.val
  have hs : star a = a := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [a,w,sourceGL2Weyl,Matrix.star_apply]
  have ha : a ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, hs]
    exact congrArg (fun m : GL (Fin 2) ℂ => m.val) sourceKPCoupledWeyl_matrix_square
  exact ⟨⟨a,ha⟩, Units.ext rfl⟩

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPCoupledCancelledWeylMatrix : sourceKPCoupledWeylMatrices K :=
  sourceKPCoupledFullWeylMatrix K * sourceKPCoupledWeylMatrixProduct K (sixthWildPrimes K)

theorem sourceKPCoupledCancelledWeylMatrix_at (P : HeightOneSpectrum (𝓞 K)) :
    sourceKPAdeleMatrixAt K P (sourceKPCoupledCancelledWeylMatrix K).val =
      if P ∈ sixthWildPrimes K then 1 else sourceGL2Weyl := by
  change sourceKPAdeleMatrixAt K P (sourceKPWeylMatrix 𝔸ᶠ[K] *
    (sourceKPCoupledWeylMatrixProduct K (sixthWildPrimes K)).val) = _
  rw [map_mul, sourceKPAdeleMatrixAt_weyl, sourceKPCoupledWeylMatrixProduct_at]
  split_ifs
  · exact sourceKPCoupledWeyl_matrix_square
  · exact mul_one _

theorem sourceKPCoupledWildWeyl_cancel_mem :
    sourceKPAdelicProjectiveWeyl K hζ * sourceKPCoupledWildWeyl K hζ ∈ sourceKPAdelicDeepCompact K hζ := by
  let w := sourceKPWeylMatrix (InfiniteAdeleRing K)
  let a := sourceKPCoupledCancelledWeylMatrix K
  let g := (sourceKPGL2ProductEquiv K).symm (w,a.val)
  have hg : sourceKPGL2ProductEquiv K g = (w,a.val) := (sourceKPGL2ProductEquiv K).apply_symm_apply _
  have hf (P : HeightOneSpectrum (𝓞 K)) : sourceKPAdelicBaseFiniteAt K P g = sourceKPAdeleMatrixAt K P a.val := by
    change sourceKPAdeleMatrixAt K P (sourceKPGL2ProductEquiv K g).2 = _
    rw [hg]
  have ha (v : InfinitePlace K) : sourceKPAdelicBaseComplexAt K hζ v g = sourceGL2Weyl := by
    change sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K (sourceKPGL2ProductEquiv K g).1 v) = _
    rw [hg]
    change GeneralLinearGroup.map ((sourceKPArchComplexEquiv K hζ v).toRingHom.comp
      (sourceArchAdeleEval K v)) (sourceKPWeylMatrix (InfiniteAdeleRing K)) = _
    rw [sourceKPWeylMatrix_map, sourceKPWeylMatrix_field]
  have hgK : g ∈ sourceKPAdelicDeepCompactMatrix K hζ := by
    refine ⟨⟨?_, fun v => (ha v).symm ▸ sourceKPCoupledArchWeyl_unitary⟩, ?_⟩
    · intro P
      rw [hf, sourceKPCoupledCancelledWeylMatrix_at]
      split_ifs
      · exact sourceKPIntegralMatrix_one _
      · exact sourceKPIntegralMatrix_weyl _
    · intro P hP
      rw [hf, sourceKPCoupledCancelledWeylMatrix_at, ite_eq_left ((mem_sixthWildPrimes P).mpr hP)]
      exact (sourceKPDeepLocalBase K P).range.one_mem
  refine ⟨⟨g,hgK⟩, ?_⟩
  apply Prod.ext
  · change ProjGenLinGroup.mk (sourceKPGL2ProductEquiv K g).1 =
      (sourceKPAdelicProjectiveWeyl K hζ).1 * (sourceKPCoupledWildWeyl K hζ).1
    rw [hg, sourceKPCoupledWildWeyl_arch, mul_one, sourceKPAdelicWeyl_arch_component]
  · change sourceKPFiniteAdeleProjectiveLift K hζ (sourceKPGL2ProductEquiv K g).2 =
      (sourceKPAdelicProjectiveWeyl K hζ).2 * (sourceKPCoupledWildWeyl K hζ).2
    rw [hg, sourceKPCoupledWildWeyl_lift]
    change sourceKPCoupledWeylMatrixLift K hζ
      (sourceKPCoupledFullWeylMatrix K * sourceKPCoupledWeylMatrixProduct K (sixthWildPrimes K)) =
      sourceKPFiniteAdeleProjectiveRationalLift K hζ (ProjGenLinGroup.mk (sourceKPWeylMatrix K)) *
        sourceKPCoupledWeylMatrixLift K hζ (sourceKPCoupledWeylMatrixProduct K (sixthWildPrimes K))
    rw [map_mul, sourceKPFiniteAdeleProjectiveRationalLift_weyl]
    rfl

end
end ArtinMatthews
