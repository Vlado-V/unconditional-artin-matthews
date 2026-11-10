module

public import ArtinMatthews.SourceKPAdelicCompactSection
public import ArtinMatthews.SourceKPAdelicHeight
public import ArtinMatthews.SourceKPAdelicFlatTorus
public import ArtinMatthews.SourceKPAdelicHeightFactor
public import ArtinMatthews.SourceKPAdelicSectionBound
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

/-! The actual global section is flat in the spectral parameter.
Its height factor is separated from its parameter-zero coefficient. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicBorelCompact_height
    (b : sourceKPAdelicCoveringBorel K hζ) (k : sourceKPAdelicDeepCompact K hζ)
    (g : GL (Fin 2) 𝔸[K])
    (hp : sourceKPAdelicProjectiveProjection K hζ (b.val*k.val) = ProjGenLinGroup.mk g) :
    sourceKPAdelicHeight K hζ g = sourceKPIdeleAbsoluteNorm K
      (sourceKPAdelicTorusIdele K hζ (sourceKPAdelicBorelTorusProjection K hζ b)) := by
  obtain ⟨m,hm,hmp,hmd⟩ := sourceKPAdelicCoveringBorel_matrix K hζ b
  obtain ⟨k₀,hk₀⟩ := k.property
  have hg : ProjGenLinGroup.mk g = ProjGenLinGroup.mk (m*k₀.val) := by
    rw [← hp,map_mul,hmp,← hk₀,sourceKPAdelicDeepCompactLift_projection,map_mul]
  rw [sourceKPAdelicHeight_projective K hζ g (m*k₀.val) hg]
  rw [sourceKPAdelicHeight_factor K hζ (m*k₀.val) m k₀.val 1 hm k₀.property.1
    (by rw [map_one,mul_one]),hmd]

theorem sourceKPAdelicCompactScalar_flat (s : ℂ) (q : SourceKPAdelicProjective K hζ)
    (g : GL (Fin 2) 𝔸[K]) (hp : sourceKPAdelicProjectiveProjection K hζ q = ProjGenLinGroup.mk g) :
    sourceKPAdelicCompactScalar K hζ s q =
      Complex.exp (s * (Real.log (sourceKPAdelicHeight K hζ g) : ℂ)) *
        sourceKPAdelicCompactScalar K hζ 0 q := by
  by_cases hq : sourceCompactInducedFactorable (sourceKPAdelicCoveringBorel K hζ)
      (sourceKPAdelicDeepCompact K hζ) q
  · obtain ⟨b,k,he⟩ := hq
    have hh := sourceKPAdelicBorelCompact_height K hζ b k g (he ▸ hp)
    unfold sourceKPAdelicCompactScalar
    rw [sourceKPAdelicCompactSection_factor K hζ s q b k he,
      sourceKPAdelicCompactSection_factor K hζ 0 q b k he,
      sourceKPAdelicNormalizedBorelVector_flat,sourceKPIdeleComplexNorm_coe,hh]
  · rw [sourceKPAdelicCompactScalar_zero K hζ s q hq,
      sourceKPAdelicCompactScalar_zero K hζ 0 q hq,mul_zero]

theorem sourceKPAdelicCompactScalar_norm_flat (s : ℂ) (q : SourceKPAdelicProjective K hζ)
    (g : GL (Fin 2) 𝔸[K]) (hp : sourceKPAdelicProjectiveProjection K hζ q = ProjGenLinGroup.mk g) :
    ‖sourceKPAdelicCompactScalar K hζ s q‖ =
      Real.exp (s.re * Real.log (sourceKPAdelicHeight K hζ g)) *
        ‖sourceKPAdelicCompactScalar K hζ 0 q‖ := by
  rw [sourceKPAdelicCompactScalar_flat K hζ s q g hp,norm_mul,Complex.norm_exp]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]

end
end ArtinMatthews
