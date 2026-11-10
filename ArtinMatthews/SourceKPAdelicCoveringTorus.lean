module

public import ArtinMatthews.SourceKPAdelicRationalCubeCharacter
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

/-! The full actual adelic covering torus and its rational-cube subgroup. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicCoveringTorus : Subgroup (SourceKPAdelicProjective K hζ) :=
  (sourceKPProjectiveDiagonalHom 𝔸[K]).range.comap (sourceKPAdelicProjectiveProjection K hζ)

theorem sourceKPAdelicCoveringTorus_center_mem (z : rootsOfUnity 3 K) :
    sourceKPAdelicProjectiveCenter K hζ z ∈ sourceKPAdelicCoveringTorus K hζ := by
  refine ⟨1, ?_⟩
  rw [map_one, sourceKPAdelicProjectiveCenter_projection_one]

theorem sourceKPAdelicCoveringTorus_diagonal_mem (a : IdeleGroup (𝓞 K) K) :
    sourceKPAdelicProjectiveDiagonalLift K hζ a ∈ sourceKPAdelicCoveringTorus K hζ :=
  ⟨a, (sourceKPAdelicProjectiveDiagonalLift_projection K hζ a).symm⟩

theorem sourceKPAdelicCoveringTorus_mem_iff (g : SourceKPAdelicProjective K hζ) :
    g ∈ sourceKPAdelicCoveringTorus K hζ ↔
      ∃ (z : rootsOfUnity 3 K) (a : IdeleGroup (𝓞 K) K),
        g = sourceKPAdelicProjectiveCenter K hζ z * sourceKPAdelicProjectiveDiagonalLift K hζ a := by
  constructor
  · rintro ⟨a, ha⟩
    have hk : g * (sourceKPAdelicProjectiveDiagonalLift K hζ a)⁻¹ ∈
        (sourceKPAdelicProjectiveProjection K hζ).ker := by
      change sourceKPAdelicProjectiveProjection K hζ
        (g * (sourceKPAdelicProjectiveDiagonalLift K hζ a)⁻¹) = 1
      rw [map_mul, map_inv, sourceKPAdelicProjectiveDiagonalLift_projection, ha, mul_inv_cancel]
    rw [← sourceKPAdelicProjective_exact K hζ] at hk
    obtain ⟨z, hz⟩ := hk
    refine ⟨z, a, ?_⟩
    rw [hz, inv_mul_cancel_right]
  · rintro ⟨z, a, rfl⟩
    exact (sourceKPAdelicCoveringTorus K hζ).mul_mem
      (sourceKPAdelicCoveringTorus_center_mem K hζ z)
      (sourceKPAdelicCoveringTorus_diagonal_mem K hζ a)

theorem sourceKPAdelicCubeTorus_le_coveringTorus :
    sourceKPAdelicCubeTorus K hζ ≤ sourceKPAdelicCoveringTorus K hζ := by
  rintro g ⟨p, rfl⟩
  exact ⟨p.2.val, (sourceKPAdelicCubeEmbedding_projection K hζ p).symm⟩

theorem sourceKPAdelicRationalCubeTorus_le_coveringTorus :
    sourceKPAdelicRationalCubeTorus K hζ ≤ sourceKPAdelicCoveringTorus K hζ := by
  rintro g ⟨p, rfl⟩
  apply (sourceKPAdelicCoveringTorus K hζ).mul_mem
  · exact sourceKPAdelicCubeTorus_le_coveringTorus K hζ p.1.property
  · change sourceKPAdelicProjectiveRationalLift K hζ (sourceKPProjectiveDiagonalHom K p.2) ∈ _
    rw [sourceKPAdelicProjectiveRationalLift_diagonal]
    exact sourceKPAdelicCoveringTorus_diagonal_mem K hζ _

end
end ArtinMatthews
