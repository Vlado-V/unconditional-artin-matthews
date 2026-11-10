module

public import ArtinMatthews.SourceKPArchComponent
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

/-! Compact finite matrix representatives for the actual rational stabilizer
of any finite-level coset. -/
namespace ArtinMatthews
open NumberField Matrix Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPFiniteLevelLift_projection (k : sourceKPFiniteDeepMatrixGroup K) :
    sourceKPFiniteAdeleProjectiveProjection K hζ (sourceKPFiniteLevelLift K hζ k) =
      ProjGenLinGroup.mk k.val := by
  have h := congrArg (fun q => (sourceKPAdelicProjectiveProductEquiv K q).2)
    (sourceKPFiniteDeepCoverLift_projection K hζ k)
  rw [sourceKPAdelicProjectiveProjection_product] at h
  change sourceKPFiniteAdeleProjectiveProjection K hζ (sourceKPFiniteLevelLift K hζ k) =
    ProjGenLinGroup.mk ((sourceKPGL2ProductEquiv K (sourceKPFiniteMatrixEmbedding K k.val)).2) at h
  rw [sourceKPFiniteMatrixEmbedding_product] at h
  exact h

theorem sourceKPRationalFiniteMap_projection (γ : PGL(2, K)) :
    sourceKPFiniteAdeleProjectiveProjection K hζ (sourceKPRationalFiniteMap K hζ γ) =
      ProjGenLinGroup.map (algebraMap K 𝔸ᶠ[K]) γ :=
  sourceKPFiniteAdeleProjectiveRationalLift_projection K hζ γ

theorem sourceKPRationalFiniteStabilizer_compact_representatives
    (b : SourceKPFiniteLevelFiber K hζ) :
    ∃ C : Set (GL (Fin 2) 𝔸ᶠ[K]), IsCompact C ∧
      ∀ γ ∈ sourceKPRationalFiniteStabilizer K hζ b,
        ∃ g ∈ C, ProjGenLinGroup.map (algebraMap K 𝔸ᶠ[K]) γ = ProjGenLinGroup.mk g := by
  induction b using Quotient.inductionOn with
  | _ b =>
    obtain ⟨t, ht⟩ := ProjGenLinGroup.mk_surjective
      (sourceKPFiniteAdeleProjectiveProjection K hζ b)
    let f : GL (Fin 2) 𝔸ᶠ[K] → GL (Fin 2) 𝔸ᶠ[K] := fun k => t * k * t⁻¹
    refine ⟨f '' (sourceKPFiniteDeepMatrixGroup K : Set (GL (Fin 2) 𝔸ᶠ[K])),
      (sourceKPFiniteDeepMatrixGroup_isCompact K).image
        ((continuous_const.mul continuous_id).mul continuous_const), ?_⟩
    intro γ hγ
    have hfix : (QuotientGroup.mk (sourceKPRationalFiniteMap K hζ γ * b) :
        SourceKPFiniteLevelFiber K hζ) = QuotientGroup.mk b := hγ
    have hmem := QuotientGroup.eq.mp hfix.symm
    obtain ⟨k, hk⟩ := hmem
    have hEq : sourceKPRationalFiniteMap K hζ γ = b * sourceKPFiniteLevelLift K hζ k * b⁻¹ := by
      rw [hk]
      group
    refine ⟨f k.val, Set.mem_image_of_mem f k.property, ?_⟩
    rw [← sourceKPRationalFiniteMap_projection K hζ, hEq, map_mul, map_mul, map_inv,
      sourceKPFiniteLevelLift_projection, ← ht]
    simp only [f, map_mul, map_inv]

end
end ArtinMatthews
