module

public import ArtinMatthews.SourceKPAdelicProjectiveHeight
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

/-! The finite positive rational-orbit height of the actual adelic
cubic cover. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicOrbitHeight (q : SourceKPAdelicProjective K hζ) : ℝ :=
  sSup (Set.range (fun γ : PGL(2,K) =>
    sourceKPAdelicCoverHeight K hζ (sourceKPAdelicProjectiveRationalLift K hζ γ*q)))

theorem sourceKPAdelicOrbitHeight_range_bddAbove (q : SourceKPAdelicProjective K hζ) :
    BddAbove (Set.range (fun γ : PGL(2,K) =>
      sourceKPAdelicCoverHeight K hζ (sourceKPAdelicProjectiveRationalLift K hζ γ*q))) := by
  obtain ⟨g,hg⟩ := ProjGenLinGroup.mk_surjective (sourceKPAdelicProjectiveProjection K hζ q)
  refine ⟨max (sourceKPAdelicHeight K hζ g) (sourceKPAdelicHeightConstant K hζ g), ?_⟩
  rintro _ ⟨γ,rfl⟩
  dsimp only
  unfold sourceKPAdelicCoverHeight
  rw [map_mul, sourceKPAdelicProjectiveRationalLift_projection, ← hg]
  exact sourceKPAdelicHeightOnProjective_rational_bound K hζ γ g

theorem sourceKPAdelicCoverHeight_le_orbit (q : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicCoverHeight K hζ q ≤ sourceKPAdelicOrbitHeight K hζ q := by
  have h := le_csSup (sourceKPAdelicOrbitHeight_range_bddAbove K hζ q)
    (Set.mem_range_self (1 : PGL(2,K)))
  simpa only [sourceKPAdelicOrbitHeight, map_one, one_mul] using h

theorem sourceKPAdelicOrbitHeight_pos (q : SourceKPAdelicProjective K hζ) :
    0 < sourceKPAdelicOrbitHeight K hζ q :=
  (sourceKPAdelicCoverHeight_pos K hζ q).trans_le (sourceKPAdelicCoverHeight_le_orbit K hζ q)

theorem sourceKPAdelicOrbitHeight_le (q : SourceKPAdelicProjective K hζ)
    (g : GL (Fin 2) 𝔸[K]) (hg : sourceKPAdelicProjectiveProjection K hζ q = ProjGenLinGroup.mk g) :
    sourceKPAdelicOrbitHeight K hζ q ≤
      max (sourceKPAdelicHeight K hζ g) (sourceKPAdelicHeightConstant K hζ g) := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨γ,rfl⟩
  dsimp only
  unfold sourceKPAdelicCoverHeight
  rw [map_mul, sourceKPAdelicProjectiveRationalLift_projection, hg]
  exact sourceKPAdelicHeightOnProjective_rational_bound K hζ γ g

theorem sourceKPAdelicOrbitHeight_rational (q : SourceKPAdelicProjective K hζ) (δ : PGL(2,K)) :
    sourceKPAdelicOrbitHeight K hζ (sourceKPAdelicProjectiveRationalLift K hζ δ*q) =
      sourceKPAdelicOrbitHeight K hζ q := by
  apply congrArg sSup
  ext x
  constructor
  · rintro ⟨γ,rfl⟩
    refine ⟨γ*δ, ?_⟩
    dsimp only
    rw [map_mul, mul_assoc]
  · rintro ⟨γ,rfl⟩
    refine ⟨γ*δ⁻¹, ?_⟩
    dsimp only
    rw [map_mul, map_inv]
    congr 1
    group

theorem sourceKPAdelicOrbitHeight_right_deep (q : SourceKPAdelicProjective K hζ)
    (k : sourceKPAdelicDeepCompact K hζ) :
    sourceKPAdelicOrbitHeight K hζ (q*k.val) = sourceKPAdelicOrbitHeight K hζ q := by
  apply congrArg sSup
  apply congrArg Set.range
  funext γ
  rw [← mul_assoc, sourceKPAdelicCoverHeight_right_deep]

end
end ArtinMatthews
