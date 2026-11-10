module

public import ArtinMatthews.SpectralCompactResolventMatchedEnergy
public import ArtinMatthews.SpectralEisensteinCriticalEnergy
public import ArtinMatthews.SpectralEisensteinReflectionScattering
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The actual Eisenstein family has the same full energy pencil at any
larger cutoff. It therefore supplies the exact scattering relation for
the arbitrary-height matching matrix. -/
noncomputable section
open Matrix
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

theorem gamma0CuspEisensteinMatchedTruncatedEnergy_mem_atHeight (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 0<Y) (hmin : gamma0EisensteinMatchingHeight N≤Y) (a : SL(2,ℤ)) (s : ℂ) :
    gamma0CuspEisensteinMatchedTruncatedEnergy N a s∈(gamma0TruncatedFormData N Y hY).subspace := by
  let u : gamma0TruncatedMeanZeroEnergy N (gamma0EisensteinMatchingHeight N)
      (gamma0EisensteinMatchingHeight_pos N) :=
    ⟨gamma0CuspEisensteinMatchedTruncatedEnergy N a s,
      gamma0CuspEisensteinMatchedTruncatedEnergy_mem N a s⟩
  apply (mem_gamma0TruncatedMeanZeroEnergy_iff N Y hY _).mpr
  intro r
  exact gamma0TruncatedMeanZeroEnergy_constantTerm_zero N _ _ u r hmin

theorem gamma0CuspEisensteinMatchedTruncatedEnergy_eq_atHeight_response (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 0<Y) (hmin : gamma0EisensteinMatchingHeight N≤Y) (a : SL(2,ℤ)) (s : ℂ)
    (hs : gamma0EisensteinMatchingRegular N s) (hYs : gamma0HeightMatchingRegular N Y hY s) :
    gamma0CuspEisensteinMatchedTruncatedEnergy N a s=
      gamma0HeightMatchingResponse N Y hY s (gamma0EisensteinMatchedForcing N a s) :=
  gamma0HeightMatchingResponse_unique_of_pencil N Y hY s hYs.1 _ _
    (gamma0CuspEisensteinMatchedTruncatedEnergy_mem_atHeight N Y hY hmin a s)
    (gamma0CuspEisensteinMatchedTruncatedEnergy_pencil_regular N a s hs)

theorem gamma0HeightMatchingMatrix_scattering_regular (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 0<Y) (hmin : gamma0EisensteinMatchingHeight N≤Y) (s : ℂ)
    (hs : gamma0EisensteinMatchingRegular N s) (hYs : gamma0HeightMatchingRegular N Y hY s) :
    gamma0HeightMatchingMatrix N Y hY s * gamma0CuspScatteringMatrix N s =
      -gamma0HeightMatchingMatrix N Y hY (1-s) := by
  ext i j
  let r := gamma0EisensteinCuspClassRepresentative N
  let L := innerSL ℂ (gamma0HeightOutgoingDefect N Y hY 2 i)
  let D := gamma0HeightMatchingDefect N Y hY s
  let c := gamma0EisensteinMatchedCoefficient N (r j) s
  have hp := gamma0CuspEisensteinMatchedTruncatedEnergy_pencil_regular N (r j) s hs
  rw [gamma0CuspEisensteinMatchedTruncatedEnergy_eq_atHeight_response N Y hY hmin (r j) s hs hYs] at hp
  have hD : D (gamma0EisensteinMatchedForcing N (r j) s)=0 := sub_eq_zero.mpr hp
  have hd := congrArg L hD
  change L (D (-gamma0CuspChannelForcing N s j-∑ k,c k • gamma0CuspChannelForcing N (1-s) k))=L 0 at hd
  simp only [map_sub,map_neg,map_sum,map_smul,map_zero,smul_eq_mul] at hd
  have hq : (1:ℂ)-(1-s)=s := eisensteinParameterReflect_involutive s
  have hR : gamma0HeightMatchingMatrix N Y hY (1-s) i j = L (D (gamma0CuspChannelForcing N s j)) := by
    change L (gamma0HeightMatchingDefect N Y hY (1-s) (gamma0CuspChannelForcing N (1-(1-s)) j))=_
    rw [gamma0HeightMatchingDefect_reflect,hq]
  rw [Matrix.mul_apply,Matrix.neg_apply,hR]
  calc
    (∑ k,gamma0HeightMatchingMatrix N Y hY s i k * gamma0CuspScatteringMatrix N s k j) =
        ∑ k,c k * L (D (gamma0CuspChannelForcing N (1-s) k)) := by
      apply Finset.sum_congr rfl
      intro k _
      change L (D (gamma0CuspChannelForcing N (1-s) k)) * c k=_
      rw [mul_comm]
    _ = _ := (sub_eq_zero.mp hd).symm

theorem gamma0CompactForcingMatchedCoefficient_reflection_regular (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (A : Gamma0CompactResolventCutoff N ψ) (s : ℂ)
    (hs : gamma0EisensteinMatchingRegular N s)
    (hYs : gamma0HeightMatchingRegular N A.height A.pos s)
    (hYq : gamma0HeightMatchingRegular N A.height A.pos (1-s)) :
    gamma0CompactForcingMatchedCoefficient N ψ A s =
      -((gamma0CuspScatteringMatrix N s).mulVec (gamma0CompactForcingMatchedCoefficient N ψ A (1-s))) := by
  let Y := A.height
  let hY := A.pos
  let F := gamma0SmoothSeedMass N ψ
  let X := gamma0HeightMatchingMatrix N Y hY s
  let Z := gamma0HeightMatchingMatrix N Y hY (1-s)
  let M := gamma0CuspScatteringMatrix N s
  let c := gamma0CompactForcingMatchedCoefficient N ψ A s
  let b := gamma0CompactForcingMatchedCoefficient N ψ A (1-s)
  have hc : X.mulVec c=gamma0HeightMatchingRhs N Y hY s F :=
    gamma0HeightMatchingCoefficient_mulVec N Y hY s F hYs.2
  have hb : Z.mulVec b=gamma0HeightMatchingRhs N Y hY (1-s) F :=
    gamma0HeightMatchingCoefficient_mulVec N Y hY (1-s) F hYq.2
  have he : gamma0HeightMatchingRhs N Y hY (1-s) F=gamma0HeightMatchingRhs N Y hY s F := by
    funext i
    unfold gamma0HeightMatchingRhs
    rw [gamma0HeightMatchingDefect_reflect]
  have hM : X*M=-Z := gamma0HeightMatchingMatrix_scattering_regular N Y hY A.matching_le s hs hYs
  have hu : IsUnit X := (Matrix.isUnit_iff_isUnit_det X).mpr (isUnit_iff_ne_zero.mpr hYs.2)
  change c=-M.mulVec b
  apply Matrix.mulVec_injective_iff_isUnit.mpr hu
  rw [Matrix.mulVec_neg,Matrix.mulVec_mulVec,hM,Matrix.neg_mulVec,neg_neg,hb,he]
  exact hc

end ArtinMatthews
