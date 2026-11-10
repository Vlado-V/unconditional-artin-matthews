module

public import ArtinMatthews.SourceKPLocalCompactFlatTorus
public import ArtinMatthews.SourceKPLocalBorelEmbedding
public import ArtinMatthews.SourceKPLocalCompactGroup
public import ArtinMatthews.SourceKPAdelicExceptionalLocalNorm
public import ArtinMatthews.SourceKPAdelicFlatTorus
public import ArtinMatthews.SourceKPLocalBorelRelations
public import ArtinMatthews.SourceKPLocalCompactBorel
public import ArtinMatthews.SourceKPLocalTorusCharacter
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

/-! The local Borel acts on the fixed adelic torus value space with
the exact norm twist. Its restriction to the genuine compact
intersection has trivial twist at every finite place. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

local notation "L" => P.adicCompletion K
local notation "B" => SourceFiniteKPProjectiveBorel K hζ P
local notation "C" => sourceKPLocalCompactCover K hζ P
local notation "V" => SourceKPAdelicTorusInducedSpace K hζ
local notation "ρ" => sourceKPAdelicLocalBorelRepresentation K hζ P
local notation "z₀" => sourceFiniteKPProjectiveBorelCenter K hζ P
local notation "n₀" => sourceFiniteKPProjectiveBorelUpper K hζ P
local notation "d₀" => sourceFiniteKPProjectiveBorelDiagonal K hζ P
local notation "e₀" => sourceFiniteKPProjectiveBorelEquiv K hζ P
local notation "ν₀" => sourceFiniteKPNormalizedBorelBase K hζ P
local notation "I" => IdeleGroup.ofAdicCompletion (𝓞 K) K P

def sourceKPLocalCompactBorelRatio : B →* Lˣ := (ν₀).comp (e₀).symm.toMonoidHom

theorem sourceKPLocalCompactBorelTorus_idele (b : B) :
    sourceKPAdelicTorusIdele K hζ
      (sourceKPAdelicBorelTorusProjection K hζ (sourceKPAdelicLocalBorel K hζ P b)) =
      I (sourceKPLocalCompactBorelRatio K hζ P b) := by
  let M := (sourceKPAdelicTorusIdele K hζ).comp
    ((sourceKPAdelicBorelTorusProjection K hζ).comp (sourceKPAdelicLocalBorel K hζ P))
  let R := sourceKPLocalCompactBorelRatio K hζ P
  have hZ (z : rootsOfUnity 3 L) : M (z₀ z) = 1 := by
    change sourceKPAdelicTorusIdele K hζ
      (sourceKPAdelicBorelTorusProjection K hζ (sourceKPAdelicLocalBorel K hζ P (z₀ z))) = 1
    rw [sourceKPAdelicLocalBorel_center K hζ P,
      show sourceKPAdelicBorelCenter K hζ ((sourceKPRootsTransport K hζ P).symm z) =
        sourceKPAdelicBorelTorusInclusion K hζ
          (sourceKPAdelicTorusInducingCenter K hζ ((sourceKPRootsTransport K hζ P).symm z)).val from rfl,
      sourceKPAdelicBorelTorusProjection_inclusion,sourceKPAdelicTorusIdele_center]
  have hN (x : L) : M (n₀ x) = 1 := by
    let a : 𝔸[K] := (0, sourceKPFiniteAdditiveSingle K P x)
    change sourceKPAdelicTorusIdele K hζ
      (sourceKPAdelicBorelTorusProjection K hζ (sourceKPAdelicLocalBorel K hζ P (n₀ x))) = 1
    rw [sourceKPAdelicLocalBorel_upper K hζ P]
    change sourceKPAdelicTorusIdele K hζ
      (sourceKPAdelicBorelTorusProjection K hζ (sourceKPAdelicBorelCoordinatesEquiv K hζ (a, 1))) = 1
    rw [sourceKPAdelicBorelTorusProjection_coordinates K hζ a 1, map_one]
  have hD (y : Lˣ) : M (d₀ y) = I y := by
    change sourceKPAdelicTorusIdele K hζ
      (sourceKPAdelicBorelTorusProjection K hζ (sourceKPAdelicLocalBorel K hζ P (d₀ y))) = I y
    rw [sourceKPAdelicLocalBorel_diagonal K hζ P,sourceKPAdelicBorelTorusProjection_inclusion,
      sourceKPAdelicLocalTorusSection_idele K hζ P]
  have hRZ (z : rootsOfUnity 3 L) : R (z₀ z) = 1 := by
    change ν₀ ((e₀).symm (z₀ z)) = 1
    rw [sourceFiniteKPProjectiveBorelCenter,MulEquiv.symm_apply_apply]
    exact map_one (GeneralLinearGroup.det : GL (Fin 2) L →* Lˣ)
  have hRN (x : L) : R (n₀ x) = 1 := by
    change ν₀ ((e₀).symm (n₀ x)) = 1
    rw [sourceFiniteKPProjectiveBorelUpper,MulEquiv.symm_apply_apply]
    exact sourceGL2Upper_det x
  have hRD (y : Lˣ) : R (d₀ y) = y := by
    change ν₀ ((e₀).symm (d₀ y)) = y
    rw [sourceFiniteKPProjectiveBorelDiagonal,MulEquiv.symm_apply_apply]
    exact sourceGL2Diagonal_det y
  obtain ⟨z,x,y,hy⟩ := sourceFiniteKPProjectiveBorel_factor K hζ P b
  have hb : b = z₀ z*n₀ x*d₀ y := Subtype.ext hy
  change M b = I (R b)
  rw [hb,map_mul M,map_mul M,hZ,hN,hD,one_mul,one_mul,
    map_mul R,map_mul R,hRZ,hRN,hRD,one_mul,one_mul]

theorem sourceKPLocalCompactBorelTorus_norm_one (b : B) (hb : b.val ∈ C) :
    sourceKPIdeleAbsoluteNorm K (sourceKPAdelicTorusIdele K hζ
      (sourceKPAdelicBorelTorusProjection K hζ (sourceKPAdelicLocalBorel K hζ P b))) = 1 := by
  rw [sourceKPLocalCompactBorelTorus_idele K hζ P, sourceKPIdeleAbsoluteNorm_ofAdicCompletion]
  exact Valued.toNormedField.norm_eq_one_iff.mpr
    (sourceKPLocalCompactBorel_base_valuation K hζ P b hb)

theorem sourceKPLocalCompactBorelFlat_action (s : ℂ) (b : B) (hb : b.val ∈ C) (v : V 0) :
    ρ s b (sourceKPLocalCompactTorusFlatEquiv K hζ s v) =
      sourceKPLocalCompactTorusFlatEquiv K hζ s (ρ 0 b v) := by
  let c := sourceKPAdelicLocalBorel K hζ P b
  have h := sourceKPLocalCompactTorusFlatEquiv_action K hζ s c v
  have hc : sourceKPLocalCompactTorusNorm K hζ s (sourceKPAdelicBorelTorusProjection K hζ c) = 1 :=
    sourceKPIdeleComplexNorm_of_norm_one K s _
      (sourceKPLocalCompactBorelTorus_norm_one K hζ P b hb)
  rw [hc,Units.val_one,one_smul] at h
  exact h

end
end ArtinMatthews
